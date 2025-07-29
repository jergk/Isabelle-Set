theory Record_Package
imports Isabelle_Set.TSBasics
    HOTG.HOTG_Binary_Relations
    Transport.Binary_Relations_Functions
    HOTG.HOTG_Functions_Evaluation
    HOTG.HOTG_Functions
    TSFunctions_Base
    SStrings
    Bin_Function_Properties
keywords 
    "extends"
    "contains"
    "\<Ztypecolon>"
and
    "StructureType"
    "Class" :: thy_decl

begin

definition select ("_@_" [999,999]) where
    "select r l \<equiv> eval_rel (rel r) l "
declare select_def[simp]

(*Helpers*)
ML\<open>
fun check_termss ctx tss = tss |> flat |> Syntax.check_terms ctx |> unflat tss
fun parse_term_schematic ctxt = Syntax.parse_term (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)
fun binding_to_free lthy (b,typ,_) = Free (Binding.name_of b,Option.getOpt (typ,dummyT))
fun double x = (x,x)
fun zipWith f xs ys =
case (xs,ys) of
    ([],_) => []
| (_,[]) => []
| (x::xs',y::ys') => (f x y)::(zipWith f xs' ys')
\<close>

(*common term and typ constants*)
ML\<open>
(*terms*)
fun rel_t lthy = @{term "rel"}
fun type_of_t lthy = parse_term_schematic lthy "type_of"
fun eval_rel_t lthy = parse_term_schematic lthy "eval_rel"
fun mem_t lthy = parse_term_schematic lthy "mem"
fun type_t lthy =  parse_term_schematic lthy "type"
fun select_t lthy = parse_term_schematic lthy "select"
fun dom_t lthy = parse_term_schematic lthy "dom"
fun restrict_left_t lthy = parse_term_schematic lthy "set_rel_restrict_left_set"
fun insert_t lthy = parse_term_schematic lthy "insert"
fun bin_union_t lthy = parse_term_schematic lthy "bin_union"
fun empty_set_t lthy = parse_term_schematic lthy "emptyset"
fun true_t lthy =  @{term "True"}

(*types*)
val record_typ = @{typ "set type"}
val set_typ = @{typ "set"}
\<close>

(*Helpers*)


(*Types to manage info about the record type*)
ML\<open> 
type softType = term
type field = 
    {label : term
    ,mix : mixfix
    , soft_type : softType}
type parameter = 
    {param : (binding * typ option * mixfix)
    , soft_type : softType}
type parent = 
    {name : string
    ,soft_type : softType}
type law = 
    {binding: binding
    , prop : term}
type record_context = 
    {name : string
    ,self : binding
    ,parameters : parameter list
    ,parents : parent list
    ,fields : field list
    ,laws: law list
    }
\<close>

(*Preprocessing*)
ML\<open> 
fun process_softtype lthy = Option.map (parse_term_schematic lthy)
    #> rpair (parse_term_schematic lthy "Any")
    #> Option.getOpt
(*take the parser output for fields and parse the name and soft type to terms*)
fun process_field lthy (((name_str,mix),styp_str) : (string * mixfix) * string option) =
    {
        label = parse_term_schematic lthy name_str,
        mix = mix,
        soft_type = process_softtype lthy styp_str
    } : field
fun process_fields lthy = map (process_field lthy)

(* take the parser output for parameters and parse the typ and soft type*)
fun process_parameter lthy ((var, styp_str): ((binding * string option * mixfix) * string option)) =
    {
        param = Proof_Context.read_var var lthy |> fst,
        soft_type =  process_softtype lthy styp_str
    } : parameter
fun process_parameters lthy = map (process_parameter lthy)

(* extract name from parent class*)
fun process_parent lthy par = let
    val parent_term =  par |> Syntax.read_term lthy
    val parent_const = parent_term |> strip_comb |> fst 
    val name = if is_Const parent_const
        then parent_const |> dest_Const |> fst |> Binding.qualified_name  |> Binding.name_of
        else error "the name of the parent:"^par^"couldn't be determined" 
    in {name = name, soft_type = parent_term }:parent end

fun process_parents lthy =  map (process_parent lthy)

fun process_law lthy ((binding, _) , law_str) = let 
    val law = law_str |> Syntax.read_prop lthy |> HOLogic.dest_Trueprop
    in {binding = binding, prop = law} : law end
fun process_laws lthy = map (process_law lthy)
\<close>


(* Props to build soft type and theorems*)
ML\<open>
(*prop for types of fields*)
fun build_field_type_constraint (field:field) lthy r = 
    ((type_of_t lthy) $ (select_t lthy $ r $ #label field )) $ (#soft_type field)

(*prop for membership of fields*)
fun build_field_mem_constraint (field:field) lthy r =
    ((mem_t lthy) $ (#label field)) $ (dom_t lthy $ r)

(*props for types of parents*)
fun build_parent_constraint (parent:parent) lthy r = 
    ((type_of_t lthy $ r) $ (#soft_type parent))

(*props for types of parameters*)
fun build_param_constraint (param:parameter) lthy r = 
    (type_of_t lthy) $ (binding_to_free lthy (#param param)) $ (#soft_type param)

(*props for assumes*)
fun build_law_constraint (law:law) lthy r = (#prop law)
\<close>

(*build proposition for all the lemmas*)
ML\<open>
(*r \<Ztypecolon> Record A B C *)
fun record_typed (ctxt:record_context) r lthy = let 
        val parameter_names = ctxt |> # parameters |> 
            map ( #param #> #1 #> Binding.name_of) 
        val free_parameters =ctxt |> # parameters |> 
            map  (#param #> binding_to_free lthy) 

        val lthy' = Variable.add_fixes (parameter_names) lthy |> snd
        val lthy'' = Variable.add_fixes_binding [ctxt |> #self] lthy' |> snd

        (*Premise*)
        val r_type = ctxt |> #name |> parse_term_schematic lthy''
        val record_type = list_comb (r_type, free_parameters)
        val prem = type_of_t lthy $ r $ record_type 
    in (prem,lthy'') 
    end

fun record_typed_prop (ctxt:record_context) r lthy = record_typed ctxt r lthy |> apfst (HOLogic.mk_Trueprop) 

(* r \<Ztypecolon> Record A B C \<Longrightarrow> conc *)
fun record_implies_conc ctxt lthy conc =
    let
        val r = Free (Binding.name_of (ctxt |> #self), set_typ)

        val (prem,lthy'') = record_typed_prop ctxt r lthy
        (*conclusion*)
        val goal = conc lthy'' r |> (HOLogic.mk_Trueprop #> pair prem #> Logic.mk_implies #> Syntax.check_term lthy'')
        (*TODO proof*)
        in (goal,lthy'')
    end

fun field_types_prop ctxt lthy = 
    build_field_type_constraint 
    #> record_implies_conc ctxt lthy

fun field_mem_prop ctxt lthy = 
    build_field_mem_constraint 
    #> record_implies_conc ctxt lthy

fun parent_subtyping_prop ctxt lthy =
    build_parent_constraint 
    #> record_implies_conc ctxt lthy

fun parameter_type_prop ctxt lthy =
    build_param_constraint 
    #> record_implies_conc ctxt lthy

fun law_prop ctxt lthy =
    build_law_constraint 
    #> record_implies_conc ctxt lthy

fun intro_prop ctxt lthy record_constraints =
    let 
        val r = Free (Binding.name_of (ctxt |> #self), set_typ)

        val (conc,lthy'') = record_typed_prop ctxt r lthy
        val goal = conc  
            |> pair (map HOLogic.mk_Trueprop record_constraints)
            |> Logic.list_implies 
            |> Syntax.check_term lthy''
    in (goal,lthy'')
    end
\<close>

(*build cheated theorems*)
ML\<open>

fun cheat lthy term = Goal.prove lthy [] [] term (fn {prems,context} => Skip_Proof.cheat_tac context 1)
fun bind_to_struct (ctxt:record_context) = ctxt |> #name |> Binding.prefix true 

fun cheat_thm lthy (goal,lthy') = 
    cheat lthy goal |> singleton (Proof_Context.export lthy' lthy)

fun bind_name_with_suffix suffix ctxt lthy = 
       Binding.name 
    #> Binding.suffix_name suffix 
    #> bind_to_struct ctxt
val _ = Pretty.writeln

fun cheat_field_types_thms ctxt lthy =
        (#fields ctxt)
    |> map double
    |> map (apfst (#label #> Syntax.pretty_term lthy #> Pretty.pure_string_of #> bind_name_with_suffix "_field_type" ctxt lthy))
    |> map (apsnd (field_types_prop ctxt lthy))
    |> map (apsnd (cheat_thm lthy))

fun cheat_field_mem_thms ctxt lthy =
        (#fields ctxt)
    |> map double
    |> map (apfst (#label #> Syntax.pretty_term lthy #> Pretty.pure_string_of #> bind_name_with_suffix "_mem" ctxt lthy))
    |> map (apsnd (field_mem_prop ctxt lthy))
    |> map (apsnd (cheat_thm lthy))


fun cheat_parent_subtyping_thms ctxt lthy =
        (#parents ctxt)
    |> map double
    |> map_index (uncurry (fn i => apfst (#name #> bind_name_with_suffix ("_sub_type"^ Int.toString i) ctxt lthy)))
    |> map (apsnd (parent_subtyping_prop ctxt lthy))
    |> map (apsnd (cheat_thm lthy))

fun cheat_parameter_type_thms ctxt lthy =
        (#parameters ctxt)
    |> map double
    |> map (apfst (#param #> #1 #> Binding.name_of #> bind_name_with_suffix "_type" ctxt lthy))
    |> map (apsnd (parameter_type_prop ctxt lthy) )
    |> map (apsnd (cheat_thm lthy))

fun cheat_laws_thms (ctxt:record_context) lthy =
    ctxt 
    |> #laws
    |> map (fn law => (law |> #binding,law))
    |> map_index (uncurry (fn i => apfst (fn s => if Binding.is_empty s then Binding.name ("thm"^Int.toString i) else s)))
    |> map (apfst (bind_to_struct ctxt))
    |> map (apsnd (law_prop ctxt lthy))
    |> map (apsnd (cheat_thm lthy))

fun cheat_intro_thms record_prop_list (ctxt:record_context) lthy =
    intro_prop ctxt lthy record_prop_list
    |> cheat_thm lthy
    |> pair ("intro" |> Binding.name |> bind_to_struct ctxt)
    |> single
\<close>

(*Notes a definition*)
ML\<open>
fun add_defn ((b,_,mx),t) lthy = let
    val arg = ((b, mx), (Binding.empty_atts,t lthy))
    val ((_, (thm_name , thm)), lthy') = Local_Theory.define arg lthy
    val thm' =  thm (*|>  singleton (Proof_Context.export lthy' lthy')*)
    val lthy'' = Local_Theory.note ((Binding.suffix_name "_def" b, []), [thm']) lthy' |> snd
in
    (thm, lthy'')
end
\<close>

ML\<open>
fun declare_structure_type (self:binding,name:binding) parameters parents fields laws lthy' =
let
    (* preprocess by parsing terms and types *)
    val ctxt : record_context = {
        name = Binding.name_of name,
        self = self,
        parameters = process_parameters lthy' parameters,
        parents = process_parents lthy' parents,
        fields = process_fields lthy' fields,
        laws = process_laws lthy' laws
        }
    
    (* build constraints*)
    fun map_double lthy r f = map (double #> apfst (fn x => f x lthy r))

    fun param_constraints lthy r = ctxt |> #parameters |> map_double lthy r build_param_constraint
    fun parent_constraints lthy r = ctxt |> #parents |> map_double lthy r build_parent_constraint
    fun field_type_constraints lthy r = ctxt |> #fields |> map_double lthy r build_field_type_constraint
    fun field_mem_constraints lthy r = ctxt |> #fields |> map_double lthy r build_field_mem_constraint
    fun law_constraints lthy r = ctxt |> #laws |> map_double lthy r build_law_constraint

    (*the soft type constraint combines all constraints*)
    fun softtype_constraint_list lthy r = 
        ( map fst (param_constraints lthy r)
        @ map fst (parent_constraints lthy r)
        @ map fst (field_type_constraints lthy r)
        @ map fst (field_mem_constraints lthy r)
        @ map fst (law_constraints lthy r) )
        
    val record = Free (Binding.name_of (ctxt |> #self), set_typ)

    fun softtype_constraint lthy =
        softtype_constraint_list lthy record
        |> (fn props => if null props then [true_t lthy] else props)
        |> foldl1 HOLogic.mk_conj

    (* type inference*)
    fun parameter_frees lthy = ctxt 
        |> # parameters 
        |> map (#param #> binding_to_free lthy)
    val checked_terms = check_termss lthy' 
        [ [softtype_constraint lthy']
        , (parameter_frees lthy')
        , (ctxt |> # parents |> map #soft_type)
        , [record]] 

    (* update context with type checked parent softtypes*)
    val ctxt' = {
        name = #name ctxt,
        self = #self ctxt,
        parameters = #parameters ctxt,
        parents = (zipWith (fn (p:parent) => fn (ct:term) => ({name = #name p,soft_type = ct}:parent))
            (ctxt |> #parents) 
            (checked_terms |> drop 2 |> hd)) ,
        fields = #fields ctxt,
        laws = #laws ctxt
    } : record_context


    (* prepare record type for decl *)
    val type_constraints' = checked_terms |> hd |> hd
    val parameter_frees' = checked_terms |> drop 1 |> hd 

    fun soft_type lthy = type_t lthy $ (lambda record (type_constraints'))
    fun add_parameters params t = fold_rev (fn param => fn t' => lambda param t' ) params t

    (*record type ready for decl:*)
    fun soft_type_term lthy = soft_type lthy |> add_parameters (parameter_frees') |> Syntax.check_term lthy

    (*add defs*)
    val all_defs = 
        (*field_consts_def@*)
        [((Binding.name (#name ctxt),record_typ,NoSyn),soft_type_term)] 
        (*@[(("dom" |> Binding.name|> bind_to_struct ctxt,record_typ,NoSyn),record_domain')]*)
        (*) @[(("leq" |> Binding.name |> bind_to_struct ,record_typ,NoSyn),equiv_term)]*)
    val (def_thms, thy_with_defs) = fold_map (add_defn) all_defs lthy'

    (*add theorems*)
    val my_thms = map (fn t => t thy_with_defs) 
        [cheat_field_types_thms ctxt' 
        ,cheat_field_mem_thms ctxt'
        ,cheat_parent_subtyping_thms ctxt'
        ,cheat_parameter_type_thms ctxt'
        ,cheat_laws_thms ctxt'
        ,cheat_intro_thms (softtype_constraint_list lthy' record)  ctxt'] 
        |> flat
        |> map (apfst (rpair []) #> apsnd single)

    val thy_with_thms = fold (fn thm =>fn thy => Local_Theory.note thm thy |> snd) my_thms thy_with_defs

in  
    thy_with_thms

end
\<close>

(*
TODO: 
- Equivalence using domains of record types. Problem: 
    We want to restrict to the domain but the Records domain may depend on parameters. 
    Better way to bind them than to list them all? 

(*record domains*)
val _ = curry (op ^) "" ""
fun parent_dom n = n^".dom"
val x = fold
fun parent_domains r lthy (ctxt:record_context) = 
    ctxt 
    |> #parents 
    |> map ( #name #> parent_dom #> parse_term_schematic lthy #> (fn p => p $ r))
fun own_domain lthy (ctxt:record_context) = fold 
    (fn f => fn s => insert_t lthy $ #label f $ s) 
    (#fields ctxt) 
    (empty_set_t lthy)

fun record_domain r ctxt lthy = 
    fold (fn d => fn s => bin_union_t lthy $ d $ s) 
    (parent_domains r lthy ctxt)
    (own_domain lthy ctxt) |> Syntax.check_term lthy

fun record_domain' lthy = (lambda record (record_domain record ctxt' lthy))
*)

ML\<open>

val set_type_name = @{type_name "set"}

val soft_type_of_ = Parse.$$$ "\<Ztypecolon>";
val soft_type_parser = soft_type_of_ |-- Parse.!!! (Parse.term);
val soft_type_parser_embedded = soft_type_of_ |-- Parse.!!! (Scan.ahead Parse.term -- Parse.embedded);

val soft_params = Parse.params -- (Scan.option soft_type_parser)
     >>  (fn (params,ST) => map (rpair ST) params);

val soft_set_params = 
    (Scan.repeat1 Parse.term) -- (Scan.option soft_type_parser)
    >> (fn ((bs), st) => map (fn y => ((y, NoSyn),st)) bs);

val soft_vars = Parse.and_list1 (soft_params) >> flat;
val soft_set_vars = Parse.and_list1 (soft_params) >> flat;
val soft_fields = Parse.list1 soft_set_params >> flat;
\<close>

(*StructureType parser*)
ML\<open>
val extends_ = Parse.$$$ "extends"
val fixes_ = Parse.$$$ "fixes"
val contains_ = Parse.$$$ "contains"
val assumes_ = Parse.$$$ "where"
val structure_type_name_parser = Parse.binding -- (soft_type_of_ |-- Parse.binding)
val structure_type_args_parser = Scan.optional (fixes_ |-- soft_vars) []
val structure_type_extends_parser = Scan.optional (extends_ |-- Parse.!!! (Parse.and_list1 Parse.term)) []
val structure_type_fields_parser = Scan.optional (contains_ |-- Parse.!!! soft_fields) []

val prop_parser = Parse_Spec.opt_thm_name ":" -- Parse.prop
val props_parser = Scan.optional (assumes_ |-- Parse.!!! (Parse.and_list1 prop_parser)) []

val structure_type_parser = structure_type_name_parser -- structure_type_args_parser -- structure_type_extends_parser -- structure_type_fields_parser --props_parser
\<close>

ML\<open>
Outer_Syntax.local_theory @{command_keyword "StructureType"}
    "description of StructureType"

    (structure_type_parser >> (declare_structure_type |> uncurry |> uncurry |> uncurry |> uncurry))
\<close>
(*TODO add inference and implicit arguments in the future*)
ML\<open>
Outer_Syntax.local_theory @{command_keyword "Class"}
    "description of StructureType"
    ( structure_type_parser >> (declare_structure_type  |> uncurry |> uncurry |> uncurry |> uncurry))
\<close>

(*record terms*)
open_bundle record_syntax_rel
begin
syntax 
    "_record_entry_rel" :: \<open>'a \<Rightarrow> 'b  \<Rightarrow> 'c\<close> (" _ := _ /")
    "_record_rel" :: \<open>args \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)\<close> ("{| _ |}")
end
(* record instances *)
translations
  "{| l := v, rest |}" \<rightleftharpoons> "CONST extend_set l v {| rest |}"
  "{| l := v |} " \<rightleftharpoons> "CONST extend_set l v (CONST emptyset)"


end