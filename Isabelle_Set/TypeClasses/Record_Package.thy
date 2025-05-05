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
and
    "Structure" :: thy_decl
and 
    "Instance" :: thy_goal
begin

(*debug*)
ML\<open>
    fun pretty_structure_type (self,name) parameters parents fields lthy= 
        let 
            fun pretty_option_map f opt = ((Option.map f opt), Pretty.str "") |> Option.getOpt
            val pretty_name = Pretty.block [Pretty.str "Name: ", Binding.pretty  name]
            fun pretty_soft_decl ((b,t,m),st) =  Pretty.block 
                [ Binding.pretty b
                , (pretty_option_map (fn s => Pretty.block [Pretty.str " :: ",Pretty.str s]) t)
                , (pretty_option_map (fn s => Pretty.block [Pretty.str " \<Ztypecolon> ",Pretty.str s]) st)]
            val (typ_params,params_ctxt) = fold_map Proof_Context.read_var (map #1 parameters) lthy
            val pretty_params = Pretty.chunks [
                Pretty.big_list "Parameters: "  (map pretty_soft_decl parameters),
                Pretty.big_list "Context" ((Proof_Context.add_fixes typ_params params_ctxt) |> #2 |> Proof_Context.pretty_ctxt)]
            val pretty_parents = Pretty.big_list "Parent Classes: " (map (Pretty.str) parents )
            val pretty_fields = Pretty.big_list "Fields: " (map pretty_soft_decl fields)
        in  [pretty_name, pretty_params,pretty_parents,pretty_fields] |> Pretty.chunks
        end
    fun debug_structure_type name parameters parents fields thy = 
        pretty_structure_type name parameters parents fields thy
        |> Pretty.writeln;
    \<close>


(* 
flat and open

restrictions
- no args yet
- not dependent
- no projections
- no theorems


note: don't add projections while creating soft type ?

todo optional parent name?
    how to use projections from parent?
    incase of 



*)
term "eval_rel"

ML\<open>
 val x : binding = Binding.prefix true (Binding.name_of @{binding "S"}) @{binding "abc"}
\<close>

ML\<open> Const (@{const_name "type_of"},@{typ "'a \<Rightarrow> 'a Soft_Types_HOL_Base.type \<Rightarrow> bool"})
    |> Thm.cterm_of @{context} \<close>



ML\<open>
fun note_many qname ((name, attrs), thms) =
    Local_Theory.note ((Binding.qualify false qname name, attrs), thms)
fun note_single1 qname ((name, attrs), thm) =
    note_many qname ((name, attrs), [thm])
fun note_single2 name attrs (qname, thm) =
    note_many (Binding.name_of qname) ((name, attrs), [thm])
\<close>

ML\<open>
    fun pretty_thm ctxt thm = Syntax.pretty_term ctxt (Thm.prop_of thm)
    fun pretty_thms ctxt n thms = Pretty.big_list n (Pretty.commas (map (pretty_thm ctxt) thms))
\<close>

ML\<open>
    (* parse term schematic for polymorphic terms
        instead Proof_Context.read_term_pattern ? 
    *)
    fun parse_term_schematic ctxt = Syntax.parse_term (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)



\<close>


ML\<open>val x = @{typ "_"}\<close>
ML\<open>dummyT\<close>
ML\<open>Syntax.check_terms\<close>
ML \<open> fastype_of @{term "set_rel_restrict_left_set"} \<close>

ML\<open> fun check_termss ctx tss = tss |> flat |> Syntax.check_terms ctx |> unflat tss\<close>

definition select ("_@_" [999,998]) where
    "select r l \<equiv> eval_rel (rel r) l "
declare select_def[simp]

term "emptyset"

ML\<open>(String.explode #> map (fn x => if x = #"." then #"_" else x) #> String.implode)  "a.b"\<close>

ML\<open>
    fun declare_structure_type_flat_open (self,name) parameters parents fields assms lthy =
    let

        (*term functions to construct the soft type*)
        val rel_t = @{term "rel"}
        val type_of_t = parse_term_schematic lthy "type_of"
        val eval_rel_t = parse_term_schematic lthy "eval_rel"
        val mem_t = parse_term_schematic lthy "mem"
        val type_t =  parse_term_schematic lthy "type"
        val select_t = parse_term_schematic lthy "select"
        val dom_t = parse_term_schematic lthy "dom"
        val restrict_left_t = parse_term_schematic lthy "set_rel_restrict_left_set"
        val insert_t = parse_term_schematic lthy "insert"
        val empty_set_t = parse_term_schematic lthy "emptyset"
        val true_t =  @{term "True"}

        (*types*)
        val record_typ = @{typ "set type"}
        val set_typ = @{typ "set"}

        (*basic pre processing*)

        (* prefixes <name>. *)
        val bind_to_struct =  Binding.prefix true (Binding.name_of name)

        val process_types = fold_map (fn (b,st) => 
            Proof_Context.read_var b >> (rpair st))
        fun process_soft_types bs ctxt = 
            map (ctxt |> parse_term_schematic |> Option.map |> apsnd) bs
        fun process_soft_vars bs ctxt = process_types (process_soft_types bs ctxt) ctxt 

        (* read type and softvar term *)
        fun parameters_typed lthy = process_soft_vars parameters lthy |> fst

        fun fields_typed lthy = process_soft_vars fields lthy |> fst
        
        fun binding_to_free ctxt (b,typ,_) = Free (Binding.name_of b,Option.getOpt (typ,dummyT))

        (*function to splice out name of parent class*)
        fun parent_term lthy=  Syntax.read_term lthy #> strip_comb #> fst 

        fun parent_name lthy t= let
            val parent_const = parent_term lthy t
            val name = if is_Const parent_const
                then parent_const |> dest_Const |> fst
                else "parent name not found" (*TODO error*)
            in name end

        fun parent_name' lthy t = 
            parent_name lthy t 
            |> String.explode 
            |> map (fn x => if x = #"." then #"_" else x) 
            |> String.implode


        (*FIELD CONSTS*)

        (*define name.field1 \<equiv> $field1*)

        val field_consts_def  = map ( fn ((b,t,m),_) => 
                (( b |> bind_to_struct ,set_typ,NoSyn)
                , fn thy' => parse_term_schematic thy' ("$"^(Binding.name_of b)) |> Syntax.check_term thy'))
            fields
        val field_consts = field_consts_def |> map (#1 #> #1)



        (*STRUCTURE SOFT TYPE*)

        (*Definition*)

        (*free var bound in predicate *)
        val record = Free (Binding.name_of self, set_typ)

        (*props for types of fields*)
        fun build_field_type_constraint thy' r ((b,_,_),maybe_st) = 
            Option.map (fn st => 
                (type_of_t  $ (select_t $ r $  (b |> Binding.name_of |> parse_term_schematic thy'))) $ st) 
                maybe_st
        fun field_type_props r thy' = map (build_field_type_constraint thy' r) (fields_typed thy')

        (*props for membership of fields*)
        fun build_field_mem_constraint thy' r ((b,_,_),_) = SOME
            ((mem_t $ (b |> Binding.name_of |> parse_term_schematic thy')) $ (dom_t $ r))
        fun field_mem_props r thy' = map (build_field_mem_constraint thy' r) (fields_typed thy')

        (*props for types of parents*)
        fun build_parent_constraint thy' r name = 
            ((type_of_t $ r) $ parse_term_schematic thy' name)
            |> SOME
        fun parent_props r thy' = map (build_parent_constraint thy' r) parents

        (*props for types of parameters*)
        fun build_param_constraint thy' (b,maybe_st) = 
            Option.map (fn st => (type_of_t  $ (binding_to_free thy' b)) $ st) maybe_st
        fun parameter_props thy' = map (build_param_constraint thy') (parameters_typed thy')

        (*props for assumes*)
        fun assms_props thy'= map (snd #> Syntax.read_prop thy' #> HOLogic.dest_Trueprop#> SOME) assms

        (*prop for soft type*)
        fun type_constraints thy' = 
            parameter_props thy' @ parent_props record thy' @ field_type_props record thy' @ field_mem_props record thy' @ assms_props thy' 
            |> map_filter I
            |> (fn props => if null props then [true_t] else props)
            |> foldl1 HOLogic.mk_conj

        (*type inference with respect to all occuring free variables*)

        (*val field_frees = map (fst #> #1 #> (fn b => Free (Binding.name_of b,set_typ))) fields
        val field_frees = map (fst #> #1 #> (fn b => Free (b |> bind_to_struct |> Binding.name_of  ,set_typ))) fields*)
        fun parameter_frees lthy' =  map (fst #> binding_to_free lthy) (parameters_typed lthy')

        fun checked_terms thy' = check_termss thy' 
            [ [type_constraints thy']
            , (parameter_frees thy')
            , (map (parse_term_schematic thy') parents)
            (*, field_frees *)
            , [record]] 

        fun type_constraints' thy' = checked_terms thy' |> hd |> hd
        fun parameter_frees' thy' = checked_terms thy' |> drop 1 |> hd 
        fun parents' thy' = checked_terms thy' |> drop 2 |> hd 
       
       

        fun soft_type thy' = type_t $ (lambda record (type_constraints' thy'))
        fun add_parameters thy' ps t = fold_rev (fn p => fn t' => lambda (p) t' ) ps t

        (*soft type ready for decl*)
        fun soft_type_term thy' = soft_type thy' |> add_parameters thy' (parameter_frees' thy') |> Syntax.check_term thy'


        (*helper functions *)

        fun record_typed r lthy = let 

                val parameter_names = map (fst #> #1 #> Binding.name_of) (parameters_typed lthy)
                val free_parameters = map  (#1 #> binding_to_free lthy) (parameters_typed lthy)
                (*val free_parameters = parameter_frees' lthy*)
                val lthy' = Variable.add_fixes (parameter_names) lthy |> snd
                val lthy'' = Variable.add_fixes_binding [self] lthy' |> snd

                (*Premise*)
                val r_type = name |> Binding.name_of |> parse_term_schematic lthy''
                val record_type = list_comb (r_type, free_parameters)
                val prem = type_of_t $ r $ record_type 
            in (prem,lthy'') 
            end

        (* EQUIVALENCE*)

        (*

        restriction
        for recordtype R with labels l_1 - l_n
        set_rel_restrict_left_set ?r {l_1, ..., l_n} \<Ztypecolon> R)"


        R.equiv r1 r2 =  ?r1 \<Ztypecolon> R \<and> ?r1 \<Ztypecolon> R \<and>
        set_rel_restrict_left_set ?r1 {l_1, ..., l_n} = 
        set_rel_restrict_left_set ?r2 {l_1, ..., l_n} 

        *)
        fun equiv_term thy' = let

                val r1 = Free ("r1", set_typ)
                val r2 = Free ("r2", set_typ)

                val dom = fold (fn b => fn dom => 
                        insert_t
                        $ (b |> #1 |> #1 |> Binding.name_of |> parse_term_schematic thy') 
                        $ dom  ) 
                    (fields) empty_set_t 
                fun restriction r  = (restrict_left_t |> Syntax.check_term thy') $ r $ dom 
                val restriction_equiv  = HOLogic.mk_eq (restriction r1,restriction r2) 
                
                val parent_equivs = map (fn t =>
                    let
                        val (_,args) = t |> parse_term_schematic thy' |> strip_comb 
                        val name = parent_name thy' t
                        val parent_leq = name  ^ ".leq" |> parse_term_schematic thy'
                        (*drop 1 is ugly hack to drop a type constraint*)
                    in (list_comb (parent_leq,drop 1 args)) $ r1 $ r2 end)
                    (parents)
                val _ = parent_equivs |> map (Syntax.pretty_term (Config.put show_types true thy')) |> Pretty.big_list "eq"|> Pretty.writeln
                
                fun record_typed' r = record_typed r thy' |> fst
                val (r1_typed,thy'') = record_typed r1 thy'
                val (r2_typed,_) = record_typed r2 thy'
                (*val equiv = foldl1 HOLogic.mk_conj ([r1_typed,r2_typed,restriction_equiv]@parent_equivs)*)
                val equiv = foldl1 HOLogic.mk_conj ([restriction_equiv]@parent_equivs)
                val _ = equiv |> (Syntax.pretty_term (Config.put show_types true thy')) |> Pretty.writeln
                val checked = check_termss thy'' [[equiv],parameter_frees thy']
                val equiv' = checked |> hd |> hd
                val parameter_frees' = checked |> drop 1 |> hd
            in  add_parameters thy'' parameter_frees' (lambda r1 (lambda r2 ( equiv')))
               (*) |> tap (Syntax.pretty_term ( Config.put show_types true thy') #> Pretty.writeln)*)
            end




        (* THEOREMS *)

        (*helper functions *)
        fun record_typed_prem lthy = record_typed record lthy
            |> apfst (HOLogic.mk_Trueprop) 

        fun cheat lthy term = Goal.prove lthy [] [] term (fn {prems,context} => Skip_Proof.cheat_tac context 1)

        fun field_types_thms lthy = let
                val (prem,lthy'') = record_typed_prem lthy
                (*conclusion*)
                fun conc field = build_field_type_constraint lthy'' record field
                fun goal field = conc field |> Option.map (HOLogic.mk_Trueprop #> pair prem #> Logic.mk_implies #> Syntax.check_term lthy'')
                (*TODO proof*)
                
                val thms = (fields_typed lthy)
                    |> map (fn f => Option.map ( f|> #1 |> #1 |> Binding.suffix_name "_type" |> bind_to_struct|> rpair [] |>  pair ) ( goal f))
                    |> map (Option.map (apsnd (cheat lthy'' #> singleton (Proof_Context.export lthy'' lthy) #> single)))
                    |> map_filter I 
            in thms
            end


        fun field_mem_thms lthy = let
            val (prem,lthy'') = record_typed_prem lthy
            (*conclusion*)
            fun conc field = build_field_mem_constraint lthy'' record field
            fun goal field = conc field |> Option.map (HOLogic.mk_Trueprop #> pair prem #> Logic.mk_implies #> Syntax.check_term lthy'')
            (*TODO proof*)
            val thms = (fields_typed lthy)
                |> map (fn f => Option.map ( f|> #1 |> #1 |> Binding.suffix_name "_mem" |> bind_to_struct|> rpair [] |>  pair ) ( goal f))
                |> map (Option.map (apsnd (cheat lthy'' #> singleton (Proof_Context.export lthy'' lthy) #> single)))
                |> map_filter I 
            in thms
            end


        fun parent_subtyping_thms lthy = let
            val (prem,lthy'') = record_typed_prem lthy
            (*conclusion*)
            fun conc parent = build_parent_constraint lthy'' record parent

            fun goal parent = conc parent |> Option.map (HOLogic.mk_Trueprop #> pair prem #> Logic.mk_implies #> Syntax.check_term lthy'')
            (*val _ = map (goal #> (Option.map (Syntax.pretty_term lthy #> Pretty.writeln))) parents*)

            (*TODO proof*)
            val thms = parents
                |> map (fn (f) => Option.map (  f |> parent_name' lthy |> Binding.name |> Binding.suffix_name "_subtype" |> bind_to_struct|> rpair [] |>  pair ) ( goal f))
                |> map (Option.map (apsnd (cheat lthy'' #> singleton (Proof_Context.export lthy'' lthy) #> single)))
                |> map_filter I 
            in thms
        end
        
        
        fun parameter_types_thms lthy = let
                val (prem,lthy'') = record_typed_prem lthy
                (*conclusion*)
                fun conc param = build_param_constraint lthy'' param
                fun goal param = conc param |> Option.map (HOLogic.mk_Trueprop #> pair prem #> Logic.mk_implies #> Syntax.check_term lthy'')
                (*TODO proof*)
                
                val thms = (parameters_typed lthy)
                    |> map (fn f => Option.map ( f|> #1 |> #1 |> Binding.suffix_name "_type" |> bind_to_struct|> rpair [] |>  pair ) ( goal f))
                    |> map (Option.map (apsnd (cheat lthy'' #> singleton (Proof_Context.export lthy'' lthy) #> single)))
                    |> map_filter I 
            in thms
            end

        (*        fun assms_props thy'= map (snd #> Syntax.read_prop thy' #> HOLogic.dest_Trueprop#> SOME) assms
*)
        fun assms_thms lthy = let
                val (prem,lthy'') = record_typed_prem lthy
                (*conclusion*)
                fun conc assm = Syntax.read_term lthy assm
                fun goal assm = conc assm |> HOLogic.mk_Trueprop |> pair prem |> Logic.mk_implies |> Syntax.check_term lthy
                (*TODO proof*)
                
                val thms = assms
                    |> map_index ( uncurry (fn i => apfst (apfst ((fn s => if Binding.is_empty s then Binding.name ("thm"^Int.toString i) else s) #> bind_to_struct ))))
                    |> map ((apsnd (goal #> (cheat lthy'' #> singleton (Proof_Context.export lthy'' lthy) #> single))))
            in thms
            end

        fun intro_thms lthy = let
                (*conclusion*)
                val prems = 
                     (parameter_props lthy @ parent_props record lthy @ field_type_props record lthy @ field_mem_props record lthy @ assms_props lthy)
                      |> map_filter I |> map HOLogic.mk_Trueprop

                val (conc,lthy'') = record_typed_prem lthy
                val goal = conc  |> pair prems |> Logic.list_implies |> Syntax.check_term lthy
                (*TODO proof*)
                val thms = goal |> cheat lthy'' |> singleton (Proof_Context.export lthy'' lthy) |> single 
                    |> pair ("intro" |> Binding.name |> bind_to_struct,[]) |> single
            in thms
            end


        (*
        
        BRINGING IT ALL TOGETHER
        
        *)

        fun add_defn ((b,_,mx),t) lthy = let
                val arg = ((b, mx), (Binding.empty_atts,t lthy))
                val ((_, (thm_name , thm)), lthy') = Local_Theory.define arg lthy
                val thm' =  thm (*|>  singleton (Proof_Context.export lthy' lthy')*)
                (*val _ = Pretty.writeln (Syntax.pretty_term lthy (t lthy))*)
                val lthy'' = Local_Theory.note ((Binding.suffix_name "_def" b, []), [thm']) lthy' |> snd
            in
                (thm, lthy'')
            end

        fun add_abbrev ((b,_,mx),t) lthy = let
                val arg = ((b, mx), (t lthy))
                val (_, lthy') = Local_Theory.abbrev Syntax.mode_default arg lthy
                (*val _ = Pretty.writeln (Syntax.pretty_term lthy (t lthy))*)
            in
                (lthy')
            end

(*)
        val all_abbrevs = field_consts_def
        val (thy_with_abbrevs) = fold (add_abbrev) all_abbrevs lthy
*)


        val all_defs = field_consts_def
            @[((name,record_typ,NoSyn),soft_type_term)]
            @[(("leq" |> Binding.name |> bind_to_struct ,record_typ,NoSyn),equiv_term)]
        val (def_thms, thy_with_defs) = fold_map (add_defn) all_defs lthy

        val my_thms = map (fn t => t thy_with_defs) 
            [field_types_thms
            ,field_mem_thms
            ,parent_subtyping_thms
            ,parameter_types_thms
            ,assms_thms
            ,intro_thms] 
            |> flat
        val thy_with_thms = fold (fn thm =>fn thy => Local_Theory.note thm thy |> snd) my_thms thy_with_defs

    in  
        Pretty.writeln (pretty_thms thy_with_defs (Binding.name_of name) def_thms);
        thy_with_thms

    end

    fun process_structure_type_flat name parameters parents fields thy =
        thy 
       (* |> tap (debug_structure_type name parameters parents fields) *)
        |> declare_structure_type_flat_open name parameters parents fields []
\<close>


(*soft params takes params and a \<Ztypecolon> after which applies to all params listed before (params of different soft types are seperated by and)
 imo not intuitive but like params which is used everywhere so its consistent at least ?*)
ML\<open>

val set_type_name = @{type_name "set"}

val soft_type_of_ = Parse.$$$ "\<Ztypecolon>";
val soft_type_parser = soft_type_of_ |-- Parse.!!! (Parse.term);
val soft_type_parser_embedded = soft_type_of_ |-- Parse.!!! (Scan.ahead Parse.term -- Parse.embedded);

val soft_params = Parse.params -- (Scan.option soft_type_parser)
     >>  (fn (params,ST) => map (rpair ST) params);

val soft_set_params = 
    (Scan.repeat1 Parse.binding) -- (Scan.option soft_type_parser)
    >> (fn ((bs), st) => map (fn y => ((y, SOME set_type_name, NoSyn),st)) bs);

val soft_vars = Parse.and_list1 (soft_params) >> flat;
val soft_set_vars = Parse.and_list1 (soft_params) >> flat;
val soft_fields = Parse.list1 soft_set_params >> flat;
\<close>

ML\<open>Binding.make\<close>
(*StructureType parser*)
ML\<open>
    val extends_ = Parse.$$$ "extends"
    val fixes_ = Parse.$$$ "fixes"
    val contains_ = Parse.$$$ "contains"
    val structure_type_name_parser = Parse.binding -- (soft_type_of_ |-- Parse.binding)
    val structure_type_args_parser = Scan.optional (fixes_ |-- soft_vars) []
    val structure_type_extends_parser = Scan.optional (extends_ |-- Parse.!!! (Parse.and_list1 Parse.term)) []
    val structure_type_fields_parser = Scan.optional (contains_ |-- Parse.!!! soft_fields) []

    val structure_type_parser = structure_type_name_parser -- structure_type_args_parser -- structure_type_extends_parser -- structure_type_fields_parser
\<close>

ML\<open>
Outer_Syntax.local_theory @{command_keyword "StructureType"}
    "description of StructureType"

    (structure_type_parser >> (process_structure_type_flat |> uncurry |> uncurry |> uncurry))
\<close>


(*Typeclasses : *)


ML\<open> fun pretty_prop (name,prop) = Pretty.block [Pretty.str ": ",Pretty.str prop]
    fun pretty_props props =  Pretty.big_list "Props: "  (map pretty_prop props) |> Pretty.writeln 
    fun debug_type_class name parameters parents fields assms thy =
        debug_structure_type name parameters parents fields thy |> K (pretty_props assms);
    fun process_type_class_flat name parameters parents fields assms thy =
        thy 
        (*|> tap (debug_type_class name parameters parents fields assms) *)
        |> declare_structure_type_flat_open name parameters parents fields assms

\<close>

ML\<open>
    val assumes_ = Parse.$$$ "where"
    val prop_parser = Parse_Spec.opt_thm_name ":" -- Parse.prop
    val props_parser = Scan.optional (assumes_ |-- Parse.!!! (Parse.and_list1 prop_parser)) []
    val type_class_parser = structure_type_parser -- props_parser 
\<close>

ML\<open>
Outer_Syntax.local_theory @{command_keyword "Class"}
    "description of StructureType"
    ( type_class_parser >> (process_type_class_flat |> uncurry |> uncurry |> uncurry |> uncurry))
\<close>

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


(*Tests and other stuff*)

definition "A x \<equiv> Any "
definition "B \<equiv> Any "
definition "C \<equiv> Any :: set type"


ML\<open>
    val test1 = lambda (Syntax.read_term @{context} "field11") (parse_term_schematic @{context} "type (\<lambda>x . x = field11 )");
    val _ = test1 |> Syntax.pretty_term (@{context} )|> Pretty.writeln \<close>

term "dom"


(*operational*)
StructureType self \<Ztypecolon> myStructure3 contains
    field1 ,
    field2 field3 \<Ztypecolon> Any
    print_theorems

(* unbundled extreme*)
StructureType self \<Ztypecolon> myStructure4 
    fixes arg1 \<Ztypecolon> "Any" and arg2 
    print_theorems

ML\<open>parse_term_schematic @{context} "myStructure arg1 arg2"\<close>

term "insert x {}"



(*everything*)
StructureType self \<Ztypecolon> myStructure 
    fixes "arg1":: set and arg2 \<Ztypecolon> "Any" and arg3 
    extends "myStructure3" and "myStructure4 arg2 arg3" 
    contains
        field1 ,
        field2 field3 \<Ztypecolon> "Element (self @ field1 )",
        field4 \<Ztypecolon> "(type (\<lambda>x . x = arg1 ))",
        field5 \<Ztypecolon> "Any"
print_theorems

ML\<open> 
    @{term "myStructure {} {} {}"} |> strip_comb |> fst;
    @{term "Any"} |> strip_comb |> fst;
    
\<close>

definition "test_struct \<equiv> {| myStructure.field1 := {} ,
         myStructure.field2 := {} ,
         myStructure.field3 := {} ,
         myStructure.field4 := {} ,
         myStructure.field5 := {} |}"

term "myStructure.leq {} {} {} test_struct test_struct"

term myStructure
term "myStructure.field1"
term "Record_Package.myStructure.field1"
term "field1"

thm "myStructure_def"

ML\<open>pretty_thm (Config.put show_types true @{context})@{thm "myStructure_def"}\<close>


(* bundled extreme*)
StructureType self \<Ztypecolon> myStructure2 
    fixes "arg1":: set and arg2 \<Ztypecolon> "Any" and arg3
    extends "myStructure arg1 arg2 arg3" 
    contains
        field1 \<Ztypecolon> "Element (select self myStructure.field1)"
print_theorems


(*everything*)

Class self \<Ztypecolon> Monoid 
    fixes "T" :: "set type"
    contains
        add \<Ztypecolon> "(T \<rightarrow> T \<rightarrow> T)",
        unit \<Ztypecolon> "T"
    where
        left_id : "is_left_identity T (self @ add) (self @ unit)" and 
        right_id: "is_right_identity T (self @ add) (self @ unit)" and 
        assoc: "is_associative T (self @ add)"
    print_theorems

lemma helper1:
    assumes "set_rel_restrict_left_set r1 d= set_rel_restrict_left_set r2 d"
        " l \<in> d "
    shows "r1 @ l = r2 @ l"
    proof -
        have rest: "rel (set_rel_restrict_left_set r d)` l = rel r `l " for r by auto
        from assms rest[of r1] rest[of r2] show ?thesis by auto 
    qed

lemma helper2:
    assumes "set_rel_restrict_left_set r1 d = set_rel_restrict_left_set r2 d"
        "l \<in> d"
        " l \<in> dom r1 "
    shows "l \<in> dom r2"
    proof -
        have r1: "l \<in> dom (set_rel_restrict_left_set r1 d)" using assms by auto
        then have r2: "l \<in> dom (set_rel_restrict_left_set r2 d)" using assms by blast
        then show ?thesis by auto
    qed




lemma equiv_implies_monoid:
    assumes "Monoid.leq T r1 r2 " "r1 \<Ztypecolon> Monoid T"
    shows " r2 \<Ztypecolon> Monoid T" using assms unfolding Monoid.leq_def
    proof -
        have leq: "r1\<restriction>\<^bsub>insert Monoid.unit (insert Monoid.add 0)\<^esub> = r2\<restriction>\<^bsub>insert Monoid.unit (insert Monoid.add 0)\<^esub>" 
        using assms unfolding Monoid.leq_def by simp
        have add: "r2 @ Monoid.add = r1 @ Monoid.add" using sym[OF leq] helper1 unfolding Monoid.leq_def by auto
        have unit: "r2 @ Monoid.unit = r1 @ Monoid.unit" using sym[OF leq] helper1 unfolding Monoid.leq_def by auto
        have ?thesis proof (intro Monoid.intro,goal_cases)
          case 1
          then show ?case using Monoid.add_type[OF assms(2)] add by auto
        next
          case 2
          then show ?case using Monoid.unit_type[OF assms(2)] unit by auto
        next
          case 3
          then show ?case using helper2[OF leq _ Monoid.add_mem[OF assms(2)]] by auto
        next
          case 4
          then show ?case using helper2[OF leq _ Monoid.unit_mem[OF assms(2)]] by auto
        next
          case 5
          then show ?case using Monoid.left_id[OF assms(2)] add unit by auto 
        next
          case 6
          then show ?case using Monoid.right_id[OF assms(2)] add unit by auto 
        next
          case 7
          then show ?case using Monoid.assoc[OF assms(2)] add unit by auto 
        qed
 

thm Monoid.left_id
    
ML\<open> parse_term_schematic @{context} "Monoid.add" |> Syntax.check_term @{context}\<close>

Class self \<Ztypecolon> Group_flat
    fixes "T" :: "set type"
    extends "Monoid T" 
    where
        "is_divisible T (self @ Monoid.add) (self @ Monoid.unit)"

Class self \<Ztypecolon> Group_nested
    fixes "T" :: "set type"
    contains 
        monoid \<Ztypecolon> "Monoid T"
    where
        "is_divisible T ((self @ monoid) @ Monoid.add) ((self @ monoid) @ Monoid.unit)"



(*

The other Stuff

*)

ML\<open>@{prop "True"}\<close>

ML\<open>@{term "Any"}\<close>

ML\<open>
    let 
        val test_class2 = "r \<Ztypecolon> myStructure  \"arg1\" and \"arg3\" \<Ztypecolon> \"Any\" and arg2 extends \"(A )\" and \"(B)\" where \
        \ field1 , \
        \ field2 field3 \<Ztypecolon> \"Any\", \
        \ field4 \<Ztypecolon> \"type (\<lambda>x . x = arg1 )\" "
        val test_class = "myStructure extends \"(self \<Ztypecolon> A )\"  where \
        \ field1 \<Ztypecolon> \"C\" "
        val test_class3 =  "r \<Ztypecolon> myStructure  \"arg1\" and \"arg3\" :: set  and arg2 \<Ztypecolon> Any where \
        \ field1 \<Ztypecolon> \"(type (\<lambda> x . x = arg3))\", \
        \ fiedl2 \<Ztypecolon> \"Any\""
        val test_class4= "self \<Ztypecolon> myStructure \"arg1\" :: \"set\" and \"arg2\" \<Ztypecolon> \"Any\" and arg3 where \
            \ field1 , \
            \ field2 field3 \<Ztypecolon> \"(type (\<lambda>x . x = arg1 ))\" , \
            \ field4 \<Ztypecolon> \"Any\" "
        val _ =     writeln test_class;
        fun parse p input = Scan.finite Token.stopper (Scan.error p) input
        fun filtered_input str =
            filter Token.is_proper (Token.explode (Thy_Header.get_keywords'
            @{context}) Position.none str)
        val rel_t = Const (@{const_name "rel"},@{typ "set => set => set => bool"})
        val type_of_t = Const (@{const_name "type_of"},dummyT)
        val eval_rel_t = Const (@{const_name "eval_rel"},dummyT)
        fun eval_record_t r = (eval_rel_t $ (rel_t $ r))
        fun field_to_sstring_t thy' name = Syntax.read_term thy' ("$" ^  name)
        fun field_to_access_t thy' r (name:string) = 
            eval_record_t r $ field_to_sstring_t thy' name

        val check = Syntax.check_term @{context} #> tap (Thm.cterm_of @{context});
        
        val parsed_class = test_class4  |> filtered_input |> parse structure_type_parser |> fst
        val dec = (declare_structure_type_flat_open |> uncurry |> uncurry |> uncurry) parsed_class [] @{context}
        val _ = dec |> Syntax.pretty_term @{context}|>Pretty.writeln 
        val dec_checked = check dec

    in dec
        (*field_to_sstring_t @{context} "abc"*)
        (*Thm.cterm_of @{context} dec*)

        (*)
        dec 
        |> Syntax.pretty_term @{context}
        |> Pretty.writeln;
        @{term "identity :: 'a \<Rightarrow> 'a"} $ @{term "x :: set"}
        |> Thm.cterm_of @{context}*)

        (*
        dec
        |> Syntax.check_term @{context}
        |> (Sign.certify_term @{theory} #> fst)
        |> Thm.cterm_of @{context}*)
        

    end

\<close>

ML\<open>val x = Variable.declare_term\<close>
ML\<open>Envir.norm_type\<close>
ML\<open>map_type_tfree (fn (n,s) => TFree (n^"s",s)) @{typ "'a \<Rightarrow> bool"}\<close>
ML\<open>Type\<close>
ML\<open>Proof_Context.read_term_pattern @{context} "type" \<close>
ML\<open>@{term "type_of"}\<close>
ML\<open>Term.add_tfrees\<close>
ML\<open>singleton (Variable.export_terms @{context} @{context}) @{term "type"}\<close>
ML\<open>Variable.polymorphic @{context} [@{term "type"}]\<close>
ML\<open>Type.unify\<close>
ML\<open>Sign.cert_term @{theory} @{term "type"}\<close>
ML\<open> @{term "\<lambda> (x::set) . True"}\<close>
ML\<open>@{term "type (\<lambda>r. r \<Ztypecolon> A \<and> eval_rel (rel r) $field1 \<Ztypecolon> C)"}\<close>


ML\<open>val t_pred =  @{term "\<lambda> (x::set) . True"}
    |> singleton (Variable.export_terms @{context} @{context})
    |> type_of \<close>
ML\<open>val t = @{term "type"}
    |> singleton (Variable.export_terms @{context} @{context})
    |> type_of \<close>

ML\<open>Sign.typ_unify @{theory} (t,t_pred --> (TVar (("?'bla",0),["HOL.type"]) )) (Vartab.empty,0) \<close>



ML\<open>
    val rtp = Proof_Context.read_term_pattern
    val rts = Proof_Context.read_term_schematic
    val rt = Syntax.read_term
    val pt = Syntax.parse_term
    val o = operation
\<close>

ML\<open>let
    val x = type_of
    val type_ = Const (@{const_name "type"},dummyT)
    val type__ = @{term "type"}
        |> singleton (Variable.export_terms @{context} @{context})
    (*
    val test = apply_unify type__ @{term "\<lambda> (x::set) . True"}
    fun eval_record_t r = apply_unify @{term "eval_rel"} ( @{term "rel"} $ r)
    fun field_to_sstring_t thy' name = Syntax.read_term thy' ("$" ^  name)
    fun field_to_access_t thy' r (name:string) = 
            eval_record_t r $ field_to_sstring_t thy' name
            
   val record = Free ("self", @{typ "set"})

    val test2 =  apply_unify
                ( apply_unify (@{term "type_of"}) ("field" |> field_to_access_t @{context} record))
                (Syntax.read_term @{context} "Any")
                *)
    val ctxt' = (Proof_Context.set_mode Proof_Context.mode_pattern @{context})
    val schematic_type = Syntax.read_term ctxt' "type"
    val schematic_t = Syntax.parse_term ctxt' "\<lambda> x . True"
    val test3 = (schematic_type $ schematic_t)
    in 
        (schematic_t,
        schematic_type)
        (*
        test3
         |> Syntax.check_term @{context} 
         |> Thm.cterm_of @{context})*)


         (*

        |> type_of
        |> Syntax.pretty_typ @{context}
        |> Pretty.writeln
        *)
        
    end\<close>

ML\<open>Symbol_Pos.is_identifier\<close>

ML\<open>x : term\<close>


ML\<open>val ctx = (Proof_Context.set_mode Proof_Context.mode_pattern @{context})
    val ctx' = Variable.add_fixes ["a::set","y"] ctx |> snd

    val rtp = Proof_Context.read_term_pattern; (*like set mode*)
    val rts = Proof_Context.read_term_schematic;
    fun rt ctxt = Syntax.read_term ctxt;
    val pt = Syntax.parse_term;

    val t = "\<lambda> x . x";
    val t2 = "\<lambda> y . a";
    val absvar = "a";
    
    val t2' = lambda (pt ctx "y") (pt ctx absvar);
    
    fun lambda_ rt1 rt2 = lambda (rt1 absvar) (rt2 t2);
    val check = Syntax.check_term @{context} #> tap (Thm.cterm_of @{context});

    val [absvar',t2'] = Syntax.check_terms ctx [pt ctx absvar,pt ctx t2];
    lambda absvar' t2' |> tap (Thm.cterm_of @{context});

    val a = pt ctx "\<lambda> x . a";
    val b = pt ctx' "\<lambda> x . a";


    
    (*((lambda_ (pt ctx) (pt ctx')) $ pt ctx t |> check,
    lambda_ (pt ctx) (pt ctx') |> check,
    lambda_ (pt ctx) (pt ctx)); 
    lambda_ (rt ctx) (rt ctx);
     lambda_ (pt ctx) (pt ctx) $ pt ctx t |> check
    ;*)
    
    \<close>

(*
ML\<open>Parse.term (Token.explode (Thy_Header.get_keywords' @{context}) Position.none "a list")\<close>
ML\<open>Parse.binding (Token.explode (Thy_Header.get_keywords' @{context}) Position.none "abc ") |> fst\<close>
ML\<open> soft_vars (Token.explode (Thy_Header.get_keywords' @{context}) Position.none "a : cd and b") |> fst\<close>
ML\<open>Parse.vars (Token.explode (Thy_Header.get_keywords' @{context}) Position.none "Tester :: \"'a\" and Tester2") |> fst\<close>
*)




end