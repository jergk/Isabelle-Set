theory Examples
imports 
    Isabelle_Set.Record_Package
    Isabelle_Set.SStrings
begin

(*Simple parents*)
StructureType self \<Ztypecolon> myStructure1

StructureType self \<Ztypecolon> myStructure2
    fixes arg2 \<Ztypecolon> "Any" and arg3 


(*everything*)
StructureType self \<Ztypecolon> myStructure3 
    fixes "arg1":: set and arg2 \<Ztypecolon> "Any" and arg3 
    extends "myStructure1" and "myStructure2 arg2 arg3" 
    contains
        "$field1" ,
        "$field2" "$field3" \<Ztypecolon> "Element (self @ $field1 )",
        "$field4" \<Ztypecolon> "(type (\<lambda>x . x = arg1 ))",
        "$field5" \<Ztypecolon> "Any"
print_theorems

definition "instance \<equiv> {| $field1 := {} ,
         $field2 := {} ,
         $field3 := {} ,
         $field4 := {} ,
         $field5 := {} |}"


(*simple algebraic with flat and nexted hierarchies*)

Class self \<Ztypecolon> Monoid 
    fixes "T" :: "set type"
    contains
        "$add" \<Ztypecolon> "(T \<rightarrow> T \<rightarrow> T)",
        "$unit" \<Ztypecolon> "T"
    where
        left_id : "is_left_identity T (self @ $add) (self @ $unit)" and 
        right_id: "is_right_identity T (self @ $add) (self @ $unit)" and 
        assoc: "is_associative T (self @ $add)"
    print_theorems

Class self \<Ztypecolon> Group_flat
    fixes "T" :: "set type"
    extends "Monoid T" 
    where
        "is_divisible T (self @ $add) (self @ $unit)"

Class self \<Ztypecolon> Group_nested
    fixes "T" :: "set type"
    contains 
        "$monoid" \<Ztypecolon> "Monoid T"
    where
        "is_divisible T ((self @ $monoid) @ $add) ((self @ $monoid) @ $unit)"


(* 
    
Abstractng over labels

*)
Class self \<Ztypecolon> Monoid_labeled
    fixes "T" :: "set type" and "op_l" "unit_l"
    contains
        "op_l" \<Ztypecolon> "(T \<rightarrow> T \<rightarrow> T)",
        "unit_l" \<Ztypecolon> "T"
    where
        left_id : "is_left_identity T (self @ op_l) (self @ unit_l)" and 
        right_id: "is_right_identity T (self @ op_l) (self @ unit_l)" and 
        assoc: "is_associative T (self @ op_l)"
    print_theorems

(*we can state generic functions*)
lemma left_id2: "m \<Ztypecolon> Monoid_labeled T op_l unit_l \<Longrightarrow> x \<Ztypecolon> T \<Longrightarrow> ((m@op_l)`(m@unit_l)`x = x)" 
    using Monoid_labeled.left_id[of m T op_l unit_l] 
       unfolding is_left_identity_def
    by auto

(*
we can bind explicit notation
For Typeclasses
the m argument would be implicit and inferred 
and would add a Monoid_labeled T $add $zero constraint
*)
definition add where
    "add m x y \<equiv> (m@$add)`x`y"

definition zero where
    "zero m \<equiv> m@$zero"


lemma left_id3: "m \<Ztypecolon> (Monoid_labeled T $add $zero) \<Longrightarrow> x \<Ztypecolon> T \<Longrightarrow> add m (zero m) x = x "
    unfolding add_def zero_def
    using left_id2[of m T "$add" "$zero" x] by simp

(*we can have multiple different ancestors of the same record type useful to define Ring like structures for example*)
Class self \<Ztypecolon> AddMul
     fixes "T" :: "set type"
     extends "Monoid_labeled T $add $zero" and "Monoid_labeled T $mul $one"
print_theorems

end