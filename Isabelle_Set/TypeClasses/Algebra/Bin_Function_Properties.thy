theory Bin_Function_Properties
imports 
    Isabelle_Set.TSBasics
    HOTG.HOTG_Functions_Evaluation
begin
    (* Properties used by Compound Typeclasses *)
definition "is_left_identity (A::set type) (op::set) \<iota> \<equiv> (\<forall>\<sigma> : A. (op` \<iota>` \<sigma>) = \<sigma>)"
definition "is_right_identity (A::set type) (op::set) \<iota> \<equiv> (\<forall>\<sigma> : A. (op` \<sigma>` \<iota>) = \<sigma>)" 
definition "is_associative (A::set type) (op::set) \<equiv> (\<forall>\<sigma>: A . \<forall> \<tau>:A . \<forall> \<gamma>:A. 
        op` \<sigma>` (op` \<tau>` \<gamma>) = op` (op` \<sigma>` \<tau>)` \<gamma>)" 
definition "is_divisible (A::set type) (op::set) \<iota> \<equiv> (\<forall> \<sigma> : A . (\<exists>\<sigma>' :A . op` \<sigma>'` \<sigma> = \<iota>))"
definition "is_commutative (A::set type) (op::set) \<equiv> (\<forall>\<sigma> :A . \<forall> \<tau>:A . (op` \<sigma>` \<tau>) = (op`\<tau>` \<sigma>))" 

definition "is_distributive (A::set type) (add::set) (mul::set) \<equiv> (\<forall> \<sigma> : A . \<forall> \<tau> : A . \<forall> \<gamma> : A . 
    mul`\<sigma>`(add`\<tau>`\<gamma>) = add`(mul`\<sigma>`\<tau>)`(mul`\<sigma>`\<gamma>))"

lemma is_divisibleE[elim!,dest]: 
    assumes "is_divisible A op \<iota>" and "\<sigma> \<Ztypecolon> A"
    obtains \<sigma>' where "op` \<sigma>'` \<sigma> = \<iota>" and "\<sigma>' \<Ztypecolon> A "
    using assms unfolding is_divisible_def
    by auto

lemma is_left_identityE[elim!,dest]: 
    assumes "is_left_identity A op \<iota>" and "\<sigma> \<Ztypecolon> A"
    shows "(op` \<iota>` \<sigma>) = \<sigma>"
    using assms unfolding is_left_identity_def
    by auto


lemma is_right_identityE[elim!,dest]: 
    assumes "is_right_identity A op \<iota>" and "\<sigma> \<Ztypecolon> A"
    shows "(op` \<sigma>` \<iota>) = \<sigma>"
    using assms unfolding is_right_identity_def
    by auto

lemma is_associativeE[elim!,dest]: 
    assumes "is_associative A op" and "\<sigma> \<Ztypecolon> A"  "\<tau> \<Ztypecolon> A"  "\<gamma> \<Ztypecolon> A"
    shows "op` \<sigma>` (op` \<tau>` \<gamma>) = op` (op` \<sigma>` \<tau>)` \<gamma>"
    using assms unfolding is_associative_def
    by auto

lemma is_commutativeE[elim!,dest]: 
    assumes "is_commutative A op" and "\<sigma> \<Ztypecolon> A"  "\<tau> \<Ztypecolon> A" 
    shows "(op` \<sigma>` \<tau>) = (op`\<tau>` \<sigma>)"
    using assms unfolding is_commutative_def
    by auto

end