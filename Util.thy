theory Util
  imports Complex_Main
    "HOL-Algebra.Algebra"
begin

\<comment>\<open>A non-locale implementation of LFP and GFP of functions based on FuncSet\<close>
definition ambient_inter :: "'a set \<Rightarrow> ('a set) set \<Rightarrow> 'a set" where
"ambient_inter U F = {x\<in>U. \<forall>A\<in>F. x\<in>A}"

definition fun_le :: "('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> bool" where
"fun_le f g = (\<forall>x. f x \<subseteq> g x)"

definition extension :: "'a set set \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "extension B = {f. \<forall>x. x \<notin> B \<longrightarrow> f x = {} }"

definition empty_func :: "'a set \<Rightarrow> 'a set" where
  "empty_func A = {}"

definition extension_fn :: "('a set \<Rightarrow> 'a set) set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) set" where
  "extension_fn W = {f. \<forall>x. x\<notin> W \<longrightarrow> f x = empty_func}"

definition carrier_of :: "'a set \<Rightarrow> ('a set\<Rightarrow> 'a set) set" where
  "carrier_of A = (Pow A\<rightarrow>Pow A) \<inter> extension (Pow A)"

definition mono_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "mono_of A = {f.  \<forall>x y. x\<subseteq>A \<and> y\<subseteq>A \<and> x \<subseteq> y \<longrightarrow> f x \<subseteq> f y}"

definition effective_fn_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "effective_fn_of A = (Pow A\<rightarrow>Pow A) \<inter> mono_of A"

definition monotone_op_of ::"'a set \<Rightarrow> ( ('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set) ) set" where
  "monotone_op_of A = (effective_fn_of A \<rightarrow> effective_fn_of A)
  \<inter> {F. \<forall>g1\<in>effective_fn_of A. \<forall>g2\<in> effective_fn_of A. fun_le g1 g2 \<longrightarrow> fun_le (F g1) (F g2)}"

definition Lfp_family :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "Lfp_family A f = {\<phi>. \<phi>\<in> carrier_of A \<and> fun_le (f \<phi>) \<phi>}"

definition Lfp :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "Lfp w f a = ambient_inter w {\<phi> a | \<phi>. \<phi> \<in> Lfp_family w f}"

definition max_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "max_of A x = (if x\<subseteq>A then A else {})"

lemma max_of_in_carrier : "max_of A \<in> carrier_of A"
  apply (auto simp add:max_of_def carrier_of_def)
proof show "max_of A \<in> extension (Pow A)"
    apply (simp add:extension_def)
  proof
    fix x show "\<not> x \<subseteq> A \<longrightarrow> max_of A x = {} " by (auto simp add:max_of_def)
  qed
  show "extension (Pow A) \<subseteq> extension (Pow A) " by auto
qed

lemma max_of_in_funcset : "max_of A \<in> Pow A \<rightarrow> Pow A"
proof -
  from max_of_in_carrier have "max_of A \<in> (Pow A\<rightarrow>Pow A) \<inter> extension (Pow A)" by (simp add:carrier_of_def)
  then show ?thesis by auto
qed

lemma max_of_mono : "max_of A \<in> mono_of A"

lemma carrier_op_funcset : "f\<in> monotone_op_of A \<Longrightarrow> \<phi>\<in> effective_fn_of A \<Longrightarrow> f \<phi> \<in> (Pow A\<rightarrow> Pow A) "
  by (simp add: Pi_iff effective_fn_of_def monotone_op_of_def)

lemma max_of_properties : 
  assumes "A \<noteq> {}"
    and P1: " f\<in> monotone_op_of A "
  shows "max_of A \<in> Pow A \<rightarrow> Pow A \<and> (\<forall>xa. xa \<subseteq> A \<or> max_of A xa = {})
\<and> (\<forall> xa. f (max_of A) xa \<subseteq> max_of A xa)"
  proof -
    have R1: "max_of A \<in> Pow A \<rightarrow> Pow A" by (auto simp add: max_of_def)
    have R2: "\<forall>xa. xa \<subseteq> A \<or> max_of A xa = {}" by (auto simp add: max_of_def)
    have R3: "\<forall>xa. f (max_of A) xa \<subseteq> max_of A xa"
      apply (simp add:max_of_def)
    proof 
      fix xa show "(xa \<subseteq> A \<longrightarrow> f (max_of A) xa \<subseteq> A) \<and> (\<not> xa \<subseteq> A \<longrightarrow> f (max_of A) xa = {})"
      proof -
        have Q1:"xa \<subseteq> A \<longrightarrow> f (max_of A) xa \<subseteq> A"
        proof -
          have P2: "max_of A \<in> Pow A \<rightarrow> Pow A" by (rule max_of_in_funcset[where A="A"])
          then have "f (max_of A) \<in> Pow A \<rightarrow> Pow A"
          proof -
            have "f\<in> monotone_op_of A \<Longrightarrow> max_of A \<in> Pow A \<rightarrow> Pow A \<Longrightarrow> f (max_of A) \<in> Pow A\<rightarrow> Pow A"
              by (rule carrier_op_funcset[of "f" "A" "max_of A"]) (auto)
            then show "f (max_of A) \<in> Pow A\<rightarrow> Pow A" using assms P2 by auto
          qed
          thus ?thesis by auto
        qed

        have Q2: "(\<not> xa \<subseteq> A \<longrightarrow> f (max_of A) xa = {})"
        proof -
          have P2: "max_of A \<in> Pow A \<rightarrow> Pow A" by (rule max_of_in_funcset[of "A"])
          from P1 P2 have "f (max_of A) \<in> extension (Pow A)" using carrier_op_ext[of "f" "A" "max_of A"] by auto
          thus "\<not> xa \<subseteq> A \<longrightarrow> f (max_of A) xa = {}" by (auto simp add:extension_def)
        qed
        from Q1 Q2 show ?thesis by rule
      qed
    qed
    from R1 R2 R3 show ?thesis by auto
  qed

lemma Lfp_family_nonempty :
  assumes "A \<noteq> {}"
    and P1: " f\<in> monotone_op_of A "
  shows " Lfp_family A f \<noteq> {}"
  apply (simp add:Lfp_family_def carrier_of_def extension_def fun_le_def)
proof
  show "max_of A \<in> Pow A \<rightarrow> Pow A \<and> (\<forall>xa. xa \<subseteq> A \<or> (max_of A) xa = {}) \<and> (\<forall>xa. f (max_of A) xa \<subseteq> (max_of A) xa)"
    using assms max_of_properties[of "A" "f"] by auto
qed

definition Gfp_family :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
"Gfp_family A f = {\<phi>. \<phi>\<in> carrier_of A \<and> fun_le \<phi> (f \<phi>)}"

definition Gfp :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "Gfp w f a = \<Union>{\<phi> a | \<phi>. \<phi>\<in> Gfp_family w f}"

lemma Lfp_in_carrier : 
  assumes "f\<in> monotone_op_of w"
  and "w\<noteq> {}"
shows "Lfp w f a \<subseteq> w"
proof -
  consider (In) "a \<subseteq> w" | (NotIn) "\<not> a\<subseteq> w" by auto
  then have ?thesis
  proof cases
    case In
    then have P0: "\<And>\<phi>. \<phi> \<in> Pow w \<rightarrow> Pow w \<Longrightarrow> \<phi> a\<subseteq>w" by auto
    then show "Lfp w f a \<subseteq> w"
      apply (simp add:Lfp_def Lfp_family_def carrier_of_def)
    proof
      fix x
      assume P1: " x\<in> \<Inter> {\<phi> a |\<phi>. \<phi> \<in> Pow w \<rightarrow> Pow w \<and> \<phi> \<in> extension (Pow w) \<and> fun_le (f \<phi>) \<phi>}"
      show "x \<in> w"
      proof -
        from P1 have P2:"\<And>\<phi>.  \<phi> \<in> Pow w \<rightarrow> Pow w \<and> \<phi> \<in> extension (Pow w) \<and> fun_le (f \<phi>) \<phi> \<Longrightarrow> x \<in> \<phi> a" by auto
        have P3: "(\<forall>xa. f (max_of w) xa \<subseteq> max_of w xa)" using max_of_properties[of "w" "f"] assms by auto
        from P0[of "max_of w"] max_of_properties[of "w" "f"] assms have P4: "max_of w a \<subseteq> w" by auto
        have P5: "x \<in> max_of w a" using max_of_properties[of "w" "f"] P2[of "max_of w"] assms by (auto simp add:extension_def fun_le_def)
        thus ?thesis using P4  In assms by auto
      qed
    qed
  next
    case NotIn
    show "Lfp w f a \<subseteq> w" apply (simp add:Lfp_def Lfp_family_def)
    proof - 
      have "\<And>\<phi>. \<phi> \<in> carrier_of w \<and> fun_le (f \<phi>) \<phi> \<Longrightarrow> \<phi> a = {}" using NotIn by (auto simp add:carrier_of_def extension_def)
      then have "\<Inter> {\<phi> a |\<phi>. \<phi> \<in> carrier_of w \<and> fun_le (f \<phi>) \<phi>} = {}"
      by (smt (verit) Inter_iff Lfp_family_def Lfp_family_nonempty assms(1,2) empty_iff equals0I mem_Collect_eq)
    then show "\<Inter> {\<phi> a |\<phi>. \<phi> \<in> carrier_of w \<and> fun_le (f \<phi>) \<phi>} \<subseteq> w" by simp
    qed
  qed
  thus ?thesis by simp
qed

\<comment>\<open>locale-based implementation\<close>
locale fun_comp_lattice =
  fixes A :: "'a set"
begin

definition const_A :: "'a set \<Rightarrow> 'a set" where
  "const_A = restrict (\<lambda>x. A) (Pow A)"

lemma max_exists : "greatest \<lparr>carrier = (Pow A \<rightarrow> Pow A) \<inter> (extensional (Pow A)), eq = (=), le = fun_le\<rparr> 
  const_A ((Pow A \<rightarrow> Pow A) \<inter> extensional (Pow A))"
  by (auto simp add: const_A_def greatest_def fun_le_def extensional_def)
end

sublocale fun_comp_lattice \<subseteq> equivalence "\<lparr> carrier = Pow A \<rightarrow> Pow A, eq = (=) \<rparr>"
  by (rule equivalenceI) (auto)

lemma weak_partial_orderI:
  fixes P :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and E :: "'a set" and R:: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes refl: "\<And>x.     \<lbrakk> x \<in> E \<rbrakk> \<Longrightarrow> P x x"
    and    sym: "\<And>x y.   \<lbrakk> x \<in> E; y \<in> E \<rbrakk> \<Longrightarrow> P x y \<Longrightarrow> P y x"
    and  trans: "\<And>x y z. \<lbrakk> x \<in> E; y \<in> E; z \<in> E \<rbrakk> \<Longrightarrow> P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
    and le_refl: "\<And>x.  \<lbrakk> x \<in> E \<rbrakk> \<Longrightarrow> R x x"
    and weak_le_antisym : "\<And> x y. \<lbrakk> R x y; R y x; x\<in>E; y\<in>E \<rbrakk> \<Longrightarrow> P x y"
    and le_trans: "\<And> x y z. \<lbrakk> R x y; R y z; x \<in>E ; y\<in>E;z\<in>E \<rbrakk> \<Longrightarrow> R x z"
    and le_cong: "\<And>x y z w. \<lbrakk> P x y; P z w; x\<in>E; y\<in>E; z\<in>E; w\<in>E \<rbrakk> \<Longrightarrow> (R x z \<longleftrightarrow> R y w)"
  shows "weak_partial_order \<lparr> carrier = E, eq = P, le=R \<rparr>"
  unfolding weak_partial_order_def using assms
  by (smt (verit) eq_object.select_convs(1) equivalence_def gorder.select_convs(1) partial_object.select_convs(1)
      weak_partial_order_axioms_def)

lemma partial_orderI:
  fixes E :: "'a set" and R:: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    assumes le_refl: "\<And>x.  \<lbrakk> x \<in> E \<rbrakk> \<Longrightarrow> R x x"
    and weak_le_antisym : "\<And> x y. \<lbrakk> R x y; R y x; x\<in>E; y\<in>E \<rbrakk> \<Longrightarrow> x=y"
    and le_trans: "\<And> x y z. \<lbrakk> R x y; R y z; x \<in>E ; y\<in>E;z\<in>E \<rbrakk> \<Longrightarrow> R x z"
    and le_cong: "\<And>x y z w. \<lbrakk> x=y; z=w; x\<in>E; y\<in>E; z\<in>E; w\<in>E \<rbrakk> \<Longrightarrow> (R x z \<longleftrightarrow> R y w)"
  shows "partial_order \<lparr> carrier = E, eq = (=), le=R \<rparr>"
  unfolding partial_order_def using assms
  by (smt (verit, best) eq_object.select_convs(1) partial_order_axioms.intro partial_order_def
      weak_partial_orderI)

sublocale fun_comp_lattice \<subseteq> partial_order "\<lparr> carrier = (Pow A \<rightarrow> Pow A) \<inter> extensional (Pow A), 
  eq = (=), le=fun_le \<rparr>"
  apply (rule partial_orderI)
  apply (auto simp add:fun_le_def)
proof -
  fix x and y show " \<forall>xa. x xa \<subseteq> y xa \<Longrightarrow> \<forall>xa. y xa \<subseteq> x xa \<Longrightarrow> x \<in> Pow A \<rightarrow> Pow A \<Longrightarrow> y \<in> Pow A \<rightarrow> Pow A \<Longrightarrow> x = y"
  proof
    fix z show " \<forall>xa. x xa \<subseteq> y xa \<Longrightarrow> \<forall>xa. y xa \<subseteq> x xa \<Longrightarrow> x \<in> Pow A \<rightarrow> Pow A \<Longrightarrow> y \<in> Pow A \<rightarrow> Pow A \<Longrightarrow> x z = y z"
      by auto
  qed
qed

sublocale fun_comp_lattice \<subseteq> complete_lattice "\<lparr> carrier = (Pow A \<rightarrow> Pow A) \<inter> extensional (Pow A), eq = (=), le=fun_le \<rparr>"
  apply (rule complete_lattice_criterion1)
  unfolding greatest_def
proof - 
  show "\<forall>f\<in> Pow A \<rightarrow> Pow A. fun_le f const_A"
    sorry
qed




end
