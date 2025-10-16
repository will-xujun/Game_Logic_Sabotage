theory Util
  imports Complex_Main
    "HOL-Algebra.Algebra"
begin

\<comment>\<open>A non-locale implementation of LFP and GFP of functions based on FuncSet\<close>
definition ambient_inter :: "'a set \<Rightarrow> ('a set) set \<Rightarrow> 'a set" where
"ambient_inter U F = {x\<in>U. \<forall>A\<in>F. x\<in>A}"

lemma ambient_inter_compat : "F1\<subseteq> F2 \<Longrightarrow> ambient_inter U F2 \<subseteq> ambient_inter U F1"
  unfolding ambient_inter_def by auto

lemma ambient_inter_eq: "F1=F2 \<Longrightarrow> ambient_inter U F1 = ambient_inter U F2"
  by auto

definition fun_le :: "('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> bool" where
"fun_le f g = (\<forall>x. f x \<subseteq> g x)"

definition extension :: "'a set set \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "extension B = {f. \<forall>x. x \<notin> B \<longrightarrow> f x = undefined }"

definition compo :: "'a set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)"
  where "compo A g f = (\<lambda>x\<in>A. g (f x))"

lemma extension_union_extension: "f\<in> extension A\<Longrightarrow> g\<in> extension A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> extension A"
  by (simp add:extension_def)

lemma extension_inter_extension: "f\<in> extension A \<Longrightarrow> g\<in> extension A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> extension A"
  by (simp add:extension_def)

lemma extension_compo_extension: "f\<in> extension A\<Longrightarrow> g \<in> extension A \<Longrightarrow> compo A g f \<in> extension A"
  by (simp add:compo_def extension_def)

definition empty_func :: "'a set \<Rightarrow> 'a set" where
  "empty_func A = {}"

definition extension_fn :: "('a set \<Rightarrow> 'a set) set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) set" where
  "extension_fn W = {f. \<forall>x. x\<notin> W \<longrightarrow> f x = empty_func}"

definition carrier_of :: "'a set \<Rightarrow> ('a set\<Rightarrow> 'a set) set" where
  "carrier_of A = (Pow A\<rightarrow>Pow A) \<inter> extension (Pow A)"

lemma funcset_compo_funcset: "f\<in> Pow A \<rightarrow> Pow A \<Longrightarrow> g\<in> Pow A \<rightarrow> Pow A \<Longrightarrow> (compo (Pow A) g f) \<in> Pow A \<rightarrow> Pow A"
  by (simp add: Pi_iff compo_def)

lemma carrier_compo_carrier: "f\<in> carrier_of A \<Longrightarrow> g\<in> carrier_of A \<Longrightarrow> (compo (Pow A) g f) \<in> carrier_of A"
  using extension_compo_extension[of "f" "Pow A" "g"] funcset_compo_funcset[of "f" "A" "g"] carrier_of_def[of "A"] by auto 

lemma carrier_union_carrier: "f\<in> carrier_of A \<Longrightarrow> g\<in> carrier_of A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> carrier_of A"
  using extension_union_extension by (auto simp add:carrier_of_def)

lemma carrier_inter_carrier: "f\<in>carrier_of A \<Longrightarrow> g\<in> carrier_of A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> carrier_of A"
  using extension_inter_extension by (auto simp add:carrier_of_def)

definition mono_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "mono_of A = {f.  \<forall>x y. x\<subseteq>A \<and> y\<subseteq>A \<and> x \<subseteq> y \<longrightarrow> f x \<subseteq> f y}"

definition effective_fn_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "effective_fn_of A = carrier_of A \<inter> mono_of A "

lemma eff_compo_mono: "f\<in> carrier_of A \<inter> mono_of A \<Longrightarrow> g\<in> carrier_of A \<inter> mono_of A \<Longrightarrow> compo (Pow A) g f \<in> mono_of A"
  apply (simp add: mono_of_def compo_def carrier_of_def)
  by (simp add: Pi_iff)

lemma mono_union_mono: "f\<in> mono_of A \<Longrightarrow> g\<in> mono_of A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> mono_of A"
  apply (simp add:mono_of_def)
  by (simp add: sup.coboundedI1 sup.coboundedI2)

lemma mono_inter_mono: "f\<in> mono_of A \<Longrightarrow> g\<in> mono_of A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> mono_of A"
  apply (simp add:mono_of_def)
  by (simp add: inf.coboundedI1 inf.coboundedI2)

lemma eff_compo_eff: "f\<in> effective_fn_of A \<Longrightarrow> g\<in>effective_fn_of A \<Longrightarrow> compo (Pow A) g f \<in> effective_fn_of A"
  using eff_compo_mono carrier_compo_carrier apply (auto simp add:effective_fn_of_def)
  by force

lemma eff_union_eff: "f\<in> effective_fn_of A \<Longrightarrow> g\<in>effective_fn_of A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> effective_fn_of A"
  using carrier_union_carrier mono_union_mono by (auto simp add:effective_fn_of_def)

lemma eff_inter_eff: "f\<in> effective_fn_of A \<Longrightarrow> g\<in>effective_fn_of A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> effective_fn_of A"
  using carrier_inter_carrier mono_inter_mono by (auto simp add:effective_fn_of_def)

lemma compo_preserve_fun_le: "f1\<in> effective_fn_of A \<Longrightarrow> f2\<in> effective_fn_of A \<Longrightarrow> g1\<in> effective_fn_of A \<Longrightarrow> g2 \<in> effective_fn_of A \<Longrightarrow> fun_le f1 f2 \<Longrightarrow> fun_le g1 g2 \<Longrightarrow> fun_le (compo (Pow A) g1 f1) (compo (Pow A) g2 f2)"
  unfolding compo_def fun_le_def effective_fn_of_def carrier_of_def mono_of_def extension_def
  by (smt (verit, ccfv_threshold) Int_iff PiE Pow_iff mem_Collect_eq restrict_apply subsetD subsetI)


definition monotone_op_of ::"'a set \<Rightarrow> ( ('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set) ) set" where
  "monotone_op_of A = (effective_fn_of A \<rightarrow> effective_fn_of A)
  \<inter> {F. \<forall>g1\<in>effective_fn_of A. \<forall>g2\<in> effective_fn_of A. fun_le g1 g2 \<longrightarrow> fun_le (F g1) (F g2)}"

definition Lfp_family :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "Lfp_family A f = {\<phi>. \<phi>\<in> effective_fn_of A \<and> fun_le (f \<phi>) \<phi>}"


definition Lfp :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "Lfp w f a = (if a \<subseteq> w then ambient_inter w {\<phi> a | \<phi>. \<phi> \<in> Lfp_family w f} else undefined)"


definition max_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "max_of A x = (if x\<subseteq>A then A else undefined)"

lemma max_of_in_carrier : "max_of A \<in> carrier_of A"
  apply (auto simp add:max_of_def carrier_of_def)
proof show "max_of A \<in> extension (Pow A)"
    apply (simp add:extension_def)
  proof
    fix x show "\<not> x \<subseteq> A \<longrightarrow> max_of A x = undefined " by (auto simp add:max_of_def)
  qed
  show "extension (Pow A) \<subseteq> extension (Pow A) " by auto
qed

lemma max_of_in_funcset : "max_of A \<in> Pow A \<rightarrow> Pow A"
proof -
  from max_of_in_carrier have "max_of A \<in> (Pow A\<rightarrow>Pow A) \<inter> extension (Pow A)" by (simp add:carrier_of_def)
  then show ?thesis by auto
qed

lemma max_of_mono : "max_of A \<in> mono_of A" 
  by (auto simp add:mono_of_def max_of_def)

lemma max_of_effective [simp]: "max_of A \<in> effective_fn_of A"
  using max_of_mono[of "A"] max_of_in_carrier[of "A"] by (simp add:effective_fn_of_def)

lemma effective_op_effective : "f\<in> monotone_op_of A \<Longrightarrow> \<phi>\<in> effective_fn_of A \<Longrightarrow> f \<phi> \<in> effective_fn_of A "
  by (simp add: Pi_iff monotone_op_of_def)

lemma max_of_properties : 
  assumes "A \<noteq> {}"
    and P1: " f\<in> monotone_op_of A "
  shows "max_of A \<in> effective_fn_of A
\<and> (\<forall> xa. f (max_of A) xa \<subseteq> max_of A xa)"
  proof -
    have R1: "max_of A \<in> effective_fn_of A" using max_of_effective by auto
    have R2: "\<forall>xa. f (max_of A) xa \<subseteq> max_of A xa"
      apply (simp add:max_of_def)
    proof 
      fix xa show "(xa \<subseteq> A \<longrightarrow> f (max_of A) xa \<subseteq> A) \<and> (\<not> xa \<subseteq> A \<longrightarrow> f (max_of A) xa \<subseteq> undefined)"
      proof -
        have Q1:"xa \<subseteq> A \<longrightarrow> f (max_of A) xa \<subseteq> A"
        proof -
          have P2: "max_of A \<in> effective_fn_of A" by simp
          then have "f (max_of A) \<in> effective_fn_of A" using assms by (auto simp add:monotone_op_of_def)
          thus ?thesis by (auto simp add:effective_fn_of_def carrier_of_def)
        qed

        have Q2: "(\<not> xa \<subseteq> A \<longrightarrow> f (max_of A) xa = undefined)"
        proof assume a:"\<not> xa \<subseteq> A"
          have "f (max_of A)\<in> effective_fn_of A" using assms effective_op_effective[of "f" "A" "max_of A"] by simp 
          then have "f (max_of A) \<in> extension (Pow A)" by (auto simp add:effective_fn_of_def carrier_of_def)
          then show "f (max_of A) xa = undefined" using a by (simp add:effective_fn_of_def carrier_of_def extension_def)
        qed
        from Q1 Q2 show ?thesis by auto
      qed
    qed
    from R1 R2 show ?thesis by auto
  qed

lemma Lfp_family_nonempty :
  assumes "A \<noteq> {}"
    and P1: " f\<in> monotone_op_of A "
  shows " Lfp_family A f \<noteq> {}"
  apply (simp add:Lfp_family_def carrier_of_def extension_def fun_le_def)
proof
  show "max_of A \<in> effective_fn_of A \<and> (\<forall>x. f (max_of A) x \<subseteq> (max_of A) x)"
    using assms max_of_properties[of "A" "f"] by auto
qed

definition Gfp_family :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
"Gfp_family A f = {\<phi>. \<phi>\<in> effective_fn_of A \<and> fun_le \<phi> (f \<phi>)}"

definition Gfp :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "Gfp w f a = (if a\<subseteq>w then \<Union>{\<phi> a | \<phi>. \<phi>\<in> Gfp_family w f} else undefined)"

lemma Lfp_in_carrier : "Lfp w f \<in> carrier_of w"
  apply (auto simp add:carrier_of_def)
proof -
  fix x xa
  show "x \<subseteq> w \<Longrightarrow> xa \<in> Lfp w f x \<Longrightarrow> xa \<in> w" unfolding Lfp_def ambient_inter_def by auto

  show "Lfp w f \<in> extension (Pow w)" unfolding Lfp_def Lfp_family_def effective_fn_of_def carrier_of_def
    by (simp add:extension_def ambient_inter_def)
qed

lemma Lfp_eff: "Lfp w f \<in> effective_fn_of w"
  apply (simp add:effective_fn_of_def)
  apply (auto simp add:Lfp_in_carrier)
  unfolding Lfp_def mono_of_def apply auto
proof -
  fix x y z assume a0:"z \<in> ambient_inter w {\<phi> x |\<phi>. \<phi> \<in> Lfp_family w f}" 
    and a1:"x \<subseteq> w"
    and a2:"y \<subseteq> w"
    and a3:"x \<subseteq> y"
  have "\<And>\<phi>. \<phi>\<in> Lfp_family w f \<Longrightarrow> \<phi> x \<subseteq> \<phi> y" using a1 a2 a3 by (auto simp add:Lfp_family_def effective_fn_of_def mono_of_def)
  then show "z \<in> ambient_inter w {\<phi> y |\<phi>. \<phi> \<in> Lfp_family w f}" using a0
  by (smt (verit, ccfv_threshold) ambient_inter_def in_mono mem_Collect_eq)
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
