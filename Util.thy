theory Util
  imports Complex_Main
    "HOL-Algebra.Algebra"
begin

definition fun_le :: "('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> bool" where
"fun_le f g = (\<forall>x. f x \<subseteq> g x)"

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
end
