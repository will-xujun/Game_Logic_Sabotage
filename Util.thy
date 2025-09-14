theory Util
  imports Complex_Main
begin

lemma lfp_preserve:
  fixes W:: "'a set"
    and f:: "'a set \<Rightarrow> 'a set"
  assumes "\<forall>A. f A \<subseteq> W"
  shows "lfp f \<subseteq> W"
  apply (simp add:lfp_def)
proof - 
  show " \<Inter> {u. f u \<subseteq> u} \<subseteq> W " using assms by blast
qed

end