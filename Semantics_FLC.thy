theory Semantics_FLC
  imports 
  "Syntax"
  "Util"
  "Semantics"
begin
type_synonym FLC_var_type = "int"
type_synonym FLC_ground_type = "int"
type_synonym FLC_world_type = "FLC_ground_type world_type"
type_synonym FLC_sub_world_type = "FLC_ground_type sub_world_type"
type_synonym FLC_eff_fn_type = "FLC_sub_world_type \<Rightarrow> FLC_sub_world_type"

fun FLC_sem :: "RGL_ground_type Nbd_Struct \<Rightarrow> FLC_var_type val \<Rightarrow> FLC_var_type FLC_fml \<Rightarrow> FLC_eff_fn_type" where
  "FLC_sem N I FLC_Id = id_eff (World N)"
|   "FLC_sem N I (FLC_Atm_fml f) = con_eff (World N) ((PropInterp N) f)"
|   "FLC_sem N I (FLC_Not f) = con_eff (World N) (World N - ((PropInterp N) f))"
|   "FLC_sem N I (FLC_Var x) = I x"
|   "FLC_sem N I (FLC_Or f1 f2) = (\<lambda>x. (FLC_sem N I f1 x) \<union> FLC_sem N I f2 x)"
|   "FLC_sem N I (FLC_And f1 f2) = (\<lambda>x. (FLC_sem N I f1 x) \<inter> FLC_sem N I f2 x)"
|   "FLC_sem N I (FLC_Mod_Exist a f) = compo (Pow (World N)) (GameInterp N a) (FLC_sem N I f)"
|   "FLC_sem N I (FLC_Mod_Forall a f) = compo (Pow (World N)) (Util.dual_eff_fn (World N) (GameInterp N a)) (FLC_sem N I f)"
|   "FLC_sem N I (FLC_Chop f1 f2) = compo (Pow (World N)) (FLC_sem N I f1) (FLC_sem N I f2)"
|   "FLC_sem N I (FLC_mu x f) = Lfp (World N) (\<lambda>q. FLC_sem N (I(x:=q)) f)"
|   "FLC_sem N I (FLC_nu x f) = Gfp (World N) (\<lambda>q. FLC_sem N (I(x:=q)) f)"

definition FLC_fixpt_op where "FLC_fixpt_op N I x f q = FLC_sem N (I(x:=q)) f"

lemma FLC_mu_sem: "FLC_sem N I (FLC_mu x f) = Lfp (World N) (FLC_fixpt_op N I x f)" 
  unfolding FLC_fixpt_op_def by auto

lemma FLC_nu_sem: "FLC_sem N I (FLC_nu x f) = Gfp (World N) (FLC_fixpt_op N I x f)"
  unfolding FLC_fixpt_op_def by auto

lemma FLC_sem_wd: assumes "is_nbd_struct N" and "is_val N I"
  shows "FLC_sem N I f \<in> effective_fn_of (World N)"
  using assms
proof (induction f)
  case FLC_Id
  then show ?case
    using id_eff_eff by auto
next
  case (FLC_Atm_fml f1)
  then show ?case
  proof - from assms have "PropInterp N f1 \<subseteq> World N" unfolding is_nbd_struct_def by auto
    then show ?thesis using con_eff_eff by auto
  qed
next
  case (FLC_Not f1)
  then show ?case
  proof (simp)
    from assms have "PropInterp N f1 \<subseteq> World N" unfolding is_nbd_struct_def by auto
    then have "World N - PropInterp N f1 \<subseteq> World N" by auto
    then show "con_eff (World N) (World N - PropInterp N f1) \<in> effective_fn_of (World N)"
      using con_eff_eff[of "World N - PropInterp N f1"] by auto
  qed
next
  case (FLC_Var x)
  then show ?case
  proof (simp)
    from assms show "I x \<in> effective_fn_of (World N)" unfolding is_val_def by auto
  qed
next
  case (FLC_Or f1 f2)
  then show ?case
  proof (simp)
    from FLC_Or.IH assms 
    show "(\<lambda>a. FLC_sem N I f1 a \<union> FLC_sem N I f2 a) \<in> effective_fn_of (World N)"
      using eff_union_eff by auto
  qed
next
  case (FLC_And f1 f2)
  then show ?case
  proof (simp)
    from FLC_And.IH assms
    show "(\<lambda>a. FLC_sem N I f1 a \<inter> FLC_sem N I f2 a) \<in> effective_fn_of (World N)"
      using eff_inter_eff by auto
  qed
next
  case (FLC_Mod_Exist a f1)
  then show ?case 
  proof (simp)
    from assms have "GameInterp N a\<in> effective_fn_of (World N)" unfolding is_nbd_struct_def effective_fn_of_def
      by auto
    then show "compo (Pow (World N)) (GameInterp N a) (FLC_sem N I f1) \<in> effective_fn_of (World N)"
      using eff_compo_eff[of "FLC_sem N I f1""World N""GameInterp N a"] FLC_Mod_Exist.IH assms by auto
  qed
next
  case (FLC_Mod_Forall a f1)
  then show ?case
  proof (simp)
    from assms have "GameInterp N a\<in> effective_fn_of (World N)" unfolding is_nbd_struct_def effective_fn_of_def
      by auto
    then show "compo (Pow (World N)) (Util.dual_eff_fn (World N) (GameInterp N a)) (FLC_sem N I f1) \<in> effective_fn_of (World N)"
      using eff_compo_eff[of "FLC_sem N I f1""World N"] FLC_Mod_Forall.IH assms eff_dual_eff[of "GameInterp N a""World N"]
      by auto
  qed
next
  case (FLC_Chop f1 f2)
  then show ?case using eff_compo_eff by auto
next
  case (FLC_mu x f)
  then show ?case using Lfp_eff[of "World N""\<lambda>q. FLC_sem N (I(x := q)) f"] by auto
next
  case (FLC_nu x1 f)
  then show ?case sorry
qed

end