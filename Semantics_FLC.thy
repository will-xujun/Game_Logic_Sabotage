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
|   "FLC_sem N I (FLC_Or f1 f2) = eff_fn_union (FLC_sem N I f1) (FLC_sem N I f2)"
|   "FLC_sem N I (FLC_And f1 f2) = eff_fn_inter (FLC_sem N I f1) (FLC_sem N I f2)"
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

(* FLC interpretation of any term is an effective function. *)
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
  proof (simp add:eff_fn_union_def)
    from FLC_Or.IH assms 
    show "(\<lambda>a. FLC_sem N I f1 a \<union> FLC_sem N I f2 a) \<in> effective_fn_of (World N)"
      using eff_union_eff by auto
  qed
next
  case (FLC_And f1 f2)
  then show ?case
  proof (simp add:eff_fn_inter_def)
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

lemma FLC_fixpt_op_id_monotone:
  "FLC_fixpt_op N I x (FLC_Id)\<in> monotone_op_of (World N)"
  unfolding FLC_fixpt_op_def monotone_op_of_def
  apply auto unfolding fun_le_def apply auto
  using id_eff_eff by auto

lemma FLC_fixpt_op_var_monotone:
  assumes "is_val N I"
  shows "FLC_fixpt_op N I x (FLC_Var y)\<in> monotone_op_of (World N)"
proof (cases "x=y")
  case True
  then show ?thesis unfolding FLC_fixpt_op_def monotone_op_of_def by auto
next
  case False
  then show ?thesis unfolding FLC_fixpt_op_def monotone_op_of_def fun_le_def apply auto
    using assms unfolding is_val_def by auto
qed


(* Lemma 4.1. FLC fixpt operator is monotone. *)
lemma FLC_fixpt_op_monotone:
  assumes "is_nbd_struct N" and "is_val N I"
  shows "FLC_fixpt_op N I x f \<in> monotone_op_of (World N)"
  using assms
proof (induction f)
  case FLC_Id
  then show ?case using FLC_fixpt_op_id_monotone by auto
next
  case (FLC_Atm_fml x)
  then show ?case unfolding FLC_fixpt_op_def monotone_op_of_def fun_le_def apply auto
    using con_eff_eff assms unfolding is_nbd_struct_def by auto
next
  case (FLC_Not x)
  then show ?case unfolding FLC_fixpt_op_def monotone_op_of_def fun_le_def apply auto
    using con_eff_eff assms unfolding is_nbd_struct_def using Diff_subset by blast
next
  case (FLC_Var y)
  then show ?case using FLC_fixpt_op_var_monotone  by auto
next
  case (FLC_Or f1 f2)
  then show ?case unfolding FLC_fixpt_op_def apply simp
  proof -
    have "(\<lambda>a. eff_fn_union (FLC_sem N (I(x := a)) f1) (FLC_sem N (I(x := a)) f2)) = op_union (FLC_fixpt_op N I x f1) (FLC_fixpt_op N I x f2)"
      unfolding FLC_fixpt_op_def op_union_def by auto
    then show "(\<lambda>a. eff_fn_union (FLC_sem N (I(x := a)) f1) (FLC_sem N (I(x := a)) f2)) \<in> monotone_op_of (World N)"
      using FLC_Or.IH assms monotone_op_union_monotone by auto
  qed
next
  case (FLC_And f1 f2)
  then show ?case unfolding FLC_fixpt_op_def apply simp
  proof -
    have "(\<lambda>a. eff_fn_inter (FLC_sem N (I(x := a)) f1) (FLC_sem N (I(x := a)) f2)) = op_inter (FLC_fixpt_op N I x f1) (FLC_fixpt_op N I x f2)"
      unfolding FLC_fixpt_op_def op_inter_def by auto
    then show "(\<lambda>a. eff_fn_inter (FLC_sem N (I(x := a)) f1) (FLC_sem N (I(x := a)) f2)) \<in> monotone_op_of (World N)"
      using FLC_And.IH assms monotone_op_inter_monotone by auto
  qed  
next
  case (FLC_Mod_Exist y f)
  then show ?case
  proof (cases "x=y")
    case True
    then show ?thesis unfolding FLC_fixpt_op_def monotone_op_of_def apply (simp add:True)
    proof
      show "(\<lambda>a. compo (Pow (World N)) (GameInterp N y) (FLC_sem N (I(y := a)) f)) \<in> effective_fn_of (World N) \<rightarrow> effective_fn_of (World N)"
        apply rule
      proof - fix x1 assume ass:"x1 \<in> effective_fn_of (World N)"
        show "compo (Pow (World N)) (GameInterp N y) (FLC_sem N (I(y := x1)) f) \<in> effective_fn_of (World N)"
          using assms effective_fn_of_def FLC_sem_wd[of "N""I(y:=x1)""f"] val_modify_val[of "x1""N""I""y"] ass eff_compo_eff[of "FLC_sem N (I(y := x1)) f""World N""GameInterp N y"]
          unfolding is_nbd_struct_def by blast
      qed
    next
      show "\<forall>g1\<in>effective_fn_of (World N).
       \<forall>g2\<in>effective_fn_of (World N).
          fun_le g1 g2 \<longrightarrow>
          fun_le (compo (Pow (World N)) (GameInterp N y) (FLC_sem N (I(y := g1)) f)) (compo (Pow (World N)) (GameInterp N y) (FLC_sem N (I(y := g2)) f))"
        apply rule apply rule
      proof fix g1 g2 assume a1:"g1 \<in> effective_fn_of (World N)" and a2:"g2 \<in> effective_fn_of (World N)" and a3:"fun_le g1 g2"
        show "fun_le (compo (Pow (World N)) (GameInterp N y) (FLC_sem N (I(y := g1)) f)) (compo (Pow (World N)) (GameInterp N y) (FLC_sem N (I(y := g2)) f))"
        proof -
          from True FLC_Mod_Exist.IH assms a1 a2 a3 have b1:"fun_le (FLC_sem N (I(y := g1)) f) (FLC_sem N (I(y := g2)) f)" 
            unfolding monotone_op_of_def FLC_fixpt_op_def
            by auto
          have b2:"fun_le (GameInterp N y) (GameInterp N y)" unfolding fun_le_def by auto
          have b3:"GameInterp N y \<in> effective_fn_of (World N)" using assms unfolding is_nbd_struct_def effective_fn_of_def by auto
          from b1 b2 b3 compo_preserve_fun_le FLC_sem_wd val_modify_val a1 a2 assms show ?thesis by metis
        qed
      qed
    qed
  next
    case False
    then show ?thesis unfolding FLC_fixpt_op_def monotone_op_of_def apply simp
    proof assume "x\<noteq>y"
      show "(\<lambda>a. compo (Pow (World N)) (GameInterp N y) (FLC_sem N (I(x := a)) f)) \<in> effective_fn_of (World N) \<rightarrow> effective_fn_of (World N)"
        apply rule 
        using eff_compo_eff assms unfolding is_nbd_struct_def using val_modify_val assms(1) FLC_sem_wd 
        unfolding effective_fn_of_def by metis
    next
      assume "x\<noteq>y"
      show "\<forall>g1\<in>effective_fn_of (World N).
       \<forall>g2\<in>effective_fn_of (World N).
          fun_le g1 g2 \<longrightarrow>
          fun_le (compo (Pow (World N)) (GameInterp N y) (FLC_sem N (I(x := g1)) f)) (compo (Pow (World N)) (GameInterp N y) (FLC_sem N (I(x := g2)) f))"
        apply rule apply rule
      proof fix g1 g2 assume a1:"g1 \<in> effective_fn_of (World N)" and a2:"g2 \<in> effective_fn_of (World N)" and a3:"fun_le g1 g2"
        show "fun_le (compo (Pow (World N)) (GameInterp N y) (FLC_sem N (I(x := g1)) f)) (compo (Pow (World N)) (GameInterp N y) (FLC_sem N (I(x := g2)) f))"
        proof -
          from False FLC_Mod_Exist.IH assms a1 a2 a3 have b1:"fun_le (FLC_sem N (I(x := g1)) f) (FLC_sem N (I(x := g2)) f)" 
            unfolding monotone_op_of_def FLC_fixpt_op_def
            by auto
          have b2:"fun_le (GameInterp N y) (GameInterp N y)" unfolding fun_le_def by auto
          have b3:"GameInterp N y \<in> effective_fn_of (World N)" using assms unfolding is_nbd_struct_def effective_fn_of_def by auto
          from b1 b2 b3 compo_preserve_fun_le FLC_sem_wd val_modify_val a1 a2 assms show ?thesis by metis
        qed
      qed
    qed
  qed
next
  case (FLC_Mod_Forall y f)
  then show ?case
    unfolding FLC_fixpt_op_def monotone_op_of_def apply simp apply rule
  proof fix xa show "xa \<in> effective_fn_of (World N) \<Longrightarrow>
          compo (Pow (World N)) (Util.dual_eff_fn (World N) (GameInterp N y)) (FLC_sem N (I(x := xa)) f) \<in> effective_fn_of (World N)"
      using assms val_modify_val FLC_sem_wd
      by (metis FLC_sem.simps(8))
  next
    show "\<forall>g1\<in>effective_fn_of (World N).
       \<forall>g2\<in>effective_fn_of (World N).
          fun_le g1 g2 \<longrightarrow>
          fun_le (compo (Pow (World N)) (Util.dual_eff_fn (World N) (GameInterp N y)) (FLC_sem N (I(x := g1)) f))
           (compo (Pow (World N)) (Util.dual_eff_fn (World N) (GameInterp N y)) (FLC_sem N (I(x := g2)) f))"
      apply rule apply rule apply rule
    proof - fix g1 g2 assume a1:"g1 \<in> effective_fn_of (World N)" and a2:"g2 \<in> effective_fn_of (World N)"
    and a3:"fun_le g1 g2" 
      from FLC_Mod_Forall.IH a3 a1 a2 assms have a4:"fun_le (FLC_sem N (I(x := g1)) f)(FLC_sem N (I(x := g2)) f)" 
        unfolding monotone_op_of_def FLC_fixpt_op_def by auto
      then show "fun_le (compo (Pow (World N)) (Util.dual_eff_fn (World N) (GameInterp N y)) (FLC_sem N (I(x := g1)) f))
        (compo (Pow (World N)) (Util.dual_eff_fn (World N) (GameInterp N y)) (FLC_sem N (I(x := g2)) f))"
        using a4 compo_preserve_fun_le eff_dual_eff assms unfolding is_nbd_struct_def
      by (metis (no_types, lifting) FLC_sem_wd a1 a2 assms(1) effective_fn_of_def fun_le_def set_eq_subset val_modify_val)
    qed
  qed
next
  case (FLC_Chop f1 f2)
  then show ?case apply (simp add:FLC_fixpt_op_def)
    using eff_compo_eff FLC_sem_wd val_modify_val
    by (smt (z3) Int_Collect Pi_iff compo_preserve_fun_le monotone_op_of_def)
next
  case (FLC_mu x1 f)
  then show ?case sorry
next
  case (FLC_nu x1 f)
  then show ?case sorry
qed


(* syntactic negation of FLC formulas. *)



end