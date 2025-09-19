theory Semantics
  imports
  "Syntax"
  "Util"
  
begin
\<comment>\<open>We realise the semantics of GL, GLs, RGL, FLC, Lmu, LStar.\<close>

section \<open>Base defs: nbd structs, ground types, contexts, valuations\<close>

type_synonym ground_type = "int"
type_synonym 'a world_type = "'a set"
type_synonym 'a sub_world_type = "'a set"
type_synonym 'a eff_fn_type = "'a sub_world_type \<Rightarrow> 'a sub_world_type"

type_synonym atm_fmls = "Atm_fml set"
type_synonym atm_games = "Atm_game set"
type_synonym var_set_type = "int set"
type_synonym var_type = "int"

\<comment>\<open>monotone neighbourhood structure\<close>
record ('a) Nbd_Struct = 
  World :: "'a world_type"
  PropInterp :: "Atm_fml \<Rightarrow> 'a sub_world_type"
  GameInterp :: "Atm_game \<Rightarrow> 'a eff_fn_type"

\<comment>\<open>predicate to ensure monotone nbd structure is defined correctly.\<close>
definition is_nbd_struct :: "'a Nbd_Struct \<Rightarrow> bool" where
  "is_nbd_struct S \<equiv> 
    (World S \<noteq> {})
  \<and> (\<forall>g. mono (GameInterp S g))
  \<and> (\<forall>g. ( (GameInterp S g) \<in> carrier_of (World S) ))
  \<and> (\<forall>p. (PropInterp S p) \<subseteq> (World S)) "


\<comment>\<open>valuation\<close>
type_synonym 'a val = "var_type \<Rightarrow> 'a eff_fn_type"

definition is_val :: "'a Nbd_Struct \<Rightarrow> 'a val \<Rightarrow> bool" where
  "is_val S f \<equiv> \<forall>i. \<forall>A\<subseteq> (World S). (mono (f i)) \<and>  ((f i A) \<subseteq> (World S))"

\<comment>\<open>context\<close>
definition Sab :: "int set" where
  "Sab = {-1,0,1}"

type_synonym cx = "Atm_game \<Rightarrow> int"

definition ALL_CX :: "(Atm_game \<Rightarrow> int) set" where
"ALL_CX = \<int> \<rightarrow> Sab"

definition is_cx :: "cx \<Rightarrow> bool" where
  "is_cx c \<equiv> c \<in> ALL_CX"

definition dual_cx :: "cx \<Rightarrow> cx" where
  "dual_cx cx = -cx"

definition subst_cx :: "cx \<Rightarrow> Atm_game \<Rightarrow> int \<Rightarrow> cx" where
  "subst_cx f a i b = (if a=b then i else f b)"

lemma subst_cx_compat :
  assumes "c\<in> ALL_CX"
  shows "subst_cx c a 1 \<in> ALL_CX \<and> subst_cx c a (-1)\<in> ALL_CX"
  apply (auto simp add:Sab_def ALL_CX_def subst_cx_def)
proof -
  show "\<And>x. x \<in> \<int> \<Longrightarrow> c x \<noteq> - 1 \<Longrightarrow> c x \<noteq> 0 \<Longrightarrow> a \<noteq> x \<Longrightarrow> c x = 1" using assms by (auto simp add:ALL_CX_def Sab_def)
  show "\<And>x. x \<in> \<int> \<Longrightarrow> c x \<noteq> - 1 \<Longrightarrow> c x \<noteq> 0 \<Longrightarrow> a \<noteq> x \<Longrightarrow> c x = 1" using assms by (auto simp add:ALL_CX_def Sab_def)
qed

definition dual_eff_fn :: "'a Nbd_Struct  \<Rightarrow> 'a eff_fn_type \<Rightarrow> 'a eff_fn_type" where
  "dual_eff_fn N f A = World N - ( f ( World N - A ) )"

section \<open>The GLs extension of base \<close>

\<comment>\<open>World type is a cartesian product with context, instead of a ground set\<close>
type_synonym GLs_ground_type = "int \<times> cx"
type_synonym GLs_world_type = "GLs_ground_type world_type"
type_synonym GLs_sub_world_type = "GLs_ground_type sub_world_type"
type_synonym GLs_eff_fn_type = "GLs_sub_world_type \<Rightarrow> GLs_sub_world_type"

definition sabo_comp :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_world_type \<Rightarrow> GLs_world_type" where
  "sabo_comp N A = {(w,cx)\<in> World N. (w, dual_cx cx) \<notin> A }"

definition sabo_dual :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_eff_fn_type \<Rightarrow> GLs_eff_fn_type" where
  "sabo_dual N f A = sabo_comp N (f (sabo_comp N A))"

\<comment>\<open>function that substitutes atomic game "a" to Angelic control in context\<close>
definition GLs_game_subst :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_sub_world_type \<Rightarrow> Atm_game \<Rightarrow> GLs_sub_world_type" where
  "GLs_game_subst N A a = {(w,c)\<in> World N. (w,(subst_cx c a 1)) \<in> A}"

definition GLs_game_Dsubst :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_sub_world_type \<Rightarrow> Atm_game \<Rightarrow> GLs_sub_world_type" where
  "GLs_game_Dsubst N A a = {(w,c) \<in> World N. (w,(subst_cx c a (-1))) \<in> A}"

definition GLs_dual_eff_fn :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_eff_fn_type \<Rightarrow> GLs_eff_fn_type" where
"GLs_dual_eff_fn N f A = sabo_comp N (f (sabo_comp N A))"

definition union :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "union A B = A\<union>B"

lemma union_mono : "\<forall>A::'a set. mono (union A)"
  apply (simp add:mono_def union_def)
  apply (auto)
  done

definition union2 :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "union2 f A B = A \<union> f(B)"

definition inter:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "inter A B = A \<inter> B"

lemma set_double_diff: 
  fixes X:: "'a set" and A::"'a set"
  assumes "A \<subseteq> X"
  shows "X-(X-A) = A"
proof (rule set_eqI)
  fix x
  show "(x \<in> X - (X - A)) = (x \<in> A)"
    using \<open>A \<subseteq> X\<close> by auto
qed

lemma union_mono_strong: "\<forall>A. mono f \<Longrightarrow> mono (union2 f A)"
  apply (simp add:mono_def union2_def)
  apply (auto)
  done

definition lift_game_interp :: "ground_type Nbd_Struct \<Rightarrow> (Atm_game \<Rightarrow> GLs_ground_type eff_fn_type)" where
"lift_game_interp N a (U:: (int\<times>(int \<Rightarrow> int)) set)
  ={(w,c). (c a = 0) \<and> (w \<in> (GameInterp N) a (fst ` U)) \<or> (c a = 1) \<and> ((w,c)\<in> U)}"

definition lift_prop_interp :: "ground_type Nbd_Struct \<Rightarrow> Atm_fml \<Rightarrow> GLs_ground_type sub_world_type" where
"lift_prop_interp N P = (PropInterp N P) \<times> ALL_CX"

definition GLs_lift_nbd :: "ground_type Nbd_Struct \<Rightarrow> GLs_ground_type Nbd_Struct" where
  "GLs_lift_nbd N = \<lparr> World=(World N)\<times>ALL_CX , 
    PropInterp = lift_prop_interp N,
    GameInterp = lift_game_interp N 
 \<rparr>"

lemma sab_negate_compat : "a\<in>Sab \<Longrightarrow> -a\<in>Sab" by (auto simp add:Sab_def)

lemma cx_negate_compat : 
  assumes "b\<in>ALL_CX"
  shows"-b\<in> ALL_CX"
  using assms by (auto simp add:ALL_CX_def Sab_def)


\<comment>\<open> Complement takes negative \<close>
lemma sabo_dbl_comp : 
  assumes "A \<subseteq> World N \<times> ALL_CX"
  shows "sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) A) = A"
  apply (auto simp add:sabo_comp_def dual_cx_def GLs_lift_nbd_def)
proof -
  show "\<And>a b. a \<in> World N \<Longrightarrow> b \<in> ALL_CX \<Longrightarrow> - b \<notin> ALL_CX \<Longrightarrow> (a, b) \<in> A" by (simp add: cx_negate_compat)
  show "\<And>a b. a \<in> World N \<Longrightarrow> b \<in> ALL_CX \<Longrightarrow> (a, - (- b)) \<in> A \<Longrightarrow> (a, b) \<in> A"
    using uminus_apply by fastforce
  show "\<And>a b. (a, b) \<in> A \<Longrightarrow> a \<in> World N" using assms by auto
  show "\<And>a b. (a, b) \<in> A \<Longrightarrow> b \<in> ALL_CX" using assms by auto
  show "\<And>a b. (a, b) \<in> A \<Longrightarrow> - b \<in> ALL_CX \<Longrightarrow> a \<in> World N \<Longrightarrow> (a, - (- b)) \<in> A"
    by (simp add: fun_Compl_def)
qed

fun GLs_fml_sem :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_fml \<Rightarrow> GLs_sub_world_type"
 and GLs_game_sem :: "GLs_ground_type Nbd_Struct => GLs_game => GLs_eff_fn_type"
  where
  "GLs_fml_sem N (GLs_Atm_fml i) = PropInterp N i"
| "GLs_fml_sem N (GLs_Not fml) = (World N)-(GLs_fml_sem N fml)"
| "GLs_fml_sem N (GLs_Or f1 f2) = GLs_fml_sem N f1 \<union> GLs_fml_sem N f2"
| "GLs_fml_sem N (GLs_Mod g f) = (GLs_game_sem N g) (GLs_fml_sem N f)"
| "GLs_game_sem N (GLs_Atm_Game i) A = GameInterp N i A"
| "GLs_game_sem N (GLs_Test fml) A = (GLs_fml_sem N fml) \<inter> A "
| "GLs_game_sem N (GLs_Sabo a) A = GLs_game_subst N A a"
| "GLs_game_sem N (GLs_Dual g) A = sabo_dual N (GLs_game_sem N g) A"
| "GLs_game_sem N (GLs_Choice a b) A = (GLs_game_sem N a A) \<union> (GLs_game_sem N b A)"
| "GLs_game_sem N (GLs_Seq a b) A = GLs_game_sem N a (GLs_game_sem N b A)"
| "GLs_game_sem N (GLs_Star a) A = lfp (\<lambda>B. A \<union> (GLs_game_sem N a B))"


fun GLs_ext_fml_sem :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_ext_fml \<Rightarrow> GLs_sub_world_type"
  and GLs_ext_game_sem :: "GLs_ground_type  Nbd_Struct \<Rightarrow> GLs_ext_game \<Rightarrow> GLs_eff_fn_type"
  where
  "GLs_ext_fml_sem N (GLs_ext_Atm_fml P) = (PropInterp N) P"
| "GLs_ext_fml_sem N (GLs_ext_Not f) = sabo_comp N (GLs_ext_fml_sem N f)"
| "GLs_ext_fml_sem N (GLs_ext_Or f1 f2) = (GLs_ext_fml_sem N f1) \<union> (GLs_ext_fml_sem N f2)"
| "GLs_ext_fml_sem N (GLs_ext_And f1 f2) = (GLs_ext_fml_sem N f1) \<inter> (GLs_ext_fml_sem N f2)"
| "GLs_ext_fml_sem N (GLs_ext_Mod g f) = GLs_ext_game_sem N g (GLs_ext_fml_sem N f)"
| "GLs_ext_game_sem N (GLs_ext_Atm_Game a) A = (GameInterp N) a A"
| "GLs_ext_game_sem N (GLs_ext_Sabo a) A = GLs_game_subst N A a"
| "GLs_ext_game_sem N (GLs_ext_DSabo a) A = GLs_game_Dsubst N A a"
| "GLs_ext_game_sem N (GLs_ext_Dual g) A = GLs_dual_eff_fn N (GLs_ext_game_sem N g) A"
| "GLs_ext_game_sem N (GLs_ext_Test f) A = A \<inter> GLs_ext_fml_sem N f"
| "GLs_ext_game_sem N (GLs_ext_DTest f) A = (sabo_comp N A) \<union> sabo_comp N (GLs_ext_fml_sem N f)"
| "GLs_ext_game_sem N (GLs_ext_Choice g1 g2) A = GLs_ext_game_sem N g1 A \<union> GLs_ext_game_sem N g2 A"
| "GLs_ext_game_sem N (GLs_ext_DChoice g1 g2) A = GLs_ext_game_sem N g1 A \<inter> GLs_ext_game_sem N g2 A"
| "GLs_ext_game_sem N (GLs_ext_Seq g1 g2) A = GLs_ext_game_sem N g2 (GLs_ext_game_sem N g1 A)"
| "GLs_ext_game_sem N (GLs_ext_Star g) A = \<Inter> { B \<in> Pow (World N). A \<union> GLs_ext_game_sem N g B \<subseteq> B}"
| "GLs_ext_game_sem N (GLs_ext_Cross g) A = \<Union> { B \<in> Pow (World N). B \<subseteq> A \<union> GLs_ext_game_sem N g B}"

lemma cx_double_neg : 
  assumes "c \<in> ALL_CX" shows "subst_cx c x (-1) = - subst_cx (- c) x 1" by (auto simp add:subst_cx_def)

lemma cx_neg_sub:
  assumes "c\<in> ALL_CX" shows "- (subst_cx c x t) = subst_cx (-c) x (-t)" by (auto simp add:subst_cx_def)

lemma GLs_syn_inversion_compat :
  fixes N:: "ground_type Nbd_Struct"
  and f:: "GLs_ext_fml"
  and g:: "GLs_ext_game"
assumes isStruct: "is_nbd_struct N"
  and isStructlift: "is_nbd_struct (GLs_lift_nbd N)"
shows "GLs_ext_fml_sem (GLs_lift_nbd N) (GLs_syn_comp f) = sabo_comp (GLs_lift_nbd N) (GLs_ext_fml_sem (GLs_lift_nbd N) f)"
   "GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual g) = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) g)"
proof (induction f and g)
  case (GLs_ext_Atm_Game x)
  then show ?case by (auto simp add: GLs_dual_eff_fn_def )
next
  case (GLs_ext_Sabo x)
  then show ?case
    apply (auto simp add: isStructlift
       GLs_lift_nbd_def  GLs_dual_eff_fn_def sabo_comp_def dual_cx_def GLs_game_subst_def GLs_game_Dsubst_def)
    apply (rule)
  proof
    fix xa show " {(w, c). w \<in> World N \<and> c \<in> ALL_CX \<and> (w, subst_cx c x (- 1)) \<in> xa}
          \<subseteq> {(w, cx). w \<in> World N \<and> cx \<in> ALL_CX \<and> (subst_cx (- cx) x 1 \<in> ALL_CX \<longrightarrow> w \<in> World N \<longrightarrow> - cx \<in> ALL_CX \<longrightarrow> (w, - subst_cx (- cx) x 1) \<in> xa)}"
      by (auto simp add:cx_double_neg)
    fix xa show "{(w, cx). w \<in> World N \<and> cx \<in> ALL_CX \<and> (subst_cx (- cx) x 1 \<in> ALL_CX \<longrightarrow> w \<in> World N \<longrightarrow> - cx \<in> ALL_CX \<longrightarrow> (w, - subst_cx (- cx) x 1) \<in> xa)}
          \<subseteq> {(w, c). w \<in> World N \<and> c \<in> ALL_CX \<and> (w, subst_cx c x (- 1)) \<in> xa}  "
      by (auto simp add:cx_double_neg cx_negate_compat subst_cx_compat)
  qed
next
  case (GLs_ext_DSabo x)
  then show ?case
    apply (auto simp add: isStructlift
    GLs_lift_nbd_def  GLs_dual_eff_fn_def sabo_comp_def dual_cx_def GLs_game_subst_def GLs_game_Dsubst_def)
    apply rule
  proof - fix xa show "{(w, c). w \<in> World N \<and> c \<in> ALL_CX \<and> (w, subst_cx c x 1) \<in> xa} =
          {(w, cx). w \<in> World N \<and> cx \<in> ALL_CX \<and> (subst_cx (- cx) x (- 1) \<in> ALL_CX \<longrightarrow> w \<in> World N \<longrightarrow> - cx \<in> ALL_CX \<longrightarrow> (w, - subst_cx (- cx) x (- 1)) \<in> xa)}"
      apply (auto simp add: isStructlift ALL_CX_def
    GLs_lift_nbd_def  GLs_dual_eff_fn_def sabo_comp_def dual_cx_def GLs_game_subst_def GLs_game_Dsubst_def)
    proof (metis (lifting) ext ALL_CX_def cx_neg_sub uminus_apply verit_minus_simplify(4))
      fix a b xb show " a \<in> World N \<Longrightarrow> b \<in> \<int> \<rightarrow> Sab \<Longrightarrow> xb \<in> \<int> \<Longrightarrow> subst_cx (- b) x (- 1) xb \<notin> Sab \<Longrightarrow> (a, subst_cx b x 1) \<in> xa"
        by (metis ALL_CX_def Pi_mem cx_negate_compat subst_cx_compat)
      fix a b xb show "a \<in> World N \<Longrightarrow> b \<in> \<int> \<rightarrow> Sab \<Longrightarrow> xb \<in> \<int> \<Longrightarrow> - b xb \<notin> Sab \<Longrightarrow> (a, subst_cx b x 1) \<in> xa"
        by (metis Pi_mem sab_negate_compat)
      fix a b show "a \<in> World N \<Longrightarrow> b \<in> \<int> \<rightarrow> Sab \<Longrightarrow> (a, - subst_cx (- b) x (- 1)) \<in> xa \<Longrightarrow> (a, subst_cx b x 1) \<in> xa"
        by (metis (lifting) ext ALL_CX_def cx_neg_sub uminus_apply verit_minus_simplify(4))
    qed
  qed
next
  case (GLs_ext_Dual x)
  then show ?case sorry
next
  case (GLs_ext_Test x)
  then show ?case sorry
next
  case (GLs_ext_Choice x1 x2)
  then show ?case sorry
next
  case (GLs_ext_DChoice x1 x2)
  then show ?case sorry
next
  case (GLs_ext_DTest x)
  then show ?case sorry
next
  case (GLs_ext_Seq x1 x2)
  then show ?case sorry
next
  case (GLs_ext_Star x)
  then show ?case sorry
next
  case (GLs_ext_Cross x)
  then show ?case sorry
next
  case (GLs_ext_Atm_fml x)
  then show ?case sorry
next
  case (GLs_ext_Not x)
  then show ?case sorry
next
  case (GLs_ext_Or x1 x2)
  then show ?case sorry
next
  case (GLs_ext_And x1 x2)
  then show ?case sorry
next
  case (GLs_ext_Mod x1 x2)
  then show ?case sorry
qed

section \<open>The RGL extension of base \<close>
type_synonym RGL_var_type = "int"
type_synonym RGL_ground_type = "int"
type_synonym RGL_world_type = "RGL_ground_type world_type"
type_synonym RGL_sub_world_type = "RGL_ground_type sub_world_type"
type_synonym RGL_eff_fn_type = "RGL_sub_world_type \<Rightarrow> RGL_sub_world_type"

\<comment>\<open>No modification to the base\<close>
fun RGL_fml_sem :: "RGL_ground_type Nbd_Struct \<Rightarrow> RGL_var_type val \<Rightarrow> RGL_var_type RGL_fml \<Rightarrow> RGL_sub_world_type"
  and RGL_game_sem :: "RGL_ground_type Nbd_Struct \<Rightarrow> RGL_var_type val \<Rightarrow> RGL_var_type RGL_game \<Rightarrow> RGL_eff_fn_type"
  where
  "RGL_fml_sem N I (RGL_Atm_fml fl) = PropInterp N fl"
| "RGL_fml_sem N I (RGL_Not fl) = (World N) - (RGL_fml_sem N I fl)"
| "RGL_fml_sem N I (RGL_Or fl1 fl2) = (RGL_fml_sem N I fl1) \<union> (RGL_fml_sem N I fl2)"
| "RGL_fml_sem N I (RGL_Mod g fl) = (RGL_game_sem N I g) (RGL_fml_sem N I fl)"
| "RGL_game_sem N I (RGL_Atm_Game a) A = GameInterp N a A"
| "RGL_game_sem N I (RGL_Var x) A = I x A"
| "RGL_game_sem N I (RGL_Dual g) A = (dual_eff_fn N (RGL_game_sem N I g)) A"
| "RGL_game_sem N I (RGL_Test fl) A = (RGL_fml_sem N I fl) \<inter> A"
| "RGL_game_sem N I (RGL_Choice g1 g2) A = (RGL_game_sem N I g1 A) \<union> (RGL_game_sem N I g2 A)"
| "RGL_game_sem N I (RGL_Seq g1 g2) A = ((RGL_game_sem N I g2) \<circ> (RGL_game_sem N I g1)) A"
| "RGL_game_sem N I (RGL_Rec x g) A = (lfp (\<lambda>u. (RGL_game_sem N (I(x:=u)) g))) A"

fun RGL_dualize_free :: "RGL_var_type \<Rightarrow> RGL_var_type RGL_ext_game \<Rightarrow> RGL_var_type RGL_ext_game" where
"RGL_dualize_free x (RGL_ext_Var y) = (if x=y then (RGL_ext_Var_Dual x) else (RGL_ext_Var y))"
| "RGL_dualize_free x (RGL_ext_Var_Dual y) = (if x=y then (RGL_ext_Var x) else (RGL_ext_Var_Dual y))"
| "RGL_dualize_free x (RGL_ext_Rec y g) = (if x=y then (RGL_ext_Rec y g) else RGL_ext_Rec y (RGL_dualize_free x g))"
| "RGL_dualize_free x (RGL_ext_Rec_Dual y g) = (if x=y then (RGL_ext_Rec_Dual y g) else RGL_ext_Rec_Dual y (RGL_dualize_free x g))"
| "RGL_dualize_free x (RGL_ext_Choice g1 g2) = RGL_ext_Choice (RGL_dualize_free x g1) (RGL_dualize_free x g2)"
| "RGL_dualize_free x (RGL_ext_Choice_Dual g1 g2) = RGL_ext_Choice_Dual (RGL_dualize_free x g1) (RGL_dualize_free x g2)"
| "RGL_dualize_free x (RGL_ext_Seq g1 g2) = RGL_ext_Seq (RGL_dualize_free x g1) (RGL_dualize_free x g2)"
| "RGL_dualize_free x g = g"

\<comment>\<open>syntactic dual and complement functions. The return value is automatically in normal form.\<close>
fun RGL_syn_comp :: "RGL_var_type RGL_ext_fml \<Rightarrow> RGL_var_type RGL_ext_fml"
and RGL_syn_dual :: "RGL_var_type RGL_ext_game \<Rightarrow> RGL_var_type RGL_ext_game" 
where
 "RGL_syn_comp (RGL_ext_Atm_fml P) = RGL_ext_Not (RGL_ext_Atm_fml P)"
| "RGL_syn_comp (RGL_ext_Not f) = RGL_syn_comp f"
| "RGL_syn_comp (RGL_ext_Or f1 f2) = RGL_ext_And (RGL_syn_comp f1) (RGL_syn_comp f2)"
| "RGL_syn_comp (RGL_ext_Mod g f) = RGL_ext_Mod (RGL_syn_dual g) (RGL_syn_comp f)"
| "RGL_syn_comp (RGL_ext_And f1 f2) = RGL_ext_Or (RGL_syn_comp f1) (RGL_syn_comp f2)"

| "RGL_syn_dual (RGL_ext_Atm_Game a) = RGL_ext_Atm_Game_Dual a"
| "RGL_syn_dual (RGL_ext_Atm_Game_Dual a) = RGL_ext_Atm_Game a"
| "RGL_syn_dual (RGL_ext_Var x) = RGL_ext_Var_Dual x"
| "RGL_syn_dual (RGL_ext_Var_Dual x) = RGL_ext_Var x"
| "RGL_syn_dual (RGL_ext_Seq g1 g2) = RGL_ext_Seq (RGL_syn_dual g1) (RGL_syn_dual g2)"
| "RGL_syn_dual (RGL_ext_Test f) = RGL_ext_Test_Dual f"
| "RGL_syn_dual (RGL_ext_Test_Dual f) = RGL_ext_Test f"
| "RGL_syn_dual (RGL_ext_Choice g1 g2) = RGL_ext_Choice_Dual (RGL_syn_dual g1) (RGL_syn_dual g2)"
| "RGL_syn_dual (RGL_ext_Choice_Dual g1 g2) = RGL_ext_Choice (RGL_syn_dual g1) (RGL_syn_dual g2)"
| "RGL_syn_dual (RGL_ext_Rec x g) = 
  RGL_ext_Rec_Dual x (RGL_dualize_free x (RGL_syn_dual g))"
| "RGL_syn_dual (RGL_ext_Rec_Dual x g) = RGL_ext_Rec x (RGL_dualize_free x (RGL_syn_dual g))"


fun RGL_syn_subst :: "RGL_var_type \<Rightarrow> RGL_var_type RGL_ext_game \<Rightarrow> RGL_var_type RGL_ext_game \<Rightarrow> RGL_var_type RGL_ext_game" 
where
  "RGL_syn_subst x0 g0 (RGL_ext_Var x) = (if x=x0 then g0 else (RGL_ext_Var x))"
| "RGL_syn_subst x0 g0 (RGL_ext_Var_Dual x) = (if x=x0 then RGL_syn_dual g0 
      else (RGL_ext_Var_Dual x))"
| "RGL_syn_subst x0 g0 (RGL_ext_Atm_Game a) = RGL_ext_Atm_Game a"
| "RGL_syn_subst x0 g0 (RGL_ext_Atm_Game_Dual a) = RGL_ext_Atm_Game_Dual a"
| "RGL_syn_subst x0 g0 (RGL_ext_Test f) = RGL_ext_Test f"
| "RGL_syn_subst x0 g0 (RGL_ext_Test_Dual f) = RGL_ext_Test_Dual f"
| "RGL_syn_subst x0 g0 (RGL_ext_Choice g1 g2) = RGL_ext_Choice (RGL_syn_subst x0 g0 g1) (RGL_syn_subst x0 g0 g2)"
| "RGL_syn_subst x0 g0 (RGL_ext_Choice_Dual g1 g2) = RGL_ext_Choice_Dual (RGL_syn_subst x0 g0 g1) (RGL_syn_subst x0 g0 g2)"
| "RGL_syn_subst x0 g0 (RGL_ext_Seq g1 g2) = RGL_ext_Seq (RGL_syn_subst x0 g0 g1) (RGL_syn_subst x0 g0 g2)"
| "RGL_syn_subst x0 g0 (RGL_ext_Rec x g) = 
    (if x0=x then RGL_ext_Rec x g else RGL_ext_Rec x (RGL_syn_subst x0 g0 g))"
| "RGL_syn_subst x0 g0 (RGL_ext_Rec_Dual x g) = 
    (if x0=x then (RGL_ext_Rec_Dual x g) else RGL_ext_Rec_Dual x (RGL_syn_subst x0 g0 g))"


fun RGL_fml_embed_ext :: "RGL_var_type RGL_fml \<Rightarrow> RGL_var_type RGL_ext_fml"
and  RGL_gm_embed_ext :: "RGL_var_type RGL_game \<Rightarrow> RGL_var_type RGL_ext_game" where
 "RGL_fml_embed_ext (RGL_Atm_fml f) = RGL_ext_Atm_fml f"
| "RGL_fml_embed_ext (RGL_Not f) = RGL_ext_Not (RGL_fml_embed_ext f)"
| "RGL_fml_embed_ext (RGL_Or f1 f2) = RGL_ext_Or (RGL_fml_embed_ext f1) (RGL_fml_embed_ext f2)"
| "RGL_fml_embed_ext (RGL_Mod g f) = RGL_ext_Mod (RGL_gm_embed_ext g) (RGL_fml_embed_ext f)"
| "RGL_gm_embed_ext (RGL_Atm_Game a) = RGL_ext_Atm_Game a"
| "RGL_gm_embed_ext (RGL_Var x) = RGL_ext_Var x"
| "RGL_gm_embed_ext (RGL_Dual g) = RGL_syn_dual (RGL_gm_embed_ext g)"
| "RGL_gm_embed_ext (RGL_Test fl) = RGL_ext_Test (RGL_fml_embed_ext fl)"
| "RGL_gm_embed_ext (RGL_Choice g1 g2) = RGL_ext_Choice (RGL_gm_embed_ext g1) (RGL_gm_embed_ext g2)"
| "RGL_gm_embed_ext (RGL_Seq g1 g2) = RGL_ext_Seq (RGL_gm_embed_ext g1) (RGL_gm_embed_ext g2)"
| "RGL_gm_embed_ext (RGL_Rec x g) = RGL_ext_Rec x (RGL_gm_embed_ext g)"

\<comment>\<open>For the syntax extended with complement and dual, we only interpret normal form formulas.
  Choice_Dual = cap, interpreted as set intersection
  Rec_Dual = inverted r. binder, interpreted as the gfp
  Test_Dual = inverted question mark, interpreted as the dual function
  \<close>
fun RGL_ext_fml_sem :: "RGL_ground_type Nbd_Struct \<Rightarrow> RGL_var_type val \<Rightarrow> RGL_var_type RGL_ext_fml \<Rightarrow> RGL_sub_world_type"
  and RGL_ext_game_sem :: "RGL_ground_type Nbd_Struct \<Rightarrow> RGL_var_type val \<Rightarrow> RGL_var_type RGL_ext_game \<Rightarrow> RGL_eff_fn_type"
  where
  "RGL_ext_fml_sem N I (RGL_ext_Atm_fml fl) = PropInterp N fl"
| "RGL_ext_fml_sem N I (RGL_ext_Not fl) = (World N) - (RGL_ext_fml_sem N I fl)"
| "RGL_ext_fml_sem N I (RGL_ext_Or fl1 fl2) = (RGL_ext_fml_sem N I fl1) \<union> (RGL_ext_fml_sem N I fl2)"
| "RGL_ext_fml_sem N I (RGL_ext_And fl1 fl2) = (RGL_ext_fml_sem N I fl1) \<inter> (RGL_ext_fml_sem N I fl2)"
| "RGL_ext_fml_sem N I (RGL_ext_Mod g fl) = (RGL_ext_game_sem N I g) (RGL_ext_fml_sem N I fl)"
| "RGL_ext_game_sem N I (RGL_ext_Atm_Game a) A = GameInterp N a A"
| "RGL_ext_game_sem N I (RGL_ext_Atm_Game_Dual a) A = (dual_eff_fn N (GameInterp N a)) A"
| "RGL_ext_game_sem N I (RGL_ext_Var x) A = I x A"
| "RGL_ext_game_sem N I (RGL_ext_Var_Dual x) A = (dual_eff_fn N (I x)) A"
| "RGL_ext_game_sem N I (RGL_ext_Test fl) A = (RGL_ext_fml_sem N I fl) \<inter> A"
| "RGL_ext_game_sem N I (RGL_ext_Test_Dual fl) A = (dual_eff_fn N (inter (RGL_ext_fml_sem N I fl))) A"
| "RGL_ext_game_sem N I (RGL_ext_Choice g1 g2) A = (RGL_ext_game_sem N I g1 A) \<union> (RGL_ext_game_sem N I g2 A)"
| "RGL_ext_game_sem N I (RGL_ext_Choice_Dual g1 g2) A = (RGL_ext_game_sem N I g1 A) \<inter> (RGL_ext_game_sem N I g2 A)"
| "RGL_ext_game_sem N I (RGL_ext_Seq g1 g2) A = ((RGL_ext_game_sem N I g2) \<circ> (RGL_ext_game_sem N I g1)) A"
| "RGL_ext_game_sem N I (RGL_ext_Rec x g) A = (Lfp (World N) (\<lambda>u. (RGL_ext_game_sem N (I(x:=u)) g))) A"
| "RGL_ext_game_sem N I (RGL_ext_Rec_Dual x g) A = (Gfp (World N) (\<lambda>u. (RGL_ext_game_sem N (I(x:=u)) g))) A"

lemma RGL_ext_game_sem_wd :
  fixes N :: "RGL_ground_type Nbd_Struct"
  and I :: "RGL_var_type val"
assumes "is_nbd_struct N"
    and "is_val N I"
  shows
    "(RGL_ext_fml_sem N I f) \<subseteq> (World N)"
    " \<forall>A. A \<subseteq> (World N) \<longrightarrow> (RGL_ext_game_sem N I g) A \<subseteq> (World N)"
proof (induction f and g arbitrary:A)
  case (RGL_ext_Atm_Game x)
  then show ?case using assms by (auto simp add:is_nbd_struct_def carrier_of_def)
next
  case (RGL_ext_Atm_Game_Dual x)
  then show ?case using assms by (auto simp add:is_nbd_struct_def dual_eff_fn_def)
next
  case (RGL_ext_Var x)
  then show ?case using assms by (auto simp add:is_val_def)
next
  case (RGL_ext_Var_Dual x)
  then show ?case using assms by (auto simp add:is_val_def dual_eff_fn_def)
next
  case (RGL_ext_Test x)
  then show ?case using assms by (auto simp add:is_nbd_struct_def)
next
  case (RGL_ext_Test_Dual x)
  then show ?case using assms by (auto simp add:is_nbd_struct_def dual_eff_fn_def)
next
  case (RGL_ext_Choice x1 x2)
  then show ?case using assms by (auto simp add:is_nbd_struct_def)
next
  case (RGL_ext_Choice_Dual x1 x2)
  then show ?case using assms by (auto simp add:is_nbd_struct_def dual_eff_fn_def)
next
  case (RGL_ext_Seq x1 x2)
  then show ?case by auto
next
  case (RGL_ext_Rec x1 x2)
  then show ?case
    apply simp
  proof -
    
  qed
next
  case (RGL_ext_Rec_Dual x1 x2)
  then show ?case using assms by (auto simp add:is_nbd_struct_def)
next
  case (RGL_ext_Atm_fml x)
  then show ?case using assms by (auto simp add:is_nbd_struct_def)
next
  case (RGL_ext_Not x)
  then show ?case using assms by (auto simp add:is_nbd_struct_def)
next
  case (RGL_ext_Or x1 x2)
  then show ?case using assms by (auto simp add:is_nbd_struct_def)
next
  case (RGL_ext_And x1 x2)
  then show ?case using assms by (auto simp add:is_nbd_struct_def)
next
  case (RGL_ext_Mod x1 x2)
  then show ?case using assms by (auto simp add:is_nbd_struct_def)
qed

lemma syn_invert_save_sem :
  fixes \<phi> :: "RGL_var_type RGL_ext_fml"
  and \<alpha> :: "RGL_var_type RGL_ext_game" 
  and N :: "RGL_ground_type Nbd_Struct"
  and I :: "RGL_var_type val"
assumes 
  "is_nbd_struct N"
  and "is_val N I"
shows "(RGL_ext_fml_sem N I (RGL_syn_comp \<phi>) = (World N)-(RGL_ext_fml_sem N I \<phi>))"
  "restrict (RGL_ext_game_sem N I (RGL_syn_dual \<alpha>)) (Pow (World N)) 
    = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I \<alpha>)) (Pow (World N))"
proof 
 (induction \<phi> and \<alpha>)
  case (RGL_ext_Atm_Game x)
  then show ?case by simp
next
  case (RGL_ext_Atm_Game_Dual x)
  show ?case
  proof (rule ext)
    fix xa show "restrict (RGL_ext_game_sem N I (RGL_syn_dual (RGL_ext_Atm_Game_Dual x))) (Pow (World N)) xa = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I (RGL_ext_Atm_Game_Dual x))) (Pow (World N)) xa "
      apply (simp add:restrict_def dual_eff_fn_def)
      apply (simp add:set_double_diff)
      apply (rule impI)
    proof -
      from assms(1) have "\<forall>A. (A \<subseteq> (World N) \<longrightarrow> (GameInterp N x A) \<subseteq> (World N))" by (simp add:is_nbd_struct_def)
      then have "\<forall> A. (A \<subseteq> (World N) \<longrightarrow>  GameInterp N x A = (World N - ((World N)- (GameInterp N x A))))" by auto
      then show "xa \<subseteq> World N \<Longrightarrow> GameInterp N x xa = World N - (World N - GameInterp N x xa)" by blast
    qed
  qed
next
  case (RGL_ext_Var x)
  show ?case by auto
next
  case (RGL_ext_Var_Dual x)
  show ?case
  proof (rule)
    fix xa show "restrict (RGL_ext_game_sem N I (RGL_syn_dual (RGL_ext_Var_Dual x))) (Pow (World N)) xa = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I (RGL_ext_Var_Dual x))) (Pow (World N)) xa"
      apply (simp add:restrict_def dual_eff_fn_def)
      apply (simp add:set_double_diff)
      apply (rule impI)
    proof -
      from assms(2) have "\<forall>A \<subseteq> (World N). (I x A) \<subseteq> (World N)" by (auto simp add:is_val_def)
      then show "xa \<subseteq> World N \<Longrightarrow> I x xa = World N - (World N - I x xa)" by blast
    qed
  qed
next
  case (RGL_ext_Test x)
  show ?case
  proof (rule)
    fix xa show "restrict (RGL_ext_game_sem N I (RGL_syn_dual (RGL_ext_Test x))) (Pow (World N)) xa = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I (RGL_ext_Test x))) (Pow (World N)) xa"
      by (simp add:restrict_def dual_eff_fn_def inter_def)
  qed
next
  case (RGL_ext_Test_Dual x)
  show ?case
  proof (rule)
    fix xa show "restrict (RGL_ext_game_sem N I (RGL_syn_dual (RGL_ext_Test_Dual x))) (Pow (World N)) xa = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I (RGL_ext_Test_Dual x))) (Pow (World N)) xa"
      apply (simp add:restrict_def dual_eff_fn_def inter_def)
      apply (simp add:set_double_diff)
      apply (rule impI)
    proof -
      assume P: "xa \<subseteq> World N"
      have "(RGL_ext_fml_sem N I x) \<inter> xa \<subseteq> World N" using P by auto
      then show "RGL_ext_fml_sem N I x \<inter> xa = World N - (World N - RGL_ext_fml_sem N I x \<inter> xa)" by blast
    qed
  qed
next
  case (RGL_ext_Choice x1 x2)
  then show ?case
  proof -
    assume P1: "restrict (RGL_ext_game_sem N I (RGL_syn_dual x1)) (Pow (World N)) = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x1)) (Pow (World N))"
      and P2 : "restrict (RGL_ext_game_sem N I (RGL_syn_dual x2)) (Pow (World N)) = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x2)) (Pow (World N))"
    show "restrict (RGL_ext_game_sem N I (RGL_syn_dual (RGL_ext_Choice x1 x2))) (Pow (World N)) = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I (RGL_ext_Choice x1 x2))) (Pow (World N))"
    proof (rule)
      fix x show "restrict (RGL_ext_game_sem N I (RGL_syn_dual (RGL_ext_Choice x1 x2))) (Pow (World N)) x = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I (RGL_ext_Choice x1 x2))) (Pow (World N)) x"
        apply (simp add:dual_eff_fn_def)
      proof (rule)
        assume P3 : "x \<subseteq> World N"
        show "RGL_ext_game_sem N I (RGL_syn_dual x1) x \<inter> RGL_ext_game_sem N I (RGL_syn_dual x2) x = World N - (RGL_ext_game_sem N I x1 (World N - x) \<union> RGL_ext_game_sem N I x2 (World N - x)) "
        proof -
          from P1 have
            "restrict (RGL_ext_game_sem N I (RGL_syn_dual x1)) (Pow (World N)) x = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x1)) (Pow (World N)) x" by simp
          then have
            P1': "RGL_ext_game_sem N I (RGL_syn_dual x1) x = dual_eff_fn (World N) (RGL_ext_game_sem N I x1) x" using P3 by simp
          from P2 have 
            "restrict (RGL_ext_game_sem N I (RGL_syn_dual x2)) (Pow (World N))x = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x2)) (Pow (World N))x" by simp
          then have
            P2': "RGL_ext_game_sem N I (RGL_syn_dual x2) x = dual_eff_fn (World N) (RGL_ext_game_sem N I x2) x" using P3 by simp
          from P1' P2' show " RGL_ext_game_sem N I (RGL_syn_dual x1) x \<inter> RGL_ext_game_sem N I (RGL_syn_dual x2) x =
            World N - (RGL_ext_game_sem N I x1 (World N - x) \<union> RGL_ext_game_sem N I x2 (World N - x))" by (auto simp add:dual_eff_fn_def)
        qed
      qed
    qed
  qed
next
  case (RGL_ext_Choice_Dual x1 x2)
  then show ?case
  proof -
    assume P1: "restrict (RGL_ext_game_sem N I (RGL_syn_dual x1)) (Pow (World N)) = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x1)) (Pow (World N))"
    and P2: "restrict (RGL_ext_game_sem N I (RGL_syn_dual x2)) (Pow (World N)) = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x2)) (Pow (World N))"
    show "restrict (RGL_ext_game_sem N I (RGL_syn_dual (RGL_ext_Choice_Dual x1 x2))) (Pow (World N)) =
    restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I (RGL_ext_Choice_Dual x1 x2))) (Pow (World N)) "
    proof 
      fix x show " restrict (RGL_ext_game_sem N I (RGL_syn_dual (RGL_ext_Choice_Dual x1 x2))) (Pow (World N)) x =
         restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I (RGL_ext_Choice_Dual x1 x2))) (Pow (World N)) x "
        apply (simp add:dual_eff_fn_def)
      proof 
        assume P3: "x\<subseteq> World N"
        show "RGL_ext_game_sem N I (RGL_syn_dual x1) x \<union> RGL_ext_game_sem N I (RGL_syn_dual x2) x =
    World N - RGL_ext_game_sem N I x1 (World N - x) \<inter> RGL_ext_game_sem N I x2 (World N - x)"
        proof -
          have "restrict (RGL_ext_game_sem N I (RGL_syn_dual x1)) (Pow (World N)) x = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x1)) (Pow (World N)) x"
            using P1 by simp
          then have P1': "RGL_ext_game_sem N I (RGL_syn_dual x1) x = dual_eff_fn (World N) (RGL_ext_game_sem N I x1) x" using P3 by simp
          have "restrict (RGL_ext_game_sem N I (RGL_syn_dual x2)) (Pow (World N)) x = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x2)) (Pow (World N)) x"
            using P2 by simp
          then have P2': "RGL_ext_game_sem N I (RGL_syn_dual x2) x = dual_eff_fn (World N) (RGL_ext_game_sem N I x2) x" using P3 by simp
          show "RGL_ext_game_sem N I (RGL_syn_dual x1) x \<union> RGL_ext_game_sem N I (RGL_syn_dual x2) x =
            World N - RGL_ext_game_sem N I x1 (World N - x) \<inter> RGL_ext_game_sem N I x2 (World N - x)" using P1' P2' by (auto simp add:dual_eff_fn_def)
        qed
      qed
    qed
  qed
next
  case (RGL_ext_Seq x1 x2)
  then show ?case
  proof -
    assume P1: "restrict (RGL_ext_game_sem N I (RGL_syn_dual x1)) (Pow (World N)) = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x1)) (Pow (World N))"
    and P2: "restrict (RGL_ext_game_sem N I (RGL_syn_dual x2)) (Pow (World N)) = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x2)) (Pow (World N))"
    show "restrict (RGL_ext_game_sem N I (RGL_syn_dual (RGL_ext_Seq x1 x2))) (Pow (World N)) =
    restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I (RGL_ext_Seq x1 x2))) (Pow (World N)) "
    proof 
      fix x show "restrict (RGL_ext_game_sem N I (RGL_syn_dual (RGL_ext_Seq x1 x2))) (Pow (World N)) x =
         restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I (RGL_ext_Seq x1 x2))) (Pow (World N)) x"
        apply (simp add:dual_eff_fn_def)
      proof 
        assume P3: "x\<subseteq> World N"
        show " RGL_ext_game_sem N I (RGL_syn_dual x2) (RGL_ext_game_sem N I (RGL_syn_dual x1) x) 
          = World N - RGL_ext_game_sem N I x2 (RGL_ext_game_sem N I x1 (World N - x))"
        proof -
          have "restrict (RGL_ext_game_sem N I (RGL_syn_dual x1)) (Pow (World N)) x = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x1)) (Pow (World N)) x"
            using P1 by simp
          then have P1': "RGL_ext_game_sem N I (RGL_syn_dual x1) x = dual_eff_fn (World N) (RGL_ext_game_sem N I x1) x" using P3 by simp
          have P2': "restrict (RGL_ext_game_sem N I (RGL_syn_dual x2)) (Pow (World N))(RGL_ext_game_sem N I (RGL_syn_dual x1) x)
               = restrict (dual_eff_fn (World N) (RGL_ext_game_sem N I x2)) (Pow (World N)) (RGL_ext_game_sem N I (RGL_syn_dual x1) x)"
            using P2 by simp

          then have "RGL_ext_game_sem N I (RGL_syn_dual x1) x \<subseteq> World N" using  by auto
          then have P2'': "RGL_ext_game_sem N I (RGL_syn_dual x2) (RGL_ext_game_sem N I (RGL_syn_dual x1) x)
             = dual_eff_fn (World N) (RGL_ext_game_sem N I x2) (RGL_ext_game_sem N I (RGL_syn_dual x1) x)" using P3 by simp
          show "RGL_ext_game_sem N I (RGL_syn_dual x2) (RGL_ext_game_sem N I (RGL_syn_dual x1) x) 
          = World N - RGL_ext_game_sem N I x2 (RGL_ext_game_sem N I x1 (World N - x))" using P1' P2' by (simp add:dual_eff_fn_def)
        qed
      qed
    qed
  qed
  
next
  case (RGL_ext_Rec x1 x2)
  consider "a \<in> Pow (World N)" | "a \<notin> Pow (World N)" by blast
  then show ?case 
next
  case (RGL_ext_Rec_Dual x1 x2)
  consider "a \<in> Pow (World N)" | "a \<notin> Pow (World N)" by blast
  then show ?case 
next
  case (RGL_ext_Atm_fml x)
  consider "a \<in> Pow (World N)" | "a \<notin> Pow (World N)" by blast
  then show ?case by auto
next
  case (RGL_ext_Not x)
  consider "a \<in> Pow (World N)" | "a \<notin> Pow (World N)" by blast
  then show ?case 
next
  case (RGL_ext_Or x1 x2)
  consider "a \<in> Pow (World N)" | "a \<notin> Pow (World N)" by blast
  then show ?case 
next
  case (RGL_ext_And x1 x2)
  consider "a \<in> Pow (World N)" | "a \<notin> Pow (World N)" by blast
  then show ?case 
next
  case (RGL_ext_Mod x1 x2)
  consider "a \<in> Pow (World N)" | "a \<notin> Pow (World N)" by blast
  then show ?case 
qed
  
end