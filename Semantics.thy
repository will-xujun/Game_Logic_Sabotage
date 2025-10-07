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
  \<and> (\<forall>g. ( (GameInterp S g) \<in> carrier_of (World S) \<inter> mono_of (World S) ))
  \<and> (\<forall>p. (PropInterp S p) \<subseteq> (World S)) "

\<comment>\<open>valuation\<close>
type_synonym 'a val = "var_type \<Rightarrow> 'a eff_fn_type"

definition is_val :: "'a Nbd_Struct \<Rightarrow> 'a val \<Rightarrow> bool" where
  "is_val N I \<equiv> \<forall>i. I i \<in> effective_fn_of (World N)"

\<comment>\<open>context\<close>
definition Sab :: "int set" where
  "Sab = {-1,0,1}"

type_synonym cx = "Atm_game \<Rightarrow> int"

definition ALL_CX :: "(Atm_game \<Rightarrow> int) set" where
"ALL_CX = \<int> \<rightarrow> Sab"

definition const1_cx :: "cx" where
  "const1_cx t = 1"

lemma ALL_CX_nonempty : "ALL_CX \<noteq> {}"
proof -
  have"const1_cx \<in> ALL_CX"
    apply (simp add:ALL_CX_def const1_cx_def)
    apply (auto simp add:const1_cx_def Sab_def)
    done
  then show ?thesis by auto
qed

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

lemma cx_double_neg : 
  assumes "c \<in> ALL_CX" shows "subst_cx c x (-1) = - subst_cx (- c) x 1" by (auto simp add:subst_cx_def)

lemma cx_neg_sub:
  assumes "c\<in> ALL_CX" shows "- (subst_cx c x t) = subst_cx (-c) x (-t)" by (auto simp add:subst_cx_def)

lemma cx_double_dual : 
  assumes "c\<in> ALL_CX" shows "dual_cx (dual_cx c) = c" using assms by (auto simp add:dual_cx_def)

lemma sab_negate_compat : "a\<in>Sab \<Longrightarrow> -a\<in>Sab" by (auto simp add:Sab_def)

lemma cx_negate_compat : 
  assumes "b\<in>ALL_CX"
  shows"-b\<in> ALL_CX"
  using assms by (auto simp add:ALL_CX_def Sab_def)

definition comp :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "comp N A = (if A\<subseteq> N then N-A else {})"

lemma comp_compat : assumes "A \<subseteq> N" shows "comp N A\<subseteq> N" by (auto simp add:comp_def)

lemma comp_subset_is_diff: assumes "A\<subseteq>N" shows "comp N A = N - A"
  using assms by (auto simp add:comp_def)

lemma comp_flip:
  assumes "a\<subseteq>b" and "a\<subseteq>N" and "b\<subseteq>N"
  shows "comp N b \<subseteq>comp N a"
  using assms comp_subset_is_diff
  by (metis Diff_mono order_refl)

definition dual_eff_fn :: "'a Nbd_Struct  \<Rightarrow> 'a eff_fn_type \<Rightarrow> 'a eff_fn_type" where
  "dual_eff_fn N f A = comp (World N) (f (comp (World N) A ))"

lemma dual_eff_fn_compat:
  fixes N :: "'a Nbd_Struct"
  and f:: "'a eff_fn_type"
  assumes "is_nbd_struct N" "f\<in>Pow (World N) \<rightarrow> Pow (World N)"
  shows "dual_eff_fn N f \<in> Pow (World N) \<rightarrow> Pow (World N)"
  using assms apply (auto simp add:effective_fn_of_def carrier_of_def is_nbd_struct_def)
    apply (simp add:dual_eff_fn_def)
  apply (metis Diff_subset Semantics.comp_def equals0D in_mono)
  done

lemma mono_dual_mono:
  fixes N :: "'a Nbd_Struct"
  and f:: "'a eff_fn_type"
assumes "f\<in> mono_of (World N)" and "f\<in> Pow (World N)\<rightarrow> Pow (World N)"
shows "dual_eff_fn N f \<in> mono_of (World N)"
  apply (simp add:dual_eff_fn_def mono_of_def)
  apply rule
  apply rule
  apply rule
proof -
  fix x y assume P1:" x \<subseteq> World N \<and> y \<subseteq> World N \<and> x \<subseteq> y"
  show "Semantics.comp (World N) (f (Semantics.comp (World N) x)) \<subseteq> Semantics.comp (World N) (f (Semantics.comp (World N) y))"
  proof -
    from P1 have P2:"Semantics.comp (World N) x\<subseteq> World N" using comp_compat by auto
    from P1 have P3:"Semantics.comp (World N) y\<subseteq> World N" using comp_compat by auto
    from comp_flip P1 have "comp (World N) y \<subseteq> comp (World N) x" by auto
    then have Q: "f (comp (World N) y) \<subseteq> f (comp (World N) x)" using assms P2 P3 by (auto simp add:mono_of_def)

    have P4:"f (comp (World N) x)\<subseteq> World N" using P2 assms by (auto simp add:mono_of_def)
    have P5:"f (comp (World N) y)\<subseteq> World N" using P3 assms by (auto simp add:mono_of_def)

    from P4 P5 Q show ?thesis using comp_flip[of "f (Semantics.comp (World N) y)" "f (Semantics.comp (World N) x)" "World N"] 
      by auto
  qed
qed

section \<open>The GLs extension of base \<close>

\<comment>\<open>World type is a cartesian product with context, instead of a ground set\<close>
type_synonym GLs_ground_type = "int \<times> cx"
type_synonym GLs_world_type = "GLs_ground_type world_type"
type_synonym GLs_sub_world_type = "GLs_ground_type sub_world_type"
type_synonym GLs_eff_fn_type = "GLs_sub_world_type \<Rightarrow> GLs_sub_world_type"


definition lift_game_interp :: "ground_type Nbd_Struct \<Rightarrow> (Atm_game \<Rightarrow> GLs_ground_type eff_fn_type)" where
"lift_game_interp N a (U::(int\<times>(int \<Rightarrow> int)) set)
  = (if U \<subseteq> World N \<times> ALL_CX 
    then {(w,c)\<in> World N \<times> ALL_CX. (c a = 0) \<and> (w \<in> (GameInterp N) a (fst ` U)) \<or> (c a = 1) \<and> ((w,c)\<in> U)}
    else {})"

lemma lift_game_interp_comat :
  fixes N :: "ground_type Nbd_Struct"
  and a :: "Atm_game"
assumes
  "is_nbd_struct N"
shows "lift_game_interp N a \<in> carrier_of (World N \<times> ALL_CX)"
  by (auto simp add:carrier_of_def lift_game_interp_def extension_def)

definition lift_prop_interp :: "ground_type Nbd_Struct \<Rightarrow> Atm_fml \<Rightarrow> GLs_ground_type sub_world_type" where
"lift_prop_interp N P = (PropInterp N P) \<times> ALL_CX"

definition GLs_lift_nbd :: "ground_type Nbd_Struct \<Rightarrow> GLs_ground_type Nbd_Struct" where
  "GLs_lift_nbd N = \<lparr> World=(World N)\<times>ALL_CX , 
    PropInterp = lift_prop_interp N,
    GameInterp = lift_game_interp N 
 \<rparr>"

definition sabo_comp :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_world_type \<Rightarrow> GLs_world_type" where
  "sabo_comp N A = (if A \<subseteq> World N then {(w,cx)\<in> World N. (w, dual_cx cx) \<notin> A } else {})"

lemma sabo_comp_compat : assumes "A\<subseteq> World N" shows "sabo_comp N A\<subseteq> World N" by (auto simp add:sabo_comp_def)

lemma sabo_comp_dm_andor : assumes "A\<subseteq>World N"
  and "B\<subseteq> World N"
shows "sabo_comp N (A \<inter> B) = sabo_comp N A \<union> sabo_comp N B" using assms by (auto simp add:sabo_comp_def)

lemma sabo_comp_dm_orand : assumes "A\<subseteq>World N"
and "B\<subseteq> World N"
shows "sabo_comp N (A \<union> B) = sabo_comp N A \<inter> sabo_comp N B" using assms by (auto simp add:sabo_comp_def)

lemma sabo_comp_dm_general_orand: assumes "\<Omega> \<subseteq> Pow (World N)"
  shows "ambient_inter (World N) {sabo_comp N A | A. A \<in> \<Omega>}=sabo_comp N (\<Union> \<Omega>)"
  apply (auto simp add:ambient_inter_def sabo_comp_def)
  by (metis (no_types, lifting) case_prod_conv empty_iff mem_Collect_eq)

lemma sabo_comp_dm_general_andor: assumes "\<Omega> \<subseteq> Pow (World N \<times> ALL_CX)"
  shows "sabo_comp (GLs_lift_nbd N) (ambient_inter (World (GLs_lift_nbd N)) \<Omega>) = \<Union> {sabo_comp (GLs_lift_nbd N) A| A. A\<in>\<Omega>}"
proof -
  consider (Emp) "\<Omega>={}" | (NEmp) "\<Omega>\<noteq>{}" by auto
  then show ?thesis
  proof cases
    case Emp
    then show ?thesis
    proof - 
      from Emp have LHS:"\<Union> {sabo_comp (GLs_lift_nbd N) A |A. A \<in> \<Omega>} = {}" by auto
      from Emp have RHS:"sabo_comp (GLs_lift_nbd N) (ambient_inter (World N\<times>ALL_CX) \<Omega>) = {}" 
        by (auto simp add: GLs_lift_nbd_def cx_negate_compat dual_cx_def ambient_inter_def sabo_comp_def)
      from LHS RHS show ?thesis by (simp add:GLs_lift_nbd_def)
    qed
  next
    case NEmp
    then show ?thesis
      apply (auto simp add: cx_negate_compat sabo_comp_def GLs_lift_nbd_def ambient_inter_def dual_cx_def)
      by (smt (verit, del_insts) Pow_def assms case_prodI mem_Collect_eq subset_iff)
  qed
qed

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
  show "\<And>a b aa ba. (a, b) \<in> A \<Longrightarrow> (aa, ba) \<in> A \<Longrightarrow> a \<notin> World N \<Longrightarrow> aa \<in> World N"
    using \<open>\<And>b a. (a, b) \<in> A \<Longrightarrow> a \<in> World N\<close> by blast
  show "\<And>a b aa ba. (a, b) \<in> A \<Longrightarrow> (aa, ba) \<in> A \<Longrightarrow> a \<notin> World N \<Longrightarrow> ba \<in> ALL_CX"
    using \<open>\<And>b a. (a, b) \<in> A \<Longrightarrow> a \<in> World N\<close> by blast
  show "\<And>a b aa ba. (a, b) \<in> A \<Longrightarrow> (aa, ba) \<in> A \<Longrightarrow> b \<notin> ALL_CX \<Longrightarrow> aa \<in> World N"
    using \<open>\<And>b a. (a, b) \<in> A \<Longrightarrow> a \<in> World N\<close> by auto
  show "\<And>a b aa ba. (a, b) \<in> A \<Longrightarrow> (aa, ba) \<in> A \<Longrightarrow> b \<notin> ALL_CX \<Longrightarrow> ba \<in> ALL_CX "
  using \<open>\<And>b a. (a, b) \<in> A \<Longrightarrow> b \<in> ALL_CX\<close> by blast
qed

lemma set_sabo_comp : "{A. A\<subseteq> (World N \<times> ALL_CX) \<and> P A} 
  = {sabo_comp (GLs_lift_nbd N) A| A. sabo_comp (GLs_lift_nbd N) A \<subseteq> (World N \<times>ALL_CX) \<and> P (sabo_comp (GLs_lift_nbd N) A)}"
  apply auto
proof -
  fix x assume P1:"x \<subseteq> World N \<times> ALL_CX" and P2:"P x"
  show
    "\<exists>A. x = sabo_comp (GLs_lift_nbd N) A \<and> sabo_comp (GLs_lift_nbd N) A \<subseteq> World N \<times> ALL_CX \<and> P (sabo_comp (GLs_lift_nbd N) A)"
  proof
    show "x = sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x)  \<and> sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x) \<subseteq> World N \<times> ALL_CX \<and> P (sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x))"
    proof
      from P1 show P3:"x = sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x)" using sabo_dbl_comp by auto
      show "sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x) \<subseteq> World N \<times> ALL_CX \<and> P (sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x))"
      proof 
        from P1 P3 show "sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x) \<subseteq> World N \<times> ALL_CX" by simp
        from P2 P3 show " P (sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x))" by simp
      qed
    qed
  qed
qed

lemma set_sabo_comp2 : "{A. A\<subseteq> (World N \<times> ALL_CX) \<and> P A} 
  = {sabo_comp (GLs_lift_nbd N) A| A. A \<subseteq> (World N \<times>ALL_CX) \<and> P (sabo_comp (GLs_lift_nbd N) A)}"
  apply auto
proof -
  fix x assume P1:"x \<subseteq> World N \<times> ALL_CX" and P2:"P x"
  show
    "\<exists>A. x = sabo_comp (GLs_lift_nbd N) A \<and> A \<subseteq> World N \<times> ALL_CX \<and> P (sabo_comp (GLs_lift_nbd N) A)"
  proof
    show "x = sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x)  \<and> (sabo_comp (GLs_lift_nbd N) x) \<subseteq> World N \<times> ALL_CX \<and> P (sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x))"
    proof
      from P1 show P3:"x = sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x)" using sabo_dbl_comp by auto
      show "(sabo_comp (GLs_lift_nbd N) x) \<subseteq> World N \<times> ALL_CX \<and> P (sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x))"
      proof 
        from P1 show "(sabo_comp (GLs_lift_nbd N) x) \<subseteq> World N \<times> ALL_CX" using sabo_comp_compat[of "x" "GLs_lift_nbd N"] by (auto simp add:GLs_lift_nbd_def)
        from P2 P3 show " P (sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) x))" by simp
      qed
    qed
  qed
next
  show "\<And>A a b. A \<subseteq> World N \<times> ALL_CX \<Longrightarrow> P (sabo_comp (GLs_lift_nbd N) A) \<Longrightarrow> (a, b) \<in> sabo_comp (GLs_lift_nbd N) A \<Longrightarrow> a \<in> World N"
    by (metis GLs_lift_nbd_def Nbd_Struct.select_convs(1) mem_Sigma_iff sabo_comp_compat subsetD)
next
  show "\<And>A a b. A \<subseteq> World N \<times> ALL_CX \<Longrightarrow> P (sabo_comp (GLs_lift_nbd N) A) \<Longrightarrow> (a, b) \<in> sabo_comp (GLs_lift_nbd N) A \<Longrightarrow> b \<in> ALL_CX "
  by (metis GLs_lift_nbd_def Nbd_Struct.select_convs(1) mem_Sigma_iff sabo_comp_compat subset_eq)
qed

lemma sabo_comp_homo : assumes "A\<subseteq>World N\<times> ALL_CX" and "B\<subseteq> World N\<times> ALL_CX"
shows "A\<subseteq>B \<longleftrightarrow> sabo_comp (GLs_lift_nbd N) B \<subseteq> sabo_comp (GLs_lift_nbd N) A"
  by (metis GLs_lift_nbd_def Nbd_Struct.select_convs(1) Un_Int_eq(1) sabo_comp_compat sabo_comp_dm_andor subset_Un_eq assms sabo_dbl_comp)

definition sabo_dual :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_eff_fn_type \<Rightarrow> GLs_eff_fn_type" where
  "sabo_dual N f A = sabo_comp N (f (sabo_comp N A))"

\<comment>\<open>function that substitutes atomic game "a" to Angelic control in context\<close>
definition GLs_game_subst :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_sub_world_type \<Rightarrow> Atm_game \<Rightarrow> GLs_sub_world_type" where
  "GLs_game_subst N A a = {(w,c)\<in> World N. (w,(subst_cx c a 1)) \<in> A}"

definition GLs_game_Dsubst :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_sub_world_type \<Rightarrow> Atm_game \<Rightarrow> GLs_sub_world_type" where
  "GLs_game_Dsubst N A a = {(w,c) \<in> World N. (w,(subst_cx c a (-1))) \<in> A}"

definition GLs_dual_eff_fn :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_eff_fn_type \<Rightarrow> GLs_eff_fn_type" where
"GLs_dual_eff_fn N f A = sabo_comp N (f (sabo_comp N A))"

lemma GLs_dual_eff_fn_compat:
  fixes N :: "ground_type Nbd_Struct"
    and f :: "GLs_eff_fn_type"
  assumes "is_nbd_struct N" "f\<in> Pow (World N \<times> ALL_CX) \<rightarrow> Pow (World N\<times> ALL_CX)" 
  shows "(GLs_dual_eff_fn (GLs_lift_nbd N) f) \<in> Pow (World N \<times> ALL_CX) \<rightarrow> Pow (World N\<times> ALL_CX)"
  apply (auto simp add:carrier_of_def GLs_lift_nbd_def GLs_dual_eff_fn_def sabo_comp_def)
    apply (metis (no_types, lifting) Nbd_Struct.select_convs(1) empty_def mem_Collect_eq mem_Sigma_iff old.prod.case)
   apply (metis (no_types, lifting) Nbd_Struct.select_convs(1) SigmaD2 empty_def mem_Collect_eq old.prod.case)
  done

lemma GLs_dual_eff_fn_demorgan : 
  assumes "A\<subseteq> World N" and "f\<in> Pow (World N) \<rightarrow> Pow (World N)" and "g\<in>Pow (World N) \<rightarrow> Pow (World N)"
  shows "GLs_dual_eff_fn N (\<lambda>x. f x \<inter> g x) A = GLs_dual_eff_fn N f A \<union> GLs_dual_eff_fn N g A"
proof -
  have "sabo_comp N A \<subseteq> World N" using assms(1) by (auto simp add:sabo_comp_def)
  then show ?thesis
    by (smt (verit) GLs_dual_eff_fn_def PiE Pow_iff assms(2,3) sabo_comp_dm_andor)
qed
  
lemma GLs_dual_eff_fn_composition:
  assumes "A\<subseteq> World N \<times> ALL_CX" and "f\<in> Pow (World N\<times>ALL_CX) \<rightarrow> Pow (World N\<times>ALL_CX)" and "g\<in>Pow (World N\<times>ALL_CX) \<rightarrow> Pow (World N\<times>ALL_CX)"
  shows "GLs_dual_eff_fn (GLs_lift_nbd N) (\<lambda>x. g (f x)) A = GLs_dual_eff_fn (GLs_lift_nbd N) g (GLs_dual_eff_fn (GLs_lift_nbd N) f A)"
  apply (simp add:GLs_dual_eff_fn_def)
proof -
  have "sabo_comp (GLs_lift_nbd N) A\<subseteq> World N \<times> ALL_CX" using sabo_comp_compat[of "A" "GLs_lift_nbd N"] assms(1) by (auto simp add:GLs_lift_nbd_def)
  then have "f (sabo_comp (GLs_lift_nbd N) A) \<subseteq> World (GLs_lift_nbd N)" using assms(2) by (auto simp add:GLs_lift_nbd_def)
  then have "f (sabo_comp (GLs_lift_nbd N) A) = sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) (f (sabo_comp (GLs_lift_nbd N) A)))" 
    using sabo_dbl_comp[of "f (sabo_comp (GLs_lift_nbd N) A)" "N"] by (auto simp add:GLs_lift_nbd_def)
  then show "sabo_comp (GLs_lift_nbd N) (g (f (sabo_comp (GLs_lift_nbd N) A))) =
    sabo_comp (GLs_lift_nbd N) (g (sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) (f (sabo_comp (GLs_lift_nbd N) A)))))"
    by auto
qed

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
  fixes B:: "'a set" and A::"'a set"
  assumes "A \<subseteq> B"
  shows "B-(B-A) = A"
  by (simp add: assms double_diff)

lemma union_mono_strong: "\<forall>A. mono f \<Longrightarrow> mono (union2 f A)"
  apply (simp add:mono_def union2_def)
  apply (auto)
  done

fun GLs_fml_sem :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_fml \<Rightarrow> GLs_sub_world_type"
 and GLs_game_sem :: "GLs_ground_type Nbd_Struct => GLs_game => GLs_eff_fn_type"
  where
  "GLs_fml_sem N (GLs_Atm_fml i) = PropInterp N i"
| "GLs_fml_sem N (GLs_Not fml) = (World N)-(GLs_fml_sem N fml)"
| "GLs_fml_sem N (GLs_Or f1 f2) = GLs_fml_sem N f1 \<union> GLs_fml_sem N f2"
| "GLs_fml_sem N (GLs_Mod g f) = (GLs_game_sem N g) (GLs_fml_sem N f)"

| "GLs_game_sem N (GLs_Atm_Game (Agl_gm i)) A = GameInterp N i A"
| "GLs_game_sem N (GLs_Atm_Game (Dmn_gm i)) A = GLs_dual_eff_fn N (GameInterp N i) A"
| "GLs_game_sem N (GLs_Test fml) A = (GLs_fml_sem N fml) \<inter> A "
| "GLs_game_sem N (GLs_Sabo (Agl_gm a)) A = GLs_game_subst N A a"
| "GLs_game_sem N (GLs_Sabo (Dmn_gm a)) A = GLs_game_Dsubst N A a"
| "GLs_game_sem N (GLs_Dual g) A = sabo_dual N (GLs_game_sem N g) A"
| "GLs_game_sem N (GLs_Choice a b) A = (GLs_game_sem N a A) \<union> (GLs_game_sem N b A)"
| "GLs_game_sem N (GLs_Seq a b) A = GLs_game_sem N a (GLs_game_sem N b A)"
| "GLs_game_sem N (GLs_Star a) A = lfp (\<lambda>B. A \<union> (GLs_game_sem N a B))"


lemma GLs_sem_wd:
  fixes N:: "ground_type Nbd_Struct"
  and f:: "GLs_fml"
  and g:: "GLs_game"
assumes "is_nbd_struct N"
shows "GLs_fml_sem (GLs_lift_nbd N) f \<subseteq> World N\<times> ALL_CX"
  "\<forall>A \<subseteq> (World N\<times> ALL_CX). GLs_game_sem (GLs_lift_nbd N) g A \<subseteq> (World N \<times> ALL_CX)"
proof (induction f and g)
  case (GLs_Atm_Game x)
  then show ?case
  proof (cases x)
    case (Agl_gm x1)
    then show ?thesis 
      using assms by (auto simp add:is_nbd_struct_def GLs_lift_nbd_def lift_game_interp_comat lift_game_interp_def)
  next
    case (Dmn_gm x2)
    then show ?thesis
      using assms GLs_dual_eff_fn_compat sabo_comp_compat
      by (auto simp add: sabo_comp_def is_nbd_struct_def GLs_dual_eff_fn_def GLs_lift_nbd_def lift_game_interp_comat lift_game_interp_def)
    qed
next
  case (GLs_Sabo x)
  then show ?case
  proof (cases x)
    case (Agl_gm x1)
    then show ?thesis 
    using assms apply (simp add:is_nbd_struct_def GLs_lift_nbd_def GLs_game_subst_def subst_cx_compat lift_game_interp_comat carrier_of_def)
    by blast
  next
    case (Dmn_gm x2)
    then show ?thesis 
    using assms apply (simp add:is_nbd_struct_def GLs_lift_nbd_def GLs_game_subst_def subst_cx_compat lift_game_interp_comat carrier_of_def)
    
  qed
next
  case (GLs_Dual x)
  then show ?case sorry
next
  case (GLs_Test x)
  then show ?case sorry
next
  case (GLs_Choice x1 x2)
  then show ?case sorry
next
  case (GLs_Seq x1 x2)
  then show ?case sorry
next
  case (GLs_Star x)
  then show ?case sorry
next
  case (GLs_Atm_fml x)
  then show ?case sorry
next
  case (GLs_Not x)
  then show ?case sorry
next
  case (GLs_Or x1 x2)
  then show ?case sorry
next
  case (GLs_Mod x1 x2)
  then show ?case sorry
qed

lemma GLs_And_sem : "GLs_fml_sem N (GLs_And f1 f2) = GLs_fml_sem N f1 \<inter> GLs_fml_sem N f2"
  unfolding GLs_And_def apply auto


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
| "GLs_ext_game_sem N (GLs_ext_DTest f) A = A \<union> sabo_comp N (GLs_ext_fml_sem N f)"
| "GLs_ext_game_sem N (GLs_ext_Choice g1 g2) A = GLs_ext_game_sem N g1 A \<union> GLs_ext_game_sem N g2 A"
| "GLs_ext_game_sem N (GLs_ext_DChoice g1 g2) A = GLs_ext_game_sem N g1 A \<inter> GLs_ext_game_sem N g2 A"
| "GLs_ext_game_sem N (GLs_ext_Seq g1 g2) A = GLs_ext_game_sem N g2 (GLs_ext_game_sem N g1 A)"
| "GLs_ext_game_sem N (GLs_ext_Star g) A = ambient_inter (World N) { B \<in> Pow (World N). A \<union> GLs_ext_game_sem N g B \<subseteq> B}"
| "GLs_ext_game_sem N (GLs_ext_Cross g) A = \<Union> { B \<in> Pow (World N). B \<subseteq> A \<inter> GLs_ext_game_sem N g B}"

lemma GLs_eff_fn_double_dual : 
  assumes "A \<subseteq> World N \<times> ALL_CX"
        "f \<in> Pow (World N \<times> ALL_CX) \<rightarrow> Pow (World N \<times> ALL_CX)"
  shows "GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_dual_eff_fn (GLs_lift_nbd N) f) A = f A"
  apply (simp add:GLs_dual_eff_fn_def sabo_dbl_comp assms)
proof -
  have "f A\<in> Pow (World N\<times> ALL_CX)" using assms by auto
  then show "sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) (f A)) = f A"
    by (simp add:sabo_dbl_comp assms GLs_dual_eff_fn_def)
qed


lemma carrier_lift_carrier : assumes "is_nbd_struct N"
  shows "GameInterp (GLs_lift_nbd N) g \<in> carrier_of (World (GLs_lift_nbd N))"
  apply (simp add:GLs_lift_nbd_def carrier_of_def extension_def)
  apply (auto simp add:lift_game_interp_def)
  done

lemma prop_lift_prop : assumes "is_nbd_struct N" 
  shows "PropInterp (GLs_lift_nbd N) p \<subseteq> World (GLs_lift_nbd N)"
  apply (simp add:GLs_lift_nbd_def lift_prop_interp_def)
  using assms apply (auto simp add:is_nbd_struct_def) done

lemma mono_lift_mono : 
  assumes "(GameInterp N g) \<in> mono_of (World N)"
  shows "(GameInterp (GLs_lift_nbd N) g) \<in> mono_of (World N\<times> ALL_CX)"
  apply (simp add: GLs_lift_nbd_def mono_of_def lift_game_interp_def)
  apply auto
proof - fix x y a b show "x \<subseteq> World N \<times> ALL_CX \<Longrightarrow>
       a \<in> World N \<Longrightarrow> y \<subseteq> World N \<times> ALL_CX \<Longrightarrow> x \<subseteq> y \<Longrightarrow> b \<in> ALL_CX \<Longrightarrow> b g = 0 \<Longrightarrow> a \<in> GameInterp N g (fst ` x) \<Longrightarrow> a \<in> GameInterp N g (fst ` y)"
  proof - assume P1:"x\<subseteq> World N\<times>ALL_CX" and P2:"y\<subseteq>World N\<times>ALL_CX" and P3:"x \<subseteq> y" and " b \<in> ALL_CX" and " b g = 0" and P4:"a \<in> GameInterp N g (fst ` x)"
    show "a \<in> GameInterp N g (fst ` y)"
    proof -
      from assms have Q:"\<forall>x y. x\<subseteq> World N \<and> y\<subseteq>World N \<and> x \<subseteq> y \<longrightarrow> GameInterp N g x \<subseteq> GameInterp N g y" by (simp add:mono_of_def)
      have "fst ` x\<subseteq> World N \<and> fst ` y\<subseteq> World N \<and> fst ` x \<subseteq> fst ` y" using P1 P2 P3 by auto
      then show ?thesis using P4 Q by auto
    qed
  qed
  fix x y a b
  assume P1:"x \<subseteq> World N \<times> ALL_CX " and "a \<in> World N" and P2:"y \<subseteq> World N \<times> ALL_CX" and P3:"x \<subseteq> y" and "b \<in> ALL_CX" and "b g = 0" and P4:"a \<in> GameInterp N g (fst ` x)"
  and "(a, b) \<notin> y"
  show "a \<in> GameInterp N g (fst ` y)"
  proof -
    from assms have Q:"\<forall>x y. x\<subseteq> World N \<and> y\<subseteq>World N \<and> x \<subseteq> y \<longrightarrow> GameInterp N g x \<subseteq> GameInterp N g y" by (simp add:mono_of_def)
    have "fst ` x\<subseteq> World N \<and> fst ` y\<subseteq> World N \<and> fst ` x \<subseteq> fst ` y" using P1 P2 P3 by auto
    then show ?thesis using P4 Q by auto
  qed
qed

lemma nbd_lift_nbd : assumes "is_nbd_struct N"
  shows "is_nbd_struct (GLs_lift_nbd N)"
  apply (simp add:is_nbd_struct_def)
proof 
  have "World N\<noteq>{} \<Longrightarrow> World (GLs_lift_nbd N) \<noteq> {}" apply (auto simp add:GLs_lift_nbd_def ALL_CX_nonempty) done
  then show "World (GLs_lift_nbd N) \<noteq> {}" using assms by (auto simp add:is_nbd_struct_def)

  from assms have P1:"\<forall>g. GameInterp N g \<in> carrier_of (World N) \<and> GameInterp N g \<in> mono_of (World N)"
    and P2:"\<forall>p. PropInterp N p \<subseteq> World N" by (auto simp add:is_nbd_struct_def)
  then have "
    (\<forall>g. GameInterp (GLs_lift_nbd N) g \<in> carrier_of (World (GLs_lift_nbd N)) \<and> GameInterp (GLs_lift_nbd N) g \<in> mono_of (World (GLs_lift_nbd N))) \<and>
    (\<forall>p. PropInterp (GLs_lift_nbd N) p \<subseteq> World (GLs_lift_nbd N))"
  proof - have R1:"(\<forall>g. GameInterp (GLs_lift_nbd N) g \<in> carrier_of (World (GLs_lift_nbd N)) \<and> GameInterp (GLs_lift_nbd N) g \<in> mono_of (World (GLs_lift_nbd N)))"
    proof fix g
      show "GameInterp (GLs_lift_nbd N) g \<in> carrier_of (World (GLs_lift_nbd N)) \<and> GameInterp (GLs_lift_nbd N) g \<in> mono_of (World (GLs_lift_nbd N))"
      proof -
        from P1 mono_lift_mono[of "N""g"] carrier_lift_carrier[of "N" "g"] show ?thesis using assms by (auto simp add:GLs_lift_nbd_def)
      qed
    qed

    have R2:"\<forall>p. PropInterp (GLs_lift_nbd N) p \<subseteq> World (GLs_lift_nbd N)" using assms P2 prop_lift_prop[of "N"] by auto
    show ?thesis using R1 R2 by auto
  qed
  thus "(\<forall>g. GameInterp (GLs_lift_nbd N) g \<in> carrier_of (World (GLs_lift_nbd N)) \<and> GameInterp (GLs_lift_nbd N) g \<in> mono_of (World (GLs_lift_nbd N))) \<and>
    (\<forall>p. PropInterp (GLs_lift_nbd N) p \<subseteq> World (GLs_lift_nbd N))" by simp
qed

lemma GLs_ext_sem_wd:
  fixes N:: "ground_type Nbd_Struct"
  and f:: "GLs_ext_fml"
  and g:: "GLs_ext_game"
assumes "is_nbd_struct N"
shows "GLs_ext_fml_sem (GLs_lift_nbd N) f \<subseteq> World N\<times> ALL_CX"
  "\<forall>A \<subseteq> (World N\<times> ALL_CX). GLs_ext_game_sem (GLs_lift_nbd N) g A \<subseteq> (World N \<times> ALL_CX)"
proof (induction f and g)
  case (GLs_ext_Atm_Game x)
  then show ?case
    using assms by (auto simp add:is_nbd_struct_def GLs_lift_nbd_def lift_game_interp_comat lift_game_interp_def)
next
  case (GLs_ext_Sabo x)
  then show ?case 
    using assms apply (simp add:is_nbd_struct_def GLs_lift_nbd_def GLs_game_subst_def subst_cx_compat lift_game_interp_comat carrier_of_def)
    by blast
next
  case (GLs_ext_DSabo x)
  then show ?case
    using assms apply (simp add:is_nbd_struct_def GLs_lift_nbd_def GLs_game_Dsubst_def subst_cx_compat lift_game_interp_comat carrier_of_def)
    by blast    
next
  case (GLs_ext_Dual x)
  then show ?case
  proof -
    assume P:"\<forall>A\<subseteq>World N \<times> ALL_CX. GLs_ext_game_sem (GLs_lift_nbd N) x A \<subseteq> World N \<times> ALL_CX"
    show "\<forall>A\<subseteq>World N \<times> ALL_CX. GLs_ext_game_sem (GLs_lift_nbd N) (GLs_ext_Dual x) A \<subseteq> World N \<times> ALL_CX"
      apply auto
    proof -
      have "GLs_ext_game_sem (GLs_lift_nbd N) x \<in> Pow (World N\<times>ALL_CX) \<rightarrow> Pow (World N\<times>ALL_CX)"
        using P by auto
      then have Q:"GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x)\<in>Pow (World N\<times>ALL_CX) \<rightarrow> Pow (World N\<times>ALL_CX)"
        using GLs_dual_eff_fn_compat assms by auto
      then show "\<And>A a b. A \<subseteq> World N \<times> ALL_CX \<Longrightarrow> (a, b) \<in> GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x) A \<Longrightarrow> a \<in> World N" by auto
      from Q show
        "\<And>A a b. A \<subseteq> World N \<times> ALL_CX \<Longrightarrow> (a, b) \<in> GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x) A \<Longrightarrow> b \<in> ALL_CX" by auto
    qed
  qed
next
  case (GLs_ext_Test x)
  then show ?case by auto
next
  case (GLs_ext_Choice x1 x2)
  then show ?case by simp
next
  case (GLs_ext_DChoice x1 x2)
  then show ?case by auto
next
  case (GLs_ext_DTest x)
  then show ?case by (auto simp add: GLs_lift_nbd_def sabo_comp_def)
next
  case (GLs_ext_Seq x1 x2)
  then show ?case by simp
next
  case (GLs_ext_Star x)
  then show ?case by (simp add: GLs_lift_nbd_def Inter_lower ambient_inter_def)
next
  case (GLs_ext_Cross x)
  then show ?case
    by (simp add: GLs_lift_nbd_def Sup_le_iff)
next
  case (GLs_ext_Atm_fml x)
  then show ?case using assms by (auto simp add:is_nbd_struct_def GLs_lift_nbd_def lift_prop_interp_def)
next
  case (GLs_ext_Not x)
  then show ?case by (auto simp add:GLs_lift_nbd_def sabo_comp_def)
next
  case (GLs_ext_Or x1 x2)
  then show ?case by simp
next
  case (GLs_ext_And x1 x2)
  then show ?case using GLs_ext_fml_sem.simps(4) by blast
next
  case (GLs_ext_Mod x1 x2)
  then show ?case by auto
qed

lemma GLs_syn_inversion_compat :
  fixes N:: "ground_type Nbd_Struct"
  and f:: "GLs_ext_fml"
  and g:: "GLs_ext_game"
  and A:: "GLs_ground_type set"
assumes isStruct: "is_nbd_struct N"
shows "GLs_ext_fml_sem (GLs_lift_nbd N) (GLs_syn_comp f) = sabo_comp (GLs_lift_nbd N) (GLs_ext_fml_sem (GLs_lift_nbd N) f)"
   "\<forall>A \<subseteq> (World N\<times> ALL_CX). GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual g) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) g) A"
proof (induction f and g)
  case (GLs_ext_Atm_Game x)
  then show ?case by (auto simp add: GLs_dual_eff_fn_def )
next
  case (GLs_ext_Sabo x)
  then show ?case
    by (auto simp add: assms
       GLs_lift_nbd_def  GLs_dual_eff_fn_def sabo_comp_def dual_cx_def GLs_game_subst_def GLs_game_Dsubst_def
      cx_double_neg subst_cx_compat cx_negate_compat)
next
  case (GLs_ext_DSabo x)
  then show ?case
    apply (auto simp add: assms
       GLs_lift_nbd_def  GLs_dual_eff_fn_def sabo_comp_def dual_cx_def GLs_game_subst_def GLs_game_Dsubst_def
      cx_double_neg subst_cx_compat cx_negate_compat)
    using cx_double_dual dual_cx_def subst_cx_compat apply force
    using cx_double_dual dual_cx_def subst_cx_compat by force
next
  case (GLs_ext_Dual x)
  then show ?case
  proof - 
    assume P1:"\<forall>A\<subseteq>World N \<times> ALL_CX. GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual x) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x) A"
    show " \<forall>A\<subseteq>World N \<times> ALL_CX.
       GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual (GLs_ext_Dual x)) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) (GLs_ext_Dual x)) A"
    proof fix A show "A \<subseteq> World N \<times> ALL_CX \<longrightarrow>
         GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual (GLs_ext_Dual x)) A =
         GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) (GLs_ext_Dual x)) A"
      proof assume P2:"A \<subseteq> World N \<times> ALL_CX"
         have "GLs_ext_game_sem (GLs_lift_nbd N) x \<in> Pow (World N\<times> ALL_CX) \<rightarrow> Pow (World N \<times> ALL_CX)"
           by (simp add: GLs_ext_sem_wd(2) nbd_lift_nbd[of "N"] assms(1))
         from P2 this GLs_eff_fn_double_dual[of "A""N""GLs_ext_game_sem (GLs_lift_nbd N) x"]
         show "GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual (GLs_ext_Dual x)) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) (GLs_ext_Dual x)) A"
           by (simp add: GLs_dual_eff_fn_def)
      qed
    qed
  qed
next
  case (GLs_ext_Test x)
  then show ?case
  proof -
    have "GLs_ext_fml_sem (GLs_lift_nbd N) x \<subseteq> World N\<times> ALL_CX" using GLs_ext_sem_wd assms by auto
    thus ?case using sabo_comp_dm_andor assms
    by (smt (verit, ccfv_threshold) GLs_dual_eff_fn_def GLs_ext_game_sem.simps(5,6) GLs_lift_nbd_def GLs_syn_dual.simps(5) Int_Un_eq(1) Nbd_Struct.select_convs(1)
        Un_Int_assoc_eq boolean_algebra.conj_zero_right sabo_comp_def sabo_dbl_comp sup.absorb_iff2)
  qed
next
  case (GLs_ext_Choice x1 x2)
  then show ?case
    using GLs_dual_eff_fn_def sabo_comp_def by force
next
  case (GLs_ext_DChoice x1 x2)
  then show ?case apply simp
  proof -
    assume Q1:"\<forall>A\<subseteq>World N \<times> ALL_CX. GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual x1) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x1) A" 
and Q2:"\<forall>A\<subseteq>World N \<times> ALL_CX. GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual x2) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x2) A" 
    show "\<forall>A\<subseteq>World N \<times> ALL_CX.
       GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x1) A \<union> GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x2) A =
       GLs_dual_eff_fn (GLs_lift_nbd N) (\<lambda>a. GLs_ext_game_sem (GLs_lift_nbd N) x1 a \<inter> GLs_ext_game_sem (GLs_lift_nbd N) x2 a) A"
      apply (rule)
      apply (rule)
    proof - fix A assume Q3:"A \<subseteq> World N \<times> ALL_CX"
      have P1:"GLs_ext_game_sem (GLs_lift_nbd N) x1 \<in> Pow (World N\<times>ALL_CX) \<rightarrow> Pow (World N\<times> ALL_CX)" 
        using assms(1) nbd_lift_nbd[of "N"] GLs_ext_sem_wd by (auto simp add:is_nbd_struct_def)
      have P2:"GLs_ext_game_sem (GLs_lift_nbd N) x2 \<in> Pow (World N\<times>ALL_CX) \<rightarrow> Pow (World N\<times> ALL_CX)" 
        using assms(1) nbd_lift_nbd[of "N"] GLs_ext_sem_wd by (auto simp add:is_nbd_struct_def)
      from P1 P2 Q3
      GLs_dual_eff_fn_demorgan[of "A""GLs_lift_nbd N" "GLs_ext_game_sem (GLs_lift_nbd N) x1" "GLs_ext_game_sem (GLs_lift_nbd N) x2"]
      show "GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x1) A \<union> GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x2) A =
         GLs_dual_eff_fn (GLs_lift_nbd N) (\<lambda>a. GLs_ext_game_sem (GLs_lift_nbd N) x1 a \<inter> GLs_ext_game_sem (GLs_lift_nbd N) x2 a) A"
      by (auto simp add:GLs_lift_nbd_def)
    qed
  qed
next
  case (GLs_ext_DTest x)
  then show ?case apply simp
    apply (simp add:GLs_dual_eff_fn_def) apply rule apply rule
  proof - fix A
    assume Q1:"GLs_ext_fml_sem (GLs_lift_nbd N) (GLs_syn_comp x) = sabo_comp (GLs_lift_nbd N) (GLs_ext_fml_sem (GLs_lift_nbd N) x)"
      and Q2:"A \<subseteq> World N \<times> ALL_CX"
    have P1:"GLs_ext_fml_sem (GLs_lift_nbd N) x \<subseteq> World N\<times> ALL_CX" using GLs_ext_sem_wd assms by auto
    have P2:"sabo_comp (GLs_lift_nbd N) A \<subseteq> World N\<times> ALL_CX" using Q2 sabo_comp_compat[of "A" "GLs_lift_nbd N"] GLs_lift_nbd_def by (auto)
    have P3: "sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) A) = A" using sabo_dbl_comp Q2 by auto
    have P4: "GLs_ext_fml_sem (GLs_lift_nbd N) x \<subseteq> World N\<times> ALL_CX" using assms GLs_ext_sem_wd(1) by auto
    from P4 have P5: "sabo_comp (GLs_lift_nbd N) (GLs_ext_fml_sem (GLs_lift_nbd N) x) \<subseteq> World N\<times> ALL_CX" 
      using sabo_comp_compat[of "GLs_ext_fml_sem (GLs_lift_nbd N) x" "GLs_lift_nbd N"] by (auto simp add:GLs_lift_nbd_def)
    have P6: "sabo_comp (GLs_lift_nbd N) 
                (sabo_comp (GLs_lift_nbd N) A \<union> sabo_comp (GLs_lift_nbd N) (GLs_ext_fml_sem (GLs_lift_nbd N) x))
      = sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) A) 
          \<inter> sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) (GLs_ext_fml_sem (GLs_lift_nbd N) x))"
      using P2 P5 sabo_comp_dm_orand[of "sabo_comp (GLs_lift_nbd N) A" "GLs_lift_nbd N" "sabo_comp (GLs_lift_nbd N) (GLs_ext_fml_sem (GLs_lift_nbd N) x)"]
      by (auto simp add:GLs_lift_nbd_def)
    then have P7: "sabo_comp (GLs_lift_nbd N) 
                (sabo_comp (GLs_lift_nbd N) A \<union> sabo_comp (GLs_lift_nbd N) (GLs_ext_fml_sem (GLs_lift_nbd N) x))
        = A \<inter> GLs_ext_fml_sem (GLs_lift_nbd N) x"
      using Q2 sabo_dbl_comp P4 by auto
    thus "A \<inter> GLs_ext_fml_sem (GLs_lift_nbd N) x =
         sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) A \<union> sabo_comp (GLs_lift_nbd N) (GLs_ext_fml_sem (GLs_lift_nbd N) x))" by auto
  qed
next
  case (GLs_ext_Seq x1 x2)
  then show ?case 
    apply simp 
    apply rule 
    apply rule
  proof - fix A assume
    P1:"\<forall>A\<subseteq>World N \<times> ALL_CX. GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual x1) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x1) A"
  and P2:"\<forall>A\<subseteq>World N \<times> ALL_CX. GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual x2) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x2) A"
  and Q1: "A \<subseteq> World N \<times> ALL_CX"
   show "GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual x2) (GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x1) A) =
         GLs_dual_eff_fn (GLs_lift_nbd N) (\<lambda>a. GLs_ext_game_sem (GLs_lift_nbd N) x2 (GLs_ext_game_sem (GLs_lift_nbd N) x1 a)) A"
      
   proof -
     have "GLs_ext_game_sem (GLs_lift_nbd N) x1 \<in> Pow (World N\<times> ALL_CX) \<rightarrow> Pow (World N\<times> ALL_CX)" 
       using assms nbd_lift_nbd GLs_ext_sem_wd by simp

     from Q1 sabo_comp_compat[of "A" "GLs_lift_nbd N"] GLs_ext_sem_wd(2)[of "N""x1"] assms 
       GLs_dual_eff_fn_compat[of "N" "GLs_ext_game_sem (GLs_lift_nbd N) x1" ]
     have P3:"GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x1) A \<subseteq> World N\<times>ALL_CX" 
       by blast

     from this P2 have "GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual x2) (GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x1) A) 
        = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x2) (GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x1) A)"
       by simp

     from GLs_dual_eff_fn_composition[of "A" "N" "GLs_ext_game_sem (GLs_lift_nbd N) x1" "GLs_ext_game_sem (GLs_lift_nbd N) x2"]
          GLs_ext_sem_wd(2)[of "N"]
          Q1 assms
     have "GLs_dual_eff_fn (GLs_lift_nbd N) (\<lambda>x. GLs_ext_game_sem (GLs_lift_nbd N) x2 (GLs_ext_game_sem (GLs_lift_nbd N) x1 x)) A =
    GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x2) (GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x1) A)"
       by auto

     then show ?thesis using P2 P3 by blast
   qed
  qed
next
  case (GLs_ext_Star x)
  then show ?case 
  proof -
    assume P:" \<forall>A\<subseteq>World N \<times> ALL_CX. GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual x) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x) A"
    show "\<forall>A\<subseteq>World N \<times> ALL_CX.
       GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual (GLs_ext_Star x)) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) (GLs_ext_Star x)) A"
      apply rule
    proof
      fix A assume P0:"A\<subseteq>World N \<times> ALL_CX"
      show "GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual (GLs_ext_Star x)) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) (GLs_ext_Star x)) A"
        apply (simp add:GLs_dual_eff_fn_def)
      proof -
        let ?LHS = " \<Union> {B. B \<subseteq> World (GLs_lift_nbd N) \<and> B \<subseteq> A \<and> B \<subseteq> GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual x) B}"
        let ?RHS = "sabo_comp (GLs_lift_nbd N)
     (ambient_inter (World (GLs_lift_nbd N)) {B. B \<subseteq> World (GLs_lift_nbd N) \<and> sabo_comp (GLs_lift_nbd N) A \<subseteq> B \<and> GLs_ext_game_sem (GLs_lift_nbd N) x B \<subseteq> B}) "
        let ?o = "{B. B \<subseteq> World (GLs_lift_nbd N) \<and> sabo_comp (GLs_lift_nbd N) A \<subseteq> B \<and> GLs_ext_game_sem (GLs_lift_nbd N) x B \<subseteq> B}"
        have "?o\<subseteq> Pow (World (GLs_lift_nbd N))" by auto
        then have "?o\<subseteq> Pow (World N\<times>ALL_CX)" by (simp add:GLs_lift_nbd_def)
        then have 
          R1:"?RHS = \<Union> {sabo_comp (GLs_lift_nbd N) B|B. B \<subseteq> World (GLs_lift_nbd N) \<and> sabo_comp (GLs_lift_nbd N) A \<subseteq> B \<and> GLs_ext_game_sem (GLs_lift_nbd N) x B \<subseteq> B}" 
          using sabo_comp_dm_general_andor[of "?o" "N"]
          by auto

        from P have L1:"?LHS = \<Union> {B. B \<subseteq> World (GLs_lift_nbd N) \<and> B \<subseteq> A \<and> B \<subseteq> GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x) B}"
          by (metis \<open>A \<subseteq> World N \<times> ALL_CX\<close> order_trans)
        also have "... = \<Union> {sabo_comp (GLs_lift_nbd N) B| B. B \<subseteq> World (GLs_lift_nbd N) 
          \<and> sabo_comp (GLs_lift_nbd N) B \<subseteq> A 
          \<and> sabo_comp (GLs_lift_nbd N) B \<subseteq> GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x) (sabo_comp (GLs_lift_nbd N) B)}"
          using set_sabo_comp2[of "N"] by (simp add: GLs_lift_nbd_def)
        also have "... = \<Union> {sabo_comp (GLs_lift_nbd N) B| B. B \<subseteq> World (GLs_lift_nbd N) 
          \<and> sabo_comp (GLs_lift_nbd N) A \<subseteq> B
          \<and> sabo_comp (GLs_lift_nbd N) B \<subseteq> GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x) (sabo_comp (GLs_lift_nbd N) B)}"
          using P0 GLs_lift_nbd_def sabo_comp_homo sabo_dbl_comp
          by (metis (lifting) Nbd_Struct.select_convs(1) sabo_comp_compat)
        also have "... = \<Union> {sabo_comp (GLs_lift_nbd N) B| B. B \<subseteq> World (GLs_lift_nbd N) 
          \<and> sabo_comp (GLs_lift_nbd N) A \<subseteq> B
          \<and> GLs_ext_game_sem (GLs_lift_nbd N) x B \<subseteq> B}"
          using sabo_dbl_comp sabo_comp_homo GLs_dual_eff_fn_def
          by (smt (verit, ccfv_SIG) Collect_cong GLs_lift_nbd_def GLs_ext_sem_wd(2) Nbd_Struct.select_convs(1) isStruct)
        finally have L2:"?LHS = \<Union> {sabo_comp (GLs_lift_nbd N) B| B. B \<subseteq> World (GLs_lift_nbd N) 
          \<and> sabo_comp (GLs_lift_nbd N) A \<subseteq> B
          \<and> GLs_ext_game_sem (GLs_lift_nbd N) x B \<subseteq> B}" by auto

        from L2 R1 show "?LHS=?RHS" by auto
      qed
    qed
  qed
next
  case (GLs_ext_Cross x)
  then show ?case 
  proof -
    assume P1:"\<forall>A\<subseteq>World N \<times> ALL_CX. GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual x) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x) A"
    show "\<forall>A\<subseteq>World N \<times> ALL_CX. GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual (GLs_ext_Cross x)) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) (GLs_ext_Cross x)) A"
      apply rule
    proof
      fix A assume P0:"A\<subseteq> World N\<times>ALL_CX"
      show "GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual (GLs_ext_Cross x)) A = GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) (GLs_ext_Cross x)) A"
        apply (simp add:GLs_dual_eff_fn_def)
      proof -
        let ?LHS = "ambient_inter (World (GLs_lift_nbd N)) {B. B \<subseteq> World (GLs_lift_nbd N) \<and> A \<subseteq> B \<and> GLs_ext_game_sem (GLs_lift_nbd N) (GLs_syn_dual x) B \<subseteq> B}"
        let ?RHS = "sabo_comp (GLs_lift_nbd N) (\<Union> {B. B \<subseteq> World (GLs_lift_nbd N) \<and> B \<subseteq> sabo_comp (GLs_lift_nbd N) A \<and> B \<subseteq> GLs_ext_game_sem (GLs_lift_nbd N) x B})"

        let ?o = "{B. B \<subseteq> World (GLs_lift_nbd N) \<and> B \<subseteq> sabo_comp (GLs_lift_nbd N) A \<and> B \<subseteq> GLs_ext_game_sem (GLs_lift_nbd N) x B}"
        have "?o \<subseteq> Pow (World (GLs_lift_nbd N))" by auto
        then have "?RHS = ambient_inter (World (GLs_lift_nbd N)) {sabo_comp (GLs_lift_nbd N) B|B. B \<subseteq> World (GLs_lift_nbd N) \<and> B \<subseteq> sabo_comp (GLs_lift_nbd N) A \<and> B \<subseteq> GLs_ext_game_sem (GLs_lift_nbd N) x B}"
          using sabo_comp_dm_general_orand[of "?o" "GLs_lift_nbd N"] by auto 
        also have "... = ambient_inter (World (GLs_lift_nbd N)) {B|B. B \<subseteq> World (GLs_lift_nbd N) 
                \<and>  sabo_comp (GLs_lift_nbd N) B \<subseteq> sabo_comp (GLs_lift_nbd N) A 
                \<and> sabo_comp (GLs_lift_nbd N) B \<subseteq> GLs_ext_game_sem (GLs_lift_nbd N) x (sabo_comp (GLs_lift_nbd N) B)}"
          using set_sabo_comp2 sabo_dbl_comp
          by (metis (lifting) GLs_lift_nbd_def Nbd_Struct.select_convs(1) sabo_comp_compat)
        also have "... = ambient_inter (World (GLs_lift_nbd N)) {B|B. B \<subseteq> World (GLs_lift_nbd N) 
                \<and>  A \<subseteq> B
                \<and> sabo_comp (GLs_lift_nbd N) B \<subseteq> GLs_ext_game_sem (GLs_lift_nbd N) x (sabo_comp (GLs_lift_nbd N) B)}"
          using sabo_comp_homo sabo_dbl_comp
          by (metis (lifting) GLs_lift_nbd_def Nbd_Struct.select_convs(1) P0)
        finally have R1: "?RHS = ambient_inter (World (GLs_lift_nbd N)) {B|B. B \<subseteq> World (GLs_lift_nbd N) 
                \<and>  A \<subseteq> B
                \<and> sabo_comp (GLs_lift_nbd N) B \<subseteq> GLs_ext_game_sem (GLs_lift_nbd N) x (sabo_comp (GLs_lift_nbd N) B)}" by auto
        
        from P1 have L1: "?LHS = ambient_inter (World (GLs_lift_nbd N)) {B. B \<subseteq> World (GLs_lift_nbd N) \<and> A \<subseteq> B \<and> GLs_dual_eff_fn (GLs_lift_nbd N) (GLs_ext_game_sem (GLs_lift_nbd N) x) B \<subseteq> B}"
          by (metis GLs_lift_nbd_def Nbd_Struct.select_convs(1))
        also have "... = ambient_inter (World (GLs_lift_nbd N)) {B. B \<subseteq> World (GLs_lift_nbd N) 
            \<and> A \<subseteq> B 
            \<and> sabo_comp (GLs_lift_nbd N) ((GLs_ext_game_sem (GLs_lift_nbd N) x) (sabo_comp (GLs_lift_nbd N) B)) \<subseteq> B}"
          using GLs_dual_eff_fn_def by auto
        also have "... = ambient_inter (World (GLs_lift_nbd N)) {B. B \<subseteq> World (GLs_lift_nbd N) 
            \<and> A \<subseteq> B 
            \<and> sabo_comp (GLs_lift_nbd N) B \<subseteq> GLs_ext_game_sem (GLs_lift_nbd N) x (sabo_comp (GLs_lift_nbd N) B)}"
          using sabo_dbl_comp sabo_comp_homo
          by (metis (no_types, lifting) GLs_lift_nbd_def GLs_ext_sem_wd(2) Nbd_Struct.select_convs(1) isStruct sabo_comp_compat)
        finally have L2:"?LHS = ambient_inter (World (GLs_lift_nbd N)) {B. B \<subseteq> World (GLs_lift_nbd N) 
            \<and> A \<subseteq> B 
            \<and> sabo_comp (GLs_lift_nbd N) B \<subseteq> GLs_ext_game_sem (GLs_lift_nbd N) x (sabo_comp (GLs_lift_nbd N) B)}" by auto

         from R1 L2 show "?LHS = ?RHS" by auto
      qed
    qed
  qed
next
  case (GLs_ext_Atm_fml x)
  then show ?case by auto
next
  case (GLs_ext_Not x)
  then show ?case apply simp 
  proof -
    have "GLs_ext_fml_sem (GLs_lift_nbd N) x \<subseteq> World N\<times>ALL_CX" using assms(1) GLs_ext_sem_wd(1)[of "N""x"] by auto
    then show "GLs_ext_fml_sem (GLs_lift_nbd N) x = sabo_comp (GLs_lift_nbd N) (sabo_comp (GLs_lift_nbd N) (GLs_ext_fml_sem (GLs_lift_nbd N) x))"
      using sabo_dbl_comp by auto
  qed
next
  case (GLs_ext_Or x1 x2)
  then show ?case
  using GLs_lift_nbd_def GLs_ext_sem_wd(1) isStruct sabo_comp_dm_orand by auto
next
  case (GLs_ext_And x1 x2)
  then show ?case
  using GLs_lift_nbd_def GLs_ext_sem_wd(1) isStruct sabo_comp_dm_andor by force
next
  case (GLs_ext_Mod x1 x2)
  then show ?case
  by (metis GLs_dual_eff_fn_def GLs_ext_fml_sem.simps(5) GLs_ext_sem_wd(1) GLs_syn_comp.simps(5) isStruct sabo_dbl_comp)
qed

section \<open>The RGL extension of base, with world structure un-modified\<close>
type_synonym RGL_var_type = "int"
type_synonym RGL_ground_type = "int"
type_synonym RGL_world_type = "RGL_ground_type world_type"
type_synonym RGL_sub_world_type = "RGL_ground_type sub_world_type"
type_synonym RGL_eff_fn_type = "RGL_sub_world_type \<Rightarrow> RGL_sub_world_type"

\<comment>\<open>RGL semantics\<close>
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
| "RGL_game_sem N I (RGL_Seq g1 g2) A = (RGL_game_sem N I g2) ((RGL_game_sem N I g1) A)"
| "RGL_game_sem N I (RGL_Rec x g) A =  (Lfp (World N) (\<lambda>u. (RGL_game_sem N (I(x:=u)) g))) A"

fun RGL_dualize_free :: "RGL_var_type \<Rightarrow> RGL_var_type RGL_ext_game \<Rightarrow> RGL_var_type RGL_ext_game" 
  and RGL_dualize_free_fml :: "RGL_var_type \<Rightarrow> RGL_var_type RGL_ext_fml \<Rightarrow> RGL_var_type RGL_ext_fml"
  where
"RGL_dualize_free x (RGL_ext_Var y) = (if x=y then (RGL_ext_Var_Dual x) else (RGL_ext_Var y))"
| "RGL_dualize_free x (RGL_ext_Atm_Game g) = RGL_ext_Atm_Game g"
| "RGL_dualize_free x (RGL_ext_Atm_Game_Dual g) = RGL_ext_Atm_Game_Dual g"
| "RGL_dualize_free x (RGL_ext_Var_Dual y) = (if x=y then (RGL_ext_Var x) else (RGL_ext_Var_Dual y))"
| "RGL_dualize_free x (RGL_ext_Rec y g) = (if x=y then (RGL_ext_Rec y g) else RGL_ext_Rec y (RGL_dualize_free x g))"
| "RGL_dualize_free x (RGL_ext_Rec_Dual y g) = (if x=y then (RGL_ext_Rec_Dual y g) else RGL_ext_Rec_Dual y (RGL_dualize_free x g))"
| "RGL_dualize_free x (RGL_ext_Choice g1 g2) = RGL_ext_Choice (RGL_dualize_free x g1) (RGL_dualize_free x g2)"
| "RGL_dualize_free x (RGL_ext_Choice_Dual g1 g2) = RGL_ext_Choice_Dual (RGL_dualize_free x g1) (RGL_dualize_free x g2)"
| "RGL_dualize_free x (RGL_ext_Seq g1 g2) = RGL_ext_Seq (RGL_dualize_free x g1) (RGL_dualize_free x g2)"
| "RGL_dualize_free x (RGL_ext_Test f) = RGL_ext_Test (RGL_dualize_free_fml x f)"
| "RGL_dualize_free x (RGL_ext_Test_Dual f) = RGL_ext_Test_Dual (RGL_dualize_free_fml x f)"
| "RGL_dualize_free_fml x (RGL_ext_Atm_fml P) = RGL_ext_Atm_fml P"
| "RGL_dualize_free_fml x (RGL_ext_Not f) = RGL_ext_Not (RGL_dualize_free_fml x f)"
| "RGL_dualize_free_fml x (RGL_ext_Or f1 f2)  = RGL_ext_Or (RGL_dualize_free_fml x f1) (RGL_dualize_free_fml x f2)"
| "RGL_dualize_free_fml x (RGL_ext_And f1 f2) = RGL_ext_And (RGL_dualize_free_fml x f1) (RGL_dualize_free_fml x f2) "
| "RGL_dualize_free_fml x (RGL_ext_Mod g f) = RGL_ext_Mod (RGL_dualize_free x g) (RGL_dualize_free_fml x f)"

lemma RGL_dualize_free_invo :
  fixes g :: " RGL_var_type RGL_ext_game"
  and f :: "RGL_var_type RGL_ext_fml"
shows "RGL_dualize_free x (RGL_dualize_free x g) = g" 
   "RGL_dualize_free_fml x (RGL_dualize_free_fml x f) = f"
   apply (induction g and f) 
   apply auto done

\<comment>\<open>syntactic dual and complement functions. The return value is automatically in normal form.\<close>
fun RGL_syn_comp :: "RGL_var_type RGL_ext_fml \<Rightarrow> RGL_var_type RGL_ext_fml"
and RGL_syn_dual :: "RGL_var_type RGL_ext_game \<Rightarrow> RGL_var_type RGL_ext_game" 
where
 "RGL_syn_comp (RGL_ext_Atm_fml P) = RGL_ext_Not (RGL_ext_Atm_fml P)"
| "RGL_syn_comp (RGL_ext_Not f) = f"
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
| "RGL_syn_dual (RGL_ext_Rec x g) = RGL_ext_Rec_Dual x (RGL_dualize_free x (RGL_syn_dual g))"
| "RGL_syn_dual (RGL_ext_Rec_Dual x g) = RGL_ext_Rec x (RGL_dualize_free x (RGL_syn_dual g))"

lemma RGL_dualize_free_comm : 
    fixes f::"RGL_var_type RGL_ext_fml"
  and g:: "RGL_var_type RGL_ext_game"
  and x:: "RGL_var_type"
  and y:: "RGL_var_type"
assumes "x \<noteq> y"
shows "RGL_dualize_free x (RGL_dualize_free y g) = RGL_dualize_free y (RGL_dualize_free x g)"
  "RGL_dualize_free_fml x (RGL_dualize_free_fml y f) = RGL_dualize_free_fml y (RGL_dualize_free_fml x f)"
apply (induction g and f) apply auto done


lemma RGL_syn_dual__dualize_free_comm :
  fixes f::"RGL_var_type RGL_ext_fml"
  and g:: "RGL_var_type RGL_ext_game"
shows "RGL_dualize_free_fml x (RGL_syn_comp f) = RGL_syn_comp (RGL_dualize_free_fml x f)"
    "RGL_dualize_free x (RGL_syn_dual g) = RGL_syn_dual (RGL_dualize_free x g)"
proof (induction f and g)
  case (RGL_ext_Atm_Game x)
  then show ?case by auto
next
  case (RGL_ext_Atm_Game_Dual x)
  then show ?case by auto
next
  case (RGL_ext_Var x)
  then show ?case by auto
next
  case (RGL_ext_Var_Dual x)
  then show ?case by auto
next
  case (RGL_ext_Test x)
  then show ?case by auto
next
  case (RGL_ext_Test_Dual x)
  then show ?case by auto
next
  case (RGL_ext_Choice x1 x2)
  then show ?case by auto
next
  case (RGL_ext_Choice_Dual x1 x2)
  then show ?case by auto
next
  case (RGL_ext_Seq x1 x2)
  then show ?case by auto
next
  case (RGL_ext_Rec y g)
  then show ?case 
    using RGL_dualize_free_comm(1)[of "x""y""g"] apply auto
    by (metis RGL_dualize_free_comm(1))
next
  case (RGL_ext_Rec_Dual y g)
  then show ?case
    using RGL_dualize_free_comm(1)[of "x""y""g"] apply auto
    by (metis RGL_dualize_free_comm(1))
next
  case (RGL_ext_Atm_fml x)
  then show ?case by auto
next
  case (RGL_ext_Not x)
  then show ?case by auto
next
  case (RGL_ext_Or x1 x2)
  then show ?case by auto
next
  case (RGL_ext_And x1 x2)
  then show ?case by auto
next
  case (RGL_ext_Mod x1 x2)
  then show ?case by auto
qed

lemma RGL_syn_invert_invo :
  fixes f::"RGL_var_type RGL_ext_fml"
  and g:: "RGL_var_type RGL_ext_game"
assumes "RGL_ext_fml_normal f"
shows "RGL_syn_comp (RGL_syn_comp f) = f"
    "RGL_syn_dual (RGL_syn_dual g) = g"
  using assms
proof (induction f and g)
  case (RGL_ext_Atm_Game x)
  then show ?case by auto
next
  case (RGL_ext_Atm_Game_Dual x)
  then show ?case by auto
next
  case (RGL_ext_Var x)
  then show ?case by auto
next
  case (RGL_ext_Var_Dual x)
  then show ?case by auto
next
  case (RGL_ext_Test x)
  then show ?case by auto
next
  case (RGL_ext_Test_Dual x)
  then show ?case by auto
next
  case (RGL_ext_Choice x1 x2)
  then show ?case by auto
next
  case (RGL_ext_Choice_Dual x1 x2)
  then show ?case by auto
next
  case (RGL_ext_Seq x1 x2)
  then show ?case by auto
next
  case (RGL_ext_Rec x g)
  then show ?case apply auto
    using RGL_syn_dual__dualize_free_comm(2) RGL_dualize_free_invo(1) by auto
next
  case (RGL_ext_Rec_Dual x1 x2)
  then show ?case 
    using RGL_syn_dual__dualize_free_comm(2) RGL_dualize_free_invo(1) by auto
next
  case (RGL_ext_Atm_fml P)
  then show ?case by auto
next
  case (RGL_ext_Not f')
  then show ?case 
    by (auto simp add: RGL_ext_fml_normal_def RGL_ext_fml_atomic_def)
next
  case (RGL_ext_Or f1 f2)
  then show ?case 
    apply auto
next
  case (RGL_ext_And x1 x2)
  then show ?case by auto
next
  case (RGL_ext_Mod x1 x2)
  then show ?case by auto
qed

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

\<comment>\<open>embed RGL formula and game into extended grammar
  The result is automatically in normal form since RGL_syn_dual pushes duality down recursively.
\<close>
fun RGL_fml_embed :: "RGL_var_type RGL_fml \<Rightarrow> RGL_var_type RGL_ext_fml"
and  RGL_game_embed :: "RGL_var_type RGL_game \<Rightarrow> RGL_var_type RGL_ext_game" where
 "RGL_fml_embed (RGL_Atm_fml f) = RGL_ext_Atm_fml f"
| "RGL_fml_embed (RGL_Not f) = RGL_ext_Not (RGL_fml_embed f)"
| "RGL_fml_embed (RGL_Or f1 f2) = RGL_ext_Or (RGL_fml_embed f1) (RGL_fml_embed f2)"
| "RGL_fml_embed (RGL_Mod g f) = RGL_ext_Mod (RGL_game_embed g) (RGL_fml_embed f)"
| "RGL_game_embed (RGL_Atm_Game a) = RGL_ext_Atm_Game a"
| "RGL_game_embed (RGL_Var x) = RGL_ext_Var x"
| "RGL_game_embed (RGL_Dual g) = RGL_syn_dual (RGL_game_embed g)"
| "RGL_game_embed (RGL_Test fl) = RGL_ext_Test (RGL_fml_embed fl)"
| "RGL_game_embed (RGL_Choice g1 g2) = RGL_ext_Choice (RGL_game_embed g1) (RGL_game_embed g2)"
| "RGL_game_embed (RGL_Seq g1 g2) = RGL_ext_Seq (RGL_game_embed g1) (RGL_game_embed g2)"
| "RGL_game_embed (RGL_Rec x g) = RGL_ext_Rec x (RGL_game_embed g)"

lemma RGL_even_dual_syn_dual: fixes
  g:: "RGL_var_type RGL_game" and
  f:: "RGL_var_type RGL_fml" and
  x:: "RGL_var_type"
assumes "RGL_even_dual False x g" and "RGL_game_valid g"
shows "RGL_ext_game_no_dual x (RGL_syn_dual (RGL_game_embed g))" "True"
  using assms
proof (induction g and f)
  case (RGL_Atm_Game x)
  then show ?case by auto
next
  case (RGL_Var x)
  then show ?case by auto
next
  case (RGL_Dual g)
  then show ?case apply simp
  proof - 
  qed
next
  case (RGL_Test x)
  then show ?case sorry
next
  case (RGL_Choice x1 x2)
  then show ?case sorry
next
  case (RGL_Seq x1 x2)
  then show ?case sorry
next
  case (RGL_Rec x1 x2)
  then show ?case sorry
next
  case (RGL_Atm_fml x)
  then show ?case sorry
next
  case (RGL_Not x)
  then show ?case sorry
next
  case (RGL_Or x1 x2)
  then show ?case sorry
next
  case (RGL_Mod x1 x2)
  then show ?case sorry
qed

\<comment>\<open> When g = rx.h, RGL_game_embed h is no free dual on x.\<close>
lemma RGL_Rec_embed_no_dual: 
  fixes
    h :: "RGL_var_type RGL_game"
    and x :: "RGL_var_type"
    and f :: "RGL_var_type RGL_fml"
  assumes "RGL_even_dual True x h"
  shows "RGL_ext_game_no_dual x (RGL_game_embed h)" "True"
  using assms
proof (induction h and f)
  case (RGL_Atm_Game x)
  then show ?case by auto
next
  case (RGL_Var x)
  then show ?case by auto
next
  case (RGL_Dual g)
  then show ?case
    apply (auto)
next
  case (RGL_Test x)
  then show ?case sorry
next
  case (RGL_Choice x1 x2)
  then show ?case sorry
next
  case (RGL_Seq x1 x2)
  then show ?case sorry
next
  case (RGL_Rec x1 x2)
  then show ?case sorry
next
  case (RGL_Atm_fml x)
  then show ?case sorry
next
  case (RGL_Not x)
  then show ?case sorry
next
  case (RGL_Or x1 x2)
  then show ?case sorry
next
  case (RGL_Mod x1 x2)
  then show ?case sorry
qed

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

definition RGL_ext_fixpoint_op :: "RGL_ground_type Nbd_Struct \<Rightarrow> RGL_var_type val \<Rightarrow> RGL_var_type \<Rightarrow> RGL_var_type RGL_ext_game \<Rightarrow> RGL_eff_fn_type \<Rightarrow> RGL_eff_fn_type" where
  "RGL_ext_fixpoint_op N I x g u = RGL_ext_game_sem N (I(x:=u)) g"

definition RGL_fixpoint_op :: "RGL_ground_type Nbd_Struct \<Rightarrow> RGL_var_type val \<Rightarrow> RGL_var_type \<Rightarrow> RGL_var_type RGL_game \<Rightarrow> RGL_eff_fn_type \<Rightarrow> RGL_eff_fn_type" where
  "RGL_fixpoint_op N I x g u = RGL_game_sem N (I(x:=u)) g"

lemma RGL_ext_game_sem_wd :
  fixes N :: "RGL_ground_type Nbd_Struct"
  and I :: "RGL_var_type val"
assumes "is_nbd_struct N"
    and "is_val N I"
  shows
    "(RGL_ext_fml_sem N I f) \<subseteq> (World N)"
    " \<forall>A \<subseteq> (World N).(RGL_ext_game_sem N I g) A \<subseteq> (World N)"
proof (induction f and g)
  case (RGL_ext_Atm_Game x)
  then show ?case using assms by (auto simp add:is_nbd_struct_def carrier_of_def)
next
  case (RGL_ext_Atm_Game_Dual x)
  then show ?case 
    using assms apply ( simp )
    using dual_eff_fn_compat[of "N" "GameInterp N x"] assms 
      apply (auto simp add:is_nbd_struct_def carrier_of_def)
    done
next
  case (RGL_ext_Var x)
  then show ?case 
    using assms(2) apply (auto simp add:is_val_def effective_fn_of_def)
    done
next
  case (RGL_ext_Var_Dual x)
  then show ?case 
    using assms dual_eff_fn_compat[of "N" "I x"] 
    apply (auto simp add:is_val_def effective_fn_of_def)
    done
next
  case (RGL_ext_Test x)
  then show ?case using assms by (auto simp add:is_nbd_struct_def)
next
  case (RGL_ext_Test_Dual x)
  then show ?case using assms
    by (simp add: is_nbd_struct_def Semantics.comp_def dual_eff_fn_def)
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
  then show ?case by (simp add:Lfp_def ambient_inter_def)
next
  case (RGL_ext_Rec_Dual x1 x2)
  then show ?case 
    apply (simp add:Gfp_def is_nbd_struct_def Gfp_family_def carrier_of_def)
    by blast
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

lemma RGL_interp_subst_is_monotone_op:
  fixes N :: "RGL_ground_type Nbd_Struct"
     and   I :: "RGL_var_type val"
     and   g :: "RGL_var_type RGL_game"
     and  f :: "RGL_var_type RGL_fml"
     and  x:: "RGL_var_type"
  assumes "is_nbd_struct N" and "is_val N I" and " RGL_even_dual True x g"
  shows "RGL_fixpoint_op N I x g \<in> monotone_op_of (World N)" 
        "True"
  using assms(3)
proof (induction g and f)
  case (RGL_Atm_Game x)
  then show ?case
    using assms apply (simp add:RGL_fixpoint_op_def)
    apply (simp add:carrier_of_def is_nbd_struct_def is_val_def effective_fn_of_def fun_le_def monotone_op_of_def)
    done
next
  case (RGL_Var x)
  then show ?case
    using assms apply (auto simp add:  RGL_fixpoint_op_def monotone_op_of_def effective_fn_of_def is_val_def is_nbd_struct_def carrier_of_def)
    using mono_dual_mono[of "GameInterp N x" "N"] apply auto
    using fun_le_def by blast
next
  case (RGL_Dual g')
  then show ?case
next
  case (RGL_Test x)
  then show ?case sorry
next
  case (RGL_Choice x1 x2)
  then show ?case sorry
next
  case (RGL_Seq x1 x2)
  then show ?case sorry
next
  case (RGL_Rec x1 x2)
  then show ?case sorry
next
  case (RGL_Atm_fml x)
  then show ?case sorry
next
  case (RGL_Not x)
  then show ?case sorry
next
  case (RGL_Or x1 x2)
  then show ?case sorry
next
  case (RGL_Mod x1 x2)
  then show ?case sorry
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