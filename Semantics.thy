theory Semantics
imports
  "Syntax"
  
begin
\<comment>\<open>We realise the semantics of GL, GLs, RGL, FLC, Lmu, LStar.\<close>

section \<open>Base defs: nbd structs, ground types, contexts, valuations\<close>

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
    (\<forall>G::atm_games. \<forall>g\<in>G. mono (GameInterp S g))
  \<and> (\<forall>G::atm_games. \<forall>g\<in>G. \<forall>A\<subseteq>(World S). (GameInterp S g A) \<subseteq> (World S))
  \<and> (\<forall>P::atm_fmls. \<forall>p\<in>P. (PropInterp S p) \<subseteq> (World S))"

\<comment>\<open>valuation\<close>
type_synonym 'a val = "var_type \<Rightarrow> 'a eff_fn_type"

definition is_val :: "'a Nbd_Struct \<Rightarrow> 'a val \<Rightarrow> bool" where
  "is_val S f \<equiv> \<forall>V::var_set_type. \<forall>i\<in>V. (mono (f i)) \<and> (\<forall>A\<subseteq> (World S). (f i A) \<subseteq> (World S))"

\<comment>\<open>context\<close>
definition Sab :: "int set" where
  "Sab = {-1,0,1}"

type_synonym cx = "Atm_game \<Rightarrow> int"

definition is_cx :: "cx \<Rightarrow> bool" where
  "is_cx C \<equiv> \<forall>g::Atm_game. C g\<in>Sab"

definition dual_cx :: "cx \<Rightarrow> cx" where
  "dual_cx cx = -cx"

fun subst_cx :: "cx \<Rightarrow> Atm_game \<Rightarrow> int \<Rightarrow> cx" where
  "subst_cx f a i b = (if a=b then i else f b)"

definition dual_eff_fn :: "'a set \<Rightarrow> 'a eff_fn_type \<Rightarrow> 'a eff_fn_type" where
  "dual_eff_fn X f A = X-(f(X-A))"

section \<open>The GLs extension of base \<close>

\<comment>\<open>World type is a cartesian product with context, instead of a ground set\<close>
type_synonym GLs_ground_type = "int \<times> cx"
type_synonym GLs_world_type = "GLs_ground_type world_type"
type_synonym GLs_sub_world_type = "GLs_ground_type sub_world_type"
type_synonym GLs_eff_fn_type = "GLs_sub_world_type \<Rightarrow> GLs_sub_world_type"

definition sabo_compl :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_world_type \<Rightarrow> GLs_world_type" where
  "sabo_compl N A = {(w,cx). (w,dual_cx cx)\<notin> A }"

definition sabo_dual :: "GLs_ground_type Nbd_Struct \<Rightarrow> GLs_eff_fn_type \<Rightarrow> GLs_eff_fn_type" where
  "sabo_dual N f A = sabo_compl N (f (sabo_compl N A))"

\<comment>\<open>function that substitutes atomic game "a" to Angelic control in context\<close>
definition GLs_game_subst :: "GLs_sub_world_type \<Rightarrow> Atm_game \<Rightarrow> GLs_sub_world_type" where
  "GLs_game_subst A a = {(w,c). (w,(subst_cx c a 1)) \<in> A}"

definition union :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "union A B = A\<union>B"

lemma union_mono : "\<forall>A::'a set. mono (union A)"
  apply (simp add:mono_def union_def)
  apply (auto)
  done

definition union2 :: "('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "union2 f A B = A \<union> f(B)"

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
| "GLs_game_sem N (GLs_Atm_Game i) A = GameInterp N i A"
| "GLs_game_sem N (GLs_Test fml) A = (GLs_fml_sem N fml) \<inter> A "
| "GLs_game_sem N (GLs_Sabo a) A = GLs_game_subst A a"
| "GLs_game_sem N (GLs_Dual g) A = sabo_dual N (GLs_game_sem N g) A"
| "GLs_game_sem N (GLs_Choice a b) A = (GLs_game_sem N a A) \<union> (GLs_game_sem N b A)"
| "GLs_game_sem N (GLs_Seq a b) A = GLs_game_sem N a (GLs_game_sem N b A)"
| "GLs_game_sem N (GLs_Star a) A = lfp (\<lambda>B. A \<union> (GLs_game_sem N a B))"

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
| "RGL_game_sem N I (RGL_Dual g) A = (dual_eff_fn (World N) (RGL_game_sem N I g)) A"
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



end