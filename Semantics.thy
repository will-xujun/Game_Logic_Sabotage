theory Semantics
imports
  "Syntax"
  
begin
\<comment>\<open>We realise the semantics of GL, GLs, RGL, FLC, Lmu, LStar.\<close>

type_synonym world_type = "int set"
type_synonym sub_world_type = "int set"
type_synonym eff_fn_type = "sub_world_type \<Rightarrow> sub_world_type"

type_synonym atm_fmls = "Atm_fml set"
type_synonym atm_games = "Atm_game set"
type_synonym var_set_type = "int set"
type_synonym var_type = "int"

locale mono_nbd =
  fixes
    World :: "'a set"
  and  PropInterp :: "Atm_fml \<Rightarrow> 'a set"
  and  GameInterp :: "Atm_game \<Rightarrow> 'a set \<Rightarrow> 'a set"
assumes
  wd_prop:  "\<forall>P::atm_fmls. \<forall>p\<in>P. (PropInterp p) \<subseteq> World"
and 
  wd_game: "(\<forall>G::atm_games. \<forall>g\<in>G. mono (GameInterp g))
  \<and> (\<forall>G::atm_games. \<forall>g\<in>G. \<forall>A\<subseteq>World. (GameInterp g A) \<subseteq> World)"


\<comment>\<open>notion of monotone neighbourhood structure\<close>
record Nbd_Struct = 
  World :: world_type
  PropInterp :: "Atm_fml \<Rightarrow> sub_world_type"
  GameInterp :: "Atm_game \<Rightarrow> eff_fn_type"

\<comment>\<open>use a predicate to ensure monotone nbd structure is defined correctly.\<close>
definition is_nbd_struct :: "Nbd_Struct \<Rightarrow> bool" where
  "is_nbd_struct S \<equiv> 
    (\<forall>G::atm_games. \<forall>g\<in>G. mono (GameInterp S g))
  \<and> (\<forall>G::atm_games. \<forall>g\<in>G. \<forall>A\<subseteq>(World S). (GameInterp S g A) \<subseteq> (World S))
  \<and> (\<forall>P::atm_fmls. \<forall>p\<in>P. (PropInterp S p) \<subseteq> (World S))"

\<comment>\<open>notion of valuation\<close>
type_synonym val = "var_type \<Rightarrow> sub_world_type \<Rightarrow> sub_world_type"

definition is_val :: "Nbd_Struct \<Rightarrow> val \<Rightarrow> bool" where
  "is_val S f \<equiv> \<forall>V::var_set_type. \<forall>i\<in>V. (mono (f i)) \<and> (\<forall>A\<subseteq> (World S). (f i A) \<subseteq> (World S))"

\<comment>\<open>notion of context\<close>
definition Sab :: "int set" where
  "Sab = {-1,0,1}"

type_synonym cx = "Atm_game \<Rightarrow> int"

definition is_cx :: "cx \<Rightarrow> bool" where
  "is_cx C \<equiv> \<forall>g::Atm_game. C g\<in>Sab"

definition dual_cx :: "cx \<Rightarrow> cx" where
  "dual_cx cx = -cx"

fun subst_cx :: "cx \<Rightarrow> Atm_game \<Rightarrow> int \<Rightarrow> cx" where
  "subst_cx cx a i = cx[a \<mapsto> i]"

\<comment>\<open>semantics for GLs fmls and games\<close>

\<comment>\<open>take world_type product with contexts\<close>
type_synonym GLs_ground_type = "int \<times> cx"
type_synonym GLs_eff_fn_type = "GLs_ground_type set \<Rightarrow> GLs_ground_type set"

definition sabo_compl :: "Nbd_Struct \<Rightarrow> GLs_ground_type set \<Rightarrow> GLs_ground_type set" where
  "sabo_compl N A = {(w,cx). (w,dual_cx cx)\<notin> A }"

definition sabo_dual :: "Nbd_Struct \<Rightarrow> GLs_eff_fn_type \<Rightarrow> GLs_eff_fn_type" where
  "sabo_dual N f A = sabo_compl N (f (sabo_compl N A))"

definition GLs_game_subst :: "GLs_ground_type set \<Rightarrow> "

fun GLs_fml_sem :: "Nbd_Struct \<Rightarrow> GLs_fml \<Rightarrow> GLs_ground_type set" 
 and GLs_game_sem :: "Nbd_Struct => GLs_game => GLs_eff_fn_type"
  where
  "GLs_fml_sem N (GLs_Atm_fm i) = PropInterp N i"
| "GLs_fml_sem N (GLs_Not fml) = (World N)-(GLs_fml_sem N fml)"
| "GLs_fml_sem N (GLs_Or) f1 f2 = GLs_fml_sem N f1 \<union> GLs_fml_sem N f2"
| "GLs_fml_sem N (GLs_Mod) g f = (GLs_game_sem N g) (GLs_fml_sem N f)"
| "GLs_game_sem N (GLs_Atm_Game i) = GameInterp N i"
| "GLs_game_sem N (GLs_Test fml) A = (GLs_fml_sem N fml) \<inter> A "
| "GLs_game_sem N (GLs_Sabo a) = GLs_game_subst A g"
| "GLs_game_sem N (GLs_Dual g) = sabo_dual N (GLs_game_sem N g)"
| "GLs_game_sem N (GLs_Choice a b) A = (GLs_game_sem N a A) \<union> (GLs_game_sem N b A)"
| "GLs_game_sem N (GLs_Seq a b) A = GLs_game_sem N a (GLs_game_sem N b A)"
| "GLs_game_sem N (Star a) A = \<mu>B.(A \<union> (GLs_game_sem N a B))"


end