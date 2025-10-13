theory Syntax
imports
  Complex_Main
begin 

\<comment>\<open>We realise the syntax of GL, GLs, RGL, FLC, Lmu, LStar.
  Separable formulas of Lmu should be realised as an inductive property.
  right-linearity in RGL is also an inductive property. \<close>

type_synonym Atm_game = "int"
type_synonym Atm_fml = "int"

datatype atm_gm = Agl_gm Atm_game | Dmn_gm Atm_game

datatype GL_game = 
  GL_Atm_Game "Atm_game"
  | GL_Dual "GL_game"
  | GL_Test "GL_fml"
  | GL_Choice "GL_game" "GL_game"
  | GL_Seq "GL_game" "GL_game"
  | GL_Star "GL_game"
and GL_fml = 
    GL_Atm_fml "Atm_fml"
  | GL_Not "GL_fml"
  | GL_Or "GL_fml" "GL_fml"
  | GL_Mod "GL_game" "GL_fml"

datatype GLs_game =
  GLs_Atm_Game "atm_gm"
  | GLs_Sabo "atm_gm"
  | GLs_Dual "GLs_game"
  | GLs_Test "GLs_fml"
  | GLs_Choice "GLs_game" "GLs_game"
  | GLs_Seq "GLs_game" "GLs_game"
  | GLs_Star "GLs_game"
and GLs_fml = 
  GLs_Atm_fml "Atm_fml"
  | GLs_Not "GLs_fml"
  | GLs_Or "GLs_fml" "GLs_fml"
  | GLs_Mod "GLs_game" "GLs_fml"

definition GLs_And where "GLs_And A B = GLs_Not (GLs_Or (GLs_Not A) (GLs_Not B))"

definition GLs_DChoice where "GLs_DChoice g1 g2 = GLs_Dual (GLs_Choice (GLs_Dual g1) (GLs_Dual g2))"

definition GLs_DTest where "GLs_DTest f = GLs_Dual (GLs_Test f)"

definition GLs_DStar where "GLs_DStar g = GLs_Dual (GLs_Star (GLs_Dual g))"

fun GLs_sy_comp :: "GLs_fml \<Rightarrow> GLs_fml" 
  and GLs_sy_dual :: "GLs_game \<Rightarrow> GLs_game" where
  "GLs_sy_comp (GLs_Atm_fml a) = GLs_Not (GLs_Atm_fml a)"
|   "GLs_sy_comp (GLs_Not f) = f"
|   "GLs_sy_comp (GLs_Or f1 f2) = GLs_And (GLs_sy_comp f1) (GLs_sy_comp f2)"
|   "GLs_sy_comp (GLs_Mod g f) = GLs_Mod (GLs_sy_dual g) (GLs_sy_comp f)"

|   "GLs_sy_dual (GLs_Atm_Game (Agl_gm a)) = GLs_Atm_Game (Dmn_gm a)"
|   "GLs_sy_dual (GLs_Atm_Game (Dmn_gm a)) = GLs_Atm_Game (Agl_gm a)"
|   "GLs_sy_dual (GLs_Sabo (Agl_gm a)) = GLs_Sabo (Dmn_gm a)"
|   "GLs_sy_dual (GLs_Sabo (Dmn_gm a)) = GLs_Sabo (Agl_gm a)"
|   "GLs_sy_dual (GLs_Dual g) = g"
|   "GLs_sy_dual (GLs_Test f) = GLs_DTest f"
|   "GLs_sy_dual (GLs_Choice g1 g2) = GLs_DChoice (GLs_sy_dual g1) (GLs_sy_dual g2)"
|   "GLs_sy_dual (GLs_Seq g1 g2) = GLs_Seq (GLs_sy_dual g1) (GLs_sy_dual g2)"
|   "GLs_sy_dual (GLs_Star g) = GLs_DStar (GLs_sy_dual g)"

datatype 'c RGL_game =
  RGL_Atm_Game "atm_gm"
  | RGL_Var 'c
  | RGL_Dual "'c RGL_game"
  | RGL_Test "'c RGL_fml" 
  | RGL_Choice "'c RGL_game" "'c RGL_game"
  | RGL_Seq "'c RGL_game" "'c RGL_game"
  | RGL_Rec 'c "'c RGL_game"
and
 'c RGL_fml = 
    RGL_Atm_fml "Atm_fml"
  | RGL_Not "'c RGL_fml"
  | RGL_Or "'c RGL_fml" "'c RGL_fml"
  | RGL_Mod "'c RGL_game" "'c RGL_fml"

text \<open>Induction principles for RGL games and fmls\<close>

lemma RGL_game_induct [case_names RGL_Atm_Game RGL_Var RGL_Dual RGL_Test RGL_Choice RGL_Seq RGL_Rec]:
  "(\<And>a. P (RGL_Atm_Game a))
    \<Longrightarrow> (\<And>x. P (RGL_Var x))
    \<Longrightarrow> (\<And>g. P g \<Longrightarrow> P (RGL_Dual g))
    \<Longrightarrow> (\<And>f. P (RGL_Test f))
    \<Longrightarrow> (\<And>g1 g2. P g1 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_Choice g1 g2))
    \<Longrightarrow> (\<And>g1 g2. P g1 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_Seq g1 g2))
    \<Longrightarrow> (\<And>x g. P g \<Longrightarrow> P (RGL_Rec x g))
    \<Longrightarrow> P \<alpha>
  "
  by (induction rule: RGL_game.induct) (auto)


lemma RGL_fml_induct [case_names Atm Not Or Mod]:
  "(\<And>a. P (RGL_Atm_fml a))
  \<Longrightarrow> (\<And>f. P f \<Longrightarrow> P (RGL_Not f))
  \<Longrightarrow> (\<And>f1 f2. P f1 \<Longrightarrow> P f2 \<Longrightarrow> P (RGL_Or f1 f2))
  \<Longrightarrow> (\<And>g f. P f \<Longrightarrow> P (RGL_Mod g f))
  \<Longrightarrow> P \<beta>"
  using RGL_fml.induct[where ?P1.0="\<lambda>x. True" and ?P2.0="P" and ?RGL_fml="\<beta>"] by auto

\<comment>\<open>replaces every free occurrence of x with x^d.
  Does not reduce double duals.\<close>
fun RGL_dual_free :: "'c \<Rightarrow> 'c RGL_game \<Rightarrow> 'c RGL_game" 
  and RGL_dual_free_fml :: "'c \<Rightarrow> 'c RGL_fml \<Rightarrow> 'c RGL_fml"
  where
"RGL_dual_free x (RGL_Var y) = (if x=y then (RGL_Dual (RGL_Var x)) else (RGL_Var y))"
| "RGL_dual_free x (RGL_Dual g) = RGL_Dual (RGL_dual_free x g)"
| "RGL_dual_free x (RGL_Atm_Game a) = RGL_Atm_Game a"
| "RGL_dual_free x (RGL_Rec y g) = (if x=y then (RGL_Rec y g) else RGL_Rec y (RGL_dual_free x g))"
| "RGL_dual_free x (RGL_Choice g1 g2) = RGL_Choice (RGL_dual_free x g1) (RGL_dual_free x g2)"
| "RGL_dual_free x (RGL_Seq g1 g2) = RGL_Seq (RGL_dual_free x g1) (RGL_dual_free x g2)"
| "RGL_dual_free x (RGL_Test f) = RGL_Test (RGL_dual_free_fml x f)"
| "RGL_dual_free_fml x (RGL_Atm_fml P) = RGL_Atm_fml P"
| "RGL_dual_free_fml x (RGL_Not f) = RGL_Not (RGL_dual_free_fml x f)"
| "RGL_dual_free_fml x (RGL_Or f1 f2)  = RGL_Or (RGL_dual_free_fml x f1) (RGL_dual_free_fml x f2)"
| "RGL_dual_free_fml x (RGL_Mod g f) = RGL_Mod (RGL_dual_free x g) (RGL_dual_free_fml x f)"

\<comment>\<open>detects all free instances of x^d and replaces it by x, through pattern matching in the Dual case.
  Does not reduce double duals.\<close>
fun RGL_undual_free :: "'c \<Rightarrow> 'c RGL_game \<Rightarrow> 'c RGL_game"
  and RGL_undual_free_fml :: "'c \<Rightarrow> 'c RGL_fml \<Rightarrow> 'c RGL_fml" where
  "RGL_undual_free x (RGL_Var y) = (RGL_Var y)"
| "RGL_undual_free x (RGL_Dual (RGL_Var y)) = (if x=y then RGL_Var x else RGL_Dual (RGL_Var y))"
| "RGL_undual_free x (RGL_Dual g) = RGL_Dual (RGL_undual_free x g)"
| "RGL_undual_free x (RGL_Atm_Game a) = RGL_Atm_Game a"
| "RGL_undual_free x (RGL_Rec y g) = (if x=y then (RGL_Rec y g) else RGL_Rec y (RGL_undual_free x g))"
| "RGL_undual_free x (RGL_Choice g1 g2) = RGL_Choice (RGL_undual_free x g1) (RGL_undual_free x g2)"
| "RGL_undual_free x (RGL_Seq g1 g2) = RGL_Seq (RGL_undual_free x g1) (RGL_undual_free x g2)"
| "RGL_undual_free x (RGL_Test f) = RGL_Test (RGL_undual_free_fml x f)"
| "RGL_undual_free_fml x (RGL_Mod g f) = RGL_Mod (RGL_undual_free x g) (RGL_undual_free_fml x f)"
| "RGL_undual_free_fml x (RGL_Or f1 f2) = RGL_Or (RGL_undual_free_fml x f1) (RGL_undual_free_fml x f2)"
| "RGL_undual_free_fml x (RGL_Not f) = RGL_Not (RGL_undual_free_fml x f)"
| "RGL_undual_free_fml x (RGL_Atm_fml P) = RGL_Atm_fml P"

definition RGL_And where "RGL_And A B = RGL_Not (RGL_Or (RGL_Not A) (RGL_Not B))"

definition RGL_DTest where "RGL_DTest f = RGL_Dual (RGL_Test f)"

definition RGL_DChoice where "RGL_DChoice g1 g2 = RGL_Dual (RGL_Choice (RGL_Dual g1) (RGL_Dual g2))"

definition RGL_DRec where "RGL_DRec x g = RGL_Dual (RGL_undual_free x (RGL_Rec x g))"
  
fun RGL_sy_dual :: "'c RGL_game \<Rightarrow> 'c RGL_game" 
  and RGL_sy_comp :: "'c RGL_fml \<Rightarrow> 'c RGL_fml" where
    "RGL_sy_dual (RGL_Atm_Game (Agl_gm a)) = RGL_Atm_Game (Dmn_gm a)"
  | "RGL_sy_dual (RGL_Atm_Game (Dmn_gm a)) = RGL_Atm_Game (Agl_gm a)"
  | "RGL_sy_dual (RGL_Var x) = RGL_Dual (RGL_Var x)"
  | "RGL_sy_dual (RGL_Dual g) = g"
  | "RGL_sy_dual (RGL_Test f) = RGL_DTest f"
  | "RGL_sy_dual (RGL_Choice g1 g2) = RGL_DChoice (RGL_sy_dual g1) (RGL_sy_dual g2)"
  | "RGL_sy_dual (RGL_Seq g1 g2) = RGL_Seq (RGL_sy_dual g1) (RGL_sy_dual g2)"
  | "RGL_sy_dual (RGL_Rec x g) = RGL_DRec x (RGL_dual_free x (RGL_sy_dual g))"

  | "RGL_sy_comp (RGL_Atm_fml P) = RGL_Not (RGL_Atm_fml P)"
  | "RGL_sy_comp (RGL_Not f) = f"
  | "RGL_sy_comp (RGL_Or f1 f2) = RGL_And (RGL_sy_comp f1) (RGL_sy_comp f2)"
  | "RGL_sy_comp (RGL_Mod g f) = RGL_Mod (RGL_sy_dual g) (RGL_sy_comp f)"

\<comment>\<open>reduces RGL fml and game to normal form, using syntactic dual and comp.\<close>
fun RGL_red_game :: "'c RGL_game \<Rightarrow> 'c RGL_game"
and RGL_red_fml :: "'c RGL_fml \<Rightarrow> 'c RGL_fml" where
    "RGL_red_game (RGL_Dual g) = RGL_sy_dual g"
  | "RGL_red_game (RGL_Test f) = RGL_Test (RGL_red_fml f)"
  | "RGL_red_game (RGL_Choice g1 g2) = RGL_Choice (RGL_red_game g1) (RGL_red_game g2)"
  | "RGL_red_game (RGL_Seq g1 g2) = RGL_Seq (RGL_red_game g1) (RGL_red_game g2)"
  | "RGL_red_game (RGL_Rec x g) = RGL_Rec x (RGL_red_game g)"
  | "RGL_red_game g = g"
  | "RGL_red_fml (RGL_Not f) = RGL_sy_comp f"
  | "RGL_red_fml (RGL_Or f1 f2) = RGL_Or (RGL_red_fml f1) (RGL_red_fml f2)"
  | "RGL_red_fml (RGL_Mod g f) = RGL_Mod (RGL_red_game g) (RGL_red_fml f)"
  | "RGL_red_fml (RGL_Atm_fml P) = RGL_Atm_fml P"

\<comment>\<open>collects free variables of RGL fml and games\<close>
primrec free_var:: "'c RGL_fml \<Rightarrow> 'c set"
  and free_var_game :: "'c RGL_game \<Rightarrow> 'c set" where
  "free_var (RGL_Atm_fml f) = {}"
|  "free_var (RGL_Not f) = free_var f"
|  "free_var (RGL_Or f1 f2) = free_var f1 \<union> free_var f2"
|  "free_var (RGL_Mod g f) = free_var_game g \<union> free_var f"
|  "free_var_game (RGL_Atm_Game a) = {}"
|  "free_var_game (RGL_Var x) = {x}"
|  "free_var_game (RGL_Dual g) = free_var_game g"
|  "free_var_game (RGL_Test f) = free_var f"
|  "free_var_game (RGL_Choice g1 g2) = free_var_game g1 \<union> free_var_game g2"
|  "free_var_game (RGL_Seq g1 g2) = free_var_game g1 \<union> free_var_game g2"
|  "free_var_game (RGL_Rec x g) = free_var_game g - {x}"

\<comment>\<open>tests if an RGL fml is closed\<close>
definition RGL_fml_closed :: "'c RGL_fml \<Rightarrow> bool" where
  "RGL_fml_closed f = (free_var f = {})"

definition RGL_game_closed where "RGL_game_closed g = (free_var_game g = {})"

\<comment>\<open>An RGL game is in normal form if 1) ?\<phi> for closed \<phi> only; 2)rx.\<alpha>
  only has x occurring in a scope with even number of duals in \<alpha>. 
  Hence all are in normal form except in the negation of these cases;
  hence we only need to worry about the forms ? and r.
\<close>

\<comment>\<open>This function tests if the given RGL game (not RGL_game) contains a free variable x with ALL even number of duals.
  For ?\<phi>, we need the modality in \<phi> to contain ALL even number of duals on x
  For Rec y g, if the tested variable x equals y, then x occurring in g does not belong to the current scope.
  
  Args: n: (parity of) number of dual operators in current scope, represented as a bool
    x: the variable under test
\<close>
primrec RGL_even_dual :: "bool \<Rightarrow> 'c \<Rightarrow> 'c RGL_game \<Rightarrow> bool" 
  and RGL_even_dual_fml :: "bool \<Rightarrow> 'c \<Rightarrow> 'c RGL_fml \<Rightarrow> bool" where
  "RGL_even_dual n x (RGL_Atm_Game a) = True"
| "RGL_even_dual n x (RGL_Var y) = (if y\<noteq>x then True else n)"  
| "RGL_even_dual n x (RGL_Dual g) = RGL_even_dual (\<not> n) x g"
| "RGL_even_dual n x (RGL_Test f) = RGL_even_dual_fml n x f" 
| "RGL_even_dual n x (RGL_Choice g1 g2) = (RGL_even_dual n x g1 \<and> RGL_even_dual n x g2)"
| "RGL_even_dual n x (RGL_Seq g1 g2) = (RGL_even_dual n x g1 \<and> RGL_even_dual n x g2)"
| "RGL_even_dual n x (RGL_Rec y g) = (if x=y then True else RGL_even_dual n x g)"
| "RGL_even_dual_fml n x (RGL_Atm_fml P) = True"
| "RGL_even_dual_fml n x (RGL_Not f) = RGL_even_dual_fml n x f"
| "RGL_even_dual_fml n x (RGL_Or f1 f2) =  (RGL_even_dual_fml n x f1 \<and>  RGL_even_dual_fml n x f2)"
| "RGL_even_dual_fml n x (RGL_Mod g f) = (RGL_even_dual n x g \<and> RGL_even_dual_fml n x f)"

\<comment>\<open>Tests if an RGL recursive game is valid. A valid RGL recursive game is rx.a where a has an even number of duals over x
  When g is rx.h, the predicate tests above mentioned validity.
  When g is not rx.h, the predicate always returns True.
\<close>
definition RGL_Rec_valid :: "'c RGL_game \<Rightarrow> bool" where
  "RGL_Rec_valid g \<equiv> \<forall>x. \<forall>h. (g = RGL_Rec x h \<longrightarrow> RGL_even_dual True x h)"

definition RGL_Test_valid :: "'c RGL_game \<Rightarrow> bool" where
  "RGL_Test_valid g \<equiv> \<forall>f. (g = RGL_Test f \<longrightarrow> RGL_fml_closed f)"

definition RGL_game_valid :: "'c RGL_game \<Rightarrow> bool" where
  "RGL_game_valid g \<equiv> (RGL_Rec_valid g \<and> RGL_Test_valid g)"

inductive RGL_nml_game:: "'c RGL_game \<Rightarrow> bool"
  and RGL_nml_fml :: "'c RGL_fml \<Rightarrow> bool" where
    RGL_nml_Atm_game: "RGL_nml_game (RGL_Atm_Game a)"
  | RGL_nml_Var: "RGL_nml_game (RGL_Var x)"
  | RGL_nml_DVar: "RGL_nml_game (RGL_Dual (RGL_Var x))"
  | RGL_nml_Test: "RGL_nml_fml f \<Longrightarrow>  RGL_nml_game (RGL_Test f)"
  | RGL_nml_DTest: "RGL_nml_fml f \<Longrightarrow> RGL_nml_game (RGL_DTest f)"
  | RGL_nml_Choice: "RGL_nml_game g1 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> RGL_nml_game (RGL_Choice g1 g2)"
  | RGL_nml_DChoice: "RGL_nml_game g1 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> RGL_nml_game (RGL_DChoice g1 g2)"
  | RGL_nml_Seq: "RGL_nml_game g1 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> RGL_nml_game (RGL_Seq g1 g2)"
  | RGL_nml_Rec: "RGL_nml_game g \<Longrightarrow> RGL_nml_game (RGL_Rec x g)"
  | RGL_nml_DRec: "RGL_nml_game g \<Longrightarrow> RGL_nml_game (RGL_DRec x g)"
  | RGL_nml_Atm_fml: "RGL_nml_fml (RGL_Atm_fml f)"
  | RGL_nml_Not_atm: "RGL_nml_fml (RGL_Not (RGL_Atm_fml f))"
  | RGL_nml_Or: "RGL_nml_fml f1 \<Longrightarrow> RGL_nml_fml f2 \<Longrightarrow> RGL_nml_fml (RGL_Or f1 f2)"
  | RGL_nml_And: "RGL_nml_fml f1 \<Longrightarrow> RGL_nml_fml f2 \<Longrightarrow> RGL_nml_fml (RGL_And f1 f2)"
  | RGL_nml_Mod: "RGL_nml_game g \<Longrightarrow> RGL_nml_fml f \<Longrightarrow> RGL_nml_fml (RGL_Mod g f)"

lemma RGL_nml_game_induct [case_names RGL_nml_Atm_Game RGL_nml_Var RGL_nml_DVar RGL_nml_Test RGL_nml_DTest RGL_nml_Choice RGL_nml_DChoice RGL_nml_Seq RGL_nml_Rec RGL_nml_DRec]:
  "(\<And>a. P (RGL_Atm_Game a))
    \<Longrightarrow> (\<And>x. P (RGL_Var x))
    \<Longrightarrow> (\<And>x. P (RGL_Dual (RGL_Var x)))
    \<Longrightarrow> (\<And>f. P (RGL_Test f))
    \<Longrightarrow> (\<And>f. P (RGL_DTest f))
    \<Longrightarrow> (\<And>g1 g2. RGL_nml_game g1 \<Longrightarrow> P g1 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_Choice g1 g2))
    \<Longrightarrow> (\<And>g1 g2. RGL_nml_game g1 \<Longrightarrow> P g1 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_DChoice g1 g2))
    \<Longrightarrow> (\<And>g1 g2. RGL_nml_game g1 \<Longrightarrow> P g1 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_Seq g1 g2))
    \<Longrightarrow> (\<And>x g. RGL_nml_game g \<Longrightarrow>P g \<Longrightarrow> P (RGL_Rec x g))
    \<Longrightarrow> (\<And>x g. RGL_nml_game g \<Longrightarrow>P g \<Longrightarrow> P (RGL_DRec x g))
    \<Longrightarrow> (RGL_nml_game \<alpha> \<Longrightarrow> P \<alpha>)
  "
  by (auto simp add:Syntax.RGL_nml_game_RGL_nml_fml.inducts(1))

lemma RGL_nml_fml_induct [case_names RGL_atm RGL_notatm RGL_or RGL_and RGL_mod]:
  "(\<And>f. P (RGL_Atm_fml f))
    \<Longrightarrow> (\<And>f. P (RGL_Not (RGL_Atm_fml f)))
    \<Longrightarrow> (\<And>f1 f2. RGL_nml_fml f1 \<Longrightarrow> P f1 \<Longrightarrow> RGL_nml_fml f2 \<Longrightarrow> P f2 \<Longrightarrow> P (RGL_Or f1 f2))
    \<Longrightarrow> (\<And>f1 f2. RGL_nml_fml f1 \<Longrightarrow> P f1 \<Longrightarrow> RGL_nml_fml f2 \<Longrightarrow> P f2 \<Longrightarrow> P (RGL_And f1 f2))
    \<Longrightarrow> (\<And>g f. RGL_nml_game g \<Longrightarrow> RGL_nml_fml f \<Longrightarrow> P f \<Longrightarrow> P (RGL_Mod g f))
    \<Longrightarrow> (RGL_nml_fml f \<Longrightarrow> P f)
  "
  by (auto simp add:Syntax.RGL_nml_game_RGL_nml_fml.inducts(2))

thm Syntax.RGL_nml_game_RGL_nml_fml.induct

lemma RGL_nml_game_nml_fml_inducts[case_names Atm Var Dvar Test Dtest Choice Dchoice Seq Rec Drec Atm_fml Natm_fml Or_fml And_fml Mod_fml]:
  "(\<And>a. P (RGL_Atm_Game a))
    \<Longrightarrow> (\<And>x. P (RGL_Var x))
    \<Longrightarrow> (\<And>x. P (RGL_Dual (RGL_Var x)))
    \<Longrightarrow> (\<And>f. RGL_nml_fml f \<Longrightarrow> Q f \<Longrightarrow> P (RGL_Test f))
    \<Longrightarrow> (\<And>f. RGL_nml_fml f \<Longrightarrow> Q f \<Longrightarrow> P (RGL_DTest f))
    \<Longrightarrow> (\<And>g1 g2. RGL_nml_game g1 \<Longrightarrow> P g1 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_Choice g1 g2))
    \<Longrightarrow> (\<And>g1 g2. RGL_nml_game g1 \<Longrightarrow> P g1 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_DChoice g1 g2))
    \<Longrightarrow> (\<And>g1 g2. RGL_nml_game g1 \<Longrightarrow> P g1 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_Seq g1 g2))
    \<Longrightarrow> (\<And>x g. RGL_nml_game g \<Longrightarrow>P g \<Longrightarrow> P (RGL_Rec x g))
    \<Longrightarrow> (\<And>x g. RGL_nml_game g \<Longrightarrow>P g \<Longrightarrow> P (RGL_DRec x g))
    \<Longrightarrow> (\<And>f. Q (RGL_Atm_fml f))
    \<Longrightarrow> (\<And>f. Q (RGL_Not (RGL_Atm_fml f)))
    \<Longrightarrow> (\<And>f1 f2. RGL_nml_fml f1 \<Longrightarrow> Q f1 \<Longrightarrow> RGL_nml_fml f2 \<Longrightarrow> Q f2 \<Longrightarrow> Q (RGL_Or f1 f2))
    \<Longrightarrow> (\<And>f1 f2. RGL_nml_fml f1 \<Longrightarrow> Q f1 \<Longrightarrow> RGL_nml_fml f2 \<Longrightarrow> Q f2 \<Longrightarrow> Q (RGL_And f1 f2))
    \<Longrightarrow> (\<And>g f. RGL_nml_game g \<Longrightarrow> P g \<Longrightarrow> RGL_nml_fml f \<Longrightarrow> Q f \<Longrightarrow> Q (RGL_Mod g f))
    \<Longrightarrow> (RGL_nml_game \<alpha> \<Longrightarrow> P \<alpha> &&& RGL_nml_fml f \<Longrightarrow> Q f) 
  "
  using Syntax.RGL_nml_game_RGL_nml_fml.induct[of "P" "Q" "g" "f"] by auto

inductive RGL_gm_nodual:: "'c \<Rightarrow> 'c RGL_game \<Rightarrow> bool"
  and RGL_fml_nodual:: "'c \<Rightarrow> 'c RGL_fml \<Rightarrow> bool" where
    RGL_gm_nodual_atm: "(RGL_gm_nodual x) (RGL_Atm_Game a)"
  | RGL_gm_nodual_Var: "(RGL_gm_nodual x) (RGL_Var y)"
  | RGL_gm_nodual_DVar: "x\<noteq>y \<Longrightarrow> RGL_gm_nodual x (RGL_Dual (RGL_Var y))"
  | RGL_gm_nodual_Test: "RGL_fml_nodual x f \<Longrightarrow> RGL_gm_nodual x (RGL_Test f)"
  | RGL_gm_nodual_DTest: "RGL_fml_nodual x f \<Longrightarrow> RGL_gm_nodual x (RGL_DTest f)"
  | RGL_gm_nodual_Choice: "RGL_gm_nodual x g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> RGL_gm_nodual x (RGL_Choice g1 g2)"
  | RGL_gm_nodual_DChoice: "RGL_gm_nodual x g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> RGL_gm_nodual x (RGL_DChoice g1 g2)"
  | RGL_gm_nodual_Seq: "RGL_gm_nodual x g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> RGL_gm_nodual x (RGL_Seq g1 g2)"
  | RGL_gm_nodual_Rec_free: "x\<noteq>y \<Longrightarrow> RGL_gm_nodual x g \<Longrightarrow> RGL_gm_nodual x (RGL_Rec y g)"
  | RGL_gm_nodual_Rec_bound: "RGL_gm_nodual x (RGL_Rec x g)"
  | RGL_gm_nodual_DRec_free: "x\<noteq>y \<Longrightarrow> RGL_gm_nodual x g \<Longrightarrow> RGL_gm_nodual x (RGL_DRec y g)"
  | RGL_gm_nodual_DRec_bound: "RGL_gm_nodual x (RGL_DRec x g)"
  | RGL_fml_nodual_atm: "RGL_fml_nodual x (RGL_Atm_fml P)"
  | RGL_fml_nodual_negatm: "RGL_fml_nodual x (RGL_Not (RGL_Atm_fml P))"
  | RGL_fml_nodual_Or: "RGL_fml_nodual x f1 \<Longrightarrow> RGL_fml_nodual x f2 \<Longrightarrow> RGL_fml_nodual x (RGL_Or f1 f2)"
  | RGL_fml_nodual_And: "RGL_fml_nodual x f1 \<Longrightarrow> RGL_fml_nodual x f2 \<Longrightarrow> RGL_fml_nodual x (RGL_And f1 f2)"
  | RGL_fml_nodual_Mod: "RGL_fml_nodual x f \<Longrightarrow> RGL_gm_nodual x g \<Longrightarrow> RGL_fml_nodual x (RGL_Mod g f)"


lemma RGL_nodual_nml:
  fixes g::"'c RGL_game" and f::"'c RGL_fml"
  shows
  "\<And>x. RGL_gm_nodual x g \<Longrightarrow> RGL_nml_game g"
  "\<And>x. RGL_fml_nodual x f \<Longrightarrow> RGL_nml_fml f"
proof (induction g and f)
  case (RGL_Atm_Game y)
  then show ?case using RGL_nml_Atm_game by auto
next
  case (RGL_Var y)
  then show ?case using RGL_nml_Var[of "y"] by auto
next
  case (RGL_Dual y)
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


lemma RGL_nodual_game_nodual_fml_inducts:
  fixes x::"'c"
    and \<alpha>::"'c RGL_game"
    and f::"'c RGL_fml"
  assumes
    nml: "RGL_nml_game \<alpha>"
    and nml_fml: "RGL_nml_fml f"
    and nd:"RGL_gm_nodual x \<alpha>"
    and nd_fml:"RGL_fml_nodual x f"
    and atm:"(\<And>a. P x (RGL_Atm_Game a))"
    and var:"(\<And>y. P x (RGL_Var y))"
    and dvar:"(\<And>y. x\<noteq>y \<Longrightarrow> P x (RGL_Dual (RGL_Var y)))"
    and tst:"(\<And>f. RGL_fml_nodual x f \<Longrightarrow> P x (RGL_Test f))"
    and dtst:"(\<And>f. RGL_fml_nodual x f \<Longrightarrow> P x (RGL_DTest f))"
    and choi:"(\<And>g1 g2. RGL_gm_nodual x g1 \<Longrightarrow> P x g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> P x g2 \<Longrightarrow> P x (RGL_Choice g1 g2))"
    and dchoi:"(\<And>g1 g2. RGL_gm_nodual x g1 \<Longrightarrow> P x g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> P x g2 \<Longrightarrow> P x (RGL_DChoice g1 g2))"
    and seq:"(\<And>g1 g2. RGL_gm_nodual x g1 \<Longrightarrow> P x g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> P x g2 \<Longrightarrow> P x (RGL_Seq g1 g2))"
    and rec_fr:"\<And>y g. x\<noteq>y \<Longrightarrow> RGL_gm_nodual x g \<Longrightarrow> P x g \<Longrightarrow> P x (RGL_Rec y g)"
    and rec_bd:"\<And>g. P x (RGL_Rec x g)"
    and drec_fr:"(\<And>y g. x\<noteq>y \<Longrightarrow> RGL_gm_nodual x g \<Longrightarrow> P x g \<Longrightarrow> P x (RGL_DRec y g))"
    and drec_bd:"(\<And>g. P x (RGL_DRec x g))"
    and atm_fml:"\<And>f. Q x (RGL_Atm_fml f)"
    and negatm: "\<And>f. Q x (RGL_Not (RGL_Atm_fml f))"
    and or:"\<And>f1 f2. RGL_fml_nodual x f1 \<Longrightarrow> Q x f1 \<Longrightarrow> RGL_fml_nodual x f2 \<Longrightarrow> Q x f2 \<Longrightarrow> Q x (RGL_Or f1 f2)"
    and and_fml:"\<And>f1 f2. RGL_fml_nodual x f1 \<Longrightarrow> Q x f1 \<Longrightarrow> RGL_fml_nodual x f2 \<Longrightarrow> Q x f2 \<Longrightarrow> Q x (RGL_And f1 f2)"
    and mod:"\<And>g f. RGL_fml_nodual x f \<Longrightarrow> Q x f \<Longrightarrow> RGL_gm_nodual x g \<Longrightarrow> P x g \<Longrightarrow> Q x (RGL_Mod g f)"
  shows
    "P x \<alpha>"
    "Q x f"
  using assms
proof (induction \<alpha> and f)
  case (RGL_Atm_Game x)
  then show ?case using assms by auto
next
  case (RGL_Var x)
  then show ?case using assms by auto
next
  case (RGL_Dual g)
  then show ?case sorry
next
  case (RGL_Test f')
  then show ?case 
  proof - have a:"RGL_fml_nodual x f'" using RGL_Test.prems(3) apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
    from tst a show ?thesis by auto
  qed
next
  case (RGL_Choice g1 g2)
  then show ?case 
  proof - have a:"RGL_gm_nodual x g1" using RGL_Choice.prems(3) apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
    have b:"RGL_gm_nodual x g2" using RGL_Choice.prems(3) apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
    have c:"RGL_nml_game g1" using RGL_Choice.prems(1) apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
    have d:"RGL_nml_game g2" using RGL_Choice.prems(1) apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
    from a b choi RGL_Choice.IH assms c d show ?thesis by blast
  qed
next
  case (RGL_Seq g1 g2)
  then show ?case
  proof - have a:"RGL_gm_nodual x g1" using RGL_Seq.prems(3) apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
    have b:"RGL_gm_nodual x g2" using RGL_Seq.prems(3) apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
    have c:"RGL_nml_game g1" using RGL_Seq.prems(1) apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
    have d:"RGL_nml_game g2" using RGL_Seq.prems(1) apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
    from a b seq RGL_Seq.IH assms c d show ?thesis by blast
  qed
next
  case (RGL_Rec y g)
  then show ?case
  proof (cases "x=y")
    case True
    then show ?thesis using rec_bd by auto
  next
    case False
    then show ?thesis
    proof -
      have a:"RGL_gm_nodual x g" using RGL_Rec.prems(3) apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def
        using False by auto
      from RGL_Rec.prems(1) have b:"RGL_nml_game g" apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
      from a b rec_fr[of "y""g"] False assms RGL_Rec.IH show ?thesis by blast
    qed
  qed
next
  case (RGL_Atm_fml x)
  then show ?case using atm_fml by auto
next
  case (RGL_Not f')
  then show ?case
    using assms
    proof (induction f' rule:RGL_fml_induct)
      case (Atm a)
      then show ?case using negatm by auto
    next
      case (Not f1)
      then show ?case
      proof - from Not.prems(3) have False apply cases unfolding RGL_And_def by auto
        then show ?thesis by auto
      qed
    next
      case (Or f1 f2)
      then show ?case
      proof -
        from Or.prems(3) obtain f3 f4 where "RGL_Not (RGL_Or f1 f2) = RGL_And f3 f4" apply cases by auto
        then show ?thesis using Or.IH
      qed
    next
      case (Mod g f)
      then show ?case
      proof - from Mod.prems(3) have False apply cases unfolding RGL_And_def by auto
        then show ?thesis by auto
      qed
    qed
next
  case (RGL_Or f1 f2)
  then show ?case sorry
next
  case (RGL_Mod g1 f1)
  then show ?case sorry
qed

  proof (induction rule:RGL_nml_fml_induct)
    case (RGL_atm f1)
    then show ?case using atm by auto
  next
    case (RGL_notatm f1)
    then show ?case using negatm by auto
  next
    case (RGL_or f1 f2)
    then show ?case
    proof -
      from RGL_or.prems(5) have a1:"RGL_fml_nodual x f1" apply cases unfolding RGL_And_def by auto
      from RGL_or.prems(3) have b1:"RGL_nml_fml f1" apply cases unfolding RGL_And_def by auto
      from RGL_or.prems(5) have a2:"RGL_fml_nodual x f2" apply cases unfolding RGL_And_def by auto
      from RGL_or.prems(3) have b2:"RGL_nml_fml f2" apply cases unfolding RGL_And_def by auto
      from a1 b1 RGL_Not.IH RGL_or.IH(1) assms RGL_or.prems have c1:"Q x f1" by blast
      from a2 b2 RGL_Not.IH RGL_or.IH(2) assms RGL_or.prems have c2:"Q x f2" by blast
      show ?thesis using c1 c2 or a1 a2 by auto
    qed
  next
    case (RGL_and f1 f2)
    then show ?case
    proof -
      from RGL_and.prems(5) have a1:"RGL_fml_nodual x f1" apply cases unfolding RGL_And_def by auto
      from RGL_and.prems(3) have b1:"RGL_nml_fml f1" apply cases unfolding RGL_And_def by auto
      from RGL_and.prems(5) have a2:"RGL_fml_nodual x f2" apply cases unfolding RGL_And_def by auto
      from RGL_and.prems(3) have b2:"RGL_nml_fml f2" apply cases unfolding RGL_And_def by auto
      from a1 b1 RGL_Not.IH RGL_and.IH(1) assms RGL_and.prems have c1:"Q x f1" by blast
      from a2 b2 RGL_Not.IH RGL_and.IH(2) assms RGL_and.prems have c2:"Q x f2" by blast
      show ?thesis using c1 c2 and_fml a1 a2 by auto
    qed
  next
    case (RGL_mod g f1)
    then show ?case
    proof -
      from RGL_Not.prems(2) RGL_mod.prems have False apply cases unfolding RGL_And_def apply auto
    qed
  next
    show "RGL_nml_fml (RGL_Not f')" using RGL_Not.prems by simp
  qed
next


datatype Lmu_fml = 
  Lmu_Id
  | Lmu_Atm_fml "Atm_fml"
  | Lmu_Not "Lmu_fml"
  | Lmu_Or "Lmu_fml" "Lmu_fml"
  | Lmu_Mod "Atm_game" "Lmu_fml"
  | Lmu_Star "Lmu_fml"

datatype 'a FLC_fml =
  FLC_Id
  | FLC_Atm_fml "Atm_fml"
  | FLC_Not "Atm_fml"
  | FLC_Var 'a
  | FLC_Or "'a FLC_fml" "'a FLC_fml"
  | FLC_And "'a FLC_fml" "'a FLC_fml"
  | FLC_Mod_Exist "Atm_game" "'a FLC_fml"
  | FLC_Mod_Forall "Atm_game" "'a FLC_fml"
  | FLC_Chop "'a FLC_fml" "'a FLC_fml"
  | FLC_mu 'a "'a FLC_fml"
  | FLC_nu 'a "'a FLC_fml"

datatype LStar_fml = 
  LStar_Id
  | LStar_Atm_fml "Atm_fml"
  | LStar_Not "LStar_fml"
  | LStar_Or "LStar_fml" "LStar_fml"
  | LStar_Mod "Atm_game" "LStar_fml"
  | LStar_Chop "LStar_fml" "LStar_fml"
  | LStar_Star "LStar_fml"


end