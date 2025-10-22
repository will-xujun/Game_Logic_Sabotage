theory Syntax
imports
  Complex_Main
  "HOL-IMP.Star"
begin 

\<comment>\<open>We realise the syntax of GL, GLs, RGL, FLC, Lmu, LStar.
  Separable formulas of Lmu should be realised as an inductive property.
  right-linearity in RGL is also an inductive property. \<close>

type_synonym ident = "int"

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

datatype RGL_game =
  RGL_Atm_Game "atm_gm"
  | RGL_Var ident
  | RGL_Dual "RGL_game"
  | RGL_Test "RGL_fml" 
  | RGL_Choice "RGL_game" "RGL_game"
  | RGL_Seq "RGL_game" "RGL_game"
  | RGL_Rec ident "RGL_game"
and
 RGL_fml = 
    RGL_Atm_fml "Atm_fml"
  | RGL_Not "RGL_fml"
  | RGL_Or "RGL_fml" "RGL_fml"
  | RGL_Mod "RGL_game" "RGL_fml"

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

lemma RGL_game_induct_finer [case_names RGL_Atm_Game RGL_Var RGL_Dual RGL_Choice RGL_Seq RGL_Rec RGL_Atm_fml RGL_Not RGL_Or RGL_Mod]:
  "(\<And>a. P (RGL_Atm_Game a))
    \<Longrightarrow> (\<And>x. P (RGL_Var x))
    \<Longrightarrow> (\<And>g. P g \<Longrightarrow> P (RGL_Dual g))
    \<Longrightarrow> (\<And>g1 g2. P g1 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_Choice g1 g2))
    \<Longrightarrow> (\<And>g1 g2. P g1 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_Seq g1 g2))
    \<Longrightarrow> (\<And>x g. P g \<Longrightarrow> P (RGL_Rec x g))
    \<Longrightarrow> (\<And>f. P (RGL_Test (RGL_Atm_fml f)))
    \<Longrightarrow> (\<And>f. P (RGL_Test f) \<Longrightarrow> P (RGL_Test (RGL_Not f)))
    \<Longrightarrow> (\<And>f g. P (RGL_Test f) \<Longrightarrow> P (RGL_Test g) \<Longrightarrow> P (RGL_Test (RGL_Or f g)))
    \<Longrightarrow> (\<And>g f. P g \<Longrightarrow> P (RGL_Test f) \<Longrightarrow> P (RGL_Test (RGL_Mod g f)))
    \<Longrightarrow> P \<alpha>
  "
  using RGL_game.induct[of "P" "\<lambda>x. P (RGL_Test x)" "\<alpha>"] by fastforce

lemma RGL_fml_induct [case_names Atm Not Or Mod]:
  "(\<And>a. P (RGL_Atm_fml a))
  \<Longrightarrow> (\<And>f. P f \<Longrightarrow> P (RGL_Not f))
  \<Longrightarrow> (\<And>f1 f2. P f1 \<Longrightarrow> P f2 \<Longrightarrow> P (RGL_Or f1 f2))
  \<Longrightarrow> (\<And>g f. P f \<Longrightarrow> P (RGL_Mod g f))
  \<Longrightarrow> P \<beta>"
  using RGL_fml.induct[where ?P1.0="\<lambda>x. True" and ?P2.0="P" and ?RGL_fml="\<beta>"] by auto

definition RGL_And where "RGL_And A B = RGL_Not (RGL_Or (RGL_Not A) (RGL_Not B))"

definition RGL_DTest where "RGL_DTest f = RGL_Dual (RGL_Test f)"

definition RGL_DChoice where "RGL_DChoice g1 g2 = RGL_Dual (RGL_Choice (RGL_Dual g1) (RGL_Dual g2))"

(* replaces every free occurrence of x with x^d.
  Reduces double dual on variables. *)
fun RGL_dual_free :: "ident \<Rightarrow> RGL_game \<Rightarrow> RGL_game" 
  and RGL_dual_free_fml :: "ident \<Rightarrow> RGL_fml \<Rightarrow> RGL_fml"
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

definition RGL_DRec where "RGL_DRec x g = RGL_Dual (RGL_Rec x (RGL_Dual (RGL_dual_free x g)))"

lemma RGL_dual_free_vars_comm: 
  "RGL_dual_free x (RGL_dual_free y g) = RGL_dual_free y (RGL_dual_free x g)"
  "RGL_dual_free_fml x (RGL_dual_free_fml y f) = RGL_dual_free_fml y (RGL_dual_free_fml x f)"
proof (induction g and f)
  case (RGL_Atm_Game x)
  then show ?case by auto
next
  case (RGL_Var y)
  then show ?case by (cases "x=y") (auto)
next
  case (RGL_Dual g1)
  then show ?case by auto
next
  case (RGL_Test f)
  then show ?case by auto
next
  case (RGL_Choice x1 x2)
  then show ?case by auto
next
  case (RGL_Seq x1 x2)
  then show ?case by auto
next
  case (RGL_Rec x1 x2)
  then show ?case by auto
next
  case (RGL_Atm_fml x)
  then show ?case by auto
next
  case (RGL_Not x)
  then show ?case by auto
next
  case (RGL_Or x1 x2)
  then show ?case by auto
next
  case (RGL_Mod x1 x2)
  then show ?case by auto
qed



(*detects all free instances of x^d and replaces it by x, through pattern matching in the Dual case.
  Does not reduce double duals.*)
fun RGL_undual_free :: "ident \<Rightarrow> RGL_game \<Rightarrow> RGL_game"
  and RGL_undual_free_fml :: "ident \<Rightarrow> RGL_fml \<Rightarrow> RGL_fml" where
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


(* this function traverses the recursive structure and applies Dual at the bottom (Atomic /Var).
  This is achieved using pattern matching on the Dual case.
*)
fun RGL_sy_dual :: " RGL_game \<Rightarrow> RGL_game" 
  and RGL_sy_comp ::  "RGL_fml \<Rightarrow> RGL_fml" where
    "RGL_sy_dual (RGL_Atm_Game (Agl_gm a)) = RGL_Atm_Game (Dmn_gm a)"
  | "RGL_sy_dual (RGL_Atm_Game (Dmn_gm a)) = RGL_Atm_Game (Agl_gm a)"
  | "RGL_sy_dual (RGL_Var x) = RGL_Dual (RGL_Var x)"
  | "RGL_sy_dual (RGL_Dual (RGL_Choice (RGL_Dual g1) (RGL_Dual g2))) = RGL_Choice (RGL_sy_dual g1) (RGL_sy_dual g2)"
  | "RGL_sy_dual (RGL_Dual g) = g"
  | "RGL_sy_dual (RGL_Test f) = RGL_DTest f"
  | "RGL_sy_dual (RGL_Choice g1 g2) = RGL_DChoice (RGL_sy_dual g1) (RGL_sy_dual g2)"
  | "RGL_sy_dual (RGL_Seq g1 g2) = RGL_Seq (RGL_sy_dual g1) (RGL_sy_dual g2)"
  | "RGL_sy_dual (RGL_Rec x g) = RGL_DRec x (RGL_dual_free x (RGL_sy_dual g))"
  | "RGL_sy_comp (RGL_Atm_fml P) = RGL_Not (RGL_Atm_fml P)"
  | "RGL_sy_comp (RGL_Not (RGL_Or (RGL_Not f1) (RGL_Not f2))) = RGL_Or (RGL_sy_comp f1) (RGL_sy_comp f2)"
  | "RGL_sy_comp (RGL_Not f) = f"
  | "RGL_sy_comp (RGL_Or f1 f2) = RGL_And (RGL_sy_comp f1) (RGL_sy_comp f2)"
  | "RGL_sy_comp (RGL_Mod g f) = RGL_Mod (RGL_sy_dual g) (RGL_sy_comp f)"

(* normalize recursively replaces all Dual by sy_dual, so that evaluation result is an n-nml form. *)
fun RGL_normalize_game :: "RGL_game \<Rightarrow> RGL_game"
and RGL_normalize_fml :: "RGL_fml \<Rightarrow> RGL_fml" where
    "RGL_normalize_game (RGL_Dual (RGL_Choice (RGL_Dual g1) (RGL_Dual g2))) = RGL_DChoice (RGL_normalize_game g1) (RGL_normalize_game g2)"
  | "RGL_normalize_game (RGL_Dual (RGL_Rec x (RGL_Dual g))) = RGL_DRec x (RGL_normalize_game g)"
  | "RGL_normalize_game (RGL_Dual g) = RGL_sy_dual (RGL_normalize_game g)"
  | "RGL_normalize_game (RGL_Test f) = RGL_Test (RGL_normalize_fml f)"
  | "RGL_normalize_game (RGL_Choice g1 g2) = RGL_Choice (RGL_normalize_game g1) (RGL_normalize_game g2)"
  | "RGL_normalize_game (RGL_Seq g1 g2) = RGL_Seq (RGL_normalize_game g1) (RGL_normalize_game g2)"
  | "RGL_normalize_game (RGL_Rec x g) = RGL_Rec x (RGL_normalize_game g)"
  | "RGL_normalize_game g = g"
  | "RGL_normalize_fml (RGL_Not (RGL_Or (RGL_Not f1) (RGL_Not f2))) = RGL_And (RGL_normalize_fml f1) (RGL_normalize_fml f2)"
  | "RGL_normalize_fml (RGL_Not f) = RGL_sy_comp (RGL_normalize_fml f)"
  | "RGL_normalize_fml (RGL_Or f1 f2) = RGL_Or (RGL_normalize_fml f1) (RGL_normalize_fml f2)"
  | "RGL_normalize_fml (RGL_Mod g f) = RGL_Mod (RGL_normalize_game g) (RGL_normalize_fml f)"
  | "RGL_normalize_fml (RGL_Atm_fml P) = RGL_Atm_fml P"

(*Collects free variables of terms*)
primrec free_var:: "RGL_fml \<Rightarrow> ident set"
  and free_var_game :: "RGL_game \<Rightarrow> ident set" where
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
definition RGL_fml_closed :: "RGL_fml \<Rightarrow> bool" where
  "RGL_fml_closed f = (free_var f = {})"

definition RGL_game_closed where "RGL_game_closed g = (free_var_game g = {})"

lemma RGL_notfree_dual_free_id:
  "x\<notin> free_var_game g \<Longrightarrow> RGL_dual_free x g = g"
  "x\<notin> free_var f \<Longrightarrow> RGL_dual_free_fml x f = f"
proof (induction g and f)
  case (RGL_Atm_Game a)
  then show ?case by auto
next
  case (RGL_Var y)
  then show ?case unfolding RGL_game_closed_def by auto
next
  case (RGL_Dual g1)
  then show ?case by auto
next
  case (RGL_Test f1)
  then show ?case unfolding RGL_game_closed_def RGL_fml_closed_def by auto
next
  case (RGL_Choice g1 g2)
  then show ?case unfolding RGL_game_closed_def by auto
next
  case (RGL_Seq g1 g2)
  then show ?case unfolding RGL_game_closed_def by auto
next
  case (RGL_Rec y g1)
  then show ?case by (cases "x=y") (auto)
next
  case (RGL_Atm_fml P)
  then show ?case by auto
next
  case (RGL_Not f1)
  then show ?case by auto
next
  case (RGL_Or f1 f2)
  then show ?case by auto
next
  case (RGL_Mod g1 f1)
  then show ?case by auto
qed

lemma RGL_closed_dual_free_id:
  "RGL_game_closed g \<Longrightarrow> RGL_dual_free x g = g"
  "RGL_fml_closed f \<Longrightarrow> RGL_dual_free_fml x f = f"
  using RGL_notfree_dual_free_id unfolding RGL_game_closed_def RGL_fml_closed_def by auto


lemma RGL_closed_dual_free__closed:
  "RGL_game_closed g \<Longrightarrow> RGL_game_closed (RGL_dual_free x g)"
  "RGL_fml_closed f \<Longrightarrow> RGL_fml_closed (RGL_dual_free_fml x f)"
  using RGL_closed_dual_free_id by auto

(*An RGL game is in normal form if 1) ?\<phi> for closed \<phi> only; 2)rx.\<alpha>
  only has x occurring in a scope with even number of duals in \<alpha>. 
  Hence all are in normal form except in the negation of these cases;
  hence we only need to worry about the forms ? and r.

  \<open>This function tests if the given RGL game (not RGL_game) contains a free variable x with ALL even number of duals.
  For ?\<phi>, we need the modality in \<phi> to contain ALL even number of duals on x
  For Rec y g, if the tested variable x equals y, then x occurring in g does not belong to the current scope.
  
  Args: n: (parity of) number of dual operators in current scope, represented as a bool
    x: the variable under test
*)
primrec RGL_even_dual :: "bool \<Rightarrow> ident \<Rightarrow> RGL_game \<Rightarrow> bool" 
  and RGL_even_dual_fml :: "bool \<Rightarrow> ident \<Rightarrow> RGL_fml \<Rightarrow> bool" where
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
definition RGL_Rec_valid :: "RGL_game \<Rightarrow> bool" where
  "RGL_Rec_valid g \<equiv> \<forall>x. \<forall>h. (g = RGL_Rec x h \<longrightarrow> RGL_even_dual True x h)"

definition RGL_Test_valid :: "RGL_game \<Rightarrow> bool" where
  "RGL_Test_valid g \<equiv> \<forall>f. (g = RGL_Test f \<longrightarrow> RGL_fml_closed f)"

definition RGL_game_valid :: "RGL_game \<Rightarrow> bool" where
  "RGL_game_valid g \<equiv> (RGL_Rec_valid g \<and> RGL_Test_valid g)"

inductive RGL_nml_game:: "RGL_game \<Rightarrow> bool"
  and RGL_nml_fml :: "RGL_fml \<Rightarrow> bool" where
    RGL_nml_Atm_game: "RGL_nml_game (RGL_Atm_Game a)"
  | RGL_nml_Var: "RGL_nml_game (RGL_Var x)"
  | RGL_nml_DVar: "RGL_nml_game (RGL_Dual (RGL_Var x))"
  | RGL_nml_Test: "RGL_nml_fml f \<Longrightarrow>  RGL_fml_closed f \<Longrightarrow> RGL_nml_game (RGL_Test f)"
  | RGL_nml_DTest: "RGL_nml_fml f \<Longrightarrow> RGL_fml_closed f \<Longrightarrow> RGL_nml_game (RGL_DTest f)"
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


inductive RGL_ddnml_game:: "RGL_game \<Rightarrow> bool"
  and RGL_ddnml_fml :: "RGL_fml \<Rightarrow> bool" where
    RGL_ddnml_Atm_game: "RGL_ddnml_game (RGL_Atm_Game a)"
  | RGL_ddnml_Var: "RGL_ddnml_game (RGL_Var x)"
  | RGL_ddnml_DVar: "RGL_ddnml_game (RGL_Dual (RGL_Var x))"
  | RGL_ddnml_DDVar: "RGL_ddnml_game (RGL_Dual (RGL_Dual (RGL_Var x)))"
  | RGL_ddnml_Test: "RGL_ddnml_fml f \<Longrightarrow>  RGL_fml_closed f \<Longrightarrow> RGL_ddnml_game (RGL_Test f)"
  | RGL_ddnml_DTest: "RGL_ddnml_fml f \<Longrightarrow> RGL_fml_closed f \<Longrightarrow> RGL_ddnml_game (RGL_DTest f)"
  | RGL_ddnml_Choice: "RGL_ddnml_game g1 \<Longrightarrow> RGL_ddnml_game g2 \<Longrightarrow> RGL_ddnml_game (RGL_Choice g1 g2)"
  | RGL_ddnml_DChoice: "RGL_ddnml_game g1 \<Longrightarrow> RGL_ddnml_game g2 \<Longrightarrow> RGL_ddnml_game (RGL_DChoice g1 g2)"
  | RGL_ddnml_Seq: "RGL_ddnml_game g1 \<Longrightarrow> RGL_ddnml_game g2 \<Longrightarrow> RGL_ddnml_game (RGL_Seq g1 g2)"
  | RGL_ddnml_Rec: "RGL_ddnml_game g \<Longrightarrow> RGL_ddnml_game (RGL_Rec x g)"
  | RGL_ddnml_DRec: "RGL_ddnml_game g \<Longrightarrow> RGL_ddnml_game (RGL_DRec x g)"
  | RGL_ddnml_Atm_fml: "RGL_ddnml_fml (RGL_Atm_fml f)"
  | RGL_ddnml_Not_atm: "RGL_ddnml_fml (RGL_Not (RGL_Atm_fml f))"
  | RGL_ddnml_Or: "RGL_ddnml_fml f1 \<Longrightarrow> RGL_ddnml_fml f2 \<Longrightarrow> RGL_ddnml_fml (RGL_Or f1 f2)"
  | RGL_ddnml_And: "RGL_ddnml_fml f1 \<Longrightarrow> RGL_ddnml_fml f2 \<Longrightarrow> RGL_ddnml_fml (RGL_And f1 f2)"
  | RGL_ddnml_Mod: "RGL_ddnml_game g \<Longrightarrow> RGL_ddnml_fml f \<Longrightarrow> RGL_ddnml_fml (RGL_Mod g f)"

lemma RGL_nml_game_induct [case_names rGL_nml_Atm_Game rGL_nml_Var rGL_nml_DVar rGL_nml_Test rGL_nml_DTest rGL_nml_Choice rGL_nml_DChoice rGL_nml_Seq rGL_nml_Rec rGL_nml_DRec]:
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


lemma RGL_nml__ddnml:
  "RGL_nml_game g \<Longrightarrow> RGL_ddnml_game g" 
  "RGL_nml_fml f \<Longrightarrow> RGL_ddnml_fml f"
proof (induction g and f rule:RGL_nml_game_RGL_nml_fml.inducts)
  case (RGL_nml_Atm_game a)
  then show ?case by (simp add:RGL_ddnml_Atm_game)
next
  case (RGL_nml_Var x)
  then show ?case by (simp add:RGL_ddnml_Var)
next
  case (RGL_nml_DVar x)
  then show ?case by (simp add:RGL_ddnml_DVar)
next
  case (RGL_nml_Test f)
  then show ?case by (simp add:RGL_ddnml_Test)
next
  case (RGL_nml_DTest f)
  then show ?case using RGL_ddnml_DTest RGL_nml_DTest.IH by auto
next
  case (RGL_nml_Choice g1 g2)
  then show ?case using RGL_ddnml_Choice by auto
next
  case (RGL_nml_DChoice g1 g2)
  then show ?case using RGL_ddnml_DChoice by auto
next
  case (RGL_nml_Seq g1 g2)
  then show ?case using RGL_ddnml_Seq by auto
next
  case (RGL_nml_Rec g x)
  then show ?case using RGL_ddnml_Rec by auto
next
  case (RGL_nml_DRec g x)
  then show ?case using RGL_ddnml_DRec by auto
next
  case (RGL_nml_Atm_fml f)
  then show ?case using RGL_ddnml_Atm_fml by auto
next
  case (RGL_nml_Not_atm f)
  then show ?case using RGL_ddnml_Not_atm by auto
next
  case (RGL_nml_Or f1 f2)
  then show ?case using RGL_ddnml_Or by auto
next
  case (RGL_nml_And f1 f2)
  then show ?case using RGL_ddnml_And by auto
next
  case (RGL_nml_Mod g f)
  then show ?case using RGL_ddnml_Mod by auto
qed


(* This relation expresses that two games are either the same, or
  differ at the variable level by exactly two Dual constructors (no restriction on which variables differ).
  Its rtclosure is symmetric by an easy induction, because we have varl and varr.
  RGL_ddrel_fml plays an auxiliary role.
 *)
inductive RGL_ddrel_gm::"RGL_game \<Rightarrow> RGL_game \<Rightarrow> bool"
  and RGL_ddrel_fml:: "RGL_fml \<Rightarrow> RGL_fml \<Rightarrow> bool" where
  RGL_ddgm_varl: "RGL_ddrel_gm (RGL_Var x) (RGL_Dual (RGL_Dual (RGL_Var x)))"
| RGL_ddgm_varr: "RGL_ddrel_gm (RGL_Dual (RGL_Dual (RGL_Var x))) (RGL_Var x)"
| RGL_ddgm_choi: "RGL_ddrel_gm g1 g2 \<Longrightarrow> RGL_ddrel_gm g3 g4 \<Longrightarrow> RGL_ddrel_gm (RGL_Choice g1 g3) (RGL_Choice g2 g4)"
| RGL_ddgm_seq: "RGL_ddrel_gm g1 g2 \<Longrightarrow> RGL_ddrel_gm g3 g4 \<Longrightarrow> RGL_ddrel_gm (RGL_Seq g1 g3) (RGL_Seq g2 g4)"
| RGL_ddgm_dchoi: "RGL_ddrel_gm g1 g2 \<Longrightarrow> RGL_ddrel_gm g3 g4 \<Longrightarrow> RGL_ddrel_gm (RGL_DChoice g1 g3) (RGL_DChoice g2 g4)"
| RGL_ddgm_rec: "RGL_ddrel_gm g1 g2 \<Longrightarrow> RGL_ddrel_gm (RGL_Rec x g1) (RGL_Rec x g2)"
| RGL_ddgm_drec: "RGL_ddrel_gm g1 g2 \<Longrightarrow> RGL_ddrel_gm (RGL_DRec x g1) (RGL_DRec x g2)"
| RGL_ddgm_tst: "RGL_ddrel_fml f1 f2 \<Longrightarrow> RGL_ddrel_gm (RGL_Test f1) (RGL_Test f2)"
| RGL_ddgm_dtst: "RGL_ddrel_fml f1 f2 \<Longrightarrow> RGL_ddrel_gm (RGL_DTest f1) (RGL_DTest f2)"
| RGL_ddfml_not: "RGL_ddrel_fml f1 f2 \<Longrightarrow> RGL_ddrel_fml (RGL_Not f1) (RGL_Not f2)"
| RGL_ddfml_or: "RGL_ddrel_fml f1 f2 \<Longrightarrow> RGL_ddrel_fml f3 f4 \<Longrightarrow> RGL_ddrel_fml (RGL_Or f1 f3) (RGL_Or f2 f4)"
| RGL_ddfml_mod: "RGL_ddrel_gm g1 g2 \<Longrightarrow> RGL_ddrel_fml f1 f2 \<Longrightarrow> RGL_ddrel_fml (RGL_Mod g1 f1) (RGL_Mod g2 f2)"

definition RGL_ddrel_gm_rt where "RGL_ddrel_gm_rt = star RGL_ddrel_gm"

definition RGL_ddrel_fml_rt where "RGL_ddrel_fml_rt = star RGL_ddrel_fml"

notation RGL_ddrel_gm_rt (infix "\<sim>\<^sub>g" 50)

notation RGL_ddrel_fml_rt (infix "\<sim>\<^sub>f" 50)

lemma RGL_sym: fixes g1::"RGL_game" and g2::"RGL_game" and f1::"RGL_fml" and f2::"RGL_fml"
  shows "g1 \<sim>\<^sub>g g2 \<longrightarrow> g2 \<sim>\<^sub>g g1 \<and> f1 \<sim>\<^sub>f f2 \<longrightarrow> f2 \<sim>\<^sub>f f1"
  thm RGL_ddrel_gm_RGL_ddrel_fml.induct[where ?x1.0="g1" and ?x2.0="g2" and ?x3.0="f1" and ?x4.0="f2"]
proof (induction rule:RGL_ddrel_gm_RGL_ddrel_fml.induct[where ?x1.0="g1" and ?x2.0="g2" and ?x3.0="f1" and ?x4.0="f2"])

(* RGL_dual_free is almost an involution except x^d^d is left unreduced. *)
lemma RGL_dual_free_invo_dd:
  fixes g:: "RGL_game" and f::"RGL_fml"
  shows "(RGL_dual_free x (RGL_dual_free x g)) \<sim>\<^sub>g g"
        "(RGL_dual_free_fml x (RGL_dual_free_fml x f)) \<sim>\<^sub>f RGL_normalize_fml f"
proof (induction g and f)
  case (RGL_Atm_Game x)
  then show ?case
  by (simp add: RGL_ddrel_gm_rt_def)
next
  case (RGL_Var x)
  then show ?case
  by (simp add: RGL_ddgm_varr RGL_ddrel_gm_rt_def)
next
  case (RGL_Dual g1)
  then show ?case
  proof (cases "\<exists>y. g1=RGL_Var y")
    case True
    then show ?thesis
    proof fix y assume "g1=RGL_Var y"
      then show "RGL_normalize_game (RGL_dual_free x (RGL_dual_free x (RGL_Dual g1))) = RGL_normalize_game (RGL_Dual g1)"
        by simp
    qed
  next
    case False
    then show ?thesis
    proof - assume ass:"\<nexists>y. g1 = RGL_Var y"
      have "RGL_dual_free x (RGL_Dual g1) = RGL_Dual (RGL_dual_free x g1)" using ass
        by (metis RGL_dual_free.simps(3,4,5,6,7,8) RGL_game.exhaust)
      have "\<nexists>y. RGL_dual_free x g1 = RGL_Dual (RGL_Var y)"
      show "RGL_normalize_game (RGL_dual_free x (RGL_dual_free x (RGL_Dual g1))) = RGL_normalize_game (RGL_Dual g1)"
    qed
  qed
next
  case (RGL_Test x)
  then show ?case by auto
next
  case (RGL_Choice x1 x2)
  then show ?case by auto
next
  case (RGL_Seq x1 x2)
  then show ?case by auto
next
  case (RGL_Rec x1 x2)
  then show ?case by auto
next
  case (RGL_Atm_fml x)
  then show ?case by auto
next
  case (RGL_Not x)
  then show ?case by auto
next
  case (RGL_Or x1 x2)
  then show ?case by auto
next
  case (RGL_Mod x1 x2)
  then show ?case by auto
qed

lemma RGL_sy_dual_normalize:
  fixes g::"RGL_game"
  shows "RGL_sy_dual (RGL_sy_dual (RGL_normalize_game g)) = RGL_normalize_game g"
proof (induction g rule:RGL_game_induct)
  case (RGL_Atm_Game a)
  then show ?case by (cases a) (auto)
next
  case (RGL_Var x)
  then show ?case by auto
next
  case (RGL_Dual g1)
  then show ?case apply simp
next
  case (RGL_Test f)
  then show ?case sorry
next
  case (RGL_Choice g1 g2)
  then show ?case sorry
next
  case (RGL_Seq g1 g2)
  then show ?case sorry
next
  case (RGL_Rec x g)
  then show ?case sorry
qed

lemma RGL_sy_dual_normalize_comm:
  fixes g::"RGL_game"
  shows "RGL_normalize_game (RGL_sy_dual g) = RGL_sy_dual (RGL_normalize_game g)"
proof (induction g rule:RGL_game_induct)
  case (RGL_Atm_Game a)
  then show ?case by (cases a) (auto)
next
  case (RGL_Var x)
  then show ?case by auto
next
  case (RGL_Dual g1)
  then show ?case apply auto
next
  case (RGL_Test f)
  then show ?case sorry
next
  case (RGL_Choice g1 g2)
  then show ?case sorry
next
  case (RGL_Seq g1 g2)
  then show ?case sorry
next
  case (RGL_Rec x g)
  then show ?case sorry
qed

lemma RGL_sy_dual_invo:
  fixes g:: "RGL_game" and f::"RGL_fml"
  shows " RGL_sy_dual (RGL_sy_dual g) \<sim>\<^sub>g RGL_normalize_game g"
        "RGL_normalize_fml (RGL_sy_comp (RGL_sy_comp f)) = RGL_normalize_fml f"
proof (induction g and f)
  case (RGL_Atm_Game x)
  then show ?case by (cases x) (auto)
next
  case (RGL_Var x)
  then show ?case by auto
next
  case (RGL_Dual g1)
  then show ?case apply simp 
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

(* Problem: Clearly if g is not normal then (sy_dual (Dual g) = g) is not normal. 
  then normalize (Dual (Dual g')) = sy_dual (Dual g') = g' which is not normal if g' is not normal.
  Therefore need a new normalize function.
*)
lemma RGL_normalize_normal:
  fixes g::"RGL_game"
    and f::"RGL_fml"
  shows
  "RGL_nml_game (RGL_normalize_game g)"
  "RGL_nml_fml (RGL_normalize_fml f)"
proof (induction g and f)
  case (RGL_Atm_Game x)
  then show ?case by (simp add:RGL_nml_Atm_game)
next
  case (RGL_Var x)
  then show ?case by (simp add:RGL_nml_Var)
next
  case (RGL_Dual g1)
  then show ?case
  proof (induction g1 rule:RGL_game_induct)
    case (RGL_Atm_Game a)
    then show ?case sorry
  next
    case (RGL_Var x)
    then show ?case sorry
  next
    case (RGL_Dual g11)
    then show ?case 
  next
    case (RGL_Test f)
    then show ?case sorry
  next
    case (RGL_Choice g11 g12)
    then show ?case
    proof (simp)
      assume a1:"(RGL_nml_game (RGL_normalize_game g11) \<Longrightarrow> RGL_nml_game (RGL_sy_dual (RGL_normalize_game g11)))"
        and a2:"(RGL_nml_game (RGL_normalize_game g12) \<Longrightarrow> RGL_nml_game (RGL_sy_dual (RGL_normalize_game g12)))"
        and a3:"RGL_nml_game (RGL_Choice (RGL_normalize_game g11) (RGL_normalize_game g12))"
      from a3 have a4:"RGL_nml_game (RGL_normalize_game g11)" apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
      from a3 have a5:"RGL_nml_game (RGL_normalize_game g12)" apply cases unfolding RGL_DTest_def RGL_DChoice_def RGL_DRec_def by auto
      show "RGL_nml_game (RGL_DChoice (RGL_sy_dual (RGL_normalize_game g11)) (RGL_sy_dual (RGL_normalize_game g12)))"
        using a4 a5 RGL_nml_DChoice a1 a2 by auto
    qed
  next
    case (RGL_Seq g1 g2)
    then show ?case sorry
  next
    case (RGL_Rec x g11)
    then show ?case sorry
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

(* Subgame relation over normal forms *)
inductive RGL_subgm:: "RGL_game \<Rightarrow> RGL_game \<Rightarrow> bool" where
  RGL_subgm_var: "RGL_subgm (RGL_Var x) (RGL_Dual (RGL_Var x))"
| RGL_subgm_choicel: "RGL_subgm a (RGL_Choice a b)"
| RGL_subgm_choicer: "RGL_subgm a (RGL_Choice b a)"
| RGL_subgm_dchoicel: "RGL_subgm a (RGL_DChoice a b)"
| RGL_subgm_dchoicer: "RGL_subgm a (RGL_DChoice b a)"
| RGL_subgm_seql: "RGL_subgm a (RGL_Seq a b)"
| RGL_subgm_seqr: "RGL_subgm a (RGL_Seq b a)"
| RGL_subgm_tst: "RGL_subgm (RGL_Test f) (RGL_DTest f)"
| RGL_subgm_rec: "RGL_subgm a (RGL_Rec x a)"
| RGL_subgm_drec: "RGL_subgm a (RGL_DRec x a)"

definition RGL_subgm_rt where "RGL_subgm_rt = star RGL_subgm"


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


(* If one dualizes a nml game, which can have at most one dual, the result has at most two duals. *)
lemma RGL_nml_dual_free__ddnml:
  "RGL_nml_game g \<Longrightarrow> RGL_ddnml_game (RGL_dual_free x g)"
  "RGL_nml_fml f \<Longrightarrow> RGL_ddnml_fml (RGL_dual_free_fml x f)"
proof (induction g and f rule:RGL_nml_game_RGL_nml_fml.inducts)
  case (RGL_nml_Atm_game a)
  then show ?case by (simp add:Syntax.RGL_ddnml_Atm_game)
next
  case (RGL_nml_Var y)
  then show ?case by (cases "x=y") 
    (auto simp add:Syntax.RGL_ddnml_DVar Syntax.RGL_ddnml_Var)
next
  case (RGL_nml_DVar y)
  then show ?case by (cases "x=y") (auto simp add:Syntax.RGL_ddnml_DVar Syntax.RGL_ddnml_DDVar)
next
  case (RGL_nml_Test f)
  then show ?case apply simp
    using RGL_closed_dual_free_id(2)[of "f""x"] Syntax.RGL_ddnml_Test by auto
next
  case (RGL_nml_DTest f)
  then show ?case unfolding RGL_DTest_def using 
    RGL_nml__ddnml RGL_ddnml_DTest[OF \<open>RGL_ddnml_fml (RGL_dual_free_fml x f)\<close>] 
    RGL_closed_dual_free__closed(2)[of "f""x"]
    unfolding RGL_DTest_def by auto
next
  case (RGL_nml_Choice g1 g2)
  then show ?case using Syntax.RGL_ddnml_Choice by auto
next
  case (RGL_nml_DChoice g1 g2)
  then show ?case  
    using Syntax.RGL_ddnml_DChoice unfolding RGL_DChoice_def by simp
next
  case (RGL_nml_Seq g1 g2)
  then show ?case using Syntax.RGL_ddnml_Seq by auto
next
  case (RGL_nml_Rec g1 y)
  then show ?case using RGL_ddnml_Rec RGL_nml__ddnml by (cases "x=y") (auto)
next
  case (RGL_nml_DRec g1 y)
  then show ?case using RGL_ddnml_DRec RGL_nml__ddnml unfolding RGL_DRec_def 
    apply (cases "x=y") apply simp
  proof -
    assume ass:"x\<noteq>y" and a1:"\<And>g x. RGL_ddnml_game g \<Longrightarrow> RGL_ddnml_game (RGL_Dual (RGL_Rec x (RGL_Dual (RGL_dual_free x g))))"
      and a2:"RGL_ddnml_game (RGL_dual_free x g1)"
    then have "RGL_dual_free x (RGL_Dual (RGL_Rec y (RGL_Dual (RGL_dual_free y g1)))) 
      = RGL_Dual (RGL_Rec y (RGL_Dual (RGL_dual_free x (RGL_dual_free y g1))))" by auto
    also have "... = RGL_Dual (RGL_Rec y (RGL_Dual (RGL_dual_free y (RGL_dual_free x g1))))" using RGL_dual_free_vars_comm by auto
    finally have b:"RGL_dual_free x (RGL_Dual (RGL_Rec y (RGL_Dual (RGL_dual_free y g1)))) = RGL_Dual (RGL_Rec y (RGL_Dual (RGL_dual_free y (RGL_dual_free x g1))))" by auto
    then show "RGL_ddnml_game (RGL_dual_free x (RGL_Dual (RGL_Rec y (RGL_Dual (RGL_dual_free y g1)))))"
      using a1[OF a2] b by auto
  qed
next
  case (RGL_nml_Atm_fml f)
  then show ?case using RGL_ddnml_Atm_fml by auto
next
  case (RGL_nml_Not_atm f)
  then show ?case using RGL_ddnml_Not_atm by auto
next
  case (RGL_nml_Or f1 f2)
  then show ?case using RGL_ddnml_Or by auto
next
  case (RGL_nml_And f1 f2)
  then show ?case using RGL_ddnml_And unfolding RGL_And_def by auto
next
  case (RGL_nml_Mod g f)
  then show ?case using RGL_ddnml_Mod by auto
qed

lemma RGL_nml_sy_dual__ddnml_Rec: 
  assumes "RGL_nml_game g" and "RGL_nml_game (RGL_sy_dual g)" 
  shows "RGL_ddnml_game (RGL_DRec x (RGL_dual_free x (RGL_sy_dual g)))"
  using assms
proof (induction g rule:RGL_nml_game_induct)
  case (rGL_nml_Atm_Game a)
  then show ?case using RGL_nml_DRec RGL_nml_Atm_game RGL_nml__ddnml
    apply (cases a) by auto
next
  case (rGL_nml_Var y)
  then show ?case apply (cases "x=y") 
    using RGL_nml__ddnml RGL_ddnml_DRec RGL_ddnml_DDVar by auto
next
  case (rGL_nml_DVar y)
  then show ?case apply (cases "x=y")
    using RGL_nml__ddnml RGL_ddnml_DRec RGL_ddnml_DVar by auto
next
  case (rGL_nml_Test f)
  then show ?case
  proof (simp)
    from rGL_nml_Test.prems(1) have "RGL_fml_closed f"
      by (smt (verit) RGL_DChoice_def RGL_DRec_def RGL_DTest_def RGL_fml_closed_def RGL_game.distinct(15,23,31,33,35) RGL_nml_game.cases free_var_game.simps(1,4))
    
  qed
next
  case (rGL_nml_DTest f)
  then show ?case sorry
next
  case (rGL_nml_Choice g1 g2)
  then show ?case sorry
next
  case (rGL_nml_DChoice g1 g2)
  then show ?case sorry
next
  case (rGL_nml_Seq g1 g2)
  then show ?case sorry
next
  case (rGL_nml_Rec x g)
  then show ?case sorry
next
  case (rGL_nml_DRec x g)
  then show ?case sorry
qed

(* sy_dual does not preserve normality. Example: sy_dual (rx.x) = DRec x (dualize_free x (Dual x)) = DRec x (Dual (Dual x)), which is not normal.
  The best we can ask for is ddnml.
  This is due to the lack of normalization that leaves Dual unchanged.
  normalize (DRec x (Dual (Dual x))) = normalize Dual ((Rec x (dualize x (Dual (Dual (Dual x))))))
      = sy
  *)
lemma RGL_nml_sy_dual__ddnml:
  fixes g::"RGL_game" and f::"RGL_fml"
  shows
  "RGL_nml_game g \<Longrightarrow> RGL_ddnml_game (RGL_sy_dual g)"
  "RGL_nml_fml f \<Longrightarrow> RGL_ddnml_fml (RGL_sy_comp f)"
  thm RGL_nml_game_nml_fml_inducts[where \<alpha>="g" and f="f"]
  thm RGL_nml_game_nml_fml_inducts[where P=\<open>\<lambda>g. RGL_nml_game (RGL_sy_dual g)\<close> and Q=\<open>\<lambda>f. RGL_nml_fml (RGL_sy_comp f)\<close> and \<alpha>=\<open>g\<close>
        and f=\<open>f\<close>]
proof (induction g and f rule:RGL_nml_game_RGL_nml_fml.inducts)
  case (RGL_nml_Atm_game a)
  then show ?case by (cases a) (auto simp add:Syntax.RGL_ddnml_Atm_game)
next
  case (RGL_nml_Var x)
  then show ?case by (auto simp add:RGL_ddnml_DVar)
next
  case (RGL_nml_DVar x)
  then show ?case by (auto simp add:RGL_ddnml_Var)
next
  case (RGL_nml_Test f)
  then show ?case using RGL_nml__ddnml RGL_ddnml_DTest by force
next
  case (RGL_nml_DTest f)
  then show ?case using RGL_nml__ddnml RGL_ddnml_Test unfolding RGL_DTest_def by simp
next
  case (RGL_nml_Choice g1 g2)
  then show ?case by (simp add:RGL_ddnml_DChoice)
next
  case (RGL_nml_DChoice g1 g2)
  then show ?case unfolding RGL_DChoice_def
    by (auto simp add:RGL_ddnml_Choice)
next
  case (RGL_nml_Seq g1 g2)
  then show ?case by (simp add:Syntax.RGL_ddnml_Seq)
next
  case (RGL_nml_Rec g x)
  then show ?case apply simp sorry (* need normal induction *)
next
  case (RGL_nml_DRec g x)
  then show ?case sorry (* need induction *)
next
  case (RGL_nml_Atm_fml f)
  then show ?case using Syntax.RGL_ddnml_Not_atm by simp
next
  case (RGL_nml_Not_atm f)
  then show ?case using Syntax.RGL_ddnml_Atm_fml by simp
next
  case (RGL_nml_Or f1 f2)
  then show ?case using Syntax.RGL_ddnml_And by simp
next
  case (RGL_nml_And f1 f2)
  then show ?case using Syntax.RGL_ddnml_Or unfolding RGL_And_def by auto
next
  case (RGL_nml_Mod g f)
  then show ?case using Syntax.RGL_ddnml_Mod by auto
qed


(* nodual predicate to detect the absence of x^d. 
  Note: does not only test for free variables. For example in rx.\<alpha>, the intention is for \<alpha> to not contain x^d. 
  TODO: fix a set of identifiers. POLISHING. ENUM for context.
*)
inductive RGL_gm_nodual:: "ident \<Rightarrow> RGL_game \<Rightarrow> bool"
  and RGL_fml_nodual:: "ident \<Rightarrow> RGL_fml \<Rightarrow> bool" for x where
    RGL_gm_nodual_atm: "(RGL_gm_nodual x) (RGL_Atm_Game a)"
  | RGL_gm_nodual_Var: "(RGL_gm_nodual x) (RGL_Var y)"
  | RGL_gm_nodual_DVar: "x\<noteq>y \<Longrightarrow> RGL_gm_nodual x (RGL_Dual (RGL_Var y))"
  | RGL_gm_nodual_Test: "RGL_fml_nodual x f \<Longrightarrow> RGL_fml_closed f \<Longrightarrow> RGL_gm_nodual x (RGL_Test f)"
  | RGL_gm_nodual_DTest: "RGL_fml_nodual x f \<Longrightarrow> RGL_fml_closed f \<Longrightarrow> RGL_gm_nodual x (RGL_DTest f)"
  | RGL_gm_nodual_Choice: "RGL_gm_nodual x g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> RGL_gm_nodual x (RGL_Choice g1 g2)"
  | RGL_gm_nodual_DChoice: "RGL_gm_nodual x g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> RGL_gm_nodual x (RGL_DChoice g1 g2)"
  | RGL_gm_nodual_Seq: "RGL_gm_nodual x g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> RGL_gm_nodual x (RGL_Seq g1 g2)"
  | RGL_gm_nodual_Rec: "RGL_gm_nodual x g \<Longrightarrow> RGL_gm_nodual x (RGL_Rec y g)"
  | RGL_gm_nodual_DRec: "RGL_gm_nodual x g \<Longrightarrow> RGL_gm_nodual x (RGL_DRec y g)"
  | RGL_fml_nodual_atm: "RGL_fml_nodual x (RGL_Atm_fml P)"
  | RGL_fml_nodual_negatm: "RGL_fml_nodual x (RGL_Not (RGL_Atm_fml P))"
  | RGL_fml_nodual_Or: "RGL_fml_nodual x f1 \<Longrightarrow> RGL_fml_nodual x f2 \<Longrightarrow> RGL_fml_nodual x (RGL_Or f1 f2)"
  | RGL_fml_nodual_And: "RGL_fml_nodual x f1 \<Longrightarrow> RGL_fml_nodual x f2 \<Longrightarrow> RGL_fml_nodual x (RGL_And f1 f2)"
  | RGL_fml_nodual_Mod: "RGL_fml_nodual x f \<Longrightarrow> RGL_gm_nodual x g \<Longrightarrow> RGL_fml_nodual x (RGL_Mod g f)"

lemma RGL_fml_nodual_induct [case_names atm negatm or_f and_f mod_f]:
  "(\<And> f. P (RGL_Atm_fml f))
    \<Longrightarrow> (\<And> f. P (RGL_Not (RGL_Atm_fml f)))
    \<Longrightarrow> (\<And> f1 f2. RGL_fml_nodual x f1 \<Longrightarrow> P f1 \<Longrightarrow> RGL_fml_nodual x f2 \<Longrightarrow> P f2\<Longrightarrow> P (RGL_Or f1 f2))
    \<Longrightarrow> (\<And> f1 f2. RGL_fml_nodual x f1 \<Longrightarrow> P f1 \<Longrightarrow> RGL_fml_nodual x f2 \<Longrightarrow> P f2\<Longrightarrow> P (RGL_And f1 f2))
    \<Longrightarrow> (\<And> g f. RGL_gm_nodual x g \<Longrightarrow> RGL_fml_nodual x f \<Longrightarrow> P f \<Longrightarrow> P (RGL_Mod g f))
    \<Longrightarrow> (RGL_fml_nodual x f \<Longrightarrow> P f)
  "
  by (auto simp add:Syntax.RGL_gm_nodual_RGL_fml_nodual.inducts(2))

lemma RGL_gm_nodual_induct [case_names atm var dvar tst dtst choi dchoi seq rec drec]:
  "(\<And> a. P (RGL_Atm_Game a))
    \<Longrightarrow> (\<And> x. P (RGL_Var x))
    \<Longrightarrow> (\<And> x. P (RGL_Dual (RGL_Var x)))
    \<Longrightarrow> (\<And> f. P (RGL_Test f))
    \<Longrightarrow> (\<And> f. P (RGL_DTest f))
    \<Longrightarrow> (\<And> g1 g2. RGL_gm_nodual x g1 \<Longrightarrow> P g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_Choice g1 g2))
    \<Longrightarrow> (\<And> g1 g2. RGL_gm_nodual x g1 \<Longrightarrow> P g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_DChoice g1 g2))
    \<Longrightarrow> (\<And> g1 g2. RGL_gm_nodual x g1 \<Longrightarrow> P g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> P g2 \<Longrightarrow> P (RGL_Seq g1 g2))
    \<Longrightarrow> (\<And> y g. RGL_gm_nodual x g \<Longrightarrow> P g \<Longrightarrow> P (RGL_Rec y g))
    \<Longrightarrow> (\<And> y g. RGL_gm_nodual x g \<Longrightarrow> P g \<Longrightarrow> P (RGL_DRec y g))
    \<Longrightarrow> (RGL_gm_nodual x g \<Longrightarrow> P g)
  "
  using RGL_gm_nodual_RGL_fml_nodual.inducts(1)[where ?x="x" and ?x1.0="g" and ?P1.0="P" and ?P2.0="\<lambda>x. True"] by auto


(* If a formula has no dual for any variable, then it is normal. This follows because we constructed 
    RGL_nodual and RGL_nml in accordance to normality.
   This enables us to use conclusions from normality in inductive proofs involving nodual. *)
lemma RGL_nodual__nml:
   "(RGL_gm_nodual x g \<longrightarrow> RGL_nml_game g) \<and> (RGL_fml_nodual x f \<longrightarrow> RGL_nml_fml f)"
   using RGL_gm_nodual_RGL_fml_nodual.induct[where ?P1.0="RGL_nml_game" and ?P2.0="RGL_nml_fml" and ?x1.0="g" and ?x2.0="f"]
proof
  show "\<And>a. RGL_nml_game (RGL_Atm_Game a)" using RGL_nml_Atm_game by auto
next
  fix y show "RGL_nml_game (RGL_Var y)"using RGL_nml_Var[of "y"] by auto
next
  fix y show "x \<noteq> y \<Longrightarrow> RGL_nml_game (RGL_Dual (RGL_Var y))" using RGL_nml_DVar[of "y"] by auto
next
  fix f1 show "RGL_fml_nodual x f1 \<Longrightarrow> RGL_nml_fml f1 \<Longrightarrow> RGL_fml_closed f1 \<Longrightarrow> RGL_nml_game (RGL_Test f1)" using RGL_nml_Test[of "f1"] by auto
next
  fix f1 show "RGL_fml_nodual x f1 \<Longrightarrow> RGL_nml_fml f1 \<Longrightarrow> RGL_fml_closed f1 \<Longrightarrow> RGL_nml_game (RGL_DTest f1)" using RGL_nml_DTest[of "f1"] by auto
next
  fix g1 g2 show "RGL_gm_nodual x g1 \<Longrightarrow> RGL_nml_game g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> RGL_nml_game (RGL_Choice g1 g2)"
    using RGL_nml_Choice[of "g1""g2"] by auto
next
  fix g1 g2 show "RGL_gm_nodual x g1 \<Longrightarrow> RGL_nml_game g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> RGL_nml_game (RGL_DChoice g1 g2)"
    using RGL_nml_DChoice[of "g1""g2"] by auto
next
  fix g1 g2 show "RGL_gm_nodual x g1 \<Longrightarrow> RGL_nml_game g1 \<Longrightarrow> RGL_gm_nodual x g2 \<Longrightarrow> RGL_nml_game g2 \<Longrightarrow> RGL_nml_game (RGL_Seq g1 g2)"
    using RGL_nml_Seq[of "g1""g2"] by auto
next
  fix g1 y show "RGL_gm_nodual x g1 \<Longrightarrow> RGL_nml_game g1 \<Longrightarrow> RGL_nml_game (RGL_Rec y g1)" using RGL_nml_Rec[of "g1""y"] by auto
next
  fix g1 y show "RGL_gm_nodual x g1 \<Longrightarrow> RGL_nml_game g1 \<Longrightarrow> RGL_nml_game (RGL_DRec y g1)" using RGL_nml_DRec[of "g1""y"] by auto
next
  fix P show "RGL_nml_fml (RGL_Atm_fml P)" using RGL_nml_Atm_fml by auto
next
  fix P show "RGL_nml_fml (RGL_Not (RGL_Atm_fml P))" using RGL_nml_Not_atm by auto
next
  fix f1 f2 show "RGL_fml_nodual x f1 \<Longrightarrow> RGL_nml_fml f1 \<Longrightarrow> RGL_fml_nodual x f2 \<Longrightarrow> RGL_nml_fml f2 \<Longrightarrow> RGL_nml_fml (RGL_Or f1 f2)"
    using RGL_nml_Or by auto
next
  fix f1 f2 show "RGL_fml_nodual x f1 \<Longrightarrow> RGL_nml_fml f1 \<Longrightarrow> RGL_fml_nodual x f2 \<Longrightarrow> RGL_nml_fml f2 \<Longrightarrow> RGL_nml_fml (RGL_And f1 f2)"
    using RGL_nml_And by auto
next
  fix f1 g1 show "RGL_fml_nodual x f1 \<Longrightarrow> RGL_nml_fml f1 \<Longrightarrow> RGL_gm_nodual x g1 \<Longrightarrow> RGL_nml_game g1 \<Longrightarrow> RGL_nml_fml (RGL_Mod g1 f1)"
    using RGL_nml_Mod by auto
next
  show "RGL_gm_nodual x g \<longrightarrow> RGL_nml_game g \<Longrightarrow> RGL_fml_nodual x f \<longrightarrow> RGL_nml_fml f \<Longrightarrow> (RGL_gm_nodual x g \<longrightarrow> RGL_nml_game g) \<and> (RGL_fml_nodual x f \<longrightarrow> RGL_nml_fml f)"
    by auto
qed

(* Replace this to be a part (inductive predicate) of FLC grammar. e.g. Lmu_fml (FLC_Id) | Lmu_fml f \<Longrightarrow> Lmu_fml (Not FLC_Atm f) | ...
  construct induction principle. *)
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

fun FLC_sy_comp ::"'a FLC_fml \<Rightarrow> 'a FLC_fml" where
  "FLC_sy_comp (FLC_Atm_fml f) = FLC_Not f"
|   "FLC_sy_comp (FLC_Not f) = FLC_Atm_fml f"
|   "FLC_sy_comp (FLC_Var x) = FLC_Var x"
|   "FLC_sy_comp (FLC_Id) = undefined"
|   "FLC_sy_comp (FLC_Chop v va) = undefined"
|   "FLC_sy_comp (FLC_Or f1 f2) = FLC_And (FLC_sy_comp f1) (FLC_sy_comp f2)"
|   "FLC_sy_comp (FLC_And f1 f2) = FLC_Or (FLC_sy_comp f1) (FLC_sy_comp f2)"
|   "FLC_sy_comp (FLC_Mod_Exist a f) = FLC_Mod_Forall a (FLC_sy_comp f)"
|   "FLC_sy_comp (FLC_Mod_Forall a f) = FLC_Mod_Exist a (FLC_sy_comp f)"
|   "FLC_sy_comp (FLC_mu x f) = FLC_nu x (FLC_sy_comp f)"
|   "FLC_sy_comp (FLC_nu x f) = FLC_mu x (FLC_sy_comp f)"

definition Star where
  "Star x \<phi> = FLC_mu x (FLC_Or FLC_Id (FLC_Chop \<phi> (FLC_Var x)))"

primrec FLC_free_var:: "'a FLC_fml \<Rightarrow> 'a set" where
  "FLC_free_var (FLC_Id) = {}"
| "FLC_free_var (FLC_Atm_fml f) = {}"
| "FLC_free_var (FLC_Not f) = {}"
| "FLC_free_var (FLC_Var x) = {x}"
| "FLC_free_var (FLC_Or f1 f2) = FLC_free_var f1 \<union> FLC_free_var f2"
| "FLC_free_var (FLC_And f1 f2) = FLC_free_var f1 \<union> FLC_free_var f2"
| "FLC_free_var (FLC_Chop f1 f2) = FLC_free_var f1 \<union> FLC_free_var f2"
| "FLC_free_var (FLC_Mod_Exist a f) = FLC_free_var f"
| "FLC_free_var (FLC_Mod_Forall a f) = FLC_free_var f"
| "FLC_free_var (FLC_mu x f) = FLC_free_var f - {x}"
| "FLC_free_var (FLC_nu x f) = FLC_free_var f - {x}"

inductive L_Star :: "'a FLC_fml \<Rightarrow> bool" where
  "L_Star (FLC_Id)"
| "L_Star (FLC_Atm_fml f)"
| "L_Star f \<Longrightarrow> L_Star (FLC_sy_comp f)"
| "L_Star f \<Longrightarrow> L_Star g \<Longrightarrow> L_Star (FLC_Or f g)"
| "L_Star f \<Longrightarrow> L_Star (FLC_Mod_Exist a f)"
| "L_Star f \<Longrightarrow> L_Star g \<Longrightarrow> L_Star (FLC_Chop f g)"
| "L_Star f \<Longrightarrow> x \<notin> FLC_free_var f \<Longrightarrow> L_Star (Star x f)"

end