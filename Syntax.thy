theory Syntax
imports
  Complex_Main
begin 

\<comment>\<open>We realise the syntax of GL, GLs, RGL, FLC, Lmu, LStar.
  Separable formulas of Lmu should be realised as an inductive property.
  right-linearity in RGL is also an inductive property. \<close>

type_synonym Atm_game = "int"
type_synonym Atm_fml = "int"

datatype atm_gm = Agl_gm "int" | Dmn_gm "int"

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

datatype GLs_ext_game =
  GLs_ext_Atm_Game "Atm_game"
  | GLs_ext_Sabo "Atm_game"
  | GLs_ext_DSabo "Atm_game"
  | GLs_ext_Dual "GLs_ext_game"
  | GLs_ext_Test "GLs_ext_fml"
  | GLs_ext_Choice "GLs_ext_game" "GLs_ext_game"
  | GLs_ext_DChoice "GLs_ext_game" "GLs_ext_game"
  | GLs_ext_DTest "GLs_ext_fml"
  | GLs_ext_Seq "GLs_ext_game" "GLs_ext_game"
  | GLs_ext_Star "GLs_ext_game"
  | GLs_ext_Cross "GLs_ext_game"
and GLs_ext_fml = 
  GLs_ext_Atm_fml "Atm_fml"
| GLs_ext_Not "GLs_ext_fml"
| GLs_ext_Or "GLs_ext_fml" "GLs_ext_fml"
| GLs_ext_And "GLs_ext_fml" "GLs_ext_fml"
| GLs_ext_Mod "GLs_ext_game" "GLs_ext_fml"

fun GLs_syn_comp :: "GLs_ext_fml \<Rightarrow> GLs_ext_fml"
  and GLs_syn_dual :: "GLs_ext_game \<Rightarrow> GLs_ext_game"
  where 
  "GLs_syn_comp (GLs_ext_Atm_fml P) = GLs_ext_Not (GLs_ext_Atm_fml P)"
|   "GLs_syn_comp (GLs_ext_Not f) = f"
|   "GLs_syn_comp (GLs_ext_Or f1 f2) = GLs_ext_And (GLs_syn_comp f1) (GLs_syn_comp f2)"
|   "GLs_syn_comp (GLs_ext_And f1 f2) = GLs_ext_Or (GLs_syn_comp f1) (GLs_syn_comp f2)"
|   "GLs_syn_comp (GLs_ext_Mod g f) = GLs_ext_Mod (GLs_syn_dual g) (GLs_syn_comp f)"
|   "GLs_syn_dual (GLs_ext_Atm_Game a) = GLs_ext_Dual (GLs_ext_Atm_Game a)"
|   "GLs_syn_dual (GLs_ext_Sabo a) = GLs_ext_DSabo a"
|   "GLs_syn_dual (GLs_ext_DSabo a) = GLs_ext_Sabo a"   
|   "GLs_syn_dual (GLs_ext_Dual g) = g"
|   "GLs_syn_dual (GLs_ext_Test f) = GLs_ext_DTest f"
|   "GLs_syn_dual (GLs_ext_Choice g1 g2) = GLs_ext_DChoice (GLs_syn_dual g1) (GLs_syn_dual g2)"
|   "GLs_syn_dual (GLs_ext_DChoice g1 g2) = GLs_ext_Choice (GLs_syn_dual g1) (GLs_syn_dual g2)"
|   "GLs_syn_dual (GLs_ext_DTest f) = GLs_ext_Test f"
|   "GLs_syn_dual (GLs_ext_Seq g1 g2) = GLs_ext_Seq (GLs_syn_dual g1) (GLs_syn_dual g2)"
|   "GLs_syn_dual (GLs_ext_Star g) = GLs_ext_Cross (GLs_syn_dual g)"
|   "GLs_syn_dual (GLs_ext_Cross g) = GLs_ext_Star (GLs_syn_dual g)"

datatype 'c RGL_game =
  RGL_Atm_Game "Atm_game"
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

datatype 'c RGL_ext_game =
  RGL_ext_Atm_Game "Atm_game"
  | RGL_ext_Atm_Game_Dual "Atm_game"
  | RGL_ext_Var 'c
  | RGL_ext_Var_Dual 'c
  | RGL_ext_Test "'c RGL_ext_fml"
  | RGL_ext_Test_Dual "'c RGL_ext_fml"
  | RGL_ext_Choice "'c RGL_ext_game" "'c RGL_ext_game"
  | RGL_ext_Choice_Dual "'c RGL_ext_game" "'c RGL_ext_game"
  | RGL_ext_Seq "'c RGL_ext_game" "'c RGL_ext_game"
  | RGL_ext_Rec 'c "'c RGL_ext_game"
  | RGL_ext_Rec_Dual 'c "'c RGL_ext_game"
and 
  'c RGL_ext_fml = 
    RGL_ext_Atm_fml "Atm_fml"
  | RGL_ext_Not "'c RGL_ext_fml"
  | RGL_ext_Or "'c RGL_ext_fml" "'c RGL_ext_fml"
  | RGL_ext_And "'c RGL_ext_fml" "'c RGL_ext_fml"
  | RGL_ext_Mod "'c RGL_ext_game" "'c RGL_ext_fml"   

definition RGL_ext_fml_atomic :: "'c RGL_ext_fml \<Rightarrow> bool" where
  "RGL_ext_fml_atomic f \<equiv> \<exists>P. (f = RGL_ext_Atm_fml P)"

\<comment>\<open>Tests if an RGL_ext_fml or an RGL_ext_game is in normal form\<close>
definition RGL_ext_fml_normal :: "'c RGL_ext_fml \<Rightarrow> bool" where
  "RGL_ext_fml_normal f \<equiv> \<forall>g. (f = RGL_ext_Not g \<longrightarrow> RGL_ext_fml_atomic g)"


\<comment>\<open>Tests if a RGL_ext_fml contains no explicit ()^d constructor on a variable x.
  Does not go through binders.
\<close>
primrec RGL_ext_game_no_dual :: "'c \<Rightarrow> 'c RGL_ext_game \<Rightarrow> bool"
  and RGL_ext_fml_no_dual :: "'c \<Rightarrow> 'c RGL_ext_fml \<Rightarrow> bool" where
  "RGL_ext_game_no_dual x (RGL_ext_Atm_Game a) = True"
|   "RGL_ext_game_no_dual x (RGL_ext_Atm_Game_Dual a) = True"
|   "RGL_ext_game_no_dual x (RGL_ext_Var y) = True"
|   "RGL_ext_game_no_dual x (RGL_ext_Var_Dual y) = (if x=y then False else True)"
|   "RGL_ext_game_no_dual x (RGL_ext_Test f) = RGL_ext_fml_no_dual x f"
|   "RGL_ext_game_no_dual x (RGL_ext_Test_Dual f) = RGL_ext_fml_no_dual x f"
|   "RGL_ext_game_no_dual x (RGL_ext_Choice g1 g2) = (RGL_ext_game_no_dual x g1 \<and> RGL_ext_game_no_dual x g2)"
|   "RGL_ext_game_no_dual x (RGL_ext_Choice_Dual g1 g2) = (RGL_ext_game_no_dual x g1 \<and> RGL_ext_game_no_dual x g2)"
|   "RGL_ext_game_no_dual x (RGL_ext_Seq g1 g2) = (RGL_ext_game_no_dual x g1 \<and> RGL_ext_game_no_dual x g2)"
|   "RGL_ext_game_no_dual x (RGL_ext_Rec y g) = (if x=y then True else RGL_ext_game_no_dual x g)"
|   "RGL_ext_game_no_dual x (RGL_ext_Rec_Dual y g) = (if x=y then True else RGL_ext_game_no_dual x g)"
|   "RGL_ext_fml_no_dual x (RGL_ext_Atm_fml P) = True"
|   "RGL_ext_fml_no_dual x (RGL_ext_Not f) = RGL_ext_fml_no_dual x f"
|   "RGL_ext_fml_no_dual x (RGL_ext_Or f1 f2) = (RGL_ext_fml_no_dual x f1 \<and> RGL_ext_fml_no_dual x f2)"
|   "RGL_ext_fml_no_dual x (RGL_ext_And f1 f2) = (RGL_ext_fml_no_dual x f1 \<and> RGL_ext_fml_no_dual x f2)"
|   "RGL_ext_fml_no_dual x (RGL_ext_Mod g f) = (RGL_ext_game_no_dual x g \<and> RGL_ext_fml_no_dual x f) "


\<comment>\<open>outputs free variables of RGL fml and games\<close>
primrec free_var_ext:: "'c RGL_ext_fml \<Rightarrow> 'c set" 
  and free_var_ext_game where
  "free_var_ext (RGL_ext_Atm_fml f) = {}"
|  "free_var_ext (RGL_ext_Not f) = free_var_ext f"
|  "free_var_ext (RGL_ext_Or f g) = free_var_ext f \<union> free_var_ext g"
|  "free_var_ext (RGL_ext_And f g) = free_var_ext f \<union> free_var_ext g"
|  "free_var_ext (RGL_ext_Mod g f) = free_var_ext_game g"
|  "free_var_ext_game (RGL_ext_Atm_Game a) = {}"
|  "free_var_ext_game (RGL_ext_Atm_Game_Dual a) = {}"
|  "free_var_ext_game (RGL_ext_Var x) = {x}"
|  "free_var_ext_game (RGL_ext_Var_Dual x) = {x}"
|  "free_var_ext_game (RGL_ext_Test f) = free_var_ext f"
|  "free_var_ext_game (RGL_ext_Test_Dual f) = free_var_ext f"
|  "free_var_ext_game (RGL_ext_Choice g1 g2) = free_var_ext_game g1 \<union> free_var_ext_game g2"
|  "free_var_ext_game (RGL_ext_Choice_Dual g1 g2) = free_var_ext_game g1 \<union> free_var_ext_game g2"
|  "free_var_ext_game (RGL_ext_Seq g1 g2) = free_var_ext_game g1 \<union> free_var_ext_game g2"
|  "free_var_ext_game (RGL_ext_Rec x g) = free_var_ext_game g - {x}"
|  "free_var_ext_game (RGL_ext_Rec_Dual x g) = free_var_ext_game g - {x}"

primrec free_var:: "'c RGL_fml \<Rightarrow> 'c set" 
  and free_var_game :: "'c RGL_game \<Rightarrow> 'c set" where
  "free_var (RGL_Atm_fml f) = {}"
|  "free_var (RGL_Not f) = free_var f"
|  "free_var (RGL_Or f g) = free_var f \<union> free_var g"
|  "free_var (RGL_Mod g f) = free_var_game g"
|  "free_var_game (RGL_Atm_Game a) = {}"
|  "free_var_game (RGL_Var x) = {x}"
|  "free_var_game (RGL_Dual g) = free_var_game g"
|  "free_var_game (RGL_Test f) = free_var f"
|  "free_var_game (RGL_Choice g1 g2) = free_var_game g1 \<union> free_var_game g2"
|  "free_var_game (RGL_Seq g1 g2) = free_var_game g1 \<union> free_var_game g2"
|  "free_var_game (RGL_Rec x g) = free_var_game g - {x}"

definition RGL_ext_game_no_free_dual :: "'c \<Rightarrow> 'c RGL_ext_game \<Rightarrow> bool" where
  "RGL_ext_game_no_free_dual x g \<equiv> x\<in>free_var_ext_game g \<longrightarrow> RGL_ext_game_no_dual x g"

\<comment>\<open>tests if an RGL fml is closed\<close>
definition RGL_ext_fml_closed :: "'c RGL_ext_fml \<Rightarrow> bool" where
  "RGL_ext_fml_closed f = (free_var_ext f = {})"

definition RGL_fml_closed :: "'c RGL_fml \<Rightarrow> bool" where
  "RGL_fml_closed f = (free_var f = {})"

\<comment>\<open>An RGL game is in normal form if 1) ?\<phi> for closed \<phi> only; 2)rx.\<alpha>
  only has x occurring in a scope with even number of duals in \<alpha>. 
  Hence all are in normal form except in the negation of these cases;
  hence we only need to worry about the forms ? and r.
\<close>

\<comment>\<open>This function tests if the given RGL game (not RGL_ext_game) contains a free variable x with ALL even number of duals.
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
  "RGL_Rec_valid g \<equiv> \<forall>x. (\<exists>h. g = RGL_Rec x h \<longrightarrow> RGL_even_dual True x h)"

definition RGL_Test_valid :: "'c RGL_game \<Rightarrow> bool" where
  "RGL_Test_valid g \<equiv> \<forall>f. (g = RGL_Test f \<longrightarrow> RGL_fml_closed f)"

definition RGL_game_valid :: "'c RGL_game \<Rightarrow> bool" where 
  "RGL_game_valid g \<equiv> (RGL_Rec_valid g \<and> RGL_Test_valid g)"

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