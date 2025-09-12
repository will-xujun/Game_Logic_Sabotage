theory Syntax
imports
  Complex_Main
begin 

\<comment>\<open>We realise the syntax of GL, GLs, RGL, FLC, Lmu, LStar.
  Separable formulas of Lmu should be realised as an inductive property.
  right-linearity in RGL is also an inductive property. \<close>

datatype Atm_game = "int"
datatype Atm_fml = "int"

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
  GLs_Atm_Game "Atm_game"
  | GLs_Sabo "Atm_game"
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