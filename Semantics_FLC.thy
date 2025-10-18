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
  "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I (FLC_Atm_fml f) = (PropInterp N) f"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"
|   "FLC_sem N I FLC_Id = id"







end