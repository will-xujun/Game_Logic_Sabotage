theory Semantics
imports
  "Syntax"
  
begin
\<comment>\<open>We realise the semantics of GL, GLs, RGL, FLC, Lmu, LStar.\<close>

type_synonym world_type = "unit set"
type_synonym atm_fmls = "Atm_fml set"
type_synonym atm_games = "Atm_game set"

\<comment>\<open>notion of monotone neighbourhood structure\<close>
record Nbd_Struct = 
  World :: world_type
  PropInterp :: "Atm_fml \<Rightarrow> world_type"
  GameInterp :: "Atm_game \<Rightarrow> world_type \<Rightarrow> world_type"

\<comment>\<open>We add a predicate to ensure monotone nbd structure is defined correctly.\<close>
definition is_nbd_struct :: "Nbd_Struct \<Rightarrow> bool" where
  "is_nbd_struct S \<equiv> 
    (\<forall>x::atm_games. \<forall>y\<in>x.  mono (GameInterp S y))
  \<and> (\<forall> a::world_type. \<forall>p::atm_fmls. \<forall>z\<in>p. (PropInterp S z) \<subseteq> a)"

\<comment>\<open>notion of valuation\<close>

end