theory Util
  imports Complex_Main
    "HOL-Algebra.Algebra"
begin

\<comment>\<open>A non-locale implementation of LFP and GFP of functions based on FuncSet\<close>
definition ambient_inter :: "'a set \<Rightarrow> ('a set) set \<Rightarrow> 'a set" where
"ambient_inter U F = {x\<in>U. \<forall>A\<in>F. x\<in>A}"

lemma ambient_inter_compat [simp]: "F1\<subseteq> F2 \<Longrightarrow> ambient_inter U F2 \<subseteq> ambient_inter U F1"
  unfolding ambient_inter_def by auto

lemma ambient_inter_ambient [simp]: "ambient_inter U F \<subseteq> U" unfolding ambient_inter_def by simp

lemma ambient_inter_eq: "F1=F2 \<Longrightarrow> ambient_inter U F1 = ambient_inter U F2"
  by auto

lemma ambient_inter_emp: "ambient_inter U {} = U" unfolding ambient_inter_def by auto

lemma ambient_inter_smallest: "\<And>x. x\<in>F \<Longrightarrow> ambient_inter U F \<subseteq> x" unfolding ambient_inter_def by auto

definition amb_comp where
  "amb_comp w a = (if a\<subseteq>w then w-a else undefined)"

lemma amb_comp_compat [simp]: "a\<subseteq>w \<Longrightarrow> amb_comp w a\<subseteq>w" by (auto simp add:amb_comp_def)

lemma amb_comp_invo [simp]: "a\<subseteq> w \<Longrightarrow> amb_comp w (amb_comp w a) = a" unfolding amb_comp_def by auto

lemma amb_comp_flip : "a\<subseteq> w \<Longrightarrow> b\<subseteq> w \<Longrightarrow> a\<subseteq>b \<Longrightarrow> amb_comp w b \<subseteq> amb_comp w a"
  unfolding amb_comp_def by auto

lemma amb_comp_dm_andor: 
  assumes "\<Omega> \<subseteq> Pow w"
  shows "amb_comp w (ambient_inter w \<Omega>) = \<Union> {amb_comp w s |s. s\<in>\<Omega>}"
proof (cases "\<Omega>={}")
  case True
  then show ?thesis by (simp add:ambient_inter_emp amb_comp_def)
next
  case False
  then show ?thesis using ambient_inter_ambient apply simp
  proof assume nonemp:"\<Omega> \<noteq> {}"
    show "amb_comp w (ambient_inter w \<Omega>) \<subseteq> \<Union> {amb_comp w s |s. s \<in> \<Omega>}"
    proof fix x assume a:"x \<in> amb_comp w (ambient_inter w \<Omega>)"
      have "ambient_inter w \<Omega>\<subseteq> w" using ambient_inter_ambient by auto
      then have "amb_comp w (ambient_inter w \<Omega>) \<subseteq> w" using amb_comp_compat by auto
      then have b:"x\<in> w" using a by blast 
      from a nonemp have "\<exists>s. s\<in>\<Omega> \<and> x\<notin>s" unfolding amb_comp_def ambient_inter_def 
          using ambient_inter_ambient[of "w" "\<Omega>"]
          by fastforce
        then obtain s where c:"s \<in> \<Omega> \<and> x \<notin> s" by auto
        then have "x\<in> amb_comp w s" using b assms unfolding amb_comp_def by auto
        then show "x \<in> \<Union> {amb_comp w s |s. s \<in> \<Omega>}" using c by auto
      qed
    next
      assume nonemp:"\<Omega>\<noteq>{}"
      show "\<Union> {amb_comp w s |s. s \<in> \<Omega>} \<subseteq> amb_comp w (ambient_inter w \<Omega>)"
      proof - from ambient_inter_smallest have a1:"\<And>s. s\<in>\<Omega> \<Longrightarrow> ambient_inter w \<Omega> \<subseteq> s" by auto
        then have "\<And>s. s\<in>\<Omega> \<Longrightarrow> amb_comp w s \<subseteq> amb_comp w (ambient_inter w \<Omega>)"
          using assms ambient_inter_ambient[of "w""\<Omega>"] by (meson Pow_iff amb_comp_flip in_mono)
        then show ?thesis by auto
      qed
  qed
qed

definition fun_le :: "('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> bool" where
"fun_le f g = (\<forall>x. f x \<subseteq> g x)"

definition extension where
  "extension B = {f. \<forall>x. x \<notin> B \<longrightarrow> f x = undefined }"

definition compo :: "'a set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)"
  where "compo A g f = (\<lambda>x\<in>A. g (f x))"

lemma extension_union_extension: "f\<in> extension A\<Longrightarrow> g\<in> extension A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> extension A"
  by (simp add:extension_def)

lemma extension_inter_extension: "f\<in> extension A \<Longrightarrow> g\<in> extension A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> extension A"
  by (simp add:extension_def)

lemma extension_compo_extension: "f\<in> extension A\<Longrightarrow> g \<in> extension A \<Longrightarrow> compo A g f \<in> extension A"
  by (simp add:compo_def extension_def)

definition empty_func :: "'a set \<Rightarrow> 'a set" where
  "empty_func A = {}"

definition extension_fn :: "('a set \<Rightarrow> 'a set) set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) set" where
  "extension_fn W = {f. \<forall>x. x\<notin> W \<longrightarrow> f x = empty_func}"

definition carrier_of :: "'a set \<Rightarrow> ('a set\<Rightarrow> 'a set) set" where
  "carrier_of A = (Pow A\<rightarrow>Pow A) \<inter> extension (Pow A)"

lemma funcset_compo_funcset: "f\<in> Pow A \<rightarrow> Pow A \<Longrightarrow> g\<in> Pow A \<rightarrow> Pow A \<Longrightarrow> (compo (Pow A) g f) \<in> Pow A \<rightarrow> Pow A"
  by (simp add: Pi_iff compo_def)

lemma carrier_compo_carrier: "f\<in> carrier_of A \<Longrightarrow> g\<in> carrier_of A \<Longrightarrow> (compo (Pow A) g f) \<in> carrier_of A"
  using extension_compo_extension[of "f" "Pow A" "g"] funcset_compo_funcset[of "f" "A" "g"] carrier_of_def[of "A"] by auto 

lemma carrier_union_carrier: "f\<in> carrier_of A \<Longrightarrow> g\<in> carrier_of A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> carrier_of A"
  using extension_union_extension by (auto simp add:carrier_of_def)

lemma carrier_inter_carrier: "f\<in>carrier_of A \<Longrightarrow> g\<in> carrier_of A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> carrier_of A"
  using extension_inter_extension by (auto simp add:carrier_of_def)

definition mono_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "mono_of A = {f.  \<forall>x y. x\<subseteq>A \<and> y\<subseteq>A \<and> x \<subseteq> y \<longrightarrow> f x \<subseteq> f y}"

definition effective_fn_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "effective_fn_of A = carrier_of A \<inter> mono_of A "

lemma eff_compo_mono: "f\<in> carrier_of A \<inter> mono_of A \<Longrightarrow> g\<in> carrier_of A \<inter> mono_of A \<Longrightarrow> compo (Pow A) g f \<in> mono_of A"
  apply (simp add: mono_of_def compo_def carrier_of_def)
  by (simp add: Pi_iff)

lemma mono_union_mono: "f\<in> mono_of A \<Longrightarrow> g\<in> mono_of A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> mono_of A"
  apply (simp add:mono_of_def)
  by (simp add: sup.coboundedI1 sup.coboundedI2)

lemma mono_inter_mono: "f\<in> mono_of A \<Longrightarrow> g\<in> mono_of A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> mono_of A"
  apply (simp add:mono_of_def)
  by (simp add: inf.coboundedI1 inf.coboundedI2)

lemma eff_compo_eff: "f\<in> effective_fn_of A \<Longrightarrow> g\<in>effective_fn_of A \<Longrightarrow> compo (Pow A) g f \<in> effective_fn_of A"
  using eff_compo_mono carrier_compo_carrier apply (auto simp add:effective_fn_of_def)
  by force

lemma eff_union_eff: "f\<in> effective_fn_of A \<Longrightarrow> g\<in>effective_fn_of A \<Longrightarrow> (\<lambda>x. f x \<union> g x) \<in> effective_fn_of A"
  using carrier_union_carrier mono_union_mono by (auto simp add:effective_fn_of_def)

lemma eff_inter_eff: "f\<in> effective_fn_of A \<Longrightarrow> g\<in>effective_fn_of A \<Longrightarrow> (\<lambda>x. f x \<inter> g x) \<in> effective_fn_of A"
  using carrier_inter_carrier mono_inter_mono by (auto simp add:effective_fn_of_def)

lemma compo_preserve_fun_le: "f1\<in> effective_fn_of A \<Longrightarrow> f2\<in> effective_fn_of A \<Longrightarrow> g1\<in> effective_fn_of A \<Longrightarrow> g2 \<in> effective_fn_of A \<Longrightarrow> fun_le f1 f2 \<Longrightarrow> fun_le g1 g2 \<Longrightarrow> fun_le (compo (Pow A) g1 f1) (compo (Pow A) g2 f2)"
  unfolding compo_def fun_le_def effective_fn_of_def carrier_of_def mono_of_def extension_def
  by (smt (verit, ccfv_threshold) Int_iff PiE Pow_iff mem_Collect_eq restrict_apply subsetD subsetI)

definition op_of where
  "op_of A = (effective_fn_of A) \<rightarrow> (effective_fn_of A)"

definition op_ext where
  "op_ext A = extension (effective_fn_of A)"

definition eff_op_of where
  "eff_op_of A = op_of A \<inter> op_ext A"

definition monotone_op_of ::"'a set \<Rightarrow> ( ('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set) ) set" where
  "monotone_op_of A = (effective_fn_of A \<rightarrow> effective_fn_of A)
  \<inter> {F. \<forall>g1\<in>effective_fn_of A. \<forall>g2\<in> effective_fn_of A. fun_le g1 g2 \<longrightarrow> fun_le (F g1) (F g2)}"

definition Lfp_family :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
  "Lfp_family A f = {\<phi>. \<phi>\<in> effective_fn_of A \<and> fun_le (f \<phi>) \<phi>}"

definition Lfp :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "Lfp w F a = (if a \<subseteq> w then ambient_inter w {\<phi> a | \<phi>. \<phi> \<in> Lfp_family w F} else undefined)"

definition dual_eff_fn where
  "dual_eff_fn w f a = (if a\<subseteq> w then amb_comp w (f (amb_comp w a)) else undefined)"

lemma dual_eff_fn_compat_img: "a\<subseteq>w \<Longrightarrow> dual_eff_fn w f a = amb_comp w (f (amb_comp w a))" unfolding dual_eff_fn_def by simp

lemma ext_dual_ext: "f \<in> extension (Pow w) \<Longrightarrow> dual_eff_fn w f \<in>  extension (Pow w)"
  unfolding extension_def dual_eff_fn_def by auto

lemma mono_dual_mono: "f \<in> mono_of w \<Longrightarrow> f\<in> Pow w \<rightarrow> Pow w \<Longrightarrow> dual_eff_fn w f \<in> mono_of w"
  unfolding dual_eff_fn_def mono_of_def amb_comp_def apply simp
  by (metis Diff_mono Diff_subset Pow_iff funcset_mem order_eq_refl)

lemma funcset_dual_funcset: "f\<in> Pow w \<rightarrow> Pow w \<Longrightarrow> dual_eff_fn w f\<in> Pow w \<rightarrow> Pow w"
  unfolding dual_eff_fn_def amb_comp_def
  by (simp add: Pi_iff)

lemma eff_dual_eff: "f\<in> effective_fn_of w \<Longrightarrow> dual_eff_fn w f \<in> effective_fn_of w"
  using mono_dual_mono[of "f""w"] ext_dual_ext[of "f""w"] funcset_dual_funcset[of "f""w"] 
  unfolding effective_fn_of_def carrier_of_def by auto

lemma dual_eff_fn_invo: "f\<in> effective_fn_of w \<Longrightarrow> dual_eff_fn w (dual_eff_fn w f) = f"
  unfolding dual_eff_fn_def effective_fn_of_def carrier_of_def extension_def
proof fix a assume a1:"f \<in> (Pow w \<rightarrow> Pow w) \<inter> {f. \<forall>x. x \<notin> Pow w \<longrightarrow> f x = undefined} \<inter> mono_of w"
  show "(if a \<subseteq> w then amb_comp w (if amb_comp w a \<subseteq> w then amb_comp w (f (amb_comp w (amb_comp w a))) else undefined) else undefined) = f a"
    apply simp apply rule
  proof
    assume a2:"a\<subseteq>w"
    show "amb_comp w (amb_comp w (f a)) = f a" using amb_comp_invo a2 a1 Pow_iff by auto
  next
    show "\<not> a \<subseteq> w \<longrightarrow> undefined = f a"
    proof assume a2:"\<not> a\<subseteq> w"
      show "undefined = f a" using a1 Pow_iff a2 by auto
    qed
  qed
qed

definition dual_op where
  "dual_op w F f = dual_eff_fn w (F (dual_eff_fn w f))"

lemma dual_op_invo: "F\<in> eff_op_of w \<Longrightarrow> dual_op w (dual_op w F) = F"
  unfolding dual_op_def eff_op_of_def op_ext_def op_of_def extension_def
proof fix f assume a1:"F \<in> (effective_fn_of w \<rightarrow> effective_fn_of w) \<inter> {f. \<forall>x. x \<notin> effective_fn_of w \<longrightarrow> f x = undefined}"
  show "dual_eff_fn w (dual_eff_fn w (F (dual_eff_fn w (dual_eff_fn w f)))) = F f"
  proof (cases "f\<in> effective_fn_of w")
    case True
    then show ?thesis using dual_eff_fn_invo a1
    by (metis (no_types, lifting) Int_iff PiE)
  next
    case False
    then show ?thesis using a1 
    proof - from a1 have "F (dual_eff_fn w (dual_eff_fn w f)) = undefined" 
    qed
  qed
qed

definition op_homo_dual where
  "op_homo_dual w F \<equiv> \<forall>f\<in> effective_fn_of w. F (dual_eff_fn w f) = dual_eff_fn w (F f)"

definition max_of :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "max_of A x = (if x\<subseteq>A then A else undefined)"

lemma max_of_in_carrier : "max_of A \<in> carrier_of A"
  apply (auto simp add:max_of_def carrier_of_def)
proof show "max_of A \<in> extension (Pow A)"
    apply (simp add:extension_def)
  proof
    fix x show "\<not> x \<subseteq> A \<longrightarrow> max_of A x = undefined " by (auto simp add:max_of_def)
  qed
  show "extension (Pow A) \<subseteq> extension (Pow A) " by auto
qed

lemma max_of_in_funcset : "max_of A \<in> Pow A \<rightarrow> Pow A"
proof -
  from max_of_in_carrier have "max_of A \<in> (Pow A\<rightarrow>Pow A) \<inter> extension (Pow A)" by (simp add:carrier_of_def)
  then show ?thesis by auto
qed

lemma max_of_mono : "max_of A \<in> mono_of A" 
  by (auto simp add:mono_of_def max_of_def)

lemma max_of_effective [simp]: "max_of A \<in> effective_fn_of A"
  using max_of_mono[of "A"] max_of_in_carrier[of "A"] by (simp add:effective_fn_of_def)

lemma effective_op_effective : "f\<in> monotone_op_of A \<Longrightarrow> \<phi>\<in> effective_fn_of A \<Longrightarrow> f \<phi> \<in> effective_fn_of A "
  by (simp add: Pi_iff monotone_op_of_def)

lemma max_of_properties : 
  assumes "A \<noteq> {}"
    and P1: " f\<in> monotone_op_of A "
  shows "max_of A \<in> effective_fn_of A
\<and> (\<forall> xa. f (max_of A) xa \<subseteq> max_of A xa)"
  proof -
    have R1: "max_of A \<in> effective_fn_of A" using max_of_effective by auto
    have R2: "\<forall>xa. f (max_of A) xa \<subseteq> max_of A xa"
      apply (simp add:max_of_def)
    proof 
      fix xa show "(xa \<subseteq> A \<longrightarrow> f (max_of A) xa \<subseteq> A) \<and> (\<not> xa \<subseteq> A \<longrightarrow> f (max_of A) xa \<subseteq> undefined)"
      proof -
        have Q1:"xa \<subseteq> A \<longrightarrow> f (max_of A) xa \<subseteq> A"
        proof -
          have P2: "max_of A \<in> effective_fn_of A" by simp
          then have "f (max_of A) \<in> effective_fn_of A" using assms by (auto simp add:monotone_op_of_def)
          thus ?thesis by (auto simp add:effective_fn_of_def carrier_of_def)
        qed

        have Q2: "(\<not> xa \<subseteq> A \<longrightarrow> f (max_of A) xa = undefined)"
        proof assume a:"\<not> xa \<subseteq> A"
          have "f (max_of A)\<in> effective_fn_of A" using assms effective_op_effective[of "f" "A" "max_of A"] by simp 
          then have "f (max_of A) \<in> extension (Pow A)" by (auto simp add:effective_fn_of_def carrier_of_def)
          then show "f (max_of A) xa = undefined" using a by (simp add:effective_fn_of_def carrier_of_def extension_def)
        qed
        from Q1 Q2 show ?thesis by auto
      qed
    qed
    from R1 R2 show ?thesis by auto
  qed

lemma Lfp_family_nonempty :
  assumes "A \<noteq> {}"
    and P1: " f\<in> monotone_op_of A "
  shows " Lfp_family A f \<noteq> {}"
  apply (simp add:Lfp_family_def carrier_of_def extension_def fun_le_def)
proof
  show "max_of A \<in> effective_fn_of A \<and> (\<forall>x. f (max_of A) x \<subseteq> (max_of A) x)"
    using assms max_of_properties[of "A" "f"] by auto
qed

definition Gfp_family :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set) set" where
"Gfp_family A f = {\<phi>. \<phi>\<in> effective_fn_of A \<and> fun_le \<phi> (f \<phi>)}"

definition Gfp :: "'a set \<Rightarrow> (('a set \<Rightarrow> 'a set) \<Rightarrow> ('a set \<Rightarrow> 'a set)) \<Rightarrow> ('a set \<Rightarrow> 'a set)" where
  "Gfp w F a = (if a\<subseteq>w then \<Union>{\<phi> a | \<phi>. \<phi>\<in> Gfp_family w F} else undefined)"

definition eff_fn_fam_dual_closed where
  "eff_fn_fam_dual_closed w F \<equiv> \<forall>x\<in>F. (dual_eff_fn w x) \<in> F"

lemma all_eff_fn_dual_closed: "eff_fn_fam_dual_closed w (effective_fn_of w)"
  unfolding eff_fn_fam_dual_closed_def
  using eff_dual_eff by auto

lemma dual_eff_fn_compre:
  "{\<phi>. \<phi>\<in> effective_fn_of w \<and> P \<phi>} = {dual_eff_fn w \<phi>|\<phi>. \<phi>\<in>effective_fn_of w \<and> P (dual_eff_fn w \<phi>)}"
  using eff_dual_eff dual_eff_fn_invo
  by force

lemma fun_fam_img_fam:
  "F=G \<Longrightarrow> {f a|f. f\<in>F} = {f a|f. f\<in>G}" by auto

lemma dual_funle_anti:
  "f\<in> effective_fn_of w \<Longrightarrow> g\<in> effective_fn_of w \<Longrightarrow> fun_le f g \<Longrightarrow> fun_le (dual_eff_fn w g) (dual_eff_fn w f)"
  unfolding fun_le_def dual_eff_fn_def apply simp
proof fix x assume a1:"f \<in> effective_fn_of w"
  and a2:"g \<in> effective_fn_of w" and a3:"\<forall>x. f x \<subseteq> g x"
  show "x \<subseteq> w \<longrightarrow> amb_comp w (g (amb_comp w x)) \<subseteq> amb_comp w (f (amb_comp w x))"
  proof 
    assume a4:"x\<subseteq> w"    
    show "amb_comp w (g (amb_comp w x)) \<subseteq> amb_comp w (f (amb_comp w x))"
    proof -
      from a4 have "(amb_comp w x) \<subseteq> w" using amb_comp_compat by auto
      then have b2:"g (amb_comp w x) \<subseteq> w" using a2 
        unfolding effective_fn_of_def carrier_of_def by auto

      from a4 have "(amb_comp w x) \<subseteq> w" using amb_comp_compat by auto
      then have b1:"f (amb_comp w x) \<subseteq> w" using a1
        unfolding effective_fn_of_def carrier_of_def by auto

      from a3 have "f (amb_comp w x) \<subseteq> g (amb_comp w x)" by auto
      then show ?thesis using amb_comp_flip[of "f (amb_comp w x)""w""g (amb_comp w x)"] b2 b1 by auto
    qed
  qed
qed


lemma dual_Lfp__Gfp_dualop: 
  assumes "F\<in> op_of w"
  shows "dual_eff_fn w (Lfp w F) = Gfp w (dual_op w F)"
  unfolding Lfp_def Lfp_family_def Gfp_def Gfp_family_def dual_op_def dual_eff_fn_def apply rule
proof - fix a
  show "(if a \<subseteq> w then amb_comp w (if amb_comp w a \<subseteq> w then ambient_inter w {\<phi> (amb_comp w a) |\<phi>. \<phi> \<in> {\<phi> \<in> effective_fn_of w. fun_le (F \<phi>) \<phi>}} else undefined) else undefined) =
         (if a \<subseteq> w then \<Union> {\<phi> a |\<phi>. \<phi> \<in> {\<phi> \<in> effective_fn_of w. fun_le \<phi> (\<lambda>a. if a \<subseteq> w then amb_comp w (F (\<lambda>a. if a \<subseteq> w then amb_comp w (\<phi> (amb_comp w a)) else undefined) (amb_comp w a)) else undefined)}} else undefined)"
  proof (cases "a\<subseteq> w")
    case True
    then show ?thesis apply (simp)
    proof -
      assume a1:"a\<subseteq>w"
      show "amb_comp w (ambient_inter w {\<phi> (amb_comp w a) |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>}) =
    \<Union> {\<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le \<phi> (\<lambda>a. if a \<subseteq> w then amb_comp w (F (\<lambda>a. if a \<subseteq> w then amb_comp w (\<phi> (amb_comp w a)) else undefined) (amb_comp w a)) else undefined)}" 
      proof - let ?LHS = "amb_comp w (ambient_inter w {\<phi> (amb_comp w a) |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>})"
        let ?RHS = "\<Union> {\<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le \<phi> (\<lambda>a. if a \<subseteq> w then amb_comp w (F (\<lambda>a. if a \<subseteq> w then amb_comp w (\<phi> (amb_comp w a)) else undefined) (amb_comp w a)) else undefined)}"
        have "{\<phi> (amb_comp w a) |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>} \<subseteq> Pow w"
          using a1 amb_comp_compat[of "a""w"] effective_fn_of_def[of "w"] carrier_of_def[of "w"] by blast
        then have "?LHS = \<Union> {amb_comp w (\<phi> (amb_comp w a)) |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>}"
          using amb_comp_dm_andor[of "{\<phi> (amb_comp w a) |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>}" "w"] by auto
        also have "... = \<Union> {dual_eff_fn w \<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F \<phi>) \<phi>}"
          using a1 unfolding dual_eff_fn_def by auto
        also have "... = \<Union> {dual_eff_fn w (dual_eff_fn w \<phi>) a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F (dual_eff_fn w \<phi>)) (dual_eff_fn w \<phi>)}"
          by (metis (no_types, opaque_lifting) dual_eff_fn_invo eff_dual_eff)
        also have "... = \<Union> {\<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F (dual_eff_fn w \<phi>)) (dual_eff_fn w \<phi>)}"
          using dual_eff_fn_invo by fastforce
        finally have a3:"?LHS = \<Union> {\<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F (dual_eff_fn w \<phi>)) (dual_eff_fn w \<phi>)}" by simp

        have a2:"\<forall>\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le (F (dual_eff_fn w \<phi>)) (dual_eff_fn w \<phi>) 
          \<longleftrightarrow> \<phi> \<in> effective_fn_of w \<and> fun_le \<phi> (dual_eff_fn w (F (dual_eff_fn w \<phi>)))"          
          using assms dual_funle_anti dual_eff_fn_invo unfolding op_of_def
          by (metis (no_types, lifting) Pi_mem eff_dual_eff)

        from a3 a2 have a4:"?LHS = \<Union> {\<phi> a |\<phi>. \<phi> \<in> effective_fn_of w \<and> fun_le \<phi> (dual_eff_fn w (F (dual_eff_fn w \<phi>))) }" by simp

        from a4 show "?LHS=?RHS" unfolding dual_eff_fn_def by simp
      qed
    qed
  next
    case False
    then show ?thesis by auto
  qed
qed

lemma Lfp_in_carrier : "Lfp w f \<in> carrier_of w"
  apply (auto simp add:carrier_of_def)
proof -
  fix x xa
  show "x \<subseteq> w \<Longrightarrow> xa \<in> Lfp w f x \<Longrightarrow> xa \<in> w" unfolding Lfp_def ambient_inter_def by auto

  show "Lfp w f \<in> extension (Pow w)" unfolding Lfp_def Lfp_family_def effective_fn_of_def carrier_of_def
    by (simp add:extension_def ambient_inter_def)
qed

lemma Lfp_eff: "Lfp w f \<in> effective_fn_of w"
  apply (simp add:effective_fn_of_def)
  apply (auto simp add:Lfp_in_carrier)
  unfolding Lfp_def mono_of_def apply auto
proof -
  fix x y z assume a0:"z \<in> ambient_inter w {\<phi> x |\<phi>. \<phi> \<in> Lfp_family w f}" 
    and a1:"x \<subseteq> w"
    and a2:"y \<subseteq> w"
    and a3:"x \<subseteq> y"
  have "\<And>\<phi>. \<phi>\<in> Lfp_family w f \<Longrightarrow> \<phi> x \<subseteq> \<phi> y" using a1 a2 a3 by (auto simp add:Lfp_family_def effective_fn_of_def mono_of_def)
  then show "z \<in> ambient_inter w {\<phi> y |\<phi>. \<phi> \<in> Lfp_family w f}" using a0
  by (smt (verit, ccfv_threshold) ambient_inter_def in_mono mem_Collect_eq)
qed

\<comment>\<open>locale-based implementation\<close>
locale fun_comp_lattice =
  fixes A :: "'a set"
begin

definition const_A :: "'a set \<Rightarrow> 'a set" where
  "const_A = restrict (\<lambda>x. A) (Pow A)"

lemma max_exists : "greatest \<lparr>carrier = (Pow A \<rightarrow> Pow A) \<inter> (extensional (Pow A)), eq = (=), le = fun_le\<rparr> 
  const_A ((Pow A \<rightarrow> Pow A) \<inter> extensional (Pow A))"
  by (auto simp add: const_A_def greatest_def fun_le_def extensional_def)
end

sublocale fun_comp_lattice \<subseteq> equivalence "\<lparr> carrier = Pow A \<rightarrow> Pow A, eq = (=) \<rparr>"
  by (rule equivalenceI) (auto)

lemma weak_partial_orderI:
  fixes P :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and E :: "'a set" and R:: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes refl: "\<And>x.     \<lbrakk> x \<in> E \<rbrakk> \<Longrightarrow> P x x"
    and    sym: "\<And>x y.   \<lbrakk> x \<in> E; y \<in> E \<rbrakk> \<Longrightarrow> P x y \<Longrightarrow> P y x"
    and  trans: "\<And>x y z. \<lbrakk> x \<in> E; y \<in> E; z \<in> E \<rbrakk> \<Longrightarrow> P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
    and le_refl: "\<And>x.  \<lbrakk> x \<in> E \<rbrakk> \<Longrightarrow> R x x"
    and weak_le_antisym : "\<And> x y. \<lbrakk> R x y; R y x; x\<in>E; y\<in>E \<rbrakk> \<Longrightarrow> P x y"
    and le_trans: "\<And> x y z. \<lbrakk> R x y; R y z; x \<in>E ; y\<in>E;z\<in>E \<rbrakk> \<Longrightarrow> R x z"
    and le_cong: "\<And>x y z w. \<lbrakk> P x y; P z w; x\<in>E; y\<in>E; z\<in>E; w\<in>E \<rbrakk> \<Longrightarrow> (R x z \<longleftrightarrow> R y w)"
  shows "weak_partial_order \<lparr> carrier = E, eq = P, le=R \<rparr>"
  unfolding weak_partial_order_def using assms
  by (smt (verit) eq_object.select_convs(1) equivalence_def gorder.select_convs(1) partial_object.select_convs(1)
      weak_partial_order_axioms_def)

lemma partial_orderI:
  fixes E :: "'a set" and R:: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    assumes le_refl: "\<And>x.  \<lbrakk> x \<in> E \<rbrakk> \<Longrightarrow> R x x"
    and weak_le_antisym : "\<And> x y. \<lbrakk> R x y; R y x; x\<in>E; y\<in>E \<rbrakk> \<Longrightarrow> x=y"
    and le_trans: "\<And> x y z. \<lbrakk> R x y; R y z; x \<in>E ; y\<in>E;z\<in>E \<rbrakk> \<Longrightarrow> R x z"
    and le_cong: "\<And>x y z w. \<lbrakk> x=y; z=w; x\<in>E; y\<in>E; z\<in>E; w\<in>E \<rbrakk> \<Longrightarrow> (R x z \<longleftrightarrow> R y w)"
  shows "partial_order \<lparr> carrier = E, eq = (=), le=R \<rparr>"
  unfolding partial_order_def using assms
  by (smt (verit, best) eq_object.select_convs(1) partial_order_axioms.intro partial_order_def
      weak_partial_orderI)

sublocale fun_comp_lattice \<subseteq> partial_order "\<lparr> carrier = (Pow A \<rightarrow> Pow A) \<inter> extensional (Pow A), 
  eq = (=), le=fun_le \<rparr>"
  apply (rule partial_orderI)
  apply (auto simp add:fun_le_def)
proof -
  fix x and y show " \<forall>xa. x xa \<subseteq> y xa \<Longrightarrow> \<forall>xa. y xa \<subseteq> x xa \<Longrightarrow> x \<in> Pow A \<rightarrow> Pow A \<Longrightarrow> y \<in> Pow A \<rightarrow> Pow A \<Longrightarrow> x = y"
  proof
    fix z show " \<forall>xa. x xa \<subseteq> y xa \<Longrightarrow> \<forall>xa. y xa \<subseteq> x xa \<Longrightarrow> x \<in> Pow A \<rightarrow> Pow A \<Longrightarrow> y \<in> Pow A \<rightarrow> Pow A \<Longrightarrow> x z = y z"
      by auto
  qed
qed

sublocale fun_comp_lattice \<subseteq> complete_lattice "\<lparr> carrier = (Pow A \<rightarrow> Pow A) \<inter> extensional (Pow A), eq = (=), le=fun_le \<rparr>"
  apply (rule complete_lattice_criterion1)
  unfolding greatest_def
proof - 
  show "\<forall>f\<in> Pow A \<rightarrow> Pow A. fun_le f const_A"
    sorry
qed




end
