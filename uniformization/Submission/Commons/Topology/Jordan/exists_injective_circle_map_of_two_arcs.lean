import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.Topology.Jordan

open Set

private lemma h01 : (0:ℝ) ≤ 1 := zero_le_one

private noncomputable def arcFun (P Q : C(Set.Icc (0:ℝ) 1, ℂ)) (t : ℝ) : ℂ :=
  if t ≤ 1 then P (Set.projIcc 0 1 h01 (1 - t))
  else Q (Set.projIcc 0 1 h01 (t - 1))

private lemma arcFun_of_le_one (P Q : C(Set.Icc (0:ℝ) 1, ℂ)) {t : ℝ} (ht : t ≤ 1) :
    arcFun P Q t = P (Set.projIcc 0 1 h01 (1 - t)) := by
  rw [arcFun, if_pos ht]

private lemma arcFun_of_ge_one (P Q : C(Set.Icc (0:ℝ) 1, ℂ)) (hP0 : P 0 = Q 0)
    {t : ℝ} (ht : 1 ≤ t) :
    arcFun P Q t = Q (Set.projIcc 0 1 h01 (t - 1)) := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    rw [arcFun, if_pos le_rfl]
    have hz : Set.projIcc (0:ℝ) 1 h01 (1 - 1) = (0 : Set.Icc (0:ℝ) 1) := by
      rw [sub_self, Set.projIcc_left]; rfl
    rw [hz]
    exact hP0
  · rw [arcFun, if_neg (not_le.mpr h)]

private lemma arcFun_zero (P Q : C(Set.Icc (0:ℝ) 1, ℂ)) : arcFun P Q 0 = P 1 := by
  rw [arcFun_of_le_one P Q (by norm_num : (0:ℝ) ≤ 1)]
  have hm : (1 - 0 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
  rw [Set.projIcc_of_mem h01 hm]
  congr 1
  ext; norm_num

private lemma arcFun_two (P Q : C(Set.Icc (0:ℝ) 1, ℂ)) (hP0 : P 0 = Q 0) :
    arcFun P Q 2 = Q 1 := by
  rw [arcFun_of_ge_one P Q hP0 (by norm_num : (1:ℝ) ≤ 2)]
  have hm : (2 - 1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
  rw [Set.projIcc_of_mem h01 hm]
  congr 1
  ext; norm_num

private lemma continuousOn_arcFun (P Q : C(Set.Icc (0:ℝ) 1, ℂ)) (hP0 : P 0 = Q 0) :
    ContinuousOn (arcFun P Q) (Set.Icc (0:ℝ) 2) := by
  have hg : Continuous fun t : ℝ => P (Set.projIcc 0 1 h01 (1 - t)) :=
    P.continuous.comp ((continuous_projIcc).comp (by fun_prop))
  have hh : Continuous fun t : ℝ => Q (Set.projIcc 0 1 h01 (t - 1)) :=
    Q.continuous.comp ((continuous_projIcc).comp (by fun_prop))
  have h1 : ContinuousOn (arcFun P Q) (Set.Icc (0:ℝ) 1) :=
    hg.continuousOn.congr (fun t ht => arcFun_of_le_one P Q ht.2)
  have h2 : ContinuousOn (arcFun P Q) (Set.Icc (1:ℝ) 2) :=
    hh.continuousOn.congr (fun t ht => arcFun_of_ge_one P Q hP0 ht.1)
  have hu := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  have hunion : Set.Icc (0:ℝ) 1 ∪ Set.Icc (1:ℝ) 2 = Set.Icc (0:ℝ) 2 := by
    ext x
    simp only [mem_union, mem_Icc]
    constructor
    · rintro (⟨h1', h2'⟩ | ⟨h1', h2'⟩)
      · exact ⟨h1', by linarith⟩
      · exact ⟨by linarith, h2'⟩
    · rintro ⟨h1', h2'⟩
      rcases le_or_gt x 1 with h | h
      · exact Or.inl ⟨h1', h⟩
      · exact Or.inr ⟨h.le, h2'⟩
  rwa [hunion] at hu

private lemma arcFun_cross_false (P Q : C(Set.Icc (0:ℝ) 1, ℂ)) (hQ : Function.Injective Q)
    (hP0 : P 0 = Q 0) (hP1 : P 1 = Q 1)
    (hdisj : ∀ s t : Set.Icc (0:ℝ) 1, P s = Q t → s = 0 ∨ s = 1)
    {a b : ℝ} (ha : a ∈ Set.Ico (0:ℝ) 2) (hb : b ∈ Set.Ico (0:ℝ) 2)
    (hale : a ≤ 1) (hbgt : 1 < b) (h : arcFun P Q a = arcFun P Q b) : False := by
  have h1 : (1 - a : ℝ) ∈ Set.Icc 0 1 := ⟨by linarith [hale], by linarith [ha.1]⟩
  have h2 : (b - 1 : ℝ) ∈ Set.Icc 0 1 := ⟨by linarith [hbgt.le], by linarith [hb.2]⟩
  rw [arcFun_of_le_one P Q hale, arcFun_of_ge_one P Q hP0 hbgt.le,
      Set.projIcc_of_mem h01 h1, Set.projIcc_of_mem h01 h2] at h
  have hdis := hdisj ⟨1 - a, h1⟩ ⟨b - 1, h2⟩ h
  have hdis' : (1 - a : ℝ) = 0 ∨ (1 - a : ℝ) = 1 := by
    rcases hdis with hh | hh
    · exact Or.inl (congrArg Subtype.val hh)
    · exact Or.inr (congrArg Subtype.val hh)
  rcases hdis' with hh | hh
  · have hzero : (⟨1 - a, h1⟩ : Set.Icc (0:ℝ) 1) = 0 := by ext; simpa using hh
    rw [hzero] at h
    have hq : (0 : Set.Icc (0:ℝ) 1) = ⟨b - 1, h2⟩ := hQ (hP0.symm.trans h)
    have hb0 : (b - 1 : ℝ) = 0 := by simpa using (congrArg Subtype.val hq).symm
    linarith [hbgt]
  · have hone : (⟨1 - a, h1⟩ : Set.Icc (0:ℝ) 1) = 1 := by ext; simpa using hh
    rw [hone] at h
    have hq : (1 : Set.Icc (0:ℝ) 1) = ⟨b - 1, h2⟩ := hQ (hP1.symm.trans h)
    have hb1 : (b - 1 : ℝ) = 1 := by simpa using (congrArg Subtype.val hq).symm
    linarith [hb.2]

private lemma arcFun_injOn (P Q : C(Set.Icc (0:ℝ) 1, ℂ)) (hP : Function.Injective P)
    (hQ : Function.Injective Q) (hP0 : P 0 = Q 0) (hP1 : P 1 = Q 1)
    (hdisj : ∀ s t : Set.Icc (0:ℝ) 1, P s = Q t → s = 0 ∨ s = 1) :
    Set.InjOn (arcFun P Q) (Set.Ico (0:ℝ) 2) := by
  intro a ha b hb hab
  rcases le_or_gt a 1 with ha1 | ha1
  · rcases le_or_gt b 1 with hb1 | hb1
    · rw [arcFun_of_le_one P Q ha1, arcFun_of_le_one P Q hb1] at hab
      have h1 : (1 - a : ℝ) ∈ Set.Icc 0 1 := ⟨by linarith [ha1], by linarith [ha.1]⟩
      have h2 : (1 - b : ℝ) ∈ Set.Icc 0 1 := ⟨by linarith [hb1], by linarith [hb.1]⟩
      rw [Set.projIcc_of_mem h01 h1, Set.projIcc_of_mem h01 h2] at hab
      have hval : (1 - a : ℝ) = 1 - b := congrArg Subtype.val (hP hab)
      linarith
    · exact absurd hab (arcFun_cross_false P Q hQ hP0 hP1 hdisj ha hb ha1 hb1)
  · rcases le_or_gt b 1 with hb1 | hb1
    · exact absurd hab.symm (arcFun_cross_false P Q hQ hP0 hP1 hdisj hb ha hb1 ha1)
    · rw [arcFun_of_ge_one P Q hP0 ha1.le, arcFun_of_ge_one P Q hP0 hb1.le] at hab
      have h1 : (a - 1 : ℝ) ∈ Set.Icc 0 1 := ⟨by linarith [ha1.le], by linarith [ha.2]⟩
      have h2 : (b - 1 : ℝ) ∈ Set.Icc 0 1 := ⟨by linarith [hb1.le], by linarith [hb.2]⟩
      rw [Set.projIcc_of_mem h01 h1, Set.projIcc_of_mem h01 h2] at hab
      have hval : (a - 1 : ℝ) = b - 1 := congrArg Subtype.val (hQ hab)
      linarith

private lemma arcFun_mem_range (P Q : C(Set.Icc (0:ℝ) 1, ℂ)) (hP0 : P 0 = Q 0)
    {t : ℝ} (ht : t ∈ Set.Ico (0:ℝ) 2) :
    arcFun P Q t ∈ Set.range P ∪ Set.range Q := by
  rcases le_or_gt t 1 with h1 | h1
  · left
    have hm : (1 - t : ℝ) ∈ Set.Icc 0 1 := ⟨by linarith [h1], by linarith [ht.1]⟩
    refine ⟨⟨1 - t, hm⟩, ?_⟩
    rw [arcFun_of_le_one P Q h1, Set.projIcc_of_mem h01 hm]
  · right
    have hm : (t - 1 : ℝ) ∈ Set.Icc 0 1 := ⟨by linarith [h1.le], by linarith [ht.2]⟩
    refine ⟨⟨t - 1, hm⟩, ?_⟩
    rw [arcFun_of_ge_one P Q hP0 h1.le, Set.projIcc_of_mem h01 hm]

private lemma liftIco_apply_eq [Fact (0 < (2:ℝ))] (P Q : C(Set.Icc (0:ℝ) 1, ℂ))
    (x : AddCircle (2:ℝ)) :
    AddCircle.liftIco (2:ℝ) 0 (arcFun P Q) x
      = arcFun P Q ((AddCircle.equivIco (2:ℝ) 0 x).1) := by
  set s := (AddCircle.equivIco (2:ℝ) 0 x).1 with hsdef
  have hs : s ∈ Set.Ico (0:ℝ) (0 + 2) := by
    have := (AddCircle.equivIco (2:ℝ) 0 x).2
    simpa using this
  have hcoe : (↑s : AddCircle (2:ℝ)) = x := AddCircle.coe_equivIco
  rw [← hcoe, AddCircle.liftIco_coe_apply (a := (0:ℝ)) (p := (2:ℝ)) (f := arcFun P Q) hs]

private lemma range_liftIco_eq [Fact (0 < (2:ℝ))] (P Q : C(Set.Icc (0:ℝ) 1, ℂ))
    (hP0 : P 0 = Q 0) (hP1 : P 1 = Q 1) :
    Set.range (AddCircle.liftIco (2:ℝ) 0 (arcFun P Q)) = Set.range P ∪ Set.range Q := by
  apply Subset.antisymm
  · rintro y ⟨x, rfl⟩
    rw [liftIco_apply_eq]
    have hs : (AddCircle.equivIco (2:ℝ) 0 x).1 ∈ Set.Ico (0:ℝ) 2 := by
      have := (AddCircle.equivIco (2:ℝ) 0 x).2
      simpa using this
    exact arcFun_mem_range P Q hP0 hs
  · rintro y (hy | hy)
    · obtain ⟨u, rfl⟩ := hy
      have hs : (1 - (u:ℝ)) ∈ Set.Ico (0:ℝ) 2 :=
        ⟨by linarith [u.2.2], by linarith [u.2.1]⟩
      refine ⟨(↑(1 - (u:ℝ)) : AddCircle (2:ℝ)), ?_⟩
      have hs' : (1 - (u:ℝ)) ∈ Set.Ico (0:ℝ) (0 + 2) := by simpa using hs
      rw [AddCircle.liftIco_coe_apply (a := (0:ℝ)) (p := (2:ℝ)) (f := arcFun P Q) hs']
      rw [arcFun_of_le_one P Q (by linarith [u.2.1] : (1:ℝ) - (u:ℝ) ≤ 1)]
      rw [show (1 - (1 - (u:ℝ)) : ℝ) = (u:ℝ) by ring, Set.projIcc_val]
    · obtain ⟨u, rfl⟩ := hy
      rcases eq_or_lt_of_le u.2.2 with hu | hu
      · refine ⟨(↑(0:ℝ) : AddCircle (2:ℝ)), ?_⟩
        have hs0 : (0:ℝ) ∈ Set.Ico (0:ℝ) (0 + 2) := ⟨by norm_num, by norm_num⟩
        rw [AddCircle.liftIco_coe_apply (a := (0:ℝ)) (p := (2:ℝ)) (f := arcFun P Q) hs0]
        rw [arcFun_zero P Q, show u = 1 from Subtype.ext hu]
        exact hP1
      · have hs : ((u:ℝ) + 1) ∈ Set.Ico (0:ℝ) 2 :=
          ⟨by linarith [u.2.1], by linarith [hu]⟩
        refine ⟨(↑((u:ℝ) + 1) : AddCircle (2:ℝ)), ?_⟩
        have hs' : ((u:ℝ) + 1) ∈ Set.Ico (0:ℝ) (0 + 2) := by simpa using hs
        rw [AddCircle.liftIco_coe_apply (a := (0:ℝ)) (p := (2:ℝ)) (f := arcFun P Q) hs']
        rw [arcFun_of_ge_one P Q hP0 (by linarith [u.2.1] : (1:ℝ) ≤ (u:ℝ) + 1)]
        rw [show ((u:ℝ) + 1 - 1 : ℝ) = (u:ℝ) by ring, Set.projIcc_val]

theorem exists_injective_circle_map_of_two_arcs
    (P Q : C(Set.Icc (0:ℝ) 1, ℂ))
    (hP : Function.Injective P) (hQ : Function.Injective Q)
    (hP0 : P 0 = Q 0) (hP1 : P 1 = Q 1) (hne : P 0 ≠ P 1)
    (hdisj : ∀ s t : Set.Icc (0:ℝ) 1, P s = Q t → s = 0 ∨ s = 1) :
    ∃ γ : C(Circle, ℂ), Function.Injective γ ∧ Set.range γ = Set.range P ∪ Set.range Q := by
  haveI : Fact (0 < (2:ℝ)) := ⟨by norm_num⟩
  let F : AddCircle (2:ℝ) → ℂ := AddCircle.liftIco (2:ℝ) 0 (arcFun P Q)
  have hFcont : Continuous F := by
    refine AddCircle.liftIco_continuous (p := (2:ℝ)) (a := (0:ℝ)) (f := arcFun P Q) ?_ ?_
    · rw [zero_add, arcFun_zero P Q, arcFun_two P Q hP0, hP1]
    · simpa using continuousOn_arcFun P Q hP0
  have hFinj : Function.Injective F := by
    intro x y hxy
    have hx := liftIco_apply_eq P Q x
    have hy := liftIco_apply_eq P Q y
    have hsx : (AddCircle.equivIco (2:ℝ) 0 x).1 ∈ Set.Ico (0:ℝ) 2 := by
      have := (AddCircle.equivIco (2:ℝ) 0 x).2; simpa using this
    have hsy : (AddCircle.equivIco (2:ℝ) 0 y).1 ∈ Set.Ico (0:ℝ) 2 := by
      have := (AddCircle.equivIco (2:ℝ) 0 y).2; simpa using this
    have hxy' : arcFun P Q ((AddCircle.equivIco (2:ℝ) 0 x).1)
        = arcFun P Q ((AddCircle.equivIco (2:ℝ) 0 y).1) := by
      rw [← hx, ← hy]; exact hxy
    have heq := arcFun_injOn P Q hP hQ hP0 hP1 hdisj hsx hsy hxy'
    have hcx : (↑((AddCircle.equivIco (2:ℝ) 0 x).1) : AddCircle (2:ℝ)) = x :=
      AddCircle.coe_equivIco
    have hcy : (↑((AddCircle.equivIco (2:ℝ) 0 y).1) : AddCircle (2:ℝ)) = y :=
      AddCircle.coe_equivIco
    rw [← hcx, ← hcy, heq]
  let e := AddCircle.homeomorphCircle (T := (2:ℝ)) (by norm_num : (2:ℝ) ≠ 0)
  let γ : C(Circle, ℂ) := ⟨fun z => F (e.symm z), hFcont.comp e.continuous_symm⟩
  refine ⟨γ, ?_, ?_⟩
  · intro z w hzw
    exact e.symm.injective (hFinj hzw)
  · have hrange : Set.range γ = Set.range F := by
      have hcomp : (γ : Circle → ℂ) = F ∘ e.symm := rfl
      rw [hcomp, Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]
    rw [hrange]
    exact range_liftIco_eq P Q hP0 hP1

end Commons.Topology.Jordan