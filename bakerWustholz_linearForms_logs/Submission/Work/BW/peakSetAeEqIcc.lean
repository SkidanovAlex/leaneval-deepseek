import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Set

/-- For an even function `U`, `U` only depends on `|x|`. -/
private lemma U_abs_eq {U : ℝ → ℝ} (hU_even : ∀ x, U (-x) = U x) (x : ℝ) : U |x| = U x := by
  rcases lt_or_ge 0 x with h | h
  · rw [abs_of_pos h]
  · rw [abs_of_nonpos h, hU_even x]

/-- The superlevel set `{x | t ≤ U x}` of an even function `U` which is antitone on `[0,∞)`
and tends to `-∞` at `+∞` is, up to a null set, the symmetric interval `[-r, r]`. -/
lemma peakSetAeEqIcc {U : ℝ → ℝ} (hU_even : ∀ x, U (-x) = U x)
    (hU_anti : AntitoneOn U (Set.Ici 0))
    (hU_small : ∀ t > 0, ∃ Y, ∀ y, Y ≤ y → U y < t) {t : ℝ} (ht : 0 < t) :
    ∃ r : ℝ, 0 ≤ r ∧ {x : ℝ | t ≤ U x} =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] Set.Icc (-r) r := by
  classical
  obtain ⟨Y, hY⟩ := hU_small t ht
  -- `T` is the part of the superlevel set lying in `[0,∞)`.
  set T : Set ℝ := {y | 0 ≤ y ∧ t ≤ U y} with hT
  have hTbdd : BddAbove T := by
    refine ⟨Y, ?_⟩
    intro y hy
    by_contra hcon
    rw [not_le] at hcon
    exact absurd (hY y (le_of_lt hcon)) (not_lt.mpr hy.2)
  -- `r` is the (finite) supremum of `T`.
  let r : ℝ := sSup T
  have hmemT_le : ∀ y ∈ T, y ≤ r := by
    intro y hy
    exact le_csSup hTbdd hy
  have hr_nonneg : 0 ≤ r := by
    rcases T.eq_empty_or_nonempty with hempty | hne
    · rw [show r = sSup T from rfl, hempty, Real.sSup_empty]
    · obtain ⟨y, hy⟩ := hne
      have h0T : (0:ℝ) ∈ T := by
        refine ⟨le_refl 0, ?_⟩
        exact le_trans hy.2 (hU_anti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hy.1) hy.1)
      exact le_csSup hTbdd h0T
  -- `T` is an initial segment of `[0,∞)`: everything below `r` (and nonnegative) lies in `T`.
  have hmemT_of_lt : ∀ y, 0 ≤ y → y < r → y ∈ T := by
    intro y hy0 hyr
    have hyr' : y < sSup T := hyr
    have hne : T.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, Real.sSup_empty] at hyr'
      linarith
    obtain ⟨z, hzT, hyz⟩ := exists_lt_of_lt_csSup hne hyr'
    refine ⟨hy0, ?_⟩
    exact le_trans hzT.2 (hU_anti (mem_Ici.mpr hy0) (mem_Ici.mpr hzT.1) (le_of_lt hyz))
  -- The superlevel set is exactly `{x | |x| ∈ T}`.
  have hA_eq : {x : ℝ | t ≤ U x} = {x : ℝ | |x| ∈ T} := by
    ext x
    constructor
    · intro hx
      refine ⟨abs_nonneg x, ?_⟩
      rwa [U_abs_eq hU_even x]
    · intro hx
      have h2 : t ≤ U |x| := hx.2
      rwa [U_abs_eq hU_even x] at h2
  have hIcc_eq : Set.Icc (-r) r = {x : ℝ | |x| ≤ r} := by
    ext x
    show -r ≤ x ∧ x ≤ r ↔ |x| ≤ r
    rw [abs_le]
  -- The two sides differ only where `|x| = r`, i.e. on `{-r, r}`.
  have hsub : symmDiff {x : ℝ | |x| ∈ T} {x : ℝ | |x| ≤ r} ⊆ ({-r, r} : Set ℝ) := by
    intro x hx
    rw [Set.mem_symmDiff] at hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd (hmemT_le |x| h1) h2
    · have hle : |x| ≤ r := h1
      have habs : |x| = r := by
        by_contra hne
        exact h2 (hmemT_of_lt |x| (abs_nonneg x) (lt_of_le_of_ne hle hne))
      rcases (abs_eq hr_nonneg).mp habs with h | h
      · exact Or.inr h
      · exact Or.inl h
  have hfin : ({-r, r} : Set ℝ).Finite := Set.finite_insert.mpr (Set.finite_singleton r)
  have hnull : (MeasureTheory.volume : MeasureTheory.Measure ℝ) ({-r, r} : Set ℝ) = 0 :=
    hfin.measure_zero _
  have hae : {x : ℝ | |x| ∈ T} =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℝ)] {x : ℝ | |x| ≤ r} := by
    rw [← MeasureTheory.measure_symmDiff_eq_zero_iff]
    exact measure_mono_null hsub hnull
  refine ⟨r, hr_nonneg, ?_⟩
  rw [hA_eq, hIcc_eq]
  exact hae

end Work.BW
