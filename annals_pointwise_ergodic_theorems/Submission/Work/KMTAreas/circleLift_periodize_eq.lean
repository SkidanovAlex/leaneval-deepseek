import Mathlib
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Work.KMTAreas.MSW_periodize_integral

/-!
# The fundamental-domain lift of the periodisation is the reflected Schwartz function

For a Schwartz function `φ : ℝ → ℂ` whose support lies in the arc `ℝ_{≤k} = [-2^k, 2^k]`
with `2^k ≤ 1/2`, the fundamental-domain lift (`Work.BourgainPlan.Thm52.circleLift`) of the
periodisation `Work.Analysis.IonescuWainger.periodize φ` agrees almost everywhere with the
reflected function `x ↦ φ (-x)`.

On the fundamental domain `(-1/2, 1/2)` the periodisation is the sum `∑_{j ∈ ℤ} φ(ν + j)` of
the integer shifts of `φ` along the representative `ν ∈ [0, 1)` of `-x`; since `supp φ` is
contained in `[-2^k, 2^k] ⊆ [-1/2, 1/2]`, exactly one shift contributes, namely the one that
lands on `-x`: the shift `j = 0` when `x ≤ 0` (there `ν = -x`) and the shift `j = -1` when
`x > 0` (there `ν = -x + 1`).  Outside the fundamental domain the lift vanishes, and `φ (-x)`
vanishes as well because then `|-x| > 1/2 ≥ 2^k`.  The only points where the identity can fail
for a general support in `[-1/2, 1/2]` are `x = ±1/2`, a null set.
-/

namespace Work.KMTAreas

open MeasureTheory

theorem circleLift_periodize_eq {k : ℤ} (hk : (2 : ℝ) ^ k ≤ 1 / 2) {φ : SchwartzMap ℝ ℂ}
    (hφ : ∀ x, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k) :
    (fun x : ℝ => Work.BourgainPlan.Thm52.circleLift
        (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) x)
      =ᵐ[MeasureTheory.volume] (fun x : ℝ => φ (-x)) := by
  -- the support of `φ` is contained in `[-2^k, 2^k]`
  have hφ0 : ∀ y : ℝ, (2 : ℝ) ^ k < |y| → φ y = 0 := by
    intro y hy
    by_contra h
    have hyarc := hφ y h
    rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc] at hyarc
    have : |y| ≤ (2 : ℝ) ^ k := abs_le.mpr ⟨hyarc.1, hyarc.2⟩
    linarith
  -- on the fundamental domain the identity is pointwise
  have key : ∀ x : ℝ, x ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) →
      Work.BourgainPlan.Thm52.circleLift
        (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) x = φ (-x) := by
    intro x hx
    have hx1 : -(1 / 2 : ℝ) < x := hx.1
    have hx2 : x < 1 / 2 := hx.2
    rw [Work.BourgainPlan.Thm52.circleLift_of_mem ⟨hx1, le_of_lt hx2⟩]
    set ν : ℝ := (AddCircle.equivIco (1 : ℝ) 0 (-(x : AddCircle (1:ℝ)))).val with hνdef
    have hνcoe : ((ν : ℝ) : AddCircle (1:ℝ)) =
        -(x : AddCircle (1:ℝ)) := AddCircle.coe_equivIco
    show (∑' j : ℤ, φ (ν + (j : ℝ))) = φ (-x)
    rcases lt_or_ge (0:ℝ) x with hx0 | hx0
    · -- `0 < x`: the representative of `-x` is `-x + 1` and the contributing shift is `-1`
      have hy : (-x + 1 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hcy : (((-x + 1 : ℝ)) : AddCircle (1:ℝ)) = -(x : AddCircle (1:ℝ)) := by
        rw [AddCircle.coe_add, AddCircle.coe_neg, AddCircle.coe_period]
        simp
      have hνeq : ν = -x + 1 := by
        rw [hνdef, ← hcy]
        exact AddCircle.equivIco_coe_of_mem (p := (1:ℝ)) (a := 0) (by simpa using hy)
      rw [hνeq]
      rw [tsum_eq_single (-1) (fun j hj => ?_)]
      · norm_num
      · refine hφ0 _ ?_
        rcases lt_or_gt_of_ne hj with hjlt | hjgt
        · have hjle : (j : ℝ) ≤ -2 := by
            exact_mod_cast (show j ≤ (-2 : ℤ) by omega)
          rw [abs_of_neg (by linarith)]
          linarith
        · have hjge : (0 : ℝ) ≤ (j : ℝ) := by
            exact_mod_cast (show (0 : ℤ) ≤ j by omega)
          rw [abs_of_nonneg (by linarith)]
          linarith
    · -- `x ≤ 0`: the representative of `-x` is `-x` and the contributing shift is `0`
      have hy : (-x : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      have hcy : (((-x : ℝ)) : AddCircle (1:ℝ)) = -(x : AddCircle (1:ℝ)) := by
        rw [AddCircle.coe_neg]
      have hνeq : ν = -x := by
        rw [hνdef, ← hcy]
        exact AddCircle.equivIco_coe_of_mem (p := (1:ℝ)) (a := 0) (by simpa using hy)
      rw [hνeq]
      rw [tsum_eq_single 0 (fun j hj => ?_)]
      · norm_num
      · refine hφ0 _ ?_
        rcases lt_or_gt_of_ne hj with hjlt | hjgt
        · have hjle : (j : ℝ) ≤ -1 := by
            exact_mod_cast (show j ≤ (-1 : ℤ) by omega)
          rw [abs_of_neg (by linarith)]
          linarith
        · have hjge : (1 : ℝ) ≤ (j : ℝ) := by
            exact_mod_cast (show (1 : ℤ) ≤ j by omega)
          rw [abs_of_nonneg (by linarith)]
          linarith
  -- the identity fails at most at `x = ±1/2`
  have hpoint : ∀ x : ℝ, x ∉ ({-(1 / 2 : ℝ), (1 / 2 : ℝ)} : Set ℝ) →
      Work.BourgainPlan.Thm52.circleLift
        (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) x = φ (-x) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rcases lt_or_ge x (-(1 / 2 : ℝ)) with h | h
    · -- `x < -1/2`: the lift vanishes
      rw [Work.BourgainPlan.Thm52.circleLift_of_notMem]
      · symm
        exact hφ0 (-x) (by rw [abs_of_pos (by linarith : (0:ℝ) < -x)]; linarith)
      · intro hmem
        exact absurd hmem.1 (not_lt.mpr (le_of_lt h))
    · rcases lt_or_ge x (1 / 2 : ℝ) with h2 | h2
      · rcases eq_or_lt_of_le h with heq | hlt
        · exact absurd heq.symm hx1
        · exact key x ⟨hlt, h2⟩
      · -- `1/2 < x`: the lift vanishes
        rcases eq_or_lt_of_le h2 with heq | hlt
        · exact absurd heq.symm hx2
        · rw [Work.BourgainPlan.Thm52.circleLift_of_notMem]
          · symm
            exact hφ0 (-x) (by rw [abs_of_neg (by linarith : -x < 0)]; linarith)
          · intro hmem
            exact absurd hmem.2 (not_le.mpr hlt)
  have hs : MeasureTheory.volume ({-(1 / 2 : ℝ), (1 / 2 : ℝ)} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hae : ∀ᵐ x : ℝ ∂MeasureTheory.volume,
      x ∉ ({-(1 / 2 : ℝ), (1 / 2 : ℝ)} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    exact MeasureTheory.measure_mono_null (fun y hy => of_not_not hy) hs
  exact hae.mono hpoint

end Work.KMTAreas
