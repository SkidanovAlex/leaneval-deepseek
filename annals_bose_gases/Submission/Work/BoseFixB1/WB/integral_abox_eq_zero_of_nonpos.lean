import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.integral_abox_eq_zero_of_nonpos`

The box `abox n ℓ = (Λ(ℓ))ⁿ` with side `ℓ ≤ 0` is a null set for `n ≥ 1`, so
every integral over it vanishes.

* `ℓ < 0`: the centred cube `acube ℓ = {y | ∀ m, y m ∈ Icc (−ℓ/2) (ℓ/2)}` is
  **empty** — the interval `Icc (−ℓ/2) (ℓ/2)` has `ℓ/2 < −ℓ/2`, and the box is a
  product of empty sets.
* `ℓ = 0`: the box is a single point and `(0³)ⁿ = 0` for `n ≥ 1`
  (`Submission.BoseGases.abox_volume`).

In both cases the restricted measure `volume.restrict (abox n ℓ)` is `0`, and
`MeasureTheory.setIntegral_measure_zero` gives the claim.
-/

namespace Work.BoseFixB1.WB

/-- For `ℓ ≤ 0` and `n ≥ 1` the box `abox n ℓ` is a null set. -/
theorem volume_abox_eq_zero_of_nonpos {n : ℕ} (hn : 0 < n) {ℓ : ℝ} (hℓ : ℓ ≤ 0) :
    (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      (Submission.BoseGases.abox n ℓ) = 0 := by
  rcases lt_or_eq_of_le hℓ with h | h
  · -- `ℓ < 0`: the one-particle cube is empty, hence so is the box
    have hInt : Set.Icc (-ℓ / 2) (ℓ / 2) = (∅ : Set ℝ) := Set.Icc_eq_empty (by linarith)
    have hacube : Submission.BoseGases.acube ℓ = (∅ : Set ℝ³) := by
      ext y
      rw [Submission.BoseGases.mem_acube_iff, Set.mem_empty_iff_false]
      constructor
      · intro hy
        have h0 := hy 0
        rw [hInt] at h0
        exact h0
      · intro hy
        exact absurd hy (Set.notMem_empty y)
    have habox : Submission.BoseGases.abox n ℓ = (∅ : Set (Submission.BoseGases.X n)) := by
      ext x
      rw [Submission.BoseGases.mem_abox_iff, Set.mem_empty_iff_false]
      constructor
      · intro hx
        have h0 := hx ⟨0, hn⟩
        rw [hacube] at h0
        exact h0
      · intro hx
        exact absurd hx (Set.notMem_empty x)
    rw [habox, MeasureTheory.measure_empty]
  · -- `ℓ = 0`: the box volume is `(0³)ⁿ = 0` because `n ≥ 1`
    subst h
    rw [Submission.BoseGases.abox_volume n 0 le_rfl]
    simp [zero_pow hn.ne']

theorem integral_abox_eq_zero_of_nonpos {n : ℕ} (hn : 0 < n) {ℓ : ℝ} (hℓ : ℓ ≤ 0)
    (F : Submission.BoseGases.X n → ℝ) :
    ∫ x in Submission.BoseGases.abox n ℓ, F x = 0 :=
  MeasureTheory.setIntegral_measure_zero F (volume_abox_eq_zero_of_nonpos hn hℓ)

end Work.BoseFixB1.WB
