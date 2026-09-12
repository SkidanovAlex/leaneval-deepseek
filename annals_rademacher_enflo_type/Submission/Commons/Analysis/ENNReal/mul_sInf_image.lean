import Mathlib.Data.ENNReal.Inv

open scoped ENNReal

namespace Commons.Analysis.ENNReal

/-- Multiplication by a nonzero finite extended nonnegative real commutes with `sInf`.

Follows from the fact that left multiplication by `k` is an order isomorphism of `ℝ≥0∞`
when `k ≠ 0` and `k ≠ ∞` (`ENNReal.mulLeftOrderIso`), and order isomorphisms of complete
lattices preserve `sInf` (`OrderIso.map_sInf`). -/
theorem mul_sInf_image {k : ℝ≥0∞} (hk : k ≠ 0) (hktop : k ≠ ∞) (S : Set ℝ≥0∞) :
    k * sInf S = sInf ((fun x : ℝ≥0∞ => k * x) '' S) := by
  let e : ℝ≥0∞ ≃o ℝ≥0∞ := ENNReal.mulLeftOrderIso k (ENNReal.isUnit_iff.mpr ⟨hk, hktop⟩)
  have he : ∀ x : ℝ≥0∞, e x = k * x := by
    intro x
    simp [e]
  have hmain : e (sInf S) = sInf (e '' S) := by
    rw [OrderIso.map_sInf e S]
    rw [← sInf_image]
  calc
    k * sInf S = e (sInf S) := by rw [he]
    _ = sInf (e '' S) := hmain
    _ = sInf ((fun x : ℝ≥0∞ => k * x) '' S) := by simp [he]

end Commons.Analysis.ENNReal