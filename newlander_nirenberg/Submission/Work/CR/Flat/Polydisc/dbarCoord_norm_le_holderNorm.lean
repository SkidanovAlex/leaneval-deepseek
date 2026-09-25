import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder

namespace Work.CR.Flat.Polydisc

open scoped NNReal ENNReal
open MeasureTheory Set

noncomputable section

/-- The `∂̄`-combination `(1/2)(D v + i·D (i v))` of two evaluations of a real-linear
map `D` along the unit vectors `Pi.single j 1` and `Pi.single j Complex.I` is bounded by
the operator norm of `D`: the triangle inequality and `‖(1/2 : ℂ)‖ = 1/2` give a factor
`(1/2)(‖D‖ + ‖D‖) = ‖D‖`. -/
lemma norm_dbarCombination_le {n : ℕ} (j : Fin n) (D : (Fin n → ℂ) →L[ℝ] ℂ) :
    ‖(1/2 : ℂ) * (D (Pi.single j 1) + Complex.I * D (Pi.single j Complex.I))‖ ≤ ‖D‖ := by
  have hv1 : ‖(Pi.single j (1 : ℂ) : Fin n → ℂ)‖ = 1 := by rw [Pi.norm_single]; norm_num
  have hv2 : ‖(Pi.single j (Complex.I : ℂ) : Fin n → ℂ)‖ = 1 := by rw [Pi.norm_single]; simp
  have h1 : ‖D (Pi.single j (1 : ℂ))‖ ≤ ‖D‖ := by
    have := D.le_opNorm (Pi.single j (1 : ℂ)); rwa [hv1, mul_one] at this
  have h2 : ‖D (Pi.single j (Complex.I : ℂ))‖ ≤ ‖D‖ := by
    have := D.le_opNorm (Pi.single j (Complex.I : ℂ)); rwa [hv2, mul_one] at this
  calc ‖(1/2 : ℂ) * (D (Pi.single j 1) + Complex.I * D (Pi.single j Complex.I))‖
      = (1/2) * ‖D (Pi.single j 1) + Complex.I * D (Pi.single j Complex.I)‖ := by
        rw [norm_mul]; norm_num
    _ ≤ (1/2) * (‖D (Pi.single j 1)‖ + ‖Complex.I * D (Pi.single j Complex.I)‖) := by
        have h := norm_add_le (D (Pi.single j 1)) (Complex.I * D (Pi.single j Complex.I))
        have h1' : (0 : ℝ) ≤ ‖D (Pi.single j 1)‖ := norm_nonneg _
        have h2' : (0 : ℝ) ≤ ‖Complex.I * D (Pi.single j Complex.I)‖ := norm_nonneg _
        linarith
    _ = (1/2) * (‖D (Pi.single j 1)‖ + ‖D (Pi.single j Complex.I)‖) := by
        rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ (1/2) * (‖D‖ + ‖D‖) := by linarith
    _ = ‖D‖ := by ring

/-- The `j`-th `∂̄`-derivative of `u` is controlled by the `C^{k,α}` norm of `u`
as soon as `1 ≤ k`: the norm contains the sup norm of the first derivative, and
`dbarCoord j u z` is the average of two evaluations of the real derivative along
unit vectors, hence bounded by its operator norm.  This is the estimate a caller
needs to read `∂̄u` off the Hölder norm in the Newlander–Nirenberg iteration. -/
theorem dbarCoord_norm_le_holderNorm {n : ℕ} (j : Fin n) {u : (Fin n → ℂ) → ℂ}
    {Ω : Set (Fin n → ℂ)} (hΩ : UniqueDiffOn ℝ Ω) {z : Fin n → ℂ} (hz : z ∈ Ω)
    {k : ℕ} (hk : 1 ≤ k) (α : ℝ) :
    ENNReal.ofReal ‖dbarCoord j u z‖ ≤ holderNorm k α u Ω := by
  have hz' : UniqueDiffWithinAt ℝ Ω z := hΩ z hz
  have hkey : ‖dbarCoord j u z‖ ≤ ‖iteratedFDerivWithin ℝ 1 u Ω z‖ := by
    rw [norm_iteratedFDerivWithin_one u hz']
    by_cases hd : DifferentiableAt ℝ u z
    · -- `u` is differentiable: the within derivative agrees with the derivative.
      rw [fderivWithin_eq_fderiv hz' hd]
      exact norm_dbarCombination_le j (fderiv ℝ u z)
    · -- `u` is not differentiable: `fderiv ℝ u z = 0`, so `∂̄u = 0`.
      have hzero : dbarCoord j u z = 0 := by
        unfold dbarCoord
        rw [fderiv_zero_of_not_differentiableAt hd]
        simp
      simp [hzero]
  calc ENNReal.ofReal ‖dbarCoord j u z‖
      ≤ ENNReal.ofReal ‖iteratedFDerivWithin ℝ 1 u Ω z‖ := ENNReal.ofReal_le_ofReal hkey
    _ ≤ iterDerivNorm 1 u Ω := le_iterDerivNorm 1 u Ω hz
    _ ≤ holderNorm k α u Ω := iterDerivNorm_le_holderNorm k α u Ω hk

end

end Work.CR.Flat.Polydisc
