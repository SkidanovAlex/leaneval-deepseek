import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.Eps.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Eps/highSlot_chiSq_aP_eq`

The **fibre collapse** of the `3Q`-convolution word: because `P_jΦ` is constant in the
slot `j` (`Q0Sector.aP_const_in_coord`), the slot-`j` fibre of `χ_Λ²·P_jΦ` is the *constant*
`P_jΦ(x)` times the one-body profile `χ_Λ² = chiU ℓ 0 · ²`.  Hence the complementary
multiplier `1 − f_L` (`Work.BoseFixB3.highSlot`) only ever acts on that single profile, and

  `highSlot fc κ ℓ j (χ_Λ²·P_jΦ) x = P_jΦ x · (1 − f_L)(χ_Λ²)(x j) = aP … x · hRes fc κ ℓ (x j)`,

with `hRes` the one-body residual of `Work.BoseFixB3.Eps.Defs`.  This is the identity that
turns `q3convWord` into a sum of one-body pairings of `hRes`.

The two inputs are
* `aP_const_in_coord` — `P_jΦ` does not depend on the value of slot `j`;
* `lowMult_const_mul` — `lowMult` (a `kinFT` multiplier, hence a `p`-integral) is `ℝ`-linear
  in the state, proved here from `kinFT`'s `ℂ`-linearity (`kinFT_const_mul_C`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.Eps

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The two linearity/constancy inputs -/

/-- The `p`-convention Fourier transform `kinFT` is `ℂ`-linear in the state (an
unconditional Bochner-integral identity, no integrability needed). -/
lemma kinFT_const_mul_C (c : ℂ) (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.kinFT (fun z => c * f z) p = c * Submission.BoseGases.kinFT f p := by
  unfold Submission.BoseGases.kinFT
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  ring

/-- `lowMult fc κ ℓ` is `ℝ`-homogeneous in the state: it is the `p`-integral of
`kinFT` of the windowed state, and both `kinFT` and the `p`-integral are linear. -/
lemma lowMult_const_mul (fc : LowCut) (κ ℓ c : ℝ)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    lowMult fc κ ℓ (fun z => c * ψ z) x = c * lowMult fc κ ℓ ψ x := by
  unfold Work.BoseBoxFix.lowMult
  have hpt : (fun z : EuclideanSpace ℝ (Fin 3) =>
        (((acube ℓ).indicator (fun z => c * ψ z) z : ℝ) : ℂ))
      = fun z => (c : ℂ) * (((acube ℓ).indicator ψ z : ℝ) : ℂ) := by
    funext z
    by_cases hz : z ∈ acube ℓ
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  rw [hpt]
  simp only [kinFT_const_mul_C]
  generalize hA : (∫ p : EuclideanSpace ℝ (Fin 3),
      Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
      Submission.BoseGases.kinFT
        (fun z : EuclideanSpace ℝ (Fin 3) => (((acube ℓ).indicator ψ z : ℝ) : ℂ)) p) = A
  have h1 : (∫ p : EuclideanSpace ℝ (Fin 3),
      Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
      ((c : ℂ) * Submission.BoseGases.kinFT
        (fun z : EuclideanSpace ℝ (Fin 3) => (((acube ℓ).indicator ψ z : ℝ) : ℂ)) p))
      = (c : ℂ) * A := by
    rw [← hA, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    ring
  rw [h1]
  have h2 : (((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) * ((c : ℂ) * A)).re
      = c * (((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) * A).re := by
    rw [show (((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) * ((c : ℂ) * A))
          = (c : ℂ) * (((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) * A) by ring]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  exact h2

/-! ## 2. The fibre collapse -/

/-- **The slot-`j` fibre of `χ_Λ²·P_jΦ` is the constant `P_jΦ(x)` times `χ_Λ²`**: since
`P_jΦ` does not see the slot-`j` variable (`aP_const_in_coord`) and `update x j z` has
`j`-th coordinate `z`. -/
lemma aP_mul_chiU_fibre_eq {ℓ : ℝ} {n : ℕ} {j : Fin n} {Φ : X n → ℝ}
    (hℓ : 0 < ℓ) (hΦ : Continuous Φ) (x : X n) :
    (fun z : EuclideanSpace ℝ (Fin 3) =>
        chiU ℓ 0 ((Function.update x j z) j) ^ 2 * aP ℓ j Φ (Function.update x j z))
      = fun z : EuclideanSpace ℝ (Fin 3) => aP ℓ j Φ x * chiU ℓ 0 z ^ 2 := by
  funext z
  rw [Function.update_self, aP_const_in_coord hℓ j hΦ x z]
  ring

/-- **The requested identity.**  `P_jΦ` is constant in the slot `j`, so the slot-`j`
high-momentum part of `χ_Λ²·P_jΦ` is `P_jΦ` times the one-body high-momentum part of
`χ_Λ²`, i.e. `P_jΦ(x)·hRes fc κ ℓ (x j)`. -/
theorem highSlot_chiSq_aP_eq {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} {n : ℕ} {j : Fin n}
    {Φ : Submission.BoseGases.X n → ℝ} (hℓ : 0 < ℓ) (hΦ : Continuous Φ)
    (x : Submission.BoseGases.X n) :
    Work.BoseFixB3.highSlot fc κ ℓ j
        (fun y => Submission.BoseGases.chiU ℓ 0 (y j) ^ 2 * Submission.BoseGases.aP ℓ j Φ y) x
      = Submission.BoseGases.aP ℓ j Φ x * Work.BoseFixB3.Eps.hRes fc κ ℓ (x j) := by
  unfold Work.BoseFixB3.highSlot Work.BoseBoxFix.lowSlot Work.BoseFixB3.Eps.hRes
  rw [aP_mul_chiU_fibre_eq (ℓ := ℓ) (j := j) hℓ hΦ x]
  rw [lowMult_const_mul fc κ ℓ (Submission.BoseGases.aP ℓ j Φ x)
    (fun w : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chiU ℓ 0 w ^ 2) (x j)]
  ring

end Work.BoseFixB3.Eps
