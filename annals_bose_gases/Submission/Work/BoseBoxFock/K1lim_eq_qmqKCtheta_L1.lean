import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1lim_eq_qmqKernelTheta
import Submission.Work.BoseBoxFock.boxChi_pinQBl_eq_pinQDl
import Submission.Work.BoseBoxFock.pinQBl_eq_boxAvg_L1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1lim_eq_qmqKCtheta_L1` — the limit pair kernel is the `QMQ` kernel of the
periodised weight, under `L¹` hypotheses

The limit pair kernel `K1lim ℓ W` of the FS `Q₂` row is the kernel of the `Q = 1 − ℓ⁻³|θ_Λ⟩⟨θ_Λ|`
sandwich of the windowed **periodisation** of `W`:

    `K1lim ℓ W w y = qmqKCθ ℓ (fun a b => ℓ⁻³·χ_ℓ(a)·latPer3 ℓ W (a − b)·χ_ℓ(b)) w y`.

The mathematical content is the **box-average form** of the three `χ̂`-lattice rows defining
`K1lim`: the bump `χ_ℓ` is supported in the ball of radius `ℓ/2 ⊆ acube ℓ`, so its Fourier
coefficients on the box are its Fourier samples, and

* `∫_{acube} k w y' dy' = χ_ℓ(w)·pinQBl ℓ W w`        (child lemma `pinQBl_eq_boxAvg_L1`),
* `∫_{acube} k w' y dw' = χ_ℓ(y)·pinQCl ℓ W y`        (derived here from the previous one by the
  reflection `y ↦ −y` and the evenness of the bump, using the proved `boxInt_neg` and
  `pinQCl_eq_pinQBl_neg`),
* `∬_{acube²} k = ℓ³·pinQDl ℓ W`                      (`pinQDl_eq_boxAvg_L1_of_chi` below, from the
  previous box average and the `χ`-average identity `boxChi_pinQBl_eq_pinQDl`),

where `k a b = ℓ⁻³·χ_ℓ(a)·latPer3 ℓ W (a−b)·χ_ℓ(b)`.

This is the `L¹` (rather than bounded) form of `K1lim_eq_qmqKernelTheta`: `W` is only assumed
integrable, compactly supported and even, with support in the ball of radius `R`.  The final
assembly (the four rows of `qmqKCθ`, the two `θ_Λ`-cuttings and the `ℓ⁻³` bookkeeping) is the
same as in `K1lim_eq_qmqKernelTheta`.

Everything here is complete (no unfinished proofs).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-! ## The second box-average identity -/

/-- **The `χθ` row as a box average**: `pinQCl ℓ W y = ℓ⁻³∫_{acube} χ_ℓ(w)·latPer3 ℓ W (w−y)`.
This is the `pinQBl` box average reflected in `y` (`boxInt_neg`), the two rows being related by
`pinQCl ℓ W y = pinQBl ℓ W (−y)`. -/
theorem pinQCl_eq_boxAvg_L1 {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWi : MeasureTheory.Integrable W) (hWs : HasCompactSupport W)
    (hWev : ∀ z, W (-z) = W z)
    (hW : ∀ z, R < ‖z‖ → W z = 0) (y : E3) :
    pinQCl ℓ W y = ((ℓ ^ 3)⁻¹ : ℂ) * ∫ w in Submission.BoseGases.acube ℓ,
        (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ) * latPer3 ℓ W (w - y) := by
  rw [pinQCl_eq_pinQBl_neg, pinQBl_eq_boxAvg_L1 hℓ hWi hWs hWev hW (-y)]
  congr 1
  exact boxInt_neg hℓ W y

/-! ## The third box-average identity -/

/-- A pure-algebra bookkeeping identity: for `A ≠ 0`, `(A⁻¹A⁻¹)(A·A·x) = x`. -/
private lemma coef_key (A x : ℂ) (hA : A ≠ 0) : (A⁻¹ * A⁻¹) * (A * A * x) = x := by
  rw [show (A⁻¹ * A⁻¹) * (A * A * x) = (A⁻¹ * A) * (A⁻¹ * A) * x from by ring]
  rw [inv_mul_cancel₀ hA, one_mul, one_mul]

/-- **The `θθ` row as a box average**, from the `χχ` box average and the `χ`-average identity:
`pinQDl ℓ W = ℓ⁻⁶∬_{acube²} χ_ℓ(w)·latPer3 ℓ W (w−y)·χ_ℓ(y)`.

Indeed the inner `y`-integral is `ℓ³·pinQBl ℓ W w` by `pinQBl_eq_boxAvg_L1`, so the double
integral is `ℓ³∫_{acube} χ_ℓ(w)·pinQBl ℓ W w dw = ℓ³·ℓ³·pinQDl ℓ W` by
`boxChi_pinQBl_eq_pinQDl`; the two `ℓ³` cancel against the outer `ℓ⁻⁶`. -/
theorem pinQDl_eq_boxAvg_L1_of_chi {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWi : MeasureTheory.Integrable W) (hWs : HasCompactSupport W)
    (hWev : ∀ z, W (-z) = W z)
    (hW : ∀ z, R < ‖z‖ → W z = 0) :
    pinQDl ℓ W
      = (((ℓ ^ 3)⁻¹ : ℝ) * ((ℓ ^ 3)⁻¹ : ℝ)) * ∫ w in Submission.BoseGases.acube ℓ,
          ∫ y in Submission.BoseGases.acube ℓ,
            (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
              * Work.BoseBoxFock.latPer3 ℓ W (w - y)
              * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) := by
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ)
  have h3c : ((ℓ ^ 3 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_pow]
    exact pow_ne_zero 3 hℓc
  -- the box average of the periodisation, in inverse direction
  have hI : ∀ w : E3, (∫ y in Submission.BoseGases.acube ℓ,
        (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * latPer3 ℓ W (w - y))
      = ((ℓ ^ 3 : ℝ) : ℂ) * pinQBl ℓ W w := by
    intro w
    have hA := pinQBl_eq_boxAvg_L1 hℓ hWi hWs hWev hW w
    rw [hA, ← mul_assoc]
    simp only [Complex.ofReal_pow]
    rw [mul_inv_cancel₀ (pow_ne_zero 3 hℓc), one_mul]
  have hinner : ∀ w : E3, (∫ y in Submission.BoseGases.acube ℓ,
        (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
          * Work.BoseBoxFock.latPer3 ℓ W (w - y)
          * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ))
      = (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
          * (((ℓ ^ 3 : ℝ) : ℂ) * pinQBl ℓ W w) := by
    intro w
    have hEq : (fun y : E3 => (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
          * Work.BoseBoxFock.latPer3 ℓ W (w - y)
          * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ))
        = fun y : E3 => (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
          * (Work.BoseBoxFock.latPer3 ℓ W (w - y)
              * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)) := by
      funext y; ring
    rw [hEq, MeasureTheory.integral_const_mul]
    congr 1
    rw [show (∫ y in Submission.BoseGases.acube ℓ,
            Work.BoseBoxFock.latPer3 ℓ W (w - y)
              * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ))
          = (∫ y in Submission.BoseGases.acube ℓ,
              (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
                * Work.BoseBoxFock.latPer3 ℓ W (w - y)) from
        integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))]
    exact hI w
  have hbox : (∫ w in Submission.BoseGases.acube ℓ,
        ∫ y in Submission.BoseGases.acube ℓ,
          (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
            * Work.BoseBoxFock.latPer3 ℓ W (w - y)
            * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ))
      = ((ℓ ^ 3 : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ) * pinQDl ℓ W := by
    calc (∫ w in Submission.BoseGases.acube ℓ,
          ∫ y in Submission.BoseGases.acube ℓ,
            (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
              * Work.BoseBoxFock.latPer3 ℓ W (w - y)
              * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ))
        = ∫ w in Submission.BoseGases.acube ℓ,
            (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
              * (((ℓ ^ 3 : ℝ) : ℂ) * pinQBl ℓ W w) :=
          integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = ∫ w in Submission.BoseGases.acube ℓ,
            (((ℓ ^ 3 : ℝ) : ℂ))
              * ((((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ) * pinQBl ℓ W w) :=
          integral_congr_ae (Filter.Eventually.of_forall (fun w => by ring))
      _ = ((ℓ ^ 3 : ℝ) : ℂ) * (∫ w in Submission.BoseGases.acube ℓ,
            (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ) * pinQBl ℓ W w) := by
          rw [MeasureTheory.integral_const_mul]
      _ = ((ℓ ^ 3 : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ) : ℂ) * pinQDl ℓ W) := by
          rw [boxChi_pinQBl_eq_pinQDl hℓ hWi]
      _ = ((ℓ ^ 3 : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ) * pinQDl ℓ W := by ring
  rw [hbox]
  simpa only [Complex.ofReal_inv, Complex.ofReal_pow] using
    (coef_key (((ℓ ^ 3 : ℝ) : ℂ)) (pinQDl ℓ W) h3c).symm

/-! ## The target -/

theorem K1lim_eq_qmqKCtheta_L1 {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWi : MeasureTheory.Integrable W) (hWs : HasCompactSupport W)
    (hWev : ∀ z, W (-z) = W z)
    (hW : ∀ z, R < ‖z‖ → W z = 0)
    (w y : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.K1lim ℓ W w y
      = Work.BoseBoxFock.qmqKCθ ℓ (fun a b => ((ℓ ^ 3)⁻¹ : ℂ)
          * ((Submission.BoseGases.chiScale ℓ a : ℝ) : ℂ)
          * Work.BoseBoxFock.latPer3 ℓ W (a - b)
          * ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)) w y := by
  have hB := pinQBl_eq_boxAvg_L1 hℓ hWi hWs hWev hW w
  have hC := pinQCl_eq_boxAvg_L1 hℓ hWi hWs hWev hW y
  have hD := pinQDl_eq_boxAvg_L1_of_chi hℓ hWi hWs hWev hW
  rw [K1lim, qmqKCθ_eq]
  -- ### the three box averages of the kernel
  have hint1 : (∫ y' in Submission.BoseGases.acube ℓ,
        ((ℓ ^ 3)⁻¹ : ℂ) * ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
          * latPer3 ℓ W (w - y') * ((Submission.BoseGases.chiScale ℓ y' : ℝ) : ℂ))
      = ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * pinQBl ℓ W w := by
    have hfun : (fun y' : E3 => ((ℓ ^ 3)⁻¹ : ℂ)
          * ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
          * latPer3 ℓ W (w - y') * ((Submission.BoseGases.chiScale ℓ y' : ℝ) : ℂ))
        = fun y' : E3 => (((ℓ ^ 3)⁻¹ : ℂ) * ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ))
            * (((Submission.BoseGases.chiScale ℓ y' : ℝ) : ℂ) * latPer3 ℓ W (w - y')) := by
      funext y'; ring
    rw [hfun, MeasureTheory.integral_const_mul, hB]
    ring
  have hint2 : (∫ w' in Submission.BoseGases.acube ℓ,
        ((ℓ ^ 3)⁻¹ : ℂ) * ((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ)
          * latPer3 ℓ W (w' - y) * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ))
      = ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ) * pinQCl ℓ W y := by
    have hfun : (fun w' : E3 => ((ℓ ^ 3)⁻¹ : ℂ)
          * ((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ)
          * latPer3 ℓ W (w' - y) * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ))
        = fun w' : E3 => (((ℓ ^ 3)⁻¹ : ℂ) * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ))
            * (((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ) * latPer3 ℓ W (w' - y)) := by
      funext w'; ring
    rw [hfun, MeasureTheory.integral_const_mul, hC]
    ring
  have hab : ((ℓ ^ 3 : ℝ) : ℂ) * (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), Complex.ofReal_one]
  have hdc : (((ℓ ^ 3 : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ))
      * ((((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (((ℓ ^ 3)⁻¹ : ℝ) : ℂ)) = 1 := by
    calc (((ℓ ^ 3 : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ))
          * ((((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * (((ℓ ^ 3)⁻¹ : ℝ) : ℂ))
        = (((ℓ ^ 3 : ℝ) : ℂ) * (((ℓ ^ 3)⁻¹ : ℝ) : ℂ))
            * (((ℓ ^ 3 : ℝ) : ℂ) * (((ℓ ^ 3)⁻¹ : ℝ) : ℂ)) := by ring
      _ = 1 := by rw [hab]; ring
  have hX : (∫ w' in Submission.BoseGases.acube ℓ, ∫ y' in Submission.BoseGases.acube ℓ,
        (((Submission.BoseGases.chiScale ℓ w' : ℝ)) : ℂ) * latPer3 ℓ W (w' - y')
          * (((Submission.BoseGases.chiScale ℓ y' : ℝ)) : ℂ))
      = (((ℓ ^ 3 : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ)) * pinQDl ℓ W := by
    rw [hD]
    rw [show (((ℓ ^ 3 : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ))
          * (((((ℓ ^ 3)⁻¹ : ℝ) * ((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)
              * (∫ w' in Submission.BoseGases.acube ℓ, ∫ y' in Submission.BoseGases.acube ℓ,
                  (((Submission.BoseGases.chiScale ℓ w' : ℝ)) : ℂ) * latPer3 ℓ W (w' - y')
                    * (((Submission.BoseGases.chiScale ℓ y' : ℝ)) : ℂ))) = _ from by
      rw [← mul_assoc, hdc, one_mul]]
  have hint3 : (∫ w' in Submission.BoseGases.acube ℓ, ∫ y' in Submission.BoseGases.acube ℓ,
        ((ℓ ^ 3)⁻¹ : ℂ) * ((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ)
          * latPer3 ℓ W (w' - y') * ((Submission.BoseGases.chiScale ℓ y' : ℝ) : ℂ))
      = ((ℓ ^ 3 : ℝ) : ℂ) * pinQDl ℓ W := by
    have hfun : (fun w' : E3 => ∫ y' in Submission.BoseGases.acube ℓ,
          ((ℓ ^ 3)⁻¹ : ℂ) * ((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ)
            * latPer3 ℓ W (w' - y') * ((Submission.BoseGases.chiScale ℓ y' : ℝ) : ℂ))
        = fun w' : E3 => ((ℓ ^ 3)⁻¹ : ℂ) * ∫ y' in Submission.BoseGases.acube ℓ,
            ((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ) * latPer3 ℓ W (w' - y')
              * ((Submission.BoseGases.chiScale ℓ y' : ℝ) : ℂ) := by
      funext w'
      rw [show (fun y' : E3 => ((ℓ ^ 3)⁻¹ : ℂ)
            * ((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ)
            * latPer3 ℓ W (w' - y') * ((Submission.BoseGases.chiScale ℓ y' : ℝ) : ℂ))
          = fun y' : E3 => ((ℓ ^ 3)⁻¹ : ℂ)
              * (((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ) * latPer3 ℓ W (w' - y')
                  * ((Submission.BoseGases.chiScale ℓ y' : ℝ) : ℂ)) from by
        funext y'; ring]
      rw [MeasureTheory.integral_const_mul]
    rw [hfun, MeasureTheory.integral_const_mul, hX]
    have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ)
    rw [show ((ℓ ^ 3 : ℝ) : ℂ) = (ℓ : ℂ) ^ 3 from Complex.ofReal_pow ℓ 3]
    field_simp
  -- ### the algebra
  rw [hint1, hint2, hint3]
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ)
  simp only [Complex.ofReal_inv, Complex.ofReal_pow]
  field_simp

end Work.BoseBoxFock
