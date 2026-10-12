import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.pairRowS3Defs
import Submission.Work.BoseBoxFock.pinQBl_eq_boxAvg
import Submission.Work.BoseBoxFock.pinQDl_eq_boxAvg
import Submission.Work.BoseBoxFock.qmqDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1lim_eq_qmqKernelTheta`

The limit pair kernel `K1lim ℓ W` of the FS `Q₂` row is the `QMQ` kernel of the windowed
periodisation of `W`:

    K1lim ℓ W w y = qmqKCθ ℓ (fun a b => ℓ⁻³ · χ_ℓ(a) · latPer3 ℓ W (a − b) · χ_ℓ(b)) w y .

Equivalently: the **box averages** of the kernel `k(a,b) = ℓ⁻³χ_ℓ(a) latPer3 ℓ W (a−b) χ_ℓ(b)`
reproduce exactly the three `χ̂`-lattice rows `pinQBl`, `pinQCl`, `pinQDl` that define `K1lim`:

* `∫_{acube} k w y' dy' = χ_ℓ(w)·pinQBl ℓ W w`               (`pinQBl_eq_boxAvg`,
  the child lemma, is the `w`-dependent identity `pinQBl ℓ W w = ℓ⁻³∫_{acube}χ_ℓ(y)·latPer3(w−y)`),
* `∫_{acube} k w' y dw' = χ_ℓ(y)·pinQCl ℓ W y`               (derived here from the previous
  one by the reflection `y ↦ -y` and the evenness of the bump),
* `∬_{acube²} k = ℓ³·pinQDl ℓ W`                              (from the child lemma
  `pinQDl_eq_boxAvg`).

The mathematical content of all three is the aliasing (Poisson) identity: the bump `χ` is
supported inside the box `acube ℓ`, so its Fourier coefficients on the box are its Fourier
samples, and the `χ̂`-rows of FS `eq:DefQ2` are exactly the box averages of the periodisation.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The reflected box average -/

/-- **Reflection of the box average.** Replacing `t` by `-t` inside the box integral
(`acube ℓ` is symmetric, and `χ_ℓ` is even) turns `latPer3 ℓ W (-y - t)` into
`latPer3 ℓ W (t - y)`.  The two elementary bump facts used here — evenness of `χ_ℓ` and
`chiScale ℓ x = 0` off `acube ℓ` — are the sibling lemmas `chiScale_neg` and
`chiScale_eq_zero_of_notMem_acube` of `BoseBoxFock/boxAvgAux.lean`. -/
lemma boxInt_neg {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (y : E3) :
    (∫ t in Submission.BoseGases.acube ℓ,
        ((Submission.BoseGases.chiScale ℓ t : ℝ) : ℂ) * latPer3 ℓ W (-y - t))
      = ∫ w in Submission.BoseGases.acube ℓ,
          ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * latPer3 ℓ W (w - y) := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
        rw [chiScale_eq_zero_of_notMem_acube hℓ ht, Complex.ofReal_zero, zero_mul]),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => by
        rw [chiScale_eq_zero_of_notMem_acube hℓ hw, Complex.ofReal_zero, zero_mul])]
  rw [← MeasureTheory.integral_neg_eq_self
    (fun w : E3 => ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * latPer3 ℓ W (w - y)) volume]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [chiScale_neg]
  congr 1
  abel

/-- `pinQCl` at `y` is `pinQBl` at `-y` (the two lattice rows differ by the sign of the phase). -/
lemma pinQCl_eq_pinQBl_neg (ℓ : ℝ) (W : E3 → ℝ) (y : E3) :
    pinQCl ℓ W y = pinQBl ℓ W (-y) := by
  rw [pinQCl, pinQBl]
  refine tsum_congr fun n => ?_
  have hphase : -(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ))
      = Complex.I * ((inner ℝ (kmomInt ℓ n) (-y) : ℝ) : ℂ) := by
    rw [inner_neg_right]
    push_cast
    ring
  rw [hphase]

/-- **The `χθ` row as a box average**: `pinQCl ℓ W y = ℓ⁻³∫_{acube} χ_ℓ(w)·latPer3 ℓ W (w−y)`. -/
theorem pinQCl_eq_boxAvg {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W)
    (hWev : ∀ z, W (-z) = W z)
    (hW : ∀ z, R < ‖z‖ → W z = 0) (y : E3) :
    pinQCl ℓ W y = ((ℓ ^ 3)⁻¹ : ℂ) * ∫ w in Submission.BoseGases.acube ℓ,
        (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ) * latPer3 ℓ W (w - y) := by
  rw [pinQCl_eq_pinQBl_neg,
    pinQBl_eq_boxAvg hℓ hWm hWb hWs hWev hW (-y)]
  congr 1
  exact boxInt_neg hℓ W y

/-! ## The `QMQ` kernel form of `K1lim` -/

theorem K1lim_eq_qmqKernelTheta {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W)
    (hWev : ∀ z, W (-z) = W z)
    (hW : ∀ z, R < ‖z‖ → W z = 0)
    (w y : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.K1lim ℓ W w y
      = Work.BoseBoxFock.qmqKCθ ℓ (fun a b => ((ℓ ^ 3)⁻¹ : ℂ)
          * ((Submission.BoseGases.chiScale ℓ a : ℝ) : ℂ)
          * Work.BoseBoxFock.latPer3 ℓ W (a - b)
          * ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)) w y := by
  have hB := pinQBl_eq_boxAvg hℓ hWm hWb hWs hWev hW w
  have hC := pinQCl_eq_boxAvg hℓ hWm hWb hWs hWev hW y
  have hD := pinQDl_eq_boxAvg hℓ hWm hWb hWs hWev hW
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
