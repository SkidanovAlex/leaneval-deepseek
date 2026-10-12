import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxTBWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `𝒯_B` word — elementary API

Nonnegativity, monotonicity in the symbol, and the two immediate
consequences of the definition:

* `tBword_ge_gapPart` — `tbGapCoeff s ε·cnPlusBox ≤ tBword`: FS `eq:appTB`'s
  plain `Q_B`-gap part, **property (a)** of the chapter;
* `tBwordKin_le_tBdiagForm_sq` — the symbol inequality `[·−c]₊² ≤ (·)²`
  (`fsKinCoeff c ≤ (·)²`), the first step of the domination **(b)**.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- the `(2π)⁻³` prefactor of the `p`-integral is positive. -/
lemma twoPiInv3_pos : 0 < ((2 * Real.pi) ^ 3)⁻¹ := by
  exact inv_pos.mpr (pow_pos (by positivity) 3)

/-- `(1+π⁻²)⁻¹` is positive. -/
lemma tbPiFactor_pos : 0 < tbPiFactor := by
  unfold tbPiFactor
  exact inv_pos.mpr (by positivity)

/-- `(1+π⁻²)⁻¹ ≤ 1`. -/
lemma tbPiFactor_le_one : tbPiFactor ≤ 1 := by
  unfold tbPiFactor
  rw [inv_le_one₀ (by positivity : (0:ℝ) < 1 + (Real.pi ^ 2)⁻¹)]
  linarith [inv_nonneg.mpr (sq_nonneg Real.pi)]

/-- The gap coefficient is nonnegative for `0 ≤ ε`. -/
lemma tbGapCoeff_nonneg {s ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ tbGapCoeff s ε := by
  unfold tbGapCoeff
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε) (le_of_lt tbPiFactor_pos))
    (inv_nonneg.mpr (sq_nonneg s))

/-- `cnPlusBox` is a sum of integrals of squares. -/
lemma cnPlusBox_nonneg (a : ℝ) (A : Set ℝ³) (volA : ℝ) {N : ℕ} (Ψ : X N → ℝ) :
    0 ≤ cnPlusBox a A volA Ψ := by
  unfold cnPlusBox
  exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))

/-- `tBdiagForm` is nonnegative for a nonnegative symbol. -/
lemma tBdiagForm_nonneg {a : ℝ} {A : Set ℝ³} {volA : ℝ} {χ : ℝ³ → ℝ} {F : ℝ → ℝ}
    {N : ℕ} {Ψ : X N → ℝ} (ha : 0 ≤ a) (hF : ∀ r, 0 ≤ F r) :
    0 ≤ tBdiagForm a A volA χ F Ψ := by
  unfold tBdiagForm
  refine Finset.sum_nonneg (fun i _ => ?_)
  refine mul_nonneg (le_of_lt twoPiInv3_pos) ?_
  refine integral_nonneg (fun p => ?_)
  refine mul_nonneg (hF ‖p‖) ?_
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ha 3))
    (integral_nonneg (fun x => sq_nonneg _))

/-- **Monotonicity of `tBdiagForm` in the symbol.** -/
lemma tBdiagForm_mono {a : ℝ} {A : Set ℝ³} {volA : ℝ} {χ : ℝ³ → ℝ} {F G : ℝ → ℝ}
    {N : ℕ} {Ψ : X N → ℝ} (ha : 0 ≤ a) (hF0 : ∀ r, 0 ≤ F r) (hFG : ∀ r, F r ≤ G r)
    (hF : ∀ i : Fin N, Integrable (fun p : ℝ³ => F ‖p‖ *
      ((a ^ 3)⁻¹ * ∫ x in abox N a, ‖tBamp χ p (boxQ volA A i Ψ) i x‖ ^ 2)))
    (hG : ∀ i : Fin N, Integrable (fun p : ℝ³ => G ‖p‖ *
      ((a ^ 3)⁻¹ * ∫ x in abox N a, ‖tBamp χ p (boxQ volA A i Ψ) i x‖ ^ 2))) :
    tBdiagForm a A volA χ F Ψ ≤ tBdiagForm a A volA χ G Ψ := by
  unfold tBdiagForm
  refine Finset.sum_le_sum (fun i _ => ?_)
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt twoPiInv3_pos)
  refine integral_mono_of_nonneg (Eventually.of_forall (fun p => ?_))
    (hG i) (Eventually.of_forall (fun p => ?_))
  · exact mul_nonneg (hF0 ‖p‖)
      (mul_nonneg (inv_nonneg.mpr (pow_nonneg ha 3))
        (integral_nonneg (fun x => sq_nonneg _)))
  · exact mul_le_mul_of_nonneg_right (hFG ‖p‖)
      (mul_nonneg (inv_nonneg.mpr (pow_nonneg ha 3))
        (integral_nonneg (fun x => sq_nonneg _)))

/-- The spectral half of `𝒯_B` is nonnegative. -/
lemma tBwordKin_nonneg {a : ℝ} (A : Set ℝ³) (volA : ℝ) (χ : ℝ³ → ℝ) (c : ℝ)
    {N : ℕ} (Ψ : X N → ℝ) (ha : 0 ≤ a) : 0 ≤ tBwordKin a A volA χ c Ψ := by
  unfold tBwordKin
  exact tBdiagForm_nonneg ha (fun r => fsKinCoeff_nonneg c r)

/-- **Property (a), plain form**: the `Q_B`-gap part is a lower bound for the
word `𝒯_B` (FS `eq:appTB`; the spectral half is nonnegative). -/
theorem tBword_ge_gapPart {a s ε c : ℝ} {A : Set ℝ³} {volA : ℝ} {χ : ℝ³ → ℝ}
    {N : ℕ} {Ψ : X N → ℝ} (ha : 0 ≤ a) :
    tbGapCoeff s ε * cnPlusBox a A volA Ψ ≤ tBword a A volA χ s ε c Ψ := by
  unfold tBword
  exact le_add_of_nonneg_right (tBwordKin_nonneg A volA χ c Ψ ha)

/-- `[r−c]₊² ≤ r²` for every real `r` (`0 ≤ c`; the version at all `r`, used by the
symbol monotonicity, where the Bridge's `fsKinCoeff_le_sq` only covers `0 ≤ r`). -/
lemma fsKinCoeff_le_sq_all {c r : ℝ} (hc : 0 ≤ c) : fsKinCoeff c r ≤ r ^ 2 := by
  by_cases hr : 0 ≤ r
  · exact fsKinCoeff_le_sq hc hr
  · have hmax : max (r - c) 0 = 0 := by
      rw [max_eq_right]
      linarith
    rw [fsKinCoeff, hmax]
    simpa using sq_nonneg r

theorem tBwordKin_le_tBdiagForm_sq {a c : ℝ} {A : Set ℝ³} {volA : ℝ} {χ : ℝ³ → ℝ}
    {N : ℕ} {Ψ : X N → ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hintF : ∀ i : Fin N, Integrable (fun p : ℝ³ => fsKinCoeff c ‖p‖ *
      ((a ^ 3)⁻¹ * ∫ x in abox N a, ‖tBamp χ p (boxQ volA A i Ψ) i x‖ ^ 2)))
    (hintG : ∀ i : Fin N, Integrable (fun p : ℝ³ => (‖p‖ ^ 2) *
      ((a ^ 3)⁻¹ * ∫ x in abox N a, ‖tBamp χ p (boxQ volA A i Ψ) i x‖ ^ 2))) :
    tBwordKin a A volA χ c Ψ ≤ tBdiagForm a A volA χ (fun r => r ^ 2) Ψ := by
  unfold tBwordKin
  exact tBdiagForm_mono ha (F := fsKinCoeff c) (G := fun r => r ^ 2)
    (fun r => fsKinCoeff_nonneg c r) (fun r => fsKinCoeff_le_sq_all hc) hintF hintG

end Work.SmallBoxTBWord
