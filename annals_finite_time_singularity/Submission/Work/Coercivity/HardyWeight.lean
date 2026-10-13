/-
# Lemma `HardyWeight` of the coercivity chapter

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021), Lemma `HardyWeight`:
if `f w ∈ L²` and `L₁₂(f) w ∈ L²` then `|L₁₂(f) w|_{L²} ≤ 4 |f w|_{L²}`.  Here we prove the
(squared, weaker-constant) form needed downstream,
`|L₁₂(f) w|²_{L²} ≤ 1024 |f w|²_{L²}`.

The proof decomposes as
* `Work.Coercivity.angular_avg_w_sq_le` — the angular average
  `g z = ∫_θ K θ f z θ` satisfies `∫ g² w² ≤ 3 ∫ w² (∫_θ f²)`;
* `Work.Coercivity.L12f_w_hardy` — the weighted Hardy bound
  `∫ (L₁₂(f) w)² ≤ 107 ∫ g² w²`;
* and the elementary reduction of the two `L²`-norms over `[0,∞) × [0,π/2]` to the radial
  integrals (`L2Sq_radial`, `L2Sq_mul_w_slice`), together with the numerical bound
  `(π/2) · 107 · 3 ≤ 1024`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.L12f_w_hardy
import Submission.Work.Coercivity.angular_avg_w_sq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The squared `L²`-norm of a radial function `z ↦ G z`, viewed as a function of `(z,θ)`:
the `θ`-integral of a constant is `π/2` times that constant. -/
theorem L2Sq_radial (G : ℝ → ℝ) :
    Spaces.L2Sq (fun z _ => G z) = (Real.pi / 2) * ∫ z in Spaces.Iz, (G z) ^ 2 := by
  rw [Spaces.L2Sq]
  have h1 : ∀ z, (∫ θ in Spaces.Iθ, (G z) ^ 2) = (Real.pi / 2) * (G z) ^ 2 := by
    intro z
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul]
    congr 1
    rw [Spaces.Iθ, MeasureTheory.Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  simp_rw [h1]
  rw [MeasureTheory.integral_const_mul]

/-- `|f w|²_{L²}` as the radial integral of `w² ∫_θ f²`. -/
theorem L2Sq_mul_w_slice (f : ℝ → ℝ → ℝ) :
    Spaces.L2Sq (fun z θ => f z θ * Spaces.w z)
      = ∫ z in Spaces.Iz, (Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ, (f z θ) ^ 2) := by
  rw [Spaces.L2Sq]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
  intro z _
  change (∫ θ in Spaces.Iθ, (f z θ * Spaces.w z) ^ 2)
      = (Spaces.w z) ^ 2 * ∫ θ in Spaces.Iθ, (f z θ) ^ 2
  rw [show (fun θ => (f z θ * Spaces.w z) ^ 2)
        = (fun θ => (Spaces.w z) ^ 2 * (f z θ) ^ 2) from by funext θ; ring]
  rw [MeasureTheory.integral_const_mul]

/-- **Lemma `HardyWeight`** of the paper: the weighted `L²` norm of `L₁₂(f)` is controlled by
that of `f`, on the quadrant `[0,∞) × [0,π/2]` with measure `dz dθ`. -/
theorem HardyWeight (f : ℝ → ℝ → ℝ) (hf : HardyHyp f)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Spaces.w z) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    Spaces.L2Sq (fun z θ => L12f f z * Spaces.w z)
      ≤ 1024 * Spaces.L2Sq (fun z θ => f z θ * Spaces.w z) := by
  obtain ⟨hgint, hgle⟩ := angular_avg_w_sq_le f hf hfw
  obtain ⟨_, hUle⟩ := L12f_w_hardy f hf hgint
  rw [L2Sq_radial (fun z => L12f f z * Spaces.w z), L2Sq_mul_w_slice f]
  have hWInn : (0 : ℝ) ≤
      ∫ z in Spaces.Iz, (Spaces.w z) ^ 2 * (∫ θ in Spaces.Iθ, (f z θ) ^ 2) :=
    integral_nonneg fun z => mul_nonneg (sq_nonneg _) (integral_nonneg fun θ => sq_nonneg _)
  have hnum : (Real.pi / 2) * 107 * 3 ≤ (1024 : ℝ) := by nlinarith [Real.pi_lt_four]
  nlinarith [hUle, hgle, hWInn, hnum, Real.pi_pos]

end Work.Coercivity
