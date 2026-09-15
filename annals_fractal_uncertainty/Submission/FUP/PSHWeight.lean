import Submission.FUP.PSHExtension
import Submission.Commons.Analysis.Calculus.iteratedFDeriv_two_sqrt_one_add_norm_sq

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators Real RealInnerProductSpace Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-!
# The weight `⟨y⟩ = sqrt(1+‖y‖²)` of §5

Cohen's §5 (`sec:constr_entire_from_psh`) uses the plurisubharmonic weight

  `φ = 2u + 20d log‖z‖_∞ + ρ u₀ + (ρ/2)(⟨y⟩ - 1)`,  `⟨y⟩ = sqrt(1 + ‖y‖²)`,

and the key estimate `eq:varphi_deldelbar_bd`, `∂∂̄φ(z) ≥ κ(z) = (ρ/8)⟨y⟩^{-3}`, obtained from
the explicit computation

  `∂∂̄⟨y⟩ = (1/4)⟨y⟩^{-3}(1 + |y|² - y yᵗ)`.

In the real coordinates `z = (x,y) ∈ ℝᵈ × ℝᵈ` the complex Hessian of a weight depending only on
`y` in the direction `v = (v₁,v₂)` is `(D²u y)![v₁,v₁] + (D²u y)![v₂,v₂]` (the two directions of
the complex line are `(v₁,v₂)` and `(-v₂,v₁)`, which project to `v₂` and `v₁`).  The lemma below
is exactly the resulting lower bound, which is the `d`-dimensional content of
`eq:varphi_deldelbar_bd`; it is reduced to the shared commons computation
`Commons.Analysis.Calculus.iteratedFDeriv_two_sqrt_one_add_norm_sq`.
-/

/-- **`∂∂̄⟨y⟩ ≥ ⟨y⟩^{-3}·Id`** (Cohen's §5, `eq:varphi_deldelbar_bd`), in the `(Re,Im)`
coordinates: the sum of the second derivatives of `⟨y⟩ = sqrt(1+‖y‖²)` in the two real
directions of a complex line is at least `‖v‖²/⟨y⟩³`. -/
theorem complexHessian_sqrt_one_add_norm_sq_bound (y v₁ v₂ : ℝᵈ) :
    (‖v₁‖ ^ 2 + ‖v₂‖ ^ 2) / (Real.sqrt (1 + ‖y‖ ^ 2)) ^ 3
      ≤ (iteratedFDeriv ℝ 2 (fun z : ℝᵈ => Real.sqrt (1 + ‖z‖ ^ 2)) y) ![v₁, v₁]
        + (iteratedFDeriv ℝ 2 (fun z : ℝᵈ => Real.sqrt (1 + ‖z‖ ^ 2)) y) ![v₂, v₂] := by
  rw [Commons.Analysis.Calculus.iteratedFDeriv_two_sqrt_one_add_norm_sq y v₁,
    Commons.Analysis.Calculus.iteratedFDeriv_two_sqrt_one_add_norm_sq y v₂]
  set s : ℝ := Real.sqrt (1 + ‖y‖ ^ 2) with hs
  have hs2 : s ^ 2 = 1 + ‖y‖ ^ 2 := by rw [hs]; exact Real.sq_sqrt (by positivity)
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (by positivity)
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hcs1 : (inner ℝ y v₁) ^ 2 ≤ ‖y‖ ^ 2 * ‖v₁‖ ^ 2 := by
    have h := abs_real_inner_le_norm y v₁
    nlinarith [h, abs_nonneg (inner ℝ y v₁), sq_abs (inner ℝ y v₁), norm_nonneg y]
  have hcs2 : (inner ℝ y v₂) ^ 2 ≤ ‖y‖ ^ 2 * ‖v₂‖ ^ 2 := by
    have h := abs_real_inner_le_norm y v₂
    nlinarith [h, abs_nonneg (inner ℝ y v₂), sq_abs (inner ℝ y v₂), norm_nonneg y]
  have hkey : (‖v₁‖ ^ 2 / s - (inner ℝ y v₁) ^ 2 / s ^ 3)
        + (‖v₂‖ ^ 2 / s - (inner ℝ y v₂) ^ 2 / s ^ 3) - (‖v₁‖ ^ 2 + ‖v₂‖ ^ 2) / s ^ 3
      = (‖y‖ ^ 2 * (‖v₁‖ ^ 2 + ‖v₂‖ ^ 2) - (inner ℝ y v₁) ^ 2 - (inner ℝ y v₂) ^ 2) / s ^ 3 := by
    field_simp
    rw [hs2]
    ring
  rw [← sub_nonneg, hkey]
  exact div_nonneg (by nlinarith [hcs1, hcs2]) (by positivity)

end Submission.FUP
