import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.integrableOn_Pz_div_pow
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.hasDerivAt_Pz
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.sq_two_Qz_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12Aux.abs_Qang_le
import Submission.Work.Analysis.WeightedPoincare.le_cube_mul_of_deriv_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.L12Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The angular moment of a `ClassC` profile vanishes faster than `z^{1/2}` at `z = 0`.**

`Work.Elliptic.Qang x k z = ∫_{Iθ} K(θ)·D_z^k x(z,θ) dθ` (`K = 3 sin θ cos²θ`).

This is the analytic heart of `RegQo α 4 (𝓛_Γ^T x)` from `ClassC α x`: the traces of the
nonlocal term `(2zΓ/(c(1+z)²))·L₁₂(x)(z)` at `z → 0⁺` require `D_z^k L₁₂(x) = O(z^{3/2})`,
i.e. `Qang x k = O(z^{3/2})`.

Route (all inputs are in the tree).  Put `P_k(z) = ∫_θ (D_z^k x(z,θ))² sin(2θ)^{-η}dθ`,
`η = 99/100`, `R_k = sqrt(P_k)`.
* `∫_{Iz} w(z)² P_k(z) dz < ∞` for `k ≤ 4` (`w = (1+z)²/z²`): the first sum of
  `HkIntegrand α 10 x` contains the slot `(D_z^k x · w · sin(2θ)^{-η/2})²`, and `HkMem α 10 x`
  is a field of `ClassC`; since `w(z)² ≥ z^{-4}` on `(0,1)`, this gives
  `∫_0^1 P_k z^{-4} < ∞`.
* `z P_k'(z) = 2 ∫_θ (D_z^k x)(D_z^{k+1} x)·sin(2θ)^{-η}dθ` (differentiation under the angular
  integral; the dominating function is `2·M_k·M_{k+1}/z₀·sin(2θ)^{-η}`, integrable, with the
  *uniform* pointwise bounds `M_k` supplied by
  `Work.FTS.StrongEps.classC_mixed_sup_le_four`).  Cauchy–Schwarz gives
  `|z P_k'| ≤ 2 sqrt(P_k P_{k+1})`, i.e. `(z R_k')² ≤ P_{k+1}`.
* Local Poincaré inside a dyadic window: for `z ∈ (0,1)` and `I = (z/2, z)`, one gets
  `R_k(z)² ≤ z³(J_2 + 4J_0)` with `J_0 = ∫_0^1 P_k z^{-4}`, `J_2 = ∫_0^1 (R_k')² z^{-2} ≤ ∫_0^1 P_{k+1} z^{-4}`.
* Cauchy–Schwarz in θ: `|Qang x k z| ≤ (∫_{Iθ} K² sin(2θ)^{η})^{1/2}·R_k(z)`.

Note the last step needs `k` and `k+1` slots only, so `k ≤ 3` (i.e. `k+1 ≤ 4`) is the
admissible range. -/
theorem Qang_small_z {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {x : Work.FTS.Galerkin.Fn}
    (hx : Work.FTS.ClassC.ClassC α x) {k : ℕ} (hk : k ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z → z < 1 →
      |Work.Elliptic.Qang x k z| ≤ C * z ^ ((3 : ℝ) / 2) := by
  have hk4 : k + 1 ≤ 4 := by omega
  -- the three constants of the bound
  set KK : ℝ := ∫ θ in Work.Spaces.Iθ,
    (Work.Elliptic.Ktheta θ) ^ 2 * (Real.sin (2 * θ)) ^ (Work.Spaces.eta) with hKK
  set J0 : ℝ := ∫ t in Set.Ioo (0 : ℝ) 1, Pz x k t / t ^ 4 with hJ0def
  set J1 : ℝ := ∫ t in Set.Ioo (0 : ℝ) 1, Pz x (k + 1) t / t ^ 4 with hJ1def
  refine ⟨Real.sqrt KK * Real.sqrt (4 * J0 + J1) + 1, by positivity, ?_⟩
  intro z hz0 hz1
  -- Cauchy–Schwarz in θ (the last bullet)
  have hE : |Work.Elliptic.Qang x k z| ≤ Real.sqrt KK * Real.sqrt (Pz x k z) := by
    rw [hKK]
    exact abs_Qang_le hα hx hk z hz0
  -- the derivative and the Cauchy–Schwarz bound (the second bullet)
  have hd : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (Pz x k) ((fun t => 2 / t * Qz x k t) t) t :=
    fun t ht => hasDerivAt_Pz hα hx hk ht.1
  have hbnd : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (t * (2 / t * Qz x k t)) ^ 2 ≤ 4 * Pz x k t * Pz x (k + 1) t := by
    intro t ht
    have hq : t * (2 / t * Qz x k t) = 2 * Qz x k t := by
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      field_simp
    rw [hq]
    exact sq_two_Qz_le hα hx hk ht.1
  -- the local Poincaré bound of the route (third bullet)
  have hA : Pz x k z ≤ z ^ 3 * (4 * J0 + J1) :=
    Work.Analysis.WeightedPoincare.le_cube_mul_of_deriv_bound
      (P := Pz x k) (Pd := fun t => 2 / t * Qz x k t) (P1 := Pz x (k + 1))
      (J0 := J0) (J1 := J1) hz0 hz1 hd
      (fun t _ => Pz_nonneg x k t) (fun t _ => Pz_nonneg x (k + 1) t) hbnd
      (by exact integrableOn_Pz_div_pow hx (by omega))
      (by exact integrableOn_Pz_div_pow hx hk4)
      (le_of_eq hJ0def.symm) (le_of_eq hJ1def.symm)
  -- assemble
  have hsq : Real.sqrt (Pz x k z) ≤ Real.sqrt (z ^ 3 * (4 * J0 + J1)) :=
    Real.sqrt_le_sqrt hA
  have hsplit : Real.sqrt (z ^ 3 * (4 * J0 + J1))
      = Real.sqrt (z ^ 3) * Real.sqrt (4 * J0 + J1) :=
    Real.sqrt_mul (by positivity) _
  have hz32 : Real.sqrt (z ^ 3) = z ^ ((3 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast z 3, ← Real.rpow_mul (le_of_lt hz0)]
    norm_num
  calc |Work.Elliptic.Qang x k z| ≤ Real.sqrt KK * Real.sqrt (Pz x k z) := hE
    _ ≤ Real.sqrt KK * Real.sqrt (z ^ 3 * (4 * J0 + J1)) :=
        mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
    _ = Real.sqrt KK * Real.sqrt (4 * J0 + J1) * z ^ ((3 : ℝ) / 2) := by
        rw [hsplit, hz32]; ring
    _ ≤ (Real.sqrt KK * Real.sqrt (4 * J0 + J1) + 1) * z ^ ((3 : ℝ) / 2) := by
        have h1 : 0 ≤ Real.sqrt KK * Real.sqrt (4 * J0 + J1) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        have h2 : 0 ≤ z ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (le_of_lt hz0) _
        nlinarith

end Work.FTS.StrongEps.EpsE4Thr.L12Aux
