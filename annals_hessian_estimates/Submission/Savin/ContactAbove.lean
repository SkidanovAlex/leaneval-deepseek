/-
# The from-above contact bound for the `σ₂` equation on the positive branch

For a solution of `σ₂(D²u) = 1` with `Δu > 0` (the *positive branch*), one can slide paraboloids
**from above** as well as from below: the map `x ↦ x - b⁻¹∇u(x)` has derivative `1 - b⁻¹D²u(x)`,
and at a contact point of a paraboloid of opening `b` one has `D²u(x) ⪯ b • 1`.  The bound needed to
make the Jacobian bounded is the *lower* bound `D²u(x) ⪰ -K b • 1`.

This is **false** if one only knows the quadratic expansion `σ₂(A+M) - σ₂(A) = tr(cof A ∘ M) + σ₂(M)`
of the operator around `A` (the quadratic term `σ₂(M)` is not controlled).  It is **true** when the
*concavity* of the square-root formulation
`H(M) = trM - √(2 + tr(M ∘ M))` (which vanishes exactly on the positive branch of `σ₂ = 1`) is
used: `H` is concave and `H(A) = H(A+M) = 0` gives `tr(cof A ∘ M) ≥ 0`, from which the bound
follows (see `Submission/Roadmap.md`, SESSION 27).

The two ingredients from the commons are
* `Commons.Analysis.Trace.trace_sub_sqrt_tangent` (the tangency inequality for `H`), and
* `Commons.Algebra.Order.negPart_mul_le_of_sum_mul_nonneg` (the elementary sign-splitting bound).

`Submission.contact_bound` (SESSION 25) is the analogous *from-below* estimate; there the argument
only uses `M ⪰ -a•1` and is uniform in the reference operator `A`.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Operator
import Submission.Commons.Analysis.Sigma2.coord_minor_sum_eq_trace_invariants
import Submission.Commons.Analysis.Trace.trace_sub_sqrt_tangent
import Submission.Commons.Algebra.Order.negPart_mul_le_of_sum_mul_nonneg

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- `(trOp A)² = 2 + trOp (A ∘ A)` whenever `A` is symmetric with `s2 A = 1`: this is the identity
`(Σ λᵢ)² = Σ λᵢ² + 2 Σ_{i<j} λᵢλⱼ` of the coordinate minor sum
(`Commons.Analysis.Sigma2.coord_minor_sum_eq_trace_invariants`).  Equivalently, `A` lies on the
positive branch of the quadric `{σ₂ = 1}`, where `tr A = √(2 + tr (A ∘ A))`. -/
theorem trOp_sq_eq_two_add_of_s2_eq_one {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (h : s2 A = 1) :
    (trOp A) ^ 2 = 2 + trOp (A * A) := by
  have h1 := Commons.Analysis.Sigma2.coord_minor_sum_eq_trace_invariants hA stdB4
  have h2 : s2 A = ∑ j : Fin 4, ∑ i : Fin 4, if i < j then
      (⟪A (stdB4 i), stdB4 i⟫ * ⟪A (stdB4 j), stdB4 j⟫ - ⟪A (stdB4 i), stdB4 j⟫ ^ 2) else 0 := rfl
  rw [h2] at h
  rw [h] at h1
  show (LinearMap.trace ℝ ℝ⁴ (A : ℝ⁴ →ₗ[ℝ] ℝ⁴)) ^ 2
      = 2 + LinearMap.trace ℝ ℝ⁴ ((A * A : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴)
  rw [show ((A * A : ℝ⁴ →L[ℝ] ℝ⁴) : ℝ⁴ →ₗ[ℝ] ℝ⁴)
      = (A : ℝ⁴ →ₗ[ℝ] ℝ⁴) ∘ₗ (A : ℝ⁴ →ₗ[ℝ] ℝ⁴) from rfl]
  linarith [h1]

/-- The square-root form of the previous identity: `√(2 + trOp (A ∘ A)) = trOp A` for symmetric
`A` with `s2 A = 1` and `trOp A > 0`. -/
theorem sqrt_two_add_trOp_mul_self {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (h : s2 A = 1)
    (htr : 0 < trOp A) : Real.sqrt (2 + trOp (A * A)) = trOp A := by
  rw [← trOp_sq_eq_two_add_of_s2_eq_one hA h, Real.sqrt_sq_eq_abs, abs_of_pos htr]

/-- `trOp (cofOp A ∘ M) = trOp A * trOp M - trOp (A ∘ M)`. -/
theorem pairOp_sub_left (S₁ S₂ M : ℝ⁴ →L[ℝ] ℝ⁴) :
    pairOp (S₁ - S₂) M = pairOp S₁ M - pairOp S₂ M := by
  unfold pairOp
  simp only [sub_apply, inner_sub_left, Finset.sum_sub_distrib]

theorem pairOp_one_left (M : ℝ⁴ →L[ℝ] ℝ⁴) : pairOp (1 : ℝ⁴ →L[ℝ] ℝ⁴) M = trOp M := by
  rw [pairOp_eq_trace, trOp]
  refine congrArg (LinearMap.trace ℝ ℝ⁴) ?_
  ext x
  rfl

theorem pairOp_cofOp_eq (A M : ℝ⁴ →L[ℝ] ℝ⁴) :
    pairOp (cofOp A) M = trOp A * trOp M - trOp (A * M) := by
  rw [cofOp, pairOp_sub_left, pairOp_const_smul_left, pairOp_one_left]
  congr 1
  rw [pairOp_eq_trace]
  rfl

/-- **From-above contact bound for the `σ₂` equation (positive branch).**

Let `A`, `M` be symmetric operators with `s2 A = s2 (A + M) = 1`, `trOp A > 0`, `trOp (A + M) > 0`,
let `C = cofOp A = trOp A • 1 - A` be bounded below and above by `c > 0` and `c'` in the quadratic
form sense, and suppose `M ⪯ a • 1` with `a ≥ 0`.  Then `M ⪰ -(4 c'/c) a • 1`.

In the application `A = D²Q` is a fixed quadratic solution of `σ₂ = 1` on the positive branch, and
one takes `c = trOp A - λ_max(A) = λ_min(cofOp A) > 0` and `c' = (3/2) trOp A`. -/
theorem contact_bound_above_sigma2 {A M : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hM : M.IsSymmetric)
    (hA1 : s2 A = 1) (hAM1 : s2 (A + M) = 1) (htrA : 0 < trOp A) (htrAM : 0 < trOp (A + M))
    {c c' a : ℝ} (hc : 0 < c) (ha : 0 ≤ a)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    (hMle : ∀ v : ℝ⁴, ⟪M v, v⟫ ≤ a * ‖v‖ ^ 2) :
    ∀ v : ℝ⁴, -(4 * c' / c) * a * ‖v‖ ^ 2 ≤ ⟪M v, v⟫ := by
  have hAsym : (A + M).IsSymmetric := hA.add hM
  -- The tangency inequality for `H(M) = trM - √(2 + tr(M ∘ M))` at `N = A`, `D = M`.
  have htan := Commons.Analysis.Trace.trace_sub_sqrt_tangent hA hM
  rw [show LinearMap.trace ℝ ℝ⁴ ((A + M : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap)
      = trOp (A + M) from rfl,
    show LinearMap.trace ℝ ℝ⁴ (((A + M : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap)
        ∘ₗ ((A + M : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap)) = trOp ((A + M) * (A + M)) from rfl,
    show LinearMap.trace ℝ ℝ⁴ ((A : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap) = trOp A from rfl,
    show LinearMap.trace ℝ ℝ⁴ (((A : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap)
        ∘ₗ ((A : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap)) = trOp (A * A) from rfl,
    show LinearMap.trace ℝ ℝ⁴ ((M : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap) = trOp M from rfl,
    show LinearMap.trace ℝ ℝ⁴ (((A : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap)
        ∘ₗ ((M : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap)) = trOp (A * M) from rfl,
    sqrt_two_add_trOp_mul_self hA hA1 htrA,
    sqrt_two_add_trOp_mul_self hAsym hAM1 htrAM] at htan
  have hone : trOp (A + M) = trOp A + trOp M := by
    unfold trOp
    rw [show ((A + M : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap)
        = (A : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap + (M : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap from rfl, map_add]
  have hpair : 0 ≤ pairOp (cofOp A) M := by
    rw [pairOp_cofOp_eq]
    have h2 : 0 ≤ trOp M - trOp (A * M) / trOp A := by
      have h := htan
      rw [hone] at h
      simpa using h
    have h3 : trOp A * (trOp M - trOp (A * M) / trOp A) = trOp A * trOp M - trOp (A * M) := by
      field_simp
    nlinarith [h3, htrA]
  -- Eigen decomposition of `M`.
  have hfin : Module.finrank ℝ ℝ⁴ = 4 := by simp
  set b : OrthonormalBasis (Fin 4) ℝ ℝ⁴ := hM.eigenvectorBasis hfin with hb
  set lam : Fin 4 → ℝ := hM.eigenvalues hfin with hlam
  set xi : Fin 4 → ℝ := fun i => ⟪cofOp A (b i), b i⟫ with hxi
  have hbunit : ∀ i : Fin 4, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hxi_lo : ∀ i, c ≤ xi i := by
    intro i
    have h := hcq (b i)
    rw [hbunit i, one_pow, mul_one] at h
    exact h
  have hxi_hi : ∀ i, xi i ≤ c' := by
    intro i
    have h := hcq' (b i)
    rw [hbunit i, one_pow, mul_one] at h
    exact h
  have hlam_le : ∀ i, lam i ≤ a := by
    intro i
    have h := hMle (b i)
    rw [hbunit i, one_pow, mul_one] at h
    have h2 : ⟪M (b i), b i⟫ = lam i := by
      change ⟪(M : ℝ⁴ →ₗ[ℝ] ℝ⁴) (b i), b i⟫ = lam i
      rw [hM.apply_eigenvectorBasis hfin i, real_inner_smul_left, real_inner_self_eq_norm_sq,
        hbunit i]
      simp [hlam]
    rwa [h2] at h
  -- `pairOp (cofOp A) M = Σ λᵢ ξᵢ`.
  have hsum : pairOp (cofOp A) M = ∑ i : Fin 4, lam i * xi i := by
    rw [pairOp_eq_trace]
    rw [LinearMap.trace_eq_sum_inner ((cofOp A : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap
      ∘ₗ (M : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap) b]
    apply Finset.sum_congr rfl
    intro i _
    have h2 : ((cofOp A : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap
        ∘ₗ (M : ℝ⁴ →L[ℝ] ℝ⁴).toLinearMap) (b i) = lam i • (cofOp A (b i)) := by
      rw [LinearMap.comp_apply]
      have hMbi : (M : ℝ⁴ →ₗ[ℝ] ℝ⁴) (b i) = lam i • b i := hM.apply_eigenvectorBasis hfin i
      rw [hMbi, map_smul]
      rfl
    rw [h2, real_inner_smul_right]
    have h3 : ⟪b i, (cofOp A) (b i)⟫ = xi i := real_inner_comm _ _
    rw [h3]
  have hnegsplit := Commons.Algebra.Order.negPart_mul_le_of_sum_mul_nonneg hc hxi_lo hxi_hi
    hlam_le ha (by rw [← hsum]; exact hpair)
  -- Hence `Σ max(-λᵢ) 0 ≤ 4 c' a / c`.
  have hbound : (∑ i : Fin 4, max (-(lam i)) 0) ≤ 4 * c' * a / c := by
    rw [le_div_iff₀ hc]
    have hcard : (Fintype.card (Fin 4) : ℝ) = 4 := by simp
    rwa [hcard] at hnegsplit
  -- Conclude the quadratic-form bound.
  intro v
  have hexp : ⟪M v, v⟫ = ∑ i : Fin 4, lam i * (⟪b i, v⟫) ^ 2 := by
    have hsym : ∀ i : Fin 4, ⟪M v, b i⟫ = lam i * ⟪b i, v⟫ := by
      intro i
      have hMbi : (M : ℝ⁴ →ₗ[ℝ] ℝ⁴) (b i) = lam i • b i := hM.apply_eigenvectorBasis hfin i
      have h1 : ⟪M v, b i⟫ = ⟪v, (M : ℝ⁴ →ₗ[ℝ] ℝ⁴) (b i)⟫ := hM v (b i)
      rw [h1, hMbi, real_inner_smul_right, real_inner_comm v (b i)]
    rw [← b.sum_inner_mul_inner (M v) v]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym i]; ring
  have hnorm : ‖v‖ ^ 2 = ∑ i : Fin 4, (⟪b i, v⟫) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [← b.sum_inner_mul_inner v v]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm]; ring
  have hterm : ∀ i : Fin 4, -(4 * c' / c) * a * (⟪b i, v⟫) ^ 2 ≤ lam i * (⟪b i, v⟫) ^ 2 := by
    intro i
    have hli : -(4 * c' / c) * a ≤ lam i := by
      have h1 : -(∑ j : Fin 4, max (-(lam j)) 0) ≤ lam i := by
        have hle := Finset.single_le_sum (f := fun j : Fin 4 => max (-(lam j)) 0)
          (fun j _ => le_max_right _ _) (Finset.mem_univ i)
        have hge : -(lam i) ≤ max (-(lam i)) 0 := le_max_left _ _
        linarith
      have h2 : -(∑ j : Fin 4, max (-(lam j)) 0) ≥ -(4 * c' * a / c) := by linarith [hbound]
      have h3 : -(4 * c' * a / c) = -(4 * c' / c) * a := by ring
      linarith [h2, h3]
    exact mul_le_mul_of_nonneg_right hli (sq_nonneg _)
  calc -(4 * c' / c) * a * ‖v‖ ^ 2
        = -(4 * c' / c) * a * ∑ i : Fin 4, (⟪b i, v⟫) ^ 2 := by rw [hnorm]
    _ = ∑ i : Fin 4, -(4 * c' / c) * a * (⟪b i, v⟫) ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ i : Fin 4, lam i * (⟪b i, v⟫) ^ 2 := Finset.sum_le_sum (fun i _ => hterm i)
    _ = ⟪M v, v⟫ := hexp.symm

end

end Submission
