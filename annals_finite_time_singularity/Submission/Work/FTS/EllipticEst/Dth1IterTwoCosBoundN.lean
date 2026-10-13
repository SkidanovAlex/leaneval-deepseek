import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.Algebra
import Submission.Work.FTS.EllipticEst.Dth1IterTwoCosDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

noncomputable section

/-! ## The recursion of `D_θ` on multiples of `sin(2θ)²` -/

/-- `(sin 2θ)²` has derivative `4 sin 2θ cos 2θ`. -/
private lemma deriv_sin_two_sq (θ : ℝ) :
    deriv (fun t : ℝ => Real.sin (2 * t) ^ 2) θ
      = 4 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h1
  have h3 := h2.pow 2
  have h4 : deriv (fun t : ℝ => Real.sin (2 * t) ^ 2) θ
      = 2 * Real.sin (2 * θ) ^ (2 - 1) * (Real.cos (2 * θ) * 2) := h3.deriv
  rw [h4]; ring

/-- The recursion of `D_θ = sin(2θ) ∂_θ` on a function of the form `sin(2θ)² · g`: dividing by
`sin(2θ)²` transforms `g` by `g ↦ 4 cos(2θ) · g + sin(2θ) · g'`. -/
private lemma Dth1_sin_sq_mul (θ : ℝ) (g : ℝ → ℝ) (hg : DifferentiableAt ℝ g θ) :
    Work.Elliptic.Dth1 (fun t : ℝ => Real.sin (2 * t) ^ 2 * g t) θ
      = Real.sin (2 * θ) ^ 2 *
          (4 * Real.cos (2 * θ) * g θ + Real.sin (2 * θ) * deriv g θ) := by
  have hsin : DifferentiableAt ℝ (fun t : ℝ => Real.sin (2 * t) ^ 2) θ := by fun_prop
  have hprod : deriv (fun t : ℝ => Real.sin (2 * t) ^ 2 * g t) θ
      = deriv (fun t : ℝ => Real.sin (2 * t) ^ 2) θ * g θ
        + Real.sin (2 * θ) ^ 2 * deriv g θ := by
    have hfun : (fun t : ℝ => Real.sin (2 * t) ^ 2 * g t)
        = (fun t : ℝ => Real.sin (2 * t) ^ 2) * g := by
      funext t; rw [Pi.mul_apply]
    rw [hfun]
    exact deriv_mul hsin hg
  simp only [Work.Elliptic.Dth1]
  rw [hprod, deriv_sin_two_sq]
  ring

/-! ## The factorisation of the iterates -/

/-- `D_θ^{n+1}(2 cos 2θ) = sin(2θ)² · gSeq n`, as an identity of functions. -/
private lemma Dth1Iter_two_cos_factor_fun (n : ℕ) :
    Work.Elliptic.Dth1Iter (n + 1) (fun t : ℝ => 2 * Real.cos (2 * t))
      = fun θ => Real.sin (2 * θ) ^ 2 * gSeq n θ := by
  induction n with
  | zero =>
    funext θ
    simp only [Work.Elliptic.Dth1Iter_succ, Work.Elliptic.Dth1Iter_zero, Work.Elliptic.Dth1,
      gSeq_zero]
    rw [Work.Elliptic.deriv_two_cos_two]
    ring
  | succ n ih =>
    rw [Work.Elliptic.Dth1Iter_succ, ih]
    funext θ
    rw [Dth1_sin_sq_mul θ (gSeq n) ((gSeq_differentiable n).differentiableAt), gSeq_succ]

/-- `D_θ^{n+1}(2 cos 2θ) = sin(2θ)² · gSeq n`, pointwise. -/
private lemma Dth1Iter_two_cos_factor (n : ℕ) (θ : ℝ) :
    Work.Elliptic.Dth1Iter (n + 1) (fun t : ℝ => 2 * Real.cos (2 * t)) θ
      = Real.sin (2 * θ) ^ 2 * gSeq n θ :=
  congrFun (Dth1Iter_two_cos_factor_fun n) θ

/-- For every `k ≥ 1` the `k`-th iterate `D_θ^k (2 cos 2θ)` of the angular operator
`D_θ = sin(2θ) ∂_θ` is bounded, uniformly over ALL real `θ`, by a constant times `sin(2θ)²`
(not merely on the interval `[0, π/2]`).

ROUTE. Prove globally (`∀ θ : ℝ`) the factorisation `D_θ^j (2 cos 2θ) θ = sin(2θ)^2 * g_j θ`,
where `g_1 := fun _ => -4` and `g_{j+1} := 4 cos(2θ) * g_j + sin(2θ) * deriv g_j`, from the
recursion `D_θ (sin(2θ)^2 g) = sin(2θ)^2 (4 cos(2θ) g + sin(2θ) g')`.  Each `g_j` is `C^∞` and
`π`-periodic (the derivative of a `π`-periodic function is `π`-periodic; `sin(2·)`, `cos(2·)`
are `π`-periodic), so it is bounded on `ℝ`: bound it on the compact `[0, π]`
(`isCompact_Icc.exists_bound_of_continuousOn`) and transport to any point with
`Function.Periodic.exists_mem_Ico₀`.  Compare `Work.Elliptic.DivSinPhiBound`
(`Submission/Work/Elliptic/DivSinPhiBound.lean`), which does the cases `k = 1,2,3` by explicit
formulas. -/
theorem Dth1IterTwoCosBoundN (k : ℕ) (hk : 1 ≤ k) :
    ∃ M : ℝ, 0 < M ∧ ∀ θ : ℝ,
      |Work.Elliptic.Dth1Iter k (fun t : ℝ => 2 * Real.cos (2 * t)) θ|
        ≤ M * (Real.sin (2 * θ)) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨C, hCpos, hC⟩ := gSeq_bdd m
  refine ⟨C, hCpos, fun θ => ?_⟩
  rw [Dth1Iter_two_cos_factor m θ, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin (2 * θ)))]
  calc Real.sin (2 * θ) ^ 2 * |gSeq m θ| ≤ Real.sin (2 * θ) ^ 2 * C :=
        mul_le_mul_of_nonneg_left (hC θ) (sq_nonneg (Real.sin (2 * θ)))
    _ = C * Real.sin (2 * θ) ^ 2 := by ring

end

end Work.FTS.EllipticEst
