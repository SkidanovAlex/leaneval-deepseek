import Mathlib
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.isRepelling_iterate_mul
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Interface

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Repelling periodic points lie in the closure of the escaping set

Let `T_c z = z̄² + c` be the antiholomorphic quadratic and let `y` be a **repelling periodic
point** of `T_c` of odd period `k`, measured through the holomorphic second return map
`(T_c)^{2k} = (Tsq c)^[k]`:

`Work.Landing.IsRepelling c k y` says `(T_c)^[k] y = y` and `1 < ‖multiplier2 c k y‖`, where
`multiplier2 c k y = deriv ((Tsq c)^[k]) y`.

The claim proved here is

`y ∈ closure (Work.ParamRays.escapingSet c)`,

i.e. **every neighbourhood of a repelling periodic point contains points whose orbit tends to
infinity** (equivalently, `y` is not in the interior of the filled Julia set — the classical
statement `J(T_c) = ∂ K(T_c)` restricted to repelling periodic points).

## Proof

The argument is elementary and quantitative; it uses no Julia-set theory.

Write `f := (Tsq c)^[k] = (T_c)^{2k}`, a polynomial fixing `y` with multiplier
`λ := multiplier2 c k y = f'(y)`, `‖λ‖ > 1`, so that `(f^n)'(y) = λⁿ` grows exponentially.

Suppose for contradiction that a whole ball `B(y, ε)` is disjoint from the escaping set.  Then
`B(y, ε)` is contained in the filled Julia set `{z | BoundedOrbit c z}`
(`Work.ParamRays.escaping_iff_not_bounded`), so every point of it has *all* its `T_c`-iterates
bounded by the escape radius `M := max 2 ‖c‖` (`Work.ParamRays.norm_le_max_of_bounded`).  In
particular the polynomials `fⁿ` are uniformly bounded by `M` on the disc `B(y, ε/2)`.

Cauchy's estimate (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) then gives

`‖λ‖ⁿ = ‖(fⁿ)'(y)‖ ≤ M / (ε/2)`

for every `n`, which is absurd since `‖λ‖ > 1` makes the left side tend to infinity.  Hence no
ball around `y` avoids the escaping set, i.e. `y ∈ closure (escapingSet c)`.

The identity `(fⁿ)'(y) = λⁿ` is the chain rule for iterates at a fixed point
(`HasDerivAt.iterate`), and `fⁿ z = orbit c z (2 * k * n)` transfers the boundedness of the
`T_c`-orbits to boundedness of the `fⁿ`.
-/

open Filter

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar)

/-- **A repelling periodic point of `T_c` lies in the closure of the escaping set.**

This is the `∂K = J` statement in the only form needed by the landing theory: a repelling
periodic orbit cannot lie in the interior of the filled Julia set, so arbitrarily close to it
there are points escaping to infinity. -/
theorem closure_escapingSet_of_isRepelling {c : ℂ} {k : ℕ} {y : ℂ}
    (hrep : Work.Landing.IsRepelling c k y) :
    y ∈ closure (Work.ParamRays.escapingSet c) := by
  -- suppose a whole ball around `y` misses the escaping set
  by_contra hcon
  rw [Metric.mem_closure_iff] at hcon
  push Not at hcon
  obtain ⟨ε, hεpos, hε⟩ := hcon
  -- then that ball lies in the filled Julia set, so all orbits there are bounded by the escape
  -- radius `M = max 2 ‖c‖`
  have hbdd : ∀ z : ℂ, dist z y < ε → Work.ParamRays.BoundedOrbit c z := by
    intro z hz
    by_contra hz'
    have hmem : z ∈ Work.ParamRays.escapingSet c :=
      Work.ParamRays.mem_escapingSet.mpr ((Work.ParamRays.escaping_iff_not_bounded c z).mpr hz')
    have h := hε z hmem
    rw [dist_comm] at h
    linarith
  set M : ℝ := max 2 ‖c‖ with hM
  have hbound : ∀ z : ℂ, dist z y < ε → ∀ m : ℕ, ‖Work.ParamRays.orbit c z m‖ ≤ M := by
    intro z hz m
    rw [hM]
    exact Work.ParamRays.norm_le_max_of_bounded c _ ((hbdd z hz).shift m)
  set R : ℝ := ε / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  -- `f = (Tsq c)^[k]` is a polynomial
  have hTsq : Differentiable ℂ (Work.Landing.Tsq c) := by
    unfold Work.Landing.Tsq
    fun_prop
  have hiter : (Work.Landing.Tsq c)^[k] = (Tantibar c)^[2 * k] := by
    rw [Work.LandLeaves.Tsq_eq_iterate_two, Function.iterate_mul]
  -- `y` is a fixed point of `f`
  have hgfix : ((Work.Landing.Tsq c)^[k]) y = y := by
    rw [hiter, show 2 * k = k * 2 from by ring, Function.iterate_mul]
    exact (show Function.IsFixedPt ((Tantibar c)^[k]) y from hrep.1.2).iterate 2
  -- Cauchy's estimate bounds the derivative of the `n`-th iterate on the ball of radius `R`
  have hkey : ∀ n : ℕ, ‖Work.Landing.multiplier2 c k y‖ ^ n ≤ M / R := by
    intro n
    have hd : Differentiable ℂ ((Work.Landing.Tsq c)^[k * n]) := hTsq.iterate (k * n)
    -- chain rule at the fixed point: `(fⁿ)'(y) = λⁿ`
    have hderiv : deriv ((Work.Landing.Tsq c)^[k * n]) y =
        Work.Landing.multiplier2 c k y ^ n := by
      show deriv ((Work.Landing.Tsq c)^[k * n]) y =
        (deriv ((Work.Landing.Tsq c)^[k]) y) ^ n
      rw [Function.iterate_mul]
      exact (HasDerivAt.iterate y (((hTsq.iterate k).differentiableAt).hasDerivAt)
        hgfix n).deriv
    -- the iterate `fⁿ` is the `2 * k * n`-th iterate of `T_c`
    have hfun : (Work.Landing.Tsq c)^[k * n] = (Tantibar c)^[2 * k * n] := by
      rw [Work.LandLeaves.Tsq_eq_iterate_two]
      rw [← Function.iterate_mul]
      rw [Nat.mul_assoc]
    -- so it is bounded by `M` on the boundary circle of the disc `B(y, R)`
    have hsphere : ∀ z ∈ Metric.sphere y R, ‖((Work.Landing.Tsq c)^[k * n]) z‖ ≤ M := by
      intro z hz
      have hzy : dist z y < ε := by
        rw [mem_sphere_iff_norm] at hz
        rw [dist_eq_norm, hz, hRdef]
        linarith
      rw [hfun]
      exact hbound z hzy (2 * k * n)
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := y) (R := R)
      (C := M) (f := (Work.Landing.Tsq c)^[k * n]) hRpos hd.diffContOnCl hsphere
    rw [hderiv, norm_pow] at hcauchy
    exact hcauchy
  -- but `‖λ‖ⁿ → ∞`, a contradiction
  have hmul : 1 < ‖Work.Landing.multiplier2 c k y‖ := hrep.2
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    ((tendsto_pow_atTop_atTop_of_one_lt hmul).eventually_gt_atTop (M / R))
  exact absurd (hkey n) (not_le.mpr (hn n le_rfl))

end Work.LandLeaves
