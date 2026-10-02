/-
# `Work.PARIMPL.ParSplit.parRho_ne_zero`

`parRho S c = R_c (S.m c)` is the value at `S.m c` of the quotient `R_c` of the fixed-point
polynomial `Q_c = F c - id` by `(X - S.m c)^2 - G c` (`G c = (S.E c / 2)^2`).  It is the
function which appears in the normal-form chart (`parS = parU0 / parRho`), so it has to be
shown not to vanish near `c₀`.

The point is that at `c₀` the two split fixed points collide (`S.E c₀ = 0`), so all the
`G c₀ ^ j`, `j ≥ 1`, drop out of the defining sum and

  `parRho S c₀ = phi S c₀ 2 = [w²] Q_{c₀} (z₁ + w)`,

which is (one half of) the second derivative `(F c₀)''(z₁)` of the fixed-point equation: the
`squared factor` follows from `S.fixed_add`/`S.fixed_sub` (`w² | Q_{c₀}(z₁ + w)`), and what
remains is exactly the *simplicity* of the parabolic fixed point, `d.simple`.  Hence
`parRho S c₀ ≠ 0`, and by continuity of `parRho` (`continuousOn_parRho`) it stays nonzero on a
small enough ball around `c₀`, which is the statement to prove.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

open Polynomial

/-! ## Two elementary facts about polynomial coefficients -/

/-- Twice the coefficient of `w²` in `p (z + w)` is the second formal derivative of `p` at `z`.
For `p` the fixed-point polynomial this is `(p'' (z))`. -/
theorem two_mul_coeff_comp_X_add_C (p : Polynomial ℂ) (z : ℂ) :
    2 * ((p.comp (Polynomial.X + Polynomial.C z)).coeff 2)
      = (Polynomial.derivative (Polynomial.derivative p)).eval z := by
  have hc : (p.comp (Polynomial.X + Polynomial.C z)).coeff 2
      = (Polynomial.hasseDeriv 2 p).eval z := by
    rw [← Polynomial.taylor_apply, Polynomial.taylor_coeff]
  have hh : (2 : Polynomial ℂ) * Polynomial.hasseDeriv 2 p
      = Polynomial.derivative (Polynomial.derivative p) := by
    have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) (k := 2)) p
    simpa using h
  rw [hc, ← hh]
  simp

/-- The second analytic derivative of a polynomial function is the second formal derivative
evaluated at the point. -/
theorem iteratedDeriv_two_poly (p : Polynomial ℂ) (z : ℂ) :
    iteratedDeriv 2 (fun y => p.eval y) z
      = (Polynomial.derivative (Polynomial.derivative p)).eval z := by
  have h1 : iteratedDeriv 2 (fun y => p.eval y) = deriv (deriv (fun y => p.eval y)) := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h1]
  have h2 : deriv (fun y => p.eval y) = fun y => (Polynomial.derivative p).eval y := by
    funext y
    exact Polynomial.deriv p
  rw [h2]
  exact Polynomial.deriv (Polynomial.derivative p)

/-! ## `parRho` at the root-parabolic parameter -/

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- `G c₀ = (S.E c₀ / 2)² = 0`: the two split fixed points collide at `c₀`. -/
theorem Gc_c₀ (S : SplitData d) : Gc S c₀ = 0 := by
  simp [Gc, S.E₀]

/-- At `c₀` all the terms with `j ≥ 1` in the defining sum of `psi` drop out. -/
theorem parRho_at_c₀ (S : SplitData d) : parRho S c₀ = phi S c₀ 2 := by
  have h : Gc S c₀ = 0 := Gc_c₀ S
  unfold parRho psi
  rw [h, Finset.sum_eq_single 0]
  · simp
  · intro j _ hne
    rw [zero_pow hne, zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.mpr (by norm_num [wallN])) h0

/-- `phi S c₀ 2` is `[w²] Q_{c₀}(z₁ + w)`, i.e. `(F c₀)''(z₁)/2`, which is nonzero because the
parabolic fixed point is simple (`d.simple`). -/
theorem phi_two_ne_zero (S : SplitData d) : phi S c₀ 2 ≠ 0 := by
  intro hzero
  have hQ : 2 * ((Qpoly c₀).comp (Polynomial.X + Polynomial.C d.z₁)).coeff 2
      = (Polynomial.derivative (Polynomial.derivative (Qpoly c₀))).eval d.z₁ :=
    two_mul_coeff_comp_X_add_C (Qpoly c₀) d.z₁
  have hd : Polynomial.derivative (Polynomial.derivative (Qpoly c₀))
      = Polynomial.derivative (Polynomial.derivative (Fpoly c₀)) := by
    rw [show Qpoly c₀ = Fpoly c₀ - Polynomial.X from rfl]
    simp only [map_sub, Polynomial.derivative_X, Polynomial.derivative_one, sub_zero]
  have hiter : (Polynomial.derivative (Polynomial.derivative (Fpoly c₀))).eval d.z₁
      = iteratedDeriv 2 (fun y => (Fpoly c₀).eval y) d.z₁ :=
    (iteratedDeriv_two_poly (Fpoly c₀) d.z₁).symm
  have hF : (fun y => (Fpoly c₀).eval y) = Work.EL.F c₀ := by
    funext y; exact Fpoly_eval c₀ y
  have key : 2 * phi S c₀ 2 = iteratedDeriv 2 (Work.EL.F c₀) d.z₁ := by
    unfold phi Phi
    rw [S.m₀, hQ, hd, hiter, hF]
  rw [hzero, mul_zero] at key
  exact d.simple key.symm

/-! ## Nonvanishing on a ball -/

theorem parRho_ne_zero {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ',
      Work.PARIMPL.ParSplit.parRho S c ≠ 0 := by
  have h0 : parRho S c₀ ≠ 0 := by
    rw [parRho_at_c₀ S]
    exact phi_two_ne_zero S
  have hcont : ContinuousOn (parRho S) (ball c₀ S.ρ) := continuousOn_parRho S le_rfl
  have hmem : c₀ ∈ ball c₀ S.ρ := Metric.mem_ball_self S.hρ
  have hca : ContinuousAt (parRho S) c₀ :=
    hcont.continuousAt (Metric.isOpen_ball.mem_nhds hmem)
  have hnhds : {c : ℂ | parRho S c ≠ 0} ∈ nhds c₀ :=
    hca.preimage_mem_nhds (isOpen_ne.mem_nhds h0)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨min δ (S.ρ / 2), lt_min hδ (by linarith [S.hρ]),
    le_trans (min_le_right _ _) (by linarith [S.hρ]), ?_⟩
  intro c hc
  exact hδsub (Metric.ball_subset_ball (min_le_left _ _) hc)

end Work.PARIMPL.ParSplit
