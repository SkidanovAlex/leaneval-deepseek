import Mathlib
import Submission.Work.ZeroFreeTables.lam0w.PrincipalDefs
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs

open DirichletCharacter Complex
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.lam0w

/-! ## Analyticity of `L(·,χ)` and of the corrector `princCorr q` on `Re z > 1` -/

/-- `L(·,χ)` is analytic on `{1 < Re z}` (where it is given by its Dirichlet series). -/
lemma analyticAt_LFunction_of_one_lt_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z : ℂ} (hz : 1 < z.re) : AnalyticAt ℂ (DirichletCharacter.LFunction χ) z := by
  refine DifferentiableOn.analyticAt (s := {w : ℂ | 1 < w.re}) (fun w hw => ?_)
    ((isOpen_lt continuous_const continuous_re).mem_nhds hz)
  exact (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl (by
    rintro rfl; simp at hw))).differentiableWithinAt

/-- `princCorr q` is analytic on `Re z > 1`. -/
lemma analyticAt_princCorr {q : ℕ} [NeZero q] {z : ℂ} (hz : 1 < z.re) :
    AnalyticAt ℂ (princCorr q) z := by
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) z :=
    analyticAt_LFunction_of_one_lt_re _ hz
  have hne : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) z ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ hz]
    exact LSeries_ne_zero_of_one_lt_re _ hz
  have hquot : AnalyticAt ℂ (fun w =>
      deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) w
        / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) w) z :=
    (hL.deriv).div hL hne
  have h1 : AnalyticAt ℂ (fun w => -logDeriv
      (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) w) z := by
    have heq : (fun w => -logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) w)
        = fun w => -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) w
            / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) w) := by
      funext w; rw [logDeriv_apply]
    rw [heq]; exact hquot.neg
  have hz1 : z - 1 ≠ 0 := fun h => by
    have h' : z.re = 1 := by
      have := congrArg Complex.re h
      simp at this
      linarith
    linarith
  have h2 : AnalyticAt ℂ (fun w : ℂ => (w - 1)⁻¹) z := by
    have hbase : AnalyticAt ℂ (fun w : ℂ => w - 1) z := by fun_prop
    have hfun : (fun w : ℂ => (w - 1)⁻¹) = (fun w : ℂ => w - 1)⁻¹ := by funext w; rfl
    rw [hfun]
    exact hbase.inv hz1
  unfold princCorr
  exact h1.sub h2

/-! ## The pole derivatives -/

/-- The first derivative of `z ↦ (z-1)⁻¹` (closed form, from `iter_deriv_inv_linear_sub`). -/
lemma iteratedDeriv_one_inv_sub_one (s : ℂ) :
    iteratedDeriv 1 (fun z : ℂ => (z - 1)⁻¹) s = -(((s - 1) ^ 2)⁻¹) := by
  have h := congrFun (iter_deriv_inv_linear_sub 1 (1 : ℂ) 1) s
  simp only [one_mul, one_pow, mul_one] at h
  rw [iteratedDeriv_eq_iterate, h]
  norm_num [zpow_neg]

/-- The second derivative of `z ↦ (z-1)⁻¹`. -/
lemma iteratedDeriv_two_inv_sub_one (s : ℂ) :
    iteratedDeriv 2 (fun z : ℂ => (z - 1)⁻¹) s = 2 * (((s - 1) ^ 3)⁻¹) := by
  have h := congrFun (iter_deriv_inv_linear_sub 2 (1 : ℂ) 1) s
  simp only [one_mul, one_pow, mul_one] at h
  rw [iteratedDeriv_eq_iterate, h]
  norm_num [zpow_neg]

/-- `Re (2 * x) = 2 * Re x`. -/
lemma two_mul_re' (x : ℂ) : (2 * x).re = 2 * x.re := by
  rw [Complex.mul_re]; simp

/-! ## The pole bracket -/

/-- The pole bracket `Re P₃(A/u)` written as the three explicit pole terms. -/
lemma P3_re_arg' (A : ℝ) (u : ℂ) :
    (Work.ZeroFreeTables.P3 ((A : ℂ) * u⁻¹)).re
      = A * (u⁻¹).re + A ^ 2 * ((u ^ 2)⁻¹).re + (2 / 3) * A ^ 3 * ((u ^ 3)⁻¹).re := by
  rw [Work.ZeroFreeTables.P9.P3_re_mul_inv]
  simp only [inv_pow]

/-- **Pole extraction for the principal character.**  For `Re s > 1`,
`Σ(s,χ₀) = Re P₃(α/((s-1)L)) + α·Re H(s) - α²·Re H'(s) + (1/3)α³·Re H''(s)` with
`α = (a+λ₁)/L` and `H = princCorr q`.

Read `Submission/Work/ZeroFreeTables/Rep9/principalRepair.lean`'s
`SigmaP3L_principal_eq_pole_add_corrector` and its helpers for the exact proof pattern (that
module is being edited concurrently, so do NOT import it -- transcribe instead).  The steps are:
`Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs` writes `Σ` in terms of
`Re (logDeriv L)`, `Re (iteratedDeriv 1 (logDeriv L))`, `Re (iteratedDeriv 2 (logDeriv L))`;
then `logDeriv L = -(princCorr q) - (·-1)⁻¹` as functions (definition of `princCorr`), so
`iteratedDeriv 1` and `iteratedDeriv 2` split with `iteratedDeriv_sub`/`iteratedDeriv_neg`
(analyticity from `AnalyticAt.princCorr`, obtained from `analyticAt` of `LFunction` and
`LSeries_ne_zero_of_one_lt_re`); finally
`iteratedDeriv 1 (·-1)⁻¹ = -((s-1)^2)⁻¹`, `iteratedDeriv 2 (·-1)⁻¹ = 2*((s-1)^3)⁻¹`
(from `iter_deriv_inv_linear_sub`), and the three resulting pole terms reassemble into
`Re P3(α/(s-1))` (`Work.ZeroFreeTables.P9.P3_re_mul_inv` in `P9/Defs.lean`). -/
theorem sigP3PoleExtraction (q : ℕ) [NeZero q] {L a lam₁ : ℝ} {s : ℂ} (hs : 1 < s.re) :
    Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      = (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
        + ((a + lam₁) / L) * (Work.ZeroFreeTables.lam0w.princCorr q s).re
        - ((a + lam₁) / L) ^ 2
            * (iteratedDeriv 1 (Work.ZeroFreeTables.lam0w.princCorr q) s).re
        + (1 / 3) * ((a + lam₁) / L) ^ 3
            * (iteratedDeriv 2 (Work.ZeroFreeTables.lam0w.princCorr q) s).re := by
  set H : ℂ → ℂ := princCorr q with hH
  set P : ℂ → ℂ := fun z : ℂ => (z - 1)⁻¹ with hP
  have hsne : s ≠ 1 := fun h => by
    have : s.re = 1 := by simpa using congrArg Complex.re h
    linarith
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
  have hF : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) = -(H + P) := by
    rw [hH, hP]
    funext z
    simp only [Pi.neg_apply, Pi.add_apply, princCorr]
    ring
  have hcd2H : ContDiffAt ℂ 2 H s := (analyticAt_princCorr hs).contDiffAt
  have hcd2P : ContDiffAt ℂ 2 P s := by
    rw [hP]
    have hfun : (fun z : ℂ => (z - 1)⁻¹) = (fun z : ℂ => z - 1)⁻¹ := by funext z; rfl
    rw [hfun]
    exact (contDiffAt_id.sub contDiffAt_const).inv hs1
  have ht0 : (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s).re
      = -((H s).re + (P s).re) := by
    rw [hF, Pi.neg_apply, Pi.add_apply, Complex.neg_re, Complex.add_re]
  have ht1 : (iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s).re
      = -((iteratedDeriv 1 H s).re + (iteratedDeriv 1 P s).re) := by
    have h : iteratedDeriv 1 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s
        = -(iteratedDeriv 1 H s + iteratedDeriv 1 P s) := by
      rw [hF, iteratedDeriv_neg,
        iteratedDeriv_add (hcd2H.of_le (by norm_num)) (hcd2P.of_le (by norm_num))]
    rw [h, Complex.neg_re, Complex.add_re]
  have ht2 : (iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s).re
      = -((iteratedDeriv 2 H s).re + (iteratedDeriv 2 P s).re) := by
    have h : iteratedDeriv 2 (logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q))) s
        = -(iteratedDeriv 2 H s + iteratedDeriv 2 P s) := by
      rw [hF, iteratedDeriv_neg, iteratedDeriv_add hcd2H hcd2P]
    rw [h, Complex.neg_re, Complex.add_re]
  have hP1 : iteratedDeriv 1 P s = -(((s - 1) ^ 2)⁻¹) := by
    rw [hP]; exact iteratedDeriv_one_inv_sub_one s
  have hP2 : iteratedDeriv 2 P s = 2 * (((s - 1) ^ 3)⁻¹) := by
    rw [hP]; exact iteratedDeriv_two_inv_sub_one s
  have hpole : (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
      = ((a + lam₁) / L) * (P s).re - ((a + lam₁) / L) ^ 2 * (iteratedDeriv 1 P s).re
        + (1 / 3) * ((a + lam₁) / L) ^ 3 * (iteratedDeriv 2 P s).re := by
    have harg : (a + lam₁) / ((s - 1) * (L : ℂ))
        = (((a + lam₁) / L : ℝ) : ℂ) * (s - 1)⁻¹ := by
      push_cast
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      ring
    have hPval : P s = (s - 1)⁻¹ := by rw [hP]
    rw [harg, P3_re_arg', hPval, hP1, hP2, two_mul_re', Complex.neg_re]
    ring
  rw [Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs (1 : DirichletCharacter ℂ q) hs a lam₁ L,
    ht0, ht1, ht2, hpole]
  ring_nf

end Work.ZeroFreeTables.lam0w
