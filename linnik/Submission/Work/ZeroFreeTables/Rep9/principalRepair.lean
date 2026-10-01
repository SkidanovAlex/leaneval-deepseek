/-
# ZeroFreeTables/Rep9/principalRepair — the pole-extraction reduction for the principal
character, and the repaired principal bound of HB §9.

## Why the file exists

The requested `Work.ZeroFreeTables.Rep9.principalBound` (kept, unchanged, in
`Rep9/principalBound.lean`) is **false**.  For `q = 1` the left hand side is, by the von
Mangoldt identity `Σ_n Λ(n)(log n)^k n^{-s} = (-1)^k (-ζ'/ζ)^{(k)}(s)`,
`L⁻¹(α Re F(s) - α²L⁻¹ Re F'(s) + (1/3)α³L⁻³Re F''(s))`, `F = -ζ'/ζ`, `α = a + λ₁`: an exact
*cubic* in `α` with cubic coefficient `(1/3)L⁻³Re F''(s) > 0` for `|Im s| = 3`, while the right
hand side's cubic coefficient is `(2/3)Re(((s-1)L)^{-3}) = O(L⁻⁴)`.  So `LHS - RHS → +∞` as
`λ₁ → ∞` at *every* `L` and no `L₀` exists.  (Witness: `a = 1`, `e = 10⁻⁶`, `q = 1`, `L = 10`,
`λ₁ = 99`, `s = 1.1 + 4i`, where `LHS = -4.6487` but `RHS = -6.9553`.)

## The repair

In Heath-Brown's §9 the shift is always bounded (Table 8: `λ₁ ≤ 0.745` with `a = 2`; the side
conditions (9.9)–(9.12) force `λ₁ ≲ a`), whereas the formalized statement assumed only
`0 ≤ λ₁ ≤ M` with a *free, universally quantified* `M` and an error term linear in `α`.  The
faithful repair keeps `|Im s| ≤ 4` (the working window of the contract's zeros `|Im ρ| ≤ 1`, so
§9's points `s = σ + i(γ₁-γ₀)` satisfy `|Im s| ≤ 2`) and bounds the shift,
`∀ M, ∃ L₀(a,M,e), …`; this is the shape of the area's own targets
(`Work.ZeroFreeTables.XY.PrincipalSigmaBound`, `λ₁ ≤ 1/2`, `|Im s| ≤ 5`) and what the workspace's
`P₃`-engines can deliver, since their error terms `(α/L)C₁ + (α²/L²)C₂ + (α³/L³)C₃`, `C_j ≥ 0`,
are `≤ αe` exactly when `α` is bounded relative to `L` (or when `|Im s| = O(1/L)`, the *scaled*
alternative, whose proof needs the Taylor coefficients of `-ζ'/ζ - 1/(s-1)` at `1` with signs).

## Contents

* `zetaCorrector`, `principalCorrector`: `-logDeriv - 1/(z-1)`, the log-derivatives with the pole
  at `1` subtracted (the objects whose size controls every principal-character `P₃` bound);
* `SigmaP3L_principal_eq_pole_add_corrector`: the **exact** reduction
  `Σ(s,χ₀) = Re P₃(α/((s-1)L)) + [P₃-operator applied to the corrector]`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs

open DirichletCharacter Complex Filter
open scoped BigOperators Topology
noncomputable section

namespace Work.ZeroFreeTables.Rep9

/-! ## The correctors -/

/-- The log-derivative of `ζ` with its pole at `1` subtracted:
`zetaCorrector z = -ζ'/ζ(z) - 1/(z-1)`.  This is holomorphic near `1`, with
`zetaCorrector 1 = -γ₀` (`γ₀` the Euler–Mascheroni constant), and it is the exact "error" in the
principal-character `P₃` bound. -/
def zetaCorrector (z : ℂ) : ℂ := -logDeriv riemannZeta z - (z - 1)⁻¹

/-- The log-derivative of the principal character's `L`-function mod `q`, with its pole at `1`
subtracted.  For `Re z > 1` it equals `zetaCorrector z - ∑_{p | q} log p/(p^z - 1)`. -/
def principalCorrector (q : ℕ) [NeZero q] (z : ℂ) : ℂ :=
  -logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) z - (z - 1)⁻¹

/-- `principalCorrector` is `-logDeriv` minus the pole. -/
lemma neg_logDeriv_eq_pole_add_corrector (q : ℕ) [NeZero q] (z : ℂ) :
    -logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) z
      = (z - 1)⁻¹ + principalCorrector q z := by
  rw [principalCorrector]; ring

/-- For `q = 1` the two correctors agree (`L(·,χ₀) = ζ` for the trivial level `1`). -/
lemma principalCorrector_one_eq_zetaCorrector (z : ℂ) : principalCorrector 1 z = zetaCorrector z := by
  have hfun : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta := by
    funext w
    rw [DirichletCharacter.LFunction, ZMod.LFunction_modOne_eq,
      MulChar.one_apply (isUnit_of_subsingleton (0 : ZMod 1)), one_mul]
  rw [principalCorrector, zetaCorrector, hfun]

/-- The function-level form of `principalCorrector_one_eq_zetaCorrector`. -/
lemma principalCorrector_one_eq_zetaCorrector_fun : principalCorrector 1 = zetaCorrector :=
  funext principalCorrector_one_eq_zetaCorrector

/-! ## Analyticity of the corrector on `Re z > 1`

The reduction below differentiates the corrector twice, so we record that it is analytic there. -/

/-- `L(·,χ)` is analytic on `{1 < Re z}` (where it is given by its Dirichlet series). -/
lemma analyticAt_LFunction_of_one_lt_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {z : ℂ} (hz : 1 < z.re) : AnalyticAt ℂ (DirichletCharacter.LFunction χ) z := by
  refine DifferentiableOn.analyticAt (s := {w : ℂ | 1 < w.re}) (fun w hw => ?_)
    ((isOpen_lt continuous_const continuous_re).mem_nhds hz)
  exact (DirichletCharacter.differentiableAt_LFunction χ w (Or.inl (by
    rintro rfl; simp at hw))).differentiableWithinAt

/-- `principalCorrector q` is analytic on `Re z > 1`. -/
lemma analyticAt_principalCorrector {q : ℕ} [NeZero q] {z : ℂ} (hz : 1 < z.re) :
    AnalyticAt ℂ (principalCorrector q) z := by
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
    first
    | fun_prop
    | (have hbase : AnalyticAt ℂ (fun w : ℂ => w - 1) z := by fun_prop
       have hfun : (fun w : ℂ => (w - 1)⁻¹) = (fun w : ℂ => w - 1)⁻¹ := by funext w; rfl
       rw [hfun]
       exact hbase.inv hz1)
  exact h1.sub h2

/-! ## The pole derivatives -/

/-- The first derivative of `z ↦ (z-1)⁻¹` (closed form, from `iter_deriv_inv_linear_sub`). -/
lemma iteratedDeriv_one_inv_sub_one (s : ℂ) :
    iteratedDeriv 1 (fun z : ℂ => (z - 1)⁻¹) s = -(((s - 1) ^ 2)⁻¹) := by
  have h := congrFun (iter_deriv_inv_linear_sub 1 (1 : ℂ) 1) s
  simp only [one_mul, one_pow, mul_one] at h
  rw [iteratedDeriv_eq_iterate, h]
  first
  | norm_num [zpow_neg]
  | (rw [show (-1 : ℤ) - 1 = -((2 : ℕ) : ℤ) by norm_num, zpow_neg]; ring)

/-- The second derivative of `z ↦ (z-1)⁻¹`. -/
lemma iteratedDeriv_two_inv_sub_one (s : ℂ) :
    iteratedDeriv 2 (fun z : ℂ => (z - 1)⁻¹) s = 2 * (((s - 1) ^ 3)⁻¹) := by
  have h := congrFun (iter_deriv_inv_linear_sub 2 (1 : ℂ) 1) s
  simp only [one_mul, one_pow, mul_one] at h
  rw [iteratedDeriv_eq_iterate, h]
  first
  | norm_num [zpow_neg]
  | (rw [show (-1 : ℤ) - 2 = -((3 : ℕ) : ℤ) by norm_num, zpow_neg]; ring)

/-- `Re (2 * x) = 2 * Re x`. -/
private lemma two_mul_re (x : ℂ) : (2 * x).re = 2 * x.re := by
  rw [Complex.mul_re]; simp

/-! ## The reduction -/

/-- The pole bracket `Re P₃(A/u)` written as the three explicit pole terms. -/
lemma P3_re_arg (A : ℝ) (u : ℂ) :
    (P3 ((A : ℂ) * u⁻¹)).re
      = A * (u⁻¹).re + A ^ 2 * ((u ^ 2)⁻¹).re + (2 / 3) * A ^ 3 * ((u ^ 3)⁻¹).re := by
  rw [Work.ZeroFreeTables.P9.P3_re_mul_inv]
  simp only [inv_pow]

/-- **The pole-extraction reduction for the principal character.**
For `Re s > 1`,
`Σ(s, χ₀) = Re P₃(α/((s-1)L)) + (α/L)·Re H(s) - (α/L)²·Re H'(s) + (1/3)(α/L)³·Re H''(s)`,
where `H = principalCorrector q = -L'/L(·,χ₀) - 1/(· - 1)` and `α = a + λ₁`.
Consequently every upper bound for `Σ(s,χ₀)` of the shape "pole term + α·e" is *exactly* a bound
for the `P₃`-operator applied to the corrector `H`. -/
theorem SigmaP3L_principal_eq_pole_add_corrector (q : ℕ) [NeZero q] {L a lam₁ : ℝ} {s : ℂ}
    (hs : 1 < s.re) :
    SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      = (P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
        + ((a + lam₁) / L) * (principalCorrector q s).re
        - ((a + lam₁) / L) ^ 2 * (iteratedDeriv 1 (principalCorrector q) s).re
        + (1 / 3) * ((a + lam₁) / L) ^ 3 * (iteratedDeriv 2 (principalCorrector q) s).re := by
  set H : ℂ → ℂ := principalCorrector q with hH
  set P : ℂ → ℂ := fun z : ℂ => (z - 1)⁻¹ with hP
  have hsne : s ≠ 1 := fun h => by
    have : s.re = 1 := by simpa using congrArg Complex.re h
    linarith
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
  have hF : logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) = -(H + P) := by
    rw [hH, hP]
    funext z
    simp only [Pi.neg_apply, Pi.add_apply, principalCorrector]
    ring
  have hcd2H : ContDiffAt ℂ 2 H s := (analyticAt_principalCorrector hs).contDiffAt
  have hcd2P : ContDiffAt ℂ 2 P s := by
    rw [hP]
    first
    | fun_prop
    | (have hfun : (fun z : ℂ => (z - 1)⁻¹) = (fun z : ℂ => z - 1)⁻¹ := by funext z; rfl
       rw [hfun]
       exact (contDiffAt_id.sub contDiffAt_const).inv hs1)
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
  have hpole : (P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
      = ((a + lam₁) / L) * (P s).re - ((a + lam₁) / L) ^ 2 * (iteratedDeriv 1 P s).re
        + (1 / 3) * ((a + lam₁) / L) ^ 3 * (iteratedDeriv 2 P s).re := by
    have harg : (a + lam₁) / ((s - 1) * (L : ℂ)) = (((a + lam₁) / L : ℝ) : ℂ) * (s - 1)⁻¹ := by
      push_cast
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
      ring
    have hPval : P s = (s - 1)⁻¹ := by rw [hP]
    rw [harg, P3_re_arg, hPval, hP1, hP2, two_mul_re, Complex.neg_re]
    ring
  rw [Work.ZeroFreeTables.P9.SigmaP3L_eq_logDeriv_derivs (1 : DirichletCharacter ℂ q) hs a lam₁ L,
    ht0, ht1, ht2, hpole]
  ring_nf


/-! ## The amended principal bound of HB §9 (the repaired `principalBoundM`)

The original `Rep9.principalBound` is false because `λ₁` was only assumed `≤ M` with `M` a *free*,
universally quantified variable, which makes the conclusion uniform in the shift; the correct form
(as in `Rep9/principalBoundM.lean`) has `M` as a parameter, so that `L₀` may depend on it.  That
statement is *derived* here from the pole-extraction reduction
`SigmaP3L_principal_eq_pole_add_corrector` plus three analytic inputs:

* `hZ`: the size of the `ζ`-corrector `-ζ'/ζ - 1/(z-1)` and of its two derivatives on the strip
  `1 < Re s ≤ 2, |Im s| ≤ 5` (`P9/zetaCorrector_three_bounds`);
* `Rep9.principalSigmaDiff`: the mod-`q` correction, i.e. the contribution of the primes dividing
  `q`: `C·(1+√(log q))·(1+α/L+(α/L)²)·α/L`;
* `Rep9.shiftAbsorb`: the elementary absorption of these corrections into `α·e` when the shift
  `α = a+λ₁` is bounded by `a + M` and `L` is large.

The proof is then a short `calc`: reduction at `q = 1`, add the mod-`q` correction, bound the
corrector by `(α/L)C₁(1+α/L+(α/L)²)` and absorb. -/
theorem principalBoundM_of_bounds {a e M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (he : 0 < e)
    (hZ : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ 5 →
      |(zetaCorrector s).re| ≤ C ∧ |(iteratedDeriv 1 zetaCorrector s).re| ≤ C
        ∧ |(iteratedDeriv 2 zetaCorrector s).re| ≤ C)
    (hD : ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] {L lam₁ : ℝ}, 0 < L → Real.log (q:ℝ) ≤ L →
      0 ≤ lam₁ → lam₁ ≤ M → ∀ s : ℂ, s.re = 1 + a/L → |s.im| ≤ 5 →
        |SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁ - SigmaP3L 1 L 1 s a lam₁|
          ≤ ((a + lam₁) / L) * C * (1 + Real.sqrt (Real.log q))
              * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2))
    (hS : ∀ C C' : ℝ, 0 < C → 0 < C' → ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ {L : ℝ}, L₀ ≤ L →
      ∀ {x : ℝ}, 0 ≤ x → x ≤ a + M →
        (x / L) * C * (1 + x / L + (x / L) ^ 2)
          + (x / L) * C' * (1 + Real.sqrt L) * (1 + x / L + (x / L) ^ 2) ≤ x * e) :
    ∃ L₀ : ℝ, ∀ {q : ℕ} [NeZero q] {L lam₁ : ℝ}, L₀ ≤ L → Real.log (q:ℝ) ≤ L →
      0 ≤ lam₁ → lam₁ ≤ M →
      ∀ s : ℂ, s.re = 1 + a/L → |s.im| ≤ 4 →
        SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
          ≤ (P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re + (a + lam₁) * e := by
  obtain ⟨C₁, hC₁pos, hZ⟩ := hZ
  obtain ⟨C₂, hC₂pos, hD⟩ := hD
  obtain ⟨L₀, _hL₀one, hL₀⟩ := hS C₁ C₂ hC₁pos hC₂pos
  refine ⟨max (max L₀ a) 1, ?_⟩
  intro q _inst L lam₁ hL hlogq hlam0 hlamM s hsre hsim
  have hL₀le : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have haL : a ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have h1L : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one h1L
  have hs1 : 1 < s.re := by
    rw [hsre]; exact lt_add_of_pos_right 1 (div_pos ha hLpos)
  have hs2 : s.re ≤ 2 := by
    rw [hsre]
    have hle : a / L ≤ 1 := by rw [div_le_one hLpos]; exact haL
    linarith
  have hsim5 : |s.im| ≤ 5 := le_trans hsim (by norm_num)
  have hαnn : 0 ≤ a + lam₁ := by linarith
  have hαM : a + lam₁ ≤ a + M := by linarith
  have hy : 0 ≤ (a + lam₁) / L := div_nonneg hαnn hLpos.le
  -- ## the reduction at `q = 1`
  have hred : SigmaP3L 1 L 1 s a lam₁
      = (P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
        + ((a + lam₁) / L) * (zetaCorrector s).re
        - ((a + lam₁) / L) ^ 2 * (iteratedDeriv 1 zetaCorrector s).re
        + (1 / 3) * ((a + lam₁) / L) ^ 3 * (iteratedDeriv 2 zetaCorrector s).re := by
    rw [SigmaP3L_principal_eq_pole_add_corrector (q := 1) (L := L) (a := a) (lam₁ := lam₁)
      (s := s) hs1, principalCorrector_one_eq_zetaCorrector_fun]
  -- ## the bounds for the three corrector terms
  obtain ⟨hZ0, hZ1, hZ2⟩ := hZ s hs1 hs2 hsim5
  have hcorr : ((a + lam₁) / L) * (zetaCorrector s).re
      - ((a + lam₁) / L) ^ 2 * (iteratedDeriv 1 zetaCorrector s).re
      + (1 / 3) * ((a + lam₁) / L) ^ 3 * (iteratedDeriv 2 zetaCorrector s).re
      ≤ ((a + lam₁) / L) * C₁ * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
    have hb0 : (zetaCorrector s).re ≤ C₁ := le_trans (le_abs_self _) hZ0
    have hb1 : -(iteratedDeriv 1 zetaCorrector s).re ≤ C₁ := le_trans (neg_le_abs _) hZ1
    have hb2 : (iteratedDeriv 2 zetaCorrector s).re ≤ C₁ := le_trans (le_abs_self _) hZ2
    have h2 : 0 ≤ ((a + lam₁) / L) ^ 2 := sq_nonneg _
    have h3 : 0 ≤ ((a + lam₁) / L) ^ 3 := pow_nonneg hy 3
    have e1 : ((a + lam₁) / L) * (zetaCorrector s).re ≤ ((a + lam₁) / L) * C₁ :=
      mul_le_mul_of_nonneg_left hb0 hy
    have e2 : ((a + lam₁) / L) ^ 2 * (-(iteratedDeriv 1 zetaCorrector s).re)
        ≤ ((a + lam₁) / L) ^ 2 * C₁ := mul_le_mul_of_nonneg_left hb1 h2
    have e3 : ((a + lam₁) / L) ^ 3 * (iteratedDeriv 2 zetaCorrector s).re
        ≤ ((a + lam₁) / L) ^ 3 * C₁ := mul_le_mul_of_nonneg_left hb2 h3
    nlinarith [e1, e2, e3, hy, h2, h3, hC₁pos]
  -- ## the mod-`q` correction
  have hdiff : SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁ - SigmaP3L 1 L 1 s a lam₁
      ≤ ((a + lam₁) / L) * C₂ * (1 + Real.sqrt L)
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
    have h := hD (q := q) hLpos hlogq hlam0 hlamM s hsre hsim5
    have hsq : Real.sqrt (Real.log (q:ℝ)) ≤ Real.sqrt L := Real.sqrt_le_sqrt hlogq
    have hfac : 0 ≤ ((a + lam₁) / L) * C₂ := mul_nonneg hy hC₂pos.le
    have hfac2 : 0 ≤ 1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2 := by positivity
    have hstep : ((a + lam₁) / L) * C₂ * (1 + Real.sqrt (Real.log (q:ℝ)))
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2)
        ≤ ((a + lam₁) / L) * C₂ * (1 + Real.sqrt L)
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
      have h1 : 1 + Real.sqrt (Real.log (q:ℝ)) ≤ 1 + Real.sqrt L := by linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hfac) hfac2
    have habs := le_abs_self (SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      - SigmaP3L 1 L 1 s a lam₁)
    linarith [habs, h, hstep]
  -- ## absorption
  have hkey := hL₀ hL₀le (x := a + lam₁) hαnn hαM
  calc SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      ≤ SigmaP3L 1 L 1 s a lam₁
        + ((a + lam₁) / L) * C₂ * (1 + Real.sqrt L)
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by linarith [hdiff]
    _ = (P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
        + (((a + lam₁) / L) * (zetaCorrector s).re
          - ((a + lam₁) / L) ^ 2 * (iteratedDeriv 1 zetaCorrector s).re
          + (1 / 3) * ((a + lam₁) / L) ^ 3 * (iteratedDeriv 2 zetaCorrector s).re)
        + ((a + lam₁) / L) * C₂ * (1 + Real.sqrt L)
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
      rw [hred]
      ring
    _ ≤ (P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re
        + ((a + lam₁) / L) * C₁ * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2)
        + ((a + lam₁) / L) * C₂ * (1 + Real.sqrt L)
          * (1 + (a + lam₁) / L + ((a + lam₁) / L) ^ 2) := by
      linarith [hcorr]
    _ ≤ (P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re + (a + lam₁) * e := by
      linarith [hkey]


end Work.ZeroFreeTables.Rep9
