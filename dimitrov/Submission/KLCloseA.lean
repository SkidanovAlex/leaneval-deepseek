import Mathlib
import Submission.Core.FaAnalytic
import Submission.Core.F1Norm
import Submission.Core.FaPolar
import Submission.Core.FullPeriod
import Submission.Core.LogMean

/-!
# KL-assembly A: weight maximum, margin, max modulus (R6), closed-disk bounds

(KL proof, DESIGN NOTE 5 D0/D1/R6 + assembly step (a)/(e).)  Work in the
angle parametrization: `z_j := E(θ_j)` on the unit circle, weights
`p_j ≥ 0`, `Σ p_j = n ≥ 1`, and Fedja's function

    faE n a θ p σ := fa n a (fun j => E (θ j)) p (E σ)
                  = a · ∏_j (1 + E(σ−θ_j))^{p_j}

with the KL weight at the circle point of angle `σ`:

    weightAngle n θ p σ := ∏_j ‖E σ − E(θ_j)‖^{p_j}.

PROVE the theorems below (add helpers as needed; complete every proof;
no incomplete proofs may remain; `lake build Submission.KLCloseA`).

Mathematical content (steps D0/D1/R6 of the KL proof):
  * `weightAngle` is `2π`-periodic and continuous (with `p_j ≥ 0`; note
    `x ↦ x^p` for real `p ≥ 0` is continuous on `[0,∞)`, and `0^0 = 1` in
    the conventions where needed — avoid `0 ^ 0` issues by `by_cases` or
    use `Real.continuousAt_rpow_const_of_pos`-type facts; `‖Eσ−Eθ_j‖` is a
    nonnegative real, continuous in `σ`, zero only at `σ ≡ θ_j (2π)`).
  * `weightAngle_max`: since `weightAngle` is continuous and `2π`-periodic,
    its maximum on ℝ is attained (maximize over `[0, 2π]` with
    `isCompact_Icc.exists_isMaxOn`-style, extend by periodicity).
  * Pointwise circle-norm bound `faE_bound_of_weight_bound`:
    `‖faE n a θ p σ‖ ≤ a · weightAngle n θ p (σ+π)` for EVERY `σ`
    (0 ≤ a).  Proof: at a jump-free `σ` (all factors nonzero) use the F1
    norm identity (`fa_norm_on_circle` with `z j := E (θ j)`, `w := E σ`,
    plus `‖Eσ + Eθ_j‖ = ‖1 + E(σ−θ_j)‖` via `E_add`); at a jump point
    `σ ≡ θ_j + π (mod 2π)` for a `j` with `p_j ≠ 0` (so `p_j > 0` since
    `0 ≤ p_j`), `faE n a θ p σ = 0` (the `j`-factor is `0^{p_j} = 0`),
    and the right-hand side is also `0` (its `j`-factor
    `‖E(σ+π)−E(θ_j)‖^{p_j} = 0`).  For `σ` that is a "zero-exponent jump"
    (only `j` with `p_j = 0` have `σ ≡ θ_j + π`), no factor vanishes, so it
    is jump-free for our purposes.  Handle with `by_cases h : ∃ j, p j ≠ 0
    ∧ E σ = -E (θ j)` and a direct check in each case.
  * From `weightAngle ≤ M` everywhere (e.g. `M` the max), get the uniform
    margin `‖faE n a θ p σ‖ ≤ a·M` for all `σ`.
  * Continuity/max-modulus on the closed unit disk for
    `w ↦ fa n a (fun j => E (θ j)) p w`:
    - `fa_cont_closedBall`: continuous on `closedBall 0 1`.  Each factor
      `w ↦ (1 + w·conj(E θ_j))^{p_j}` is continuous on the closed disk:
      for `w ≠ -E(θ_j)` (factor base ≠ 0, base in slitPlane) by
      `ContinuousAt.cpow_const`/`continuousAt_cpow_const`; at
      `w = -E(θ_j)` the base is `0`, and `x ↦ x^p` is continuous at `0`
      for `0 < p` (`continuousAt_cpow_zero_of_re_pos`), and constantly `1`
      for `p = 0`.  Products and the scalar `a` preserve continuity.
    - `fa_bound_closedBall` (max modulus, R6): if
      `∀ σ, ‖faE n a θ p σ‖ ≤ c` then `∀ z, ‖z‖ ≤ 1 →
      ‖fa n a (fun j => E (θ j)) p z‖ ≤ c`.  Use
      `norm_le_of_forall_mem_frontier_norm_le` (AbsMax.lean) with
      `U := ball 0 1` (`IsBounded` via `Metric.isBounded_ball`), the
      `DiffContOnCl` from `fa_differentiableOn` (FaAnalytic) plus
      `fa_cont_closedBall`, and the frontier bound: every `z` with
      `‖z‖ = 1` equals `E σ` for some `σ` (prove `exists_E_eq_of_norm_one`
      locally via `Circle.exp_arg`-style or `Complex.arg`), then
      `‖fa n a (fun j => E (θ j)) p z‖ = ‖faE n a θ p σ‖ ≤ c`.
    - `fa_analytic_ball`: `AnalyticOn ℂ (fa n a (fun j => E (θ j)) p)
      (ball 0 1)` from `fa_differentiableOn` +
      `DifferentiableOn.analyticOn` (`IsOpen (ball 0 1)`).
  * `two_sub_fa_lower_bound_closedBall`: if `‖fa n a z0 p z‖ ≤ c` on the
    closed disk with `c < 2`, then `2 - c ≤ ‖2 - fa n a z0 p z‖` there
    (triangle inequality: `2 ≤ ‖2 - fa z‖ + ‖fa z‖`), in particular
    `0 < 2 - c ≤ ‖h z‖` for `h z := 2 - fa n a z0 p z`; used to feed
    `LogMean.boundary_log_nonneg_of_inner_log_neg` (R5).

Hints: `E` from `Submission.Core.FullPeriod`; `faE`/`faE_eq`/`faE_polar`
from `FaPolar`; `fa_norm_on_circle`/`norm_one_add_mul_conj` from `F1Norm`;
`fa_differentiableOn` from `FaAnalytic`.  Conventions: `0 ^ (p:ℂ) = 0` for
`0 < p`, `0 ^ (0:ℂ) = 1`; `Real.rpow` at `0`: `0 ^ p = 0` for `p > 0`,
`0 ^ 0 = 1`.  Periodicity: `E (σ + 2π) = E σ`.  `norm_neg`,
`E_add_pi : E (σ + π) = -E σ` (prove locally).  Everything real/ℂ; open
`Complex`, `MeasureTheory` as needed.
-/

noncomputable section

open scoped Real Complex
open Complex

namespace Submission.KLMain

open Submission.Core

/-! ## Local plumbing: `E` periodicity and half-period -/

/-- `E` is `2π`-periodic. -/
lemma E_two_pi (t : ℝ) : E (t + 2 * Real.pi) = E t := by
  calc
    E (t + 2 * Real.pi) = E t * E (2 * Real.pi) := by rw [E_add]
    _ = E t * 1 := by
        congr 1
        dsimp [E]
        have h : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
          push_cast
          ring
        rw [h]
        rw [Complex.exp_two_pi_mul_I]
    _ = E t := by ring

/-- `E (t + π) = -E t`. -/
lemma E_add_pi (t : ℝ) : E (t + Real.pi) = -E t := by
  calc
    E (t + Real.pi) = E t * E Real.pi := by rw [E_add]
    _ = E t * (-1) := by
        congr 1
        dsimp [E]
        rw [Complex.exp_pi_mul_I]
    _ = -E t := by ring

/-- The modulus of a real cast into `ℂ` is its absolute value. -/
lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- The KL weight at the circle point of angle `σ` (points `E(θ_j)`,
weights `p_j`). -/
noncomputable def weightAngle (n : ℕ) (θ : Fin n → ℝ) (p : Fin n → ℝ) (σ : ℝ) : ℝ :=
  ∏ j : Fin n, ‖E σ - E (θ j)‖ ^ p j

/-- `weightAngle` is `2π`-periodic in the circle parameter. -/
lemma weightAngle_periodic (n : ℕ) (θ : Fin n → ℝ) (p : Fin n → ℝ) (σ : ℝ) :
    weightAngle n θ p (σ + 2 * Real.pi) = weightAngle n θ p σ := by
  unfold weightAngle
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  rw [E_two_pi]

/-- `weightAngle` is continuous in the circle parameter (for `p_j ≥ 0`). -/
theorem weightAngle_continuous (n : ℕ) (θ : Fin n → ℝ) (p : Fin n → ℝ)
    (hp : ∀ j : Fin n, 0 ≤ p j) :
    Continuous (fun σ : ℝ => weightAngle n θ p σ) := by
  unfold weightAngle
  have hE : Continuous (fun t : ℝ => E t) := by
    dsimp [E]
    exact Complex.continuous_exp.comp (continuous_ofReal.mul continuous_const)
  have hfac : ∀ j : Fin n, Continuous (fun σ : ℝ => ‖E σ - E (θ j)‖) := by
    intro j
    exact Continuous.norm (hE.sub continuous_const)
  exact continuous_finset_prod (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => fun σ : ℝ => ‖E σ - E (θ j)‖ ^ p j) (by
      intro j hj
      exact Continuous.rpow_const (hfac j) (fun σ => Or.inr (hp j)))

/-- The maximum of `weightAngle` over ℝ is attained (for `p_j ≥ 0`). -/
theorem weightAngle_max (n : ℕ) (θ : Fin n → ℝ) (p : Fin n → ℝ)
    (hp : ∀ j : Fin n, 0 ≤ p j) :
    ∃ σ₀ : ℝ, ∀ σ : ℝ, weightAngle n θ p σ ≤ weightAngle n θ p σ₀ := by
  let f : ℝ → ℝ := fun σ => weightAngle n θ p σ
  let T : ℝ := 2 * Real.pi
  have hper : Function.Periodic f T := by
    intro σ
    dsimp [f, T]
    exact weightAngle_periodic n θ p σ
  have hTpos : 0 < T := by
    dsimp [T]
    positivity
  have hfcont : Continuous f := by
    dsimp [f]
    exact weightAngle_continuous n θ p hp
  obtain ⟨σ₀, _hσ₀in, hmax⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMaxOn
      ⟨0, by dsimp [T]; exact ⟨le_rfl, by positivity⟩⟩ hfcont.continuousOn
  refine ⟨σ₀, ?_⟩
  intro σ
  let n' : ℤ := toIcoDiv hTpos 0 σ
  let σ' : ℝ := toIcoMod hTpos 0 σ
  have hσ'Ico : σ' ∈ Set.Ico (0 : ℝ) T := toIcoMod_mem_Ico' hTpos σ
  have hσ'Icc : σ' ∈ Set.Icc (0 : ℝ) T := ⟨hσ'Ico.1, le_of_lt hσ'Ico.2⟩
  have hle : f σ' ≤ f σ₀ := hmax hσ'Icc
  have hEq : f σ' = f σ := by
    have hh : f σ' = f (σ - n' • T) := by rfl
    rw [hh]
    exact hper.sub_zsmul_eq n'
  have hfinal : f σ ≤ f σ₀ := by
    calc
      f σ = f σ' := hEq.symm
      _ ≤ f σ₀ := hle
  simpa [f] using hfinal

/-- For circle `z` and `w` with `‖z‖ = 1`, `‖w‖ ≤ 1`:
the factor base `1 + w · conj z` has nonnegative real part. -/
lemma re_of_one_add_mul_conj_nonneg {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ ≤ 1) :
    0 ≤ (1 + w * starRingEnd ℂ z).re := by
  have hnorm : ‖w * starRingEnd ℂ z‖ ≤ 1 := by
    calc
      ‖w * starRingEnd ℂ z‖ = ‖w‖ * ‖starRingEnd ℂ z‖ := by rw [norm_mul]
      _ = ‖w‖ * ‖z‖ := by rw [Complex.norm_conj]
      _ = ‖w‖ := by rw [hz, mul_one]
      _ ≤ 1 := hw
  have hre : -1 ≤ (w * starRingEnd ℂ z).re := by
    have habs : |(w * starRingEnd ℂ z).re| ≤ ‖w * starRingEnd ℂ z‖ :=
      Complex.abs_re_le_norm _
    have hle : |(w * starRingEnd ℂ z).re| ≤ 1 := le_trans habs hnorm
    exact (abs_le.mp hle).1
  have hu_re : (w * starRingEnd ℂ z).re = w.re * z.re + w.im * z.im := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hre' : -1 ≤ w.re * z.re + w.im * z.im := by
    simpa [hu_re] using hre
  have hreal : (1 + w * starRingEnd ℂ z).re = 1 + (w.re * z.re + w.im * z.im) := by
    rw [Complex.add_re]
    rw [hu_re]
    norm_num
  rw [hreal]
  linarith

/-- Each factor `w ↦ (1 + w·conj z)^p` is continuous on the closed unit disk
for circle `z` (`‖z‖ = 1`) and `p ≥ 0`. -/
private lemma factor_continuousOn_closedBall (z : ℂ) (hz : ‖z‖ = 1) (p : ℝ) (hp : 0 ≤ p) :
    ContinuousOn (fun w : ℂ => cPow (1 + w * starRingEnd ℂ z) p)
      (Metric.closedBall (0 : ℂ) 1) := by
  intro w hw
  apply ContinuousAt.continuousWithinAt
  have hwle : ‖w‖ ≤ 1 := by
    have hd : dist w (0 : ℂ) ≤ 1 := (Metric.mem_closedBall.mp hw)
    simpa [dist_eq_norm] using hd
  by_cases hp0 : p = 0
  · have hgconst : (fun u : ℂ => cPow (1 + u * starRingEnd ℂ z) p) = fun _ : ℂ => (1 : ℂ) := by
      funext u
      dsimp [cPow]
      simp [hp0]
    rw [hgconst]
    exact continuousAt_const
  · have hppos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    -- the base has nonnegative real part on the closed disk, and
    -- `x ↦ x ^ p` is continuous at every point of the closed right
    -- half-plane for `p > 0` (including at `x = 0`).
    have hpow : ContinuousAt (fun x : ℂ => x ^ (p : ℂ)) (1 + w * starRingEnd ℂ z) := by
      exact Complex.continuousAt_cpow_const_of_re_pos (z := (1 + w * starRingEnd ℂ z)) (w := (p : ℂ))
        (Or.inl (re_of_one_add_mul_conj_nonneg hz hwle)) (by simpa using hppos)
    have hbcont : ContinuousAt (fun u : ℂ => 1 + u * starRingEnd ℂ z) w := by fun_prop
    simpa [cPow, Function.comp_def] using
      (hpow.comp (f := fun u : ℂ => 1 + u * starRingEnd ℂ z) (x := w) hbcont)

/-- Pointwise identity on the circle: `‖faE n a θ p σ‖ =
`a · weightAngle n θ p (σ + π)` (for `0 ≤ a`; true at every `σ`,
including jumps). -/
lemma faE_norm_weightAngle (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ)
    (p : Fin n → ℝ) (σ : ℝ) :
    ‖faE n a θ p σ‖ = a * weightAngle n θ p (σ + Real.pi) := by
  have hfac : ∀ j : Fin n, ‖1 + E (σ - θ j)‖ = ‖E (σ + Real.pi) - E (θ j)‖ := by
    intro j
    calc
      ‖(1 : ℂ) + E (σ - θ j)‖ = ‖E σ + E (θ j)‖ := (norm_E_add_E σ (θ j)).symm
      _ = ‖-E σ - E (θ j)‖ := by
          rw [← norm_neg (E σ + E (θ j))]
          congr 1
          ring
      _ = ‖E (σ + Real.pi) - E (θ j)‖ := by
          congr 1
          rw [← E_add_pi (t := σ)]
  calc
    ‖faE n a θ p σ‖
        = ‖(a : ℂ) * ∏ j : Fin n, cPow (1 + E (σ - θ j)) (p j)‖ := by rw [faE_eq]
    _ = ‖(a : ℂ)‖ * ‖∏ j : Fin n, cPow (1 + E (σ - θ j)) (p j)‖ := by rw [norm_mul]
    _ = a * ‖∏ j : Fin n, cPow (1 + E (σ - θ j)) (p j)‖ := by
        rw [norm_ofReal_complex, abs_of_nonneg ha]
    _ = a * ∏ j : Fin n, ‖cPow (1 + E (σ - θ j)) (p j)‖ := by rw [norm_prod]
    _ = a * ∏ j : Fin n, ‖1 + E (σ - θ j)‖ ^ p j := by
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        exact norm_cPow (1 + E (σ - θ j)) (p j)
    _ = a * ∏ j : Fin n, ‖E (σ + Real.pi) - E (θ j)‖ ^ p j := by
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        congr 1
        exact hfac j
    _ = a * weightAngle n θ p (σ + Real.pi) := by rfl

/-- **Circle norm bound.**  For `0 ≤ a`, `‖faE n a θ p σ‖ ≤
a · weightAngle n θ p (σ+π)` for every `σ` (pointwise, including jumps). -/
theorem faE_bound_of_weightAngle (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ)
    (p : Fin n → ℝ) (hp : ∀ j : Fin n, 0 ≤ p j) (σ : ℝ) :
    ‖faE n a θ p σ‖ ≤ a * weightAngle n θ p (σ + Real.pi) := by
  rw [faE_norm_weightAngle n a ha θ p σ]

/-- **Uniform margin.**  If `weightAngle n θ p σ ≤ M` for all `σ`, then
`‖faE n a θ p σ‖ ≤ a * M` for all `σ`. -/
theorem faE_margin (n : ℕ) (a M : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ) (p : Fin n → ℝ)
    (hp : ∀ j : Fin n, 0 ≤ p j) (hM : ∀ σ : ℝ, weightAngle n θ p σ ≤ M) (σ : ℝ) :
    ‖faE n a θ p σ‖ ≤ a * M := by
  calc
    ‖faE n a θ p σ‖ ≤ a * weightAngle n θ p (σ + Real.pi) :=
      faE_bound_of_weightAngle n a ha θ p hp σ
    _ ≤ a * M := mul_le_mul_of_nonneg_left (hM (σ + Real.pi)) ha

/-- Every unit-modulus complex number is `E σ` for some real `σ`. -/
lemma exists_E_eq_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) : ∃ σ : ℝ, E σ = w := by
  let z : Circle := ⟨w, by simpa [Submonoid.unitSphere] using hw⟩
  refine ⟨z.val.arg, ?_⟩
  have hz : Circle.exp z.val.arg = z := Circle.exp_arg z
  have hz2 : (Circle.exp z.val.arg : ℂ) = w := by
    simpa [z] using congrArg Subtype.val hz
  rw [Circle.coe_exp] at hz2
  simpa [E] using hz2

/-- `fa` (with circle points `E (θ j)`) is analytic on the open unit disk. -/
theorem fa_analytic_ball (n : ℕ) (a : ℝ) (θ : Fin n → ℝ) (p : Fin n → ℝ) :
    AnalyticOn ℂ (fun w : ℂ => fa n a (fun j : Fin n => E (θ j)) p w)
      (Metric.ball (0 : ℂ) 1) := by
  exact (fa_differentiableOn n a (fun j : Fin n => E (θ j)) p (by
    intro j; exact (norm_E (θ j)).le)).analyticOn Metric.isOpen_ball

/-- `fa` (with circle points `E (θ j)`) is continuous on the closed unit
disk (for `0 ≤ a`, `p_j ≥ 0`). -/
theorem fa_cont_closedBall (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ)
    (p : Fin n → ℝ) (hp : ∀ j : Fin n, 0 ≤ p j) :
    ContinuousOn (fun w : ℂ => fa n a (fun j : Fin n => E (θ j)) p w)
      (Metric.closedBall (0 : ℂ) 1) := by
  change ContinuousOn (fun w : ℂ =>
      (a : ℂ) * ∏ j : Fin n, cPow (1 + w * starRingEnd ℂ (E (θ j))) (p j))
      (Metric.closedBall (0 : ℂ) 1)
  have hf : ∀ j : Fin n,
      ContinuousOn (fun w : ℂ => cPow (1 + w * starRingEnd ℂ (E (θ j))) (p j))
        (Metric.closedBall (0 : ℂ) 1) := by
    intro j
    exact factor_continuousOn_closedBall (E (θ j)) (norm_E (θ j)) (p j) (hp j)
  have hprod : ContinuousOn (fun w : ℂ =>
      ∏ j : Fin n, cPow (1 + w * starRingEnd ℂ (E (θ j))) (p j))
      (Metric.closedBall (0 : ℂ) 1) := by
    simpa using (continuousOn_finsetProd (s := (Finset.univ : Finset (Fin n)))
      (t := Metric.closedBall (0 : ℂ) 1)
      (f := fun j w => cPow (1 + w * starRingEnd ℂ (E (θ j))) (p j)) (by
        intro j hj
        exact hf j))
  exact ContinuousOn.mul (continuousOn_const (s := Metric.closedBall (0 : ℂ) 1)) hprod

/-- **Max modulus (R6).**  If `‖faE n a θ p σ‖ ≤ c` for all circle angles
`σ`, then `‖fa n a (fun j => E (θ j)) p z‖ ≤ c` for all `‖z‖ ≤ 1`. -/
theorem fa_bound_closedBall (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ)
    (p : Fin n → ℝ) (hp : ∀ j : Fin n, 0 ≤ p j) {c : ℝ}
    (hcircle : ∀ σ : ℝ, ‖faE n a θ p σ‖ ≤ c) :
    ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖fa n a (fun j : Fin n => E (θ j)) p z‖ ≤ c := by
  intro z hz
  let F : ℂ → ℂ := fun w => fa n a (fun j : Fin n => E (θ j)) p w
  have hdiff : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1) := by
    dsimp [F]
    exact fa_differentiableOn n a (fun j : Fin n => E (θ j)) p (by
      intro j; exact (norm_E (θ j)).le)
  have hcontCl : ContinuousOn F (closure (Metric.ball (0 : ℂ) 1)) := by
    rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    dsimp [F]
    exact fa_cont_closedBall n a ha θ p hp
  have hd : DiffContOnCl ℂ F (Metric.ball (0 : ℂ) 1) := ⟨hdiff, hcontCl⟩
  have hC : ∀ w ∈ frontier (Metric.ball (0 : ℂ) 1), ‖F w‖ ≤ c := by
    intro w hw
    rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hw
    have hw1 : ‖w‖ = 1 := by simpa [dist_eq_norm] using hw
    rcases exists_E_eq_of_norm_one hw1 with ⟨σ, hσ⟩
    have hEq : F w = faE n a θ p σ := by
      dsimp [F, faE]
      rw [hσ]
    rw [hEq]
    exact hcircle σ
  have hzcl : z ∈ closure (Metric.ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hz))
  simpa [F] using
    (Complex.norm_le_of_forall_mem_frontier_norm_le (f := F)
      (U := Metric.ball (0 : ℂ) 1) (C := c) (Metric.isBounded_ball) hd hC hzcl)

/-- **Margin on the closed disk.**  With `c < 2` and the circle bound, the
function `z ↦ 2 − fa n a (fun j => E (θ j)) p z` has modulus `≥ 2 − c > 0`
on the closed unit disk. -/
theorem two_sub_fa_lower_bound_closedBall (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (θ : Fin n → ℝ) (p : Fin n → ℝ) (hp : ∀ j : Fin n, 0 ≤ p j) {c : ℝ}
    (hc : c < 2) (hcircle : ∀ σ : ℝ, ‖faE n a θ p σ‖ ≤ c) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → 2 - c ≤ ‖(2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p z‖ := by
  intro z hz
  have hbd := fa_bound_closedBall n a ha θ p hp hcircle z hz
  have htri : (2 : ℝ) ≤ ‖(2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p z‖
      + ‖fa n a (fun j : Fin n => E (θ j)) p z‖ := by
    have hn := norm_add_le ((2 : ℂ) - fa n a (fun j : Fin n => E (θ j)) p z)
      (fa n a (fun j : Fin n => E (θ j)) p z)
    rw [sub_add_cancel] at hn
    simpa using hn
  nlinarith

end Submission.KLMain

end
