import Mathlib
import Submission.Commons.Analysis.StationaryPhase.log_phase_stationary_phase
import Submission.Commons.Analysis.StationaryPhase.log_phase_prim_left_general
import Submission.Commons.Analysis.StationaryPhase.log_phase_prim_right_general
import Submission.Commons.Analysis.StationaryPhase.log_phase_half_line_left
import Submission.Commons.Analysis.StationaryPhase.logphase_outer_bound_general
import Submission.Commons.Analysis.Oscillatory.norm_integral_exp_two_ibp
import Submission.Commons.Analysis.Oscillatory.norm_integral_mul_exp_le_of_deriv_ge_mono
import Submission.Commons.Analysis.Oscillatory.norm_integral_mul_exp_le_of_deriv_ge_mono
import Submission.Commons.NumberTheory.DirichletPolynomial.vdc_transform_log_phase_reverse
import Submission.Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le

/-
## Elaboration notes (hard-won; reuse rather than rediscover)

* `ContDiffBump.contDiff` has regularity `↑(⊤ : ℕ∞) : WithTop ℕ∞`, which is `some ∞`, **not**
  `⊤ : WithTop ℕ∞` (which is `none`).  Consequently `simpa`/`ContDiff.of_le` against a `⊤`-valued
  goal fails, and `WithTop.coe_top` does not exist.  The robust pattern is to state helpers with a
  general `n : ℕ∞` and to recover finite regularities *definitionally* by
  `ContDiffBump.contDiff (n := (2 : ℕ∞))  -- : ContDiff ℝ 2 WwB, on the nose`.
* For a `ℝ`-valued `f`, `IsCompact.exists_bound_of_continuousOn` (the *additive* form) yields
  `∃ C, ∀ x ∈ s, ‖f x‖ ≤ C`; the primed (`...On'`) form requires a multiplicative `SeminormedGroup`
  and therefore fails on `ℝ`.
* `Complex.norm_ofReal` does not exist; use `Complex.norm_of_nonneg` when the real part is `≥ 0`.
* Monotonicity of products of norms: `mul_le_mul_of_nonneg_right` / `_left` (rather than
  `mul_le_mul`, whose argument order is `a ≤ c`, `b ≤ d`, `0 ≤ c`, `0 ≤ b`).
* To invoke the contrapositive of `ContDiffBump.zero_of_le_dist` (deriving `|u-1| < rOut` from
  `WwB u ≠ 0`), use `not_lt.mp`.
-/

namespace Commons.NumberTheory.DirichletPolynomial

open MeasureTheory Complex Real
open scoped Real Topology

set_option autoImplicit false
noncomputable section

/-- The integrand of the `m`-th Fourier integral. -/
def WwF (χ : ℝ → ℝ) (τ : ℝ) (m : ℤ) (y : ℝ) : ℂ :=
  ((Real.sqrt y)⁻¹ : ℂ) * Complex.exp (Complex.I * ((τ : ℂ) * (Real.log y : ℂ)))
    * (χ y : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I) * ((m : ℝ) * y))

/-- The `m`-th Fourier integral appearing in `weighted_window_reflection`. -/
def WwI (χ : ℝ → ℝ) (τ : ℝ) (m : ℤ) : ℂ := ∫ y : ℝ, WwF χ τ m y

/-- The stationary-phase normal form `∫ u^{-1/2} χ(su) e^{iτ(log u - u)} du`. -/
def WwJ (χ : ℝ → ℝ) (τ s : ℝ) : ℂ :=
  ∫ u : ℝ, ((Real.sqrt u)⁻¹ : ℂ) * (χ (s * u) : ℂ)
    * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))

/-- The dual sum of the statement. -/
def WwK (N : ℕ) (τ : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
            (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
    (k : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)

/-- pointwise substitution identity: `WwF χ τ m (s*u)` equals
`(√s)^{-1} e^{iτ log s}` times the `WwJ`-integrand, when `2π m s = τ`. -/
lemma WwF_comp (χ : ℝ → ℝ) {τ s : ℝ} (hs : 0 < s) {m : ℤ} (h : 2 * Real.pi * (m : ℝ) * s = τ)
    (u : ℝ) :
    WwF χ τ m (s * u) = ((Real.sqrt s)⁻¹ : ℂ) * Complex.exp (Complex.I * ((τ : ℂ) * (Real.log s : ℂ)))
      * (((Real.sqrt u)⁻¹ : ℂ) * (χ (s * u) : ℂ)
          * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))) := by
  by_cases hu : u = 0
  · subst hu
    unfold WwF
    simp [Real.log_zero]
  have hlog : Real.log (s * u) = Real.log s + Real.log u := Real.log_mul (ne_of_gt hs) hu
  have hR : (m : ℝ) * (s * u) = τ * u / (2 * Real.pi) := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [← h]; field_simp
  unfold WwF
  rw [Real.sqrt_mul (le_of_lt hs) u, hlog]
  have harg : Complex.I * ((τ : ℂ) * ((Real.log s + Real.log u : ℝ) : ℂ))
      + (-(2 * Real.pi * Complex.I) * (((m : ℝ) * (s * u) : ℝ) : ℂ))
      = Complex.I * ((τ : ℂ) * (Real.log s : ℂ))
        + Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)) := by
    have h2 : (((m : ℝ) * (s * u) : ℝ) : ℂ) = (τ : ℂ) * (u : ℂ) / (2 * Real.pi) := by
      rw [hR]; push_cast; ring
    rw [h2]
    push_cast
    field_simp
    ring
  have hexp : Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log s + Real.log u : ℝ) : ℂ)))
        * Complex.exp (-(2 * Real.pi * Complex.I) * (((m : ℝ) * (s * u) : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((τ : ℂ) * (Real.log s : ℂ)))
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, harg]
  have step : ((Real.sqrt s * Real.sqrt u : ℝ) : ℂ)⁻¹
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log s + Real.log u : ℝ) : ℂ)))
        * (χ (s * u) : ℂ)
        * Complex.exp (-(2 * Real.pi * Complex.I) * (((m : ℝ) * (s * u) : ℝ) : ℂ))
      = ((Real.sqrt s)⁻¹ : ℂ) * Complex.exp (Complex.I * ((τ : ℂ) * (Real.log s : ℂ)))
        * (((Real.sqrt u)⁻¹ : ℂ) * (χ (s * u) : ℂ)
            * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))) := by
    rw [show ((Real.sqrt s * Real.sqrt u : ℝ) : ℂ)⁻¹
          = ((Real.sqrt s)⁻¹ : ℂ) * ((Real.sqrt u)⁻¹ : ℂ) from by push_cast; ring]
    rw [show ((Real.sqrt s)⁻¹ : ℂ) * ((Real.sqrt u)⁻¹ : ℂ)
          * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log s + Real.log u : ℝ) : ℂ)))
          * (χ (s * u) : ℂ)
          * Complex.exp (-(2 * Real.pi * Complex.I) * (((m : ℝ) * (s * u) : ℝ) : ℂ))
        = ((Real.sqrt s)⁻¹ : ℂ)
          * (Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log s + Real.log u : ℝ) : ℂ)))
              * Complex.exp (-(2 * Real.pi * Complex.I) * (((m : ℝ) * (s * u) : ℝ) : ℂ)))
          * (((Real.sqrt u)⁻¹ : ℂ) * (χ (s * u) : ℂ)) from by ring]
    rw [hexp]
    ring
  simpa only [Complex.ofReal_mul] using step

/-- Substitution `y = s u` on the line. -/
lemma WwI_subst (χ : ℝ → ℝ) (τ : ℝ) (m : ℤ) {s : ℝ} (hs : 0 < s) :
    WwI χ τ m = (s : ℂ) * ∫ u : ℝ, WwF χ τ m (s * u) := by
  unfold WwI
  have h := MeasureTheory.Measure.integral_comp_mul_left (WwF χ τ m) s
  rw [Complex.real_smul, abs_of_pos (inv_pos.mpr hs)] at h
  rw [h, Complex.ofReal_inv, ← mul_assoc]
  rw [mul_inv_cancel₀ (show (s : ℂ) ≠ 0 by exact_mod_cast ne_of_gt hs), one_mul]

/-- **Scaled log-phase stationary phase** (from the unscaled commons version). -/
theorem log_phase_stationary_phase_scaled :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ → ℂ) (a b t M : ℝ),
      (1/2 : ℝ) ≤ a → a < 1 → 1 < b → b ≤ 6 →
      0 < M →
      ContDiff ℝ 2 A → (∀ y, y ∉ Set.Icc a b → A y = 0) →
      (∀ y, ‖A y‖ ≤ M) → (∀ y, ‖deriv A y‖ ≤ M) → 2 ≤ t →
      ‖(∫ y in a..b, A y * Complex.exp (Complex.I * t * (Real.log y - y)))
        - A 1 * Complex.exp (-(t : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ)
            * Complex.exp (-(Real.pi / 4) * Complex.I)‖
      ≤ C * M * (Real.log t / t) := by
  obtain ⟨C, hCpos, hC⟩ := Commons.Analysis.StationaryPhase.log_phase_stationary_phase
  refine ⟨C, hCpos, ?_⟩
  intro A a b t M ha ha1 h1b hb6 hM hA hsupp hAb hAd ht
  set At : ℝ → ℂ := fun y => (M : ℂ)⁻¹ * A y with hAt
  have hAtdiff : ContDiff ℝ 2 At := by rw [hAt]; exact contDiff_const.mul hA
  have hAtsupp : ∀ y, y ∉ Set.Icc a b → At y = 0 := fun y hy => by
    rw [hAt]; simp [hsupp y hy]
  have hMn : ‖(M:ℂ)‖ = M := by rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (le_of_lt hM)]
  have hAtb : ∀ y, ‖At y‖ ≤ 1 := fun y => by
    rw [hAt, norm_mul, norm_inv, hMn]
    have h1 : ‖A y‖ ≤ M := hAb y
    calc M⁻¹ * ‖A y‖ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hM)
  have hAtd : ∀ y, ‖deriv At y‖ ≤ 1 := fun y => by
    have hd : deriv At y = (M:ℂ)⁻¹ * deriv A y := by
      rw [hAt]
      exact deriv_const_mul _ ((hA.differentiable (by norm_num)).differentiableAt)
    rw [hd, norm_mul, norm_inv, hMn]
    have h1 : ‖deriv A y‖ ≤ M := hAd y
    calc M⁻¹ * ‖deriv A y‖ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hM)
  have key := hC At a b t ha ha1 h1b hb6 hAtdiff hAtsupp hAtb hAtd ht
  have hAt1 : At 1 = (M:ℂ)⁻¹ * A 1 := rfl
  have hInt : (∫ y in a..b, At y * Complex.exp (Complex.I * t * (Real.log y - y)))
      = (M:ℂ)⁻¹ * ∫ y in a..b, A y * Complex.exp (Complex.I * t * (Real.log y - y)) := by
    rw [show (fun y => At y * Complex.exp (Complex.I * t * (Real.log y - y)))
        = (fun y => (M:ℂ)⁻¹ * (A y * Complex.exp (Complex.I * t * (Real.log y - y)))) from by
      funext y; rw [hAt]; ring]
    exact intervalIntegral.integral_const_mul _ _
  rw [hInt, hAt1] at key
  have hfac : (M:ℂ)⁻¹ * (∫ y in a..b, A y * Complex.exp (Complex.I * t * (Real.log y - y)))
      - (M:ℂ)⁻¹ * A 1 * Complex.exp (-(t : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ)
          * Complex.exp (-(Real.pi / 4) * Complex.I)
      = (M:ℂ)⁻¹ * ((∫ y in a..b, A y * Complex.exp (Complex.I * t * (Real.log y - y)))
          - A 1 * Complex.exp (-(t : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ)
              * Complex.exp (-(Real.pi / 4) * Complex.I)) := by ring
  rw [hfac, norm_mul, norm_inv, hMn] at key
  calc ‖(∫ y in a..b, A y * Complex.exp (Complex.I * t * (Real.log y - y)))
        - A 1 * Complex.exp (-(t : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ)
            * Complex.exp (-(Real.pi / 4) * Complex.I)‖
      = M * (M⁻¹ * ‖(∫ y in a..b, A y * Complex.exp (Complex.I * t * (Real.log y - y)))
        - A 1 * Complex.exp (-(t : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ)
            * Complex.exp (-(Real.pi / 4) * Complex.I)‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hM), one_mul]
    _ ≤ M * (C * (Real.log t / t)) := mul_le_mul_of_nonneg_left key (le_of_lt hM)
    _ = C * M * (Real.log t / t) := by ring


/-- A fixed bump: `= 1` on `[3/4,5/4]`, supported in `(1/2, 3/2) ⊂ (0,∞)`.  Used to localise the
stationary-phase amplitude so that the commons stationary-phase lemma applies. -/
def WwB : ContDiffBump (1 : ℝ) where
  rIn := 1/4
  rOut := 2/5
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

lemma WwB_one : ∀ u : ℝ, |u - 1| ≤ 1/4 → (WwB : ℝ → ℝ) u = 1 := fun u hu =>
  WwB.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall]
    show dist u 1 ≤ (1/4 : ℝ)
    rwa [Real.dist_eq])

lemma WwB_zero : ∀ u : ℝ, 2/5 ≤ |u - 1| → (WwB : ℝ → ℝ) u = 0 := fun u hu =>
  WwB.zero_of_le_dist (by
    show (2/5 : ℝ) ≤ dist u 1
    rwa [Real.dist_eq])

lemma WwB_nonneg (u : ℝ) : 0 ≤ (WwB : ℝ → ℝ) u := WwB.nonneg
lemma WwB_le_one (u : ℝ) : (WwB : ℝ → ℝ) u ≤ 1 := WwB.le_one


/-- An explicit bound for the derivative of `WwB`. -/
lemma WwB_deriv_bounded : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, |deriv (WwB : ℝ → ℝ) u| ≤ C := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WwB : ℝ → ℝ) :=
    ContDiffBump.contDiff (n := ⊤) WwB
  have hc : Continuous (deriv (WwB : ℝ → ℝ)) := hcd.continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (1:ℝ) (2:ℝ)).exists_bound_of_continuousOn hc.continuousOn
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (by simp [Metric.mem_closedBall]))
  refine ⟨C + 1, by linarith, fun u => ?_⟩
  by_cases h : dist u 1 < 2
  · have h1 := hC u (by simpa only [Metric.mem_closedBall] using le_of_lt h)
    rw [Real.norm_eq_abs] at h1
    linarith
  · push Not at h
    have hopen : IsOpen {y : ℝ | (2/5:ℝ) < dist y 1} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    have hev : (WwB : ℝ → ℝ) =ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
      filter_upwards [hopen.mem_nhds (by show (2/5:ℝ) < dist u 1; linarith)] with y hy
      apply WwB_zero
      have h2 : (2/5:ℝ) ≤ dist y 1 := le_of_lt hy
      rwa [Real.dist_eq] at h2
    rw [hev.deriv_eq, deriv_const, abs_zero]
    linarith

/-- `β · (√·)⁻¹` is `C^n` when `β` is `C^n` and vanishes on `(-∞,r]` with `r>0`. -/
theorem contDiff_bump_mul_sqrt_inv (β : ℝ → ℝ) {r : ℝ} (n : ℕ∞)
    (hβ : ContDiff ℝ (n : WithTop ℕ∞) β) (hr : 0 < r) (hβ0 : ∀ y, y ≤ r → β y = 0) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun u : ℝ => β u * (Real.sqrt u)⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_or_ge u r with hu | hu
  · have hev : (fun u : ℝ => β u * (Real.sqrt u)⁻¹) =ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hu] with y hy
      rw [hβ0 y (le_of_lt hy), zero_mul]
    exact (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq hev
  · have hu_pos : 0 < u := lt_of_lt_of_le hr hu
    have hsq : ContDiffAt ℝ (n : WithTop ℕ∞) Real.sqrt u :=
      Real.contDiffAt_sqrt (n := (n : WithTop ℕ∞)) (ne_of_gt hu_pos)
    have hne : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu_pos)
    exact (hβ.contDiffAt).mul (hsq.inv hne)

/-- `WwB · (√·)⁻¹` is `C²`. -/
lemma WwB_sqrt_inv_contDiff2 : ContDiff ℝ 2
    (fun u : ℝ => (WwB : ℝ → ℝ) u * (Real.sqrt u)⁻¹) := by
  refine contDiff_bump_mul_sqrt_inv (WwB : ℝ → ℝ) (r := 1/2) 2 ?_ (by norm_num) ?_
  · exact ContDiffBump.contDiff (n := (2 : ℕ∞)) WwB
  · intro y hy
    apply WwB_zero
    rw [abs_of_nonpos (by linarith : y - 1 ≤ 0)]
    linarith

/-- The bumped amplitude of the stationary phase. -/
def WwA (χ : ℝ → ℝ) (s : ℝ) (u : ℝ) : ℂ :=
  ((WwB u * (Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s * u) : ℂ)

lemma WwA_contDiff {χ : ℝ → ℝ} {s : ℝ} (hχd : ContDiff ℝ 3 χ) :
    ContDiff ℝ 2 (WwA χ s) := by
  have h2 : ContDiff ℝ 2 (fun u : ℝ => (χ (s * u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((hχd.comp (contDiff_const.mul contDiff_id)).of_le (by norm_num))
  exact (Complex.ofRealCLM.contDiff.comp WwB_sqrt_inv_contDiff2).mul h2

lemma WwA_one {χ : ℝ → ℝ} {s : ℝ} : WwA χ s 1 = (χ s : ℂ) := by
  have h1 : (WwB : ℝ → ℝ) 1 = 1 := WwB_one 1 (by norm_num)
  have h2 : (Real.sqrt 1)⁻¹ = (1:ℝ) := by simp
  unfold WwA
  rw [h1, h2]
  norm_num


lemma WwA_support (χ : ℝ → ℝ) (s : ℝ) :
    ∀ u : ℝ, u ∉ Set.Icc (1/2) 6 → WwA χ s u = 0 := by
  intro u hu
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  unfold WwA
  have hz : (WwB : ℝ → ℝ) u = 0 := by
    apply WwB_zero
    rcases hu with h | h
    · rw [abs_of_nonpos (by linarith : u - 1 ≤ 0)]; linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ u - 1)]; linarith
  rw [hz]; simp

lemma WwA_norm_le {χ : ℝ → ℝ} {s : ℝ} (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (u : ℝ) :
    ‖WwA χ s u‖ ≤ Real.sqrt (5/3) := by
  by_cases hw : (WwB : ℝ → ℝ) u = 0
  · simp only [WwA, hw, zero_mul, Complex.ofReal_zero, norm_zero]; positivity
  · have hlt : |u - 1| < 2/5 := by
      by_contra hc
      exact hw (WwB_zero u (not_lt.mp hc))
    rw [abs_lt] at hlt
    have hu2 : (3/5:ℝ) < u := by linarith [hlt.1]
    have hu3 : 0 < u := by linarith
    have hwu : (WwB : ℝ → ℝ) u ≤ 1 := WwB_le_one u
    have hchi : ‖(χ (s * u) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_of_nonneg (hχ0 (s*u)).1]
      exact (hχ0 (s*u)).2
    unfold WwA
    rw [norm_mul]
    have hfa : ‖((WwB u * (Real.sqrt u)⁻¹ : ℝ) : ℂ)‖ ≤ Real.sqrt (5/3) := by
      rw [Complex.norm_of_nonneg (mul_nonneg (WwB_nonneg u) (by positivity))]
      have h1 : (Real.sqrt u)⁻¹ ≤ (Real.sqrt (3/5))⁻¹ :=
        (inv_le_inv₀ (Real.sqrt_pos.mpr hu3) (Real.sqrt_pos.mpr (by norm_num))).mpr
          (Real.sqrt_le_sqrt (by linarith))
      have h2 : (Real.sqrt (3/5))⁻¹ = Real.sqrt (5/3) := by
        rw [← Real.sqrt_inv]; norm_num
      calc WwB u * (Real.sqrt u)⁻¹ ≤ 1 * (Real.sqrt u)⁻¹ :=
            mul_le_mul_of_nonneg_right hwu (by positivity)
        _ = (Real.sqrt u)⁻¹ := by ring
        _ ≤ (Real.sqrt (3/5))⁻¹ := h1
        _ = Real.sqrt (5/3) := h2
    calc ‖((WwB u * (Real.sqrt u)⁻¹ : ℝ) : ℂ)‖ * ‖(χ (s * u) : ℂ)‖
        ≤ Real.sqrt (5/3) * ‖(χ (s * u) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right hfa (norm_nonneg _)
      _ ≤ Real.sqrt (5/3) * 1 := mul_le_mul_of_nonneg_left hchi (Real.sqrt_nonneg _)
      _ = Real.sqrt (5/3) := by ring

lemma WwA_deriv_norm_le {χ : ℝ → ℝ} {s K : ℝ} {N : ℕ} {Cb : ℝ}
    (hCb : ∀ u, |deriv (WwB : ℝ → ℝ) u| ≤ Cb) (hCb0 : 0 ≤ Cb)
    (hχd : ContDiff ℝ 3 χ) (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N) (hN : 0 < N) (hs0 : 0 ≤ s) (hKnn : 0 ≤ K)
    (hle : s ≤ 3 * (N:ℝ)) (u : ℝ) :
    ‖deriv (WwA χ s) u‖ ≤ (2 * Cb + 10) * (1 + K) * (1 + Real.sqrt N) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hsr : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  by_cases hu : |u - 1| ≤ 2/5
  · have hu1 : (3/5:ℝ) ≤ u := by rw [abs_le] at hu; linarith [hu.1]
    have hu3 : 0 < u := by linarith
    have hsp : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu3
    have hnorm (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
      rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
    have hWd : DifferentiableAt ℝ (WwB : ℝ → ℝ) u :=
      ((ContDiffBump.contDiff (n := (1:ℕ∞)) WwB).differentiable (by simp)).differentiableAt
    have hsi : HasDerivAt (fun v : ℝ => (Real.sqrt v)⁻¹) (-(1 / (2 * u * Real.sqrt u))) u := by
      have h1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt u)) u := Real.hasDerivAt_sqrt (ne_of_gt hu3)
      have h2 : HasDerivAt (fun v : ℝ => (Real.sqrt v)⁻¹)
          (-(1 / (2 * Real.sqrt u)) / (Real.sqrt u) ^ 2) u := h1.inv (ne_of_gt hsp)
      have hv : -(1 / (2 * Real.sqrt u)) / (Real.sqrt u) ^ 2 = -(1 / (2 * u * Real.sqrt u)) := by
        rw [Real.sq_sqrt (le_of_lt hu3)]; field_simp; try ring
      rwa [hv] at h2
    have hf : HasDerivAt (fun v : ℝ => (WwB v * (Real.sqrt v)⁻¹ : ℝ))
        (deriv (WwB:ℝ→ℝ) u * (Real.sqrt u)⁻¹ + WwB u * (-(1 / (2 * u * Real.sqrt u)))) u :=
      hWd.hasDerivAt.mul hsi
    have hF : HasDerivAt (fun v : ℝ => ((WwB v * (Real.sqrt v)⁻¹ : ℝ) : ℂ))
        ((deriv (WwB:ℝ→ℝ) u * (Real.sqrt u)⁻¹ + WwB u * (-(1 / (2 * u * Real.sqrt u))) : ℝ) : ℂ) u :=
      hf.ofReal_comp
    have hgc : HasDerivAt (fun v : ℝ => χ (s * v)) (deriv χ (s*u) * s) u :=
      (((hχd.differentiable (by norm_num)) (s*u)).hasDerivAt).comp u
        (by simpa using (hasDerivAt_id u).const_mul s)
    have hG : HasDerivAt (fun v : ℝ => (χ (s * v) : ℂ)) ((deriv χ (s*u) * s : ℝ) : ℂ) u :=
      hgc.ofReal_comp
    have hprod := hF.mul hG
    have hFG : WwA χ s = (fun v : ℝ => ((WwB v * (Real.sqrt v)⁻¹ : ℝ) : ℂ))
        * (fun v : ℝ => (χ (s*v) : ℂ)) := rfl
    rw [hFG, hprod.deriv]
    have h1u : (Real.sqrt u)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hsp (by norm_num)]
      nlinarith [Real.sq_sqrt (le_of_lt hu3), Real.sqrt_nonneg u, hu1]
    have h2u : 1 / (2 * u * Real.sqrt u) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.sq_sqrt (le_of_lt hu3), Real.sqrt_nonneg u, hu1]
    have hGu : ‖(χ (s * u) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_of_nonneg (hχ0 (s*u)).1]; exact (hχ0 (s*u)).2
    have hFu : ‖((WwB u * (Real.sqrt u)⁻¹ : ℝ) : ℂ)‖ ≤ 2 := by
      rw [hnorm, abs_of_nonneg (mul_nonneg (WwB_nonneg u) (by positivity))]
      calc WwB u * (Real.sqrt u)⁻¹ ≤ 1 * (Real.sqrt u)⁻¹ :=
            mul_le_mul_of_nonneg_right (WwB_le_one u) (by positivity)
        _ = (Real.sqrt u)⁻¹ := by ring
        _ ≤ 2 := h1u
    have hGd : ‖((deriv χ (s*u) * s : ℝ) : ℂ)‖ ≤ s * K / Real.sqrt N := by
      rw [hnorm, abs_mul, abs_of_nonneg hs0]
      calc |deriv χ (s*u)| * s ≤ (K / Real.sqrt N) * s :=
            mul_le_mul_of_nonneg_right (hbdd (s*u)) hs0
        _ = s * K / Real.sqrt N := by ring
    have hFd : ‖((deriv (WwB:ℝ→ℝ) u * (Real.sqrt u)⁻¹ + WwB u * (-(1 / (2 * u * Real.sqrt u))) : ℝ) : ℂ)‖
        ≤ 2 * Cb + 2 := by
      rw [hnorm]
      have h3 : |WwB u * (-(1 / (2 * u * Real.sqrt u)))| ≤ 2 := by
        have hpos : (0:ℝ) < 1 / (2 * u * Real.sqrt u) := by positivity
        rw [abs_mul, abs_neg, abs_of_nonneg (WwB_nonneg u), abs_of_nonneg (le_of_lt hpos)]
        calc WwB u * (1 / (2 * u * Real.sqrt u)) ≤ 1 * (1 / (2 * u * Real.sqrt u)) :=
              mul_le_mul_of_nonneg_right (WwB_le_one u) (le_of_lt hpos)
          _ = 1 / (2 * u * Real.sqrt u) := by ring
          _ ≤ 2 := h2u
      have h4 : |deriv (WwB:ℝ→ℝ) u * (Real.sqrt u)⁻¹| ≤ 2 * Cb := by
        have hspn : (0:ℝ) < (Real.sqrt u)⁻¹ := by positivity
        rw [abs_mul, abs_of_nonneg (le_of_lt hspn)]
        calc |deriv (WwB:ℝ→ℝ) u| * (Real.sqrt u)⁻¹ ≤ Cb * (Real.sqrt u)⁻¹ :=
              mul_le_mul_of_nonneg_right (hCb u) (by positivity)
          _ ≤ Cb * 2 := mul_le_mul_of_nonneg_left h1u hCb0
          _ = 2 * Cb := by ring
      exact le_trans (abs_add_le _ _) (add_le_add h4 h3)
    calc ‖((deriv (WwB:ℝ→ℝ) u * (Real.sqrt u)⁻¹ + WwB u * (-(1 / (2 * u * Real.sqrt u))) : ℝ) : ℂ)
            * (χ (s * u) : ℂ) + ((WwB u * (Real.sqrt u)⁻¹ : ℝ) : ℂ) * ((deriv χ (s*u) * s : ℝ) : ℂ)‖
        ≤ ‖((deriv (WwB:ℝ→ℝ) u * (Real.sqrt u)⁻¹ + WwB u * (-(1 / (2 * u * Real.sqrt u))) : ℝ) : ℂ)‖
            * ‖(χ (s * u) : ℂ)‖
          + ‖((WwB u * (Real.sqrt u)⁻¹ : ℝ) : ℂ)‖ * ‖((deriv χ (s*u) * s : ℝ) : ℂ)‖ := by
          have h := norm_add_le
            (((deriv (WwB:ℝ→ℝ) u * (Real.sqrt u)⁻¹ + WwB u * (-(1 / (2 * u * Real.sqrt u))) : ℝ) : ℂ)
              * (χ (s * u) : ℂ))
            (((WwB u * (Real.sqrt u)⁻¹ : ℝ) : ℂ) * ((deriv χ (s*u) * s : ℝ) : ℂ))
          rw [norm_mul, norm_mul] at h
          exact h
      _ ≤ (2 * Cb + 2) * 1 + 2 * (s * K / Real.sqrt N) := by
          apply add_le_add
          · calc ‖((deriv (WwB:ℝ→ℝ) u * (Real.sqrt u)⁻¹ + WwB u * (-(1 / (2 * u * Real.sqrt u))) : ℝ) : ℂ)‖
                  * ‖(χ (s * u) : ℂ)‖
              ≤ (2 * Cb + 2) * ‖(χ (s * u) : ℂ)‖ :=
                mul_le_mul_of_nonneg_right hFd (norm_nonneg _)
            _ ≤ (2 * Cb + 2) * 1 := mul_le_mul_of_nonneg_left hGu (by linarith)
          · calc ‖((WwB u * (Real.sqrt u)⁻¹ : ℝ) : ℂ)‖ * ‖((deriv χ (s*u) * s : ℝ) : ℂ)‖
              ≤ 2 * ‖((deriv χ (s*u) * s : ℝ) : ℂ)‖ :=
                mul_le_mul_of_nonneg_right hFu (norm_nonneg _)
            _ ≤ 2 * (s * K / Real.sqrt N) := mul_le_mul_of_nonneg_left hGd (by norm_num)
      _ ≤ (2 * Cb + 10) * (1 + K) * (1 + Real.sqrt N) := by
          have hs' : 2 * (s * K / Real.sqrt N) ≤ 6 * K * Real.sqrt N := by
            have h1 : s / Real.sqrt N ≤ 3 * Real.sqrt N := by
              rw [div_le_iff₀ hsr]; nlinarith [Real.sq_sqrt (le_of_lt hNpos)]
            have h2 : s * K / Real.sqrt N ≤ K * (3 * Real.sqrt N) := by
              rw [show s * K / Real.sqrt N = K * (s / Real.sqrt N) by ring]
              exact mul_le_mul_of_nonneg_left h1 hKnn
            linarith [h2]
          have hKsq : (0:ℝ) ≤ K * Real.sqrt N := mul_nonneg hKnn (Real.sqrt_nonneg N)
          have hexp : (2 * Cb + 10) * (1 + K) * (1 + Real.sqrt N)
              = (2*Cb+10) + (2*Cb+10)*K + (2*Cb+10)*Real.sqrt N
                + (2*Cb+10)*(K*Real.sqrt N) := by ring
          nlinarith [hs', hKsq, hexp, hKnn, Real.sqrt_nonneg N, hCb0,
            mul_nonneg hKsq (by linarith : (0:ℝ) ≤ 2*Cb+10)]
  · push Not at hu
    have hopen : IsOpen {v : ℝ | (2/5:ℝ) < dist v 1} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    have hev : WwA χ s =ᶠ[𝓝 u] (fun _ => (0:ℂ)) := by
      filter_upwards [hopen.mem_nhds (by show (2/5:ℝ) < dist u 1; rw [Real.dist_eq]; exact hu)] with v hv
      have hv2 : (2/5:ℝ) ≤ |v - 1| := by
        have := le_of_lt hv; rwa [Real.dist_eq] at this
      simp only [WwA, WwB_zero v hv2, Complex.ofReal_zero, zero_mul]
    rw [hev.deriv_eq, deriv_const, norm_zero]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)

/-- `M`-form of the norm bound: the same constant `(2C_b+10)(1+K)(1+√N)` bounds both
`WwA` and its derivative. -/
lemma WwA_norm_le_M {χ : ℝ → ℝ} {s K : ℝ} {N : ℕ} {Cb : ℝ}
    (hCb0 : 0 ≤ Cb) (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (hN : 1 ≤ N) (hKnn : 0 ≤ K) (u : ℝ) :
    ‖WwA χ s u‖ ≤ (2 * Cb + 10) * (1 + K) * (1 + Real.sqrt N) := by
  have hN0 : (0:ℝ) ≤ N := by positivity
  refine le_trans (WwA_norm_le hχ0 u) ?_
  have h1 : (0:ℝ) ≤ 2 * Cb + 10 := by linarith
  have h2 : (0:ℝ) ≤ 1 + K := by linarith
  have h3 : (0:ℝ) ≤ 1 + Real.sqrt N := by positivity
  have h4 : (10:ℝ) ≤ (2*Cb+10)*(1+K)*(1+Real.sqrt N) := by
    have h5 : (1:ℝ) ≤ (1+K)*(1+Real.sqrt N) := by
      nlinarith [hKnn, Real.sqrt_nonneg N, hN0]
    nlinarith [mul_le_mul_of_nonneg_left h5 h1, h1]
  have h5 : Real.sqrt (5/3) ≤ 10 := by
    rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
  linarith


/-- The Fresnel constant of the log-phase stationary phase. -/
def WwFres (τ : ℝ) : ℂ :=
  Complex.exp (-(τ : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / τ) : ℝ) : ℂ)
    * Complex.exp (-(Real.pi / 4) * Complex.I)

/-- Integral form of the substitution identity: for `m ≥ 1` and `s = τ/(2πm)`,
`WwI χ τ m = √s · e^{iτ log s} · WwJ χ τ s`. -/
lemma WwI_eq_WwJ (χ : ℝ → ℝ) {τ s : ℝ} (hs : 0 < s) {m : ℤ}
    (h : 2 * Real.pi * (m : ℝ) * s = τ) :
    WwI χ τ m = ((Real.sqrt s : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ : ℂ) * (Real.log s : ℂ)))
      * WwJ χ τ s := by
  rw [WwI_subst χ τ m hs]
  rw [show (∫ u : ℝ, WwF χ τ m (s * u))
      = ∫ u : ℝ, ((Real.sqrt s)⁻¹ : ℂ) * Complex.exp (Complex.I * ((τ : ℂ) * (Real.log s : ℂ)))
          * (((Real.sqrt u)⁻¹ : ℂ) * (χ (s * u) : ℂ)
              * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))) from
    integral_congr_ae (Filter.Eventually.of_forall (fun u => WwF_comp χ hs h u))]
  rw [WwJ, MeasureTheory.integral_const_mul, ← mul_assoc]
  rw [show (s : ℂ) * (((Real.sqrt s)⁻¹ : ℂ) * Complex.exp (Complex.I * ((τ : ℂ) * (Real.log s : ℂ))))
      = ((Real.sqrt s : ℝ) : ℂ) * Complex.exp (Complex.I * ((τ : ℂ) * (Real.log s : ℂ))) from by
    have hspc : ((Real.sqrt s : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt (Real.sqrt_pos.mpr hs)
    rw [show (s : ℂ) = ((Real.sqrt s : ℝ) : ℂ) ^ 2 from by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hs)]]
    field_simp]
theorem WwA_stat {N : ℕ} {χ : ℝ → ℝ} {K τ s Cb : ℝ}
    (hCb : ∀ u, |deriv (WwB : ℝ → ℝ) u| ≤ Cb) (hCb0 : 0 ≤ Cb)
    (hτ : 2 ≤ τ) (hχd : ContDiff ℝ 3 χ) (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N) (hN : 1 ≤ N) (hs0 : 0 ≤ s) (hKnn : 0 ≤ K)
    (hle : s ≤ 3 * (N:ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ‖(∫ u : ℝ, WwA χ s u * Complex.exp (Complex.I * τ * (Real.log u - u)))
        - (χ s : ℂ) * WwFres τ‖
      ≤ C * ((2*Cb+10)*(1+K)*(1+Real.sqrt N)) * (Real.log τ / τ) := by
  obtain ⟨C, hCpos, hC⟩ := log_phase_stationary_phase_scaled
  refine ⟨C, hCpos, ?_⟩
  set M : ℝ := (2*Cb+10)*(1+K)*(1+Real.sqrt N) with hMdef
  have h1 : (0:ℝ) ≤ 2*Cb+10 := by linarith
  have h2 : (0:ℝ) ≤ 1+Real.sqrt N := by positivity
  have hMpos : 0 < M := by rw [hMdef]; positivity
  set F : ℝ → ℂ := fun u => WwA χ s u * Complex.exp (Complex.I * τ * (Real.log u - u)) with hF
  have hFsupp : ∀ u : ℝ, u ∉ Set.Icc (1/2) 6 → F u = 0 := fun u hu => by
    simp only [hF, WwA_support χ s u hu, zero_mul]
  have hIntEq : (∫ u : ℝ, F u) = ∫ u in (1/2:ℝ)..6, F u := by
    rw [intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ) ≤ 6),
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Set.Ioc (1/2) 6
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      by_cases hu2 : u ∈ Set.Icc (1/2) 6
      · have hu3 : u = 1/2 := by
          simp only [Set.mem_Icc] at hu2
          have hu4 : ¬ ((1/2:ℝ) < u ∧ u ≤ 6) := by simpa only [Set.mem_Ioc] using hu
          have hle : u ≤ 1/2 := by
            by_contra hc
            push Not at hc
            exact hu4 ⟨hc, hu2.2⟩
          linarith [hu2.1]
        subst hu3
        have hz : (WwB : ℝ → ℝ) (1/2) = 0 := WwB_zero (1/2) (by norm_num)
        have hz2 : WwA χ s (1/2) = 0 := by
          simp only [WwA, hz, Complex.ofReal_zero, zero_mul]
        rw [hF]; simp only [hz2, zero_mul]
      · exact hFsupp u hu2
  rw [hIntEq]
  have hstep := hC (WwA χ s) (1/2) 6 τ M (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hMpos (WwA_contDiff hχd) (fun y hy => WwA_support χ s y hy)
    (fun y => WwA_norm_le_M hCb0 hχ0 hN hKnn y)
    (fun y => WwA_deriv_norm_le hCb hCb0 hχd hχ0 hbdd hN hs0 hKnn hle y) hτ
  rw [hMdef] at hstep
  have hA1 : WwA χ s 1 = (χ s : ℂ) := WwA_one
  rw [hA1] at hstep
  have hFres : (χ s : ℂ) * WwFres τ = (χ s : ℂ) * Complex.exp (-(τ : ℂ) * Complex.I)
      * ((Real.sqrt (2 * Real.pi / τ) : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I) := by
    unfold WwFres; ring
  rw [hFres]
  exact hstep

def WwSm (x : ℝ) : ℝ := 1 - Real.smoothTransition (8 * x) * (1 - x)

lemma WwSm_contDiff : ContDiff ℝ 3 WwSm := by
  unfold WwSm
  have h1 : ContDiff ℝ 3 (fun x : ℝ => 8 * x) := by fun_prop
  have h2 : ContDiff ℝ 3 (fun x : ℝ => Real.smoothTransition (8 * x)) :=
    (Real.smoothTransition.contDiff (n := 3)).comp h1
  exact contDiff_const.sub (h2.mul (contDiff_const.sub contDiff_id))

lemma WwSm_eq_self {x : ℝ} (h : 1/8 ≤ x) : WwSm x = x := by
  unfold WwSm
  rw [Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ 8 * x)]
  ring

lemma WwSm_eq_one {x : ℝ} (h : x ≤ 0) : WwSm x = 1 := by
  unfold WwSm
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 8 * x ≤ 0)]
  ring

lemma WwSm_pos (x : ℝ) : 0 < WwSm x := by
  rcases le_or_gt x 0 with h | h
  · rw [WwSm_eq_one h]; norm_num
  · rcases le_or_gt (1/8) x with h1 | h1
    · rw [WwSm_eq_self h1]; linarith
    · have hs1 : Real.smoothTransition (8 * x) < 1 :=
        Real.smoothTransition.lt_one_of_lt_one (by linarith)
      have h1x : 0 < 1 - x := by linarith
      have hlt : Real.smoothTransition (8 * x) * (1 - x) < 1 := by
        calc Real.smoothTransition (8 * x) * (1 - x) < 1 * (1 - x) :=
              mul_lt_mul_of_pos_right hs1 h1x
          _ < 1 := by linarith
      have : WwSm x = 1 - Real.smoothTransition (8 * x) * (1 - x) := by unfold WwSm; ring
      rw [this]; linarith

lemma WwSm_nonneg (x : ℝ) : 0 ≤ WwSm x := le_of_lt (WwSm_pos x)

def WwLog (x : ℝ) : ℝ := Real.log (WwSm x)

lemma WwLog_contDiff : ContDiff ℝ 3 WwLog :=
  WwSm_contDiff.log (fun x => ne_of_gt (WwSm_pos x))

lemma WwLog_eq_log {x : ℝ} (h : 1/8 ≤ x) : WwLog x = Real.log x := by
  rw [WwLog, WwSm_eq_self h]

lemma WwLog_eventuallyEq {x : ℝ} (h : 1/8 < x) : WwLog =ᶠ[𝓝 x] Real.log := by
  filter_upwards [isOpen_Ioi.mem_nhds h] with y hy
  exact WwLog_eq_log (le_of_lt hy)

lemma WwSm_eventuallyEq {x : ℝ} (h : 1/8 < x) : WwSm =ᶠ[𝓝 x] id := by
  filter_upwards [isOpen_Ioi.mem_nhds h] with y hy
  exact WwSm_eq_self (le_of_lt hy)

lemma deriv_WwSm {x : ℝ} (h : 1/8 < x) : deriv WwSm x = 1 := by
  rw [(WwSm_eventuallyEq h).deriv_eq, deriv_id]

lemma iteratedDeriv_WwSm {x : ℝ} (h : 1/8 < x) (n : ℕ) :
    iteratedDeriv n WwSm x = if n = 0 then x else if n = 1 then 1 else 0 := by
  rw [(WwSm_eventuallyEq h).iteratedDeriv_eq, iteratedDeriv_id]

/-- The real amplitude `(√(WwSm y))⁻¹ · χ y`. -/
def WwGs (χ : ℝ → ℝ) (y : ℝ) : ℝ := (Real.sqrt (WwSm y))⁻¹ * χ y

lemma WwGs_contDiff {χ : ℝ → ℝ} (hχ : ContDiff ℝ 3 χ) : ContDiff ℝ 2 (WwGs χ) := by
  unfold WwGs
  have h1 : ContDiff ℝ 2 (fun y : ℝ => (Real.sqrt (WwSm y))⁻¹) :=
    ((WwSm_contDiff.of_le (by norm_num)).sqrt (fun y => ne_of_gt (WwSm_pos y))).inv
      (fun y => ne_of_gt (Real.sqrt_pos.mpr (WwSm_pos y)))
  exact h1.mul (hχ.of_le (by norm_num))

lemma WwGs_eq {χ : ℝ → ℝ} {y : ℝ} (hy : 1/8 ≤ y) : WwGs χ y = (Real.sqrt y)⁻¹ * χ y := by
  rw [WwGs, WwSm_eq_self hy]

lemma eventually_WwGs {χ : ℝ → ℝ} {y : ℝ} (hy : 1/8 < y) :
    WwGs χ =ᶠ[𝓝 y] (fun z => (Real.sqrt z)⁻¹ * χ z) := by
  filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
  exact WwGs_eq (le_of_lt hz)

lemma hasDerivAt_sqrt_inv {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => (Real.sqrt z)⁻¹) (-(1 / (2 * y * Real.sqrt y))) y := by
  have h0 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt y)) y := Real.hasDerivAt_sqrt (ne_of_gt hy)
  have hsp : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hy
  have h2 : HasDerivAt (fun z : ℝ => (Real.sqrt z)⁻¹)
      (-(1 / (2 * Real.sqrt y)) / (Real.sqrt y) ^ 2) y := h0.inv (ne_of_gt hsp)
  have hv : -(1 / (2 * Real.sqrt y)) / (Real.sqrt y) ^ 2 = -(1 / (2 * y * Real.sqrt y)) := by
    rw [Real.sq_sqrt (le_of_lt hy)]; field_simp; try ring
  rwa [hv] at h2

lemma deriv_WwGs {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {y : ℝ} (hy : 1/8 < y) :
    deriv (WwGs χ) y
      = -(1 / (2 * y * Real.sqrt y)) * χ y + (Real.sqrt y)⁻¹ * deriv χ y := by
  have hy0 : 0 < y := by linarith
  have hev := eventually_WwGs (χ := χ) hy
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun z : ℝ => (Real.sqrt z)⁻¹) (-(1/(2*y*Real.sqrt y))) y :=
    hasDerivAt_sqrt_inv hy0
  have h2 : HasDerivAt χ (deriv χ y) y := (hχ y).hasDerivAt
  exact (h1.mul h2).deriv

lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]


lemma abs3_le (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
  have h1 := abs_add_le (a + b) c
  have h2 := abs_add_le a b
  have h3 := abs_nonneg c
  have h4 := abs_nonneg (a + b)
  linarith

lemma abs_sub_add_le (a b c : ℝ) : |(a - b) + c| ≤ |a| + |b| + |c| := by
  have h := abs3_le a (-b) c
  have e : (a - b) + c = a + -b + c := by ring
  rw [e]
  simpa using h

lemma abs_sum4_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  have h4 := abs_nonneg (a + b + c)
  have h5 := abs_nonneg d
  have h6 := abs_nonneg (a + b)
  have h7 := abs_nonneg c
  linarith

variable {χ : ℝ → ℝ} {s : ℝ}

lemma hasDerivAt_const_mul' {s u : ℝ} : HasDerivAt (fun y : ℝ => s * y) s u := by
  have := (hasDerivAt_id u).const_mul s
  simpa using this

/-- First derivative of the scaled amplitude `u ↦ (√(WwSm u))⁻¹ χ (s u)` for `u > 1/8`. -/
lemma deriv_amp (hχ : Differentiable ℝ χ) {u : ℝ} (hu : 1/8 < u) :
    deriv (fun u : ℝ => (Real.sqrt (WwSm u))⁻¹ * χ (s * u)) u
      = -(1 / (2 * u * Real.sqrt u)) * χ (s * u) + (Real.sqrt u)⁻¹ * (deriv χ (s * u) * s) := by
  have hu0 : 0 < u := by linarith
  have hev : (fun u : ℝ => (Real.sqrt (WwSm u))⁻¹ * χ (s * u)) =ᶠ[𝓝 u]
      (fun u : ℝ => (Real.sqrt u)⁻¹ * χ (s * u)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    rw [WwSm_eq_self (le_of_lt hv)]
  rw [hev.deriv_eq]
  have hA : HasDerivAt (fun u : ℝ => (Real.sqrt u)⁻¹) (-(1 / (2 * u * Real.sqrt u))) u :=
    hasDerivAt_sqrt_inv hu0
  have hB : HasDerivAt (fun u : ℝ => χ (s * u)) (deriv χ (s * u) * s) u :=
    ((hχ (s*u)).hasDerivAt).comp u hasDerivAt_const_mul'
  exact (hA.mul hB).deriv

/-- Derivative value computation: `d/du (-(1/(2u√u))) = (3/4)(u²√u)⁻¹`. -/
lemma deriv_neg_inv_den {u : ℝ} (hu0 : 0 < u) :
    HasDerivAt (fun u : ℝ => -(1 / (2 * u * Real.sqrt u))) ((3/4) * (u * u * Real.sqrt u)⁻¹) u := by
  have hden : HasDerivAt (fun u : ℝ => 2 * u * Real.sqrt u) (2 * Real.sqrt u + 2 * u * (1/(2*Real.sqrt u))) u := by
    have h := ((hasDerivAt_id u).const_mul (2:ℝ)).mul (Real.hasDerivAt_sqrt (ne_of_gt hu0))
    have hfun : ((fun y : ℝ => 2 * id y) * fun x : ℝ => Real.sqrt x) = (fun y : ℝ => 2 * y * Real.sqrt y) := by
      funext y; simp only [Pi.mul_apply, id_eq, mul_assoc, mul_comm, mul_left_comm]
    rw [hfun] at h
    simpa using h
  have hinv : HasDerivAt (fun u : ℝ => (2 * u * Real.sqrt u)⁻¹) (-(2 * Real.sqrt u + 2 * u * (1/(2*Real.sqrt u))) / (2 * u * Real.sqrt u)^2) u :=
    hden.inv (by positivity)
  have hneg : HasDerivAt (fun u : ℝ => -((2 * u * Real.sqrt u)⁻¹)) (-(-(2 * Real.sqrt u + 2 * u * (1/(2*Real.sqrt u))) / (2 * u * Real.sqrt u)^2)) u :=
    hinv.neg
  have hev : (fun u : ℝ => -((2 * u * Real.sqrt u)⁻¹)) =ᶠ[𝓝 u] (fun u : ℝ => -(1 / (2 * u * Real.sqrt u))) := by
    filter_upwards with v
    rw [one_div]
  refine (hneg.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt (le_of_lt hu0)
  have hsp : Real.sqrt u ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hu0)
  field_simp
  nlinarith [hsq]

/-- Second derivative of the scaled amplitude. -/
lemma deriv2_amp {χ : ℝ → ℝ} (hχ : ContDiff ℝ 3 χ) {u : ℝ} (hu : 1/8 < u) :
    deriv (deriv (fun u : ℝ => (Real.sqrt (WwSm u))⁻¹ * χ (s * u))) u
      = (3 / 4) * (u * u * Real.sqrt u)⁻¹ * χ (s * u)
        - (u * Real.sqrt u)⁻¹ * (deriv χ (s * u) * s)
        + (Real.sqrt u)⁻¹ * (deriv (deriv χ) (s * u) * s ^ 2) := by
  have hu0 : 0 < u := by linarith
  have hd1 : Differentiable ℝ χ := hχ.differentiable (by norm_num)
  have hd2c : ContDiff ℝ 2 (deriv χ) := by fun_prop
  have hd2 : Differentiable ℝ (deriv χ) := hd2c.differentiable (by norm_num)
  have hderiv1 : deriv (fun u : ℝ => (Real.sqrt (WwSm u))⁻¹ * χ (s * u)) =ᶠ[𝓝 u]
      (fun u : ℝ => -(1 / (2 * u * Real.sqrt u)) * χ (s * u)
        + (Real.sqrt u)⁻¹ * (deriv χ (s * u) * s)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact deriv_amp hd1 hv
  rw [hderiv1.deriv_eq]
  have hC : HasDerivAt (fun u : ℝ => -(1 / (2 * u * Real.sqrt u))) ((3/4) * (u * u * Real.sqrt u)⁻¹) u :=
    deriv_neg_inv_den hu0
  have hD : HasDerivAt (fun u : ℝ => χ (s * u)) (deriv χ (s * u) * s) u :=
    ((hd1 (s*u)).hasDerivAt).comp u hasDerivAt_const_mul'
  have hE : HasDerivAt (fun u : ℝ => deriv χ (s * u)) (deriv (deriv χ) (s * u) * s) u :=
    ((hd2 (s*u)).hasDerivAt).comp u hasDerivAt_const_mul'
  have hF : HasDerivAt (fun u : ℝ => deriv χ (s * u) * s) (deriv (deriv χ) (s * u) * s * s) u := hE.mul_const s
  have hG : HasDerivAt (fun u : ℝ => (Real.sqrt u)⁻¹ * (deriv χ (s * u) * s))
      (-(1/(2*u*Real.sqrt u)) * (deriv χ (s * u) * s) + (Real.sqrt u)⁻¹ * (deriv (deriv χ) (s * u) * s * s)) u := by
    have h := (hasDerivAt_sqrt_inv hu0).mul hF
    have hfun : ((fun u : ℝ => (Real.sqrt u)⁻¹) * fun u : ℝ => deriv χ (s * u) * s)
        = (fun u : ℝ => (Real.sqrt u)⁻¹ * (deriv χ (s * u) * s)) := rfl
    rw [hfun] at h
    simpa using h
  have hsum : HasDerivAt (fun u : ℝ => -(1 / (2 * u * Real.sqrt u)) * χ (s * u) + (Real.sqrt u)⁻¹ * (deriv χ (s * u) * s))
      (((3/4) * (u * u * Real.sqrt u)⁻¹) * χ (s * u) + (-(1 / (2 * u * Real.sqrt u))) * (deriv χ (s * u) * s)
        + ((-(1/(2*u*Real.sqrt u)) * (deriv χ (s * u) * s) + (Real.sqrt u)⁻¹ * (deriv (deriv χ) (s * u) * s * s)))) u :=
    (hC.mul hD).add hG
  have hkey : ((3/4) * (u * u * Real.sqrt u)⁻¹) * χ (s * u) + (-(1 / (2 * u * Real.sqrt u))) * (deriv χ (s * u) * s)
        + ((-(1/(2*u*Real.sqrt u)) * (deriv χ (s * u) * s) + (Real.sqrt u)⁻¹ * (deriv (deriv χ) (s * u) * s * s)))
      = (3 / 4) * (u * u * Real.sqrt u)⁻¹ * χ (s * u)
        - (u * Real.sqrt u)⁻¹ * (deriv χ (s * u) * s)
        + (Real.sqrt u)⁻¹ * (deriv (deriv χ) (s * u) * s ^ 2) := by
    have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt (le_of_lt hu0)
    field_simp
    ring
  rw [← hkey]
  exact hsum.deriv

lemma abs_deriv_amp_le {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {K N s u : ℝ}
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    {u : ℝ} (hu : 1/8 < u) :
    |deriv (fun u : ℝ => (Real.sqrt (WwSm u))⁻¹ * χ (s * u)) u|
      ≤ (1/2) * (u * Real.sqrt u)⁻¹ + (Real.sqrt u)⁻¹ * (K / Real.sqrt N) * |s| := by
  have hu0 : 0 < u := by linarith
  rw [deriv_amp hχ hu]
  have h1 : |-(1 / (2 * u * Real.sqrt u)) * χ (s * u)| ≤ (1/2) * (u * Real.sqrt u)⁻¹ := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/(2*u*Real.sqrt u))]
    have hχu : |χ (s*u)| ≤ 1 := by
      rw [abs_of_nonneg (hχ0 (s*u)).1]; exact (hχ0 (s*u)).2
    calc (1 / (2 * u * Real.sqrt u)) * |χ (s * u)| ≤ (1 / (2 * u * Real.sqrt u)) * 1 :=
          mul_le_mul_of_nonneg_left hχu (by positivity)
      _ = (1/2) * (u * Real.sqrt u)⁻¹ := by rw [one_div]; ring
  have h2 : |(Real.sqrt u)⁻¹ * (deriv χ (s * u) * s)| ≤ (Real.sqrt u)⁻¹ * (K / Real.sqrt N) * |s| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt u)⁻¹)]
    have hb : |deriv χ (s*u)| ≤ K / Real.sqrt N := hbdd _
    have h3 : (Real.sqrt u)⁻¹ * (|deriv χ (s*u)| * |s|) ≤ (Real.sqrt u)⁻¹ * ((K/Real.sqrt N) * |s|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (abs_nonneg s)) (by positivity)
    calc (Real.sqrt u)⁻¹ * (|deriv χ (s * u)| * |s|) ≤ (Real.sqrt u)⁻¹ * ((K / Real.sqrt N) * |s|) := h3
      _ = (Real.sqrt u)⁻¹ * (K / Real.sqrt N) * |s| := by ring
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

lemma abs_deriv2_amp_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ 3 χ) {K N s u : ℝ}
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N)
    {u : ℝ} (hu : 1/8 < u) :
    |deriv (deriv (fun u : ℝ => (Real.sqrt (WwSm u))⁻¹ * χ (s * u))) u|
      ≤ (3/4) * (u * u * Real.sqrt u)⁻¹ + (u * Real.sqrt u)⁻¹ * (K / Real.sqrt N) * |s|
        + (Real.sqrt u)⁻¹ * (K / N) * s ^ 2 := by
  have hu0 : 0 < u := by linarith
  rw [deriv2_amp hχ hu]
  have hχu : |χ (s*u)| ≤ 1 := by rw [abs_of_nonneg (hχ0 (s*u)).1]; exact (hχ0 (s*u)).2
  have h1 : |(3/4) * (u * u * Real.sqrt u)⁻¹ * χ (s * u)| ≤ (3/4) * (u*u*Real.sqrt u)⁻¹ := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3/4) * (u*u*Real.sqrt u)⁻¹)]
    calc (3/4) * (u*u*Real.sqrt u)⁻¹ * |χ (s*u)| ≤ (3/4) * (u*u*Real.sqrt u)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hχu (by positivity)
      _ = (3/4) * (u*u*Real.sqrt u)⁻¹ := by ring
  have h2 : |(u * Real.sqrt u)⁻¹ * (deriv χ (s * u) * s)| ≤ (u * Real.sqrt u)⁻¹ * (K/Real.sqrt N) * |s| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (u*Real.sqrt u)⁻¹)]
    have hb : |deriv χ (s*u)| ≤ K / Real.sqrt N := hbdd _
    calc (u*Real.sqrt u)⁻¹ * (|deriv χ (s*u)| * |s|) ≤ (u*Real.sqrt u)⁻¹ * ((K/Real.sqrt N) * |s|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (abs_nonneg s)) (by positivity)
      _ = (u * Real.sqrt u)⁻¹ * (K / Real.sqrt N) * |s| := by ring
  have h3 : |(Real.sqrt u)⁻¹ * (deriv (deriv χ) (s * u) * s ^ 2)| ≤ (Real.sqrt u)⁻¹ * (K/N) * s^2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt u)⁻¹),
        abs_of_nonneg (sq_nonneg s)]
    have hb : |deriv (deriv χ) (s*u)| ≤ K / N := hdd _
    calc (Real.sqrt u)⁻¹ * (|deriv (deriv χ) (s*u)| * s^2) ≤ (Real.sqrt u)⁻¹ * ((K/N) * s^2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (sq_nonneg s)) (by positivity)
      _ = (Real.sqrt u)⁻¹ * (K/N) * s^2 := by ring
  have hsplit : |(3/4) * (u*u*Real.sqrt u)⁻¹ * χ (s*u) - (u*Real.sqrt u)⁻¹ * (deriv χ (s*u) * s)
      + (Real.sqrt u)⁻¹ * (deriv (deriv χ) (s*u) * s^2)|
      ≤ (3/4) * (u*u*Real.sqrt u)⁻¹ + (u*Real.sqrt u)⁻¹ * (K/Real.sqrt N) * |s|
        + (Real.sqrt u)⁻¹ * (K/N) * s^2 := by
    have h4 : |(3/4) * (u*u*Real.sqrt u)⁻¹ * χ (s * u) - (u * Real.sqrt u)⁻¹ * (deriv χ (s * u) * s)
        + (Real.sqrt u)⁻¹ * (deriv (deriv χ) (s * u) * s ^ 2)|
        ≤ |(3/4) * (u*u*Real.sqrt u)⁻¹ * χ (s*u)| + |(u*Real.sqrt u)⁻¹ * (deriv χ (s*u) * s)|
          + |(Real.sqrt u)⁻¹ * (deriv (deriv χ) (s*u) * s^2)| := abs_sub_add_le _ _ _
    linarith [h4, h1, h2, h3]
  exact hsplit


/-- The smoothed log-phase `τ log y - 2π m y`, written with the smooth logarithm. -/
def WwPhi (τ m : ℝ) : ℝ → ℝ := fun y => τ * WwLog y - 2 * Real.pi * m * y

lemma WwPhi_contDiff (τ m : ℝ) : ContDiff ℝ 3 (WwPhi τ m) := by
  unfold WwPhi
  exact (contDiff_const.mul WwLog_contDiff).sub ((contDiff_const.mul contDiff_const).mul contDiff_id)

lemma WwPhi_eventuallyEq {τ m y : ℝ} (hy : 1/8 < y) :
    WwPhi τ m =ᶠ[𝓝 y] (fun z => τ * Real.log z - 2 * Real.pi * m * z) := by
  filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
  unfold WwPhi
  rw [WwLog_eq_log (le_of_lt hz)]

lemma deriv_log_lin (τ m y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => τ * Real.log z - 2 * Real.pi * m * z) (τ * y⁻¹ - 2 * Real.pi * m) y := by
  have h1 : HasDerivAt (fun z : ℝ => Real.log z) y⁻¹ y := Real.hasDerivAt_log (ne_of_gt hy)
  have h2 : HasDerivAt (fun z : ℝ => τ * Real.log z) (τ * y⁻¹) y := HasDerivAt.const_mul τ h1
  have h3 : HasDerivAt (fun z : ℝ => 2 * Real.pi * m * z) (2 * Real.pi * m) y := by
    have h := (hasDerivAt_id y).const_mul (2 * Real.pi * m)
    have hfun : ((fun y : ℝ => 2 * Real.pi * m * id y)) = (fun z : ℝ => 2 * Real.pi * m * z) := by
      funext z; simp only [id_eq]
    rw [hfun] at h
    simpa using h
  have h4 : HasDerivAt (fun z : ℝ => τ * Real.log z - 2 * Real.pi * m * z) (τ * y⁻¹ - 2 * Real.pi * m) y := by
    have h := h2.sub h3
    have hfun : ((fun z : ℝ => τ * Real.log z) - fun z : ℝ => 2 * Real.pi * m * z)
        = (fun z : ℝ => τ * Real.log z - 2 * Real.pi * m * z) := rfl
    rw [hfun] at h
    simpa using h
  exact h4

lemma deriv_WwPhi {τ m y : ℝ} (hy : 1/8 < y) :
    deriv (WwPhi τ m) y = τ * y⁻¹ - 2 * Real.pi * m := by
  have hy0 : 0 < y := by linarith
  rw [(WwPhi_eventuallyEq (τ := τ) (m := m) hy).deriv_eq]
  exact (deriv_log_lin τ m y hy0).deriv

lemma deriv_deriv_WwPhi {τ m y : ℝ} (hy : 1/8 < y) :
    deriv (deriv (WwPhi τ m)) y = -τ * (y^2)⁻¹ := by
  have hy0 : 0 < y := by linarith
  have hev : deriv (WwPhi τ m) =ᶠ[𝓝 y] (fun z => τ * z⁻¹ - 2 * Real.pi * m) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact deriv_WwPhi hz
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun z : ℝ => z⁻¹) (-(y^2)⁻¹) y := hasDerivAt_inv (ne_of_gt hy0)
  have h2 : HasDerivAt (fun z : ℝ => τ * z⁻¹) (τ * (-(y^2)⁻¹)) y := HasDerivAt.const_mul τ h1
  have h3 : HasDerivAt (fun z : ℝ => τ * z⁻¹ - 2 * Real.pi * m) (τ * (-(y^2)⁻¹)) y := h2.sub_const _
  rw [h3.deriv]
  ring

lemma iteratedDeriv3_WwPhi {τ m y : ℝ} (hy : 1/8 < y) :
    iteratedDeriv 3 (WwPhi τ m) y = 2 * τ * (y^3)⁻¹ := by
  have hy0 : 0 < y := by linarith
  have hev : deriv (deriv (WwPhi τ m)) =ᶠ[𝓝 y] (fun z => -τ * (z^2)⁻¹) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact deriv_deriv_WwPhi hz
  have h1 : HasDerivAt (fun z : ℝ => (z^2)⁻¹) (-(2*y) / (y^2)^2) y := by
    have hsq : HasDerivAt (fun z : ℝ => z^2) (2*y) y := by
      have h := hasDerivAt_pow 2 y
      norm_num at h
      exact h
    exact hsq.inv (by positivity)
  have h2 : HasDerivAt (fun z : ℝ => -τ * (z^2)⁻¹) (-τ * (-(2*y) / (y^2)^2)) y :=
    HasDerivAt.const_mul (-τ) h1
  have h3 : HasDerivAt (fun z : ℝ => -τ * (z^2)⁻¹) (2 * τ * (y^3)⁻¹) y := by
    refine h2.congr_deriv ?_
    have hy2 : y ^ 2 ≠ 0 := by positivity
    field_simp
  have e : iteratedDeriv 3 (WwPhi τ m) y = deriv (deriv (deriv (WwPhi τ m))) y := by
    rw [show (3:ℕ) = 2 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_two_eq]
  rw [e, hev.deriv_eq]
  exact h3.deriv


/-- `WwI` as an integral of the smooth amplitude against the smooth phase. -/
lemma WwI_eq_integral {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} {τ : ℝ} {m : ℤ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0) :
    WwI χ τ m = ∫ y in ((N:ℝ) - Real.sqrt N)..((2*N:ℝ) + Real.sqrt N),
        (WwGs χ y : ℂ) * Complex.exp (Complex.I * (((WwPhi τ (m:ℝ) y) : ℝ) : ℂ)) := by
  unfold WwI
  set a : ℝ := (N:ℝ) - Real.sqrt N with hadef
  set b : ℝ := 2*(N:ℝ) + Real.sqrt N with hbdef
  have hN4 : (4:ℕ) ≤ N := hN
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN4
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have ha18 : 1/8 < a := by
    rw [hadef]; nlinarith [hsq, hsqn, hN4R]
  have hab : a ≤ b := by
    rw [hadef, hbdef]; nlinarith [hsq, hsqn, hN4R]
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem hy]
    have hay : a < y := hy.1
    have hay18 : 1/8 < y := lt_trans ha18 hay
    have h1 : WwSm y = y := WwSm_eq_self (le_of_lt hay18)
    have h2 : WwLog y = Real.log y := WwLog_eq_log (le_of_lt hay18)
    unfold WwF WwGs WwPhi
    rw [h1, h2]
    have hpair : Complex.I * (((τ * Real.log y - 2 * Real.pi * (m:ℝ) * y) : ℝ) : ℂ)
        = Complex.I * ((τ : ℂ) * (Real.log y : ℂ))
          + (-(2 * Real.pi * Complex.I) * ((m : ℝ) * y)) := by
      push_cast
      ring
    have hmain : ((Real.sqrt y)⁻¹ : ℂ) * Complex.exp (Complex.I * ((τ : ℂ) * (Real.log y : ℂ)))
          * (χ y : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I) * ((m : ℝ) * y))
        = (((Real.sqrt y)⁻¹ * χ y : ℝ) : ℂ)
          * Complex.exp (Complex.I * (((τ * Real.log y - 2 * Real.pi * (m:ℝ) * y) : ℝ) : ℂ)) := by
      rw [hpair, Complex.exp_add, Complex.ofReal_mul]
      simp only [mul_assoc, mul_comm, mul_left_comm]
      congr 1
      congr 1
      congr 1
      rw [Complex.ofReal_inv]
    exact hmain
  · rw [Set.indicator_of_notMem hy]
    unfold WwF
    rcases le_or_gt y a with hle | hgt
    · have hz := hχz y (Or.inl hle)
      rw [hz]
      simp only [Complex.ofReal_zero, mul_zero, zero_mul]
    · have hb : b < y := by
        by_contra hc
        push Not at hc
        exact hy ⟨hgt, hc⟩
      have hz := hχz y (Or.inr (le_of_lt hb))
      rw [hz]
      simp only [Complex.ofReal_zero, mul_zero, zero_mul]

/-- Pointwise bound for the smooth amplitude. -/
lemma abs_WwGs_le {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    {y : ℝ} (hy : (N:ℝ) - Real.sqrt N ≤ y) :
    |WwGs χ y| ≤ Real.sqrt (2/N) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hy2 : 1/8 < y := by
    have : (2:ℝ) ≤ (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
    linarith
  have hy0 : 0 < y := by linarith
  have hyN : (N:ℝ)/2 ≤ y := by nlinarith [hsq, hsqn, hN4R]
  rw [WwGs_eq (le_of_lt hy2), abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt y)⁻¹)]
  have hχy : |χ y| ≤ 1 := by rw [abs_of_nonneg (hχ0 y).1]; exact (hχ0 y).2
  have h2 : (1:ℝ)/y ≤ 2/N := by
    rw [div_le_div_iff₀ hy0 hNpos]
    linarith
  have h1 : (Real.sqrt y)⁻¹ = Real.sqrt (1/y) := by
    rw [← Real.sqrt_inv]; ring_nf
  calc (Real.sqrt y)⁻¹ * |χ y| = Real.sqrt (1/y) * |χ y| := by rw [h1]
    _ ≤ Real.sqrt (2/N) * 1 := mul_le_mul (Real.sqrt_le_sqrt h2) hχy (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt (2/N) := by ring

/-- Integral bound for the amplitude. -/
lemma integral_abs_WwGs_le {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) :
    ∫ y in ((N:ℝ) - Real.sqrt N)..((2*N:ℝ) + Real.sqrt N), |WwGs χ y| ≤ 6 * Real.sqrt N := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hab : (N:ℝ) - Real.sqrt N ≤ (2*N:ℝ) + Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  have hC : ∀ x ∈ Set.uIoc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      ‖|WwGs χ x|‖ ≤ Real.sqrt (2/N) := by
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    rw [Set.uIoc_of_le hab] at hx
    exact abs_WwGs_le hN hχ0 (le_of_lt hx.1)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hC
  rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg hab (fun x _ => abs_nonneg _))] at h
  have hlen : |((2*N:ℝ) + Real.sqrt N) - ((N:ℝ) - Real.sqrt N)| = (N:ℝ) + 2*Real.sqrt N := by
    rw [abs_of_nonneg (by linarith)]
    ring
  rw [hlen] at h
  refine le_trans h ?_
  have hs2 : Real.sqrt (2/N) = Real.sqrt 2 / Real.sqrt N := Real.sqrt_div (by norm_num) N
  rw [hs2]
  have h2 : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  rw [div_mul_eq_mul_div, div_le_iff₀ h2]
  have h3 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
  have h4 : Real.sqrt 2 * ((N:ℝ) + 2*Real.sqrt N) ≤ 2 * ((N:ℝ) + 2*Real.sqrt N) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  have h5 : 2 * ((N:ℝ) + 2*Real.sqrt N) ≤ 6 * (Real.sqrt N * Real.sqrt N) := by
    nlinarith [hsq, hsqn, hN4R]
  linarith [h4, h5]



/-- Second-derivative bound for the smoothed phase on `[N-√N, ∞)`. -/
lemma deriv_deriv_WwPhi_bound {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ) {m : ℤ} {y : ℝ}
    (hy : (N:ℝ) - Real.sqrt N ≤ y) :
    |deriv (deriv (WwPhi τ (m:ℝ))) y| ≤ 4 * τ / (N:ℝ)^2 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hy18 : 1/8 < y := by
    have : (2:ℝ) ≤ (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
    linarith
  have hy0 : 0 < y := by linarith
  have hyN : (N:ℝ)/2 ≤ y := by nlinarith [hsq, hsqn, hN4R]
  have h1 : (y^2)⁻¹ ≤ 4 / (N:ℝ)^2 := by
    have hy2 : ((N:ℝ)/2)^2 ≤ y^2 := pow_le_pow_left₀ (by positivity) hyN 2
    have h := (inv_le_inv₀ (by positivity : (0:ℝ) < y^2) (by positivity : (0:ℝ) < ((N:ℝ)/2)^2)).mpr hy2
    refine le_trans h ?_
    have he : (((N:ℝ)/2)^2) = (N:ℝ)^2 / 4 := by ring
    rw [he, inv_div]
  rw [deriv_deriv_WwPhi hy18]
  calc |-τ * (y^2)⁻¹| = τ * (y^2)⁻¹ := by
        rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < (y^2)⁻¹), abs_of_nonneg hτ]
    _ ≤ τ * (4 / (N:ℝ)^2) := mul_le_mul_of_nonneg_left h1 hτ
    _ = 4 * τ / (N:ℝ)^2 := by ring

/-- Third-derivative bound for the smoothed phase on `[N-√N, ∞)`. -/
lemma iteratedDeriv3_WwPhi_bound {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ) {m : ℤ} {y : ℝ}
    (hy : (N:ℝ) - Real.sqrt N ≤ y) :
    |iteratedDeriv 3 (WwPhi τ (m:ℝ)) y| ≤ 16 * τ / (N:ℝ)^3 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hy18 : 1/8 < y := by
    have : (2:ℝ) ≤ (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
    linarith
  have hyN : (N:ℝ)/2 ≤ y := by nlinarith [hsq, hsqn, hN4R]
  have h1 : (y^3)⁻¹ ≤ 8 / (N:ℝ)^3 := by
    have hy2 : ((N:ℝ)/2)^3 ≤ y^3 := pow_le_pow_left₀ (by positivity) hyN 3
    have h := (inv_le_inv₀ (by positivity : (0:ℝ) < y^3) (by positivity : (0:ℝ) < ((N:ℝ)/2)^3)).mpr hy2
    refine le_trans h ?_
    have he : (((N:ℝ)/2)^3) = (N:ℝ)^3 / 8 := by ring
    rw [he, inv_div]
  rw [iteratedDeriv3_WwPhi hy18]
  calc |2 * τ * (y^3)⁻¹| = 2 * τ * (y^3)⁻¹ := by
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (y^3)⁻¹),
          abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hτ]
    _ ≤ 2 * τ * (8 / (N:ℝ)^3) := by
        apply mul_le_mul_of_nonneg_left h1; positivity
    _ = 16 * τ / (N:ℝ)^3 := by ring


/-- **Second-order van der Corput bound for `WwI`** (the tail estimate). -/
lemma WwI_tail_bound {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    {τ : ℝ} {m : ℤ} {L I0 I1 I2 MN M3N : ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    (hL : 0 < L) (hMN : 0 ≤ MN) (hM3N : 0 ≤ M3N)
    (hmono : MonotoneOn (deriv (WwPhi τ (m:ℝ))) (Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N))
      ∨ AntitoneOn (deriv (WwPhi τ (m:ℝ))) (Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N)))
    (hbd : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      L ≤ |deriv (WwPhi τ (m:ℝ)) y|)
    (h2 : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      |deriv (deriv (WwPhi τ (m:ℝ))) y| ≤ MN)
    (h3 : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      |iteratedDeriv 3 (WwPhi τ (m:ℝ)) y| ≤ M3N)
    (hI0 : (∫ y in ((N:ℝ) - Real.sqrt N)..((2*N:ℝ) + Real.sqrt N), |WwGs χ y|) ≤ I0)
    (hI1 : (∫ y in ((N:ℝ) - Real.sqrt N)..((2*N:ℝ) + Real.sqrt N), |deriv (WwGs χ) y|) ≤ I1)
    (hI2 : (∫ y in ((N:ℝ) - Real.sqrt N)..((2*N:ℝ) + Real.sqrt N),
      |deriv (deriv (WwGs χ)) y|) ≤ I2) :
    ‖WwI χ τ m‖ ≤ 8 * (I2 + I1 * MN / L + I0 * M3N / L + I0 * MN ^ 2 / L ^ 2) / L ^ 2 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hab : (N:ℝ) - Real.sqrt N ≤ (2*N:ℝ) + Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  have hgs : ∀ x, x ∉ Set.Ioo ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N) → WwGs χ x = 0 := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    push Not at hx
    by_cases h1 : x ≤ (N:ℝ) - Real.sqrt N
    · have h0 : χ x = 0 := hχz x (Or.inl h1)
      rw [WwGs, h0, mul_zero]
    · push Not at h1
      have h2 : (2*N:ℝ) + Real.sqrt N ≤ x := hx h1
      have h0 : χ x = 0 := hχz x (Or.inr h2)
      rw [WwGs, h0, mul_zero]
  have hmain := Commons.Analysis.Oscillatory.norm_integral_exp_two_ibp
    (a := (N:ℝ) - Real.sqrt N) (b := (2*N:ℝ) + Real.sqrt N) (m := L) (M := MN) (M3 := M3N)
    hab hL (WwPhi_contDiff τ (m:ℝ)) hmono hbd h2 h3 (WwGs_contDiff hχd) hgs
  rw [WwI_eq_integral hN hχz]
  refine le_trans hmain ?_
  have hkey : (∫ x in ((N:ℝ) - Real.sqrt N)..((2*N:ℝ) + Real.sqrt N), |deriv (deriv (WwGs χ)) x|)
      + (∫ x in ((N:ℝ) - Real.sqrt N)..((2*N:ℝ) + Real.sqrt N), |deriv (WwGs χ) x|) * MN / L
      + (∫ x in ((N:ℝ) - Real.sqrt N)..((2*N:ℝ) + Real.sqrt N), |WwGs χ x|) * M3N / L
      + (∫ x in ((N:ℝ) - Real.sqrt N)..((2*N:ℝ) + Real.sqrt N), |WwGs χ x|) * MN ^ 2 / L ^ 2
      ≤ I2 + I1 * MN / L + I0 * M3N / L + I0 * MN ^ 2 / L ^ 2 :=
    add_le_add (add_le_add (add_le_add hI2
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hI1 hMN) hL.le))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hI0 hM3N) hL.le))
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hI0 (by positivity : (0:ℝ) ≤ MN^2))
        (by positivity))
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (by norm_num : (0:ℝ) ≤ 8))
    (by positivity)



lemma inv_sqrt_le {N : ℕ} (hN : 4 ≤ N) {y : ℝ} (hy : (N:ℝ)/2 ≤ y) :
    (Real.sqrt y)⁻¹ ≤ Real.sqrt 2 / Real.sqrt N := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hy0 : 0 < y := by linarith
  have h2 : y⁻¹ ≤ 2 / N := by
    rw [show y⁻¹ = (1:ℝ)/y from (one_div y).symm, div_le_div_iff₀ hy0 hNpos]
    linarith
  calc (Real.sqrt y)⁻¹ = Real.sqrt y⁻¹ := (Real.sqrt_inv y).symm
    _ ≤ Real.sqrt (2/N) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt 2 / Real.sqrt N := Real.sqrt_div (by norm_num) N

lemma six_y_sqrt_ge {N : ℕ} (hN : 4 ≤ N) {y : ℝ} (hy : (N:ℝ)/2 ≤ y) :
    (N:ℝ) ≤ 6 * (y * Real.sqrt y) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hy0 : 0 < y := by linarith
  have hy3 : ((N:ℝ)/2)^3 ≤ y^3 := pow_le_pow_left₀ (by positivity) hy 3
  have hsqy : (y * Real.sqrt y)^2 = y^3 := by rw [mul_pow, Real.sq_sqrt (le_of_lt hy0)]; ring
  have h2 : (N:ℝ)^2 ≤ (6 * (y * Real.sqrt y))^2 := by rw [mul_pow, hsqy]; nlinarith [hy3, hN4R]
  have h3 := (sq_le_sq.mp h2)
  rwa [abs_of_nonneg (le_of_lt hNpos), abs_of_nonneg (by positivity)] at h3

lemma inv_mul_sqrt_le {N : ℕ} (hN : 4 ≤ N) {y : ℝ} (hy : (N:ℝ)/2 ≤ y) :
    (y * Real.sqrt y)⁻¹ ≤ 6 / N := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hy0 : 0 < y := by linarith
  have h6 := six_y_sqrt_ge hN hy
  have hyy : (0:ℝ) < y * Real.sqrt y := by positivity
  have key : (y * Real.sqrt y)⁻¹ ≤ ((N:ℝ)/6)⁻¹ :=
    (inv_le_inv₀ hyy (by positivity : (0:ℝ) < (N:ℝ)/6)).mpr (by linarith)
  have hN6 : ((N:ℝ)/6)⁻¹ = 6/N := by field_simp
  rwa [hN6] at key

lemma two_div_sqrt_mul {N : ℝ} (hN : 0 < N) (K : ℝ) :
    (2 / Real.sqrt N) * (K / Real.sqrt N) = 2*K/N := by
  rw [div_mul_div_comm, ← sq, Real.sq_sqrt hN.le]

/-- Pointwise bound for the first derivative of the smooth amplitude. -/
lemma abs_deriv_WwGs_le_N {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {K : ℝ} (hK : 0 ≤ K)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N) {y : ℝ} (hy : (N:ℝ) - Real.sqrt N ≤ y) :
    |deriv (WwGs χ) y| ≤ 3 * (1 + K) / (N:ℝ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hyN : (N:ℝ)/2 ≤ y := by nlinarith [hsq, hsqn, hN4R]
  have hy18 : 1/8 < y := by linarith
  have hfun : WwGs χ = (fun u : ℝ => (Real.sqrt (WwSm u))⁻¹ * χ (1 * u)) := by
    funext u; rw [WwGs, one_mul]
  have hpt := abs_deriv_amp_le (χ := χ) (s := 1) (K := K) (N := (N:ℝ))
    (hχd.differentiable (by norm_num)) hχ0 hbdd (u := y) hy18
  simp only [abs_one, mul_one] at hpt
  rw [hfun]
  refine le_trans hpt ?_
  have hsx := inv_sqrt_le hN hyN
  have h1 : (1/2) * (y * Real.sqrt y)⁻¹ ≤ 3 / N := by
    have key := inv_mul_sqrt_le hN hyN
    calc (1/2) * (y * Real.sqrt y)⁻¹ ≤ (1/2) * (6/N) := mul_le_mul_of_nonneg_left key (by norm_num)
      _ = 3/N := by rw [div_eq_mul_inv]; ring
  have h2 : (Real.sqrt y)⁻¹ * (K / Real.sqrt N) ≤ 2 * K / N := by
    have hsx' : (Real.sqrt y)⁻¹ ≤ 2 / Real.sqrt N := by
      refine le_trans hsx ?_
      have h : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      exact div_le_div_of_nonneg_right h (by positivity)
    have hstep := mul_le_mul_of_nonneg_right hsx' (by positivity : (0:ℝ) ≤ K / Real.sqrt N)
    rw [two_div_sqrt_mul hNpos K] at hstep
    exact hstep
  have hle : (3 + 2*K)/N ≤ 3*(1+K)/N := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  calc (1/2) * (y * Real.sqrt y)⁻¹ + (Real.sqrt y)⁻¹ * (K / Real.sqrt N) ≤ 3/N + 2*K/N :=
        add_le_add h1 h2
    _ = (3 + 2*K)/N := by rw [div_eq_mul_inv]; ring
    _ ≤ 3*(1+K)/N := hle


/-- **Integral bound `I₁`.** -/
lemma integral_abs_deriv_WwGs_le {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {K : ℝ} (hK : 0 ≤ K)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N) :
    ∫ y in ((N:ℝ) - Real.sqrt N)..((2*N:ℝ) + Real.sqrt N), |deriv (WwGs χ) y| ≤ 10 * (1 + K) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hab : (N:ℝ) - Real.sqrt N ≤ (2*N:ℝ) + Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  have hC : ∀ x ∈ Set.uIoc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      ‖|deriv (WwGs χ) x|‖ ≤ 3 * (1 + K) / N := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact abs_deriv_WwGs_le_N hN hχd hχ0 hK hbdd (le_of_lt hx.1)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hC
  rw [Real.norm_eq_abs, abs_of_nonneg
      (intervalIntegral.integral_nonneg hab (fun x _ => abs_nonneg _))] at h
  have hlen : |((2*N:ℝ) + Real.sqrt N) - ((N:ℝ) - Real.sqrt N)| = (N:ℝ) + 2*Real.sqrt N := by
    rw [abs_of_nonneg (by linarith)]; ring
  rw [hlen] at h
  refine le_trans h ?_
  have hfin : (3 * (1 + K) / N) * ((N:ℝ) + 2*Real.sqrt N) ≤ 10 * (1 + K) := by
    have hK1 : (0:ℝ) ≤ 1 + K := by linarith
    have h6 : 6 * Real.sqrt N ≤ 7 * N := by nlinarith [hsqn, hsq, hN4R]
    rw [show (3 * (1 + K) / N) * ((N:ℝ) + 2*Real.sqrt N)
        = 3*(1+K)*((N:ℝ) + 2*Real.sqrt N)/N by ring]
    rw [div_le_iff₀ hNpos]
    nlinarith [hsqn, hsq, hN4R, hK1, mul_le_mul_of_nonneg_left h6 hK1]
  exact hfin


/-- Pointwise bound for the second derivative of the smooth amplitude. -/
lemma abs_deriv2_WwGs_le_N {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {K : ℝ} (hK : 0 ≤ K)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N) {y : ℝ} (hy : (N:ℝ) - Real.sqrt N ≤ y) :
    |deriv (deriv (WwGs χ)) y| ≤ 8 * (1 + K) / ((N:ℝ) * Real.sqrt N) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hyN : (N:ℝ)/2 ≤ y := by nlinarith [hsq, hsqn, hN4R]
  have hy0 : 0 < y := by linarith
  have hy18 : 1/8 < y := by linarith
  have hsx := inv_sqrt_le hN hyN
  have hfun : WwGs χ = (fun u : ℝ => (Real.sqrt (WwSm u))⁻¹ * χ (1 * u)) := by
    funext u; rw [WwGs, one_mul]
  have hpt := abs_deriv2_amp_le (χ := χ) (s := 1) (K := K) (N := (N:ℝ)) hχd hχ0 hbdd hdd
    (u := y) hy18
  simp only [abs_one, mul_one, one_pow] at hpt
  rw [hfun]
  refine le_trans hpt ?_
  have hden : (0:ℝ) < (N:ℝ) * Real.sqrt N := by positivity
  have t1 : (3/4) * (y * y * Real.sqrt y)⁻¹ ≤ 2 / ((N:ℝ) * Real.sqrt N) := by
    have hy2 : ((N:ℝ)/2)^2 ≤ y^2 := pow_le_pow_left₀ (by positivity) hyN 2
    have h2 : (y^2)⁻¹ ≤ 4 / (N:ℝ)^2 := by
      have h := (inv_le_inv₀ (by positivity : (0:ℝ) < y^2)
        (by positivity : (0:ℝ) < ((N:ℝ)/2)^2)).mpr hy2
      refine le_trans h ?_
      have he : (((N:ℝ)/2)^2) = (N:ℝ)^2 / 4 := by ring
      rw [he, inv_div]
    have h3 : (y * y * Real.sqrt y)⁻¹ ≤ (4/(N:ℝ)^2) * (Real.sqrt 2 / Real.sqrt N) := by
      rw [show (y * y * Real.sqrt y)⁻¹ = (y^2)⁻¹ * (Real.sqrt y)⁻¹ by
        rw [mul_inv]; congr 1; ring]
      exact mul_le_mul h2 hsx (by positivity) (by positivity)
    refine le_trans (mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 3/4)) ?_
    rw [show (3/4) * ((4/(N:ℝ)^2) * (Real.sqrt 2 / Real.sqrt N))
        = 3 * Real.sqrt 2 / ((N:ℝ)^2 * Real.sqrt N) by field_simp; try ring]
    rw [div_le_div_iff₀ (by positivity) hden]
    have h2N : 3 * Real.sqrt 2 ≤ 2 * N := by
      nlinarith [hsq, hsqn, hN4R, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    nlinarith [mul_le_mul_of_nonneg_right h2N (by positivity : (0:ℝ) ≤ (N:ℝ) * Real.sqrt N)]
  have t2 : (y * Real.sqrt y)⁻¹ * (K / Real.sqrt N) ≤ 6 * K / ((N:ℝ) * Real.sqrt N) := by
    have hb := inv_mul_sqrt_le hN hyN
    have hstep : (y * Real.sqrt y)⁻¹ * (K / Real.sqrt N) ≤ (6/N) * (K / Real.sqrt N) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    rw [show (6/N) * (K / Real.sqrt N) = 6 * K / (N * Real.sqrt N) by field_simp; try ring]
  have t3 : (Real.sqrt y)⁻¹ * (K / N) ≤ 2 * K / ((N:ℝ) * Real.sqrt N) := by
    have hstep : (Real.sqrt y)⁻¹ * (K / N) ≤ (Real.sqrt 2 / Real.sqrt N) * (K / N) :=
      mul_le_mul_of_nonneg_right hsx (by positivity)
    refine le_trans hstep ?_
    rw [show (Real.sqrt 2 / Real.sqrt N) * (K / N) = Real.sqrt 2 * K / (N * Real.sqrt N) by
      field_simp; try ring]
    have h2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hK) (by positivity)
  have hcomb : 2 / ((N:ℝ) * Real.sqrt N) + 6 * K / ((N:ℝ) * Real.sqrt N)
      + 2 * K / ((N:ℝ) * Real.sqrt N) ≤ 8 * (1 + K) / ((N:ℝ) * Real.sqrt N) := by
    rw [← add_div, ← add_div, div_le_div_iff₀ (by positivity) hden]
    nlinarith [hsqn, hN4R, hK]
  calc (3/4) * (y * y * Real.sqrt y)⁻¹ + (y * Real.sqrt y)⁻¹ * (K / Real.sqrt N)
        + (Real.sqrt y)⁻¹ * (K / N)
      ≤ 2 / ((N:ℝ) * Real.sqrt N) + 6 * K / ((N:ℝ) * Real.sqrt N) + 2 * K / ((N:ℝ) * Real.sqrt N) :=
        add_le_add (add_le_add t1 t2) t3
    _ ≤ 8 * (1 + K) / ((N:ℝ) * Real.sqrt N) := hcomb

/-- **Integral bound `I₂`.** -/
lemma integral_abs_deriv2_WwGs_le {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {K : ℝ} (hK : 0 ≤ K)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N) :
    ∫ y in ((N:ℝ) - Real.sqrt N)..((2*N:ℝ) + Real.sqrt N), |deriv (deriv (WwGs χ)) y|
      ≤ 25 * (1 + K) / Real.sqrt N := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hab : (N:ℝ) - Real.sqrt N ≤ (2*N:ℝ) + Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  have hC : ∀ x ∈ Set.uIoc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      ‖|deriv (deriv (WwGs χ)) x|‖ ≤ 8 * (1 + K) / ((N:ℝ) * Real.sqrt N) := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact abs_deriv2_WwGs_le_N hN hχd hχ0 hK hbdd hdd (le_of_lt hx.1)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hC
  rw [Real.norm_eq_abs, abs_of_nonneg
      (intervalIntegral.integral_nonneg hab (fun x _ => abs_nonneg _))] at h
  have hlen : |((2*N:ℝ) + Real.sqrt N) - ((N:ℝ) - Real.sqrt N)| = (N:ℝ) + 2*Real.sqrt N := by
    rw [abs_of_nonneg (by linarith)]; ring
  rw [hlen] at h
  refine le_trans h ?_
  have hfin : (8 * (1 + K) / ((N:ℝ) * Real.sqrt N)) * ((N:ℝ) + 2*Real.sqrt N)
      ≤ 25 * (1 + K) / Real.sqrt N := by
    have hK1 : (0:ℝ) ≤ 1 + K := by linarith
    have h6 : 2 * Real.sqrt N ≤ N := by nlinarith [hsqn, hsq, hN4R]
    rw [show (8 * (1 + K) / ((N:ℝ) * Real.sqrt N)) * ((N:ℝ) + 2*Real.sqrt N)
        = 8*(1+K)*((N:ℝ) + 2*Real.sqrt N)/(N * Real.sqrt N) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsqn, hsq, hN4R, hK1, mul_le_mul_of_nonneg_left h6 hK1,
      mul_le_mul_of_nonneg_left hK1 (le_of_lt hNpos)]
  exact hfin


/-- The phase derivative in explicit form. -/
lemma deriv_WwPhi_eq {τ y : ℝ} {m : ℝ} (hy : 1/8 < y) :
    deriv (WwPhi τ m) y = τ / y - 2 * Real.pi * m := by
  rw [deriv_WwPhi hy]; ring

/-- `deriv Φ` is antitone on the support interval (`τ ≥ 0`). -/
lemma antitone_deriv_WwPhi {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ) (m : ℝ) :
    AntitoneOn (deriv (WwPhi τ m)) (Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N)) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have ha2 : (2:ℝ) ≤ (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  intro x hx y hy hxy
  have hx18 : 1/8 < x := by linarith [hx.1]
  have hy18 : 1/8 < y := by linarith [hy.1]
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  rw [deriv_WwPhi_eq hx18, deriv_WwPhi_eq hy18]
  have hinv : y⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hy0 hx0).mpr hxy
  have h2 : τ / y ≤ τ / x := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hτ
  linarith

/-- Left-tail lower bound for the phase derivative: for `m ≤ 0` it is at least
`τ/(2N+√N) + 2π|m|` on the support. -/
lemma deriv_WwPhi_nonpos_lower {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 ≤ τ) {m : ℤ} (hm : m ≤ 0)
    {y : ℝ} (hy : y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N)) :
    τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)| ≤ |deriv (WwPhi τ (m:ℝ)) y| := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have ha2 : (2:ℝ) ≤ (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  have hy18 : 1/8 < y := by linarith [hy.1]
  have hy0 : 0 < y := by linarith
  rw [deriv_WwPhi_eq hy18]
  have hmR : (m:ℝ) ≤ 0 := by exact_mod_cast hm
  have habs : |τ / y - 2 * Real.pi * (m:ℝ)| = τ / y - 2 * Real.pi * (m:ℝ) := by
    apply abs_of_nonneg
    have h1 : (0:ℝ) ≤ τ / y := div_nonneg hτ (le_of_lt hy0)
    nlinarith [h1, hmR, Real.pi_pos]
  rw [habs]
  have hinv : ((2*N:ℝ) + Real.sqrt N)⁻¹ ≤ y⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr hy.2
  have h1 : τ / ((2*N:ℝ) + Real.sqrt N) ≤ τ / y := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hτ
  have h2 : 2 * Real.pi * |(m:ℝ)| = -2 * Real.pi * (m:ℝ) := by
    rw [abs_of_nonpos hmR]; ring
  linarith [h1, h2.le, h2.ge]


/-- Concrete bound for `WwI` on the left tail (`m ≤ 0`), from `WwI_tail_bound`. -/
lemma WwI_nonpos_bound {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N) {m : ℤ} (hm : m ≤ 0) :
    ‖WwI χ τ m‖ ≤ 8 * (25*(1+K)/Real.sqrt N
        + 10*(1+K) * (4*τ/(N:ℝ)^2) / (τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)|)
        + 6*Real.sqrt N * (16*τ/(N:ℝ)^3) / (τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)|)
        + 6*Real.sqrt N * ((4*τ/(N:ℝ)^2)^2)
            / (τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)|)^2)
      / (τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)|)^2 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 < τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)| := by positivity
  have hmn : (0:ℝ) ≤ 4*τ/(N:ℝ)^2 := by positivity
  have hm3 : (0:ℝ) ≤ 16*τ/(N:ℝ)^3 := by positivity
  have hmono : MonotoneOn (deriv (WwPhi τ (m:ℝ))) (Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N))
      ∨ AntitoneOn (deriv (WwPhi τ (m:ℝ))) (Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N)) :=
    Or.inr (antitone_deriv_WwPhi hN hτ.le (m:ℝ))
  have hbd : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)| ≤ |deriv (WwPhi τ (m:ℝ)) y| :=
    fun y hy => deriv_WwPhi_nonpos_lower hN hτ.le hm hy
  have h2 : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      |deriv (deriv (WwPhi τ (m:ℝ))) y| ≤ 4*τ/(N:ℝ)^2 :=
    fun y hy => deriv_deriv_WwPhi_bound hN hτ.le hy.1
  have h3 : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      |iteratedDeriv 3 (WwPhi τ (m:ℝ)) y| ≤ 16*τ/(N:ℝ)^3 :=
    fun y hy => iteratedDeriv3_WwPhi_bound hN hτ.le hy.1
  exact WwI_tail_bound hN hχd hχz hL hmn hm3 hmono hbd h2 h3
    (integral_abs_WwGs_le hN hχ0)
    (integral_abs_deriv_WwGs_le hN hχd hχ0 hK hbdd)
    (integral_abs_deriv2_WwGs_le hN hχd hχ0 hK hbdd hdd)








/-- Rearranging a sum of quotients into inverse powers (the `e` step of the finite chunk). -/
lemma div_pow_rearrange {A B C D L : ℝ} (hL : L ≠ 0) :
    8 * (A + B / L + C / L + D / L ^ 2) / L ^ 2
      = 8 * (A * (1 / L) ^ 2 + B * (1 / L) ^ 3 + C * (1 / L) ^ 3
          + D * (1 / L) ^ 4) := by
  field_simp
  try ring

/-- The four monomial comparisons of the finite chunk. -/
lemma sqrt_monomial_four {N : ℕ} (hN : 4 ≤ N) {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ)
    (hNτ : (N : ℝ) ≤ τ) :
    225 * (1 + K) * (N : ℝ) ^ 2 * τ ≤ 6000 * (1 + K) * (N : ℝ) * (Real.sqrt N * τ ^ 2)
    ∧ 1080 * (1 + K) * (N : ℝ) * τ ≤ 6000 * (1 + K) * (N : ℝ) * τ ^ 2
    ∧ 2592 * Real.sqrt N * τ ≤ 6000 * (1 + K) * (N : ℝ) * τ ^ 2
    ∧ 7776 * Real.sqrt N * τ ≤ 6000 * (1 + K) * (N : ℝ) * τ ^ 2 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hK1 : (0:ℝ) ≤ 1 + K := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hbase : 225*(N:ℝ) ≤ 6000*Real.sqrt N*τ := by
      have h1 : 225*(N:ℝ) ≤ 6000*Real.sqrt N*(N:ℝ) := by nlinarith [hsqn, hsq, hN4R]
      calc 225*(N:ℝ) ≤ 6000*Real.sqrt N*(N:ℝ) := h1
        _ ≤ 6000*Real.sqrt N*τ := mul_le_mul_of_nonneg_left hNτ (by positivity)
    calc 225*(1+K)*(N:ℝ)^2*τ = (225*(N:ℝ))*((1+K)*(N:ℝ)*τ) := by ring
      _ ≤ (6000*Real.sqrt N*τ)*((1+K)*(N:ℝ)*τ) :=
          mul_le_mul_of_nonneg_right hbase (by positivity)
      _ = 6000*(1+K)*(N:ℝ)*(Real.sqrt N*τ^2) := by ring
  · have hbase : (1080:ℝ) ≤ 6000*τ := by nlinarith [hτ]
    calc 1080*(1+K)*(N:ℝ)*τ = 1080*((1+K)*(N:ℝ)*τ) := by ring
      _ ≤ (6000*τ)*((1+K)*(N:ℝ)*τ) := mul_le_mul_of_nonneg_right hbase (by positivity)
      _ = 6000*(1+K)*(N:ℝ)*τ^2 := by ring
  · have hbase : 2592*Real.sqrt N ≤ 6000*(1+K)*(N:ℝ)*τ := by
      have h1 : 2592*Real.sqrt N ≤ 6000*(N:ℝ) := by nlinarith [hsqn, hsq, hN4R]
      have h3 : (1:ℝ) ≤ (1+K)*τ := by nlinarith [hK1, hτ]
      calc 2592*Real.sqrt N ≤ 6000*(N:ℝ) := h1
        _ = 6000*(N:ℝ)*1 := by ring
        _ ≤ 6000*(N:ℝ)*((1+K)*τ) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 6000*(1+K)*(N:ℝ)*τ := by ring
    calc 2592*Real.sqrt N*τ = (2592*Real.sqrt N)*τ := by ring
      _ ≤ (6000*(1+K)*(N:ℝ)*τ)*τ := mul_le_mul_of_nonneg_right hbase hτ.le
      _ = 6000*(1+K)*(N:ℝ)*τ^2 := by ring
  · have hbase : 7776*Real.sqrt N ≤ 6000*(1+K)*(N:ℝ)*τ := by
      have h1 : 7776*Real.sqrt N ≤ 6000*(N:ℝ) := by nlinarith [hsqn, hsq, hN4R]
      have h3 : (1:ℝ) ≤ (1+K)*τ := by nlinarith [hK1, hτ]
      calc 7776*Real.sqrt N ≤ 6000*(N:ℝ) := h1
        _ = 6000*(N:ℝ)*1 := by ring
        _ ≤ 6000*(N:ℝ)*((1+K)*τ) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 6000*(1+K)*(N:ℝ)*τ := by ring
    calc 7776*Real.sqrt N*τ = (7776*Real.sqrt N)*τ := by ring
      _ ≤ (6000*(1+K)*(N:ℝ)*τ)*τ := mul_le_mul_of_nonneg_right hbase hτ.le
      _ = 6000*(1+K)*(N:ℝ)*τ^2 := by ring




/-- Finite chunk of the left tail: `-M₀ ≤ m ≤ 0` with `M₀ = ⌈τ/(2πN)⌉`. -/
lemma WwI_nonpos_finite_sum {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hNτ : (N:ℝ) ≤ τ)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N) :
    ∑ m ∈ Finset.Icc (-(Nat.ceil (τ / (2 * Real.pi * (N:ℝ))) : ℤ)) 0, ‖WwI χ τ m‖
      ≤ 500000 * (1 + K) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hK1 : (0:ℝ) ≤ 1 + K := by linarith
  have hL3 : ∀ m : ℤ, τ/(3*N) ≤ τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)| := by
    intro m
    have h2 : τ/(3*N) ≤ τ/((2*N:ℝ) + Real.sqrt N) := by
      apply div_le_div_of_nonneg_left hτ.le (by positivity)
      nlinarith [hsq, hsqn, hN4R]
    have h3 : (0:ℝ) ≤ 2*Real.pi*|(m:ℝ)| := by positivity
    linarith
  have hLpos : ∀ m : ℤ, 0 < τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)| :=
    fun m => lt_of_lt_of_le (by positivity : (0:ℝ) < τ/(3*N)) (hL3 m)
  have hL1 : ∀ m : ℤ, 1 / (τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)|) ≤ 3*N/τ := by
    intro m
    rw [div_le_div_iff₀ (hLpos m) hτ]
    have h := mul_le_mul_of_nonneg_right (hL3 m) (by positivity : (0:ℝ) ≤ 3*N)
    have hτeq : τ/(3*N) * (3*N) = τ := div_mul_cancel₀ τ (by positivity : (3:ℝ)*N ≠ 0)
    rw [hτeq] at h
    linarith
  have hterm : ∀ m ∈ Finset.Icc (-(Nat.ceil (τ / (2 * Real.pi * (N:ℝ))) : ℤ)) 0,
      ‖WwI χ τ m‖ ≤ 200000 * (1 + K) * N / τ := by
    intro m hm
    have hm0 : m ≤ 0 := (Finset.mem_Icc.mp hm).2
    have hb := WwI_nonpos_bound hN hχd hχ0 hχz hK hτ hbdd hdd hm0
    set L : ℝ := τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)| with hLdef
    have hLp : 0 < L := hLpos m
    have hL1' : 1/L ≤ 3*N/τ := hL1 m
    have h2 : (1/L)^2 ≤ (3*N/τ)^2 := pow_le_pow_left₀ (by positivity) hL1' 2
    have h3 : (1/L)^3 ≤ (3*N/τ)^3 := pow_le_pow_left₀ (by positivity) hL1' 3
    have h4 : (1/L)^4 ≤ (3*N/τ)^4 := pow_le_pow_left₀ (by positivity) hL1' 4
    rw [hLdef] at hb
    refine le_trans hb ?_
    have e : 8 * (25*(1+K)/Real.sqrt N
          + 10*(1+K) * (4*τ/(N:ℝ)^2) / L
          + 6*Real.sqrt N * (16*τ/(N:ℝ)^3) / L
          + 6*Real.sqrt N * ((4*τ/(N:ℝ)^2)^2) / L^2) / L^2
        = 8 * (25*(1+K)/Real.sqrt N * (1/L)^2
          + 10*(1+K) * (4*τ/(N:ℝ)^2) * (1/L)^3
          + 6*Real.sqrt N * (16*τ/(N:ℝ)^3) * (1/L)^3
          + 6*Real.sqrt N * ((4*τ/(N:ℝ)^2)^2) * (1/L)^4) :=
      div_pow_rearrange (A := 25*(1+K)/Real.sqrt N)
        (B := 10*(1+K) * (4*τ/(N:ℝ)^2)) (C := 6*Real.sqrt N * (16*τ/(N:ℝ)^3))
        (D := 6*Real.sqrt N * ((4*τ/(N:ℝ)^2)^2)) (L := L) (ne_of_gt hLp)
    rw [e]
    have hs1 : 25*(1+K)/Real.sqrt N * (1/L)^2 ≤ 6000*(1+K)*N/τ := by
      refine le_trans (mul_le_mul_of_nonneg_left h2 (by positivity)) ?_
      rw [show 25*(1+K)/Real.sqrt N * (3*N/τ)^2
          = 225*(1+K)*N^2/(Real.sqrt N * τ^2) by field_simp; try ring]
      rw [div_le_div_iff₀ (by positivity) hτ]
      exact (sqrt_monomial_four hN hK hτ hNτ).1
    have hs2 : 10*(1+K) * (4*τ/(N:ℝ)^2) * (1/L)^3 ≤ 6000*(1+K)*N/τ := by
      refine le_trans (mul_le_mul_of_nonneg_left h3 (by positivity)) ?_
      rw [show 10*(1+K) * (4*τ/(N:ℝ)^2) * (3*N/τ)^3 = 1080*(1+K)*N/τ^2 by
        field_simp; try ring]
      rw [div_le_div_iff₀ (by positivity) hτ]
      exact (sqrt_monomial_four hN hK hτ hNτ).2.1
    have hs3 : 6*Real.sqrt N * (16*τ/(N:ℝ)^3) * (1/L)^3 ≤ 6000*(1+K)*N/τ := by
      refine le_trans (mul_le_mul_of_nonneg_left h3 (by positivity)) ?_
      rw [show 6*Real.sqrt N * (16*τ/(N:ℝ)^3) * (3*N/τ)^3 = 2592*Real.sqrt N/τ^2 by
        field_simp; try ring]
      rw [div_le_div_iff₀ (by positivity) hτ]
      exact (sqrt_monomial_four hN hK hτ hNτ).2.2.1
    have hs4 : 6*Real.sqrt N * ((4*τ/(N:ℝ)^2)^2) * (1/L)^4 ≤ 6000*(1+K)*N/τ := by
      refine le_trans (mul_le_mul_of_nonneg_left h4 (by positivity)) ?_
      rw [show 6*Real.sqrt N * ((4*τ/(N:ℝ)^2)^2) * (3*N/τ)^4 = 7776*Real.sqrt N/τ^2 by
        field_simp; try ring]
      rw [div_le_div_iff₀ (by positivity) hτ]
      exact (sqrt_monomial_four hN hK hτ hNτ).2.2.2
    have hsum : 25*(1+K)/Real.sqrt N * (1/L)^2
          + 10*(1+K) * (4*τ/(N:ℝ)^2) * (1/L)^3
          + 6*Real.sqrt N * (16*τ/(N:ℝ)^3) * (1/L)^3
          + 6*Real.sqrt N * ((4*τ/(N:ℝ)^2)^2) * (1/L)^4
        ≤ 4 * (6000*(1+K)*N/τ) := by
      rw [show 4 * (6000*(1+K)*N/τ) = (6000*(1+K)*N/τ) + (6000*(1+K)*N/τ)
            + (6000*(1+K)*N/τ) + (6000*(1+K)*N/τ) by ring]
      exact add_le_add (add_le_add (add_le_add hs1 hs2) hs3) hs4
    have hnn : (0:ℝ) ≤ (1+K)*N/τ := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ) ≤ 8)) ?_
    have hA : 8 * (4 * (6000*(1+K)*N/τ)) = 192000 * ((1+K)*N/τ) := by ring
    have hB : 200000 * (1 + K) * N / τ = 200000 * ((1+K)*N/τ) := by ring
    rw [hA, hB]
    exact mul_le_mul_of_nonneg_right (by norm_num : (192000:ℝ) ≤ 200000) hnn
  calc ∑ m ∈ Finset.Icc (-(Nat.ceil (τ / (2 * Real.pi * (N:ℝ))) : ℤ)) 0, ‖WwI χ τ m‖
      ≤ ∑ m ∈ Finset.Icc (-(Nat.ceil (τ / (2 * Real.pi * (N:ℝ))) : ℤ)) 0,
          (200000 * (1 + K) * N / τ) := Finset.sum_le_sum hterm
    _ = ((Finset.Icc (-(Nat.ceil (τ / (2 * Real.pi * (N:ℝ))) : ℤ)) 0).card : ℝ)
          * (200000 * (1 + K) * N / τ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Nat.ceil (τ / (2 * Real.pi * (N:ℝ))) : ℝ) + 1) * (200000 * (1 + K) * N / τ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [Int.card_Icc]
        have hcard : ((0 : ℤ) + 1 - (-(Nat.ceil (τ / (2 * Real.pi * (N:ℝ))) : ℤ))).toNat
            = Nat.ceil (τ / (2 * Real.pi * (N:ℝ))) + 1 := by omega
        rw [hcard]
        push_cast
        linarith
    _ ≤ 500000 * (1 + K) := by
        have hM : (Nat.ceil (τ / (2 * Real.pi * (N:ℝ))) : ℝ) + 1 ≤ τ / (2 * Real.pi * (N:ℝ)) + 2 := by
          have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ τ / (2 * Real.pi * (N:ℝ)) by positivity)
          linarith
        refine le_trans (mul_le_mul_of_nonneg_right hM (by positivity)) ?_
        have he : (τ / (2 * Real.pi * (N:ℝ)) + 2) * (200000 * (1 + K) * N / τ)
            = 200000*(1+K)/(2*Real.pi) + 400000*(1+K)*N/τ := by
          field_simp
          ring
        rw [he]
        have hpi : (6:ℝ) ≤ 2*Real.pi := by nlinarith [Real.pi_gt_three]
        have h1 : 200000*(1+K)/(2*Real.pi) ≤ (100000/3)*(1+K) := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)]
          nlinarith [hK1, hpi]
        have h2 : 400000*(1+K)*N/τ ≤ 400000*(1+K) := by
          rw [div_le_iff₀ hτ]
          exact mul_le_mul_of_nonneg_left hNτ (mul_nonneg (by norm_num : (0:ℝ) ≤ 400000) hK1)
        have h3 : ((100000/3 : ℝ) + 400000)*(1+K) ≤ 500000*(1+K) :=
          mul_le_mul_of_nonneg_right (by norm_num) hK1
        linarith [h1, h2, h3]


/-! ## Log-phase primitive bounds (used for the tail estimates)

The classical bounds for `∫ e^{i t (log s - s)}` over an interval that does **not**
contain the stationary point `s = 1`: the trivial length bound, the "harmonic" bound
`1/(t·dist)` and the Fresnel/half-line bound `1/√t`. -/

/-- Harmonic primitive bound on an interval strictly left of the stationary point. -/
lemma logPhasePrim_left {t p q Y : ℝ} (ht : 4 ≤ t) (hp : 1/4 ≤ p) (hpq : p ≤ q) (hq : q < 1)
    (hY : Y ∈ Set.Icc p q) :
    ‖∫ s in p..Y, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
      ≤ 24 / (t * (1 - q)) := by
  have ht1 : (1:ℝ) ≤ t := by linarith
  have hpY : p ≤ Y := hY.1
  have hYq : Y ≤ q := hY.2
  have hY1 : Y < 1 := lt_of_le_of_lt hYq hq
  have h := Commons.Analysis.StationaryPhase.log_phase_prim_left_general t p Y ht1
    (by linarith) hpY hY1
  have h1 : ‖∫ s in p..Y, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
      ≤ 24 / (t * (1 - Y)) := le_trans h (min_le_right _ _)
  have h2 : 1 - q ≤ 1 - Y := by linarith
  have h3 : t * (1 - q) ≤ t * (1 - Y) := mul_le_mul_of_nonneg_left h2 (by linarith)
  have h4 : (0:ℝ) < t * (1 - q) := by
    have : (0:ℝ) < 1 - q := by linarith
    positivity
  exact le_trans h1 (div_le_div_of_nonneg_left (by norm_num) h4 h3)

/-- Fresnel (half-line) primitive bound on an interval left of the stationary point. -/
lemma logPhasePrim_left_fresnel :
    ∃ C : ℝ, 0 < C ∧ ∀ {t p q Y : ℝ}, 4 ≤ t → 1/4 ≤ p → p ≤ q → q ≤ 1 →
      Y ∈ Set.Icc p q →
      ‖∫ s in p..Y, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
        ≤ C / Real.sqrt t := by
  obtain ⟨C, hCpos, hC⟩ := Commons.Analysis.StationaryPhase.log_phase_half_line_left
  refine ⟨max C 26, lt_max_of_lt_left hCpos, ?_⟩
  intro t p q Y ht hp hpq hq hY
  have ht2 : (2:ℝ) ≤ t := by linarith
  have h := hC t p Y ht2 hp hY.1 (le_trans hY.2 hq)
  have hs : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
  refine le_trans h ?_
  rw [div_le_div_iff₀ hs hs]
  nlinarith [le_max_left C 26, le_max_right C 26, hs]

/-- Harmonic primitive bound on an interval strictly right of the stationary point. -/
lemma logPhasePrim_right {t p q Y : ℝ} (ht : 4 ≤ t) (hp : 1 < p) (hpq : p ≤ q) (hq : q ≤ 6)
    (hY : Y ∈ Set.Icc p q) :
    ‖∫ s in p..Y, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
      ≤ 144 / (t * (p - 1)) := by
  have ht1 : (1:ℝ) ≤ t := by linarith
  have hpY : p ≤ Y := hY.1
  have hYq : Y ≤ q := hY.2
  have h := Commons.Analysis.StationaryPhase.log_phase_prim_right_general t p Y ht1 hp hpY
    (le_trans hYq hq)
  have h1 : ‖∫ s in p..Y, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
      ≤ 24 * Y / (t * (p - 1)) := le_trans h (min_le_right _ _)
  have h2 : 24 * Y ≤ 24 * 6 := by linarith
  have h3 : (0:ℝ) < t * (p - 1) := by
    have : (0:ℝ) < p - 1 := by linarith
    positivity
  refine le_trans h1 ?_
  rw [div_le_div_iff₀ h3 h3]
  nlinarith [h2]

/-- Fresnel (half-line) primitive bound on an interval right of the stationary point,
inside `[1,6]`. -/
lemma logPhasePrim_right_fresnel {t p q Y : ℝ} (ht : 4 ≤ t) (hp : 1 ≤ p) (hpq : p ≤ q)
    (hq : q ≤ 6) (hY : Y ∈ Set.Icc p q) :
    ‖∫ s in p..Y, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
      ≤ 145 / Real.sqrt t := by
  have ht2 : (2:ℝ) ≤ t := by linarith
  have h := vdc_half_line_right_145 t p Y ht2 hp hY.1 (le_trans hY.2 hq)
  simpa only [vdcPhase] using h

/-- Far-region primitive bound: for `p ≥ 6` the phase has `|φ'| ≥ 5t/6` and the
primitive is `O(1/t)`. -/
lemma logPhasePrim_far {t p Y : ℝ} (ht : 4 ≤ t) (hp : 6 ≤ p) (hpY : p ≤ Y) :
    ‖∫ s in p..Y, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))‖
      ≤ 24 / (5 * t) := by
  have ht0 : (0:ℝ) < t := by linarith
  set Φ : ℝ → ℝ := fun y => t * (WwLog y - y) with hΦ
  have hΦ2 : ContDiff ℝ 2 Φ := by
    rw [hΦ]
    exact contDiff_const.mul ((WwLog_contDiff.of_le (by norm_num)).sub contDiff_id)
  have hderiv' : ∀ y ∈ Set.Icc p Y, deriv (fun y : ℝ => WwLog y - y) y = 1/y - 1 := by
    intro y hy
    have hy18 : (1/8:ℝ) < y := by linarith [hy.1]
    have h1 : deriv WwLog y = 1 / y := by
      rw [(WwLog_eventuallyEq hy18).deriv_eq, Real.deriv_log y, one_div]
    have hd : DifferentiableAt ℝ WwLog y :=
      (WwLog_contDiff.differentiable (by norm_num)).differentiableAt
    have hd2 : DifferentiableAt ℝ (fun y : ℝ => y) y := differentiableAt_id
    have hsub := deriv_sub hd hd2
    rw [show (WwLog - fun y : ℝ => y) = (fun y : ℝ => WwLog y - y) from rfl] at hsub
    rw [hsub, h1]
    simp
  have hderiv : ∀ y ∈ Set.Icc p Y, deriv Φ y = t * (1/y - 1) := by
    intro y hy
    have hd : deriv Φ y = t * deriv (fun y : ℝ => WwLog y - y) y := by
      rw [hΦ]
      exact deriv_const_mul t ((WwLog_contDiff.differentiable (by norm_num)).differentiableAt.sub
        differentiableAt_id)
    rw [hd, hderiv' y hy]
  have hmono : AntitoneOn (deriv Φ) (Set.Icc p Y) := by
    intro x hx y hy hxy
    rw [hderiv x hx, hderiv y hy]
    have hx0 : (0:ℝ) < x := by linarith [hx.1]
    have hle : 1/y ≤ 1/x := one_div_le_one_div_of_le hx0 hxy
    nlinarith [ht, hle]
  have hbound : ∀ y ∈ Set.Icc p Y, 5*t/6 ≤ |deriv Φ y| := by
    intro y hy
    rw [hderiv y hy]
    have hy6 : (6:ℝ) ≤ y := le_trans hp hy.1
    have hy0 : (0:ℝ) < y := by linarith
    have h1 : 1/y - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hy0]
      linarith
    have h1' : t * (1/y - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht0) h1
    rw [abs_of_nonpos h1']
    have h2 : 1/y ≤ 1/6 := one_div_le_one_div_of_le (by norm_num) hy6
    nlinarith [ht]
  have h1 := Commons.Analysis.Oscillatory.norm_integral_mul_exp_le_of_deriv_ge_mono
    (a := p) (b := Y) (lam := 5*t/6) hpY (by linarith) hΦ2 (Or.inr hmono) hbound
    (g := fun _ : ℝ => (1:ℝ)) contDiff_const
  have hInt : (∫ s in p..Y, ((1:ℝ):ℂ) * Complex.exp (Complex.I * (Φ s : ℂ)))
      = ∫ s in p..Y, Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le hpY] at hs
    have hs18 : (1/8:ℝ) ≤ s := by linarith [hs.1]
    have hΦs : Φ s = t * (Real.log s - s) := by
      show t * (WwLog s - s) = t * (Real.log s - s)
      rw [WwLog_eq_log hs18]
    show ((1:ℂ)) * Complex.exp (Complex.I * (Φ s : ℂ))
        = Complex.exp (Complex.I * ((t * (Real.log s - s) : ℝ) : ℂ))
    rw [hΦs]
    simp
  rw [hInt] at h1
  have h2 : 4 * (|(1:ℝ)| + ∫ s in p..Y, |deriv (fun _ : ℝ => (1:ℝ)) s|) / (5*t/6)
      = 24/(5*t) := by
    have hd0 : ∀ s : ℝ, deriv (fun _ : ℝ => (1:ℝ)) s = 0 := fun s => deriv_const s 1
    simp only [hd0, abs_zero, abs_one]
    rw [intervalIntegral.integral_zero, add_zero]
    field_simp
    ring
  rw [h2] at h1
  simpa using h1

/-! ## The complementary piece of the bumped amplitude and the main-term algebra -/

/-- The complement of the bumped amplitude: `(1 - β(u))·(√u)⁻¹·χ(su)`; its support lies in
`[1/6,3/4] ∪ [5/4,12]` for the parameters of the band, where the log-phase is non-stationary. -/
def WwC (χ : ℝ → ℝ) (s : ℝ) (u : ℝ) : ℂ :=
  (((1 - (WwB : ℝ → ℝ) u) * (Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s * u) : ℂ)

/-- The bumped amplitude plus its complement recover `(√u)⁻¹ χ(su)`. -/
lemma WwA_add_WwC (χ : ℝ → ℝ) (s u : ℝ) :
    WwA χ s u + WwC χ s u = (((Real.sqrt u)⁻¹ * χ (s * u) : ℝ) : ℂ) := by
  unfold WwA WwC
  push_cast
  ring

/-- The `m`-independent constant of the stationary-phase main term. -/
def WwC0 (τ : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((τ * Real.log τ - τ * Real.log (2 * Real.pi) - τ - Real.pi / 4 : ℝ) : ℂ))

/-- **Main-term algebra.** For `s = τ/(2πm)` the `m`-th stationary-phase value factors as the
`m`-independent constant `WwC0 τ` times `m^{-1/2-iτ}` (written as `(√m)⁻¹ e^{-iτ log m}`). -/
lemma mainTerm_factor {m : ℕ} (hm : 1 ≤ m) {τ : ℝ} (hτ : 0 < τ) :
    ((Real.sqrt (τ / (2 * Real.pi * (m:ℝ))) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (τ / (2 * Real.pi * (m:ℝ))) : ℝ) : ℂ)))
        * WwFres τ
      = WwC0 τ * (((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (m:ℝ) : ℝ) : ℂ)))) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlog : Real.log (τ / (2 * Real.pi * (m:ℝ)))
      = Real.log τ - Real.log (2 * Real.pi) - Real.log (m:ℝ) := by
    rw [Real.log_div (ne_of_gt hτ) (by positivity), Real.log_mul (by positivity) (ne_of_gt hm0)]
    ring
  have hsqrt : Real.sqrt (τ / (2 * Real.pi * (m:ℝ))) * Real.sqrt (2 * Real.pi / τ)
      = (Real.sqrt (m:ℝ))⁻¹ := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ τ / (2 * Real.pi * (m:ℝ))),
      show τ / (2 * Real.pi * (m:ℝ)) * (2 * Real.pi / τ) = (m:ℝ)⁻¹ by field_simp,
      Real.sqrt_inv]
  have hexp : Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (τ / (2 * Real.pi * (m:ℝ))) : ℝ) : ℂ)))
        * Complex.exp (-(τ : ℂ) * Complex.I) * Complex.exp (-(Real.pi / 4) * Complex.I)
      = WwC0 τ * Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (m:ℝ) : ℝ) : ℂ)))) := by
    rw [WwC0, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast [hlog]
    ring
  rw [WwFres,
    show ((Real.sqrt (τ / (2 * Real.pi * (m:ℝ))) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (τ / (2 * Real.pi * (m:ℝ))) : ℝ) : ℂ)))
        * (Complex.exp (-(τ : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / τ) : ℝ) : ℂ)
            * Complex.exp (-(Real.pi / 4) * Complex.I))
      = (((Real.sqrt (τ / (2 * Real.pi * (m:ℝ))) : ℝ) : ℂ)
          * ((Real.sqrt (2 * Real.pi / τ) : ℝ) : ℂ))
        * (Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (τ / (2 * Real.pi * (m:ℝ))) : ℝ) : ℂ)))
            * Complex.exp (-(τ : ℂ) * Complex.I) * Complex.exp (-(Real.pi / 4) * Complex.I))
      from by ring,
    ← Complex.ofReal_mul, hsqrt, hexp]
  ring

/-- Complex conjugate of the dual sum `WwK`, written in the "unfactored" form. -/
lemma conj_WwK (N : ℕ) (τ : ℝ) :
    (starRingEnd ℂ) (WwK N τ)
      = ∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N:ℝ))))
            (Nat.floor (τ / (2 * Real.pi * (N:ℝ)))),
          (((Real.sqrt (k:ℝ))⁻¹ : ℝ) : ℂ)
            * Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (k:ℝ) : ℝ) : ℂ)))) := by
  have hW : WwK N τ
      = ∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N:ℝ))))
            (Nat.floor (τ / (2 * Real.pi * (N:ℝ)))),
          (k : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / ((Real.sqrt (k:ℝ)) : ℂ) := rfl
  rw [hW, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hk0 : k = 0
  · subst hk0
    simp [Real.sqrt_zero]
  · have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hkne : (k:ℂ) ≠ 0 := by
      have : (k:ℝ) ≠ 0 := ne_of_gt hkpos
      exact_mod_cast this
    have hlogk : Complex.log ((k:ℂ)) = ((Real.log (k:ℝ) : ℝ) : ℂ) :=
      (Complex.ofReal_log (le_of_lt hkpos)).symm
    have hcp : (k:ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (k:ℝ) : ℝ) : ℂ))) := by
      rw [Complex.cpow_def_of_ne_zero hkne, hlogk]
      congr 1
      ring
    have hexp : (starRingEnd ℂ) (Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (k:ℝ) : ℝ) : ℂ))))
        = Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (k:ℝ) : ℝ) : ℂ)))) := by
      rw [(Complex.exp_conj (Complex.I * ((τ : ℂ) * ((Real.log (k:ℝ) : ℝ) : ℂ)))).symm]
      congr 1
      rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
      ring
    rw [hcp, map_div₀, hexp, Complex.conj_ofReal, div_eq_mul_inv, Complex.ofReal_inv]
    ring

/-- **Left tail (first-derivative test).**  If `m < τ/(6πN)` the stationary point of the
phase lies beyond the support, the phase is monotone on the support and `|Φ_m'| ≥ τ/(18N)`
there; hence `‖WwI χ τ m‖ ≤ C(1+K)N/τ`. -/
lemma WwI_left_tail_bound {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hτ : 0 < τ) {m : ℕ} (hm : (m:ℝ) < τ/(6*Real.pi*(N:ℝ))) :
    ‖WwI χ τ m‖ ≤ 800 * (1 + K) * N / τ := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hb52 : 2*(N:ℝ) + Real.sqrt N ≤ 5*N/2 := by nlinarith [hsq, hsqn, hN4R]
  have ha18 : (1:ℝ)/8 < (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  have hab : (N:ℝ) - Real.sqrt N ≤ 2*(N:ℝ) + Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  have hlam : (0:ℝ) < τ/(18*N) := by positivity
  have hbound : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) (2*(N:ℝ) + Real.sqrt N),
      τ/(18*N) ≤ |deriv (WwPhi τ (m:ℝ)) y| := by
    intro y hy
    have hy18 : (1:ℝ)/8 < y := lt_of_lt_of_le ha18 hy.1
    have hyN : (0:ℝ) < y := by linarith
    rw [deriv_WwPhi_eq hy18]
    have h1 : 2*τ/(5*N) ≤ τ / y := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 5*(N:ℝ)) hyN]
      nlinarith [hy.2, hb52, hτ.le]
    have h2 : 2*Real.pi*(m:ℝ) < τ/(3*N) := by
      have h6 : (0:ℝ) < 6*Real.pi*(N:ℝ) := by positivity
      have hm' : (m:ℝ) * (6*Real.pi*(N:ℝ)) < τ := (lt_div_iff₀ h6).mp hm
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 3*(N:ℝ))]
      nlinarith [hm', Real.pi_pos, hNpos]
    have h3 : 2*τ/(5*N) - τ/(3*N) = τ/(15*N) := by
      field_simp
      ring
    have h4 : τ/(18*N) ≤ 2*τ/(5*N) - τ/(3*N) := by
      rw [h3]
      have h5 : (0:ℝ) < τ/(15*N) := by positivity
      calc τ/(18*N) = τ/(15*N) * (15/18) := by field_simp; try ring
        _ ≤ τ/(15*N) * 1 := by
            exact mul_le_mul_of_nonneg_left (by norm_num) h5.le
        _ = τ/(15*N) := by ring
    rw [abs_of_pos (by linarith : (0:ℝ) < τ/y - 2*Real.pi*(m:ℝ))]
    linarith
  have hmono : AntitoneOn (deriv (WwPhi τ (m:ℝ)))
      (Set.Icc ((N:ℝ) - Real.sqrt N) (2*(N:ℝ) + Real.sqrt N)) :=
    fun x hx y hy hxy => antitone_deriv_WwPhi hN (le_of_lt hτ) (m:ℝ) hx hy hxy
  have hg1 : ContDiff ℝ 1 (WwGs χ) := (WwGs_contDiff hχd).of_le (by norm_num)
  have htool := Commons.Analysis.Oscillatory.norm_integral_mul_exp_le_of_deriv_ge_mono
    (a := (N:ℝ) - Real.sqrt N) (b := 2*(N:ℝ) + Real.sqrt N) (lam := τ/(18*N))
    hab hlam ((WwPhi_contDiff τ (m:ℝ)).of_le (by norm_num)) (Or.inr hmono) hbound
    (g := WwGs χ) hg1
  rw [WwI_eq_integral hN hχz]
  refine le_trans htool ?_
  have hga : |WwGs χ ((N:ℝ) - Real.sqrt N)| ≤ 1 := by
    refine le_trans (abs_WwGs_le hN hχ0 le_rfl) ?_
    rw [Real.sqrt_le_one]
    rw [div_le_one (by positivity : (0:ℝ) < N)]
    linarith
  have hgi : ∫ y in ((N:ℝ) - Real.sqrt N)..(2*(N:ℝ) + Real.sqrt N), |deriv (WwGs χ) y|
      ≤ 10*(1+K) := integral_abs_deriv_WwGs_le hN hχd hχ0 hK hbdd
  have hnum : 4 * (|WwGs χ ((N:ℝ) - Real.sqrt N)|
        + ∫ y in ((N:ℝ) - Real.sqrt N)..(2*(N:ℝ) + Real.sqrt N), |deriv (WwGs χ) y|)
      ≤ 4 * (1 + 10*(1+K)) := by linarith
  refine le_trans (div_le_div_of_nonneg_right hnum hlam.le) ?_
  have hK1 : (0:ℝ) ≤ 1 + K := by linarith
  rw [show (4 * (1 + 10*(1+K))) / (τ/(18*N)) = 4 * (1 + 10*(1+K)) * 18 * N / τ by
    field_simp]
  rw [div_le_div_iff₀ hτ hτ]
  have hle : 4 * (1 + 10*(1+K)) * 18 ≤ 800 * (1 + K) := by nlinarith [hK]
  calc 4 * (1 + 10*(1+K)) * 18 * N * τ = (4 * (1 + 10*(1+K)) * 18) * (N * τ) := by ring
    _ ≤ (800 * (1 + K)) * (N * τ) := mul_le_mul_of_nonneg_right hle (by positivity)
    _ = 800 * (1 + K) * N * τ := by ring

/-- In the band parameters `N/4 ≤ s ≤ 3N` the complementary amplitude `WwC` is supported
in the fixed interval `[1/6,12]`. -/
lemma WwC_eq_zero_of_notMem {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {s u : ℝ} (hs1 : (N:ℝ)/4 ≤ s) (hs2 : s ≤ 3*N) (hu : u ∉ Set.Icc (1/6:ℝ) 12) :
    WwC χ s u = 0 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hlow : (N:ℝ) - Real.sqrt N ≥ (N:ℝ)/2 := by nlinarith [hsq, hsqn, hN4R]
  have hhigh : (2*N:ℝ) + Real.sqrt N ≤ 3*N := by nlinarith [hsqn, hN4R]
  have key : χ (s * u) = 0 := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hu | hu
    · exact hχz _ (Or.inl (by nlinarith [hu, hs2, hlow]))
    · exact hχz _ (Or.inr (by nlinarith [hu, hs1, hhigh]))
  unfold WwC
  rw [key]
  simp

/-- The complementary amplitude vanishes on the middle interval `[3/4,5/4]` (where the bump
`WwB` equals one). -/
lemma WwC_eq_zero_of_middle {χ : ℝ → ℝ} {s u : ℝ} (hu : u ∈ Set.Icc (3/4:ℝ) (5/4)) :
    WwC χ s u = 0 := by
  unfold WwC
  have h1 : (WwB : ℝ → ℝ) u = 1 := by
    apply WwB_one
    rw [abs_le]
    constructor <;> linarith [hu.1, hu.2]
  rw [h1]
  norm_num

/-- A fixed smooth cutoff: `= 1` on `[1/6,12]` and `= 0` outside `(1/12,24)`.  Used to make
the complementary amplitude globally smooth and bounded. -/
def WwPsi (u : ℝ) : ℝ :=
  Real.smoothTransition (12*u - 1) * (1 - Real.smoothTransition ((u - 12)/12))

lemma WwPsi_contDiff : ContDiff ℝ 3 WwPsi := by
  unfold WwPsi
  fun_prop

lemma WwPsi_eq_one {u : ℝ} (h1 : (1:ℝ)/6 ≤ u) (h2 : u ≤ 12) : WwPsi u = 1 := by
  unfold WwPsi
  have ha : (1:ℝ) ≤ 12*u - 1 := by linarith
  have hb : (u - 12)/12 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)
  rw [Real.smoothTransition.one_of_one_le ha, Real.smoothTransition.zero_of_nonpos hb]
  ring

lemma WwPsi_eq_zero_of_le {u : ℝ} (hu : u ≤ (1:ℝ)/12) : WwPsi u = 0 := by
  unfold WwPsi
  have ha : 12*u - 1 ≤ 0 := by linarith
  rw [Real.smoothTransition.zero_of_nonpos ha]
  ring

lemma WwPsi_eq_zero_of_ge {u : ℝ} (hu : 24 ≤ u) : WwPsi u = 0 := by
  unfold WwPsi
  have hb : (1:ℝ) ≤ (u - 12)/12 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  rw [Real.smoothTransition.one_of_one_le hb]
  ring

lemma WwPsi_nonneg (u : ℝ) : 0 ≤ WwPsi u := by
  unfold WwPsi
  have h1 : 0 ≤ Real.smoothTransition (12*u - 1) := Real.smoothTransition.nonneg _
  have h2 : 0 ≤ 1 - Real.smoothTransition ((u - 12)/12) := by
    have := Real.smoothTransition.le_one ((u - 12)/12)
    linarith
  exact mul_nonneg h1 h2

lemma WwPsi_le_one (u : ℝ) : WwPsi u ≤ 1 := by
  unfold WwPsi
  have h1 : Real.smoothTransition (12*u - 1) ≤ 1 := Real.smoothTransition.le_one _
  have h2 : 0 ≤ 1 - Real.smoothTransition ((u - 12)/12) := by
    have := Real.smoothTransition.le_one ((u - 12)/12)
    linarith
  have h2' : 1 - Real.smoothTransition ((u - 12)/12) ≤ 1 := by
    linarith [Real.smoothTransition.nonneg ((u - 12)/12)]
  calc Real.smoothTransition (12*u - 1) * (1 - Real.smoothTransition ((u - 12)/12))
      ≤ 1 * 1 := mul_le_mul h1 h2' h2 (by norm_num)
    _ = 1 := by ring

/-- `WwSm u ≥ min u 1` — the smoothing never decreases the identity below one. -/
lemma WwSm_ge_min (u : ℝ) : min u 1 ≤ WwSm u := by
  rcases le_or_gt u 0 with h | h
  · rw [WwSm_eq_one h]
    exact le_trans (min_le_right _ _) le_rfl
  rcases le_or_gt u 1 with h1 | h1
  · have hs : Real.smoothTransition (8*u) ≤ 1 := Real.smoothTransition.le_one _
    have hs0 : 0 ≤ Real.smoothTransition (8*u) := Real.smoothTransition.nonneg _
    have hu : 0 ≤ 1 - u := by linarith
    have h2 : Real.smoothTransition (8*u) * (1 - u) ≤ 1 - u := by nlinarith
    have hmin : min u 1 = u := min_eq_left h1
    rw [hmin, WwSm]
    linarith
  · rw [WwSm_eq_self (by linarith : (1:ℝ)/8 ≤ u)]
    exact le_trans (min_le_left _ _) le_rfl

/-- The globally smooth complementary amplitude: the cutoff `WwPsi` times the literal
complementary amplitude `WwC`.  (The cutoff makes it globally `C¹` and globally bounded; on
`[1/6,12]` the cutoff is one, so it agrees with `WwC` there.) -/
def WwAc (χ : ℝ → ℝ) (s u : ℝ) : ℂ :=
  (((WwPsi u * (1 - (WwB : ℝ → ℝ) u) * (Real.sqrt u)⁻¹ : ℝ)) : ℂ) * (χ (s*u) : ℂ)

lemma WwAc_contDiff {χ : ℝ → ℝ} (hχ : ContDiff ℝ 3 χ) (s : ℝ) :
    ContDiff ℝ 1 (WwAc χ s) := by
  have hβ : ContDiff ℝ ((1:ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => WwPsi u * (1 - (WwB : ℝ → ℝ) u)) := by
    have h1 : ContDiff ℝ ((1:ℕ∞) : WithTop ℕ∞) WwPsi :=
      WwPsi_contDiff.of_le (by norm_num)
    have h2 : ContDiff ℝ ((1:ℕ∞) : WithTop ℕ∞) (WwB : ℝ → ℝ) :=
      (ContDiffBump.contDiff (n := ⊤) WwB).of_le (by simp)
    exact h1.mul (contDiff_const.sub h2)
  have h3 : ContDiff ℝ ((1:ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => WwPsi u * (1 - (WwB : ℝ → ℝ) u) * (Real.sqrt u)⁻¹) :=
    contDiff_bump_mul_sqrt_inv (r := 1/12) (fun u : ℝ => WwPsi u * (1 - (WwB : ℝ → ℝ) u)) 1 hβ
      (by norm_num) (fun y hy => by
        rw [WwPsi_eq_zero_of_le hy, zero_mul])
  have h4 : ContDiff ℝ 1 (fun u : ℝ =>
      (((WwPsi u * (1 - (WwB : ℝ → ℝ) u) * (Real.sqrt u)⁻¹ : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h3
  have h5 : ContDiff ℝ 1 (fun u : ℝ => (χ (s*u) : ℂ)) :=
    ((Complex.ofRealCLM.contDiff.comp (hχ.comp (contDiff_const.mul contDiff_id)))).of_le (by norm_num)
  exact h4.mul h5

lemma WwAc_norm_le {χ : ℝ → ℝ} (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (s u : ℝ) :
    ‖WwAc χ s u‖ ≤ 4 := by
  rcases lt_or_ge u (1/12) with hu | hu
  · have h0 : WwPsi u = 0 := WwPsi_eq_zero_of_le (le_of_lt hu)
    unfold WwAc
    rw [h0]
    norm_num
  · unfold WwAc
    rw [norm_mul]
    have hcast : ∀ r : ℝ, ‖((r:ℂ))‖ = |r| := fun r => by
      rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
    have hnorm : ‖(((WwPsi u * (1 - (WwB : ℝ → ℝ) u) * (Real.sqrt u)⁻¹ : ℝ)) : ℂ)‖
        = |WwPsi u| * |1 - (WwB : ℝ → ℝ) u| * |(Real.sqrt u)⁻¹| := by
      rw [hcast, abs_mul, abs_mul]
    rw [hnorm, hcast]
    have h1 : |WwPsi u| ≤ 1 := by
      rw [abs_of_nonneg (WwPsi_nonneg u)]
      exact WwPsi_le_one u
    have h2 : |1 - (WwB : ℝ → ℝ) u| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [WwB_le_one u], by linarith [WwB_nonneg u]⟩
    have h3 : |(Real.sqrt u)⁻¹| ≤ 4 := by
      rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg u)), inv_le_comm₀ (Real.sqrt_pos.mpr (by linarith)) (by norm_num)]
      refine le_trans ?_ (Real.sqrt_le_sqrt hu)
      rw [show (4:ℝ)⁻¹ = 1/4 by norm_num, ← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/4)]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h4 : |χ (s*u)| ≤ 1 := by
      rw [abs_of_nonneg (hχ0 (s*u)).1]
      exact (hχ0 (s*u)).2
    calc |WwPsi u| * |1 - (WwB : ℝ → ℝ) u| * |(Real.sqrt u)⁻¹| * |χ (s*u)|
        ≤ 1 * 1 * 4 * 1 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) h3
            (abs_nonneg _) (by norm_num)) h4 (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num

/-- The `s`-free real factor of the complementary amplitude. -/
def WwFc (u : ℝ) : ℝ := WwPsi u * (1 - (WwB : ℝ → ℝ) u) * (Real.sqrt u)⁻¹

lemma WwPsi_contDiff_top : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) WwPsi := by
  unfold WwPsi
  fun_prop

lemma WwFc_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) WwFc := by
  have hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => WwPsi u * (1 - (WwB : ℝ → ℝ) u)) := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) WwPsi := WwPsi_contDiff_top
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (WwB : ℝ → ℝ) :=
      ContDiffBump.contDiff (n := ⊤) WwB
    exact h1.mul (contDiff_const.sub h2)
  exact contDiff_bump_mul_sqrt_inv (r := 1/12)
    (fun u : ℝ => WwPsi u * (1 - (WwB : ℝ → ℝ) u)) ⊤ hβ (by norm_num)
    (fun y hy => by rw [WwPsi_eq_zero_of_le hy, zero_mul])

/-- An absolute derivative bound for the `s`-free real factor. -/
lemma WwFc_deriv_bounded : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, |deriv WwFc u| ≤ C := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) WwFc := WwFc_contDiff
  have hc : Continuous (deriv WwFc) := hcd.continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (1/12:ℝ)) (b := 24)).exists_bound_of_continuousOn hc.continuousOn
  have hnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC (1/12) (by norm_num))
  refine ⟨C + 1, by linarith, fun u => ?_⟩
  by_cases hu : u < 1/12
  · have hev : WwFc =ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds hu] with y hy
      unfold WwFc
      rw [WwPsi_eq_zero_of_le (le_of_lt hy), zero_mul, zero_mul]
    rw [hev.deriv_eq, deriv_const, abs_zero]
    linarith
  · push Not at hu
    by_cases hu' : u ≤ 24
    · have h1 := hC u (by exact ⟨hu, hu'⟩)
      rw [Real.norm_eq_abs] at h1
      linarith
    · push Not at hu'
      have hopen : IsOpen {y : ℝ | 24 < y} := isOpen_lt continuous_const continuous_id
      have hev : WwFc =ᶠ[𝓝 u] (fun _ => (0:ℝ)) := by
        filter_upwards [hopen.mem_nhds hu'] with y hy
        unfold WwFc
        have h0 : WwPsi y = 0 := WwPsi_eq_zero_of_ge (le_of_lt hy)
        rw [h0, zero_mul, zero_mul]
      rw [hev.deriv_eq, deriv_const, abs_zero]
      linarith

lemma norm_ofReal_cast (r : ℝ) : ‖((r : ℂ))‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

lemma WwFc_abs_le (u : ℝ) : |WwFc u| ≤ 4 := by
  rcases lt_or_ge u (1/12) with hu | hu
  · unfold WwFc
    rw [WwPsi_eq_zero_of_le (le_of_lt hu), zero_mul, zero_mul, abs_zero]
    norm_num
  · unfold WwFc
    rw [abs_mul, abs_mul]
    have h1 : |WwPsi u| ≤ 1 := by
      rw [abs_of_nonneg (WwPsi_nonneg u)]
      exact WwPsi_le_one u
    have h2 : |1 - (WwB : ℝ → ℝ) u| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [WwB_le_one u], by linarith [WwB_nonneg u]⟩
    have h3 : |(Real.sqrt u)⁻¹| ≤ 4 := by
      have hu4 : (1:ℝ)/4 ≤ Real.sqrt u := by
        rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/4)]
        exact Real.sqrt_le_sqrt (by linarith)
      rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg u)),
        inv_le_comm₀ (Real.sqrt_pos.mpr (by linarith)) (by norm_num),
        show (4:ℝ)⁻¹ = 1/4 by norm_num]
      exact hu4
    calc |WwPsi u| * |1 - (WwB : ℝ → ℝ) u| * |(Real.sqrt u)⁻¹|
        ≤ 1 * 1 * 4 := by
          refine mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)) h3
            (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num

/-- **Derivative bound for the complementary amplitude.**  `∃ M > 0` (an absolute constant)
with `‖deriv (WwAc χ s) u‖ ≤ M(1+K)√N` for all `u`. -/
lemma WwAc_deriv_bound {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {K s : ℝ} (hK : 0 ≤ K) (hs0 : 0 ≤ s)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N) (hs2 : s ≤ 3*N) :
    ∃ M : ℝ, 0 < M ∧ ∀ u : ℝ, ‖deriv (WwAc χ s) u‖ ≤ M * (1 + K) * Real.sqrt N := by
  obtain ⟨C, hCpos, hC⟩ := WwFc_deriv_bounded
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hsqrtN1 : (1:ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ N))
  refine ⟨max C 99 + 12, by positivity, ?_⟩
  intro u
  have hχd' : Differentiable ℝ χ := hχd.differentiable (by norm_num)
  have hfd : HasDerivAt WwFc (deriv WwFc u) u :=
    (WwFc_contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hf : HasDerivAt (fun y : ℝ => ((WwFc y : ℝ) : ℂ)) (((deriv WwFc u : ℝ)) : ℂ) u :=
    hfd.ofReal_comp
  have hcomp : HasDerivAt (fun y : ℝ => χ (s*y)) (deriv χ (s*u) * s) u :=
    (hχd'.differentiableAt.hasDerivAt).comp u (hasDerivAt_const_mul' (s := s) (u := u))
  have hg : HasDerivAt (fun y : ℝ => ((χ (s*y) : ℝ) : ℂ)) (((deriv χ (s*u)) * s : ℝ) : ℂ) u :=
    hcomp.ofReal_comp
  have hprod := hf.mul hg
  have hfun : WwAc χ s = fun y : ℝ => ((WwFc y : ℝ) : ℂ) * ((χ (s*y) : ℝ) : ℂ) := by
    funext y
    simp only [WwAc, WwFc]
  have hderiv : deriv (WwAc χ s) u
      = (((deriv WwFc u : ℝ)) : ℂ) * ((χ (s*u) : ℝ) : ℂ)
        + ((WwFc u : ℝ) : ℂ) * ((((deriv χ (s*u)) * s : ℝ)) : ℂ) := by
    rw [hfun]
    exact hprod.deriv
  rw [hderiv]
  refine le_trans (norm_add_le _ _) ?_
  have hA : ‖(((deriv WwFc u : ℝ)) : ℂ) * ((χ (s*u) : ℝ) : ℂ)‖ ≤ max C 99 := by
    rw [norm_mul, norm_ofReal_cast, norm_ofReal_cast]
    have h1 : |deriv WwFc u| ≤ C := hC u
    have h2 : |χ (s*u)| ≤ 1 := by
      rw [abs_of_nonneg (hχ0 (s*u)).1]
      exact (hχ0 (s*u)).2
    calc |deriv WwFc u| * |χ (s*u)| ≤ (max C 99) * 1 :=
          mul_le_mul (le_trans h1 (le_max_left _ _)) h2 (abs_nonneg _) (by positivity)
      _ = max C 99 := by ring
  have hB : ‖((WwFc u : ℝ) : ℂ) * ((((deriv χ (s*u)) * s : ℝ)) : ℂ)‖
      ≤ 12 * K * Real.sqrt N := by
    rw [norm_mul, norm_ofReal_cast, norm_ofReal_cast]
    have h1 : |WwFc u| ≤ 4 := WwFc_abs_le u
    have h2 : |deriv χ (s*u) * s| ≤ 3 * K * Real.sqrt N := by
      rw [abs_mul]
      have ha : |deriv χ (s*u)| ≤ K / Real.sqrt N := hbdd (s*u)
      have hb : |s| ≤ 3*N := by rw [abs_of_nonneg hs0]; exact hs2
      have h3 : (K / Real.sqrt N) * (3*N) = 3 * K * Real.sqrt N := by
        rw [show (K / Real.sqrt N) * (3*N) = 3 * (N / Real.sqrt N) * K by ring,
          Real.div_sqrt]
        ring
      calc |deriv χ (s*u)| * |s| ≤ (K / Real.sqrt N) * (3*N) :=
            mul_le_mul ha hb (abs_nonneg _) (by positivity)
        _ = 3 * K * Real.sqrt N := h3
    have h4 : 4 * (3 * K * Real.sqrt N) = 12 * K * Real.sqrt N := by ring
    calc |WwFc u| * |deriv χ (s*u) * s| ≤ 4 * (3 * K * Real.sqrt N) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = 12 * K * Real.sqrt N := h4
  refine le_trans (add_le_add hA hB) ?_
  have hK1 : (0:ℝ) ≤ 1 + K := by linarith
  have hone : (1:ℝ) ≤ (1 + K) * Real.sqrt N := by
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ (1 + K) * Real.sqrt N :=
          mul_le_mul (by linarith) hsqrtN1 (by norm_num) (by linarith)
  have h1a : max C 99 ≤ (max C 99) * (1 + K) * Real.sqrt N := by
    calc max C 99 = max C 99 * 1 := by ring
      _ ≤ (max C 99) * ((1 + K) * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hone (by positivity)
      _ = max C 99 * (1 + K) * Real.sqrt N := by ring
  have h2a : 12 * K * Real.sqrt N ≤ 12 * (1 + K) * Real.sqrt N := by
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg N)
    nlinarith [hK]
  have key : (max C 99) * (1 + K) * Real.sqrt N + 12 * (1 + K) * Real.sqrt N
      = (max C 99 + 12) * (1 + K) * Real.sqrt N := by ring
  linarith [h1a, h2a, key]

/-- **Scaled outer bound** (companion of `logphase_stationary_phase_scaled`): the commons
`logphase_outer_bound_general` with the amplitude bounds given by a single constant `M`. -/
lemma logphase_outer_bound_scaled {A : ℝ → ℂ} {c d t lam Q M : ℝ}
    (hcd : c ≤ d) (ht : 0 < t) (hlam : 0 < lam) (hQ : 0 ≤ Q) (hM : 0 < M)
    (hA : ContDiff ℝ 1 A) (hAc : ∀ y, ‖A y‖ ≤ M) (hAd : ∀ y, ‖deriv A y‖ ≤ M)
    (hdphi : ∀ y ∈ Set.Icc c d, lam ≤ |1 / y - 1|)
    (hy0 : ∀ y ∈ Set.Icc c d, 0 < y)
    (hquad : ∀ y ∈ Set.Icc c d, 1 / y ^ 2 ≤ Q) :
    ‖∫ y in c..d, A y * Complex.exp (Complex.I * t * (Real.log y - y))‖
      ≤ M * (t⁻¹ * (2 / lam + (d - c) * (1 / lam + Q / lam ^ 2))) := by
  have hMne : M ≠ 0 := ne_of_gt hM
  set A' : ℝ → ℂ := fun y => (M:ℂ)⁻¹ * A y with hA'
  have hA'cd : ContDiff ℝ 1 A' := by rw [hA']; exact contDiff_const.mul hA
  have hA'c : ∀ y, ‖A' y‖ ≤ 1 := by
    intro y
    rw [hA', norm_mul, norm_inv, norm_ofReal_cast, abs_of_pos hM]
    calc M⁻¹ * ‖A y‖ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hAc y) (by positivity)
      _ = 1 := inv_mul_cancel₀ hMne
  have hA'd : ∀ y, ‖deriv A' y‖ ≤ 1 := by
    intro y
    have hd : deriv A' y = (M:ℂ)⁻¹ * deriv A y := by
      rw [hA']
      exact deriv_const_mul _ (hA.differentiable (by norm_num)).differentiableAt
    rw [hd, norm_mul, norm_inv, norm_ofReal_cast, abs_of_pos hM]
    calc M⁻¹ * ‖deriv A y‖ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hAd y) (by positivity)
      _ = 1 := inv_mul_cancel₀ hMne
  have key := Commons.Analysis.StationaryPhase.logphase_outer_bound_general
    (A := A') hcd ht hlam hQ hA'cd hA'c hA'd hdphi hy0 hquad
  have hInt : (∫ y in c..d, A' y * Complex.exp (Complex.I * t * (Real.log y - y)))
      = (M:ℂ)⁻¹ * ∫ y in c..d, A y * Complex.exp (Complex.I * t * (Real.log y - y)) := by
    rw [hA',
      show (fun y => (M:ℂ)⁻¹ * A y * Complex.exp (Complex.I * t * (Real.log y - y)))
          = (fun y => (M:ℂ)⁻¹ * (A y * Complex.exp (Complex.I * t * (Real.log y - y)))) from by
        funext y; ring]
    exact intervalIntegral.integral_const_mul _ _
  rw [hInt, norm_mul, norm_inv, norm_ofReal_cast, abs_of_pos hM] at key
  calc ‖∫ y in c..d, A y * Complex.exp (Complex.I * t * (Real.log y - y))‖
      = M * (M⁻¹ * ‖∫ y in c..d, A y * Complex.exp (Complex.I * t * (Real.log y - y))‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ hMne, one_mul]
    _ ≤ M * (t⁻¹ * (2 / lam + (d - c) * (1 / lam + Q / lam ^ 2))) :=
        mul_le_mul_of_nonneg_left key (le_of_lt hM)

/-- Factorisation of the cut-off amplitude: `WwAc = WwPsi · WwC`. -/
lemma WwAc_eq_psi_mul_WwC (χ : ℝ → ℝ) (s u : ℝ) :
    WwAc χ s u = ((WwPsi u : ℝ) : ℂ) * WwC χ s u := by
  unfold WwAc WwC
  push_cast
  ring

/-- On `[1/6,12]` the cutoff is one, so the globally smooth amplitude agrees with the literal
complementary amplitude. -/
lemma WwAc_eq_WwC {χ : ℝ → ℝ} {s u : ℝ} (hu : u ∈ Set.Icc (1/6:ℝ) 12) :
    WwAc χ s u = WwC χ s u := by
  rw [WwAc_eq_psi_mul_WwC, WwPsi_eq_one hu.1 hu.2]
  norm_num

/-- The cut-off amplitude vanishes on the middle interval `[3/4,5/4]`. -/
lemma WwAc_eq_zero_of_middle {χ : ℝ → ℝ} {s u : ℝ} (hu : u ∈ Set.Icc (3/4:ℝ) (5/4)) :
    WwAc χ s u = 0 := by
  rw [WwAc_eq_psi_mul_WwC, WwC_eq_zero_of_middle hu, mul_zero]

/-- **Step 1 of the complementary estimate.**  In the band parameters the complementary
integrand is supported in the fixed interval `[1/6,12]`, so the integral over `ℝ` collapses to
an interval integral (the single boundary point `u = 1/6` also vanishes because
`s/6 ≤ N/2 ≤ N−√N`). -/
lemma WwC_integral_eq_interval {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {s τ : ℝ} (hs1 : (N:ℝ)/4 ≤ s) (hs2 : s ≤ 3*N) :
    (∫ u : ℝ, WwC χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))
      = ∫ u in (1/6:ℝ)..12,
          WwC χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hlow : (N:ℝ)/2 ≤ (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  rw [intervalIntegral.integral_of_le (by norm_num : (1/6:ℝ) ≤ 12),
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Set.Ioc (1/6:ℝ) 12
  · rw [Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu]
    by_cases hu2 : u ∈ Set.Icc (1/6:ℝ) 12
    · have hu3 : u = 1/6 := by
        rw [Set.mem_Icc] at hu2
        rw [Set.mem_Ioc, not_and_or, not_lt] at hu
        rcases hu with h | h
        · linarith [hu2.1, h]
        · linarith [hu2.2, h]
      subst hu3
      have hz : WwC χ s (1/6) = 0 := by
        unfold WwC
        have h1 : χ (s * (1/6)) = 0 := hχz _ (Or.inl (by nlinarith [hs2, hlow]))
        rw [h1]
        simp
      rw [hz, zero_mul]
    · rw [WwC_eq_zero_of_notMem hN hχz hs1 hs2 hu2, zero_mul]

/-- **Step 2 of the complementary estimate.**  On `[1/6,12]` the cutoff is one, so the
complementary integrand may be replaced by the globally smooth amplitude `WwAc`. -/
lemma WwC_integral_eq_WwAc_integral {χ : ℝ → ℝ} {s τ : ℝ} :
    (∫ u in (1/6:ℝ)..12, WwC χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))
      = ∫ u in (1/6:ℝ)..12,
          WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (by norm_num : (1/6:ℝ) ≤ 12)] at hu
  show WwC χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))
      = WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))
  rw [WwAc_eq_WwC hu]

/-- **Step 3 of the complementary estimate.**  Split `[1/6,12]` at `3/4` and `5/4`.  The
integrability side conditions come from continuity on `[1/6,12]` (`Real.log` is continuous there),
transported to any sub-interval in either orientation. -/
lemma WwAc_integral_split {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ) (s τ : ℝ) :
    (∫ u in (1/6:ℝ)..12,
        WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))
      = (∫ u in (1/6:ℝ)..(3/4),
            WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))
        + (∫ u in (3/4:ℝ)..(5/4),
            WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))
        + ∫ u in (5/4:ℝ)..12,
            WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)) := by
  have hc : ContinuousOn (fun u : ℝ =>
      WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))
      (Set.Icc (1/6:ℝ) 12) := by
    refine ContinuousOn.mul (WwAc_contDiff hχd s).continuous.continuousOn ?_
    refine Complex.continuous_exp.comp_continuousOn ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    have hlog : ContinuousOn (fun u : ℝ => Real.log u) (Set.Icc (1/6:ℝ) 12) :=
      Real.continuousOn_log.mono (fun u hu h0 => by
        rw [h0] at hu
        norm_num at hu)
    exact continuousOn_const.mul (hlog.sub continuousOn_id)
  have hInt : ∀ a b : ℝ, (1/6:ℝ) ≤ a → b ≤ 12 → a ≤ b →
      IntervalIntegrable (fun u : ℝ =>
        WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))) volume a b := by
    intro a b ha hb hab
    refine (hc.mono ?_).intervalIntegrable
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans ha h1, le_trans h2 hb⟩
    · exact ⟨le_trans ha (le_trans hab h1), le_trans h2 (le_trans hab hb)⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (hInt (1/6) (5/4) le_rfl (by norm_num) (by norm_num))
        (hInt (5/4) 12 (by norm_num) le_rfl (by norm_num)),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hInt (1/6) (3/4) le_rfl (by norm_num) (by norm_num))
        (hInt (3/4) (5/4) (by norm_num) (by norm_num) (by norm_num))]

/-- **Step 4 of the complementary estimate.**  The middle piece `∫_{3/4}^{5/4}` vanishes. -/
lemma WwAc_integral_middle_zero {χ : ℝ → ℝ} {s τ : ℝ} :
    (∫ u in (3/4:ℝ)..(5/4),
        WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))) = 0 := by
  have hzero : (∫ u in (3/4:ℝ)..(5/4),
        WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))
      = ∫ u in (3/4:ℝ)..(5/4), (0:ℂ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (3/4:ℝ) ≤ 5/4)] at hu
    show WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)) = 0
    rw [WwAc_eq_zero_of_middle hu, zero_mul]
  rw [hzero, intervalIntegral.integral_zero]

/-- **Step 5, first half.**  There is `M > 0` so that `(M:ℂ)⁻¹ * WwAc χ s` satisfies both
amplitude hypotheses of `logphase_outer_bound_scaled` (`‖·‖ ≤ 1` and `‖deriv ·‖ ≤ 1`). -/
lemma WwAc_scaled_bounds {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {K s : ℝ} (hK : 0 ≤ K) (hs0 : 0 ≤ s)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N) (hs2 : s ≤ 3*N) :
    ∃ M : ℝ, 0 < M ∧
      (∀ u : ℝ, ‖(M:ℂ)⁻¹ * WwAc χ s u‖ ≤ 1) ∧
      (∀ u : ℝ, ‖deriv (fun u : ℝ => (M:ℂ)⁻¹ * WwAc χ s u) u‖ ≤ 1) := by
  obtain ⟨Md, hMdpos, hMdb⟩ := WwAc_deriv_bound hN hχd hχ0 hK hs0 hbdd hs2
  refine ⟨max 4 (Md * (1 + K) * Real.sqrt N), lt_max_of_lt_left (by norm_num), ?_, ?_⟩
  · intro u
    have hMpos : (0:ℝ) < max 4 (Md * (1 + K) * Real.sqrt N) := lt_max_of_lt_left (by norm_num)
    rw [norm_mul, norm_inv, norm_ofReal_cast, abs_of_pos hMpos]
    have h1 : ‖WwAc χ s u‖ ≤ max 4 (Md * (1 + K) * Real.sqrt N) :=
      le_trans (WwAc_norm_le hχ0 s u) (le_max_left _ _)
    calc (max 4 (Md * (1 + K) * Real.sqrt N))⁻¹ * ‖WwAc χ s u‖
        ≤ (max 4 (Md * (1 + K) * Real.sqrt N))⁻¹ * max 4 (Md * (1 + K) * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hMpos)
  · intro u
    have hMpos : (0:ℝ) < max 4 (Md * (1 + K) * Real.sqrt N) := lt_max_of_lt_left (by norm_num)
    have hdiff : DifferentiableAt ℝ (WwAc χ s) u :=
      ((WwAc_contDiff hχd s).differentiable (by norm_num)).differentiableAt
    have hd : deriv (fun u : ℝ => ((max 4 (Md * (1 + K) * Real.sqrt N) : ℝ) : ℂ)⁻¹ * WwAc χ s u) u
        = (((max 4 (Md * (1 + K) * Real.sqrt N) : ℝ) : ℂ)⁻¹) * deriv (WwAc χ s) u :=
      deriv_const_mul _ hdiff
    rw [hd, norm_mul, norm_inv, norm_ofReal_cast, abs_of_pos hMpos]
    have h1 : ‖deriv (WwAc χ s) u‖ ≤ Md * (1 + K) * Real.sqrt N := hMdb u
    have h2 : Md * (1 + K) * Real.sqrt N ≤ max 4 (Md * (1 + K) * Real.sqrt N) := le_max_right _ _
    calc (max 4 (Md * (1 + K) * Real.sqrt N))⁻¹ * ‖deriv (WwAc χ s) u‖
        ≤ (max 4 (Md * (1 + K) * Real.sqrt N))⁻¹ * max 4 (Md * (1 + K) * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left (le_trans h1 h2) (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hMpos)

/-- The bridge between the phase form used in this file and the one used by the commons outer
bound: both exponentials have the same argument. -/
lemma exp_form_bridge (τ u : ℝ) :
    Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))
      = Complex.exp (Complex.I * τ * ((Real.log u : ℂ) - (u : ℂ))) := by
  congr 1
  push_cast
  ring

/-- Pointwise factorisation used to pull the scaling constant out of an integral. -/
lemma mul_inv_mul_factor {M : ℝ} (hM : M ≠ 0) (z : ℂ) :
    z = (M:ℂ) * ((M:ℂ)⁻¹ * z) := by
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hM), one_mul]

/-- **`hcomm`, as a standalone lemma.**  Pull the scaling constant `M` out of the complementary
integral (the pointwise identity is stated separately so that no rewriting happens under `∫`). -/
lemma WwAc_integral_factor {χ : ℝ → ℝ} {s τ M : ℝ} (hM : M ≠ 0) (c d : ℝ) :
    (∫ u in c..d, WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))
      = (M:ℂ) * ∫ u in c..d, ((M:ℂ)⁻¹ * WwAc χ s u)
          * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)) := by
  have hpt : ∀ u : ℝ, WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))
      = (M:ℂ) * (((M:ℂ)⁻¹ * WwAc χ s u)
          * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))) := by
    intro u
    rw [mul_inv_mul_factor hM (WwAc χ s u
      * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))]
    ring
  rw [show (∫ u in c..d, WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))
        = ∫ u in c..d, (M:ℂ) * (((M:ℂ)⁻¹ * WwAc χ s u)
            * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))) from
      intervalIntegral.integral_congr fun u _ => hpt u,
    intervalIntegral.integral_const_mul]

/-- **`hbridge`, as a standalone lemma.**  Replace the phase form of this file by the one used by
the commons outer bound. -/
lemma WwAc_integral_bridge {χ : ℝ → ℝ} {s τ M : ℝ} (c d : ℝ) :
    (∫ u in c..d, ((M:ℂ)⁻¹ * WwAc χ s u)
        * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))
      = ∫ u in c..d, ((M:ℂ)⁻¹ * WwAc χ s u)
          * Complex.exp (Complex.I * τ * ((Real.log u : ℂ) - (u : ℂ))) := by
  apply intervalIntegral.integral_congr
  intro u _
  show ((M:ℂ)⁻¹ * WwAc χ s u) * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))
      = ((M:ℂ)⁻¹ * WwAc χ s u) * Complex.exp (Complex.I * τ * ((Real.log u : ℂ) - (u : ℂ)))
  rw [exp_form_bridge τ u]

/-- **Per-interval bound.**  On an interval where the log-phase is non-stationary with
`|1/u − 1| ≥ lam` and `1/u² ≤ Q`, the cut-off complementary integral is
`≤ M·τ⁻¹(2/lam + (d−c)(1/lam + Q/lam²))`. -/
lemma WwAc_interval_bound {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {K s : ℝ} (hK : 0 ≤ K) (hs0 : 0 ≤ s)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N) (hs2 : s ≤ 3*N)
    {τ M : ℝ} (hτ : 4 ≤ τ) (hMpos : 0 < M)
    (hA1 : ∀ u : ℝ, ‖(M:ℂ)⁻¹ * WwAc χ s u‖ ≤ 1)
    (hA2 : ∀ u : ℝ, ‖deriv (fun u : ℝ => (M:ℂ)⁻¹ * WwAc χ s u) u‖ ≤ 1)
    {c d lam Q : ℝ} (hcd : c ≤ d) (hlam : 0 < lam) (hQ : 0 ≤ Q)
    (hdphi : ∀ y ∈ Set.Icc c d, lam ≤ |1 / y - 1|) (hy0 : ∀ y ∈ Set.Icc c d, 0 < y)
    (hquad : ∀ y ∈ Set.Icc c d, 1 / y ^ 2 ≤ Q) :
    ‖∫ u in c..d, WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖
      ≤ M * (τ⁻¹ * (2 / lam + (d - c) * (1 / lam + Q / lam ^ 2))) := by
  have hMne : M ≠ 0 := ne_of_gt hMpos
  rw [WwAc_integral_factor (χ := χ) (s := s) (τ := τ) hMne c d, norm_mul,
    norm_ofReal_cast M, abs_of_pos hMpos]
  rw [WwAc_integral_bridge (χ := χ) (s := s) (τ := τ) (M := M) c d]
  have hkey := logphase_outer_bound_scaled (A := fun u : ℝ => (M:ℂ)⁻¹ * WwAc χ s u)
    (M := 1) (t := τ) hcd (by linarith) hlam hQ one_pos
    (contDiff_const.mul (WwAc_contDiff hχd s)) hA1 hA2 hdphi hy0 hquad
  simpa only [one_mul] using mul_le_mul_of_nonneg_left hkey (le_of_lt hMpos)

/-! ## Arithmetic providers for the two non-stationary intervals `[1/6,3/4]` and `[5/4,12]` -/

lemma one_div_sub_one_ge_third {y : ℝ} (hy1 : (1/6:ℝ) ≤ y) (hy2 : y ≤ 3/4) :
    (1:ℝ)/3 ≤ |1/y - 1| := by
  have hy0 : (0:ℝ) < y := by linarith
  have h3 : (1:ℝ)/y ≥ 4/3 := by
    have h := one_div_le_one_div_of_le hy0 hy2
    rw [show (1:ℝ)/(3/4) = 4/3 by norm_num] at h
    linarith
  rw [abs_of_nonneg (by linarith)]
  linarith

lemma one_div_sq_le_36 {y : ℝ} (hy1 : (1/6:ℝ) ≤ y) : 1/y^2 ≤ 36 := by
  have hy0 : (0:ℝ) < y := by linarith
  have h : (1:ℝ)/y ≤ 6 := by
    have h2 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/6) hy1
    rw [show (1:ℝ)/(1/6) = 6 by norm_num] at h2
    linarith
  have h4 : (0:ℝ) < 1/y := by positivity
  have heq : (1:ℝ)/y^2 = (1/y)^2 := by
    rw [div_pow, one_pow]
  rw [heq]
  nlinarith [h, h4]

lemma one_div_sub_one_ge_fifth {y : ℝ} (hy1 : (5/4:ℝ) ≤ y) : (1:ℝ)/5 ≤ |1/y - 1| := by
  have hy0 : (0:ℝ) < y := by linarith
  have h : (1:ℝ)/y ≤ 4/5 := by
    have h2 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 5/4) hy1
    rw [show (1:ℝ)/(5/4) = 4/5 by norm_num] at h2
    linarith
  rw [abs_of_nonpos (by linarith)]
  linarith

lemma one_div_sq_le_one {y : ℝ} (hy1 : (1:ℝ) ≤ y) : 1/y^2 ≤ 1 := by
  have hy0 : (0:ℝ) < y := by linarith
  have h : (1:ℝ)/y ≤ 1 := by
    rw [div_le_one hy0]
    linarith
  have h4 : (0:ℝ) < 1/y := by positivity
  have heq : (1:ℝ)/y^2 = (1/y)^2 := by
    rw [div_pow, one_pow]
  rw [heq]
  nlinarith [h, h4]

/-- **The complementary piece is `O((1+K)√N/τ)`.**  Assembly of the four reduction lemmas
with the two instantiations of the per-interval bound. -/
lemma WwC_integral_bound {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K s τ : ℝ} (hK : 0 ≤ K) (hs0 : 0 ≤ s) (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hs1 : (N:ℝ)/4 ≤ s) (hs2 : s ≤ 3*N) (hτ : 4 ≤ τ) :
    ∃ C : ℝ, 0 < C ∧
      ‖∫ u : ℝ, WwC χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖
        ≤ C * (1 + K) * Real.sqrt N / τ := by
  obtain ⟨M, hMpos, hA1, hA2⟩ := WwAc_scaled_bounds hN hχd hχ0 hK hs0 hbdd hs2
  refine ⟨530 * max 4 M, by positivity, ?_⟩
  have hdphi1 : ∀ y ∈ Set.Icc (1/6:ℝ) (3/4), (1:ℝ)/3 ≤ |1 / y - 1| :=
    fun y hy => one_div_sub_one_ge_third hy.1 hy.2
  have hy01 : ∀ y ∈ Set.Icc (1/6:ℝ) (3/4), 0 < y := fun y hy => by linarith [hy.1]
  have hquad1 : ∀ y ∈ Set.Icc (1/6:ℝ) (3/4), 1 / y ^ 2 ≤ 36 :=
    fun y hy => one_div_sq_le_36 hy.1
  have hdphi2 : ∀ y ∈ Set.Icc (5/4:ℝ) 12, (1:ℝ)/5 ≤ |1 / y - 1| :=
    fun y hy => one_div_sub_one_ge_fifth hy.1
  have hy02 : ∀ y ∈ Set.Icc (5/4:ℝ) 12, 0 < y := fun y hy => by linarith [hy.1]
  have hquad2 : ∀ y ∈ Set.Icc (5/4:ℝ) 12, 1 / y ^ 2 ≤ 1 :=
    fun y hy => one_div_sq_le_one (by linarith [hy.1])
  have hb1 : ‖∫ u in (1/6:ℝ)..(3/4),
        WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖
      ≤ M * (τ⁻¹ * 197) := by
    refine le_trans (WwAc_interval_bound (c := (1/6:ℝ)) (d := 3/4) (lam := 1/3) (Q := 36)
      hN hχd hχ0 hK hs0 hbdd hs2 hτ hMpos hA1 hA2 (by norm_num) (by norm_num) (by norm_num)
      hdphi1 hy01 hquad1) ?_
    have hval : τ⁻¹ * (2 / (1/3) + ((3:ℝ)/4 - 1/6) * (1 / (1/3) + 36 / (1/3) ^ 2))
        ≤ τ⁻¹ * 197 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by linarith))
      norm_num
    exact mul_le_mul_of_nonneg_left hval (le_of_lt hMpos)
  have hb2 : ‖∫ u in (5/4:ℝ)..12,
        WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖
      ≤ M * (τ⁻¹ * 333) := by
    refine le_trans (WwAc_interval_bound (c := (5/4:ℝ)) (d := 12) (lam := 1/5) (Q := 1)
      hN hχd hχ0 hK hs0 hbdd hs2 hτ hMpos hA1 hA2 (by norm_num) (by norm_num) (by norm_num)
      hdphi2 hy02 hquad2) ?_
    have hval : τ⁻¹ * (2 / (1/5) + ((12:ℝ) - 5/4) * (1 / (1/5) + 1 / (1/5) ^ 2))
        ≤ τ⁻¹ * 333 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by linarith))
      norm_num
    exact mul_le_mul_of_nonneg_left hval (le_of_lt hMpos)
  have hassm : ‖∫ u : ℝ, WwC χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖
      ≤ ‖∫ u in (1/6:ℝ)..(3/4),
            WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖
        + ‖∫ u in (5/4:ℝ)..12,
            WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖ := by
    rw [WwC_integral_eq_interval hN hχz hs1 hs2,
      WwC_integral_eq_WwAc_integral (χ := χ) (s := s) (τ := τ),
      WwAc_integral_split hχd s τ, WwAc_integral_middle_zero, add_zero]
    exact norm_add_le _ _
  refine le_trans hassm (le_trans (add_le_add hb1 hb2) ?_)
  have hMle : M ≤ max 4 M * (1 + K) * Real.sqrt N := by
    have h1 : (1:ℝ) ≤ (1 + K) * Real.sqrt N := by
      have h2 : (1:ℝ) ≤ Real.sqrt N :=
        Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ N))
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ (1 + K) * Real.sqrt N := mul_le_mul (by linarith) h2 (by norm_num) (by linarith)
    calc M = M * 1 := by ring
      _ ≤ M * ((1 + K) * Real.sqrt N) := mul_le_mul_of_nonneg_left h1 (le_of_lt hMpos)
      _ = M * (1 + K) * Real.sqrt N := by ring
      _ ≤ max 4 M * (1 + K) * Real.sqrt N := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_max_right 4 M) (by linarith)
  have hsum : M * (τ⁻¹ * 197) + M * (τ⁻¹ * 333)
      ≤ (530 * max 4 M) * (1 + K) * Real.sqrt N / τ := by
    have hτinv : (0:ℝ) ≤ τ⁻¹ := inv_nonneg.mpr (by linarith)
    have h1 : M * (τ⁻¹ * 197) + M * (τ⁻¹ * 333) = M * τ⁻¹ * 530 := by ring
    rw [h1]
    have h2 : M * τ⁻¹ ≤ (max 4 M) * (1 + K) * Real.sqrt N * τ⁻¹ :=
      mul_le_mul_of_nonneg_right hMle hτinv
    calc M * τ⁻¹ * 530 ≤ ((max 4 M) * (1 + K) * Real.sqrt N * τ⁻¹) * 530 :=
          mul_le_mul_of_nonneg_right h2 (by norm_num)
      _ = (530 * max 4 M) * (1 + K) * Real.sqrt N / τ := by
          rw [inv_eq_one_div]
          ring
  exact hsum

/-- **Band, first brick.**  Pointwise, the `WwJ` integrand splits into the bumped piece `WwA`
(localised at the stationary point) and the complementary piece `WwC`. -/
lemma WwJ_integrand_split (χ : ℝ → ℝ) (s τ u : ℝ) :
    (((Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s*u) : ℂ)
        * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))
      = WwA χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))
        + WwC χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)) := by
  rw [← Complex.ofReal_mul, ← WwA_add_WwC χ s u, add_mul]

/-- **Zero-padding helper.**  A function vanishing outside `[1/6,12]` has the same integral over
`ℝ` as over that interval. -/
lemma integral_eq_interval_of_support {f : ℝ → ℂ}
    (hf : ∀ u : ℝ, u ∉ Set.Icc (1/6:ℝ) 12 → f u = 0) (hf6 : f (1/6) = 0) :
    (∫ u : ℝ, f u) = ∫ u in (1/6:ℝ)..12, f u := by
  rw [intervalIntegral.integral_of_le (by norm_num : (1/6:ℝ) ≤ 12),
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Set.Ioc (1/6:ℝ) 12
  · rw [Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu]
    by_cases hu2 : u ∈ Set.Icc (1/6:ℝ) 12
    · have hu3 : u = 1/6 := by
        rw [Set.mem_Icc] at hu2
        rw [Set.mem_Ioc, not_and_or, not_lt] at hu
        rcases hu with h | h
        · linarith [hu2.1, h]
        · linarith [hu2.2, h]
      subst hu3
      rw [hf6]
    · rw [hf u hu2]

/-- **E-form bridge (`WwJ` variant).**  The two phase forms used in this file agree:
`Complex.exp (I * ↑(τ*(log u − u))) = Complex.exp (I * (↑τ * ↑(log u − u)))`. -/
lemma exp_form_bridge' (τ u : ℝ) :
    Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) := by
  congr 1
  push_cast
  ring

/-- **Band, brick 1'.**  `WwJ_integrand_split` in `WwJ`'s exact phase form, ready for the
interval split. -/
lemma WwJ_integrand_split' (χ : ℝ → ℝ) (s τ u : ℝ) :
    (((Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s*u) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))
      = WwA χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))
        + WwC χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) := by
  rw [← exp_form_bridge' τ u]
  exact WwJ_integrand_split χ s τ u

/-- **Integral split, item 1.**  In the band parameters the `WwJ` integrand is supported in
`[1/6,12]` (the `χ(s·)`-support argument, with both endpoints of `Icc` included). -/
lemma WwJ_integrand_support {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {s τ : ℝ} (hs1 : (N:ℝ)/4 ≤ s) (hs2 : s ≤ 3*N) {u : ℝ}
    (hu : u ∉ Set.Icc (1/6:ℝ) 12) :
    (((Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s*u) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) = 0 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hlow : (N:ℝ)/2 ≤ (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  have hhigh : (2*N:ℝ) + Real.sqrt N ≤ 3*N := by nlinarith [hsqn, hN4R]
  have hkey : χ (s * u) = 0 := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hu | hu
    · exact hχz _ (Or.inl (by nlinarith [hu, hs2, hlow]))
    · exact hχz _ (Or.inr (by nlinarith [hu, hs1, hhigh]))
  rw [hkey]
  simp

/-- **Integral split, item 1 (endpoint).**  The `WwJ` integrand also vanishes at `u = 1/6`. -/
lemma WwJ_integrand_endpoint {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {s τ : ℝ} (hs2 : s ≤ 3*N) :
    (((Real.sqrt (1/6))⁻¹ : ℝ) : ℂ) * (χ (s*(1/6)) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (1/6) - 1/6 : ℝ) : ℂ))) = 0 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hlow : (N:ℝ)/2 ≤ (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  have hkey : χ (s*(1/6)) = 0 := hχz _ (Or.inl (by nlinarith [hs2, hlow]))
  rw [hkey]
  simp

/-- The bumped amplitude vanishes once `|u − 1| ≥ 2/5` (i.e. outside the support of `WwB`). -/
lemma WwA_eq_zero_of_abs {χ : ℝ → ℝ} {s u : ℝ} (hu : 2/5 ≤ |u - 1|) :
    WwA χ s u = 0 := by
  unfold WwA
  rw [WwB_zero u hu]
  simp

/-- **Integral split, item 2.**  In the band parameters the `WwA` integrand vanishes outside
`[1/6,12]` (both endpoints included: `|1/6 − 1| = 5/6` and `|1/2 − 1| = 1/2` are both `≥ 2/5`). -/
lemma WwA_integrand_support {χ : ℝ → ℝ} {s τ u : ℝ}
    (hu : u ∉ Set.Icc (1/6:ℝ) 12) :
    WwA χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) = 0 := by
  have hA : WwA χ s u = 0 := by
    apply WwA_eq_zero_of_abs
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hu | hu
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      linarith
  rw [hA, zero_mul]

/-- The `WwA` integrand also vanishes at `u = 1/6` (the `hf6` hypothesis of
`integral_eq_interval_of_support`). -/
lemma WwA_integrand_endpoint {χ : ℝ → ℝ} {s τ : ℝ} :
    WwA χ s (1/6) * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (1/6) - 1/6 : ℝ) : ℂ))) = 0 := by
  have h : 2/5 ≤ |(1/6:ℝ) - 1| := by
    rw [abs_of_neg (by norm_num : (1:ℝ)/6 - 1 < 0)]
    norm_num
  rw [WwA_eq_zero_of_abs h, zero_mul]

/-- **Integral split, item 3.**  The complementary integrand vanishes outside `[1/6,12]`. -/
lemma WwC_integrand_support {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {s τ u : ℝ} (hs1 : (N:ℝ)/4 ≤ s) (hs2 : s ≤ 3*N) (hu : u ∉ Set.Icc (1/6:ℝ) 12) :
    WwC χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) = 0 := by
  rw [WwC_eq_zero_of_notMem hN hχz hs1 hs2 hu, zero_mul]

/-- The complementary integrand also vanishes at `u = 1/6`. -/
lemma WwC_integrand_endpoint {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {s τ : ℝ} (hs2 : s ≤ 3*N) :
    WwC χ s (1/6) * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (1/6) - 1/6 : ℝ) : ℂ))) = 0 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hlow : (N:ℝ)/2 ≤ (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
  have hkey : WwC χ s (1/6) = 0 := by
    unfold WwC
    rw [hχz _ (Or.inl (by nlinarith [hs2, hlow]))]
    simp
  rw [hkey, zero_mul]

/-- **Continuity helper** for the common log-phase integrand shape on `[1/6,12]` (transcribed
from the `hc` chain of `WwAc_integral_split`). -/
lemma continuousOn_logPhase_mul {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc (1/6:ℝ) 12)) (τ : ℝ) :
    ContinuousOn (fun u : ℝ => f u *
      Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))) (Set.Icc (1/6:ℝ) 12) := by
  have htau : ContinuousOn (fun _ : ℝ => (τ : ℂ)) (Set.Icc (1/6:ℝ) 12) := continuousOn_const
  have hlog : ContinuousOn (fun u : ℝ => Real.log u) (Set.Icc (1/6:ℝ) 12) :=
    Real.continuousOn_log.mono (fun u hu h0 => by
      rw [h0] at hu
      norm_num at hu)
  have harg : ContinuousOn (fun u : ℝ => (τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))
      (Set.Icc (1/6:ℝ) 12) :=
    htau.mul (Complex.continuous_ofReal.comp_continuousOn (hlog.sub continuousOn_id))
  exact hf.mul (Complex.continuous_exp.comp_continuousOn
    (ContinuousOn.mul (continuousOn_const : ContinuousOn (fun _ : ℝ => Complex.I) (Set.Icc (1/6:ℝ) 12))
      harg))

/-- **Inverse-cast bridge.**  `WwJ` is defined with the complex inverse `((√u)⁻¹ : ℂ)` while all the
integrand lemmas use the cast of the real inverse; the two agree by `Complex.ofReal_inv`. -/
lemma sqrt_inv_cast (u : ℝ) : ((Real.sqrt u)⁻¹ : ℂ) = (((Real.sqrt u)⁻¹ : ℝ) : ℂ) := by
  rw [Complex.ofReal_inv]

/-- **Definitional rewrite of `WwJ` into the cast form** used by the integrand lemmas. -/
lemma WwJ_eq_integral_cast (χ : ℝ → ℝ) (τ s : ℝ) :
    WwJ χ τ s = ∫ u : ℝ, (((Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s*u) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) := by
  rw [WwJ]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [sqrt_inv_cast u]

/-! ## Step 1 of the `WwJ` split: the three zero-padding instances -/

lemma WwF_integral_eq_interval {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {s τ : ℝ} (hs1 : (N:ℝ)/4 ≤ s) (hs2 : s ≤ 3*N) :
    (∫ u : ℝ, (((Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s*u) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
      = ∫ u in (1/6:ℝ)..12, (((Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s*u) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) :=
  integral_eq_interval_of_support
    (f := fun u : ℝ => (((Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s*u) : ℂ)
      * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
    (fun u hu => WwJ_integrand_support hN hχz hs1 hs2 hu)
    (WwJ_integrand_endpoint hN hχz hs2)

lemma WwA_integral_eq_interval {χ : ℝ → ℝ} {s τ : ℝ} :
    (∫ u : ℝ, WwA χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
      = ∫ u in (1/6:ℝ)..12,
          WwA χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) :=
  integral_eq_interval_of_support
    (f := fun u : ℝ => WwA χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
    (fun u hu => WwA_integrand_support hu)
    (WwA_integrand_endpoint (χ := χ) (s := s) (τ := τ))

lemma WwC_integral_eq_interval' {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {s τ : ℝ} (hs1 : (N:ℝ)/4 ≤ s) (hs2 : s ≤ 3*N) :
    (∫ u : ℝ, WwC χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
      = ∫ u in (1/6:ℝ)..12,
          WwC χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) :=
  integral_eq_interval_of_support
    (f := fun u : ℝ => WwC χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
    (fun u hu => WwC_integrand_support hN hχz hs1 hs2 hu)
    (WwC_integrand_endpoint hN hχz hs2)

/-! ## Step 2 of the `WwJ` split: amplitude continuity on `[1/6,12]` -/

lemma continuousOn_sqrt_inv_complex :
    ContinuousOn (fun u : ℝ => (((Real.sqrt u)⁻¹ : ℝ) : ℂ)) (Set.Icc (1/6:ℝ) 12) := by
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  exact (Real.continuous_sqrt.continuousOn).inv₀ (fun u hu => by
    have h : (0:ℝ) < u := by linarith [hu.1]
    exact ne_of_gt (Real.sqrt_pos.mpr h))

lemma continuousOn_chi_comp {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ) (s : ℝ) :
    ContinuousOn (fun u : ℝ => (χ (s*u) : ℂ)) (Set.Icc (1/6:ℝ) 12) :=
  (Complex.continuous_ofReal.comp (hχd.continuous.comp (continuous_const.mul continuous_id))).continuousOn

lemma continuousOn_WwF_amplitude {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ) (s : ℝ) :
    ContinuousOn (fun u : ℝ => (((Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s*u) : ℂ))
      (Set.Icc (1/6:ℝ) 12) :=
  continuousOn_sqrt_inv_complex.mul (continuousOn_chi_comp hχd s)

lemma continuousOn_WwA_amplitude {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ) (s : ℝ) :
    ContinuousOn (fun u : ℝ => WwA χ s u) (Set.Icc (1/6:ℝ) 12) := by
  have h1 : ContinuousOn (fun u : ℝ => (((WwB : ℝ → ℝ) u * (Real.sqrt u)⁻¹ : ℝ) : ℂ))
      (Set.Icc (1/6:ℝ) 12) :=
    (Complex.continuous_ofReal.comp WwB_sqrt_inv_contDiff2.continuous).continuousOn
  exact h1.mul (continuousOn_chi_comp hχd s)

lemma continuousOn_WwC_amplitude {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ) (s : ℝ) :
    ContinuousOn (fun u : ℝ => WwC χ s u) (Set.Icc (1/6:ℝ) 12) := by
  have h0 : ContinuousOn (fun u : ℝ => (1 - (WwB : ℝ → ℝ) u)) (Set.Icc (1/6:ℝ) 12) :=
    (continuous_const.sub (ContDiffBump.contDiff (n := ⊤) WwB).continuous).continuousOn
  have h1 : ContinuousOn (fun u : ℝ => (((1 - (WwB : ℝ → ℝ) u) * (Real.sqrt u)⁻¹ : ℝ) : ℂ))
      (Set.Icc (1/6:ℝ) 12) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    exact h0.mul ((Real.continuous_sqrt.continuousOn).inv₀ (fun u hu => by
      have h : (0:ℝ) < u := by linarith [hu.1]
      exact ne_of_gt (Real.sqrt_pos.mpr h)))
  exact h1.mul (continuousOn_chi_comp hχd s)

/-! ## Step 2b of the `WwJ` split: the three `IntervalIntegrable` instances -/

lemma intervalIntegrable_WwF_integrand {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ) (s τ : ℝ) :
    IntervalIntegrable (fun u : ℝ => (((Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s*u) : ℂ)
      * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
      volume (1/6) 12 := by
  have h : ContinuousOn (fun u : ℝ => (((Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s*u) : ℂ)
      * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))) (Set.uIcc (1/6:ℝ) 12) := by
    rw [Set.uIcc_of_le (by norm_num : (1/6:ℝ) ≤ 12)]
    exact continuousOn_logPhase_mul (continuousOn_WwF_amplitude hχd s) τ
  exact h.intervalIntegrable

lemma intervalIntegrable_WwA_integrand {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ) (s τ : ℝ) :
    IntervalIntegrable (fun u : ℝ => WwA χ s u
      * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
      volume (1/6) 12 := by
  have h : ContinuousOn (fun u : ℝ => WwA χ s u
      * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))) (Set.uIcc (1/6:ℝ) 12) := by
    rw [Set.uIcc_of_le (by norm_num : (1/6:ℝ) ≤ 12)]
    exact continuousOn_logPhase_mul (continuousOn_WwA_amplitude hχd s) τ
  exact h.intervalIntegrable

lemma intervalIntegrable_WwC_integrand {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ) (s τ : ℝ) :
    IntervalIntegrable (fun u : ℝ => WwC χ s u
      * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
      volume (1/6) 12 := by
  have h : ContinuousOn (fun u : ℝ => WwC χ s u
      * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))) (Set.uIcc (1/6:ℝ) 12) := by
    rw [Set.uIcc_of_le (by norm_num : (1/6:ℝ) ≤ 12)]
    exact continuousOn_logPhase_mul (continuousOn_WwC_amplitude hχd s) τ
  exact h.intervalIntegrable

/-- **The `WwJ` integral splits** into the bumped piece and the complementary piece. -/
lemma WwJ_eq_integral_add {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {s τ : ℝ} (hs1 : (N:ℝ)/4 ≤ s) (hs2 : s ≤ 3*N) :
    WwJ χ τ s
      = (∫ u : ℝ, WwA χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
        + ∫ u : ℝ, WwC χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) := by
  rw [WwJ_eq_integral_cast χ τ s, WwF_integral_eq_interval hN hχz hs1 hs2,
    WwA_integral_eq_interval (χ := χ) (s := s) (τ := τ),
    WwC_integral_eq_interval' hN hχz hs1 hs2,
    ← intervalIntegral.integral_add (intervalIntegrable_WwA_integrand hχd s τ)
      (intervalIntegrable_WwC_integrand hχd s τ)]
  apply intervalIntegral.integral_congr
  intro u _
  show (((Real.sqrt u)⁻¹ : ℝ) : ℂ) * (χ (s*u) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))
      = WwA χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))
        + WwC χ s u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))
  exact WwJ_integrand_split' χ s τ u

/-- **Per-`m` band estimate, algebraic factorisation.**  The difference between `WwI χ τ m` and
its stationary-phase main term factors as `√s·e^{iτ log s}` times
`(∫WwA − χ(s)WwFres τ) + ∫WwC`, exposing the two pieces bounded by `WwA_stat` and
`WwC_integral_bound`. -/
lemma WwI_band_factor {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {τ : ℝ} (hτ : 4 ≤ τ) {m : ℕ} (hm : 1 ≤ m)
    (hs1 : (N:ℝ)/4 ≤ τ/(2*Real.pi*(m:ℝ))) (hs2 : τ/(2*Real.pi*(m:ℝ)) ≤ 3*N) :
    WwI χ τ m - ((Real.sqrt (τ/(2*Real.pi*(m:ℝ))) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((τ:ℂ) * ((Real.log (τ/(2*Real.pi*(m:ℝ))) : ℝ) : ℂ)))
        * (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ
      = (((Real.sqrt (τ/(2*Real.pi*(m:ℝ))) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((τ:ℂ) * ((Real.log (τ/(2*Real.pi*(m:ℝ))) : ℝ) : ℂ))))
        * (((∫ u : ℝ, WwA χ (τ/(2*Real.pi*(m:ℝ))) u
              * Complex.exp (Complex.I * ((τ:ℂ) * ((Real.log u - u : ℝ) : ℂ))))
            - (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ)
          + ∫ u : ℝ, WwC χ (τ/(2*Real.pi*(m:ℝ))) u
              * Complex.exp (Complex.I * ((τ:ℂ) * ((Real.log u - u : ℝ) : ℂ)))) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hτ0 : (0:ℝ) < τ := by linarith
  have hs0 : (0:ℝ) < τ/(2*Real.pi*(m:ℝ)) := by positivity
  have hmul : 2*Real.pi*(m:ℝ) * (τ/(2*Real.pi*(m:ℝ))) = τ := by field_simp
  rw [WwI_eq_WwJ χ hs0 hmul, WwJ_eq_integral_add hN hχd hχz hs1 hs2]
  ring

/-! ## Step 5 of the band estimate: the norm peel -/

/-- The unit-modulus exponential in the phase form used throughout this file. -/
lemma norm_exp_I_mul_ofReal (θ : ℝ) : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
  rw [show Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I by ring]
  exact Complex.norm_exp_ofReal_mul_I θ

/-- **Norm peel.**  `‖√s·e^{iτ log s}·X‖ = √s·‖X‖`: the exponential factor has modulus one and
`√s ≥ 0`. -/
lemma norm_sqrt_exp_mul {s τ : ℝ} (X : ℂ) :
    ‖(((Real.sqrt s : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log s : ℝ) : ℂ)))) * X‖
      = Real.sqrt s * ‖X‖ := by
  have he : ‖Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log s : ℝ) : ℂ)))‖ = 1 := by
    rw [show Complex.I * ((τ : ℂ) * ((Real.log s : ℝ) : ℂ))
        = (((τ * Real.log s : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [norm_mul, norm_mul, norm_ofReal_cast, abs_of_nonneg (Real.sqrt_nonneg s), he, mul_one]

/-- **Step 6 arithmetic (i).**  `√(3N)·(1+√N) ≤ 2√3·N` for `N ≥ 1` (uses `1 ≤ √N ≤ 2√N`). -/
lemma sqrt_three_mul_one_add_sqrt_le {N : ℝ} (hN : 1 ≤ N) :
    Real.sqrt (3*N) * (1 + Real.sqrt N) ≤ 2*Real.sqrt 3 * N := by
  have hN0 : (0:ℝ) ≤ N := by linarith
  have hs : Real.sqrt (3*N) = Real.sqrt 3 * Real.sqrt N := Real.sqrt_mul (by norm_num) N
  have hsq : Real.sqrt N * Real.sqrt N = N := by rw [← sq, Real.sq_sqrt hN0]
  have h2 : (1:ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  have h3 : (0:ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h4 : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  rw [hs]
  have h5 : Real.sqrt 3 * Real.sqrt N * (1 + Real.sqrt N)
      ≤ Real.sqrt 3 * Real.sqrt N * (2 * Real.sqrt N) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg h3 h4)
    linarith
  have h6 : Real.sqrt 3 * Real.sqrt N * (2 * Real.sqrt N) = 2 * Real.sqrt 3 * N := by
    rw [show Real.sqrt 3 * Real.sqrt N * (2 * Real.sqrt N)
        = 2 * Real.sqrt 3 * (Real.sqrt N * Real.sqrt N) by ring, hsq]
  linarith [h5, h6]

/-- **Step 6 arithmetic (ii).**  Combining the two error bounds via `norm_add_le` and folding in the
factor `1 + log τ`. -/
lemma WwI_band_bracket_bound {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 4 ≤ τ)
    {Ca Cb Cc K : ℝ} (hCa0 : 0 ≤ Ca) (hCb0 : 0 ≤ Cb) (hCc0 : 0 ≤ Cc) (hK : 0 ≤ K)
    {x y : ℝ} (hy0 : 0 ≤ y)
    (hCa : x ≤ Ca * ((2*Cb+10)*(1+K)*(1+Real.sqrt N)) * (Real.log τ / τ))
    (hCc : y ≤ Cc * (1 + K) * Real.sqrt N / τ) :
    x + y ≤ (Ca * (2*Cb+10) * (1+K) * (1+Real.sqrt N) + Cc*(1+K)*Real.sqrt N)
      * (1 + Real.log τ) / τ := by
  have hτ0 : (0:ℝ) < τ := by linarith
  have hlog : (0:ℝ) ≤ Real.log τ := Real.log_nonneg (by linarith)
  have hCaf : x ≤ Ca * (2*Cb+10) * (1+K) * (1+Real.sqrt N) * (Real.log τ / τ) :=
    le_trans hCa (le_of_eq (by ring))
  have hM : (0:ℝ) ≤ Ca * (2*Cb+10) * (1+K) * (1+Real.sqrt N) := by positivity
  have hC : (0:ℝ) ≤ Cc * (1+K) * Real.sqrt N := by positivity
  refine le_trans (add_le_add hCaf hCc) ?_
  have e1 : Ca * (2*Cb+10) * (1+K) * (1+Real.sqrt N) * (Real.log τ / τ)
      + Cc * (1+K) * Real.sqrt N / τ
      = (Ca * (2*Cb+10) * (1+K) * (1+Real.sqrt N) * Real.log τ
          + Cc * (1+K) * Real.sqrt N) / τ := by
    field_simp
    try ring
  have e2 : (Ca * (2*Cb+10) * (1+K) * (1+Real.sqrt N) + Cc*(1+K)*Real.sqrt N)
        * (1 + Real.log τ) / τ
      = (Ca * (2*Cb+10) * (1+K) * (1+Real.sqrt N) * (1 + Real.log τ)
          + Cc*(1+K)*Real.sqrt N * (1 + Real.log τ)) / τ := by
    rw [add_mul]
  rw [e1, e2, div_le_div_iff₀ hτ0 hτ0]
  nlinarith [hM, hC, hlog, mul_nonneg hM hlog, mul_nonneg hC hlog, hτ0]

/-- **Step 6 arithmetic (iii).**  The constant collapse for the band estimate. -/
lemma sqrt_three_mul_const_collapse {N Ca Cb Cc : ℝ} (hN : 1 ≤ N)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) :
    Real.sqrt (3*N) * (Ca*(2*Cb+10)*(1+Real.sqrt N) + Cc*Real.sqrt N)
      ≤ 2*Real.sqrt 3*(Ca*(2*Cb+10) + Cc)*N := by
  have hN0 : (0:ℝ) ≤ N := by linarith
  have hsN1 : (1:ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  have hsq3N : Real.sqrt (3*N) = Real.sqrt 3 * Real.sqrt N := Real.sqrt_mul (by norm_num) N
  have hsqN : Real.sqrt N * Real.sqrt N = N := by rw [← sq, Real.sq_sqrt hN0]
  rw [hsq3N]
  have hCM : (0:ℝ) ≤ Ca*(2*Cb+10) := by positivity
  have h1 : Ca*(2*Cb+10)*(1+Real.sqrt N) + Cc*Real.sqrt N
      ≤ (2*Ca*(2*Cb+10) + Cc) * Real.sqrt N := by
    have h2 : Ca*(2*Cb+10) ≤ Ca*(2*Cb+10)*Real.sqrt N := by
      have := mul_le_mul_of_nonneg_left hsN1 hCM
      simpa using this
    have h3 : (0:ℝ) ≤ Cc*Real.sqrt N := by positivity
    nlinarith [h2, h3]
  have h2 : (0:ℝ) ≤ Real.sqrt 3 * Real.sqrt N := by positivity
  calc Real.sqrt 3 * Real.sqrt N * (Ca*(2*Cb+10)*(1+Real.sqrt N) + Cc*Real.sqrt N)
      ≤ Real.sqrt 3 * Real.sqrt N * ((2*Ca*(2*Cb+10)+Cc) * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left h1 h2
    _ = Real.sqrt 3 * (2*Ca*(2*Cb+10)+Cc) * N := by
        rw [show Real.sqrt 3 * Real.sqrt N * ((2*Ca*(2*Cb+10)+Cc) * Real.sqrt N)
            = Real.sqrt 3 * (2*Ca*(2*Cb+10)+Cc) * (Real.sqrt N * Real.sqrt N) by ring, hsqN]
    _ ≤ 2*Real.sqrt 3*(Ca*(2*Cb+10)+Cc)*N := by
        apply mul_le_mul_of_nonneg_right _ hN0
        rw [show 2 * Real.sqrt 3 * (Ca*(2*Cb+10) + Cc)
            = Real.sqrt 3 * (2*(Ca*(2*Cb+10) + Cc)) by ring]
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 3)
        linarith

/-- **Fourth phase-form bridge.**  `Complex.exp (I * ↑(τ*(log u − u)))` agrees with the form in
which the casts are distributed, `Complex.exp (I * ↑τ * (↑(log u) − ↑u))` — the shape produced by
`WwA_stat` / `WwC_integral_bound`. -/
lemma exp_form_bridge'' (τ u : ℝ) :
    Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))
      = Complex.exp (Complex.I * τ * ((Real.log u : ℂ) - (u : ℂ))) := by
  congr 1
  push_cast
  ring

/-- **Association bridge.**  The right-associated and left-associated forms of the phase argument
agree (`I * (↑τ * ↑r) = I * ↑τ * ↑r`); this is the push that lets `WwI_band_factor`'s output meet
the `WwA_stat`/`WwC_integral_bound` shapes. -/
lemma exp_form_bridge_comm (τ u : ℝ) :
    Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))
      = Complex.exp (Complex.I * τ * ((Real.log u - u : ℝ) : ℂ)) := by
  congr 1
  ring

/-- **Log-argument association bridge.**  For the *main-term* exponent `τ·log s` (no subtraction)
the two associations of the phase argument agree; this is the companion of
`exp_form_bridge_comm` that the band assembly needs for `√s·e^{iτ log s}`. -/
lemma exp_form_bridge_log (τ s : ℝ) :
    Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log s : ℝ) : ℂ)))
      = Complex.exp (Complex.I * τ * ((Real.log s : ℝ) : ℂ)) := by
  congr 1
  ring

/-! ## Translation lemmas: the two phase forms give the same integrals -/

lemma integral_WwA_exp_form (χ : ℝ → ℝ) (s τ : ℝ) :
    (∫ u : ℝ, WwA χ s u * Complex.exp (Complex.I * τ * ((Real.log u - u : ℝ) : ℂ)))
      = ∫ u : ℝ, WwA χ s u
          * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [exp_form_bridge_comm τ u]

lemma integral_WwC_exp_form (χ : ℝ → ℝ) (s τ : ℝ) :
    (∫ u : ℝ, WwC χ s u * Complex.exp (Complex.I * τ * ((Real.log u - u : ℝ) : ℂ)))
      = ∫ u : ℝ, WwC χ s u
          * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [exp_form_bridge_comm τ u]

/-- **Extracted band arithmetic.**  The final inequality of the band estimate, factored out as a
self-contained arithmetic fact (only `sqrt_three_mul_const_collapse` and `Real.log_nonneg` needed).
This makes `WwI_band_bound` a short application instead of a long `calc`. -/
lemma band_final_arith {N τ s Ca Cb Cc K z : ℝ} (hN : 1 ≤ N) (hτ : 4 ≤ τ)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCc : 0 ≤ Cc) (hK : 0 ≤ K) (hz : 0 ≤ z)
    (hs : Real.sqrt s ≤ Real.sqrt (3*N))
    (h : z ≤ (Ca*(2*Cb+10)*(1+K)*(1+Real.sqrt N) + Cc*(1+K)*Real.sqrt N)
        * (1 + Real.log τ) / τ) :
    Real.sqrt s * z ≤ 2*Real.sqrt 3*(Ca*(2*Cb+10)+Cc)*(1+K)*N*(1+Real.log τ)/τ := by
  have hτ0 : (0:ℝ) < τ := by linarith
  have hlog : (0:ℝ) ≤ Real.log τ := Real.log_nonneg (by linarith)
  have h1 : Real.sqrt s * z ≤ Real.sqrt (3*N)
      * ((Ca*(2*Cb+10)*(1+K)*(1+Real.sqrt N) + Cc*(1+K)*Real.sqrt N)
          * (1 + Real.log τ) / τ) :=
    mul_le_mul hs h hz (Real.sqrt_nonneg _)
  have h3 := sqrt_three_mul_const_collapse hN hCa hCb hCc
  have h2 : Real.sqrt (3*N) * (Ca*(2*Cb+10)*(1+K)*(1+Real.sqrt N) + Cc*(1+K)*Real.sqrt N)
      ≤ 2*Real.sqrt 3*(Ca*(2*Cb+10)+Cc)*(1+K)*N := by
    calc Real.sqrt (3*N) * (Ca*(2*Cb+10)*(1+K)*(1+Real.sqrt N) + Cc*(1+K)*Real.sqrt N)
        = (1+K) * (Real.sqrt (3*N) * (Ca*(2*Cb+10)*(1+Real.sqrt N) + Cc*Real.sqrt N)) := by ring
      _ ≤ (1+K) * (2*Real.sqrt 3*(Ca*(2*Cb+10)+Cc)*N) :=
          mul_le_mul_of_nonneg_left h3 (by linarith)
      _ = 2*Real.sqrt 3*(Ca*(2*Cb+10)+Cc)*(1+K)*N := by ring
  have hY0 : (0:ℝ) ≤ (1 + Real.log τ)/τ := div_nonneg (by linarith) (by linarith)
  have h4 : Real.sqrt (3*N) * ((Ca*(2*Cb+10)*(1+K)*(1+Real.sqrt N) + Cc*(1+K)*Real.sqrt N)
        * (1 + Real.log τ)/τ)
      ≤ (2*Real.sqrt 3*(Ca*(2*Cb+10)+Cc)*(1+K)*N) * (1 + Real.log τ)/τ := by
    calc Real.sqrt (3*N) * ((Ca*(2*Cb+10)*(1+K)*(1+Real.sqrt N) + Cc*(1+K)*Real.sqrt N)
          * (1 + Real.log τ)/τ)
        = (Real.sqrt (3*N) * (Ca*(2*Cb+10)*(1+K)*(1+Real.sqrt N) + Cc*(1+K)*Real.sqrt N))
            * ((1 + Real.log τ)/τ) := by ring
      _ ≤ (2*Real.sqrt 3*(Ca*(2*Cb+10)+Cc)*(1+K)*N) * ((1 + Real.log τ)/τ) :=
          mul_le_mul_of_nonneg_right h2 hY0
      _ = (2*Real.sqrt 3*(Ca*(2*Cb+10)+Cc)*(1+K)*N) * (1 + Real.log τ)/τ := by ring
  exact le_trans h1 h4
/-- **The band index range lands in `[N,2N]`.**  For `m` in the dual range
`[⌈τ/4πN⌉, ⌊τ/2πN⌋]`, the stationary point `s_m = τ/(2πm)` lies in `[N,2N]` — which is exactly where
`χ = 1`, so the main terms of the band sum match `conj(WwK)` term by term. -/
lemma band_s_mem {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 < τ) {m : ℕ}
    (hm : m ∈ Finset.Icc (Nat.ceil (τ/(4*Real.pi*(N:ℝ)))) (Nat.floor (τ/(2*Real.pi*(N:ℝ))))) :
    (N:ℝ) ≤ τ/(2*Real.pi*(m:ℝ)) ∧ τ/(2*Real.pi*(m:ℝ)) ≤ 2*N := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hmem := Finset.mem_Icc.mp hm
  have ha : τ/(4*Real.pi*(N:ℝ)) ≤ (m:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hmem.1)
  have hb : (m:ℝ) ≤ τ/(2*Real.pi*(N:ℝ)) := le_trans (by exact_mod_cast hmem.2) (Nat.floor_le (by positivity))
  have hm0 : (0:ℝ) < (m:ℝ) := by
    have : (0:ℝ) < τ/(4*Real.pi*(N:ℝ)) := by positivity
    linarith
  have hd : (0:ℝ) < 2*Real.pi*(m:ℝ) := by positivity
  constructor
  · rw [le_div_iff₀ hd]
    have h2 : (2*Real.pi*(N:ℝ)) * (m:ℝ) ≤ τ := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(N:ℝ))] at hb
      linarith [hb]
    nlinarith [h2, Real.pi_pos, hm0, hNpos]
  · rw [div_le_iff₀ hd]
    have h2 : τ ≤ (2*Real.pi*((2:ℝ)*N)) * (m:ℝ) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4*Real.pi*(N:ℝ))] at ha
      nlinarith [ha, Real.pi_pos, hm0, hNpos]
    nlinarith [h2, Real.pi_pos, hm0, hNpos]
/-- **Main-term sum identity.**  The band's stationary-phase main terms sum to `WwC0 τ` times the
complex conjugate of the dual sum `WwK` (in the regime `τ ≥ 4πN`, where the dual range starts at
`1`).  Uses `mainTerm_factor` (each summand), `band_s_mem` + the `χ = 1` hypothesis, and
`conj_WwK` (the identification of the reindexed sum). -/
lemma mainTerm_sum_eq {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hχ1 : ∀ y : ℝ, (N:ℝ) ≤ y → y ≤ 2*N → χ y = 1)
    (ha1 : 1 ≤ Nat.ceil (τ/(4*Real.pi*(N:ℝ)))) :
    (∑ m ∈ Finset.Icc (Nat.ceil (τ/(4*Real.pi*(N:ℝ)))) (Nat.floor (τ/(2*Real.pi*(N:ℝ)))),
        ((Real.sqrt (τ/(2*Real.pi*(m:ℝ))) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((τ:ℂ) * (Real.log (τ/(2*Real.pi*(m:ℝ))) : ℂ)))
          * (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ)
      = WwC0 τ * (starRingEnd ℂ) (WwK N τ) := by
  have hstep : ∀ m ∈ Finset.Icc (Nat.ceil (τ/(4*Real.pi*(N:ℝ)))) (Nat.floor (τ/(2*Real.pi*(N:ℝ)))),
      (((Real.sqrt (τ/(2*Real.pi*(m:ℝ))) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((τ:ℂ) * (Real.log (τ/(2*Real.pi*(m:ℝ))) : ℂ)))
          * (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ)
        = WwC0 τ * ((((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((τ:ℂ) * ((Real.log (m:ℝ)):ℂ))))) := by
    intro m hm
    have hm1 : 1 ≤ m := le_trans ha1 (Finset.mem_Icc.mp hm).1
    have hχs : χ (τ/(2*Real.pi*(m:ℝ))) = 1 :=
      hχ1 _ (band_s_mem hN hτ hm).1 (band_s_mem hN hτ hm).2
    rw [hχs]
    simp only [Complex.ofReal_one, mul_one]
    rw [mainTerm_factor hm1 hτ]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, conj_WwK]
/-- **Main-term sum identity, general form.**  Same as `mainTerm_sum_eq` but over the range
`Icc (max ⌈τ/4πN⌉ 1) (⌊τ/2πN⌋)`, which is the correct index set for *all* `τ > 0`: when
`⌈τ/4πN⌉ = 0` the sum over `Icc ⌈τ/4πN⌉ _` would also contain `m = 0`, where `s_0` degenerates;
that term contributes `0` to both sides (`conj_WwK`'s `k = 0` term vanishes) and is removed here by
`Finset.sum_subset`. -/
lemma mainTerm_sum_eq' {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hχ1 : ∀ y : ℝ, (N:ℝ) ≤ y → y ≤ 2*N → χ y = 1) :
    (∑ m ∈ Finset.Icc (max (Nat.ceil (τ/(4*Real.pi*(N:ℝ)))) 1)
          (Nat.floor (τ/(2*Real.pi*(N:ℝ)))),
        ((Real.sqrt (τ/(2*Real.pi*(m:ℝ))) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((τ:ℂ) * (Real.log (τ/(2*Real.pi*(m:ℝ))) : ℂ)))
          * (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ)
      = WwC0 τ * (starRingEnd ℂ) (WwK N τ) := by
  have hstep : ∀ m ∈ Finset.Icc (max (Nat.ceil (τ/(4*Real.pi*(N:ℝ)))) 1)
        (Nat.floor (τ/(2*Real.pi*(N:ℝ)))),
      (((Real.sqrt (τ/(2*Real.pi*(m:ℝ))) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((τ:ℂ) * (Real.log (τ/(2*Real.pi*(m:ℝ))) : ℂ)))
          * (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ)
        = WwC0 τ * ((((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ)
          * Complex.exp (-(Complex.I * ((τ:ℂ) * ((Real.log (m:ℝ)):ℂ))))) := by
    intro m hm
    obtain ⟨hmA, hmB⟩ := Finset.mem_Icc.mp hm
    have hmab : m ∈ Finset.Icc (Nat.ceil (τ/(4*Real.pi*(N:ℝ))))
        (Nat.floor (τ/(2*Real.pi*(N:ℝ)))) :=
      Finset.mem_Icc.mpr ⟨le_trans (le_max_left _ _) hmA, hmB⟩
    have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hmA
    have hχs : χ (τ/(2*Real.pi*(m:ℝ))) = 1 :=
      hχ1 _ (band_s_mem hN hτ hmab).1 (band_s_mem hN hτ hmab).2
    rw [hχs]
    simp only [Complex.ofReal_one, mul_one]
    rw [mainTerm_factor hm1 hτ]
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, conj_WwK]
  congr 1
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    obtain ⟨hmA, hmB⟩ := Finset.mem_Icc.mp hm
    exact Finset.mem_Icc.mpr ⟨le_trans (le_max_left _ _) hmA, hmB⟩
  · intro m hm hnot
    obtain ⟨hmA, hmB⟩ := Finset.mem_Icc.mp hm
    have hlt : m < max (Nat.ceil (τ/(4*Real.pi*(N:ℝ)))) 1 := by
      by_contra hc
      push Not at hc
      exact hnot (Finset.mem_Icc.mpr ⟨hc, hmB⟩)
    have hz : m = 0 := by omega
    rw [hz]
    simp [Real.sqrt_zero]
lemma integral_exp_form_A (A : ℝ → ℂ) (τ : ℝ) :
    (∫ u : ℝ, A u * Complex.exp (Complex.I * τ * ((Real.log u : ℂ) - (u : ℂ))))
      = ∫ u : ℝ, A u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [show Complex.exp (Complex.I * τ * ((Real.log u : ℂ) - (u : ℂ)))
      = Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) from by
        congr 1; push_cast; ring]

lemma integral_exp_form_C (A : ℝ → ℂ) (τ : ℝ) :
    (∫ u : ℝ, A u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ)))
      = ∫ u : ℝ, A u * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [show Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))) from by
        congr 1; push_cast; ring]

lemma WwI_band_bound {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hτ : 4 ≤ τ) {m : ℕ} (hm : 1 ≤ m)
    (hs1 : (N:ℝ)/4 ≤ τ/(2*Real.pi*(m:ℝ))) (hs2 : τ/(2*Real.pi*(m:ℝ)) ≤ 3*N) :
    ∃ C : ℝ, 0 < C ∧
      ‖WwI χ τ m - ((Real.sqrt (τ/(2*Real.pi*(m:ℝ))) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((τ:ℂ) * ((Real.log (τ/(2*Real.pi*(m:ℝ))) : ℝ) : ℂ)))
        * (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ‖
      ≤ C * (1+K) * N * (1 + Real.log τ) / τ := by
  obtain ⟨Cb, hCbpos, hCb⟩ := WwB_deriv_bounded
  obtain ⟨Ca, hCapos, hCa⟩ := WwA_stat (N := N) (s := τ/(2*Real.pi*(m:ℝ))) (τ := τ) (Cb := Cb)
    hCb hCbpos.le (by linarith) hχd hχ0 hbdd (by omega) (by positivity) hK hs2
  obtain ⟨Cc, hCcpos, hCc⟩ := WwC_integral_bound (N := N) (χ := χ) hN hχd hχ0 hχz
    (K := K) (s := τ/(2*Real.pi*(m:ℝ))) (τ := τ) hK (by positivity) hbdd hs1 hs2 hτ
  refine ⟨2*Real.sqrt 3*(Ca*(2*Cb+10)+Cc), by positivity, ?_⟩
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hCa' : ‖(∫ u : ℝ, WwA χ (τ/(2*Real.pi*(m:ℝ))) u
          * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
        - (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ‖
      ≤ Ca * ((2*Cb+10)*(1+K)*(1+Real.sqrt N)) * (Real.log τ / τ) := by
    rw [integral_exp_form_A (WwA χ (τ/(2*Real.pi*(m:ℝ)))) τ] at hCa
    exact hCa
  have hCc' : ‖∫ u : ℝ, WwC χ (τ/(2*Real.pi*(m:ℝ))) u
          * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))‖
      ≤ Cc * (1 + K) * Real.sqrt N / τ := by
    rw [integral_exp_form_C (WwC χ (τ/(2*Real.pi*(m:ℝ)))) τ] at hCc
    exact hCc
  have hbr : ‖(∫ u : ℝ, WwA χ (τ/(2*Real.pi*(m:ℝ))) u
              * Complex.exp (Complex.I * ((τ:ℂ) * ((Real.log u - u : ℝ) : ℂ))))
            - (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ
          + ∫ u : ℝ, WwC χ (τ/(2*Real.pi*(m:ℝ))) u
              * Complex.exp (Complex.I * ((τ:ℂ) * ((Real.log u - u : ℝ) : ℂ)))‖
      ≤ (Ca * (2*Cb+10) * (1+K) * (1+Real.sqrt N) + Cc*(1+K)*Real.sqrt N)
        * (1 + Real.log τ) / τ := by
    refine le_trans (norm_add_le _ _) ?_
    exact WwI_band_bracket_bound hN hτ hCapos.le hCbpos.le hCcpos.le hK (norm_nonneg _) hCa' hCc'
  rw [WwI_band_factor (N := N) hN hχd hχz hτ hm hs1 hs2, norm_sqrt_exp_mul]
  exact band_final_arith hN1 hτ hCapos.le hCbpos.le hCcpos.le hK (norm_nonneg _)
    (Real.sqrt_le_sqrt hs2) hbr

lemma res_bridge (τ x : ℝ) :
    -(Complex.I * ((τ : ℂ) * ((Real.log x : ℝ) : ℂ)))
      = ((((2 * Real.pi) * ((-(τ * Real.log x)) / (2 * Real.pi)) : ℝ)) : ℂ) * Complex.I := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  push_cast
  field_simp
  try ring

noncomputable def resPhi (τ : ℝ) : ℝ → ℝ := fun x => (-(τ * Real.log x)) / (2 * Real.pi)

lemma resPhi_hasDerivAt (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (resPhi τ) (-(τ * x⁻¹) / (2 * Real.pi)) x := by
  have h1 : HasDerivAt (fun x : ℝ => τ * Real.log x) (τ * x⁻¹) x :=
    (Real.hasDerivAt_log (ne_of_gt hx)).const_mul τ
  have h2 : HasDerivAt (fun x : ℝ => -(τ * Real.log x)) (-(τ * x⁻¹)) x := h1.neg
  exact h2.div_const (2 * Real.pi)

lemma resPhi_hasDerivAt' (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -(τ * x⁻¹) / (2 * Real.pi)) (-(τ * (-(x^2)⁻¹)) / (2 * Real.pi)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x⁻¹) (-(x^2)⁻¹) x := hasDerivAt_inv (ne_of_gt hx)
  have h2 : HasDerivAt (fun x : ℝ => τ * x⁻¹) (τ * (-(x^2)⁻¹)) x := h1.const_mul τ
  have h3 : HasDerivAt (fun x : ℝ => -(τ * x⁻¹)) (-(τ * (-(x^2)⁻¹))) x := h2.neg
  exact h3.div_const (2 * Real.pi)

lemma resPhi_deriv (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (resPhi τ) x = -(τ * x⁻¹) / (2 * Real.pi) := (resPhi_hasDerivAt τ hx).deriv

lemma resPhi_deriv2 (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (deriv (resPhi τ)) x = τ / (2 * Real.pi * x^2) := by
  have hev : deriv (resPhi τ) =ᶠ[𝓝 x] (fun y => -(τ * y⁻¹) / (2 * Real.pi)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (0:ℝ) < x from hx)] with y hy
    exact resPhi_deriv τ hy
  rw [hev.deriv_eq]
  rw [(resPhi_hasDerivAt' τ hx).deriv]
  field_simp
  try ring

lemma resPhi_contDiffOn (τ : ℝ) {a b : ℝ} (ha : 1 ≤ a) :
    ContDiffOn ℝ 2 (resPhi τ) (Set.Icc a b) := by
  unfold resPhi
  apply ContDiffOn.div_const
  apply ContDiffOn.neg
  apply ContDiffOn.mul contDiffOn_const
  refine ContDiffOn.log contDiffOn_id ?_
  intro x hx
  exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_trans ha hx.1))

/-- `√(τ/(2π n²)) = √(τ/(2π))/n`. -/
lemma res_sqrt_div (τ : ℝ) (hτ : 0 < τ) {n : ℕ} (hn : 0 < n) :
    Real.sqrt (τ / (2 * Real.pi * (n:ℝ)^2)) = Real.sqrt (τ / (2 * Real.pi)) / (n:ℝ) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h1 : (0:ℝ) < τ / (2*Real.pi) := by positivity
  rw [show τ / (2*Real.pi*(n:ℝ)^2) = (τ/(2*Real.pi)) * ((n:ℝ)^2)⁻¹ by field_simp; try ring]
  rw [Real.sqrt_mul (le_of_lt h1), Real.sqrt_inv, Real.sqrt_sq (le_of_lt hnpos)]
  rfl

lemma res_inv_sqrt_div (τ : ℝ) (hτ : 0 < τ) {n : ℕ} (hn : 0 < n) :
    1 / Real.sqrt (τ / (2 * Real.pi * (n:ℝ)^2)) = Real.sqrt (2 * Real.pi) * (n:ℝ) / Real.sqrt τ := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hst : (0:ℝ) < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hsp : (0:ℝ) < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [res_sqrt_div τ hτ hn]
  have hdiv : Real.sqrt (τ / (2*Real.pi)) = Real.sqrt τ / Real.sqrt (2*Real.pi) :=
    Real.sqrt_div (le_of_lt hτ) (2*Real.pi)
  rw [hdiv]
  field_simp
  try rw [Real.sq_sqrt (le_of_lt hst), Real.sq_sqrt (le_of_lt hsp)]
  try ring

/-- The numeric bracket produced by the second-derivative test is bounded by `Kb`. -/
lemma res_bracket_le (τ : ℝ) (hτ : 0 < τ) {A B n : ℕ} (hA : 2 ≤ A) (hAn : A ≤ n)
    (hnB : n ≤ B) (h2A : B ≤ 2 * A) :
    ((n - A + 1 : ℕ) : ℝ) * Real.sqrt (τ / (2 * Real.pi * (n:ℝ)^2))
        + 1 / Real.sqrt (τ / (2 * Real.pi * (n:ℝ)^2))
      ≤ Real.sqrt (τ / (2 * Real.pi)) * ((((B - A + 1 : ℕ)) : ℝ) / (B : ℝ))
        + Real.sqrt (2 * Real.pi) * (B : ℝ) / Real.sqrt τ := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) (by omega : 2 ≤ n)
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
  have hBpos : (0:ℝ) < (B:ℝ) := by
    have h2 : 2 ≤ B := le_trans hA (le_trans hAn hnB)
    have h2' : (2:ℝ) ≤ (B:ℝ) := by exact_mod_cast h2
    linarith
  have hnB' : (n:ℝ) ≤ (B:ℝ) := by exact_mod_cast hnB
  have hA2R : (2:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
  rw [res_inv_sqrt_div τ hτ hn0, res_sqrt_div τ hτ hn0]
  have hn1 : ((n - A + 1 : ℕ) : ℝ) = (n:ℝ) - (A:ℝ) + 1 := by
    rw [show n - A + 1 = n + 1 - A from by omega, Nat.cast_sub (by omega : A ≤ n + 1)]
    push_cast; ring
  have hB1 : ((B - A + 1 : ℕ) : ℝ) = (B:ℝ) - (A:ℝ) + 1 := by
    rw [show B - A + 1 = B + 1 - A from by omega, Nat.cast_sub (by omega : A ≤ B + 1)]
    push_cast; ring
  have hfrac : ((n:ℝ) - (A:ℝ) + 1) / (n:ℝ) ≤ ((B:ℝ) - (A:ℝ) + 1) / (B:ℝ) := by
    rw [div_le_div_iff₀ hnpos hBpos]
    nlinarith [hA2R, hnB']
  have hs1 : Real.sqrt (τ / (2 * Real.pi)) * (((n:ℝ) - (A:ℝ) + 1) / (n:ℝ))
      ≤ Real.sqrt (τ / (2 * Real.pi)) * (((B:ℝ) - (A:ℝ) + 1) / (B:ℝ)) :=
    mul_le_mul_of_nonneg_left hfrac (by positivity)
  have hs2 : Real.sqrt (2 * Real.pi) * (n:ℝ) / Real.sqrt τ
      ≤ Real.sqrt (2 * Real.pi) * (B:ℝ) / Real.sqrt τ := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg τ)
    exact mul_le_mul_of_nonneg_left hnB' (by positivity)
  rw [hn1, hB1]
  rw [show ((n:ℝ) - (A:ℝ) + 1) * (Real.sqrt (τ / (2 * Real.pi)) / (n:ℝ))
      = Real.sqrt (τ / (2 * Real.pi)) * (((n:ℝ) - (A:ℝ) + 1) / (n:ℝ)) by ring]
  linarith [hs1, hs2]

theorem weighted_log_phase_short_range :
    ∃ C : ℝ, 0 < C ∧ ∀ {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) (h2A : B ≤ 2 * A)
      {τ : ℝ} (hτ : 0 < τ) (w : ℕ → ℂ),
      ‖∑ m ∈ Finset.Icc A B,
          w m * Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (m : ℝ) : ℝ) : ℂ))))‖
        ≤ C * (Real.sqrt (τ / (2 * Real.pi)) * ((((B - A + 1 : ℕ)) : ℝ) / (B : ℝ))
              + Real.sqrt (2 * Real.pi) * (B : ℝ) / Real.sqrt τ + 1)
            * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m + 1)‖) := by
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Commons.Analysis.ExponentialSums.second_derivative_test (B := (16:ℝ)) (by norm_num)
  refine ⟨4 * max 1 C0, by positivity, ?_⟩
  intro A B hA hAB h2A τ hτ w
  have hA1 : 1 ≤ A := by omega
  have hA2R : (2:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA
  have hBpos : (0:ℝ) < (B:ℝ) := by
    have : (2:ℝ) ≤ (B:ℝ) := by
      have h2 : 2 ≤ B := le_trans hA hAB
      exact_mod_cast h2
    linarith
  set Kb : ℝ := Real.sqrt (τ / (2 * Real.pi)) * ((((B - A + 1 : ℕ)) : ℝ) / (B : ℝ))
      + Real.sqrt (2 * Real.pi) * (B : ℝ) / Real.sqrt τ with hKb
  have hKbnn : 0 ≤ Kb := by rw [hKb]; positivity
  have hpre : ∀ n : ℕ, A ≤ n → n ≤ B →
      ‖∑ k ∈ Finset.Icc A n, Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (k : ℝ) : ℝ) : ℂ))))‖
        ≤ max 1 C0 * (Kb + 1) := by
    intro n hAn hnB
    have hn0 : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) (by omega : 2 ≤ n)
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
    have hlo : (1:ℝ) ≤ (A:ℝ) - 1 := by linarith
    have hN1 : 1 ≤ n - A + 1 := by omega
    have hcastN : (A:ℝ) - 1 + (((n - A + 1 : ℕ)) : ℝ) = (n:ℝ) := by
      have h1 : ((n - A + 1 : ℕ) : ℝ) = (n:ℝ) - (A:ℝ) + 1 := by
        rw [show n - A + 1 = n + 1 - A from by omega,
          Nat.cast_sub (by omega : A ≤ n + 1)]
        push_cast; ring
      rw [h1]; ring
    have hca : ((((A:ℤ) - 1 : ℤ)) : ℝ) = (A:ℝ) - 1 := by push_cast; ring
    have hf : ContDiffOn ℝ 2 (resPhi τ)
        (Set.Icc ((((A:ℤ) - 1 : ℤ)) : ℝ) (((((A:ℤ) - 1 : ℤ)) : ℝ) + (((n - A + 1 : ℕ)) : ℝ))) := by
      rw [hca, hcastN]
      exact resPhi_contDiffOn τ hlo
    have hr : 0 < τ / (2 * Real.pi * (n:ℝ)^2) := by positivity
    have hpp : ∀ x ∈ Set.Ioo ((((A:ℤ) - 1 : ℤ)) : ℝ)
        (((((A:ℤ) - 1 : ℤ)) : ℝ) + (((n - A + 1 : ℕ)) : ℝ)),
        τ/(2*Real.pi*(n:ℝ)^2) ≤ deriv (deriv (resPhi τ)) x
        ∧ deriv (deriv (resPhi τ)) x ≤ 16 * (τ/(2*Real.pi*(n:ℝ)^2)) := by
      intro x hx
      rw [hca, hcastN] at hx
      have hx' : (A:ℝ) - 1 < x ∧ x < (n:ℝ) := hx
      have hxpos : 0 < x := by linarith [hx'.1, hlo]
      rw [resPhi_deriv2 τ hxpos]
      have hx2 : x^2 < (n:ℝ)^2 := by nlinarith
      constructor
      · refine div_le_div_of_nonneg_left (le_of_lt hτ) (by positivity) ?_
        exact mul_le_mul_of_nonneg_left (le_of_lt hx2) (by positivity)
      · rw [show 16 * (τ/(2*Real.pi*(n:ℝ)^2)) = τ/((2*Real.pi) * ((n:ℝ)^2/16)) by
            field_simp
            try ring]
        refine div_le_div_of_nonneg_left (le_of_lt hτ) (by positivity) ?_
        have hn4 : (n:ℝ) ≤ 4*(A:ℝ) - 4 := by
          have hBle : (B:ℝ) ≤ 2*(A:ℝ) := by exact_mod_cast h2A
          have hnl : (n:ℝ) ≤ (B:ℝ) := by exact_mod_cast hnB
          linarith
        have hxlo : (n:ℝ)/4 ≤ x := by linarith [hx'.1]
        have hsq : ((n:ℝ)/4)^2 ≤ x^2 := pow_le_pow_left₀ (by positivity) hxlo 2
        have hgoal : (n:ℝ)^2/16 ≤ x^2 := by
          have he : ((n:ℝ)/4)^2 = (n:ℝ)^2/16 := by rw [div_pow]; norm_num
          rw [← he]
          exact hsq
        exact mul_le_mul_of_nonneg_left hgoal (show (0:ℝ) ≤ 2*Real.pi by positivity)
    have hSDT := hC0 (a := ((A:ℤ) - 1)) (N := n - A + 1) hN1 (resPhi τ) hr hf hpp
    have hidx1 : (A:ℤ) - 1 + 1 = (A:ℤ) := by ring
    have hidx2 : (A:ℤ) - 1 + (((n - A + 1 : ℕ)) : ℤ) = (n:ℤ) := by
      have h1 : ((n - A + 1 : ℕ) : ℤ) = (n:ℤ) - (A:ℤ) + 1 := by
        rw [show n - A + 1 = n + 1 - A from by omega,
          Nat.cast_sub (by omega : A ≤ n + 1)]
        push_cast; ring
      rw [h1]; ring
    rw [hidx1, hidx2] at hSDT
    -- bound the numeric bracket by Kb
    have hbrack : ((((n - A + 1 : ℕ)) : ℝ) * Real.sqrt (τ / (2 * Real.pi * (n:ℝ)^2))
        + 1 / Real.sqrt (τ / (2 * Real.pi * (n:ℝ)^2))) ≤ Kb := by
      rw [hKb]
      exact res_bracket_le τ hτ hA hAn hnB h2A
    have hsum_eq : (∑ k ∈ Finset.Icc A n,
          Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (k : ℝ) : ℝ) : ℂ)))))
        = ∑ m ∈ Finset.Icc A n,
            Complex.exp ((((2 * Real.pi * resPhi τ ((m:ℝ))) : ℝ) : ℂ) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [resPhi]
      rw [res_bridge]
    have hbridge :
        (∑ j ∈ Finset.Icc ((A:ℤ)) ((n:ℤ)),
            Complex.exp ((((2 * Real.pi * resPhi τ ((j:ℝ))) : ℝ) : ℂ) * Complex.I))
          = ∑ m ∈ Finset.Icc A n,
              Complex.exp ((((2 * Real.pi * resPhi τ ((m:ℝ))) : ℝ) : ℂ) * Complex.I) := by
      rw [← sum_Icc_int_eq_sum_Icc_nat' A n
        (fun m : ℕ => Complex.exp ((((2 * Real.pi * resPhi τ ((m:ℝ))) : ℝ) : ℂ) * Complex.I))]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hj0 : (0:ℤ) ≤ j := by
        have h1 : (1:ℤ) ≤ (A:ℤ) := by exact_mod_cast hA1
        omega
      have hcast : ((j.toNat : ℕ) : ℝ) = (j:ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg hj0]
      rw [hcast]
    rw [hsum_eq, ← hbridge]
    refine le_trans hSDT ?_
    refine le_trans (mul_le_mul_of_nonneg_left hbrack (le_of_lt hC0pos)) ?_
    have h1 : (0:ℝ) ≤ Kb + 1 := by linarith
    have h2 : C0 ≤ max 1 C0 := le_max_right _ _
    calc C0 * Kb ≤ C0 * (Kb + 1) := by linarith [hC0pos]
      _ ≤ max 1 C0 * (Kb + 1) := mul_le_mul_of_nonneg_right h2 h1
  -- Abel step
  have hswap : (∑ m ∈ Finset.Icc A B, w m * Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (m : ℝ) : ℝ) : ℂ)))))
      = ∑ m ∈ Finset.Icc A B, Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (m : ℝ) : ℝ) : ℂ)))) * w m := by
    apply Finset.sum_congr rfl; intro m hm; ring
  rw [hswap]
  have habel := Commons.Analysis.Summation.abel_prefix_bound
    (fun k : ℕ => Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (k : ℝ) : ℝ) : ℂ)))))
    w (max 1 C0 * (Kb + 1)) (N := A) (M := B) hAB hA1 hpre
  refine le_trans habel ?_
  have h1 : (0:ℝ) ≤ ‖w B‖ + ∑ n ∈ Finset.Icc A (B - 1), ‖w n - w (n + 1)‖ := by positivity
  have h2 : max 1 C0 ≤ 4 * max 1 C0 := by linarith [le_max_left (1:ℝ) C0]
  have h3 : (0:ℝ) ≤ Kb + 1 := by linarith
  calc (max 1 C0 * (Kb + 1)) * ‖w B‖
        + (max 1 C0 * (Kb + 1)) * (∑ n ∈ Finset.Icc A (B - 1), ‖w n - w (n + 1)‖)
      = max 1 C0 * (Kb + 1) * (‖w B‖ + ∑ n ∈ Finset.Icc A (B - 1), ‖w n - w (n + 1)‖) := by
        ring
    _ ≤ (4 * max 1 C0) * (Kb + 1)
          * (‖w B‖ + ∑ n ∈ Finset.Icc A (B - 1), ‖w n - w (n + 1)‖) := by
        have h4 : max 1 C0 * (Kb + 1) ≤ (4 * max 1 C0) * (Kb + 1) :=
          mul_le_mul_of_nonneg_right h2 h3
        exact mul_le_mul_of_nonneg_right h4 h1


open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 800000

/-- The stationary point `s_m = τ/(2πm)`. -/
noncomputable def WwS (τ : ℝ) (m : ℕ) : ℝ := τ / (2 * Real.pi * (m:ℝ))

/-- Lower end of the "good" band `[⌈τ/6πN⌉, ⌊2τ/πN⌋]` where the stationary phase analysis
of `WwI` applies. -/
noncomputable def WwLo (N : ℕ) (τ : ℝ) : ℕ := Nat.ceil (τ / (6 * Real.pi * (N:ℝ)))
/-- Upper end of the good band. -/
noncomputable def WwHi (N : ℕ) (τ : ℝ) : ℕ := Nat.floor (2 * τ / (Real.pi * (N:ℝ)))
/-- Lower end of the dual range `[⌈τ/4πN⌉, ⌊τ/2πN⌋]`. -/
noncomputable def WwDLo (N : ℕ) (τ : ℝ) : ℕ := Nat.ceil (τ / (4 * Real.pi * (N:ℝ)))
/-- Upper end of the dual range. -/
noncomputable def WwDHi (N : ℕ) (τ : ℝ) : ℕ := Nat.floor (τ / (2 * Real.pi * (N:ℝ)))
/-- Lower end of the support range of `χ(s_m)`. -/
noncomputable def WwALo (N : ℕ) (τ : ℝ) : ℕ :=
  Nat.ceil (τ / (2 * Real.pi * ((2*N:ℝ) + Real.sqrt N)))
/-- Upper end of the support range of `χ(s_m)`. -/
noncomputable def WwBHi (N : ℕ) (τ : ℝ) : ℕ :=
  Nat.floor (τ / (2 * Real.pi * ((N:ℝ) - Real.sqrt N)))

/-- The stationary-phase main term of `WwI` at index `m`. -/
noncomputable def WwMain {N : ℕ} (χ : ℝ → ℝ) (τ : ℝ) (m : ℕ) : ℂ :=
  ((Real.sqrt (WwS τ m) : ℝ) : ℂ)
    * Complex.exp (Complex.I * ((τ:ℂ) * ((Real.log (WwS τ m) : ℝ) : ℂ)))
    * (χ (WwS τ m) : ℂ) * WwFres τ

/-- The `m`-dependent factor of the main term (with `χ(s_m)` inserted). -/
noncomputable def WwMainTerm (χ : ℝ → ℝ) (τ : ℝ) (m : ℕ) : ℂ :=
  (((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ)
    * Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (m:ℝ) : ℝ) : ℂ))))
    * (χ (WwS τ m) : ℂ)

lemma WwMain_factor {N : ℕ} {χ : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ) {m : ℕ} (hm : 1 ≤ m) :
    WwMain (N := N) χ τ m = WwC0 τ * WwMainTerm χ τ m := by
  have h := mainTerm_factor (m := m) hm hτ
  simp only [WwMain, WwMainTerm, WwS]
  rw [show ((Real.sqrt (τ / (2 * Real.pi * (m:ℝ))) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (τ / (2 * Real.pi * (m:ℝ))) : ℝ) : ℂ)))
        * (χ (τ / (2 * Real.pi * (m:ℝ))) : ℂ) * WwFres τ
      = (((Real.sqrt (τ / (2 * Real.pi * (m:ℝ))) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log (τ / (2 * Real.pi * (m:ℝ))) : ℝ) : ℂ)))
        * WwFres τ) * (χ (τ / (2 * Real.pi * (m:ℝ))) : ℂ) by ring, h]
  ring

lemma WwS_pos {τ : ℝ} (hτ : 0 < τ) {m : ℕ} (hm : 0 < m) : 0 < WwS τ m := by
  unfold WwS; positivity

lemma WwS_band_mem {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 < τ) {m : ℕ}
    (hm : m ∈ Finset.Icc (WwLo N τ) (WwHi N τ)) :
    (N:ℝ)/4 ≤ WwS τ m ∧ WwS τ m ≤ 3*N ∧ 1 ≤ m := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  have hm1' : τ/(6*Real.pi*(N:ℝ)) ≤ (m:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hm1)
  have hm2' : (m:ℝ) ≤ 2*τ/(Real.pi*(N:ℝ)) :=
    le_trans (by exact_mod_cast hm2) (Nat.floor_le (by positivity))
  have hm0 : (0:ℝ) < (m:ℝ) := by
    have : (0:ℝ) < τ/(6*Real.pi*(N:ℝ)) := by positivity
    linarith
  have hd : (0:ℝ) < 2*Real.pi*(m:ℝ) := by positivity
  have hm1m : 1 ≤ m := by
    rw [WwLo] at hm1
    exact le_trans (Nat.ceil_pos.mpr (by positivity)) hm1
  refine ⟨?_, ?_, hm1m⟩
  · unfold WwS
    rw [le_div_iff₀ hd]
    have hstep : ((N:ℝ)/4) * (2*Real.pi*(m:ℝ))
        ≤ ((N:ℝ)/4) * (2*Real.pi) * (2*τ/(Real.pi*(N:ℝ))) := by
      have h4 : (0:ℝ) ≤ ((N:ℝ)/4) * (2*Real.pi) := by positivity
      have := mul_le_mul_of_nonneg_left hm2' h4
      linarith [this]
    have he : ((N:ℝ)/4) * (2*Real.pi) * (2*τ/(Real.pi*(N:ℝ))) = τ := by
      field_simp
      ring
    linarith [hstep, he]
  · unfold WwS
    rw [div_le_iff₀ hd]
    have he : (3*(N:ℝ)) * (2*Real.pi) * (τ/(6*Real.pi*(N:ℝ))) = τ := by
      field_simp
      ring
    have hstep : (3*(N:ℝ)) * (2*Real.pi) * (τ/(6*Real.pi*(N:ℝ)))
        ≤ (3*(N:ℝ)) * (2*Real.pi) * (m:ℝ) := by
      apply mul_le_mul_of_nonneg_left hm1' (by positivity)
    linarith [hstep, he]

lemma WwD_subset_band {N : ℕ} {τ : ℝ} (hτ : 0 < τ) (hN : 0 < N) :
    Finset.Icc (WwDLo N τ) (WwDHi N τ) ⊆ Finset.Icc (WwLo N τ) (WwHi N τ) := by
  intro m hm
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · have h01 : WwLo N τ ≤ WwDLo N τ := by
      rw [WwLo, WwDLo]
      apply Nat.ceil_mono
      have hN' : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
      apply div_le_div_of_nonneg_left (le_of_lt hτ) (by positivity)
      nlinarith [Real.pi_pos]
    exact le_trans h01 hm1
  · have h01 : WwDHi N τ ≤ WwHi N τ := by
      rw [WwHi, WwDHi]
      apply Nat.floor_mono
      have hN' : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hpos : (0:ℝ) < τ * (Real.pi * (N:ℝ)) := by positivity
      nlinarith [hpos]
    exact le_trans hm2 h01



section Tails

/-- `A₀ := τ/(2N+√N)`, the phase-derivative lower bound at the right end of the support. -/
noncomputable def WwA0 (N : ℕ) (τ : ℝ) : ℝ := τ / ((2*N:ℝ) + Real.sqrt N)

/-- The left-tail phase-derivative lower bound `A₀ - 2πm`. -/
noncomputable def WwLm (N : ℕ) (τ : ℝ) (m : ℤ) : ℝ := WwA0 N τ - 2*Real.pi*(m:ℝ)

/-- Instantiated double-IBP tail bound for `WwI`, with the explicit integral bounds. -/
lemma WwI_tail_pt {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N)
    {m : ℤ} {L : ℝ} (hL : 0 < L)
    (hbd : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      L ≤ |deriv (WwPhi τ (m:ℝ)) y|) :
    ‖WwI χ τ m‖ ≤ 8 * (25*(1+K)/Real.sqrt N
        + 10*(1+K) * (4*τ/(N:ℝ)^2) / L
        + 6*Real.sqrt N * (16*τ/(N:ℝ)^3) / L
        + 6*Real.sqrt N * ((4*τ/(N:ℝ)^2)^2) / L^2) / L^2 := by
  have hmono : MonotoneOn (deriv (WwPhi τ (m:ℝ)))
        (Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N))
      ∨ AntitoneOn (deriv (WwPhi τ (m:ℝ)))
        (Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N)) :=
    Or.inr (antitone_deriv_WwPhi hN hτ.le (m:ℝ))
  have h2 : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      |deriv (deriv (WwPhi τ (m:ℝ))) y| ≤ 4*τ/(N:ℝ)^2 :=
    fun y hy => deriv_deriv_WwPhi_bound hN hτ.le hy.1
  have h3 : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      |iteratedDeriv 3 (WwPhi τ (m:ℝ)) y| ≤ 16*τ/(N:ℝ)^3 :=
    fun y hy => iteratedDeriv3_WwPhi_bound hN hτ.le hy.1
  exact WwI_tail_bound hN hχd hχz hL (by positivity) (by positivity) hmono hbd h2 h3
    (integral_abs_WwGs_le (N:=N) hN hχ0)
    (integral_abs_deriv_WwGs_le (N:=N) hN hχd hχ0 hK hbdd)
    (integral_abs_deriv2_WwGs_le (N:=N) hN hχd hχ0 hK hbdd hdd)

/-- `WwLm` is positive on the left tail. -/
lemma WwLm_pos {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 < τ) {m : ℕ}
    (hm : m ≤ WwLo N τ - 1) :
    0 < WwLm N τ (m:ℤ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have h6 : (0:ℝ) < τ/(6*Real.pi*(N:ℝ)) := by positivity
  have hle : (m:ℝ) ≤ (WwLo N τ : ℝ) - 1 := by
    have hW1 : 1 ≤ WwLo N τ := Nat.ceil_pos.mpr h6
    have hmm : (m : ℝ) ≤ ((WwLo N τ - 1 : ℕ) : ℝ) := by exact_mod_cast hm
    rw [Nat.cast_sub hW1] at hmm
    push_cast at hmm
    linarith
  have hceil : (WwLo N τ : ℝ) < τ/(6*Real.pi*(N:ℝ)) + 1 := by
    rw [WwLo]; exact Nat.ceil_lt_add_one (le_of_lt h6)
  have hm6 : (m:ℝ) < τ/(6*Real.pi*(N:ℝ)) := by linarith
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hden : (0:ℝ) < (2*N:ℝ) + Real.sqrt N := by positivity
  have hstep : 2*Real.pi*(m:ℝ) < τ/(3*N) := by
    have h1 : 2*Real.pi*(m:ℝ) < 2*Real.pi*(τ/(6*Real.pi*(N:ℝ))) := by
      apply mul_lt_mul_of_pos_left hm6 (by positivity)
    have h2 : 2*Real.pi*(τ/(6*Real.pi*(N:ℝ))) = τ/(3*N) := by field_simp; ring
    linarith [h1, h2]
  have h3N : τ/(3*N) ≤ τ/((2*N:ℝ) + Real.sqrt N) := by
    apply div_le_div_of_nonneg_left (le_of_lt hτ) (by positivity)
    nlinarith [hsq, hsqn, hN4R]
  unfold WwLm WwA0
  push_cast
  linarith

/-- Per-term bound on the left tail for positive indices `1 ≤ m ≤ WwLo - 1`. -/
lemma WwI_pos_left_pt {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N)
    {m : ℕ} (hm : m ≤ WwLo N τ - 1) :
    ‖WwI χ τ (m:ℤ)‖ ≤ 8 * (25*(1+K)/Real.sqrt N
        + 10*(1+K) * (4*τ/(N:ℝ)^2) / WwLm N τ (m:ℤ)
        + 6*Real.sqrt N * (16*τ/(N:ℝ)^3) / WwLm N τ (m:ℤ)
        + 6*Real.sqrt N * ((4*τ/(N:ℝ)^2)^2) / (WwLm N τ (m:ℤ))^2) / (WwLm N τ (m:ℤ))^2 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have h6 : (0:ℝ) < τ/(6*Real.pi*(N:ℝ)) := by positivity
  have hle : (m:ℝ) ≤ (WwLo N τ : ℝ) - 1 := by
    have hW1 : 1 ≤ WwLo N τ := Nat.ceil_pos.mpr h6
    have hmm : (m : ℝ) ≤ ((WwLo N τ - 1 : ℕ) : ℝ) := by exact_mod_cast hm
    rw [Nat.cast_sub hW1] at hmm
    push_cast at hmm
    linarith
  have hceil : (WwLo N τ : ℝ) < τ/(6*Real.pi*(N:ℝ)) + 1 := by
    rw [WwLo]; exact Nat.ceil_lt_add_one (le_of_lt h6)
  have hm6 : (m:ℝ) < τ/(6*Real.pi*(N:ℝ)) := by linarith
  have hstep : 2*Real.pi*(m:ℝ) < τ/(3*N) := by
    have h1 : 2*Real.pi*(m:ℝ) < 2*Real.pi*(τ/(6*Real.pi*(N:ℝ))) :=
      mul_lt_mul_of_pos_left hm6 (by positivity)
    have h2 : 2*Real.pi*(τ/(6*Real.pi*(N:ℝ))) = τ/(3*N) := by field_simp; ring
    linarith [h1, h2]
  have hy : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      WwLm N τ (m:ℤ) ≤ |deriv (WwPhi τ (m:ℝ)) y| := by
    intro y hy'
    have hy18 : (1/8:ℝ) < y := by
      have ha2 : (2:ℝ) ≤ (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
      linarith [hy'.1]
    have hy0 : 0 < y := by linarith
    have hy2 : y ≤ (2*N:ℝ) + Real.sqrt N := hy'.2
    rw [deriv_WwPhi hy18]
    have h3N : τ/(3*N) ≤ τ/((2*N:ℝ) + Real.sqrt N) := by
      apply div_le_div_of_nonneg_left (le_of_lt hτ) (by positivity)
      nlinarith [hsq, hsqn, hN4R]
    have hA0 : WwLm N τ (m:ℤ) = WwA0 N τ - 2*Real.pi*(m:ℝ) := rfl
    have hyinv : τ/((2*N:ℝ) + Real.sqrt N) ≤ τ * y⁻¹ := by
      apply div_le_div_of_nonneg_left (le_of_lt hτ) (by positivity)
      exact hy2
    have hpos : 0 ≤ τ * y⁻¹ - 2*Real.pi*(m:ℝ) := by
      have h1 : 2*Real.pi*(m:ℝ) < τ/((2*N:ℝ) + Real.sqrt N) := lt_of_lt_of_le hstep h3N
      linarith [h1, hyinv]
    rw [abs_of_nonneg hpos]
    unfold WwLm WwA0
    push_cast
    linarith [hyinv]
  exact WwI_tail_pt hN hχd hχ0 hχz hK hτ hbdd hdd (WwLm_pos hN hτ hm) hy

end Tails


section TailSums

lemma WwLm_ge_eighteen {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 < τ) {m : ℤ}
    (hm : m ≤ (WwLo N τ : ℤ) - 1) : τ/(18*N) ≤ WwLm N τ m := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have h6 : (0:ℝ) < τ/(6*Real.pi*(N:ℝ)) := by positivity
  have hceil : (WwLo N τ : ℝ) < τ/(6*Real.pi*(N:ℝ)) + 1 := by
    rw [WwLo]; exact Nat.ceil_lt_add_one (le_of_lt h6)
  have hml : (m:ℝ) ≤ (WwLo N τ : ℝ) - 1 := by
    have h2 : (m:ℝ) ≤ ((((WwLo N τ : ℤ) - 1 : ℤ)) : ℝ) := by exact_mod_cast hm
    have h3 : ((((WwLo N τ : ℤ) - 1 : ℤ)) : ℝ) = (WwLo N τ : ℝ) - 1 := by push_cast; ring
    linarith [h2, h3]
  have hm' : (m:ℝ) < τ/(6*Real.pi*(N:ℝ)) := by linarith
  have hstep : 2*Real.pi*(m:ℝ) < τ/(3*N) := by
    have h1 : 2*Real.pi*(m:ℝ) < 2*Real.pi*(τ/(6*Real.pi*(N:ℝ))) :=
      mul_lt_mul_of_pos_left hm' (by positivity)
    have h2 : 2*Real.pi*(τ/(6*Real.pi*(N:ℝ))) = τ/(3*N) := by field_simp; ring
    linarith [h1, h2]
  have hmain : (1:ℝ)/(18*N) ≤ 1/((2*N:ℝ) + Real.sqrt N) - 1/(3*N) := by
    have he : 1/((2*N:ℝ) + Real.sqrt N) - 1/(3*N)
        = ((3*N) - ((2*N:ℝ) + Real.sqrt N))/(((2*N:ℝ) + Real.sqrt N)*(3*N)) := by
      field_simp
      try ring
    rw [he, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hsq, hsqn, hN4R, sq_nonneg (4*(N:ℝ) - 7*Real.sqrt N)]
  have hkey : τ/(18*N) ≤ τ/((2*N:ℝ) + Real.sqrt N) - τ/(3*N) := by
    rw [show τ/(18*N) = τ * ((1:ℝ)/(18*N)) by ring,
      show τ/((2*N:ℝ) + Real.sqrt N) - τ/(3*N)
        = τ * ((1:ℝ)/((2*N:ℝ) + Real.sqrt N) - 1/(3*N)) by ring]
    exact mul_le_mul_of_nonneg_left hmain (le_of_lt hτ)
  have h3N : τ/(3*N) ≤ τ/((2*N:ℝ) + Real.sqrt N) := by
    apply div_le_div_of_nonneg_left (le_of_lt hτ) (by positivity)
    nlinarith [hsq, hsqn, hN4R]
  unfold WwLm WwA0
  push_cast
  linarith [hstep, h3N, hkey]

end TailSums


section TailSums2

/-- Per-term bound on the right tail. -/
lemma WwI_right_pt {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hNτ : (N:ℝ) ≤ τ)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N)
    {m : ℕ} (hm : WwHi N τ + 1 ≤ m) :
    ‖WwI χ τ (m:ℤ)‖ ≤ 8 * (25*(1+K)/Real.sqrt N
        + 10*(1+K) * (4*τ/(N:ℝ)^2) / (Real.pi*(m:ℝ))
        + 6*Real.sqrt N * (16*τ/(N:ℝ)^3) / (Real.pi*(m:ℝ))
        + 6*Real.sqrt N * ((4*τ/(N:ℝ)^2)^2) / (Real.pi*(m:ℝ))^2) / (Real.pi*(m:ℝ))^2 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hmpos : (0:ℝ) < (m:ℝ) := by
    have h0 : 0 < m := lt_of_lt_of_le (by positivity : 0 < WwHi N τ + 1) hm
    exact_mod_cast h0
  have hm2 : 2*τ/(Real.pi*(N:ℝ)) < (m:ℝ) := by
    have h1 : ((WwHi N τ : ℕ) : ℝ) + 1 ≤ (m:ℝ) := by
      have := hm
      push_cast
      exact_mod_cast this
    have h2 : 2*τ/(Real.pi*(N:ℝ)) - 1 < ((WwHi N τ : ℕ) : ℝ) := by
      rw [WwHi]
      have := Nat.lt_floor_add_one (2*τ/(Real.pi*(N:ℝ)))
      push_cast
      linarith
    linarith
  have hy : ∀ y ∈ Set.Icc ((N:ℝ) - Real.sqrt N) ((2*N:ℝ) + Real.sqrt N),
      Real.pi*(m:ℝ) ≤ |deriv (WwPhi τ (m:ℝ)) y| := by
    intro y hy'
    have hy18 : (1/8:ℝ) < y := by
      have ha2 : (2:ℝ) ≤ (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
      linarith [hy'.1]
    have hy0 : 0 < y := by linarith
    rw [deriv_WwPhi hy18]
    have hle : τ * y⁻¹ ≤ 2*τ/N := by
      have h1 : y⁻¹ ≤ ((N:ℝ) - Real.sqrt N)⁻¹ := by
        have h2 : (0:ℝ) < (N:ℝ) - Real.sqrt N := by
          nlinarith [hsq, hsqn, hN4R]
        apply inv_anti₀ h2
        exact hy'.1
      have h3 : ((N:ℝ) - Real.sqrt N)⁻¹ ≤ 2/(N:ℝ) := by
        have ha : (0:ℝ) < (N:ℝ) - Real.sqrt N := by nlinarith [hsq, hsqn, hN4R]
        rw [show ((N:ℝ) - Real.sqrt N)⁻¹ = 1/((N:ℝ) - Real.sqrt N) by rw [one_div]]
        rw [div_le_div_iff₀ ha (by positivity : (0:ℝ) < N)]
        nlinarith [hsq, hsqn, hN4R]
      calc τ * y⁻¹ = τ * y⁻¹ := rfl
        _ ≤ τ * ((N:ℝ) - Real.sqrt N)⁻¹ := by
            exact mul_le_mul_of_nonneg_left h1 (le_of_lt hτ)
        _ ≤ τ * (2/(N:ℝ)) := mul_le_mul_of_nonneg_left h3 (le_of_lt hτ)
        _ = 2*τ/N := by ring
    have hbig : 2*τ/N < Real.pi*(m:ℝ) := by
      have h2 : (2*τ/N)/Real.pi < (m:ℝ) := by
        have := hm2
        rw [show 2*τ/(Real.pi*(N:ℝ)) = (2*τ/N)/Real.pi by ring] at this
        linarith
      have h3 : 2*τ/N < (m:ℝ) * Real.pi := by
        rw [div_lt_iff₀ Real.pi_pos] at h2
        linarith
      linarith [h3]
    have hneg : τ * y⁻¹ - 2*Real.pi*(m:ℝ) ≤ 0 := by
      have h4 : Real.pi*(m:ℝ) ≤ 2*Real.pi*(m:ℝ) := by nlinarith [Real.pi_pos, hmpos]
      linarith [hle, hbig, h4]
    rw [abs_of_nonpos hneg]
    linarith
  exact WwI_tail_pt hN hχd hχ0 hχz hK hτ hbdd hdd (by positivity) hy

end TailSums2


open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 800000

/-- Combined far-tail bound: the three `p`-series tails (`p = 2,3,4`) with a common constant. -/
lemma tsum_int_tail_three :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ) (hK : 1 ≤ K),
      (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^2)⁻¹ else 0))
        + (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^3)⁻¹ else 0))
        + (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^4)⁻¹ else 0))
        ≤ C * (K ^ (1 - (2:ℝ)) + K ^ (1 - (3:ℝ)) + K ^ (1 - (4:ℝ))) := by
  obtain ⟨C₂, h₂pos, h₂⟩ := Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le
  obtain ⟨C₃, h₃pos, h₃⟩ := Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le
  obtain ⟨C₄, h₄pos, h₄⟩ := Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le
  refine ⟨C₂ + C₃ + C₄, by positivity, ?_⟩
  intro K hK
  have hKpos : (0:ℝ) < K := by linarith
  have h1 := h₂ 2 K (by norm_num) hK
  have h2 := h₃ 3 K (by norm_num) hK
  have h3 := h₄ 4 K (by norm_num) hK
  have e2 : K ^ (1 - ((2:ℕ):ℝ)) = K ^ (1 - (2:ℝ)) := rfl
  have e3 : K ^ (1 - ((3:ℕ):ℝ)) = K ^ (1 - (3:ℝ)) := rfl
  have e4 : K ^ (1 - ((4:ℕ):ℝ)) = K ^ (1 - (4:ℝ)) := rfl
  have h1' : (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^2)⁻¹ else 0)) ≤ C₂ * K ^ (1 - (2:ℝ)) := by
    simpa using h1
  have h2' : (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^3)⁻¹ else 0)) ≤ C₃ * K ^ (1 - (3:ℝ)) := by
    simpa using h2
  have h3' : (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^4)⁻¹ else 0)) ≤ C₄ * K ^ (1 - (4:ℝ)) := by
    simpa using h3
  have hA : (0:ℝ) < K ^ (1 - (2:ℝ)) := by positivity
  have hB : (0:ℝ) < K ^ (1 - (3:ℝ)) := by positivity
  have hC : (0:ℝ) < K ^ (1 - (4:ℝ)) := by positivity
  have e : (C₂ + C₃ + C₄) * (K ^ (1 - (2:ℝ)) + K ^ (1 - (3:ℝ)) + K ^ (1 - (4:ℝ)))
      = (C₂ * K ^ (1 - (2:ℝ)) + C₃ * K ^ (1 - (3:ℝ)) + C₄ * K ^ (1 - (4:ℝ)))
        + (C₂ * K ^ (1 - (3:ℝ)) + C₂ * K ^ (1 - (4:ℝ)) + C₃ * K ^ (1 - (2:ℝ))
           + C₃ * K ^ (1 - (4:ℝ)) + C₄ * K ^ (1 - (2:ℝ)) + C₄ * K ^ (1 - (3:ℝ))) := by ring
  rw [e]
  have hS : (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^2)⁻¹ else 0))
        + (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^3)⁻¹ else 0))
        + (∑' k : ℤ, (if K ≤ |(k:ℝ)| then ((|(k:ℝ)|)^4)⁻¹ else 0))
      ≤ C₂ * K ^ (1 - (2:ℝ)) + C₃ * K ^ (1 - (3:ℝ)) + C₄ * K ^ (1 - (4:ℝ)) := by
    linarith [h1', h2', h3']
  have hT : 0 ≤ C₂ * K ^ (1 - (3:ℝ)) + C₂ * K ^ (1 - (4:ℝ)) + C₃ * K ^ (1 - (2:ℝ))
           + C₃ * K ^ (1 - (4:ℝ)) + C₄ * K ^ (1 - (2:ℝ)) + C₄ * K ^ (1 - (3:ℝ)) := by positivity
  exact le_trans hS (le_add_of_nonneg_right hT)


section ShiftPSeries

/-- Telescoping bound: `1/(c+n)^2 ≤ (1 + 1/c)(1/(c+n) - 1/(c+n+1))` for `c > 0`. -/
lemma inv_sq_le_telescope {c : ℝ} (hc : 0 < c) (n : ℕ) :
    1/(((n:ℝ) + c)^2) ≤ (1 + 1/c) * (1/((n:ℝ) + c) - 1/((n:ℝ) + c + 1)) := by
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h1 : (0:ℝ) < (n:ℝ) + c := by positivity
  have h2 : (0:ℝ) < (n:ℝ) + c + 1 := by linarith
  have key : 1/(((n:ℝ) + c)^2)
      = (1/((n:ℝ)+c) - 1/((n:ℝ)+c+1)) * (1 + 1/((n:ℝ)+c)) := by
    field_simp
    ring
  have hdiff : 0 ≤ 1/((n:ℝ)+c) - 1/((n:ℝ)+c+1) := by
    have h : 1/((n:ℝ)+c+1) ≤ 1/((n:ℝ)+c) := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) < (n:ℝ)+c)
      linarith [hn0]
    linarith
  have hle : 1 + 1/((n:ℝ)+c) ≤ 1 + 1/c := by
    have h : 1/((n:ℝ)+c) ≤ 1/c := by
      apply div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) hc
      linarith [hn0]
    linarith
  rw [key, mul_comm ((1:ℝ) + 1/c) (1/((n:ℝ)+c) - 1/((n:ℝ)+c+1))]
  exact mul_le_mul_of_nonneg_left hle hdiff

/-- Telescoping sum: `∑_{n<N} 1/(c+n)^2 ≤ 2/c + 2/c^2`. -/
lemma sum_range_inv_add_sq_le {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1/(((n:ℝ) + c)^2) ≤ 2/c + 2/c^2 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp; positivity
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [Finset.sum_range_succ']
  have hbase : 1/((((0:ℕ):ℝ) + c)^2) = 1/c^2 := by norm_num
  rw [hbase]
  have htel : ∑ n ∈ Finset.range M,
      (1/((((n+1:ℕ):ℝ) + c)) - 1/((((n+1:ℕ):ℝ) + c) + 1))
      = 1/(1 + c) - 1/((M:ℝ) + 1 + c) := by
    have hfun : ∀ n : ℕ, (1/((((n+1:ℕ):ℝ) + c)) - 1/((((n+1:ℕ):ℝ) + c) + 1))
        = (fun k : ℕ => 1/((k:ℝ) + (1+c))) n - (fun k : ℕ => 1/((k:ℝ) + (1+c))) (n+1) := by
      intro n
      simp only
      push_cast
      ring_nf
    rw [Finset.sum_congr rfl (fun n _ => hfun n), Finset.sum_range_sub']
    simp only [Nat.cast_zero, zero_add]
    congr 1
    ring
  have hterm : ∀ n ∈ Finset.range M,
      1/((((n+1:ℕ):ℝ) + c)^2)
        ≤ (1 + 1/c) * (1/((((n+1:ℕ):ℝ) + c)) - 1/((((n+1:ℕ):ℝ) + c) + 1)) :=
    fun n _ => inv_sq_le_telescope hc (n+1)
  have hsum : ∑ n ∈ Finset.range M, 1/((((n+1:ℕ):ℝ) + c)^2)
      ≤ (1 + 1/c) * (1/(1 + c) - 1/((M:ℝ) + 1 + c)) := by
    calc ∑ n ∈ Finset.range M, 1/((((n+1:ℕ):ℝ) + c)^2)
        ≤ ∑ n ∈ Finset.range M,
            (1 + 1/c) * (1/((((n+1:ℕ):ℝ) + c)) - 1/((((n+1:ℕ):ℝ) + c) + 1)) :=
          Finset.sum_le_sum hterm
      _ = (1 + 1/c) * ∑ n ∈ Finset.range M,
            (1/((((n+1:ℕ):ℝ) + c)) - 1/((((n+1:ℕ):ℝ) + c) + 1)) := by
          rw [Finset.mul_sum]
      _ = (1 + 1/c) * (1/(1 + c) - 1/((M:ℝ) + 1 + c)) := by rw [htel]
  have hc1 : (1 + 1/c) * (1/(1+c)) ≤ 2/c := by
    have h : (1 + 1/c) * (1/(1+c)) = 1/c := by field_simp; ring
    rw [h]
    exact div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) hc.le
  have hlast : (0:ℝ) < 1/((M:ℝ) + 1 + c) := by positivity
  have hfin : (1 + 1/c) * (1/(1 + c) - 1/((M:ℝ) + 1 + c)) ≤ 2/c := by
    have hA : 1/(1 + c) - 1/((M:ℝ) + 1 + c) ≤ 1/(1+c) := by linarith [hlast]
    have hB := mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ 1 + 1/c)
    linarith [hB, hc1]
  have h1c : (0:ℝ) < 1/c^2 := by positivity
  have h2c : 1/c^2 ≤ 2/c^2 := div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 2) (by positivity)
  linarith [hsum, hfin, h1c, h2c]

/-- Finset form of the shifted `p`-series bound. -/
lemma finset_sum_inv_add_sq_le {c : ℝ} (hc : 0 < c) (u : Finset ℕ) :
    ∑ n ∈ u, 1/(((n:ℝ) + c)^2) ≤ 2/c + 2/c^2 := by
  rcases u.eq_empty_or_nonempty with h | ⟨m, hm⟩
  · rw [h]; simp; positivity
  · have hsub : u ⊆ Finset.range (u.max' ⟨m, hm⟩ + 1) := by
      intro x hx
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_max' u x hx)
    calc ∑ n ∈ u, 1/(((n:ℝ) + c)^2)
        ≤ ∑ n ∈ Finset.range (u.max' ⟨m, hm⟩ + 1), 1/(((n:ℝ) + c)^2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
      _ ≤ 2/c + 2/c^2 := sum_range_inv_add_sq_le hc _

lemma summable_nat_inv_add_sq {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => 1/(((n:ℝ) + c)^2)) :=
  summable_of_sum_le (fun n => by positivity) (finset_sum_inv_add_sq_le hc)

/-- Shifted `p`-series bound (`k = 2`) over `ℕ`. -/
lemma tsum_nat_inv_add_sq_le {c : ℝ} (hc : 0 < c) :
    ∑' n : ℕ, 1/(((n:ℝ) + c)^2) ≤ 2/c + 2/c^2 :=
  Summable.tsum_le_of_sum_le (summable_nat_inv_add_sq hc) (finset_sum_inv_add_sq_le hc)

/-- Shifted `p`-series bound over `ℕ`, all `k ≥ 2`. -/
lemma tsum_nat_inv_add_pow_le (k : ℕ) (hk : 2 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∑' n : ℕ, 1/(((n:ℝ) + c)^k) ≤ (1/c^(k-2)) * (2/c + 2/c^2) := by
  have h2 := tsum_nat_inv_add_sq_le hc
  have h2s := summable_nat_inv_add_sq hc
  have hcmp : ∀ n : ℕ,
      1/(((n:ℝ) + c)^k) ≤ (1/c^(k-2)) * (1/(((n:ℝ) + c)^2)) := by
    intro n
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h1 : (0:ℝ) < (n:ℝ) + c := by positivity
    have hck : (0:ℝ) < c^(k-2) := by positivity
    have hlep : c^(k-2) ≤ ((n:ℝ)+c)^(k-2) :=
      pow_le_pow_left₀ hc.le (by linarith [hn0]) (k-2)
    have hpow : ((n:ℝ)+c)^k = ((n:ℝ)+c)^2 * ((n:ℝ)+c)^(k-2) := by
      rw [← pow_add]; congr 1; omega
    have hsplit : 1/(((n:ℝ) + c)^k) = (1/(((n:ℝ)+c)^2)) * (1/(((n:ℝ)+c)^(k-2))) := by
      rw [hpow, div_mul_div_comm]
      norm_num
    have hfin : (1/(((n:ℝ)+c)^2)) * (1/(((n:ℝ)+c)^(k-2)))
        ≤ (1/(((n:ℝ)+c)^2)) * (1/c^(k-2)) :=
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity : (0:ℝ) < c^(k-2)) hlep) (by positivity)
    rw [hsplit]
    calc (1/(((n:ℝ)+c)^2)) * (1/(((n:ℝ)+c)^(k-2)))
        ≤ (1/(((n:ℝ)+c)^2)) * (1/c^(k-2)) := hfin
      _ = (1/c^(k-2)) * (1/(((n:ℝ)+c)^2)) := by ring
  refine le_trans (Summable.tsum_le_tsum hcmp ?_ ?_) ?_
  · exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => hcmp n) (h2s.mul_left _)
  · exact h2s.mul_left _
  · rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)

end ShiftPSeries


section TailArith

/-- Arithmetic: the double-IBP per-term tail bound with `L ≥ τ/(18N)` is `≤ 10^9(1+K)N/τ`. -/
lemma tail_left_arith {N τ L K : ℝ} (hN : 1 ≤ N) (hτN : N ≤ τ) (hK : 0 ≤ K)
    (hL : 0 < L) (hLD : τ/(18*N) ≤ L) :
    8 * (25*(1+K)/Real.sqrt N
        + 10*(1+K) * (4*τ/N^2) / L
        + 6*Real.sqrt N * (16*τ/N^3) / L
        + 6*Real.sqrt N * ((4*τ/N^2)^2) / L^2) / L^2
      ≤ 1000000000 * (1+K) * N / τ := by
  have hNpos : (0:ℝ) < N := by linarith
  have hτpos : (0:ℝ) < τ := by linarith
  have hτ1 : (1:ℝ) ≤ τ := le_trans hN hτN
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  have hsqrtpos : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hK1 : (0:ℝ) ≤ 1 + K := by linarith
  have hDpos : (0:ℝ) < τ/(18*N) := by positivity
  have h1L : 1/L ≤ 18*N/τ := by
    rw [div_le_div_iff₀ hL hτpos]
    have h := mul_le_mul_of_nonneg_right hLD (by positivity : (0:ℝ) ≤ 18*N)
    rw [div_mul_cancel₀ _ (by positivity : (18:ℝ)*N ≠ 0)] at h
    linarith
  have h2L : (1/L)^2 ≤ (18*N/τ)^2 := pow_le_pow_left₀ (by positivity) h1L 2
  have h3L : (1/L)^3 ≤ (18*N/τ)^3 := pow_le_pow_left₀ (by positivity) h1L 3
  have h4L : (1/L)^4 ≤ (18*N/τ)^4 := pow_le_pow_left₀ (by positivity) h1L 4
  have e : 8 * (25*(1+K)/Real.sqrt N
      + 10*(1+K) * (4*τ/N^2) / L
      + 6*Real.sqrt N * (16*τ/N^3) / L
      + 6*Real.sqrt N * ((4*τ/N^2)^2) / L^2) / L^2
      = 8 * (25*(1+K)/Real.sqrt N * (1/L)^2
        + 10*(1+K) * (4*τ/N^2) * (1/L)^3
        + 6*Real.sqrt N * (16*τ/N^3) * (1/L)^3
        + 6*Real.sqrt N * ((4*τ/N^2)^2) * (1/L)^4) := by
    field_simp
    try ring
  rw [e]
  have hA : 25*(1+K)/Real.sqrt N * (1/L)^2 ≤ 25*(1+K)/Real.sqrt N * (18*N/τ)^2 :=
    mul_le_mul_of_nonneg_left h2L (by positivity)
  have hB : 10*(1+K) * (4*τ/N^2) * (1/L)^3 ≤ 10*(1+K) * (4*τ/N^2) * (18*N/τ)^3 :=
    mul_le_mul_of_nonneg_left h3L (by positivity)
  have hC : 6*Real.sqrt N * (16*τ/N^3) * (1/L)^3 ≤ 6*Real.sqrt N * (16*τ/N^3) * (18*N/τ)^3 :=
    mul_le_mul_of_nonneg_left h3L (by positivity)
  have hE : 6*Real.sqrt N * ((4*τ/N^2)^2) * (1/L)^4 ≤ 6*Real.sqrt N * ((4*τ/N^2)^2) * (18*N/τ)^4 :=
    mul_le_mul_of_nonneg_left h4L (by positivity)
  have hsum : 8 * (25*(1+K)/Real.sqrt N * (1/L)^2
        + 10*(1+K) * (4*τ/N^2) * (1/L)^3
        + 6*Real.sqrt N * (16*τ/N^3) * (1/L)^3
        + 6*Real.sqrt N * ((4*τ/N^2)^2) * (1/L)^4)
      ≤ 8 * (25*(1+K)/Real.sqrt N * (18*N/τ)^2
        + 10*(1+K) * (4*τ/N^2) * (18*N/τ)^3
        + 6*Real.sqrt N * (16*τ/N^3) * (18*N/τ)^3
        + 6*Real.sqrt N * ((4*τ/N^2)^2) * (18*N/τ)^4) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    linarith [hA, hB, hC, hE]
  refine le_trans hsum ?_
  -- explicit evaluation of the four terms
  have e1 : 25*(1+K)/Real.sqrt N * (18*N/τ)^2 = 8100*(1+K) * N * Real.sqrt N / τ^2 := by
    rw [div_mul_eq_mul_div, div_pow]
    field_simp
    rw [Real.sq_sqrt hNpos.le]
    ring
  have e2 : 10*(1+K) * (4*τ/N^2) * (18*N/τ)^3 = 233280*(1+K)/τ^2 * N := by
    rw [div_pow]
    field_simp
    ring
  have e3 : 6*Real.sqrt N * (16*τ/N^3) * (18*N/τ)^3 = 559872*Real.sqrt N/τ^2 := by
    rw [div_pow]
    field_simp
    ring
  have e4 : 6*Real.sqrt N * ((4*τ/N^2)^2) * (18*N/τ)^4 = 10077696*Real.sqrt N/τ^2 := by
    rw [div_pow]
    field_simp
    ring
  rw [e1, e2, e3, e4]
  have hNsqrt : Real.sqrt N ≤ N := by
    nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg N, hsqrt1]
  have hNsqrtτ : Real.sqrt N ≤ τ := le_trans hNsqrt hτN
  have hb1 : 8 * (8100*(1+K) * N * Real.sqrt N / τ^2) ≤ 64800 * (1+K) * N / τ := by
    rw [show 8 * (8100*(1+K) * N * Real.sqrt N / τ^2)
        = 64800 * (1+K) * N / τ * (Real.sqrt N/τ) by ring]
    have h1 : Real.sqrt N/τ ≤ 1 := by rw [div_le_one hτpos]; exact hNsqrtτ
    calc 64800 * (1+K) * N / τ * (Real.sqrt N/τ) ≤ 64800 * (1+K) * N / τ * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 64800 * (1+K) * N / τ := by ring
  have hb2 : 8 * (233280*(1+K)/τ^2 * N) ≤ 1866240 * (1+K) * N / τ := by
    rw [show 8 * (233280*(1+K)/τ^2 * N) = 1866240*(1+K)*N/τ * (1/τ) by ring]
    have h : (1:ℝ)/τ ≤ 1 := by rw [div_le_one hτpos]; linarith
    calc 1866240*(1+K)*N/τ * (1/τ) ≤ 1866240*(1+K)*N/τ * 1 :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 1866240*(1+K)*N/τ := by ring
  have hb3 : 8 * (559872*Real.sqrt N/τ^2) ≤ 4478976 * (1+K) * N / τ := by
    have hkey : Real.sqrt N/τ^2 ≤ (1+K)*N/τ := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < τ^2) hτpos]
      have h1 : Real.sqrt N ≤ (1+K)*N := by
        calc Real.sqrt N ≤ N := hNsqrt
          _ ≤ (1+K)*N := by
              rw [show (1+K)*N = N + K*N by ring]
              linarith [mul_nonneg hK hNpos.le]
      have hτ2 : (1:ℝ) ≤ τ := hτ1
      have h3 : τ ≤ τ^2 := by nlinarith [hτpos, hτ2]
      have h4 : Real.sqrt N * τ ≤ (1+K)*N * τ := mul_le_mul_of_nonneg_right h1 hτpos.le
      have h5 : (1+K)*N * τ ≤ (1+K)*N * τ^2 := by
        apply mul_le_mul_of_nonneg_left h3 (mul_nonneg (by linarith) hNpos.le)
      linarith [h4, h5]
    have hfin : 4478976 * (Real.sqrt N/τ^2) ≤ 4478976 * ((1+K)*N/τ) :=
      mul_le_mul_of_nonneg_left hkey (by norm_num : (0:ℝ) ≤ 4478976)
    calc 8 * (559872*Real.sqrt N/τ^2) = 4478976 * (Real.sqrt N/τ^2) := by ring
      _ ≤ 4478976 * ((1+K)*N/τ) := hfin
      _ = 4478976 * (1+K) * N / τ := by ring
  have hb4 : 8 * (10077696*Real.sqrt N/τ^2) ≤ 80621568 * (1+K) * N / τ := by
    have hkey : Real.sqrt N/τ^2 ≤ (1+K)*N/τ := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < τ^2) hτpos]
      have h1 : Real.sqrt N ≤ (1+K)*N := by
        calc Real.sqrt N ≤ N := hNsqrt
          _ ≤ (1+K)*N := by
              rw [show (1+K)*N = N + K*N by ring]
              linarith [mul_nonneg hK hNpos.le]
      have hτ2 : (1:ℝ) ≤ τ := hτ1
      have h3 : τ ≤ τ^2 := by nlinarith [hτpos, hτ2]
      have h4 : Real.sqrt N * τ ≤ (1+K)*N * τ := mul_le_mul_of_nonneg_right h1 hτpos.le
      have h5 : (1+K)*N * τ ≤ (1+K)*N * τ^2 := by
        apply mul_le_mul_of_nonneg_left h3 (mul_nonneg (by linarith) hNpos.le)
      linarith [h4, h5]
    have hfin : 80621568 * (Real.sqrt N/τ^2) ≤ 80621568 * ((1+K)*N/τ) :=
      mul_le_mul_of_nonneg_left hkey (by norm_num : (0:ℝ) ≤ 80621568)
    calc 8 * (10077696*Real.sqrt N/τ^2) = 80621568 * (Real.sqrt N/τ^2) := by ring
      _ ≤ 80621568 * ((1+K)*N/τ) := hfin
      _ = 80621568 * (1+K) * N / τ := by ring
  rw [show 8 * (8100*(1+K) * N * Real.sqrt N / τ^2 + 233280*(1+K)/τ^2 * N
      + 559872*Real.sqrt N/τ^2 + 10077696*Real.sqrt N/τ^2)
      = 8*(8100*(1+K) * N * Real.sqrt N / τ^2) + 8*(233280*(1+K)/τ^2 * N)
        + 8*(559872*Real.sqrt N/τ^2) + 8*(10077696*Real.sqrt N/τ^2) by ring]
  have hsum4 := add_le_add (add_le_add (add_le_add hb1 hb2) hb3) hb4
  have htot : 64800*(1+K)*N/τ + 1866240*(1+K)*N/τ + 4478976*(1+K)*N/τ + 80621568*(1+K)*N/τ
      ≤ 1000000000*(1+K)*N/τ := by
    have h : (0:ℝ) ≤ (1+K)*N/τ := by positivity
    have he : 64800*(1+K)*N/τ + 1866240*(1+K)*N/τ + 4478976*(1+K)*N/τ + 80621568*(1+K)*N/τ
        = (64800 + 1866240 + 4478976 + 80621568) * ((1+K)*N/τ) := by ring
    rw [he]
    have h2 : (64800 + 1866240 + 4478976 + 80621568 : ℝ) ≤ 1000000000 := by norm_num
    have h3 := mul_le_mul_of_nonneg_right h2 h
    rwa [show (1000000000:ℝ) * ((1+K)*N/τ) = 1000000000 * (1+K) * N / τ by ring] at h3
  linarith [hsum4, htot]

end TailArith


open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 800000


section Mid

lemma WwI_left_mid_pt {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hNτ : (N:ℝ) ≤ τ)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N)
    {m : ℕ} (hm : m ≤ WwLo N τ - 1) :
    ‖WwI χ τ (m:ℤ)‖ ≤ 1000000000 * (1+K) * N / τ := by
  have hmZ : (m:ℤ) ≤ (WwLo N τ : ℤ) - 1 := by
    have h1 : 1 ≤ WwLo N τ := Nat.ceil_pos.mpr (by positivity : (0:ℝ) < τ/(6*Real.pi*(N:ℝ)))
    have h2 : (m:ℤ) ≤ ((WwLo N τ - 1 : ℕ) : ℤ) := by exact_mod_cast hm
    have h3 : ((WwLo N τ - 1 : ℕ) : ℤ) = (WwLo N τ : ℤ) - 1 := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    linarith [h2, h3]
  have h1 := WwI_pos_left_pt hN hχd hχ0 hχz hK hτ hbdd hdd hm
  have h2 := WwLm_ge_eighteen hN hτ hmZ
  have h3 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  exact le_trans h1 (tail_left_arith h3 hNτ hK (WwLm_pos hN hτ hm) h2)

lemma WwLo_le (N : ℕ) (τ : ℝ) (hτ : 0 < τ) (hN : 0 < N) (hNτ : (N:ℝ) ≤ τ) :
    (WwLo N τ : ℝ) ≤ 2 * τ / N := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have h1 : (WwLo N τ : ℝ) < τ/(6*Real.pi*(N:ℝ)) + 1 := by
    rw [WwLo]; exact Nat.ceil_lt_add_one (by positivity)
  have h2 : τ/(6*Real.pi*(N:ℝ)) ≤ τ/(6*N) := by
    apply div_le_div_of_nonneg_left hτ.le (by positivity)
    nlinarith [Real.pi_gt_three]
  have h5 : τ/(6*N) ≤ τ/N := by
    apply div_le_div_of_nonneg_left hτ.le (by positivity)
    linarith
  have h6 : τ/(6*N) + 1 ≤ τ/(6*N) + τ/N := by
    have h7 : (1:ℝ) ≤ τ/N := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    linarith
  have h8 : τ/(6*N) + τ/N = (7:ℝ)/6 * (τ/N) := by ring
  have h9 : (7:ℝ)/6 * (τ/N) ≤ 2 * (τ/N) := by
    have h10 : (0:ℝ) ≤ τ/N := by positivity
    linarith
  have h11 : 2 * (τ/N) = 2*τ/N := by ring
  linarith [h1, h2, h5, h6, h8, h9, h11]

lemma WwI_left_mid_sum {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hNτ : (N:ℝ) ≤ τ)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N) :
    ∑ m ∈ Finset.Icc 1 (WwLo N τ - 1), ‖WwI χ τ (m:ℤ)‖ ≤ 10000000000 * (1+K) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hbound : ∀ m ∈ Finset.Icc 1 (WwLo N τ - 1),
      ‖WwI χ τ (m:ℤ)‖ ≤ 1000000000 * (1+K) * N / τ := by
    intro m hm
    exact WwI_left_mid_pt hN hχd hχ0 hχz hK hτ hNτ hbdd hdd (Finset.mem_Icc.mp hm).2
  have hcard : ((Finset.Icc 1 (WwLo N τ - 1)).card : ℝ) ≤ 2 * τ / N := by
    have h1 : (Finset.Icc 1 (WwLo N τ - 1)).card ≤ WwLo N τ := by
      rw [Nat.card_Icc]
      omega
    have h2 : ((Finset.Icc 1 (WwLo N τ - 1)).card : ℝ) ≤ (WwLo N τ : ℝ) := by exact_mod_cast h1
    exact le_trans h2 (WwLo_le N τ hτ (by omega) hNτ)
  calc ∑ m ∈ Finset.Icc 1 (WwLo N τ - 1), ‖WwI χ τ (m:ℤ)‖
      ≤ ∑ m ∈ Finset.Icc 1 (WwLo N τ - 1), (1000000000 * (1+K) * N / τ) :=
        Finset.sum_le_sum hbound
    _ = ((Finset.Icc 1 (WwLo N τ - 1)).card : ℝ) * (1000000000 * (1+K) * N / τ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * τ / N) * (1000000000 * (1+K) * N / τ) := by
        apply mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2000000000 * (1+K) := by
        field_simp
        ring
    _ ≤ 10000000000 * (1+K) := by nlinarith [hK]

end Mid


open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 800000

section Maj

/-- Uniform lower bound for the phase derivative outside the band. -/
noncomputable def WwLb {N : ℕ} (τ : ℝ) (m : ℤ) : ℝ :=
  max (τ/(18*(N:ℝ))) (Real.pi*|(m:ℝ)|/200)

lemma WwLb_pos {N : ℕ} (hN : 0 < N) {τ : ℝ} (hτ : 0 < τ) (m : ℤ) :
    0 < WwLb (N := N) τ m := by
  have h1 : (0:ℝ) < τ/(18*(N:ℝ)) := by
    have : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    positivity
  exact lt_of_lt_of_le h1 (le_max_left _ _)

/-- The majorant for the terms outside the band. -/
noncomputable def WwMaj {N : ℕ} (K τ : ℝ) (m : ℤ) : ℝ :=
  8 * (25*(1+K)/Real.sqrt N
      + (10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))/WwLb (N:=N) τ m
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ m)^2) / (WwLb (N:=N) τ m)^2

lemma WwMaj_nonneg {N : ℕ} (hN : 0 < N) {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (m : ℤ) :
    0 ≤ WwMaj (N := N) K τ m := by
  have h1 : 0 < WwLb (N := N) τ m := WwLb_pos hN hτ m
  have h2 : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have h3 : (0:ℝ) ≤ 1 + K := by linarith
  have h4 : (0:ℝ) ≤ τ := le_of_lt hτ
  have h5 : (0:ℝ) ≤ N := by positivity
  unfold WwMaj
  positivity

/-- On the positive side of the band, `WwLb` is a valid lower bound for the phase derivative. -/
lemma WwLb_le_pos {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 < τ) {m : ℕ}
    (hm1 : 1 ≤ m) (hm2 : m ≤ WwLo N τ - 1) :
    WwLb (N := N) τ (m:ℤ) ≤ WwLm N τ (m:ℤ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hW1 : 1 ≤ WwLo N τ :=
    Nat.ceil_pos.mpr (by positivity : (0:ℝ) < τ/(6*Real.pi*(N:ℝ)))
  have hmZ : (m:ℤ) ≤ (WwLo N τ : ℤ) - 1 := by
    have h2 : (m:ℤ) ≤ ((WwLo N τ - 1 : ℕ) : ℤ) := by exact_mod_cast hm2
    have h3 : ((WwLo N τ - 1 : ℕ) : ℤ) = (WwLo N τ : ℤ) - 1 := by
      rw [Nat.cast_sub hW1]; push_cast; ring
    linarith [h2, h3]
  have hceil : (WwLo N τ : ℝ) < τ/(6*Real.pi*(N:ℝ)) + 1 := by
    rw [WwLo]; exact Nat.ceil_lt_add_one (by positivity)
  have hmlt : (m:ℝ) ≤ τ/(6*Real.pi*(N:ℝ)) := by
    have h1 : (m:ℝ) ≤ ((WwLo N τ - 1 : ℕ) : ℝ) := by exact_mod_cast hm2
    rw [Nat.cast_sub hW1] at h1
    push_cast at h1
    linarith
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hL := WwLm_ge_eighteen hN hτ hmZ
  have hm0 : (0:ℝ) ≤ ((m:ℤ):ℝ) := by exact_mod_cast (Int.natCast_nonneg m)
  have habs : |((m:ℤ):ℝ)| = (m:ℝ) := by
    rw [abs_of_nonneg hm0]
    push_cast
    rfl
  have harith : Real.pi*(m:ℝ)/200 ≤ τ/(18*N) := by
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 200) (by positivity : (0:ℝ) < 18*N)]
    have h1 : Real.pi*(m:ℝ) ≤ Real.pi*(τ/(6*Real.pi*(N:ℝ))) :=
      mul_le_mul_of_nonneg_left hmlt hpi.le
    have h2 : Real.pi*(τ/(6*Real.pi*(N:ℝ))) = τ/(6*N) := by
      field_simp
      try ring
    have h3 : Real.pi*(m:ℝ) ≤ τ/(6*N) := by rw [← h2]; exact h1
    have h5 : Real.pi*(m:ℝ) * (18*N) ≤ 3*τ := by
      have h6 := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ 18*N)
      have h7 : τ/(6*N) * (18*N) = 3*τ := by field_simp; try ring
      linarith [h6, h7]
    have h8 : 3*τ ≤ τ*200 := by nlinarith [hτ]
    linarith [h5, h8]
  have hclaim : Real.pi*|((m:ℤ):ℝ)|/200 ≤ WwLm N τ (m:ℤ) := by
    rw [habs]
    exact le_trans harith hL
  unfold WwLb
  exact max_le hL hclaim

end Maj


open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 800000

/-- `WwLb` is dominated by `WwLm` on the non-positive left tail. -/
lemma WwLb_le_neg {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 < τ) {m : ℤ} (hm : m ≤ 0) :
    WwLb (N := N) τ m ≤ WwLm N τ m := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = (N:ℝ) := Real.sq_sqrt (le_of_lt hNpos)
  have hsqn : (0:ℝ) ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hmR : (m:ℝ) ≤ 0 := by exact_mod_cast hm
  have hnonneg : (0:ℝ) ≤ -(m:ℝ) := by linarith
  have hA0pos : (0:ℝ) < WwA0 N τ := by unfold WwA0; positivity
  have h1a : τ/(18*N) ≤ WwA0 N τ := by
    unfold WwA0
    apply div_le_div_of_nonneg_left hτ.le (by positivity)
    nlinarith [hsq, hsqn, hN4R]
  have h1 : τ/(18*N) ≤ WwLm N τ m := by
    unfold WwLm
    have h1b : WwA0 N τ ≤ WwA0 N τ - 2*Real.pi*(m:ℝ) := by
      nlinarith [mul_nonneg (le_of_lt Real.pi_pos) hnonneg]
    linarith [h1a, h1b]
  have h2 : Real.pi*|(m:ℝ)|/200 ≤ WwLm N τ m := by
    have habs : |(m:ℝ)| = -(m:ℝ) := abs_of_nonpos hmR
    rw [habs]
    unfold WwLm
    have h5 : Real.pi*(-(m:ℝ))/200 ≤ Real.pi*(-(m:ℝ)) := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 200)]
      nlinarith [mul_nonneg (le_of_lt Real.pi_pos) hnonneg]
    have h6 : Real.pi*(-(m:ℝ)) ≤ WwA0 N τ - 2*Real.pi*(m:ℝ) := by
      have h7 : Real.pi*(-(m:ℝ)) = -Real.pi*(m:ℝ) := by ring
      rw [h7]
      have h8 : -Real.pi*(m:ℝ) ≤ -2*Real.pi*(m:ℝ) := by
        nlinarith [mul_nonneg (le_of_lt Real.pi_pos) hnonneg]
      linarith [h8, hA0pos]
    linarith [h5, h6]
  unfold WwLb
  exact max_le h1 h2

/-- `WwLb` is dominated by `πm` on the right tail. -/
lemma WwLb_le_right {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 < τ) {m : ℕ}
    (hm : WwHi N τ + 1 ≤ m) :
    WwLb (N := N) τ (m:ℤ) ≤ Real.pi * (m:ℝ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hmR : 2*τ/(Real.pi*(N:ℝ)) < (m:ℝ) := by
    have h1 : 2*τ/(Real.pi*(N:ℝ)) < ((WwHi N τ : ℕ) : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (2*τ/(Real.pi*(N:ℝ)))
      rw [WwHi]
      push_cast
      linarith
    have h2 : ((WwHi N τ : ℕ) : ℝ) + 1 ≤ (m:ℝ) := by
      have := hm
      push_cast
      exact_mod_cast this
    linarith
  have h3 : 2*τ/N < Real.pi*(m:ℝ) := by
    have h4 : Real.pi * (2*τ/(Real.pi*(N:ℝ))) < Real.pi * (m:ℝ) :=
      mul_lt_mul_of_pos_left hmR hπ
    have h5 : Real.pi * (2*τ/(Real.pi*(N:ℝ))) = 2*τ/N := by
      field_simp
      try ring
    linarith [h4, h5]
  have h6 : τ/(18*N) ≤ Real.pi*(m:ℝ) := by
    have h7 : τ/(18*N) ≤ 2*τ/N := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hτ]
    linarith [h7, h3]
  have h8 : Real.pi*|((m:ℤ):ℝ)|/200 ≤ Real.pi*(m:ℝ) := by
    have hm0 : (0:ℝ) ≤ ((m:ℤ):ℝ) := by exact_mod_cast (Int.natCast_nonneg m)
    have habs : |((m:ℤ):ℝ)| = (m:ℝ) := by simp [abs_of_nonneg hm0]
    have hmn : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    rw [habs]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 200)]
    nlinarith [hπ, hmn]
  unfold WwLb
  exact max_le h6 h8


section Mono

/-- Monotonicity of the per-term majorant expression in `L ≥ Lb > 0`. -/
lemma WwMaj_anti {A B C D L Lb : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hLb : 0 < Lb) (hLL : Lb ≤ L) :
    8 * (A + B/L + C/L + D/L^2)/L^2 ≤ 8 * (A + B/Lb + C/Lb + D/Lb^2)/Lb^2 := by
  have hLpos : 0 < L := lt_of_lt_of_le hLb hLL
  have h1 : 1/L ≤ 1/Lb := by
    rw [div_le_div_iff₀ hLpos hLb]
    linarith
  have h2 : 1/L^2 ≤ 1/Lb^2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simpa using pow_le_pow_left₀ hLb.le hLL 2
  have h3 : 1/L^3 ≤ 1/Lb^3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simpa using pow_le_pow_left₀ hLb.le hLL 3
  have h4 : 1/L^4 ≤ 1/Lb^4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    simpa using pow_le_pow_left₀ hLb.le hLL 4
  have e1 : 8 * (A + B/L + C/L + D/L^2)/L^2
      = 8 * (A * (1/L^2) + B * (1/L^3) + C * (1/L^3) + D * (1/L^4)) := by
    field_simp
    try ring
  have e2 : 8 * (A + B/Lb + C/Lb + D/Lb^2)/Lb^2
      = 8 * (A * (1/Lb^2) + B * (1/Lb^3) + C * (1/Lb^3) + D * (1/Lb^4)) := by
    field_simp
    try ring
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have g1 : A * (1/L^2) ≤ A * (1/Lb^2) := mul_le_mul_of_nonneg_left h2 hA
  have g2 : B * (1/L^3) ≤ B * (1/Lb^3) := mul_le_mul_of_nonneg_left h3 hB
  have g3 : C * (1/L^3) ≤ C * (1/Lb^3) := mul_le_mul_of_nonneg_left h3 hC
  have g4 : D * (1/L^4) ≤ D * (1/Lb^4) := mul_le_mul_of_nonneg_left h4 hD
  linarith [g1, g2, g3, g4]

end Mono


open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 800000

section MajApp

lemma WwMaj_four_nonneg {N : ℕ} {K τ : ℝ} (hN : (0:ℝ) < N) (hK : 0 ≤ K) (hτ : 0 < τ) :
    (0:ℝ) ≤ 25*(1+K)/Real.sqrt N ∧ (0:ℝ) ≤ 10*(1+K)*(4*τ/(N:ℝ)^2)
    ∧ (0:ℝ) ≤ 6*Real.sqrt N*(16*τ/(N:ℝ)^3) ∧ (0:ℝ) ≤ 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> positivity

/-- `WwI ≤ WwMaj` on the right tail. -/
lemma WwI_le_WwMaj_right {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hNτ : (N:ℝ) ≤ τ)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N)
    {m : ℕ} (hm : WwHi N τ + 1 ≤ m) :
    ‖WwI χ τ (m:ℤ)‖ ≤ WwMaj (N := N) K τ (m:ℤ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hA, hB, hC, hD⟩ := WwMaj_four_nonneg (N := N) (K := K) (τ := τ) hNpos hK hτ
  have hper := WwI_right_pt hN hχd hχ0 hχz hK hτ hNτ hbdd hdd hm
  have hll := WwLb_le_right hN hτ hm
  have hLb := WwLb_pos (N := N) (by omega : 0 < N) hτ (m:ℤ)
  unfold WwMaj
  rw [show (25*(1+K)/Real.sqrt N
      + (10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))/WwLb (N:=N) τ (m:ℤ)
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ (m:ℤ))^2)
    = (25*(1+K)/Real.sqrt N + 10*(1+K)*(4*τ/(N:ℝ)^2)/WwLb (N:=N) τ (m:ℤ)
      + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)/WwLb (N:=N) τ (m:ℤ)
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ (m:ℤ))^2) by ring]
  exact le_trans hper (WwMaj_anti hA hB hC hD hLb hll)

/-- `WwI ≤ WwMaj` in the positive part of the left tail. -/
lemma WwI_le_WwMaj_mid {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hNτ : (N:ℝ) ≤ τ)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ WwLo N τ - 1) :
    ‖WwI χ τ (m:ℤ)‖ ≤ WwMaj (N := N) K τ (m:ℤ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hA, hB, hC, hD⟩ := WwMaj_four_nonneg (N := N) (K := K) (τ := τ) hNpos hK hτ
  have hper := WwI_pos_left_pt hN hχd hχ0 hχz hK hτ hbdd hdd hm2
  have hll := WwLb_le_pos hN hτ hm1 hm2
  have hLb := WwLb_pos (N := N) (by omega : 0 < N) hτ (m:ℤ)
  unfold WwMaj
  rw [show (25*(1+K)/Real.sqrt N
      + (10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))/WwLb (N:=N) τ (m:ℤ)
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ (m:ℤ))^2)
    = (25*(1+K)/Real.sqrt N + 10*(1+K)*(4*τ/(N:ℝ)^2)/WwLb (N:=N) τ (m:ℤ)
      + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)/WwLb (N:=N) τ (m:ℤ)
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ (m:ℤ))^2) by ring]
  exact le_trans hper (WwMaj_anti hA hB hC hD hLb hll)

/-- `WwI ≤ WwMaj` on the non-positive left tail. -/
lemma WwI_le_WwMaj_neg {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / N)
    {m : ℤ} (hm : m ≤ 0) :
    ‖WwI χ τ m‖ ≤ WwMaj (N := N) K τ m := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hA, hB, hC, hD⟩ := WwMaj_four_nonneg (N := N) (K := K) (τ := τ) hNpos hK hτ
  have hper := WwI_nonpos_bound hN hχd hχ0 hχz hK hτ hbdd hdd hm
  have hll := WwLb_le_neg hN hτ hm
  have hLb := WwLb_pos (N := N) (by omega : 0 < N) hτ m
  have hLm : WwLm N τ m = τ/((2*N:ℝ) + Real.sqrt N) + 2*Real.pi*|(m:ℝ)| := by
    have hmR : (m:ℝ) ≤ 0 := by exact_mod_cast hm
    unfold WwLm WwA0
    rw [abs_of_nonpos hmR]
    ring
  unfold WwMaj
  rw [show (25*(1+K)/Real.sqrt N
      + (10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))/WwLb (N:=N) τ (m:ℤ)
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ (m:ℤ))^2)
    = (25*(1+K)/Real.sqrt N + 10*(1+K)*(4*τ/(N:ℝ)^2)/WwLb (N:=N) τ (m:ℤ)
      + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)/WwLb (N:=N) τ (m:ℤ)
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ (m:ℤ))^2) by ring]
  refine le_trans hper (WwMaj_anti hA hB hC hD hLb ?_)
  rw [← hLm]
  exact hll

end MajApp


open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 800000

section Summ

lemma summable_int_inv_sq : Summable (fun m : ℤ => ((|(m:ℝ)|)^2)⁻¹) := by
  have h := Real.summable_abs_int_rpow (b := (2:ℝ)) (by norm_num)
  refine h.congr (fun m => ?_)
  rw [Real.rpow_neg (abs_nonneg _)]
  congr 1
  exact Real.rpow_natCast _ 2

lemma summable_max_one_inv_sq : Summable (fun m : ℤ => ((max 1 |(m:ℝ)|)^2)⁻¹) := by
  have h1 := summable_int_inv_sq
  have h2 : Summable (fun m : ℤ => if (m:ℤ) = 0 then (1:ℝ) else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by intro m hm; simp at hm; simp [hm])
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (h1.add h2)
  by_cases hm : (m:ℤ) = 0
  · subst hm
    simp
  · have hpos : (0:ℝ) < |((m:ℤ):ℝ)| := by
      rw [abs_pos]
      exact_mod_cast hm
    have h1' : (1:ℝ) ≤ |((m:ℤ):ℝ)| := by
      have h1z : (1:ℤ) ≤ |(m:ℤ)| := Int.one_le_abs hm
      rw [← Int.cast_abs]
      exact_mod_cast h1z
    have hmax : max 1 |((m:ℤ):ℝ)| = |((m:ℤ):ℝ)| := max_eq_right h1'
    rw [hmax]
    simp only [hm, if_false, add_zero]
    linarith [show (0:ℝ) ≤ ((|((m:ℤ):ℝ)|)^2)⁻¹ by positivity]

end Summ


open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 800000

section Summ2

lemma summable_WwMaj {N : ℕ} (hN : 1 ≤ N) {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ)
    (hNτ : (N:ℝ) ≤ τ) :
    Summable (fun m : ℤ => WwMaj (N := N) K τ m) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ18 : (18:ℝ) ≤ 200/Real.pi := by
    rw [le_div_iff₀ hπ]
    nlinarith [Real.pi_lt_four]
  -- the uniform reciprocal bound `1/WwLb m ≤ (200/π)·(max 1 |m|)⁻¹`
  have hr : ∀ m : ℤ, 1 / WwLb (N := N) τ m ≤ (200/Real.pi) * ((max 1 |(m:ℝ)|))⁻¹ := by
    intro m
    have hLpos : 0 < WwLb (N := N) τ m := WwLb_pos (N := N) (by omega : 0 < N) hτ m
    by_cases hm : (m:ℤ) = 0
    · subst hm
      have hL0 : WwLb (N := N) τ (0:ℤ) = τ/(18*N) := by
        unfold WwLb
        rw [show |(((0:ℤ):ℝ))| = 0 by norm_num, mul_zero, zero_div,
          show max (τ/(18*(N:ℝ))) 0 = τ/(18*(N:ℝ)) from max_eq_left (by positivity)]
      rw [hL0]
      have h1 : (1:ℝ) / (τ/(18*N)) = 18*N/τ := by field_simp
      rw [h1]
      have h2 : (18:ℝ)*N/τ ≤ 18 := by
        rw [div_le_iff₀ hτ]
        nlinarith [hNτ]
      have h3 : ((max 1 |(((0:ℤ):ℝ))|))⁻¹ = 1 := by
        rw [show |(((0:ℤ):ℝ))| = 0 by norm_num,
          show max (1:ℝ) 0 = 1 from max_eq_left (by norm_num), inv_one]
      rw [h3, mul_one]
      linarith [h2, hπ18]
    · have hpos : (0:ℝ) < |((m:ℤ):ℝ)| := by rw [abs_pos]; exact_mod_cast hm
      have h1 : (1:ℝ) ≤ |((m:ℤ):ℝ)| := by
        have h1z : (1:ℤ) ≤ |(m:ℤ)| := Int.one_le_abs hm
        rw [← Int.cast_abs]; exact_mod_cast h1z
      have hmax : max 1 |((m:ℤ):ℝ)| = |((m:ℤ):ℝ)| := max_eq_right h1
      rw [hmax]
      have hLb : Real.pi*|((m:ℤ):ℝ)|/200 ≤ WwLb (N := N) τ m := le_max_right _ _
      have h1' : 1 / WwLb (N := N) τ m ≤ 200/(Real.pi*|((m:ℤ):ℝ)|) := by
        rw [div_le_div_iff₀ hLpos (by positivity)]
        nlinarith [hLb]
      rw [show (200/Real.pi) * (|((m:ℤ):ℝ)|)⁻¹ = 200/(Real.pi*|((m:ℤ):ℝ)|) by
        rw [div_mul_eq_div_mul_one_div]; ring]
      exact h1'
  -- the coefficient bound
  have hPpos : (0:ℝ) < 200/Real.pi := by positivity
  set A : ℝ := 25*(1+K)/Real.sqrt N with hA
  set B : ℝ := 10*(1+K)*(4*τ/(N:ℝ)^2) with hB
  set Cc : ℝ := 6*Real.sqrt N*(16*τ/(N:ℝ)^3) with hC
  set D : ℝ := 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2) with hD
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hCnn : 0 ≤ Cc := by rw [hC]; positivity
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  set K' : ℝ := 8 * (200/Real.pi)^2 * (A + (B+Cc)*(200/Real.pi) + D*(200/Real.pi)^2) with hK'
  have hK'nn : 0 ≤ K' := by rw [hK']; positivity
  -- pointwise majorant
  have hmaj : ∀ m : ℤ, WwMaj (N := N) K τ m ≤ K' * ((max 1 |(m:ℝ)|)^2)⁻¹ := by
    intro m
    have hLpos : 0 < WwLb (N := N) τ m := WwLb_pos (N := N) (by omega : 0 < N) hτ m
    have h1 := hr m
    have hmax1 : (1:ℝ) ≤ max 1 |(m:ℝ)| := le_max_left _ _
    have hmaxpos : (0:ℝ) < max 1 |(m:ℝ)| := lt_of_lt_of_le (by norm_num) hmax1
    have hrle : (200/Real.pi) * ((max 1 |(m:ℝ)|))⁻¹ ≤ 200/Real.pi := by
      have h3 : ((max 1 |(m:ℝ)|))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hmax1
      nlinarith [h3, hPpos]
    have hrnn : 0 ≤ (200/Real.pi) * ((max 1 |(m:ℝ)|))⁻¹ := by positivity
    -- normalize
    rw [show WwMaj (N := N) K τ m
        = 8 * (A * (1/WwLb (N:=N) τ m)^2 + B * (1/WwLb (N:=N) τ m)^3
            + Cc * (1/WwLb (N:=N) τ m)^3 + D * (1/WwLb (N:=N) τ m)^4) by
      unfold WwMaj
      rw [show (25*(1+K)/Real.sqrt N
          + (10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))/WwLb (N:=N) τ m
          + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ m)^2)
        = (A + B/WwLb (N:=N) τ m + Cc/WwLb (N:=N) τ m + D/(WwLb (N:=N) τ m)^2) by
        rw [← hA, ← hB, ← hC, ← hD]; ring]
      field_simp
      try ring]
    -- bound in terms of `r`
    set r : ℝ := (200/Real.pi) * ((max 1 |(m:ℝ)|))⁻¹ with hrdef
    have hLr : 1/WwLb (N:=N) τ m ≤ r := h1
    have hrnn' : 0 ≤ r := hrnn
    have h1L : (0:ℝ) < 1/WwLb (N:=N) τ m := by positivity
    have hA' : A * (1/WwLb (N:=N) τ m)^2 ≤ A * r^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1L.le hLr 2) hAnn
    have hB' : B * (1/WwLb (N:=N) τ m)^3 ≤ B * r^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1L.le hLr 3) hBnn
    have hC' : Cc * (1/WwLb (N:=N) τ m)^3 ≤ Cc * r^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1L.le hLr 3) hCnn
    have hD' : D * (1/WwLb (N:=N) τ m)^4 ≤ D * r^4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1L.le hLr 4) hDnn
    have step1 : A * (1/WwLb (N:=N) τ m)^2 + B * (1/WwLb (N:=N) τ m)^3
        + Cc * (1/WwLb (N:=N) τ m)^3 + D * (1/WwLb (N:=N) τ m)^4
        ≤ A * r^2 + (B+Cc) * r^3 + D * r^4 := by linarith [hA', hB', hC', hD']
    have step2 : A * r^2 + (B+Cc) * r^3 + D * r^4 = r^2 * (A + (B+Cc)*r + D*r^2) := by ring
    have step3 : r ≤ 200/Real.pi := hrle
    have hfac : A + (B+Cc)*r + D*r^2 ≤ A + (B+Cc)*(200/Real.pi) + D*(200/Real.pi)^2 := by
      have h2 : (B+Cc)*r ≤ (B+Cc)*(200/Real.pi) :=
        mul_le_mul_of_nonneg_left step3 (by linarith)
      have h3 : D*r^2 ≤ D*(200/Real.pi)^2 := by
        apply mul_le_mul_of_nonneg_left _ hDnn
        exact pow_le_pow_left₀ hrnn' step3 2
      linarith
    have hr2 : r^2 = (200/Real.pi)^2 * ((max 1 |(m:ℝ)|)^2)⁻¹ := by
      rw [hrdef]
      rw [mul_pow, inv_pow]
    calc 8 * (A * (1/WwLb (N:=N) τ m)^2 + B * (1/WwLb (N:=N) τ m)^3
          + Cc * (1/WwLb (N:=N) τ m)^3 + D * (1/WwLb (N:=N) τ m)^4)
        ≤ 8 * (A * r^2 + (B+Cc) * r^3 + D * r^4) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith [step1]
      _ = 8 * (r^2 * (A + (B+Cc)*r + D*r^2)) := by rw [step2]
      _ ≤ 8 * (r^2 * (A + (B+Cc)*(200/Real.pi) + D*(200/Real.pi)^2)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hfac (by positivity)
      _ = K' * ((max 1 |(m:ℝ)|)^2)⁻¹ := by
          rw [hr2, hK']
          ring
  exact Summable.of_nonneg_of_le (fun m => WwMaj_nonneg (N := N) (by omega : 0 < N) hK hτ m) hmaj
    (summable_max_one_inv_sq.mul_left K')

end Summ2


open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 800000

section Far

/-- Uniform bound for a single majorant term. -/
lemma WwMaj_le_const {N : ℕ} (hN : 1 ≤ N) {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ)
    (hNτ : (N:ℝ) ≤ τ) (m : ℤ) :
    WwMaj (N:=N) K τ m ≤ 1000000000 * (1+K) * N / τ := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hLb : (0:ℝ) < τ/(18*N) := by positivity
  have hW : τ/(18*N) ≤ WwLb (N:=N) τ m := le_max_left _ _
  have hmono := WwMaj_anti
    (A := 25*(1+K)/Real.sqrt N) (B := 10*(1+K)*(4*τ/(N:ℝ)^2))
    (C := 6*Real.sqrt N*(16*τ/(N:ℝ)^3)) (D := 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2))
    (L := WwLb (N:=N) τ m) (Lb := τ/(18*N))
    (by positivity) (by positivity) (by positivity) (by positivity) hLb hW
  unfold WwMaj
  rw [show (25*(1+K)/Real.sqrt N
      + (10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))/WwLb (N:=N) τ m
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ m)^2)
    = (25*(1+K)/Real.sqrt N + 10*(1+K)*(4*τ/(N:ℝ)^2)/WwLb (N:=N) τ m
      + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)/WwLb (N:=N) τ m
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ m)^2) by ring]
  exact le_trans hmono (tail_left_arith (by exact_mod_cast hN) hNτ hK hLb le_rfl)

/-- The far-field majorant: for `K ≤ |m|` the term is bounded by
`C₂|m|⁻² + C₃|m|⁻³ + C₄|m|⁻⁴`. -/
lemma WwMaj_far_pt {N : ℕ} (hN : 1 ≤ N) {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ)
    (hNτ : (N:ℝ) ≤ τ) {Kf : ℝ} (hKf : 1 ≤ Kf)
    (hdom : τ/(18*(N:ℝ)) ≤ Real.pi*Kf/200) {m : ℤ} (hm : Kf ≤ |(m:ℝ)|) :
    WwMaj (N:=N) K τ m ≤
      8 * ((25*(1+K)/Real.sqrt N) * (200/Real.pi)^2 * (((|(m:ℝ)|)^2)⁻¹)
        + ((10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)) * (200/Real.pi)^3
            * (((|(m:ℝ)|)^3)⁻¹))
        + (6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2) * (200/Real.pi)^4 * (((|(m:ℝ)|)^4)⁻¹))) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hmpos : (0:ℝ) < |(m:ℝ)| := lt_of_lt_of_le (by linarith : (0:ℝ) < Kf) hm
  have hLb : WwLb (N:=N) τ m = Real.pi*|(m:ℝ)|/200 := by
    unfold WwLb
    rw [max_eq_right]
    have h1 : Real.pi*Kf/200 ≤ Real.pi*|(m:ℝ)|/200 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left hm hπ.le
    linarith [hdom, h1]
  have hLpos : 0 < WwLb (N:=N) τ m := WwLb_pos (N := N) (by omega : 0 < N) hτ m
  unfold WwMaj
  rw [show (25*(1+K)/Real.sqrt N
      + (10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))/WwLb (N:=N) τ m
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ m)^2)
    = (25*(1+K)/Real.sqrt N + 10*(1+K)*(4*τ/(N:ℝ)^2)/WwLb (N:=N) τ m
      + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)/WwLb (N:=N) τ m
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(WwLb (N:=N) τ m)^2) by ring]
  rw [hLb]
  rw [show 8 * (25*(1+K)/Real.sqrt N + 10*(1+K)*(4*τ/(N:ℝ)^2)/(Real.pi*|(m:ℝ)|/200)
      + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)/(Real.pi*|(m:ℝ)|/200)
      + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)/(Real.pi*|(m:ℝ)|/200)^2)/(Real.pi*|(m:ℝ)|/200)^2
    = 8 * ((25*(1+K)/Real.sqrt N) * (200/Real.pi)^2 * (((|(m:ℝ)|)^2)⁻¹)
      + ((10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)) * (200/Real.pi)^3 * (((|(m:ℝ)|)^3)⁻¹))
      + (6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2) * (200/Real.pi)^4 * (((|(m:ℝ)|)^4)⁻¹))) by
    field_simp
    try ring]

end Far


open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 400000

/-- Far-term one: `8·25·(1+K)/√N·(200/π)²·(CT/Kf) ≤ 10⁶·CT·(1+K)`. -/
lemma far_term1 {N τ Kf K CT : ℝ} (hN : 1 ≤ N) (hNτ : (N:ℝ) ≤ τ) (hKf : 1 ≤ Kf)
    (hK : 0 ≤ K) (hCT : 0 < CT) (hinv : 1/Kf ≤ 9*Real.pi*(N:ℝ)/(100*τ)) :
    8*((25*(1+K)/Real.sqrt N)*(200/Real.pi)^2) * (CT * (1/Kf)) ≤ 1000000 * CT * (1+K) := by
  have hNpos : (0:ℝ) < N := by linarith
  have hτpos : (0:ℝ) < τ := lt_of_lt_of_le hNpos hNτ
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  have hsqrt1 : (1:ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  have hK1 : (0:ℝ) < 1 + K := by linarith
  have h1 : (1:ℝ)/Real.sqrt N ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hsqrt1
  have h2 : (200/Real.pi)^2 ≤ 4445 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith [hπ3]
  have h3 : Real.pi*(N:ℝ)/(100*τ) ≤ 1/25 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hπ4, hNτ, hNpos, hτpos]
  calc 8*((25*(1+K)/Real.sqrt N)*(200/Real.pi)^2) * (CT * (1/Kf))
      = 200*CT*(1+K) * (((1/Real.sqrt N) * ((200/Real.pi)^2)) * (1/Kf)) := by ring
    _ ≤ 200*CT*(1+K) * (1 * 4445 * (9*Real.pi*(N:ℝ)/(100*τ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) hinv
          (by positivity) (by positivity)
    _ = 200*4445*9*CT*(1+K) * (Real.pi*(N:ℝ)/(100*τ)) := by ring
    _ ≤ 200*4445*9*CT*(1+K) * (1/25) := by
        apply mul_le_mul_of_nonneg_left h3 (by positivity)
    _ ≤ 1000000 * CT * (1+K) := by nlinarith [hCT, hK1]



section Terms23

/-- Far-term two. -/
lemma far_term2 {N τ Kf K CT : ℝ} (hN : 1 ≤ N) (hNτ : (N:ℝ) ≤ τ) (hKf : 1 ≤ Kf)
    (hK : 0 ≤ K) (hCT : 0 < CT)
    (hinv : 1/Kf^2 ≤ (9*Real.pi*(N:ℝ)/(100*τ))^2) :
    8*((10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)))*(200/Real.pi)^3
        * (CT * (1/Kf^2)) ≤ 1000000000 * CT * (1+K) := by
  have hNpos : (0:ℝ) < N := by linarith
  have hτpos : (0:ℝ) < τ := lt_of_lt_of_le hNpos hNτ
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hsqrt : Real.sqrt N ≤ N := by
    nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg N,
      (by exact_mod_cast hN : (1:ℝ) ≤ N)]
  have hK1 : (0:ℝ) < 1 + K := by linarith
  have hτ1 : (1:ℝ) ≤ τ := le_trans (by exact_mod_cast hN) hNτ
  have hsqrtdiv : Real.sqrt N/N ≤ 1 := by
    rw [div_le_one hNpos]; exact hsqrt
  have hA : 10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)
      ≤ 40*(1+K)*(τ/(N:ℝ)^2) + 96*(τ/(N:ℝ)^2) := by
    have h1 : Real.sqrt N*(16*τ/(N:ℝ)^3) ≤ 16*τ/(N:ℝ)^2 := by
      have h2 : (0:ℝ) ≤ 16*τ/(N:ℝ)^2 := by positivity
      calc Real.sqrt N*(16*τ/(N:ℝ)^3) = (16*τ/(N:ℝ)^2) * (Real.sqrt N/N) := by
            field_simp
            try ring
        _ ≤ (16*τ/(N:ℝ)^2) * 1 := mul_le_mul_of_nonneg_left hsqrtdiv h2
        _ = 16*τ/(N:ℝ)^2 := by ring
    have h5 : 6*Real.sqrt N*(16*τ/(N:ℝ)^3) ≤ 96*(τ/(N:ℝ)^2) := by
      calc 6*Real.sqrt N*(16*τ/(N:ℝ)^3) = 6*(Real.sqrt N*(16*τ/(N:ℝ)^3)) := by ring
        _ ≤ 6*(16*τ/(N:ℝ)^2) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 96*(τ/(N:ℝ)^2) := by ring
    have h6 : 10*(1+K)*(4*τ/(N:ℝ)^2) = 40*(1+K)*(τ/(N:ℝ)^2) := by ring
    linarith [h5, h6]
  have hA' : 40*(1+K)*(τ/(N:ℝ)^2) + 96*(τ/(N:ℝ)^2) ≤ 136*(1+K)*(τ/(N:ℝ)^2) := by
    have h4 : (0:ℝ) < τ/(N:ℝ)^2 := by positivity
    have h6 : (1:ℝ) ≤ 1+K := by linarith
    have h7 : 96*(τ/(N:ℝ)^2) ≤ 96*(1+K)*(τ/(N:ℝ)^2) := by
      apply mul_le_mul_of_nonneg_right _ h4.le
      linarith
    have h8 : 40*(1+K)*(τ/(N:ℝ)^2) + 96*(1+K)*(τ/(N:ℝ)^2) = 136*(1+K)*(τ/(N:ℝ)^2) := by ring
    linarith [h7, h8]
  have hA2 := le_trans hA hA'
  have h2 : (200/Real.pi)^3 ≤ 300000 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have hp3 : (27:ℝ) ≤ Real.pi^3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) hπ3.le 3
      norm_num at h
      linarith [h]
    nlinarith [hp3]
  have hX : 8*(10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))*(200/Real.pi)^3*CT
      ≤ 8*(136*(1+K)*(τ/(N:ℝ)^2))*300000*CT := by
    have h9 : 8*(10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))
        ≤ 8*(136*(1+K)*(τ/(N:ℝ)^2)) := mul_le_mul_of_nonneg_left hA2 (by norm_num)
    have h10 : (0:ℝ) ≤ 8*(136*(1+K)*(τ/(N:ℝ)^2)) := by positivity
    have h11 : 8*(10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))*(200/Real.pi)^3
        ≤ 8*(136*(1+K)*(τ/(N:ℝ)^2))*300000 := by
      calc 8*(10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))*(200/Real.pi)^3
          = (8*(10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))) * ((200/Real.pi)^3) := by
            ring
        _ ≤ (8*(136*(1+K)*(τ/(N:ℝ)^2))) * 300000 := mul_le_mul h9 h2 (by positivity) h10
    calc 8*(10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))*(200/Real.pi)^3*CT
        = (8*(10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))*(200/Real.pi)^3) * CT := by
          ring
      _ ≤ (8*(136*(1+K)*(τ/(N:ℝ)^2))*300000) * CT :=
          mul_le_mul_of_nonneg_right h11 hCT.le
      _ = 8*(136*(1+K)*(τ/(N:ℝ)^2))*300000*CT := by ring
  have hfin : 8*(136*(1+K)*(τ/(N:ℝ)^2))*300000*CT * (9*Real.pi*(N:ℝ)/(100*τ))^2
      ≤ 1000000000 * CT * (1+K) := by
    have h3 : 8*(136*(1+K)*(τ/(N:ℝ)^2))*300000*CT * (9*Real.pi*(N:ℝ)/(100*τ))^2
        = 8*136*300000*81*Real.pi^2/10^4 * CT*(1+K) * (1/τ) := by
      field_simp
      ring
    rw [h3]
    have h4 : (0:ℝ) ≤ 8*136*300000*81*Real.pi^2/10^4 * CT*(1+K) := by positivity
    have h5 : (1:ℝ)/τ ≤ 1 := by rw [div_le_one hτpos]; exact hτ1
    have h6 : 8*136*300000*81*Real.pi^2/10^4 ≤ 1000000000 := by
      nlinarith [Real.pi_lt_four]
    calc 8*136*300000*81*Real.pi^2/10^4 * CT*(1+K) * (1/τ)
        = 8*136*300000*81*Real.pi^2/10^4 * (CT*(1+K)) * (1/τ) := by ring
      _ ≤ 8*136*300000*81*Real.pi^2/10^4 * (CT*(1+K)) * 1 :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ ≤ 1000000000 * (CT*(1+K)) := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = 1000000000 * CT * (1+K) := by ring
  calc 8*((10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)))*(200/Real.pi)^3
        * (CT * (1/Kf^2))
      = 8*(10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))*(200/Real.pi)^3*CT
          * (1/Kf^2) := by ring
    _ ≤ 8*(10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))*(200/Real.pi)^3*CT
          * (9*Real.pi*(N:ℝ)/(100*τ))^2 := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ 8*(136*(1+K)*(τ/(N:ℝ)^2))*300000*CT * (9*Real.pi*(N:ℝ)/(100*τ))^2 :=
        mul_le_mul_of_nonneg_right hX (by positivity)
    _ ≤ 1000000000 * CT * (1+K) := hfin

end Terms23


open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 400000

/-- Far-term three. -/
lemma far_term3 {N τ Kf K CT : ℝ} (hN : 1 ≤ N) (hNτ : (N:ℝ) ≤ τ) (hKf : 1 ≤ Kf)
    (hK : 0 ≤ K) (hCT : 0 < CT)
    (hinv : 1/Kf^3 ≤ (9*Real.pi*(N:ℝ)/(100*τ))^3) :
    8*(6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2))*(200/Real.pi)^4 * (CT * (1/Kf^3))
      ≤ 1000000000 * CT := by
  have hNpos : (0:ℝ) < N := by linarith
  have hτpos : (0:ℝ) < τ := lt_of_lt_of_le hNpos hNτ
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hτ1 : (1:ℝ) ≤ τ := le_trans (by exact_mod_cast hN) hNτ
  have hsqrt : Real.sqrt N ≤ N := by
    nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg N,
      (by exact_mod_cast hN : (1:ℝ) ≤ N)]
  have hX : (0:ℝ) < 8*(6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2))*(200/Real.pi)^4*CT := by positivity
  rw [show 8*(6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2))*(200/Real.pi)^4 * (CT * (1/Kf^3))
      = (8*(6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2))*(200/Real.pi)^4*CT) * (1/Kf^3) by ring]
  have h2 : (8*(6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2))*(200/Real.pi)^4*CT)
        * ((9*Real.pi*(N:ℝ)/(100*τ))^3)
      = 768*729/10^6 * (200^4/Real.pi) * CT * (Real.sqrt N/((N:ℝ)*τ)) := by
    field_simp
    try ring
  calc (8*(6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2))*(200/Real.pi)^4*CT) * (1/Kf^3)
      ≤ (8*(6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2))*(200/Real.pi)^4*CT)
          * ((9*Real.pi*(N:ℝ)/(100*τ))^3) := mul_le_mul_of_nonneg_left hinv hX.le
    _ = 768*729/10^6 * (200^4/Real.pi) * CT * (Real.sqrt N/((N:ℝ)*τ)) := h2
    _ ≤ 768*729/10^6 * (200^4/3) * CT * 1 := by
        have h3 : (200^4/Real.pi) ≤ 200^4/3 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          exact hπ3.le
        have h4 : Real.sqrt N/((N:ℝ)*τ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith [hsqrt, hNpos, hτ1]
        calc 768*729/10^6 * (200^4/Real.pi) * CT * (Real.sqrt N/((N:ℝ)*τ))
            = (768*729/10^6 * CT) * (200^4/Real.pi) * (Real.sqrt N/((N:ℝ)*τ)) := by ring
          _ ≤ (768*729/10^6 * CT) * (200^4/3) * 1 := by
              apply mul_le_mul (mul_le_mul (le_refl _) h3 (by positivity) (by positivity)) h4
                (by positivity) (by positivity)
              all_goals positivity
          _ = 768*729/10^6 * (200^4/3) * CT * 1 := by ring
    _ ≤ 1000000000 * CT := by
        rw [mul_one]
        have h8 : (768*729/10^6 * (200^4/3) : ℝ) ≤ 1000000000 := by norm_num
        exact mul_le_mul_of_nonneg_right h8 hCT.le


/-! ## Assembly: the far-field tail, the residual, the band error and the sharp constants -/

open Finset Complex MeasureTheory

open scoped Real BigOperators Topology

set_option maxHeartbeats 800000

/-- The far-field majorant. -/
noncomputable def WwFar {N : ℕ} (K τ : ℝ) (m : ℤ) : ℝ :=
  8 * ((25*(1+K)/Real.sqrt N) * (200/Real.pi)^2 * (((|(m:ℝ)|)^2)⁻¹)
      + ((10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)) * (200/Real.pi)^3
          * (((|(m:ℝ)|)^3)⁻¹))
      + (6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2) * (200/Real.pi)^4 * (((|(m:ℝ)|)^4)⁻¹)))

lemma summable_indicator_inv_pow (j : ℕ) (hj : 2 ≤ j) {Kf : ℝ} (hKf : 1 ≤ Kf) :
    Summable (fun m : ℤ => (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^j)⁻¹) else 0)) := by
  have hbase : Summable (fun m : ℤ => ((|(m:ℝ)|)^2)⁻¹) := summable_int_inv_sq
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hbase
  by_cases hm : Kf ≤ |(m:ℝ)|
  · simp only [hm, if_true]
    have h1 : (1:ℝ) ≤ |(m:ℝ)| := le_trans hKf hm
    rw [inv_eq_one_div, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    simpa using (pow_le_pow_right₀ h1 hj)
  · simp only [hm, if_false]; positivity

lemma tsum_WwFar_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} {K τ Kf : ℝ}, 1 ≤ N → 0 ≤ K → 0 < τ → (N:ℝ) ≤ τ →
      1 ≤ Kf → 100*τ/(9*Real.pi*(N:ℝ)) ≤ Kf →
      ∑' m : ℤ, (if Kf ≤ |(m:ℝ)| then WwFar (N:=N) K τ m else 0) ≤ C * (1+K) := by
  obtain ⟨CT, hCTpos, hCT⟩ := Commons.Analysis.PSeries.tsum_int_abs_pow_neg_tail_le
  refine ⟨4000000000 * CT, by positivity, ?_⟩
  intro N K τ Kf hN hK hτ hNτ hKf hKfτ
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hK1 : (0:ℝ) ≤ 1 + K := by linarith
  have hKfpos : (0:ℝ) < Kf := by linarith
  have hτpos : (0:ℝ) < τ := lt_of_lt_of_le hNpos hNτ
  have e2 : Kf ^ (1 - ((2:ℕ):ℝ)) = 1/Kf := by
    rw [show (1:ℝ) - ((2:ℕ):ℝ) = -1 by norm_num, Real.rpow_neg_one, one_div]
  have e3 : Kf ^ (1 - ((3:ℕ):ℝ)) = 1/Kf^2 := by
    rw [show (1:ℝ) - ((3:ℕ):ℝ) = -(2:ℝ) by norm_num, Real.rpow_neg (by linarith : (0:ℝ) ≤ Kf)]
    norm_num
  have e4 : Kf ^ (1 - ((4:ℕ):ℝ)) = 1/Kf^3 := by
    rw [show (1:ℝ) - ((4:ℕ):ℝ) = -(3:ℝ) by norm_num, Real.rpow_neg (by linarith : (0:ℝ) ≤ Kf)]
    norm_num
  set C2 : ℝ := 8*(25*(1+K)/Real.sqrt N)*(200/Real.pi)^2 with hC2
  set C3 : ℝ := 8*((10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3)))*(200/Real.pi)^3 with hC3
  set C4 : ℝ := 8*(6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2))*(200/Real.pi)^4 with hC4
  have hC2nn : 0 ≤ C2 := by rw [hC2]; positivity
  have hC3nn : 0 ≤ C3 := by rw [hC3]; positivity
  have hC4nn : 0 ≤ C4 := by rw [hC4]; positivity
  have hS2 : Summable (fun m : ℤ => (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^2)⁻¹) else 0)) :=
    summable_indicator_inv_pow 2 (by norm_num) hKf
  have hS3 : Summable (fun m : ℤ => (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^3)⁻¹) else 0)) :=
    summable_indicator_inv_pow 3 (by norm_num) hKf
  have hS4 : Summable (fun m : ℤ => (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^4)⁻¹) else 0)) :=
    summable_indicator_inv_pow 4 (by norm_num) hKf
  have key : ∀ m : ℤ, (if Kf ≤ |(m:ℝ)| then WwFar (N:=N) K τ m else 0)
      = C2 * (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^2)⁻¹) else 0)
        + C3 * (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^3)⁻¹) else 0)
        + C4 * (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^4)⁻¹) else 0) := by
    intro m
    unfold WwFar
    by_cases hm : Kf ≤ |(m:ℝ)| <;> simp only [hm, if_true, if_false]
    · rw [hC2, hC3, hC4]; ring
    · rw [hC2, hC3, hC4]; ring
  have hsum_eq : ∑' m : ℤ, (if Kf ≤ |(m:ℝ)| then WwFar (N:=N) K τ m else 0)
      = C2 * (∑' m : ℤ, (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^2)⁻¹) else 0))
        + C3 * (∑' m : ℤ, (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^3)⁻¹) else 0))
        + C4 * (∑' m : ℤ, (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^4)⁻¹) else 0)) := by
    have hkey := funext key
    rw [hkey, Summable.tsum_add ((hS2.mul_left C2).add (hS3.mul_left C3)) (hS4.mul_left C4),
      Summable.tsum_add (hS2.mul_left C2) (hS3.mul_left C3),
      tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rw [hsum_eq]
  have hS2b : (∑' k : ℤ, (if Kf ≤ |(k:ℝ)| then ((|(k:ℝ)|)^2)⁻¹ else 0)) ≤ CT * (1/Kf) := by
    have h := hCT 2 Kf (by norm_num) hKf
    rwa [e2] at h
  have hS3b : (∑' k : ℤ, (if Kf ≤ |(k:ℝ)| then ((|(k:ℝ)|)^3)⁻¹ else 0)) ≤ CT * (1/Kf^2) := by
    have h := hCT 3 Kf (by norm_num) hKf
    rwa [e3] at h
  have hS4b : (∑' k : ℤ, (if Kf ≤ |(k:ℝ)| then ((|(k:ℝ)|)^4)⁻¹ else 0)) ≤ CT * (1/Kf^3) := by
    have h := hCT 4 Kf (by norm_num) hKf
    rwa [e4] at h
  have hinv1 : 1/Kf ≤ 9*Real.pi*(N:ℝ)/(100*τ) := by
    have ha : (0:ℝ) < 100*τ/(9*Real.pi*(N:ℝ)) := by positivity
    have h := one_div_le_one_div_of_le ha hKfτ
    have h4 : (1:ℝ)/(100*τ/(9*Real.pi*(N:ℝ))) = 9*Real.pi*(N:ℝ)/(100*τ) := by
      field_simp
    rwa [h4] at h
  have hinv2 : 1/Kf^2 ≤ (9*Real.pi*(N:ℝ)/(100*τ))^2 := by
    have h : (1/Kf)^2 ≤ ((9*Real.pi*(N:ℝ))/(100*τ))^2 :=
      pow_le_pow_left₀ (by positivity) hinv1 2
    have h1 : (1/Kf)^2 = 1/Kf^2 := by rw [div_pow]; norm_num
    rwa [h1] at h
  have hinv3 : 1/Kf^3 ≤ (9*Real.pi*(N:ℝ)/(100*τ))^3 := by
    have h : (1/Kf)^3 ≤ ((9*Real.pi*(N:ℝ))/(100*τ))^3 :=
      pow_le_pow_left₀ (by positivity) hinv1 3
    have h1 : (1/Kf)^3 = 1/Kf^3 := by rw [div_pow]; norm_num
    rwa [h1] at h
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have ht1 := far_term1 hN1 hNτ hKf hK hCTpos hinv1
  have ht2 := far_term2 hN1 hNτ hKf hK hCTpos hinv2
  have ht3 := far_term3 hN1 hNτ hKf hK hCTpos hinv3
  have hb2 : C2 * (∑' m : ℤ, (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^2)⁻¹) else 0)) ≤ C2 * (CT * (1/Kf)) :=
    mul_le_mul_of_nonneg_left hS2b hC2nn
  have hb3 : C3 * (∑' m : ℤ, (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^3)⁻¹) else 0)) ≤ C3 * (CT * (1/Kf^2)) :=
    mul_le_mul_of_nonneg_left hS3b hC3nn
  have hb4 : C4 * (∑' m : ℤ, (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^4)⁻¹) else 0)) ≤ C4 * (CT * (1/Kf^3)) :=
    mul_le_mul_of_nonneg_left hS4b hC4nn
  have hfin : C2 * (CT * (1/Kf)) + C3 * (CT * (1/Kf^2)) + C4 * (CT * (1/Kf^3))
      ≤ (4000000000 * CT) * (1+K) := by
    rw [hC2, hC3, hC4]
    nlinarith [ht1, ht2, ht3, hCTpos, hK1]
  linarith [hb2, hb3, hb4, hfin]

lemma WwFar_nonneg {N : ℕ} {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 ≤ τ) (m : ℤ) :
    0 ≤ WwFar (N:=N) K τ m := by
  unfold WwFar
  positivity

/-- The far majorant is dominated by a multiple of `(|m|^2)⁻¹` for `|m| ≥ 1`. -/
lemma WwFar_le_sd {N : ℕ} {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 ≤ τ) {m : ℤ} (hm : 1 ≤ |(m:ℝ)|) :
    WwFar (N:=N) K τ m
      ≤ 8*((25*(1+K)/Real.sqrt N)
            + (10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))
            + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)) * (200/Real.pi)^4 * (((|(m:ℝ)|)^2)⁻¹) := by
  rw [WwFar]
  set A : ℝ := 25*(1+K)/Real.sqrt N with hA
  set B : ℝ := 10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3) with hB
  set D : ℝ := 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2) with hD
  set p : ℝ := 200/Real.pi with hp
  have hAn : 0 ≤ A := by rw [hA]; positivity
  have hBn : 0 ≤ B := by rw [hB]; positivity
  have hDn : 0 ≤ D := by rw [hD]; positivity
  have hp1 : (1:ℝ) ≤ p := by
    rw [hp, le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_four]
  have hp2 : p^2 ≤ p^4 := pow_le_pow_right₀ hp1 (by norm_num)
  have hp3 : p^3 ≤ p^4 := pow_le_pow_right₀ hp1 (by norm_num)
  have hX2 : (0:ℝ) < ((|(m:ℝ)|)^2)⁻¹ := by positivity
  have hX2n : (0:ℝ) ≤ ((|(m:ℝ)|)^2)⁻¹ := le_of_lt hX2
  have habs2 : (|(m:ℝ)|)^2 ≤ (|(m:ℝ)|)^3 := by
    have h := mul_le_mul_of_nonneg_left hm (sq_nonneg |(m:ℝ)|)
    calc (|(m:ℝ)|)^2 = (|(m:ℝ)|)^2 * 1 := (mul_one _).symm
      _ ≤ (|(m:ℝ)|)^2 * |(m:ℝ)| := h
      _ = (|(m:ℝ)|)^3 := by ring
  have habs4 : (|(m:ℝ)|)^2 ≤ (|(m:ℝ)|)^4 := by
    have h1 : (1:ℝ) ≤ (|(m:ℝ)|)^2 := one_le_pow₀ hm
    have h := mul_le_mul_of_nonneg_left h1 (sq_nonneg |(m:ℝ)|)
    calc (|(m:ℝ)|)^2 = (|(m:ℝ)|)^2 * 1 := (mul_one _).symm
      _ ≤ (|(m:ℝ)|)^2 * (|(m:ℝ)|)^2 := h
      _ = (|(m:ℝ)|)^4 := by ring
  have hX3 : ((|(m:ℝ)|)^3)⁻¹ ≤ ((|(m:ℝ)|)^2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    simpa using habs2
  have hX4 : ((|(m:ℝ)|)^4)⁻¹ ≤ ((|(m:ℝ)|)^2)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    simpa using habs4
  have t1 : A*p^2*((|(m:ℝ)|)^2)⁻¹ ≤ A*p^4*((|(m:ℝ)|)^2)⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp2 hAn) hX2n
  have t2 : B*p^3*((|(m:ℝ)|)^3)⁻¹ ≤ B*p^4*((|(m:ℝ)|)^2)⁻¹ := by
    have h1 : B*p^3 ≤ B*p^4 := mul_le_mul_of_nonneg_left hp3 hBn
    calc B*p^3*((|(m:ℝ)|)^3)⁻¹ ≤ B*p^4*((|(m:ℝ)|)^3)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ B*p^4*((|(m:ℝ)|)^2)⁻¹ := mul_le_mul_of_nonneg_left hX3 (by positivity)
  have t3 : D*p^4*((|(m:ℝ)|)^4)⁻¹ ≤ D*p^4*((|(m:ℝ)|)^2)⁻¹ :=
    mul_le_mul_of_nonneg_left hX4 (by positivity)
  have hsum : A*p^2*((|(m:ℝ)|)^2)⁻¹ + B*p^3*((|(m:ℝ)|)^3)⁻¹ + D*p^4*((|(m:ℝ)|)^4)⁻¹
      ≤ (A + B + D)*p^4*((|(m:ℝ)|)^2)⁻¹ := by
    have hR : A*p^4*((|(m:ℝ)|)^2)⁻¹ + B*p^4*((|(m:ℝ)|)^2)⁻¹ + D*p^4*((|(m:ℝ)|)^2)⁻¹
        = (A + B + D)*p^4*((|(m:ℝ)|)^2)⁻¹ := by ring
    linarith [t1, t2, t3, hR]
  calc 8*(A*p^2*((|(m:ℝ)|)^2)⁻¹ + B*p^3*((|(m:ℝ)|)^3)⁻¹ + D*p^4*((|(m:ℝ)|)^4)⁻¹)
      ≤ 8*((A + B + D)*p^4*((|(m:ℝ)|)^2)⁻¹) := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 8*(A + B + D)*p^4*((|(m:ℝ)|)^2)⁻¹ := by ring

/-- Summability of the far majorant on the region `|m| ≥ Kf`. -/
lemma summable_WwFar_ite {N : ℕ} {K τ Kf : ℝ} (hK : 0 ≤ K) (hτ : 0 ≤ τ) (hKf : 1 ≤ Kf) :
    Summable (fun m : ℤ => if Kf ≤ |(m:ℝ)| then WwFar (N:=N) K τ m else 0) := by
  set SD : ℝ := 8*((25*(1+K)/Real.sqrt N)
            + (10*(1+K)*(4*τ/(N:ℝ)^2) + 6*Real.sqrt N*(16*τ/(N:ℝ)^3))
            + 6*Real.sqrt N*((4*τ/(N:ℝ)^2)^2)) * (200/Real.pi)^4 with hSD
  have hbase : Summable (fun m : ℤ => (if Kf ≤ |(m:ℝ)| then (((|(m:ℝ)|)^2)⁻¹) else 0)) :=
    summable_indicator_inv_pow 2 (by norm_num) hKf
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (hbase.mul_left SD)
  · by_cases h : Kf ≤ |(m:ℝ)|
    · rw [if_pos h]; exact WwFar_nonneg hK hτ m
    · simp [if_neg h]
  · by_cases h : Kf ≤ |(m:ℝ)|
    · rw [if_pos h, if_pos h]
      exact WwFar_le_sd hK hτ (le_trans hKf h)
    · simp [if_neg h]

/-- The total mass of the off-band majorant is `O(1+K)`. -/
lemma tsum_WwMaj_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} {K τ : ℝ}, 1 ≤ N → 0 ≤ K → 0 < τ → (N:ℝ) ≤ τ →
      ∑' m : ℤ, WwMaj (N := N) K τ m ≤ C * (1+K) := by
  obtain ⟨Cfar, hCfarp, hfar⟩ := tsum_WwFar_le
  refine ⟨Cfar + 11000000000, by positivity, ?_⟩
  intro N K τ hN hK hτ hNτ
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  set M₀ : ℕ := Nat.ceil (100*τ/(9*Real.pi*(N:ℝ))) with hM₀
  set Kf : ℝ := ((M₀:ℤ) + 1 : ℝ) with hKf
  have hceil : 100*τ/(9*Real.pi*(N:ℝ)) ≤ (M₀:ℝ) := by
    have h := Nat.le_ceil (100*τ/(9*Real.pi*(N:ℝ)))
    rw [← hM₀] at h
    exact h
  have hceil2 : (M₀:ℝ) < 100*τ/(9*Real.pi*(N:ℝ)) + 1 := by
    have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 100*τ/(9*Real.pi*(N:ℝ)) by positivity)
    rw [← hM₀] at h
    exact h
  have hKf1 : (1:ℝ) ≤ Kf := by
    rw [hKf]; push_cast
    have : (0:ℤ) ≤ (M₀:ℤ) := Int.natCast_nonneg M₀
    linarith
  have hKfτ : 100*τ/(9*Real.pi*(N:ℝ)) ≤ Kf := by
    rw [hKf]; push_cast; linarith [hceil]
  have hdom : τ/(18*(N:ℝ)) ≤ Real.pi*Kf/200 := by
    have h1 : (100:ℝ)*τ/(9*(N:ℝ)) ≤ Real.pi*Kf := by
      have h2 : Real.pi * (100*τ/(9*Real.pi*(N:ℝ))) = 100*τ/(9*(N:ℝ)) := by
        field_simp
      calc (100:ℝ)*τ/(9*(N:ℝ)) = Real.pi * (100*τ/(9*Real.pi*(N:ℝ))) := h2.symm
        _ ≤ Real.pi * Kf := mul_le_mul_of_nonneg_left hKfτ hπ.le
    have h3 : τ/(18*(N:ℝ)) * 200 = (100:ℝ)*τ/(9*(N:ℝ)) := by
      field_simp
      try ring
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 200), h3]
    exact h1
  have hsMaj : Summable (fun m : ℤ => WwMaj (N:=N) K τ m) := summable_WwMaj hN hK hτ hNτ
  have hsFar : Summable (fun m : ℤ => if Kf ≤ |(m:ℝ)| then WwFar (N:=N) K τ m else 0) :=
    summable_WwFar_ite hK hτ.le hKf1
  rw [← Summable.sum_add_tsum_compl hsMaj (s := Finset.Icc (-(M₀:ℤ)) (M₀:ℤ))]
  have hfin : ∑ x ∈ Finset.Icc (-(M₀:ℤ)) (M₀:ℤ), WwMaj (N:=N) K τ x ≤ 11000000000*(1+K) := by
    have hcard : (((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ)).card : ℕ) : ℝ) ≤ 2*(M₀:ℝ) + 1 := by
      rw [Int.card_Icc]
      have h : (M₀:ℤ) + 1 - (-(M₀:ℤ)) = ((2*M₀+1 : ℕ) : ℤ) := by push_cast; ring
      rw [h, Int.toNat_natCast]
      push_cast
      linarith
    have hM1 : (2*(M₀:ℝ) + 1 : ℝ) ≤ 200*τ/(9*Real.pi*(N:ℝ)) + 3 := by
      have h2 : (2*(M₀:ℝ) : ℝ) < 2*(100*τ/(9*Real.pi*(N:ℝ)) + 1) := by linarith [hceil2]
      have h3 : (2*(100*τ/(9*Real.pi*(N:ℝ)) + 1) : ℝ) = 200*τ/(9*Real.pi*(N:ℝ)) + 2 := by ring
      linarith [h2, h3]
    have hCnn : (0:ℝ) ≤ 1000000000*(1+K)*N/τ := by positivity
    calc ∑ x ∈ Finset.Icc (-(M₀:ℤ)) (M₀:ℤ), WwMaj (N:=N) K τ x
        ≤ ∑ x ∈ Finset.Icc (-(M₀:ℤ)) (M₀:ℤ), (1000000000*(1+K)*N/τ) :=
          Finset.sum_le_sum (fun x _ => WwMaj_le_const hN hK hτ hNτ x)
      _ = (((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ)).card : ℕ) : ℝ) * (1000000000*(1+K)*N/τ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2*(M₀:ℝ) + 1) * (1000000000*(1+K)*N/τ) := mul_le_mul_of_nonneg_right hcard hCnn
      _ ≤ (200*τ/(9*Real.pi*(N:ℝ)) + 3) * (1000000000*(1+K)*N/τ) :=
          mul_le_mul_of_nonneg_right hM1 hCnn
      _ ≤ 11000000000*(1+K) := by
          rw [show (200*τ/(9*Real.pi*(N:ℝ)) + 3) * (1000000000*(1+K)*N/τ)
              = 1000000000*(1+K) * (200/(9*Real.pi) + 3*((N:ℝ)/τ)) by
                field_simp
                try ring]
          have hb : 200/(9*Real.pi) + 3*((N:ℝ)/τ) ≤ 11 := by
            have h1 : 200/(9*Real.pi) ≤ 200/27 := by
              rw [div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith [hπ3]
            have h2 : 3*((N:ℝ)/τ) ≤ 3 := by
              have h3 : (N:ℝ)/τ ≤ 1 := by rw [div_le_one hτ]; exact hNτ
              linarith
            linarith
          calc 1000000000*(1+K) * (200/(9*Real.pi) + 3*((N:ℝ)/τ))
              ≤ 1000000000*(1+K) * 11 := mul_le_mul_of_nonneg_left hb (by positivity)
            _ = 11000000000*(1+K) := by ring
  have hfar' : ∑' (x : ↑((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Finset ℤ) : Set ℤ)ᶜ), WwMaj (N:=N) K τ ↑x
      ≤ Cfar*(1+K) := by
    have hsub1 : Summable (fun x : ↑((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Finset ℤ) : Set ℤ)ᶜ =>
        WwMaj (N:=N) K τ (x:ℤ)) := hsMaj.subtype _
    have hsub2 : Summable (fun x : ↑((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Finset ℤ) : Set ℤ)ᶜ =>
        (if Kf ≤ |(((x:ℤ)):ℝ)| then WwFar (N:=N) K τ (x:ℤ) else 0)) := hsFar.subtype _
    have hstep1 : ∑' (x : ↑((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Finset ℤ) : Set ℤ)ᶜ),
          WwMaj (N:=N) K τ ↑x
        ≤ ∑' (x : ↑((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Finset ℤ) : Set ℤ)ᶜ),
          (if Kf ≤ |(((x:ℤ)):ℝ)| then WwFar (N:=N) K τ (x:ℤ) else 0) := by
      apply Summable.tsum_le_tsum _ hsub1 hsub2
      intro x
      have hx : ¬ ((x:ℤ) ∈ (Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Set ℤ)) := by
        have h := x.2
        rwa [Set.mem_compl_iff] at h
      have hx' : ¬ ((x:ℤ) ∈ Finset.Icc (-(M₀:ℤ)) (M₀:ℤ)) := by simpa using hx
      have hKfx : Kf ≤ |(((x:ℤ)):ℝ)| := by
        rw [hKf]
        have h1 : ((M₀:ℤ) + 1 : ℤ) ≤ |(x:ℤ)| := by
          rw [Finset.mem_Icc] at hx'
          rcases (not_and_or.mp hx') with h | h
          · have h2 : ((x:ℤ)) ≤ -((M₀:ℤ)) - 1 := by omega
            rw [abs_of_nonpos (by omega : ((x:ℤ)) ≤ 0)]
            omega
          · have h2 : ((M₀:ℤ)) + 1 ≤ (x:ℤ) := by omega
            rw [abs_of_nonneg (by omega : (0:ℤ) ≤ (x:ℤ))]
            exact h2
        calc (((M₀:ℤ):ℝ) + 1) = ((((M₀:ℤ) + 1 : ℤ)) : ℝ) := by push_cast; ring
          _ ≤ ((|(x:ℤ)| : ℤ) : ℝ) := by exact_mod_cast h1
          _ = |(((x:ℤ)):ℝ)| := by rw [Int.cast_abs]
      rw [if_pos hKfx]
      exact WwMaj_far_pt hN hK hτ hNτ hKf1 hdom hKfx
    have hstep2 : ∑' (x : ↑((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Finset ℤ) : Set ℤ)ᶜ),
          (if Kf ≤ |(((x:ℤ)):ℝ)| then WwFar (N:=N) K τ (x:ℤ) else 0)
        = ∑' m : ℤ, (((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Finset ℤ) : Set ℤ)ᶜ).indicator
            (fun m => if Kf ≤ |(m:ℝ)| then WwFar (N:=N) K τ m else 0) m := by
      exact _root_.tsum_subtype (((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Finset ℤ) : Set ℤ)ᶜ)
        (fun m => if Kf ≤ |(m:ℝ)| then WwFar (N:=N) K τ m else 0)
    have hstep3 : ∑' m : ℤ, (((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Finset ℤ) : Set ℤ)ᶜ).indicator
            (fun m => if Kf ≤ |(m:ℝ)| then WwFar (N:=N) K τ m else 0) m
        ≤ ∑' m : ℤ, (if Kf ≤ |(m:ℝ)| then WwFar (N:=N) K τ m else 0) := by
      apply Summable.tsum_le_tsum _ (hsFar.indicator _) hsFar
      intro m
      by_cases hm : m ∈ (((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Finset ℤ)) : Set ℤ)ᶜ
      · rw [Set.indicator_of_mem hm]
      · rw [Set.indicator_of_notMem hm]
        by_cases h : Kf ≤ |(m:ℝ)|
        · rw [if_pos h]; exact WwFar_nonneg hK hτ.le m
        · rw [if_neg h]
    calc ∑' (x : ↑((Finset.Icc (-(M₀:ℤ)) (M₀:ℤ) : Finset ℤ) : Set ℤ)ᶜ), WwMaj (N:=N) K τ ↑x
        ≤ _ := hstep1
      _ = _ := hstep2
      _ ≤ _ := hstep3
      _ ≤ Cfar*(1+K) := hfar hN hK hτ hNτ hKf1 hKfτ
  have hgoal : (Cfar + 11000000000)*(1+K) = Cfar*(1+K) + 11000000000*(1+K) := by ring
  linarith [hfin, hfar', hgoal]

/-! ## Interval facts for the band / dual range / support range -/

lemma Ww_lo_hi_facts {N : ℕ} (hN : 4 ≤ N) {τ : ℝ} (hτ : 0 < τ) :
    WwLo N τ ≤ WwALo N τ ∧ WwALo N τ ≤ WwDLo N τ ∧ WwDLo N τ ≤ WwDHi N τ + 1 ∧
      WwDHi N τ + 1 ≤ WwHi N τ + 1 ∧ WwBHi N τ ≤ WwHi N τ := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN4R : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N * Real.sqrt N = (N:ℝ) := by
    rw [← sq, Real.sq_sqrt hNpos.le]
  have hsqpos : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hsqrt_le : Real.sqrt N ≤ N := by nlinarith [hsq, Real.sqrt_nonneg N, hN4R]
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hd1 : 2*Real.pi*(2*(N:ℝ) + Real.sqrt N) ≤ 6*Real.pi*(N:ℝ) := by
    nlinarith [hsqrt_le, Real.pi_pos, Real.sqrt_nonneg N]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [WwLo, WwALo]
    exact Nat.ceil_mono (div_le_div_of_nonneg_left (le_of_lt hτ)
      (by positivity) hd1)
  · rw [WwALo, WwDLo]
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_left (le_of_lt hτ) (by positivity)
    nlinarith [Real.sqrt_nonneg N, hπ]
  · rw [WwDLo, Nat.ceil_le]
    have h2 : τ/(2*Real.pi*(N:ℝ)) < (WwDHi N τ : ℝ) + 1 := by
      rw [WwDHi]
      exact Nat.lt_floor_add_one _
    have h3 : τ/(4*Real.pi*(N:ℝ)) ≤ τ/(2*Real.pi*(N:ℝ)) :=
      div_le_div_of_nonneg_left (le_of_lt hτ) (by positivity)
        (by nlinarith [hπ, hNpos])
    have h4 : ((WwDHi N τ + 1 : ℕ) : ℝ) = (WwDHi N τ : ℝ) + 1 := by push_cast; ring
    rw [h4]
    linarith
  · have h : WwDHi N τ ≤ WwHi N τ := by
      rw [WwDHi, WwHi]
      apply Nat.floor_mono
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(N:ℝ))
        (by positivity : (0:ℝ) < Real.pi*(N:ℝ))]
      have hpos : (0:ℝ) < τ*Real.pi*(N:ℝ) := by positivity
      nlinarith [hpos]
    omega
  · rw [WwBHi, WwHi]
    apply Nat.floor_mono
    have hsqrt2 : (2:ℝ) ≤ Real.sqrt N := by
      have h := Real.sqrt_le_sqrt hN4R
      rwa [show Real.sqrt (4:ℝ) = 2 by norm_num] at h
    have hkey : 4*Real.sqrt N ≤ 3*(N:ℝ) := by
      have h4 : (4:ℝ) ≤ 3*Real.sqrt N := by linarith
      have hmul := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg N)
      nlinarith [hmul, hsq]
    rw [div_le_div_iff₀ (by nlinarith [hsq, hsqpos, hN4R] : (0:ℝ) < 2*Real.pi*((N:ℝ) - Real.sqrt N))
      (by positivity : (0:ℝ) < Real.pi*(N:ℝ))]
    have h1 : 4*τ*Real.pi*Real.sqrt N ≤ 3*τ*Real.pi*(N:ℝ) := by
      have := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ τ*Real.pi)
      nlinarith [this]
    have h2 : (0:ℝ) < τ*Real.pi := by positivity
    nlinarith [h1, h2]

lemma lt_WwALo {N : ℕ} {τ : ℝ} (hτ : 0 ≤ τ) {m : ℕ} (hm : m < WwALo N τ) :
    (m:ℝ) < τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) := by
  have hW : 1 ≤ WwALo N τ := by omega
  have h1 : ((m:ℕ):ℝ) ≤ ((WwALo N τ - 1 : ℕ):ℝ) := by
    exact_mod_cast (by omega : m ≤ WwALo N τ - 1)
  have h1' : ((WwALo N τ - 1 : ℕ):ℝ) = ((WwALo N τ : ℕ):ℝ) - 1 := by
    rw [Nat.cast_sub hW]; norm_num
  rw [h1'] at h1
  have h2 : ((WwALo N τ : ℕ):ℝ) - 1 < τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) := by
    rw [WwALo]
    have h3 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) by
      positivity)
    push_cast at h3 ⊢
    linarith
  linarith

lemma gt_WwBHi {N : ℕ} {τ : ℝ} {m : ℕ} (hm : WwBHi N τ < m) :
    τ/(2*Real.pi*((N:ℝ) - Real.sqrt N)) < (m:ℝ) := by
  have h1 : ((WwBHi N τ : ℕ):ℝ) < (m:ℝ) := by exact_mod_cast hm
  have h2 : τ/(2*Real.pi*((N:ℝ) - Real.sqrt N)) < ((WwBHi N τ : ℕ):ℝ) + 1 := by
    have h3 := Nat.lt_floor_add_one (τ/(2*Real.pi*((N:ℝ) - Real.sqrt N)))
    rw [WwBHi]
    linarith
  have h4 : ((WwBHi N τ : ℕ):ℝ) + 1 ≤ (m:ℝ) := by
    have : WwBHi N τ + 1 ≤ m := hm
    exact_mod_cast this
  linarith

/-! ## Telescoping sums and vanishing of `χ(s_m)` outside the transition strips -/

/-- Telescoping sum over `Icc A (B-1)`. -/
lemma sum_Icc_tele {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (f : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc A (B - 1), (f m - f (m + 1)) = f A - f B := by
  have hIcc : Finset.Icc A (B - 1) = Finset.Ico A B := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have h2 : ∑ k ∈ Finset.range (B - A), (f (A + k) - f (A + (k + 1)))
      = f (A + 0) - f (A + (B - A)) :=
    Finset.sum_range_sub' (fun k : ℕ => f (A + k)) (B - A)
  have hgoal : (∑ k ∈ Finset.range (B - A), (f (A + k) - f (A + k + 1)))
      = ∑ k ∈ Finset.range (B - A), (f (A + k) - f (A + (k + 1))) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.add_assoc]
  rw [hgoal, h2]
  have h3 : A + (B - A) = B := by omega
  rw [h3, Nat.add_zero]

lemma chi_WwS_eq_zero_left {N : ℕ} (hN : 1 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {τ : ℝ} (hτ : 0 < τ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < WwALo N τ) :
    χ (WwS τ m) = 0 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  apply hχz
  right
  have hmR : (m:ℝ) < τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) := lt_WwALo hτ.le hm
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hden : (0:ℝ) < 2*Real.pi*(2*(N:ℝ) + Real.sqrt N) := by
    have : (0:ℝ) < 2*(N:ℝ) + Real.sqrt N := by
      have := Real.sqrt_nonneg N; linarith
    positivity
  have h1 : (m:ℝ) * (2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) < τ := (lt_div_iff₀ hden).mp hmR
  have h3 : (2*N:ℝ) + Real.sqrt N < τ/(2*Real.pi*(m:ℝ)) := by
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < 2*Real.pi*(m:ℝ))]
    nlinarith [h1]
  show (2*N:ℝ) + Real.sqrt N ≤ WwS τ m
  rw [WwS]
  exact le_of_lt h3

lemma chi_WwS_eq_zero_right {N : ℕ} (hN : 2 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {τ : ℝ} (hτ : 0 < τ) {m : ℕ} (hm : WwBHi N τ < m) :
    χ (WwS τ m) = 0 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hsqN : Real.sqrt N < N := by
    have h2 : (1:ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    have h3 : (1:ℝ) < Real.sqrt N := by
      rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)]
      simpa using h2
    have h4 : Real.sqrt N * 1 < Real.sqrt N * Real.sqrt N :=
      mul_lt_mul_of_pos_left h3 (Real.sqrt_pos.mpr hNpos)
    nlinarith [h4, Real.sq_sqrt hNpos.le]
  apply hχz
  left
  have hmR : τ/(2*Real.pi*((N:ℝ) - Real.sqrt N)) < (m:ℝ) := gt_WwBHi hm
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hden : (0:ℝ) < 2*Real.pi*(m:ℝ) := by positivity
  have hD : (0:ℝ) < 2*Real.pi*((N:ℝ) - Real.sqrt N) := by
    have : (0:ℝ) < (N:ℝ) - Real.sqrt N := by linarith
    positivity
  have h1 : τ < (m:ℝ) * (2*Real.pi*((N:ℝ) - Real.sqrt N)) := (div_lt_iff₀ hD).mp hmR
  have h3 : τ/(2*Real.pi*(m:ℝ)) < (N:ℝ) - Real.sqrt N := by
    rw [div_lt_iff₀ hden]
    nlinarith [h1]
  show WwS τ m ≤ (N:ℝ) - Real.sqrt N
  rw [WwS]
  exact le_of_lt h3

/-! ## The weight variation bound for the residual -/

lemma weight_var_bound {N A B : ℕ} (hN : 1 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 1 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hA : 2 ≤ A) (hAB : A ≤ B)
    (hAl : τ/(8*Real.pi*(N:ℝ)) ≤ (A:ℝ))
    (hspread : τ/(2*Real.pi*(A:ℝ)) - τ/(2*Real.pi*(B:ℝ)) ≤ Real.sqrt N) :
    ‖(((Real.sqrt (B:ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ B) : ℂ)‖
      + ∑ m ∈ Finset.Icc A (B - 1),
          ‖(((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ m) : ℂ)
            - (((Real.sqrt (((m+1:ℕ)):ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ (m+1)) : ℂ)‖
      ≤ 12 * (1+K) * Real.sqrt ((N:ℝ)/τ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hsqrtNpos : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hApos : (0:ℝ) < (A:ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hBpos : (0:ℝ) < (B:ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hsqrtA : (0:ℝ) < Real.sqrt (A:ℝ) := Real.sqrt_pos.mpr hApos
  have hsqrtB : (0:ℝ) < Real.sqrt (B:ℝ) := Real.sqrt_pos.mpr hBpos
  have hτpos : (0:ℝ) < τ := hτ
  set c : ℝ := Real.sqrt ((N:ℝ)/τ) with hcdef
  have hcpos : (0:ℝ) < c := by rw [hcdef]; exact Real.sqrt_pos.mpr (by positivity)
  -- (1) 1/√A ≤ √(8π)·c
  have h1A : 1/Real.sqrt (A:ℝ) ≤ Real.sqrt (8*Real.pi) * c := by
    have hone : (1:ℝ) ≤ Real.sqrt (A:ℝ) * Real.sqrt (8*Real.pi*((N:ℝ)/τ)) := by
      have hkey : (1:ℝ) ≤ (A:ℝ) * (8*Real.pi*((N:ℝ)/τ)) := by
        have hmul := mul_le_mul_of_nonneg_left hAl (by positivity : (0:ℝ) ≤ 8*Real.pi*((N:ℝ)/τ))
        have h2 : (8*Real.pi*((N:ℝ)/τ)) * (τ/(8*Real.pi*(N:ℝ))) = 1 := by
          field_simp
          try ring
        linarith [hmul, h2]
      have hsq : (1:ℝ) ≤ Real.sqrt ((A:ℝ) * (8*Real.pi*((N:ℝ)/τ))) := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt hkey
      rwa [Real.sqrt_mul hApos.le] at hsq
    rw [div_le_iff₀ hsqrtA]
    have h2 : Real.sqrt (8*Real.pi*((N:ℝ)/τ)) = Real.sqrt (8*Real.pi) * c := by
      rw [hcdef, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 8*Real.pi)]
    rw [h2] at hone
    calc (1:ℝ) ≤ Real.sqrt (A:ℝ) * (Real.sqrt (8*Real.pi) * c) := hone
      _ = Real.sqrt (8*Real.pi) * c * Real.sqrt (A:ℝ) := by ring
  -- (2) the first term
  have hfirst : ‖(((Real.sqrt (B:ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ B) : ℂ)‖
      ≤ Real.sqrt (8*Real.pi) * c := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt (B:ℝ))⁻¹)]
    have hχB : ‖(χ (WwS τ B) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 _).1]
      exact (hχ0 _).2
    have hBA : (Real.sqrt (B:ℝ))⁻¹ ≤ (Real.sqrt (A:ℝ))⁻¹ := by
      rw [inv_le_inv₀ hsqrtB hsqrtA]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hAB)
    calc (Real.sqrt (B:ℝ))⁻¹ * ‖(χ (WwS τ B) : ℂ)‖
        ≤ (Real.sqrt (B:ℝ))⁻¹ * 1 := mul_le_mul_of_nonneg_left hχB (by positivity)
      _ ≤ (Real.sqrt (A:ℝ))⁻¹ := by rw [mul_one]; exact hBA
      _ = 1/Real.sqrt (A:ℝ) := by rw [inv_eq_one_div]
      _ ≤ Real.sqrt (8*Real.pi) * c := h1A
  -- (3) the mean value bound
  have hchain : ∀ y z : ℝ, |χ y - χ z| ≤ (K/Real.sqrt N) * |y - z| := by
    intro y z
    have hdiff : ∀ x : ℝ, DifferentiableAt ℝ χ x := fun x =>
      (hχd.differentiable (by norm_num)).differentiableAt
    have hbd : ∀ x : ℝ, ‖deriv χ x‖ ≤ K/Real.sqrt N := by
      intro x; rw [Real.norm_eq_abs]; exact hbdd x
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := χ) (s := Set.univ)
      (fun x _ => hdiff x) (fun x _ => hbd x) convex_univ (Set.mem_univ z) (Set.mem_univ y)
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    exact h
  -- (4) monotonicity of WwS in m
  have hmono : ∀ m : ℕ, 1 ≤ m → WwS τ (m + 1) ≤ WwS τ m := by
    intro m hm1
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    rw [WwS, WwS]
    apply div_le_div_of_nonneg_left (le_of_lt hτpos) (by positivity : (0:ℝ) < 2*Real.pi*(m:ℝ))
    push_cast
    nlinarith [Real.pi_pos]
  -- (5) per-term bound
  have hper : ∀ m ∈ Finset.Icc A (B-1),
      ‖(((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ m) : ℂ)
        - (((Real.sqrt (((m+1:ℕ)):ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ (m+1)) : ℂ)‖
      ≤ (1/Real.sqrt (A:ℝ)) * ((K/Real.sqrt N) * (WwS τ m - WwS τ (m+1)))
        + ((Real.sqrt (m:ℝ))⁻¹ - (Real.sqrt (((m+1:ℕ)):ℝ))⁻¹) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hdecomp : (((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ m) : ℂ)
        - (((Real.sqrt (((m+1:ℕ)):ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ (m+1)) : ℂ)
        = (((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ) * ((χ (WwS τ m) : ℂ) - (χ (WwS τ (m+1)) : ℂ))
          + ((((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ) - (((Real.sqrt (((m+1:ℕ)):ℝ))⁻¹ : ℝ) : ℂ))
            * (χ (WwS τ (m+1)) : ℂ) := by ring
    rw [hdecomp]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · rw [norm_mul]
      have h1 : ‖(((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt (m:ℝ))⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [h1]
      have hχd1 : ‖((χ (WwS τ m) : ℂ) - (χ (WwS τ (m+1)) : ℂ))‖
          = |χ (WwS τ m) - χ (WwS τ (m+1))| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [hχd1]
      have hch := hchain (WwS τ m) (WwS τ (m+1))
      have hmn := hmono m (by omega)
      have habs : |WwS τ m - WwS τ (m+1)| = WwS τ m - WwS τ (m+1) :=
        abs_of_nonneg (by linarith)
      rw [habs] at hch
      have hle1 : (Real.sqrt (m:ℝ))⁻¹ ≤ 1/Real.sqrt (A:ℝ) := by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le hsqrtA (Real.sqrt_le_sqrt (by exact_mod_cast hm.1))
      exact mul_le_mul hle1 hch (abs_nonneg _) (by positivity)
    · rw [norm_mul]
      have hge : (Real.sqrt (((m+1:ℕ)):ℝ))⁻¹ ≤ (Real.sqrt (m:ℝ))⁻¹ := by
        rw [inv_le_inv₀ (by positivity) (by positivity)]
        exact Real.sqrt_le_sqrt (by push_cast; linarith)
      have h2 : ‖((((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ) - (((Real.sqrt (((m+1:ℕ)):ℝ))⁻¹ : ℝ) : ℂ))‖
          = (Real.sqrt (m:ℝ))⁻¹ - (Real.sqrt (((m+1:ℕ)):ℝ))⁻¹ := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        linarith
      rw [h2]
      have hχle : ‖(χ (WwS τ (m+1)) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 _).1]
        exact (hχ0 _).2
      calc ((Real.sqrt (m:ℝ))⁻¹ - (Real.sqrt (((m+1:ℕ)):ℝ))⁻¹) * ‖(χ (WwS τ (m+1)) : ℂ)‖
          ≤ ((Real.sqrt (m:ℝ))⁻¹ - (Real.sqrt (((m+1:ℕ)):ℝ))⁻¹) * 1 :=
            mul_le_mul_of_nonneg_left hχle (by linarith)
        _ = _ := by ring
  -- (6) sum of the variation
  have hsumvar : ∑ m ∈ Finset.Icc A (B - 1),
      ‖(((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ m) : ℂ)
        - (((Real.sqrt (((m+1:ℕ)):ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ (m+1)) : ℂ)‖
      ≤ (1 + K) * (Real.sqrt (8*Real.pi) * c) := by
    have hsum1 : ∑ m ∈ Finset.Icc A (B - 1),
        ((Real.sqrt (m:ℝ))⁻¹ - (Real.sqrt (((m+1:ℕ)):ℝ))⁻¹)
        = (Real.sqrt (A:ℝ))⁻¹ - (Real.sqrt (B:ℝ))⁻¹ :=
      sum_Icc_tele (by omega : 1 ≤ A) hAB (fun m : ℕ => (Real.sqrt (m:ℝ))⁻¹)
    have hsum2 : ∑ m ∈ Finset.Icc A (B - 1), (WwS τ m - WwS τ (m+1))
        = WwS τ A - WwS τ B :=
      sum_Icc_tele (by omega : 1 ≤ A) hAB (fun m : ℕ => WwS τ m)
    have hstep : (∑ m ∈ Finset.Icc A (B-1),
        ((1/Real.sqrt (A:ℝ)) * ((K/Real.sqrt N) * (WwS τ m - WwS τ (m+1)))))
        = (1/Real.sqrt (A:ℝ)) * (K/Real.sqrt N) * (WwS τ A - WwS τ B) := by
      rw [show (∑ m ∈ Finset.Icc A (B-1),
          ((1/Real.sqrt (A:ℝ)) * ((K/Real.sqrt N) * (WwS τ m - WwS τ (m+1)))))
          = ∑ m ∈ Finset.Icc A (B-1),
            (((1/Real.sqrt (A:ℝ)) * (K/Real.sqrt N)) * (WwS τ m - WwS τ (m+1))) by
        apply Finset.sum_congr rfl; intro m hm; ring]
      rw [← Finset.mul_sum, hsum2]
    calc ∑ m ∈ Finset.Icc A (B - 1),
        ‖(((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ m) : ℂ)
          - (((Real.sqrt (((m+1:ℕ)):ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ (m+1)) : ℂ)‖
        ≤ ∑ m ∈ Finset.Icc A (B-1),
            ((1/Real.sqrt (A:ℝ)) * ((K/Real.sqrt N) * (WwS τ m - WwS τ (m+1)))
              + ((Real.sqrt (m:ℝ))⁻¹ - (Real.sqrt (((m+1:ℕ)):ℝ))⁻¹)) :=
          Finset.sum_le_sum hper
      _ = (1/Real.sqrt (A:ℝ)) * (K/Real.sqrt N) * (WwS τ A - WwS τ B)
            + ((Real.sqrt (A:ℝ))⁻¹ - (Real.sqrt (B:ℝ))⁻¹) := by
          rw [Finset.sum_add_distrib, hstep, hsum1]
      _ ≤ (1 + K) * (Real.sqrt (8*Real.pi) * c) := by
          rw [WwS, WwS]
          have h3 : (K/Real.sqrt N) * Real.sqrt N = K := div_mul_cancel₀ K (ne_of_gt hsqrtNpos)
          have hfirst2 : (1/Real.sqrt (A:ℝ)) * (K/Real.sqrt N)
              * (τ/(2*Real.pi*(A:ℝ)) - τ/(2*Real.pi*(B:ℝ))) ≤ K * (Real.sqrt (8*Real.pi) * c) := by
            calc (1/Real.sqrt (A:ℝ)) * (K/Real.sqrt N)
                  * (τ/(2*Real.pi*(A:ℝ)) - τ/(2*Real.pi*(B:ℝ)))
                ≤ (1/Real.sqrt (A:ℝ)) * (K/Real.sqrt N) * Real.sqrt N :=
                  mul_le_mul_of_nonneg_left hspread (by positivity)
              _ = (1/Real.sqrt (A:ℝ)) * ((K/Real.sqrt N) * Real.sqrt N) := by ring
              _ = K * (1/Real.sqrt (A:ℝ)) := by rw [h3]; ring
              _ ≤ K * (Real.sqrt (8*Real.pi) * c) := mul_le_mul_of_nonneg_left h1A hK
          have hsecond2 : (Real.sqrt (A:ℝ))⁻¹ - (Real.sqrt (B:ℝ))⁻¹
              ≤ Real.sqrt (8*Real.pi) * c := by
            have h0 : (0:ℝ) ≤ (Real.sqrt (B:ℝ))⁻¹ := by positivity
            have h1 : (Real.sqrt (A:ℝ))⁻¹ ≤ 1/Real.sqrt (A:ℝ) := le_of_eq (inv_eq_one_div _)
            linarith [h1A, h0, h1]
          have hfin : (K + 1) * (Real.sqrt (8*Real.pi) * c)
              = (1 + K) * (Real.sqrt (8*Real.pi) * c) := by ring
          linarith [hfirst2, hsecond2, hfin]
  -- (7) combine
  have h9 : Real.sqrt (8*Real.pi) ≤ 6 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    nlinarith [Real.pi_lt_four]
  have hW : ‖(((Real.sqrt (B:ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ B) : ℂ)‖
      + ∑ m ∈ Finset.Icc A (B - 1),
          ‖(((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ m) : ℂ)
            - (((Real.sqrt (((m+1:ℕ)):ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ (m+1)) : ℂ)‖
      ≤ (Real.sqrt (8*Real.pi) * c) + (1 + K) * (Real.sqrt (8*Real.pi) * c) :=
    add_le_add hfirst hsumvar
  have hgoal : (Real.sqrt (8*Real.pi) * c) + (1 + K) * (Real.sqrt (8*Real.pi) * c)
      ≤ 12 * (1+K) * Real.sqrt ((N:ℝ)/τ) := by
    rw [hcdef]
    have hsqrtNτ : (0:ℝ) ≤ Real.sqrt ((N:ℝ)/τ) := Real.sqrt_nonneg _
    have h2 : (Real.sqrt (8*Real.pi) * Real.sqrt ((N:ℝ)/τ))
        + (1+K) * (Real.sqrt (8*Real.pi) * Real.sqrt ((N:ℝ)/τ))
        = (Real.sqrt (8*Real.pi) * Real.sqrt ((N:ℝ)/τ)) * (2 + K) := by ring
    rw [h2]
    have h3 : (Real.sqrt (8*Real.pi)) * (2+K) ≤ 12 * (1+K) := by nlinarith [h9, hK]
    calc (Real.sqrt (8*Real.pi) * Real.sqrt ((N:ℝ)/τ)) * (2 + K)
        = (Real.sqrt (8*Real.pi) * (2+K)) * Real.sqrt ((N:ℝ)/τ) := by ring
      _ ≤ (12*(1+K)) * Real.sqrt ((N:ℝ)/τ) := mul_le_mul_of_nonneg_right h3 hsqrtNτ
      _ = 12 * (1+K) * Real.sqrt ((N:ℝ)/τ) := by ring
  linarith [hW, hgoal]
/-! ## Norm bounds for the main term and the residual sums -/

lemma WwMainTerm_norm_le {N : ℕ} {χ : ℝ → ℝ} (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    {τ : ℝ} {m : ℕ} (hm : 1 ≤ m) : ‖WwMainTerm χ τ m‖ ≤ 1 := by
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  unfold WwMainTerm
  rw [norm_mul, norm_mul]
  have h2 : ‖(((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ)‖ = (Real.sqrt (m:ℝ))⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h3 : ‖Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (m:ℝ) : ℝ) : ℂ))))‖ = 1 := by
    have heq : -(Complex.I * ((τ : ℂ) * ((Real.log (m:ℝ) : ℝ) : ℂ)))
        = (((-(τ * Real.log (m:ℝ))) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_neg, Complex.ofReal_mul]
      ring
    rw [heq, Complex.norm_exp_ofReal_mul_I]
  have h4 : ‖(χ (WwS τ m) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχ0 _).1]
    exact (hχ0 _).2
  have h5 : (0:ℝ) < Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr hmpos
  have h6 : (1:ℝ) ≤ Real.sqrt (m:ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hm)
  have h7 : (Real.sqrt (m:ℝ))⁻¹ ≤ 1 := by
    rw [inv_eq_one_div, div_le_one h5]; exact h6
  rw [h2, h3]
  nlinarith [h4, h7, norm_nonneg (χ (WwS τ m) : ℂ)]

lemma WwMainTerm_eq_zero_of_lt {N : ℕ} (hN : 1 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {τ : ℝ} (hτ : 0 < τ) {m : ℕ} (hm1 : 1 ≤ m) (hm : m < WwALo N τ) :
    WwMainTerm χ τ m = 0 := by
  have h := chi_WwS_eq_zero_left hN hχz hτ hm1 hm
  unfold WwMainTerm
  rw [h]
  simp

lemma WwMainTerm_eq_zero_of_gt {N : ℕ} (hN : 2 ≤ N) {χ : ℝ → ℝ}
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {τ : ℝ} (hτ : 0 < τ) {m : ℕ} (hm : WwBHi N τ < m) :
    WwMainTerm χ τ m = 0 := by
  have h := chi_WwS_eq_zero_right hN hχz hτ hm
  unfold WwMainTerm
  rw [h]
  simp

/-- In the "small `τ`" regime the residual sum is bounded by an absolute constant. -/
lemma WwMainTerm_sum_bound_small :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ}, 4 ≤ N → ∀ {χ : ℝ → ℝ}, (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) →
      ∀ {K τ : ℝ}, 0 ≤ K → 0 < τ → ∀ {A B : ℕ}, 1 ≤ A → A ≤ B →
      ((B - A + 1 : ℕ) : ℝ) ≤ τ/(Real.pi*((N:ℝ)*Real.sqrt N)) + 2 →
      τ ≤ 100*((N:ℝ)*Real.sqrt N) →
      ‖∑ m ∈ Finset.Icc A B, WwMainTerm χ τ m‖ ≤ C * (1+K) := by
  refine ⟨200, by norm_num, ?_⟩
  intro N hN χ hχ0 K τ hK hτ A B hA1 hAB hlen hsmall
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN32pos : (0:ℝ) < (N:ℝ) * Real.sqrt N := by positivity
  have hcard1 : ((Finset.Icc A B).card : ℝ) ≤ ((B - A + 1 : ℕ) : ℝ) := by
    rw [Nat.card_Icc]
    exact_mod_cast (by omega : B + 1 - A ≤ B - A + 1)
  have hcard2 : (((B - A + 1 : ℕ)) : ℝ) ≤ 200 := by
    have h3 : τ/(Real.pi*((N:ℝ)*Real.sqrt N)) ≤ 100/Real.pi := by
      rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
      nlinarith [hsmall, Real.pi_pos]
    have h4 : (100:ℝ)/Real.pi ≤ 100/3 := by
      rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
      nlinarith [Real.pi_gt_three]
    linarith [hlen, h3, h4]
  calc ‖∑ m ∈ Finset.Icc A B, WwMainTerm χ τ m‖
      ≤ ∑ m ∈ Finset.Icc A B, ‖WwMainTerm χ τ m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc A B, (1:ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [Finset.mem_Icc] at hm
        exact WwMainTerm_norm_le (N := N) hχ0 (by omega)
    _ = ((Finset.Icc A B).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 200 := by linarith [hcard1, hcard2]
    _ = 200 * 1 := by ring
    _ ≤ 200 * (1+K) := by
        apply mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ 1+K) (by norm_num)

/-- In the "large `τ`" regime the weighted stationary-phase sum is applied to the residual. -/
lemma WwMainTerm_sum_bound_big :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 1 χ)
      (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
      {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hNτ : (N:ℝ) ≤ τ)
      (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
      {A B : ℕ} (hA2 : 2 ≤ A) (hAB : A ≤ B) (h2A : B ≤ 2*A)
      (hAl : τ/(8*Real.pi*(N:ℝ)) ≤ (A:ℝ))
      (hspread : τ/(2*Real.pi*(A:ℝ)) - τ/(2*Real.pi*(B:ℝ)) ≤ Real.sqrt N)
      (hlen : ((B - A + 1 : ℕ) : ℝ) ≤ τ/(Real.pi*((N:ℝ)*Real.sqrt N)) + 2)
      (hBle : (B:ℝ) ≤ τ/(Real.pi*(N:ℝ))) (hbig : 100*((N:ℝ)*Real.sqrt N) < τ),
      ‖∑ m ∈ Finset.Icc A B, WwMainTerm χ τ m‖ ≤ C * (1+K) := by
  obtain ⟨Cw, hCwpos, hCw⟩ := weighted_log_phase_short_range
  refine ⟨Cw * 2000, by positivity, ?_⟩
  intro N hN χ hχd hχ0 K τ hK hτ hNτ hbdd A B hA2 hAB h2A hAl hspread hlen hBle hbig
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hsqrtNpos : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hN32pos : (0:ℝ) < (N:ℝ) * Real.sqrt N := by positivity
  have hApos : (0:ℝ) < (A:ℝ) := by exact_mod_cast (by omega : 0 < A)
  have hBpos : (0:ℝ) < (B:ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hτpos : (0:ℝ) < τ := hτ
  -- the range is short relative to `B`
  have hBge : τ/(8*Real.pi*(N:ℝ)) ≤ (B:ℝ) := by
    calc τ/(8*Real.pi*(N:ℝ)) ≤ (A:ℝ) := hAl
      _ ≤ (B:ℝ) := by exact_mod_cast hAB
  have hlenB : ((((B - A + 1 : ℕ)) : ℝ) / (B:ℝ)) ≤ 9/Real.sqrt N := by
    have hone : (1:ℝ)/(B:ℝ) ≤ 8*Real.pi*(N:ℝ)/τ := by
      rw [div_le_div_iff₀ hBpos hτpos]
      have hD : (0:ℝ) < 8*Real.pi*(N:ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hBge hD.le
      have he : τ/(8*Real.pi*(N:ℝ)) * (8*Real.pi*(N:ℝ)) = τ := div_mul_cancel₀ τ (ne_of_gt hD)
      rw [he] at hmul
      linarith [hmul]
    have h1 : ((((B - A + 1 : ℕ)) : ℝ) / (B:ℝ)) ≤ (((B - A + 1 : ℕ)) : ℝ) * (8*Real.pi*(N:ℝ)/τ) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hone (by positivity)
    have h2 : (((B - A + 1 : ℕ)) : ℝ) * (8*Real.pi*(N:ℝ)/τ)
        ≤ (τ/(Real.pi*((N:ℝ)*Real.sqrt N)) + 2) * (8*Real.pi*(N:ℝ)/τ) :=
      mul_le_mul_of_nonneg_right hlen (by positivity)
    have h3 : (τ/(Real.pi*((N:ℝ)*Real.sqrt N)) + 2) * (8*Real.pi*(N:ℝ)/τ)
        = 8/Real.sqrt N + 16*Real.pi*(N:ℝ)/τ := by
      field_simp
      try ring
    have h4 : 16*Real.pi*(N:ℝ)/τ ≤ 1/Real.sqrt N := by
      rw [div_le_iff₀ hτpos]
      rw [show (1/Real.sqrt N) * τ = τ/Real.sqrt N by ring]
      rw [le_div_iff₀ hsqrtNpos]
      nlinarith [hbig, Real.pi_lt_four, hNpos, hsqrtNpos]
    have h5 : (8:ℝ)/Real.sqrt N + 1/Real.sqrt N = 9/Real.sqrt N := by ring
    linarith [h1, h2, h3, h4, h5]
  -- weight variation bound
  set w : ℕ → ℂ := fun m => (((Real.sqrt (m:ℝ))⁻¹ : ℝ) : ℂ) * (χ (WwS τ m) : ℂ) with hw
  have hWb := weight_var_bound (N:=N) (A:=A) (B:=B) (χ:=χ) (K:=K) (τ:=τ)
    (by omega : 1 ≤ N) hχd hχ0 hK hτ hbdd hA2 hAB hAl hspread
  have hWnn : (0:ℝ) ≤ ‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖ := by positivity
  -- the stationary-phase sum
  have htool := hCw hA2 hAB h2A hτ w
  have hsum_eq : ∑ m ∈ Finset.Icc A B, WwMainTerm χ τ m
      = ∑ m ∈ Finset.Icc A B, w m * Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (m:ℝ) : ℝ) : ℂ)))) := by
    apply Finset.sum_congr rfl
    intro m hm
    unfold WwMainTerm
    simp only [hw]
    ring
  rw [hsum_eq]
  -- bounds on the bracket factors
  have hsqrtτN : Real.sqrt (τ/(N:ℝ)) * Real.sqrt ((N:ℝ)/τ) = 1 := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ τ/(N:ℝ))]
    rw [show τ/(N:ℝ) * ((N:ℝ)/τ) = 1 by field_simp]
    exact Real.sqrt_one
  have hbr1 : Real.sqrt (τ/(2*Real.pi)) * ((((B - A + 1 : ℕ)) : ℝ) / (B:ℝ))
      ≤ 9*Real.sqrt (τ/(N:ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hlenB (Real.sqrt_nonneg (τ/(2*Real.pi)))
    have h2 : Real.sqrt (τ/(2*Real.pi)) * (9/Real.sqrt N) = 9*Real.sqrt (τ/(2*Real.pi*(N:ℝ))) := by
      rw [show Real.sqrt (τ/(2*Real.pi)) * (9/Real.sqrt N)
          = 9*(Real.sqrt (τ/(2*Real.pi))/Real.sqrt N) by ring]
      rw [← Real.sqrt_div (by positivity : (0:ℝ) ≤ τ/(2*Real.pi))]
      congr 1
      field_simp
      try ring
    have h3 : Real.sqrt (τ/(2*Real.pi*(N:ℝ))) ≤ Real.sqrt (τ/(N:ℝ)) := by
      apply Real.sqrt_le_sqrt
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_gt_three, hNpos, hτpos, mul_pos hτpos hNpos]
    linarith [h1, h2, h3]
  have hbr2 : Real.sqrt (2*Real.pi) * (B:ℝ) / Real.sqrt τ ≤ Real.sqrt τ/(N:ℝ) := by
    have hst : (0:ℝ) < Real.sqrt τ := Real.sqrt_pos.mpr hτpos
    rw [div_le_iff₀ hst]
    rw [show Real.sqrt τ/(N:ℝ) * Real.sqrt τ = Real.sqrt τ * Real.sqrt τ/(N:ℝ) by ring]
    rw [le_div_iff₀ hNpos]
    rw [← sq, Real.sq_sqrt hτpos.le]
    have h1' : Real.sqrt (2*Real.pi) * ((B:ℝ) * (N:ℝ)) ≤
        Real.sqrt (2*Real.pi) * ((τ/(Real.pi*(N:ℝ))) * (N:ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBle hNpos.le)
        (Real.sqrt_nonneg (2*Real.pi))
    have h1 : Real.sqrt (2*Real.pi) * (B:ℝ) * (N:ℝ) ≤
        Real.sqrt (2*Real.pi) * ((τ/(Real.pi*(N:ℝ))) * (N:ℝ)) := by nlinarith [h1']
    have he : (τ/(Real.pi*(N:ℝ))) * (N:ℝ) = τ/Real.pi := by field_simp; try ring
    have h2 : Real.sqrt (2*Real.pi) * (τ/Real.pi) ≤ τ := by
      rw [show Real.sqrt (2*Real.pi) * (τ/Real.pi) = Real.sqrt (2*Real.pi) * τ / Real.pi by ring]
      rw [div_le_iff₀ Real.pi_pos]
      have h3 : Real.sqrt (2*Real.pi) ≤ Real.pi := by
        rw [Real.sqrt_le_iff]
        refine ⟨le_of_lt Real.pi_pos, ?_⟩
        nlinarith [Real.pi_gt_three]
      nlinarith [mul_le_mul_of_nonneg_right h3 hτpos.le]
    rw [he] at h1
    linarith [h1, h2]
  -- the three product bounds
  have hp1 : (Real.sqrt (τ/(2*Real.pi)) * ((((B - A + 1 : ℕ)) : ℝ) / (B:ℝ)))
      * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖) ≤ 200*(1+K) := by
    calc (Real.sqrt (τ/(2*Real.pi)) * ((((B - A + 1 : ℕ)) : ℝ) / (B:ℝ)))
          * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖)
        ≤ (9*Real.sqrt (τ/(N:ℝ))) * (12*(1+K)*Real.sqrt ((N:ℝ)/τ)) :=
          mul_le_mul hbr1 hWb hWnn (by positivity)
      _ = 12*(1+K)*9*(Real.sqrt (τ/(N:ℝ)) * Real.sqrt ((N:ℝ)/τ)) := by ring
      _ = 12*(1+K)*9*1 := by rw [hsqrtτN]
      _ = 108*(1+K) := by ring
      _ ≤ 200*(1+K) := by nlinarith [hK]
  have hp2 : (Real.sqrt (2*Real.pi) * (B:ℝ) / Real.sqrt τ)
      * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖) ≤ 12*(1+K) := by
    have hD : (0:ℝ) < N := hNpos
    have hN' : Real.sqrt (N:ℝ)/(N:ℝ) = 1/Real.sqrt (N:ℝ) := by
      rw [div_eq_div_iff (ne_of_gt hD) (ne_of_gt hsqrtNpos)]
      rw [← sq, Real.sq_sqrt hD.le]
      ring
    calc (Real.sqrt (2*Real.pi) * (B:ℝ) / Real.sqrt τ)
          * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖)
        ≤ (Real.sqrt τ/(N:ℝ)) * (12*(1+K)*Real.sqrt ((N:ℝ)/τ)) :=
          mul_le_mul hbr2 hWb hWnn (by positivity)
      _ = 12*(1+K)*(Real.sqrt τ * Real.sqrt ((N:ℝ)/τ))/(N:ℝ) := by ring
      _ = 12*(1+K)*(Real.sqrt (N:ℝ))/(N:ℝ) := by
          rw [← Real.sqrt_mul hτ.le]
          rw [show τ * ((N:ℝ)/τ) = (N:ℝ) by field_simp]
      _ = 12*(1+K)*(Real.sqrt (N:ℝ)/(N:ℝ)) := by ring
      _ = 12*(1+K)*(1/Real.sqrt (N:ℝ)) := by rw [hN']
      _ ≤ 12*(1+K)*1 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [div_le_one hsqrtNpos]
          exact Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ N))
      _ = 12*(1+K) := by ring
  have hbrsum : (Real.sqrt (τ/(2*Real.pi)) * ((((B - A + 1 : ℕ)) : ℝ) / (B:ℝ))
        + Real.sqrt (2*Real.pi) * (B:ℝ) / Real.sqrt τ + 1)
      * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖)
      = (Real.sqrt (τ/(2*Real.pi)) * ((((B - A + 1 : ℕ)) : ℝ) / (B:ℝ)))
          * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖)
        + (Real.sqrt (2*Real.pi) * (B:ℝ) / Real.sqrt τ)
          * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖)
        + 1 * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖) := by ring
  have hWle : (1:ℝ) * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖) ≤ 12*(1+K) := by
    rw [one_mul]
    refine le_trans hWb ?_
    have h0 : (0:ℝ) ≤ 12*(1+K) := by linarith
    have hL : Real.sqrt ((N:ℝ)/τ) ≤ 1 := by
      rw [Real.sqrt_le_one, div_le_one hτpos]; exact hNτ
    nlinarith [hL, h0]
  have hsum36 : (Real.sqrt (τ/(2*Real.pi)) * ((((B - A + 1 : ℕ)) : ℝ) / (B:ℝ))
        + Real.sqrt (2*Real.pi) * (B:ℝ) / Real.sqrt τ + 1)
      * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖) ≤ 300*(1+K) := by
    rw [hbrsum]
    linarith [hp1, hp2, hWle]
  calc ‖∑ m ∈ Finset.Icc A B, w m * Complex.exp (-(Complex.I * ((τ : ℂ) * ((Real.log (m:ℝ) : ℝ) : ℂ))))‖
      ≤ Cw * (Real.sqrt (τ/(2*Real.pi)) * ((((B - A + 1 : ℕ)) : ℝ) / (B:ℝ))
          + Real.sqrt (2*Real.pi) * (B:ℝ) / Real.sqrt τ + 1)
          * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖) := htool
    _ = Cw * ((Real.sqrt (τ/(2*Real.pi)) * ((((B - A + 1 : ℕ)) : ℝ) / (B:ℝ))
        + Real.sqrt (2*Real.pi) * (B:ℝ) / Real.sqrt τ + 1)
        * (‖w B‖ + ∑ m ∈ Finset.Icc A (B - 1), ‖w m - w (m+1)‖)) := by ring
    _ ≤ Cw * (300*(1+K)) := mul_le_mul_of_nonneg_left hsum36 (le_of_lt hCwpos)
    _ ≤ Cw * 2000 * (1+K) := by
        have h2 : (0:ℝ) < Cw := hCwpos
        have h3 : (0:ℝ) < 1+K := by linarith
        nlinarith [mul_pos h2 h3, h2, h3]

/-- Finset identity: `Icc a b \ Icc c d = Icc a (c-1) ∪ Icc (d+1) b`. -/
lemma Icc_sdiff_Icc {a b c d : ℕ} (ha : 1 ≤ a) (hac : a ≤ c) (hcd : c ≤ d + 1) (hdb : d ≤ b) :
    Finset.Icc a b \ Finset.Icc c d = Finset.Icc a (c - 1) ∪ Finset.Icc (d + 1) b := by
  apply Finset.Subset.antisymm
  · intro m hm
    rw [Finset.mem_sdiff, Finset.mem_Icc] at hm
    obtain ⟨⟨hm1, hm2⟩, hm3⟩ := hm
    have hm3' : ¬ (c ≤ m ∧ m ≤ d) := fun hc => hm3 (by simpa [Finset.mem_Icc] using hc)
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
    by_cases h : m < c
    · exact Or.inl ⟨hm1, by omega⟩
    · exact Or.inr ⟨by omega, hm2⟩
  · intro m hm
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc] at hm
    rw [Finset.mem_sdiff]
    constructor
    · rw [Finset.mem_Icc]
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, by omega⟩
      · exact ⟨by omega, h2⟩
    · intro hc
      rw [Finset.mem_Icc] at hc
      rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- The residual sum of the main terms over `band \ D` is `O(1+K)`. -/
lemma residual_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 1 χ)
      (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
      (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
      {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hNτ : (N:ℝ) ≤ τ)
      (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N),
      ‖∑ m ∈ (Finset.Icc (WwLo N τ) (WwHi N τ)) \ (Finset.Icc (WwDLo N τ) (WwDHi N τ)),
          WwMainTerm χ τ m‖ ≤ C * (1+K) := by
  obtain ⟨Cs, hCsp, hs⟩ := WwMainTerm_sum_bound_small
  obtain ⟨Cb, hCbp, hb⟩ := WwMainTerm_sum_bound_big
  refine ⟨2*Cs + 2*Cb + 2, by positivity, ?_⟩
  intro N hN χ hχd hχ0 hχz K τ hK hτ hNτ hbdd
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hsqrtNpos : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hN32pos : (0:ℝ) < (N:ℝ) * Real.sqrt N := by positivity
  have hsqrt2 : (2:ℝ) ≤ Real.sqrt N := by
    have h := Real.sqrt_le_sqrt (by exact_mod_cast hN : (4:ℝ) ≤ N)
    rwa [show Real.sqrt (4:ℝ) = 2 by norm_num] at h
  have hτpos : (0:ℝ) < τ := hτ
  obtain ⟨hLoALo, hALoDLo, hDLoDHi, hDHiHi, hBHiHi⟩ := Ww_lo_hi_facts hN hτ
  have hLo1 : 1 ≤ WwLo N τ := Nat.ceil_pos.mpr (by positivity)
  have hALo1 : 1 ≤ WwALo N τ := Nat.ceil_pos.mpr (by positivity)
  have hDLo1 : 1 ≤ WwDLo N τ := Nat.ceil_pos.mpr (by positivity)
  have hsplit : (Finset.Icc (WwLo N τ) (WwHi N τ)) \ (Finset.Icc (WwDLo N τ) (WwDHi N τ))
      = (Finset.Icc (WwLo N τ) (WwDLo N τ - 1))
        ∪ (Finset.Icc (WwDHi N τ + 1) (WwHi N τ)) :=
    Icc_sdiff_Icc hLo1 (le_trans hLoALo hALoDLo) hDLoDHi (by omega)
  have hdisj : Disjoint (Finset.Icc (WwLo N τ) (WwDLo N τ - 1))
      (Finset.Icc (WwDHi N τ + 1) (WwHi N τ)) := by
    rw [Finset.disjoint_left]
    intro m hm1 hm2
    rw [Finset.mem_Icc] at hm1 hm2
    omega
  have hvanL : ∑ m ∈ Finset.Icc (WwALo N τ) (WwDLo N τ - 1), WwMainTerm χ τ m
      = ∑ m ∈ Finset.Icc (WwLo N τ) (WwDLo N τ - 1), WwMainTerm χ τ m := by
    apply Finset.sum_subset
    · intro m hm
      have hm' := Finset.mem_Icc.mp hm
      exact Finset.mem_Icc.mpr ⟨le_trans hLoALo hm'.1, hm'.2⟩
    · intro m hm hmn
      have hm' := Finset.mem_Icc.mp hm
      have hlt : m < WwALo N τ := by
        by_contra hc
        exact hmn (Finset.mem_Icc.mpr ⟨not_lt.mp hc, hm'.2⟩)
      exact WwMainTerm_eq_zero_of_lt (by omega : 1 ≤ N) hχz hτ (by omega) hlt
  have hvanR : ∑ m ∈ Finset.Icc (WwDHi N τ + 1) (WwBHi N τ), WwMainTerm χ τ m
      = ∑ m ∈ Finset.Icc (WwDHi N τ + 1) (WwHi N τ), WwMainTerm χ τ m := by
    apply Finset.sum_subset
    · intro m hm
      have hm' := Finset.mem_Icc.mp hm
      exact Finset.mem_Icc.mpr ⟨hm'.1, le_trans hm'.2 hBHiHi⟩
    · intro m hm hmn
      have hm' := Finset.mem_Icc.mp hm
      have hlt : WwBHi N τ < m := by
        by_contra hc
        exact hmn (Finset.mem_Icc.mpr ⟨hm'.1, not_lt.mp hc⟩)
      exact WwMainTerm_eq_zero_of_gt hN2 hχz hτ hlt
  have hdecomp : ∑ m ∈ (Finset.Icc (WwLo N τ) (WwHi N τ)) \ (Finset.Icc (WwDLo N τ) (WwDHi N τ)),
        WwMainTerm χ τ m
      = (∑ m ∈ Finset.Icc (WwALo N τ) (WwDLo N τ - 1), WwMainTerm χ τ m)
        + ∑ m ∈ Finset.Icc (WwDHi N τ + 1) (WwBHi N τ), WwMainTerm χ τ m := by
    rw [hsplit, Finset.sum_union hdisj, ← hvanL, ← hvanR]
  rw [hdecomp]
  refine le_trans (norm_add_le _ _) ?_
  -- the two length bounds
  have hlenL0 : (((WwDLo N τ - WwALo N τ : ℕ)) : ℝ)
      ≤ τ/(8*Real.pi*((N:ℝ)*Real.sqrt N)) + 2 := by
    have h1 : ((WwDLo N τ : ℕ) : ℝ) < τ/(4*Real.pi*(N:ℝ)) + 1 := by
      rw [WwDLo]; exact Nat.ceil_lt_add_one (by positivity)
    have h2 : τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) ≤ ((WwALo N τ : ℕ) : ℝ) := by
      rw [WwALo]; exact Nat.le_ceil _
    have h3 : τ/(4*Real.pi*(N:ℝ)) - τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N))
        ≤ τ/(8*Real.pi*((N:ℝ)*Real.sqrt N)) := by
      have hb : 4*Real.pi*(N:ℝ) ≠ 0 := by positivity
      have hd : 2*Real.pi*(2*(N:ℝ) + Real.sqrt N) ≠ 0 := by positivity
      rw [div_sub_div (τ : ℝ) (τ : ℝ) hb hd]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : 2*Real.sqrt N ≤ (N:ℝ) := by
        have h := mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg N)
        nlinarith [h, Real.sq_sqrt hNpos.le]
      have h4' : (0:ℝ) ≤ 2*Real.pi^2*τ*(N:ℝ) := by positivity
      have h5 := mul_le_mul_of_nonneg_right h4 h4'
      nlinarith [h5, Real.sq_sqrt hNpos.le, Real.sq_sqrt Real.pi_pos.le, Real.pi_pos, hτpos]
    rw [Nat.cast_sub hALoDLo]
    linarith [h1, h2, h3]
  have hlenR0 : (((WwBHi N τ - WwDHi N τ : ℕ)) : ℝ)
      ≤ τ/(Real.pi*((N:ℝ)*Real.sqrt N)) + 2 := by
    by_cases hle : WwDHi N τ ≤ WwBHi N τ
    · have hDen : (0:ℝ) < (N:ℝ) - Real.sqrt N := by
        nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg N, hN1]
      have h1 : ((WwBHi N τ : ℕ) : ℝ) ≤ τ/(2*Real.pi*((N:ℝ) - Real.sqrt N)) := by
        show ((Nat.floor (τ/(2*Real.pi*((N:ℝ) - Real.sqrt N))) : ℕ) : ℝ)
          ≤ τ/(2*Real.pi*((N:ℝ) - Real.sqrt N))
        apply Nat.floor_le
        exact div_nonneg hτ.le (by positivity)
      have h2 : τ/(2*Real.pi*(N:ℝ)) < ((WwDHi N τ : ℕ) : ℝ) + 1 := by
        show τ/(2*Real.pi*(N:ℝ)) < ((Nat.floor (τ/(2*Real.pi*(N:ℝ))) : ℕ) : ℝ) + 1
        exact Nat.lt_floor_add_one _
      have h3 : τ/(2*Real.pi*((N:ℝ) - Real.sqrt N)) - τ/(2*Real.pi*(N:ℝ))
          ≤ τ/(Real.pi*((N:ℝ)*Real.sqrt N)) := by
        have hb : 2*Real.pi*((N:ℝ) - Real.sqrt N) ≠ 0 := by positivity
        have hd : 2*Real.pi*(N:ℝ) ≠ 0 := by positivity
        rw [div_sub_div (τ : ℝ) (τ : ℝ) hb hd]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h4 : 2*Real.sqrt N ≤ (N:ℝ) := by
          have h := mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg N)
          nlinarith [h, Real.sq_sqrt hNpos.le]
        have h4' : (0:ℝ) ≤ 2*Real.pi^2*τ*(N:ℝ) := by positivity
        have h5 := mul_le_mul_of_nonneg_right h4 h4'
        nlinarith [h5, Real.sq_sqrt hNpos.le, Real.sq_sqrt Real.pi_pos.le, Real.pi_pos, hτpos]
      rw [Nat.cast_sub hle]
      linarith [h1, h2, h3]
    · have h0 : WwBHi N τ - WwDHi N τ = 0 := by omega
      rw [h0]
      push_cast
      have hpos : (0:ℝ) ≤ τ/(Real.pi*((N:ℝ)*Real.sqrt N)) + 2 := by positivity
      linarith
  -- the `A ≥ τ/(8πN)` bounds
  have hAlL : τ/(8*Real.pi*(N:ℝ)) ≤ ((WwALo N τ : ℕ) : ℝ) := by
    have h2 : τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) ≤ ((WwALo N τ : ℕ) : ℝ) := by
      rw [WwALo]; exact Nat.le_ceil _
    have h3 : τ/(8*Real.pi*(N:ℝ)) ≤ τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) := by
      apply div_le_div_of_nonneg_left hτ.le (by positivity)
      have h4 : 2*Real.sqrt N ≤ 2*(N:ℝ) := by
        have h := mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg N)
        nlinarith [h, Real.sq_sqrt hNpos.le]
      have h5 : 2*(2*(N:ℝ) + Real.sqrt N) ≤ 8*(N:ℝ) := by linarith
      nlinarith [h5, Real.pi_pos]
    linarith [h2, h3]
  have hAlR : τ/(8*Real.pi*(N:ℝ)) ≤ (((WwDHi N τ + 1 : ℕ)) : ℝ) := by
    have h2 : τ/(2*Real.pi*(N:ℝ)) < ((WwDHi N τ : ℕ) : ℝ) + 1 := by
      show τ/(2*Real.pi*(N:ℝ)) < ((Nat.floor (τ/(2*Real.pi*(N:ℝ))) : ℕ) : ℝ) + 1
      exact Nat.lt_floor_add_one _
    have h3 : τ/(8*Real.pi*(N:ℝ)) ≤ τ/(2*Real.pi*(N:ℝ)) :=
      div_le_div_of_nonneg_left hτ.le (by positivity) (by nlinarith [Real.pi_pos, hNpos])
    push_cast
    linarith [h2, h3]
  have hBleL : (((WwDLo N τ - 1 : ℕ)) : ℝ) ≤ τ/(Real.pi*(N:ℝ)) := by
    have h6 : ((WwDLo N τ : ℕ) : ℝ) < τ/(4*Real.pi*(N:ℝ)) + 1 := by
      rw [WwDLo]; exact Nat.ceil_lt_add_one (by positivity)
    have h7 : τ/(4*Real.pi*(N:ℝ)) ≤ τ/(Real.pi*(N:ℝ)) :=
      div_le_div_of_nonneg_left hτ.le (by positivity) (by nlinarith [Real.pi_pos, hNpos])
    rw [Nat.cast_sub hDLo1]
    linarith [h6, h7]
  have hBleR : ((WwBHi N τ : ℕ) : ℝ) ≤ τ/(Real.pi*(N:ℝ)) := by
    have hDen : (0:ℝ) ≤ (N:ℝ) - Real.sqrt N := by
      nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg N, hN1]
    have h1 : ((WwBHi N τ : ℕ) : ℝ) ≤ τ/(2*Real.pi*((N:ℝ) - Real.sqrt N)) := by
      show ((Nat.floor (τ/(2*Real.pi*((N:ℝ) - Real.sqrt N))) : ℕ) : ℝ)
        ≤ τ/(2*Real.pi*((N:ℝ) - Real.sqrt N))
      apply Nat.floor_le
      exact div_nonneg hτ.le (by positivity)
    have h2 : τ/(2*Real.pi*((N:ℝ) - Real.sqrt N)) ≤ τ/(Real.pi*(N:ℝ)) := by
      apply div_le_div_of_nonneg_left hτ.le (by positivity)
      have h3 : 2*Real.sqrt N ≤ (N:ℝ) := by
        have h := mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg N)
        nlinarith [h, Real.sq_sqrt hNpos.le]
      nlinarith [Real.pi_pos, hNpos, h3]
    linarith [h1, h2]
  by_cases hbig : 100*((N:ℝ)*Real.sqrt N) < τ
  · -- large `τ` : apply the stationary-phase estimate to both ranges
    have hsqrtNle : Real.sqrt N ≤ (N:ℝ) := by
      nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg N, hN1]
    have hA2L : 2 ≤ WwALo N τ := by
      have h2 : (2:ℝ) ≤ τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) := by
        rw [le_div_iff₀ (by positivity)]
        have hkey : 4*Real.pi*(2*(N:ℝ) + Real.sqrt N) ≤ 100*((N:ℝ)*Real.sqrt N) := by
          nlinarith [Real.pi_lt_four, hNpos, hsqrt2, hsqrtNle, Real.sqrt_nonneg N]
        linarith [hkey, hbig]
      have h3 := Nat.le_ceil (τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N)))
      rw [WwALo]
      exact_mod_cast le_trans h2 h3
    have hA2R : 2 ≤ WwDHi N τ + 1 := by
      have h2 : τ/(2*Real.pi*(N:ℝ)) < ((WwDHi N τ : ℕ) : ℝ) + 1 := by
        show τ/(2*Real.pi*(N:ℝ)) < ((Nat.floor (τ/(2*Real.pi*(N:ℝ))) : ℕ) : ℝ) + 1
        exact Nat.lt_floor_add_one _
      have h3 : (1:ℝ) ≤ τ/(2*Real.pi*(N:ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have hkey : 2*Real.pi*(N:ℝ) ≤ 100*((N:ℝ)*Real.sqrt N) := by
          nlinarith [Real.pi_lt_four, hNpos, hsqrt2]
        linarith [hkey, hbig]
      push_cast
      linarith [h2, h3]
    have hDLo2 : 2 ≤ WwDLo N τ := by
      have h2 : (2:ℝ) ≤ τ/(4*Real.pi*(N:ℝ)) := by
        rw [le_div_iff₀ (by positivity)]
        have hkey : 8*Real.pi*(N:ℝ) ≤ 100*((N:ℝ)*Real.sqrt N) := by
          nlinarith [Real.pi_lt_four, hNpos, hsqrt2]
        linarith [hkey, hbig]
      have h3 := Nat.le_ceil (τ/(4*Real.pi*(N:ℝ)))
      rw [WwDLo]
      exact_mod_cast le_trans h2 h3
    have hBHi1 : 1 ≤ WwBHi N τ := by
      have hDen : (0:ℝ) < 2*Real.pi*((N:ℝ) - Real.sqrt N) := by
        have hD : (0:ℝ) < (N:ℝ) - Real.sqrt N := by
          nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg N, hN1]
        positivity
      have h2 : (1:ℝ) ≤ τ/(2*Real.pi*((N:ℝ) - Real.sqrt N)) := by
        rw [le_div_iff₀ hDen]
        have hkey : 2*Real.pi*((N:ℝ) - Real.sqrt N) ≤ 100*((N:ℝ)*Real.sqrt N) := by
          nlinarith [Real.pi_lt_four, hNpos, hsqrt2, hsqrtNle, Real.sqrt_nonneg N]
        linarith [hkey, hbig]
      rw [WwBHi]
      exact Nat.le_floor (by simpa using h2)
    have hDHIlt : τ/(2*Real.pi*(N:ℝ)) < ((WwDHi N τ : ℕ) : ℝ) + 1 := by
      show τ/(2*Real.pi*(N:ℝ)) < ((Nat.floor (τ/(2*Real.pi*(N:ℝ))) : ℕ) : ℝ) + 1
      exact Nat.lt_floor_add_one _
    have hBHIle : ((WwBHi N τ : ℕ) : ℝ) ≤ τ/(2*Real.pi*((N:ℝ) - Real.sqrt N)) := by
      show ((Nat.floor (τ/(2*Real.pi*((N:ℝ) - Real.sqrt N))) : ℕ) : ℝ)
        ≤ τ/(2*Real.pi*((N:ℝ) - Real.sqrt N))
      apply Nat.floor_le
      apply div_nonneg hτ.le
      have hD : (0:ℝ) ≤ (N:ℝ) - Real.sqrt N := by
        nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg N, hN1]
      positivity
    have hDLo1' : ((WwDLo N τ - 1 : ℕ) : ℝ) ≤ τ/(4*Real.pi*(N:ℝ)) := by
      have h6 : ((WwDLo N τ : ℕ) : ℝ) < τ/(4*Real.pi*(N:ℝ)) + 1 := by
        show ((Nat.ceil (τ/(4*Real.pi*(N:ℝ))) : ℕ) : ℝ) < τ/(4*Real.pi*(N:ℝ)) + 1
        exact Nat.ceil_lt_add_one (by positivity)
      rw [Nat.cast_sub hDLo1]
      linarith
    have hspreadL : τ/(2*Real.pi*((WwALo N τ : ℕ):ℝ)) - τ/(2*Real.pi*((WwDLo N τ - 1 : ℕ):ℝ))
        ≤ Real.sqrt N := by
      have h1 : τ/(2*Real.pi*((WwALo N τ : ℕ):ℝ)) ≤ 2*(N:ℝ) + Real.sqrt N := by
        have hA : (0:ℝ) < 2*Real.pi*((WwALo N τ : ℕ):ℝ) := by
          have h0 : (0:ℝ) < ((WwALo N τ : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 0 < WwALo N τ)
          positivity
        have hD : (0:ℝ) < 2*Real.pi*(2*(N:ℝ) + Real.sqrt N) := by positivity
        have h2 : τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) ≤ ((WwALo N τ : ℕ) : ℝ) := by
          rw [WwALo]; exact Nat.le_ceil _
        have h3 : τ ≤ ((WwALo N τ : ℕ) : ℝ) * (2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) :=
          (div_le_iff₀ hD).mp h2
        rw [div_le_iff₀ hA]
        calc τ ≤ ((WwALo N τ : ℕ) : ℝ) * (2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) := h3
          _ = (2*(N:ℝ) + Real.sqrt N) * (2*Real.pi*((WwALo N τ : ℕ):ℝ)) := by ring
      have h5 : 2*(N:ℝ) ≤ τ/(2*Real.pi*((WwDLo N τ - 1 : ℕ):ℝ)) := by
        have hD : (0:ℝ) < 2*Real.pi*((WwDLo N τ - 1 : ℕ):ℝ) := by
          have h0 : (0:ℝ) < ((WwDLo N τ - 1 : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 0 < WwDLo N τ - 1)
          positivity
        rw [le_div_iff₀ hD]
        have hm := mul_le_mul_of_nonneg_right hDLo1' (by positivity : (0:ℝ) ≤ 4*Real.pi*(N:ℝ))
        have he : (τ/(4*Real.pi*(N:ℝ))) * (4*Real.pi*(N:ℝ)) = τ :=
          div_mul_cancel₀ τ (by positivity)
        rw [he] at hm
        nlinarith [hm]
      linarith [h1, h5]
    have hspreadR : τ/(2*Real.pi*(((WwDHi N τ + 1 : ℕ)):ℝ)) - τ/(2*Real.pi*((WwBHi N τ : ℕ):ℝ))
        ≤ Real.sqrt N := by
      have h1 : τ/(2*Real.pi*(((WwDHi N τ + 1 : ℕ)):ℝ)) ≤ (N:ℝ) := by
        have hA : (0:ℝ) < 2*Real.pi*(((WwDHi N τ + 1 : ℕ)):ℝ) := by
          have h0 : (0:ℝ) < (((WwDHi N τ + 1 : ℕ)) : ℝ) := by
            exact_mod_cast (by omega : 0 < WwDHi N τ + 1)
          positivity
        have h3 : τ < (((WwDHi N τ + 1 : ℕ)) : ℝ) * (2*Real.pi*(N:ℝ)) := by
          have hm := mul_lt_mul_of_pos_right hDHIlt (by positivity : (0:ℝ) < 2*Real.pi*(N:ℝ))
          have he : (τ/(2*Real.pi*(N:ℝ))) * (2*Real.pi*(N:ℝ)) = τ := div_mul_cancel₀ τ (by positivity)
          rw [he] at hm
          have hpc : (((WwDHi N τ + 1 : ℕ)) : ℝ) = ((WwDHi N τ : ℕ) : ℝ) + 1 := by push_cast; ring
          rw [hpc]
          exact hm
        rw [div_le_iff₀ hA]
        calc τ ≤ (((WwDHi N τ + 1 : ℕ)) : ℝ) * (2*Real.pi*(N:ℝ)) := le_of_lt h3
          _ = (N:ℝ) * (2*Real.pi*(((WwDHi N τ + 1 : ℕ)):ℝ)) := by ring
      have h5 : (N:ℝ) - Real.sqrt N ≤ τ/(2*Real.pi*((WwBHi N τ : ℕ):ℝ)) := by
        have hD : (0:ℝ) < 2*Real.pi*((WwBHi N τ : ℕ):ℝ) := by
          have h0 : (0:ℝ) < ((WwBHi N τ : ℕ) : ℝ) := by
            exact_mod_cast (by omega : 0 < WwBHi N τ)
          positivity
        rw [le_div_iff₀ hD]
        have hm := mul_le_mul_of_nonneg_right hBHIle
          (by positivity : (0:ℝ) ≤ 2*Real.pi*((N:ℝ) - Real.sqrt N))
        have hNnz : (2*Real.pi*((N:ℝ) - Real.sqrt N)) ≠ 0 :=
          mul_ne_zero (by positivity : (2*Real.pi : ℝ) ≠ 0)
            (ne_of_gt (by nlinarith [Real.sq_sqrt hNpos.le, Real.sqrt_nonneg N, hN1] :
              (0:ℝ) < (N:ℝ) - Real.sqrt N))
        have he : (τ/(2*Real.pi*((N:ℝ) - Real.sqrt N))) * (2*Real.pi*((N:ℝ) - Real.sqrt N)) = τ :=
          div_mul_cancel₀ τ hNnz
        rw [he] at hm
        calc τ ≥ ((WwBHi N τ : ℕ) : ℝ) * (2*Real.pi*((N:ℝ) - Real.sqrt N)) := hm
          _ = ((N:ℝ) - Real.sqrt N) * (2*Real.pi*((WwBHi N τ : ℕ):ℝ)) := by ring
      linarith [h1, h5]
    have h2AL : WwDLo N τ - 1 ≤ 2 * WwALo N τ := by
      have h2 : τ/(4*Real.pi*(N:ℝ)) ≤ ((2 * WwALo N τ : ℕ) : ℝ) := by
        have h3 : τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N)) ≤ ((WwALo N τ : ℕ) : ℝ) := by
          rw [WwALo]; exact Nat.le_ceil _
        have h4 : τ/(4*Real.pi*(N:ℝ)) ≤ τ/(Real.pi*(2*(N:ℝ) + Real.sqrt N)) := by
          apply div_le_div_of_nonneg_left hτ.le (by positivity)
          nlinarith [Real.pi_pos, hNpos, hsqrtNpos, Real.sq_sqrt hNpos.le, hsqrt2]
        have h5 : τ/(Real.pi*(2*(N:ℝ) + Real.sqrt N))
            = 2*(τ/(2*Real.pi*(2*(N:ℝ) + Real.sqrt N))) := by
          field_simp
          try ring
        push_cast
        linarith [h3, h4, h5]
      have h6 : ((WwDLo N τ - 1 : ℕ) : ℝ) ≤ ((2 * WwALo N τ : ℕ) : ℝ) := by
        linarith [hDLo1', h2]
      exact_mod_cast h6
    have h2AR : WwBHi N τ ≤ 2 * (WwDHi N τ + 1) := by
      have h3 : τ/(2*Real.pi*((N:ℝ) - Real.sqrt N)) ≤ 2*(τ/(2*Real.pi*(N:ℝ))) := by
        rw [show 2*(τ/(2*Real.pi*(N:ℝ))) = τ/(Real.pi*(N:ℝ)) by ring]
        apply div_le_div_of_nonneg_left hτ.le (by positivity)
        have h4 : 2*Real.sqrt N ≤ (N:ℝ) := by
          have h := mul_le_mul_of_nonneg_right hsqrt2 (Real.sqrt_nonneg N)
          nlinarith [h, Real.sq_sqrt hNpos.le]
        nlinarith [Real.pi_pos, h4, hNpos]
      have h5 : 2*(τ/(2*Real.pi*(N:ℝ))) ≤ 2*(((WwDHi N τ + 1 : ℕ)) : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left (le_of_lt hDHIlt) (by norm_num : (0:ℝ) ≤ 2)
        push_cast at hm ⊢
        linarith
      have h4 : ((WwBHi N τ : ℕ) : ℝ) ≤ 2 * (((WwDHi N τ + 1 : ℕ)) : ℝ) := by
        linarith [hBHIle, h3, h5]
      exact_mod_cast h4
    have hbL : ‖∑ m ∈ Finset.Icc (WwALo N τ) (WwDLo N τ - 1), WwMainTerm χ τ m‖
        ≤ Cb * (1+K) := by
      by_cases hAB : WwALo N τ ≤ WwDLo N τ - 1
      · have hlen : ((((WwDLo N τ - 1) - WwALo N τ + 1 : ℕ)) : ℝ)
            ≤ τ/(Real.pi*((N:ℝ)*Real.sqrt N)) + 2 := by
          have he : ((WwDLo N τ - 1) - WwALo N τ + 1 : ℕ) = (WwDLo N τ - WwALo N τ : ℕ) := by omega
          rw [he]
          linarith [hlenL0, show τ/(8*Real.pi*((N:ℝ)*Real.sqrt N))
            ≤ τ/(Real.pi*((N:ℝ)*Real.sqrt N)) by
              apply div_le_div_of_nonneg_left hτ.le (by positivity)
              nlinarith [Real.pi_pos, hN32pos]]
        exact hb hN hχd hχ0 hK hτ hNτ hbdd hA2L hAB h2AL hAlL hspreadL hlen hBleL hbig
      · rw [Finset.Icc_eq_empty_iff.mpr hAB]
        simp only [Finset.sum_empty, norm_zero]
        exact mul_nonneg hCbp.le (by linarith)
    have hbR : ‖∑ m ∈ Finset.Icc (WwDHi N τ + 1) (WwBHi N τ), WwMainTerm χ τ m‖
        ≤ Cb * (1+K) := by
      by_cases hAB : WwDHi N τ + 1 ≤ WwBHi N τ
      · have hlen : ((((WwBHi N τ) - (WwDHi N τ + 1) + 1 : ℕ)) : ℝ)
            ≤ τ/(Real.pi*((N:ℝ)*Real.sqrt N)) + 2 := by
          have he : (WwBHi N τ - (WwDHi N τ + 1) + 1 : ℕ) = (WwBHi N τ - WwDHi N τ : ℕ) := by omega
          rw [he]
          exact hlenR0
        exact hb hN hχd hχ0 hK hτ hNτ hbdd hA2R hAB h2AR hAlR hspreadR hlen hBleR hbig
      · rw [Finset.Icc_eq_empty_iff.mpr hAB]
        simp only [Finset.sum_empty, norm_zero]
        exact mul_nonneg hCbp.le (by linarith)
    have hfin : (2*Cs + 2*Cb + 2) * (1+K) = 2*(Cb*(1+K)) + (2*Cs*(1+K) + 2*(1+K)) := by ring
    have hnn : (0:ℝ) ≤ 2*Cs*(1+K) + 2*(1+K) := by
      have h2 : (0:ℝ) < 1+K := by linarith
      have h1 : (0:ℝ) ≤ 2*Cs*(1+K) :=
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hCsp)) h2.le
      have h3 : (0:ℝ) ≤ 2*(1+K) := mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h2.le
      linarith
    linarith [hbL, hbR, hfin, hnn]
  · -- small `τ` : the residual is short
    have hsmall : τ ≤ 100*((N:ℝ)*Real.sqrt N) := not_lt.mp hbig
    have hsL : ‖∑ m ∈ Finset.Icc (WwALo N τ) (WwDLo N τ - 1), WwMainTerm χ τ m‖
        ≤ Cs * (1+K) := by
      by_cases hAB : WwALo N τ ≤ WwDLo N τ - 1
      · have hlen : ((((WwDLo N τ - 1) - WwALo N τ + 1 : ℕ)) : ℝ)
            ≤ τ/(Real.pi*((N:ℝ)*Real.sqrt N)) + 2 := by
          have he : ((WwDLo N τ - 1) - WwALo N τ + 1 : ℕ) = (WwDLo N τ - WwALo N τ : ℕ) := by omega
          rw [he]
          linarith [hlenL0, show τ/(8*Real.pi*((N:ℝ)*Real.sqrt N))
            ≤ τ/(Real.pi*((N:ℝ)*Real.sqrt N)) by
              apply div_le_div_of_nonneg_left hτ.le (by positivity)
              nlinarith [Real.pi_pos, hN32pos]]
        exact hs hN hχ0 hK hτ hALo1 hAB hlen hsmall
      · rw [Finset.Icc_eq_empty_iff.mpr hAB]
        simp only [Finset.sum_empty, norm_zero]
        exact mul_nonneg hCsp.le (by linarith)
    have hsR : ‖∑ m ∈ Finset.Icc (WwDHi N τ + 1) (WwBHi N τ), WwMainTerm χ τ m‖
        ≤ Cs * (1+K) := by
      by_cases hAB : WwDHi N τ + 1 ≤ WwBHi N τ
      · have hlen : ((((WwBHi N τ) - (WwDHi N τ + 1) + 1 : ℕ)) : ℝ)
            ≤ τ/(Real.pi*((N:ℝ)*Real.sqrt N)) + 2 := by
          have he : (WwBHi N τ - (WwDHi N τ + 1) + 1 : ℕ) = (WwBHi N τ - WwDHi N τ : ℕ) := by omega
          rw [he]
          exact hlenR0
        exact hs hN hχ0 hK hτ (by omega : 1 ≤ WwDHi N τ + 1) hAB hlen hsmall
      · rw [Finset.Icc_eq_empty_iff.mpr hAB]
        simp only [Finset.sum_empty, norm_zero]
        exact mul_nonneg hCsp.le (by linarith)
    have hfin : (2*Cs + 2*Cb + 2) * (1+K) = 2*(Cs*(1+K)) + (2*Cb*(1+K) + 2*(1+K)) := by ring
    have hnn : (0:ℝ) ≤ 2*Cb*(1+K) + 2*(1+K) := by
      have h2 : (0:ℝ) < 1+K := by linarith
      have h1 : (0:ℝ) ≤ 2*Cb*(1+K) :=
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (le_of_lt hCbp)) h2.le
      have h3 : (0:ℝ) ≤ 2*(1+K) := mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h2.le
      linarith
    linarith [hsL, hsR, hfin, hnn]

/-- The band of integers `[⌈τ/6πN⌉, ⌊2τ/πN⌋]`. -/
noncomputable def WwBandZ (N : ℕ) (τ : ℝ) : Finset ℤ :=
  Finset.Icc ((WwLo N τ : ℕ) : ℤ) ((WwHi N τ : ℕ) : ℤ)

lemma summable_WwI {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hNτ : (N:ℝ) ≤ τ)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / (N:ℝ)) :
    Summable (fun m : ℤ => WwI χ τ m) := by
  refine Summable.of_norm_bounded_eventually
    (g := fun m : ℤ => WwMaj (N:=N) K τ m) (summable_WwMaj (by omega) hK hτ hNτ) ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Finset.finite_toSet (WwBandZ N τ)) ?_
  intro m hm
  simp only [Set.mem_setOf_eq] at hm
  by_contra hb
  have hb' : ¬ (((WwLo N τ : ℕ) : ℤ) ≤ m ∧ m ≤ ((WwHi N τ : ℕ) : ℤ)) := by
    intro hc
    exact hb (by rw [WwBandZ]; exact Finset.mem_Icc.mpr hc)
  have hb'' : m < ((WwLo N τ : ℕ) : ℤ) ∨ ((WwHi N τ : ℕ) : ℤ) < m := by
    rcases not_and_or.mp hb' with h | h
    · exact Or.inl (not_le.mp h)
    · exact Or.inr (not_le.mp h)
  rcases hb'' with h1 | h1
  · by_cases h0 : m ≤ 0
    · exact hm (WwI_le_WwMaj_neg hN hχd hχ0 hχz hK hτ hbdd hdd h0)
    · have hm1 : 1 ≤ m.toNat := by omega
      have hcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
      have hmid : m.toNat ≤ WwLo N τ - 1 := by omega
      have hres := WwI_le_WwMaj_mid hN hχd hχ0 hχz hK hτ hNτ hbdd hdd hm1 hmid
      rw [hcast] at hres
      exact hm hres
  · have hcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg (by omega)
    have hri : WwHi N τ + 1 ≤ m.toNat := by omega
    have hres := WwI_le_WwMaj_right hN hχd hχ0 hχz hK hτ hNτ hbdd hdd hri
    rw [hcast] at hres
    exact hm hres

lemma WwI_offband_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
      (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
      (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
      {K τ : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hNτ : (N:ℝ) ≤ τ)
      (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
      (hdd : ∀ y, |deriv (deriv χ) y| ≤ K / (N:ℝ)),
      ‖∑' (m : ↑((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ), WwI χ τ m‖
        ≤ C * (1+K) := by
  obtain ⟨Cm, hCmp, hm⟩ := tsum_WwMaj_le
  refine ⟨Cm, hCmp, ?_⟩
  intro N hN χ hχd hχ0 hχz K τ hK hτ hNτ hbdd hdd
  have hsMaj : Summable (fun m : ℤ => WwMaj (N:=N) K τ m) := summable_WwMaj (by omega) hK hτ hNτ
  have hsumI : Summable (fun m : ℤ => WwI χ τ m) := summable_WwI hN hχd hχ0 hχz hK hτ hNτ hbdd hdd
  have hsub1 : Summable (fun m : ↑((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ => ‖WwI χ τ (m:ℤ)‖) :=
    (Summable.norm hsumI).subtype _
  have hsub2 : Summable (fun m : ↑((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ =>
      WwMaj (N:=N) K τ (m:ℤ)) := hsMaj.subtype _
  have hstep1 : ∑' (m : ↑((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ), ‖WwI χ τ ↑m‖
      ≤ ∑' (m : ↑((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ), WwMaj (N:=N) K τ ↑m := by
    apply Summable.tsum_le_tsum _ hsub1 hsub2
    intro m
    by_contra hb
    have hmem : ¬ (((m:ℤ)) ∈ WwBandZ N τ) := by
      have h := m.2
      rwa [Set.mem_compl_iff] at h
    have hmem' : ¬ (((WwLo N τ : ℕ) : ℤ) ≤ (m:ℤ) ∧ (m:ℤ) ≤ ((WwHi N τ : ℕ) : ℤ)) := by
      intro hc
      exact hmem (Finset.mem_Icc.mpr hc : (m:ℤ) ∈ WwBandZ N τ)
    have hmem'' : (m:ℤ) < ((WwLo N τ : ℕ) : ℤ) ∨ ((WwHi N τ : ℕ) : ℤ) < (m:ℤ) := by
      rcases not_and_or.mp hmem' with h | h
      · exact Or.inl (not_le.mp h)
      · exact Or.inr (not_le.mp h)
    rcases hmem'' with h1 | h1
    · by_cases h0 : (m:ℤ) ≤ 0
      · exact hb (WwI_le_WwMaj_neg hN hχd hχ0 hχz hK hτ hbdd hdd h0)
      · have hm1 : 1 ≤ (m:ℤ).toNat := by omega
        have hcast : (((m:ℤ).toNat : ℕ) : ℤ) = (m:ℤ) := Int.toNat_of_nonneg (by omega)
        have hmid : (m:ℤ).toNat ≤ WwLo N τ - 1 := by omega
        have hres := WwI_le_WwMaj_mid hN hχd hχ0 hχz hK hτ hNτ hbdd hdd hm1 hmid
        rw [hcast] at hres
        exact hb hres
    · have hcast : (((m:ℤ).toNat : ℕ) : ℤ) = (m:ℤ) := Int.toNat_of_nonneg (by omega)
      have hri : WwHi N τ + 1 ≤ (m:ℤ).toNat := by omega
      have hres := WwI_le_WwMaj_right hN hχd hχ0 hχz hK hτ hNτ hbdd hdd hri
      rw [hcast] at hres
      exact hb hres
  have hstep2 : ∑' (m : ↑((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ), WwMaj (N:=N) K τ ↑m
      = ∑' m : ℤ, (((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ).indicator
          (fun m => WwMaj (N:=N) K τ m) m := by
    exact _root_.tsum_subtype (((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ)
      (fun m => WwMaj (N:=N) K τ m)
  have hstep3 : ∑' m : ℤ, (((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ).indicator
        (fun m => WwMaj (N:=N) K τ m) m ≤ ∑' m : ℤ, WwMaj (N:=N) K τ m := by
    apply Summable.tsum_le_tsum _ (hsMaj.indicator _) hsMaj
    intro m
    by_cases hmm : m ∈ (((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ)
    · rw [Set.indicator_of_mem hmm]
    · rw [Set.indicator_of_notMem hmm]
      exact WwMaj_nonneg (by omega) hK hτ m
  have htail := hm (by omega : 1 ≤ N) hK hτ hNτ
  calc ‖∑' (m : ↑((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ), WwI χ τ m‖
      ≤ ∑' (m : ↑((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ), ‖WwI χ τ m‖ :=
        norm_tsum_le_tsum_norm hsub1
    _ ≤ ∑' (m : ↑((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ), WwMaj (N:=N) K τ ↑m := hstep1
    _ = _ := hstep2
    _ ≤ ∑' m : ℤ, WwMaj (N:=N) K τ m := hstep3
    _ ≤ Cm * (1+K) := htail

/-! ## The band error and the main-term identity -/

lemma WwI_band_sum_bound {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K τ : ℝ} (hK : 0 ≤ K) (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hτ : 4 ≤ τ) (hNτ : (N:ℝ) ≤ τ) :
    ∃ C : ℝ, 0 < C ∧
      ‖∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
          (WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m)‖
        ≤ C * (1+K) * (1 + Real.log τ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hτpos : (0:ℝ) < τ := by linarith
  have hlog : (0:ℝ) ≤ 1 + Real.log τ := by
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ τ)
    linarith
  let Cm : ℕ → ℝ := fun m => if h : (1 ≤ m ∧ (N:ℝ)/4 ≤ τ/(2*Real.pi*(m:ℝ))
        ∧ τ/(2*Real.pi*(m:ℝ)) ≤ 3*(N:ℝ))
      then Classical.choose (WwI_band_bound (N:=N) (χ:=χ) (K:=K) (τ:=τ) hN hχd hχ0 hχz
        hK hbdd hτ h.1 h.2.1 h.2.2)
      else 1
  have hCmpos : ∀ m : ℕ, 0 < Cm m := by
    intro m
    simp only [Cm]
    by_cases h : (1 ≤ m ∧ (N:ℝ)/4 ≤ τ/(2*Real.pi*(m:ℝ))
        ∧ τ/(2*Real.pi*(m:ℝ)) ≤ 3*(N:ℝ))
    · rw [dif_pos h]
      exact (Classical.choose_spec (WwI_band_bound (N:=N) (χ:=χ) (K:=K) (τ:=τ) hN hχd hχ0
        hχz hK hbdd hτ h.1 h.2.1 h.2.2)).1
    · rw [dif_neg h]; norm_num
  set S : Finset ℕ := Finset.Icc 1 (WwHi N τ + 1) with hSdef
  have hSne : S.Nonempty := ⟨1, by rw [hSdef]; exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  have hCpos : (0:ℝ) < S.sup' hSne Cm + 1 := by
    have h1 : Cm 1 ≤ S.sup' hSne Cm :=
      Finset.le_sup' Cm (by rw [hSdef]; exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    have := hCmpos 1
    linarith
  refine ⟨3 * (S.sup' hSne Cm + 1), by positivity, ?_⟩
  have hper : ∀ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
      ‖WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m‖
        ≤ (S.sup' hSne Cm + 1) * (1+K) * N * (1 + Real.log τ) / τ := by
    intro m hm
    obtain ⟨hLo, hHi⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hs1m, hs2m, h1⟩ := WwS_band_mem hN hτpos hm
    have h2' : (N:ℝ)/4 ≤ τ/(2*Real.pi*(m:ℝ)) := by simpa [WwS] using hs1m
    have h3' : τ/(2*Real.pi*(m:ℝ)) ≤ 3*(N:ℝ) := by simpa [WwS] using hs2m
    have hcond : (1 ≤ m ∧ (N:ℝ)/4 ≤ τ/(2*Real.pi*(m:ℝ))
        ∧ τ/(2*Real.pi*(m:ℝ)) ≤ 3*(N:ℝ)) := ⟨h1, h2', h3'⟩
    have hspec := (Classical.choose_spec (WwI_band_bound (N:=N) (χ:=χ) (K:=K) (τ:=τ)
      hN hχd hχ0 hχz hK hbdd hτ hcond.1 hcond.2.1 hcond.2.2)).2
    have hmS : m ∈ S := by
      rw [hSdef]
      exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
    have hCmle : Classical.choose (WwI_band_bound (N:=N) (χ:=χ) (K:=K) (τ:=τ)
        hN hχd hχ0 hχz hK hbdd hτ hcond.1 hcond.2.1 hcond.2.2) ≤ S.sup' hSne Cm + 1 := by
      have hCmeq : Cm m = Classical.choose (WwI_band_bound (N:=N) (χ:=χ) (K:=K) (τ:=τ)
          hN hχd hχ0 hχz hK hbdd hτ hcond.1 hcond.2.1 hcond.2.2) := by
        simp only [Cm]
        exact dif_pos hcond
      have hsup := Finset.le_sup' Cm hmS
      linarith
    have hXn : (0:ℝ) ≤ (1+K) * (N:ℝ) * (1 + Real.log τ) / τ := by positivity
    calc ‖WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m‖
        ≤ _ * (1+K) * N * (1 + Real.log τ) / τ := hspec
      _ ≤ (S.sup' hSne Cm + 1) * (1+K) * N * (1 + Real.log τ) / τ := by
          calc _ * (1+K) * N * (1 + Real.log τ) / τ
              = _ * ((1+K) * (N:ℝ) * (1 + Real.log τ) / τ) := by ring
            _ ≤ (S.sup' hSne Cm + 1) * ((1+K) * (N:ℝ) * (1 + Real.log τ) / τ) :=
                mul_le_mul_of_nonneg_right hCmle hXn
            _ = (S.sup' hSne Cm + 1) * (1+K) * N * (1 + Real.log τ) / τ := by ring
  have hcard : ((Finset.Icc (WwLo N τ) (WwHi N τ)).card : ℝ) ≤ 3*τ/(N:ℝ) := by
    have h1 : ((Finset.Icc (WwLo N τ) (WwHi N τ)).card : ℝ) ≤ (WwHi N τ : ℕ) + 1 := by
      have h : (Finset.Icc (WwLo N τ) (WwHi N τ)).card ≤ WwHi N τ + 1 := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast h
    have h2 : ((WwHi N τ : ℕ) : ℝ) + 1 ≤ 2*τ/(Real.pi*(N:ℝ)) + 1 := by
      have hfl : ((WwHi N τ : ℕ) : ℝ) ≤ 2*τ/(Real.pi*(N:ℝ)) := by
        show ((Nat.floor (2*τ/(Real.pi*(N:ℝ))) : ℕ) : ℝ) ≤ 2*τ/(Real.pi*(N:ℝ))
        exact Nat.floor_le (by positivity)
      linarith
    have hπ34 : (2:ℝ)/Real.pi ≤ 4/3 := by
      rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
      nlinarith [Real.pi_gt_three]
    have h3 : 2*τ/(Real.pi*(N:ℝ)) + 1 ≤ 3*τ/(N:ℝ) := by
      have h5 : (1:ℝ) ≤ τ/(N:ℝ) := by rw [le_div_iff₀ hNpos]; simpa using hNτ
      have hkey : (1:ℝ) ≤ (τ/(N:ℝ))*(3 - 2/Real.pi) := by nlinarith [h5, hπ34, Real.pi_pos]
      have he : 3*τ/(N:ℝ) - 2*τ/(Real.pi*(N:ℝ)) = (τ/(N:ℝ))*(3 - 2/Real.pi) := by
        field_simp
        try ring
      linarith [hkey, he]
    linarith [h1, h2, h3]
  have hXnn : (0:ℝ) ≤ (S.sup' hSne Cm + 1) * (1+K) * (N:ℝ) * (1 + Real.log τ) / τ := by
    have h2 : (0:ℝ) ≤ 1+K := by linarith
    have h3 : (0:ℝ) ≤ (N:ℝ) := by positivity
    positivity
  calc ‖∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
          (WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m)‖
      ≤ ∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
          ‖WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
          ((S.sup' hSne Cm + 1) * (1+K) * N * (1 + Real.log τ) / τ) := Finset.sum_le_sum hper
    _ = (((Finset.Icc (WwLo N τ) (WwHi N τ)).card : ℕ) : ℝ)
          * (((S.sup' hSne Cm + 1) * (1+K) * N * (1 + Real.log τ) / τ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3*τ/(N:ℝ)) * (((S.sup' hSne Cm + 1) * (1+K) * N * (1 + Real.log τ) / τ)) :=
        mul_le_mul_of_nonneg_right hcard hXnn
    _ = 3 * (S.sup' hSne Cm + 1) * (1+K) * (1 + Real.log τ) := by
        field_simp
        try ring


/-! ## Explicit normalisation of `WwAc` (sharp constants) -/

/-- The sup-norm bound for `deriv WwFc`, made explicit. -/
noncomputable def WwFcD : ℝ := Classical.choose WwFc_deriv_bounded

lemma WwFcD_pos : 0 < WwFcD := (Classical.choose_spec WwFc_deriv_bounded).1

lemma WwFcD_le (u : ℝ) : |deriv WwFc u| ≤ WwFcD := (Classical.choose_spec WwFc_deriv_bounded).2 u

/-- Explicit sup-norm bound for `deriv (WwAc χ s)`. -/
lemma WwAc_deriv_bound_expl {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {K s : ℝ} (hK : 0 ≤ K) (hs0 : 0 ≤ s)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N) (hs2 : s ≤ 3*N) :
    ∀ u : ℝ, ‖deriv (WwAc χ s) u‖ ≤ (max WwFcD 99 + 12) * (1 + K) * Real.sqrt N := by
  intro u
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqrtN1 : (1:ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ N))
  have hχd' : Differentiable ℝ χ := hχd.differentiable (by norm_num)
  have hfd : HasDerivAt WwFc (deriv WwFc u) u :=
    (WwFc_contDiff.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hf : HasDerivAt (fun y : ℝ => ((WwFc y : ℝ) : ℂ)) (((deriv WwFc u : ℝ)) : ℂ) u :=
    hfd.ofReal_comp
  have hcomp : HasDerivAt (fun y : ℝ => χ (s*y)) (deriv χ (s*u) * s) u :=
    (hχd'.differentiableAt.hasDerivAt).comp u (hasDerivAt_const_mul' (s := s) (u := u))
  have hg : HasDerivAt (fun y : ℝ => ((χ (s*y) : ℝ) : ℂ)) (((deriv χ (s*u)) * s : ℝ) : ℂ) u :=
    hcomp.ofReal_comp
  have hprod := hf.mul hg
  have hfun : WwAc χ s = fun y : ℝ => ((WwFc y : ℝ) : ℂ) * ((χ (s*y) : ℝ) : ℂ) := by
    funext y
    simp only [WwAc, WwFc]
  have hderiv : deriv (WwAc χ s) u
      = (((deriv WwFc u : ℝ)) : ℂ) * ((χ (s*u) : ℝ) : ℂ)
        + ((WwFc u : ℝ) : ℂ) * ((((deriv χ (s*u)) * s : ℝ)) : ℂ) := by
    rw [hfun]
    exact hprod.deriv
  rw [hderiv]
  refine le_trans (norm_add_le _ _) ?_
  have hA : ‖(((deriv WwFc u : ℝ)) : ℂ) * ((χ (s*u) : ℝ) : ℂ)‖ ≤ max WwFcD 99 := by
    rw [norm_mul, norm_ofReal_cast, norm_ofReal_cast]
    have h1 : |deriv WwFc u| ≤ WwFcD := WwFcD_le u
    have h2 : |χ (s*u)| ≤ 1 := by
      rw [abs_of_nonneg (hχ0 (s*u)).1]
      exact (hχ0 (s*u)).2
    calc |deriv WwFc u| * |χ (s*u)| ≤ (max WwFcD 99) * 1 :=
          mul_le_mul (le_trans h1 (le_max_left _ _)) h2 (abs_nonneg _) (by positivity)
      _ = max WwFcD 99 := by ring
  have hB : ‖((WwFc u : ℝ) : ℂ) * ((((deriv χ (s*u)) * s : ℝ)) : ℂ)‖
      ≤ 12 * K * Real.sqrt N := by
    rw [norm_mul, norm_ofReal_cast, norm_ofReal_cast]
    have h1 : |WwFc u| ≤ 4 := WwFc_abs_le u
    have h2 : |deriv χ (s*u) * s| ≤ 3 * K * Real.sqrt N := by
      rw [abs_mul]
      have ha : |deriv χ (s*u)| ≤ K / Real.sqrt N := hbdd (s*u)
      have hb : |s| ≤ 3*N := by rw [abs_of_nonneg hs0]; exact hs2
      have h3 : (K / Real.sqrt N) * (3*N) = 3 * K * Real.sqrt N := by
        rw [show (K / Real.sqrt N) * (3*N) = 3 * (N / Real.sqrt N) * K by ring,
          Real.div_sqrt]
        ring
      calc |deriv χ (s*u)| * |s| ≤ (K / Real.sqrt N) * (3*N) :=
            mul_le_mul ha hb (abs_nonneg _) (by positivity)
        _ = 3 * K * Real.sqrt N := h3
    have h4 : 4 * (3 * K * Real.sqrt N) = 12 * K * Real.sqrt N := by ring
    calc |WwFc u| * |deriv χ (s*u) * s| ≤ 4 * (3 * K * Real.sqrt N) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = 12 * K * Real.sqrt N := h4
  refine le_trans (add_le_add hA hB) ?_
  have hK1 : (0:ℝ) ≤ 1 + K := by linarith
  have hone : (1:ℝ) ≤ (1 + K) * Real.sqrt N := by
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ (1 + K) * Real.sqrt N :=
          mul_le_mul (by linarith) hsqrtN1 (by norm_num) (by linarith)
  have h1a : max WwFcD 99 ≤ (max WwFcD 99) * (1 + K) * Real.sqrt N := by
    calc max WwFcD 99 = max WwFcD 99 * 1 := by ring
      _ ≤ (max WwFcD 99) * ((1 + K) * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left hone (by positivity)
      _ = max WwFcD 99 * (1 + K) * Real.sqrt N := by ring
  have h2a : 12 * K * Real.sqrt N ≤ 12 * (1 + K) * Real.sqrt N := by
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg N)
    nlinarith [hK]
  have h3a : max WwFcD 99 + 12 * K * Real.sqrt N
      ≤ (max WwFcD 99 + 12) * (1 + K) * Real.sqrt N := by
    nlinarith [h1a, h2a, hK1, Real.sqrt_nonneg N]
  linarith [h3a]

lemma WwAc_scaled_bounds_expl {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) {K s : ℝ} (hK : 0 ≤ K) (hs0 : 0 ≤ s)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N) (hs2 : s ≤ 3*N) :
    (∀ u : ℝ, ‖((max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) : ℝ) : ℂ)⁻¹
        * WwAc χ s u‖ ≤ 1) ∧
    (∀ u : ℝ, ‖deriv (fun u : ℝ =>
        ((max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) : ℝ) : ℂ)⁻¹ * WwAc χ s u) u‖ ≤ 1) := by
  refine ⟨?_, ?_⟩
  · intro u
    have hMpos : (0:ℝ) < max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) :=
      lt_max_of_lt_left (by norm_num)
    rw [norm_mul, norm_inv, norm_ofReal_cast, abs_of_pos hMpos]
    have h1 : ‖WwAc χ s u‖ ≤ max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) :=
      le_trans (WwAc_norm_le hχ0 s u) (le_max_left _ _)
    calc (max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N))⁻¹ * ‖WwAc χ s u‖
        ≤ (max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N))⁻¹
            * max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hMpos)
  · intro u
    have hMpos : (0:ℝ) < max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) :=
      lt_max_of_lt_left (by norm_num)
    have hdiff : DifferentiableAt ℝ (WwAc χ s) u :=
      ((WwAc_contDiff hχd s).differentiable (by norm_num)).differentiableAt
    have hd : deriv (fun u : ℝ =>
        ((max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) : ℝ) : ℂ)⁻¹ * WwAc χ s u) u
        = (((max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) : ℝ) : ℂ)⁻¹)
          * deriv (WwAc χ s) u := deriv_const_mul _ hdiff
    rw [hd, norm_mul, norm_inv, norm_ofReal_cast, abs_of_pos hMpos]
    have h1 : ‖deriv (WwAc χ s) u‖ ≤ (max WwFcD 99 + 12) * (1 + K) * Real.sqrt N :=
      WwAc_deriv_bound_expl hN hχd hχ0 hK hs0 hbdd hs2 u
    have h2 : (max WwFcD 99 + 12) * (1 + K) * Real.sqrt N
        ≤ max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) := le_max_right _ _
    calc (max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N))⁻¹ * ‖deriv (WwAc χ s) u‖
        ≤ (max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N))⁻¹
            * max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left (le_trans h1 h2) (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hMpos)


/-! ## Sharp constants: the `WwC` integral and the band error -/

noncomputable def WwCb : ℝ := Classical.choose WwB_deriv_bounded
lemma WwCb_pos : 0 < WwCb := (Classical.choose_spec WwB_deriv_bounded).1
lemma WwCb_le (u : ℝ) : |deriv (WwB : ℝ → ℝ) u| ≤ WwCb :=
  (Classical.choose_spec WwB_deriv_bounded).2 u

noncomputable def WwCw : ℝ := Classical.choose log_phase_stationary_phase_scaled
lemma WwCw_pos : 0 < WwCw := (Classical.choose_spec log_phase_stationary_phase_scaled).1
lemma WwCw_spec : ∀ (A : ℝ → ℂ) (a b t M : ℝ),
    (1/2 : ℝ) ≤ a → a < 1 → 1 < b → b ≤ 6 →
    0 < M → ContDiff ℝ 2 A → (∀ y, y ∉ Set.Icc a b → A y = 0) →
    (∀ y, ‖A y‖ ≤ M) → (∀ y, ‖deriv A y‖ ≤ M) → 2 ≤ t →
    ‖(∫ y in a..b, A y * Complex.exp (Complex.I * t * (Real.log y - y)))
      - A 1 * Complex.exp (-(t : ℂ) * Complex.I) * ((Real.sqrt (2 * Real.pi / t) : ℝ) : ℂ)
          * Complex.exp (-(Real.pi / 4) * Complex.I)‖
      ≤ WwCw * M * (Real.log t / t) :=
  (Classical.choose_spec log_phase_stationary_phase_scaled).2

lemma WwA_stat_unif {N : ℕ} {χ : ℝ → ℝ} {K τ : ℝ}
    (hCb : ∀ u, |deriv (WwB : ℝ → ℝ) u| ≤ WwCb) (hτ : 2 ≤ τ)
    (hχd : ContDiff ℝ 3 χ) (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N) (hN : 1 ≤ N) (hKnn : 0 ≤ K) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 3 * (N:ℝ) →
      ‖(∫ u : ℝ, WwA χ s u * Complex.exp (Complex.I * τ * (Real.log u - u)))
        - (χ s : ℂ) * WwFres τ‖
      ≤ WwCw * ((2*WwCb+10)*(1+K)*(1+Real.sqrt N)) * (Real.log τ / τ) := by
  intro s hs0 hle
  set M : ℝ := (2*WwCb+10)*(1+K)*(1+Real.sqrt N) with hMdef
  have h1 : (0:ℝ) ≤ 2*WwCb+10 := by linarith [WwCb_pos]
  have h2 : (0:ℝ) ≤ 1+Real.sqrt N := by positivity
  have hMpos : 0 < M := by
    rw [hMdef]
    have h3 : (0:ℝ) < 2*WwCb+10 := by linarith [WwCb_pos]
    have h4 : (0:ℝ) < 1+Real.sqrt N := by positivity
    positivity
  set F : ℝ → ℂ := fun u => WwA χ s u * Complex.exp (Complex.I * τ * (Real.log u - u)) with hF
  have hFsupp : ∀ u : ℝ, u ∉ Set.Icc (1/2) 6 → F u = 0 := fun u hu => by
    simp only [hF, WwA_support χ s u hu, zero_mul]
  have hIntEq : (∫ u : ℝ, F u) = ∫ u in (1/2:ℝ)..6, F u := by
    rw [intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ) ≤ 6),
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Set.Ioc (1/2) 6
    · rw [Set.indicator_of_mem hu]
    · rw [Set.indicator_of_notMem hu]
      by_cases hu2 : u ∈ Set.Icc (1/2) 6
      · have hu3 : u = 1/2 := by
          simp only [Set.mem_Icc] at hu2
          have hu4 : ¬ ((1/2:ℝ) < u ∧ u ≤ 6) := by simpa only [Set.mem_Ioc] using hu
          have hle' : u ≤ 1/2 := by
            by_contra hc
            push Not at hc
            exact hu4 ⟨hc, hu2.2⟩
          linarith [hu2.1]
        subst hu3
        have hz : (WwB : ℝ → ℝ) (1/2) = 0 := WwB_zero (1/2) (by norm_num)
        have hz2 : WwA χ s (1/2) = 0 := by
          simp only [WwA, hz, Complex.ofReal_zero, zero_mul]
        rw [hF]; simp only [hz2, zero_mul]
      · exact hFsupp u hu2
  rw [hIntEq]
  have hstep := WwCw_spec (WwA χ s) (1/2) 6 τ M (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hMpos (WwA_contDiff hχd) (fun y hy => WwA_support χ s y hy)
    (fun y => WwA_norm_le_M (by linarith [WwCb_pos] : (0:ℝ) ≤ WwCb) hχ0 hN hKnn y)
    (fun y => WwA_deriv_norm_le hCb (by linarith [WwCb_pos] : (0:ℝ) ≤ WwCb) hχd hχ0 hbdd
      (by omega : 0 < N) hs0 hKnn hle y) hτ
  rw [hMdef] at hstep
  have hA1 : WwA χ s 1 = (χ s : ℂ) := WwA_one
  rw [hA1] at hstep
  have hFres : (χ s : ℂ) * WwFres τ = (χ s : ℂ) * Complex.exp (-(τ : ℂ) * Complex.I)
      * ((Real.sqrt (2 * Real.pi / τ) : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I) := by
    unfold WwFres; ring
  rw [hFres]
  exact hstep

lemma WwC_integral_sharp {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
    (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
    {K s τ : ℝ} (hK : 0 ≤ K) (hs0 : 0 ≤ s) (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
    (hs1 : (N:ℝ)/4 ≤ s) (hs2 : s ≤ 3*N) (hτ : 4 ≤ τ) :
    ‖∫ u : ℝ, WwC χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖
      ≤ (530 * max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N)) / τ := by
  obtain ⟨hA1, hA2⟩ := WwAc_scaled_bounds_expl hN hχd hχ0 hK hs0 hbdd hs2
  set M : ℝ := max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; exact lt_max_of_lt_left (by norm_num)
  have hdphi1 : ∀ y ∈ Set.Icc (1/6:ℝ) (3/4), (1:ℝ)/3 ≤ |1 / y - 1| :=
    fun y hy => one_div_sub_one_ge_third hy.1 hy.2
  have hy01 : ∀ y ∈ Set.Icc (1/6:ℝ) (3/4), 0 < y := fun y hy => by linarith [hy.1]
  have hquad1 : ∀ y ∈ Set.Icc (1/6:ℝ) (3/4), 1 / y ^ 2 ≤ 36 :=
    fun y hy => one_div_sq_le_36 hy.1
  have hdphi2 : ∀ y ∈ Set.Icc (5/4:ℝ) 12, (1:ℝ)/5 ≤ |1 / y - 1| :=
    fun y hy => one_div_sub_one_ge_fifth hy.1
  have hy02 : ∀ y ∈ Set.Icc (5/4:ℝ) 12, 0 < y := fun y hy => by linarith [hy.1]
  have hquad2 : ∀ y ∈ Set.Icc (5/4:ℝ) 12, 1 / y ^ 2 ≤ 1 :=
    fun y hy => one_div_sq_le_one (by linarith [hy.1])
  have hb1 : ‖∫ u in (1/6:ℝ)..(3/4),
        WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖
      ≤ M * (τ⁻¹ * 197) := by
    refine le_trans (WwAc_interval_bound (c := (1/6:ℝ)) (d := 3/4) (lam := 1/3) (Q := 36)
      hN hχd hχ0 hK hs0 hbdd hs2 hτ hMpos hA1 hA2 (by norm_num) (by norm_num) (by norm_num)
      hdphi1 hy01 hquad1) ?_
    have hval : τ⁻¹ * (2 / (1/3) + ((3:ℝ)/4 - 1/6) * (1 / (1/3) + 36 / (1/3) ^ 2))
        ≤ τ⁻¹ * 197 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by linarith))
      norm_num
    exact mul_le_mul_of_nonneg_left hval (le_of_lt hMpos)
  have hb2 : ‖∫ u in (5/4:ℝ)..12,
        WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖
      ≤ M * (τ⁻¹ * 333) := by
    refine le_trans (WwAc_interval_bound (c := (5/4:ℝ)) (d := 12) (lam := 1/5) (Q := 1)
      hN hχd hχ0 hK hs0 hbdd hs2 hτ hMpos hA1 hA2 (by norm_num) (by norm_num) (by norm_num)
      hdphi2 hy02 hquad2) ?_
    have hval : τ⁻¹ * (2 / (1/5) + ((12:ℝ) - 5/4) * (1 / (1/5) + 1 / (1/5) ^ 2))
        ≤ τ⁻¹ * 333 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by linarith))
      norm_num
    exact mul_le_mul_of_nonneg_left hval (le_of_lt hMpos)
  have hassm : ‖∫ u : ℝ, WwC χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖
      ≤ ‖∫ u in (1/6:ℝ)..(3/4),
            WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖
        + ‖∫ u in (5/4:ℝ)..12,
            WwAc χ s u * Complex.exp (Complex.I * ((τ * (Real.log u - u) : ℝ) : ℂ))‖ := by
    rw [WwC_integral_eq_interval hN hχz hs1 hs2,
      WwC_integral_eq_WwAc_integral (χ := χ) (s := s) (τ := τ),
      WwAc_integral_split hχd s τ, WwAc_integral_middle_zero, add_zero]
    exact norm_add_le _ _
  refine le_trans hassm (le_trans (add_le_add hb1 hb2) ?_)
  have hsum : M * (τ⁻¹ * 197) + M * (τ⁻¹ * 333) ≤ 530 * M / τ := by
    rw [show M * (τ⁻¹ * 197) + M * (τ⁻¹ * 333) = (530 * M) / τ by ring]
  exact hsum


/-! ## The sharp band bound with a global constant -/

lemma WwI_band_sharp :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} (hχd : ContDiff ℝ 3 χ)
      (hχ0 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
      (hχz : ∀ y : ℝ, y ≤ (N:ℝ) - Real.sqrt N ∨ (2*N:ℝ) + Real.sqrt N ≤ y → χ y = 0)
      {K τ : ℝ} (hK : 0 ≤ K) (hbdd : ∀ y, |deriv χ y| ≤ K / Real.sqrt N)
      (hτ : 4 ≤ τ) {m : ℕ} (hm : 1 ≤ m)
      (hs1 : (N:ℝ)/4 ≤ τ/(2*Real.pi*(m:ℝ))) (hs2 : τ/(2*Real.pi*(m:ℝ)) ≤ 3*N),
      ‖WwI χ τ m - WwMain (N:=N) χ τ m‖ ≤ C * (1+K) * N * (1 + Real.log τ) / τ := by
  have hmax4pos : (0:ℝ) < max 4 (max WwFcD 99 + 12) :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hA0nn : (0:ℝ) ≤ 2*WwCw*(2*WwCb+10) + 530*max 4 (max WwFcD 99 + 12) := by
    have h1 : (0:ℝ) ≤ 2*WwCw*(2*WwCb+10) :=
      mul_nonneg (mul_nonneg (by norm_num) (le_of_lt WwCw_pos)) (by linarith [WwCb_pos])
    have h2 : (0:ℝ) ≤ 530*max 4 (max WwFcD 99 + 12) := by linarith
    linarith
  refine ⟨2*(2*WwCw*(2*WwCb+10) + 530*max 4 (max WwFcD 99 + 12)) + 1, by linarith, ?_⟩
  intro N hN χ hχd hχ0 hχz K τ hK hbdd hτ m hm hs1 hs2
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN0 : (0:ℝ) ≤ N := le_of_lt hNpos
  have hτ0 : (0:ℝ) < τ := by linarith
  have hlog0 : (0:ℝ) ≤ 1 + Real.log τ := by
    have h := Real.log_nonneg (by linarith : (1:ℝ) ≤ τ)
    linarith
  have hs0 : (0:ℝ) ≤ τ/(2*Real.pi*(m:ℝ)) := by positivity
  have hs2' : τ/(2*Real.pi*(m:ℝ)) ≤ 3*(N:ℝ) := hs2
  have hCa := WwA_stat_unif (N := N) (χ := χ) (K := K) (τ := τ) WwCb_le (by linarith) hχd hχ0
    hbdd (by omega) hK (τ/(2*Real.pi*(m:ℝ))) hs0 hs2'
  have hCc := WwC_integral_sharp (N := N) (χ := χ) hN hχd hχ0 hχz (K := K) (s := τ/(2*Real.pi*(m:ℝ)))
    (τ := τ) hK hs0 hbdd hs1 hs2' hτ
  have hsqrtN1 : (1:ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN1
  have hY1 : (1:ℝ) ≤ (1+K)*Real.sqrt N := by
    calc (1:ℝ) = 1*1 := by ring
      _ ≤ (1+K)*Real.sqrt N := mul_le_mul (by linarith) hsqrtN1 (by norm_num) (by linarith)
  have hY0 : (0:ℝ) ≤ (1+K)*Real.sqrt N := by linarith
  have hMbound : max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N)
      ≤ max 4 (max WwFcD 99 + 12) * ((1 + K) * Real.sqrt N) := by
    have ha4 : (4:ℝ) ≤ max 4 (max WwFcD 99 + 12) := le_max_left _ _
    have ha2 : (max WwFcD 99 + 12) ≤ max 4 (max WwFcD 99 + 12) := le_max_right _ _
    refine max_le ?_ ?_
    · calc (4:ℝ) ≤ max 4 (max WwFcD 99 + 12) * 1 := by simpa using ha4
        _ ≤ max 4 (max WwFcD 99 + 12) * ((1+K)*Real.sqrt N) :=
            mul_le_mul_of_nonneg_left hY1 (by linarith)
    · calc (max WwFcD 99 + 12) * (1 + K) * Real.sqrt N
          = (max WwFcD 99 + 12) * ((1+K)*Real.sqrt N) := by ring
        _ ≤ max 4 (max WwFcD 99 + 12) * ((1+K)*Real.sqrt N) :=
            mul_le_mul_of_nonneg_right ha2 hY0
  have hCa' : ‖(∫ u : ℝ, WwA χ (τ/(2*Real.pi*(m:ℝ))) u
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
      - (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ‖
      ≤ WwCw * ((2*WwCb+10)*(1+K)*(1+Real.sqrt N)) * (Real.log τ / τ) := by
    rw [integral_exp_form_A (WwA χ (τ/(2*Real.pi*(m:ℝ)))) τ] at hCa
    exact hCa
  have hCc' : ‖∫ u : ℝ, WwC χ (τ/(2*Real.pi*(m:ℝ))) u
        * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))‖
      ≤ (530 * max 4 (max WwFcD 99 + 12)) * (1+K) * Real.sqrt N / τ := by
    rw [integral_exp_form_C (WwC χ (τ/(2*Real.pi*(m:ℝ)))) τ] at hCc
    refine le_trans hCc ?_
    have h2 : 530 * max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N)
        ≤ (530 * max 4 (max WwFcD 99 + 12)) * ((1+K)*Real.sqrt N) := by
      calc 530 * max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N)
          ≤ 530 * (max 4 (max WwFcD 99 + 12) * ((1 + K) * Real.sqrt N)) :=
            mul_le_mul_of_nonneg_left hMbound (by norm_num)
        _ = (530 * max 4 (max WwFcD 99 + 12)) * ((1+K)*Real.sqrt N) := by ring
    calc 530 * max 4 ((max WwFcD 99 + 12) * (1 + K) * Real.sqrt N) / τ
        ≤ ((530 * max 4 (max WwFcD 99 + 12)) * ((1+K)*Real.sqrt N)) / τ :=
          div_le_div_of_nonneg_right h2 (le_of_lt hτ0)
      _ = (530 * max 4 (max WwFcD 99 + 12)) * (1+K) * Real.sqrt N / τ := by ring
  have hCc0 : (0:ℝ) ≤ 530 * max 4 (max WwFcD 99 + 12) := by linarith
  have hbr : ‖(∫ u : ℝ, WwA χ (τ/(2*Real.pi*(m:ℝ))) u
              * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
            - (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ
          + ∫ u : ℝ, WwC χ (τ/(2*Real.pi*(m:ℝ))) u
              * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))‖
      ≤ (WwCw * (2*WwCb+10) * (1+K) * (1+Real.sqrt N)
          + (530 * max 4 (max WwFcD 99 + 12)) * (1+K) * Real.sqrt N)
        * (1 + Real.log τ) / τ :=
    le_trans (norm_add_le _ _)
      (WwI_band_bracket_bound (N := N) hN hτ (le_of_lt WwCw_pos) (le_of_lt WwCb_pos) hCc0 hK
        (norm_nonneg _) hCa' hCc')
  have hsum2 : WwCw * (2*WwCb+10) * (1+K) * (1+Real.sqrt N)
      + (530 * max 4 (max WwFcD 99 + 12)) * (1+K) * Real.sqrt N
      ≤ (2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) * ((1+K)*Real.sqrt N) := by
    have hC10 : (0:ℝ) ≤ WwCw * (2*WwCb+10) * (1+K) :=
      mul_nonneg (mul_nonneg (le_of_lt WwCw_pos) (by linarith [WwCb_pos])) (by linarith)
    have hone : (1 + Real.sqrt N) ≤ 2 * Real.sqrt N := by linarith
    have hT1 : WwCw * (2*WwCb+10) * (1+K) * (1+Real.sqrt N)
        ≤ (2*(WwCw*(2*WwCb+10)))*((1+K)*Real.sqrt N) := by
      calc WwCw * (2*WwCb+10) * (1+K) * (1+Real.sqrt N)
          ≤ WwCw * (2*WwCb+10) * (1+K) * (2*Real.sqrt N) :=
            mul_le_mul_of_nonneg_left hone hC10
        _ = (2*(WwCw*(2*WwCb+10)))*((1+K)*Real.sqrt N) := by ring
    calc WwCw * (2*WwCb+10) * (1+K) * (1+Real.sqrt N)
          + (530 * max 4 (max WwFcD 99 + 12)) * (1+K) * Real.sqrt N
        ≤ (2*(WwCw*(2*WwCb+10)))*((1+K)*Real.sqrt N)
          + (530 * max 4 (max WwFcD 99 + 12))*((1+K)*Real.sqrt N) :=
          add_le_add hT1 (le_of_eq (by ring))
      _ = (2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) * ((1+K)*Real.sqrt N) := by ring
  have hbr2 : ‖(∫ u : ℝ, WwA χ (τ/(2*Real.pi*(m:ℝ))) u
              * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ))))
            - (χ (τ/(2*Real.pi*(m:ℝ))) : ℂ) * WwFres τ
          + ∫ u : ℝ, WwC χ (τ/(2*Real.pi*(m:ℝ))) u
              * Complex.exp (Complex.I * ((τ : ℂ) * ((Real.log u - u : ℝ) : ℂ)))‖
      ≤ (2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) * (1+K) * Real.sqrt N * (1 + Real.log τ) / τ := by
    refine le_trans hbr ?_
    have hnum : (WwCw * (2*WwCb+10) * (1+K) * (1+Real.sqrt N)
        + (530 * max 4 (max WwFcD 99 + 12)) * (1+K) * Real.sqrt N) * (1 + Real.log τ)
        ≤ (2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) * (1+K) * Real.sqrt N * (1 + Real.log τ) :=
      le_trans (mul_le_mul_of_nonneg_right hsum2 hlog0) (le_of_eq (by ring))
    exact div_le_div_of_nonneg_right hnum (le_of_lt hτ0)
  have hfact := WwI_band_factor (N := N) hN hχd hχz hτ hm hs1 hs2
  simp only [WwMain, WwS] at hfact ⊢
  rw [hfact, norm_sqrt_exp_mul]
  refine le_trans (mul_le_mul_of_nonneg_left hbr2 (Real.sqrt_nonneg _)) ?_
  have hs2r : Real.sqrt (τ/(2*Real.pi*(m:ℝ))) ≤ Real.sqrt (3*(N:ℝ)) := Real.sqrt_le_sqrt hs2
  have hsplit : Real.sqrt (3*(N:ℝ)) = Real.sqrt 3 * Real.sqrt N := Real.sqrt_mul (by norm_num) (N:ℝ)
  have hNsq : Real.sqrt N * Real.sqrt N = (N:ℝ) := by
    rw [← sq, Real.sq_sqrt (by positivity)]
  have h3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hP0 : (0:ℝ) ≤ (1+K)*(N:ℝ)*(1 + Real.log τ) :=
    mul_nonneg (mul_nonneg (by linarith) hN0) hlog0
  have hQ0 : (0:ℝ) ≤ (2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) * (1+K) * Real.sqrt N * (1 + Real.log τ) / τ :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA0nn (by linarith)) (Real.sqrt_nonneg N)) hlog0)
      (le_of_lt hτ0)
  calc Real.sqrt (τ/(2*Real.pi*(m:ℝ)))
        * ((2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) * (1+K) * Real.sqrt N * (1 + Real.log τ) / τ)
      ≤ Real.sqrt (3*(N:ℝ))
        * ((2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) * (1+K) * Real.sqrt N * (1 + Real.log τ) / τ) :=
        mul_le_mul_of_nonneg_right hs2r hQ0
    _ = Real.sqrt 3
        * ((2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) * (1+K) * (Real.sqrt N * Real.sqrt N) * (1 + Real.log τ) / τ) := by
        rw [hsplit]; ring
    _ = Real.sqrt 3
        * ((2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) * (1+K) * N * (1 + Real.log τ) / τ) := by
        rw [hNsq]
    _ ≤ 2 * ((2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) * (1+K) * N * (1 + Real.log τ) / τ) := by
        apply mul_le_mul_of_nonneg_right h3
        exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA0nn (by linarith)) hN0) hlog0) (le_of_lt hτ0)
    _ = 2*((2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12))*((1+K)*N*(1 + Real.log τ))) / τ := by ring
    _ ≤ ((2*(2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) + 1)*((1+K)*N*(1 + Real.log τ))) / τ := by
        have hnum2 : 2*((2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12))*((1+K)*N*(1 + Real.log τ)))
            ≤ (2*(2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) + 1)*((1+K)*N*(1 + Real.log τ)) := by
          nlinarith [hA0nn, hP0]
        exact div_le_div_of_nonneg_right hnum2 (le_of_lt hτ0)
    _ = (2*(2*WwCw*(2*WwCb+10) + 530 * max 4 (max WwFcD 99 + 12)) + 1) * (1+K) * N * (1 + Real.log τ) / τ := by ring


/-! ## The main-term identity on the band -/

lemma WwC0_norm (τ : ℝ) : ‖WwC0 τ‖ = 1 := by
  have heq : WwC0 τ = Complex.exp
      (((τ * Real.log τ - τ * Real.log (2 * Real.pi) - τ - Real.pi / 4 : ℝ) : ℂ) * Complex.I) := by
    unfold WwC0
    rw [mul_comm]
  rw [heq, Complex.norm_exp_ofReal_mul_I]

lemma band_main_identity {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hχ1 : ∀ y : ℝ, (N:ℝ) ≤ y → y ≤ 2*N → χ y = 1) :
    ∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ), WwMain (N:=N) χ τ m
      = WwC0 τ * ((starRingEnd ℂ) (WwK N τ)
          + ∑ m ∈ (Finset.Icc (WwLo N τ) (WwHi N τ)) \ (Finset.Icc (WwDLo N τ) (WwDHi N τ)),
              WwMainTerm χ τ m) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hDsub : Finset.Icc (WwDLo N τ) (WwDHi N τ) ⊆ Finset.Icc (WwLo N τ) (WwHi N τ) :=
    WwD_subset_band hτ (by omega : 0 < N)
  have hDLo1 : 1 ≤ WwDLo N τ := Nat.ceil_pos.mpr (by positivity)
  have hfac : ∀ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
      WwMain (N:=N) χ τ m = WwC0 τ * WwMainTerm χ τ m := by
    intro m hm
    exact WwMain_factor (N:=N) hτ (WwS_band_mem hN hτ hm).2.2
  have hDfac : ∀ m ∈ Finset.Icc (WwDLo N τ) (WwDHi N τ),
      WwMain (N:=N) χ τ m = WwC0 τ * WwMainTerm χ τ m := by
    intro m hm
    exact WwMain_factor (N:=N) hτ (le_trans hDLo1 (Finset.mem_Icc.mp hm).1)
  have hmain : ∑ m ∈ Finset.Icc (WwDLo N τ) (WwDHi N τ), WwMainTerm χ τ m
      = (starRingEnd ℂ) (WwK N τ) := by
    have h1 := mainTerm_sum_eq (N := N) (χ := χ) hN hτ hχ1 hDLo1
    have h1' : ∑ m ∈ Finset.Icc (WwDLo N τ) (WwDHi N τ), WwMain (N:=N) χ τ m
        = WwC0 τ * (starRingEnd ℂ) (WwK N τ) := h1
    have h2 : ∑ m ∈ Finset.Icc (WwDLo N τ) (WwDHi N τ), WwMain (N:=N) χ τ m
        = WwC0 τ * ∑ m ∈ Finset.Icc (WwDLo N τ) (WwDHi N τ), WwMainTerm χ τ m := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hDfac
    rw [h2] at h1'
    have hc0 : WwC0 τ ≠ 0 := by
      intro hc
      have hh := WwC0_norm τ
      rw [hc] at hh
      simp at hh
    exact mul_left_cancel₀ hc0 h1'
  have hstep : ∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ), WwMain (N:=N) χ τ m
      = WwC0 τ * ∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ), WwMainTerm χ τ m := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hfac
  rw [hstep]
  congr 1
  rw [← Finset.sum_sdiff hDsub, hmain]
  ring


/-- **The band error with a global constant.**  Given a per-term bound
`‖WwI m - WwMain m‖ ≤ C₀(1+K)N(1+log τ)/τ` on the band (indices with
`N/4 ≤ τ/(2πm) ≤ 3N`), the sum over the whole band is bounded by
`3 C₀ (1+K) (1+log τ)`: the band contains at most `3τ/N` integers. -/
lemma WwI_band_sum_bound_sharp {C0 : ℝ} (hC0nn : 0 ≤ C0)
    {N : ℕ} (hN : 4 ≤ N) {χ : ℝ → ℝ} {K τ : ℝ} (hK : 0 ≤ K) (hτ : 4 ≤ τ) (hNτ : (N:ℝ) ≤ τ)
    (hband : ∀ (m : ℕ), 1 ≤ m → (N:ℝ)/4 ≤ τ/(2*Real.pi*(m:ℝ)) →
        τ/(2*Real.pi*(m:ℝ)) ≤ 3*(N:ℝ) →
        ‖WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m‖ ≤ C0 * (1+K) * N * (1 + Real.log τ) / τ) :
    ‖∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ), (WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m)‖
      ≤ 3*C0 * (1+K) * (1 + Real.log τ) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hτpos : (0:ℝ) < τ := by linarith
  have h1K : (0:ℝ) ≤ 1+K := by linarith
  have hlog : (0:ℝ) ≤ 1 + Real.log τ := by
    have := Real.log_nonneg (by linarith : (1:ℝ) ≤ τ)
    linarith
  have hper : ∀ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
      ‖WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m‖ ≤ C0 * (1+K) * N * (1 + Real.log τ) / τ := by
    intro m hm
    obtain ⟨hs1m, hs2m, h1⟩ := WwS_band_mem hN hτpos hm
    exact hband m h1 (by simpa [WwS] using hs1m) (by simpa [WwS] using hs2m)
  have hcard : ((Finset.Icc (WwLo N τ) (WwHi N τ)).card : ℝ) ≤ 3*τ/(N:ℝ) := by
    have h1 : ((Finset.Icc (WwLo N τ) (WwHi N τ)).card : ℝ) ≤ (WwHi N τ : ℕ) + 1 := by
      have h : (Finset.Icc (WwLo N τ) (WwHi N τ)).card ≤ WwHi N τ + 1 := by
        rw [Nat.card_Icc]
        omega
      exact_mod_cast h
    have h2 : ((WwHi N τ : ℕ) : ℝ) + 1 ≤ 2*τ/(Real.pi*(N:ℝ)) + 1 := by
      have hfl : ((WwHi N τ : ℕ) : ℝ) ≤ 2*τ/(Real.pi*(N:ℝ)) := by
        show ((Nat.floor (2*τ/(Real.pi*(N:ℝ))) : ℕ) : ℝ) ≤ 2*τ/(Real.pi*(N:ℝ))
        exact Nat.floor_le (by positivity)
      linarith
    have hπ34 : (2:ℝ)/Real.pi ≤ 4/3 := by
      rw [div_le_div_iff₀ Real.pi_pos (by norm_num)]
      nlinarith [Real.pi_gt_three]
    have h3 : 2*τ/(Real.pi*(N:ℝ)) + 1 ≤ 3*τ/(N:ℝ) := by
      have h5 : (1:ℝ) ≤ τ/(N:ℝ) := by rw [le_div_iff₀ hNpos]; simpa using hNτ
      have hkey : (1:ℝ) ≤ (τ/(N:ℝ))*(3 - 2/Real.pi) := by nlinarith [h5, hπ34, Real.pi_pos]
      have he : 3*τ/(N:ℝ) - 2*τ/(Real.pi*(N:ℝ)) = (τ/(N:ℝ))*(3 - 2/Real.pi) := by
        field_simp
        try ring
      linarith [hkey, he]
    linarith [h1, h2, h3]
  have hXnn : (0:ℝ) ≤ C0 * (1+K) * (N:ℝ) * (1 + Real.log τ) / τ :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0nn h1K) hNpos.le) hlog) hτpos.le
  calc ‖∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
          (WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m)‖
      ≤ ∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
          ‖WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
          (C0 * (1+K) * N * (1 + Real.log τ) / τ) := Finset.sum_le_sum hper
    _ = (((Finset.Icc (WwLo N τ) (WwHi N τ)).card : ℕ) : ℝ)
          * (C0 * (1+K) * N * (1 + Real.log τ) / τ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3*τ/(N:ℝ)) * (C0 * (1+K) * N * (1 + Real.log τ) / τ) :=
        mul_le_mul_of_nonneg_right hcard hXnn
    _ = 3*C0 * (1+K) * (1 + Real.log τ) := by
        field_simp
        try ring

/-- The auxiliary form of the target theorem, with `∑' WwI` in place of the explicit integral
sum and with `WwK` unfolded. -/
theorem weighted_window_reflection_aux :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 4 ≤ N → ∀ (τ : ℝ), (N : ℝ) ≤ τ →
      ∀ (χ : ℝ → ℝ) (K : ℝ), 0 < K →
      ContDiff ℝ 3 χ → (∀ y : ℝ, 0 ≤ χ y ∧ χ y ≤ 1) →
      (∀ y : ℝ, (N : ℝ) ≤ y → y ≤ 2 * N → χ y = 1) →
      (∀ y : ℝ, y ≤ (N : ℝ) - Real.sqrt N ∨ (2 * N : ℝ) + Real.sqrt N ≤ y → χ y = 0) →
      (∀ y : ℝ, |deriv χ y| ≤ K / Real.sqrt N) →
      (∀ y : ℝ, |deriv (deriv χ) y| ≤ K / (Real.sqrt N * Real.sqrt N)) →
      ‖∑' m : ℤ, WwI χ τ m‖ ≤
        C * (1 + K) * (1 + Real.log (2 + τ)) * (1 + ‖WwK N τ‖) := by
  obtain ⟨Ct, hCtp, ht⟩ := WwI_offband_tail
  obtain ⟨Cr, hCrp, hr⟩ := residual_bound
  obtain ⟨C0, hC0p, hC0b⟩ := WwI_band_sharp
  refine ⟨3*C0 + Cr + Ct + 1, by positivity, ?_⟩
  intro N hN τ hNτ χ K hK hχd hχ0 hχ1 hχz hbdd hbdd2
  have hNpos : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hτpos : (0:ℝ) < τ := lt_of_lt_of_le hNpos hNτ
  have hτ4 : (4:ℝ) ≤ τ := le_trans (by exact_mod_cast hN) hNτ
  have hdd : ∀ y, |deriv (deriv χ) y| ≤ K / (N:ℝ) := by
    intro y
    have h := hbdd2 y
    have hs : Real.sqrt (N:ℝ) * Real.sqrt (N:ℝ) = (N:ℝ) := by
      rw [← sq, Real.sq_sqrt hNpos.le]
    rwa [hs] at h
  have hCe0 : (0:ℝ) < 3*C0 := by linarith
  have he : ‖∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
      (WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m)‖ ≤ 3*C0 * (1+K) * (1 + Real.log τ) :=
    WwI_band_sum_bound_sharp (C0 := C0) (le_of_lt hC0p) hN (χ := χ) (K := K) (le_of_lt hK) hτ4 hNτ
      (fun m hm1 hm2 hm3 => hC0b (N := N) hN hχd hχ0 hχz (K := K) (τ := τ) (le_of_lt hK)
        hbdd hτ4 (m := m) hm1 hm2 hm3)
  have hsumI : Summable (fun m : ℤ => WwI χ τ m) :=
    summable_WwI hN hχd hχ0 hχz (le_of_lt hK) hτpos hNτ hbdd hdd
  -- the band/tail split
  have hsplit : (∑ m ∈ WwBandZ N τ, WwI χ τ m)
      + ∑' (m : ↑((WwBandZ N τ : Finset ℤ) : Set ℤ)ᶜ), WwI χ τ m
      = ∑' m : ℤ, WwI χ τ m := Summable.sum_add_tsum_compl hsumI (s := WwBandZ N τ)
  -- the band sum as a `ℕ`-sum
  have hbandconv : ∑ m ∈ WwBandZ N τ, WwI χ τ m
      = ∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ), WwI χ τ (m:ℤ) := by
    rw [WwBandZ]
    rw [← sum_Icc_int_eq_sum_Icc_nat' (WwLo N τ) (WwHi N τ) (fun m : ℕ => WwI χ τ (m:ℤ))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ n)]
  -- the band decomposition
  have hbanddecomp : ∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ), WwI χ τ (m:ℤ)
      = (∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
            (WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m))
        + ∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ), WwMain (N:=N) χ τ m := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm; ring
  have hmainid := band_main_identity (N := N) (χ := χ) hN hτpos hχ1
  have hχd1 : ContDiff ℝ 1 χ := hχd.of_le (by norm_num)
  have hres := hr hN hχd1 hχ0 hχz (le_of_lt hK) hτpos hNτ hbdd
  -- norm bounds
  have htail := ht hN hχd hχ0 hχz (le_of_lt hK) hτpos hNτ hbdd hdd
  have hC0' : ‖WwC0 τ‖ = 1 := WwC0_norm τ
  have hconj : ‖(starRingEnd ℂ) (WwK N τ)‖ = ‖WwK N τ‖ := Complex.norm_conj _
  have hband : ‖∑ m ∈ WwBandZ N τ, WwI χ τ m‖
      ≤ 3*C0 * (1+K) * (1 + Real.log τ) + ‖WwK N τ‖ + Cr * (1+K) := by
    have h2 : ‖∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ), WwMain (N:=N) χ τ m‖
        ≤ ‖WwK N τ‖ + Cr * (1+K) := by
      rw [hmainid, norm_mul, hC0', one_mul]
      exact le_trans (norm_add_le _ _) (add_le_add (le_of_eq hconj) hres)
    have h3 : ‖∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
        (WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m)‖ ≤ 3*C0 * (1+K) * (1 + Real.log τ) := he
    rw [hbandconv, hbanddecomp]
    have h4 := norm_add_le (∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ),
        (WwI χ τ (m:ℤ) - WwMain (N:=N) χ τ m))
      (∑ m ∈ Finset.Icc (WwLo N τ) (WwHi N τ), WwMain (N:=N) χ τ m)
    linarith [h2, h3, h4]
  rw [← hsplit]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add hband htail) ?_
  -- final arithmetic
  have hlognn : (0:ℝ) ≤ Real.log (2 + τ) := Real.log_nonneg (by linarith)
  have hlogτ : Real.log τ ≤ Real.log (2 + τ) := Real.log_le_log hτpos (by linarith)
  have hnormK : (0:ℝ) ≤ ‖WwK N τ‖ := norm_nonneg _
  have hX1 : (1:ℝ) ≤ (1+K) := by linarith
  have hX2 : (1:ℝ) ≤ 1 + Real.log (2 + τ) := by linarith
  have hX3 : (1:ℝ) ≤ 1 + ‖WwK N τ‖ := by linarith
  have hX23 : (1:ℝ) ≤ (1 + Real.log (2+τ)) * (1 + ‖WwK N τ‖) := by
    have h := mul_le_mul hX2 hX3 (by norm_num : (0:ℝ) ≤ 1) (by linarith)
    linarith [h]
  have hX : (1:ℝ) ≤ (1+K) * (1 + Real.log (2+τ)) * (1 + ‖WwK N τ‖) := by
    have h := mul_le_mul hX1 hX23 (by norm_num : (0:ℝ) ≤ 1) (by linarith)
    linarith [h]
  have hE : 3*C0 * (1+K) * (1+Real.log τ)
      ≤ 3*C0 * ((1+K) * (1+Real.log (2+τ)) * (1+‖WwK N τ‖)) := by
    have h1 : (1+Real.log τ) ≤ (1+Real.log (2+τ)) * (1+‖WwK N τ‖) := by
      have h := mul_le_mul_of_nonneg_left hX3 (by linarith : (0:ℝ) ≤ 1 + Real.log (2+τ))
      linarith [h, hlogτ]
    have h2 : (1+K) * (1+Real.log τ) ≤ (1+K) * ((1+Real.log (2+τ)) * (1+‖WwK N τ‖)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt hCe0)
    linarith [h3]
  have hF : (Cr+Ct) * (1+K) ≤ (Cr+Ct) * ((1+K) * (1+Real.log (2+τ)) * (1+‖WwK N τ‖)) := by
    have h1 : (1+K) ≤ (1+K) * (1+Real.log (2+τ)) * (1+‖WwK N τ‖) := by
      have h := mul_le_mul_of_nonneg_left hX23 (by linarith : (0:ℝ) ≤ 1+K)
      linarith [h]
    exact mul_le_mul_of_nonneg_left h1 (by linarith)
  have hG : ‖WwK N τ‖ ≤ (1+K) * (1+Real.log (2+τ)) * (1+‖WwK N τ‖) := by
    have h2 : (1:ℝ) ≤ (1+K) * (1+Real.log (2+τ)) := by
      have h := mul_le_mul hX1 hX2 (by norm_num : (0:ℝ) ≤ 1) (by linarith)
      linarith [h]
    have h3 := mul_le_mul_of_nonneg_right h2 (by linarith : (0:ℝ) ≤ 1 + ‖WwK N τ‖)
    linarith [h3, hX3]
  have hF2 : Ct * (1+K) ≤ (Cr+Ct) * ((1+K) * (1+Real.log (2+τ)) * (1+‖WwK N τ‖)) := by
    have h1 : Ct * (1+K) ≤ (Cr+Ct)*(1+K) := by
      have h2 : (0:ℝ) ≤ Cr*(1+K) := by positivity
      linarith [h2]
    linarith [h1, hF]
  have hfin : (3*C0 + Cr + Ct) * ((1+K) * (1+Real.log (2+τ)) * (1+‖WwK N τ‖))
      + ((1+K) * (1+Real.log (2+τ)) * (1+‖WwK N τ‖))
      = (3*C0 + Cr + Ct + 1) * ((1+K) * (1+Real.log (2+τ)) * (1+‖WwK N τ‖)) := by ring
  have hgoal : (3*C0 + Cr + Ct + 1) * ((1+K) * (1+Real.log (2+τ)) * (1+‖WwK N τ‖))
      = (3*C0 + Cr + Ct + 1) * (1 + K) * (1 + Real.log (2 + τ)) * (1 + ‖WwK N τ‖) := by ring
  linarith [hE, hF2, hG, hfin, hgoal]

/-- **Weighted window reflection** (target statement). -/
theorem weighted_window_reflection :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 4 ≤ N → ∀ (τ : ℝ), (N : ℝ) ≤ τ →
      ∀ (χ : ℝ → ℝ) (K : ℝ), 0 < K →
      ContDiff ℝ 3 χ → (∀ y : ℝ, 0 ≤ χ y ∧ χ y ≤ 1) →
      (∀ y : ℝ, (N : ℝ) ≤ y → y ≤ 2 * N → χ y = 1) →
      (∀ y : ℝ, y ≤ (N : ℝ) - Real.sqrt N ∨ (2 * N : ℝ) + Real.sqrt N ≤ y → χ y = 0) →
      (∀ y : ℝ, |deriv χ y| ≤ K / Real.sqrt N) →
      (∀ y : ℝ, |deriv (deriv χ) y| ≤ K / (Real.sqrt N * Real.sqrt N)) →
      ‖∑' m : ℤ, (∫ y : ℝ, (((Real.sqrt y)⁻¹ : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((τ : ℂ) * (Real.log y : ℂ))) * (χ y : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I) * ((m : ℝ) * y)))‖
        ≤ C * (1 + K) * (1 + Real.log (2 + τ)) *
          (1 + ‖∑ k ∈ Finset.Icc (Nat.ceil (τ / (4 * Real.pi * (N : ℝ))))
                    (Nat.floor (τ / (2 * Real.pi * (N : ℝ)))),
                (k : ℂ) ^ (Complex.I * ((τ : ℝ) : ℂ)) / (Real.sqrt (k : ℝ) : ℂ)‖) := by
  obtain ⟨C, hCpos, hC⟩ := weighted_window_reflection_aux
  refine ⟨C, hCpos, ?_⟩
  intro N hN τ hNτ χ K hK hχd hχ0 hχ1 hχz hbdd hbdd2
  rw [show (∑' m : ℤ, (∫ y : ℝ, (((Real.sqrt y)⁻¹ : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((τ : ℂ) * (Real.log y : ℂ))) * (χ y : ℂ) *
            Complex.exp (-(2 * Real.pi * Complex.I) * ((m : ℝ) * y))))
      = ∑' m : ℤ, WwI χ τ m from by
    apply tsum_congr
    intro m
    rw [WwI]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    unfold WwF
    rw [Complex.ofReal_inv]]
  exact hC N hN τ hNτ χ K hK hχd hχ0 hχ1 hχz hbdd hbdd2

end
end Commons.NumberTheory.DirichletPolynomial
