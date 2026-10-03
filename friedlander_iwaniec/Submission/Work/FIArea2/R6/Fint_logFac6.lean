/-
# *FI* (7.10) at the zero frequency, with the discrete mean value `Fhat` of *FI* (7.7)

The target of this module is *FI* (7.10) in its round-6 form (the `FintProp` of
`R6/Inputs6.lean`): for a `C¹` majorant `F` supported in `[A,B] ⊆ [M/64, 64M]` whose *integer*
values vanish outside the annulus `[M/4,4M]` that `Work.FITop3.Fhat` sums over,

`‖Fint F γ 0 0 − Fhat·logFac6‖ ≤ C·Cder·(√M(1−γ²)log(2+1/(1−γ²)) + M^{−1/2}log(2+8√|z₁z₂|))`.

The proof chain is

* **(7.6)**, `Fint_zero_zero_eq_four_quadrant`: `Fint F γ 0 0` is real and equals
  `4∫∫_{quadrant} F(g(t₁,t₂))dt` (the object `QuadInt`);
* **(7.9)–(7.10)**, `ellInt_asymptotic` + `lemma_7_2_core`: for `γ ∈ [1/2,1)`,
  `|4∫∫_{quadrant}F(g) − (1/2)f̂(0)log(64/δ²)| ≤ 32·δ²log(64/δ²)·f̂(0)`, `δ² = 1−γ²`,
  `f̂(0) = ∫₀^∞ F(u)u^{−1/2}du` (the object `FintInt`);
* **(7.7)**, `sum_Icc_Fhat_sub_integral_le`: for a `C¹` extension `F` of `f` supported in
  `[A,B]` with `|F'| ≤ 1/M`, `|Σ_{u∈ℤ∩[A,B]} f(u)u^{−1/2} − f̂(0)| ≤ 100/M^{1/2}`;
  combined with the elementary identity `Fhat Pa f = Σ_{u∈ℤ∩[A,B]} f(u)u^{−1/2}`
  (`Fhat_eq_FhatAnn` below, which is where the hypothesis `f u ≠ 0 → M/4 ≤ u ≤ 4M` enters:
  `Fhat` sums over `[⌊M/4⌋,⌈4M⌉]` only, so without it the two sides are of different orders).

Everything is assembled with the absolute constant `C = 10^6`.
-/
import Mathlib
import Submission.Work.FIArea2.ellInt_asymptotic
import Submission.Work.FIArea2.sec9_error_Hweight
import Submission.Work.FIArea2.abs_deriv_div_sqrt_le
import Submission.Work.FIArea2.integral_psi_bound
import Submission.Work.FIArea2.integral_Ioi_eq_interval_of_support
import Submission.Work.FIArea2.sum_Icc_int_eq_sum_Ico_nat
import Submission.Work.FIArea2.sum_sub_integral_le_of_deriv_bound
import Submission.Work.FIArea2.lemma_7_6_identity
import Submission.Work.FIArea2.lemma_7_2_core
import Submission.Work.FIArea2.Fint_zero_zero_eq_four_quadrant
import Submission.Work.FIArea2.R6.integrable_comp_gQuartic
import Submission.Work.FIArea2.R6.one_sub_gamOf_sq_eq
import Submission.Work.FIArea2.R6.logFac6_eq_half_log
import Submission.Work.FITop4.Defs6

namespace Work.FIArea2.R6

open MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## 1. The two sides of the estimate -/

/-- **(7.7)**: the integral `f̂(0) = ∫₀^∞ F(u)u^{-1/2}du` of the smooth extension `F`. -/
def FintInt (F : ℝ → ℝ) : ℝ := ∫ u in Set.Ioi (0 : ℝ), F u / Real.sqrt u

/-- **(7.1)+(7.6) at `(0,0)`**: `4∫∫_{quadrant}F(g(t₁,t₂))dt`. -/
def QuadInt (F : ℝ → ℝ) (γ : ℝ) : ℝ :=
  4 * ∫ t₁ in Set.Ioi (0 : ℝ), ∫ t₂ in Set.Ioi (0 : ℝ), F (gQuartic γ (t₁, t₂))

/-- **(7.7) over the support window**: `Σ f(u)u^{-1/2}` over the integers in `[A,B]`. -/
def FhatAnn (Pa : Work.FITop.Params) (A B : ℝ) (f : ℤ → ℝ) : ℝ :=
  ∑ u ∈ Finset.Icc (⌈A⌉₊ : ℤ) (⌊B⌋₊ : ℤ), f u / Real.sqrt (u : ℝ)

/-! ## 2. Elementary facts -/

theorem FintInt_nonneg (F : ℝ → ℝ) (hF0 : ∀ u : ℝ, 0 ≤ F u) : 0 ≤ FintInt F := by
  rw [FintInt]
  exact setIntegral_nonneg measurableSet_Ioi
    (fun u _ => div_nonneg (hF0 u) (Real.sqrt_nonneg u))

private theorem gnorm_eq_zero_iff (z : GaussianInt) : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  rw [Work.FIPlan.gnorm, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero]

private theorem gnorm_mul_z1z2_ne_zero {z1 z2 : GaussianInt}
    (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0) : Work.FIPlan.gnorm (z1 * z2) ≠ 0 := by
  intro h0
  have hz : z1 * z2 = 0 := (gnorm_eq_zero_iff (z1 * z2)).mp h0
  have him : Work.FIPlan.Delta z1 z2 = 0 := by
    have h1 : star z1 * z2 = 0 := by
      rcases mul_eq_zero.mp hz with h | h
      · rw [h]; simp
      · rw [h]; simp
    rw [Work.FIPlan.Delta, h1]
    rfl
  exact hΔ (by simp [Work.FIPlan.absDelta, him])

private theorem absDelta_one_le {z1 z2 : GaussianInt} (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0) :
    (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by
  have h : (1 : ℕ) ≤ Work.FIPlan.absDelta z1 z2 := Nat.one_le_iff_ne_zero.mpr hΔ
  exact_mod_cast h

private theorem gnorm_mul_pos {z1 z2 : GaussianInt} (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0) :
    (0 : ℝ) < ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := by
  have h := gnorm_mul_z1z2_ne_zero hΔ
  exact_mod_cast Nat.pos_of_ne_zero h

private theorem log_64_div_le (y : ℝ) (hy0 : 0 < y) (hy : y ≤ 3 / 4) :
    Real.log (64 / y) ≤ 5 * Real.log (2 + 1 / y) := by
  have hpos : (0 : ℝ) < 1 + 2 * y := by linarith
  have h3 : 3 * y ≤ 1 + 2 * y := by linarith
  have h4 : (3 * y) ^ 4 ≤ (1 + 2 * y) ^ 4 := pow_le_pow_left₀ (by positivity) h3 4
  have h4' : 81 * y ^ 4 ≤ (1 + 2 * y) ^ 4 := by
    have h := h4
    rw [mul_pow] at h
    norm_num at h
    exact h
  have h5 : (1 + 2 * y) ^ 4 ≤ (1 + 2 * y) ^ 5 := by
    rw [pow_succ]
    nlinarith [pow_nonneg hpos.le 4]
  have hkey : (64 : ℝ) * y ^ 4 ≤ (1 + 2 * y) ^ 5 := by nlinarith [h4', h5]
  have hy5 : (0 : ℝ) < y ^ 5 := pow_pos hy0 5
  have hineq : 64 / y ≤ (2 + 1 / y) ^ 5 := by
    have h2 : (2 + 1 / y) ^ 5 = (1 + 2 * y) ^ 5 / y ^ 5 := by
      field_simp
      ring
    rw [h2, le_div_iff₀ hy5]
    have hcalc : 64 / y * y ^ 5 = 64 * y ^ 4 := by field_simp
    rw [hcalc]
    exact hkey
  calc Real.log (64 / y) ≤ Real.log ((2 + 1 / y) ^ 5) :=
        Real.log_le_log (by positivity) hineq
    _ = 5 * Real.log (2 + 1 / y) := by rw [Real.log_pow]; push_cast; ring

/-! ## 3. Scaling of support, size and derivative by `Cder` -/

private theorem hasCompactSupport_div_const {F : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hcs : HasCompactSupport F) : HasCompactSupport (fun u : ℝ => F u / c) := by
  rw [hasCompactSupport_def] at hcs ⊢
  have hsupp : Function.support (fun u : ℝ => F u / c) = Function.support F := by
    ext u
    simp [div_ne_zero_iff, hc]
  rwa [hsupp]

private theorem div_const_supp {F : ℝ → ℝ} {A B c : ℝ} (hc : c ≠ 0)
    (h : ∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B) :
    ∀ u : ℝ, F u / c ≠ 0 → A ≤ u ∧ u ≤ B :=
  fun u hu => h u (div_ne_zero_iff.mp hu).1

private theorem div_const_bound {F : ℝ → ℝ} {c : ℝ} (hc : 1 ≤ c)
    (h : ∀ u : ℝ, |F u| ≤ c) : ∀ u : ℝ, |F u / c| ≤ 2 := by
  intro u
  have hcpos : 0 < c := by linarith
  rw [abs_div, abs_of_pos hcpos, div_le_iff₀ hcpos]
  nlinarith [h u]

private theorem div_const_deriv {F : ℝ → ℝ} {M c : ℝ} (hc : 0 < c) (hM : 0 < M)
    (h : ∀ u : ℝ, |deriv F u| ≤ c / M) :
    ∀ u : ℝ, |deriv (fun u : ℝ => F u / c) u| ≤ 1 / M := by
  intro u
  rw [deriv_div_const (c := F) c, abs_div, abs_of_pos hc, div_le_iff₀ hc]
  have h' := h u
  have hcM : (1 / M) * c = c / M := by ring
  rw [hcM]
  exact h'

private theorem integral_div_const_div_sqrt (F : ℝ → ℝ) {c : ℝ} (hc : c ≠ 0) :
    ∫ u in Set.Ioi (0 : ℝ), (F u / c) / Real.sqrt u = FintInt F / c := by
  rw [FintInt, ← MeasureTheory.integral_div]
  exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => by ring)

/-! ## 4. The analytic inputs -/

/-- **(6.8) at `(0,0)` is the real quadrant integral (7.6).** -/
theorem Fint_eq_quadInt (F : ℝ → ℝ) (γ : ℝ) (hF : Continuous F)
    (hcs : HasCompactSupport F) (hγ : |γ| < 1) :
    Fint F γ 0 0 = ((QuadInt F γ : ℝ) : ℂ) := by
  have hInt : Integrable (fun t : ℝ × ℝ => F (gQuartic γ t)) :=
    integrable_comp_gQuartic F hF hcs γ hγ
  have h1 : Fint F γ 0 0 = ((∫ t : ℝ × ℝ, F (gQuartic γ t) : ℝ) : ℂ) := by
    rw [Fint_zero_zero]
    exact integral_ofReal
  have h2 : (Fint F γ 0 0).re = QuadInt F γ := Fint_zero_zero_eq_four_quadrant F γ hInt
  have h3 : (∫ t : ℝ × ℝ, F (gQuartic γ t)) = QuadInt F γ := by
    rw [h1] at h2
    simpa [QuadInt] using h2
  rw [h1, h3]

/-- **(7.10)** in the shape used by the assembly. -/
theorem QuadInt_sub_half_le (F : ℝ → ℝ) (γ : ℝ) (hF0 : ∀ u : ℝ, 0 ≤ F u)
    (hFc : Continuous F) (hfsupp : ∀ u : ℝ, u ≤ 0 → F u = 0)
    (hcc : HasCompactSupport F) (hγ0 : 1 / 2 ≤ γ) (hγ1 : γ < 1) :
    |QuadInt F γ - (1 / 2) * FintInt F * Real.log (64 / (1 - γ ^ 2))|
      ≤ 32 * |FintInt F| * ((1 - γ ^ 2) * Real.log (64 / (1 - γ ^ 2))) := by
  simp only [QuadInt, FintInt]
  refine le_trans (lemma_7_2_core F γ hF0 hFc hfsupp hcc hγ0 hγ1) (le_of_eq ?_)
  ring

/-- `f̂(0) ≤ 512·Cder·√M` for `F` supported in `[A,B] ⊆ [M/64,64M]`, `|F| ≤ Cder`. -/
theorem FintInt_le (Pa : Work.FITop.Params) (A B Cder : ℝ) (F : ℝ → ℝ) (hFc : Continuous F)
    (hF0 : ∀ u : ℝ, 0 ≤ F u) (hFbd : ∀ u : ℝ, |F u| ≤ Cder)
    (hfsupp : ∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hA : Pa.M / 64 ≤ A) (hB : B ≤ 64 * Pa.M) (hM : 1 ≤ Pa.M) (hCder : 0 ≤ Cder) :
    FintInt F ≤ 512 * Cder * Real.sqrt Pa.M := by
  have hMpos : 0 < Pa.M := by linarith
  have hApos : 0 < A := by linarith
  have hsM : 0 < Real.sqrt Pa.M := Real.sqrt_pos.mpr hMpos
  rw [FintInt]
  by_cases hAB : A ≤ B
  · have hEq : ∫ u in Set.Ioi (0 : ℝ), F u / Real.sqrt u = ∫ u in A..B, F u / Real.sqrt u :=
      integral_Ioi_eq_interval_of_support (g := fun u => F u / Real.sqrt u) (a := A) (b := B)
        (L := A) (U := B) hApos hAB hApos.le le_rfl le_rfl
        (fun x hx => by
          have hxF : F x = 0 := by
            by_contra h
            exact absurd (hfsupp x h).1 (not_le.mpr hx)
          simp [hxF])
        (fun x hx => by
          have hxF : F x = 0 := by
            by_contra h
            exact absurd (hfsupp x h).2 (not_le.mpr hx)
          simp [hxF])
    rw [hEq]
    have hbound : ∀ x ∈ Set.Icc A B, F x / Real.sqrt x ≤ 8 * Cder / Real.sqrt Pa.M := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hApos hx.1
      have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
      have h1 : F x ≤ Cder := le_trans (le_abs_self _) (hFbd x)
      have h2 : 1 / Real.sqrt x ≤ 8 / Real.sqrt Pa.M := by
        have hx64 : Pa.M ≤ 64 * x := by nlinarith [hA, hx.1, hMpos]
        have hsqrt : Real.sqrt Pa.M ≤ 8 * Real.sqrt x := by
          calc Real.sqrt Pa.M ≤ Real.sqrt (64 * x) := Real.sqrt_le_sqrt hx64
            _ = 8 * Real.sqrt x := by
                rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64)]
                norm_num
        rw [div_le_iff₀ hsx, div_mul_eq_mul_div, le_div_iff₀ hsM]
        linarith
      calc F x / Real.sqrt x ≤ Cder / Real.sqrt x := by gcongr
        _ = Cder * (1 / Real.sqrt x) := by ring
        _ ≤ Cder * (8 / Real.sqrt Pa.M) := by gcongr
        _ = 8 * Cder / Real.sqrt Pa.M := by ring
    have hcont : ContinuousOn (fun x : ℝ => F x / Real.sqrt x) (Set.Icc A B) :=
      hFc.continuousOn.div Real.continuous_sqrt.continuousOn
        (fun x hx => (Real.sqrt_pos.mpr (lt_of_lt_of_le hApos hx.1)).ne')
    have hint : IntervalIntegrable (fun x : ℝ => F x / Real.sqrt x) volume A B := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hAB]
      exact hcont
    have hmono : ∫ x in A..B, F x / Real.sqrt x ≤ ∫ x in A..B, 8 * Cder / Real.sqrt Pa.M :=
      intervalIntegral.integral_mono_on hAB hint intervalIntegrable_const hbound
    have hconst : ∫ x in A..B, 8 * Cder / Real.sqrt Pa.M
        = (8 * Cder / Real.sqrt Pa.M) * (B - A) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    calc ∫ x in A..B, F x / Real.sqrt x ≤ ∫ x in A..B, 8 * Cder / Real.sqrt Pa.M := hmono
      _ = (8 * Cder / Real.sqrt Pa.M) * (B - A) := hconst
      _ ≤ 512 * Cder * Real.sqrt Pa.M := by
          have hBA : B - A ≤ 64 * Pa.M := by linarith
          have hsq : Real.sqrt Pa.M * Real.sqrt Pa.M = Pa.M := by
            rw [← pow_two]
            exact Real.sq_sqrt hMpos.le
          rw [div_mul_eq_mul_div, div_le_iff₀ hsM]
          have hrewrite : (512 * Cder * Real.sqrt Pa.M) * Real.sqrt Pa.M
              = 512 * Cder * Pa.M := by rw [mul_assoc, hsq]
          rw [hrewrite]
          nlinarith [hBA, hCder]
  · have hBA : B < A := not_le.mp hAB
    have hzero : ∀ u : ℝ, F u = 0 := by
      intro u
      by_contra hcon
      have h1 := (hfsupp u hcon).1
      have h2 := (hfsupp u hcon).2
      linarith
    have hz : ∫ u in Set.Ioi (0 : ℝ), F u / Real.sqrt u = 0 := by simp [hzero]
    rw [hz]
    nlinarith [Real.sqrt_nonneg Pa.M, hCder]

/-! ## 4a. The discretisation error (7.7) for the general support window

(7.7) compares the discrete mean value `Σ_{u∈ℤ∩[A,B]}f(u)u^{-1/2}` with the integral
`f̂(0) = ∫₀^∞F(u)u^{-1/2}du`.  Euler–Maclaurin on the unit intervals
(`Work.FIArea2.sum_sub_integral_le_of_deriv_bound`), with the `L¹`-bound
`∫_L^{U+1}(1/(M√x) + 1/(x√x)) ≤ 2√(U+1)/M + 2/√L` (`Work.FIArea2.integral_psi_bound`) for the
derivative of `x ↦ F x/√x` under `|F'| ≤ 1/M`, `|F| ≤ 2` (`Work.FIArea2.abs_deriv_div_sqrt_le`),
gives the interior error.  The two partial unit intervals `[A,⌈A⌉₊]` and `[⌊B⌋₊+1,B]` at the ends
contribute `≤ 32/√M`, because `|F x|/√x ≤ 2/√A ≤ 16/√M` there and `⌈A⌉₊ - A < 1`,
`⌊B⌋₊ + 1 - B ≤ 1`. -/

/-- Arithmetic: `2√x/M + 2/√L + 32/√M ≤ 100/√M` for `M ≥ 1`, `0 ≤ x ≤ 64M+1`, `L ≥ M/64`. -/
private lemma disc_num_bound (M x L : ℝ) (hM : 1 ≤ M) (hx0 : 0 ≤ x) (hx : x ≤ 64 * M + 1)
    (hL0 : 0 < L) (hL : M / 64 ≤ L) :
    2 * Real.sqrt x / M + 2 / Real.sqrt L + 32 / Real.sqrt M ≤ 100 / Real.sqrt M := by
  have hMpos : 0 < M := by linarith
  have hsM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have key : 2 * Real.sqrt x / M + 2 / Real.sqrt L + 32 / Real.sqrt M
      = (2 * Real.sqrt x / Real.sqrt M + 2 * Real.sqrt M / Real.sqrt L + 32)
        / Real.sqrt M := by
    have h2 : Real.sqrt M ^ 2 = M := by rw [sq, Real.mul_self_sqrt hMpos.le]
    field_simp
    ring_nf
    rw [h2]
    ring
  rw [key]
  refine div_le_div_of_nonneg_right ?_ hsM.le
  have h1 : 2 * Real.sqrt x / Real.sqrt M ≤ 18 := by
    have hxM : Real.sqrt x ≤ 9 * Real.sqrt M := by
      calc Real.sqrt x ≤ Real.sqrt (81 * M) := by
            apply Real.sqrt_le_sqrt
            nlinarith
        _ = Real.sqrt 81 * Real.sqrt M := Real.sqrt_mul (by norm_num) M
        _ = 9 * Real.sqrt M := by norm_num
    rw [div_le_iff₀ hsM]
    linarith
  have h2' : 2 * Real.sqrt M / Real.sqrt L ≤ 16 := by
    have hML : Real.sqrt M ≤ 8 * Real.sqrt L := by
      calc Real.sqrt M ≤ Real.sqrt (64 * L) := by
            apply Real.sqrt_le_sqrt
            linarith
        _ = Real.sqrt 64 * Real.sqrt L := Real.sqrt_mul (by norm_num) L
        _ = 8 * Real.sqrt L := by norm_num
    rw [div_le_iff₀ hsL]
    linarith
  linarith

/-- **(7.7) for the general support window** `[A,B] ⊆ [M/64,64M]`: the discrete mean value over
the integers of `[A,B]` differs from the integral `f̂(0)` by at most `100/√M`. -/
theorem FhatAnn_discretisation (Pa : Work.FITop.Params) (A B : ℝ) (F : ℝ → ℝ) (f : ℤ → ℝ)
    (hA : Pa.M / 64 ≤ A) (hB : B ≤ 64 * Pa.M) (hM : 1 ≤ Pa.M)
    (hFc : ContDiff ℝ 1 F) (hcs : HasCompactSupport F)
    (hFint : ∀ n : ℤ, F (n : ℝ) = f n)
    (hF0 : ∀ u : ℝ, 0 ≤ F u) (hFbd : ∀ u : ℝ, |F u| ≤ 2)
    (hfsupp : ∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hFder : ∀ u : ℝ, |deriv F u| ≤ 1 / Pa.M) :
    |(∑ u ∈ Finset.Icc (⌈A⌉₊ : ℤ) (⌊B⌋₊ : ℤ), f u / Real.sqrt (u : ℝ))
        - ∫ u in Set.Ioi (0 : ℝ), F u / Real.sqrt u| ≤ 100 / Real.sqrt Pa.M := by
  have hMpos : 0 < Pa.M := by linarith
  have hApos : 0 < A := lt_of_lt_of_le (by linarith : (0 : ℝ) < Pa.M / 64) hA
  have hsMpos : 0 < Real.sqrt Pa.M := Real.sqrt_pos.mpr hMpos
  have hFdiff : ∀ x : ℝ, DifferentiableAt ℝ F x :=
    fun x => (hFc.differentiable (by norm_num)).differentiableAt
  set g : ℝ → ℝ := fun x => F x / Real.sqrt x with hgdef
  by_cases hAB : A ≤ B
  · -- ## the window is nonempty: compare with the interval integral over `[A,B]`
    have hInt : (∫ u in Set.Ioi (0 : ℝ), F u / Real.sqrt u) = ∫ x in A..B, g x := by
      rw [hgdef]
      exact integral_Ioi_eq_interval_of_support (a := A) (b := B) (L := A) (U := B)
        hApos hAB hApos.le le_rfl le_rfl
        (fun x hx => by
          have hxF : F x = 0 := by
            by_contra hcon
            exact absurd (hfsupp x hcon).1 (not_le.mpr hx)
          simp [hxF])
        (fun x hx => by
          have hxF : F x = 0 := by
            by_contra hcon
            exact absurd (hfsupp x hcon).2 (not_le.mpr hx)
          simp [hxF])
    have hsum_ico : (∑ u ∈ Finset.Icc (⌈A⌉₊ : ℤ) (⌊B⌋₊ : ℤ), f u / Real.sqrt (u : ℝ))
        = ∑ k ∈ Finset.Ico (⌈A⌉₊) (⌊B⌋₊ + 1), g (k : ℝ) := by
      rw [Work.FIArea2.sum_Icc_int_eq_sum_Ico_nat (fun u : ℤ => f u / Real.sqrt (u : ℝ))
        (⌈A⌉₊) (⌊B⌋₊)]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have h1 : ((k : ℤ) : ℝ) = (k : ℝ) := by push_cast; ring
      show f (k : ℤ) / Real.sqrt ((k : ℤ) : ℝ) = g (k : ℝ)
      rw [hgdef]
      simp only [h1, ← hFint (k : ℤ)]
    have hcontA : ContinuousOn g (Set.Ici A) := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hApos hx
      rw [hgdef]
      exact ((hFdiff x).div (Real.hasDerivAt_sqrt hxpos.ne').differentiableAt
        (Real.sqrt_pos.mpr hxpos).ne').continuousAt.continuousWithinAt
    have hIint : ∀ a b : ℝ, A ≤ a → A ≤ b → IntervalIntegrable g volume a b := by
      intro a b ha hb
      apply ContinuousOn.intervalIntegrable
      refine hcontA.mono ?_
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨hx1, _⟩ | ⟨hx1, _⟩
      · exact le_trans ha hx1
      · exact le_trans hb hx1
    have hLt : (⌈A⌉₊ : ℝ) < A + 1 := Nat.ceil_lt_add_one hApos.le
    have hUt : B < (⌊B⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one B
    have hradius : 2 / Real.sqrt A ≤ 16 / Real.sqrt Pa.M := by
      have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hApos
      have hMA : Real.sqrt Pa.M ≤ 8 * Real.sqrt A := by
        calc Real.sqrt Pa.M ≤ Real.sqrt (64 * A) := by
              apply Real.sqrt_le_sqrt
              linarith
          _ = Real.sqrt 64 * Real.sqrt A := Real.sqrt_mul (by norm_num) A
          _ = 8 * Real.sqrt A := by norm_num
      rw [div_le_iff₀ hsA]
      have hrw : (16 / Real.sqrt Pa.M) * Real.sqrt A = 16 * Real.sqrt A / Real.sqrt Pa.M := by
        ring
      rw [hrw, le_div_iff₀ hsMpos]
      linarith
    by_cases hLU : ⌈A⌉₊ ≤ ⌊B⌋₊
    · -- ## Euler–Maclaurin in the interior plus the boundary correction
      have hL1 : 1 ≤ ⌈A⌉₊ := Nat.one_le_ceil_iff.mpr hApos
      have hLR : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
      have hUR : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (le_trans hApos.le hAB)
      have hdiff : ∀ x ∈ Set.Icc (⌈A⌉₊ : ℝ) ((⌊B⌋₊ : ℝ) + 1), DifferentiableAt ℝ g x := by
        intro x hx
        have hx1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hL1) hx.1
        have hxpos : 0 < x := lt_of_lt_of_le one_pos hx1
        rw [hgdef]
        exact (hFdiff x).div (Real.hasDerivAt_sqrt hxpos.ne').differentiableAt
          (Real.sqrt_pos.mpr hxpos).ne'
      have hbound : ∀ x ∈ Set.Icc (⌈A⌉₊ : ℝ) ((⌊B⌋₊ : ℝ) + 1),
          |deriv g x| ≤ 1 / (Pa.M * Real.sqrt x) + 1 / (x * Real.sqrt x) := by
        intro x hx
        have hx1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hL1) hx.1
        rw [hgdef]
        exact Work.FIArea2.abs_deriv_div_sqrt_le hFc hMpos hFder hFbd hx1
      have hψint : ∀ k ∈ Finset.Ico (⌈A⌉₊) (⌊B⌋₊ + 1),
          IntervalIntegrable (fun x : ℝ => 1 / (Pa.M * Real.sqrt x) + 1 / (x * Real.sqrt x))
            volume (k : ℝ) ((k : ℝ) + 1) := by
        intro k hk
        rw [Finset.mem_Ico] at hk
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_trans hL1 hk.1)
        have hstep : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le hstep]
        refine ContinuousOn.add ?_ ?_
        · refine ContinuousOn.div continuousOn_const ?_ ?_
          · exact continuousOn_const.mul Real.continuous_sqrt.continuousOn
          · intro x hx
            have hxpos : 0 < x := lt_of_lt_of_le one_pos (le_trans hk1 hx.1)
            exact mul_ne_zero hMpos.ne' (Real.sqrt_pos.mpr hxpos).ne'
        · refine ContinuousOn.div continuousOn_const ?_ ?_
          · exact continuousOn_id.mul Real.continuous_sqrt.continuousOn
          · intro x hx
            have hxpos : 0 < x := lt_of_lt_of_le one_pos (le_trans hk1 hx.1)
            exact mul_ne_zero hxpos.ne' (Real.sqrt_pos.mpr hxpos).ne'
      have hEM := Work.FIArea2.sum_sub_integral_le_of_deriv_bound hLU hdiff hbound hψint
      have hL1R : (1 : ℝ) ≤ (⌈A⌉₊ : ℝ) := by exact_mod_cast hL1
      have hLU_R : (⌈A⌉₊ : ℝ) ≤ (⌊B⌋₊ : ℝ) := by exact_mod_cast hLU
      have hpsi := Work.FIArea2.integral_psi_bound hMpos hL1R
        (by linarith : (⌈A⌉₊ : ℝ) ≤ (⌊B⌋₊ : ℝ) + 1)
      have hgap : |(∫ x in (⌈A⌉₊ : ℝ)..((⌊B⌋₊ : ℝ) + 1), g x) - ∫ x in A..B, g x|
          ≤ 32 / Real.sqrt Pa.M := by
        have hgapid : (∫ x in (⌈A⌉₊ : ℝ)..((⌊B⌋₊ : ℝ) + 1), g x) - ∫ x in A..B, g x
            = (∫ x in B..((⌊B⌋₊ : ℝ) + 1), g x) - ∫ x in A..(⌈A⌉₊ : ℝ), g x := by
          have e1 := intervalIntegral.integral_add_adjacent_intervals
            (hIint A (⌈A⌉₊ : ℝ) le_rfl hLR) (hIint (⌈A⌉₊ : ℝ) B hLR hAB)
          have e2 := intervalIntegral.integral_add_adjacent_intervals
            (hIint (⌈A⌉₊ : ℝ) B hLR hAB) (hIint B ((⌊B⌋₊ : ℝ) + 1) hAB (by linarith))
          linarith [e1, e2]
        have hb1 : |∫ x in A..(⌈A⌉₊ : ℝ), g x| ≤ 16 / Real.sqrt Pa.M := by
          have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (f := g)
            (a := A) (b := (⌈A⌉₊ : ℝ)) (C := 2 / Real.sqrt A) (fun x hx => by
              rw [Set.uIoc_of_le hLR] at hx
              have hxpos : 0 < x := lt_of_lt_of_le hApos hx.1.le
              have hsx : Real.sqrt A ≤ Real.sqrt x := Real.sqrt_le_sqrt hx.1.le
              rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg x)]
              calc |F x| / Real.sqrt x ≤ 2 / Real.sqrt x :=
                    div_le_div_of_nonneg_right (hFbd x) (Real.sqrt_nonneg x)
                _ ≤ 2 / Real.sqrt A := by
                    rw [div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)
                      (Real.sqrt_pos.mpr hxpos) (Real.sqrt_pos.mpr hApos)]
                    exact hsx)
          rw [Real.norm_eq_abs] at hnorm
          have hLA : |(⌈A⌉₊ : ℝ) - A| ≤ 1 := by
            rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (⌈A⌉₊ : ℝ) - A)]
            linarith
          calc |∫ x in A..(⌈A⌉₊ : ℝ), g x| ≤ (2 / Real.sqrt A) * |(⌈A⌉₊ : ℝ) - A| := hnorm
            _ ≤ (2 / Real.sqrt A) * 1 := by
                refine mul_le_mul_of_nonneg_left hLA ?_
                positivity
            _ ≤ 16 / Real.sqrt Pa.M := by
                rw [mul_one]; exact hradius
        have hb2 : |∫ x in B..((⌊B⌋₊ : ℝ) + 1), g x| ≤ 16 / Real.sqrt Pa.M := by
          have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (f := g)
            (a := B) (b := (⌊B⌋₊ : ℝ) + 1) (C := 2 / Real.sqrt B) (fun x hx => by
              rw [Set.uIoc_of_le (le_of_lt hUt)] at hx
              have hxpos : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le hApos hAB) hx.1.le
              have hsx : Real.sqrt B ≤ Real.sqrt x := Real.sqrt_le_sqrt hx.1.le
              rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg x)]
              calc |F x| / Real.sqrt x ≤ 2 / Real.sqrt x :=
                    div_le_div_of_nonneg_right (hFbd x) (Real.sqrt_nonneg x)
                _ ≤ 2 / Real.sqrt B := by
                    rw [div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)
                      (Real.sqrt_pos.mpr hxpos)
                      (Real.sqrt_pos.mpr (lt_of_lt_of_le hApos hAB))]
                    exact hsx)
          rw [Real.norm_eq_abs] at hnorm
          have hBUB : |(⌊B⌋₊ : ℝ) + 1 - B| ≤ 1 := by
            rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (⌊B⌋₊ : ℝ) + 1 - B)]
            linarith
          have hradB : 2 / Real.sqrt B ≤ 16 / Real.sqrt Pa.M := by
            have hbA : 2 / Real.sqrt B ≤ 2 / Real.sqrt A := by
              rw [div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)
                (Real.sqrt_pos.mpr (lt_of_lt_of_le hApos hAB)) (Real.sqrt_pos.mpr hApos)]
              exact Real.sqrt_le_sqrt hAB
            linarith [hradius]
          calc |∫ x in B..((⌊B⌋₊ : ℝ) + 1), g x|
              ≤ (2 / Real.sqrt B) * |(⌊B⌋₊ : ℝ) + 1 - B| := hnorm
            _ ≤ (2 / Real.sqrt B) * 1 := by
                refine mul_le_mul_of_nonneg_left hBUB ?_
                positivity
            _ ≤ 16 / Real.sqrt Pa.M := by rw [mul_one]; exact hradB
        rw [hgapid]
        have hsub := abs_sub_le (∫ x in B..((⌊B⌋₊ : ℝ) + 1), g x) 0
          (∫ x in A..(⌈A⌉₊ : ℝ), g x)
        rw [sub_zero, zero_sub, abs_neg] at hsub
        calc |(∫ x in B..((⌊B⌋₊ : ℝ) + 1), g x) - ∫ x in A..(⌈A⌉₊ : ℝ), g x|
            ≤ |∫ x in B..((⌊B⌋₊ : ℝ) + 1), g x| + |∫ x in A..(⌈A⌉₊ : ℝ), g x| := hsub
          _ ≤ 16 / Real.sqrt Pa.M + 16 / Real.sqrt Pa.M := add_le_add hb2 hb1
          _ = 32 / Real.sqrt Pa.M := by ring
      have htri : |(∑ k ∈ Finset.Ico (⌈A⌉₊) (⌊B⌋₊ + 1), g (k : ℝ)) - ∫ x in A..B, g x|
          ≤ |(∑ k ∈ Finset.Ico (⌈A⌉₊) (⌊B⌋₊ + 1), g (k : ℝ))
              - ∫ x in (⌈A⌉₊ : ℝ)..((⌊B⌋₊ : ℝ) + 1), g x|
            + |(∫ x in (⌈A⌉₊ : ℝ)..((⌊B⌋₊ : ℝ) + 1), g x) - ∫ x in A..B, g x| := by
        have h := abs_add_le
          ((∑ k ∈ Finset.Ico (⌈A⌉₊) (⌊B⌋₊ + 1), g (k : ℝ))
            - ∫ x in (⌈A⌉₊ : ℝ)..((⌊B⌋₊ : ℝ) + 1), g x)
          ((∫ x in (⌈A⌉₊ : ℝ)..((⌊B⌋₊ : ℝ) + 1), g x) - ∫ x in A..B, g x)
        rwa [show ((∑ k ∈ Finset.Ico (⌈A⌉₊) (⌊B⌋₊ + 1), g (k : ℝ))
              - ∫ x in (⌈A⌉₊ : ℝ)..((⌊B⌋₊ : ℝ) + 1), g x)
            + ((∫ x in (⌈A⌉₊ : ℝ)..((⌊B⌋₊ : ℝ) + 1), g x) - ∫ x in A..B, g x)
            = (∑ k ∈ Finset.Ico (⌈A⌉₊) (⌊B⌋₊ + 1), g (k : ℝ)) - ∫ x in A..B, g x
            by ring] at h
      rw [hsum_ico, hInt]
      refine le_trans (le_trans (le_trans htri (add_le_add hEM hgap)) (add_le_add hpsi le_rfl)) ?_
      exact disc_num_bound Pa.M ((⌊B⌋₊ : ℝ) + 1) (⌈A⌉₊ : ℝ) hM (by positivity)
        (by have := Nat.floor_le (le_trans hApos.le hAB); linarith)
        (by exact_mod_cast Nat.ceil_pos.mpr hApos)
        (le_trans hA (Nat.le_ceil A))
    · -- ## no integer in `[A,B]`: the sum vanishes and `B - A < 1`
      have hempty : Finset.Icc (⌈A⌉₊ : ℤ) (⌊B⌋₊ : ℤ) = ∅ := by
        rw [Finset.Icc_eq_empty_iff]
        intro h
        exact hLU (by exact_mod_cast h)
      have hsum0 : (∑ u ∈ Finset.Icc (⌈A⌉₊ : ℤ) (⌊B⌋₊ : ℤ), f u / Real.sqrt (u : ℝ)) = 0 := by
        rw [hempty, Finset.sum_empty]
      have hBA1 : B - A < 1 := by
        have h1 : (⌊B⌋₊ : ℤ) < (⌈A⌉₊ : ℤ) := by exact_mod_cast not_le.mp hLU
        have h2 : (⌊B⌋₊ : ℝ) + 1 ≤ (⌈A⌉₊ : ℝ) := by
          have h2' : (⌊B⌋₊ : ℤ) + 1 ≤ (⌈A⌉₊ : ℤ) := Int.add_one_le_iff.mpr h1
          exact_mod_cast h2'
        linarith [hLt, hUt, h2]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (f := g)
        (a := A) (b := B) (C := 2 / Real.sqrt A) (fun x hx => by
          rw [Set.uIoc_of_le hAB] at hx
          have hxpos : 0 < x := lt_of_lt_of_le hApos hx.1.le
          have hsx : Real.sqrt A ≤ Real.sqrt x := Real.sqrt_le_sqrt hx.1.le
          rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.sqrt_nonneg x)]
          calc |F x| / Real.sqrt x ≤ 2 / Real.sqrt x :=
                div_le_div_of_nonneg_right (hFbd x) (Real.sqrt_nonneg x)
            _ ≤ 2 / Real.sqrt A := by
                rw [div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)
                  (Real.sqrt_pos.mpr hxpos) (Real.sqrt_pos.mpr hApos)]
                exact hsx)
      rw [Real.norm_eq_abs] at hnorm
      rw [hInt, hsum0, zero_sub, abs_neg]
      have hBA0 : 0 ≤ B - A := by linarith
      calc |∫ x in A..B, g x| ≤ (2 / Real.sqrt A) * |B - A| := hnorm
        _ = (2 / Real.sqrt A) * (B - A) := by rw [abs_of_nonneg hBA0]
        _ ≤ (2 / Real.sqrt A) * 1 := by
            refine mul_le_mul_of_nonneg_left hBA1.le ?_
            positivity
        _ = 2 / Real.sqrt A := by ring
        _ ≤ 16 / Real.sqrt Pa.M := hradius
        _ ≤ 100 / Real.sqrt Pa.M := by
            rw [div_le_div_iff_of_pos_right hsMpos]
            norm_num
  · -- ## the support window is empty: `F ≡ 0`, hence `f ≡ 0`
    have hzero : ∀ u : ℝ, F u = 0 := by
      intro u
      by_contra hcon
      have h1 := (hfsupp u hcon).1
      have h2 := (hfsupp u hcon).2
      linarith
    have hsum0 : (∑ u ∈ Finset.Icc (⌈A⌉₊ : ℤ) (⌊B⌋₊ : ℤ), f u / Real.sqrt (u : ℝ)) = 0 := by
      refine Finset.sum_eq_zero (fun u _ => ?_)
      rw [← hFint u, hzero, zero_div]
    have hint0 : (∫ u in Set.Ioi (0 : ℝ), F u / Real.sqrt u) = 0 := by
      simp [hzero]
    rw [hsum0, hint0, sub_zero, abs_zero]
    exact div_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- **(7.7) with the general support window, scaled to `Cder`**: the discrete mean value
`Σ_{u∈ℤ∩[A,B]}f(u)u^{-1/2}` differs from the integral `f̂(0)` by at most `100·Cder/√M`.  The
unscaled form is `FhatAnn_discretisation`. -/
theorem FhatAnn_sub_integral_le (Pa : Work.FITop.Params) (A B Cder : ℝ) (F : ℝ → ℝ)
    (f : ℤ → ℝ) (hFc : ContDiff ℝ 1 F) (hcs : HasCompactSupport F)
    (hFint : ∀ n : ℤ, F (n : ℝ) = f n) (hF0 : ∀ u : ℝ, 0 ≤ F u)
    (hFbd : ∀ u : ℝ, |F u| ≤ Cder) (hfsupp : ∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hFder : ∀ u : ℝ, |deriv F u| ≤ Cder / Pa.M)
    (hA : Pa.M / 64 ≤ A) (hB : B ≤ 64 * Pa.M) (hM : 1 ≤ Pa.M) (hCder : 1 ≤ Cder) :
    |FhatAnn Pa A B f - FintInt F| ≤ 100 * Cder / Real.sqrt Pa.M := by
  have hCpos : 0 < Cder := by linarith
  have hCne : Cder ≠ 0 := ne_of_gt hCpos
  have hMpos : 0 < Pa.M := by linarith
  have h1 := FhatAnn_discretisation Pa A B (fun u : ℝ => F u / Cder)
    (fun n : ℤ => f n / Cder) hA hB hM (hFc.div_const Cder)
    (hasCompactSupport_div_const hCne hcs)
    (fun n => by simp [hFint n]) (fun u => div_nonneg (hF0 u) hCpos.le)
    (div_const_bound hCder hFbd) (div_const_supp hCne hfsupp)
    (div_const_deriv hCpos hMpos hFder)
  have hsum : (∑ u ∈ Finset.Icc (⌈A⌉₊ : ℤ) (⌊B⌋₊ : ℤ),
        (fun n : ℤ => f n / Cder) u / Real.sqrt (u : ℝ))
      = (∑ u ∈ Finset.Icc (⌈A⌉₊ : ℤ) (⌊B⌋₊ : ℤ), f u / Real.sqrt (u : ℝ)) / Cder := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  have hFhatAnn : (∑ u ∈ Finset.Icc (⌈A⌉₊ : ℤ) (⌊B⌋₊ : ℤ), f u / Real.sqrt (u : ℝ))
      = FhatAnn Pa A B f := rfl
  rw [hsum, hFhatAnn, integral_div_const_div_sqrt F hCne] at h1
  have hsplit : FhatAnn Pa A B f / Cder - FintInt F / Cder
      = (FhatAnn Pa A B f - FintInt F) / Cder := by ring
  rw [hsplit, abs_div, abs_of_pos hCpos, div_le_iff₀ hCpos] at h1
  have hfin : (100 / Real.sqrt Pa.M) * Cder = 100 * Cder / Real.sqrt Pa.M := by ring
  rw [hfin] at h1
  exact h1

/-- `logFac6 ≥ 0`. -/
theorem logFac6_nonneg (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0) :
    0 ≤ Work.FITop4.logFac6 z1 z2 := by
  have hd2 : 1 - (gamOf z1 z2) ^ 2
      = (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ^ 2
        / ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := one_sub_gamOf_sq_eq z1 z2 hΔ
  have hpos : 0 < 1 - (gamOf z1 z2) ^ 2 := by
    rw [hd2]
    have h1 : (0 : ℝ) < (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ^ 2 := by
      have := absDelta_one_le hΔ
      positivity
    exact div_pos h1 (gnorm_mul_pos hΔ)
  have hle1 : 1 - (gamOf z1 z2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (gamOf z1 z2)]
  have hge : (1 : ℝ) ≤ 64 / (1 - (gamOf z1 z2) ^ 2) := by
    rw [le_div_iff₀ hpos]
    nlinarith
  have hlog : 0 ≤ Real.log (64 / (1 - (gamOf z1 z2) ^ 2)) := Real.log_nonneg hge
  rw [logFac6_eq_half_log z1 z2 hΔ]
  linarith

/-- `logFac6 ≤ log(2 + 8√|z₁z₂|)`. -/
theorem logFac6_le (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0) :
    Work.FITop4.logFac6 z1 z2
      ≤ Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))) := by
  rw [Work.FITop4.logFac6]
  have hG : (0 : ℝ) < ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := gnorm_mul_pos hΔ
  have hD1 : (1 : ℝ) ≤ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := absDelta_one_le hΔ
  have hDpos : (0 : ℝ) < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by linarith
  have hsG : 0 < Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := Real.sqrt_pos.mpr hG
  refine Real.log_le_log ?h1 ?h2
  · positivity
  · rw [div_le_iff₀ hDpos]
    nlinarith [Real.sqrt_nonneg (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)), hD1, hsG]

/-! ## 5. The assembly -/

/-- Ordered-field step: `|a - S·L6| ≤ El + L6·K` from `|a - (1/2)b·L64| ≤ El`,
`|b - S| ≤ K`, `L6 = (1/2)L64 ≥ 0`. -/
private theorem abs_sub_mul_le' {a b S L64 L6 El K : ℝ} (hL6 : L6 = (1 / 2) * L64)
    (hL6nn : 0 ≤ L6) (h1 : |a - (1 / 2) * b * L64| ≤ El) (h2 : |b - S| ≤ K) :
    |a - S * L6| ≤ El + L6 * K := by
  have hL64nn : 0 ≤ L64 := by linarith [hL6, hL6nn]
  have h3 : |(1 / 2) * b * L64 - S * L6| = L6 * |b - S| := by
    rw [hL6]
    rw [show (1 / 2) * b * L64 - S * ((1 / 2) * L64) = ((1 / 2) * L64) * (b - S) by ring]
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (1 / 2) * L64)]
  have h4 : a - S * L6 = (a - (1 / 2) * b * L64) + ((1 / 2) * b * L64 - S * L6) := by ring
  calc |a - S * L6| = |(a - (1 / 2) * b * L64) + ((1 / 2) * b * L64 - S * L6)| := by rw [h4]
    _ ≤ |a - (1 / 2) * b * L64| + |(1 / 2) * b * L64 - S * L6| := abs_add_le _ _
    _ ≤ El + L6 * |b - S| := by linarith [h1, h3]
    _ ≤ El + L6 * K := by linarith [mul_le_mul_of_nonneg_left h2 hL6nn]

/-- **The assembly.**  Bound `‖Fint F γ 0 0 - S·logFac6‖` from (7.10), the discretisation error of
`S` and the size of `f̂(0)`. -/
theorem Fint_sub_sum_logFac6_le (Pa : Work.FITop.Params) (Cder S : ℝ) (F : ℝ → ℝ)
    (z1 z2 : GaussianInt) (hFc : Continuous F) (hcs : HasCompactSupport F)
    (hF0 : ∀ u : ℝ, 0 ≤ F u) (hfsupp0 : ∀ u : ℝ, u ≤ 0 → F u = 0)
    (hγ0 : 1 / 2 ≤ gamOf z1 z2) (hγ1 : gamOf z1 z2 < 1)
    (hΔ : Work.FIPlan.absDelta z1 z2 ≠ 0)
    (hQ : |QuadInt F (gamOf z1 z2) - (1 / 2) * FintInt F
            * Real.log (64 / (1 - (gamOf z1 z2) ^ 2))|
          ≤ 32 * |FintInt F| * ((1 - (gamOf z1 z2) ^ 2)
            * Real.log (64 / (1 - (gamOf z1 z2) ^ 2))))
    (hdisc : |S - FintInt F| ≤ 100 * Cder / Real.sqrt Pa.M)
    (hBle : FintInt F ≤ 512 * Cder * Real.sqrt Pa.M) (hCpos : 0 < Cder) (hMpos : 0 < Pa.M) :
    ‖Fint F (gamOf z1 z2) 0 0 - ((S : ℝ) : ℂ) * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)‖
      ≤ 1000000 * Cder * (Real.sqrt Pa.M * (1 - (gamOf z1 z2) ^ 2)
            * Real.log (2 + 1 / (1 - (gamOf z1 z2) ^ 2))
          + (Real.sqrt Pa.M)⁻¹
            * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)))) := by
  have hBnn : 0 ≤ FintInt F := FintInt_nonneg F hF0
  have hγabs : |gamOf z1 z2| < 1 := abs_lt.mpr ⟨by linarith, hγ1⟩
  have hFintQ : Fint F (gamOf z1 z2) 0 0 = ((QuadInt F (gamOf z1 z2) : ℝ) : ℂ) :=
    Fint_eq_quadInt F (gamOf z1 z2) hFc hcs hγabs
  have hL6 : Work.FITop4.logFac6 z1 z2
      = (1 / 2) * Real.log (64 / (1 - (gamOf z1 z2) ^ 2)) := logFac6_eq_half_log z1 z2 hΔ
  have hL6nn : 0 ≤ Work.FITop4.logFac6 z1 z2 := logFac6_nonneg z1 z2 hΔ
  have hL6le : Work.FITop4.logFac6 z1 z2
      ≤ Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))) :=
    logFac6_le z1 z2 hΔ
  have hQ' : |QuadInt F (gamOf z1 z2) - (1 / 2) * FintInt F
        * Real.log (64 / (1 - (gamOf z1 z2) ^ 2))|
      ≤ 32 * FintInt F * ((1 - (gamOf z1 z2) ^ 2)
          * Real.log (64 / (1 - (gamOf z1 z2) ^ 2))) := by
    rw [abs_of_nonneg hBnn] at hQ
    exact hQ
  have hstep := abs_sub_mul_le' (a := QuadInt F (gamOf z1 z2)) (b := FintInt F) (S := S)
    (L64 := Real.log (64 / (1 - (gamOf z1 z2) ^ 2))) (L6 := Work.FITop4.logFac6 z1 z2)
    (El := 32 * FintInt F * ((1 - (gamOf z1 z2) ^ 2)
      * Real.log (64 / (1 - (gamOf z1 z2) ^ 2))))
    (K := 100 * Cder / Real.sqrt Pa.M) hL6 hL6nn hQ' (by rw [abs_sub_comm]; exact hdisc)
  -- elementary facts about `1-γ²`
  have hd2 : 1 - (gamOf z1 z2) ^ 2
      = (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ^ 2
        / ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) := one_sub_gamOf_sq_eq z1 z2 hΔ
  have hd2pos : 0 < 1 - (gamOf z1 z2) ^ 2 := by
    rw [hd2]
    have h1 : (0 : ℝ) < (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ^ 2 := by
      have := absDelta_one_le hΔ
      positivity
    exact div_pos h1 (gnorm_mul_pos hΔ)
  have hd2nn : 0 ≤ 1 - (gamOf z1 z2) ^ 2 := le_of_lt hd2pos
  have hd2le : 1 - (gamOf z1 z2) ^ 2 ≤ 3 / 4 := by nlinarith [hγ0, sq_nonneg (gamOf z1 z2)]
  have hL64nn : 0 ≤ Real.log (64 / (1 - (gamOf z1 z2) ^ 2)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hd2pos]
    linarith
  have hlogAnn : 0 ≤ Real.log (2 + 1 / (1 - (gamOf z1 z2) ^ 2)) := by
    refine Real.log_nonneg ?_
    have h : 0 < 1 / (1 - (gamOf z1 z2) ^ 2) := one_div_pos.mpr hd2pos
    linarith
  have hlogBnn : 0 ≤ Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))) := by
    refine Real.log_nonneg ?_
    nlinarith [Real.sqrt_nonneg (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))]
  have hfold : (1 - (gamOf z1 z2) ^ 2) * Real.log (64 / (1 - (gamOf z1 z2) ^ 2))
      ≤ 5 * ((1 - (gamOf z1 z2) ^ 2)
        * Real.log (2 + 1 / (1 - (gamOf z1 z2) ^ 2))) := by
    have h := log_64_div_le (1 - (gamOf z1 z2) ^ 2) hd2pos hd2le
    calc (1 - (gamOf z1 z2) ^ 2) * Real.log (64 / (1 - (gamOf z1 z2) ^ 2))
        ≤ (1 - (gamOf z1 z2) ^ 2)
          * (5 * Real.log (2 + 1 / (1 - (gamOf z1 z2) ^ 2))) :=
          mul_le_mul_of_nonneg_left h hd2nn
      _ = 5 * ((1 - (gamOf z1 z2) ^ 2)
          * Real.log (2 + 1 / (1 - (gamOf z1 z2) ^ 2))) := by ring
  -- the two pieces
  have hP1 : 32 * FintInt F * ((1 - (gamOf z1 z2) ^ 2)
        * Real.log (64 / (1 - (gamOf z1 z2) ^ 2)))
      ≤ 81920 * Cder * (Real.sqrt Pa.M * (1 - (gamOf z1 z2) ^ 2)
        * Real.log (2 + 1 / (1 - (gamOf z1 z2) ^ 2))) := by
    have h1 : 32 * FintInt F ≤ 32 * (512 * Cder * Real.sqrt Pa.M) :=
      mul_le_mul_of_nonneg_left hBle (by norm_num)
    have h2 : 32 * FintInt F * ((1 - (gamOf z1 z2) ^ 2)
          * Real.log (64 / (1 - (gamOf z1 z2) ^ 2)))
        ≤ 32 * (512 * Cder * Real.sqrt Pa.M) * ((1 - (gamOf z1 z2) ^ 2)
          * Real.log (64 / (1 - (gamOf z1 z2) ^ 2))) :=
      mul_le_mul_of_nonneg_right h1 (mul_nonneg hd2nn hL64nn)
    have h3 : (0 : ℝ) ≤ 32 * (512 * Cder * Real.sqrt Pa.M) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hCpos.le)
        (Real.sqrt_nonneg _))
    calc 32 * FintInt F * ((1 - (gamOf z1 z2) ^ 2)
          * Real.log (64 / (1 - (gamOf z1 z2) ^ 2)))
        ≤ 32 * (512 * Cder * Real.sqrt Pa.M) * ((1 - (gamOf z1 z2) ^ 2)
          * Real.log (64 / (1 - (gamOf z1 z2) ^ 2))) := h2
      _ ≤ 32 * (512 * Cder * Real.sqrt Pa.M) * (5 * ((1 - (gamOf z1 z2) ^ 2)
          * Real.log (2 + 1 / (1 - (gamOf z1 z2) ^ 2)))) :=
          mul_le_mul_of_nonneg_left hfold h3
      _ = 81920 * Cder * (Real.sqrt Pa.M * (1 - (gamOf z1 z2) ^ 2)
          * Real.log (2 + 1 / (1 - (gamOf z1 z2) ^ 2))) := by ring
  have hP2 : Work.FITop4.logFac6 z1 z2 * (100 * Cder / Real.sqrt Pa.M)
      ≤ 100 * Cder * ((Real.sqrt Pa.M)⁻¹
        * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)))) := by
    have hb : 0 ≤ 100 * Cder / Real.sqrt Pa.M :=
      div_nonneg (by linarith) (Real.sqrt_nonneg _)
    calc Work.FITop4.logFac6 z1 z2 * (100 * Cder / Real.sqrt Pa.M)
        ≤ Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)))
          * (100 * Cder / Real.sqrt Pa.M) := mul_le_mul_of_nonneg_right hL6le hb
      _ = 100 * Cder * ((Real.sqrt Pa.M)⁻¹
          * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)))) := by ring
  -- the norm is an absolute value of reals
  have hnorm : ‖Fint F (gamOf z1 z2) 0 0
        - ((S : ℝ) : ℂ) * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)‖
      = |QuadInt F (gamOf z1 z2) - S * Work.FITop4.logFac6 z1 z2| := by
    have hc : ∀ x : ℝ, ‖((x : ℝ) : ℂ)‖ = |x| := fun x => by
      have h2 : ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
        ring
      nlinarith [norm_nonneg ((x : ℝ) : ℂ), abs_nonneg x, sq_abs x,
        sq_nonneg (‖((x : ℝ) : ℂ)‖ - |x|)]
    rw [hFintQ, ← Complex.ofReal_mul, ← Complex.ofReal_sub, hc]
  rw [hnorm]
  refine le_trans hstep ?_
  have hXnn : 0 ≤ Real.sqrt Pa.M * (1 - (gamOf z1 z2) ^ 2)
      * Real.log (2 + 1 / (1 - (gamOf z1 z2) ^ 2)) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hd2nn) hlogAnn
  have hYnn : 0 ≤ (Real.sqrt Pa.M)⁻¹
      * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))) :=
    mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hlogBnn
  nlinarith [hP1, hP2, hXnn, hYnn, hCpos,
    mul_nonneg hCpos.le hXnn, mul_nonneg hCpos.le hYnn]

/-! ## 6. The discrete mean value `Fhat` over the support window

`Work.FITop3.Fhat` sums `f(u)u^{-1/2}` over the integers of `[⌊M/4⌋,⌈4M⌉]` only.  Under the
hypothesis `f u ≠ 0 → M/4 ≤ u ≤ 4M` (which says that the *integer* values of the majorant are
confined to that annulus, even though its support spreads over `[M/64,64M]`) that range contains
every nonzero summand, and the support hypothesis `F u ≠ 0 → A ≤ u ≤ B` says that the integers of
`[A,B]` do too; so both sums reduce to the sum over `Icc ⌈A⌉₊ ⌊B⌋₊ ∩ Icc ⌊M/4⌋₊ ⌈4M⌉₊`. -/

/-- `⌈c⌉₊ ≤ u` for an integer `u ≥ c ≥ 0`. -/
private lemma ceil_le_intCast {c : ℝ} {u : ℤ} (hc : 0 ≤ c) (h : c ≤ (u : ℝ)) :
    (⌈c⌉₊ : ℤ) ≤ u := by
  have hu0 : (0 : ℤ) ≤ u := by exact_mod_cast (le_trans hc h)
  have hcast : (u.toNat : ℝ) = (u : ℝ) := by
    rw [← Int.cast_natCast (R := ℝ) u.toNat, Int.toNat_of_nonneg hu0]
  have hce : ⌈c⌉₊ ≤ u.toNat := by
    rw [Nat.ceil_le, hcast]
    exact h
  have h2 : (⌈c⌉₊ : ℤ) ≤ (u.toNat : ℤ) := by exact_mod_cast hce
  rwa [Int.toNat_of_nonneg hu0] at h2

/-- `u ≤ ⌊c⌋₊` for an integer `u ≤ c`. -/
private lemma le_floor_intCast {c : ℝ} {u : ℤ} (h : (u : ℝ) ≤ c) : u ≤ (⌊c⌋₊ : ℤ) := by
  have h1 := Nat.lt_floor_add_one c
  have h2 : (u : ℝ) < (((⌊c⌋₊ : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
  have h3 : u < (⌊c⌋₊ : ℤ) + 1 := Int.cast_lt.mp h2
  exact Int.lt_add_one_iff.mp h3

/-- `u ≤ ⌈c⌉₊` for an integer `u ≤ c`. -/
private lemma intCast_le_ceil {c : ℝ} {u : ℤ} (h : (u : ℝ) ≤ c) : u ≤ (⌈c⌉₊ : ℤ) := by
  have h1 := Nat.le_ceil c
  have h2 : (u : ℝ) ≤ ((⌈c⌉₊ : ℤ) : ℝ) := by push_cast; linarith
  exact_mod_cast h2

/-- `⌊c⌋₊ ≤ u` for an integer `u ≥ c ≥ 0`. -/
private lemma floor_le_intCast {c : ℝ} {u : ℤ} (hc : 0 ≤ c) (h : c ≤ (u : ℝ)) :
    (⌊c⌋₊ : ℤ) ≤ u := by
  have h1 : ((⌊c⌋₊ : ℤ) : ℝ) ≤ (u : ℝ) := by
    push_cast
    exact le_trans (Nat.floor_le hc) h
  exact_mod_cast h1

/-- **`Work.FITop3.Fhat` is the discrete mean value over the support window** `[A,B]`. -/
theorem Fhat_eq_FhatAnn (Pa : Work.FITop.Params) (A B : ℝ) (f : ℤ → ℝ)
    (hA : Pa.M / 64 ≤ A) (hM : 1 ≤ Pa.M)
    (hvanish : ∀ u : ℤ, f u ≠ 0 → A ≤ (u : ℝ) ∧ (u : ℝ) ≤ B)
    (hnarrow : ∀ u : ℤ, f u ≠ 0 → Pa.M / 4 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 4 * Pa.M) :
    Work.FITop3.Fhat Pa f = FhatAnn Pa A B f := by
  have hApos : 0 < A := by linarith
  have hMpos : 0 < Pa.M := by linarith
  have hmem : ∀ u : ℤ, f u ≠ 0 →
      u ∈ Finset.Icc (⌊Pa.M / 4⌋₊ : ℤ) (⌈4 * Pa.M⌉₊ : ℤ) ∧
      u ∈ Finset.Icc (⌈A⌉₊ : ℤ) (⌊B⌋₊ : ℤ) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hnarrow u hu
    obtain ⟨hu3, hu4⟩ := hvanish u hu
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨floor_le_intCast (by positivity) hu1, intCast_le_ceil hu2⟩
    · rw [Finset.mem_Icc]
      exact ⟨ceil_le_intCast hApos.le hu3, le_floor_intCast hu4⟩
  have hS : Work.FITop3.Fhat Pa f
      = ∑ u ∈ Finset.Icc (⌊Pa.M / 4⌋₊ : ℤ) (⌈4 * Pa.M⌉₊ : ℤ),
          f u / Real.sqrt (u : ℝ) := rfl
  have hT : FhatAnn Pa A B f
      = ∑ u ∈ Finset.Icc (⌈A⌉₊ : ℤ) (⌊B⌋₊ : ℤ), f u / Real.sqrt (u : ℝ) := rfl
  rw [hS, hT]
  refine (Finset.sum_subset (Finset.inter_subset_left) ?_).symm.trans
    (Finset.sum_subset (Finset.inter_subset_right) ?_)
  · intro x hxS hxnot
    by_cases hx : f x = 0
    · simp [hx]
    · exact absurd (hmem x hx).2 (fun hxT => hxnot (Finset.mem_inter.mpr ⟨hxS, hxT⟩))
  · intro x hxT hxnot
    by_cases hx : f x = 0
    · simp [hx]
    · exact absurd (hmem x hx).1 (fun hxS => hxnot (Finset.mem_inter.mpr ⟨hxS, hxT⟩))

/-! ## 7. The requested estimate -/

/-- `Fhat Pa f` (the discrete mean value of (7.7)) differs from `f̂(0) = FintInt F` by at most
`100·Cder/√M`.  This is `FhatAnn_sub_integral_le` with the discrete sum replaced by `Fhat`
(`Fhat_eq_FhatAnn`). -/
theorem Fhat_sub_integral_le_gen (Pa : Work.FITop.Params) (A B Cder : ℝ) (F : ℝ → ℝ)
    (f : ℤ → ℝ) (hA : Pa.M / 64 ≤ A) (hB : B ≤ 64 * Pa.M) (hM : 1 ≤ Pa.M)
    (hCder : 1 ≤ Cder) (hFc : ContDiff ℝ 1 F) (hcs : HasCompactSupport F)
    (hFint : ∀ n : ℤ, F (n : ℝ) = f n)
    (hfv : ∀ u : ℤ, f u ≠ 0 → Pa.M / 4 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 4 * Pa.M)
    (hF0 : ∀ u : ℝ, 0 ≤ F u) (hFbd : ∀ u : ℝ, |F u| ≤ Cder)
    (hfsupp : ∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B)
    (hFder : ∀ u : ℝ, |deriv F u| ≤ Cder / Pa.M) :
    |Work.FITop3.Fhat Pa f - FintInt F| ≤ 100 * Cder / Real.sqrt Pa.M := by
  have hvanish : ∀ u : ℤ, f u ≠ 0 → A ≤ (u : ℝ) ∧ (u : ℝ) ≤ B := by
    intro u hu
    exact hfsupp (u : ℝ) (by rw [hFint u]; exact hu)
  have h1 := FhatAnn_sub_integral_le Pa A B Cder F f hFc hcs hFint hF0 hFbd hfsupp hFder
    hA hB hM hCder
  have h2 := Fhat_eq_FhatAnn Pa A B f hA hM hvanish hfv
  rwa [← h2] at h1

theorem Fint_logFac6 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Pa : Work.FITop.Params) (A B Cder : ℝ) (F : ℝ → ℝ) (f : ℤ → ℝ)
        (z1 z2 : GaussianInt),
        Pa.M / 64 ≤ A → B ≤ 64 * Pa.M → 1 ≤ Cder → 1 ≤ Pa.M →
        ContDiff ℝ 1 F → HasCompactSupport F → (∀ n : ℤ, F (n : ℝ) = f n) →
        (∀ u : ℤ, f u ≠ 0 → Pa.M / 4 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 4 * Pa.M) →
        (∀ u : ℝ, 0 ≤ F u) → (∀ u : ℝ, |F u| ≤ Cder) →
        (∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B) →
        (∀ u : ℝ, |deriv F u| ≤ Cder / Pa.M) →
        (1 / 2 : ℝ) ≤ Work.FIArea2.gamOf z1 z2 → Work.FIArea2.gamOf z1 z2 < 1 →
        Work.FIPlan.absDelta z1 z2 ≠ 0 →
        ‖Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
            - ((Work.FITop3.Fhat Pa f : ℝ) : ℂ) * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)‖
          ≤ C * Cder * (Real.sqrt Pa.M * (1 - Work.FIArea2.gamOf z1 z2 ^ 2)
                * Real.log (2 + 1 / (1 - Work.FIArea2.gamOf z1 z2 ^ 2))
              + (Real.sqrt Pa.M)⁻¹
                * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)))) := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro Pa A B Cder F f z1 z2 hA hB hCder hM hFc hcs hFint hfv hF0 hFbd hfsupp hFder
    hγ0 hγ1 hΔ
  have hCpos : 0 < Cder := by linarith
  have hMpos : 0 < Pa.M := by linarith
  have hFcont : Continuous F := hFc.continuous
  have hsupp0 : ∀ u : ℝ, u ≤ 0 → F u = 0 := by
    intro u hu
    by_contra hcon
    have h1 : Pa.M / 64 ≤ u := le_trans hA (hfsupp u hcon).1
    have h2 : (0 : ℝ) < Pa.M / 64 := by linarith
    linarith
  exact Fint_sub_sum_logFac6_le Pa Cder (Work.FITop3.Fhat Pa f) F z1 z2 hFcont hcs hF0 hsupp0
    hγ0 hγ1 hΔ (QuadInt_sub_half_le F (gamOf z1 z2) hF0 hFcont hsupp0 hcs hγ0 hγ1)
    (Fhat_sub_integral_le_gen Pa A B Cder F f hA hB hM hCder hFc hcs hFint hfv hF0 hFbd
      hfsupp hFder)
    (FintInt_le Pa A B Cder F hFcont hF0 hFbd hfsupp hA hB hM hCpos.le) hCpos hMpos

end

end Work.FIArea2.R6
