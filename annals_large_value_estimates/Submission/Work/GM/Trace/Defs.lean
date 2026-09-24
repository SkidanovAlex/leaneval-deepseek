import Submission.GM.Interfaces
import Submission.LargeValues.Spectral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# Basic objects for the GM §4 / Proposition 5.1 area (`Work.GM.Trace`)

This file fixes the auxiliary definitions used by the whole `Work.GM.Trace` development
(the trace estimates of GM §4 and Proposition 5.1):

* `w2`      : `w(u)²`, the weight appearing in `h_t`.
* `hfunLog` : the `exp(i t log u)` form of `hfun t`, which agrees with `hfun t` **everywhere**
  (`hfun_eq_hfunLog`) because `w` vanishes off `[1,2]`.
* `Azero`   : the reference constant `ĥ_0(0) = ∫ w² > 0`.
* `tinyN N` : the explicit tiny error `1/N^50` used throughout.

Paper reference: `REFS/GuthMaynard_2405.20552.txt`, §4–§5.
-/

open Complex Finset MeasureTheory
open scoped BigOperators
set_option autoImplicit false

namespace Work.GM.Trace

open Submission.GM Submission.LargeValues

/-- The weight `w(u)²` of GM (4.4). -/
noncomputable def w2 (u : ℝ) : ℝ := bumpW u ^ 2

/-- The `log`-form of `h_t`: `w(u)² e^{i t log u}`.  Equal to `hfun t` everywhere. -/
noncomputable def hfunLog (t u : ℝ) : ℂ :=
  ((w2 u : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (Real.log u : ℂ))

/-- The reference constant `∫ w² = ĥ_0(0) > 0`. -/
noncomputable def Azero : ℝ := ∫ x : ℝ, bumpW x ^ 2

/-- The explicit tiny error used throughout: `N^{-50}`. -/
noncomputable def tinyN (N : ℕ) : ℝ := 1 / (N : ℝ) ^ 50

theorem w2_nonneg (u : ℝ) : 0 ≤ w2 u := pow_nonneg (bumpW_nonneg u) 2

theorem w2_eq_zero_of_notMem {u : ℝ} (hu : u ∉ Set.Icc 1 2) : w2 u = 0 := by
  rw [w2, bumpW_eq_zero_of_notMem hu, zero_pow]; norm_num

theorem w2_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w2 :=
  bumpW_contDiff.pow 2

theorem w2_le_of_mem {u : ℝ} (hu : u ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ)) : w2 u = 1 := by
  rw [w2, bumpW_eq_one hu, one_pow]

/-- `hfun t` written in terms of `exp` and `Real.log`. -/
theorem hfun_eq_hfunLog (t u : ℝ) : hfun t u = hfunLog t u := by
  rw [hfun, hfunLog, w2]
  push_cast
  rcases le_or_gt u 0 with hu | hu
  · have h1 : u ∉ Set.Icc (1 : ℝ) 2 := by
      simp only [Set.mem_Icc, not_and, not_le]; intro _; linarith
    rw [bumpW_eq_zero_of_notMem h1]; simp
  · have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hu
    rw [Complex.cpow_def_of_ne_zero hu0, Complex.ofReal_log hu.le]
    congr 1
    ring

/-- `hfun 0 = w²` as a complex-valued function. -/
theorem hfun_zero (u : ℝ) : hfun 0 u = ((bumpW u ^ 2 : ℝ) : ℂ) := by
  rw [hfun]
  simp

/-- `ĥ_0(0) = ∫ w² = Azero`. -/
theorem hhat_zero_zero : hhat 0 0 = (Azero : ℂ) := by
  rw [hhat, Real.fourier_eq]
  have h : (∫ v : ℝ, Real.fourierChar (-inner ℝ v 0) • hfun 0 v)
      = ∫ v : ℝ, ((bumpW v ^ 2 : ℝ) : ℂ) := by
    apply integral_congr_ae
    filter_upwards with v
    simp [hfun]
  rw [h]
  exact integral_ofReal

theorem Azero_nonneg : 0 ≤ Azero := integral_nonneg fun x => pow_nonneg (bumpW_nonneg x) 2

theorem Azero_pos : 0 < Azero := by
  have hcont : Continuous fun x : ℝ => bumpW x ^ 2 := bumpW_contDiff.continuous.pow 2
  have hInt : Integrable (fun x : ℝ => bumpW x ^ 2) :=
    hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_Icc
        (fun x hx => by rw [bumpW_eq_zero_of_notMem hx]; ring))
  have hne : bumpW (6 / 5 : ℝ) ^ 2 ≠ 0 := by
    rw [bumpW_eq_one (by norm_num [Set.mem_Icc])]; norm_num
  exact integral_pos_of_integrable_nonneg_nonzero hcont hInt
    (fun x => pow_nonneg (bumpW_nonneg x) 2) hne

/-- `‖hfun t u‖ = w(u)²` for `u > 0` (the phase has modulus one). -/
theorem norm_hfun_of_pos (t : ℝ) (u : ℝ) (hu : 0 < u) : ‖hfun t u‖ = bumpW u ^ 2 := by
  rw [hfun, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu]
  simp

end Work.GM.Trace
