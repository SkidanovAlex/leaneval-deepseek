import Mathlib
import Submission.Work.ZeroDensity.Ingham.Defs
import Submission.Work.ZeroDensity.Montgomery.integralMulLeSqrtMulSqrt
import Submission.Work.ZeroDensity.Ingham.dirPolySepMeanSquareTN
import Submission.Work.ZeroDensity.Ingham.zetaTailDivisorLogWeightSelf

set_option maxHeartbeats 1000000

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-! ### scaffolding: the two analytic inputs (to be replaced by the delegated modules) -/

/-! ### the Dirichlet polynomial and its real-direction derivative -/

private noncomputable def etaP (N : ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, c n * (n : ℂ) ^ (-s)

private noncomputable def etaPd (N : ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (-(Real.log (n : ℝ) : ℂ)) * c n * (n : ℂ) ^ (-s)

private lemma natCast_ne_zero_of_mem {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) : (n : ℂ) ≠ 0 := by
  have h : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  exact_mod_cast h

private lemma etaP_hasDerivAt (N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    ∀ u : ℝ, HasDerivAt (fun v : ℝ => etaP N c ((v : ℂ) + (t : ℂ) * Complex.I))
      (etaPd N c ((u : ℂ) + (t : ℂ) * Complex.I)) u := by
  intro u
  unfold etaP etaPd
  rw [show (fun v : ℝ => ∑ n ∈ Finset.Icc 1 N,
        c n * (n : ℂ) ^ (-((v : ℂ) + (t : ℂ) * Complex.I)))
      = (∑ n ∈ Finset.Icc 1 N, fun v : ℝ =>
          c n * (n : ℂ) ^ (-((v : ℂ) + (t : ℂ) * Complex.I)))
      from by funext v; rw [Finset.sum_apply]]
  apply HasDerivAt.sum
  intro n hn
  have hnz : (n : ℂ) ≠ 0 := natCast_ne_zero_of_mem hn
  have h1 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u :=
    (Complex.ofRealCLM.hasFDerivAt (x := u)).hasDerivAt
  have h2 : HasDerivAt (fun v : ℝ => (v : ℂ) + (t : ℂ) * Complex.I) 1 u := by
    simpa using h1.add_const ((t : ℂ) * Complex.I)
  have h3 : HasDerivAt (fun v : ℝ => -((v : ℂ) + (t : ℂ) * Complex.I)) (-1) u := by
    simpa [Pi.neg_def] using h2.neg
  have h4 : HasDerivAt (fun v : ℝ => Complex.log (n : ℂ) * -((v : ℂ) + (t : ℂ) * Complex.I))
      (Complex.log (n : ℂ) * -1) u := h3.const_mul (Complex.log (n : ℂ))
  have h5 : HasDerivAt
      (fun v : ℝ => Complex.exp (Complex.log (n : ℂ) * -((v : ℂ) + (t : ℂ) * Complex.I)))
      (Complex.exp (Complex.log (n : ℂ) * -((u : ℂ) + (t : ℂ) * Complex.I))
        * (Complex.log (n : ℂ) * -1)) u := h4.cexp
  have h6 := h5.const_mul (c n)
  have hfun : (fun v : ℝ => c n *
        Complex.exp (Complex.log (n : ℂ) * -((v : ℂ) + (t : ℂ) * Complex.I)))
      = (fun v : ℝ => c n * (n : ℂ) ^ (-((v : ℂ) + (t : ℂ) * Complex.I))) := by
    funext v; rw [Complex.cpow_def_of_ne_zero hnz]
  rw [hfun] at h6
  have hderiv : c n * (Complex.exp (Complex.log (n : ℂ) * -((u : ℂ) + (t : ℂ) * Complex.I))
        * (Complex.log (n : ℂ) * -1))
      = (-(Real.log (n : ℝ) : ℂ)) * c n * (n : ℂ) ^ (-((u : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [← Complex.cpow_def_of_ne_zero hnz, ← Complex.natCast_log]
    ring
  rw [hderiv] at h6
  exact h6

private lemma continuous_etaPd (N : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    Continuous (fun u : ℝ => etaPd N c ((u : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold etaPd
  apply continuous_finsetSum
  intro n hn
  have hnz : (n : ℂ) ≠ 0 := natCast_ne_zero_of_mem hn
  have hc : Continuous (fun u : ℝ => (n : ℂ) ^ (-((u : ℂ) + (t : ℂ) * Complex.I))) := by
    have heq : (fun u : ℝ => (n : ℂ) ^ (-((u : ℂ) + (t : ℂ) * Complex.I)))
        = fun u : ℝ => Complex.exp (Complex.log (n : ℂ) * -((u : ℂ) + (t : ℂ) * Complex.I)) := by
      funext u; rw [Complex.cpow_def_of_ne_zero hnz]
    rw [heq]
    exact Complex.continuous_exp.comp (by fun_prop)
  exact continuous_const.mul hc

/-! ### the per-point interpolation (fixed vs varying real part) -/

private lemma etaP_norm_sq_le (N : ℕ) (c : ℕ → ℂ) (σ : ℝ) (z : ℂ)
    (hσ0 : 0 ≤ σ) (hσz : σ ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖etaP N c z‖ ^ 2
      ≤ 2 * ‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)‖ ^ 2
        + 2 * ∫ u in σ..(1 : ℝ), ‖etaPd N c ((u : ℂ) + (z.im : ℂ) * Complex.I)‖ ^ 2 := by
  have hσ1 : σ ≤ 1 := le_trans hσz hz1
  set hr : ℝ → ℝ := fun u => ‖etaPd N c ((u : ℂ) + (z.im : ℂ) * Complex.I)‖ with hrh
  have hrc : Continuous hr := by rw [hrh]; exact (continuous_etaPd N c z.im).norm
  have hr0 : ∀ u : ℝ, 0 ≤ hr u := fun u => norm_nonneg _
  have hderiv : ∀ u ∈ Set.uIcc σ z.re,
      HasDerivAt (fun v : ℝ => etaP N c ((v : ℂ) + (z.im : ℂ) * Complex.I))
        (etaPd N c ((u : ℂ) + (z.im : ℂ) * Complex.I)) u :=
    fun u _ => etaP_hasDerivAt N c z.im u
  have hint : IntervalIntegrable (fun u : ℝ => etaPd N c ((u : ℂ) + (z.im : ℂ) * Complex.I))
      MeasureTheory.volume σ z.re := (continuous_etaPd N c z.im).intervalIntegrable σ z.re
  have hFTC : ∫ u in σ..z.re, etaPd N c ((u : ℂ) + (z.im : ℂ) * Complex.I)
      = etaP N c z - etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Complex.re_add_im]
  have htri : ‖etaP N c z‖ ≤ ‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)‖
      + ∫ u in σ..z.re, hr u := by
    have h1 : ‖etaP N c z‖ = ‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)
        + ∫ u in σ..z.re, etaPd N c ((u : ℂ) + (z.im : ℂ) * Complex.I)‖ := by
      rw [hFTC]; ring_nf
    rw [h1]
    refine le_trans (norm_add_le _ _) (add_le_add le_rfl ?_)
    have h2 := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) hσz
      (f := fun u : ℝ => etaPd N c ((u : ℂ) + (z.im : ℂ) * Complex.I))
    simpa only [hrh] using h2
  have hmono : ∫ u in σ..z.re, hr u ≤ ∫ u in σ..(1 : ℝ), hr u :=
    intervalIntegral.integral_mono_interval le_rfl hσz hz1
      (Filter.Eventually.of_forall (fun u => hr0 u)) (hrc.intervalIntegrable σ 1)
  have hcs0 := Work.ZeroDensity.Montgomery.integralMulLeSqrtMulSqrt (f := hr)
    (k := fun _ : ℝ => (1 : ℝ)) hrc continuous_const hr0 (fun _ => zero_le_one) hσ1
  have hleft : ∫ u in σ..(1 : ℝ), hr u * (1 : ℝ) = ∫ u in σ..(1 : ℝ), hr u := by
    simp
  have hInt1 : ∫ u in σ..(1 : ℝ), (1 : ℝ) ^ 2 = 1 - σ := by
    rw [show (fun u : ℝ => (1:ℝ)^2) = fun _ : ℝ => (1:ℝ) from by funext u; norm_num,
      intervalIntegral.integral_const]
    simp
  have hsqrt1 : Real.sqrt (∫ u in σ..(1 : ℝ), (1 : ℝ) ^ 2) ≤ 1 := by
    rw [hInt1]
    calc Real.sqrt (1 - σ) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      _ = 1 := Real.sqrt_one
  have hstep : ∫ u in σ..(1 : ℝ), hr u ≤ Real.sqrt (∫ u in σ..(1 : ℝ), hr u ^ 2) := by
    rw [hleft] at hcs0
    calc ∫ u in σ..(1 : ℝ), hr u
        ≤ Real.sqrt (∫ u in σ..(1 : ℝ), hr u ^ 2) * Real.sqrt (∫ u in σ..(1 : ℝ), (1 : ℝ) ^ 2) := hcs0
      _ ≤ Real.sqrt (∫ u in σ..(1 : ℝ), hr u ^ 2) * 1 :=
          mul_le_mul_of_nonneg_left hsqrt1 (Real.sqrt_nonneg _)
      _ = Real.sqrt (∫ u in σ..(1 : ℝ), hr u ^ 2) := mul_one _
  have hsq : (∫ u in σ..(1 : ℝ), hr u) ^ 2 ≤ ∫ u in σ..(1 : ℝ), hr u ^ 2 := by
    have hnn1 : 0 ≤ ∫ u in σ..(1 : ℝ), hr u :=
      intervalIntegral.integral_nonneg hσ1 (fun u _ => hr0 u)
    have hnn2 : 0 ≤ ∫ u in σ..(1 : ℝ), hr u ^ 2 :=
      intervalIntegral.integral_nonneg hσ1 (fun u _ => sq_nonneg _)
    have hsqrtnn : 0 ≤ Real.sqrt (∫ u in σ..(1 : ℝ), hr u ^ 2) := Real.sqrt_nonneg _
    have hsqeq : (Real.sqrt (∫ u in σ..(1 : ℝ), hr u ^ 2)) ^ 2
        = ∫ u in σ..(1 : ℝ), hr u ^ 2 := Real.sq_sqrt hnn2
    nlinarith [hstep, hnn1, hsqrtnn, hsqeq]
  have hnn1 : 0 ≤ ∫ u in σ..z.re, hr u :=
    intervalIntegral.integral_nonneg hσz (fun u _ => hr0 u)
  have hcB : (∫ u in σ..z.re, hr u) ^ 2 ≤ (∫ u in σ..(1 : ℝ), hr u) ^ 2 := by
    simpa using pow_le_pow_left₀ hnn1 hmono 2
  have hfin : ‖etaP N c z‖ ^ 2
      ≤ 2 * ‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)‖ ^ 2
        + 2 * (∫ u in σ..(1 : ℝ), hr u) ^ 2 := by
    have h1 : ‖etaP N c z‖ ^ 2
        ≤ (‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)‖ + ∫ u in σ..z.re, hr u) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    have h2 : (‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)‖ + ∫ u in σ..z.re, hr u) ^ 2
        ≤ 2 * ‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)‖ ^ 2
          + 2 * (∫ u in σ..z.re, hr u) ^ 2 := by
      nlinarith [sq_nonneg (‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)‖
        - ∫ u in σ..z.re, hr u)]
    linarith [h1, h2, hcB]
  calc ‖etaP N c z‖ ^ 2
      ≤ 2 * ‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)‖ ^ 2
        + 2 * (∫ u in σ..(1 : ℝ), hr u) ^ 2 := hfin
    _ ≤ 2 * ‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)‖ ^ 2
        + 2 * ∫ u in σ..(1 : ℝ), hr u ^ 2 := by linarith
    _ = 2 * ‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)‖ ^ 2
        + 2 * ∫ u in σ..(1 : ℝ), ‖etaPd N c ((u : ℂ) + (z.im : ℂ) * Complex.I)‖ ^ 2 := by
        rw [hrh]

/-! ### elementary absorption of the polylogarithms -/

private lemma logPowAbsorb (a : ℝ) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → (Real.log (2 * T)) ^ a ≤ C * T ^ ε := by
  set δ : ℝ := ε / (2 * a) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hmul : δ * a = ε / 2 := by rw [hδdef]; field_simp
  refine ⟨(2:ℝ) ^ (ε / 2) / δ ^ a, by positivity, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hx : (0 : ℝ) ≤ 2 * T := by linarith
  have hlog0 : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
  have hlog : Real.log (2 * T) ≤ (2 * T) ^ δ / δ := Real.log_le_rpow_div hx hδpos
  have hpow : (Real.log (2 * T)) ^ a ≤ ((2 * T) ^ δ / δ) ^ a :=
    Real.rpow_le_rpow hlog0 hlog ha.le
  have hsplit : ((2 * T) ^ δ / δ) ^ a = (2:ℝ) ^ (ε / 2) * T ^ (ε / 2) / δ ^ a := by
    have h2T : (0 : ℝ) ≤ 2 * T := by linarith
    have h1 : ((2 * T) ^ δ / δ) ^ a = ((2 * T) ^ δ) ^ a / δ ^ a :=
      Real.div_rpow (Real.rpow_nonneg h2T δ) hδpos.le a
    have h2 : ((2 * T) ^ δ) ^ a = (2 * T) ^ (δ * a) := (Real.rpow_mul h2T δ a).symm
    have h3 : (2 * T) ^ (δ * a) = 2 ^ (δ * a) * T ^ (δ * a) :=
      Real.mul_rpow (by norm_num) (le_of_lt hTpos)
    rw [h1, h2, h3, hmul]
  rw [hsplit] at hpow
  have hTe : T ^ (ε / 2) ≤ T ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  have hTnn : 0 ≤ T ^ (ε / 2) := Real.rpow_nonneg (le_of_lt hTpos) _
  have h2nn : 0 ≤ (2:ℝ) ^ (ε / 2) := Real.rpow_nonneg (by norm_num) _
  have hδnn : 0 < δ ^ a := Real.rpow_pos_of_pos hδpos a
  have hstep : (2:ℝ) ^ (ε / 2) * T ^ (ε / 2) / δ ^ a
      ≤ ((2:ℝ) ^ (ε / 2) / δ ^ a) * T ^ ε := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hinv : 0 ≤ (δ ^ a)⁻¹ := inv_nonneg.mpr hδnn.le
    calc (2:ℝ) ^ (ε / 2) * T ^ (ε / 2) * (δ ^ a)⁻¹
        ≤ (2:ℝ) ^ (ε / 2) * T ^ ε * (δ ^ a)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTe h2nn) hinv
      _ = (2:ℝ) ^ (ε / 2) * (δ ^ a)⁻¹ * T ^ ε := by ring
  calc (Real.log (2 * T)) ^ a ≤ (2:ℝ) ^ (ε / 2) * T ^ (ε / 2) / δ ^ a := hpow
    _ ≤ ((2:ℝ) ^ (ε / 2) / δ ^ a) * T ^ ε := hstep

private lemma rpow_neg_two_cont (n : ℕ) (hn : 0 < n) :
    Continuous (fun u : ℝ => (n : ℝ) ^ (-(2 * u))) := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have heq : (fun u : ℝ => (n : ℝ) ^ (-(2 * u)))
      = fun u : ℝ => Real.exp (-(2 * u) * Real.log (n : ℝ)) := by
    funext u; rw [Real.rpow_def_of_pos hpos]; congr 1; ring
  rw [heq]
  exact Real.continuous_exp.comp (by fun_prop)

private lemma rpow_neg_two_le (n : ℕ) (hn : 1 ≤ n) {σ u : ℝ} (hσu : σ ≤ u) :
    (n : ℝ) ^ (-(2 * u)) ≤ (n : ℝ) ^ (-(2 * σ)) :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

private lemma integral_rpow_neg_two_le (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∫ u in σ..(1 : ℝ), (n : ℝ) ^ (-(2 * u)) ≤ (n : ℝ) ^ (-(2 * σ)) := by
  have hnpos : 0 < n := by omega
  have h1 : ∫ u in σ..(1 : ℝ), (n : ℝ) ^ (-(2 * u)) ≤ ∫ u in σ..(1 : ℝ), (n : ℝ) ^ (-(2 * σ)) :=
    intervalIntegral.integral_mono_on hσ1
      ((rpow_neg_two_cont n hnpos).intervalIntegrable _ _)
      intervalIntegrable_const
      (fun u hu => rpow_neg_two_le n hn hu.1)
  calc ∫ u in σ..(1 : ℝ), (n : ℝ) ^ (-(2 * u)) ≤ ∫ u in σ..(1 : ℝ), (n : ℝ) ^ (-(2 * σ)) := h1
    _ = (1 - σ) * (n : ℝ) ^ (-(2 * σ)) := by
        rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
    _ ≤ (n : ℝ) ^ (-(2 * σ)) := by
        have hnn : 0 ≤ (n : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg (by positivity) _
        have h2 : (1 - σ) * (n : ℝ) ^ (-(2 * σ)) ≤ 1 * (n : ℝ) ^ (-(2 * σ)) :=
          mul_le_mul_of_nonneg_right (show (1 : ℝ) - σ ≤ 1 by linarith) hnn
        linarith


private lemma log_two_n_le (A : ℝ) (hA : 1 ≤ A) (T Y : ℝ) (hT : 2 ≤ T) (hY : 1 ≤ Y)
    (hY2 : Y ≤ (A * T) ^ 2) :
    Real.log (2 * ((⌊Y * (Real.log (A * T)) ^ 2⌋₊ : ℝ) + 1)) ≤ (8 + 4 * Real.log A) * Real.log (2 * T) := by
  set L : ℝ := Y * (Real.log (A * T)) ^ 2 with hLdef
  have hAT1 : 1 ≤ A * T := by nlinarith
  have hATpos : 0 < A * T := by linarith
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlogAT0 : 0 ≤ Real.log (A * T) := Real.log_nonneg hAT1
  have hlog2T1 : 1 ≤ Real.log (2 * T) := by
    have h1 : Real.log 4 ≤ Real.log (2 * T) := Real.log_le_log (by norm_num) (by linarith)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h5 := Real.log_two_gt_d9
    rw [h4] at h1; linarith
  have hLnn : 0 ≤ L := by rw [hLdef]; positivity
  have hlogL : Real.log (A * T) ≤ A * T := Real.log_le_self (le_of_lt hATpos)
  have hsq : (Real.log (A * T)) ^ 2 ≤ (A * T) ^ 2 := by
    nlinarith [mul_self_le_mul_self hlogAT0 hlogL]
  have hLle : L ≤ (A * T) ^ 4 := by
    rw [hLdef]
    calc Y * (Real.log (A * T)) ^ 2 ≤ (A * T) ^ 2 * (Real.log (A * T)) ^ 2 :=
          mul_le_mul_of_nonneg_right hY2 (by positivity)
      _ ≤ (A * T) ^ 2 * (A * T) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (A * T) ^ 4 := by ring
  have hfloor : ((⌊L⌋₊ : ℝ) + 1) ≤ (A * T) ^ 4 + 1 := by
    have h1 : ((⌊L⌋₊ : ℝ)) ≤ L := Nat.floor_le hLnn
    linarith
  have harg : 2 * ((⌊L⌋₊ : ℝ) + 1) ≤ 4 * (A * T) ^ 4 := by nlinarith [hAT1]
  have hargpos : 0 < 2 * ((⌊L⌋₊ : ℝ) + 1) := by positivity
  have h4AT : 0 < 4 * (A * T) ^ 4 := by positivity
  have hlog4 : Real.log 4 ≤ 4 := Real.log_le_self (by norm_num)
  have hT2T : Real.log T ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
  have hA2T : Real.log A ≤ Real.log A * Real.log (2 * T) := by nlinarith
  calc Real.log (2 * ((⌊L⌋₊ : ℝ) + 1))
      ≤ Real.log (4 * (A * T) ^ 4) := Real.log_le_log hargpos harg
    _ = Real.log 4 + Real.log ((A * T) ^ 4) := Real.log_mul (by norm_num) (by positivity)
    _ = Real.log 4 + 4 * Real.log (A * T) := by rw [Real.log_pow]; norm_num
    _ = Real.log 4 + 4 * (Real.log A + Real.log T) := by
        rw [Real.log_mul (by positivity) (by positivity)]
    _ ≤ (8 + 4 * Real.log A) * Real.log (2 * T) := by
        nlinarith [hlog4, hT2T, hA2T, hlogA0, hlog2T1]

private lemma etaAbsorb (A : ℝ) (hA : 6 ≤ A) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T Y : ℝ), 2 ≤ T → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
      (Real.log (2 * ((⌊Y * (Real.log (A * T)) ^ 2⌋₊ : ℝ) + 1))) ^ 17
        * (Real.log (2 * (A * T))) ^ 12 ≤ C * T ^ ε := by
  obtain ⟨Clog, hClogpos, hClog⟩ := logPowAbsorb 29 (by norm_num) ε hε
  have hlogApos : 0 < Real.log A := Real.log_pos (by linarith)
  have hAp : 0 < (8 + 4 * Real.log A) ^ 17 := by positivity
  have hBp : 0 < (2 + Real.log A) ^ 12 := by positivity
  refine ⟨(8 + 4 * Real.log A) ^ 17 * (2 + Real.log A) ^ 12 * Clog, by positivity, ?_⟩
  intro T Y hT hY1 hY2
  have h1 := log_two_n_le A (by linarith : (1:ℝ) ≤ A) T Y hT hY1 hY2
  have hlogA0 : 0 ≤ Real.log A := le_of_lt hlogApos
  have hlog2T1 : 1 ≤ Real.log (2 * T) := by
    have h1' : Real.log 4 ≤ Real.log (2 * T) := Real.log_le_log (by norm_num) (by linarith)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have h5 := Real.log_two_gt_d9
    rw [h4] at h1'; linarith
  have h2 : Real.log (2 * (A * T)) ≤ (2 + Real.log A) * Real.log (2 * T) := by
    have hAT : Real.log (2 * (A * T)) = Real.log 2 + Real.log A + Real.log T := by
      rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
      ring
    have hlogT : Real.log T ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
    have hlog2 : Real.log 2 ≤ Real.log (2 * T) := Real.log_le_log (by norm_num) (by linarith)
    have hlogA2T : Real.log A ≤ Real.log A * Real.log (2 * T) := by nlinarith
    nlinarith [hAT, hlogT, hlog2, hlogA2T, hlog2T1, hlogA0]
  have hlog2Tnn : 0 ≤ Real.log (2 * T) := by linarith
  have hlogAT0 : 0 ≤ Real.log (2 * (A * T)) := Real.log_nonneg (by nlinarith [hT])
  have hlog1nn : 0 ≤ Real.log (2 * ((⌊Y * (Real.log (A * T)) ^ 2⌋₊ : ℝ) + 1)) := by
    apply Real.log_nonneg
    have := Nat.cast_nonneg (α := ℝ) (⌊Y * (Real.log (A * T)) ^ 2⌋₊)
    linarith
  calc (Real.log (2 * ((⌊Y * (Real.log (A * T)) ^ 2⌋₊ : ℝ) + 1))) ^ 17
        * (Real.log (2 * (A * T))) ^ 12
      ≤ ((8 + 4 * Real.log A) * Real.log (2 * T)) ^ 17
          * ((2 + Real.log A) * Real.log (2 * T)) ^ 12 := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ hlog1nn h1 17
        · exact pow_le_pow_left₀ hlogAT0 h2 12
        · positivity
        · positivity
    _ = (8 + 4 * Real.log A) ^ 17 * (2 + Real.log A) ^ 12 * (Real.log (2 * T)) ^ 29 := by ring
    _ ≤ (8 + 4 * Real.log A) ^ 17 * (2 + Real.log A) ^ 12 * (Clog * T ^ ε) := by
        have h29 : (Real.log (2 * T)) ^ (29:ℕ) = (Real.log (2 * T)) ^ (29:ℝ) :=
          (Real.rpow_natCast _ 29).symm
        rw [h29]
        exact mul_le_mul_of_nonneg_left (hClog T hT) (by positivity)
    _ = ((8 + 4 * Real.log A) ^ 17 * (2 + Real.log A) ^ 12 * Clog) * T ^ ε := by ring

private lemma etaCoefAbs (K : ℕ) (Y : ℝ) (n : ℕ) :
    ‖mCoef K n * Complex.exp (-(n : ℂ) / (Y : ℂ))‖ ^ 2
      ≤ ((Nat.divisors n).card : ℝ) ^ 2 * Real.exp (-(2 * (n : ℝ) / Y)) := by
  have hre : (-(n : ℂ) / (Y : ℂ)).re = -(n : ℝ) / Y := by
    have hcast : -(n : ℂ) / (Y : ℂ) = (((-(n : ℝ)) / Y : ℝ) : ℂ) := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
        ← Complex.ofReal_neg, ← Complex.ofReal_div]
    rw [hcast, Complex.ofReal_re]
  have h1 : ‖mCoef K n * Complex.exp (-(n : ℂ) / (Y : ℂ))‖
      ≤ ((Nat.divisors n).card : ℝ) * Real.exp (-(n : ℝ) / Y) := by
    rw [norm_mul, Complex.norm_exp, hre]
    exact mul_le_mul_of_nonneg_right (norm_mCoef_le_tau K n) (Real.exp_nonneg _)
  calc ‖mCoef K n * Complex.exp (-(n : ℂ) / (Y : ℂ))‖ ^ 2
      ≤ (((Nat.divisors n).card : ℝ) * Real.exp (-(n : ℝ) / Y)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = ((Nat.divisors n).card : ℝ) ^ 2 * Real.exp (-(2 * (n : ℝ) / Y)) := by
        rw [mul_pow]
        congr 1
        rw [← Real.exp_nat_mul]
        congr 1
        ring

private lemma etaCoefBound (K : ℕ) (Y : ℝ) (c : ℕ → ℂ)
    (hc : ∀ n, c n = if K < n then mCoef K n * Complex.exp (-(n : ℂ) / (Y : ℂ)) else 0) (n : ℕ) :
    ‖c n‖ ^ 2
      ≤ (if K < n then ((Nat.divisors n).card : ℝ) ^ 2 * Real.exp (-(2 * (n : ℝ) / Y)) else 0) := by
  rw [hc n]
  by_cases h : K < n
  · rw [if_pos h, if_pos h]
    exact etaCoefAbs K Y n
  · rw [if_neg h, if_neg h]; simp

private lemma etaCoefBound2 (K : ℕ) (Y : ℝ) (c : ℕ → ℂ)
    (hc : ∀ n, c n = if K < n then mCoef K n * Complex.exp (-(n : ℂ) / (Y : ℂ)) else 0)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖(-(Real.log (n : ℝ) : ℂ)) * c n‖ ^ 2
      ≤ (if K < n then (1 + Real.log (n : ℝ)) ^ 3
          * (((Nat.divisors n).card : ℝ) ^ 2 * Real.exp (-(2 * (n : ℝ) / Y))) else 0) := by
  rw [hc n]
  by_cases h : K < n
  · rw [if_pos h, if_pos h]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hnorm2 : ‖(Real.log (n : ℝ) : ℂ)‖ ^ 2 = (Real.log (n : ℝ)) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
    calc ‖(-(Real.log (n : ℝ) : ℂ)) * (mCoef K n * Complex.exp (-(n : ℂ) / (Y : ℂ)))‖ ^ 2
        = ‖(-(Real.log (n : ℝ) : ℂ))‖ ^ 2
            * ‖mCoef K n * Complex.exp (-(n : ℂ) / (Y : ℂ))‖ ^ 2 := by
          rw [norm_mul, mul_pow]
      _ = (Real.log (n : ℝ)) ^ 2
            * ‖mCoef K n * Complex.exp (-(n : ℂ) / (Y : ℂ))‖ ^ 2 := by
          rw [norm_neg, hnorm2]
      _ ≤ (Real.log (n : ℝ)) ^ 2
            * (((Nat.divisors n).card : ℝ) ^ 2 * Real.exp (-(2 * (n : ℝ) / Y))) :=
          mul_le_mul_of_nonneg_left (etaCoefAbs K Y n) (by positivity)
      _ ≤ (1 + Real.log (n : ℝ)) ^ 3
            * (((Nat.divisors n).card : ℝ) ^ 2 * Real.exp (-(2 * (n : ℝ) / Y))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith [hlog0, sq_nonneg (Real.log (n : ℝ))]
  · rw [if_neg h, if_neg h]; simp


theorem zetaTailCountEtaSelf (A : ℝ) (hA : 6 ≤ A) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (σ T : ℝ), 1 / 2 ≤ σ → σ ≤ 1 → 2 ≤ T →
      ∀ (K : ℕ) (Y : ℝ), 1 ≤ K → 1 ≤ Y → Y ≤ (A * T) ^ 2 →
        ∀ R : Finset ℂ,
          (∀ z ∈ R, analyticOrderNatAt completedRiemannZeta z ≠ 0 ∧
            σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) →
          (∀ z ∈ R, ∀ z' ∈ R, z ≠ z' → 1 ≤ |z.im - z'.im|) →
          (∀ z ∈ R, (1 : ℝ) / 12 ≤ ‖∑ n ∈ Finset.Ioc K ⌊Y * (Real.log (A * T)) ^ 2⌋₊,
              mCoef K n * (n : ℂ) ^ (-z)
                * Complex.exp (-(n : ℂ) / Y)‖) →
          (R.card : ℝ) ≤ C * T ^ ε * (Y ^ (2 - 2 * σ) + (A * T) * (K : ℝ) ^ (1 - 2 * σ)) := by
  intro ε hε
  obtain ⟨CM, hCMpos, hMVT⟩ := dirPolySepMeanSquareTN
  obtain ⟨CD, hCDpos, hDIV⟩ := zetaTailDivisorLogWeightSelf
  obtain ⟨Cabs, hCabspos, habs⟩ := etaAbsorb A hA ε hε
  refine ⟨576 * CM * CD * Cabs, by positivity, ?_⟩
  intro σ T hσhalf hσone hT K Y hK1 hY1 hY2 R hzero hsep htail
  set N : ℕ := ⌊Y * (Real.log (A * T)) ^ 2⌋₊ with hNdef
  by_cases hNK : N ≤ K
  · have hcard0 : R.card = 0 := by
      rw [Finset.card_eq_zero]
      ext z
      constructor
      · intro hz
        have h := htail z hz
        have hz0 : (∑ n ∈ Finset.Ioc K N,
            mCoef K n * (n : ℂ) ^ (-z) * Complex.exp (-(n : ℂ) / Y)) = 0 :=
          Finset.sum_eq_zero (fun n hn => by
            exfalso
            have h1 : K < n := (Finset.mem_Ioc.mp hn).1
            have h2 : n ≤ N := (Finset.mem_Ioc.mp hn).2
            omega)
        rw [hz0, norm_zero] at h
        norm_num at h
      · intro hz
        exact absurd hz (by simp)
    rw [hcard0]
    simp only [Nat.cast_zero]
    have h1 : (0:ℝ) ≤ Y ^ (2 - 2*σ) := Real.rpow_nonneg (by linarith) _
    have h2 : (0:ℝ) ≤ (A*T) * (K:ℝ) ^ (1-2*σ) :=
      mul_nonneg (by nlinarith [hT]) (Real.rpow_nonneg (by positivity) _)
    have h3 : (0:ℝ) < 576 * CM * CD * Cabs * T ^ ε := by positivity
    exact mul_nonneg h3.le (by linarith)
  · have hKN : K < N := by omega
    have hYpos : 0 < Y := by linarith
    have hN1 : 1 ≤ N := by omega
    set c : ℕ → ℂ := fun n => if K < n then mCoef K n * Complex.exp (-(n : ℂ) / (Y : ℂ)) else 0
      with hcdef
    have hcdef' : ∀ n, c n = if K < n then mCoef K n * Complex.exp (-(n : ℂ) / (Y : ℂ)) else 0 :=
      fun n => congrFun hcdef n
    have hL0 : (0:ℝ) ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * N))
    have hLAT0 : (0:ℝ) ≤ Real.log (2 * (A * T)) := Real.log_nonneg (by nlinarith [hT])
    have hL5 : (0:ℝ) ≤ (Real.log (2 * (N : ℝ)))^5 := pow_nonneg hL0 5
    have hL17 : (0:ℝ) ≤ (Real.log (2 * (N : ℝ)))^17 := pow_nonneg hL0 17
    have hLA12 : (0:ℝ) ≤ (Real.log (2 * (A * T)))^12 := pow_nonneg hLAT0 12
    have htail_eq : ∀ z : ℂ, etaP N c z
        = ∑ n ∈ Finset.Ioc K N, mCoef K n * (n : ℂ) ^ (-z) * Complex.exp (-(n : ℂ) / (Y : ℂ)) := by
      intro z
      rw [etaP]
      have hIoc : (Finset.Icc 1 N).filter (fun n => K < n) = Finset.Ioc K N := by
        ext n; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
      have hterm : ∀ n : ℕ, (if K < n then mCoef K n * Complex.exp (-(n : ℂ) / (Y : ℂ)) else 0)
            * (n : ℂ) ^ (-z)
          = (if K < n then mCoef K n * (n : ℂ) ^ (-z) * Complex.exp (-(n : ℂ) / (Y : ℂ)) else 0) := by
        intro n; by_cases h : K < n <;> simp [h] <;> ring
      simp only [hcdef, hterm]
      rw [← Finset.sum_filter, hIoc]
    have hbig : ∀ z ∈ R, (1:ℝ)/12 ≤ ‖etaP N c z‖ := by
      intro z hz
      rw [htail_eq z]
      exact htail z hz
    set S : Finset ℝ := R.image (fun z : ℂ => z.im) with hSdef
    have hinj : Set.InjOn (fun z : ℂ => z.im) ↑R := by
      intro x hx y hy hxy
      change x.im = y.im at hxy
      by_contra hne
      have hs := hsep x hx y hy hne
      rw [hxy, sub_self, abs_zero] at hs
      linarith
    have hSsum : ∀ F : ℝ → ℝ, (∑ t ∈ S, F t) = ∑ z ∈ R, F z.im := by
      intro F
      have h := Finset.sum_image (f := F) (g := fun z : ℂ => z.im) (s := R) hinj
      simpa [hSdef] using h
    have hSbd : ∀ t ∈ S, |t| ≤ T := by
      intro t ht
      rw [hSdef, Finset.mem_image] at ht
      obtain ⟨z, hz, rfl⟩ := ht
      exact (hzero z hz).2.2.2
    have hSsep : ∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'| := by
      intro t ht t' ht' hne
      rw [hSdef, Finset.mem_image] at ht ht'
      obtain ⟨z, hz, hzt⟩ := ht
      obtain ⟨z', hz', hz't⟩ := ht'
      subst hzt; subst hz't
      exact hsep z hz z' hz' (fun h => hne (by rw [h]))
    have hTn0 : ∀ n : ℕ, (0:ℝ) ≤ T + (n : ℝ) :=
      fun n => by linarith [Nat.cast_nonneg (α := ℝ) n, hT]
    have hper : ∀ z ∈ R, ‖etaP N c z‖ ^ 2
        ≤ 2 * ‖etaP N c ((σ : ℂ) + (z.im : ℂ) * Complex.I)‖ ^ 2
          + 2 * ∫ u in σ..(1:ℝ), ‖etaPd N c ((u : ℂ) + (z.im : ℂ) * Complex.I)‖ ^ 2 := by
      intro z hz
      obtain ⟨-, hσz, hz1, -⟩ := hzero z hz
      exact etaP_norm_sq_le N c σ z (by linarith) hσz hz1
    have hsum1 : ∑ z ∈ R, ‖etaP N c z‖ ^ 2
        ≤ 2 * (∑ z ∈ R, ‖etaP N c ((σ:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2)
          + 2 * (∑ z ∈ R, ∫ u in σ..(1:ℝ), ‖etaPd N c ((u:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hper
    have hM1 : ∑ z ∈ R, ‖etaP N c ((σ:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2
        ≤ CM * (Real.log (2*(N:ℝ)))^5 *
            ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2 * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ)) := by
      rw [← hSsum (fun t => ‖etaP N c ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ^ 2)]
      have h := hMVT N σ T c S hN1 hσhalf hT hSbd hSsep
      simpa only [etaP] using h
    have hswap : ∑ z ∈ R, (∫ u in σ..(1:ℝ), ‖etaPd N c ((u:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2)
        = ∫ u in σ..(1:ℝ), ∑ z ∈ R, ‖etaPd N c ((u:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2 := by
      rw [intervalIntegral.integral_finsetSum]
      intro z hz
      exact ((continuous_etaPd N c z.im).norm.pow 2).intervalIntegrable _ _
    have hpt : ∀ u ∈ Set.Icc σ 1, ∑ z ∈ R, ‖etaPd N c ((u:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2
        ≤ CM * (Real.log (2*(N:ℝ)))^5 *
            ∑ n ∈ Finset.Icc 1 N,
              (‖(-(Real.log (n:ℝ):ℂ)) * c n‖^2 * (T+(n:ℝ))) * (n:ℝ)^(-(2*u)) := by
      intro u hu
      have hu1 : (1:ℝ)/2 ≤ u := le_trans hσhalf hu.1
      have h := hMVT N u T (fun n => (-(Real.log (n:ℝ):ℂ)) * c n) S hN1 hu1 hT hSbd hSsep
      have h' : ∑ t ∈ S, ‖etaPd N c ((u:ℂ)+(t:ℂ)*Complex.I)‖ ^ 2
          ≤ CM * (Real.log (2*(N:ℝ)))^5 *
              ∑ n ∈ Finset.Icc 1 N,
                ‖(-(Real.log (n:ℝ):ℂ)) * c n‖^2 * (n:ℝ)^(-(2*u)) * (T+(n:ℝ)) := by
        simpa only [etaPd] using h
      rw [← hSsum (fun t => ‖etaPd N c ((u:ℂ)+(t:ℂ)*Complex.I)‖ ^ 2)]
      refine h'.trans ?_
      apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCMpos.le hL5)
      exact le_of_eq (Finset.sum_congr rfl (fun n hn => by ring))
    have hcontR : Continuous (fun u : ℝ => CM * (Real.log (2*(N:ℝ)))^5 *
            ∑ n ∈ Finset.Icc 1 N,
              (‖(-(Real.log (n:ℝ):ℂ)) * c n‖^2 * (T+(n:ℝ))) * (n:ℝ)^(-(2*u))) := by
      apply continuous_const.mul
      apply continuous_finsetSum (Finset.Icc 1 N)
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact continuous_const.mul (rpow_neg_two_cont n (by omega))
    have hint2 : ∫ u in σ..(1:ℝ), ∑ z ∈ R, ‖etaPd N c ((u:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2
        ≤ ∫ u in σ..(1:ℝ), CM * (Real.log (2*(N:ℝ)))^5 *
            ∑ n ∈ Finset.Icc 1 N,
              (‖(-(Real.log (n:ℝ):ℂ)) * c n‖^2 * (T+(n:ℝ))) * (n:ℝ)^(-(2*u)) := by
      refine intervalIntegral.integral_mono_on hσone ?_ ?_ hpt
      · exact (continuous_finsetSum R (fun z hz =>
          (continuous_etaPd N c z.im).norm.pow 2)).intervalIntegrable _ _
      · exact hcontR.intervalIntegrable _ _
    have hintval : ∫ u in σ..(1:ℝ), CM * (Real.log (2*(N:ℝ)))^5 *
            ∑ n ∈ Finset.Icc 1 N,
              (‖(-(Real.log (n:ℝ):ℂ)) * c n‖^2 * (T+(n:ℝ))) * (n:ℝ)^(-(2*u))
        = CM * (Real.log (2*(N:ℝ)))^5 *
            ∑ n ∈ Finset.Icc 1 N,
              (‖(-(Real.log (n:ℝ):ℂ)) * c n‖^2 * (T+(n:ℝ))) *
                (∫ u in σ..(1:ℝ), (n:ℝ)^(-(2*u))) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro n hn
        rw [intervalIntegral.integral_const_mul]
      · intro n hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        exact (continuous_const.mul (rpow_neg_two_cont n (by omega))).intervalIntegrable _ _
    have hT2 : ∑ z ∈ R, (∫ u in σ..(1:ℝ), ‖etaPd N c ((u:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2)
        ≤ CM * (Real.log (2*(N:ℝ)))^5 *
            ∑ n ∈ Finset.Icc 1 N,
              (‖(-(Real.log (n:ℝ):ℂ)) * c n‖^2 * (T+(n:ℝ))) * (n:ℝ)^(-(2*σ)) := by
      rw [hswap]
      refine le_trans hint2 ?_
      rw [hintval]
      apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCMpos.le hL5)
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact mul_le_mul_of_nonneg_left
        (integral_rpow_neg_two_le n hn1 σ (by linarith) hσone)
        (mul_nonneg (sq_nonneg _) (hTn0 n))
    -- the four sums
    set T1 : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2 * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ)) with hT1def
    set T2 : ℝ := ∑ n ∈ Finset.Icc 1 N,
        (‖(-(Real.log (n:ℝ):ℂ)) * c n‖^2 * (T+(n:ℝ))) * (n:ℝ)^(-(2*σ)) with hT2def
    set T4 : ℝ := ∑ n ∈ Finset.Ioc K N, ((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y))
        * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ)) with hT4def
    set T3 : ℝ := ∑ n ∈ Finset.Ioc K N, ((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y))
        * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ)) * (1+Real.log (n:ℝ))^3 with hT3def
    have hM1' : ∑ z ∈ R, ‖etaP N c ((σ:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2
        ≤ CM * (Real.log (2*(N:ℝ)))^5 * T1 := by rw [hT1def]; exact hM1
    have hT2'' : ∑ z ∈ R, (∫ u in σ..(1:ℝ), ‖etaPd N c ((u:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2)
        ≤ CM * (Real.log (2*(N:ℝ)))^5 * T2 := by rw [hT2def]; exact hT2
    have hB1 : T1 ≤ T4 := by
      rw [hT1def, hT4def]
      have hIoc : (Finset.Icc 1 N).filter (fun n => K < n) = Finset.Ioc K N := by
        ext n; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
      calc ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2 * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ))
          ≤ ∑ n ∈ Finset.Icc 1 N,
              (if K < n then ((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y)) else 0)
                * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ)) := by
            apply Finset.sum_le_sum
            intro n hn
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (etaCoefBound K Y c hcdef' n)
                (Real.rpow_nonneg (by positivity) _)) (hTn0 n)
        _ = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => K < n),
              ((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y))
                * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ)) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro n hn
            by_cases h : K < n <;> simp [h]
        _ = ∑ n ∈ Finset.Ioc K N, ((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y))
              * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ)) := by rw [hIoc]
    have hB2 : T2 ≤ T3 := by
      rw [hT2def, hT3def]
      have hIoc : (Finset.Icc 1 N).filter (fun n => K < n) = Finset.Ioc K N := by
        ext n; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]; omega
      have hc2 : ∀ n : ℕ, ‖(-(Real.log (n:ℝ):ℂ)) * c n‖^2
          ≤ (if K < n then (1+Real.log (n:ℝ))^3
              * (((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y))) else 0) := by
        intro n
        rcases Nat.eq_zero_or_pos n with h | h
        · subst h
          rw [hcdef']
          have h0 : ¬ K < 0 := by omega
          rw [if_neg h0]; simp
        · exact etaCoefBound2 K Y c hcdef' n h
      calc ∑ n ∈ Finset.Icc 1 N, (‖(-(Real.log (n:ℝ):ℂ)) * c n‖^2 * (T+(n:ℝ))) * (n:ℝ)^(-(2*σ))
          ≤ ∑ n ∈ Finset.Icc 1 N,
              ((if K < n then (1+Real.log (n:ℝ))^3
                * (((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y))) else 0)
                * (T+(n:ℝ))) * (n:ℝ)^(-(2*σ)) := by
            apply Finset.sum_le_sum
            intro n hn
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc2 n) (hTn0 n))
              (Real.rpow_nonneg (by positivity) _)
        _ = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => K < n),
              ((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y))
                * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ)) * (1+Real.log (n:ℝ))^3 := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro n hn
            by_cases h : K < n <;> simp [h] <;> ring
        _ = ∑ n ∈ Finset.Ioc K N, ((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y))
              * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ)) * (1+Real.log (n:ℝ))^3 := by rw [hIoc]
    have hT43 : T4 ≤ T3 := by
      rw [hT4def, hT3def]
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
      have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
      have hone : (1:ℝ) ≤ (1 + Real.log (n:ℝ))^3 := by
        nlinarith [hlog0, sq_nonneg (Real.log (n:ℝ)),
          mul_nonneg (sq_nonneg (Real.log (n:ℝ))) hlog0]
      have hA0 : (0:ℝ) ≤ ((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y))
          * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ)) := by positivity
      calc ((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y)) * (n:ℝ)^(-(2*σ)) * (T+(n:ℝ))
          = ((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y)) * (n:ℝ)^(-(2*σ))
              * (T+(n:ℝ)) * 1 := by ring
        _ ≤ ((Nat.divisors n).card : ℝ)^2 * Real.exp (-(2*(n:ℝ)/Y)) * (n:ℝ)^(-(2*σ))
              * (T+(n:ℝ)) * (1 + Real.log (n:ℝ))^3 := mul_le_mul_of_nonneg_left hone hA0
    have hLN : (N : ℝ) ≤ Y * (Real.log (A * T)) ^ 4 := by
      have h1 : (N : ℝ) ≤ Y * (Real.log (A * T)) ^ 2 := by
        rw [hNdef]
        exact Nat.floor_le (by positivity)
      have hlog1 : 1 ≤ Real.log (A * T) := by
        have h1' : Real.log 12 ≤ Real.log (A * T) := Real.log_le_log (by norm_num) (by nlinarith)
        have h2' : (1:ℝ) ≤ Real.log 12 := by
          have h3 : Real.log 4 ≤ Real.log 12 := Real.log_le_log (by norm_num) (by norm_num)
          have h4 : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
          have h5 := Real.log_two_gt_d9
          rw [h4] at h3; linarith
        linarith
      have ht2_nonneg : (0:ℝ) ≤ Real.log (A * T) := le_trans zero_le_one hlog1
      have h2 : (Real.log (A * T)) ^ 2 ≤ (Real.log (A * T)) ^ 4 := by
        have h3 : (1:ℝ) ≤ (Real.log (A * T))^2 := by nlinarith
        nlinarith [h3, sq_nonneg (Real.log (A * T)), mul_nonneg (sq_nonneg (Real.log (A*T)))
          (by linarith : (0:ℝ) ≤ (Real.log (A*T))^2 - 1)]
      calc (N : ℝ) ≤ Y * (Real.log (A * T)) ^ 2 := h1
        _ ≤ Y * (Real.log (A * T)) ^ 4 := mul_le_mul_of_nonneg_left h2 (by linarith)
    have hDIV' : T3 ≤ CD * (Real.log (2 * (N:ℝ)))^12 * (Real.log (2 * (A*T)))^12
        * (T*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by
      rw [hT3def]
      exact hDIV K N σ Y T A hK1 hσhalf hσone hY1 hT (by linarith : (1:ℝ) ≤ A) hLN
    have hK0 : (0:ℝ) ≤ (K:ℝ)^(1-2*σ) := Real.rpow_nonneg (by positivity) _
    have hY0 : (0:ℝ) ≤ Y^(2-2*σ) := Real.rpow_nonneg (by linarith) _
    have hfin : ∑ z ∈ R, ‖etaP N c z‖ ^ 2
        ≤ 4 * CM * CD * (Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12
            * (T*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by
      have hCM0 : (0:ℝ) ≤ CM := hCMpos.le
      have hs1 : ∑ z ∈ R, ‖etaP N c z‖ ^ 2 ≤ 4 * (CM * (Real.log (2*(N:ℝ)))^5 * T3) := by
        have hT13 : T1 ≤ T3 := le_trans hB1 hT43
        calc ∑ z ∈ R, ‖etaP N c z‖ ^ 2
            ≤ 2 * (∑ z ∈ R, ‖etaP N c ((σ:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2)
              + 2 * (∑ z ∈ R, ∫ u in σ..(1:ℝ), ‖etaPd N c ((u:ℂ)+(z.im:ℂ)*Complex.I)‖ ^ 2) := hsum1
          _ ≤ 2 * (CM * (Real.log (2*(N:ℝ)))^5 * T1) + 2 * (CM * (Real.log (2*(N:ℝ)))^5 * T2) :=
              add_le_add (mul_le_mul_of_nonneg_left hM1' (by norm_num))
                (mul_le_mul_of_nonneg_left hT2'' (by norm_num))
          _ ≤ 2 * (CM * (Real.log (2*(N:ℝ)))^5 * T3) + 2 * (CM * (Real.log (2*(N:ℝ)))^5 * T3) := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hT13 (mul_nonneg hCM0 hL5)) (by norm_num)
              · exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hB2 (mul_nonneg hCM0 hL5)) (by norm_num)
          _ = 4 * (CM * (Real.log (2*(N:ℝ)))^5 * T3) := by ring
      have hs2 : 4 * (CM * (Real.log (2*(N:ℝ)))^5 * T3)
          ≤ 4 * CM * CD * (Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12
              * (T*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by
        have hb : (0:ℝ) ≤ CD * (Real.log (2 * (N:ℝ)))^12 * (Real.log (2 * (A*T)))^12
            * (T*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by
          have h2 : (0:ℝ) ≤ T*(K:ℝ)^(1-2*σ) := mul_nonneg (by linarith) hK0
          have h3 : (0:ℝ) ≤ CD * (Real.log (2*(N:ℝ)))^12 * (Real.log (2*(A*T)))^12 :=
            mul_nonneg (mul_nonneg hCDpos.le (pow_nonneg hL0 12)) hLA12
          exact mul_nonneg h3 (by linarith)
        calc 4 * (CM * (Real.log (2*(N:ℝ)))^5 * T3)
            ≤ 4 * (CM * (Real.log (2*(N:ℝ)))^5
                * (CD * (Real.log (2 * (N:ℝ)))^12 * (Real.log (2 * (A*T)))^12
                    * (T*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)))) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul_of_nonneg_left hDIV' (mul_nonneg hCM0 hL5)
          _ = 4 * CM * CD * (Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12
                * (T*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by ring
      linarith [hs1, hs2]
    have hpl : (Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12 ≤ Cabs * T^ε := by
      have h1 := habs T Y hT hY1 hY2
      have hlogNN : Real.log (2 * (N:ℝ))
          ≤ Real.log (2 * ((⌊Y * (Real.log (A * T)) ^ 2⌋₊ : ℝ) + 1)) := by
        apply Real.log_le_log (by positivity)
        have hle : (N:ℝ) ≤ ((⌊Y * (Real.log (A * T)) ^ 2⌋₊ : ℝ) + 1) := by
          rw [hNdef]
          have := Nat.floor_le (show (0:ℝ) ≤ Y * (Real.log (A * T))^2 by positivity)
          linarith
        linarith
      have h2 : (Real.log (2*(N:ℝ)))^17
          ≤ (Real.log (2 * ((⌊Y * (Real.log (A * T)) ^ 2⌋₊ : ℝ) + 1)))^17 :=
        pow_le_pow_left₀ hL0 hlogNN 17
      have h3 : (0:ℝ) ≤ (Real.log (2 * (A * T)))^12 := hLA12
      calc (Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12
          ≤ (Real.log (2 * ((⌊Y * (Real.log (A * T)) ^ 2⌋₊ : ℝ) + 1)))^17
              * (Real.log (2*(A*T)))^12 := mul_le_mul_of_nonneg_right h2 h3
        _ ≤ Cabs * T^ε := h1
    have hgoal : ∑ z ∈ R, ‖etaP N c z‖ ^ 2
        ≤ 4 * CM * CD * Cabs * T^ε * ((A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by
      have hcK0 : (0:ℝ) ≤ (A*T)*((K:ℝ)^(1-2*σ) + Y^(2-2*σ)) :=
        mul_nonneg (by nlinarith [hT]) (by linarith)
      have h1 : 4 * CM * CD * (Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12
            * (T*(K:ℝ)^(1-2*σ) + Y^(2-2*σ))
          ≤ 4 * CM * CD * (Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12
            * ((A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by
        have hle : T*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)
            ≤ (A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ) := by
          have := mul_le_mul_of_nonneg_right (show T ≤ A * T by nlinarith) hK0
          linarith
        have hnn : (0:ℝ) ≤ 4 * CM * CD * (Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12 := by
          have ha : (0:ℝ) ≤ 4 * CM * CD := by positivity
          have hb2 : (0:ℝ) ≤ (Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12 :=
            mul_nonneg hL17 hLA12
          nlinarith [ha, hb2]
        exact mul_le_mul_of_nonneg_left hle hnn
      have h2 : 4 * CM * CD * (Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12
            * ((A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ))
          ≤ 4 * CM * CD * Cabs * T^ε * ((A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by
        have hb : (0:ℝ) ≤ (A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ) := by
          have h1 : (0:ℝ) ≤ (A*T)*(K:ℝ)^(1-2*σ) := mul_nonneg (by nlinarith [hT]) hK0
          linarith
        calc 4 * CM * CD * (Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12
              * ((A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ))
            = (4 * CM * CD) * ((Real.log (2*(N:ℝ)))^17 * (Real.log (2*(A*T)))^12)
              * ((A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by ring
          _ ≤ (4 * CM * CD) * (Cabs * T^ε) * ((A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by
              have hnn2 : (0:ℝ) ≤ 4 * CM * CD := by positivity
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpl hnn2) hb
          _ = 4 * CM * CD * Cabs * T^ε * ((A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by ring
      linarith [hfin, h1, h2]
    have hcard : (R.card : ℝ) * (1/144) ≤ ∑ z ∈ R, ‖etaP N c z‖ ^ 2 := by
      have h1 : ∀ z ∈ R, (1/144 : ℝ) ≤ ‖etaP N c z‖ ^ 2 := by
        intro z hz
        have h := hbig z hz
        nlinarith [h, norm_nonneg (etaP N c z)]
      have hconst : ∑ z ∈ R, (1/144 : ℝ) = (R.card : ℝ) * (1/144) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [← hconst]
      exact Finset.sum_le_sum h1
    have hfinal : (R.card : ℝ)
        ≤ 576 * CM * CD * Cabs * T^ε * ((A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ)) := by
      have h5 : (0:ℝ) ≤ (A*T)*(K:ℝ)^(1-2*σ) + Y^(2-2*σ) := by
        have h1 : (0:ℝ) ≤ (A*T)*(K:ℝ)^(1-2*σ) := mul_nonneg (by nlinarith [hT]) hK0
        linarith
      nlinarith [hcard, hgoal, h5]
    linarith [hfinal]

end Work.ZeroDensity.Ingham
