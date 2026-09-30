import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Complex Filter Set MeasureTheory Metric intervalIntegral
open scoped Real Topology

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- `1 - e^{-y} ≤ y` for all real `y`. -/
lemma one_sub_exp_neg_le_self (y : ℝ) : 1 - rexp (-y) ≤ y := by
  have h := Real.one_sub_le_exp_neg y
  linarith

/-- Bernoulli: `(1 - x)^n ≥ 1 - n·x` for `0 ≤ x ≤ 1`. -/
lemma bernoulli_one_sub {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  have hB := one_add_mul_sub_le_pow (a := 1 - x) (H := by linarith) n
  have hx : (1 - x) - 1 = -x := by ring
  rw [hx] at hB
  have : 1 + (n : ℝ) * (-x) = 1 - (n : ℝ) * x := by ring
  rwa [this] at hB

/-- `e^{-u}·(1 - u²) ≤ 1 - u` for `0 ≤ u ≤ 1` (from `e^u ≥ 1 + u`). -/
lemma exp_neg_mul_sub_sq_le_one_sub {u : ℝ} (_hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    rexp (-u) * (1 - u^2) ≤ 1 - u := by
  have he : 1 + u ≤ rexp u := by simpa [add_comm] using (Real.add_one_le_exp u)
  have hmain : 1 - u^2 ≤ (1 - u) * rexp u := by
    calc
      1 - u^2 = (1 - u) * (1 + u) := by ring
      _ ≤ (1 - u) * rexp u := by
        exact mul_le_mul_of_nonneg_left he (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hmain (le_of_lt (Real.exp_pos (-u)))
  calc
    rexp (-u) * (1 - u^2) ≤ rexp (-u) * ((1 - u) * rexp u) := hmul
    _ = 1 - u := by
      calc
        rexp (-u) * ((1 - u) * rexp u) = (1 - u) * (rexp (-u) * rexp u) := by ring
        _ = (1 - u) * 1 := by
          have heu' : rexp (-u) * rexp u = 1 := by
            rw [← Real.exp_add]
            norm_num
          rw [heu']
        _ = 1 - u := by ring

/-- `(1-u)^N ≥ e^{-Nu}·(1 - N u²)` for `0 ≤ u ≤ 1`. -/
lemma pow_sub_ge_exp_neg_mul (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (N : ℕ) :
    rexp (-((N : ℝ) * u)) * (1 - (N : ℝ) * u^2) ≤ (1 - u) ^ N := by
  have hA : rexp (-u) * (1 - u^2) ≤ 1 - u := exp_neg_mul_sub_sq_le_one_sub hu0 hu1
  have hBern : 1 - (N : ℝ) * u^2 ≤ (1 - u^2) ^ N := bernoulli_one_sub (sq_nonneg u) (by nlinarith) N
  have hpow : (rexp (-u) * (1 - u^2)) ^ N ≤ (1 - u) ^ N := by
    have hsub : 0 ≤ 1 - u^2 := by nlinarith
    have h0 : 0 ≤ rexp (-u) * (1 - u^2) := mul_nonneg (le_of_lt (Real.exp_pos (-u))) hsub
    exact pow_le_pow_left₀ h0 hA N
  have hLHS : (rexp (-u) * (1 - u^2)) ^ N = rexp (-((N : ℝ) * u)) * (1 - u^2) ^ N := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring
  calc
    rexp (-((N : ℝ) * u)) * (1 - (N : ℝ) * u^2)
        ≤ rexp (-((N : ℝ) * u)) * (1 - u^2) ^ N := by
          exact mul_le_mul_of_nonneg_left hBern (le_of_lt (Real.exp_pos (-((N : ℝ) * u))))
    _ = (rexp (-u) * (1 - u^2)) ^ N := by rw [← hLHS]
    _ ≤ (1 - u) ^ N := hpow

/-- crude: `0 ≤ e^{-t} - (1-t/N)^N ≤ e^{-t}` for `0 ≤ t ≤ N`. -/
lemma diff_between_zero_and_exp {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (htN : t ≤ (N : ℝ)) :
    0 ≤ rexp (-t) - (1 - t / (N : ℝ)) ^ N ∧ rexp (-t) - (1 - t / (N : ℝ)) ^ N ≤ rexp (-t) := by
  have hle : (1 - t / (N : ℝ)) ^ N ≤ rexp (-t) := by
    simpa using (Real.one_sub_div_pow_le_exp_neg (n := N) (t := t) htN)
  have hbase_nonneg : 0 ≤ 1 - t / (N : ℝ) := by
    exact sub_nonneg.mpr (div_le_one_of_le₀ htN (by positivity : 0 ≤ (N : ℝ)))
  have hp_nonneg : 0 ≤ (1 - t / (N : ℝ)) ^ N := pow_nonneg hbase_nonneg N
  constructor <;> linarith

/-- second order: for `0 ≤ t ≤ N/2`, `|e^{-t} - (1-t/N)^N| ≤ e^{-t}·t²/N`. -/
lemma diff_sq_bound {N : ℕ} (hN : 0 < N) {t : ℝ} (ht0 : 0 ≤ t) (htN2 : t ≤ (N : ℝ) / 2) :
    |rexp (-t) - (1 - t / (N : ℝ)) ^ N| ≤ rexp (-t) * (t^2 / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have htN : t ≤ (N : ℝ) := by linarith
  let u : ℝ := t / (N : ℝ)
  have hu0 : 0 ≤ u := div_nonneg ht0 (le_of_lt hNpos)
  have hu1 : u ≤ 1 := by
    dsimp [u]
    exact div_le_one_of_le₀ htN (le_of_lt hNpos)
  have ht_mul : t = (N : ℝ) * u := by
    dsimp [u]
    field_simp [hNpos.ne']
  have hpow := pow_sub_ge_exp_neg_mul u hu0 hu1 N
  have hp2 : (1 - u) ^ N * rexp t ≥ 1 - (N : ℝ) * u^2 := by
    have hm := mul_le_mul_of_nonneg_right hpow (le_of_lt (Real.exp_pos t))
    have hcancel : rexp (-((N : ℝ) * u)) * rexp t = 1 := by
      rw [← ht_mul, ← Real.exp_add]
      norm_num
    have hLC : rexp (-((N : ℝ) * u)) * (1 - (N : ℝ) * u^2) * rexp t
        = 1 - (N : ℝ) * u^2 := by
      calc
        rexp (-((N : ℝ) * u)) * (1 - (N : ℝ) * u^2) * rexp t
            = (1 - (N : ℝ) * u^2) * (rexp (-((N : ℝ) * u)) * rexp t) := by ring
        _ = (1 - (N : ℝ) * u^2) * 1 := by rw [hcancel]
        _ = 1 - (N : ℝ) * u^2 := by ring
    simpa [hLC] using hm
  have hdiff : rexp (-t) - (1 - t / (N : ℝ)) ^ N ≤ rexp (-t) * (t^2 / (N : ℝ)) := by
    have hmain : rexp (-t) * (1 - (1 - u) ^ N * rexp t) ≤ rexp (-t) * ((N : ℝ) * u^2) := by
      have hinner : 1 - (1 - u) ^ N * rexp t ≤ (N : ℝ) * u^2 := by linarith
      exact mul_le_mul_of_nonneg_left hinner (le_of_lt (Real.exp_pos (-t)))
    have hlhs : rexp (-t) * (1 - (1 - u) ^ N * rexp t) = rexp (-t) - (1 - u) ^ N := by
      have hcancel2 : rexp (-t) * rexp t = 1 := by rw [← Real.exp_add]; norm_num
      calc
        rexp (-t) * (1 - (1 - u) ^ N * rexp t)
            = rexp (-t) * 1 - rexp (-t) * ((1 - u) ^ N * rexp t) := by rw [mul_sub, mul_one]
        _ = rexp (-t) - (1 - u) ^ N := by
          have hc2 : rexp (-t) * ((1 - u) ^ N * rexp t) = (1 - u) ^ N := by
            calc
              rexp (-t) * ((1 - u) ^ N * rexp t) = (1 - u) ^ N * (rexp (-t) * rexp t) := by ring
              _ = (1 - u) ^ N * 1 := by rw [hcancel2]
              _ = (1 - u) ^ N := by ring
          rw [hc2]
          ring
    have hNu2 : (N : ℝ) * u^2 = t^2 / (N : ℝ) := by
      dsimp [u]
      field_simp [hNpos.ne']
    calc
      rexp (-t) - (1 - t / (N : ℝ)) ^ N = rexp (-t) - (1 - u) ^ N := by dsimp [u]
      _ = rexp (-t) * (1 - (1 - u) ^ N * rexp t) := by rw [hlhs]
      _ ≤ rexp (-t) * ((N : ℝ) * u^2) := hmain
      _ = rexp (-t) * (t^2 / (N : ℝ)) := by rw [hNu2]
  have hle0 : 0 ≤ rexp (-t) - (1 - t / (N : ℝ)) ^ N :=
    (diff_between_zero_and_exp (N := N) ht0 htN).1
  have habs : |rexp (-t) - (1 - t / (N : ℝ)) ^ N| = rexp (-t) - (1 - t / (N : ℝ)) ^ N :=
    abs_of_nonneg hle0
  rw [habs]
  exact hdiff

/-- complex Gamma integrand -/
def Eg (s : ℂ) (t : ℝ) : ℂ := ↑(rexp (-t)) * (t : ℂ) ^ (s - 1)

/-- approximate integrand (Euler) -/
def Gg (s : ℂ) (N : ℕ) (t : ℝ) : ℂ := ↑((1 - t / (N : ℝ)) ^ N) * (t : ℂ) ^ (s - 1)

/-- pointwise norm of the complex integrand difference (t > 0). -/
lemma norm_Eg_sub_Gg (s : ℂ) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖Eg s t - Gg s N t‖ =
      |rexp (-t) - (1 - t / (N : ℝ)) ^ N| * t ^ (s.re - 1) := by
  unfold Eg Gg
  rw [← sub_mul]
  rw [norm_mul]
  congr 1
  · rw [← Complex.ofReal_sub]
    exact RCLike.norm_ofReal _
  · exact Complex.norm_cpow_eq_rpow_re_of_pos ht (s - 1)

/-- norm of the Gamma integrand (t > 0). -/
lemma norm_Eg (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖Eg s t‖ = rexp (-t) * t ^ (s.re - 1) := by
  unfold Eg
  rw [norm_mul]
  congr 1
  · calc
      ‖(rexp (-t) : ℂ)‖ = |rexp (-t)| := RCLike.norm_ofReal (r := rexp (-t))
      _ = rexp (-t) := abs_of_nonneg (le_of_lt (Real.exp_pos (-t)))
  · exact Complex.norm_cpow_eq_rpow_re_of_pos ht (s - 1)

/-- identity: `Γ(s) - Γ_N(s)` as the sum of a finite part and a tail. -/
lemma Eg_eq_gamma_integrand (s : ℂ) (t : ℝ) :
    Eg s t = cexp (-(t : ℂ)) * (t : ℂ) ^ (s - 1) := by
  unfold Eg
  have hx : cexp (-(t : ℂ)) = ↑(rexp (-t)) := by
    rw [Complex.ofReal_exp (-t)]
    congr 1
    exact (Complex.ofReal_neg t).symm
  rw [← hx]

lemma integrableOn_Eg_Ioi (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (Eg s) (Ioi (0 : ℝ)) := by
  convert (Complex.GammaIntegral_convergent hs) using 1
  funext t
  rfl

lemma intervalIntegrable_Eg (s : ℂ) (hs : 0 < s.re) (X : ℝ) (hX : 0 ≤ X) :
    IntervalIntegrable (Eg s) volume 0 X := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  exact (integrableOn_Eg_Ioi s hs).mono_set (fun t ht => ht.1)

lemma norm_Gg_le_norm_Eg (s : ℂ) (N : ℕ) {t : ℝ} (ht : 0 < t) (htN : t ≤ (N : ℝ)) :
    ‖Gg s N t‖ ≤ ‖Eg s t‖ := by
  have hbase : 0 ≤ 1 - t / (N : ℝ) :=
    sub_nonneg.mpr (div_le_one_of_le₀ htN (by positivity : 0 ≤ (N : ℝ)))
  have hp : 0 ≤ (1 - t / (N : ℝ)) ^ N := pow_nonneg hbase N
  have hple : (1 - t / (N : ℝ)) ^ N ≤ rexp (-t) := by
    exact Real.one_sub_div_pow_le_exp_neg (n := N) (t := t) htN
  have hL : ‖Gg s N t‖ = (1 - t / (N : ℝ)) ^ N * t ^ (s.re - 1) := by
    let p : ℝ := (1 - t / (N : ℝ)) ^ N
    change ‖(p : ℂ) * (t : ℂ) ^ (s - 1)‖ = p * t ^ (s.re - 1)
    rw [norm_mul]
    have hp' : 0 ≤ p := by simpa [p] using hp
    have hfac1 : ‖(p : ℂ)‖ = p := by
      calc
        ‖(p : ℂ)‖ = |p| := RCLike.norm_ofReal (r := p)
        _ = p := abs_of_nonneg hp'
    have hfac2 : ‖(t : ℂ) ^ (s - 1)‖ = t ^ (s.re - 1) :=
      Complex.norm_cpow_eq_rpow_re_of_pos ht (s - 1)
    rw [hfac1, hfac2]
  have hR : ‖Eg s t‖ = rexp (-t) * t ^ (s.re - 1) := norm_Eg s ht
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_right hple (Real.rpow_nonneg (le_of_lt ht) (s.re - 1))

lemma continuousOn_Gg (s : ℂ) (N : ℕ) : ContinuousOn (Gg s N) (Ioi (0 : ℝ)) := by
  have h1 : ContinuousOn (fun t : ℝ => (((1 - t / (N : ℝ)) ^ N : ℝ) : ℂ)) (Ioi (0 : ℝ)) := by
    exact (continuous_ofReal.comp (by fun_prop : Continuous fun t : ℝ => (1 - t / (N : ℝ)) ^ N)).continuousOn
  have h2 : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioi (0 : ℝ)) := by
    refine continuousOn_of_forall_continuousAt ?_
    intro t ht
    have htpos : 0 < t := by simpa using ht
    exact (continuousAt_cpow_const (a := (t : ℂ)) (b := s - 1) ((Complex.ofReal_mem_slitPlane).2 htpos)).comp
      continuous_ofReal.continuousAt
  unfold Gg
  exact h1.mul h2

lemma intervalIntegrable_Gg (s : ℂ) (hs : 0 < s.re) {N : ℕ} (hN : 2 ≤ N) :
    IntervalIntegrable (Gg s N) volume 0 (N : ℝ) := by
  have hNge : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hNge]
  have hEioc : IntegrableOn (Eg s) (Ioc 0 (N : ℝ)) :=
    (integrableOn_Eg_Ioi s hs).mono_set (fun t ht => ht.1)
  have hEint : Integrable (Eg s) (volume.restrict (Ioc 0 (N : ℝ))) := hEioc.integrable
  have hc : ContinuousOn (Gg s N) (Ioc 0 (N : ℝ)) :=
    (continuousOn_Gg s N).mono (fun t ht => ht.1)
  have hGmeas : AEStronglyMeasurable (Gg s N) (volume.restrict (Ioc 0 (N : ℝ))) :=
    hc.aestronglyMeasurable measurableSet_Ioc
  exact Integrable.mono hEint hGmeas (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact norm_Gg_le_norm_Eg s N hx.1 hx.2)

lemma gammaSeq_sub_integral (s : ℂ) (hs : 0 < s.re) {N : ℕ} (hN : 2 ≤ N) :
    Complex.Gamma s - Complex.GammaSeq s N =
      (∫ t in (0 : ℝ)..(N : ℝ), Eg s t - Gg s N t) + ∫ t in Ioi (N : ℝ), Eg s t := by
  have hNge : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hN0 : N ≠ 0 := by omega
  have hE0 : IntegrableOn (Eg s) (Ioi 0) := integrableOn_Eg_Ioi s hs
  have hEN : IntegrableOn (Eg s) (Ioi (N : ℝ)) := hE0.mono_set (by
      intro t ht
      change 0 < t
      have hNpos : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
      have hlt : (N : ℝ) < t := by simpa using ht
      linarith)
  have hadd := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := (N : ℝ)) (f := Eg s) hE0 hEN
  have hseq : Complex.GammaSeq s N = ∫ t in (0 : ℝ)..(N : ℝ), Gg s N t := by
    simpa [Gg] using (Complex.GammaSeq_eq_approx_Gamma_integral hs hN0)
  have hgam : Complex.Gamma s = ∫ t in Ioi (0 : ℝ), Eg s t := by
    rw [Complex.Gamma_eq_integral hs]
    rfl
  have hEI : IntervalIntegrable (Eg s) volume 0 (N : ℝ) := intervalIntegrable_Eg s hs (N : ℝ) hNge
  have hGI : IntervalIntegrable (Gg s N) volume 0 (N : ℝ) := intervalIntegrable_Gg s hs hN
  have hsub := intervalIntegral.integral_sub (f := Eg s) (g := Gg s N) hEI hGI
  let A := ∫ t in (0 : ℝ)..(N : ℝ), Eg s t
  let B := ∫ t in Ioi (N : ℝ), Eg s t
  let C := ∫ t in (0 : ℝ)..(N : ℝ), Gg s N t
  calc
    Complex.Gamma s - Complex.GammaSeq s N
        = (∫ t in Ioi (0 : ℝ), Eg s t) - C := by rw [hgam, hseq]
    _ = (A + B) - C := by
          have : ∫ t in Ioi (0 : ℝ), Eg s t = A + B := by
            simpa [A, B] using hadd.symm
          rw [this]
    _ = (A - C) + B := by ring
    _ = (∫ t in (0 : ℝ)..(N : ℝ), Eg s t - Gg s N t) + B := by
          have : A - C = ∫ t in (0 : ℝ)..(N : ℝ), Eg s t - Gg s N t := by
            dsimp [A, C]
            exact hsub.symm
          rw [this]
    _ = (∫ t in (0 : ℝ)..(N : ℝ), Eg s t - Gg s N t) + ∫ t in Ioi (N : ℝ), Eg s t := by
          rfl



/-- tail integral `∫_{Ioi x} e^{-t}·t^{R-1}`. -/
noncomputable def tailInt (R x : ℝ) : ℝ := ∫ t in Ioi x, rexp (-t) * t ^ (R - 1)

/-- master constant `∫_{Ioi 0} e^{-t}·t^{R+1}`. -/
noncomputable def constInt (R : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), rexp (-t) * t ^ (R + 1)

/-- For `N/2 ≤ t`: `t^{σ-1} ≤ t^{σ+1}·(2/N)²`. -/
lemma rpow_sub_one_le_rpow_add_one_mul (N : ℕ) (hN : 2 ≤ N) {t : ℝ} (ht0 : 0 < t)
    {σ : ℝ} (ht2 : (N : ℝ) / 2 ≤ t) :
    t ^ (σ - 1) ≤ t ^ (σ + 1) * (2 / (N : ℝ)) ^ 2 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hge : 1 ≤ 2 * t / (N : ℝ) := by
    rw [one_le_div hNpos]
    linarith
  have hsq1 : 1 ≤ (2 * t / (N : ℝ)) ^ 2 := by
    simpa using (pow_le_pow_left₀ (by norm_num) hge 2)
  have hpow2 : t ^ (σ + 1) = t ^ (σ - 1) * t ^ (2 : ℝ) := by
    rw [show σ + 1 = (σ - 1) + 2 by ring, Real.rpow_add ht0 (σ - 1) 2]
  calc
    t ^ (σ - 1) = t ^ (σ - 1) * 1 := by ring
    _ ≤ t ^ (σ - 1) * (2 * t / (N : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq1 (le_of_lt (Real.rpow_pos_of_pos ht0 (σ - 1)))
    _ = t ^ (σ + 1) * (2 / (N : ℝ)) ^ 2 := by
      rw [hpow2]
      rw [Real.rpow_two]
      ring

/-- pointwise four-N bound: `‖E - G‖ ≤ (4/N)·e^{-t}·t^{σ+1}` for `t ∈ (0,N]`. -/
lemma norm_diff_le_four_N (s : ℂ) {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht0 : 0 < t)
    (htN : t ≤ (N : ℝ)) :
    ‖Eg s t - Gg s N t‖ ≤ (4 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1) := by
  have hNnat : (0 : ℕ) < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hX0 : 0 ≤ rexp (-t) * t ^ (s.re + 1) := by positivity
  by_cases hA : t ≤ (N : ℝ) / 2
  · have hsq := diff_sq_bound (N := N) hNnat (le_of_lt ht0) hA
    have hsmall : (1 / (N : ℝ)) ≤ 4 / (N : ℝ) := by
      rw [div_le_div_iff₀ hNpos hNpos]
      nlinarith
    have hmain1 : ‖Eg s t - Gg s N t‖ ≤ (1 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1) := by
      have h2 : t ^ (2 : ℝ) = t ^ 2 := by simpa using (Real.rpow_natCast t 2)
      have hmul : t ^ (s.re + 1) = t ^ (s.re - 1) * t ^ (2 : ℝ) := by
        rw [show s.re + 1 = (s.re - 1) + 2 by ring, Real.rpow_add ht0 (s.re - 1) 2]
      calc
        ‖Eg s t - Gg s N t‖
            = |rexp (-t) - (1 - t / (N : ℝ)) ^ N| * t ^ (s.re - 1) := norm_Eg_sub_Gg s N ht0
        _ ≤ (rexp (-t) * (t ^ 2 / (N : ℝ))) * t ^ (s.re - 1) := by
              exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (le_of_lt ht0) (s.re - 1))
        _ = (1 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1) := by
              calc
                rexp (-t) * (t ^ 2 / (N : ℝ)) * t ^ (s.re - 1)
                    = rexp (-t) * t ^ (s.re - 1) * t ^ 2 / (N : ℝ) := by ring
                _ = rexp (-t) * (t ^ (s.re - 1) * t ^ 2) / (N : ℝ) := by ring
                _ = rexp (-t) * (t ^ (s.re - 1) * t ^ (2 : ℝ)) / (N : ℝ) := by rw [← h2]
                _ = rexp (-t) * t ^ (s.re + 1) / (N : ℝ) := by rw [hmul]
                _ = (1 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1) := by ring
    calc
      ‖Eg s t - Gg s N t‖ ≤ (1 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1) := hmain1
      _ ≤ (4 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1) := by
            calc
              (1 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1)
                  = (1 / (N : ℝ)) * (rexp (-t) * t ^ (s.re + 1)) := by ring
              _ ≤ (4 / (N : ℝ)) * (rexp (-t) * t ^ (s.re + 1)) := by
                    exact mul_le_mul_of_nonneg_right hsmall hX0
              _ = (4 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1) := by ring
  · have hcrude : |rexp (-t) - (1 - t / (N : ℝ)) ^ N| ≤ rexp (-t) := by
      have hbe := diff_between_zero_and_exp (N := N) (le_of_lt ht0) htN
      rw [abs_of_nonneg hbe.1]
      exact hbe.2
    have hA2 : (N : ℝ) / 2 ≤ t := le_of_not_gt (fun h => hA (le_of_lt h))
    have hpow := rpow_sub_one_le_rpow_add_one_mul N hN ht0 (σ := s.re) hA2
    have hsmall2 : (2 / (N : ℝ)) ^ 2 ≤ 4 / (N : ℝ) := by
      have hmain : (4 : ℝ) / (N : ℝ) ^ 2 ≤ 4 / (N : ℝ) := by
        rw [div_le_div_iff₀ (sq_pos_of_pos hNpos) hNpos]
        have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
        nlinarith
      calc
        (2 / (N : ℝ)) ^ 2 = (2 : ℝ) ^ 2 / (N : ℝ) ^ 2 := by rw [div_pow]
        _ = 4 / (N : ℝ) ^ 2 := by norm_num
        _ ≤ 4 / (N : ℝ) := hmain
    have hcrude2 : ‖Eg s t - Gg s N t‖ ≤ rexp (-t) * t ^ (s.re + 1) * (4 / (N : ℝ)) := by
      calc
        ‖Eg s t - Gg s N t‖
            = |rexp (-t) - (1 - t / (N : ℝ)) ^ N| * t ^ (s.re - 1) := norm_Eg_sub_Gg s N ht0
        _ ≤ rexp (-t) * t ^ (s.re - 1) := by
              exact mul_le_mul_of_nonneg_right hcrude (Real.rpow_nonneg (le_of_lt ht0) (s.re - 1))
        _ ≤ rexp (-t) * (t ^ (s.re + 1) * (2 / (N : ℝ)) ^ 2) := by
              exact mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos (-t)))
        _ = rexp (-t) * t ^ (s.re + 1) * (2 / (N : ℝ)) ^ 2 := by ring
        _ ≤ rexp (-t) * t ^ (s.re + 1) * (4 / (N : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hsmall2 hX0
    calc
      ‖Eg s t - Gg s N t‖ ≤ rexp (-t) * t ^ (s.re + 1) * (4 / (N : ℝ)) := hcrude2
      _ = (4 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1) := by ring

/-- interval integrability of `t ↦ e^{-t}·t^{c}` on `0..X`, `c ≥ 0`. -/
lemma intervalIntegrable_exp_mul_rpow (c : ℝ) (hc : 0 ≤ c) (X : ℝ) (hX : 0 ≤ X) :
    IntervalIntegrable (fun t : ℝ => rexp (-t) * t ^ (c : ℝ)) volume 0 X := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  let f : ℝ → ℝ := fun t => rexp (-t) * t ^ (c : ℝ)
  let g : ℝ → ℝ := fun t => |t ^ (c : ℝ)|
  have hgI : IntegrableOn g (Ioc 0 X) := by
    have hgint : IntervalIntegrable (fun t : ℝ => |t ^ (c : ℝ)|) volume 0 X := by
      have h0 : IntervalIntegrable (fun t : ℝ => t ^ (c : ℝ)) volume 0 X := by
        exact intervalIntegral.intervalIntegrable_rpow' (by linarith : (-1 : ℝ) < c)
      exact h0.abs
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mp hgint
  have hcont : Continuous (fun t : ℝ => rexp (-t) * t ^ (c : ℝ)) := by
    have h1 : Continuous (fun t : ℝ => rexp (-t)) := by fun_prop
    exact h1.mul (Real.continuous_rpow_const hc)
  have hfmeas : AEStronglyMeasurable f (volume.restrict (Ioc 0 X)) := by
    dsimp [f]
    exact hcont.aestronglyMeasurable
  have hle_pt : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ ‖g t‖ := by
    intro t ht
    have h1 : |rexp (-t)| = rexp (-t) := abs_of_nonneg (le_of_lt (Real.exp_pos (-t)))
    have hnonneg : 0 ≤ t ^ (c : ℝ) := Real.rpow_nonneg ht c
    have hg : ‖g t‖ = t ^ (c : ℝ) := by
      dsimp [g]
      simp [abs_of_nonneg hnonneg]
    have hlef : ‖f t‖ ≤ rexp (-t) * t ^ (c : ℝ) := by
      dsimp [f]
      simp [abs_mul, h1, abs_of_nonneg hnonneg]
    have hexp : rexp (-t) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (by linarith : -t ≤ 0)
      simpa using h
    calc
      ‖f t‖ ≤ rexp (-t) * t ^ (c : ℝ) := hlef
      _ ≤ 1 * t ^ (c : ℝ) := by
        exact mul_le_mul_of_nonneg_right hexp hnonneg
      _ = t ^ (c : ℝ) := by ring
      _ = ‖g t‖ := hg.symm
  have hle : (fun x => ‖f x‖) ≤ᵐ[volume.restrict (Ioc 0 X)] fun x => ‖g x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hle_pt t (le_of_lt ht.1)
  change Integrable f (volume.restrict (Ioc 0 X))
  exact Integrable.mono hgI.integrable hfmeas hle

/-- integrability of `e^{-t}·t^{c-1}` on `Ioi 0` for `0 < c`. -/
lemma integrableOn_exp_mul_rpow_Ioi (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => rexp (-t) * t ^ (c - 1)) (Ioi (0 : ℝ)) := by
  simpa using (Real.GammaIntegral_convergent (s := c) hc)

/-- `∫_{Ioi 0} e^{-t}·t^{σ+1} ≤ 1 + constInt R` for `0 < σ ≤ R`. -/
lemma constInt_ge (R : ℝ) {σ : ℝ} (hσpos : 0 < σ) (hσR : σ ≤ R) :
    (∫ t in Ioi (0 : ℝ), rexp (-t) * t ^ (σ + 1)) ≤ 1 + constInt R := by
  let f : ℝ → ℝ := fun t => rexp (-t) * t ^ (σ + 1)
  let g : ℝ → ℝ := fun t => rexp (-t) * t ^ (R + 1)
  have hσ1 : 0 < σ + 2 := by linarith
  have hg0 : IntegrableOn g (Ioi (0 : ℝ)) := by
    have hmain := integrableOn_exp_mul_rpow_Ioi (R + 2) (by linarith : 0 < R + 2)
    convert hmain using 1
    ext t
    dsimp [g]
    congr 1
    ring
  have hf0 : IntegrableOn f (Ioi (0 : ℝ)) := by
    have hmain := Real.GammaIntegral_convergent (s := σ + 2) hσ1
    convert hmain using 1
    ext t
    dsimp [f]
    congr 1
    ring
  have hsubset01 : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := by
    exact Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)
  have hf1 : IntegrableOn f (Ioi (1 : ℝ)) := hf0.mono_set hsubset01
  have hg1 : IntegrableOn g (Ioi (1 : ℝ)) := hg0.mono_set hsubset01
  have hf01 : IntervalIntegrable f volume 0 1 := by
    dsimp [f]
    exact intervalIntegrable_exp_mul_rpow (σ + 1) (by linarith : 0 ≤ σ + 1) 1 (by norm_num)
  have hadd := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := 1) (f := f) hf0 hf1
  have hb01 : (∫ t in (0 : ℝ)..1, f t) ≤ 1 := by
    have hmono : ∀ x ∈ Set.Icc 0 1, f x ≤ (1 : ℝ) := by
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hx1 : x ≤ 1 := hx.2
      have he : rexp (-x) ≤ 1 := by
        have h := Real.exp_le_exp.mpr (by linarith : -x ≤ 0)
        simpa using h
      have hp : x ^ (σ + 1) ≤ 1 := by
        exact Real.rpow_le_one hx0 hx1 (by linarith : 0 ≤ σ + 1)
      have hn1 : 0 ≤ x ^ (σ + 1) := Real.rpow_nonneg hx0 (σ + 1)
      calc
        f x = rexp (-x) * x ^ (σ + 1) := rfl
        _ ≤ 1 * 1 := mul_le_mul he hp hn1 (by norm_num)
        _ = 1 := by ring
    have hc1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable_of_Icc (a := 0) (b := 1) (by norm_num)
      exact continuous_const.continuousOn
    have hle := intervalIntegral.integral_mono_on (f := f) (g := fun _ : ℝ => (1 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1) hf01 hc1 hmono
    have hval : (∫ t in (0 : ℝ)..1, (1 : ℝ)) = 1 := by
      rw [intervalIntegral.integral_const]
      norm_num
    linarith
  have hpt : ∀ x : ℝ, x ∈ Ioi (1 : ℝ) → f x ≤ g x := by
    intro t ht
    have hlt : (1 : ℝ) < t := by simpa using ht
    have ht1 : 1 ≤ t := le_of_lt hlt
    have hσ1le : σ + 1 ≤ R + 1 := by linarith
    have hr := Real.rpow_le_rpow_of_exponent_le ht1 hσ1le
    have hE : 0 ≤ rexp (-t) := le_of_lt (Real.exp_pos (-t))
    calc
      f t = rexp (-t) * t ^ (σ + 1) := rfl
      _ ≤ rexp (-t) * t ^ (R + 1) := mul_le_mul_of_nonneg_left hr hE
  have hb1 : (∫ t in Ioi (1 : ℝ), f t) ≤ ∫ t in Ioi (1 : ℝ), g t := by
    exact MeasureTheory.setIntegral_mono_on (μ := volume) (f := f) (g := g) (s := Ioi (1 : ℝ))
      hf1 hg1 measurableSet_Ioi hpt
  have hb2 : (∫ t in Ioi (1 : ℝ), g t) ≤ ∫ t in Ioi (0 : ℝ), g t := by
    apply MeasureTheory.setIntegral_mono_set (f := g) (s := Ioi (1 : ℝ)) (t := Ioi (0 : ℝ))
      (μ := volume) hg0
    · -- 0 ≤ᵐ[volume.restrict (Ioi 0)] g
      change ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), (0 : ℝ) ≤ g x
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall ?_
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa using hx
      dsimp [g]
      positivity
    · -- Ioi 1 ≤ᵐ[volume] Ioi 0
      refine Eventually.of_forall ?_
      intro x hx
      exact hsubset01 hx
  calc
    (∫ t in Ioi (0 : ℝ), f t) = (∫ t in (0 : ℝ)..1, f t) + ∫ t in Ioi (1 : ℝ), f t := by
      exact hadd.symm
    _ ≤ 1 + (∫ t in Ioi (1 : ℝ), g t) := by exact add_le_add hb01 hb1
    _ ≤ 1 + constInt R := by
      have hb2' : (∫ t in Ioi (1 : ℝ), g t) ≤ constInt R := by
        simpa [constInt] using hb2
      linarith

/-- main estimate: `‖Γ_N(s) - Γ(s)‖ ≤ (4/N)(1 + constInt R) + tailInt R N`. -/
lemma gammaSeq_sub_norm_le (s : ℂ) (R : ℝ) (hσpos : 0 < s.re) (hσR : s.re ≤ R)
    {N : ℕ} (hN : 2 ≤ N) :
    ‖Complex.GammaSeq s N - Complex.Gamma s‖ ≤
      (4 / (N : ℝ)) * (1 + constInt R) + tailInt R (N : ℝ) := by
  have hNge : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hRpos : 0 < R := by linarith
  have hseq := gammaSeq_sub_integral s hσpos hN
  let A := ∫ t in (0 : ℝ)..(N : ℝ), Eg s t - Gg s N t
  let B := ∫ t in Ioi (N : ℝ), Eg s t
  have hsig : ‖Complex.Gamma s - Complex.GammaSeq s N‖ ≤ ‖A‖ + ‖B‖ := by
    dsimp [A, B]
    rw [hseq]
    exact norm_add_le _ _
  have hA : ‖A‖ ≤ (4 / (N : ℝ)) * (1 + constInt R) := by
    -- ‖∫0..N (Eg−Gg)‖ ≤ ∫0..N (4/N)e^{-t}t^{σ+1} ≤ (4/N)(1 + J)
    dsimp [A]
    -- step 1: bound by integral of domination
    have hbound : IntervalIntegrable (fun t : ℝ => (4 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1))
        volume 0 (N : ℝ) := by
      apply ContinuousOn.intervalIntegrable_of_Icc (a := 0) (b := (N : ℝ)) hNge
      have hct : Continuous (fun t : ℝ => (4 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1)) := by
        have hc1 : Continuous (fun t : ℝ => rexp (-t)) := by fun_prop
        have hc2 : Continuous (fun t : ℝ => t ^ (s.re + 1)) :=
          Real.continuous_rpow_const (q := s.re + 1) (by linarith : 0 ≤ s.re + 1)
        exact ((continuous_const.mul hc1).mul hc2)
      exact hct.continuousOn
    have hnorm1 : ‖∫ t in (0 : ℝ)..(N : ℝ), Eg s t - Gg s N t‖ ≤
        ∫ t in (0 : ℝ)..(N : ℝ), (4 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hNge
      · -- ∀ᵐ t ∂volume, t ∈ Ioc 0 N → ‖Eg−Gg‖(t) ≤ bound(t)
        refine Eventually.of_forall ?_
        intro t ht
        have ht0 : 0 < t := ht.1
        have htN : t ≤ (N : ℝ) := ht.2
        exact norm_diff_le_four_N s hN ht0 htN
      · exact hbound
    -- step 2: bound ∫0..N (4/N) w ≤ (4/N)(1+J)
    have hw_int_i : IntegrableOn (fun t : ℝ => rexp (-t) * t ^ (s.re + 1)) (Ioi (0 : ℝ)) := by
      convert (integrableOn_exp_mul_rpow_Ioi (s.re + 2) (by linarith : 0 < s.re + 2)) using 1
      ext t
      congr 1
      ring
    have hw_ii : IntervalIntegrable (fun t : ℝ => rexp (-t) * t ^ (s.re + 1)) volume 0 (N : ℝ) := by
      exact intervalIntegrable_exp_mul_rpow (s.re + 1) (by linarith : 0 ≤ s.re + 1) (N : ℝ) hNge
    have hle_0N : (∫ t in (0 : ℝ)..(N : ℝ), rexp (-t) * t ^ (s.re + 1)) ≤
        ∫ t in Ioi (0 : ℝ), rexp (-t) * t ^ (s.re + 1) := by
      have hEq : (∫ t in (0 : ℝ)..(N : ℝ), rexp (-t) * t ^ (s.re + 1)) =
          ∫ t in Ioc 0 (N : ℝ), rexp (-t) * t ^ (s.re + 1) := by
        exact intervalIntegral.integral_of_le hNge
      rw [hEq]
      apply MeasureTheory.setIntegral_mono_set
        (f := fun t : ℝ => rexp (-t) * t ^ (s.re + 1)) (s := Ioc 0 (N : ℝ))
        (t := Ioi (0 : ℝ)) (μ := volume) hw_int_i
      · change ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), (0 : ℝ) ≤ rexp (-x) * x ^ (s.re + 1)
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall ?_
        intro x hx
        have hx0 : (0 : ℝ) < x := by simpa using hx
        exact mul_nonneg (le_of_lt (Real.exp_pos (-x))) (Real.rpow_nonneg (le_of_lt hx0) (s.re + 1))
      · refine Eventually.of_forall ?_
        intro x hx
        change (0 : ℝ) < x
        exact hx.1
    have hJ : (∫ t in Ioi (0 : ℝ), rexp (-t) * t ^ (s.re + 1)) ≤ 1 + constInt R :=
      constInt_ge R hσpos hσR
    have hstep : (∫ t in (0 : ℝ)..(N : ℝ), (4 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1)) ≤
        (4 / (N : ℝ)) * (1 + constInt R) := by
      have hnonneg4 : 0 ≤ (4 / (N : ℝ)) := by positivity
      have hprod : (∫ t in (0 : ℝ)..(N : ℝ), (4 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1)) =
          (4 / (N : ℝ)) * (∫ t in (0 : ℝ)..(N : ℝ), rexp (-t) * t ^ (s.re + 1)) := by
        calc
          (∫ t in (0 : ℝ)..(N : ℝ), (4 / (N : ℝ)) * rexp (-t) * t ^ (s.re + 1))
              = ∫ t in (0 : ℝ)..(N : ℝ), (4 / (N : ℝ)) * (rexp (-t) * t ^ (s.re + 1)) := by
                  apply intervalIntegral.integral_congr
                  intro t ht
                  ring
          _ = (4 / (N : ℝ)) * (∫ t in (0 : ℝ)..(N : ℝ), rexp (-t) * t ^ (s.re + 1)) := by
                  exact intervalIntegral.integral_const_mul (r := (4 / (N : ℝ)))
                    (f := fun t : ℝ => rexp (-t) * t ^ (s.re + 1))
      rw [hprod]
      exact mul_le_mul_of_nonneg_left (le_trans hle_0N hJ) hnonneg4
    exact le_trans hnorm1 hstep
  have hB : ‖B‖ ≤ tailInt R (N : ℝ) := by
    dsimp [B]
    have hEN : IntegrableOn (Eg s) (Ioi (N : ℝ)) := (integrableOn_Eg_Ioi s hσpos).mono_set (by
        intro t ht
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
        have hlt : (N : ℝ) < t := by simpa using ht
        change (0 : ℝ) < t
        linarith)
    have hnn : ‖∫ t in Ioi (N : ℝ), Eg s t‖ ≤ ∫ t in Ioi (N : ℝ), ‖Eg s t‖ := by
      simpa using (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Ioi (N : ℝ))) (f := Eg s))
    have hg_i : IntegrableOn (fun t : ℝ => rexp (-t) * t ^ (R - 1)) (Ioi (N : ℝ)) :=
      (integrableOn_exp_mul_rpow_Ioi R hRpos).mono_set (by
        intro t ht
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
        have hlt : (N : ℝ) < t := by simpa using ht
        change (0 : ℝ) < t
        linarith)
    have hpt : ∀ t : ℝ, t ∈ Ioi (N : ℝ) → ‖Eg s t‖ ≤ rexp (-t) * t ^ (R - 1) := by
      intro t ht
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
      have hltN : (N : ℝ) < t := by simpa using ht
      have ht0 : 0 < t := by linarith
      have ht1 : 1 ≤ t := by
        have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have h1 := norm_Eg s ht0
      rw [h1]
      have hle := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith : s.re - 1 ≤ R - 1)
      exact mul_le_mul_of_nonneg_left hle (le_of_lt (Real.exp_pos (-t)))
    have hmono2 : (∫ t in Ioi (N : ℝ), ‖Eg s t‖) ≤ ∫ t in Ioi (N : ℝ), rexp (-t) * t ^ (R - 1) := by
      exact MeasureTheory.setIntegral_mono_on (μ := volume) (f := fun t : ℝ => ‖Eg s t‖)
        (g := fun t : ℝ => rexp (-t) * t ^ (R - 1)) (s := Ioi (N : ℝ))
        hEN.integrable.norm hg_i measurableSet_Ioi hpt
    calc
      ‖∫ t in Ioi (N : ℝ), Eg s t‖ ≤ ∫ t in Ioi (N : ℝ), ‖Eg s t‖ := hnn
      _ ≤ ∫ t in Ioi (N : ℝ), rexp (-t) * t ^ (R - 1) := hmono2
      _ = tailInt R (N : ℝ) := rfl
  calc
    ‖Complex.GammaSeq s N - Complex.Gamma s‖ = ‖Complex.Gamma s - Complex.GammaSeq s N‖ := by
      rw [← norm_neg]
      congr 1
      ring
    _ ≤ ‖A‖ + ‖B‖ := by simpa [A, B] using hsig
    _ ≤ (4 / (N : ℝ)) * (1 + constInt R) + tailInt R (N : ℝ) := by exact add_le_add hA hB


/-- `tailInt R N → 0` along `N : ℕ` for `0 < R`. -/
lemma tendsto_tailInt_nat (R : ℝ) (hR : 0 < R) :
    Tendsto (fun N : ℕ => tailInt R (N : ℝ)) atTop (𝓝 0) := by
  have hb : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hmain := MeasureTheory.tendsto_integral_Ioi_zero (μ := volume) (l := atTop)
    (f := fun t : ℝ => rexp (-t) * t ^ (R - 1)) hb
  simpa [tailInt] using hmain

/-- uniform convergence of the Euler products to `Γ` on vertical strips inside the
right half-plane. -/
theorem GammaSeq_tendstoUniformlyOn_strip (δ R : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R) :
    TendstoUniformlyOn (fun N z => Complex.GammaSeq z N) Complex.Gamma atTop
      {z : ℂ | δ ≤ z.re ∧ z.re ≤ R} := by
  have hR : 0 < R := lt_of_lt_of_le hδ hδR
  have ht1 : Tendsto (fun N : ℕ => (4 / (N : ℝ)) * (1 + constInt R)) atTop (𝓝 0) := by
    have hmain := tendsto_const_div_atTop_nhds_zero_nat (4 : ℝ)
    simpa [mul_comm] using hmain.const_mul (1 + constInt R)
  have ht2 : Tendsto (fun N : ℕ => tailInt R (N : ℝ)) atTop (𝓝 0) := tendsto_tailInt_nat R hR
  have hsum : Tendsto (fun N : ℕ => (4 / (N : ℝ)) * (1 + constInt R) + tailInt R (N : ℝ))
      atTop (𝓝 0) := by simpa using ht1.add ht2
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev : ∀ᶠ N : ℕ in atTop,
      (4 / (N : ℝ)) * (1 + constInt R) + tailInt R (N : ℝ) < ε := by
    exact hsum (Iio_mem_nhds hε)
  filter_upwards [hev, eventually_ge_atTop 2] with N hNlt hN2
  intro z hz
  have hzδ : δ ≤ z.re := hz.1
  have hzR : z.re ≤ R := hz.2
  have hzpos : 0 < z.re := lt_of_lt_of_le hδ hzδ
  have hbd := gammaSeq_sub_norm_le z R hzpos hzR hN2
  have hne : ‖Complex.GammaSeq z N - Complex.Gamma z‖ < ε := lt_of_le_of_lt hbd hNlt
  have hne2 : ‖Complex.Gamma z - Complex.GammaSeq z N‖ < ε := by
    have hh : Complex.Gamma z - Complex.GammaSeq z N = -(Complex.GammaSeq z N - Complex.Gamma z) := by ring
    rw [hh, norm_neg]
    exact hne
  rw [dist_eq_norm]
  exact hne2

/-- Euler's limit formula for the Gamma function converges uniformly on closed balls
contained in the right half-plane. -/
theorem GammaSeq_tendstoUniformlyOn_closedBall (a : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : 0 < a.re - r) :
    TendstoUniformlyOn (fun N z => Complex.GammaSeq z N) Complex.Gamma atTop
      (Metric.closedBall a r) := by
  let δ : ℝ := a.re - r
  let R : ℝ := a.re + r
  have hmem : Metric.closedBall a r ⊆ {z : ℂ | δ ≤ z.re ∧ z.re ≤ R} := by
    intro z hz
    have hdist : dist z a ≤ r := by simpa [Metric.mem_closedBall] using hz
    have habs : |z.re - a.re| ≤ r := by
      have h1 := Complex.abs_re_le_norm (z - a)
      have h2 : |(z - a).re| = |z.re - a.re| := by simp
      have h3 : ‖z - a‖ = dist z a := by rw [dist_eq_norm]
      rw [h2, h3] at h1
      simpa [dist_comm] using h1.trans hdist
    have hlo : -(r) ≤ z.re - a.re := (abs_le.mp habs).1
    have hhi : z.re - a.re ≤ r := (abs_le.mp habs).2
    constructor <;> dsimp [δ, R] <;> linarith
  have hstrip : TendstoUniformlyOn (fun N z => Complex.GammaSeq z N) Complex.Gamma atTop
      {z : ℂ | δ ≤ z.re ∧ z.re ≤ R} := by
    exact GammaSeq_tendstoUniformlyOn_strip δ R (by dsimp [δ]; exact ha)
      (by dsimp [δ, R]; nlinarith)
  exact hstrip.mono hmem