import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.ZFRStatementDefs
import Submission.Work.FIArea6Hecke.R.CompletionStrictDefs
import Submission.Work.FIArea6Hecke.R.noCompletion_of_primaryTrivial

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open MeasureTheory Set Filter
open scoped Topology BigOperators

noncomputable section

open Work.FIArea5.S16Hecke
open Work.FIPlan

/-! ## Auxiliary measure-theoretic and Gaussian facts -/

/-- Summability over `ℤ` of the Gaussian `n ↦ e^{-β n²}`. -/
lemma summable_int_exp_neg_sq (β : ℝ) (hβ : 0 < β) :
    Summable (fun n : ℤ => Real.exp (-(β * (n : ℝ) ^ 2))) := by
  set g : ℝ → ℝ := fun x => Real.exp (-(β * x ^ 2)) with hg
  have hanti : AntitoneOn g (Ici 0) := by
    intro a ha b hb hab
    simp only [hg]
    rw [Real.exp_le_exp]
    nlinarith [mul_self_le_mul_self ha hab, hβ]
  have hint : IntegrableOn g (Ioi 0) := by
    rw [hg]
    simpa using integrableOn_rpow_mul_exp_neg_mul_sq (b := β) hβ (s := 0) (by norm_num)
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ g t := fun t _ => (Real.exp_pos _).le
  have hsumm_nat : Summable (fun n : ℕ => g n) := hanti.summable_of_integrableOn_Ioi_zero hint hnn
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨hsumm_nat.congr (fun n => ?_), hsumm_nat.congr (fun n => ?_)⟩
  · simp only [hg, Int.cast_natCast]
  · simp only [hg, Int.cast_neg, Int.cast_natCast]
    congr 1
    ring

/-- Sum over `ℤ` of a Gaussian: `∑_n e^{-β n²} ≤ 1 + √(π/β)`. -/
lemma int_tsum_exp_neg_sq_le (β : ℝ) (hβ : 0 < β) :
    ∑' n : ℤ, Real.exp (-(β * (n : ℝ) ^ 2)) ≤ 1 + Real.sqrt (Real.pi / β) := by
  set g : ℝ → ℝ := fun x => Real.exp (-(β * x ^ 2)) with hg
  have hanti : AntitoneOn g (Ici 0) := by
    intro a ha b hb hab
    simp only [hg]
    rw [Real.exp_le_exp]
    have hsq : a * a ≤ b * b := mul_self_le_mul_self ha hab
    nlinarith [hsq, hβ]
  have hint : IntegrableOn g (Ioi 0) := by
    rw [hg]
    simpa using integrableOn_rpow_mul_exp_neg_mul_sq (b := β) hβ (s := 0) (by norm_num)
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ g t := fun t _ => (Real.exp_pos _).le
  have hsumm_nat : Summable (fun n : ℕ => g n) := hanti.summable_of_integrableOn_Ioi_zero hint hnn
  have hInt : ∫ x in Ioi (0 : ℝ), g x = Real.sqrt (Real.pi / β) / 2 := by
    rw [hg]; simpa using integral_gaussian_Ioi β
  have htail : ∑' n : ℕ, g ↑(n + 1) ≤ Real.sqrt (Real.pi / β) / 2 := by
    have h := hanti.tsum_add_one_le_integral hint hnn
    rw [hInt] at h
    exact h
  set f : ℤ → ℝ := fun n => Real.exp (-(β * (n : ℝ) ^ 2)) with hf
  have hfg : ∀ n : ℕ, f (n : ℤ) = g n := by intro n; simp only [hf, hg, Int.cast_natCast]
  have heven : Function.Even f := by
    intro n
    simp only [hf]
    rw [show ((-n : ℤ) : ℝ) = -(n : ℝ) by push_cast; ring]
    ring_nf
  have hsumm_int : Summable f := by
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨hsumm_nat.congr (fun n => (hfg n).symm),
      hsumm_nat.congr (fun n => by rw [heven]; exact hfg n)⟩
  have hpn : ∑' n : ℕ+, f n ≤ Real.sqrt (Real.pi / β) / 2 := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => f (n : ℤ))]
    calc ∑' n : ℕ, f ↑(n + 1) = ∑' n : ℕ, g ↑(n + 1) := tsum_congr (fun n => hfg (n + 1))
      _ ≤ Real.sqrt (Real.pi / β) / 2 := htail
  have h0 : f 0 = 1 := by simp [hf]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsumm_int, h0, two_nsmul]
  have h3 : (2 : ℝ) * (Real.sqrt (Real.pi / β) / 2) = Real.sqrt (Real.pi / β) := by ring
  linarith [hpn, h3]

/-- `∑_{z ∈ ℤ[i]} e^{-β |z|²} ≤ (1 + √(π/β))²`. -/
lemma gaussianInt_tsum_exp_le (β : ℝ) (hβ : 0 < β) :
    ∑' z : GaussianInt, Real.exp (-(β * (gnorm z : ℝ))) ≤ (1 + Real.sqrt (Real.pi / β)) ^ 2 := by
  have hsumm_n : Summable (fun n : ℤ => Real.exp (-(β * (n : ℝ) ^ 2))) :=
    summable_int_exp_neg_sq β hβ
  have hnorm : Summable (fun n : ℤ => ‖Real.exp (-(β * (n : ℝ) ^ 2))‖) := hsumm_n.norm
  have hprodeq : (∑' n : ℤ, Real.exp (-(β * (n : ℝ) ^ 2))) ^ 2
      = ∑' p : ℤ × ℤ, Real.exp (-(β * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    rw [sq, tsum_mul_tsum_of_summable_norm hnorm hnorm]
    refine tsum_congr (fun p => ?_)
    rw [← Real.exp_add]; congr 1; ring
  have hpair : ∑' z : GaussianInt, Real.exp (-(β * (gnorm z : ℝ)))
      = ∑' p : ℤ × ℤ, Real.exp (-(β * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) := by
    rw [← Equiv.tsum_eq gaussEquiv (fun z : GaussianInt => Real.exp (-(β * (gnorm z : ℝ))))]
    exact tsum_congr (fun p => by simp only [gaussEquiv, Equiv.coe_fn_mk, gnorm_mk_cast])
  rw [hpair, ← hprodeq]
  exact pow_le_pow_left₀ (tsum_nonneg (fun n => (Real.exp_pos _).le)) (int_tsum_exp_neg_sq_le β hβ) 2

/-- The Gaussian sum at `β = π/(16d²) = π · completionCut d`. -/
lemma gaussianTsumExp {d : ℕ} (hd : 1 ≤ d) :
    ∑' z : GaussianInt, Real.exp (-(Real.pi * completionCut d * (gnorm z : ℝ)))
      ≤ 100 * (d : ℝ) ^ 2 := by
  have hd0 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hβ : 0 < Real.pi * completionCut d := by
    rw [completionCut]; positivity
  refine (gaussianInt_tsum_exp_le (Real.pi * completionCut d) hβ).trans ?_
  have hsqrt : Real.sqrt (Real.pi / (Real.pi * completionCut d)) = 4 * (d : ℝ) := by
    have hc : Real.pi / (Real.pi * completionCut d) = (4 * (d : ℝ)) ^ 2 := by
      have hne : Real.pi * completionCut d ≠ 0 := by rw [completionCut]; positivity
      rw [div_eq_iff hne, completionCut]
      rw [show (4 * (d : ℝ)) ^ 2 * (Real.pi * (1 / (4 * (d : ℝ)) ^ 2))
            = Real.pi * ((4 * (d : ℝ)) ^ 2 * (1 / (4 * (d : ℝ)) ^ 2)) by ring]
      rw [mul_one_div, div_self (by positivity), mul_one]
    rw [hc, Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  nlinarith [hd0]

/-! ## Generic Mellin bounds on the two cuts -/

/-- Low-cut Mellin bound: a function supported on `(0,c]` with `‖f u‖ ≤ C u⁻¹ e^{-δ/u}` has
Mellin transform bounded by `2C√c/δ` in the strip `-1/2 ≤ re s - 1 ≤ 1`. -/
lemma mellinLowBound {c C δ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ) (hC : 0 ≤ C)
    {f : ℝ → ℂ} (hfmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ u : ℝ, c ≤ u → f u = 0)
    (hdec : ∀ u : ℝ, 0 < u → u ≤ c → ‖f u‖ ≤ C * (1 / u) * Real.exp (-δ / u)) :
    ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re - 1 → s.re - 1 ≤ 1 →
      ‖mellin f s‖ ≤ 2 * C * Real.sqrt c / δ := by
  intro s hs1 hs2
  set h : ℝ → ℝ := fun u => C * u ^ (-(1 / 2 : ℝ)) / δ with hh
  set G : ℝ → ℝ := (Ioc 0 c).indicator h with hG
  have hGint : Integrable G (volume.restrict (Ioi 0)) := by
    rw [hG]
    change IntegrableOn ((Ioc 0 c).indicator h) (Ioi 0) volume
    rw [integrableOn_indicator_iff measurableSet_Ioc]
    rw [show Ioc 0 c ∩ Ioi (0 : ℝ) = Ioc 0 c from by ext u; simp [Set.mem_Ioc]]
    rw [hh, ← intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le]
    exact ((intervalIntegral.intervalIntegrable_rpow'
      (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul C).div_const δ
  have hintG : ∫ u in Ioi (0 : ℝ), G u = 2 * C * Real.sqrt c / δ := by
    rw [hG, setIntegral_indicator measurableSet_Ioc]
    rw [show Ioi (0 : ℝ) ∩ Ioc 0 c = Ioc 0 c from by ext u; simp [Set.mem_Ioc]]
    rw [show (fun u : ℝ => C * u ^ (-(1 / 2 : ℝ)) / δ)
        = (fun u : ℝ => (C / δ) * u ^ (-(1 / 2 : ℝ))) from by funext u; ring]
    rw [← intervalIntegral.integral_of_le hc.le, intervalIntegral.integral_const_mul]
    have hr : ∫ u in (0 : ℝ)..c, u ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt c := by
      rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
      rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num, Real.zero_rpow (by norm_num), sub_zero]
      rw [show c ^ (1 / 2 : ℝ) = Real.sqrt c by rw [Real.sqrt_eq_rpow]]
      ring
    rw [hr]
    ring
  have hpt : ∀ u ∈ Ioi (0 : ℝ), ‖(u : ℂ) ^ (s - 1) • f u‖ ≤ G u := by
    intro u hu
    rw [mem_Ioi] at hu
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re, Complex.one_re]
    by_cases huc : u ≤ c
    · rw [hG, Set.indicator_of_mem (show u ∈ Ioc 0 c from ⟨hu, huc⟩), hh]
      have h1 := hdec u hu huc
      have hy : 0 < δ / u := by positivity
      have hexp : Real.exp (-δ / u) ≤ u / δ := by
        rw [show -δ / u = -(δ / u) by ring, Real.exp_neg]
        rw [show u / δ = (δ / u)⁻¹ by rw [inv_div]]
        exact (inv_le_inv₀ (Real.exp_pos (δ / u)) hy).mpr
          (le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp (δ / u)))
      have hrpow : u ^ (s.re - 1) ≤ u ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_ge hu (le_trans huc hc1) (by linarith [hs1])
      have hstep : ‖f u‖ ≤ C * (1 / u) * (u / δ) := by
        refine h1.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
      calc u ^ (s.re - 1) * ‖f u‖
          ≤ u ^ (-(1 / 2 : ℝ)) * (C * (1 / u) * (u / δ)) :=
            mul_le_mul hrpow hstep (norm_nonneg _) (Real.rpow_nonneg hu.le _)
        _ = C * u ^ (-(1 / 2 : ℝ)) / δ := by
            field_simp <;> ring
    · push_neg at huc
      have hnot : u ∉ Ioc 0 c := by
        simp only [Set.mem_Ioc, not_and]; exact fun _ => not_le.mpr huc
      rw [hf u (le_of_lt huc), norm_zero, mul_zero, hG, Set.indicator_of_notMem hnot]
  rw [mellin]
  refine (norm_integral_le_of_norm_le hGint ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpt u hu
  · rw [hintG]

/-- High-cut Mellin bound: a function supported on `[c,∞)` with `‖f u‖ ≤ C e^{-π(u-c)}` has
Mellin transform bounded by `C (2 + e^{πc}/π²)` in the strip `-1/2 ≤ re s - 1 ≤ 1`. -/
lemma mellinHighBound {c C : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 ≤ C)
    {f : ℝ → ℂ} (hfmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hf : ∀ u : ℝ, u < c → f u = 0)
    (hdec : ∀ u : ℝ, c ≤ u → ‖f u‖ ≤ C * Real.exp (-(Real.pi * (u - c)))) :
    ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re - 1 → s.re - 1 ≤ 1 →
      ‖mellin f s‖ ≤ C * (Real.exp (Real.pi * c) * (1 + 1 / Real.pi ^ 2)) := by
  intro s hs1 hs2
  have hsub : Ioi (0 : ℝ) ∩ Ici c = Ici c := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
    exact ⟨fun h => h.2, fun h => ⟨lt_of_lt_of_le hc h, h⟩⟩
  have hsub2 : Ici c ∩ Ioi (0 : ℝ) = Ici c := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
    exact ⟨fun h => h.1, fun h => ⟨h, lt_of_lt_of_le hc h⟩⟩
  have hi1 : IntegrableOn (fun u : ℝ => u ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * u)))
      (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2 : ℝ))
      (by norm_num) (by norm_num) Real.pi_pos
    simpa using h
  have hi2 : IntegrableOn (fun u : ℝ => u * Real.exp (-(Real.pi * u))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (1 : ℝ))
      (by norm_num) (by norm_num) Real.pi_pos
    simpa using h
  have hI1 : ∫ u : ℝ in Ioi 0, u ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * u)) = 1 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (1 : ℝ) / 2) (r := Real.pi)
      (by norm_num) Real.pi_pos
    rw [show (1 : ℝ) / 2 - 1 = -(1 / 2 : ℝ) by norm_num] at h
    rw [h, Real.Gamma_one_half_eq]
    have h1 : (1 : ℝ) ^ ((1 : ℝ) / 2) = 1 := by simp
    have hsqrt : (1 / Real.pi : ℝ) ^ ((1 : ℝ) / 2) = (Real.sqrt Real.pi)⁻¹ := by
      rw [Real.div_rpow (by norm_num) (le_of_lt Real.pi_pos), h1, ← Real.sqrt_eq_rpow, one_div]
    rw [hsqrt]
    rw [inv_mul_cancel₀ (by positivity : (Real.sqrt Real.pi) ≠ 0)]
  have hI2 : ∫ u : ℝ in Ioi 0, u * Real.exp (-(Real.pi * u)) = 1 / Real.pi ^ 2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := Real.pi)
      (by norm_num) Real.pi_pos
    rw [show (2 : ℝ) - 1 = 1 by norm_num] at h
    simp only [Real.rpow_one] at h
    rw [h]
    have hg : Real.Gamma 2 = 1 := by
      rw [show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num]
      simpa using Real.Gamma_nat_eq_factorial 1
    have h2 : (1 / Real.pi : ℝ) ^ (2 : ℝ) = 1 / Real.pi ^ 2 := by
      rw [Real.rpow_two]; ring_nf
    rw [hg, mul_one]
    exact h2
  set K : ℝ := C * Real.exp (Real.pi * c) with hK
  set hI : ℝ → ℝ := fun u => u ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * u)) +
      u * Real.exp (-(Real.pi * u)) with hhI
  have hhI_int : IntegrableOn hI (Ioi 0) := by rw [hhI]; exact hi1.add hi2
  have hhI_val : ∫ u : ℝ in Ioi 0, hI u = 1 + 1 / Real.pi ^ 2 := by
    rw [hhI, integral_add hi1 hi2, hI1, hI2]
  set G : ℝ → ℝ := (Ici c).indicator (fun u => K * hI u) with hG
  have hGint : Integrable G (volume.restrict (Ioi 0)) := by
    rw [hG]
    change IntegrableOn ((Ici c).indicator (fun u => K * hI u)) (Ioi 0) volume
    rw [integrableOn_indicator_iff measurableSet_Ici, hsub2]
    exact IntegrableOn.mono_set (hhI_int.const_mul K) (Set.Ici_subset_Ioi.mpr hc)
  have hintG : ∫ u in Ioi (0 : ℝ), G u ≤ C * (Real.exp (Real.pi * c) * (1 + 1 / Real.pi ^ 2)) := by
    rw [hG, setIntegral_indicator measurableSet_Ici, hsub]
    have hbig : IntegrableOn (fun u => K * hI u) (Ioi 0) := hhI_int.const_mul K
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun u => K * hI u) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have h1 : 0 ≤ u ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * u)) :=
        mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_nonneg _)
      have h2 : 0 ≤ u * Real.exp (-(Real.pi * u)) := mul_nonneg hu.le (Real.exp_nonneg _)
      refine mul_nonneg ?_ ?_
      · rw [hK]; positivity
      · rw [hhI]; exact add_nonneg h1 h2
    calc ∫ u in Ici c, K * hI u ≤ ∫ u in Ioi (0 : ℝ), K * hI u :=
          setIntegral_mono_set hbig hnonneg (Set.Ici_subset_Ioi.mpr hc).eventuallyLE
      _ = K * (1 + 1 / Real.pi ^ 2) := by
          rw [MeasureTheory.integral_const_mul, hhI_val]
      _ = C * (Real.exp (Real.pi * c) * (1 + 1 / Real.pi ^ 2)) := by rw [hK]; ring
  have hpt : ∀ u ∈ Ioi (0 : ℝ), ‖(u : ℂ) ^ (s - 1) • f u‖ ≤ G u := by
    intro u hu
    rw [mem_Ioi] at hu
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re, Complex.one_re]
    by_cases huc : c ≤ u
    · rw [hG, Set.indicator_of_mem (show u ∈ Ici c from huc)]
      have h1 := hdec u huc
      have hrpow : u ^ (s.re - 1) ≤ u ^ (-(1 / 2 : ℝ)) + u := by
        by_cases hu1 : u ≤ 1
        · have h : u ^ (s.re - 1) ≤ u ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hu hu1 (by linarith [hs1])
          exact h.trans (le_add_of_nonneg_right hu.le)
        · push_neg at hu1
          have h : u ^ (s.re - 1) ≤ u ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hu1.le (by linarith [hs2])
          rw [Real.rpow_one] at h
          exact h.trans (le_add_of_nonneg_left (Real.rpow_nonneg hu.le _))
      calc u ^ (s.re - 1) * ‖f u‖
          ≤ (u ^ (-(1 / 2 : ℝ)) + u) * (C * Real.exp (-(Real.pi * (u - c)))) :=
            mul_le_mul hrpow h1 (norm_nonneg _) (by positivity)
        _ = K * hI u := by
            rw [hK, hhI, show -(Real.pi * (u - c)) = Real.pi * c + -(Real.pi * u) by ring,
              Real.exp_add]
            ring
    · push_neg at huc
      have hnot : u ∉ Ici c := by simp only [Set.mem_Ici]; exact not_le.mpr huc
      rw [hf u huc, norm_zero, mul_zero, hG, Set.indicator_of_notMem hnot]
  rw [mellin]
  refine (norm_integral_le_of_norm_le hGint ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpt u hu
  · exact hintG

/-! ## Explicit decay bounds for the theta series -/

/-- High decay of `thetaHol χ 0` past `completionCut d`. -/
lemma thetaHolHighDecayExplicit {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ∀ u : ℝ, completionCut d ≤ u →
      ‖thetaHol chi 0 u‖ ≤
        100 * (d : ℝ) ^ 2 * Real.exp (-(Real.pi * (u - completionCut d))) := by
  classical
  have hcpos : 0 < completionCut d := completionCut_pos hd
  set G : ℝ → GaussianInt → ℝ :=
    fun v z => if IsPrimary z then Real.exp (-(Real.pi * v * (gnorm z : ℝ))) else 0 with hG
  have hGnonneg : ∀ v z, 0 ≤ G v z := by
    intro v z; by_cases hz : IsPrimary z <;> simp [hG, hz, Real.exp_nonneg]
  have hGs : ∀ v : ℝ, 0 < v → Summable (G v) := by
    intro v hv
    refine Summable.of_nonneg_of_le (fun z => hGnonneg v z) (fun z => ?_)
      (summable_gnorm_exp v hv)
    by_cases hz : IsPrimary z <;> simp [hG, hz, Real.exp_nonneg]
  intro u hu
  have hu0 : 0 < u := lt_of_lt_of_le hcpos hu
  have hstep1 : ‖thetaHol chi 0 u‖ ≤ ∑' z : GaussianInt, G u z := by
    rw [thetaHol_eq_tsum]
    refine (norm_tsum_le_tsum_norm (summable_thetaSummand hu0 chi 0 hb).norm).trans ?_
    refine Summable.tsum_le_tsum (fun z => ?_) (summable_thetaSummand hu0 chi 0 hb).norm
      (hGs u hu0)
    by_cases hz : IsPrimary z
    · have h := thetaSummand_norm_le (chi := chi) (m := 0) (u := u) hb z
      simpa [hG, hz] using h
    · simp [hG, hz, thetaSummand]
  have hstep2 : ∑' z : GaussianInt, G u z ≤
      Real.exp (-(Real.pi * (u - completionCut d))) * ∑' z : GaussianInt, G (completionCut d) z := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun z => ?_) (hGs u hu0) ((hGs _ hcpos).mul_left _)
    by_cases hz : IsPrimary z
    · simp only [hG, if_pos hz]
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hg1 : (1 : ℝ) ≤ (gnorm z : ℝ) := by
        exact_mod_cast one_le_gnorm_of_isPrimary z hz
      have huc : 0 ≤ u - completionCut d := by linarith
      have hprod : 0 ≤ Real.pi * (u - completionCut d) * ((gnorm z : ℝ) - 1) :=
        mul_nonneg (mul_nonneg Real.pi_pos.le huc) (by linarith)
      nlinarith [hprod]
    · simp only [hG, if_neg hz, mul_zero, le_refl]
  have hstep3 : ∑' z : GaussianInt, G (completionCut d) z ≤ 100 * (d : ℝ) ^ 2 := by
    refine (Summable.tsum_le_tsum (fun z => ?_) (hGs _ hcpos)
      (summable_gnorm_exp _ hcpos)).trans (gaussianTsumExp hd)
    by_cases hz : IsPrimary z <;> simp [hG, hz, Real.exp_nonneg]
  calc ‖thetaHol chi 0 u‖ ≤ ∑' z : GaussianInt, G u z := hstep1
    _ ≤ Real.exp (-(Real.pi * (u - completionCut d))) * ∑' z : GaussianInt, G (completionCut d) z :=
        hstep2
    _ ≤ Real.exp (-(Real.pi * (u - completionCut d))) * (100 * (d : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hstep3 (Real.exp_pos _).le
    _ = 100 * (d : ℝ) ^ 2 * Real.exp (-(Real.pi * (u - completionCut d))) := by ring

/-- The `ℤ²`-Gaussian sum at `β = π · completionCut d`. -/
lemma intProdTsumExp {d : ℕ} (hd : 1 ≤ d) :
    ∑' p : ℤ × ℤ, Real.exp (-(Real.pi * completionCut d * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)))
      ≤ 100 * (d : ℝ) ^ 2 := by
  have h1 : (∑' p : ℤ × ℤ,
        Real.exp (-(Real.pi * completionCut d * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))))
      = ∑' z : GaussianInt, Real.exp (-(Real.pi * completionCut d * (gnorm z : ℝ))) := by
    rw [← Equiv.tsum_eq gaussEquiv
      (fun z : GaussianInt => Real.exp (-(Real.pi * completionCut d * (gnorm z : ℝ))))]
    exact tsum_congr (fun p => by simp only [gaussEquiv, Equiv.coe_fn_mk, gnorm_mk_cast])
  rw [h1]; exact gaussianTsumExp hd

lemma summable_intProd_exp {d : ℕ} (hd : 1 ≤ d) :
    Summable (fun p : ℤ × ℤ =>
      Real.exp (-(Real.pi * completionCut d * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)))) := by
  have hu : 0 < completionCut d := completionCut_pos hd
  have h := summable_gnorm_exp (completionCut d) hu
  rw [summable_gaussian_iff (fun z : GaussianInt => Real.exp
      (-(Real.pi * completionCut d * (gnorm z : ℝ))))] at h
  exact h.congr (fun p => by rw [gnorm_mk_cast])

/-- Explicit dual (Poisson) decay. -/
lemma heckeDualDecayExplicit {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (h0 : gaussSum d chi 0 = 0) :
    ∀ u : ℝ, 0 < u → u ≤ completionCut d →
      ‖hci_heckeDual d chi 0 u‖ ≤
        10000 * (d : ℝ) ^ 4 * Real.exp (-(Real.pi / (2 * (4 * (d : ℝ)) ^ 2)) / u) := by
  intro u hu hule
  have hu0 : 0 < completionCut d := completionCut_pos hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  set W : ℝ := Real.exp (-(Real.pi / (2 * (4 * (d : ℝ)) ^ 2)) / u) with hW
  have hWnn : 0 ≤ W := Real.exp_nonneg _
  -- exponential factor `e^{π/(4d)²} ≤ 4`
  have hexp4 : Real.exp (Real.pi / (4 * (d : ℝ)) ^ 2) ≤ 4 := by
    have hle : Real.pi / (4 * (d : ℝ)) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      have hge : (4 : ℝ) ≤ (4 * (d : ℝ)) ^ 2 := by
        nlinarith [hd1, sq_nonneg ((d : ℝ) - 1)]
      linarith [Real.pi_lt_four]
    refine (Real.exp_le_exp.mpr hle).trans ?_
    have h3 := Real.exp_one_lt_three
    linarith
  have hkey : ∀ ξ : ℤ × ℤ,
      ‖gaussSum d chi ⟨ξ.1, ξ.2⟩ *
        (((ξ.1 : ℂ) + Complex.I * (ξ.2 : ℂ)) / (((4 * d : ℕ) : ℂ))) ^ 0 *
        Complex.exp (-(Real.pi : ℂ) * (((ξ.1 : ℂ) ^ 2 + (ξ.2 : ℂ) ^ 2) /
          ((u : ℂ) * (((4 * d : ℕ) : ℂ)) ^ 2)))‖
      ≤ W * (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp (Real.pi / (4 * (d : ℝ)) ^ 2) *
          Real.exp (-(Real.pi * completionCut d * ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2)))) := by
    intro ξ
    have h := hci_norm_summand_le d hd chi 0 hchi (Or.inl h0) hu hule ξ
    refine h.trans (le_of_eq ?_)
    rw [hW]
    have h4 : (((4 * d : ℕ) : ℝ)) ^ 2 = 16 * (d : ℝ) ^ 2 := by push_cast; ring
    have hcc : Real.pi * completionCut d = Real.pi / (4 * (d : ℝ)) ^ 2 := by
      rw [completionCut]; ring
    have hpow : (2 : ℝ) ^ (0 : ℕ) = 1 := by norm_num
    have hpow2 : (1 + (ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) ^ (0 : ℕ) = 1 := by norm_num
    rw [hpow, hpow2, mul_one, one_mul, hcc]
    ring
  have hsumm : Summable (fun ξ : ℤ × ℤ => W *
      (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp (Real.pi / (4 * (d : ℝ)) ^ 2) *
        Real.exp (-(Real.pi * completionCut d * ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2))))) := by
    refine (((summable_intProd_exp hd).mul_left
      (W * (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp (Real.pi / (4 * (d : ℝ)) ^ 2))))).congr
      (fun ξ => ?_)
    ring
  rw [hci_heckeDual]
  refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun ξ => norm_nonneg _)
    (fun ξ => hkey ξ) hsumm)).trans ?_
  refine (Summable.tsum_le_tsum (fun ξ => hkey ξ)
    (Summable.of_nonneg_of_le (fun ξ => norm_nonneg _) (fun ξ => hkey ξ) hsumm) hsumm).trans ?_
  rw [tsum_mul_left]
  have hX : ∑' ξ : ℤ × ℤ,
        (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp (Real.pi / (4 * (d : ℝ)) ^ 2)) *
          Real.exp (-(Real.pi * completionCut d * ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2)))
      ≤ 10000 * (d : ℝ) ^ 4 := by
    calc ∑' ξ : ℤ × ℤ,
          (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp (Real.pi / (4 * (d : ℝ)) ^ 2)) *
            Real.exp (-(Real.pi * completionCut d * ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2)))
        = (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp (Real.pi / (4 * (d : ℝ)) ^ 2)) *
          ∑' ξ : ℤ × ℤ,
            Real.exp (-(Real.pi * completionCut d * ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2))) :=
          tsum_mul_left
      _ ≤ (((4 * d : ℕ) : ℝ) ^ 2 * 4) * (100 * (d : ℝ) ^ 2) := by
          refine mul_le_mul ?_ (intProdTsumExp hd) (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hexp4 (by positivity)
      _ ≤ 10000 * (d : ℝ) ^ 4 := by
          have h4 : (((4 * d : ℕ) : ℝ)) ^ 2 = 16 * (d : ℝ) ^ 2 := by push_cast; ring
          rw [h4]; nlinarith [hd1]
  calc W * (∑' ξ : ℤ × ℤ,
        (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp (Real.pi / (4 * (d : ℝ)) ^ 2)) *
          Real.exp (-(Real.pi * completionCut d * ((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2))))
      ≤ W * (10000 * (d : ℝ) ^ 4) := mul_le_mul_of_nonneg_left hX hWnn
    _ = 10000 * (d : ℝ) ^ 4 * W := by ring

/-- Low decay of `thetaHol χ 0` below `completionCut d`, when `χ` is non-trivial on the primary
units mod `4d`. -/
lemma thetaHolLowDecayExplicit {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi)
    (hne : ∃ z : GaussianInt, IsPrimary z ∧ IsUnitMod4d d z ∧ chi z ≠ 1) :
    ∀ u : ℝ, 0 < u → u ≤ completionCut d →
      ‖thetaHol chi 0 u‖ ≤
        2000 * (d : ℝ) ^ 2 * (1 / u) *
          Real.exp (-(Real.pi / (2 * (4 * (d : ℝ)) ^ 2)) / u) := by
  intro u hu hule
  set psi : GaussianInt → ℂ := twist chi 0 with hpsi
  have hpsi_strict : IsCharMod4dStrict d psi := by
    rw [hpsi]; exact twist_isCharMod4dStrict d hd chi 0 hchi
  have hU : unitSum psi 0 ≠ 0 := by
    rw [hpsi, twist_unitSum d hd chi 0 hchi.1]; norm_num
  have hne' : ∃ z : GaussianInt, IsPrimary z ∧ IsUnitMod4d d z ∧ psi z ≠ 1 := by
    obtain ⟨z, hzp, hzu, hzne⟩ := hne
    exact ⟨z, hzp, hzu, by rw [hpsi, twist_eq_of_isPrimary chi 0 hzp]; exact hzne⟩
  have h0 : gaussSum d psi 0 = 0 := gaussSum_zero_of_nontrivial hd hpsi_strict hne'
  have htw : thetaHol psi 0 u = thetaHol chi 0 u := by
    rw [hpsi]; exact thetaHol_twist_eq d chi 0 u
  have h1 : thetaHol psi 0 u = (unitSum psi 0)⁻¹ * thetaOdd psi 0 u :=
    hci_thetaHol_eq_inv_unitSum_mul psi 0 hpsi_strict.1.2.1 hU u
  have hpoi : thetaOdd psi 0 u =
      1 / (((4 * d : ℕ)) : ℂ) ^ 2 * (-Complex.I) ^ (0 : ℤ) * ((u : ℂ) ^ (0 + 1 : ℤ))⁻¹ *
        hci_heckeDual d psi 0 u := hci_thetaOdd_eq_poisson d hd psi hpsi_strict 0 hu
  have hdual := heckeDualDecayExplicit hd hpsi_strict h0 u hu hule
  rw [← htw, h1, hpoi, hpsi, twist_unitSum d hd chi 0 hchi.1]
  have hI : ‖(-Complex.I) ^ (0 : ℤ)‖ = 1 := by simp
  have hu1 : ‖((u : ℂ) ^ (0 + 1 : ℤ))⁻¹‖ = 1 / u := by
    rw [show (0 + 1 : ℤ) = 1 by norm_num, zpow_one, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hu, one_div]
  have h4 : ‖(4 : ℂ)⁻¹‖ = 1 / 4 := by rw [norm_inv, Complex.norm_ofNat]; norm_num
  have h4d : ‖(1 / (((4 * d : ℕ)) : ℂ) ^ 2)‖ = 1 / (4 * (d : ℝ)) ^ 2 := by
    rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
    congr 1
    push_cast; ring
  have hnormeq : ‖(4 : ℂ)⁻¹ * (1 / (((4 * d : ℕ)) : ℂ) ^ 2 * (-Complex.I) ^ (0 : ℤ) *
        ((u : ℂ) ^ (0 + 1 : ℤ))⁻¹ * hci_heckeDual d psi 0 u)‖
      = (1 / 4) * (1 / (4 * (d : ℝ)) ^ 2) * (1 / u) * ‖hci_heckeDual d psi 0 u‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, h4, h4d, hI, hu1]
    ring
  rw [hnormeq]
  refine (mul_le_mul_of_nonneg_left hdual (by positivity)).trans ?_
  have hle : (1 / 4 : ℝ) * (1 / (4 * (d : ℝ)) ^ 2) * (10000 * (d : ℝ) ^ 4) ≤
      2000 * (d : ℝ) ^ 2 := by
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have heq : (1 / 4 : ℝ) * (1 / (4 * (d : ℝ)) ^ 2) * (10000 * (d : ℝ) ^ 4)
        = (625 / 4 : ℝ) * (d : ℝ) ^ 2 := by
      field_simp
      ring
    rw [heq]
    nlinarith [sq_nonneg (d : ℝ)]
  rw [show (1 / 4 : ℝ) * (1 / (4 * (d : ℝ)) ^ 2) * (1 / u) *
      (10000 * (d : ℝ) ^ 4 * Real.exp (-(Real.pi / (2 * (4 * (d : ℝ)) ^ 2)) / u))
      = ((1 / 4) * (1 / (4 * (d : ℝ)) ^ 2) * (10000 * (d : ℝ) ^ 4)) *
        ((1 / u) * Real.exp (-(Real.pi / (2 * (4 * (d : ℝ)) ^ 2)) / u)) from by ring]
  refine (mul_le_mul_of_nonneg_right hle (by positivity)).trans_eq ?_
  ring

/-! ## The explicit completion: analyticity and agreement -/

lemma completionL0_spec {d : ℕ} (hd : 1 ≤ d) {psi : GaussianInt → ℂ}
    (hpsi : IsCharMod4dStrict d psi) (hU : unitSum psi 0 ≠ 0) (h0 : gaussSum d psi 0 = 0) :
    AnalyticOn ℂ (completionL0 d psi) Set.univ ∧
      (∀ s : ℂ, 1 < s.re → completionL0 d psi s =
        Work.FITop4.Bridge.heckeArch d 0 s * heckeLSeries psi 0 s) := by
  have hb : ∀ z : GaussianInt, ‖psi z‖ ≤ 1 := hpsi.1.2.2.1
  obtain ⟨hlowconv, hlowan⟩ := hci_lowCut_facts d hd psi 0 hpsi hU (Or.inl h0)
  obtain ⟨hhighconv, hhighan⟩ := hci_highCut_facts d hd psi 0 hpsi
  refine ⟨?_, ?_⟩
  · have hL : AnalyticOn ℂ (mellin (completionLowCut d psi)) Set.univ := hlowan
    have hH : AnalyticOn ℂ (mellin (completionHighCut d psi)) Set.univ := hhighan
    exact (Work.FIArea5.S16Hecke.analyticOn_fourd_cpow d hd).mul (hL.add hH)
  · intro s hs
    have hs' : 1 + ((0 : ℕ) : ℝ) / 2 < s.re := by simpa using hs
    have hsplit : mellin (completionLowCut d psi) s + mellin (completionHighCut d psi) s
        = mellin (thetaHol psi 0) s := by
      have hL : MellinConvergent (completionLowCut d psi) s := hlowconv s
      have hH : MellinConvergent (completionHighCut d psi) s := hhighconv s
      rw [mellin, mellin, mellin, ← integral_add hL hH]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
      rw [← smul_add]
      congr 1
      show (if u < completionCut d then thetaHol psi 0 u else 0)
          + (if completionCut d ≤ u then thetaHol psi 0 u else 0) = thetaHol psi 0 u
      by_cases h : u < completionCut d
      · rw [if_pos h, if_neg (not_le_of_gt h), add_zero]
      · rw [if_neg h, if_pos (le_of_not_gt h), zero_add]
    have hmain : completionL0 d psi s =
        (((4 * d : ℕ)) : ℂ) ^ s *
          (Complex.Gamma s * (Real.pi : ℂ) ^ (-s) * heckeLSeries psi 0 s) := by
      rw [completionL0, hsplit, hci_mellin_thetaHol_eq psi 0 hb hs']
      simp only [Nat.cast_zero, zero_div, sub_zero]
    rw [hmain, Work.FITop4.Bridge.heckeArch]
    have hgam : s + ((|(((0 : ℤ)) : ℝ)| / 2 : ℝ) : ℂ) = s := by simp
    rw [hgam]
    have hfour : (((4 * d : ℕ)) : ℂ) ^ s * ((Real.pi : ℂ) ^ (-s))
        = (4 * ((d : ℝ) : ℂ) / (Real.pi : ℂ)) ^ s := by
      have h := Work.FIArea5.S16Hecke.fourd_pow_pi_pow d hd 0 s
      simp only [Nat.cast_zero, zero_div, add_zero] at h
      rw [show ((Real.pi : ℂ) ^ (0 : ℂ)) = 1 from by simp, mul_one] at h
      rw [h]
      congr 1
      push_cast; ring
    rw [show (((4 * d : ℕ)) : ℂ) ^ s *
            (Complex.Gamma s * (Real.pi : ℂ) ^ (-s) * heckeLSeries psi 0 s)
          = (((4 * d : ℕ)) : ℂ) ^ s * (Real.pi : ℂ) ^ (-s) *
            (Complex.Gamma s * heckeLSeries psi 0 s) from by ring]
    rw [hfour]
    ring

/-! ## The bound on the explicit completion -/

lemma completionL0_bound {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi)
    (hne : ∃ z : GaussianInt, IsPrimary z ∧ IsUnitMod4d d z ∧ chi z ≠ 1)
    (s : ℂ) (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖completionL0 d (twist chi 0) s‖ ≤ (10 : ℝ) ^ 6 * (d : ℝ) ^ (10 : ℕ) := by
  set psi : GaussianInt → ℂ := twist chi 0 with hpsi
  have hpsi_strict : IsCharMod4dStrict d psi := by
    rw [hpsi]; exact twist_isCharMod4dStrict d hd chi 0 hchi
  have hb : ∀ z : GaussianInt, ‖psi z‖ ≤ 1 := hpsi_strict.1.2.2.1
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have htw : ∀ u, thetaHol psi 0 u = thetaHol chi 0 u := by
    intro u; rw [hpsi]; exact thetaHol_twist_eq d chi 0 u
  have hsq : Real.sqrt (completionCut d) = 1 / (4 * (d : ℝ)) := by
    rw [completionCut, show (1 : ℝ) / (4 * (d : ℝ)) ^ 2 = (1 / (4 * (d : ℝ))) ^ 2 by ring_nf,
      Real.sqrt_sq (by positivity)]
  have hlow : ‖mellin (completionLowCut d psi) s‖ ≤
      2 * (2000 * (d : ℝ) ^ 2) * Real.sqrt (completionCut d) /
        (Real.pi / (2 * (4 * (d : ℝ)) ^ 2)) := by
    refine mellinLowBound (completionCut_pos hd) (completionCut_le_one hd) (by positivity)
      (by positivity) ?_ ?_ ?_ s (by linarith) (by linarith)
    · have h : AEStronglyMeasurable
          ((Iio (completionCut d)).indicator (fun u => thetaHol psi 0 u)) volume :=
        (hci_thetaHol_aestronglyMeasurable psi 0).indicator measurableSet_Iio
      exact h.mono_measure Measure.restrict_le_self
    · intro u hu
      show (if u < completionCut d then thetaHol psi 0 u else 0) = 0
      rw [if_neg (not_lt.mpr hu)]
    · intro u hu0 huc
      by_cases hlt : u < completionCut d
      · show ‖(if u < completionCut d then thetaHol psi 0 u else 0)‖ ≤ _
        rw [if_pos hlt, htw u]
        exact thetaHolLowDecayExplicit hd hchi hne u hu0 huc
      · show ‖(if u < completionCut d then thetaHol psi 0 u else 0)‖ ≤ _
        rw [if_neg hlt, norm_zero]
        refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
          (div_nonneg zero_le_one hu0.le)) (Real.exp_nonneg _)
  have hhigh : ‖mellin (completionHighCut d psi) s‖ ≤
      100 * (d : ℝ) ^ 2 * (Real.exp (Real.pi * completionCut d) * (1 + 1 / Real.pi ^ 2)) := by
    refine mellinHighBound (completionCut_pos hd) (completionCut_le_one hd) (by positivity)
      ?_ ?_ ?_ s (by linarith) (by linarith)
    · have h : AEStronglyMeasurable
          ((Ici (completionCut d)).indicator (fun u => thetaHol psi 0 u)) volume :=
        (hci_thetaHol_aestronglyMeasurable psi 0).indicator measurableSet_Ici
      exact h.mono_measure Measure.restrict_le_self
    · intro u hu
      show (if completionCut d ≤ u then thetaHol psi 0 u else 0) = 0
      rw [if_neg (not_le.mpr hu)]
    · intro u huc
      show ‖(if completionCut d ≤ u then thetaHol psi 0 u else 0)‖ ≤ _
      rw [if_pos huc, htw u]
      exact thetaHolHighDecayExplicit hd (hchi.1.2.2.1) u huc
  have h4d : ‖(((4 * d : ℕ)) : ℂ) ^ s‖ ≤ (4 * (d : ℝ)) ^ 2 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have h1 : (1 : ℝ) ≤ ((4 * d : ℕ) : ℝ) := by push_cast; linarith
    calc ((4 * d : ℕ) : ℝ) ^ s.re ≤ ((4 * d : ℕ) : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 hs2
      _ = ((4 * d : ℕ) : ℝ) ^ (2 : ℕ) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      _ = (4 * (d : ℝ)) ^ 2 := by push_cast; ring
  have hexp : Real.exp (Real.pi * completionCut d) ≤ 3 := by
    have hle : Real.pi * completionCut d ≤ 1 := by
      rw [completionCut, mul_one_div, div_le_one (by positivity)]
      nlinarith [Real.pi_lt_four, hd1, sq_nonneg ((d : ℝ) - 1)]
    have h := Real.exp_le_exp.mpr hle
    linarith [Real.exp_one_lt_three]
  have hA : 2 * (2000 * (d : ℝ) ^ 2) * Real.sqrt (completionCut d) /
      (Real.pi / (2 * (4 * (d : ℝ)) ^ 2)) ≤ 11000 * (d : ℝ) ^ 3 := by
    rw [hsq, div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi / (2 * (4 * (d : ℝ)) ^ 2))]
    have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    field_simp
    nlinarith [hpi3, hdpos, sq_nonneg ((d : ℝ) ^ 2), mul_pos hdpos hdpos]
  have hB : 100 * (d : ℝ) ^ 2 *
      (Real.exp (Real.pi * completionCut d) * (1 + 1 / Real.pi ^ 2)) ≤ 600 * (d : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) + 1 / Real.pi ^ 2 ≤ 2 := by
      have h2 : 1 / Real.pi ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity : (0 : ℝ) < Real.pi ^ 2)]
        nlinarith [Real.pi_gt_three]
      linarith
    calc 100 * (d : ℝ) ^ 2 * (Real.exp (Real.pi * completionCut d) * (1 + 1 / Real.pi ^ 2))
        ≤ 100 * (d : ℝ) ^ 2 * (3 * 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hexp h1 (by positivity) (by norm_num)) (by positivity)
      _ = 600 * (d : ℝ) ^ 2 := by ring
  have hfin : (4 * (d : ℝ)) ^ 2 * (11000 * (d : ℝ) ^ 3 + 600 * (d : ℝ) ^ 2) ≤
      (10 : ℝ) ^ 6 * (d : ℝ) ^ (10 : ℕ) := by
    have h5 : (d : ℝ) ^ 5 ≤ (d : ℝ) ^ 10 := pow_le_pow_right₀ hd1 (by norm_num)
    have h4 : (d : ℝ) ^ 4 ≤ (d : ℝ) ^ 10 := pow_le_pow_right₀ hd1 (by norm_num)
    have h10 : (0 : ℝ) ≤ (d : ℝ) ^ 10 := by positivity
    nlinarith [h5, h4, h10]
  show ‖(((4 * d : ℕ)) : ℂ) ^ s *
      (mellin (completionLowCut d psi) s + mellin (completionHighCut d psi) s)‖ ≤
      (10 : ℝ) ^ 6 * (d : ℝ) ^ (10 : ℕ)
  calc ‖(((4 * d : ℕ)) : ℂ) ^ s *
        (mellin (completionLowCut d psi) s + mellin (completionHighCut d psi) s)‖
      ≤ ‖(((4 * d : ℕ)) : ℂ) ^ s‖ *
        ‖mellin (completionLowCut d psi) s + mellin (completionHighCut d psi) s‖ :=
        norm_mul_le _ _
    _ ≤ ‖(((4 * d : ℕ)) : ℂ) ^ s‖ *
        (‖mellin (completionLowCut d psi) s‖ + ‖mellin (completionHighCut d psi) s‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ (4 * (d : ℝ)) ^ 2 *
        (2 * (2000 * (d : ℝ) ^ 2) * Real.sqrt (completionCut d) /
          (Real.pi / (2 * (4 * (d : ℝ)) ^ 2)) +
          100 * (d : ℝ) ^ 2 * (Real.exp (Real.pi * completionCut d) * (1 + 1 / Real.pi ^ 2))) :=
        mul_le_mul h4d (add_le_add hlow hhigh) (by positivity) (by positivity)
    _ ≤ (4 * (d : ℝ)) ^ 2 * (11000 * (d : ℝ) ^ 3 + 600 * (d : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (by positivity)
    _ ≤ (10 : ℝ) ^ 6 * (d : ℝ) ^ (10 : ℕ) := hfin

/-- **The entire completion `Lam` of the Hecke `L`-function `L(s,χ)` of `ℚ(i)` is bounded on the
strip `1/2 ≤ re s ≤ 2` by an absolute constant times `d^10`, uniformly in `d` and `χ`.** -/
theorem completion_strip_bound_strict :
    ∃ K : ℝ, 0 < K ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
        ∀ (Lam : ℂ → ℂ), AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi 0 s) →
        ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
          ‖Lam s‖ ≤ K * (d : ℝ) ^ (10 : ℕ) := by
  refine ⟨(10 : ℝ) ^ 6, by norm_num, ?_⟩
  intro d hd chi hchi hb Lam hAn hagr s hs1 hs2
  by_cases htriv : ∀ z : GaussianInt, IsPrimary z → IsUnitMod4d d z → chi z = 1
  · exact absurd ⟨Lam, hAn, fun s hs => hagr s (by simpa using hs)⟩
      (noCompletion_of_primaryTrivial d chi 0 hd hchi
        (fun z hz hu => by simpa [Work.FIArea5.S16Hecke.psi] using htriv z hz hu))
  · push_neg at htriv
    set ps : GaussianInt → ℂ := twist chi 0 with hps
    have hps_strict : IsCharMod4dStrict d ps := by
      rw [hps]; exact twist_isCharMod4dStrict d hd chi 0 hchi
    have hU : unitSum ps 0 ≠ 0 := by
      rw [hps, twist_unitSum d hd chi 0 hchi.1]; norm_num
    have hne : ∃ z : GaussianInt, IsPrimary z ∧ IsUnitMod4d d z ∧ ps z ≠ 1 := by
      obtain ⟨z, hzp, hzu, hzne⟩ := htriv
      exact ⟨z, hzp, hzu, by rw [hps, twist_eq_of_isPrimary chi 0 hzp]; exact hzne⟩
    have h0 : gaussSum d ps 0 = 0 := gaussSum_zero_of_nontrivial hd hps_strict hne
    obtain ⟨hL0an, hL0agr⟩ := completionL0_spec (d := d) hd hps_strict hU h0
    have hLseries : heckeLSeries ps 0 = heckeLSeries chi 0 := by
      rw [hps]; exact heckeLSeries_twist chi 0
    have hLam : Lam = completionL0 d ps := by
      refine eq_of_agrees_right (completionL0 d ps) Lam hL0an hAn ?_
      intro w hw
      rw [hagr w hw, hL0agr w hw, hLseries]
    rw [congrFun hLam s]
    exact completionL0_bound hd hchi htriv s hs1 hs2

end

end Work.FIArea6Hecke.R
