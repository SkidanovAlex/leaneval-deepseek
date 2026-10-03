/-
# `Submission.Work.FIArea6Road.HeartZcAux` — shared elementary lemmas for the §16 heart

This module collects the *elementary* (module-independent) lemmas used by the contour shift
`Work.FIArea6Road.HeartZcCore` and by the pieces delegated for it:

* `hzc_eta_le_quarter` — the exponent bound `η ≤ 1/4` of the numerical set-up;
* `hzc_E1_ge` — `exp(-√log N/8) ≤ S16E1` for `c ≤ 1/2`, `d ≥ 1`;
* `hzc_integral_inv_sq_le` — `∫_{-T}^{T}(1+(θy)²)⁻¹ dy ≤ π/θ`;
* `hzc_integral_arctan_le` — `∫_{-T}^{T} θ(1+(θy)²)⁻¹ dy ≤ π` (the vertical-line kernel);
* `hzc_mellin_diffAt` — differentiability of the Mellin transform of a `C²` bump in `re s > 0`.

None of these mentions the continuation interface, so the module is safe to import from the
child files without creating an import cycle.
-/
import Mathlib
import Submission.Work.FIArea6.S16.HeartIface
import Submission.Work.FIArea6.S16MellinInversion

namespace Work.FIArea6Road

open MeasureTheory intervalIntegral

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `η ≤ 1/4`, from `x^{1/4+η} < N < x^{1/2}(log x)^{-B} ≤ x^{1/2}`. -/
lemma hzc_eta_le_quarter (Pa : Work.FITop.Params) : Pa.η ≤ 1 / 4 := by
  have hlog1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have h1 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) h3
    have h3' : 1 < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
      rwa [Real.log_exp] at h
    linarith
  have hx1 : 1 < (Pa.x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hpowle : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlog1 (by linarith [Pa.hB])
  have hxhalf : (0 : ℝ) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  have hupper : Pa.N < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := by
    refine lt_of_lt_of_le Pa.hNhi ?_
    calc (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B)
        ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left hpowle hxhalf
      _ = (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := mul_one _
  have hlt : (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) :=
    lt_trans Pa.hNlo hupper
  have h := (Real.rpow_lt_rpow_left_iff hx1).mp hlt
  linarith

/-- `E1 = exp(-η c (4d)^{-ε}√log N) ≥ exp(-√log N/8)` for `c ≤ 1/2`, `η ≤ 1/4`, `d ≥ 1`,
`ε ≥ 0`. -/
lemma hzc_E1_ge (Pa : Work.FITop.Params) (c : ℝ) (d : ℕ) (ε : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1 / 2) (hε : 0 ≤ ε) (hd : 1 ≤ d) (hη : Pa.η ≤ 1 / 4) :
    Real.exp (-(Real.sqrt (Real.log Pa.N) / 8)) ≤ Work.FIArea6.S16.S16E1 Pa c d ε := by
  unfold Work.FIArea6.S16.S16E1
  apply Real.exp_le_exp.mpr
  have h4d : (1 : ℝ) ≤ (((4 * d : ℕ)) : ℝ) := by
    have h : (1 : ℕ) ≤ 4 * d := by omega
    exact_mod_cast h
  have hbase : (0 : ℝ) < (((4 * d : ℕ)) : ℝ) := by linarith
  have hpow : (((4 * d : ℕ) : ℝ)) ^ (-ε) ≤ 1 := by
    rw [Real.rpow_neg hbase.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow h4d hε)
  have hsqrt : 0 ≤ Real.sqrt (Real.log Pa.N) := Real.sqrt_nonneg _
  have hc_combo : Pa.η * c ≤ 1 / 8 := by nlinarith [hη, hc1]
  have hnc_nonneg : 0 ≤ Pa.η * c := le_of_lt (mul_pos Pa.hη hc)
  have hprod_le : (((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)
      ≤ 1 * Real.sqrt (Real.log Pa.N) := mul_le_mul_of_nonneg_right hpow hsqrt
  have hprod_nonneg : 0 ≤ (((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N) :=
    mul_nonneg (Real.rpow_nonneg hbase.le _) hsqrt
  have hkey : Pa.η * c * (((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)
      ≤ Real.sqrt (Real.log Pa.N) / 8 := by
    calc Pa.η * c * (((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)
        = (Pa.η * c) * ((((4 * d : ℕ) : ℝ)) ^ (-ε) * Real.sqrt (Real.log Pa.N)) := by ring
      _ ≤ (1 / 8) * (1 * Real.sqrt (Real.log Pa.N)) :=
          mul_le_mul hc_combo hprod_le hprod_nonneg (by norm_num)
      _ = Real.sqrt (Real.log Pa.N) / 8 := by ring
  linarith [hkey]

/-- `∫_{-T}^{T} (1 + (θy)²)⁻¹ dy ≤ π/θ` for `θ > 0`. -/
lemma hzc_integral_inv_sq_le (θ T : ℝ) (hθ : 0 < θ) :
    (∫ y in (-T)..T, (1 + (θ * y) ^ 2)⁻¹) ≤ Real.pi / θ := by
  have hsub := intervalIntegral.integral_comp_mul_left
      (f := fun u : ℝ => (1 + u ^ 2)⁻¹) (a := -T) (b := T) (c := θ) (ne_of_gt hθ)
  have h1 : (∫ y in (-T)..T, (1 + (θ * y) ^ 2)⁻¹)
      = θ⁻¹ * ∫ u in (θ * (-T))..(θ * T), (1 + u ^ 2)⁻¹ := by
    simpa using hsub
  rw [h1]
  have harctan : (∫ u in (θ * (-T))..(θ * T), (1 + u ^ 2)⁻¹)
      = Real.arctan (θ * T) - Real.arctan (θ * (-T)) := integral_inv_one_add_sq
  rw [harctan]
  have hlt : Real.arctan (θ * T) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hgt : -(Real.pi / 2) < Real.arctan (θ * (-T)) := Real.neg_pi_div_two_lt_arctan _
  have hmul : θ⁻¹ * (Real.arctan (θ * T) - Real.arctan (θ * (-T))) ≤ θ⁻¹ * Real.pi := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hθ))
    linarith
  simpa [div_eq_inv_mul] using hmul

/-- `∫_{-T}^{T} θ (1 + (θy)²)⁻¹ dy = 2 arctan (θT) ≤ π` for `θ > 0`: the vertical-line kernel
with the `θ`-factor of the Mellin decay, in the form the Cauchy estimate consumes. -/
lemma hzc_integral_arctan_le (θ T : ℝ) (hθ : 0 < θ) :
    ∫ y in (-T)..T, θ * (1 + (θ * y) ^ 2)⁻¹ ≤ Real.pi := by
  have hsub := intervalIntegral.integral_comp_mul_left
      (f := fun u : ℝ => (1 + u ^ 2)⁻¹) (a := -T) (b := T) (c := θ) (ne_of_gt hθ)
  have h1 : ∫ y in (-T)..T, (1 + (θ * y) ^ 2)⁻¹
      = θ⁻¹ * ∫ u in (θ * (-T))..(θ * T), (1 + u ^ 2)⁻¹ := by
    simpa using hsub
  have h2 : ∫ y in (-T)..T, θ * (1 + (θ * y) ^ 2)⁻¹
      = θ * ∫ y in (-T)..T, (1 + (θ * y) ^ 2)⁻¹ := by
    rw [intervalIntegral.integral_const_mul]
  have harctan : ∫ u in (θ * (-T))..(θ * T), (1 + u ^ 2)⁻¹
      = Real.arctan (θ * T) - Real.arctan (θ * (-T)) := integral_inv_one_add_sq
  have h3 : Real.arctan (θ * (-T)) = -Real.arctan (θ * T) := by
    rw [mul_neg, Real.arctan_neg]
  rw [h2, h1, harctan, h3, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hθ), one_mul]
  have hlt : Real.arctan (θ * T) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  linarith

/-- The Mellin transform of a `C²` bump supported in `(N, (1+θ)N]` is differentiable in the
open half-plane `re s > 0`. -/
lemma hzc_mellin_diffAt (p : ℝ → ℝ) (N θ : ℝ) (hN : 0 < N) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hpC : ContDiff ℝ 2 p) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ (1 + θ) * N) :
    ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ (mellin (fun u : ℝ => (p u : ℂ))) s := by
  intro s hs
  have hcont : Continuous (fun u : ℝ => (p u : ℂ)) := Complex.continuous_ofReal.comp hpC.continuous
  have hli : LocallyIntegrableOn (fun u : ℝ => (p u : ℂ)) (Set.Ioi 0) volume :=
    hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hzero : ∀ u : ℝ, (1 + θ) * N < u → p u = 0 := by
    intro u hu
    by_contra hne
    exact absurd (hpsupp u hne).2 (not_le.mpr hu)
  have htop : (fun u : ℝ => (p u : ℂ)) =O[Filter.atTop]
      (fun u : ℝ => Real.exp (-1 * u)) := by
    have hev : (fun u : ℝ => (p u : ℂ)) =ᶠ[Filter.atTop] (fun _ => 0) := by
      filter_upwards [Filter.eventually_gt_atTop ((1 + θ) * N)] with u hu
      simp [hzero u hu]
    exact (Asymptotics.isBigO_zero (fun u : ℝ => Real.exp (-1 * u)) Filter.atTop).congr'
      hev.symm Filter.EventuallyEq.rfl
  have hbot : (fun u : ℝ => (p u : ℂ)) =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun u : ℝ => u ^ (-(0 : ℝ))) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with u _hu
    rw [show (-(0 : ℝ)) = 0 by norm_num, Real.rpow_zero, norm_one, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hp0 u], hp1 u⟩
  exact mellin_differentiableAt_of_isBigO_rpow_exp (a := 1) one_pos hli htop hbot hs

/-- **Numerical consequences of `10^8 ≤ log N`.**  From `x^{1/4+η} < N` one gets
`log x ≥ 4·10^8`, hence `log log x ≥ 3` and (by `(log log x)^2 ≤ log Pz`) `log Pz ≥ 6`. -/
lemma hzc_logPz_ge_six (Pa : Work.FITop.Params) (hL : 10 ^ 8 ≤ Real.log Pa.N) :
    6 ≤ Real.log (Pa.Pz : ℝ) := by
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hx1 : (1 : ℝ) < (Pa.x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  -- `N < x^{1/2} (log x)^{-B} ≤ x^{1/2}` gives `log x > 2 log N ≥ 2·10^8`
  have hlog31 : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
    rwa [Real.log_exp] at h
  have hlogx1 : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
    have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 3) h3, hlog31]
  have hpowle : (Real.log (Pa.x : ℝ)) ^ (-Pa.B) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlogx1 (by linarith [Pa.hB])
  have hxh : (0 : ℝ) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hxpos.le _
  have hupper : Pa.N < (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := by
    refine lt_of_lt_of_le Pa.hNhi ?_
    calc (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (Pa.x : ℝ)) ^ (-Pa.B)
        ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left hpowle hxh
      _ = (Pa.x : ℝ) ^ ((1 : ℝ) / 2) := mul_one _
  have hlogx_low : 2 * 10 ^ 8 ≤ Real.log (Pa.x : ℝ) := by
    have h1 : Real.log Pa.N < Real.log ((Pa.x : ℝ) ^ ((1 : ℝ) / 2)) :=
      Real.log_lt_log (lt_of_lt_of_le zero_lt_one Pa.hN1) hupper
    rw [Real.log_rpow hxpos] at h1
    linarith
  have h27 : Real.exp 3 < 27 := by
    have h := pow_lt_pow_left₀ Real.exp_one_lt_three (le_of_lt (Real.exp_pos 1))
      (by norm_num : (3 : ℕ) ≠ 0)
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    exact h
  have h4 : (3 : ℝ) ≤ Real.log (Real.log (Pa.x : ℝ)) :=
    (Real.le_log_iff_exp_le (Real.log_pos hx1)).mpr (by linarith)
  have h6 := Pa.hPlo
  nlinarith [h4, h6]

end

end Work.FIArea6Road
