/-
# `Submission.Work.FIArea6.S16ErrTwo.Base` — the §16 pair-sum identities, self-contained

Copies (under the `sc_` prefix, so that they coexist with the originals) of the §16 facts needed by
the error analysis: the truncated log-sine series identity (`sc_logFac6Series_eq_sum_fcoeff`), the
support facts (`sc_coprime_gnorm_four_mul`, `sc_unitInd_eq_one_of_mem_supp`, `sc_gnorm_le_two_N`,
`sc_error_le_far`) and the two identities `sc_MainSum_eq_sum`, `sc_Vd_sub_MainSum_eq` expressing
`Vd − MainSum` as the (16.10)/(16.11) pair sum.  Keeping them here makes `S16ErrTwo` independent of
later edits of `Submission/Work/FIArea6/S16_error_bound.lean`.
-/
import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea6.S16Assembly
import Submission.Work.FIArea7.UniMollify6
import Submission.Work.FIArea6.S16_beta_mass6
import Submission.Work.FIArea6.logFac6_sub_gtrunc_le
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea6.omegaDet_eq_ratioSym
import Submission.Work.FIArea7.card_gBox_filter_dvd_absDelta
import Submission.Work.FIArea6b.sector_tau_sum
import Submission.Work.FIArea6.card_dvd_delta_fiber_near_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

lemma sc_psiK_eq_uniPow (k : ℤ) (z : GaussianInt) :
    psiK k z = Work.FIArea7.uniPow z k := by
  unfold psiK Work.FIArea7.uniPow
  rw [Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]

lemma sc_sum_fcoeff_eq (K : ℕ) (w : ℤ → ℂ) (hw0 : w 0 = 1) :
    (∑ k ∈ Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ)), (fcoeff k : ℂ) * w k)
      = ((Real.log 16 : ℝ) : ℂ)
        + ∑ k ∈ Work.FIArea7.evenFreq K, ((1 / |(k : ℝ)| : ℝ) : ℂ) * w k := by
  set s : Finset ℤ := Finset.Icc (-(2 * (K : ℤ))) (2 * (K : ℤ)) with hs
  have hmem : (0 : ℤ) ∈ s := by rw [hs]; simp
  rw [← Finset.add_sum_erase s _ hmem]
  have h0 : fcoeff 0 = Real.log 16 := by simp [fcoeff]
  rw [h0, hw0, mul_one]
  congr 1
  -- now the sum over `s.erase 0`
  have hstep : ∀ k ∈ s.erase 0,
      (fcoeff k : ℂ) * w k
        = (if Even k then ((1 / |(k : ℝ)| : ℝ) : ℂ) * w k else 0) := by
    intro k hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hk0, -⟩ := hk
    by_cases hev : Even k
    · have h2 : (2 : ℤ) ∣ k := by
        simpa [even_iff_two_dvd] using hev
      simp [fcoeff, hk0, h2, hev]
    · have h2 : ¬ ((2 : ℤ) ∣ k) := by
        simpa [even_iff_two_dvd] using hev
      simp [fcoeff, hk0, h2, hev]
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
  rw [Work.FIArea7.evenFreq]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_erase, hs]
  tauto

theorem sc_logFac6Series_eq_sum_fcoeff (X : ℕ) (z1 z2 : GaussianInt) :
    (∑ k ∈ Finset.Icc (-(2 * (Kcut X : ℤ))) (2 * (Kcut X : ℤ)),
        (fcoeff k : ℂ) * (psiK k z1 * star (psiK k z2)))
      = Work.FIArea7.logFac6Series z1 z2 (Kcut X) := by
  rw [sc_sum_fcoeff_eq (Kcut X) (fun k => psiK k z1 * star (psiK k z2)) (by simp [psiK])]
  rw [Work.FIArea7.logFac6Series, FIA6_log_sixteen]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [sc_psiK_eq_uniPow k z1, sc_psiK_eq_uniPow k z2]
  congr 1
  rw [one_div, one_div, Complex.ofReal_inv]

lemma sc_coprime_gnorm_four_mul {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) {d : ℕ} (hd : 1 ≤ d) (hPz : 4 * d ≤ Pa.Pz) :
    Nat.Coprime (Work.FIPlan.gnorm z) (4 * d) := by
  have h4d : 0 < 4 * d := by omega
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : p ∣ Work.FIPlan.gnorm z := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ 4 * d := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  have hpPz : p ≤ Pa.Pz := le_trans (Nat.le_of_dvd h4d h2) hPz
  exact (Work.FITop4.IsBetaCoeff6.noSmallPrimes hβ hz) p hp hpPz h1

lemma sc_unitInd_eq_one_of_mem_supp {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt}
    (hz : β z ≠ 0) {d : ℕ} (hd : 1 ≤ d) (hPz : 4 * d ≤ Pa.Pz) :
    Work.FIArea7.unitInd (4 * d) z = 1 := by
  simp only [Work.FIArea7.unitInd, if_pos (sc_coprime_gnorm_four_mul hβ hz hd hPz)]

lemma sc_norm_ratioSym_le_one (z1 z2 : GaussianInt) (d : ℕ) :
    ‖(Work.FIArea7.ratioSym z1 z2 d : ℂ)‖ ≤ 1 := by
  rw [Work.FIArea7.ratioSym]
  have h := Work.FIArea6.abs_jacobiSym_le_one
      ((((star z1 * z2).re : ZMod d) * ((((Work.FIPlan.gnorm z1 : ℕ)) : ZMod d))⁻¹).val) d
  exact_mod_cast h

theorem sc_MainSum_eq_sum (Pa : Work.FITop.Params) (X d : ℕ) (β : GaussianInt → ℂ) :
    MainSum Pa X d β
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          Work.FIArea7.unitInd (4 * d) z1 * Work.FIArea7.unitInd (4 * d) z2 *
            (β z1 * star (β z2)) * omegaDet d z1 z2 *
              Work.FIArea7.logFac6Series z1 z2 (Kcut X) := by
  unfold MainSum DetSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z1 _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z2 _ => ?_)
  set Cc : ℂ := Work.FIArea7.unitInd (4 * d) z1 * Work.FIArea7.unitInd (4 * d) z2 *
      (β z1 * star (β z2)) * omegaDet d z1 z2 with hCc
  have h2 : (∑ k ∈ Finset.Icc (-(2 * (Kcut X : ℤ))) (2 * (Kcut X : ℤ)),
        (fcoeff k : ℂ) * (Work.FIArea7.unitInd (4 * d) z1 * Work.FIArea7.unitInd (4 * d) z2 *
          ((β z1 * psiK k z1) * star (β z2 * psiK k z2)) * omegaDet d z1 z2))
      = ∑ k ∈ Finset.Icc (-(2 * (Kcut X : ℤ))) (2 * (Kcut X : ℤ)),
          Cc * ((fcoeff k : ℂ) * (psiK k z1 * star (psiK k z2))) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [star_mul]
    simp only [hCc]
    ring
  rw [h2, ← Finset.mul_sum, sc_logFac6Series_eq_sum_fcoeff X z1 z2]

theorem sc_Vd_sub_MainSum_eq (Pa : Work.FITop.Params) (X d : ℕ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (hd : 1 ≤ d) (hdX : d ≤ X)
    (hPz : 4 * X ≤ Pa.Pz) :
    Vd Pa d β - MainSum Pa X d β
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          β z1 * star (β z2) * (Work.FIArea7.ratioSym z1 z2 d : ℂ) *
            (if 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
              (if Work.FIPlan.GaussCoprime z1 z2 then (Work.FITop4.logFac6 z1 z2 : ℂ) else 0)
                - Work.FIArea7.logFac6Series z1 z2 (Kcut X)
             else 0) := by
  have h4d : 4 * d ≤ Pa.Pz := by
    have : 4 * d ≤ 4 * X := by omega
    linarith [hPz, this]
  rw [sc_MainSum_eq_sum]
  unfold Vd
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun z1 _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun z2 _ => ?_)
  by_cases hb1 : β z1 = 0
  · simp [hb1]
  by_cases hb2 : β z2 = 0
  · simp [hb2]
  have hu1 : Work.FIArea7.unitInd (4 * d) z1 = 1 := sc_unitInd_eq_one_of_mem_supp hβ hb1 hd h4d
  have hu2 : Work.FIArea7.unitInd (4 * d) z2 = 1 := sc_unitInd_eq_one_of_mem_supp hβ hb2 hd h4d
  have hom := Work.FIArea6.omegaDet_eq_ratioSym d hd z1 z2
    (sc_coprime_gnorm_four_mul hβ hb1 hd h4d) (sc_coprime_gnorm_four_mul hβ hb2 hd h4d)
  rw [hu1, hu2]
  have hnorm : (4 * d : ℕ) = d * 4 := Nat.mul_comm 4 d
  rw [hnorm] at hom ⊢
  by_cases hΔ : d * 4 ∣ Work.FIPlan.absDelta z1 z2
  · rw [hom]
    by_cases hc : Work.FIPlan.GaussCoprime z1 z2
    · simp only [if_pos hΔ, if_pos hc,
        if_pos (show Work.FIPlan.GaussCoprime z1 z2 ∧ d * 4 ∣ Work.FIPlan.absDelta z1 z2
          from ⟨hc, hΔ⟩)]
      ring
    · simp only [if_pos hΔ, if_neg hc,
        if_neg (show ¬ (Work.FIPlan.GaussCoprime z1 z2 ∧ d * 4 ∣ Work.FIPlan.absDelta z1 z2)
          from fun h => hc h.1)]
      ring
  · rw [hom]
    simp only [if_neg hΔ,
      if_neg (show ¬ (Work.FIPlan.GaussCoprime z1 z2 ∧ d * 4 ∣ Work.FIPlan.absDelta z1 z2)
        from fun h => hΔ h.2)]
    ring

lemma sc_theta_le_one_of_params (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
  · have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have h3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
    linarith [Real.log_le_log (by norm_num) hx3]
  · have h : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
    linarith

lemma sc_gnorm_le_two_N {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt} (hz : β z ≠ 0) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * Pa.N := by
  obtain ⟨-, -, hle, -⟩ := Work.FITop4.IsBetaCoeff6.support hβ hz
  have hθ1 := sc_theta_le_one_of_params Pa
  have hN1 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  nlinarith [hle, hθ1, hN1]

lemma sc_error_le_far {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (X : ℕ) (hX : 1 ≤ X)
    {z1 z2 : GaussianInt} (hz1 : β z1 ≠ 0) (hz2 : β z2 ≠ 0)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) :
    ‖(Work.FITop4.logFac6 z1 z2 : ℂ) - Work.FIArea7.logFac6Series z1 z2 (Kcut X)‖
      ≤ 8 * Pa.N / ((Kcut X : ℝ) * (Work.FIPlan.absDelta z1 z2 : ℝ)) := by
  have hK : 1 ≤ Kcut X := by rw [Kcut]; exact one_le_pow₀ hX
  have hM : (0 : ℝ) ≤ 2 * Pa.N := by linarith [Pa.hN1]
  refine le_trans (Work.FIArea7.abs_logFac6_sub_series_le z1 z2 (Kcut X) hK hM
    (sc_gnorm_le_two_N hβ hz1) (sc_gnorm_le_two_N hβ hz2) hΔ) (le_of_eq ?_)
  ring

end

end Work.FIArea6
