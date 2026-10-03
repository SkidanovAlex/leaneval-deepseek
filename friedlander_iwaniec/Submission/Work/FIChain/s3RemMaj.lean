import Mathlib
import Submission.Work.FIChain.S3plusC_machinery
import Submission.Work.FIChain.s3Rem_fibre_pt_le
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.zc_sharp_bounds

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The sharp `u`-level inequality for the REM integrand -/

/-- The REM integrand is dominated by its majorant, at the level of the `u`-integral. -/
lemma abs_integral_s3RemI_le_maj (x Cm ℓ : ℕ) (z sz U : ℝ) (h1 : 1 ≤ U) (hCm : 1 ≤ Cm)
    (hℓ : 1 ≤ ℓ) (hℓz : (ℓ : ℝ) * z ≤ (x : ℝ)) (hU : U ≤ (x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) :
    |∫ u in (1 : ℝ)..U, s3RemI x z sz Cm ℓ u / u|
      ≤ ∫ u in (1 : ℝ)..U, s3RemMaj x Cm ℓ z sz u / u := by
  rw [← Real.norm_eq_abs]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm h1) ?_
  have hmaj : Integrable (fun u : ℝ => s3RemMaj x Cm ℓ z sz u / u)
      (volume.restrict (Set.Ioc 1 U)) :=
    integrableOn_s3RemMaj_div x Cm ℓ z sz (a := 1) (b := U) le_rfl h1 hℓ hCm hℓz hU
  rw [intervalIntegral.integral_of_le h1, intervalIntegral.integral_of_le h1]
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun u => norm_nonneg _)) hmaj ?_
  · refine eventually_restrict_Ioc (fun u hu => ?_)
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu.1.le
    show ‖s3RemI x z sz Cm ℓ u / u‖ ≤ s3RemMaj x Cm ℓ z sz u / u
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hu0]
    exact div_le_div_of_nonneg_right (abs_s3RemI_le_s3RemMaj x Cm ℓ z sz u) hu0.le

/-! ## 2. The majorant of the REM half, and its measurability/integrability -/

/-- The fixed-range form of the REM majorant (for measurability). -/
def s3RemMajF (x Cm N ℓ : ℕ) (sc : ℝ) (z u : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (if (d : ℝ) ≤ u then
      (|cfR (ℓ * d) ⌊min ((ℓ : ℝ) * (sc * z)) (x : ℝ)⌋₊|
        + |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊|)
     else 0)

lemma measurable_s3RemMajF (x Cm N ℓ : ℕ) (sc : ℝ) :
    Measurable (fun p : ℝ × ℝ => s3RemMajF x Cm N ℓ sc p.1 p.2) := by
  refine Finset.measurable_sum _ (fun d _ => ?_)
  refine Measurable.ite (measurableSet_le measurable_const measurable_snd) ?_ measurable_const
  have h1 : Measurable (fun p : ℝ × ℝ => ⌊min ((ℓ : ℝ) * (sc * p.1)) (x : ℝ)⌋₊) := by fun_prop
  have h2 : Measurable (fun p : ℝ × ℝ =>
      ⌊max ((ℓ : ℝ) * p.1) ((ℓ : ℝ) * (Cm : ℝ) * p.2)⌋₊) := by fun_prop
  have ha : Measurable (fun p : ℝ × ℝ =>
      |cfR (ℓ * d) ⌊min ((ℓ : ℝ) * (sc * p.1)) (x : ℝ)⌋₊|) :=
    (measurable_cfR_const (ℓ * d) h1).abs
  have hb : Measurable (fun p : ℝ × ℝ =>
      |cfR (ℓ * d) ⌊max ((ℓ : ℝ) * p.1) ((ℓ : ℝ) * (Cm : ℝ) * p.2)⌋₊|) :=
    (measurable_cfR_const (ℓ * d) h2).abs
  exact ha.add hb

/-- The majorant equals its fixed-range form for `u ≤ N` (and for `u < 0` both vanish). -/
lemma s3RemMaj_eq_F (x Cm N ℓ : ℕ) (sc : ℝ) {z u : ℝ} (huN : u ≤ (N : ℝ)) :
    s3RemMaj x Cm ℓ z (sc * z) u = s3RemMajF x Cm N ℓ sc z u := by
  by_cases h : 0 ≤ u
  · exact s3RemMaj_eq_fixed x Cm ℓ z (sc * z) N h huN
  · have hfl : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [s3RemMaj, hfl, s3RemMajF]
    simp only [Finset.Icc_eq_empty_of_lt (by norm_num : (1 : ℕ) > 0), Finset.sum_empty]
    refine (Finset.sum_eq_zero (fun d hd => ?_)).symm
    rw [Finset.mem_Icc] at hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
    exact if_neg (by linarith)

/-- The parametric `u`-integral of the majorant is measurable in `z`. -/
lemma measurable_s3RemMajU (x Cm ℓ : ℕ) (sc : ℝ) :
    Measurable (fun z : ℝ => ∫ u in (1 : ℝ)..(min ((sc * z) / (Cm : ℝ))
        ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))), s3RemMaj x Cm ℓ z (sc * z) u / u) := by
  have hU : Measurable (fun z : ℝ =>
      min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))) := by fun_prop
  have hmain : Measurable (fun z : ℝ => ∫ u in (1 : ℝ)..(min ((sc * z) / (Cm : ℝ))
      ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
        s3RemMajF x Cm (⌈(x : ℝ)⌉₊ + 1) ℓ sc z u / u) := by
    refine measurable_intervalIntegral_param (α := ℝ) 1
      (G := fun q : ℝ × ℝ =>
        s3RemMajF x Cm (⌈(x : ℝ)⌉₊ + 1) ℓ sc q.1 q.2 / q.2) ?_ hU
    exact (measurable_s3RemMajF x Cm _ ℓ sc).div measurable_snd
  have hpt : ∀ z : ℝ, (∫ u in (1 : ℝ)..(min ((sc * z) / (Cm : ℝ))
        ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))), s3RemMaj x Cm ℓ z (sc * z) u / u)
      = ∫ u in (1 : ℝ)..(min ((sc * z) / (Cm : ℝ))
        ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))), s3RemMajF x Cm (⌈(x : ℝ)⌉₊ + 1) ℓ sc z u / u := by
    intro z
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    have hu_le : u ≤ ((⌈(x : ℝ)⌉₊ + 1 : ℕ) : ℝ) := by
      have h1 : u ≤ max 1 (min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))) := by
        rcases Set.mem_uIcc.mp hu with ⟨-, h⟩ | ⟨-, h⟩
        · exact le_trans h (le_max_right _ _)
        · exact le_trans h (le_max_left _ _)
      have h2 : min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) ≤ (x : ℝ) := by
        refine le_trans (min_le_right _ _) ?_
        rcases Nat.eq_zero_or_pos Cm with h | h
        · rw [h]
          simp
        · have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast h
          rcases Nat.eq_zero_or_pos ℓ with h0 | hℓ
          · rw [h0]
            simp
          · have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
            have hden : (1 : ℝ) ≤ (ℓ : ℝ) * (Cm : ℝ) := by
              calc (1 : ℝ) = 1 * 1 := by ring
                _ ≤ (ℓ : ℝ) * (Cm : ℝ) :=
                    mul_le_mul hℓ1 (by exact_mod_cast h) zero_le_one (by linarith)
            have hx2 := div_le_div_of_nonneg_left (Nat.cast_nonneg x) one_pos hden
            simpa using hx2
      have h4 : (x : ℝ) ≤ ((⌈(x : ℝ)⌉₊ + 1 : ℕ) : ℝ) :=
        (Nat.le_ceil (x : ℝ)).trans (by exact_mod_cast Nat.le_succ _)
      exact le_trans h1 (max_le (by exact_mod_cast (Nat.succ_pos _)) (le_trans h2 h4))
    rw [s3RemMaj_eq_F x Cm (⌈(x : ℝ)⌉₊ + 1) ℓ sc hu_le]
  rw [funext hpt]
  exact hmain

/-! ## 3. The majorant of the REM half and the per-`ℓ` domination -/

/-- The level integral of the REM integrand vanishes when the level cut is below `1`. -/
lemma integral_s3RemI_eq_zero_of_lt_one (x Cm ℓ : ℕ) (z sz U : ℝ) (hU : U < 1) :
    (∫ u in (1 : ℝ)..U, s3RemI x z sz Cm ℓ u / u) = 0 :=
  intervalIntegral_eq_zero_of_forall_lt_one _ hU (fun u hu => by
    have hfl : ⌊u⌋₊ = 0 := Nat.floor_eq_zero.mpr hu
    rw [s3RemI, hfl]
    simp)

/-- The `z`-majorant of the REM half: the `τ(ℓ)²`-weighted sum of the level majorants over the
`ℓ ≤ x/Cm` (the remaining `ℓ` have level cut `< 1` and contribute nothing). -/
def remMajU (x Cm : ℕ) (scf : ℝ) (z : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 x,
    (if (ℓ : ℝ) * z ≤ (x : ℝ) ∧ (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) then
      ((ℓ.divisors.card : ℝ)) ^ 2 *
        max (∫ u in (1 : ℝ)..(min ((scf * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
          s3RemMaj x Cm ℓ z (scf * z) u / u) 0
     else 0)

lemma measurable_remMajU (x Cm : ℕ) (scf : ℝ) :
    Measurable (fun z : ℝ => remMajU x Cm scf z / z) := by
  refine Measurable.div ?_ measurable_id
  refine Finset.measurable_sum _ (fun ℓ _ => ?_)
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_le (by fun_prop : Measurable (fun z : ℝ => (ℓ : ℝ) * z))
      measurable_const).inter (measurableSet_le measurable_const
        (by fun_prop : Measurable (fun _ : ℝ => ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ))))
  · refine measurable_const.mul ?_
    exact (measurable_s3RemMajU x Cm ℓ scf).max measurable_const

lemma remMajU_nonneg (x Cm : ℕ) (scf z : ℝ) : 0 ≤ remMajU x Cm scf z := by
  refine Finset.sum_nonneg (fun ℓ _ => ?_)
  by_cases h : (ℓ : ℝ) * z ≤ (x : ℝ) ∧ (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ)
  · rw [if_pos h]
    exact mul_nonneg (by positivity) (le_max_right _ _)
  · rw [if_neg h]

/-- For `ℓ ≤ x/Cm`, `ℓ ≥ 1`, `Cm ≥ 1` and `Cm ≤ sc·z` the level cut of the `ℓ`-th term is `≥ 1`. -/
lemma one_le_min_of (x Cm ℓ : ℕ) (sc z : ℝ) (hℓ1 : 1 ≤ ℓ) (hCm1 : 1 ≤ Cm)
    (hℓ : (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ)) (hscz : (Cm : ℝ) ≤ sc * z) :
    (1 : ℝ) ≤ min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) := by
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1)
  have hxCm : ((ℓ : ℝ) * (Cm : ℝ)) ≤ (x : ℝ) := by
    have h2 : ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) / (Cm : ℝ) :=
      Nat.floor_le (div_nonneg (Nat.cast_nonneg x) hCmpos.le)
    have h3 : ((ℓ : ℝ) * (Cm : ℝ)) ≤ ((x : ℝ) / (Cm : ℝ)) * (Cm : ℝ) :=
      mul_le_mul_of_nonneg_right (le_trans hℓ h2) hCmpos.le
    rwa [div_mul_cancel₀ _ hCmpos.ne'] at h3
  refine le_min ?_ ?_
  · rw [le_div_iff₀ hCmpos]
    simpa using hscz
  · rw [le_div_iff₀ (mul_pos hℓpos hCmpos)]
    linarith

/-- **Per-`ℓ` domination of the REM half by its majorant.** -/
lemma abs_s3RemPlus_le_remMajU (lam : ℕ → ℝ) (x Cm : ℕ) (sc z sy : ℝ)
    (hlam : ∀ ν : ℕ, |lam ν| ≤ 1) (hCm1 : 1 ≤ Cm) (hscz : (Cm : ℝ) ≤ sc * z) :
    |s3RemPlus lam x z sy (sc * z) Cm| ≤ remMajU x Cm sc z := by
  rw [s3RemPlus, remMajU]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum (fun ℓ hℓ => ?_)
  rw [Finset.mem_Icc] at hℓ
  by_cases hc : ((ℓ : ℕ) : ℝ) * z ≤ (x : ℝ)
  · by_cases hℓc : (ℓ : ℝ) ≤ ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ)
    · rw [if_pos hc, if_pos ⟨hc, hℓc⟩]
      have hU1 : (1 : ℝ) ≤ min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) :=
        one_le_min_of x Cm ℓ sc z hℓ.1 hCm1 hℓc hscz
      have hW := cfWeight_abs_le lam sy ℓ hlam
      have hint := abs_integral_s3RemI_le_maj x Cm ℓ z (sc * z) _ hU1 hCm1 hℓ.1 hc
        (min_le_right _ _)
      have hnonneg : (0 : ℝ) ≤ ((ℓ.divisors.card : ℝ)) ^ 2 := by positivity
      calc |(∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
              (ArithmeticFunction.moebius b : ℝ)) * Submission.ASP.rhoOf lam ℓ *
            ∫ u in (1 : ℝ)..(min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
              (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
                (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * (sc * z)) (x : ℝ)⌋₊
                  - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u|
          = |(∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
                (ArithmeticFunction.moebius b : ℝ)) * Submission.ASP.rhoOf lam ℓ|
            * |∫ u in (1 : ℝ)..(min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
                (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
                  (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * (sc * z)) (x : ℝ)⌋₊
                    - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u| :=
            abs_mul _ _
        _ ≤ ((ℓ.divisors.card : ℝ)) ^ 2 *
              (∫ u in (1 : ℝ)..(min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
                s3RemMaj x Cm ℓ z (sc * z) u / u) :=
            mul_le_mul hW hint (abs_nonneg _) hnonneg
        _ ≤ ((ℓ.divisors.card : ℝ)) ^ 2 *
              max (∫ u in (1 : ℝ)..(min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
                s3RemMaj x Cm ℓ z (sc * z) u / u) 0 :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) hnonneg
    · rw [if_pos hc, if_neg (fun h => hℓc h.2)]
      have hlt : ⌊(x : ℝ) / (Cm : ℝ)⌋₊ < ℓ := by
        by_contra hcon
        exact hℓc (by exact_mod_cast (not_lt.mp hcon))
      have hCmpos : (0 : ℝ) < (Cm : ℝ) :=
        by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hCm1)
      have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ.1)
      have hle : (x : ℝ) < (ℓ : ℝ) * (Cm : ℝ) := by
        have h2 : ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ (ℓ : ℝ) := by
          have h := Nat.succ_le_of_lt hlt
          push_cast
          exact_mod_cast h
        have h3 : (x : ℝ) / (Cm : ℝ) < ((⌊(x : ℝ) / (Cm : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        have h4 : (x : ℝ) / (Cm : ℝ) < (ℓ : ℝ) := by linarith
        rw [div_lt_iff₀ hCmpos] at h4
        linarith
      have hU : min ((sc * z) / (Cm : ℝ)) ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) < 1 := by
        refine lt_of_le_of_lt (min_le_right _ _) ?_
        rw [div_lt_one (mul_pos hℓpos hCmpos)]
        exact hle
      have hz0 : (∫ u in (1 : ℝ)..(min ((sc * z) / (Cm : ℝ))
            ((x : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
          (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
            (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * (sc * z)) (x : ℝ)⌋₊
              - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u) = 0 := by
        rw [show (fun u : ℝ => (∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
              (ArithmeticFunction.moebius d : ℝ) *
              (cfR (ℓ * d) ⌊min ((ℓ : ℝ) * (sc * z)) (x : ℝ)⌋₊
                - cfR (ℓ * d) ⌊max ((ℓ : ℝ) * z) ((ℓ : ℝ) * (Cm : ℝ) * u)⌋₊)) / u)
            = fun u : ℝ => s3RemI x z (sc * z) Cm ℓ u / u from rfl]
        exact integral_s3RemI_eq_zero_of_lt_one x Cm ℓ z (sc * z) _ hU
      rw [hz0, mul_zero, abs_zero]
  · rw [if_neg hc, if_neg (fun h => hc h.1)]
    simp

end

end Work.FIChain
