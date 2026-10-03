import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S40
import Submission.ASP.S31
import Submission.ASP.S22
import Submission.ASP.S21
import Submission.ASP.S35
import Submission.ASP.S36
import Submission.ASP.S34
import Submission.ASP.S33
import Submission.ASP.S32
import Submission.ASP.S9b
import Submission.ASP.S9d
import Submission.ASP.S37
import Submission.ASP_R3
set_option maxHeartbeats 4000000
namespace Work.FIChain
open Finset
open Submission.ASP
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
local notation "Dmax" => (141 : ℝ) / 200

theorem rMain_cubefree_not4_le (lamm : ℝ) : ∃ X₀ : ℕ,
    ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
    ∀ N : ℕ, 2 ≤ N → (N : ℝ) ≤ (x : ℝ) ^ Dmax →
    (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
        |(Submission.Ad k t : ℝ) - (Submission.gdens k : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (-lamm) := by
  obtain ⟨cA, hcA, XA, hAlow⟩ := Submission.exists_const_mul_rpow_le_Aseq
  obtain ⟨CAd, hCAd, hAd⟩ := Submission.X2Y4R.sum_Ad_le
  obtain ⟨CAu, hCAu, hAu⟩ := Submission.Aseq_le_const_mul_rpow
  obtain ⟨Cg₀, Ag₀, hCg₀, hGg₀⟩ := Submission.X2Y4R.cubeSum_gdens_le
  obtain ⟨C35, A35, hC35, hA35, h35⟩ := Submission.prop35_unconditional
  obtain ⟨Cg, Ag, hCg, hAg, hGg⟩ : ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ y : ℕ, 2 ≤ y →
      Submission.X2Y4R.cubeSum y (fun d₁ d₂ => |(Submission.gdens (d₁ * d₂ ^ 2) : ℝ)|)
        ≤ C * (Real.log y) ^ A := by
    refine ⟨Cg₀ * max 1 ((Real.log 2) ^ (Ag₀ - max Ag₀ 0)), max Ag₀ 0,
      mul_pos hCg₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)), le_max_right _ _, fun y hy => ?_⟩
    have hmain := hGg₀ y hy
    have hb := Submission.rpow_log_le_const_mul (B := Ag₀) (A := max Ag₀ 0)
      (le_max_left _ _) hy
    have hlogy : (0 : ℝ) ≤ (Real.log y) ^ (max Ag₀ 0) :=
      Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y))) _
    have h2 : (Real.log 2) ^ (Ag₀ - max Ag₀ 0) ≤ max 1 ((Real.log 2) ^ (Ag₀ - max Ag₀ 0)) :=
      le_max_right _ _
    calc Submission.X2Y4R.cubeSum y (fun d₁ d₂ => |(Submission.gdens (d₁ * d₂ ^ 2) : ℝ)|)
        ≤ Cg₀ * (Real.log y) ^ Ag₀ := hmain
      _ ≤ Cg₀ * ((Real.log 2) ^ (Ag₀ - max Ag₀ 0) * (Real.log y) ^ (max Ag₀ 0)) :=
          mul_le_mul_of_nonneg_left hb hCg₀.le
      _ = Cg₀ * (Real.log 2) ^ (Ag₀ - max Ag₀ 0) * (Real.log y) ^ (max Ag₀ 0) := by ring
      _ ≤ Cg₀ * max 1 ((Real.log 2) ^ (Ag₀ - max Ag₀ 0)) * (Real.log y) ^ (max Ag₀ 0) := by
          refine mul_le_mul_of_nonneg_right ?_ hlogy
          exact mul_le_mul_of_nonneg_left h2 hCg₀.le
  set a1 : ℝ := Dmax / 4 + 9 / 16 + 1 / 100 with ha1def
  set a3 : ℝ := Dmax * (76 / 75) with ha3def
  have hα1 : a1 < 3 / 4 := by rw [ha1def]; norm_num
  have hα3 : a3 < 3 / 4 := by rw [ha3def]; norm_num
  obtain ⟨Y1, hY1x, hY1⟩ := Submission.X2Y4R3.poly_tail_gen (C35 + C35 * 2 ^ A35) a1 A35
    cA lamm (by positivity) hα1 hcA
  obtain ⟨Y2, hY2x, hY2⟩ := Submission.X2Y4R3.poly_tail_gen
    (1 + 2 * CAd * CAu * 2 ^ ((1:ℝ)/75) + 2 * CAu * Cg)
    a3 Ag cA lamm (by positivity) hα3 hcA
  refine ⟨Y1 + Y2 + XA + 100, fun x hx t ht2 htx N hN2 hNx => ?_⟩
  have hxY1 : Y1 ≤ x := by omega
  have hxY2 : Y2 ≤ x := by omega
  have hxXA : XA ≤ x := by omega
  have hx100 : 100 ≤ x := by omega
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx2R : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 3 ≤ x)
  have hx6R : (6 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 6 ≤ x)
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have he : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_d9, hx6R]
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlog0 : (0 : ℝ) ≤ Real.log x := le_trans zero_le_one hlog1
  have hlogpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := le_of_lt htpos
  have htle : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hNle : (N : ℝ) ≤ (x : ℝ) := le_trans hNx (by
    calc (x : ℝ) ^ Dmax ≤ (x : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = (x : ℝ) := Real.rpow_one _)
  have hAx : cA * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Submission.Aseq x : ℝ) := hAlow x hxXA
  have hlogz : (0 : ℝ) ≤ (Real.log (x : ℝ)) ^ (-lamm) := Real.rpow_nonneg hlog0 _
  have hfinal : ∀ K α β : ℝ, 0 < K → α < 3 / 4 →
      K * (x : ℝ) ^ α * (Real.log x) ^ β ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) →
      True := fun _ _ _ _ _ _ => trivial
  by_cases hcase : N ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊
  · -- ## Case A : `N ≤ t^{3/4}`
    have hcf := Submission.X2Y4R3.cubefree_sum_le_cubeSum N (by omega)
      (fun d => |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      (fun d => abs_nonneg _)
    have h35' := h35 N t hN2 ht2 hcase
    have hN4 : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ (Dmax / 4) := by
      have h1 : ((N : ℝ)) ^ ((1 : ℝ) / 4) ≤ (((x : ℝ) ^ Dmax)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hN0 hNx (by norm_num)
      have h2 : (((x : ℝ) ^ Dmax)) ^ ((1 : ℝ) / 4) = (x : ℝ) ^ (Dmax / 4) := by
        rw [← Real.rpow_mul hx0]; ring_nf
      linarith [h1, h2.le, h2.ge]
    have htpow : (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) ≤ (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
      Real.rpow_le_rpow ht0 htle (by norm_num)
    have hlogNt : Real.log ((N : ℝ) + (t : ℝ) + 2) ≤ 2 * Real.log x := by
      have h1 : (N : ℝ) + (t : ℝ) + 2 ≤ 3 * (x : ℝ) := by linarith [hNle, htle, hx2R]
      have h2 : Real.log ((N : ℝ) + (t : ℝ) + 2) ≤ Real.log (3 * (x : ℝ)) :=
        Real.log_le_log (by positivity) h1
      have h3 : Real.log (3 * (x : ℝ)) = Real.log 3 + Real.log x :=
        Real.log_mul (by norm_num) (ne_of_gt hxpos)
      have h4 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx3R
      linarith [h2, h3, h4]
    have hlogNtnn : (0 : ℝ) ≤ Real.log ((N : ℝ) + (t : ℝ) + 2) := by
      refine Real.log_nonneg ?_; linarith [hN0, ht0]
    have hsqrt : Real.sqrt (t : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow ht0 htle (by norm_num)
    have hxhalf : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ a1 :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by rw [ha1def]; norm_num)
    have hlogpow : (Real.log ((N : ℝ) + (t : ℝ) + 2)) ^ A35 ≤ 2 ^ A35 * (Real.log x) ^ A35 := by
      have h1 : (Real.log ((N : ℝ) + (t : ℝ) + 2)) ^ A35 ≤ (2 * Real.log x) ^ A35 :=
        Real.rpow_le_rpow hlogNtnn hlogNt hA35
      have h2 : (2 * Real.log x) ^ A35 = 2 ^ A35 * (Real.log x) ^ A35 :=
        Real.mul_rpow (by norm_num) hlog0
      rwa [h2] at h1
    have hlogpow1 : (1 : ℝ) ≤ (Real.log x) ^ A35 := Real.one_le_rpow hlog1 hA35
    have hK1 : (N : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
        ≤ (x : ℝ) ^ a1 * (Real.log x) ^ A35 := by
      have h2 : (x : ℝ) ^ (Dmax / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) = (x : ℝ) ^ a1 := by
        rw [← Real.rpow_add hxpos]
        congr 1
        rw [ha1def]; ring
      calc (N : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
          ≤ (x : ℝ) ^ (Dmax / 4) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
            mul_le_mul hN4 htpow (Real.rpow_nonneg ht0 _) (Real.rpow_nonneg hx0 _)
        _ = (x : ℝ) ^ a1 := h2
        _ ≤ (x : ℝ) ^ a1 * (Real.log x) ^ A35 :=
            le_mul_of_one_le_right (Real.rpow_nonneg hx0 _) hlogpow1
    have hK2 : Real.sqrt (t : ℝ) * (Real.log ((N : ℝ) + (t : ℝ) + 2)) ^ A35
        ≤ 2 ^ A35 * ((x : ℝ) ^ a1 * (Real.log x) ^ A35) := by
      calc Real.sqrt (t : ℝ) * (Real.log ((N : ℝ) + (t : ℝ) + 2)) ^ A35
          ≤ (x : ℝ) ^ ((1 : ℝ) / 2) * (2 ^ A35 * (Real.log x) ^ A35) :=
            mul_le_mul hsqrt hlogpow (Real.rpow_nonneg (by positivity) _)
              (Real.rpow_nonneg hx0 _)
        _ ≤ (x : ℝ) ^ a1 * (2 ^ A35 * (Real.log x) ^ A35) :=
            mul_le_mul_of_nonneg_right hxhalf (by positivity)
        _ = 2 ^ A35 * ((x : ℝ) ^ a1 * (Real.log x) ^ A35) := by ring
    have hsum : Submission.X2Y4R.cubeSum N
        (fun a b => |(Submission.Ad (a * b ^ 2) t : ℝ)
          - (Submission.gdens (a * b ^ 2) : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ (C35 + C35 * 2 ^ A35) * ((x : ℝ) ^ a1 * (Real.log x) ^ A35) := by
      have h1 : Submission.X2Y4R.cubeSum N
          (fun a b => |(Submission.Ad (a * b ^ 2) t : ℝ)
            - (Submission.gdens (a * b ^ 2) : ℝ) * (Submission.Aseq t : ℝ)|)
          ≤ C35 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100))
            + C35 * (Real.sqrt (t : ℝ) * (Real.log ((N : ℝ) + (t : ℝ) + 2)) ^ A35) := by
        have hh := h35'
        rw [mul_add] at hh
        exact hh
      calc Submission.X2Y4R.cubeSum N
            (fun a b => |(Submission.Ad (a * b ^ 2) t : ℝ)
              - (Submission.gdens (a * b ^ 2) : ℝ) * (Submission.Aseq t : ℝ)|)
          ≤ C35 * ((N : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100))
            + C35 * (Real.sqrt (t : ℝ) * (Real.log ((N : ℝ) + (t : ℝ) + 2)) ^ A35) := h1
        _ ≤ C35 * ((x : ℝ) ^ a1 * (Real.log x) ^ A35)
            + C35 * (2 ^ A35 * ((x : ℝ) ^ a1 * (Real.log x) ^ A35)) :=
            add_le_add (mul_le_mul_of_nonneg_left hK1 hC35.le)
              (mul_le_mul_of_nonneg_left hK2 hC35.le)
        _ = (C35 + C35 * 2 ^ A35) * ((x : ℝ) ^ a1 * (Real.log x) ^ A35) := by ring
    have hY := hY1 x hxY1
    have hcApos : 0 < cA := hcA
    have hle : (C35 + C35 * 2 ^ A35) * ((x : ℝ) ^ a1 * (Real.log x) ^ A35)
        ≤ cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
      have h := hY
      rw [show (C35 + C35 * 2 ^ A35) * (x : ℝ) ^ a1 * (Real.log x) ^ A35
          = (C35 + C35 * 2 ^ A35) * ((x : ℝ) ^ a1 * (Real.log x) ^ A35) from by ring] at h
      exact h
    have hcAx : cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
        ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
      mul_le_mul_of_nonneg_right hAx hlogz
    exact le_trans (le_trans hcf hsum) (le_trans hle hcAx)
  · -- ## Case C : `t^{3/4} < N`, crude bounds only
    have hcase' : ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ < N := not_le.mp hcase
    have ht34le : (t : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 * (N : ℝ) := by
      have h1 : ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) ≤ (t : ℝ) ^ ((3 : ℝ) / 4) :=
        Nat.floor_le (by positivity)
      have h2 : ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
        have h3 : ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ + 1 ≤ N := by omega
        exact_mod_cast h3
      have h4 : (t : ℝ) ^ ((3 : ℝ) / 4) < ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1 :=
        Nat.lt_floor_add_one _
      linarith
    have hAseqN : (Submission.Aseq t : ℝ) ≤ 2 * CAu * (N : ℝ) := by
      have h1 : (Submission.Aseq t : ℝ) ≤ CAu * (t : ℝ) ^ ((3 : ℝ) / 4) := hAu t (by omega)
      have h2 : CAu * (t : ℝ) ^ ((3 : ℝ) / 4) ≤ CAu * (2 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left ht34le hCAu.le
      nlinarith [h1, h2, hCAu.le, hN0]
    have ht100 : (t : ℝ) ^ ((1 : ℝ) / 100) ≤ 2 ^ ((1 : ℝ) / 75) * (N : ℝ) ^ ((1 : ℝ) / 75) := by
      have h1 : (t : ℝ) = ((t : ℝ) ^ ((3 : ℝ) / 4)) ^ ((4 : ℝ) / 3) := by
        rw [← Real.rpow_mul ht0]; norm_num
      have h2 : (t : ℝ) ≤ (2 * (N : ℝ)) ^ ((4 : ℝ) / 3) := by
        rw [h1]
        exact Real.rpow_le_rpow (Real.rpow_nonneg ht0 _) ht34le (by norm_num)
      have h3 : (t : ℝ) ^ ((1 : ℝ) / 100) ≤ ((2 * (N : ℝ)) ^ ((4 : ℝ) / 3)) ^ ((1 : ℝ) / 100) :=
        Real.rpow_le_rpow ht0 h2 (by norm_num)
      have h4 : ((2 * (N : ℝ)) ^ ((4 : ℝ) / 3)) ^ ((1 : ℝ) / 100)
          = (2 * (N : ℝ)) ^ ((1 : ℝ) / 75) := by
        rw [← Real.rpow_mul (by positivity)]; norm_num
      have h5 : (2 * (N : ℝ)) ^ ((1 : ℝ) / 75)
          = 2 ^ ((1 : ℝ) / 75) * (N : ℝ) ^ ((1 : ℝ) / 75) :=
        Real.mul_rpow (by norm_num) hN0
      linarith [h3, h4.le, h4.ge, h5.le, h5.ge]
    have hNpow : (N : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 75) = (N : ℝ) ^ ((76 : ℝ) / 75) := by
      nth_rewrite 1 [(Real.rpow_one (N : ℝ)).symm]
      rw [← Real.rpow_add hNpos]
      norm_num
    have hxca : (x : ℝ) ^ Dmax ≤ (x : ℝ) ^ a3 :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by rw [ha3def]; norm_num)
    have hlogAg1 : (1 : ℝ) ≤ (Real.log x) ^ Ag := Real.one_le_rpow hlog1 hAg
    have hlogAg0 : (0 : ℝ) ≤ (Real.log x) ^ Ag := le_trans zero_le_one hlogAg1
    -- pointwise triangle inequality, then separate the `A_d`- and the `g`-sums
    have hpt : ∀ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
        |(Submission.Ad k t : ℝ) - (Submission.gdens k : ℝ) * (Submission.Aseq t : ℝ)|
          ≤ (Submission.Ad k t : ℝ) + (Submission.gdens k : ℝ) * (Submission.Aseq t : ℝ) := by
      intro k hk
      have h1 : (0 : ℝ) ≤ (Submission.Ad k t : ℝ) := Nat.cast_nonneg _
      have hg0 : (0 : ℝ) ≤ (Submission.gdens k : ℝ) :=
        Rat.cast_nonneg.mpr (Submission.gdens_nonneg k)
      have hA0 : (0 : ℝ) ≤ (Submission.Aseq t : ℝ) := Nat.cast_nonneg _
      have h2 : (0 : ℝ) ≤ (Submission.gdens k : ℝ) * (Submission.Aseq t : ℝ) := mul_nonneg hg0 hA0
      simp only [abs_sub_le_iff]
      constructor <;> linarith
    have hstep1 : (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
        |(Submission.Ad k t : ℝ) - (Submission.gdens k : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
              (Submission.Ad k t : ℝ))
          + (Submission.Aseq t : ℝ) * (∑ k ∈ (Finset.range N).filter
              (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d), (Submission.gdens k : ℝ)) := by
      calc (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
            |(Submission.Ad k t : ℝ) - (Submission.gdens k : ℝ) * (Submission.Aseq t : ℝ)|)
          ≤ ∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
              ((Submission.Ad k t : ℝ) + (Submission.gdens k : ℝ) * (Submission.Aseq t : ℝ)) :=
            Finset.sum_le_sum hpt
        _ = (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
              (Submission.Ad k t : ℝ))
            + (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
              (Submission.gdens k : ℝ) * (Submission.Aseq t : ℝ)) := Finset.sum_add_distrib
        _ = (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
              (Submission.Ad k t : ℝ))
            + (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
              (Submission.gdens k : ℝ)) * (Submission.Aseq t : ℝ) := by rw [Finset.sum_mul]
        _ = (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
              (Submission.Ad k t : ℝ))
            + (Submission.Aseq t : ℝ) * (∑ k ∈ (Finset.range N).filter
              (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d), (Submission.gdens k : ℝ)) := by ring
    have hAdp : (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
        (Submission.Ad k t : ℝ))
        ≤ (N : ℝ) + CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (Submission.Aseq t : ℝ) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => by positivity)) (hAd N t)
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hGp : (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
        (Submission.gdens k : ℝ)) ≤ Cg * (Real.log (x : ℝ)) ^ Ag := by
      refine le_trans (le_of_eq ?_) (le_trans (Submission.X2Y4R3.cubefree_sum_le_cubeSum N (by omega)
        (fun d => |(Submission.gdens d : ℝ)|) (fun d => abs_nonneg _))
        (le_trans (hGg N hN2) ?_))
      · exact Finset.sum_congr rfl (fun k _ => by
          rw [abs_of_nonneg (Rat.cast_nonneg.mpr (Submission.gdens_nonneg k))])
      · refine mul_le_mul_of_nonneg_left ?_ hCg.le
        exact Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
          (Real.log_le_log hNpos hNle) hAg
    -- the three pieces, each `≤ K_i · x^{a3}·(log x)^{Ag}`
    have hP1 : (N : ℝ) ≤ (x : ℝ) ^ a3 * (Real.log x) ^ Ag := by
      calc (N : ℝ) ≤ (x : ℝ) ^ Dmax := hNx
        _ ≤ (x : ℝ) ^ a3 := hxca
        _ = (x : ℝ) ^ a3 * 1 := (mul_one _).symm
        _ ≤ (x : ℝ) ^ a3 * (Real.log x) ^ Ag :=
            mul_le_mul_of_nonneg_left hlogAg1 (Real.rpow_nonneg hx0 _)
    have hP2 : CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (Submission.Aseq t : ℝ)
        ≤ (2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75)) * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag) := by
      have h1 : CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (Submission.Aseq t : ℝ)
          ≤ CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (2 * CAu * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hAseqN (mul_nonneg hCAd.le (Real.rpow_nonneg ht0 _))
      have h2 : CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (2 * CAu * (N : ℝ))
          = 2 * CAd * CAu * ((N : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 100)) := by ring
      have h3 : 2 * CAd * CAu * ((N : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 100))
          ≤ 2 * CAd * CAu * ((N : ℝ) * (2 ^ ((1 : ℝ) / 75) * (N : ℝ) ^ ((1 : ℝ) / 75))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht100 hN0) (by positivity)
      have h4 : 2 * CAd * CAu * ((N : ℝ) * (2 ^ ((1 : ℝ) / 75) * (N : ℝ) ^ ((1 : ℝ) / 75)))
          = (2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75)) * (N : ℝ) ^ ((76 : ℝ) / 75) := by
        rw [show (N : ℝ) * (2 ^ ((1 : ℝ) / 75) * (N : ℝ) ^ ((1 : ℝ) / 75))
            = 2 ^ ((1 : ℝ) / 75) * ((N : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 75)) by ring, hNpow]
        ring
      have h5 : ((N : ℝ)) ^ ((76 : ℝ) / 75) ≤ ((x : ℝ) ^ Dmax) ^ ((76 : ℝ) / 75) :=
        Real.rpow_le_rpow hN0 hNx (by norm_num)
      have h6 : ((x : ℝ) ^ Dmax) ^ ((76 : ℝ) / 75) = (x : ℝ) ^ a3 := by
        rw [← Real.rpow_mul hx0, ha3def]
      calc CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (Submission.Aseq t : ℝ)
          ≤ 2 * CAd * CAu * ((N : ℝ) * (2 ^ ((1 : ℝ) / 75) * (N : ℝ) ^ ((1 : ℝ) / 75))) :=
            le_trans h1 (le_trans (le_of_eq h2) h3)
        _ = (2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75)) * (N : ℝ) ^ ((76 : ℝ) / 75) := h4
        _ ≤ (2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75)) * (x : ℝ) ^ a3 :=
            mul_le_mul_of_nonneg_left (le_trans h5 h6.le) (by positivity)
        _ = (2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75)) * (x : ℝ) ^ a3 * 1 := by ring
        _ ≤ (2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75)) * (x : ℝ) ^ a3 * (Real.log x) ^ Ag :=
            mul_le_mul_of_nonneg_left hlogAg1 (mul_nonneg (by positivity) (Real.rpow_nonneg hx0 _))
        _ = (2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75)) * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag) := by ring
    have hP3 : (2 * CAu * (N : ℝ)) * (Cg * (Real.log (x : ℝ)) ^ Ag)
        ≤ (2 * CAu * Cg) * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag) := by
      have h1 : (N : ℝ) ≤ (x : ℝ) ^ a3 := le_trans hNx hxca
      have h2 : (2 * CAu * (N : ℝ)) * (Cg * (Real.log (x : ℝ)) ^ Ag)
          = (2 * CAu * Cg) * ((N : ℝ) * (Real.log x) ^ Ag) := by ring
      rw [h2]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right h1 hlogAg0
    have hsumC : (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
        |(Submission.Ad k t : ℝ) - (Submission.gdens k : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ (1 + 2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75) + 2 * CAu * Cg)
            * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag) := by
      calc (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
            |(Submission.Ad k t : ℝ) - (Submission.gdens k : ℝ) * (Submission.Aseq t : ℝ)|)
          ≤ (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d),
                (Submission.Ad k t : ℝ))
            + (Submission.Aseq t : ℝ) * (∑ k ∈ (Finset.range N).filter
                (fun d => Submission.CubefreeD d ∧ ¬ 4 ∣ d), (Submission.gdens k : ℝ)) := hstep1
        _ ≤ ((N : ℝ) + CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (Submission.Aseq t : ℝ))
            + (2 * CAu * (N : ℝ)) * (Cg * (Real.log (x : ℝ)) ^ Ag) :=
            add_le_add hAdp (mul_le_mul hAseqN hGp
              (Finset.sum_nonneg (fun k _ => Rat.cast_nonneg.mpr (Submission.gdens_nonneg k)))
              (mul_nonneg (mul_nonneg (by norm_num) hCAu.le) hN0))
        _ ≤ (1 + 2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75) + 2 * CAu * Cg)
            * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag) := by
            have h : (N : ℝ) + CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (Submission.Aseq t : ℝ)
                ≤ 1 * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag)
                  + (2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75)) * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag) := by
              have hp1 : (N : ℝ) ≤ 1 * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag) := by
                simpa using hP1
              exact add_le_add hp1 hP2
            calc (N : ℝ) + CAd * (t : ℝ) ^ ((1 : ℝ) / 100) * (Submission.Aseq t : ℝ)
                  + (2 * CAu * (N : ℝ)) * (Cg * (Real.log (x : ℝ)) ^ Ag)
                ≤ (1 * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag)
                    + (2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75)) * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag))
                  + (2 * CAu * Cg) * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag) :=
                  add_le_add h hP3
              _ = (1 + 2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75) + 2 * CAu * Cg)
                    * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag) := by ring
    have hY := hY2 x hxY2
    have hle : (1 + 2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75) + 2 * CAu * Cg)
        * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag)
        ≤ cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
      have h := hY
      rw [show (1 + 2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75) + 2 * CAu * Cg) * (x : ℝ) ^ a3
            * (Real.log x) ^ Ag
          = (1 + 2 * CAd * CAu * 2 ^ ((1 : ℝ) / 75) + 2 * CAu * Cg)
            * ((x : ℝ) ^ a3 * (Real.log x) ^ Ag) from by ring] at h
      exact h
    have hcAx : cA * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
        ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
      mul_le_mul_of_nonneg_right hAx hlogz
    exact le_trans hsumC (le_trans hle hcAx)

end
end Work.FIChain
