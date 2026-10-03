import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_rho_div_polylog
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_bound_of_squarefree
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube
import Submission.Commons.NumberTheory.Nat.omega_color_sum_weighted_le
import Submission.Commons.NumberTheory.ArithmeticFunction.card_Omega_eq_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open scoped BigOperators
open Finset

/-- `Real.rpow x (-1)` written with the function notation (matches the form used
by `omega_color_sum_weighted_le`). -/
private lemma rpow_neg_one_eq (x : ℝ) : Real.rpow x (-1) = x⁻¹ := Real.rpow_neg_one x

/-- The error factor `h(d)` of Lemma 3.4 (Friedlander–Iwaniec, Annals 148),
evaluated at `d = d₁ d₂²` with `d₁, d₂` squarefree and coprime, via Lemma 3.4's
displayed formula `h(d)d = (Σ_{ν₁|d₁}ρ(d₁/ν₁)τ(d₁/ν₁))(Σ_{ν₂|d₂}ρ(d₂/ν₂)τ(d₂/ν₂)ν₂)`
where `ρ(m) = #{α : ZMod m // α ^ 2 = -1}`. -/
noncomputable def hdensF (d₁ d₂ : ℕ) : ℚ :=
  (2 / (((d₁ * d₂ ^ 2 : ℕ)) : ℚ)) *
    (∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
      (ν₂ : ℚ) * (({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ) *
        ((((Nat.divisors ((d₁ * d₂) / (ν₁ * ν₂))).card : ℕ) : ℚ) + 1))

/-- The divisor counting function is monotone with respect to divisibility, as
long as the larger number is nonzero. -/
private lemma card_divisors_le_of_dvd {m n : ℕ} (hn : n ≠ 0) (h : m ∣ n) :
    (Nat.divisors m).card ≤ (Nat.divisors n).card := by
  apply Finset.card_le_card
  intro d hd
  obtain ⟨hdm, -⟩ := Nat.mem_divisors.mp hd
  exact Nat.mem_divisors.mpr ⟨hdm.trans h, hn⟩

/-- The sum of the divisors of `d` is at most `d · τ(d)`. -/
private lemma sum_divisors_cast_le (d : ℕ) (hd : d ≠ 0) :
    (∑ ν ∈ Nat.divisors d, (ν : ℚ)) ≤ (d : ℚ) * ((Nat.divisors d).card : ℚ) := by
  calc (∑ ν ∈ Nat.divisors d, (ν : ℚ))
      ≤ ∑ _ν ∈ Nat.divisors d, (d : ℚ) := by
        apply Finset.sum_le_sum
        intro ν hν
        have hνd : ν ∣ d := (Nat.mem_divisors.mp hν).1
        have hle : ν ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hνd
        exact_mod_cast hle
    _ = (d : ℚ) * ((Nat.divisors d).card : ℚ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- The key pointwise bound: for squarefree coprime `d₁ d₂`, the local error
factor `h(d₁d₂²)` is at most `4 · 8^{ω(d₁)+ω(d₂)} / (d₁d₂)`. -/
lemma hdensF_le_aux {d₁ d₂ : ℕ} (h₁ : Squarefree d₁) (h₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) :
    hdensF d₁ d₂ ≤ 4 * (8 : ℚ) ^ ((d₁.primeFactors).card + (d₂.primeFactors).card)
      / (((d₁ * d₂ : ℕ)) : ℚ) := by
  have hd₁0 : d₁ ≠ 0 := h₁.ne_zero
  have hd₂0 : d₂ ≠ 0 := h₂.ne_zero
  have hn0 : d₁ * d₂ ≠ 0 := mul_ne_zero hd₁0 hd₂0
  set A : ℕ := (d₁.primeFactors).card with hA
  set B : ℕ := (d₂.primeFactors).card with hB
  set T : ℚ := ((Nat.divisors (d₁ * d₂)).card : ℚ) with hT
  have hτ₁ : (Nat.divisors d₁).card = 2 ^ A := card_divisors_of_squarefree hd₁0 h₁
  have hτ₂ : (Nat.divisors d₂).card = 2 ^ B := card_divisors_of_squarefree hd₂0 h₂
  have hτn : (Nat.divisors (d₁ * d₂)).card = 2 ^ (A + B) := by
    rw [Nat.Coprime.card_divisors_mul hcop, hτ₁, hτ₂, ← pow_add]
  have hT_eq : T = (2 : ℚ) ^ (A + B) := by
    rw [hT, hτn]; push_cast; ring
  have hT1 : (1 : ℚ) ≤ T := by
    rw [hT]
    have : 1 ≤ (Nat.divisors (d₁ * d₂)).card :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
    exact_mod_cast this
  -- Pointwise bound of the summand.
  have hterm : ∀ ν₁ ∈ Nat.divisors d₁, ∀ ν₂ ∈ Nat.divisors d₂,
      (ν₂ : ℚ) * (({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ) *
          ((((Nat.divisors ((d₁ * d₂) / (ν₁ * ν₂))).card : ℕ) : ℚ) + 1)
        ≤ 2 * (ν₂ : ℚ) * T ^ 2 := by
    intro ν₁ hν₁ ν₂ hν₂
    have hν₁dvd : ν₁ ∣ d₁ := (Nat.mem_divisors.mp hν₁).1
    have hν₂dvd : ν₂ ∣ d₂ := (Nat.mem_divisors.mp hν₂).1
    have hν₁pos : 0 < ν₁ := Nat.pos_of_dvd_of_pos hν₁dvd (Nat.pos_of_ne_zero hd₁0)
    have hν₂pos : 0 < ν₂ := Nat.pos_of_dvd_of_pos hν₂dvd (Nat.pos_of_ne_zero hd₂0)
    have hmulpos : 0 < ν₁ * ν₂ := Nat.mul_pos hν₁pos hν₂pos
    have hdvd : ν₁ * ν₂ ∣ d₁ * d₂ := Nat.mul_dvd_mul hν₁dvd hν₂dvd
    have hle : ν₁ * ν₂ ≤ d₁ * d₂ :=
      Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hd₁0) (Nat.pos_of_ne_zero hd₂0)) hdvd
    have hm1 : 1 ≤ (d₁ * d₂) / (ν₁ * ν₂) := (Nat.one_le_div_iff hmulpos).mpr hle
    have hmdvd : (d₁ * d₂) / (ν₁ * ν₂) ∣ d₁ * d₂ := Nat.div_dvd_of_dvd hdvd
    have hρ : ({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ)
        ≤ (Nat.divisors (d₁ * d₂)).card :=
      le_trans (rho_le_divisor_count hm1) (card_divisors_le_of_dvd hn0 hmdvd)
    have hτle : (Nat.divisors ((d₁ * d₂) / (ν₁ * ν₂))).card
        ≤ (Nat.divisors (d₁ * d₂)).card := card_divisors_le_of_dvd hn0 hmdvd
    have hρq : ((({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ)) ≤ T := by
      rw [hT]; exact_mod_cast hρ
    have hτq : ((((Nat.divisors ((d₁ * d₂) / (ν₁ * ν₂))).card : ℕ) : ℚ) + 1) ≤ 2 * T := by
      have h1 : (((Nat.divisors ((d₁ * d₂) / (ν₁ * ν₂))).card : ℕ) : ℚ) ≤ T := by
        rw [hT]; exact_mod_cast hτle
      linarith
    have hν₂nn : (0 : ℚ) ≤ (ν₂ : ℚ) := by positivity
    have ha : (ν₂ : ℚ) * (({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ)
        ≤ (ν₂ : ℚ) * T := mul_le_mul_of_nonneg_left hρq hν₂nn
    have hb : (0 : ℚ) ≤ (ν₂ : ℚ) * T := by nlinarith
    calc (ν₂ : ℚ) * (({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ) *
            ((((Nat.divisors ((d₁ * d₂) / (ν₁ * ν₂))).card : ℕ) : ℚ) + 1)
        = ((ν₂ : ℚ) * (({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ))
            * ((((Nat.divisors ((d₁ * d₂) / (ν₁ * ν₂))).card : ℕ) : ℚ) + 1) := rfl
      _ ≤ ((ν₂ : ℚ) * T) * (2 * T) := mul_le_mul ha hτq (by positivity) hb
      _ = 2 * (ν₂ : ℚ) * T ^ 2 := by ring
  -- Bound the double sum.
  have hsum1 : (∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
        (ν₂ : ℚ) * (({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard : ℕ) : ℚ) *
          ((((Nat.divisors ((d₁ * d₂) / (ν₁ * ν₂))).card : ℕ) : ℚ) + 1))
      ≤ ∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂, 2 * (ν₂ : ℚ) * T ^ 2 := by
    apply Finset.sum_le_sum
    intro ν₁ hν₁
    apply Finset.sum_le_sum
    intro ν₂ hν₂
    exact hterm ν₁ hν₁ ν₂ hν₂
  have hinner : (∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂, 2 * (ν₂ : ℚ) * T ^ 2)
      ≤ 2 * (d₂ : ℚ) * (8 : ℚ) ^ (A + B) := by
    have hconst : ∀ ν₁ ∈ Nat.divisors d₁,
        (∑ ν₂ ∈ Nat.divisors d₂, 2 * (ν₂ : ℚ) * T ^ 2)
          = 2 * T ^ 2 * (∑ ν₂ ∈ Nat.divisors d₂, (ν₂ : ℚ)) := by
      intro ν₁ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν₂ _
      ring
    have hstep : (∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂, 2 * (ν₂ : ℚ) * T ^ 2)
        = ((Nat.divisors d₁).card : ℚ)
            * (2 * T ^ 2 * (∑ ν₂ ∈ Nat.divisors d₂, (ν₂ : ℚ))) := by
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    rw [hstep]
    have hcard1 : ((Nat.divisors d₁).card : ℚ) = (2 : ℚ) ^ A := by
      rw [hτ₁]; push_cast; ring
    have hcard2 : ((Nat.divisors d₂).card : ℚ) = (2 : ℚ) ^ B := by
      rw [hτ₂]; push_cast; ring
    have hsum2 : (∑ ν₂ ∈ Nat.divisors d₂, (ν₂ : ℚ)) ≤ (d₂ : ℚ) * (2 : ℚ) ^ B := by
      have h := sum_divisors_cast_le d₂ hd₂0
      rwa [hcard2] at h
    rw [hcard1]
    have hbase : (2 : ℚ) ^ A * (2 : ℚ) ^ B = T := by
      rw [hT_eq, pow_add]
    have hkey8 : (8 : ℚ) ^ (A + B) = T ^ 2 * T := by
      rw [hT_eq, show (8 : ℚ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      ring
    calc (2 : ℚ) ^ A * (2 * T ^ 2 * (∑ ν₂ ∈ Nat.divisors d₂, (ν₂ : ℚ)))
        ≤ (2 : ℚ) ^ A * (2 * T ^ 2 * ((d₂ : ℚ) * (2 : ℚ) ^ B)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hsum2 (by positivity)
      _ = 2 * (d₂ : ℚ) * (8 : ℚ) ^ (A + B) := by
          rw [hkey8, ← hbase]; ring
  have hmain : hdensF d₁ d₂
      ≤ (2 / (((d₁ * d₂ ^ 2 : ℕ)) : ℚ)) * (2 * (d₂ : ℚ) * (8 : ℚ) ^ (A + B)) := by
    rw [hdensF]
    exact mul_le_mul_of_nonneg_left (le_trans hsum1 hinner) (by positivity)
  have hgoal : (2 / (((d₁ * d₂ ^ 2 : ℕ)) : ℚ)) * (2 * (d₂ : ℚ) * (8 : ℚ) ^ (A + B))
      = 4 * (8 : ℚ) ^ (A + B) / (((d₁ * d₂ : ℕ)) : ℚ) := by
    have hd1nz : (d₁ : ℚ) ≠ 0 := by exact_mod_cast hd₁0
    have hd2nz : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂0
    push_cast
    field_simp
    norm_num
  exact le_trans hmain (le_of_eq hgoal)

theorem sum_hdens_cubefree_le :
    ∃ C A : ℝ, 0 < C ∧ ∀ y : ℕ, 2 ≤ y →
      (∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
        if Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
            ∧ d₁ * d₂ ^ 2 ≤ y then hdensF d₁ d₂ else 0)
        ≤ C * (Real.log y) ^ A := by
  refine ⟨4 * (1 + 1 / Real.log 2) ^ (16 : ℕ), (16 : ℝ), ?_, ?_⟩
  · have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · intro y hy
    rw [Real.rpow_ofNat]
    set F : ℕ → ℝ := fun d => 4 * (8 : ℝ) ^ (d.primeFactors).card / (d : ℝ) with hF
    set G : ℕ → ℝ := fun d => (8 : ℝ) ^ (d.primeFactors).card / (d : ℝ) with hG
    have hG_eq : ∀ d : ℕ, G d = (8 : ℝ) ^ (d.primeFactors).card * Real.rpow (d : ℝ) (-1) := by
      intro d
      simp only [hG]
      rw [div_eq_mul_inv, rpow_neg_one_eq]
    have hcast : (((∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
        if Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
            ∧ d₁ * d₂ ^ 2 ≤ y then hdensF d₁ d₂ else 0) : ℚ) : ℝ)
        = ∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
            (if Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
                ∧ d₁ * d₂ ^ 2 ≤ y then (hdensF d₁ d₂ : ℝ) else 0) := by
      push_cast
      apply Finset.sum_congr rfl; intro d₁ _
      apply Finset.sum_congr rfl; intro d₂ _
      by_cases hc : (Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
            ∧ d₁ * d₂ ^ 2 ≤ y)
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]
        norm_num
    have hterm : ∀ d₁ ∈ Finset.Icc 1 y, ∀ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
        (if Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
            ∧ d₁ * d₂ ^ 2 ≤ y then (hdensF d₁ d₂ : ℝ) else 0) ≤ F d₁ * G d₂ := by
      intro d₁ _ d₂ _
      by_cases hc : (Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
            ∧ d₁ * d₂ ^ 2 ≤ y)
      · rw [if_pos hc]
        obtain ⟨hs1, hs2, hcop, -, -⟩ := hc
        have h := hdensF_le_aux hs1 hs2 hcop
        have hreal : (hdensF d₁ d₂ : ℝ)
            ≤ 4 * (8 : ℝ) ^ ((d₁.primeFactors).card + (d₂.primeFactors).card)
              / ((d₁ : ℝ) * (d₂ : ℝ)) := by
          have h2 : ((hdensF d₁ d₂ : ℚ) : ℝ)
              ≤ ((4 * (8 : ℚ) ^ ((d₁.primeFactors).card + (d₂.primeFactors).card)
                  / (((d₁ * d₂ : ℕ)) : ℚ) : ℚ) : ℝ) := by
            exact_mod_cast h
          have h3 : ((4 * (8 : ℚ) ^ ((d₁.primeFactors).card + (d₂.primeFactors).card)
                  / (((d₁ * d₂ : ℕ)) : ℚ) : ℚ) : ℝ)
              = 4 * (8 : ℝ) ^ ((d₁.primeFactors).card + (d₂.primeFactors).card)
                / ((d₁ : ℝ) * (d₂ : ℝ)) := by
            push_cast; ring
          rw [h3] at h2; exact h2
        have hFG : F d₁ * G d₂
            = 4 * (8 : ℝ) ^ ((d₁.primeFactors).card + (d₂.primeFactors).card)
              / ((d₁ : ℝ) * (d₂ : ℝ)) := by
          simp only [hF, hG]
          rw [div_mul_div_comm, mul_assoc, ← pow_add]
        rw [hFG]; exact hreal
      · rw [if_neg hc]
        simp only [hF, hG]
        positivity
    have hstep1 : (∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
        (if Squarefree d₁ ∧ Squarefree d₂ ∧ Nat.Coprime d₁ d₂ ∧ ¬ 4 ∣ d₁ * d₂ ^ 2
            ∧ d₁ * d₂ ^ 2 ≤ y then (hdensF d₁ d₂ : ℝ) else 0))
        ≤ ∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), F d₁ * G d₂ := by
      apply Finset.sum_le_sum; intro d₁ hd₁
      apply Finset.sum_le_sum; intro d₂ hd₂
      exact hterm d₁ hd₁ d₂ hd₂
    have hstep2 : (∑ d₁ ∈ Finset.Icc 1 y, ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), F d₁ * G d₂)
        = (∑ d₁ ∈ Finset.Icc 1 y, F d₁) * (∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), G d₂) :=
      (Finset.sum_mul_sum _ _ _ _).symm
    have hlogy_nn : 0 ≤ Real.log (y : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
    have hsqrt_pos : 0 < Nat.sqrt y := Nat.sqrt_pos.mpr (by omega)
    have hsqrt_ge1 : 1 ≤ Nat.sqrt y := Nat.le_sqrt.mpr (by omega)
    have hGnn : ∀ d : ℕ, 0 ≤ G d := by
      intro d; simp only [hG]; positivity
    have hbnd1 : (∑ d₁ ∈ Finset.Icc 1 y, G d₁) ≤ (1 + Real.log (y : ℝ)) ^ 8 := by
      have hcolor := Commons.NumberTheory.Nat.omega_color_sum_weighted_le 8 y
        (by norm_num) 1 (by norm_num)
      calc (∑ d₁ ∈ Finset.Icc 1 y, G d₁)
          = ∑ d₁ ∈ Finset.Icc 1 y, (8 : ℝ) ^ (d₁.primeFactors).card * Real.rpow (d₁ : ℝ) (-1) := by
            apply Finset.sum_congr rfl; intro d _; exact hG_eq d
        _ ≤ (∑ k ∈ Finset.Icc 1 y, Real.rpow (k : ℝ) (-1)) ^ 8 := hcolor
        _ ≤ (1 + Real.log (y : ℝ)) ^ 8 := by
            refine pow_le_pow_left₀ ?_ ?_ 8
            · exact Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (by positivity) _)
            · rw [show (∑ k ∈ Finset.Icc 1 y, Real.rpow (k : ℝ) (-1))
                  = ∑ k ∈ Finset.Icc 1 y, 1 / (k : ℝ) by
                apply Finset.sum_congr rfl; intro k _; rw [rpow_neg_one_eq, one_div]]
              exact Commons.NumberTheory.ArithmeticFunction.sum_inv_Icc_one_le_one_add_log y
    have hbnd2 : (∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), G d₂)
        ≤ (1 + Real.log (Nat.sqrt y : ℝ)) ^ 8 := by
      have hcolor := Commons.NumberTheory.Nat.omega_color_sum_weighted_le 8 (Nat.sqrt y)
        (by norm_num) 1 (by norm_num)
      calc (∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), G d₂)
          = ∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y),
              (8 : ℝ) ^ (d₂.primeFactors).card * Real.rpow (d₂ : ℝ) (-1) := by
            apply Finset.sum_congr rfl; intro d _; exact hG_eq d
        _ ≤ (∑ k ∈ Finset.Icc 1 (Nat.sqrt y), Real.rpow (k : ℝ) (-1)) ^ 8 := hcolor
        _ ≤ (1 + Real.log (Nat.sqrt y : ℝ)) ^ 8 := by
            refine pow_le_pow_left₀ ?_ ?_ 8
            · exact Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (by positivity) _)
            · rw [show (∑ k ∈ Finset.Icc 1 (Nat.sqrt y), Real.rpow (k : ℝ) (-1))
                  = ∑ k ∈ Finset.Icc 1 (Nat.sqrt y), 1 / (k : ℝ) by
                apply Finset.sum_congr rfl; intro k _; rw [rpow_neg_one_eq, one_div]]
              exact Commons.NumberTheory.ArithmeticFunction.sum_inv_Icc_one_le_one_add_log (Nat.sqrt y)
    have hfs : (∑ d₁ ∈ Finset.Icc 1 y, F d₁) = 4 * (∑ d₁ ∈ Finset.Icc 1 y, G d₁) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      simp only [hF, hG]; ring
    have hnonneg1 : (0 : ℝ) ≤ 4 * (1 + Real.log (y : ℝ)) ^ 8 :=
      mul_nonneg (by norm_num) (pow_nonneg (by linarith) 8)
    have hnonneg2 : (0 : ℝ) ≤ 4 * (1 + 1 / Real.log 2) ^ 16 := by
      have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have : 0 ≤ 1 + 1 / Real.log 2 := by positivity
      exact mul_nonneg (by norm_num) (pow_nonneg this 16)
    have hstep3 : (∑ d₁ ∈ Finset.Icc 1 y, F d₁) * (∑ d₂ ∈ Finset.Icc 1 (Nat.sqrt y), G d₂)
        ≤ (4 * (1 + Real.log (y : ℝ)) ^ 8) * (1 + Real.log (Nat.sqrt y : ℝ)) ^ 8 := by
      rw [hfs]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hbnd1 (by norm_num)) hbnd2
        (Finset.sum_nonneg (fun d _ => hGnn d)) hnonneg1
    have hstep4 : (4 * (1 + Real.log (y : ℝ)) ^ 8) * (1 + Real.log (Nat.sqrt y : ℝ)) ^ 8
        ≤ 4 * (1 + Real.log (y : ℝ)) ^ 16 := by
      have hls : Real.log (Nat.sqrt y : ℝ) ≤ Real.log (y : ℝ) :=
        Real.log_le_log (by exact_mod_cast hsqrt_pos) (by exact_mod_cast Nat.sqrt_le_self y)
      have h1 : 1 + Real.log (Nat.sqrt y : ℝ) ≤ 1 + Real.log (y : ℝ) := by linarith
      have h0 : (0 : ℝ) ≤ 1 + Real.log (Nat.sqrt y : ℝ) := by
        have := Real.log_nonneg (show (1:ℝ) ≤ (Nat.sqrt y : ℝ) by exact_mod_cast hsqrt_ge1)
        linarith
      have hpow := pow_le_pow_left₀ h0 h1 8
      calc (4 * (1 + Real.log (y : ℝ)) ^ 8) * (1 + Real.log (Nat.sqrt y : ℝ)) ^ 8
          ≤ (4 * (1 + Real.log (y : ℝ)) ^ 8) * (1 + Real.log (y : ℝ)) ^ 8 :=
            mul_le_mul_of_nonneg_left hpow hnonneg1
        _ = 4 * (1 + Real.log (y : ℝ)) ^ 16 := by ring
    have hstep5 : 4 * (1 + Real.log (y : ℝ)) ^ 16
        ≤ 4 * (1 + 1 / Real.log 2) ^ 16 * (Real.log (y : ℝ)) ^ 16 := by
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlogy2 : Real.log 2 ≤ Real.log (y : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hy)
      have hdiv : (1 : ℝ) ≤ Real.log (y : ℝ) / Real.log 2 := (one_le_div hlog2).mpr hlogy2
      have hstep : 1 + Real.log (y : ℝ) ≤ (1 + 1 / Real.log 2) * Real.log (y : ℝ) := by
        have heq : (1 + 1 / Real.log 2) * Real.log (y : ℝ)
            = Real.log (y : ℝ) + Real.log (y : ℝ) / Real.log 2 := by
          field_simp
        rw [heq]; linarith
      have h0 : (0 : ℝ) ≤ 1 + Real.log (y : ℝ) := by linarith
      have hpow := pow_le_pow_left₀ h0 hstep 16
      calc 4 * (1 + Real.log (y : ℝ)) ^ 16
          ≤ 4 * ((1 + 1 / Real.log 2) * Real.log (y : ℝ)) ^ 16 :=
            mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ = 4 * (1 + 1 / Real.log 2) ^ 16 * (Real.log (y : ℝ)) ^ 16 := by rw [mul_pow]; ring
    rw [hcast]
    exact le_trans hstep1 (le_trans (le_of_eq hstep2)
      (le_trans hstep3 (le_trans hstep4 hstep5)))


end Commons.NumberTheory.FriedlanderIwaniec
