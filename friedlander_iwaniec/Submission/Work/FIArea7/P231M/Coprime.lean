import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.P231M.lbilinDecomp
import Submission.Work.FIArea7.P231.card_divisors_mul_le
import Submission.Work.FIArea7.P231.tau_sq_div_sum_le


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea7.P231M

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The coprime bound of Prop. 23.1 with the power loss `(MN+c+2)^ε`. -/
def CoprimeBoundEps (ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (M N c : ℕ) (k : ℤ) (χ : GaussianInt → ℂ) (α β : ℕ → ℂ),
      1 ≤ c → 1 ≤ M → 1 ≤ N →
      (∀ z, ‖χ z‖ ≤ 1) →
      (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → χ (z1 * z2) = χ z1 * χ z2) →
      (∀ m, m ∈ Finset.Icc 1 M → ‖α m‖ ≤ 1) →
      (∀ n, n ∈ Finset.Icc 1 N → ‖β n‖ ≤ 1) →
      ‖Work.FIArea7.LBilinStar M N c (Work.FIArea7.grossenChar χ k) α β‖
        ≤ C * ((c.divisors.card : ℝ)) * ((M : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 12)
            * ((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12)
            * (((M : ℝ) * (N : ℝ) + (c : ℝ) + 2) ^ ε)

/-- The elementary comparison of the `d`-dilation step. -/
lemma term_g_le {M N g : ℕ} (hg : 1 ≤ g) (hgM : g ≤ M) (hgN : g ≤ N) :
    (((M / g : ℕ) : ℝ) + ((N / g : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
        * ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ))) ^ ((11 : ℝ) / 12)
      ≤ (g : ℝ) ^ (-(23 / 12 : ℝ))
        * (((M : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 12)
            * (((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12))) := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  have hMg : ((M / g : ℕ) : ℝ) ≤ (M : ℝ) / g := by
    have h : ((M / g : ℕ) : ℝ) ≤ (M : ℝ) / (g : ℝ) := Nat.cast_div_le
    simpa using h
  have hNg : ((N / g : ℕ) : ℝ) ≤ (N : ℝ) / g := by
    have h : ((N / g : ℕ) : ℝ) ≤ (N : ℝ) / (g : ℝ) := Nat.cast_div_le
    simpa using h
  have h1 : (((M / g : ℕ) : ℝ) + ((N / g : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
      ≤ (((M : ℝ) + (N : ℝ)) / g) ^ ((1 : ℝ) / 12) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have h2 : (M : ℝ) / g + (N : ℝ) / g = ((M : ℝ) + (N : ℝ)) / g := by ring
    linarith [hMg, hNg]
  have h2 : ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ))) ^ ((11 : ℝ) / 12)
      ≤ (((M : ℝ) * (N : ℝ)) / g ^ 2) ^ ((11 : ℝ) / 12) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have h3 : ((M : ℝ) / g) * ((N : ℝ) / g) = ((M : ℝ) * (N : ℝ)) / g ^ 2 := by ring
    have h4 : ((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ)
        ≤ ((M : ℝ) / g) * ((N : ℝ) / g) :=
      mul_le_mul hMg hNg (by positivity) (by positivity)
    rwa [h3] at h4
  have hgpow : (g : ℝ) ^ (-((1 : ℝ) / 12)) * (g : ℝ) ^ (-(11 / 6 : ℝ))
      = (g : ℝ) ^ (-(23 / 12 : ℝ)) := by
    rw [← Real.rpow_add hg0]
    norm_num
  have hA : (((M : ℝ) + (N : ℝ)) / g) ^ ((1 : ℝ) / 12)
      = ((M : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 12) * (g : ℝ) ^ (-((1 : ℝ) / 12)) := by
    rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
      Real.inv_rpow (by positivity)]
    exact congrArg (fun t => ((M : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 12) * t)
      (Real.rpow_neg (le_of_lt hg0) ((1 : ℝ) / 12)).symm
  have hB : (((M : ℝ) * (N : ℝ)) / g ^ 2) ^ ((11 : ℝ) / 12)
      = ((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12) * (g : ℝ) ^ (-(11 / 6 : ℝ)) := by
    rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
      Real.inv_rpow (by positivity), ← Real.rpow_natCast (g : ℝ) 2,
      ← Real.rpow_mul (le_of_lt hg0)]
    have h2 : ((2 : ℕ) : ℝ) * ((11 : ℝ) / 12) = (11 : ℝ) / 6 := by norm_num
    rw [h2]
    exact congrArg (fun t => ((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12) * t)
      (Real.rpow_neg (le_of_lt hg0) (11 / 6)).symm
  have h4 : (((M : ℝ) + (N : ℝ)) / g) ^ ((1 : ℝ) / 12)
      * (((M : ℝ) * (N : ℝ)) / g ^ 2) ^ ((11 : ℝ) / 12)
      = (g : ℝ) ^ (-(23 / 12 : ℝ))
        * (((M : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 12) * ((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12)) := by
    rw [hA, hB, ← hgpow]
    ring
  calc (((M / g : ℕ) : ℝ) + ((N / g : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
        * ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ))) ^ ((11 : ℝ) / 12)
      ≤ (((M : ℝ) + (N : ℝ)) / g) ^ ((1 : ℝ) / 12)
        * (((M : ℝ) * (N : ℝ)) / g ^ 2) ^ ((11 : ℝ) / 12) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = _ := h4

/-! ## Prop. 23.1 from the coprime bound -/

theorem prop231_of_coprimeEps (h : ∀ ε : ℝ, 0 < ε → CoprimeBoundEps ε) :
    Work.FIArea7.Prop231 := by
  intro ε hε
  have hε1 : (0 : ℝ) < min (ε / 3) (1 / 4) := lt_min (by linarith) (by norm_num)
  obtain ⟨C₁, hC₁, hbound⟩ := h (min (ε / 3) (1 / 4)) hε1
  obtain ⟨K, hKpos, hK⟩ := Work.FIArea7.P231.tau_sq_div_sum_le
  have hε1le : min (ε / 3) (1 / 4) ≤ ε := by
    have := min_le_left (ε / 3) (1 / 4)
    linarith
  have h3ε1 : 3 * min (ε / 3) (1 / 4) ≤ ε := by
    have := min_le_left (ε / 3) (1 / 4)
    linarith
  have hC1max : C₁ ≤ C₁ * max 1 K := by
    have : (1 : ℝ) ≤ max 1 K := le_max_left _ _
    nlinarith [hC₁]
  refine ⟨C₁ * max 1 K, by positivity, ?_⟩
  intro M N c d k χ α β hc hM hN hd hχ hχmul hα hβ
  set ψ : GaussianInt → ℂ := Work.FIArea7.grossenChar χ k with hψ
  set τc : ℝ := (((c.divisors.card : ℕ) : ℝ)) with hτc
  set A : ℝ := ((M : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 12) with hA
  set B : ℝ := ((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12) with hB
  set Lb : ℝ := ((M : ℝ) * (N : ℝ) + (c : ℝ) + 2) with hLb
  have hbase : (1 : ℝ) ≤ Lb := by
    rw [hLb]
    have h1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have h2 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    have h3 : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast Nat.zero_le c
    nlinarith
  have hLb0 : (0 : ℝ) < Lb := by linarith
  have hA0 : (0 : ℝ) ≤ A := by rw [hA]; positivity
  have hB0 : (0 : ℝ) ≤ B := by rw [hB]; positivity
  have hτc0 : (0 : ℝ) ≤ τc := by rw [hτc]; positivity
  refine ⟨?_, ?_⟩
  · -- `L(M,N)` via the `d`-dilation
    rw [Work.FIArea7.P231.lbilinDecomp M N c ψ α β]
    have hterm : ∀ g ∈ Finset.Icc 1 (min M N),
        ‖Work.FIArea7.LBilinStar (M / g) (N / g) (c * g ^ 2) ψ
            (fun a => α (g * a)) (fun b => β (g * b))‖
          ≤ C₁ * ((((c * g ^ 2).divisors.card : ℕ) : ℝ)) * (g : ℝ) ^ (-(23 / 12 : ℝ))
              * (A * B * Lb ^ ε) := by
      intro g hg
      rw [Finset.mem_Icc] at hg
      obtain ⟨hg1, hg2⟩ := hg
      have hgM : g ≤ M := le_trans hg2 (min_le_left _ _)
      have hgN : g ≤ N := le_trans hg2 (min_le_right _ _)
      have hgpos : 0 < g := hg1
      have hMg : 1 ≤ M / g := (Nat.one_le_div_iff hgpos).mpr hgM
      have hNg : 1 ≤ N / g := (Nat.one_le_div_iff hgpos).mpr hgN
      have hcg : 1 ≤ c * g ^ 2 := by
        refine Nat.one_le_iff_ne_zero.mpr ?_
        exact Nat.mul_ne_zero (by omega) (pow_ne_zero 2 (by omega))
      have hαg : ∀ m, m ∈ Finset.Icc 1 (M / g) → ‖(fun a => α (g * a)) m‖ ≤ 1 := by
        intro m hm
        rw [Finset.mem_Icc] at hm
        obtain ⟨hm1, hm2⟩ := hm
        have hmem : g * m ∈ Finset.Icc 1 M := by
          rw [Finset.mem_Icc]
          exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
            le_trans (Nat.mul_le_mul_left g hm2) (Nat.mul_div_le M g)⟩
        exact hα (g * m) hmem
      have hβg : ∀ m, m ∈ Finset.Icc 1 (N / g) → ‖(fun b => β (g * b)) m‖ ≤ 1 := by
        intro m hm
        rw [Finset.mem_Icc] at hm
        obtain ⟨hm1, hm2⟩ := hm
        have hmem : g * m ∈ Finset.Icc 1 N := by
          rw [Finset.mem_Icc]
          exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
            le_trans (Nat.mul_le_mul_left g hm2) (Nat.mul_div_le N g)⟩
        exact hβ (g * m) hmem
      have hb := hbound (M / g) (N / g) (c * g ^ 2) k χ
        (fun a => α (g * a)) (fun b => β (g * b)) hcg hMg hNg hχ hχmul hαg hβg
      -- the `g`-factors and the loss
      have hterm1 : (((M / g : ℕ) : ℝ) + ((N / g : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
            * ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ))) ^ ((11 : ℝ) / 12)
          ≤ (g : ℝ) ^ (-(23 / 12 : ℝ)) * (A * B) := by
        rw [hA, hB]
        exact term_g_le hg1 hgM hgN
      have hlossg : (((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ) + ((c * g ^ 2 : ℕ) : ℝ) + 2)
            ^ min (ε / 3) (1 / 4)
          ≤ Lb ^ ε := by
        have hg1R : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
        have hg0 : (0 : ℝ) < (g : ℝ) := by linarith
        have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg c
        have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        have h9 : (g : ℝ) ≤ (M : ℝ) := by exact_mod_cast hgM
        have h1 : ((M / g : ℕ) : ℝ) ≤ (M : ℝ) / g := by
          have hh : ((M / g : ℕ) : ℝ) ≤ (M : ℝ) / (g : ℝ) := Nat.cast_div_le
          simpa using hh
        have h2 : ((N / g : ℕ) : ℝ) ≤ (N : ℝ) / g := by
          have hh : ((N / g : ℕ) : ℝ) ≤ (N : ℝ) / (g : ℝ) := Nat.cast_div_le
          simpa using hh
        have h3 : ((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ) ≤ (M : ℝ) * (N : ℝ) := by
          have hdivM : (M : ℝ) / g ≤ (M : ℝ) := by
            rw [div_le_iff₀ hg0]
            nlinarith [hM0, hg1R]
          have hdivN : (N : ℝ) / g ≤ (N : ℝ) := by
            rw [div_le_iff₀ hg0]
            nlinarith [hN0, hg1R]
          have hMg0 : (0 : ℝ) ≤ (M : ℝ) / g := div_nonneg hM0 (le_of_lt hg0)
          exact le_trans (mul_le_mul h1 h2 (by positivity) hMg0)
            (mul_le_mul hdivM hdivN (by positivity) hM0)
        have h5 : ((c * g ^ 2 : ℕ) : ℝ) ≤ (c : ℝ) * g ^ 2 := by
          rw [show ((c * g ^ 2 : ℕ) : ℝ) = (c : ℝ) * (g : ℝ) ^ 2 by push_cast; ring]
        have hgp : (1 : ℝ) ≤ g ^ 2 := by nlinarith [hg1R]
        have hMNg : (M : ℝ) * (N : ℝ) ≤ (M : ℝ) * (N : ℝ) * g ^ 2 := by
          have h1 : (M : ℝ) * 1 ≤ (M : ℝ) * g ^ 2 := mul_le_mul_of_nonneg_left hgp hM0
          nlinarith [h1, hM0, hN0]
        have h6 : ((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ) + ((c * g ^ 2 : ℕ) : ℝ) + 2
            ≤ Lb * g ^ 2 := by
          rw [hLb]
          nlinarith [h3, hMNg, h5, hgp, hc0]
        have h7 : Lb * g ^ 2 ≤ Lb ^ 3 := by
          have h8 : (g : ℝ) ≤ Lb := by
            rw [hLb]
            nlinarith [h9, hM0, hN0, hc0, hN1]
          have hg2 : g ^ 2 ≤ Lb ^ 2 := pow_le_pow_left₀ (le_of_lt hg0) h8 2
          calc Lb * g ^ 2 ≤ Lb * Lb ^ 2 :=
                mul_le_mul_of_nonneg_left hg2 (le_of_lt hLb0)
            _ = Lb ^ 3 := by ring
        calc (((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ) + ((c * g ^ 2 : ℕ) : ℝ) + 2)
              ^ min (ε / 3) (1 / 4)
            ≤ (Lb ^ 3) ^ min (ε / 3) (1 / 4) :=
              Real.rpow_le_rpow (by positivity) (le_trans h6 h7) (by positivity)
          _ = Lb ^ (3 * min (ε / 3) (1 / 4)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hLb0)]
              norm_num
          _ ≤ Lb ^ ε := Real.rpow_le_rpow_of_exponent_le hbase h3ε1
      have hprod : (((M / g : ℕ) : ℝ) + ((N / g : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
            * ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ))) ^ ((11 : ℝ) / 12)
            * (((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ) + ((c * g ^ 2 : ℕ) : ℝ) + 2)
                ^ min (ε / 3) (1 / 4)
          ≤ (g : ℝ) ^ (-(23 / 12 : ℝ)) * (A * B * Lb ^ ε) := by
        have h1 : (0 : ℝ) ≤ ((((M / g : ℕ) : ℝ) + ((N / g : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
            * ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ))) ^ ((11 : ℝ) / 12)) := by positivity
        have h2 : (0 : ℝ) ≤ (((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ)
            + ((c * g ^ 2 : ℕ) : ℝ) + 2) ^ min (ε / 3) (1 / 4) := by positivity
        have h3 : ((((M / g : ℕ) : ℝ) + ((N / g : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
              * ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ))) ^ ((11 : ℝ) / 12))
              * (((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ) + ((c * g ^ 2 : ℕ) : ℝ) + 2)
                  ^ min (ε / 3) (1 / 4)
            ≤ ((g : ℝ) ^ (-(23 / 12 : ℝ)) * (A * B)) * Lb ^ ε :=
          mul_le_mul hterm1 hlossg (by positivity) (by positivity)
        calc (((M / g : ℕ) : ℝ) + ((N / g : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
              * ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ))) ^ ((11 : ℝ) / 12)
              * (((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ) + ((c * g ^ 2 : ℕ) : ℝ) + 2)
                  ^ min (ε / 3) (1 / 4)
            = ((((M / g : ℕ) : ℝ) + ((N / g : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
              * ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ))) ^ ((11 : ℝ) / 12))
              * ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ) + ((c * g ^ 2 : ℕ) : ℝ) + 2)
                  ^ min (ε / 3) (1 / 4)) := by ring
          _ ≤ ((g : ℝ) ^ (-(23 / 12 : ℝ)) * (A * B)) * Lb ^ ε := h3
          _ = (g : ℝ) ^ (-(23 / 12 : ℝ)) * (A * B * Lb ^ ε) := by ring
      refine hb.trans ?_
      calc C₁ * ((((c * g ^ 2).divisors.card : ℕ) : ℝ))
            * (((M / g : ℕ) : ℝ) + ((N / g : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
            * ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ))) ^ ((11 : ℝ) / 12)
            * (((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ) + ((c * g ^ 2 : ℕ) : ℝ) + 2)
                ^ min (ε / 3) (1 / 4)
          = C₁ * ((((c * g ^ 2).divisors.card : ℕ) : ℝ))
              * ((((M / g : ℕ) : ℝ) + ((N / g : ℕ) : ℝ)) ^ ((1 : ℝ) / 12)
                * ((((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ))) ^ ((11 : ℝ) / 12)
                * (((M / g : ℕ) : ℝ) * ((N / g : ℕ) : ℝ) + ((c * g ^ 2 : ℕ) : ℝ) + 2)
                    ^ min (ε / 3) (1 / 4)) := by ring
        _ ≤ C₁ * ((((c * g ^ 2).divisors.card : ℕ) : ℝ))
              * ((g : ℝ) ^ (-(23 / 12 : ℝ)) * (A * B * Lb ^ ε)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = C₁ * ((((c * g ^ 2).divisors.card : ℕ) : ℝ)) * (g : ℝ) ^ (-(23 / 12 : ℝ))
              * (A * B * Lb ^ ε) := by ring
    have hsum1 : ‖∑ g ∈ Finset.Icc 1 (min M N),
          Work.FIArea7.LBilinStar (M / g) (N / g) (c * g ^ 2) ψ
            (fun a => α (g * a)) (fun b => β (g * b))‖
        ≤ ∑ g ∈ Finset.Icc 1 (min M N),
            C₁ * ((((c * g ^ 2).divisors.card : ℕ) : ℝ)) * (g : ℝ) ^ (-(23 / 12 : ℝ))
              * (A * B * Lb ^ ε) :=
      le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
    have hsum2 : (∑ g ∈ Finset.Icc 1 (min M N),
            C₁ * ((((c * g ^ 2).divisors.card : ℕ) : ℝ)) * (g : ℝ) ^ (-(23 / 12 : ℝ))
              * (A * B * Lb ^ ε))
        = C₁ * (∑ g ∈ Finset.Icc 1 (min M N),
            ((((c * g ^ 2).divisors.card : ℕ) : ℝ)) * (g : ℝ) ^ (-(23 / 12 : ℝ)))
            * (A * B * Lb ^ ε) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      ring
    have hsum3 : C₁ * (∑ g ∈ Finset.Icc 1 (min M N),
            ((((c * g ^ 2).divisors.card : ℕ) : ℝ)) * (g : ℝ) ^ (-(23 / 12 : ℝ)))
            * (A * B * Lb ^ ε)
        ≤ C₁ * (K * τc) * (A * B * Lb ^ ε) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₁)
      rw [hτc]
      calc (∑ g ∈ Finset.Icc 1 (min M N),
            ((((c * g ^ 2).divisors.card : ℕ) : ℝ)) * (g : ℝ) ^ (-(23 / 12 : ℝ)))
          ≤ ∑ g ∈ Finset.Icc 1 (min M N),
              (((c.divisors.card : ℕ) : ℝ)) * ((((g ^ 2).divisors.card : ℕ) : ℝ)
                * (g : ℝ) ^ (-(23 / 12 : ℝ))) := by
            refine Finset.sum_le_sum (fun g _ => ?_)
            have h := Work.FIArea7.P231.card_divisors_mul_le c (g ^ 2)
            have h1 : ((((c * g ^ 2).divisors.card : ℕ) : ℝ))
                ≤ (((c.divisors.card : ℕ) : ℝ)) * ((((g ^ 2).divisors.card : ℕ) : ℝ)) := by
              exact_mod_cast h
            have h2 : (0 : ℝ) ≤ (g : ℝ) ^ (-(23 / 12 : ℝ)) := by positivity
            calc ((((c * g ^ 2).divisors.card : ℕ) : ℝ)) * (g : ℝ) ^ (-(23 / 12 : ℝ))
                ≤ ((((c.divisors.card : ℕ) : ℝ)) * ((((g ^ 2).divisors.card : ℕ) : ℝ)))
                    * (g : ℝ) ^ (-(23 / 12 : ℝ)) := mul_le_mul_of_nonneg_right h1 h2
              _ = (((c.divisors.card : ℕ) : ℝ)) * ((((g ^ 2).divisors.card : ℕ) : ℝ)
                    * (g : ℝ) ^ (-(23 / 12 : ℝ))) := by ring
        _ = (((c.divisors.card : ℕ) : ℝ)) * (∑ g ∈ Finset.Icc 1 (min M N),
              (((g ^ 2).divisors.card : ℕ) : ℝ) * (g : ℝ) ^ (-(23 / 12 : ℝ))) := by
            rw [Finset.mul_sum]
        _ ≤ (((c.divisors.card : ℕ) : ℝ)) * K :=
            mul_le_mul_of_nonneg_left (hK (min M N)) (by positivity)
        _ = K * τc := by rw [hτc]; ring
    have hsum4 : C₁ * (K * τc) * (A * B * Lb ^ ε)
        ≤ (C₁ * max 1 K) * τc * (A * B * Lb ^ ε) := by
      have h2 : K ≤ max 1 K := le_max_right _ _
      have h3 : C₁ * K ≤ C₁ * max 1 K := mul_le_mul_of_nonneg_left h2 (le_of_lt hC₁)
      have h5 : (0 : ℝ) ≤ τc * (A * B * Lb ^ ε) := by positivity
      calc C₁ * (K * τc) * (A * B * Lb ^ ε)
          = (C₁ * K) * (τc * (A * B * Lb ^ ε)) := by ring
        _ ≤ (C₁ * max 1 K) * (τc * (A * B * Lb ^ ε)) :=
            mul_le_mul_of_nonneg_right h3 h5
        _ = (C₁ * max 1 K) * τc * (A * B * Lb ^ ε) := by ring
    calc ‖∑ g ∈ Finset.Icc 1 (min M N),
          Work.FIArea7.LBilinStar (M / g) (N / g) (c * g ^ 2) ψ
            (fun a => α (g * a)) (fun b => β (g * b))‖
        ≤ ∑ g ∈ Finset.Icc 1 (min M N),
            C₁ * ((((c * g ^ 2).divisors.card : ℕ) : ℝ)) * (g : ℝ) ^ (-(23 / 12 : ℝ))
              * (A * B * Lb ^ ε) := hsum1
      _ = C₁ * (∑ g ∈ Finset.Icc 1 (min M N),
            ((((c * g ^ 2).divisors.card : ℕ) : ℝ)) * (g : ℝ) ^ (-(23 / 12 : ℝ)))
            * (A * B * Lb ^ ε) := hsum2
      _ ≤ C₁ * (K * τc) * (A * B * Lb ^ ε) := hsum3
      _ ≤ (C₁ * max 1 K) * τc * (A * B * Lb ^ ε) := hsum4
      _ = (C₁ * max 1 K) * (((c.divisors.card : ℕ) : ℝ)) * ((M : ℝ) + (N : ℝ)) ^ ((1 : ℝ) / 12)
            * ((M : ℝ) * (N : ℝ)) ^ ((11 : ℝ) / 12)
            * (((M : ℝ) * (N : ℝ) + (c : ℝ) + 2) ^ ε) := by
          rw [hτc, hA, hB, hLb]
          ring
  · -- `L*(M,N)`
    have hb := hbound M N c k χ α β hc hM hN hχ hχmul hα hβ
    rw [← hτc, ← hA, ← hB, ← hLb] at hb
    refine hb.trans ?_
    have h2 : C₁ * τc * A * B * Lb ^ min (ε / 3) (1 / 4)
        ≤ C₁ * max 1 K * τc * A * B * Lb ^ ε := by
      have hloss : Lb ^ min (ε / 3) (1 / 4) ≤ Lb ^ ε :=
        Real.rpow_le_rpow_of_exponent_le hbase hε1le
      have hcoef : C₁ ≤ C₁ * max 1 K := hC1max
      have hmax0 : (0 : ℝ) < max 1 K := lt_of_lt_of_le zero_lt_one (le_max_left 1 K)
      have h3 : (0 : ℝ) ≤ τc * A * B := by positivity
      have h4 : τc * A * B * Lb ^ min (ε / 3) (1 / 4) ≤ τc * A * B * Lb ^ ε :=
        mul_le_mul_of_nonneg_left hloss h3
      have h5 : C₁ * (τc * A * B * Lb ^ min (ε / 3) (1 / 4))
          ≤ (C₁ * max 1 K) * (τc * A * B * Lb ^ ε) :=
        mul_le_mul hcoef h4 (by positivity) (le_of_lt (mul_pos hC₁ hmax0))
      calc C₁ * τc * A * B * Lb ^ min (ε / 3) (1 / 4)
          = C₁ * (τc * A * B * Lb ^ min (ε / 3) (1 / 4)) := by ring
        _ ≤ (C₁ * max 1 K) * (τc * A * B * Lb ^ ε) := h5
        _ = C₁ * max 1 K * τc * A * B * Lb ^ ε := by ring
    refine h2.trans (le_of_eq ?_)
    rw [hτc, hA, hB, hLb]

end

end Work.FIArea7.P231M
