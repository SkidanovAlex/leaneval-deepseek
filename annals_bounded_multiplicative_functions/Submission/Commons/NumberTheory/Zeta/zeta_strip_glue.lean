import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Commons.NumberTheory.Zeta

private lemma rpow_neg_one (n : ℕ) (hn1 : 1 ≤ n) : (n : ℝ) ^ (-1 : ℝ) = 1 / (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1
  calc
    (n : ℝ) ^ (-1 : ℝ) = ((n : ℝ) ^ (1 : ℝ))⁻¹ := by rw [Real.rpow_neg (le_of_lt hnpos)]
    _ = (n : ℝ)⁻¹ := by rw [Real.rpow_one]
    _ = 1 / (n : ℝ) := by field_simp [ne_of_gt hnpos]

private lemma sum_Icc_two_rpow_neg_le (N : ℕ) (p : ℝ) (hN : 2 ≤ N) (hp1 : 1 < p) :
    (∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (-p)) ≤ (1 - (N : ℝ) ^ (1 - p)) / (p - 1) := by
  let f : ℝ → ℝ := fun x : ℝ => x ^ (-p)
  have hantitone : AntitoneOn f (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    dsimp [f]
    have hx0 : 0 < x := by
      have hx1 : (1 : ℝ) ≤ x := by simpa using hx.1
      linarith
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hcomp := AntitoneOn.sum_le_integral_Ico (a := 1) (b := N) (f := f) (by omega : 1 ≤ N) hantitone
  have hconv : (∑ i ∈ Finset.Ico 1 N, f ((i + 1 : ℕ) : ℝ)) =
      (∑ n ∈ Finset.Icc 2 N, f (n : ℝ)) := by
    refine Finset.sum_bij (s := Finset.Ico 1 N) (t := Finset.Icc 2 N)
      (fun i _ => i + 1) ?_ ?_ ?_ ?_
    · intro i hi
      have hi' : 1 ≤ i ∧ i < N := (Finset.mem_Ico.mp hi)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro a ha b hb h
      omega
    · intro n hn
      have hn' : 2 ≤ n ∧ n ≤ N := (Finset.mem_Icc.mp hn)
      refine ⟨n - 1, ?_, ?_⟩
      · exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · omega
    · intro i hi
      rfl
  rw [← hconv]
  have hnotmem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) ((N : ℕ) : ℝ) := by
    intro hz
    have hle : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    rcases (Set.mem_uIcc.mp hz) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
  have hne : -p ≠ -1 := by linarith
  have hint := integral_rpow (r := -p) (a := (1 : ℝ)) (b := ((N : ℕ) : ℝ))
      (Or.inr ⟨hne, hnotmem⟩)
  have hcalc1 : ∫ x in (1 : ℝ)..((N : ℕ) : ℝ), x ^ (-p)
      = (((N : ℕ) : ℝ) ^ (1 - p) - (1 : ℝ) ^ (1 - p)) / (1 - p) := by
    have hrew : -p + 1 = 1 - p := by ring
    rw [← hrew, hint]
  have hone : (1 : ℝ) ^ (1 - p) = 1 := Real.one_rpow _
  have hcalc2 : (((N : ℕ) : ℝ) ^ (1 - p) - (1 : ℝ) ^ (1 - p)) / (1 - p)
      = (1 - ((N : ℕ) : ℝ) ^ (1 - p)) / (p - 1) := by
    rw [hone]
    have hp1' : 1 - p ≠ 0 := by linarith
    have hpne : p - 1 ≠ 0 := by linarith
    field_simp [hp1', hpne]
    ring
  calc
    (∑ i ∈ Finset.Ico 1 N, f ((i + 1 : ℕ) : ℝ)) ≤ ∫ x in (1 : ℝ)..((N : ℕ) : ℝ), x ^ (-p) := by
      simpa [f] using hcomp
    _ = (((N : ℕ) : ℝ) ^ (1 - p) - (1 : ℝ) ^ (1 - p)) / (1 - p) := hcalc1
    _ = (1 - ((N : ℕ) : ℝ) ^ (1 - p)) / (p - 1) := hcalc2

private lemma sum_Icc_split_one (N : ℕ) (hN : 1 ≤ N) (g : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, g n) = g 1 + (∑ n ∈ Finset.Icc 2 N, g n) := by
  classical
  have hnot : (1 : ℕ) ∉ Finset.Icc 2 N := by simp
  calc
    (∑ n ∈ Finset.Icc 1 N, g n) = (∑ n ∈ insert 1 (Finset.Icc 2 N), g n) := by
      apply Finset.sum_congr
      · ext n
        constructor
        · intro hn
          have hn' := (Finset.mem_Icc.mp hn)
          rw [Finset.mem_insert]
          by_cases hn1 : n = 1
          · exact Or.inl hn1
          · exact Or.inr (Finset.mem_Icc.mpr ⟨by omega, hn'.2⟩)
        · intro hn
          rw [Finset.mem_insert] at hn
          rcases hn with h1 | h2
          · rw [h1]
            exact Finset.mem_Icc.mpr ⟨by norm_num, hN⟩
          · exact Finset.mem_Icc.mpr ⟨le_trans (by norm_num : 1 ≤ (2 : ℕ)) (Finset.mem_Icc.mp h2).1, (Finset.mem_Icc.mp h2).2⟩
      · intro n hn
        rfl
    _ = g 1 + (∑ n ∈ Finset.Icc 2 N, g n) := by
      rw [Finset.sum_insert hnot]

private lemma partial_sum_le_low (δ : ℝ) (N : ℕ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hN : 4 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ))) ≤ 4 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hr0 : 0 ≤ 1 / 2 - δ := by linarith
  have hq0 : 0 ≤ 1 / 2 - δ / 2 := by linarith
  have hd2pos : 0 < δ / 2 := by linarith
  have hNnonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
  have hdne : δ ≠ 0 := ne_of_gt hδ0
  have hterm : ∀ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ)) ≤ (1 / (n : ℝ)) * (N : ℝ) ^ (1 / 2 - δ) := by
    intro n hn
    have hn1n : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn1n
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    calc
      (n : ℝ) ^ (-(1 / 2 + δ)) = (n : ℝ) ^ (-1 + (1 / 2 - δ)) := by
        congr 1
        ring
      _ = (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (1 / 2 - δ) := by
        rw [Real.rpow_add hnpos]
      _ = (1 / (n : ℝ)) * (n : ℝ) ^ (1 / 2 - δ) := by
        rw [rpow_neg_one n hn1n]
      _ ≤ (1 / (n : ℝ)) * (N : ℝ) ^ (1 / 2 - δ) := by
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (n : ℝ)) hnN hr0) (by positivity)
  have hsum1 : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ))) ≤
      (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) * (N : ℝ) ^ (1 / 2 - δ)) := by
    exact Finset.sum_le_sum hterm
  have hsum2 : (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) * (N : ℝ) ^ (1 / 2 - δ)) =
      (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ))) * (N : ℝ) ^ (1 / 2 - δ) := by
    rw [Finset.sum_mul]
  have hharm : (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ))) ≤ 1 + Real.log (N : ℝ) := by
    have h_eq : (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)) = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Rat.cast_inv, Rat.cast_natCast, one_div]
    rw [h_eq]
    exact _root_.harmonic_le_one_add_log N
  have hlog : Real.log (N : ℝ) ≤ (N : ℝ) ^ (δ / 2) / (δ / 2) := by
    exact Real.log_le_rpow_div hNnonneg hd2pos
  have hNpow : (1 : ℝ) ≤ (N : ℝ) ^ (δ / 2) := Real.one_le_rpow (by exact_mod_cast hN1) (by linarith : 0 ≤ δ / 2)
  have h2dpos : 0 < 2 / δ := by positivity
  have h2d4 : 4 ≤ 2 / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith
  have hBN : 2 / δ ≤ (2 / δ) * (N : ℝ) ^ (δ / 2) := by
    simpa using (mul_le_mul_of_nonneg_left hNpow (le_of_lt h2dpos) : (2 / δ) * 1 ≤ (2 / δ) * (N : ℝ) ^ (δ / 2))
  have hB1 : 1 ≤ 2 * (N : ℝ) ^ (δ / 2) / δ := by
    have hB : (2 / δ) * (N : ℝ) ^ (δ / 2) = 2 * (N : ℝ) ^ (δ / 2) / δ := by ring
    rw [← hB]
    linarith
  have hlogA : Real.log (N : ℝ) ≤ 2 * (N : ℝ) ^ (δ / 2) / δ := by
    have : (N : ℝ) ^ (δ / 2) / (δ / 2) = 2 * (N : ℝ) ^ (δ / 2) / δ := by
      field_simp [hdne]
    rw [this] at hlog
    exact hlog
  have h1log : 1 + Real.log (N : ℝ) ≤ 4 * (N : ℝ) ^ (δ / 2) / δ := by
    have hB : 2 * (2 * (N : ℝ) ^ (δ / 2) / δ) = 4 * (N : ℝ) ^ (δ / 2) / δ := by ring
    linarith
  have hS2 : (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ))) * (N : ℝ) ^ (1 / 2 - δ) ≤
      (1 + Real.log (N : ℝ)) * (N : ℝ) ^ (1 / 2 - δ) := by
    exact mul_le_mul_of_nonneg_right hharm (Real.rpow_nonneg hNnonneg _)
  have hstep : (1 + Real.log (N : ℝ)) * (N : ℝ) ^ (1 / 2 - δ) ≤
      (4 * (N : ℝ) ^ (δ / 2) / δ) * (N : ℝ) ^ (1 / 2 - δ) := by
    exact mul_le_mul_of_nonneg_right h1log (Real.rpow_nonneg hNnonneg _)
  have hcomb : (4 * (N : ℝ) ^ (δ / 2) / δ) * (N : ℝ) ^ (1 / 2 - δ) =
      (4 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by
    rw [show 4 * (N : ℝ) ^ (δ / 2) / δ * (N : ℝ) ^ (1 / 2 - δ) =
        (4 / δ) * ((N : ℝ) ^ (δ / 2) * (N : ℝ) ^ (1 / 2 - δ)) by ring]
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hle : (4 / δ) ≤ 4 * (1 + 1 / δ) := by
    have h : (1 / δ : ℝ) ≤ 1 + 1 / δ := by linarith
    calc
      (4 / δ) = 4 * (1 / δ) := by ring
      _ ≤ 4 * (1 + 1 / δ) := by exact mul_le_mul_of_nonneg_left h (by norm_num)
  have hfin : (4 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) ≤ 4 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by
    exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hNnonneg _)
  nlinarith

private lemma partial_sum_le_mid (δ : ℝ) (N : ℕ) (hδ0 : 0 < δ) (hδlo : 1 / 2 ≤ δ) (hδhi : δ ≤ 3 / 4) (hN : 4 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ))) ≤ 9 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by
  have hN1 : 1 ≤ N := by omega
  have hNnonneg : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hq : 0 < 1 / 2 - δ / 2 := by linarith
  have hterm : ∀ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ)) ≤ 1 / (n : ℝ) := by
    intro n hn
    have hn1n : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1n
    have hexp : -(1 / 2 + δ) ≤ (-1 : ℝ) := by linarith
    calc
      (n : ℝ) ^ (-(1 / 2 + δ)) ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hnR1 hexp
      _ = 1 / (n : ℝ) := rpow_neg_one n hn1n
  have hSleH : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ))) ≤
      (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)) := by
    exact Finset.sum_le_sum hterm
  have hH : (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
    have h_eq : (∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ)) = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Rat.cast_inv, Rat.cast_natCast, one_div]
    rw [h_eq]
    exact _root_.harmonic_le_one_add_log N
  have hlog : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 2 - δ / 2) / (1 / 2 - δ / 2) :=
    Real.log_le_rpow_div hNnonneg hq
  have hqinv : 1 / (1 / 2 - δ / 2) ≤ 8 := by
    rw [div_le_iff₀ hq]
    nlinarith
  have hqposn : 0 ≤ (N : ℝ) ^ (1 / 2 - δ / 2) := Real.rpow_nonneg hNnonneg _
  have hS : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ))) ≤ 9 * (N : ℝ) ^ (1 / 2 - δ / 2) := by
    have hNq1 : 1 ≤ (N : ℝ) ^ (1 / 2 - δ / 2) := Real.one_le_rpow (by exact_mod_cast hN1) (by linarith : 0 ≤ 1 / 2 - δ / 2)
    calc
      (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ))) ≤ 1 + Real.log (N : ℝ) := le_trans hSleH hH
      _ ≤ 1 + (N : ℝ) ^ (1 / 2 - δ / 2) / (1 / 2 - δ / 2) := by linarith
      _ = 1 + (1 / (1 / 2 - δ / 2)) * (N : ℝ) ^ (1 / 2 - δ / 2) := by ring
      _ ≤ 1 + 8 * (N : ℝ) ^ (1 / 2 - δ / 2) := by
        have hm := mul_le_mul_of_nonneg_right hqinv hqposn
        linarith
      _ ≤ 9 * (N : ℝ) ^ (1 / 2 - δ / 2) := by linarith
  calc
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ))) ≤ 9 * (N : ℝ) ^ (1 / 2 - δ / 2) := hS
    _ ≤ 9 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by
      have h1δ : 1 ≤ 1 + 1 / δ := by
        have : 0 ≤ 1 / δ := by positivity
        linarith
      nlinarith

private lemma partial_sum_le_hi (δ : ℝ) (N : ℕ) (hδ0 : 0 < δ) (hδlo : 3 / 4 ≤ δ) (hδhi : δ ≤ 1) (hN : 4 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ))) ≤ 5 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  let p : ℝ := 1 / 2 + δ
  have hp1 : 1 < p := by dsimp [p]; linarith
  have hT : (∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (-p)) ≤ (1 - (N : ℝ) ^ (1 - p)) / (p - 1) := by
    simpa [p] using sum_Icc_two_rpow_neg_le N (1 / 2 + δ) hN2 hp1
  have hTle : (1 - (N : ℝ) ^ (1 - p)) / (p - 1) ≤ 1 / (p - 1) := by
    have hppos : 0 < p - 1 := by linarith
    have hx : 0 ≤ (N : ℝ) ^ (1 - p) := by positivity
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hppos)
  have hp1ge : 1 / 4 ≤ p - 1 := by dsimp [p]; linarith
  have hp1le : 1 / (p - 1) ≤ 4 := by
    rw [div_le_iff₀ (by linarith : 0 < p - 1)]
    nlinarith
  have hTle4 : (∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (-p)) ≤ 4 := by
    exact le_trans (le_trans hT hTle) hp1le
  have hmain : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ))) ≤ 5 := by
    calc
      (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ)))
          = ((1 : ℕ) : ℝ) ^ (-(1 / 2 + δ)) + (∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (-(1 / 2 + δ))) := by
              rw [sum_Icc_split_one N hN1]
      _ = 1 + (∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (-(1 / 2 + δ))) := by
              have hg1 : ((1 : ℕ) : ℝ) ^ (-(1 / 2 + δ)) = 1 := by
                simpa using (Real.one_rpow (-(1 / 2 + δ)))
              rw [hg1]
      _ = 1 + (∑ n ∈ Finset.Icc 2 N, (n : ℝ) ^ (-p)) := by rfl
      _ ≤ 5 := by linarith
  have h1δ : 1 ≤ 1 + 1 / δ := by
    have : 0 ≤ 1 / δ := by positivity
    linarith
  have hNq1 : 1 ≤ (N : ℝ) ^ (1 / 2 - δ / 2) := by
    exact Real.one_le_rpow (by exact_mod_cast hN1) (by linarith : 0 ≤ 1 / 2 - δ / 2)
  nlinarith

private lemma partial_sum_le (δ : ℝ) (N : ℕ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 4 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ))) ≤ 16 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by
  have hqnonneg : 0 ≤ (N : ℝ) ^ (1 / 2 - δ / 2) := by positivity
  have h1δ : 1 ≤ 1 + 1 / δ := by
    have : 0 ≤ 1 / δ := by positivity
    linarith
  by_cases hA : δ ≤ 1 / 2
  · have hB := partial_sum_le_low δ N hδ0 hA hN
    have hC : 4 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) ≤
        16 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by
      have h41 : 4 ≤ 16 := by norm_num
      have hprod : 0 ≤ (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by positivity
      nlinarith
    exact le_trans hB hC
  · have hδgt : 1 / 2 < δ := by linarith
    by_cases hB : δ ≤ 3 / 4
    · have hC := partial_sum_le_mid δ N hδ0 (le_of_lt hδgt) hB hN
      have hD : 9 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) ≤
          16 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by
        have hprod : 0 ≤ (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by positivity
        nlinarith
      exact le_trans hC hD
    · have hδgt3 : 3 / 4 < δ := by linarith
      have hC := partial_sum_le_hi δ N hδ0 (le_of_lt hδgt3) hδ1 hN
      have hD : 5 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) ≤
          16 * (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by
        have hprod : 0 ≤ (1 + 1 / δ) * (N : ℝ) ^ (1 / 2 - δ / 2) := by positivity
        nlinarith
      exact le_trans hC hD


private lemma tail_le (δ σ : ℝ) (N : ℕ) (hδ0 : 0 < δ) (hσlo : (1 / 2 + δ) ≤ σ) (hN1 : 1 ≤ N) :
    (1 + 1 / σ) * (N : ℝ) ^ (1 - σ) ≤ 3 * (N : ℝ) ^ (1 / 2 - δ / 2) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN1
  have hNnonneg : 0 ≤ (N : ℝ) := le_of_lt hNpos
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hσpos : 0 < σ := by linarith
  have hσ0pos : 0 < 1 / 2 + δ := by linarith
  have hrec : 1 / σ ≤ 1 / (1 / 2 + δ) := by
    rw [div_le_div_iff₀ hσpos hσ0pos]
    linarith
  have hσ0inv : 1 / (1 / 2 + δ) ≤ 2 := by
    rw [div_le_iff₀ hσ0pos]
    nlinarith
  have h13 : 1 + 1 / σ ≤ 3 := by linarith
  have hexp1 : 1 - σ ≤ 1 / 2 - δ := by linarith
  have hexp2 : 1 / 2 - δ ≤ 1 / 2 - δ / 2 := by linarith
  have hNp1 : (N : ℝ) ^ (1 - σ) ≤ (N : ℝ) ^ (1 / 2 - δ) :=
    Real.rpow_le_rpow_of_exponent_le hN1R hexp1
  have hNp2 : (N : ℝ) ^ (1 / 2 - δ) ≤ (N : ℝ) ^ (1 / 2 - δ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hN1R hexp2
  calc
    (1 + 1 / σ) * (N : ℝ) ^ (1 - σ) ≤ 3 * (N : ℝ) ^ (1 - σ) := by
      exact mul_le_mul_of_nonneg_right h13 (Real.rpow_nonneg hNnonneg _)
    _ ≤ 3 * (N : ℝ) ^ (1 / 2 - δ / 2) := by
      exact mul_le_mul_of_nonneg_left (le_trans hNp1 hNp2) (by norm_num)

private lemma Npow_le_Mpow (M : ℝ) (N : ℕ) (q : ℝ) (hM4 : 4 ≤ M) (hNle : (N : ℝ) ≤ M + 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (N : ℝ) ^ q ≤ (5 / 4) * M ^ q := by
  have hN54 : (N : ℝ) ≤ (5 / 4) * M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have h54q : (5 / 4 : ℝ) ^ q ≤ 5 / 4 := by
    have h54 : 1 ≤ (5 / 4 : ℝ) := by norm_num
    have hp := Real.rpow_le_rpow_of_exponent_le h54 hq1
    rwa [Real.rpow_one] at hp
  calc
    (N : ℝ) ^ q ≤ ((5 / 4) * M) ^ q := Real.rpow_le_rpow hN0 hN54 hq0
    _ = (5 / 4 : ℝ) ^ q * M ^ q := Real.mul_rpow (by norm_num) hM0
    _ ≤ (5 / 4) * M ^ q := by
      exact mul_le_mul_of_nonneg_right h54q (Real.rpow_nonneg hM0 _)

theorem zeta_strip_glue (δ σ t : ℝ) (N : ℕ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hσlo : (1 / 2 + δ) ≤ σ) (hσhi : σ ≤ 2) (ht : 1 ≤ |t|)
    (hNge : |t| + 3 ≤ (N : ℝ)) (hNle : (N : ℝ) ≤ |t| + 4) :
    (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ) ^ (-σ)) + (1 + 1 / σ) * ((N : ℝ) ^ (1 - σ)) ≤
      1000000 * (1 + 1 / δ) * (|t| + 3) ^ (1 / 2 - δ / 2) := by
  let M : ℝ := |t| + 3
  let q : ℝ := 1 / 2 - δ / 2
  have hN1n : 1 ≤ N := by
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast h1N
  have hN4n : 4 ≤ N := by
    have h4N : (4 : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast h4N
  have hM4 : 4 ≤ M := by dsimp [M]; linarith
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have h1δ : 1 ≤ 1 + 1 / δ := by
    have : 0 ≤ 1 / δ := by positivity
    linarith
  have hδinv0 : 0 ≤ 1 / δ := by positivity
  -- sum bound
  have hsum : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)) ≤
      16 * (1 + 1 / δ) * (N : ℝ) ^ q := by
    have h1 := partial_sum_le δ N hδ0 hδ1 hN4n
    have h2 : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)) ≤
        (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 / 2 + δ))) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hexp : -σ ≤ -(1 / 2 + δ) := by linarith
      exact Real.rpow_le_rpow_of_exponent_le hn1 hexp
    exact le_trans h2 (by simpa [q] using h1)
  -- tail bound
  have htail : (1 + 1 / σ) * (N : ℝ) ^ (1 - σ) ≤ 3 * (N : ℝ) ^ q := by
    simpa [q] using tail_le δ σ N hδ0 hσlo hN1n
  have htail2 : 3 * (N : ℝ) ^ q ≤ 3 * (1 + 1 / δ) * (N : ℝ) ^ q := by
    have hNq : 0 ≤ (N : ℝ) ^ q := by positivity
    nlinarith
  -- total in N
  have htotN : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)) + (1 + 1 / σ) * (N : ℝ) ^ (1 - σ) ≤
      19 * (1 + 1 / δ) * (N : ℝ) ^ q := by
    nlinarith
  -- N^q to M^q
  have hNleM1 : (N : ℝ) ≤ M + 1 := by
    dsimp [M]
    linarith
  have hpowNM := Npow_le_Mpow M N q hM4 hNleM1 hq0 hq1
  have htotM : 19 * (1 + 1 / δ) * (N : ℝ) ^ q ≤
      (5 / 4) * 19 * (1 + 1 / δ) * M ^ q := by
    have hnonneg : 0 ≤ 19 * (1 + 1 / δ) := by positivity
    calc
      19 * (1 + 1 / δ) * (N : ℝ) ^ q ≤ 19 * (1 + 1 / δ) * ((5 / 4) * M ^ q) := by
        exact mul_le_mul_of_nonneg_left hpowNM (by positivity)
      _ = (5 / 4) * 19 * (1 + 1 / δ) * M ^ q := by ring
  -- final
  have hMq0 : 0 ≤ M ^ q := by positivity
  have hfin : (5 / 4) * 19 * (1 + 1 / δ) * M ^ q ≤
      1000000 * (1 + 1 / δ) * M ^ q := by
    have hc : (5 / 4 : ℝ) * 19 ≤ 1000000 := by norm_num
    nlinarith
  have hgoal : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-σ)) + (1 + 1 / σ) * (N : ℝ) ^ (1 - σ) ≤
      1000000 * (1 + 1 / δ) * M ^ q := by
    exact le_trans (le_trans htotN htotM) hfin
  simpa [M, q] using hgoal
end Commons.NumberTheory.Zeta
