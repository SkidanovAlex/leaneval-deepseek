import Mathlib
import Submission.Work.BMF.prime_tuple_count

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

open Finset Real
open scoped BigOperators

theorem n4_uniform (ℓ k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) :
    ∃ G B : ℝ, 0 < G ∧ 0 < B ∧
    ∀ (m : ℕ), 1 ≤ m → m ≤ k → ∀ (P N C₀ : ℝ) (q : ℕ),
      B ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) → 1 / Real.log P ≤ C₀ → 1 ≤ q →
      ((((Fintype.piFinset fun _ : Fin ℓ ↦ (Work.BMF.primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ q)) ×ˢ
        (Fintype.piFinset fun _ : Fin ℓ ↦ (Work.BMF.primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ q))).filter
        (fun v ↦ |((∏ i, v.2 i : ℕ) : ℝ) - ((∏ i, v.1 i : ℕ) : ℝ)| ≤ C₀ * P ^ ℓ / N ∧
          (∏ i, v.2 i) ^ m ≡ (∏ i, v.1 i) ^ m [MOD q])).card : ℝ) ≤
        G * C₀ * (P / Real.log P) ^ (2 * ℓ) / N *
          ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) + 1 / Real.log N)
:= by
  classical
  -- For every fixed `m` we have constants `C, P₀` (the proved input `prime_tuple_count`),
  -- but they are allowed to depend on `m`.  Package them below into uniform `G, B`.
  have hkey : ∀ m : ℕ, ∃ C P₀ : ℝ, (1 ≤ m → 0 < C ∧
      ∀ (P N C₀ : ℝ) (q : ℕ), P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) →
        1 / Real.log P ≤ C₀ → 1 ≤ q →
        ((((Fintype.piFinset fun _ : Fin ℓ ↦ (Work.BMF.primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ q)) ×ˢ
          (Fintype.piFinset fun _ : Fin ℓ ↦ (Work.BMF.primesIn P (2 * P)).filter (fun p ↦ ¬ p ∣ q))).filter
          (fun v ↦ |((∏ i, v.2 i : ℕ) : ℝ) - ((∏ i, v.1 i : ℕ) : ℝ)| ≤ C₀ * P ^ ℓ / N ∧
            (∏ i, v.2 i) ^ m ≡ (∏ i, v.1 i) ^ m [MOD q])).card : ℝ) ≤
          C * C₀ * (P / Real.log P) ^ (2 * ℓ) / N *
            ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) + 1 / Real.log N)) := by
    intro m
    by_cases hm : 1 ≤ m
    · obtain ⟨C, P₀, hC, hb⟩ := Work.BMF.prime_tuple_count ℓ m hℓ hm
      exact ⟨C, P₀, fun _ => ⟨hC, fun P N C₀ q hP hN hNle hC₀ hq =>
        (by simpa only [Work.BMF.pi0] using hb P N C₀ q hP hN hNle hC₀ hq)⟩⟩
    · exact ⟨1, 1, fun h => absurd h hm⟩
  choose Cfun P0fun hbody using hkey
  refine ⟨∑ m ∈ Finset.Icc 1 k, Cfun m, max 1 (∑ m ∈ Finset.Icc 1 k, |P0fun m|), ?_, ?_, ?_⟩
  · refine lt_of_lt_of_le (hbody 1 (le_refl 1)).1
      (Finset.single_le_sum (f := Cfun) (fun m hm => le_of_lt (hbody m (Finset.mem_Icc.mp hm).1).1)
        (Finset.mem_Icc.mpr ⟨le_refl 1, hk⟩))
  · exact lt_of_lt_of_le one_pos (le_max_left 1 _)
  · intro m hm1 hmk P N C₀ q hBP hN hNle hC₀ hq
    have hmS : m ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨hm1, hmk⟩
    have hP0le : P0fun m ≤ P := by
      have h1 : P0fun m ≤ |P0fun m| := le_abs_self _
      have h2 : |P0fun m| ≤ ∑ m' ∈ Finset.Icc 1 k, |P0fun m'| :=
        Finset.single_le_sum (f := fun i => |P0fun i|) (fun i _ => abs_nonneg _) hmS
      have h3 : (∑ m' ∈ Finset.Icc 1 k, |P0fun m'|) ≤ max 1 (∑ m' ∈ Finset.Icc 1 k, |P0fun m'|) :=
        le_max_right _ _
      linarith
    have hle' := (hbody m hm1).2 P N C₀ q hP0le hN hNle hC₀ hq
    have hCle : Cfun m ≤ ∑ m' ∈ Finset.Icc 1 k, Cfun m' :=
      Finset.single_le_sum (f := Cfun) (fun i hi => le_of_lt (hbody i (Finset.mem_Icc.mp hi).1).1) hmS
    have hP1 : (1:ℝ) ≤ P := le_trans (le_max_left 1 _) hBP
    have hlognn : 0 ≤ Real.log P := Real.log_nonneg hP1
    have hC₀nn : 0 ≤ C₀ := le_trans (div_nonneg (by norm_num) hlognn) hC₀
    have hXnn : 0 ≤ (P / Real.log P) ^ (2 * ℓ) :=
      pow_nonneg (div_nonneg (by linarith) hlognn) _
    have hNpos : 0 < N := by linarith
    have hBrnn : 0 ≤ ((((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) + 1 / Real.log N) :=
      add_nonneg (div_nonneg (by positivity) (by positivity))
        (div_nonneg (by norm_num) (Real.log_nonneg (by linarith)))
    have s1 : Cfun m * C₀ ≤ (∑ m' ∈ Finset.Icc 1 k, Cfun m') * C₀ :=
      mul_le_mul_of_nonneg_right hCle hC₀nn
    have s2 : Cfun m * C₀ * (P / Real.log P) ^ (2 * ℓ)
        ≤ (∑ m' ∈ Finset.Icc 1 k, Cfun m') * C₀ * (P / Real.log P) ^ (2 * ℓ) :=
      mul_le_mul_of_nonneg_right s1 hXnn
    have s3 : Cfun m * C₀ * (P / Real.log P) ^ (2 * ℓ) / N
        ≤ (∑ m' ∈ Finset.Icc 1 k, Cfun m') * C₀ * (P / Real.log P) ^ (2 * ℓ) / N :=
      div_le_div_of_nonneg_right s2 hNpos.le
    have s4 := mul_le_mul_of_nonneg_right s3 hBrnn
    exact le_trans hle' s4

end Work.N8
