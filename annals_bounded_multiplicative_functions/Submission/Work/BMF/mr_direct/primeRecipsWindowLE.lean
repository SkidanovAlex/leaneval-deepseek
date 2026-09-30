import Mathlib
import Submission.Work.BMF.Defs
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog
import Submission.Work.BMF.mr_direct.loglog_div_le
import Submission.Work.BMF.mr_direct.le_max_one_mul
import Submission.Work.BMF.mr_direct.primesIn_small_sum_le
import Submission.Work.BMF.mr_direct.primesIn_sum_le_split
import Submission.Work.BMF.mr_direct.small_case_arith
import Submission.Work.BMF.mr_direct.small_case_arith_le_eleven

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open Finset

/-- The cumulative prime reciprocal sum `∑_{p ≤ x} 1/p`, as a function of the real cut-off `x`. -/
private noncomputable def cumPrime (x : ℝ) : ℝ :=
  ∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / (p : ℝ)

/-- For a nonnegative summand, the sum over a union is at most the sum of the two sums. -/
private lemma sum_union_le_of_nonneg' {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have hun : s ∪ t = s ∪ (t \ s) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  rw [hun, Finset.sum_union Finset.disjoint_sdiff]
  have h2 : ∑ x ∈ t \ s, f x ≤ ∑ x ∈ t, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun i _ _ => hf i)
  linarith

/-- Two-endpoint comparison for the prime reciprocal sum over a window `[A,B]`, `2 ≤ A ≤ B`:
the window sum plus a single term `1/A` dominates what is left after deleting the primes `≤ ⌊A⌋₊`
from the primes `≤ ⌊B⌋₊`.  Every prime of `[A,B]` that is not `> ⌊A⌋₊` must equal `⌈A⌉₊`. -/
private lemma primesIn_sum_le_cumdiff (A B : ℝ) (hA : 2 ≤ A) (hAB : A ≤ B) :
    (∑ p ∈ Work.BMF.primesIn A B, (1 : ℝ) / (p : ℝ)) ≤ cumPrime B - cumPrime A + 1 / A := by
  have hA0 : (0 : ℝ) < A := by linarith
  have hnAB : ⌊A⌋₊ ≤ ⌊B⌋₊ := Nat.floor_mono hAB
  have hsub : Nat.primesLE ⌊A⌋₊ ⊆ Nat.primesLE ⌊B⌋₊ := Nat.primesLE_mono hnAB
  have hsd : ∑ p ∈ (Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊), (1 : ℝ) / (p : ℝ)
      = cumPrime B - cumPrime A := by
    have h := Finset.sum_sdiff (f := fun p : ℕ => (1 : ℝ) / (p : ℝ)) hsub
    unfold cumPrime
    linarith
  have hsubset : Work.BMF.primesIn A B ⊆ (Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊) ∪ {⌈A⌉₊} := by
    intro p hp
    rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc] at hp
    obtain ⟨⟨hlo, hhi⟩, hprime⟩ := hp
    rw [Finset.mem_union, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE,
      Finset.mem_singleton]
    by_cases hcase : p ≤ ⌊A⌋₊
    · exact Or.inr (le_antisymm (le_trans hcase (Nat.floor_le_ceil A)) hlo)
    · exact Or.inl ⟨⟨hhi, hprime⟩, fun h => hcase h.1⟩
  have hle1 : (∑ p ∈ Work.BMF.primesIn A B, (1:ℝ)/(p:ℝ))
      ≤ ∑ p ∈ ((Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊) ∪ {⌈A⌉₊}), (1:ℝ)/(p:ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _ _ => div_nonneg zero_le_one (Nat.cast_nonneg i))
  have hle2 : (∑ p ∈ ((Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊) ∪ {⌈A⌉₊}), (1:ℝ)/(p:ℝ))
      ≤ (∑ p ∈ (Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊), (1:ℝ)/(p:ℝ))
        + ∑ p ∈ ({⌈A⌉₊} : Finset ℕ), (1:ℝ)/(p:ℝ) :=
    sum_union_le_of_nonneg' (Nat.primesLE ⌊B⌋₊ \ Nat.primesLE ⌊A⌋₊) ({⌈A⌉₊} : Finset ℕ)
      (fun p : ℕ => (1:ℝ)/(p:ℝ)) (fun p => div_nonneg zero_le_one (Nat.cast_nonneg p))
  have hle3 : (∑ p ∈ ({⌈A⌉₊} : Finset ℕ), (1:ℝ)/(p:ℝ)) ≤ 1 / A := by
    rw [Finset.sum_singleton]
    exact one_div_le_one_div_of_le hA0 (Nat.le_ceil A)
  linarith

/-- The main range `11 ≤ A ≤ B`: subtracting the two endpoint estimates of
`Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog` (with exponent `1`) and using
`log (log B / log A) ≤ log (B/A) / log A` gives
`∑_{p ∈ [A,B]} 1/p ≤ max 1 (2C+1) · (log (B/A)/log A + 1/log A)`. -/
private lemma window_le_main (L C : ℝ) (hCpos : 0 < C) (C1 : ℝ) (hC1 : C1 = max 1 (2 * C + 1))
    (hasy : ∀ x : ℝ, 11 ≤ x → |cumPrime x - Real.log (Real.log x) - L| ≤ C / Real.log x) :
    ∀ A B : ℝ, 11 ≤ A → A ≤ B →
      (∑ p ∈ Work.BMF.primesIn A B, (1:ℝ)/(p:ℝ))
        ≤ C1 * (Real.log (B/A)/Real.log A + 1/Real.log A) := by
  intro A B hA11 hAB
  have hA2 : (2:ℝ) ≤ A := by linarith
  have hB11 : 11 ≤ B := le_trans hA11 hAB
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hlogAB : Real.log A ≤ Real.log B := Real.log_le_log (by linarith) hAB
  have hwin := primesIn_sum_le_cumdiff A B hA2 hAB
  have hub : cumPrime B ≤ Real.log (Real.log B) + L + C / Real.log B := by
    have h := (abs_le.mp (hasy B hB11)).2
    linarith
  have hlb : Real.log (Real.log A) + L - C / Real.log A ≤ cumPrime A := by
    have h := (abs_le.mp (hasy A hA11)).1
    linarith
  have hCB : C / Real.log B ≤ C / Real.log A :=
    div_le_div_of_nonneg_left hCpos.le hlogA hlogAB
  have hAinv : 1 / A ≤ 1 / Real.log A :=
    one_div_le_one_div_of_le hlogA (Real.log_le_self (by linarith))
  have hll : Real.log (Real.log B) - Real.log (Real.log A) ≤ Real.log (B/A) / Real.log A := by
    rw [(Real.log_div hlogB.ne' hlogA.ne').symm]
    exact loglog_div_le A B hA2 hAB
  have hextra : C / Real.log B + C / Real.log A + 1 / A ≤ (2 * C + 1) * (1 / Real.log A) := by
    have hid : C / Real.log A + C / Real.log A + 1 / Real.log A
        = (2 * C + 1) * (1 / Real.log A) := by ring
    linarith
  have hW : (∑ p ∈ Work.BMF.primesIn A B, (1:ℝ)/(p:ℝ))
      ≤ Real.log (B/A)/Real.log A + (2*C + 1) * (1/Real.log A) := by
    linarith
  have hX : 0 ≤ Real.log (B / A) / Real.log A := by
    apply div_nonneg _ hlogA.le
    apply Real.log_nonneg
    rw [le_div_iff₀ (by linarith : (0:ℝ) < A)]
    linarith
  have hY : 0 ≤ 1 / Real.log A := by positivity
  have hK : 0 ≤ 2 * C + 1 := by linarith
  have hm := le_max_one_mul (2*C+1) (Real.log (B/A)/Real.log A) (1/Real.log A) hK hX hY
  rw [← hC1] at hm
  linarith

/-- Window form of Mertens' second theorem: import
`Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog`, which gives
`|∑_{p ≤ x} 1/p − log log x − L| ≤ C (log x)^{-A}` for every `A > 0`, and subtract the two
endpoints; then use `log(log B / log A) ≤ log(B/A)/log A`. -/
theorem primeRecipsWindowLE :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : ℝ, 2 ≤ A → A ≤ B →
      (∑ p ∈ Work.BMF.primesIn A B, (1 : ℝ) / (p : ℝ))
        ≤ C * (Real.log (B / A) / Real.log A + 1 / Real.log A) := by
  obtain ⟨L, C, hCpos, hC⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_powLog 1
    (by norm_num)
  have hasy : ∀ x : ℝ, 11 ≤ x → |cumPrime x - Real.log (Real.log x) - L| ≤ C / Real.log x := by
    intro x hx
    have h := hC x hx
    rwa [Real.rpow_one] at h
  set C1 : ℝ := max 1 (2 * C + 1) with hC1def
  have hC1nonneg : 0 ≤ C1 := le_trans zero_le_one (le_max_left _ _)
  refine ⟨C1 + 20, by linarith, ?_⟩
  intro A B hA2 hAB
  have hmain := window_le_main L C hCpos C1 hC1def hasy
  by_cases hA11 : 11 ≤ A
  · have h' := hmain A B hA11 hAB
    have hbracket : 0 ≤ Real.log (B/A)/Real.log A + 1/Real.log A := by
      have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
      have hX : 0 ≤ Real.log (B/A)/Real.log A := by
        apply div_nonneg _ hlogA.le
        apply Real.log_nonneg
        rw [le_div_iff₀ (by linarith : (0:ℝ) < A)]; linarith
      have hY : 0 ≤ 1/Real.log A := by positivity
      linarith
    calc (∑ p ∈ Work.BMF.primesIn A B, (1:ℝ)/(p:ℝ))
        ≤ C1 * (Real.log (B/A)/Real.log A + 1/Real.log A) := h'
      _ ≤ (C1 + 20) * (Real.log (B/A)/Real.log A + 1/Real.log A) := by
          apply mul_le_mul_of_nonneg_right _ hbracket
          linarith
  · push_neg at hA11
    have hA11' : A ≤ 11 := le_of_lt hA11
    by_cases hB11 : 11 ≤ B
    · have hsplitAB := primesIn_sum_le_split A B
      have h1 : (∑ p ∈ Work.BMF.primesIn A (min B 11), (1:ℝ)/(p:ℝ)) ≤ 3/2 :=
        primesIn_small_sum_le A (min B 11) hA2 (min_le_right _ _)
      have h2 : (∑ p ∈ Work.BMF.primesIn 11 B, (1:ℝ)/(p:ℝ))
          ≤ C1 * (Real.log (B/11)/Real.log 11 + 1/Real.log 11) := hmain 11 B le_rfl hB11
      have harith := small_case_arith A B C1 hA2 hA11' hB11 hC1nonneg
      linarith
    · push_neg at hB11
      have hsmallAB := primesIn_small_sum_le A B hA2 (le_of_lt hB11)
      have harith := small_case_arith_le_eleven A B C1 hA2 hAB hA11' hC1nonneg
      linarith

end Work.BMF.mr_direct
