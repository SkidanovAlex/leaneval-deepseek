import Mathlib
import Submission.Work.FIChain.Defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Divisor-filtered interval reindexing, general form.**  For any weight `K`,
bound `N` and predicate `P`,

`∑_{ℓ ≤ N} (∑_{b | ℓ, P b} μ(b))·K ℓ = ∑_{b ≤ N, P b} μ(b)·∑_{e : be ≤ N} K (be)`.

The proof is the standard double count: the divisors of `ℓ ≤ N` are exactly the
elements of `[1,N]` dividing `ℓ`, which lets the two sums be interchanged, and the
remaining `b ∣ ℓ`-sum over `ℓ ∈ [1,N]` is reindexed by `ℓ = b·e`. -/
lemma sum_divisors_reindex_aux (K : ℕ → ℝ) (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ ℓ ∈ Finset.Icc 1 N,
        (∑ b ∈ ℓ.divisors.filter P, (ArithmeticFunction.moebius b : ℝ)) * K ℓ)
      = ∑ b ∈ (Finset.Icc 1 N).filter P, (ArithmeticFunction.moebius b : ℝ) *
          ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * e ≤ N), K (b * e) := by
  have hdiv : ∀ ℓ ∈ Finset.Icc 1 N,
      ℓ.divisors.filter P = (Finset.Icc 1 N).filter (fun b => b ∣ ℓ ∧ P b) := by
    intro ℓ hℓ
    obtain ⟨hℓ1, hℓN⟩ := Finset.mem_Icc.mp hℓ
    have hℓ0 : ℓ ≠ 0 := by omega
    ext b
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hbd, _⟩, hpb⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hbd (by omega),
        le_trans (Nat.le_of_dvd (by omega) hbd) hℓN⟩, hbd, hpb⟩
    · rintro ⟨⟨hb1, _⟩, hbd, hpb⟩
      exact ⟨⟨hbd, hℓ0⟩, hpb⟩
  calc (∑ ℓ ∈ Finset.Icc 1 N,
          (∑ b ∈ ℓ.divisors.filter P, (ArithmeticFunction.moebius b : ℝ)) * K ℓ)
      = ∑ ℓ ∈ Finset.Icc 1 N,
          ∑ b ∈ (Finset.Icc 1 N).filter (fun b => b ∣ ℓ ∧ P b),
            (ArithmeticFunction.moebius b : ℝ) * K ℓ := by
        apply Finset.sum_congr rfl; intro ℓ hℓ
        rw [hdiv ℓ hℓ, Finset.sum_mul]
    _ = ∑ ℓ ∈ Finset.Icc 1 N,
          ∑ b ∈ Finset.Icc 1 N,
            (if b ∣ ℓ ∧ P b then (ArithmeticFunction.moebius b : ℝ) * K ℓ else 0) := by
        apply Finset.sum_congr rfl; intro ℓ _
        rw [Finset.sum_filter]
    _ = ∑ b ∈ Finset.Icc 1 N,
          ∑ ℓ ∈ Finset.Icc 1 N,
            (if b ∣ ℓ ∧ P b then (ArithmeticFunction.moebius b : ℝ) * K ℓ else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ b ∈ Finset.Icc 1 N,
          (if P b then (ArithmeticFunction.moebius b : ℝ) *
              ∑ ℓ ∈ (Finset.Icc 1 N).filter (fun ℓ => b ∣ ℓ), K ℓ else 0) := by
        apply Finset.sum_congr rfl; intro b _
        by_cases hpb : P b
        · rw [if_pos hpb, Finset.sum_filter, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro ℓ _
          by_cases hbd : b ∣ ℓ <;> simp [hpb, hbd]
        · rw [if_neg hpb]
          apply Finset.sum_eq_zero; intro ℓ _
          simp [hpb]
    _ = ∑ b ∈ (Finset.Icc 1 N).filter P,
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ ℓ ∈ (Finset.Icc 1 N).filter (fun ℓ => b ∣ ℓ), K ℓ := by
        rw [Finset.sum_filter]
    _ = ∑ b ∈ (Finset.Icc 1 N).filter P,
          (ArithmeticFunction.moebius b : ℝ) *
            ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * e ≤ N), K (b * e) := by
        apply Finset.sum_congr rfl; intro b hb
        obtain ⟨hbIcc, _⟩ := Finset.mem_filter.mp hb
        obtain ⟨hb1, _⟩ := Finset.mem_Icc.mp hbIcc
        have hsum : (∑ ℓ ∈ (Finset.Icc 1 N).filter (fun ℓ => b ∣ ℓ), K ℓ)
            = ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * e ≤ N), K (b * e) :=
          Submission.ASP.sum_filter_dvd_eq'' hb1 K
        rw [hsum]

/-- **Un-reindexing the Möbius divisor weight.**  For a weight `F` supported on `[1,N]`,

`∑_{ℓ ≤ N} (∑_{b | ℓ, b > sy} μ(b))·F ℓ = ∑_{b ≤ N, b > sy} μ(b)·∑_{e ≤ N} F (b·e)`.

The left-hand side is the same double sum over pairs with `b ≤ N`, `sy < b`, `b·e ≤ N`
as the right-hand side; the terms with `b·e > N` of the right-hand side vanish by the
support hypothesis `hF`. -/
lemma sum_divisors_reindex (F : ℕ → ℝ) (N : ℕ) (sy : ℝ) (hF : ∀ ℓ, N < ℓ → F ℓ = 0) :
    ∑ ℓ ∈ Finset.Icc 1 N,
        (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ)) * F ℓ
      = ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
          (ArithmeticFunction.moebius b : ℝ) * ∑ e ∈ Finset.Icc 1 N, F (b * e) := by
  rw [sum_divisors_reindex_aux F N (fun b => sy < ((b : ℕ) : ℝ))]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hsum : (∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * e ≤ N), F (b * e))
      = ∑ e ∈ Finset.Icc 1 N, F (b * e) :=
    Finset.sum_filter_of_ne (fun e _ he => by
      by_contra h
      exact he (hF (b * e) (Nat.lt_of_not_le h)))
  rw [hsum]

end

end Work.FIChain
