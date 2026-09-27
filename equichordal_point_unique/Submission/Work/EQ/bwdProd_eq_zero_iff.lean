import Mathlib
import Submission.Work.EQ.bwdFanDefs

namespace Work.EQ

/-- **A product of radicands vanishes iff one labelled radicand vanishes.**

`bwdProd a h ε n w` is the product, over all levels `i ≤ n` and all sign lists `σ` of length `i`,
of the labelled radicands `bsq (subO1 a (bwdP a σ (fan a h ε w)))`.  Since `ℂ` has no zero
divisors, this product is zero exactly when one of its factors is, i.e. exactly when some sign
list `σ` of length `≤ n` produces a vanishing labelled radicand. -/
theorem bwdProd_eq_zero_iff {a : ℝ} {h : ℂ → ℂ} (ε : List Bool) (n : ℕ) (w : ℂ) :
    bwdProd a h ε n w = 0 ↔
      ∃ σ : List Bool, σ.length ≤ n ∧ bsq (subO1 a (bwdP a σ (fan a h ε w))) = 0 := by
  unfold bwdProd
  rw [List.prod_eq_zero_iff, List.mem_map]
  constructor
  · rintro ⟨i, hi, hprod⟩
    rw [List.mem_range] at hi
    rw [List.prod_eq_zero_iff, List.mem_map] at hprod
    obtain ⟨σ, hσmem, hσ⟩ := hprod
    refine ⟨σ, ?_, hσ⟩
    rw [mem_fanWords] at hσmem
    omega
  · rintro ⟨σ, hlen, hσ⟩
    refine ⟨σ.length, List.mem_range.mpr (Nat.lt_succ_of_le hlen), ?_⟩
    rw [List.prod_eq_zero_iff, List.mem_map]
    exact ⟨σ, mem_fanWords.mpr rfl, hσ⟩

end Work.EQ
