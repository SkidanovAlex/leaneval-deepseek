import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.Setup

namespace Work.HP.NA

open Finset

/-- If `a` is primitive but `f_a` has no primitive zero modulo `p^r`, then `σ(a; p^r) = 0`:
the defining double count of primitive zeroes is empty. -/
lemma sigQ_eq_zero_of_not_FlocSet (d n p r : ℕ) [NeZero (p ^ r)]
    (a : Mon d n → ZMod (p ^ r)) (ha : IsPrimGen (p ^ r) a) (h : ¬ FlocSet d n p r a) :
    sigQ d n (p ^ r) a = 0 := by
  have hset : {b : Fin (n + 1) → ZMod (p ^ r) |
      Ideal.span (Set.range b) = ⊤ ∧ fev d n a b = 0} = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨b, hb, hf⟩
    exact h ⟨ha, b, hb, hf⟩
  unfold sigQ
  rw [hset, Set.ncard_empty]
  simp

/-- The sum over the locally soluble coefficients `F^loc(p^r)` agrees with the sum over all
primitive coefficient vectors modulo `p^r`: a primitive `a` outside `F^loc(p^r)` has no primitive zero,
so `σ(a; p^r) = 0` and its term vanishes. -/
theorem sum_FlocInset_eq_primFinset (d n p r : ℕ) (hn : 1 ≤ n) [NeZero (p ^ r)] :
    (∑ a ∈ Work.HP.NA.FlocInset d n p r, (Work.HP.NA.sigQ d n (p ^ r) a) ^ (-(1 / (4 * (n : ℝ)))))
      = (∑ a ∈ Work.HP.NA.primFinset d n (p ^ r), (Work.HP.NA.sigQ d n (p ^ r) a) ^ (-(1 / (4 * (n : ℝ))))) := by
  classical
  have hFloc : FlocInset d n p r = (primFinset d n (p ^ r)).filter (FlocSet d n p r) := rfl
  rw [hFloc]
  refine Finset.sum_filter_of_ne ?_
  intro a ha hne
  by_contra h
  have hprim : IsPrimGen (p ^ r) a := by simpa [primFinset] using ha
  have hz := sigQ_eq_zero_of_not_FlocSet d n p r a hprim h
  rw [hz] at hne
  have hexp : (-(1 / (4 * (n : ℝ)))) ≠ 0 := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h4 : (0 : ℝ) < 4 * (n : ℝ) := by linarith
    have : (0 : ℝ) < 1 / (4 * (n : ℝ)) := one_div_pos.mpr h4
    linarith
  exact hne (Real.zero_rpow hexp)

end Work.HP.NA
