import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.BernoulliPolynomials

namespace Commons.Algebra.Polynomial.EventuallyPoly

open Finset

noncomputable section

/-- Auxiliary polynomial whose value at `t` is `∑_{s<t} s ^ n`. -/
def powSumPoly (n : ℕ) : _root_.Polynomial ℚ :=
  (_root_.Polynomial.bernoulli (n + 1) - _root_.Polynomial.C (_root_.bernoulli (n + 1))) *
    _root_.Polynomial.C (((n + 1 : ℕ) : ℚ)⁻¹)

lemma powSumPoly_eval (n t : ℕ) :
    (powSumPoly n).eval (t : ℚ) = ∑ s ∈ Finset.range t, (s : ℚ) ^ n := by
  unfold powSumPoly
  rw [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_sub, _root_.Polynomial.eval_C,
    _root_.Polynomial.eval_C, _root_.Polynomial.bernoulli_succ_eval]
  have hne : (((n : ℚ) + 1)) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-- Auxiliary polynomial whose value at `t` is `∑_{s<t} p.eval s`. -/
def sumPoly (p : _root_.Polynomial ℚ) : _root_.Polynomial ℚ :=
  ∑ i ∈ Finset.range (p.natDegree + 1), _root_.Polynomial.C (p.coeff i) * powSumPoly i

lemma sumPoly_eval (p : _root_.Polynomial ℚ) (t : ℕ) :
    (sumPoly p).eval (t : ℚ) = ∑ s ∈ Finset.range t, p.eval (s : ℚ) := by
  have h2 : (sumPoly p).eval (t : ℚ)
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∑ s ∈ Finset.range t, (s : ℚ) ^ i := by
    rw [sumPoly, _root_.Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_C, powSumPoly_eval]
  have h1 : (∑ s ∈ Finset.range t, p.eval (s : ℚ))
      = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∑ s ∈ Finset.range t, (s : ℚ) ^ i := by
    simp_rw [_root_.Polynomial.eval_eq_sum_range]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [h2, ← h1]

end

theorem partialSum {f : ℕ → ℚ}
    (hf : ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ t : ℕ, N ≤ t → f t = p.eval (t : ℚ)) :
    ∃ q : Polynomial ℚ, ∃ M : ℕ, ∀ t : ℕ, M ≤ t →
      (∑ s ∈ Finset.range t, f s) = q.eval (t : ℚ) := by
  obtain ⟨p, N, hfN⟩ := hf
  refine ⟨sumPoly p + Polynomial.C ((∑ s ∈ Finset.range N, f s) - (sumPoly p).eval (N : ℚ)),
    N, ?_⟩
  intro t ht
  rw [Polynomial.eval_add, Polynomial.eval_C]
  have hIcoF : ∑ s ∈ Finset.Ico N t, f s = ∑ s ∈ Finset.Ico N t, p.eval (s : ℚ) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_Ico] at hs
    exact hfN s hs.1
  have hIcoP : ∑ s ∈ Finset.Ico N t, p.eval (s : ℚ)
      = (∑ s ∈ Finset.range t, p.eval (s : ℚ))
        - (∑ s ∈ Finset.range N, p.eval (s : ℚ)) :=
    Finset.sum_Ico_eq_sub _ ht
  calc ∑ s ∈ Finset.range t, f s
      = ∑ s ∈ Finset.range N, f s + ∑ s ∈ Finset.Ico N t, f s := by
        rw [Finset.sum_range_add_sum_Ico f ht]
    _ = ∑ s ∈ Finset.range N, f s + ∑ s ∈ Finset.Ico N t, p.eval (s : ℚ) := by rw [hIcoF]
    _ = ∑ s ∈ Finset.range N, f s
          + ((∑ s ∈ Finset.range t, p.eval (s : ℚ))
              - (∑ s ∈ Finset.range N, p.eval (s : ℚ))) := by rw [hIcoP]
    _ = (sumPoly p).eval (t : ℚ)
          + ((∑ s ∈ Finset.range N, f s) - (sumPoly p).eval (N : ℚ)) := by
        rw [sumPoly_eval p t, sumPoly_eval p N]
        ring

end Commons.Algebra.Polynomial.EventuallyPoly