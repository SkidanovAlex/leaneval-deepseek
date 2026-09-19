import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Submission.Commons.NumberTheory.DirichletCharacter.finite_zeroHeights_window

namespace Commons.NumberTheory.DivisorSum

open scoped BigOperators

/-- Collapse a sum over `t ∈ S` of `(if a = t then f else 0) * g t` when `a ∈ S`. -/
private lemma sum_ite_mul_collapse {M : Type*} [NonUnitalNonAssocSemiring M]
    (S : Finset ℕ) {a : ℕ} (ha : a ∈ S) (f : M) (g : ℕ → M) :
    (∑ t ∈ S, (if a = t then f else 0) * g t) = f * g a := by
  have h : ∀ t ∈ S, (if a = t then f else 0) * g t = (if a = t then f * g t else 0) := by
    intro t _
    by_cases hc : a = t
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, zero_mul]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq, if_pos ha]

theorem sum_Icc_mul_fiber_regroup {M : Type*} [NonUnitalNonAssocSemiring M] (T : ℕ) (F : ℕ → ℕ → M)
    (G : ℕ → M) :
    (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T, F d e * G (d * e))
      = ∑ t ∈ Finset.Icc 1 (T * T),
          (∑ d ∈ Finset.Icc 1 T, ∑ e ∈ Finset.Icc 1 T,
            if d * e = t then F d e else 0) * G t := by
  have hmem : ∀ d ∈ Finset.Icc 1 T, ∀ e ∈ Finset.Icc 1 T, d * e ∈ Finset.Icc 1 (T * T) := by
    intro d hd e he
    simp only [Finset.mem_Icc] at hd he ⊢
    obtain ⟨hd1, hdT⟩ := hd
    obtain ⟨he1, heT⟩ := he
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul hdT heT⟩
  simp only [← Finset.sum_product']
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.mem_product] at hp
  exact (sum_ite_mul_collapse (Finset.Icc 1 (T * T)) (hmem p.1 hp.1 p.2 hp.2) (F p.1 p.2) G).symm

end Commons.NumberTheory.DivisorSum
