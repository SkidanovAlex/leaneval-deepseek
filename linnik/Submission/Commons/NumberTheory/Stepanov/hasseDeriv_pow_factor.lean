import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Algebra.Polynomial.hasseDeriv_mul_pow_degree

namespace Commons.NumberTheory.Stepanov

theorem hasseDeriv_pow_factor {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (hd : 1 ≤ g.natDegree) (u i : ℕ) (hi : i ≤ u) :
    ∃ w : Polynomial F, Polynomial.hasseDeriv i (g ^ u) = g ^ (u - i) * w ∧
      w.natDegree ≤ i * g.natDegree := by
  obtain ⟨w, hw, hdeg⟩ :=
    Commons.Algebra.Polynomial.hasseDeriv_mul_pow_degree (1 : Polynomial F) g i u hi
  refine ⟨w, ?_, ?_⟩
  · rw [one_mul, mul_comm] at hw
    exact hw
  · simp only [Polynomial.natDegree_one, zero_add] at hdeg
    exact le_trans hdeg (Nat.sub_le _ _)

end Commons.NumberTheory.Stepanov