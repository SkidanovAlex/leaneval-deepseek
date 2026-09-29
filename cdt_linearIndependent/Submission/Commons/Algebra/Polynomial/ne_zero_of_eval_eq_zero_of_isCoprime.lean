import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Algebra.Polynomial.dvd_sq_X_sub_C_iff

namespace Commons.Algebra.Polynomial

/-- **Coprime polynomials have no common root.**  If `IsCoprime p q` and `p.eval β = 0` then `q.eval β ≠ 0`.  Indeed `(X − C β) ∣ p` and (were `q.eval β = 0`) `(X − C β) ∣ q`, so `IsCoprime.isUnit_of_dvd'` would make `X − C β` a unit, i.e. `eval β (X − C β) = 0` a unit of the field, which is absurd.

Together with `IsCoprime.isUnit_of_dvd'` this is how the Bézout certificates `a·p + b·q = C c` (`c ≠ 0`) of the divisor bounds of arXiv:2408.15403 discharge the "no common root" hypotheses (e.g. `R₄` and `R₁₀`, whose coprimality is the paper's Lemma `(res)(2)`). -/
theorem ne_zero_of_eval_eq_zero_of_isCoprime {K : Type*} [Field K] {p q : Polynomial K}
    (h : IsCoprime p q) {β : K} (hp : p.eval β = 0) : q.eval β ≠ 0 := by
  intro hq
  obtain ⟨a, b, hab⟩ := h
  have h1 : (a * p + b * q).eval β = (1 : K) := by rw [hab]; simp
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hp, hq,
    mul_zero, mul_zero, add_zero] at h1
  exact one_ne_zero h1.symm

end Commons.Algebra.Polynomial