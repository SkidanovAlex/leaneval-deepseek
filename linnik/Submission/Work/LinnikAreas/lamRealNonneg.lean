/-
# `λ(n) = Σ_{d | n} χ(d)` is real and nonnegative for a real character `χ`

For a real (quadratic) Dirichlet character `χ` modulo `q` (i.e. `χ ^ 2 = 1`) the coefficients
`λ(n) = Σ_{d | n} χ(d)` of the Dirichlet series `ζ(s)L(s,χ)` are real and nonnegative, and are
bounded in modulus by the number of divisors of `n`.

* Realness is immediate: `χ` only takes the values `0, ±1` (`charValTri`).
* Nonnegativity uses multiplicativity of the divisor sum: writing `n = ∏_p p^{a_p}` one has
  `λ(n) = ∏_p λ(p^{a_p})` (`Nat.multiplicative_factorization` together with `lamMulCoprime`), and
  each local factor is the geometric sum `λ(p^{a_p}) = Σ_{j ≤ a_p} χ(p)^j ∈ {0, 1, 2, …}`
  (`lamPrimePow` together with `epsPowSumReNonneg`).
* The modulus bound is the triangle inequality together with `‖χ d‖ ≤ 1`.

Supporting lemmas proved in this workspace:
* `Work.LinnikAreas.charValTri`;
* `Work.LinnikAreas.lamPrimePow`;
* `Work.LinnikAreas.epsPowSumReNonneg`.
-/
import Mathlib
import Submission.Work.LinnikAreas.RatioDefs
import Submission.Work.LinnikAreas.charValTri
import Submission.Work.LinnikAreas.lamPrimePow
import Submission.Work.LinnikAreas.epsPowSumReNonneg

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped BigOperators

/-- A complex number with vanishing imaginary part is the casting of its real part. -/
lemma complex_eq_ofReal_re {z : ℂ} (h : z.im = 0) : z = ((z.re : ℝ) : ℂ) :=
  Complex.ext rfl (by simp [h])

/-- `λ` is multiplicative on coprime arguments: the divisors of `m * n` for coprime `m, n` are
exactly the products `d₁ * d₂` with `d₁ ∣ m`, `d₂ ∣ n`. -/
theorem lamMulCoprime {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {m n : ℕ}
    (h : m.Coprime n) : lam χ (m * n) = lam χ m * lam χ n := by
  rw [lam, lam, lam, Nat.divisors_mul, Finset.mul_def, Finset.sum_image]
  · rw [Finset.sum_product, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Nat.cast_mul, map_mul]
  · exact h.mul_injOn_divisors

/-- `λ(1) = χ(1) = 1`. -/
theorem lam_one_eq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : lam χ 1 = 1 := by
  simp [lam]

theorem lamRealNonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχsq : χ ^ 2 = 1) :
    (∀ n : ℕ, (Work.LinnikAreas.lam χ n).im = 0) ∧ (∀ n : ℕ, 0 ≤ (Work.LinnikAreas.lam χ n).re) ∧
      (∀ n : ℕ, ‖Work.LinnikAreas.lam χ n‖ ≤ ((n.divisors.card : ℕ) : ℝ)) := by
  have hval : ∀ a : ZMod q, χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := fun a => (charValTri χ hχsq a).1
  -- Realness and nonnegativity of `λ n`, via the prime factorisation of `n`.
  have hmain : ∀ n : ℕ, (lam χ n).im = 0 ∧ 0 ≤ (lam χ n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · refine ⟨by simp [lam], by simp [lam]⟩
    · -- Every prime in the support of `n.factorization` is a prime.
      have hprim : ∀ p ∈ n.factorization.support, p.Prime := by
        intro p hp
        have hp0 : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
        by_contra hcon
        exact hp0 ((Nat.factorization_eq_zero_iff n p).mpr (Or.inl hcon))
      -- Each local factor is real, with nonnegative real part.
      have hfac : ∀ p ∈ n.factorization.support,
          lam χ (p ^ n.factorization p)
            = (((∑ j ∈ Finset.range (n.factorization p + 1), (χ (p : ZMod q)) ^ j).re : ℝ) : ℂ) := by
        intro p hp
        rw [lamPrimePow χ (hprim p hp)]
        exact complex_eq_ofReal_re (epsPowSumReNonneg (hval (p : ZMod q)) _).2
      -- Multiplicativity turns `λ n` into the product of the local factors.
      have hprod : lam χ n
          = ((∏ p ∈ n.factorization.support,
                (∑ j ∈ Finset.range (n.factorization p + 1), (χ (p : ZMod q)) ^ j).re : ℝ) : ℂ) := by
        rw [Nat.multiplicative_factorization (fun m => lam χ m)
              (fun a b hab => lamMulCoprime χ hab) (lam_one_eq_one χ) hn,
            Finsupp.prod, Complex.ofReal_prod]
        exact Finset.prod_congr rfl hfac
      refine ⟨by rw [hprod, Complex.ofReal_im],
        by rw [hprod, Complex.ofReal_re]; exact Finset.prod_nonneg fun p hp =>
          (epsPowSumReNonneg (hval (p : ZMod q)) (n.factorization p)).1⟩
  -- Modulus bound: triangle inequality, `‖χ d‖ ≤ 1` and `card` terms.
  have hnorm : ∀ n : ℕ, ‖lam χ n‖ ≤ ((n.divisors.card : ℕ) : ℝ) := by
    intro n
    calc ‖lam χ n‖ = ‖∑ d ∈ n.divisors, χ (d : ZMod q)‖ := rfl
      _ ≤ ∑ d ∈ n.divisors, ‖χ (d : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ n.divisors, (1 : ℝ) := by
            refine Finset.sum_le_sum fun d _ => ?_
            rcases hval (d : ZMod q) with h | h | h <;> simp [h]
      _ = ((n.divisors.card : ℕ) : ℝ) := by simp
  exact ⟨fun n => (hmain n).1, fun n => (hmain n).2, hnorm⟩

end Work.LinnikAreas
