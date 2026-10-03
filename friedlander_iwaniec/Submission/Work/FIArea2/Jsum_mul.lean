import Mathlib
import Submission.Work.FIArea2.NsolDefs

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The arithmetic function `d ↦ φ(d)·(a/d)`, the first factor of the Dirichlet convolution
whose value at `q` is `Jsum q a`. -/
noncomputable def JacArith (a : ℤ) : ArithmeticFunction ℝ :=
  ⟨fun d => (Nat.totient d : ℝ) * (jacobiSym a d : ℝ), by simp⟩

/-- The identity arithmetic function `n ↦ n`, the second (convolution) factor. -/
noncomputable def IdArith : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ), by simp⟩

/-- `JacArith a` is multiplicative: `φ` is multiplicative and so is `d ↦ (a/d)`
(completely, for non-zero arguments). -/
lemma JacArith_isMult (a : ℤ) : (JacArith a).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [JacArith], ?_⟩
  intro m n hm hn hcop
  show (Nat.totient (m * n) : ℝ) * (jacobiSym a (m * n) : ℝ) =
    ((Nat.totient m : ℝ) * (jacobiSym a m : ℝ)) *
      ((Nat.totient n : ℝ) * (jacobiSym a n : ℝ))
  have ht : ((m * n).totient : ℝ) = (m.totient : ℝ) * (n.totient : ℝ) := by
    rw [Nat.totient_mul hcop]; push_cast; ring
  have hj : (jacobiSym a (m * n) : ℝ) = (jacobiSym a m : ℝ) * (jacobiSym a n : ℝ) := by
    rw [jacobiSym.mul_right' a hm hn]; push_cast; ring
  rw [ht, hj]; ring

/-- The identity arithmetic function is multiplicative. -/
lemma IdArith_isMult : (IdArith).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [IdArith], ?_⟩
  intro m n hm hn hcop
  show ((m * n : ℕ) : ℝ) = (m : ℝ) * (n : ℝ)
  push_cast; ring

/-- `Jsum q a` is the Dirichlet convolution of `d ↦ φ(d)(a/d)` with the identity:
distributing the factor `q` into the divisor sum, `q·Σ_{d|q}(φ(d)/d)(a/d)`
`= Σ_{d|q} φ(d)(a/d)·(q/d)`. -/
lemma JsumF_eq_conv (a : ℤ) (n : ℕ) : JsumF a n = (JacArith a * IdArith) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [JsumF]
  · rw [JsumF_eq a hn, Jsum, ArithmeticFunction.mul_apply, ← Nat.map_div_right_divisors,
      Finset.sum_map, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    show (n : ℝ) * ((Nat.totient d : ℝ) / (d : ℝ) * (jacobiSym a d : ℝ)) =
      (Nat.totient d : ℝ) * (jacobiSym a d : ℝ) * ((n / d : ℕ) : ℝ)
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd0 : (d : ℝ) ≠ 0 := by
      have := Nat.pos_of_mem_divisors hd
      exact_mod_cast this.ne'
    rw [Nat.cast_div hdn hd0]
    field_simp

/-- `JsumF a` agrees with `Jsum · a` everywhere (both vanish at `0`). -/
lemma JsumF_apply (a : ℤ) (q : ℕ) : JsumF a q = Jsum q a := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp [JsumF, Jsum_zero]
  · exact JsumF_eq a hq

/-- **The right-hand side `q Σ_{d|q}(φ(d)/d)(a/d)` of (8.13) is multiplicative in `q`.**  For coprime `m, n` one has `Jsum (m*n) a = Jsum m a * Jsum n a`; equivalently the arithmetic function `q ↦ Σ_{d|q} φ(d)(a/d)·(q/d)` (Dirichlet convolution of `d ↦ φ(d)(a/d)` with the identity) is multiplicative, since `φ` and `d ↦ (a/d)` are multiplicative and `(d₁d₂/d) = (d₁/d)(d₂/d)`.  This lets the two sides of (8.13) be compared prime-power by prime-power (`ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers`), which is exactly how the paper concludes Corollary 8.3 from Lemma 8.2. -/
theorem Jsum_mul (a : ℤ) (m n : ℕ) (h : Nat.Coprime m n) :
    Jsum (m * n) a = Jsum m a * Jsum n a := by
  have hJG : JsumF a = JacArith a * IdArith :=
    ArithmeticFunction.ext fun n => JsumF_eq_conv a n
  have hmult : (JsumF a).IsMultiplicative := by
    rw [hJG]; exact (JacArith_isMult a).mul IdArith_isMult
  have key := hmult.2 h
  rw [JsumF_apply, JsumF_apply, JsumF_apply] at key
  exact key

end Work.FIArea2
