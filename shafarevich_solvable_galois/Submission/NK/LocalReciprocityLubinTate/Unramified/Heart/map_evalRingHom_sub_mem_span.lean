import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Polynomial.Eval.Degree
import Submission.NK.LocalReciprocityLubinTate.Unramified.LTGain
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.Unramified.Heart

/-- **Divisibility of a difference of evaluations.**  For a polynomial `q` over a commutative ring,
a divisor `c` of the coefficient of `X` in `q` and an exponent `k ≥ 1`, the difference
`q(c^k) - q(0)` is divisible by `c^(k+1)`: the `X`-term contributes `q.coeff 1 * c^k`, which is a
multiple of `c^(k+1)` because `c ∣ q.coeff 1`, and every term of degree `i ≥ 2` contributes
`q.coeff i * c^(k·i)` with `k·i ≥ k+1`. -/
theorem dvd_eval_pow_sub_eval_zero {R : Type*} [CommRing R] (c : R) (k : ℕ) (hk : 1 ≤ k)
    (q : Polynomial R) (h : c ∣ q.coeff 1) :
    c ^ (k + 1) ∣ q.eval (c ^ k) - q.eval 0 := by
  have hsplit : q.eval (c ^ k) - q.coeff 0
      = ∑ i ∈ Finset.range q.natDegree, q.coeff (i + 1) * (c ^ k) ^ (i + 1) := by
    rw [Polynomial.eval_eq_sum_range (c ^ k), Finset.sum_range_succ', pow_zero, mul_one]
    ring
  rw [← Polynomial.coeff_zero_eq_eval_zero q, hsplit]
  refine Finset.dvd_sum (fun i _ => ?_)
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · rw [h0]
    simp only [Nat.zero_add, pow_one]
    obtain ⟨u, hu⟩ := h
    exact ⟨u, by rw [hu, pow_succ']; ring⟩
  · have hle : k + 1 ≤ k * (i + 1) := by
      have h2 : k * 2 ≤ k * (i + 1) := Nat.mul_le_mul_left k (by omega)
      have h3 : k + 1 ≤ k * 2 := by omega
      exact le_trans h3 h2
    exact dvd_mul_of_dvd_right (by rw [← pow_mul]; exact pow_dvd_pow c hle) _

/-- **Substituting `Polynomial.evalRingHom (c^k)` for `Polynomial.evalRingHom 0`.**  Let
`G ∈ (R[X])[Y] = R[X,Y]` and let `g₀` be the specialisation of `G` at the coefficient-variable
value `0`, `g₀ = G|_{Y=0}`.  If every coefficient of `Y` in `G` (i.e. every `G.coeff j ∈ R[X]`) has
its linear coefficient divisible by `c`, then specialising at `Y = c^k` instead of `Y = 0` changes
`G` by a multiple of `c^(k+1)`:

`G|_{Y = c^k} - G|_{Y = 0} ∈ (c^(k+1)) ⊂ R[X]`.

This is the "second substitution step" of the Lubin–Tate gain lemma: the coefficientwise statement
that the `s`-parametrised norm operator `paramNormOp P q v t`, whose coefficient of `s^1` is
divisible by `P` (`paramNormOp_sCoeff`), differs from its `s = 0` specialisation collected at
`s = P^k` by a multiple of `P^(k+1)`. -/
theorem map_evalRingHom_sub_mem_span {R : Type*} [CommRing R] (c : R) (k : ℕ) (hk : 1 ≤ k)
    (G : Polynomial (Polynomial R)) (g₀ : Polynomial R)
    (h0 : Polynomial.map (Polynomial.evalRingHom 0) G = g₀)
    (h1 : ∀ j, c ∣ (G.coeff j).coeff 1) :
    Polynomial.map (Polynomial.evalRingHom (c ^ k)) G - g₀
      ∈ Ideal.span ({Polynomial.C (c ^ (k + 1))} : Set (Polynomial R)) := by
  rw [Ideal.mem_span_singleton, Polynomial.C_dvd_iff_dvd_coeff]
  intro j
  have hcoeff : (Polynomial.map (Polynomial.evalRingHom (c ^ k)) G - g₀).coeff j
      = (G.coeff j).eval (c ^ k) - (G.coeff j).eval 0 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
    congr 1
    rw [← h0, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
  rw [hcoeff]
  exact dvd_eval_pow_sub_eval_zero c k hk (G.coeff j) (h1 j)

end NK.LocalReciprocityLubinTate.Unramified.Heart
