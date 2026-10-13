import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.ET_base
-- `Submission.Work.WilE3K.ET_step` is a colleague's work in progress and does not build yet; it is
-- not needed here, since the elimination step `hstep` enters as a hypothesis.

namespace Work.WilE3K

/-- The recursion bound `ETB q rt N` is monotone in its degree argument `D`.  This is what lets the
induction absorb the slack in the degree bookkeeping of one elimination step: the step produces a
system of degree sum `D'` with `D' + rt ≤ (N+9) * (D + (rt+1) + 11)`, and `ETB` is applied to the
*rounded up* argument.

At `rt = 0` this is the monotonicity of `q.eval : ℕ → ℕ` on the naturals, which holds because all
coefficients of `q : Polynomial ℕ` are non-negative. -/
theorem ETB_mono_d (q : Polynomial ℕ) : ∀ rt N, Monotone (ETB q rt N)
  | 0, N => by
      have hq : Monotone q.eval := by
        intro a b hab
        show q.eval a ≤ q.eval b
        rw [Polynomial.eval_eq_sum_range (p := q) a, Polynomial.eval_eq_sum_range (p := q) b]
        apply Finset.sum_le_sum
        intro k _
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab k)
      exact hq
  | (rt+1), N => by
      show Monotone (fun D => ETB q rt (N+1) ((N+9)*(D+11)))
      exact (ETB_mono_d q rt (N+1)).comp
        (fun a b hab => Nat.mul_le_mul_left _ (Nat.add_le_add_right hab 11))

/-- **The ET induction (K3) with the tight constants.**  From the base case `hbase` (`rt = 0`, the
frozen exp-affine Khovanskii bound `q`) and the elimination step `hstep` (one sphere step plus one
Rolle step, with the tight degree bookkeeping `(N+9) * (D + (rt+1) + 11)`), one gets the recursion
bound `ETB` for every number `rt` of arctan graph equations.

The induction is on `rt`.  In the step, `hstep` produces a system `E'` with one fewer arctan
equation, one more free coordinate and degree sum `D'` satisfying
`D' + rt ≤ (N+9) * (D + (rt+1) + 11)`; the induction hypothesis applied to `E'` (which lives `ℝ^{N+2}`
with `N+2+re+rt ≤ M`) bounds the new set, and `ETB_mono_d` converts the degree bound into
`ETB q (rt+1) N (D + (rt+1)) = ETB q rt (N+1) ((N+9) * (D + (rt+1) + 11))`. -/
theorem ET_all_tight (q : Polynomial ℕ) (M : ℕ)
    (hbase : ∀ (N n re : ℕ) (E : Work.WilE3K.ETData N 0 n re) (s : Finset (Fin (N + 1) → ℝ)),
      N + 1 + re ≤ M → (∀ z ∈ s, E.Nondegen z) →
        s.card ≤ q.eval (∑ i, WilkiesDesign.E.atomDeg (E.G i)))
    (hstep : ∀ (rt N n re : ℕ) (E : Work.WilE3K.ETData N (rt + 1) n re)
      (s : Finset (Fin (N + 1) → ℝ)), N + 1 + re + (rt + 1) ≤ M →
      (∀ z ∈ s, E.Nondegen z) →
      ∃ (E' : Work.WilE3K.ETData (N + 1) rt (n + 2) re) (t : Finset (Fin ((N + 1) + 1) → ℝ)),
        (∀ z ∈ t, E'.Nondegen z) ∧ s.card ≤ t.card ∧
        (∑ i, WilkiesDesign.E.atomDeg (E'.G i)) + rt ≤
          (N + 9) * ((∑ i, WilkiesDesign.E.atomDeg (E.G i)) + (rt + 1) + 11)) :
    ∀ (rt N n re : ℕ) (E : Work.WilE3K.ETData N rt n re) (s : Finset (Fin (N + 1) → ℝ)),
      N + 1 + re + rt ≤ M → (∀ z ∈ s, E.Nondegen z) →
      s.card ≤ Work.WilE3K.ETB q rt N (∑ i, WilkiesDesign.E.atomDeg (E.G i) + rt) := by
  intro rt
  induction rt with
  | zero =>
      intro N n re E s hM hs
      exact hbase N n re E s (by simpa using hM) hs
  | succ rt ih =>
      intro N n re E s hM hs
      obtain ⟨E', t, htnd, hcard, hdeg⟩ := hstep rt N n re E s hM hs
      have hM' : (N + 1) + 1 + re + rt ≤ M := by omega
      have ht := ih (N + 1) (n + 2) re E' t hM' htnd
      have hmono := ETB_mono_d q rt (N + 1) hdeg
      exact le_trans hcard (le_trans ht hmono)

end Work.WilE3K
