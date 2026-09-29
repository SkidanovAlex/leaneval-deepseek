import Mathlib
import Submission.Work.C17.adjoint_defs

/-!
# Nonvanishing of the order-8 obstruction `Ψ₈` on the admissible region

`Work.C17.Psib a b` is the degree-8 factor `Ψ₈(a,b)` appearing as the numerator of the
13-minors of the formal-adjoint linear system for the `P`-branch (the paper's (I2), see
`Submission/Work/C17/adjoint_defs.lean` and `REFS/design/ct17/CT17_design.lean.txt`).

Here we prove that `Ψ₈` does not vanish when `3 ≤ a`, `a < b` and the gap is small
(`10⁶(b−a) ≤ b`), i.e. exactly under the admissibility hypotheses used by the
seventeen-functions argument.  In fact we prove the stronger statement `Ψ₈ a b > 0`.

The proof is the "triangle inequality" of the design: writing `d = b - a` (so that
`10⁶d ≤ a + d` gives `1000 d ≤ a`), the expansion of `Ψ₈(a, a+d)` as a polynomial with
*constant* coefficients (degree 8 in `(a,d)`) has a strictly dominant term `2541 a⁸`,
because each monomial `a^i d^j` with a negative coefficient is bounded by
`a^{i+j}/1000^j ≤ a^{i+j}·10^{-3j}`, which is negligible against `a⁸`, whereas the only
negative terms without a compensating positive part are `−5586 a⁶` and `−975 d²`, both
easily dominated for `a ≥ 3`.
-/

namespace Work.C17adj

/-- The explicit expansion of `Ψ₈` in the shifted variable `d = b - a`. -/
theorem Psi8_expand (a d : ℚ) : Work.C17.Psib a (a + d) =
    2541*a^8 + 10164*a^7*d - 36421*a^6*d^2 - 144837*a^5*d^3 - 211750*a^4*d^4 - 170247*a^3*d^5
      - 59290*a^2*d^6
  - 5586*a^6 - 16758*a^5*d + 14819*a^4*d^2 + 57568*a^3*d^3 + 23086*a^2*d^4 - 8491*a*d^5
  + 2730*a^4 + 5460*a^3*d + 11865*a^2*d^2 + 9135*a*d^3 + 6090*d^4
  + 2310*a^2 + 2310*a*d - 975*d^2 - 1755 := by
  unfold Work.C17.Psib; ring

/-- From `1000 d ≤ a` (with `a, d ≥ 0`) every mixed monomial obeys `1000^j a^i d^j ≤ a^{i+j}`. -/
lemma Psi8_monomial_bound (a d : ℚ) (hd : 0 ≤ d) (h1000 : 1000 * d ≤ a) :
    ∀ i j : ℕ, 1000^j * (a^i * d^j) ≤ a^(i+j) := by
  intro i j
  have ha : 0 ≤ a := by linarith
  have hm : (1000 * d)^j ≤ a^j := pow_le_pow_left₀ (by linarith) h1000 j
  have h1 : 1000^j * d^j ≤ a^j := by simpa [mul_pow] using hm
  calc 1000^j * (a^i * d^j) = a^i * (1000^j * d^j) := by ring
    _ ≤ a^i * a^j := mul_le_mul_of_nonneg_left h1 (pow_nonneg ha i)
    _ = a^(i+j) := by rw [← pow_add]

/-- Positivity of the shifted polynomial: since `1000 d ≤ a`, every negative mixed monomial is
dominated by `a⁸/10^{3j}`, and the `a`-power part stays positive for `a ≥ 3`. -/
theorem Psi8_shift_pos (a d : ℚ) (ha : 3 ≤ a) (hd : 0 < d) (h1000 : 1000 * d ≤ a) :
    0 < 2541*a^8 + 10164*a^7*d - 36421*a^6*d^2 - 144837*a^5*d^3 - 211750*a^4*d^4 - 170247*a^3*d^5
      - 59290*a^2*d^6
  - 5586*a^6 - 16758*a^5*d + 14819*a^4*d^2 + 57568*a^3*d^3 + 23086*a^2*d^4 - 8491*a*d^5
  + 2730*a^4 + 5460*a^3*d + 11865*a^2*d^2 + 9135*a*d^3 + 6090*d^4
  + 2310*a^2 + 2310*a*d - 975*d^2 - 1755 := by
  have hd0 : (0:ℚ) ≤ d := le_of_lt hd
  have e1 : (1000:ℚ)^2 * (a^6*d^2) ≤ a^8 := by simpa using Psi8_monomial_bound a d hd0 h1000 6 2
  have e2 : (1000:ℚ)^3 * (a^5*d^3) ≤ a^8 := by simpa using Psi8_monomial_bound a d hd0 h1000 5 3
  have e3 : (1000:ℚ)^4 * (a^4*d^4) ≤ a^8 := by simpa using Psi8_monomial_bound a d hd0 h1000 4 4
  have e4 : (1000:ℚ)^5 * (a^3*d^5) ≤ a^8 := by simpa using Psi8_monomial_bound a d hd0 h1000 3 5
  have e5 : (1000:ℚ)^6 * (a^2*d^6) ≤ a^8 := by simpa using Psi8_monomial_bound a d hd0 h1000 2 6
  have f1 : (1000:ℚ)^1 * (a^5*d^1) ≤ a^6 := by simpa using Psi8_monomial_bound a d hd0 h1000 5 1
  have f5 : (1000:ℚ)^5 * (a^1*d^5) ≤ a^6 := by simpa using Psi8_monomial_bound a d hd0 h1000 1 5
  have g2 : (1000:ℚ)^2 * (a^0*d^2) ≤ a^2 := by simpa using Psi8_monomial_bound a d hd0 h1000 0 2
  have ha8 : (0:ℚ) ≤ a^8 := by positivity
  have ha6 : (0:ℚ) ≤ a^6 := by positivity
  -- the five negative degree-8 monomials
  have hB1 : 36421*a^6*d^2 + 144837*a^5*d^3 + 211750*a^4*d^4 + 170247*a^3*d^5 + 59290*a^2*d^6
      ≤ (37/1000)*a^8 := by nlinarith [e1,e2,e3,e4,e5,ha8]
  -- the two negative degree-6 monomials
  have hB2 : 16758*a^5*d + 8491*a*d^5 ≤ 17*a^6 := by nlinarith [f1,f5,ha6]
  -- the negative degree-2 monomial
  have hD2 : 975*d^2 ≤ (1/1000)*a^2 := by nlinarith [g2]
  -- all remaining mixed monomials have positive coefficients
  have hS : (0:ℚ) ≤ 10164*a^7*d + 14819*a^4*d^2 + 57568*a^3*d^3 + 23086*a^2*d^4
      + 5460*a^3*d + 11865*a^2*d^2 + 9135*a*d^3 + 6090*d^4 + 2310*a*d := by positivity
  have h2 : (9:ℚ) ≤ a^2 := by nlinarith
  have h4 : (81:ℚ) ≤ a^4 := by nlinarith [h2]
  have h6 : (729:ℚ) ≤ a^6 := by nlinarith [h2, h4]
  have h8 : (6561:ℚ) ≤ a^8 := by nlinarith [h2, h4, h6]
  nlinarith [hB1,hB2,hD2,hS,h2,h4,h6,h8]

theorem Psi8_ne_zero (a b : ℚ) (h3 : 3 ≤ a) (hlt : a < b) (hgap : 10 ^ 6 * (b - a) ≤ b) :
    Work.C17.Psib a b ≠ 0 := by
  have hdpos : 0 < b - a := by linarith
  have hgap' : 10 ^ 6 * (b - a) ≤ a + (b - a) := by linarith
  have h1000 : 1000 * (b - a) ≤ a := by nlinarith
  have hpos : 0 < Work.C17.Psib a (a + (b - a)) := by
    rw [Psi8_expand]
    exact Psi8_shift_pos a (b - a) h3 hdpos h1000
  have hb : a + (b - a) = b := by ring
  rw [hb] at hpos
  exact ne_of_gt hpos

end Work.C17adj
