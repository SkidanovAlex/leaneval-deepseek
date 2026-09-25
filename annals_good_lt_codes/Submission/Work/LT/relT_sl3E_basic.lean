import Mathlib
import Submission.Work.LT.Defs

namespace Work.LT

/-- Elementary matrices: `E_ij(0) = 1`, `E_ij(s)·E_ij(t) = E_ij(s+t)`, `E_ij(-t)·E_ij(t) = 1`
for `i ≠ j`; and `E_ac(s)` commutes with `E_bc(t)` for distinct `a,b,c`, with the resulting
product rule for the column subgroup `U = {E_ac(s)E_bc(t)}`. -/
theorem relT_sl3E_basic :
    (∀ (p : ℕ) (i j : Fin 3), sl3E p i j 0 = 1)
  ∧ (∀ (p : ℕ) {i j : Fin 3}, i ≠ j → ∀ s t : ZMod p,
        sl3E p i j s * sl3E p i j t = sl3E p i j (s + t))
  ∧ (∀ (p : ℕ) {i j : Fin 3}, i ≠ j → ∀ t : ZMod p, sl3E p i j (-t) * sl3E p i j t = 1)
  ∧ (∀ (p : ℕ) {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c → ∀ s t : ZMod p,
        sl3E p a c s * sl3E p b c t = sl3E p b c t * sl3E p a c s)
  ∧ (∀ (p : ℕ) {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c → ∀ s s' t t' : ZMod p,
        (sl3E p a c s * sl3E p b c t) * (sl3E p a c s' * sl3E p b c t') =
          sl3E p a c (s + s') * sl3E p b c (t + t')) := by
  -- Off the diagonal, `sl3E` is Mathlib's transvection, for either name of the hypothesis.
  have hE : ∀ (p : ℕ) {i j : Fin 3} (h : i ≠ j) (t : ZMod p),
      sl3E p i j t = Matrix.SpecialLinearGroup.transvection h t := by
    intro p i j h t
    unfold sl3E
    exact dite_eq_right h
  -- On the diagonal `sl3E` is the identity.
  have h0 : ∀ (p : ℕ) (i : Fin 3) (t : ZMod p), sl3E p i i t = 1 := by
    intro p i t
    unfold sl3E
    exact dite_eq_left rfl
  -- `E_ac(s)` and `E_bc(t)` commute, in transvection form, when `a ≠ c` and `b ≠ c`.
  have hcommT : ∀ (p : ℕ) {a b c : Fin 3} (hac : a ≠ c) (hbc : b ≠ c) (s t : ZMod p),
      Matrix.SpecialLinearGroup.transvection hac s * Matrix.SpecialLinearGroup.transvection hbc t
        = Matrix.SpecialLinearGroup.transvection hbc t
          * Matrix.SpecialLinearGroup.transvection hac s := by
    intro p a b c hac hbc s t
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.single_mul_single_of_ne s a c b (Ne.symm hbc) t,
      Matrix.single_mul_single_of_ne t b c a (Ne.symm hac) s, add_zero]
    abel
  -- The same commutation for `sl3E`.
  have hcomm : ∀ (p : ℕ) {a b c : Fin 3}, a ≠ c → b ≠ c → ∀ s t : ZMod p,
      sl3E p a c s * sl3E p b c t = sl3E p b c t * sl3E p a c s := by
    intro p a b c hac hbc s t
    rw [hE p hac s, hE p hbc t]
    exact hcommT p hac hbc s t
  -- In a group, `P·P' = P'·P` lets one permute the factors in `(P·Q)(P'·Q')`.
  have key : ∀ {G : Type} [Group G] (P Q P' Q' : G), P' * Q = Q * P' →
      (P * Q) * (P' * Q') = (P * P') * (Q * Q') := by
    intro G _ P Q P' Q' h
    rw [mul_assoc, ← mul_assoc Q P' Q', ← h, ← mul_assoc P (P' * Q) Q', ← mul_assoc P P' Q,
      mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p i j
    by_cases h : i = j
    · subst h
      exact h0 p i 0
    · rw [hE p h 0]
      exact Matrix.SpecialLinearGroup.transvection_coeff_zero h
  · intro p i j h s t
    rw [hE p h s, hE p h t, hE p h (s + t)]
    exact (Matrix.SpecialLinearGroup.transvection_add h s t).symm
  · intro p i j h t
    rw [hE p h (-t), hE p h t]
    simpa using Matrix.SpecialLinearGroup.transvection_mul_neg h (-t)
  · intro p a b c hab hac hbc s t
    exact hcomm p hac hbc s t
  · intro p a b c hab hac hbc s s' t t'
    rw [hE p hac s, hE p hbc t, hE p hac s', hE p hbc t', hE p hac (s + s'),
      hE p hbc (t + t')]
    rw [key (Matrix.SpecialLinearGroup.transvection hac s)
          (Matrix.SpecialLinearGroup.transvection hbc t)
          (Matrix.SpecialLinearGroup.transvection hac s')
          (Matrix.SpecialLinearGroup.transvection hbc t') (hcommT p hac hbc s' t)]
    rw [← Matrix.SpecialLinearGroup.transvection_add hac s s',
      ← Matrix.SpecialLinearGroup.transvection_add hbc t t']

end Work.LT
