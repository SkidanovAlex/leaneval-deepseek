import Mathlib
import Submission.Work.LT.Defs

namespace Work.LT

/-- The underlying matrix of the elementary matrix `sl3E p i j t` for `i ≠ j`. -/
lemma sl3E_coe_of_ne (p : ℕ) {i j : Fin 3} (h : i ≠ j) (t : ZMod p) :
    ((sl3E p i j t : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)) = Matrix.transvection i j t := by
  unfold sl3E Matrix.SpecialLinearGroup
  rw [dite_eq_right h]

/-- `E_ab(k)` commutes with `E_ac(s)`: the two single-entry matrices involved have disjoint
supports. -/
lemma transvection_comm_fst (p : ℕ) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (k s : ZMod p) :
    Matrix.transvection a b k * Matrix.transvection a c s
      = Matrix.transvection a c s * Matrix.transvection a b k := by
  have h1 : Matrix.single a b k * Matrix.single a c s = 0 :=
    Matrix.single_mul_single_of_ne k a b a (Ne.symm hab) s
  have h2 : Matrix.single a c s * Matrix.single a b k = 0 :=
    Matrix.single_mul_single_of_ne s a c a (Ne.symm hac) k
  simp only [Matrix.transvection, mul_add, add_mul, one_mul, mul_one, h1, h2, add_zero]
  abel

/-- `E_ac(s)` commutes with `E_bc(u)`: the two single-entry matrices involved have disjoint
supports. -/
lemma transvection_comm_snd (p : ℕ) {a b c : Fin 3} (hac : a ≠ c) (hbc : b ≠ c)
    (s u : ZMod p) :
    Matrix.transvection a c s * Matrix.transvection b c u
      = Matrix.transvection b c u * Matrix.transvection a c s := by
  have h1 : Matrix.single a c s * Matrix.single b c u = 0 :=
    Matrix.single_mul_single_of_ne s a c b (Ne.symm hbc) u
  have h2 : Matrix.single b c u * Matrix.single a c s = 0 :=
    Matrix.single_mul_single_of_ne u b c a (Ne.symm hac) s
  simp only [Matrix.transvection, mul_add, add_mul, one_mul, mul_one, h1, h2, add_zero]
  abel

/-- Conjugation of a product: `X (P Q) X' = (X P X')(X Q X')` whenever `X'` is a left inverse
of `X`. -/
lemma conj_mul {M : Type*} [Monoid M] {X X' P Q : M} (h : X' * X = 1) :
    X * (P * Q) * X' = (X * P * X') * (X * Q * X') := by
  simp only [mul_assoc]
  rw [← mul_assoc X' X (Q * X'), h, one_mul]

/-- Matrix form of `E_ab(k) E_ac(s) E_ab(k)⁻¹ = E_ac(s)`. -/
lemma transvection_conj_A (p : ℕ) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (k s : ZMod p) :
    Matrix.transvection a b k * Matrix.transvection a c s * Matrix.transvection a b (-k)
      = Matrix.transvection a c s := by
  rw [transvection_comm_fst p hab hac k s, mul_assoc,
    Matrix.transvection_mul_transvection_same a b hab k (-k)]
  simp

/-- Matrix form of `E_ab(k) E_bc(t) E_ab(k)⁻¹ = E_ac(kt) E_bc(t)`. -/
lemma transvection_conj_B (p : ℕ) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (k t : ZMod p) :
    Matrix.transvection a b k * Matrix.transvection b c t * Matrix.transvection a b (-k)
      = Matrix.transvection a c (k * t) * Matrix.transvection b c t := by
  have hXX : Matrix.single a b k * Matrix.single a b k = 0 :=
    Matrix.single_mul_single_of_ne k a b a (Ne.symm hab) k
  have hXY : Matrix.single a b k * Matrix.single b c t = Matrix.single a c (k * t) :=
    Matrix.single_mul_single_same k a b c t
  have hYX : Matrix.single b c t * Matrix.single a b k = 0 :=
    Matrix.single_mul_single_of_ne t b c a (Ne.symm hac) k
  have hZY : Matrix.single a c (k * t) * Matrix.single b c t = 0 :=
    Matrix.single_mul_single_of_ne (k * t) a c b (Ne.symm hbc) t
  have hZX : Matrix.single a c (k * t) * Matrix.single a b k = 0 :=
    Matrix.single_mul_single_of_ne (k * t) a c a (Ne.symm hac) k
  have hsn : Matrix.single a b (-k) = - Matrix.single a b k := (Matrix.single_neg a b k).symm
  simp only [Matrix.transvection]
  rw [hsn]
  simp only [mul_add, add_mul, one_mul, mul_one, hXX, hXY, hYX, hZY, hZX, mul_neg, add_zero]
  abel

/-- Conjugation of the column subgroup `U = {E_ac(s)·E_bc(t)}` by the two transvections
`E_ab(k)`, `E_ba(k)` of the `SL₂` on `{a,b}`.  Concretely `E_ab(k) E_ac(s) E_ab(k)⁻¹ = E_ac(s)`,
`E_ab(k) E_bc(t) E_ab(k)⁻¹ = E_ac(kt)·E_bc(t)` and `E_ba(k) E_ac(s) E_ba(k)⁻¹ = E_ac(s)·E_bc(ks)`,
`E_ba(k) E_bc(t) E_ba(k)⁻¹ = E_bc(t)`.  Here `sl3E p i j t = 1 + t·e_{ij}` is the elementary
matrix (the identity when `i = j`). -/
theorem relT_sl3E_conj :
    (∀ (p : ℕ) {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c → ∀ (k s t : ZMod p),
        sl3E p a b k * (sl3E p a c s * sl3E p b c t) * sl3E p a b (-k) =
          sl3E p a c (s + k * t) * sl3E p b c t)
  ∧ (∀ (p : ℕ) {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c → ∀ (k s t : ZMod p),
        sl3E p b a k * (sl3E p a c s * sl3E p b c t) * sl3E p b a (-k) =
          sl3E p a c s * sl3E p b c (t + k * s)) := by
  constructor
  · intro p a b c hab hac hbc k s t
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [sl3E_coe_of_ne p hab k, sl3E_coe_of_ne p hac s, sl3E_coe_of_ne p hbc t,
      sl3E_coe_of_ne p hab (-k), sl3E_coe_of_ne p hac (s + k * t)]
    have hX'X : Matrix.transvection a b (-k) * Matrix.transvection a b k = 1 := by
      rw [Matrix.transvection_mul_transvection_same a b hab (-k) k]
      simp
    rw [conj_mul hX'X, transvection_conj_A p hab hac k s,
      transvection_conj_B p hab hac hbc k t, ← mul_assoc,
      Matrix.transvection_mul_transvection_same a c hac s (k * t)]
  · intro p a b c hab hac hbc k s t
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [sl3E_coe_of_ne p (Ne.symm hab) k, sl3E_coe_of_ne p hac s, sl3E_coe_of_ne p hbc t,
      sl3E_coe_of_ne p (Ne.symm hab) (-k), sl3E_coe_of_ne p hbc (t + k * s)]
    have hY'Y : Matrix.transvection b a (-k) * Matrix.transvection b a k = 1 := by
      rw [Matrix.transvection_mul_transvection_same b a (Ne.symm hab) (-k) k]
      simp
    rw [conj_mul hY'Y, transvection_conj_B p (Ne.symm hab) hbc hac k s,
      transvection_conj_A p (Ne.symm hab) hbc k t, mul_assoc,
      transvection_comm_snd p hac hbc s t, ← mul_assoc,
      Matrix.transvection_mul_transvection_same b c hbc (k * s) t,
      ← transvection_comm_snd p hac hbc s (k * s + t), add_comm (k * s) t]

end Work.LT
