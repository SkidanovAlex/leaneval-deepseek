import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Scale.frob_map_ofReal_sq
import Submission.Work.TMComp.LocCantor.sl2_fin2_mul_self
import Submission.Work.TMComp.LocCantor.sqsum_smul_sub

set_option linter.unusedVariables false

namespace Work.TMComp.LocCantor

open Matrix

/-- The rescaled Chebyshev polynomial of the second kind satisfies `U_n (t / 2) = S_n t`
(recall `S_n (2 x) = U_n x`). -/
lemma chebU_eval_S (t : ℝ) (n : ℤ) :
    (Polynomial.Chebyshev.U ℝ n).eval (t / 2) = (Polynomial.Chebyshev.S ℝ n).eval t := by
  rw [← Polynomial.Chebyshev.S_comp_two_mul_X ℝ n, Polynomial.eval_comp]
  congr 1
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
  ring

/-- The Chebyshev identity `U_n(t/2)^2 + U_{n+1}(t/2)^2 - t · U_n(t/2) · U_{n+1}(t/2) = 1`. -/
lemma chebU_sq_ident_local (t : ℝ) (n : ℤ) :
    ((Polynomial.Chebyshev.U ℝ n).eval (t / 2)) ^ 2
      + ((Polynomial.Chebyshev.U ℝ (n + 1)).eval (t / 2)) ^ 2
      - t * (((Polynomial.Chebyshev.U ℝ n).eval (t / 2))
              * ((Polynomial.Chebyshev.U ℝ (n + 1)).eval (t / 2))) = 1 := by
  rw [chebU_eval_S t n, chebU_eval_S t (n + 1)]
  have h := congrArg (Polynomial.eval t) (Polynomial.Chebyshev.S_sq_add_S_sq ℝ n)
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one] at h
  linarith [h]

/-- The Cayley--Hamilton recurrence for the powers of an `SL₂(ℝ)` matrix, solved with the
rescaled Chebyshev polynomials of the second kind:
`A ^ (m + 1) = S_m (tr A) • A - S_{m-1} (tr A) • 1`. -/
lemma sl2_pow_eq_S (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (m : ℕ) :
    A ^ (m + 1) = (Polynomial.Chebyshev.S ℝ (m : ℤ)).eval A.trace • A
      - (Polynomial.Chebyshev.S ℝ ((m : ℤ) - 1)).eval A.trace • 1 := by
  have hCH := sl2_fin2_mul_self A hdet
  induction m with
  | zero => simp
  | succ m ih =>
    have hcast1 : ((((m + 1 : ℕ)) : ℤ)) = (m : ℤ) + 1 := by push_cast; ring
    have hcast2 : (m : ℤ) + 1 - 1 = (m : ℤ) := by ring
    rw [hcast1, hcast2]
    have hS : (Polynomial.Chebyshev.S ℝ ((m : ℤ) + 1)).eval A.trace
        = A.trace * (Polynomial.Chebyshev.S ℝ (m : ℤ)).eval A.trace
          - (Polynomial.Chebyshev.S ℝ ((m : ℤ) - 1)).eval A.trace := by
      have h := congrArg (Polynomial.eval A.trace) (Polynomial.Chebyshev.S_add_one ℝ (m : ℤ))
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at h
      linarith [h]
    rw [pow_succ', ih, Matrix.mul_sub]
    simp only [Matrix.mul_smul, Matrix.mul_one]
    rw [hCH]
    simp only [smul_sub, smul_smul]
    rw [hS, sub_smul, mul_comm ((Polynomial.Chebyshev.S ℝ (m : ℤ)).eval A.trace) A.trace]
    abel

/-- Powers of an `SL₂(ℝ)` matrix in terms of the Chebyshev polynomials of the second kind:
`A ^ k = U_{k-1}(tr A / 2) • A - U_{k-2}(tr A / 2) • 1`, valid for every `k : ℕ`. -/
lemma sl2_pow_eq_chebU_self (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (k : ℕ) :
    A ^ k = (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (A.trace / 2) • A
      - (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 2)).eval (A.trace / 2) • 1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [pow_zero]
    simp [Polynomial.Chebyshev.U_neg_one, Polynomial.Chebyshev.U_neg_two]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [sl2_pow_eq_S A hdet m]
    have h1 : (((m + 1 : ℕ) : ℤ) - 1) = (m : ℤ) := by push_cast; ring
    have h2 : (((m + 1 : ℕ) : ℤ) - 2) = (m : ℤ) - 1 := by push_cast; ring
    rw [h1, h2, ← chebU_eval_S A.trace (m : ℤ), ← chebU_eval_S A.trace ((m : ℤ) - 1)]

theorem frob_pow_sl2_rt (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) (k : ℕ) (hk : 1 ≤ k) :
    Work.TMC7Core.frob ((A.map Complex.ofRealHom) ^ k) ^ 2
      = 2 + (A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2 - 2)
          * (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (A.trace / 2) ^ 2 := by
  have hfun : (⇑Complex.ofRealHom : ℝ → ℂ) = fun x : ℝ => (x : ℂ) := rfl
  have hmap : (A.map ⇑Complex.ofRealHom) ^ k = (A ^ k).map ⇑Complex.ofRealHom :=
    (Matrix.map_pow A Complex.ofRealHom k).symm
  rw [hmap, hfun, Work.TMC7Core.Scale.frob_map_ofReal_sq (A ^ k)]
  rw [sl2_pow_eq_chebU_self A hdet k]
  set u₁ : ℝ := (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 1)).eval (A.trace / 2) with hu₁
  set u₂ : ℝ := (Polynomial.Chebyshev.U ℝ ((k : ℤ) - 2)).eval (A.trace / 2) with hu₂
  rw [sqsum_smul_sub A u₁ u₂]
  have hid := chebU_sq_ident_local A.trace ((k : ℤ) - 2)
  rw [show ((k : ℤ) - 2) + 1 = (k : ℤ) - 1 from by ring] at hid
  rw [← hu₁, ← hu₂] at hid
  linear_combination (2 : ℝ) * hid

end Work.TMComp.LocCantor
