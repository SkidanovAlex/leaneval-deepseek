import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.ASRed
import Submission.Work.MotAS.ASEntries
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Reduction machinery for the AS transport of the dual secant quintic `s'`

The Artin--Schreier Galois coordinates `z_i = Σ_j asN w i j ẑ_j = P(w + 2i)` (for
`P(T) = Σ_j ẑ_j T^j`) are elements of the algebra `A = R[w]/(w⁵ - w - g)`; `AsSDzv i z` is the
coefficient vector of `z_i` in the basis `1, w, …, w⁴`, and `redMul g` is multiplication in `A`
(`Work.MotAS.redMul_spec`).  This file collects the definitions and the "staged reduction" lemmas
used by `Work.MotAS.asTransportSD`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

variable {R : Type*} [CommRing R]

/-- Coefficients of `Σ_j (w+2*0)^j · z_j = Σ_j z_j w^j` in the basis `1,w,…,w⁴`. -/
def AsSDzv0 (z : Fin 5 → R) : Fin 5 → R := ![z 0, z 1, z 2, z 3, z 4]

/-- Coefficients of `Σ_j (w+2)^j · z_j` in the basis `1,w,…,w⁴`. -/
def AsSDzv1 (z : Fin 5 → R) : Fin 5 → R :=
  ![z 0 + 2*z 1 + 4*z 2 + 8*z 3 + 16*z 4, z 1 + 4*z 2 + 12*z 3 + 32*z 4,
    z 2 + 6*z 3 + 24*z 4, z 3 + 8*z 4, z 4]

/-- Coefficients of `Σ_j (w+4)^j · z_j` in the basis `1,w,…,w⁴`. -/
def AsSDzv2 (z : Fin 5 → R) : Fin 5 → R :=
  ![z 0 + 4*z 1 + 16*z 2 + 64*z 3 + 256*z 4, z 1 + 8*z 2 + 48*z 3 + 256*z 4,
    z 2 + 12*z 3 + 96*z 4, z 3 + 16*z 4, z 4]

/-- Coefficients of `Σ_j (w+6)^j · z_j` in the basis `1,w,…,w⁴`. -/
def AsSDzv3 (z : Fin 5 → R) : Fin 5 → R :=
  ![z 0 + 6*z 1 + 36*z 2 + 216*z 3 + 1296*z 4, z 1 + 12*z 2 + 108*z 3 + 864*z 4,
    z 2 + 18*z 3 + 216*z 4, z 3 + 24*z 4, z 4]

/-- Coefficients of `Σ_j (w+8)^j · z_j` in the basis `1,w,…,w⁴`. -/
def AsSDzv4 (z : Fin 5 → R) : Fin 5 → R :=
  ![z 0 + 8*z 1 + 64*z 2 + 512*z 3 + 4096*z 4, z 1 + 16*z 2 + 192*z 3 + 2048*z 4,
    z 2 + 24*z 3 + 384*z 4, z 3 + 32*z 4, z 4]

theorem AsSDzv0_spec (w : R) (z : Fin 5 → R) :
    (∑ j, asN w 0 j * z j) = (∑ l, AsSDzv0 z l * w ^ (l:ℕ)) := by
  simp only [asN_0_0, asN_0_1, asN_0_2, asN_0_3, asN_0_4, AsSDzv0, Fin.cons_zero,
    Fin.cons_succ, Matrix.vecCons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_five]
  norm_num
  first | refl_ring1 | ring

theorem AsSDzv1_spec (w : R) (z : Fin 5 → R) :
    (∑ j, asN w 1 j * z j) = (∑ l, AsSDzv1 z l * w ^ (l:ℕ)) := by
  simp only [asN_1_0, asN_1_1, asN_1_2, asN_1_3, asN_1_4, AsSDzv1, Fin.cons_zero,
    Fin.cons_succ, Matrix.vecCons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_five]
  norm_num
  first | refl_ring1 | ring

theorem AsSDzv2_spec (w : R) (z : Fin 5 → R) :
    (∑ j, asN w 2 j * z j) = (∑ l, AsSDzv2 z l * w ^ (l:ℕ)) := by
  simp only [asN_2_0, asN_2_1, asN_2_2, asN_2_3, asN_2_4, AsSDzv2, Fin.cons_zero,
    Fin.cons_succ, Matrix.vecCons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_five]
  norm_num
  first | refl_ring1 | ring

theorem AsSDzv3_spec (w : R) (z : Fin 5 → R) :
    (∑ j, asN w 3 j * z j) = (∑ l, AsSDzv3 z l * w ^ (l:ℕ)) := by
  simp only [asN_3_0, asN_3_1, asN_3_2, asN_3_3, asN_3_4, AsSDzv3, Fin.cons_zero,
    Fin.cons_succ, Matrix.vecCons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_five]
  norm_num
  first | refl_ring1 | ring

theorem AsSDzv4_spec (w : R) (z : Fin 5 → R) :
    (∑ j, asN w 4 j * z j) = (∑ l, AsSDzv4 z l * w ^ (l:ℕ)) := by
  simp only [asN_4_0, asN_4_1, asN_4_2, asN_4_3, asN_4_4, AsSDzv4, Fin.cons_zero,
    Fin.cons_succ, Matrix.vecCons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_five]
  norm_num
  first | refl_ring1 | ring

theorem asSDsq (g w : R) (hw : w ^ 5 = w + g) (A : Fin 5 → R) :
    (∑ l, A l * w ^ (l:ℕ)) ^ 2 = ∑ l, redMul g A A l * w ^ (l:ℕ) := by
  rw [pow_two, redMul_spec g w hw A A]

theorem asSDcube (g w : R) (hw : w ^ 5 = w + g) (A : Fin 5 → R) :
    (∑ l, A l * w ^ (l:ℕ)) ^ 3 = ∑ l, redMul g (redMul g A A) A l * w ^ (l:ℕ) := by
  have h : (∑ l, A l * w ^ (l:ℕ)) ^ 3
      = (∑ l, A l * w ^ (l:ℕ)) ^ 2 * (∑ l, A l * w ^ (l:ℕ)) := by ring
  rw [h, asSDsq g w hw A, redMul_spec g w hw (redMul g A A) A]

theorem asSD4 (g w : R) (hw : w ^ 5 = w + g) (A : Fin 5 → R) :
    (∑ l, A l * w ^ (l:ℕ)) ^ 4
      = ∑ l, redMul g (redMul g (redMul g A A) A) A l * w ^ (l:ℕ) := by
  have h : (∑ l, A l * w ^ (l:ℕ)) ^ 4
      = (∑ l, A l * w ^ (l:ℕ)) ^ 3 * (∑ l, A l * w ^ (l:ℕ)) := by ring
  rw [h, asSDcube g w hw A, redMul_spec g w hw (redMul g (redMul g A A) A) A]

theorem asSD5 (g w : R) (hw : w ^ 5 = w + g) (A : Fin 5 → R) :
    (∑ l, A l * w ^ (l:ℕ)) ^ 5
      = ∑ l, redMul g (redMul g (redMul g (redMul g A A) A) A) A l * w ^ (l:ℕ) := by
  have h : (∑ l, A l * w ^ (l:ℕ)) ^ 5
      = (∑ l, A l * w ^ (l:ℕ)) ^ 4 * (∑ l, A l * w ^ (l:ℕ)) := by ring
  rw [h, asSD4 g w hw A, redMul_spec g w hw (redMul g (redMul g (redMul g A A) A) A) A]

theorem asSDt3 (g w : R) (hw : w ^ 5 = w + g) (A B Cc : Fin 5 → R) :
    (∑ l, A l * w ^ (l:ℕ)) * ((∑ l, B l * w ^ (l:ℕ)) * (∑ l, Cc l * w ^ (l:ℕ)))
      = ∑ l, redMul g A (redMul g B Cc) l * w ^ (l:ℕ) := by
  rw [redMul_spec g w hw B Cc, redMul_spec g w hw A (redMul g B Cc)]

theorem asSDt5 (g w : R) (hw : w ^ 5 = w + g) (A B Cc D E : Fin 5 → R) :
    (∑ l, A l * w ^ (l:ℕ)) *
        ((∑ l, B l * w ^ (l:ℕ)) *
          ((∑ l, Cc l * w ^ (l:ℕ)) * ((∑ l, D l * w ^ (l:ℕ)) * (∑ l, E l * w ^ (l:ℕ)))))
      = ∑ l, redMul g A (redMul g B (redMul g Cc (redMul g D E))) l * w ^ (l:ℕ) := by
  rw [redMul_spec g w hw D E, redMul_spec g w hw Cc (redMul g D E),
    redMul_spec g w hw B (redMul g Cc (redMul g D E)),
    redMul_spec g w hw A (redMul g B (redMul g Cc (redMul g D E)))]

end Work.MotAS
