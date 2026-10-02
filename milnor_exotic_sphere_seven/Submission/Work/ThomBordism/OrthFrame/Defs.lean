import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.ThomBordism.Grassmann.Grassmannian
import Submission.Work.ThomBordism.PontryaginThom.NormalData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The combined frame of a tangent and a normal frame

For an index `i = (a,S)` of the normal data of an embedding `V ↪ ℝ^{8+k}` we have two frames of
`Euc (8+k)`:

* the **tangent frame** `Work.ThomBordism.PontryaginThom.frame E.e (coverChart i) x : Fin 8 → Euc (8+k)`
  (a basis of the tangent plane `T_x`), and
* the **normal frame** `Work.Tubular.orthFrame E ND i x : Fin k → Euc (8+k)`
  (an orthonormal basis of the normal plane `ν_x = T_x^⊥`).

Their concatenation is a basis of the ambient space; this file fixes that object in the *sum
indexing* `Fin 8 ⊕ Fin k` (`pairFrame`), the matrix of its coordinates in the standard basis
(`pairMat`), and the sign of the determinant of that matrix (`pairSign`).  The mathematical content —
the multiplicativity of `pairSign` along an orthogonal decomposition, which turns the tangent and
normal orientation cocycles into one Čech coboundary — is `sign_det_pairMat` below.
-/

open scoped BigOperators

namespace Work.ThomBordism.OrthFrame

open Work.ThomBordism.PontryaginThom

noncomputable section

/-- The pair of a `Fin 8`-frame and a `Fin k`-frame, indexed by `Fin 8 ⊕ Fin k`. -/
def pairFrame {k : ℕ} (F : Fin 8 → Euc (8 + k)) (G : Fin k → Euc (8 + k)) :
    Fin 8 ⊕ Fin k → Euc (8 + k) :=
  Sum.elim F G

@[simp] theorem pairFrame_inl {k : ℕ} (F : Fin 8 → Euc (8 + k)) (G : Fin k → Euc (8 + k))
    (a : Fin 8) : pairFrame F G (Sum.inl a) = F a := rfl

@[simp] theorem pairFrame_inr {k : ℕ} (F : Fin 8 → Euc (8 + k)) (G : Fin k → Euc (8 + k))
    (b : Fin k) : pairFrame F G (Sum.inr b) = G b := rfl

open scoped BigOperators in
/-- **The coordinate matrix of the pair frame** in the standard basis of `Euc (8+k)`, with both
indices split as `Fin 8 ⊕ Fin k` (the rows through the standard identification
`finSumFinEquiv : Fin 8 ⊕ Fin k ≃ Fin (8+k)`): its `c`-th column holds the coordinates of the `c`-th
vector of the pair frame. -/
def pairMat {k : ℕ} (F : Fin 8 → Euc (8 + k)) (G : Fin k → Euc (8 + k)) :
    Matrix (Fin 8 ⊕ Fin k) (Fin 8 ⊕ Fin k) ℝ :=
  Matrix.of fun r c => eucToFun (8 + k) (pairFrame F G c) (finSumFinEquiv r)

@[simp] theorem pairMat_apply {k : ℕ} (F : Fin 8 → Euc (8 + k)) (G : Fin k → Euc (8 + k))
    (r c : Fin 8 ⊕ Fin k) :
    pairMat F G r c = eucToFun (8 + k) (pairFrame F G c) (finSumFinEquiv r) := rfl

@[simp] theorem pairMat_inl {k : ℕ} (F : Fin 8 → Euc (8 + k)) (G : Fin k → Euc (8 + k))
    (r : Fin 8 ⊕ Fin k) (a : Fin 8) :
    pairMat F G r (Sum.inl a) = eucToFun (8 + k) (F a) (finSumFinEquiv r) := rfl

@[simp] theorem pairMat_inr {k : ℕ} (F : Fin 8 → Euc (8 + k)) (G : Fin k → Euc (8 + k))
    (r : Fin 8 ⊕ Fin k) (b : Fin k) :
    pairMat F G r (Sum.inr b) = eucToFun (8 + k) (G b) (finSumFinEquiv r) := rfl

/-- **The sign of the determinant of the pair frame** in the standard basis of `Euc (8+k)`. -/
def pairSign {k : ℕ} (F : Fin 8 → Euc (8 + k)) (G : Fin k → Euc (8 + k)) : ℝ :=
  Real.sign (pairMat F G).det

/-- The sign is `±1` when the matrix is invertible. -/
theorem pairSign_eq_one_or {k : ℕ} (F : Fin 8 → Euc (8 + k)) (G : Fin k → Euc (8 + k))
    (h : (pairMat F G).det ≠ 0) : pairSign F G = 1 ∨ pairSign F G = -1 := by
  rcases lt_trichotomy (pairMat F G).det 0 with hlt | heq | hgt
  · exact Or.inr (Real.sign_of_neg hlt)
  · exact absurd heq h
  · exact Or.inl (Real.sign_of_pos hgt)

/-- A sign of a nonzero real number is a unit (its square is one). -/
theorem sign_mul_self_of_ne_zero {t : ℝ} (h : t ≠ 0) : Real.sign t * Real.sign t = 1 := by
  rcases lt_trichotomy t 0 with hlt | heq | hgt
  · rw [Real.sign_of_neg hlt]; norm_num
  · exact absurd heq h
  · rw [Real.sign_of_pos hgt]; norm_num

/-- `Real.sign` is multiplicative on nonzero reals. -/
theorem sign_mul_of_ne_zero {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) :
    Real.sign (s * t) = Real.sign s * Real.sign t := by
  rcases lt_trichotomy s 0 with hslt | hseq | hsgt
  · rcases lt_trichotomy t 0 with htlt | hteq | htgt
    · rw [Real.sign_of_neg hslt, Real.sign_of_neg htlt,
        Real.sign_of_pos (mul_pos_of_neg_of_neg hslt htlt)]; norm_num
    · exact absurd hteq ht
    · rw [Real.sign_of_neg hslt, Real.sign_of_pos htgt,
        Real.sign_of_neg (mul_neg_of_neg_of_pos hslt htgt)]; norm_num
  · exact absurd hseq hs
  · rcases lt_trichotomy t 0 with htlt | hteq | htgt
    · rw [Real.sign_of_pos hsgt, Real.sign_of_neg htlt,
        Real.sign_of_neg (mul_neg_of_pos_of_neg hsgt htlt)]; norm_num
    · exact absurd hteq ht
    · rw [Real.sign_of_pos hsgt, Real.sign_of_pos htgt,
        Real.sign_of_pos (mul_pos hsgt htgt)]; norm_num

end

end Work.ThomBordism.OrthFrame
