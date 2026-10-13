/-
  Area E3, API layer: `detOp` is a first-order differential operator with real coefficients.

  `detOp c h ι l f = det (∂_{ι b} / ∂_l applied to the rows h, f)` is the determinant of the
  `(j+1) × (j+1)` matrix whose rows are `h₁ … hⱼ, f` and whose columns are the derivatives
  `∂_{ι 1}, …, ∂_{ι j}, ∂_l` (GV survey Def. 4.6).  As a function of the last row `f` it is

  * additive,  * real-homogeneous,  * and satisfies the Leibniz rule,

  i.e. a derivation on `EAPoly k r`.  This is exactly what the `detOp`-calculus of area E3
  (Taylor closure of the multiplicity identity, `E3_identity`/`E3_taylor_closure`) uses to
  treat `detOp c h ι l` as a first order operator.

  Proof.  Write `rvec f : Fin (j+1) → EAPoly k r` for the row vector `b ↦ ∂_{lastCases l ι b} f`.
  The defining matrix of `detOp c h ι l f` agrees, except in its last row, with the fixed matrix
  `M = detOpAux_mat c h ι l 0` (`detOpAux_mat_updateRow`), whose last row is `rvec f`.  Hence
  `detOp c h ι l f = (M.updateRow last (rvec f)).det` (`detOpAux_key`), and the three claims
  follow from multilinearity of the determinant in one row (`Matrix.det_updateRow_add`,
  `Matrix.det_updateRow_smul`) applied to `rvec (Q + Q') = rvec Q + rvec Q'`,
  `rvec (Q * Q') = Q' • rvec Q + Q • rvec Q'` and `rvec (C a) = 0`.  The latter are the
  additivity/Leibniz rule of the frozen symbolic derivative `eaD`, proved here from
  `MvPolynomial.pderiv_add`/`MvPolynomial.pderiv_mul`.
-/
import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3.API

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

noncomputable section

/-! ## §1. The frozen derivative `eaD` is additive and Leibniz -/

theorem detOpAux_eaD_add {k r : ℕ} (c : EAChain k r) (i : Fin k) (Q Q' : EAPoly k r) :
    eaD c i (Q + Q') = eaD c i Q + eaD c i Q' := by
  simp only [eaD, map_add, mul_add, Finset.sum_add_distrib]
  ac_rfl

theorem detOpAux_eaD_C {k r : ℕ} (c : EAChain k r) (i : Fin k) (a : ℝ) :
    eaD c i (MvPolynomial.C a) = 0 := by
  simp [eaD]

theorem detOpAux_eaD_mul {k r : ℕ} (c : EAChain k r) (i : Fin k) (P Q : EAPoly k r) :
    eaD c i (P * Q) = eaD c i P * Q + P * eaD c i Q := by
  have key : ∀ (u v : EAPoly k r),
      (∑ j : Fin r, MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
          MvPolynomial.pderiv (Sum.inr j) (u * v)) =
      (∑ j : Fin r, MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
          MvPolynomial.pderiv (Sum.inr j) u) * v +
      u * (∑ j : Fin r, MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) *
          MvPolynomial.pderiv (Sum.inr j) v) := by
    intro u v
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.pderiv_mul]
    ring
  have hp : MvPolynomial.pderiv (Sum.inl i) (P * Q) =
      MvPolynomial.pderiv (Sum.inl i) P * Q + P * MvPolynomial.pderiv (Sum.inl i) Q :=
    MvPolynomial.pderiv_mul
  rw [eaD, eaD, eaD, hp, key P Q]
  ring

/-! ## §2. The matrix underlying `detOp` and its last row -/

/-- The column derivatives of `detOp`, applied to one polynomial: the row vector
`b ↦ ∂_{lastCases l ι b} f`. -/
def detOpAux_row {k r j : ℕ} (c : EAChain k r) (ι : Fin j → Fin k) (l : Fin k)
    (f : EAPoly k r) : Fin (j + 1) → EAPoly k r :=
  fun b => eaD c (Fin.lastCases l ι b) f

/-- The matrix of `detOp c h ι l`: rows `h₁ … hⱼ, f`, columns `∂_{ι 1} … ∂_{ι j}, ∂_l`. -/
def detOpAux_mat {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (f : EAPoly k r) : Matrix (Fin (j + 1)) (Fin (j + 1)) (EAPoly k r) :=
  Matrix.of fun (a b : Fin (j + 1)) => eaD c (Fin.lastCases l ι b) (Fin.lastCases f h a)

/-- `detOp` is the determinant of `detOpAux_mat`. -/
theorem detOpAux_mat_detOp {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (f : EAPoly k r) :
    detOp c h ι l f = (detOpAux_mat c h ι l f).det := rfl

/-- `detOpAux_mat c h ι l f` differs from the fixed matrix `detOpAux_mat c h ι l 0` only in its
last row, which is the row vector `detOpAux_row c ι l f`. -/
theorem detOpAux_mat_updateRow {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (f : EAPoly k r) :
    detOpAux_mat c h ι l f =
      (detOpAux_mat c h ι l 0).updateRow (Fin.last j) (detOpAux_row c ι l f) := by
  apply Matrix.ext
  intro a b
  rw [Matrix.updateRow_apply]
  by_cases ha : a = Fin.last j
  · subst ha; simp [detOpAux_mat, detOpAux_row]
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last ha
    simp [detOpAux_mat, Fin.ne_of_lt i.castSucc_lt_last]

/-- `detOp c h ι l f` is the determinant of a matrix whose last row is `detOpAux_row c ι l f`,
all other rows being independent of `f`. -/
theorem detOpAux_key {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) :
    ∀ f : EAPoly k r, detOp c h ι l f =
      (Matrix.updateRow (detOpAux_mat c h ι l 0) (Fin.last j) (detOpAux_row c ι l f)).det :=
  fun f => (detOpAux_mat_detOp c h ι l f).trans
    (congrArg Matrix.det (detOpAux_mat_updateRow c h ι l f))

/-! ## §3. Additivity, homogeneity and Leibniz rule for `detOp` -/

theorem detOpAux_add {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (Q Q' : EAPoly k r) :
    detOp c h ι l (Q + Q') = detOp c h ι l Q + detOp c h ι l Q' := by
  have hrow : detOpAux_row c ι l (Q + Q') = detOpAux_row c ι l Q + detOpAux_row c ι l Q' := by
    funext b
    exact detOpAux_eaD_add c _ Q Q'
  rw [detOpAux_key c h ι l (Q + Q'), hrow, Matrix.det_updateRow_add,
    ← detOpAux_key c h ι l Q, ← detOpAux_key c h ι l Q']

theorem detOpAux_mul {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (Q Q' : EAPoly k r) :
    detOp c h ι l (Q * Q') = detOp c h ι l Q * Q' + Q * detOp c h ι l Q' := by
  have hrow : detOpAux_row c ι l (Q * Q') = Q' • detOpAux_row c ι l Q + Q • detOpAux_row c ι l Q' := by
    funext b
    simp only [detOpAux_row, Pi.add_apply, Pi.smul_apply, smul_eq_mul, detOpAux_eaD_mul]
    ring
  rw [detOpAux_key c h ι l (Q * Q'), hrow, Matrix.det_updateRow_add,
    Matrix.det_updateRow_smul, Matrix.det_updateRow_smul,
    ← detOpAux_key c h ι l Q, ← detOpAux_key c h ι l Q']
  ring

/-- `detOp` kills the constants. -/
theorem detOpAux_C {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (a : ℝ) :
    detOp c h ι l (MvPolynomial.C a) = 0 := by
  rw [detOpAux_key c h ι l (MvPolynomial.C a)]
  apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last j)
  intro b
  rw [Matrix.updateRow_self]
  simp only [detOpAux_row]
  exact detOpAux_eaD_C c _ a

theorem detOpAux_smul {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) (a : ℝ) (Q : EAPoly k r) :
    detOp c h ι l (a • Q) = a • detOp c h ι l Q := by
  rw [MvPolynomial.smul_eq_C_mul, detOpAux_mul c h ι l (MvPolynomial.C a) Q,
    detOpAux_C c h ι l a, zero_mul, zero_add, ← MvPolynomial.smul_eq_C_mul]

theorem detOp_linear_derivation {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (l : Fin k) :
    (∀ Q Q' : EAPoly k r, detOp c h ι l (Q + Q') = detOp c h ι l Q + detOp c h ι l Q') ∧
    (∀ (a : ℝ) (Q : EAPoly k r), detOp c h ι l (a • Q) = a • detOp c h ι l Q) ∧
    (∀ Q Q' : EAPoly k r,
      detOp c h ι l (Q * Q') = detOp c h ι l Q * Q' + Q * detOp c h ι l Q') :=
  ⟨fun Q Q' => detOpAux_add c h ι l Q Q',
   fun a Q => detOpAux_smul c h ι l a Q,
   fun Q Q' => detOpAux_mul c h ι l Q Q'⟩

end

end Work.WilE3.API
