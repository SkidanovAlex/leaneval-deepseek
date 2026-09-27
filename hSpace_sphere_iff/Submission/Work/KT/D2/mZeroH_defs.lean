import Mathlib
import Submission.Work.KT.D2.mZero
import Submission.Work.KT.D2.blk_det_ne_zero

/-!
# `Work.KT.D2.mZeroH_defs` — interface for the non-vanishing of `mZero` on the Bott class

The disc model of `K̃(S²)` is `Kpair ℝ² = C(D²/S¹)`.  The Bott class is `PA` (the disc-model Hopf
idempotent), whose boundary value is the constant rank-one projection `e0M = diag(1,0)`.  Its
winding invariant `mZero y0 hy0 PA` is the winding of the boundary loop

`x ↦ det (e0M * mZeroH_U y0 (inBall x) * e0M + (1 - e0M)) = mZeroH_U y0 (inBall x) 0 0`,

where `mZeroH_U y0` is a continuous family of units on the disc trivialising `PA` to its boundary
value (`trivU y0 PA PA_idem`; the companion inverse family is `mZeroH_V y0 = trivV y0 PA PA_idem`).

This file collects the `2 × 2` linear algebra, the interface definitions, and the bookkeeping that
identifies `mZero y0 hy0 PA` with the winding of that boundary loop.
-/

set_option maxHeartbeats 1000000

namespace Work.KT.D2

open Matrix
open Classical

noncomputable section

/-! ## The rank-one projection `diag(1,0)` -/

/-- The rank-one projection `diag(1,0)`: the boundary value of the disc-model Hopf idempotent. -/
def e0M : Matrix (Fin 2) (Fin 2) ℂ := !![(1 : ℂ), 0; 0, 0]

lemma e0M_eq : e0M = !![(1 : ℂ), 0; 0, 0] := rfl

lemma e0M_idem : e0M * e0M = e0M := diag10_idem

/-- The `(0,0)` entry of a `2 × 2` matrix is the determinant of its block cut down by `e0M`. -/
lemma det_e0M_block (W : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix.det (e0M * W * e0M + (1 - e0M)) = W 0 0 := by
  rw [e0M_eq]
  have h01 : ¬ ((0 : Fin 2) = 1) := by decide
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.one_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply, reduceIte, h01, h10, if_false]
  ring

/-- The block of the identity matrix at `e0M` is the identity. -/
lemma e0M_block_one : e0M * 1 * e0M + (1 - e0M) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [e0M_eq, Matrix.mul_one, diag10_idem, add_sub_cancel]

/-- A `2 × 2` matrix commuting with `e0M` has vanishing off-diagonal entries. -/
lemma comm_e0M_offdiag (W : Matrix (Fin 2) (Fin 2) ℂ) (h : W * e0M = e0M * W) :
    W 0 1 = 0 ∧ W 1 0 = 0 := by
  rw [e0M_eq] at h
  constructor
  · have h01 := congrFun (congrFun h 0) 1
    simpa [Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.sum_univ_two, reduceIte, Fin.zero_eta] using h01.symm
  · have h10 := congrFun (congrFun h 1) 0
    simpa [Matrix.mul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.sum_univ_two, reduceIte, Fin.zero_eta] using h10

/-- For matrices with `W 0 1 = 0`, the `(0,0)` entry of the product is the product of the
`(0,0)` entries. -/
lemma mul_entry_eq (W W' : Matrix (Fin 2) (Fin 2) ℂ) (h : W 0 1 = 0) :
    (W * W') 0 0 = W 0 0 * W' 0 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h, zero_mul, add_zero]

/-! ## The two trivialising families of the Bott class -/

/-- The chosen trivialising family of the Bott class `PA` at `y0`, as a continuous family of
`2 × 2` matrices on the disc: `mZeroH_U y0 y * PA(y) = e0M * mZeroH_U y0 y`. -/
def mZeroH_U (y0 : Ball (Euc 2)) : C(Ball (Euc 2), Matrix (Fin 2) (Fin 2) ℂ) :=
  trivU y0 PA PA_idem

/-- The companion inverse family of `mZeroH_U`. -/
def mZeroH_V (y0 : Ball (Euc 2)) : C(Ball (Euc 2), Matrix (Fin 2) (Fin 2) ℂ) :=
  trivV y0 PA PA_idem

lemma mZeroH_U_mul_V (y0 : Ball (Euc 2)) (y : Ball (Euc 2)) :
    mZeroH_U y0 y * mZeroH_V y0 y = 1 :=
  (trivU_spec y0 PA PA_idem).1 y

lemma mZeroH_V_mul_U (y0 : Ball (Euc 2)) (y : Ball (Euc 2)) :
    mZeroH_V y0 y * mZeroH_U y0 y = 1 :=
  (trivU_spec y0 PA PA_idem).2.1 y

/-- The boundary value of the disc-model Hopf idempotent is `e0M`. -/
lemma mZeroH_bval_eq_e0M (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    bval 2 y0 PAM = e0M := by
  rw [bval]
  exact PAM_bdry y0 hy0

/-- On the boundary circle, `mZeroH_U` commutes with the boundary value `e0M` of `PA`. -/
lemma mZeroH_U_comm (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2))
    (x : Sph (Euc 2)) :
    mZeroH_U y0 (inBall x) * e0M = e0M * mZeroH_U y0 (inBall x) := by
  have h : mZeroH_U y0 (inBall x) * bval 2 y0 PAM
      = bval 2 y0 PAM * mZeroH_U y0 (inBall x) :=
    trivU_inBall_comm y0 hy0 PA PA_idem x
  rw [mZeroH_bval_eq_e0M y0 hy0] at h
  exact h

/-- The `(0,0)` entry of the boundary loop of `mZeroH_U` is nowhere zero. -/
lemma mZeroH_U_entry_ne (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    ∀ x, mZeroH_U y0 (inBall x) 0 0 ≠ 0 := by
  intro x
  have h := blk_det_ne_zero (e := e0M) (u := mZeroH_U y0 (inBall x))
    (v := mZeroH_V y0 (inBall x)) e0M_idem (mZeroH_U_comm y0 hy0 x)
    (mZeroH_U_mul_V y0 (inBall x)) (mZeroH_V_mul_U y0 (inBall x))
  rwa [det_e0M_block] at h

/-- The block determinant of the boundary loop of `mZeroH_U` is nowhere zero. -/
lemma mZeroH_U_ne (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    ∀ x, Matrix.det (e0M * ((mZeroH_U y0).comp inBallCM) x * e0M + (1 - e0M)) ≠ 0 := by
  intro x
  rw [det_e0M_block]
  exact mZeroH_U_entry_ne y0 hy0 x

/-- Replacing the boundary value `bval 2 y0 PAM` by `e0M` does not change a winding number. -/
lemma mZeroH_windLoop_bval_e0 (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2))
    (γ : C(Sph (Euc 2), Matrix (Fin 2) (Fin 2) ℂ))
    (h : ∀ x, Matrix.det (bval 2 y0 PAM * γ x * bval 2 y0 PAM + (1 - bval 2 y0 PAM)) ≠ 0)
    (h' : ∀ x, Matrix.det (e0M * γ x * e0M + (1 - e0M)) ≠ 0) :
    windLoop 2 (bval 2 y0 PAM) γ h = windLoop 2 e0M γ h' := by
  rw [windLoop_eq_degNZ, windLoop_eq_degNZ]
  refine wlmDegNZcongr ?_ h h'
  apply ContinuousMap.ext
  intro x
  simp only [wlmDet_apply]
  rw [mZeroH_bval_eq_e0M y0 hy0]

/-- **The winding invariant of the Bott class** is the winding of the boundary loop of the
trivialising family `mZeroH_U`. -/
theorem mZeroH_mZero_eq (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    mZero y0 hy0 PA = windLoop 2 e0M ((mZeroH_U y0).comp inBallCM) (mZeroH_U_ne y0 hy0) := by
  rw [mZero_of_idem y0 hy0 PA PA_idem]
  exact mZeroH_windLoop_bval_e0 y0 hy0 ((mZeroH_U y0).comp inBallCM) _ _

end

end Work.KT.D2
