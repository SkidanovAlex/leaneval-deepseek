/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the determinant comparison of the
  Rolle step.

  The new system `E.newData y δ` has, at a crossing of the level set `{psiMap = y}` with
  `{rolleDetFun = δ}`, the same zero set as `(psiMap, rolleDetFun) = (y, δ)`.  This file compares
  the two Jacobian determinants: the rows of the Jacobian of `(E.newData y δ).map` are the rows of
  the Jacobian of `E.rolleMap`, cyclically shifted by `rowShiftFun` (the eliminated row `rt` moves
  to the last position) and with the Rolle row scaled by `E.prodEval z`; hence

  `det (jac (newData y δ)) = prodEval z · sign (rowShift) · det (fderiv rolleMap z)`.

  Consequently a regular point of `(psiMap, rolleDetFun) = (y, δ)` is a nondegenerate zero of the
  new system.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.ContAux
import Submission.Work.WilE3K.evalPoly_rolleDetP
import Submission.Work.WilE3K.contDiff_map_and_det
import Submission.Work.WilE3K.rolleDetFun_crossField
import Submission.Work.WilE3K.ETRolle.IndexBook
import Submission.Work.WilE3K.ETRolle.LevelSet
import Submission.Work.WilE2.fderiv_graphMap_det
import Submission.Work.WilE2.tangentField_exists

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re : ℕ}

/-! ## §1. The row reindexing of the Rolle step -/

/-- The cyclic shift of the block `{rt, …, N}` on natural values. -/
def rowShiftVal (h : rt + 1 + n = N + 1) (v : ℕ) : ℕ :=
  if v < rt then v else if v = rt then N else v - 1

/-- Its inverse on natural values. -/
def rowShiftInvVal (h : rt + 1 + n = N + 1) (v : ℕ) : ℕ :=
  if v < rt then v else if v = N then rt else v + 1

theorem rowShiftVal_lt (h : rt + 1 + n = N + 1) (v : ℕ) (hv : v < N + 1) :
    rowShiftVal h v < N + 1 := by
  unfold rowShiftVal
  split_ifs <;> omega

theorem rowShiftInvVal_lt (h : rt + 1 + n = N + 1) (v : ℕ) (hv : v < N + 1) :
    rowShiftInvVal h v < N + 1 := by
  unfold rowShiftInvVal
  split_ifs <;> omega

/-- The row reindexing of the Rolle step as a map of `Fin (N+1)`. -/
def rowShiftFun (h : rt + 1 + n = N + 1) (r : Fin (N + 1)) : Fin (N + 1) :=
  ⟨rowShiftVal h r.val, rowShiftVal_lt h r.val r.isLt⟩

/-- Its inverse. -/
def rowShiftInvFun (h : rt + 1 + n = N + 1) (s : Fin (N + 1)) : Fin (N + 1) :=
  ⟨rowShiftInvVal h s.val, rowShiftInvVal_lt h s.val s.isLt⟩

theorem rowShift_val {N rt n : ℕ} (h : rt + 1 + n = N + 1) (r : Fin (N + 1)) :
    (rowShiftFun h r : ℕ) = rowShiftVal h r.val := rfl

theorem rowShiftVal_inv (h : rt + 1 + n = N + 1) (v : ℕ) (hv : v < N + 1) :
    rowShiftInvVal h (rowShiftVal h v) = v := by
  unfold rowShiftVal rowShiftInvVal
  split_ifs <;> omega

theorem rowShiftVal_left (h : rt + 1 + n = N + 1) (v : ℕ) (hv : v < N + 1) :
    rowShiftVal h (rowShiftInvVal h v) = v := by
  unfold rowShiftVal rowShiftInvVal
  split_ifs <;> omega

theorem rowShiftLeftInverse (h : rt + 1 + n = N + 1) :
    Function.LeftInverse (rowShiftInvFun h) (rowShiftFun h) := by
  intro r
  refine Fin.ext ?_
  show rowShiftInvVal h (rowShiftVal h r.val) = r.val
  exact rowShiftVal_inv h r.val r.isLt

theorem rowShiftRightInverse (h : rt + 1 + n = N + 1) :
    Function.RightInverse (rowShiftInvFun h) (rowShiftFun h) := by
  intro r
  refine Fin.ext ?_
  show rowShiftVal h (rowShiftInvVal h r.val) = r.val
  exact rowShiftVal_left h r.val r.isLt

/-- The row reindexing as an equivalence of `Fin (N+1)`. -/
def rowPerm (h : rt + 1 + n = N + 1) : Equiv.Perm (Fin (N + 1)) where
  toFun := rowShiftFun h
  invFun := rowShiftInvFun h
  left_inv := rowShiftLeftInverse h
  right_inv := rowShiftRightInverse h

namespace ETData

variable (E : ETData N (rt + 1) n re)

theorem rowShiftFun_lt (r : Fin (N + 1)) (hr : (r : ℕ) < rt) :
    rowShiftFun E.h r = r := by
  refine Fin.ext ?_
  show rowShiftVal E.h r.val = r.val
  unfold rowShiftVal
  rw [if_pos hr]

theorem rowShiftFun_eq (r : Fin (N + 1)) (hr : (r : ℕ) = rt) :
    rowShiftFun E.h r = Fin.last N := by
  refine Fin.ext ?_
  show rowShiftVal E.h r.val = N
  unfold rowShiftVal
  rw [if_neg (by omega), if_pos hr]

theorem rowShiftFun_gt (r : Fin (N + 1)) (hr : rt < (r : ℕ)) :
    rowShiftFun E.h r = ⟨(r : ℕ) - 1, by have h := E.h; omega⟩ := by
  refine Fin.ext ?_
  show rowShiftVal E.h r.val = r.val - 1
  unfold rowShiftVal
  rw [if_neg (by omega), if_neg (by omega)]

/-! ## §2. The rows of the two Jacobians -/

theorem rolleMap_fun_lt (z : Fin (N + 1) → ℝ) (r : Fin (N + 1)) (hr : (r : ℕ) < N) :
    E.rolleMap z r = E.psiMap z ⟨(r : ℕ), hr⟩ := by
  simp only [ETData.rolleMap, dif_pos hr]

theorem rolleMap_fun_last (z : Fin (N + 1) → ℝ) :
    E.rolleMap z (Fin.last N) = E.rolleDetFun z := by
  have h : ((Fin.last N : Fin (N + 1)) : ℕ) = N := by simp
  simp only [ETData.rolleMap]
  rw [dif_neg (by rw [h]; exact Nat.lt_irrefl N)]

/-- The new system's map at a coordinate `r < rt` is the `r`-th coordinate of `psiMap`, shifted
by the level value. -/
theorem newData_map_fun_lt (y : Fin N → ℝ) (δ : ℝ) (r : Fin (N + 1)) (hr : (r : ℕ) < rt) :
    (fun w => (E.newData y δ).map w r)
      = fun w => E.psiMap w ⟨(r : ℕ), by have h := E.h; omega⟩
          - y ⟨(r : ℕ), by have h := E.h; omega⟩ := by
  funext w
  have hpsi : E.psiMap w (⟨(r : ℕ), by have h := E.h; omega⟩ : Fin N)
      = E.tanFun (Fin.castSucc (⟨(r : ℕ), by omega⟩ : Fin rt)) w := by
    rw [show (⟨(r : ℕ), by have h := E.h; omega⟩ : Fin N)
        = Fin.castLE (by have h := E.h; omega) (⟨(r : ℕ), by omega⟩ : Fin rt) from Fin.ext rfl]
    rw [E.psiMap_apply_tan]
  rw [ETData.map, dif_pos hr]
  rw [show (E.newData y δ).tanIndex r hr
      = (⟨(r : ℕ), by omega⟩ : Fin rt) from Fin.ext rfl]
  rw [E.newData_tanFun y δ _ (by have h := E.h; omega) w, hpsi]

/-- The new system's map at a coordinate `rt < r` is the `(r-1)`-th coordinate of `psiMap`,
shifted by the level value. -/
theorem newData_map_fun_gt (y : Fin N → ℝ) (δ : ℝ) (r : Fin (N + 1)) (hr : rt < (r : ℕ)) :
    (fun w => (E.newData y δ).map w r)
      = fun w => E.psiMap w ⟨(r : ℕ) - 1, by have h := E.h; omega⟩
          - y ⟨(r : ℕ) - 1, by have h := E.h; omega⟩ := by
  have hrt : ¬ (r : ℕ) < rt := by omega
  set k : Fin n := ⟨(r : ℕ) - rt - 1, by have h := E.h; omega⟩ with hk
  have hidx : (E.newData y δ).freeIndex r (not_lt.mp hrt) = k.succ :=
    Fin.ext (by simp only [ETData.freeIndex, Fin.val_succ, hk]; omega)
  funext w
  rw [ETData.map, dif_neg hrt, hidx, E.newData_evP_succ y δ k w]
  have hpsi : E.psiMap w ⟨(r : ℕ) - 1, by have h := E.h; omega⟩ = E.evP k w := by
    rw [show (⟨(r : ℕ) - 1, by have h := E.h; omega⟩ : Fin N)
        = Fin.castLE (by have h := E.h; omega) (Fin.natAdd rt k) from
      Fin.ext (by simp only [Fin.val_castLE, Fin.val_natAdd, hk]; omega)]
    rw [E.psiMap_apply_free]
  rw [hpsi]
  congr 1
  exact congrArg y (Fin.ext (by simp only [Fin.val_succ, hk]; omega))

/-- The new system's map at the eliminated coordinate `rt` is the Rolle equation. -/
theorem newData_map_fun_lastRow (y : Fin N → ℝ) (δ : ℝ) :
    (fun w => (E.newData y δ).map w E.lastRow)
      = fun w => E.evalPoly (E.rolleDetP - MvPolynomial.C δ * E.prodPoly) w := by
  have hidx : (E.newData y δ).freeIndex E.lastRow (by simp [ETData.lastRow]) = 0 := by
    refine Fin.ext ?_
    simp only [ETData.freeIndex, ETData.lastRow, Fin.val_zero]
    omega
  funext w
  rw [ETData.map, dif_neg (by simp [ETData.lastRow])]
  rw [show (E.newData y δ).evP ((E.newData y δ).freeIndex E.lastRow
      (by simp [ETData.lastRow])) w = (E.newData y δ).evP 0 w from by rw [hidx]]
  exact E.newData_evP_zero y δ w

/-! ## §3. The Jacobian determinant of the new system -/

/-- The Rolle equation, as a function of the point, is the product of the scaling factor with
`rolleDetFun - δ`. -/
theorem evalPoly_rolleDetP_sub_eq (y : Fin N → ℝ) (δ : ℝ) (w : Fin (N + 1) → ℝ) :
    E.evalPoly (E.rolleDetP - MvPolynomial.C δ * E.prodPoly) w
      = E.prodEval w * (E.rolleDetFun w - δ) := by
  rw [E.evalPoly_sub, E.evalPoly_mul, E.evalPoly_C, E.evalPoly_prodPoly, evalPoly_rolleDetP E w,
    ← E.rolleDetFun_eq_jac_det w]
  ring

theorem differentiableAt_prodEval (z : Fin (N + 1) → ℝ) :
    DifferentiableAt ℝ (fun w => E.prodEval w) z := by
  rw [show (fun w => E.prodEval w) = fun w => E.evalPoly E.prodPoly w from
    funext fun w => (E.evalPoly_prodPoly w).symm]
  exact ((Work.WilE3K.ETData.rcF_contDiff_evalPoly E E.prodPoly).differentiable (by norm_num)).differentiableAt

/-- The value of the eliminated row index. -/
theorem lastRow_val : ((E.lastRow : Fin (N + 1)) : ℕ) = rt := rfl

theorem lastRow_ne_of_lt {r : Fin (N + 1)} (h : (r : ℕ) < rt) : r ≠ E.lastRow := by
  intro hh
  have hval : (r : ℕ) = rt := by rw [hh, E.lastRow_val]
  omega

theorem lastRow_ne_of_gt {r : Fin (N + 1)} (h : rt < (r : ℕ)) : r ≠ E.lastRow := by
  intro hh
  have hval : (r : ℕ) = rt := by rw [hh, E.lastRow_val]
  omega

theorem eq_lastRow_of_val {r : Fin (N + 1)} (h : (r : ℕ) = rt) : r = E.lastRow := by
  refine Fin.ext ?_
  rw [h, E.lastRow_val]

theorem differentiableAt_rolleDetFun (z : Fin (N + 1) → ℝ) :
    DifferentiableAt ℝ E.rolleDetFun z := by
  have h : DifferentiableAt ℝ E.rolleMap z :=
    (Work.WilE3K.rolleDetFun_crossField E).1.differentiable (by norm_num) z
  have h2 : DifferentiableAt ℝ (fun w => E.rolleMap w (Fin.last N)) z :=
    (differentiableAt_pi.mp h) (Fin.last N)
  rwa [show (fun w => E.rolleMap w (Fin.last N)) = E.rolleDetFun from
    funext fun w => E.rolleMap_fun_last w] at h2

/-- The fderiv of the Rolle equation at a point where `rolleDetFun = δ`: the scaling factor times
the fderiv of `rolleDetFun`. -/
theorem fderiv_rolleDetP_sub (y : Fin N → ℝ) (δ : ℝ) (z : Fin (N + 1) → ℝ)
    (h2 : E.rolleDetFun z = δ) :
    fderiv ℝ (fun w => E.evalPoly (E.rolleDetP - MvPolynomial.C δ * E.prodPoly) w) z
      = E.prodEval z • fderiv ℝ E.rolleDetFun z := by
  have hfun : (fun w => E.evalPoly (E.rolleDetP - MvPolynomial.C δ * E.prodPoly) w)
      = fun w => E.prodEval w * (E.rolleDetFun w - δ) :=
    funext fun w => E.evalPoly_rolleDetP_sub_eq y δ w
  have hfun2 : (fun w => E.prodEval w * (E.rolleDetFun w - δ))
      = (fun w => E.prodEval w) * (fun w => E.rolleDetFun w - δ) := rfl
  rw [hfun, hfun2]
  have h1 : HasFDerivAt (fun w => E.prodEval w) (fderiv ℝ (fun w => E.prodEval w) z) z :=
    (E.differentiableAt_prodEval z).hasFDerivAt
  have h2' : HasFDerivAt (fun w => E.rolleDetFun w - δ) (fderiv ℝ E.rolleDetFun z) z := by
    simpa using (E.differentiableAt_rolleDetFun z).hasFDerivAt.sub_const δ
  have hmain := (h1.mul h2').fderiv
  simpa only [h2, sub_self, zero_smul, add_zero] using hmain

/-! ## §3b. The row comparison -/

/-- **The rows of the new system and of `rolleMap`.**  The `r`-th row of the Jacobian of the new
system is the row `rowShiftFun r` of the Jacobian of `E.rolleMap`, scaled by `E.prodEval z` on the
Rolle row (`r = lastRow`). -/
theorem newData_map_row_eq (y : Fin N → ℝ) (δ : ℝ) (z : Fin (N + 1) → ℝ)
    (h2 : E.rolleDetFun z = δ) (r c : Fin (N + 1)) :
    fderiv ℝ (fun w => (E.newData y δ).map w r) z (Pi.single c 1)
      = (if r = E.lastRow then E.prodEval z else 1)
        * fderiv ℝ (fun w => E.rolleMap w (rowShiftFun E.h r)) z (Pi.single c 1) := by
  by_cases hlt : (r : ℕ) < rt
  · have hrN : (r : ℕ) < N := by have h := E.h; omega
    have hne' : r ≠ E.lastRow := E.lastRow_ne_of_lt hlt
    rw [E.rowShiftFun_lt r hlt, if_neg hne', one_mul, E.newData_map_fun_lt y δ r hlt,
      fderiv_sub_const]
    congr 1
    congr 1
    funext w
    rw [E.rolleMap_fun_lt w r hrN]
  · by_cases heq : (r : ℕ) = rt
    · have heqr : r = E.lastRow := E.eq_lastRow_of_val heq
      rw [heqr]
      rw [E.rowShiftFun_eq E.lastRow E.lastRow_val, if_pos rfl]
      rw [E.newData_map_fun_lastRow y δ]
      rw [show (fun w => E.rolleMap w (Fin.last N)) = E.rolleDetFun from
        funext fun w => E.rolleMap_fun_last w]
      exact congrArg (fun L => L (Pi.single c 1)) (E.fderiv_rolleDetP_sub y δ z h2)
    · have hgt : rt < (r : ℕ) := by omega
      have hne' : r ≠ E.lastRow := E.lastRow_ne_of_gt hgt
      rw [E.rowShiftFun_gt r hgt, if_neg hne', one_mul, E.newData_map_fun_gt y δ r hgt,
        fderiv_sub_const]
      congr 1
      congr 1
      funext w
      exact (E.rolleMap_fun_lt w ⟨(r : ℕ) - 1, by have h := E.h; omega⟩
        (by show (r : ℕ) - 1 < N; have h := E.h; omega)).symm

theorem differentiableAt_rolleMap (z : Fin (N + 1) → ℝ) :
    DifferentiableAt ℝ E.rolleMap z :=
  (Work.WilE3K.rolleDetFun_crossField E).1.differentiable (by norm_num) z

/-! ## §4. The Jacobian determinant of the new system and its nondegeneracy -/

/-- **The determinant of the new system's Jacobian.**  It is the determinant of the fderiv of
`E.rolleMap`, multiplied by the scaling factor `E.prodEval z` and by the sign of the row
reindexing `rowPerm`. -/
theorem newData_jac_det_eq (y : Fin N → ℝ) (δ : ℝ) (z : Fin (N + 1) → ℝ)
    (h2 : E.rolleDetFun z = δ) :
    ((E.newData y δ).jac z).det
      = E.prodEval z * (↑↑(Equiv.Perm.sign (rowPerm E.h)) : ℝ)
          * (fderiv ℝ E.rolleMap z).det := by
  set A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    Matrix.of fun r c => fderiv ℝ (fun w => (E.newData y δ).map w r) z (Pi.single c 1) with hA
  set B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
    Matrix.of fun r c => fderiv ℝ (fun w => E.rolleMap w r) z (Pi.single c 1) with hB
  have hjac : (E.newData y δ).jac z = A := by
    rw [hA]
    exact ETData.rcF_jac_eq_fderiv (E.newData y δ) z
  have hrow : A = Matrix.diagonal (fun r => if r = E.lastRow then E.prodEval z else 1)
      * (B.submatrix (rowPerm E.h) id) := by
    ext r c
    simp only [hA, Matrix.of_apply, Matrix.diagonal_mul, Matrix.submatrix_apply]
    exact E.newData_map_row_eq y δ z h2 r c
  have hBdet : B.det = (fderiv ℝ E.rolleMap z).det := by
    rw [Work.WilE2.det_eq_det_coord (fderiv ℝ E.rolleMap z)]
    rw [← Matrix.det_transpose B]
    congr 1
    ext i j
    simp only [hB, Matrix.transpose_apply, Matrix.of_apply]
    rw [fderiv_apply (E.differentiableAt_rolleMap z) j]
    rfl
  have hprod : (∏ r : Fin (N + 1), (if r = E.lastRow then E.prodEval z else 1))
      = E.prodEval z := by
    rw [Finset.prod_eq_single E.lastRow]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ E.lastRow) h
  rw [hjac, hrow, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute, hprod, hBdet]
  ring

/-- **Nondegenerate zeros of the new system.**  Every point of the level set `{psiMap = y}` at which
the Rolle determinant takes the value `δ` and which is a regular point of `E.rolleMap` is a
nondegenerate zero of the new system `E.newData y δ`. -/
theorem newData_nondegen_of_rolleMap (y : Fin N → ℝ) (δ : ℝ) (z : Fin (N + 1) → ℝ)
    (h1 : E.psiMap z = y) (h2 : E.rolleDetFun z = δ)
    (h3 : (fderiv ℝ E.rolleMap z).det ≠ 0) :
    (E.newData y δ).Nondegen z := by
  refine ⟨E.newData_evP_eq_zero y δ z h1 h2, E.newData_tanFun_eq_zero y δ z h1, ?_⟩
  rw [E.newData_jac_det_eq y δ z h2]
  refine mul_ne_zero (mul_ne_zero (ne_of_gt (E.prodEval_pos z)) ?_) h3
  have h1' : ((↑(Equiv.Perm.sign (rowPerm E.h)) : ℤ) : ℝ) ≠ 0 := by
    have := Units.ne_zero (Equiv.Perm.sign (rowPerm E.h))
    exact_mod_cast this
  exact h1'

end ETData

end Work.WilE3K
