import Mathlib
import Submission.Work.Fold.Basic
import Submission.Work.FoldInst.FoldPiece
import Submission.Work.FoldInst.fold_theta_coord
import Submission.Work.FoldInst.Qbar_geometry

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

open Matrix
open scoped Matrix

/-! ### The normalisation `N_F` is a Lorentz matrix preserving the upper sheet

`foldN2_lorentz` (the finite certificate) says that the integral matrix `2 N_F` satisfies
`(2N_F)ᵀ J (2N_F) = 4 J`; divided by `4` this is exactly `N_Fᵀ J N_F = J`, and the last diagonal
entry is `2 > 0`.  Hence `HypModel.mobiusKlein (foldNr i)` maps the Klein ball into the upper half
space model, in particular its height is positive.

The auxiliary lemmas live in a private-to-this-chapter namespace `FoldThetaOrthantAux` so that
their (very natural) names cannot collide with the work of the other parts of the chapter. -/

namespace FoldThetaOrthantAux

/-- The integer certificate rephrased with the scalar multiplication of matrices. -/
theorem foldN2_lorentz' (i : Fin 98) :
    (foldN2 i)ᵀ * J5 * foldN2 i = (4 : ℤ) • J5 := by
  rw [foldN2_lorentz]
  revert i
  decide

theorem foldN2_diag_last (i : Fin 98) : foldN2 i 4 4 = 4 := by revert i; decide

theorem J5_map_eq_J : J5.map (Int.castRingHom ℝ) = HypModel.J := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [J5, HypModel.J]

/-- **`N_F` is a Lorentz matrix preserving the upper sheet.** -/
theorem foldNr_isLorentz (i : Fin 98) : HypModel.IsLorentzMat (foldNr i) := by
  have hJ5 := J5_map_eq_J
  have h4 := foldN2_lorentz' i
  have hN44 := foldN2_diag_last i
  constructor
  · have hMM : ((foldN2 i).map (Int.castRingHom ℝ))ᵀ * HypModel.J *
        ((foldN2 i).map (Int.castRingHom ℝ)) = (4 : ℝ) • HypModel.J := by
      rw [show HypModel.J = J5.map (Int.castRingHom ℝ) from hJ5.symm, ← Matrix.transpose_map,
        ← Matrix.map_mul, ← Matrix.map_mul, h4,
        Matrix.map_smul' (Int.castRingHom ℝ) (4 : ℤ) J5 (fun a b => map_mul _ a b)]
      rw [hJ5]
      norm_num
    rw [foldNr, matR]
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul]
    rw [smul_smul, hMM, smul_smul]
    norm_num
  · rw [foldNr, matR]
    simp only [Matrix.smul_apply, Matrix.map_apply, Int.coe_castRingHom, hN44, smul_eq_mul]
    norm_num

end FoldThetaOrthantAux

/-- **The orthant property of the fold charts.**  For every point `x` of the closed piece
`Clift i r` of the fold chart of the class `i` and the sign index `r`, the chart value at `x` lies
in the closed orthant of the sign index `signVecNeg r`: the fold framework's `signVal` is `+1` on
`true`, while `foldPattern` uses `+1` on `false`, so the *complement* of `r` is the orthant index.

The proof is the coordinate identity `fold_theta_coord`
`√(1-‖y‖²)·(θ y) t = (if r t then -1 else 1)·slack(wall t)·H`: the slack is nonnegative because
`x.2.1 ∈ Q̄`, and the height `H = (mobiusKlein N_F (act k_r y)) 3` is positive because `N_F` is a
Lorentz matrix preserving the upper sheet (`foldNr_isLorentz`) and `act k_r y` stays in the ball.
Multiplying the identity by `(if r t then -1 else 1)` (whose square is `1`) gives the claim. -/
theorem fold_theta_orthant (i : Fin 98) (r : Fin (foldCodim i) → Bool) (x : Xbar) (hx : x ∈ Clift i r) : foldTheta i r x.2.1 ∈ Work.Fold.orthant (Work.Fold.signVecNeg r) := by
  rw [Work.Fold.mem_orthant_iff]
  intro j hj
  have hy : x.2.1 ∈ HypModel.ball := Qbar_subset_ball x.2.2
  have hy' : act (toG (foldKr i r)) x.2.1 ∈ HypModel.ball :=
    Qbar_subset_ball ((Qbar_act (toG (foldKr i r)) x.2.1).mpr x.2.2)
  have hH : 0 < (HypModel.mobiusKlein (foldNr i) (act (toG (foldKr i r)) x.2.1)) 3 :=
    HypModel.mobiusKlein_mem (FoldThetaOrthantAux.foldNr_isLorentz i) hy'
  have hslack : 0 ≤ sideSlack (foldWalls i r (⟨j.val, hj⟩ : Fin (foldCodim i))) x.2.1 :=
    x.2.2.1 _
  have hsqrt : 0 < Real.sqrt (1 - ‖x.2.1‖ ^ 2) := by
    refine Real.sqrt_pos.mpr ?_
    have h : ‖x.2.1‖ < 1 := hy
    nlinarith [norm_nonneg x.2.1]
  have hcoord := fold_theta_coord i r x.2.1 hy (⟨j.val, hj⟩ : Fin (foldCodim i))
  have hidx : (⟨(⟨j.val, hj⟩ : Fin (foldCodim i)).val, by
      have h := (⟨j.val, hj⟩ : Fin (foldCodim i)).isLt
      have h' := foldCodim_le i
      omega⟩ : Fin 4) = j := Fin.ext rfl
  rw [hidx] at hcoord
  have hsign : Work.Fold.signVal (Work.Fold.signVecNeg r) ⟨j.val, hj⟩
      = (if r (⟨j.val, hj⟩ : Fin (foldCodim i)) then (-1 : ℝ) else 1) := by
    simp only [Work.Fold.signVal, Work.Fold.signVecNeg]
    by_cases h : r (⟨j.val, hj⟩ : Fin (foldCodim i)) <;> simp [h]
  rw [hsign]
  set s : ℝ := (if r (⟨j.val, hj⟩ : Fin (foldCodim i)) then (-1 : ℝ) else 1) with hs_def
  have hs2 : s * s = 1 := by
    rw [hs_def]
    by_cases h : r (⟨j.val, hj⟩ : Fin (foldCodim i)) <;> simp [h]
  have h2 : Real.sqrt (1 - ‖x.2.1‖ ^ 2) * (s * (foldTheta i r x.2.1) j) =
      sideSlack (foldWalls i r (⟨j.val, hj⟩ : Fin (foldCodim i))) x.2.1
        * (HypModel.mobiusKlein (foldNr i) (act (toG (foldKr i r)) x.2.1)) 3 := by
    calc Real.sqrt (1 - ‖x.2.1‖ ^ 2) * (s * (foldTheta i r x.2.1) j)
        = s * (Real.sqrt (1 - ‖x.2.1‖ ^ 2) * (foldTheta i r x.2.1) j) := by ring
      _ = s * (s * sideSlack (foldWalls i r (⟨j.val, hj⟩ : Fin (foldCodim i))) x.2.1
            * (HypModel.mobiusKlein (foldNr i) (act (toG (foldKr i r)) x.2.1)) 3) := by
          rw [hcoord]
      _ = s * s * sideSlack (foldWalls i r (⟨j.val, hj⟩ : Fin (foldCodim i))) x.2.1
            * (HypModel.mobiusKlein (foldNr i) (act (toG (foldKr i r)) x.2.1)) 3 := by ring
      _ = sideSlack (foldWalls i r (⟨j.val, hj⟩ : Fin (foldCodim i))) x.2.1
            * (HypModel.mobiusKlein (foldNr i) (act (toG (foldKr i r)) x.2.1)) 3 := by
          rw [hs2, one_mul]
  have hkey : s * (foldTheta i r x.2.1) j =
      (sideSlack (foldWalls i r (⟨j.val, hj⟩ : Fin (foldCodim i))) x.2.1
        * (HypModel.mobiusKlein (foldNr i) (act (toG (foldKr i r)) x.2.1)) 3)
        / Real.sqrt (1 - ‖x.2.1‖ ^ 2) := by
    rw [eq_div_iff (ne_of_gt hsqrt),
      mul_comm (s * (foldTheta i r x.2.1) j) (Real.sqrt (1 - ‖x.2.1‖ ^ 2)), h2]
  rw [hkey]
  exact div_nonneg (mul_nonneg hslack (le_of_lt hH)) (le_of_lt hsqrt)

end Work.FoldInst
