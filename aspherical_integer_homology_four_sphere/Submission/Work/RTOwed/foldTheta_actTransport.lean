import Mathlib
import Submission.Work.RTOwed.Defs
import Submission.Work.RTOwed.mobiusKlein_act
import Submission.Work.RTOwed.coordPerm_eq_mobius
import Submission.Work.RTOwed.mobiusKlein_eq_mobius
import Submission.Work.RTOwed.foldTrans_piece

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The transport of a fold chart along a sign change of the Klein coordinates

`Work.FoldInst.act g` is the sign change `y ↦ (g_i y_i)` of the Klein coordinates, a linear map
whose Klein lift is equivariant (`Work.FoldInst.hypOfKlein_act`), so that on the chart map
`foldTheta i r = coordPerm i ∘ mobiusKlein (N_F i · D_r)` it acts by *right multiplication* of the
developing matrix by the sign diagonal `diagKR (signVec g)`:

  `foldTheta j s (act g y) = coordPerm j (mobiusKlein (N_F j · D_s · diagKR (signVec g)) y)`.

This file transports the piecewise formula `Work.RTOwed.foldTheta_trans` along that identity: the
chart of the class `j` on the sign index `s`, evaluated at `act g x`, is the Möbius transform of
the chart of the class `i` on the sign index `r`, evaluated at `x`, by the matrix

  `coordPermMat j * ((N_F j · D_s · diagKR (signVec g)) * (N_F i · D_r)⁻¹) * (coordPermMat i)⁻¹`.

The proof is the same chain as in `foldTheta_trans` — the coordinate permutations are Möbius maps
of their permutation matrices (`coordPerm_eq_mobius`), Klein actions compose with inverses
(`mobiusKlein_eq_mobius`), Möbius maps compose (`HypModel.mobius_mul`) and the inverse permutation
matrix cancels against `coordPermMat i` — with the single modification that the Klein action of
`N_F j · D_s` is replaced by that of `N_F j · D_s · diagKR (signVec g)`.

## The Lorentz matrices involved

All the matrices that occur are Lorentz matrices: `N_F i · D_r` and `N_F j · D_s`
(`foldInst_foldNr_mul_foldDrR_isLorentz`), their inverses (`isLorentzMat_inv`), the sign diagonal
`diagKR (signVec g)` (whose entries are `±1` on the first four coordinates and `1` on the timelike
coordinate, so that `foldInst_diag_lorentz` applies), and the coordinate permutation matrices
`coordPermMat i`, `coordPermMat j` (permutation matrices fixing the timelike coordinate; proved
privately here).
-/

noncomputable section

namespace Work.RTOwed

/-! ### The sign diagonal `diagKR (signVec g)` is a Lorentz matrix -/

/-- The entries of `signVec g` are `±1`, hence their squares are `1`. -/
private lemma signVec_cast_mul_self (g : Fin 4 → ZMod 2) (i : Fin 4) :
    ((Work.FoldInst.signVec g i : ℤ) : ℝ) * ((Work.FoldInst.signVec g i : ℤ) : ℝ) = 1 := by
  rw [Work.FoldInst.signVec]
  split <;> norm_num

/-- **The Klein diagonal of a sign change is a Lorentz matrix.**  `diagKR (signVec g)` is the
diagonal matrix `diag(±1,±1,±1,±1,1)` whose last entry is `1`, so it is a Lorentz matrix by
`Work.FoldInst.foldInst_diag_lorentz`. -/
private theorem diagKR_signVec_isLorentz (g : Fin 4 → ZMod 2) :
    Work.HypModel.IsLorentzMat (Work.FoldInst.diagKR (Work.FoldInst.signVec g)) := by
  rw [Work.FoldInst.diagKR_eq_diagonal]
  refine Work.FoldInst.foldInst_diag_lorentz (fun j => ?_) ?_
  · by_cases h4 : (j : ℕ) < 4
    · rw [dite_eq_left h4]
      exact signVec_cast_mul_self g ⟨j, h4⟩
    · rw [dite_eq_right h4]
      norm_num
  · rw [dite_eq_right (by norm_num : ¬ (((4 : Fin 5) : ℕ) < 4))]
    norm_num

/-! ### The coordinate permutation matrix is a Lorentz matrix -/

/-- The permutation `perm5 i` of the five coordinates fixes the timelike coordinate `4`. -/
private theorem perm5_four_aux (i : Fin 98) : perm5 i 4 = 4 := by
  simp only [perm5]
  rw [dite_eq_right (by decide : ¬ (((4 : Fin 5) : ℕ) < 3))]

/-- **`coordPermMat i` is a Lorentz matrix.**  It is the `0`-`1` matrix of the permutation
`perm5 i`, which permutes the spacelike coordinates `0,1,2` (through the bijection `foldTau i`) and
fixes `3,4`; hence it is an isometry of `J = diag(1,1,1,1,-1)` with `(4,4)` entry `1`. -/
private theorem coordPermMat_isLorentz_aux (i : Fin 98) :
    Work.HypModel.IsLorentzMat (Work.RTOwed.coordPermMat i) := by
  have hinj : Function.Injective (perm5 i) := (perm5_bijective i).1
  have h4 : perm5 i 4 = 4 := perm5_four_aux i
  have hσ4 : ∀ k : Fin 5, perm5 i k = 4 ↔ k = 4 := fun k =>
    ⟨fun h => hinj (by rw [h, h4]), fun h => by rw [h, h4]⟩
  constructor
  · ext j k
    rw [Matrix.mul_apply]
    simp only [Work.HypModel.J, Matrix.mul_diagonal, Work.RTOwed.coordPermMat,
      Matrix.transpose_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single (perm5 i j)]
    · simp only [ite_true, one_mul, hσ4 j]
      by_cases h : j = k
      · subst h; simp
      · have h2 : ¬ (perm5 i k = perm5 i j) := fun hh => h (hinj hh).symm
        simp [h, h2]
    · intro b _ hb
      simp [show ¬ (perm5 i j = b) from fun h => hb h.symm]
    · intro h
      exact absurd (Finset.mem_univ (perm5 i j)) h
  · simp only [Work.RTOwed.coordPermMat, h4]
    norm_num

/-! ### The transport of the chart map -/

/-- **The transport of a fold chart along a sign change of the Klein coordinates.**

For every point `x` of the open unit ball, every two fold classes `i`, `j` with sign indices
`r`, `s` and every sign change `g`,

  `foldTheta j s (act g x) = mobius (C_j · (N_F j D_s · diagKR (signVec g)) · (N_F i D_r)⁻¹ · C_i⁻¹)`

applied to `foldTheta i r x`, where `C_i = coordPermMat i`.  The sign change is absorbed into the
developing matrix by `mobiusKlein_act`; the rest is the computation of `foldTheta_trans`. -/
theorem foldTheta_actTransport (i j : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (s : Fin (Work.FoldInst.foldCodim j) → Bool) (g : Fin 4 → ZMod 2) {x : Work.FoldInst.E4}
    (hx : x ∈ Work.HypModel.ball) :
    Work.FoldInst.foldTheta j s (Work.FoldInst.act g x)
      = Work.HypModel.mobius
          (Work.RTOwed.coordPermMat j
            * ((Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s
                * Work.FoldInst.diagKR (Work.FoldInst.signVec g))
              * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹)
            * (Work.RTOwed.coordPermMat i)⁻¹)
          (Work.FoldInst.foldTheta i r x) := by
  -- the Lorentz matrices involved
  have hKi : Work.HypModel.IsLorentzMat (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) :=
    Work.FoldInst.foldInst_foldNr_mul_foldDrR_isLorentz i r
  have hKj : Work.HypModel.IsLorentzMat (Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s) :=
    Work.FoldInst.foldInst_foldNr_mul_foldDrR_isLorentz j s
  have hG : Work.HypModel.IsLorentzMat (Work.FoldInst.diagKR (Work.FoldInst.signVec g)) :=
    diagKR_signVec_isLorentz g
  have hK2 : Work.HypModel.IsLorentzMat
      (Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s
        * Work.FoldInst.diagKR (Work.FoldInst.signVec g)) := hKj.mul hG
  have hCi : Work.HypModel.IsLorentzMat (Work.RTOwed.coordPermMat i) :=
    coordPermMat_isLorentz_aux i
  have hCj : Work.HypModel.IsLorentzMat (Work.RTOwed.coordPermMat j) :=
    coordPermMat_isLorentz_aux j
  have hKi_inv : Work.HypModel.IsLorentzMat
      ((Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹) :=
    Work.FoldInst.isLorentzMat_inv hKi
  -- the two chart values have positive height
  have hpi : 0 < (Work.HypModel.mobiusKlein
      (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) x) 3 :=
    Work.HypModel.mobiusKlein_mem hKi hx
  have hpj : 0 < (Work.HypModel.mobiusKlein
      (Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s
        * Work.FoldInst.diagKR (Work.FoldInst.signVec g)) x) 3 :=
    Work.HypModel.mobiusKlein_mem hK2 hx
  -- the left hand side, with the sign change absorbed into the developing matrix
  have hlhs : Work.FoldInst.foldTheta j s (Work.FoldInst.act g x)
      = Work.HypModel.mobius
          (Work.RTOwed.coordPermMat j
            * ((Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s
                * Work.FoldInst.diagKR (Work.FoldInst.signVec g))
              * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹))
          (Work.HypModel.mobiusKlein (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) x) := by
    simp only [Work.FoldInst.foldTheta]
    rw [mobiusKlein_act]
    rw [coordPerm_eq_mobius j hpj]
    rw [mobiusKlein_eq_mobius hKi hK2 hx]
    rw [← Work.HypModel.mobius_mul hCj (hK2.mul hKi_inv) hpi]
  -- the right hand side, with the coordinate permutation of the source absorbed
  have hM : Work.HypModel.IsLorentzMat
      (Work.RTOwed.coordPermMat j
        * ((Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s
            * Work.FoldInst.diagKR (Work.FoldInst.signVec g))
          * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹)
        * (Work.RTOwed.coordPermMat i)⁻¹) :=
    (hCj.mul (hK2.mul hKi_inv)).mul (Work.FoldInst.isLorentzMat_inv hCi)
  have hrhs : Work.HypModel.mobius
        (Work.RTOwed.coordPermMat j
          * ((Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s
              * Work.FoldInst.diagKR (Work.FoldInst.signVec g))
            * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹)
          * (Work.RTOwed.coordPermMat i)⁻¹)
        (Work.FoldInst.foldTheta i r x)
      = Work.HypModel.mobius
          (Work.RTOwed.coordPermMat j
            * ((Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s
                * Work.FoldInst.diagKR (Work.FoldInst.signVec g))
              * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹))
          (Work.HypModel.mobiusKlein (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) x) := by
    simp only [Work.FoldInst.foldTheta]
    rw [coordPerm_eq_mobius i hpi]
    rw [← Work.HypModel.mobius_mul hM hCi hpi]
    congr 1
    rw [Matrix.mul_assoc, nonsing_inv_mul_self_of_isLorentzMat hCi, Matrix.mul_one]
  exact hlhs.trans hrhs.symm

end Work.RTOwed
