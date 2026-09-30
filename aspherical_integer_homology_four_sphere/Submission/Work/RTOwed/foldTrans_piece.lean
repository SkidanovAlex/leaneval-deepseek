/-
# The transition of two fold charts on a common piece

The fold chart of the class `i : Fin 98` is assembled from the piecewise maps
`foldTheta i r = coordPerm i ∘ mobiusKlein (N_F i · D_r)` on the Voronoi pieces `Dvor i r`
(`Work.FoldInst.FoldChart`, `Work.FoldInst.FoldPiece`).  This file computes the transition of the
charts of two classes at a point `y` that lies both in the piece `Dvor i r` of the first class and
in the piece `Dvor j s` of the second: the value of the chart `j` at `y` is the Möbius transform of
the value of the chart `i` by the matrix

  `transMat i j r s = coordPermMat j * (N_F j · D_s) * (N_F i · D_r)⁻¹ * (coordPermMat i)⁻¹`.

The proof is the algebraic chain described in `Defs.lean`:

* the coordinate permutation `coordPerm i` is the Möbius map of its permutation matrix
  (`coordPerm_eq_mobius`), which is a Lorentz matrix, so that `coordPerm i` may be moved into a
  Möbius matrix product;
* the Klein action of `K₂ = N_F j · D_s` is the Möbius action of `K₂ K₁⁻¹` applied to the Klein
  action of `K₁ = N_F i · D_r` (`mobiusKlein_eq_mobius`);
* Möbius maps compose (`HypModel.mobius_mul`), and the inverse permutation matrix `(coordPermMat i)⁻¹`
  cancels against `coordPermMat i` (the associativity identity `transMat_mul_coordPermMat`).
-/
import Mathlib
import Submission.Work.RTOwed.Defs
import Submission.Work.RTOwed.coordPerm_eq_mobius
import Submission.Work.RTOwed.coordPermInv_eq_mobius
import Submission.Work.RTOwed.mobiusKlein_eq_mobius
import Submission.Work.RTOwed.mobius_height_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.RTOwed

open Work.HypModel

/-! ### The coordinate permutation matrix of a fold class is a Lorentz matrix -/

/- The statement and proof of `Work.RTOwed.coordPermMat_isLorentz`: a permutation matrix that
fixes the timelike coordinate `4` is a Lorentz matrix.  It is repeated privately here because
`Submission.Work.RTOwed.coordPermMat_isLorentz` and `Submission.Work.RTOwed.coordPermInv_eq_mobius`
both declare `Work.RTOwed.perm5_injective`, so the two modules cannot be imported together, and this
file needs both the inverse coordinate permutation (`coordPermInv_eq_mobius`, needed elsewhere in
the `RTOwed` area) and the Lorentz-ness of `coordPermMat` (needed below for `mobius_mul`). -/

/-- `perm5 i` is injective: it is the bijection `foldTau i` of the triple coordinates, extended by
the identity on the last two coordinates; `perm5Symm i` is a two-sided inverse of it. -/
private theorem perm5_injective_aux (i : Fin 98) : Function.Injective (perm5 i) := by
  intro a b h
  have h' := congrArg (perm5Symm i) h
  rwa [perm5Symm_perm5, perm5Symm_perm5] at h'

/-- `perm5 i` fixes the timelike coordinate `4`. -/
private theorem perm5_four_aux (i : Fin 98) : perm5 i 4 = 4 := by
  have h' := perm5_perm5Symm i 4
  rwa [perm5Symm_four i] at h'

/-- **The coordinate permutation matrix is a Lorentz matrix.**  `coordPermMat i` is the `0`-`1`
matrix of the permutation `perm5 i` of the five coordinates, which permutes the spacelike
coordinates `0,1,2` (through the bijection `foldTau i`) and fixes `3,4`; hence it is an isometry of
`J = diag(1,1,1,1,-1)` with `(4,4)` entry `1`. -/
private theorem coordPermMat_isLorentz_aux (i : Fin 98) : IsLorentzMat (coordPermMat i) := by
  have hinj := perm5_injective_aux i
  have h4 := perm5_four_aux i
  have hσ4 : ∀ k : Fin 5, perm5 i k = 4 ↔ k = 4 := fun k =>
    ⟨fun h => hinj (by rw [h, h4]), fun h => by rw [h, h4]⟩
  constructor
  · ext j k
    rw [Matrix.mul_apply]
    simp only [Work.HypModel.J, Matrix.mul_diagonal, coordPermMat, Matrix.transpose_apply,
      Matrix.diagonal_apply]
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
  · simp only [coordPermMat, h4]
    norm_num

/-- The inverse of the coordinate permutation matrix is a left inverse of it. -/
private theorem coordPermMat_inv_mul_self_aux (i : Fin 98) :
    (coordPermMat i)⁻¹ * coordPermMat i = 1 :=
  nonsing_inv_mul_self_of_isLorentzMat (coordPermMat_isLorentz_aux i)

/-! ### The matrix of the transition -/

/-- **The transition matrix times the coordinate permutation of the source class.**

Multiplying `transMat i j r s` on the right by `coordPermMat i` cancels the inverse permutation
matrix, leaving the product of the two developing matrices.  This is the identity that lets the
`coordPerm i` of the source chart be absorbed into the transition matrix. -/
lemma transMat_mul_coordPermMat (i j : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (s : Fin (Work.FoldInst.foldCodim j) → Bool) :
    transMat i j r s * coordPermMat i
      = coordPermMat j * ((Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s)
          * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹) := by
  have hD : (coordPermMat i)⁻¹ * coordPermMat i = 1 := coordPermMat_inv_mul_self_aux i
  rw [transMat]
  simp only [Matrix.mul_assoc]
  rw [hD, Matrix.mul_one]

/-- **The transition matrix is a Lorentz matrix**: it is a product of the Lorentz matrices
`coordPermMat j`, `N_F j · D_s` and the inverses of `N_F i · D_r` and `coordPermMat i`.

The Lorentz-ness is built up factor by factor (`IsLorentzMat.mul`), in the left-associated order in
which `transMat` is written, so that the final comparison with the unfolded `transMat` is
syntactic. -/
lemma transMat_isLorentz (i j : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (s : Fin (Work.FoldInst.foldCodim j) → Bool) :
    IsLorentzMat (transMat i j r s) := by
  have hKj : IsLorentzMat (Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s) :=
    Work.FoldInst.foldInst_foldNr_mul_foldDrR_isLorentz j s
  have hKinv : IsLorentzMat ((Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹) :=
    Work.FoldInst.isLorentzMat_inv
      (Work.FoldInst.foldInst_foldNr_mul_foldDrR_isLorentz i r)
  have hCinv : IsLorentzMat ((coordPermMat i)⁻¹) :=
    Work.FoldInst.isLorentzMat_inv (coordPermMat_isLorentz_aux i)
  have h1 : IsLorentzMat (coordPermMat j
      * (Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s)) :=
    (coordPermMat_isLorentz_aux j).mul hKj
  have h2 : IsLorentzMat (coordPermMat j * (Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s)
      * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹) := h1.mul hKinv
  have h3 : IsLorentzMat (coordPermMat j * (Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s)
      * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹ * (coordPermMat i)⁻¹) :=
    h2.mul hCinv
  rw [transMat]
  exact h3

/-! ### The transition of the chart maps -/

/-- **The transition of two fold charts on a common piece, at the level of the chart maps.**

For a point `y` of the open unit ball (a Klein model point of the truncated 24-cell),

  `foldTheta j s y = mobius (transMat i j r s) (foldTheta i r y)`.

This is the piecewise form of `foldTrans_piece`: `mobiusKlein (N_F j D_s) y` and
`mobiusKlein (N_F i D_r) y` are the two upper half space values of the Klein actions of the two
developing matrices at `y`, related by the Möbius map of `(N_F j D_s) (N_F i D_r)⁻¹`
(`mobiusKlein_eq_mobius`), and the two coordinate permutations are the Möbius maps of their
permutation matrices (`coordPerm_eq_mobius`), which are absorbed into `transMat`. -/
lemma foldTheta_trans (i j : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (s : Fin (Work.FoldInst.foldCodim j) → Bool) {y : Work.HypModel.E4}
    (hy : y ∈ ball) :
    Work.FoldInst.foldTheta j s y = mobius (transMat i j r s) (Work.FoldInst.foldTheta i r y) := by
  have hKi : IsLorentzMat (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) :=
    Work.FoldInst.foldInst_foldNr_mul_foldDrR_isLorentz i r
  have hKj : IsLorentzMat (Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s) :=
    Work.FoldInst.foldInst_foldNr_mul_foldDrR_isLorentz j s
  have hCi : IsLorentzMat (coordPermMat i) := coordPermMat_isLorentz_aux i
  have hCj : IsLorentzMat (coordPermMat j) := coordPermMat_isLorentz_aux j
  have hpi : 0 < (mobiusKlein (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) y) 3 :=
    mobiusKlein_mem hKi hy
  have hpj : 0 < (mobiusKlein (Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s) y) 3 :=
    mobiusKlein_mem hKj hy
  have hKinv : IsLorentzMat ((Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹) :=
    Work.FoldInst.isLorentzMat_inv hKi
  have hlhs : Work.FoldInst.foldTheta j s y
      = mobius (coordPermMat j * ((Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s)
          * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹))
        (mobiusKlein (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) y) := by
    simp only [Work.FoldInst.foldTheta]
    rw [coordPerm_eq_mobius j hpj]
    rw [mobiusKlein_eq_mobius hKi hKj hy]
    rw [← mobius_mul hCj (hKj.mul hKinv) hpi]
  have hrhs : mobius (transMat i j r s) (Work.FoldInst.foldTheta i r y)
      = mobius (coordPermMat j * ((Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s)
          * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹))
        (mobiusKlein (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r) y) := by
    simp only [Work.FoldInst.foldTheta]
    rw [coordPerm_eq_mobius i hpi]
    rw [← mobius_mul (transMat_isLorentz i j r s) hCi hpi]
    rw [transMat_mul_coordPermMat i j r s]
  exact hlhs.trans hrhs.symm

/-! ### The requested statement -/

theorem foldTrans_piece (i j : Fin 98) (r : Fin (Work.FoldInst.foldCodim i) → Bool)
    (s : Fin (Work.FoldInst.foldCodim j) → Bool) {y : Work.FoldInst.Xbar}
    (hyi : y ∈ Work.FoldInst.Dvor i r) (hyj : y ∈ Work.FoldInst.Dvor j s) :
    Work.FoldInst.foldChart j (Work.FoldInst.mk y) =
      Work.HypModel.mobius
        (Work.RTOwed.coordPermMat j * (Work.FoldInst.foldNr j * Work.FoldInst.foldDrR j s)
          * (Work.FoldInst.foldNr i * Work.FoldInst.foldDrR i r)⁻¹ * (Work.RTOwed.coordPermMat i)⁻¹)
        (Work.FoldInst.foldChart i (Work.FoldInst.mk y)) := by
  rw [Work.FoldInst.foldChart_apply j s y hyj, Work.FoldInst.foldChart_apply i r y hyi]
  exact foldTheta_trans i j r s (Work.FoldInst.Dvor_subset_ball i r hyi)

end Work.RTOwed
