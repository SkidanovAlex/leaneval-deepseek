/-
# The coordinate permutation of a fold class is a Möbius transformation

`Work.FoldInst.coordPerm i` is the coordinate permutation of the model attached to the fold class
`i` of `M̄`: it reindexes the coordinates of `E4 = ℝ⁴` by the inverse of the permutation
`Work.FoldInst.foldTau i` of the four coordinates (`foldTau i` moves the triple coordinates to the
front — one per wall — and fixes the height coordinate `3`).

`Work.RTOwed.coordPermMat i` is the *permutation matrix* of the induced permutation `perm5 i` of
the five coordinates of the Lorentz space `V5 = ℝ⁵` (the first three coordinates are permuted as
`foldTau i` permutes the triple coordinates, the last two — including the timelike coordinate `4` —
are fixed).

This file proves that these are the same map: a coordinate permutation is a Möbius transformation
of the upper half space, and the Möbius matrix attached to `coordPerm i` is exactly
`coordPermMat i`:

  `coordPerm i q = mobius (coordPermMat i) q`   for `0 < q 3`.

This is the algebraic half of the analysis of the transitions of the fold charts: composing a
Klein action with a fold chart produces a `coordPerm i` in front (`foldTheta`), and this lemma
lets that permutation be absorbed into the Möbius matrix `Work.RTOwed.transMat` of the transition,
where `Work.HypModel.mobius_contDiffOn` and `Work.HypModel.mobius_isometry` apply.

## The computation

`hypOfUHS q = (q₀/q₃, q₁/q₃, q₂/q₃, (‖q‖²−1)/(2q₃), (‖q‖²+1)/(2q₃))`; a permutation of the first
three coordinates of the hyperboloid point therefore permutes the first three entries, leaves the
height entries `3`, `4` (hence the height `P₄ − P₃ = 1/q₃` and so the height of the `uhs`
coordinate `q₃`) unchanged, and `uhsOfHyp` returns the permuted vector of `q`.  The matrix
`coordPermMat i` is the matrix of exactly this reindexing (`perm5 i`), and `perm5 i` acts on
`{0,1,2}` as `foldTau i` does and fixes `3`, `4`; this is what makes the two sides agree,
coordinate by coordinate.
-/
import Mathlib
import Submission.Work.RTOwed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Matrix
open scoped Matrix

namespace Work.RTOwed

/-! ### Elementary facts about the permutation `foldTau i` of the four coordinates -/

/-- `foldTau i` preserves the triple coordinates `{0,1,2}` (it is a bijection fixing `3`). -/
lemma foldTau_val_lt_three (i : Fin 98) (t : Fin 4) (ht : t.val < 3) :
    (Work.FoldInst.foldTau i t).val < 3 := by
  have hne : (Work.FoldInst.foldTau i t).val ≠ 3 := by
    intro h
    have ht3 : t = 3 :=
      (Work.FoldInst.foldTau_bijective i).1
        (show Work.FoldInst.foldTau i t = Work.FoldInst.foldTau i 3 by
          rw [Work.FoldInst.foldTau_three i]
          exact Fin.ext h)
    rw [ht3] at ht
    simp at ht
  have h4 := (Work.FoldInst.foldTau i t).isLt
  omega

/-- The same, for the inverse of `foldTau i`. -/
lemma invFun_foldTau_val_lt_three (i : Fin 98) (j : Fin 4) (hj : j.val < 3) :
    (Function.invFun (Work.FoldInst.foldTau i) j).val < 3 := by
  have hright := Function.rightInverse_invFun (Work.FoldInst.foldTau_bijective i).2 j
  have hne : (Function.invFun (Work.FoldInst.foldTau i) j).val ≠ 3 := by
    intro h
    have h3 : Function.invFun (Work.FoldInst.foldTau i) j = 3 := Fin.ext h
    rw [h3, Work.FoldInst.foldTau_three i] at hright
    have hj' : j.val = 3 := by
      rw [← hright]
      norm_num
    omega
  have h4 := (Function.invFun (Work.FoldInst.foldTau i) j).isLt
  omega

/-- `foldTau i` fixes the height coordinate, and so does its inverse. -/
lemma invFun_foldTau_three (i : Fin 98) : Function.invFun (Work.FoldInst.foldTau i) 3 = 3 := by
  have h := Function.leftInverse_invFun (Work.FoldInst.foldTau_bijective i).1 (3 : Fin 4)
  rwa [Work.FoldInst.foldTau_three i] at h

/-! ### The permutation `perm5 i` of the five matrix coordinates, and its inverse -/

/-- `perm5 i` is `foldTau i` on the triple coordinates and the identity on the last two. -/
lemma perm5_eq (i : Fin 98) (k : Fin 5) :
    perm5 i k = if hk : k.val < 3 then
        Fin.castSucc (Work.FoldInst.foldTau i ⟨k.val, by omega⟩) else k := by
  by_cases hk : k.val < 3
  · rw [dif_pos hk]
    simp only [perm5]
    rw [dif_pos hk]
    exact Fin.ext rfl
  · rw [dif_neg hk]
    simp only [perm5]
    rw [dif_neg hk]

/-- The inverse of `perm5 i`: the inverse of `foldTau i` on the triple coordinates, the identity
on the last two. -/
def perm5Symm (i : Fin 98) : Fin 5 → Fin 5 :=
  fun j => if hj : j.val < 3 then
    Fin.castSucc (Function.invFun (Work.FoldInst.foldTau i) ⟨j.val, by omega⟩) else j

lemma perm5Symm_perm5 (i : Fin 98) (k : Fin 5) : perm5Symm i (perm5 i k) = k := by
  by_cases hk : k.val < 3
  · rw [perm5_eq, dif_pos hk]
    have hlt : (Fin.castSucc (Work.FoldInst.foldTau i ⟨k.val, by omega⟩)).val < 3 := by
      simp only [Fin.val_castSucc]
      exact foldTau_val_lt_three i _ hk
    simp only [perm5Symm]
    rw [dif_pos hlt]
    have hfin : (⟨(Fin.castSucc (Work.FoldInst.foldTau i ⟨k.val, by omega⟩)).val, by omega⟩ : Fin 4)
        = Work.FoldInst.foldTau i ⟨k.val, by omega⟩ := Fin.ext rfl
    rw [hfin, Function.leftInverse_invFun (Work.FoldInst.foldTau_bijective i).1]
    exact Fin.ext rfl
  · rw [perm5_eq, dif_neg hk]
    simp only [perm5Symm]
    rw [dif_neg hk]

lemma perm5_perm5Symm (i : Fin 98) (j : Fin 5) : perm5 i (perm5Symm i j) = j := by
  by_cases hj : j.val < 3
  · have hlt : (Fin.castSucc
        (Function.invFun (Work.FoldInst.foldTau i) ⟨j.val, by omega⟩)).val < 3 := by
      simp only [Fin.val_castSucc]
      exact invFun_foldTau_val_lt_three i _ hj
    simp only [perm5Symm]
    rw [dif_pos hj]
    rw [perm5_eq, dif_pos hlt]
    have hfin : (⟨(Fin.castSucc
        (Function.invFun (Work.FoldInst.foldTau i) ⟨j.val, by omega⟩)).val,
        by omega⟩ : Fin 4) = Function.invFun (Work.FoldInst.foldTau i) ⟨j.val, by omega⟩ :=
      Fin.ext rfl
    rw [hfin, Function.rightInverse_invFun (Work.FoldInst.foldTau_bijective i).2]
    exact Fin.ext rfl
  · simp only [perm5Symm]
    rw [dif_neg hj]
    rw [perm5_eq, dif_neg hj]

/-- `perm5 i` as a permutation of `Fin 5`. -/
def perm5Perm (i : Fin 98) : Equiv.Perm (Fin 5) where
  toFun := perm5 i
  invFun := perm5Symm i
  left_inv := perm5Symm_perm5 i
  right_inv := perm5_perm5Symm i

lemma perm5Perm_apply (i : Fin 98) (k : Fin 5) : perm5Perm i k = perm5 i k := rfl

lemma perm5Perm_symm_apply (i : Fin 98) (j : Fin 5) :
    (perm5Perm i).symm j = perm5Symm i j := rfl

/-- The permutation `perm5 i` fixes the height coordinate `3`. -/
lemma perm5Symm_three (i : Fin 98) : perm5Symm i 3 = 3 := by
  simp only [perm5Symm]
  rw [dif_neg (by decide : ¬ ((3 : Fin 5).val < 3))]

/-- The permutation `perm5 i` fixes the timelike coordinate `4`. -/
lemma perm5Symm_four (i : Fin 98) : perm5Symm i 4 = 4 := by
  simp only [perm5Symm]
  rw [dif_neg (by decide : ¬ ((4 : Fin 5).val < 3))]

/-- On the triple coordinates, the inverse permutation is the inverse of `foldTau i`. -/
lemma perm5Symm_castSucc (i : Fin 98) (j : Fin 4) (hj : j.val < 3) :
    perm5Symm i (Fin.castSucc j) = Fin.castSucc (Function.invFun (Work.FoldInst.foldTau i) j) := by
  have hlt : (Fin.castSucc j).val < 3 := by simpa using hj
  simp only [perm5Symm]
  rw [dif_pos hlt]
  congr 1

/-! ### The matrix of the permutation, and its action -/

/-- `coordPermMat i` is the permutation matrix of `perm5 i` (in the `PEquiv.toMatrix` convention,
whose row `j` is the indicator of `perm5 i j`). -/
lemma coordPermMat_eq_permMatrix (i : Fin 98) :
    coordPermMat i = (perm5Perm i).symm.toPEquiv.toMatrix := by
  ext j k
  simp only [coordPermMat, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  have hiff : (k ∈ some ((perm5Perm i).symm j)) ↔ (perm5 i k = j) := by
    simp only [Option.mem_some_iff, Equiv.symm_apply_eq, perm5Perm_apply]
    exact eq_comm
  simp only [hiff]

/-- **The action of the permutation matrix**: `coordPermMat i` reindexes the five coordinates by
the inverse permutation `perm5Symm i`. -/
lemma coordPermMat_mulVec (i : Fin 98) (a : Work.HypModel.V5) :
    coordPermMat i *ᵥ a = fun j => a (perm5Symm i j) := by
  rw [coordPermMat_eq_permMatrix i, PEquiv.toMatrix_toPEquiv_mulVec]
  rfl

/-! ### The coordinates of the two models -/

/-- The height coordinate is preserved by `hypOfUHS` on the triple coordinates: for `j < 3`,
`hypOfUHS q j = q j / q 3`. -/
lemma hypOfUHS_castSucc (q : Work.FoldInst.E4) (j : Fin 4) (hj : j.val < 3) :
    Work.HypModel.hypOfUHS q (Fin.castSucc j) = q j / q 3 := by
  fin_cases j <;> simp_all [Work.HypModel.hypOfUHS]

/-- The first three coordinates of `uhsOfHyp P` are `P` on the triple coordinates, scaled by the
inverse height `(P 4 − P 3)⁻¹`. -/
lemma uhsOfHyp_apply_lt_three (P : Work.HypModel.V5) (j : Fin 4) (hj : j.val < 3) :
    Work.HypModel.uhsOfHyp P j = P (Fin.castSucc j) * (P 4 - P 3)⁻¹ := by
  fin_cases j <;> simp_all [Work.HypModel.uhsOfHyp]

/-- The height coordinate of `uhsOfHyp P` is the inverse height `(P 4 − P 3)⁻¹`. -/
lemma uhsOfHyp_apply_three (P : Work.HypModel.V5) :
    Work.HypModel.uhsOfHyp P 3 = (P 4 - P 3)⁻¹ := by
  simp [Work.HypModel.uhsOfHyp]

/-- **The coordinate permutation is the Möbius transformation of its permutation matrix.** -/
theorem coordPerm_eq_mobius (i : Fin 98) {q : Work.FoldInst.E4} (hq : 0 < q 3) :
    Work.FoldInst.coordPerm i q = Work.HypModel.mobius (Work.RTOwed.coordPermMat i) q := by
  have h3 : q 3 ≠ 0 := ne_of_gt hq
  -- the Möbius map of the permutation matrix reindexes the height-normalised coordinates
  have hmob : Work.HypModel.mobius (coordPermMat i) q
      = Work.HypModel.uhsOfHyp (fun j : Fin 5 => Work.HypModel.hypOfUHS q (perm5Symm i j)) := by
    rw [Work.HypModel.mobius, coordPermMat_mulVec]
  -- the height `q 3` is unchanged by the permutation
  have hs : ((fun j : Fin 5 => Work.HypModel.hypOfUHS q (perm5Symm i j)) 4
      - (fun j : Fin 5 => Work.HypModel.hypOfUHS q (perm5Symm i j)) 3)⁻¹ = q 3 := by
    simp only [perm5Symm_four, perm5Symm_three]
    rw [Work.HypModel.hypOfUHS_four_sub_three h3, inv_inv]
  -- coordinatewise, both sides are the inverse `foldTau`-reindexing of the coordinates of `q`
  have hmain : ∀ j : Fin 4,
      Work.HypModel.uhsOfHyp (fun j : Fin 5 => Work.HypModel.hypOfUHS q (perm5Symm i j)) j
        = Work.FoldInst.coordPerm i q j := by
    intro j
    by_cases hj : j.val < 3
    · rw [uhsOfHyp_apply_lt_three _ j hj, perm5Symm_castSucc i j hj,
        hypOfUHS_castSucc q (Function.invFun (Work.FoldInst.foldTau i) j)
          (invFun_foldTau_val_lt_three i j hj), hs, Work.FoldInst.coordPerm_apply]
      exact div_mul_cancel₀ _ h3
    · have hj3 : j = 3 := Fin.ext (by omega)
      subst hj3
      rw [uhsOfHyp_apply_three, hs, Work.FoldInst.coordPerm_apply, invFun_foldTau_three]
  rw [hmob]
  exact PiLp.ext (fun j => (hmain j).symm)

end Work.RTOwed
