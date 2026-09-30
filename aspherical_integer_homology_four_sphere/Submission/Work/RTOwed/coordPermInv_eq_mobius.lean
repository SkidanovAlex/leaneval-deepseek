import Mathlib
import Submission.Work.RTOwed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The inverse coordinate permutation of a fold class is a Möbius map

`Work.FoldInst.coordPermInv i` reindexes the four coordinates of `E4` by the bijection
`foldTau i` (`coordPermInv i y j = y (foldTau i j)`), and `Work.RTOwed.coordPermMat i` is the
`5 × 5` permutation matrix of `perm5 i`, the extension of `foldTau i` to `Fin 5` that fixes the
last two coordinates.  This file proves that the *inverse* of that permutation matrix acts by
`coordPermInv i` on the upper half space, i.e. that `coordPermInv i` is the Möbius transformation
of the inverse matrix:

  `coordPermInv i q = mobius (coordPermMat i)⁻¹ q`   for `0 < q 3`.

The proof is elementary: `foldTau i` is a bijection of `Fin 4` fixing `3` (`foldTau_bijective`,
`foldTau_three`), hence so is `perm5 i` on `Fin 5`; a permutation matrix acts on a vector by
reindexing (`Matrix.permMatrix_mulVec`), so

  `(coordPermMat i)⁻¹ *ᵥ hypOfUHS q = fun j => hypOfUHS q (perm5 i j)`,

and evaluating the explicit formulas for `hypOfUHS` and `uhsOfHyp` gives the claim: the first three
entries are `(q (foldTau i j)/q 3)`, the height `q 3` recorded in the third entry is unaffected by
the permutation of the first three coordinates, and the height difference
`hypOfUHS q 4 - hypOfUHS q 3 = (q 3)⁻¹` (`hypOfUHS_four_sub_three`) inverts to `q 3`.
-/

noncomputable section

namespace Work.RTOwed

open Work.FoldInst
open scoped Matrix

/-! ### The permutation `perm5` of `Fin 5` is a bijection -/

/-- `foldTau i` fixes `3`, so it takes no other value equal to `3`. -/
lemma foldTau_ne_three (i : Fin 98) {j : Fin 4} (hj : j ≠ 3) : foldTau i j ≠ 3 := by
  intro h
  exact hj ((foldTau_bijective i).1 (by rw [h, foldTau_three]))

/-- `foldTau i` maps the first three coordinates into the first three coordinates. -/
lemma foldTau_lt_three (i : Fin 98) {j : Fin 4} (hj : (j : ℕ) < 3) : (foldTau i j : ℕ) < 3 := by
  have hne : foldTau i j ≠ 3 := foldTau_ne_three i (by omega)
  have hlt : (foldTau i j : ℕ) < 4 := (foldTau i j).isLt
  omega

/-- The value of `perm5 i` on a coordinate below `3` is the `foldTau i`-value of that coordinate. -/
lemma perm5_val (i : Fin 98) {j : Fin 5} (hj : (j : ℕ) < 3) :
    ((perm5 i j : Fin 5) : ℕ) = (foldTau i ⟨(j : ℕ), by omega⟩ : ℕ) := by
  simp only [perm5, dite_eq_left hj]

/-- `perm5 i` maps the coordinates `0,1,2` into `0,1,2`. -/
lemma perm5_lt_three (i : Fin 98) {j : Fin 5} (hj : (j : ℕ) < 3) : (perm5 i j : ℕ) < 3 := by
  simp only [perm5, dite_eq_left hj]
  exact foldTau_lt_three i (by simpa using hj)

/-- `perm5 i` fixes the last two coordinates. -/
lemma perm5_not_lt (i : Fin 98) {j : Fin 5} (hj : ¬ ((j : ℕ) < 3)) : perm5 i j = j := by
  simp only [perm5, dite_eq_right hj]

/-- `perm5 i` is injective: it is `foldTau i` on the first three coordinates (a bijection of
`Fin 4` fixing `3`) and the identity on the last two. -/
private lemma perm5_injective (i : Fin 98) : Function.Injective (perm5 i) := by
  intro a b hab
  by_cases ha : (a : ℕ) < 3
  · by_cases hb : (b : ℕ) < 3
    · have h4 : (⟨(a : ℕ), by omega⟩ : Fin 4) = ⟨(b : ℕ), by omega⟩ := by
        apply (foldTau_bijective i).1
        apply Fin.ext
        have h := congrArg Fin.val hab
        simp only [perm5, dite_eq_left ha, dite_eq_left hb] at h
        simpa using h
      exact Fin.ext (by simpa using congrArg Fin.val h4)
    · have hva : ((perm5 i a : Fin 5) : ℕ) < 3 := perm5_lt_three i ha
      have hvb : perm5 i b = b := perm5_not_lt i hb
      have h := congrArg Fin.val hab
      rw [hvb] at h
      omega
  · by_cases hb : (b : ℕ) < 3
    · have hvb : ((perm5 i b : Fin 5) : ℕ) < 3 := perm5_lt_three i hb
      have hva : perm5 i a = a := perm5_not_lt i ha
      have h := congrArg Fin.val hab
      rw [hva] at h
      omega
    · rw [perm5_not_lt i ha, perm5_not_lt i hb] at hab
      exact hab

/-- `perm5 i` is a bijection of `Fin 5`. -/
lemma perm5_bijective (i : Fin 98) : Function.Bijective (perm5 i) :=
  ⟨perm5_injective i, (Finite.injective_iff_surjective.mp (perm5_injective i))⟩

/-- The permutation of `Fin 5` induced by `foldTau i`. -/
noncomputable def perm5Equiv (i : Fin 98) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (perm5 i) (perm5_bijective i)

@[simp] lemma perm5Equiv_apply (i : Fin 98) (j : Fin 5) : perm5Equiv i j = perm5 i j := rfl

/-! ### The matrix of the coordinate permutation and its inverse -/

/-- The inverse of a permutation matrix is the permutation matrix of the inverse permutation. -/
lemma inv_permMatrix (τ : Equiv.Perm (Fin 5)) : (τ.permMatrix ℝ)⁻¹ = (τ⁻¹).permMatrix ℝ := by
  rw [Matrix.inv_eq_left_inv]
  rw [← Matrix.permMatrix_mul, mul_inv_cancel]
  simp

/-- `coordPermMat i` is the permutation matrix of the inverse of `perm5 i`. -/
lemma coordPermMat_eq_permMatrix_inv (i : Fin 98) :
    coordPermMat i = ((perm5Equiv i)⁻¹).permMatrix ℝ := by
  ext j k
  simp only [coordPermMat, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]
  by_cases h : perm5 i k = j
  · have h' : k = (perm5Equiv i)⁻¹ j := (Equiv.eq_symm_apply (perm5Equiv i)).mpr h
    simp only [ite_eq_left h, ite_eq_left h']
  · have h' : ¬ (k = (perm5Equiv i)⁻¹ j) :=
      fun hc => h ((Equiv.eq_symm_apply (perm5Equiv i)).mp hc)
    simp only [ite_eq_right h, ite_eq_right h']

/-- The inverse of `coordPermMat i` is the permutation matrix of `perm5 i`. -/
lemma inv_coordPermMat_eq (i : Fin 98) :
    (coordPermMat i)⁻¹ = (perm5Equiv i).permMatrix ℝ := by
  rw [coordPermMat_eq_permMatrix_inv, inv_permMatrix, inv_inv]

/-- **The inverse coordinate-permutation matrix acts by reindexing the coordinates.** -/
lemma inv_coordPermMat_mulVec (i : Fin 98) (v : Work.HypModel.V5) :
    (coordPermMat i)⁻¹ *ᵥ v = (fun j => v (perm5 i j)) := by
  rw [inv_coordPermMat_eq, Matrix.permMatrix_mulVec]
  funext j
  rfl

/-! ### The coordinates of `hypOfUHS q (perm5 i j)` -/

/-- The first three coordinates of `hypOfUHS q` are `q j / q 3`. -/
lemma hypOfUHS_apply_of_lt_three {q : Work.HypModel.E4} {j : Fin 5} (hj : (j : ℕ) < 3) :
    Work.HypModel.hypOfUHS q j = q ⟨(j : ℕ), by omega⟩ / q 3 := by
  have hcases : ∀ j : Fin 5, (j : ℕ) < 3 → j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rcases hcases j hj with rfl | rfl | rfl <;> simp [Work.HypModel.hypOfUHS]

/-- The `perm5 i`-reindexed coordinate of `hypOfUHS q` below `3` is the `foldTau i`-coordinate
of `q`, divided by the height `q 3`. -/
lemma hypOfUHS_apply_perm5 (i : Fin 98) (q : Work.HypModel.E4) {j : Fin 5}
    (hj : (j : ℕ) < 3) :
    Work.HypModel.hypOfUHS q (perm5 i j)
      = q (foldTau i ⟨(j : ℕ), by omega⟩) / q 3 := by
  have hlt : (perm5 i j : ℕ) < 3 := perm5_lt_three i hj
  rw [hypOfUHS_apply_of_lt_three (q := q) hlt]
  rw [show (⟨((perm5 i j : Fin 5) : ℕ), by omega⟩ : Fin 4) = foldTau i ⟨(j : ℕ), by omega⟩
    from Fin.ext (by simp only [perm5, dite_eq_left hj])]

/-! ### The main identity -/

theorem coordPermInv_eq_mobius (i : Fin 98) {q : Work.FoldInst.E4} (hq : 0 < q 3) :
    Work.FoldInst.coordPermInv i q = Work.HypModel.mobius (Work.RTOwed.coordPermMat i)⁻¹ q := by
  have hq3 : q 3 ≠ 0 := ne_of_gt hq
  have h3 : perm5 i 3 = 3 := perm5_not_lt i (by decide)
  have h4 : perm5 i 4 = 4 := perm5_not_lt i (by decide)
  have h34 : Work.HypModel.hypOfUHS q 4 - Work.HypModel.hypOfUHS q 3 = (q 3)⁻¹ :=
    Work.HypModel.hypOfUHS_four_sub_three hq3
  rw [Work.HypModel.mobius, inv_coordPermMat_mulVec]
  ext j
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by revert j; decide
  rcases hj with rfl | rfl | rfl | rfl
  · rw [coordPermInv_ofLp]
    simp only [Work.HypModel.uhsOfHyp, WithLp.ofLp_toLp]
    rw [h3, h4]
    simp only [Matrix.cons_val_zero]
    rw [h34, inv_inv, hypOfUHS_apply_perm5 i q (by decide : ((0 : Fin 5) : ℕ) < 3)]
    rw [div_mul_cancel₀ _ hq3]
    try rfl
  · rw [coordPermInv_ofLp]
    simp only [Work.HypModel.uhsOfHyp, WithLp.ofLp_toLp]
    rw [h3, h4]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h34, inv_inv, hypOfUHS_apply_perm5 i q (by decide : ((1 : Fin 5) : ℕ) < 3)]
    rw [div_mul_cancel₀ _ hq3]
    try rfl
  · rw [coordPermInv_ofLp]
    simp only [Work.HypModel.uhsOfHyp, WithLp.ofLp_toLp]
    rw [h3, h4]
    simp only [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    rw [h34, inv_inv, hypOfUHS_apply_perm5 i q (by decide : ((2 : Fin 5) : ℕ) < 3)]
    rw [div_mul_cancel₀ _ hq3]
    try rfl
  · rw [coordPermInv_ofLp]
    simp only [Work.HypModel.uhsOfHyp, WithLp.ofLp_toLp]
    rw [h3, h4]
    rw [foldTau_three, h34, inv_inv]
    try rfl

end Work.RTOwed
