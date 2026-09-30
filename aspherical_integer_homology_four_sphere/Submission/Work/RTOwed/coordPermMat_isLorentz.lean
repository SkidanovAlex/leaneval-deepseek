/-
# `coordPermMat` is a Lorentz matrix

The fold data of `M̄` attaches to each of the 98 fold classes `i` a coordinate permutation `perm5 i`
of the five coordinates of `ℝ⁵` (the first three coordinates are permuted by `foldTau i`, which
fixes the height coordinate `3`; the last two coordinates `3` and `4` are fixed).  The matrix
`coordPermMat i` of this permutation is the Möbius matrix realising `Work.FoldInst.coordPerm i` as a
Möbius transformation of the upper half space, and the transitions of the fold charts are therefore
Möbius transformations (`Work.RTOwed.transMat`), whose smoothness and isometry properties come from
`Work.HypModel.mobius_contDiffOn` / `Work.HypModel.mobius_isometry`, both of which require their
matrix to lie in the Lorentz group and to preserve the upper sheet.

The content of this file is therefore:

* `permMatOf σ` — the `0`-`1` matrix of a map `σ : Fin 5 → Fin 5`;
* `permMatOf_isLorentz` — a permutation matrix that fixes the timelike coordinate `4` is Lorentz
  (it is an isometry of the Lorentz form `J = diag(1,1,1,1,-1)` and its `(4,4)` entry is `1`);
* `perm5_injective` / `perm5_four` — `perm5 i` is a bijection fixing `4`, since it permutes `0,1,2`
  by the bijection `foldTau i` (which fixes `3`) and fixes `3,4`;
* `coordPermMat_isLorentz` — the requested statement.
-/
import Mathlib
import Submission.Work.RTOwed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

noncomputable section

open Matrix

/-! ### Permutation matrices -/

/-- The `0`-`1` matrix of a map `σ : Fin 5 → Fin 5`: the entry `(j,k)` is `1` exactly when
`σ k = j`.  For a bijective `σ` this is the matrix of the coordinate permutation `x ↦ x ∘ σ`, i.e.
`permMatOf σ *ᵥ x` is `x` reindexed along `σ`. -/
def permMatOf (σ : Fin 5 → Fin 5) : Matrix (Fin 5) (Fin 5) ℝ := fun j k =>
  if σ k = j then 1 else 0

/-- **A permutation matrix fixing the timelike coordinate is Lorentz.**  If `σ` is injective
(hence a bijection of `Fin 5`) and `σ 4 = 4` — so that `σ` permutes the spacelike coordinates
`0,1,2,3` and fixes the timelike one — then `permMatOf σ` satisfies `Pᵀ J P = J` and has `(4,4)`
entry `1`. -/
theorem permMatOf_isLorentz {σ : Fin 5 → Fin 5} (hinj : Function.Injective σ) (h4 : σ 4 = 4) :
    Work.HypModel.IsLorentzMat (permMatOf σ) := by
  have hσ4 : ∀ k : Fin 5, σ k = 4 ↔ k = 4 := by
    intro k
    exact ⟨fun h => hinj (by rw [h, h4]), fun h => by rw [h, h4]⟩
  constructor
  · ext i j
    rw [Matrix.mul_apply]
    simp only [Work.HypModel.J, Matrix.mul_diagonal, permMatOf, Matrix.transpose_apply,
      Matrix.diagonal_apply]
    rw [Finset.sum_eq_single (σ i)]
    · simp only [ite_true, one_mul, hσ4 i]
      by_cases h : i = j
      · subst h; simp
      · have h2 : ¬ (σ j = σ i) := fun hh => h (hinj hh).symm
        simp [h, h2]
    · intro b _ hb
      simp [show ¬ (σ i = b) from fun h => hb h.symm]
    · intro h
      exact absurd (Finset.mem_univ (σ i)) h
  · simp only [permMatOf, h4]
    norm_num

/-! ### The permutation `perm5 i` of the five coordinates -/

theorem perm5_of_lt_val (i : Fin 98) {j : Fin 5} (hj : (j : ℕ) < 3) :
    ((perm5 i j : ℕ)) = ((Work.FoldInst.foldTau i ⟨(j : ℕ), by omega⟩ : Fin 4) : ℕ) := by
  simp only [perm5]
  rw [dite_eq_left hj]

theorem perm5_of_not_lt (i : Fin 98) {j : Fin 5} (hj : ¬ (j : ℕ) < 3) : perm5 i j = j := by
  simp only [perm5]
  rw [dite_eq_right hj]

/-- The first three coordinates stay in the first three coordinates: `perm5 i` permutes `0,1,2`. -/
theorem perm5_val_lt (i : Fin 98) {j : Fin 5} (hj : (j : ℕ) < 3) : ((perm5 i j : ℕ)) < 3 := by
  rw [perm5_of_lt_val i hj]
  have hne : ((Work.FoldInst.foldTau i ⟨(j : ℕ), by omega⟩ : Fin 4) : ℕ) ≠ 3 := by
    intro h
    have h1 : (Work.FoldInst.foldTau i ⟨(j : ℕ), by omega⟩ : Fin 4) = (3 : Fin 4) :=
      Fin.ext (by simpa using h)
    have h3 : (⟨(j : ℕ), by omega⟩ : Fin 4) = (3 : Fin 4) :=
      (Work.FoldInst.foldTau_bijective i).1 (h1.trans (Work.FoldInst.foldTau_three i).symm)
    have h4 : (j : ℕ) = 3 := by simpa using congrArg Fin.val h3
    omega
  have hlt := (Work.FoldInst.foldTau i ⟨(j : ℕ), by omega⟩ : Fin 4).isLt
  omega

/-- `perm5 i` is injective: it permutes the first three coordinates via the bijection `foldTau i`
(which fixes `3`) and fixes the last two. -/
private theorem perm5_injective (i : Fin 98) : Function.Injective (perm5 i) := by
  intro j k h
  by_cases hj : (j : ℕ) < 3 <;> by_cases hk : (k : ℕ) < 3
  · have hA := perm5_of_lt_val i hj
    have hB := perm5_of_lt_val i hk
    have hv := congrArg Fin.val h
    rw [hA, hB] at hv
    have h1 : (⟨(j : ℕ), by omega⟩ : Fin 4) = ⟨(k : ℕ), by omega⟩ :=
      (Work.FoldInst.foldTau_bijective i).1 (Fin.ext hv)
    have h2 : (j : ℕ) = (k : ℕ) := by simpa using congrArg Fin.val h1
    exact Fin.ext h2
  · have hA := perm5_val_lt i hj
    rw [perm5_of_not_lt i hk] at h
    have hv := congrArg Fin.val h
    exfalso
    omega
  · have hA := perm5_val_lt i hk
    rw [perm5_of_not_lt i hj] at h
    have hv := congrArg Fin.val h
    exfalso
    omega
  · rw [perm5_of_not_lt i hj, perm5_of_not_lt i hk] at h
    exact h

/-- `perm5 i` fixes the height coordinate `4` (as it fixes `3`). -/
theorem perm5_four (i : Fin 98) : perm5 i 4 = 4 := by
  simp only [perm5]
  rw [dite_eq_right (show ¬ ((4 : Fin 5) : ℕ) < 3 from by decide +kernel)]

theorem perm5_three (i : Fin 98) : perm5 i 3 = 3 := by
  simp only [perm5]
  rw [dite_eq_right (show ¬ ((3 : Fin 5) : ℕ) < 3 from by decide +kernel)]

/-! ### The requested statement -/

theorem coordPermMat_isLorentz (i : Fin 98) : Work.HypModel.IsLorentzMat (Work.RTOwed.coordPermMat i) :=
  permMatOf_isLorentz (perm5_injective i) (perm5_four i)

end

end Work.RTOwed
