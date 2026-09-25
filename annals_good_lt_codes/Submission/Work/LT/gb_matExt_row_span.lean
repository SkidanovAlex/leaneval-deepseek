import Mathlib
import Submission.Work.LT.gb_ext_defs

/-!
# Row decomposition for `GB.matExt` and the row span

For an `A`-extension operator `T₁` and a `B`-extension operator `T₂`, the matrix
`y = GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x` has the property that, for each `i ∈ A`, the
`i`-th row of `y` is `∑ j ∈ B, x (i,j) • GB.opVec T₂ j`, and consequently every row of `y` is a
linear combination of the rows with index in `A`:

`GB.row y p = ∑ i ∈ A, (GB.opVec T₁ i p) • GB.row y i`.

This is the key step in `Work.LT.gb_matExt_rowwise`: it says precisely that `GB.matExt` restricted
to `A`-rows determines all rows.  We package it here (together with the resulting span statement
`Work.LT.gb_matExt_row_span`) so that it can be reused.
-/

namespace Work.LT

namespace GB

variable {D : ℕ}

/-- For `i ∈ A`, the `i`-th row of `GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x` only sees the
`i`-th row of `x`. -/
lemma matExt_opVec_row_agree {CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (A B : Finset (Fin D)) (T₁ : GB.ExtOp CA A) (T₂ : GB.ExtOp CB B)
    (x : Fin D × Fin D → ZMod 2) {i : Fin D} (hi : i ∈ A) :
    GB.row (GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x) i =
      fun q => ∑ j ∈ B, x (i, j) * GB.opVec T₂ j q := by
  funext q
  change GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x (i, q) =
    ∑ j ∈ B, x (i, j) * GB.opVec T₂ j q
  rw [GB.matExt_apply]
  trans ∑ i' ∈ A, (GB.opVec T₁ i' i) * (∑ j ∈ B, x (i', j) * GB.opVec T₂ j q)
  · apply Finset.sum_congr rfl
    intro i' hi'
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · trans ∑ i' ∈ A, (if i = i' then 1 else 0) * (∑ j ∈ B, x (i', j) * GB.opVec T₂ j q)
    · apply Finset.sum_congr rfl
      intro i' hi'
      rw [GB.ExtOp.opVec_agree (T := T₁) hi]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro b hb hbne
        simp [Ne.symm hbne]
      · intro h
        exact absurd hi h

end GB

/-- Every row of `GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x` is a linear combination of the rows
with index in `A`. -/
lemma gb_matExt_row_eq_sum {D : ℕ} {CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (A B : Finset (Fin D)) (T₁ : GB.ExtOp CA A) (T₂ : GB.ExtOp CB B)
    (x : Fin D × Fin D → ZMod 2) (p : Fin D) :
    GB.row (GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x) p =
      ∑ i ∈ A, (GB.opVec T₁ i p) •
        GB.row (GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x) i := by
  classical
  set y : Fin D × Fin D → ZMod 2 := GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x with hy
  have hA : ∀ i ∈ A, ∀ q, y (i, q) = ∑ j ∈ B, x (i, j) * GB.opVec T₂ j q := by
    intro i hi q
    rw [hy]
    exact congrFun (GB.matExt_opVec_row_agree A B T₁ T₂ x hi) q
  funext q
  calc (GB.row y p) q = y (p, q) := rfl
    _ = ∑ i ∈ A, GB.opVec T₁ i p * (∑ j ∈ B, x (i, j) * GB.opVec T₂ j q) := by
          rw [hy, GB.matExt_apply]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = ∑ i ∈ A, GB.opVec T₁ i p * y (i, q) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hA i hi q]
    _ = (∑ i ∈ A, (GB.opVec T₁ i p) • GB.row y i) q := by
          rw [Finset.sum_apply]
          apply Finset.sum_congr rfl
          intro i hi
          simp [GB.row]

theorem gb_matExt_row_span {D : ℕ} {CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (A B : Finset (Fin D)) (T₁ : GB.ExtOp CA A) (T₂ : GB.ExtOp CB B)
    (x : Fin D × Fin D → ZMod 2) (p : Fin D) :
    GB.row (GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x) p ∈
      Submodule.span (ZMod 2) (Set.range (fun i' : {i : Fin D // i ∈ A} =>
        GB.row (GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x) ↑i')) := by
  rw [gb_matExt_row_eq_sum A B T₁ T₂ x p]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

end Work.LT
