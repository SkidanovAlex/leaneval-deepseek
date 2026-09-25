import Mathlib
import Submission.Work.LT.gb_ext_defs

namespace Work.LT

open Finset
open scoped BigOperators

namespace GB

/-- Key linear-algebra identity behind `Work.LT.gb_matExt_col_span`: every column of
`matExt A B u w x` is the `B`-linear combination of the columns indexed by `B`.

Concretely, `matExt A B u w x (p₁,p₂) = ∑_{i∈A} ∑_{j∈B} x (i,j) * u i p₁ * w j p₂`, so on the
one hand the column at `q` expands as `∑_{i∈A} ∑_{j∈B} x (i,j) * u i p * w j q`, while for
`j' ∈ B` the extension operator identity `w j j' = [j' = j]` collapses the column at `j'` to
`∑_{i∈A} x (i,j') * u i p`; exchanging the two sums gives the claim. -/
lemma col_matExt_eq_sum {D : ℕ} {CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (A B : Finset (Fin D)) (T₁ : GB.ExtOp CA A) (T₂ : GB.ExtOp CB B)
    (x : Fin D × Fin D → ZMod 2) (q : Fin D) :
    GB.col (GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x) q =
      ∑ j ∈ B, (GB.opVec T₂ j q) • GB.col (GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x) j := by
  funext p
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, GB.col, GB.matExt_apply]
  have key : ∀ j ∈ B, (∑ x_2 ∈ A, ∑ x_3 ∈ B,
        x (x_2, x_3) * GB.opVec T₁ x_2 p * GB.opVec T₂ x_3 j)
      = ∑ i ∈ A, x (i, j) * GB.opVec T₁ i p := by
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    have h1 : ∀ k ∈ B, x (i, k) * GB.opVec T₁ i p * GB.opVec T₂ k j
        = (if j = k then x (i, k) * GB.opVec T₁ i p else 0) := by
      intro k hk
      rw [T₂.opVec_agree hj]
      split <;> simp
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq]
    simp [hj]
  symm
  calc (∑ x_1 ∈ B, GB.opVec T₂ x_1 q * ∑ x_2 ∈ A, ∑ x_3 ∈ B,
          x (x_2, x_3) * GB.opVec T₁ x_2 p * GB.opVec T₂ x_3 x_1)
      = ∑ j ∈ B, GB.opVec T₂ j q * ∑ i ∈ A, x (i, j) * GB.opVec T₁ i p := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [key j hj]
    _ = ∑ j ∈ B, ∑ i ∈ A, GB.opVec T₂ j q * (x (i, j) * GB.opVec T₁ i p) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
    _ = ∑ i ∈ A, ∑ j ∈ B, GB.opVec T₂ j q * (x (i, j) * GB.opVec T₁ i p) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ A, ∑ j ∈ B, x (i, j) * GB.opVec T₁ i p * GB.opVec T₂ j q := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring

end GB

theorem gb_matExt_col_span {D : ℕ} {CA CB : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (A B : Finset (Fin D)) (T₁ : GB.ExtOp CA A) (T₂ : GB.ExtOp CB B)
    (x : Fin D × Fin D → ZMod 2) (q : Fin D) :
    GB.col (GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x) q ∈
      Submodule.span (ZMod 2) (Set.range (fun j' : {j : Fin D // j ∈ B} =>
        GB.col (GB.matExt A B (GB.opVec T₁) (GB.opVec T₂) x) ↑j')) := by
  rw [GB.col_matExt_eq_sum A B T₁ T₂ x q]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)

end Work.LT
