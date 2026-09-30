import Mathlib
import Submission.Work.BW.sieg2_PhiE_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped Classical

/--
**Surjectivity of `Phi`.**  Let `a : Fin M → Fin N → F` be a family of rows that is
`F`-linearly independent.  Then the `ℝ`-linear map
`Phi a : (Fin N → KE F) →ₗ[ℝ] (Fin M → KE F)`, `y ↦ (∑_j mulK (a i j) (y j))_i`,
sending a tuple of vectors of the Euclidean mixed space through the matrix `a`, is
surjective.

This is the `ℝ`-linear "scalar extension" of the `F`-linear map `F^N → F^M` given by the
matrix `a`: the rows of `a` being linearly independent, that map is surjective, and
surjectivity is preserved by extending scalars.  Concretely, for every `i` we pick a
preimage `y i ∈ F^N` of the standard basis vector `Pi.single i 1`; then
`j ↦ ∑_i mulK (y i j) (z i)` is a preimage of `z`.
-/
theorem Phi_surjective {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F) (hli : LinearIndependent F a) :
    Function.Surjective (Phi a) := by
  -- The matrix of scalars `a` defines a surjective `F`-linear map `F^N → F^M`, because its
  -- rows are linearly independent (so the row rank is `M`, hence so is the column rank).
  have hsurj : Function.Surjective (Matrix.mulVecLin (Matrix.of a)) := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Matrix.range_mulVecLin, ← Matrix.rank_eq_finrank_span_cols]
    rw [← Matrix.rank_transpose, Matrix.rank_eq_finrank_span_cols]
    have hcol : (Matrix.of a).transpose.col = a := rfl
    rw [hcol, finrank_span_eq_card hli, Fintype.card_fin, Module.finrank_pi, Fintype.card_fin]
  intro z
  choose y hy using fun i : Fin M => hsurj ((Pi.single i (1 : F)) : Fin M → F)
  refine ⟨fun j => ∑ i, mulK (y i j) (z i), ?_⟩
  ext i'
  rw [Phi_apply]
  -- `mulK` is multiplicative, so multiplication by the `i'`-th row commutes with the inner sum.
  have h1 : ∀ j, mulK (a i' j) (∑ i, mulK (y i j) (z i))
      = ∑ i, mulK (a i' j * y i j) (z i) := by
    intro j
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mulK_mul]
    rfl
  simp only [h1]
  rw [Finset.sum_comm]
  -- The `i`-th block reproduces the `i`-th coordinate `z i`, since `y i` solves `a *ᵥ y i = e_i`.
  have h2 : ∀ i, (∑ j, mulK (a i' j * y i j) (z i))
      = mulK ((Pi.single i (1 : F) : Fin M → F) i') (z i) := by
    intro i
    rw [← mulK_sum]
    have hh := congrFun (hy i) i'
    have hsum : ∑ j, a i' j * y i j = (Pi.single i (1 : F) : Fin M → F) i' := by
      simpa [Matrix.mulVecLin_apply, Matrix.mulVec_apply, dotProduct, Matrix.of_apply] using hh
    rw [hsum]
  simp only [h2]
  rw [Finset.sum_eq_single i']
  · rw [Pi.single_eq_same, mulK_one]
    rfl
  · intro b _ hb
    rw [Pi.single_eq_of_ne (Ne.symm hb), mulK_zero]
    simp
  · intro h
    exact absurd (Finset.mem_univ i') h

end Work.BW
