import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary bound for mixed-embedding coordinates

The per-place bound used when converting a bound on the `mixedEmbedding.stdBasis` coordinates of
an integral tuple into a bound on the (logarithmic) height: at a real place the embedding norm is
bounded by `ρ`, at a complex place by `√2 · ρ` (because the real and imaginary parts are each
bounded by `ρ`).
-/

noncomputable section

open Classical

namespace Work.BW

open NumberField

/-- The per-place bound on the norm of a mixed embedding: `ρ` at a real place, `√2 · ρ` at a
complex place. -/
def placeBound {F : Type*} [Field F] (ρ : ℝ) (v : NumberField.InfinitePlace F) : ℝ :=
  if NumberField.InfinitePlace.IsReal v then ρ else Real.sqrt 2 * ρ

@[simp]
lemma placeBound_of_isReal {F : Type*} [Field F] {ρ : ℝ}
    {v : NumberField.InfinitePlace F} (hv : v.IsReal) : placeBound ρ v = ρ := by
  rw [placeBound, if_pos hv]

@[simp]
lemma placeBound_of_isComplex {F : Type*} [Field F] {ρ : ℝ}
    {v : NumberField.InfinitePlace F} (hv : v.IsComplex) :
    placeBound ρ v = Real.sqrt 2 * ρ := by
  rw [placeBound, if_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hv)]

end Work.BW
