import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the sharp Siegel/Bombieri–Vaaler step (`siegel_short_vector2`)

This file fixes the vocabulary used by `Submission.Work.BW.siegel_short_vector2` and by the
lemmas it delegates.  Everything lives in the *mixed coordinates* of `F^N`: the mixed space
`E = mixedSpace F` is `ℝ^{r₁} × ℂ^{r₂}`, and `mixedEmbedding.stdBasis F` is the orthonormal
basis of `E` whose coordinates are (real part) / (real part, imaginary part).  Hence
`SiegCoord F N = ℝ^{d·N}` isometrically, with `d = [F : ℚ]`, and the standard inner product
is implemented below by the explicit `Finset` sums `siegInner` (avoids needing a `Fintype`
instance on `mixedEmbedding.index F`).
-/

open NumberField
open scoped Classical

namespace Work.BW

/-- The mixed coordinates of a tuple of `N` elements of `F`: an element of `ℝ^{d N}`. -/
abbrev SiegCoord (F : Type*) [Field F] (N : ℕ) :=
  Fin N → (NumberField.mixedEmbedding.index F → ℝ)

/-- The mixed coordinates of a tuple `x : Fin N → 𝓞 F`. -/
noncomputable def siegCoord {F : Type*} [Field F] [NumberField F] {N : ℕ}
    (x : Fin N → 𝓞 F) : SiegCoord F N :=
  fun j k => (NumberField.mixedEmbedding.stdBasis F).repr
    (NumberField.mixedEmbedding F ((x j : 𝓞 F) : F)) k

/-- The mixed coordinates of the tuple with entries `x j : F` (not necessarily integral). -/
noncomputable def siegCoordF {F : Type*} [Field F] [NumberField F] {N : ℕ}
    (x : Fin N → F) : SiegCoord F N :=
  fun j k => (NumberField.mixedEmbedding.stdBasis F).repr
    (NumberField.mixedEmbedding F (x j)) k

/-- The standard Euclidean inner product on `ℝ^{d N}` in mixed coordinates, written as a sum
over the *infinite places* (each contributing once: the product in the real coordinate for a
real place, and the real form `Re(z̄w)` in the pair of real coordinates for a complex place). -/
noncomputable def siegInner {F : Type*} [Field F] [NumberField F] {N : ℕ}
    (x y : SiegCoord F N) : ℝ :=
  ∑ j : Fin N, ∑ w : NumberField.InfinitePlace F,
    if hw : NumberField.InfinitePlace.IsReal w then
      x j (Sum.inl ⟨w, hw⟩) * y j (Sum.inl ⟨w, hw⟩)
    else
      x j (Sum.inr (⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩, 0)) *
        y j (Sum.inr (⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩, 0))
      + x j (Sum.inr (⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩, 1)) *
        y j (Sum.inr (⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩, 1))

/-- The Gram determinant of a family of tuples of algebraic integers, in mixed coordinates. -/
noncomputable def siegGramDet {F : Type*} [Field F] [NumberField F] {N k : ℕ}
    (v : Fin k → (Fin N → 𝓞 F)) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of (fun i i' : Fin k =>
    siegInner (siegCoord (v i)) (siegCoord (v i')))))

end Work.BW

namespace Work.BW

/-- The Gram determinant of a family of vectors *already in mixed coordinates*. -/
noncomputable def siegGramDetC {F : Type*} [Field F] [NumberField F] {N k : ℕ}
    (v : Fin k → SiegCoord F N) : ℝ :=
  Real.sqrt (Matrix.det (Matrix.of (fun i i' : Fin k =>
    siegInner (v i) (v i'))))

end Work.BW
