import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.RingTheory.TotallySplit

/-!
# Cardinality of the cokernel of an integer matrix = |det|

For a square integer matrix `M : Matrix ι ι ℤ` with `det M ≠ 0`, the additive
quotient `(ι → ℤ) ⧸ im (mulVecLin M)` (the cokernel of the matrix linear map) is
finite with cardinality `|det M|`.

The engine is Mathlib's
`LinearAlgebra/FreeModule/Finite/CardQuotient.lean`
(`Submodule.natAbs_det_equiv`: for a full-rank submodule `N ≤ M`, `|M ⧸ N|` is the
absolute determinant of any `ℤ`-linear equivalence `M ≃ N`); applied to
`N = L.range` with `L = LinearEquiv.ofInjective`, this gives the module-level core
`natCard_quotient_range_eq_det`.  The matrix form uses
`LinearMap.det_toLin'` (`det (toLin' M) = M.det`, with `mulVecLin` definitionally
`toLin'`) and `Matrix.mulVec_injective_of_det_ne_zero` (injectivity of `M.mulVec`
over `ℤ` when `det M ≠ 0`).
-/

noncomputable section

namespace Commons.LinearAlgebra.Matrix

/-- **Module core**: for an injective `ℤ`-linear endomorphism `L` of a finite free
`ℤ`-module `M`, the additive quotient `M ⧸ L.range` has cardinality
`|det L|` (the index of the image lattice). -/
lemma natCard_quotient_range_eq_det {M : Type} [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M]
    (L : M →ₗ[ℤ] M) (hL : Function.Injective L) :
    Nat.card (M ⧸ (L.range : Submodule ℤ M)) = (LinearMap.det L).natAbs := by
  have h := Submodule.natAbs_det_equiv (N := L.range) (LinearEquiv.ofInjective L hL)
  rw [← h]
  congr 1

/-- `det M ≠ 0` over `ℤ` makes the matrix linear map injective. -/
lemma mulVecLin_injective_of_det_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (hM : M.det ≠ 0) :
    Function.Injective (Matrix.mulVecLin M) := by
  rw [Matrix.coe_mulVecLin]
  exact Matrix.mulVec_injective_of_det_ne_zero (R := ℤ) hM

/-- **The determinant-index bridge**: for `M : Matrix ι ι ℤ` with `det M ≠ 0`, the
additive quotient `ι → ℤ` by the image of the matrix linear map has cardinality
`|det M|`. -/
lemma card_quotient_range_matrix {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (hM : M.det ≠ 0) :
    Nat.card ((ι → ℤ) ⧸ ((Matrix.mulVecLin M).range : Submodule ℤ (ι → ℤ))) =
      M.det.natAbs := by
  have hI : Function.Injective (Matrix.mulVecLin M) :=
    mulVecLin_injective_of_det_ne_zero M hM
  rw [natCard_quotient_range_eq_det (Matrix.mulVecLin M) hI]
  congr 1
  exact (LinearMap.det_toLin' (R := ℤ) (ι := ι) M)

end Commons.LinearAlgebra.Matrix

end