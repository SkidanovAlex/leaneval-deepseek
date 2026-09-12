import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.RingTheory.Finiteness.Prod

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Commons.Analysis.InnerProductSpace

/-- The orthogonal-split map `(w, u) ↦ w + u` from `W × Wᗮ` to `E` is measure
preserving for the (product) volume on `W × Wᗮ` and the volume on `E`.

This follows from the fact that the canonical map
`WithLp 2 (W × Wᗮ) ≃ₗᵢ[ℝ] E` (the inverse of
`Submodule.orthogonalDecomposition`) is a linear isometry equivalence, and
that the `toLp` identification `W × Wᗮ ≃ WithLp 2 (W × Wᗮ)` is volume
preserving. -/
theorem orthogonalSplit_measurePreserving {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (W : Submodule ℝ E) :
    MeasureTheory.MeasurePreserving (fun p : W × Wᗮ => (p.1 : E) + (p.2 : E))
      (MeasureTheory.volume : MeasureTheory.Measure (W × Wᗮ))
      (MeasureTheory.volume : MeasureTheory.Measure E) := by
  -- The inverse of the orthogonal decomposition is a linear isometry
  -- `WithLp 2 (W × Wᗮ) → E` sending `toLp (w, u)` to `w + u`.
  have hg : MeasureTheory.MeasurePreserving
      (W.orthogonalDecomposition.symm : WithLp 2 (↥W × ↥Wᗮ) → E)
      MeasureTheory.volume MeasureTheory.volume :=
    LinearIsometryEquiv.measurePreserving (W.orthogonalDecomposition.symm)
  -- `toLp : W × Wᗮ → WithLp 2 (W × Wᗮ)` is volume preserving.
  have hf : MeasureTheory.MeasurePreserving
      (WithLp.toLp 2 : ↥W × ↥Wᗮ → WithLp 2 (↥W × ↥Wᗮ))
      MeasureTheory.volume MeasureTheory.volume :=
    WithLp.volume_preserving_toLp (↥W) (↥Wᗮ)
  -- Pointwise, `W.orthogonalDecomposition.symm ∘ toLp` is exactly the map
  -- `(w, u) ↦ w + u`.
  have hfun : (fun p : ↥W × ↥Wᗮ => (p.1 : E) + (p.2 : E)) =
      fun p => W.orthogonalDecomposition.symm (WithLp.toLp 2 p) := by
    funext p
    symm
    calc
      W.orthogonalDecomposition.symm (WithLp.toLp 2 p)
          = (W.orthogonalDecomposition.symm.toLinearEquiv) (WithLp.toLp 2 p) := rfl
      _ = (W.prodEquivOfIsCompl Wᗮ W.isCompl_orthogonal) p := by
          rw [Submodule.toLinearEquiv_orthogonalDecomposition_symm]
          simp
      _ = (p.1 : E) + (p.2 : E) := by
          exact Submodule.coe_prodEquivOfIsCompl' W Wᗮ W.isCompl_orthogonal p
  convert hg.comp hf using 1
  exact hfun

end Commons.Analysis.InnerProductSpace