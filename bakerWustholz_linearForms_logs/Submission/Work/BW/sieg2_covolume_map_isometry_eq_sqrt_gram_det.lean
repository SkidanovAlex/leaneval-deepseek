import Mathlib
import Submission.Work.BW.covolume_isometry_map_volume
import Submission.Work.BW.covolume_sqrt_gram_det_arb

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Covolume of a `ℤ`-lattice as `√(det Gram)`, against the Lebesgue measure of an abstract
Euclidean space

Let `E` be a finite-dimensional real inner product space, `Λ ⊆ E` a full `ℤ`-lattice and
`b : Basis ι ℤ Λ` a `ℤ`-basis of `Λ`.  Given an isometry `e : EuclideanSpace ℝ (Fin k) ≃ᵢ E`
from the Euclidean coordinate model, the push-forward `Measure.map e volume` is the Lebesgue
measure of `E` (an isometry preserves Haar measure), and the covolume of `Λ` for that measure is
the square root of the Gram determinant of the vectors `b i ∈ E`.

The proof is a three-line assembly of results already in the tree:

* `Work.BW.covolume_isometry_map_volume`: an isometry pushes `volume` forward to `volume`;
* `Module.Basis.ofZLatticeBasis_span`: a `ℤ`-basis of `Λ` is in particular a real basis of `E`
  whose `ℤ`-span is `Λ`, so the lattice of the statement is the `ℤ`-span of a real basis;
* `Work.BW.covolume_sqrt_gram_det_arb`: the covolume of the `ℤ`-span of a real basis is
  `√|det Gram|`, and the Gram matrix of a family of vectors is positive semidefinite, so the
  determinant is nonnegative and the absolute value can be dropped.
-/

namespace Work.BW

theorem sieg2_covolume_map_isometry_eq_sqrt_gram_det {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {k : ℕ} (e : EuclideanSpace ℝ (Fin k) ≃ᵢ E)
    (Λ : Submodule ℤ E) [DiscreteTopology ↥Λ] [IsZLattice ℝ Λ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ ↥Λ) :
    ZLattice.covolume Λ (MeasureTheory.Measure.map e MeasureTheory.volume) =
      Real.sqrt (Matrix.det (Matrix.of (fun i j : ι => inner ℝ ((b i : E)) (b j : E)))) := by
  classical
  -- an isometry pushes the Lebesgue measure forward to the Lebesgue measure
  rw [covolume_isometry_map_volume e]
  -- the `ℤ`-basis `b` of `Λ` is also a real basis of `E` whose `ℤ`-span is `Λ`
  have hspan : Submodule.span ℤ (Set.range ⇑(b.ofZLatticeBasis ℝ Λ)) = Λ :=
    b.ofZLatticeBasis_span ℝ Λ
  conv_lhs => rw [← hspan]
  -- covolume of the `ℤ`-span of a real basis is the square root of the Gram determinant
  rw [covolume_sqrt_gram_det_arb (b.ofZLatticeBasis ℝ Λ)]
  -- identify the Gram matrix of that real basis with the Gram matrix of the `ℤ`-basis
  have hgram : (Matrix.gram ℝ ⇑(b.ofZLatticeBasis ℝ Λ))
      = Matrix.of (fun i j : ι => inner ℝ ((b i : E)) (b j : E)) := by
    ext i j
    simp [Matrix.gram_apply]
  -- a Gram matrix is positive semidefinite, so its determinant is nonnegative
  have hD : 0 ≤ (Matrix.det (Matrix.of (fun i j : ι => inner ℝ ((b i : E)) (b j : E)))) :=
    Matrix.PosSemidef.det_nonneg (Matrix.posSemidef_gram ℝ (fun i : ι => ((b i : ↥Λ) : E)))
  rw [hgram, abs_of_nonneg hD]

end Work.BW
