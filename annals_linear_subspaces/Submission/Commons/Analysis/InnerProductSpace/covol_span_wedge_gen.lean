import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul
import Submission.Commons.Lattice.Minkowski.covol_span_wedge

open scoped BigOperators
open MeasureTheory MeasureTheory.Measure Module

set_option maxHeartbeats 800000

namespace Commons.Analysis.InnerProductSpace

/-- The top exterior power of an orthonormal family has norm one.

This is `Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal` without the hypothesis
`0 < k`: for the empty index type the family is orthonormal vacuously and the statement is
still true (the `0`-fold wedge product has squared norm `det (gram ℝ u) = det 1 = 1`). -/
private lemma norm_iMulti_orthonormal' {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (u : Fin k → E)
    (hu : Orthonormal ℝ u) :
    ‖exteriorPower.ιMulti ℝ k u‖ = 1 := by
  classical
  have hsq : ‖exteriorPower.ιMulti ℝ k u‖ ^ 2 = 1 := by
    calc
      ‖exteriorPower.ιMulti ℝ k u‖ ^ 2 =
          inner ℝ (exteriorPower.ιMulti ℝ k u) (exteriorPower.ιMulti ℝ k u) := by
        exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (exteriorPower.ιMulti ℝ k u)).symm
      _ = (Matrix.gram ℝ u).det := by rw [exteriorPower.inner_ιMulti_self]
      _ = (1 : Matrix (Fin k) (Fin k) ℝ).det := by
        rw [Matrix.gram_eq_one_iff_orthonormal.mpr hu]
      _ = 1 := by simp
  have hnonneg : 0 ≤ ‖exteriorPower.ιMulti ℝ k u‖ := norm_nonneg _
  rcases (sq_eq_one_iff.mp hsq) with h | h
  · exact h
  · linarith

/-- **Covolume of the `ℤ`-span of a basis equals the norm of its top wedge, in a general
finite-dimensional real inner product space.**

Let `E` be a finite-dimensional real inner product space and `b : Module.Basis (Fin k) ℝ E` a
`ℝ`-basis of `E`. Then the `ℤ`-lattice spanned by `b` has covolume equal to the norm of its top
exterior power `‖exteriorPower.ιMulti ℝ k ⇑b‖`.

This is the general-index generalisation of `Commons.Lattice.Minkowski.covol_span_wedge` (which is
the special case `E = EuclideanSpace ℝ (Fin n)`, `b` the standard orthonormal basis). Proof route
(same as `covol_span_wedge`, replacing the standard orthonormal basis of `EuclideanSpace ℝ (Fin n)`
by an arbitrary orthonormal basis `b₀ : Module.Basis (Fin k) ℝ E` of `E`, obtained for instance
from `Commons.LinearAlgebra.BilinForm.exists_orthonormal_basis` applied to the inner product
bilinear form):
- `ZLattice.covolume_eq_measure_fundamentalDomain` + `ZSpan.isAddFundamentalDomain` +
  `ZSpan.measureReal_fundamentalDomain`: `covolume (span ℤ (range b)) = |b₀.det ⇑b| *
   volume.real (ZSpan.fundamentalDomain b₀)`, and the fundamental domain of the orthonormal basis
  `b₀` has real volume `1`;
- `Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul` writes `ιMulti ⇑b = A.det • ιMulti b₀`
  where `A := b₀.toMatrix ⇑b`, and `Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal`
  gives `‖ιMulti b₀‖ = 1`; hence `‖ιMulti ℝ k ⇑b‖ = |A.det|`;
- finally `Basis.det_apply` identifies `|b₀.det ⇑b|` with `|(b₀.toMatrix ⇑b).det|`.

The instances `DiscreteTopology (Submodule.span ℤ (Set.range ⇑b))` and
`IsZLattice ℝ (Submodule.span ℤ (Set.range ⇑b))` are available (`ZSpan` and
`instIsZLatticeRealSpan`). -/
theorem covol_span_wedge_gen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ}
    (b : Module.Basis (Fin k) ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range ⇑b)) = ‖exteriorPower.ιMulti ℝ k ⇑b‖ := by
  classical
  -- `E` has `ℝ`-dimension `k`, since it has a basis indexed by `Fin k`.
  have hk : Module.finrank ℝ E = k := by
    rw [Module.finrank_eq_card_basis b]
    simp
  -- An orthonormal basis of `E`, indexed by `Fin k`.
  let ob₀ : OrthonormalBasis (Fin k) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hk)
  let b₀ : Module.Basis (Fin k) ℝ E := ob₀.toBasis
  have horth : Orthonormal ℝ (⇑b₀) := ob₀.orthonormal
  -- The fundamental domain of the orthonormal basis has real volume `1`.
  have hvol0 : (volume : Measure E).real (ZSpan.fundamentalDomain b₀) = 1 := by
    have hae := ZSpan.fundamentalDomain_ae_parallelepiped b₀ (volume : Measure E)
    rw [measureReal_congr hae]
    have hp : volume (parallelepiped ⇑b₀) = 1 := ob₀.volume_parallelepiped
    rw [measureReal_def, hp]
    simp
  -- `covolume` is the real volume of a fundamental domain.
  have hcov : ZLattice.covolume (Submodule.span ℤ (Set.range ⇑b)) =
      (volume : Measure E).real (ZSpan.fundamentalDomain b) :=
    ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain b volume)
  -- Change of basis: volume scales by the (absolute) determinant of the change matrix.
  have hvol : (volume : Measure E).real (ZSpan.fundamentalDomain b) =
      |b₀.det ⇑b| * (volume : Measure E).real (ZSpan.fundamentalDomain b₀) :=
    ZSpan.measureReal_fundamentalDomain b volume b₀
  -- The coordinates of `b` in the orthonormal basis `b₀`.
  have hw : ∀ j : Fin k, b j = ∑ i : Fin k, (b₀.toMatrix ⇑b) i j • b₀ i := by
    intro j
    rw [← Module.Basis.sum_repr b₀ (b j)]
    exact Finset.sum_congr rfl fun i _ => by rw [Module.Basis.toMatrix_apply]
  -- Wedge products transform by the determinant of the change matrix.
  have hwedge : exteriorPower.ιMulti ℝ k ⇑b =
      (b₀.toMatrix ⇑b).det • exteriorPower.ιMulti ℝ k ⇑b₀ :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul (u := ⇑b₀) (A := b₀.toMatrix ⇑b)
      (w := ⇑b) hw
  -- The top wedge of an orthonormal basis has norm one.
  have hnrm0 : ‖exteriorPower.ιMulti ℝ k ⇑b₀‖ = 1 := norm_iMulti_orthonormal' (⇑b₀) horth
  have hnrm : ‖exteriorPower.ιMulti ℝ k ⇑b‖ = |(b₀.toMatrix ⇑b).det| := by
    calc
      ‖exteriorPower.ιMulti ℝ k ⇑b‖
          = ‖(b₀.toMatrix ⇑b).det • exteriorPower.ιMulti ℝ k ⇑b₀‖ := by rw [hwedge]
      _ = |(b₀.toMatrix ⇑b).det| := by
            rw [norm_smul, Real.norm_eq_abs, hnrm0, mul_one]
  calc
    ZLattice.covolume (Submodule.span ℤ (Set.range ⇑b))
        = (volume : Measure E).real (ZSpan.fundamentalDomain b) := hcov
    _ = |b₀.det ⇑b| * (volume : Measure E).real (ZSpan.fundamentalDomain b₀) := hvol
    _ = |b₀.det ⇑b| := by rw [hvol0, mul_one]
    _ = |(b₀.toMatrix ⇑b).det| := by rw [Module.Basis.det_apply]
    _ = ‖exteriorPower.ιMulti ℝ k ⇑b‖ := by rw [hnrm]

end Commons.Analysis.InnerProductSpace