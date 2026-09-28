import Mathlib

namespace Work.HP.Q44Child

open MeasureTheory Module

/-- For a `ℤ`-lattice `L` in a finite-dimensional real inner product space `E` and any `ℤ`-basis
`b` of `L`, the covolume of `L` (the volume of a fundamental domain, for the Lebesgue measure
normalised so that orthonormal parallelepipeds have volume `1`) equals the square root of the
determinant of the Gram matrix of the basis.

The proof goes through the fundamental domain of the `ℝ`-basis `b₀ = b.ofZLatticeBasis ℝ L`:
its volume is `|e.det b₀|` for any orthonormal basis `e` of `E`, and `det (gram ℝ b₀) = (e.det b₀)²`
by the classical Gram–Cauchy–Binet identity. -/
theorem covolume_eq_gram_det {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology ↥L] [IsZLattice ℝ L]
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℤ L) :
    ZLattice.covolume L =
      Real.sqrt (Matrix.det (Matrix.gram ℝ (fun i => (((b i : L)) : E)))) := by
  classical
  let b₀ : Basis (Fin (Module.finrank ℝ E)) ℝ E := b.ofZLatticeBasis ℝ L
  have hb₀ : (fun i => (((b i : L)) : E)) = ⇑b₀ := by
    funext i
    rw [Module.Basis.ofZLatticeBasis_apply]
  -- the covolume is the volume of the fundamental domain of the induced `ℝ`-basis
  have hcov : ZLattice.covolume L = volume.real (ZSpan.fundamentalDomain b₀) :=
    ZLattice.covolume_eq_measure_fundamentalDomain L volume
      (ZLattice.isAddFundamentalDomain b volume)
  -- an orthonormal basis has fundamental domain of volume `1`
  have hvol1 : volume (ZSpan.fundamentalDomain (stdOrthonormalBasis ℝ E).toBasis) = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped
      (stdOrthonormalBasis ℝ E).toBasis volume)]
    exact OrthonormalBasis.volume_parallelepiped (stdOrthonormalBasis ℝ E)
  -- compare with the fundamental domain of the orthonormal basis
  have hvol2 : volume (ZSpan.fundamentalDomain b₀)
      = ENNReal.ofReal |(stdOrthonormalBasis ℝ E).toBasis.det b₀| := by
    rw [ZSpan.measure_fundamentalDomain b₀ volume (stdOrthonormalBasis ℝ E).toBasis, hvol1,
      mul_one]
  have hreal : volume.real (ZSpan.fundamentalDomain b₀)
      = |(stdOrthonormalBasis ℝ E).toBasis.det b₀| := by
    rw [MeasureTheory.Measure.real, hvol2, ENNReal.toReal_ofReal (abs_nonneg _)]
  -- the Gram determinant is the square of the determinant in an orthonormal basis
  have hgram : (Matrix.gram ℝ (⇑b₀)).det
      = ((stdOrthonormalBasis ℝ E).toBasis.det b₀)^2 := by
    have hM : Matrix.of (fun i j => ((stdOrthonormalBasis ℝ E).repr (b₀ j)).ofLp i)
        = (stdOrthonormalBasis ℝ E).toBasis.toMatrix (⇑b₀) := by
      ext i j
      simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    have hg := Matrix.gram_eq_conjTranspose_mul (stdOrthonormalBasis ℝ E) (⇑b₀)
    rw [hg, Matrix.det_mul, Matrix.det_conjTranspose, hM, Module.Basis.det_apply]
    simp only [star_trivial]
    ring
  rw [hb₀, hcov, hreal, hgram, Real.sqrt_sq_eq_abs]

end Work.HP.Q44Child
