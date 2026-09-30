import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Covolume of a `ℤ`-lattice against an orthonormal basis

Let `E` be a finite-dimensional real inner product space and `L ⊆ E` a full `ℤ`-lattice.
For a `ℤ`-basis `b` of `L` and an orthonormal `ℝ`-basis `bE` of `E`, the covolume of `L` is the
absolute value of the determinant of the matrix of the coordinates of the vectors `b i` in the
basis `bE`.  This is the general-norm counterpart of `ZLattice.covolume_eq_det` (the case
`E = ι → ℝ`, where the standard basis is orthonormal).

The proof is the general "determinant multiplied by reference fundamental domain" formula
`ZLattice.covolume_eq_det_mul_measureReal`, together with the fact that the fundamental domain of
an orthonormal basis has volume `1`: the fundamental domain agrees almost everywhere with the
parallelepiped spanned by the orthonormal basis, whose volume is `1`
(`OrthonormalBasis.volume_parallelepiped`).
-/

namespace Work.BW

open MeasureTheory

/-- The fundamental domain of an orthonormal basis has volume `1`. -/
theorem volume_real_fundamentalDomain_orthonormalBasis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bE : OrthonormalBasis ι ℝ E) :
    MeasureTheory.volume.real (ZSpan.fundamentalDomain bE.toBasis) = 1 := by
  -- The fundamental domain agrees almost everywhere with the parallelepiped spanned by `bE`.
  have hae := ZSpan.fundamentalDomain_ae_parallelepiped (b := bE.toBasis)
    (μ := MeasureTheory.volume)
  have h₁ : MeasureTheory.volume (ZSpan.fundamentalDomain bE.toBasis) =
      MeasureTheory.volume (parallelepiped ⇑bE.toBasis) := hae.measure_eq
  -- ... whose volume is `1` because `bE` is orthonormal.
  have h₂ : MeasureTheory.volume (parallelepiped ⇑bE.toBasis) = 1 :=
    OrthonormalBasis.volume_parallelepiped bE
  rw [MeasureTheory.Measure.real, h₁, h₂, ENNReal.toReal_one]

theorem covolume_eq_abs_det_orthonormalBasis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ L) (bE : OrthonormalBasis ι ℝ E) :
    ZLattice.covolume L MeasureTheory.volume = |bE.toBasis.det (fun i => ((b i : L) : E))| := by
  -- Compare the lattice to its own basis, measured in the orthonormal basis `bE.toBasis`.
  have h := ZLattice.covolume_eq_det_mul_measureReal (L := L) (μ := MeasureTheory.volume)
    b bE.toBasis
  have hdet : (Subtype.val ∘ ⇑b) = (fun i => ((b i : L) : E)) := rfl
  rw [h, volume_real_fundamentalDomain_orthonormalBasis bE, mul_one, hdet]

end Work.BW
