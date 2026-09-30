import Mathlib
import Submission.Work.BW.covolume_span_eq_sqrt_gram_det

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Module MeasureTheory

/-- **Covolume of the ℤ-span of a real basis = `√|det Gram|`**, for a basis indexed by an
arbitrary finite type `ι` (the `Fin k` case is `Work.BW.covolume_span_basis_eq_sqrt_gram_det`). -/
theorem covolume_sqrt_gram_det_arb {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range ⇑b)) (MeasureTheory.volume) =
      Real.sqrt |(Matrix.gram ℝ ⇑b).det| := by
  classical
  -- an orthonormal basis indexed by the same type `ι`
  let e : Fin (Module.finrank ℝ E) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, Module.finrank_eq_card_basis b])
  let c : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex e
  have hdisc : DiscreteTopology ↥(Submodule.span ℤ (Set.range (⇑b : ι → E))) := inferInstance
  have hzlat : IsZLattice ℝ (Submodule.span ℤ (Set.range (⇑b : ι → E))) := inferInstance
  -- covolume = volume of the fundamental domain of `b`
  have h1 : ZLattice.covolume (Submodule.span ℤ (Set.range ⇑b)) (MeasureTheory.volume : Measure E)
      = (MeasureTheory.volume : Measure E).real (ZSpan.fundamentalDomain b) :=
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain b _)
  -- change of basis to the orthonormal basis `c`
  have h2 : (MeasureTheory.volume : Measure E).real (ZSpan.fundamentalDomain b)
      = |c.toBasis.det ⇑b| *
        (MeasureTheory.volume : Measure E).real (ZSpan.fundamentalDomain c.toBasis) :=
    ZSpan.measureReal_fundamentalDomain b _ c.toBasis
  -- the fundamental domain of an orthonormal basis has measure one
  have h3 : (MeasureTheory.volume : Measure E).real (ZSpan.fundamentalDomain c.toBasis) = 1 :=
    volume_real_fundamentalDomain_orthonormalBasis c
  -- the change-of-basis determinant is the square root of the Gram determinant
  have h4 : |c.toBasis.det ⇑b| = Real.sqrt |(Matrix.gram ℝ ⇑b).det| := by
    have hm : (Matrix.of fun i j => (c.repr (⇑b j)).ofLp i) = c.toBasis.toMatrix ⇑b := by
      ext i j
      simp [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    rw [Module.Basis.det_apply, Matrix.gram_eq_conjTranspose_mul c ⇑b, hm,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.det_mul, Matrix.det_transpose,
      abs_mul, ← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
  rw [h1, h2, h3, mul_one, h4]

end Work.BW
