import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.covolume_kernel_mul_image
import Submission.Work.BW.covolume_eq_abs_det_orthonormalBasis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Module MeasureTheory

/-- **Covolume of the ℤ-span of a real basis = `√|det Gram|`** (abstract form).

Let `E` be a finite-dimensional real inner product space and `b : Fin k → E` a real basis (so
`k = dim E`).  Then the covolume of the ℤ-lattice `∑ ℤ·bᵢ` with respect to the Lebesgue (ℓ²)
measure of `E` is the square root of the absolute value of the Gram determinant of `b`.

The proof uses an orthonormal basis `c` of `E`, rewrites `covolume` as the measure of the
fundamental domain `ZSpan.fundamentalDomain b`, changes the basis of that fundamental domain to
`c` (picking up `|det|` of the change-of-basis matrix), uses that the fundamental domain of an
orthonormal basis has measure `1`, and finally identifies `|det|` of the change-of-basis matrix
with `√|det Gram|` through `Matrix.gram_eq_conjTranspose_mul`. -/
theorem covolume_span_basis_eq_sqrt_gram_det {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {k : ℕ} (b : Basis (Fin k) ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range ⇑b)) (MeasureTheory.volume : Measure E)
      = Real.sqrt |(Matrix.gram ℝ ⇑b).det| := by
  classical
  -- an orthonormal basis indexed by `Fin k`
  have hfr : Module.finrank ℝ E = k := by
    rw [finrank_eq_card_basis b, Fintype.card_fin]
  let e : Fin (Module.finrank ℝ E) ≃ Fin k := Fintype.equivOfCardEq (by simp [hfr])
  let c : OrthonormalBasis (Fin k) ℝ E := (stdOrthonormalBasis ℝ E).reindex e
  have hdisc : DiscreteTopology ↥(Submodule.span ℤ (Set.range (⇑b : Fin k → E))) :=
    inferInstance
  have hzlat : IsZLattice ℝ (Submodule.span ℤ (Set.range (⇑b : Fin k → E))) := inferInstance
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
  -- (already in the tree: `Work.BW.volume_real_fundamentalDomain_orthonormalBasis`)
  have h3 : (MeasureTheory.volume : Measure E).real (ZSpan.fundamentalDomain c.toBasis) = 1 :=
    Work.BW.volume_real_fundamentalDomain_orthonormalBasis c
  -- the change-of-basis determinant is the square root of the Gram determinant
  have h4 : |c.toBasis.det ⇑b| = Real.sqrt |(Matrix.gram ℝ ⇑b).det| := by
    have hm : (Matrix.of fun i j => (c.repr (⇑b j)).ofLp i) = c.toBasis.toMatrix ⇑b := by
      ext i j
      simp [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    rw [Basis.det_apply, Matrix.gram_eq_conjTranspose_mul c ⇑b, hm,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.det_mul, Matrix.det_transpose,
      abs_mul, ← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
  rw [h1, h2, h3, mul_one, h4]

/-- **Gram determinant = ℓ² covolume (the coordinate↔abstract bridge).**

Let `V` be a real subspace of a Euclidean space, `v : Fin k → V` a `ℝ`-basis of `V` (so
`k = dim V`), and `e : EuclideanSpace ℝ (Fin k) ≃ᵢ V` an isometry of the Euclidean model onto `V`
(whose norm is the one inherited from the ambient Euclidean space, so such an `e` exists as soon as
`V` is finite-dimensional).  Then

  `covol(ℤ-span(v)) = √|det (i j ↦ ⟪v i, v j⟫)|`,

the covolume on the left being taken with respect to the measure transported by the isometry `e`
from the Lebesgue measure of `EuclideanSpace ℝ (Fin k)` — i.e. the ℓ² (Lebesgue) measure of `V`
itself, *not* any sup-norm normalisation.

This is the bridge that makes the *duality identity* `Work.BW.covolume_kernel_mul_image` (proved,
stated for abstract inner product spaces) applicable to a coordinate model such as
`Work.BW.CoordSpace F N = ℝ^{dN}` of `Work.BW.kcb_defs`, where the covolume of a lattice spanned by
`v` is the explicit Gram determinant `Work.BW.covolumeOf v = √|gramDet v|`.  Concretely: a proof of
the Bombieri–Vaaler kernel-lattice covolume bound carried out with `covolumeOf`/`gramDet` can be
transported into the abstract inner product setting with this result and then closed with the
duality identity.  Proof: compute `covol` as the measure of a fundamental domain (Mathlib
`ZLattice.covolume_eq_measure_fundamentalDomain`, `ZSpan.volume_fundamentalDomain`) and identify
the determinant of the change-of-basis matrix against an orthonormal basis with `√det Gram`.
Note `Work.BW.covolume_isometry_map_volume` (in the tree) shows `map e volume = volume` for an
isometry between finite-dimensional real inner product spaces, and the prover must supply the
`DiscreteTopology`/`IsZLattice ℝ` instances that `hv`/`hspan` give. -/
theorem covolume_span_eq_sqrt_gram_det {n k : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (v : Fin k → ↥V) (hv : LinearIndependent ℝ v) (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (e : EuclideanSpace ℝ (Fin k) ≃ᵢ ↥V) :
    ZLattice.covolume (Submodule.span ℤ (Set.range v))
        (MeasureTheory.Measure.map e MeasureTheory.volume)
      = Real.sqrt |(Matrix.of (fun i j => inner ℝ (v i) (v j))).det| := by
  -- the given `ℤ`-lattice is the `ℤ`-span of an actual `ℝ`-basis of `↥V`
  have hcoe : ⇑(Basis.mk hv (top_le_iff.mpr hspan)) = v := Basis.coe_mk hv _
  rw [← hcoe, covolume_isometry_map_volume e]
  exact covolume_span_basis_eq_sqrt_gram_det (Basis.mk hv (top_le_iff.mpr hspan))

end Work.BW
