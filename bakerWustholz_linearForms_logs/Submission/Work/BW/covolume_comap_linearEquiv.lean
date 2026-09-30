import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For a continuous linear equivalence `T` between finite-dimensional real inner product spaces,
`√(det (T.adjoint ∘ T))` is the norm-determinant of `T` (the volume scaling factor of `T`). -/
theorem sqrt_det_adjoint_comp_eq_normDet {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E ≃L[ℝ] F) :
    Real.sqrt (LinearMap.det
        (((T : E →L[ℝ] F).adjoint.comp (T : E →L[ℝ] F) : E →L[ℝ] E) : E →ₗ[ℝ] E))
      = ((T : E →L[ℝ] F) : E →ₗ[ℝ] F).normDet := by
  have hsq : ((T : E →L[ℝ] F) : E →ₗ[ℝ] F).normDet ^ 2
      = LinearMap.det
          (((T : E →L[ℝ] F).adjoint.comp (T : E →L[ℝ] F) : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    have h := LinearMap.normDet_sq (f := ((T : E →L[ℝ] F) : E →ₗ[ℝ] F))
    simp only [ContinuousLinearMap.adjoint_toLinearMap] at h
    simpa using h
  rw [← Real.sqrt_sq (LinearMap.normDet_nonneg _), hsq]

/-- **Change of variables for the covolume of a ℤ-lattice.**  Pulling back a ℤ-lattice `N` along a
continuous linear equivalence `T` multiplies its covolume by the norm-determinant (the volume
scaling factor) of `T`. -/
theorem covolume_comap_mul_normDet {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      [MeasurableSpace F] [BorelSpace F]
    (T : E ≃L[ℝ] F) (N : Submodule ℤ F) [DiscreteTopology ↥N] [IsZLattice ℝ N] :
    ZLattice.covolume (ZLattice.comap ℝ N T.toLinearMap) MeasureTheory.volume *
      ((T : E →L[ℝ] F) : E →ₗ[ℝ] F).normDet = ZLattice.covolume N MeasureTheory.volume := by
  classical
  -- A ℤ-basis of `N`, transported to a ℤ-basis of `T ⁻¹' N`, and the associated ℝ-bases.
  let b := Module.Free.chooseBasis ℤ ↥N
  let bE : Module.Basis (Module.Free.ChooseBasisIndex ℤ ↥N) ℝ F := b.ofZLatticeBasis ℝ N
  let b' : Module.Basis (Module.Free.ChooseBasisIndex ℤ ↥N) ℤ ↥(ZLattice.comap ℝ N T.toLinearMap) :=
    b.ofZLatticeComap ℝ N T.toLinearEquiv
  let bE' : Module.Basis (Module.Free.ChooseBasisIndex ℤ ↥N) ℝ E :=
    b'.ofZLatticeBasis ℝ (ZLattice.comap ℝ N T.toLinearMap)
  -- The ℝ-basis of `E` is the image of the ℝ-basis of `F` under `T.symm`.
  have hbE' : bE' = bE.map (T.symm : F ≃ₗ[ℝ] E) := Module.Basis.ofZLatticeBasis_comap ℝ N T b
  -- hence `T` maps it back to the ℝ-basis of `F`.
  have hbmap : bE'.map (T : E ≃ₗ[ℝ] F) = bE := by
    rw [hbE']
    ext i
    simp [Module.Basis.map_apply]
  -- consequently `T` maps the fundamental domain of `T ⁻¹' N` onto that of `N`.
  have himg1 := ZSpan.map_fundamentalDomain bE' (T : E ≃ₗ[ℝ] F)
  have himg : ⇑((T : E →L[ℝ] F) : E →ₗ[ℝ] F) '' ZSpan.fundamentalDomain bE' =
      ZSpan.fundamentalDomain bE := by
    rw [show ⇑((T : E →L[ℝ] F) : E →ₗ[ℝ] F) = ⇑(T : E ≃ₗ[ℝ] F) from rfl, himg1, hbmap]
  -- the volume of the image is the volume scaled by the norm-determinant.
  have hvol := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
      (((T : E →L[ℝ] F)) : E →ₗ[ℝ] F) (ZSpan.fundamentalDomain bE')
  rw [himg] at hvol
  have hvol' : (MeasureTheory.Measure.euclideanHausdorffMeasure (Module.finrank ℝ E) :
      MeasureTheory.Measure F) =
      MeasureTheory.volume := by
    rw [LinearEquiv.finrank_eq (T : E ≃ₗ[ℝ] F)]
    exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  rw [hvol'] at hvol
  have hvolfin : MeasureTheory.volume (ZSpan.fundamentalDomain bE') ≠ ⊤ :=
    ne_of_lt (ZSpan.fundamentalDomain_isBounded bE').measure_lt_top
  -- pass to real-valued measures
  have hreal : MeasureTheory.volume.real (ZSpan.fundamentalDomain bE) =
      ((T : E →L[ℝ] F) : E →ₗ[ℝ] F).normDet *
        MeasureTheory.volume.real (ZSpan.fundamentalDomain bE') := by
    have h := congrArg ENNReal.toReal hvol
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _)] at h
    simpa only [MeasureTheory.Measure.real] using h
  -- both covolumes are the volumes of the corresponding fundamental domains
  have hN : ZLattice.covolume N MeasureTheory.volume =
      MeasureTheory.volume.real (ZSpan.fundamentalDomain bE) :=
    ZLattice.covolume_eq_measure_fundamentalDomain N MeasureTheory.volume
      (ZLattice.isAddFundamentalDomain b MeasureTheory.volume)
  have hcomap : ZLattice.covolume (ZLattice.comap ℝ N T.toLinearMap) MeasureTheory.volume =
      MeasureTheory.volume.real (ZSpan.fundamentalDomain bE') :=
    ZLattice.covolume_eq_measure_fundamentalDomain _ MeasureTheory.volume
      (ZLattice.isAddFundamentalDomain b' MeasureTheory.volume)
  rw [hcomap, hN, hreal, mul_comm]

theorem covolume_comap_linearEquiv {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      [MeasurableSpace F] [BorelSpace F]
    (T : E ≃L[ℝ] F) (N : Submodule ℤ F) [DiscreteTopology ↥N] [IsZLattice ℝ N] :
    ZLattice.covolume (ZLattice.comap ℝ N T.toLinearMap) MeasureTheory.volume *
      Real.sqrt (LinearMap.det (((T : E →L[ℝ] F).adjoint.comp (T : E →L[ℝ] F) : E →L[ℝ] E) : E →ₗ[ℝ] E))
      = ZLattice.covolume N MeasureTheory.volume := by
  rw [sqrt_det_adjoint_comp_eq_normDet]
  exact covolume_comap_mul_normDet T N

end Work.BW
