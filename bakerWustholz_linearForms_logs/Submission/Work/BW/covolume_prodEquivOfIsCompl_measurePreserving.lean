import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The linear isomorphism `K × Kᗮ ≃ E`, `(x, y) ↦ x + y`, is measure preserving for the
Lebesgue (Haar) volumes. This is because it is the composition of the linear isometry
equivalence `K.orthogonalDecomposition.symm` with the `L²`-product identification, both of
which are volume preserving. -/
theorem covolume_prodEquivOfIsCompl_measurePreserving {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
    (K : Submodule ℝ E) [K.HasOrthogonalProjection] (h : IsCompl K Kᗮ) :
    MeasureTheory.MeasurePreserving (K.prodEquivOfIsCompl Kᗮ h : ↥K × ↥Kᗮ → E)
      MeasureTheory.volume MeasureTheory.volume := by
  -- `prodEquivOfIsCompl` is the map `(x, y) ↦ x + y`.
  have hfval : (K.prodEquivOfIsCompl Kᗮ h : ↥K × ↥Kᗮ → E)
      = fun x => (x.1 : E) + x.2 := rfl
  rw [hfval]
  -- It factors as `K.orthogonalDecomposition.symm ∘ WithLp.ofLp`.
  have hfeq : (⇑K.orthogonalDecomposition.symm : WithLp 2 (↥K × ↥Kᗮ) → E)
      = (fun x : ↥K × ↥Kᗮ => (x.1 : E) + x.2) ∘ WithLp.ofLp := by
    funext a
    simp [Submodule.orthogonalDecomposition_symm_apply]
  -- `K.orthogonalDecomposition.symm` is a linear isometry equivalence, hence measure preserving.
  have hm : MeasureTheory.MeasurePreserving
      (⇑K.orthogonalDecomposition.symm : WithLp 2 (↥K × ↥Kᗮ) → E)
      MeasureTheory.volume MeasureTheory.volume :=
    LinearIsometryEquiv.measurePreserving K.orthogonalDecomposition.symm
  -- The `L²`-product identification is measure preserving.
  have ho : MeasureTheory.MeasurePreserving
      (WithLp.ofLp : WithLp 2 (↥K × ↥Kᗮ) → ↥K × ↥Kᗮ)
      MeasureTheory.volume MeasureTheory.volume :=
    WithLp.volume_preserving_ofLp ↥K ↥Kᗮ
  have hmapo : MeasureTheory.Measure.map
      (WithLp.ofLp : WithLp 2 (↥K × ↥Kᗮ) → ↥K × ↥Kᗮ)
      (MeasureTheory.volume : MeasureTheory.Measure (WithLp 2 (↥K × ↥Kᗮ)))
      = (MeasureTheory.volume : MeasureTheory.Measure (↥K × ↥Kᗮ)) := ho.map_eq
  refine ⟨?_, ?_⟩
  · fun_prop
  · have h1 : MeasureTheory.Measure.map (fun x : ↥K × ↥Kᗮ => (x.1 : E) + x.2)
          (MeasureTheory.volume : MeasureTheory.Measure (↥K × ↥Kᗮ))
        = MeasureTheory.Measure.map
            ((fun x : ↥K × ↥Kᗮ => (x.1 : E) + x.2) ∘ WithLp.ofLp)
            (MeasureTheory.volume : MeasureTheory.Measure (WithLp 2 (↥K × ↥Kᗮ))) := by
      rw [← hmapo]
      exact MeasureTheory.Measure.map_map
        (f := (WithLp.ofLp : WithLp 2 (↥K × ↥Kᗮ) → ↥K × ↥Kᗮ))
        (g := fun x : ↥K × ↥Kᗮ => (x.1 : E) + x.2) (by fun_prop) ho.measurable
    have h2 : MeasureTheory.Measure.map
            ((fun x : ↥K × ↥Kᗮ => (x.1 : E) + x.2) ∘ WithLp.ofLp)
            (MeasureTheory.volume : MeasureTheory.Measure (WithLp 2 (↥K × ↥Kᗮ)))
        = (MeasureTheory.volume : MeasureTheory.Measure E) := by
      rw [← hfeq]
      exact hm.map_eq
    exact h1.trans h2

end Work.BW
