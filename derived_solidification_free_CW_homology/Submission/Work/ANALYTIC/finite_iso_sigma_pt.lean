import Mathlib

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite

/-- A finite light profinite set is the coproduct of its points: this is the coproduct decomposition
`T = ∐_{t : T} ⋆` in `LightProfinite` used to split `ℤ[T]` into copies of the monoidal unit. -/
theorem finite_iso_sigma_pt (T : LightProfinite.{0}) [Finite T] :
    Nonempty (T ≅ CategoryTheory.Limits.sigmaObj (fun _ : ↥T => LightProfinite.of PUnit.{1})) := by
  -- The coproduct of the points of `T` is computed by the explicit finite coproduct of
  -- `CompHausLike`, which is the disjoint union `Σ t, ⋆`.
  let X : ↥T → LightProfinite.{0} := fun _ => LightProfinite.of PUnit.{1}
  -- `T` is finite Hausdorff, hence discrete, so `t ↦ ⟨t, ⋆⟩` is continuous.
  let f : T ⟶ CompHausLike.finiteCoproduct X :=
    CompHausLike.ofHom _ ⟨fun t => ⟨t, PUnit.unit⟩, continuous_of_discreteTopology⟩
  -- and it is the canonical bijection `T ≃ Σ t, ⋆`.
  have hf : Function.Bijective f := by
    rw [show ⇑f = ⇑(Equiv.sigmaUnique ↥T (fun _ : ↥T => PUnit.{1})).symm from rfl]
    exact (Equiv.sigmaUnique ↥T (fun _ : ↥T => PUnit.{1})).symm.bijective
  exact ⟨(CompHausLike.isoOfBijective f hf).trans
    ((CompHausLike.finiteCoproduct.isColimit X).coconePointUniqueUpToIso (colimit.isColimit _))⟩

end Work.ANALYTIC
