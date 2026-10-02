import Submission.Work.Tubular.DiscManifold.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Transferring a smooth structure along a homeomorphism of the total space or of the model

`Work.Tubular.chartedSpaceOfHomeomorph` pushes a charted space structure forward along a
homeomorphism `M ≃ₜ M'` of the total spaces, and `Work.Tubular.chartedSpaceOfModelHomeo` changes the
model space along a homeomorphism `H ≃ₜ H'`.

This file proves that both constructions preserve `HasGroupoid`:

* for the first, no smoothness whatsoever is needed — the transitions of the pushed-forward atlas are
  the transitions of the old one, since `e.symm ≫ e ≈ id`;
* for the second, the conjugation `f ↦ Φ ≫ f ≫ Φ.symm` must map the old groupoid into the new one,
  which is the hypothesis `h` below (for `contDiffGroupoid`s it says the change of model is `C^n` in
  both directions).
-/

open scoped Manifold ContDiff Topology
open OpenPartialHomeomorph

namespace Work.Tubular

noncomputable section

variable {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
variable {M M' : Type*} [TopologicalSpace M] [TopologicalSpace M']

/-- **A `ChartedSpace` structure pushed forward along a homeomorphism has the same structure
groupoid.**  No smoothness is required of the homeomorphism: it only rearranges the charts. -/
theorem hasGroupoid_chartedSpaceOfHomeomorph (c : ChartedSpace H M) (e : M ≃ₜ M')
    (G : StructureGroupoid H) [HasGroupoid M G] :
    letI := chartedSpaceOfHomeomorph c e
    HasGroupoid M' G := by
  letI := chartedSpaceOfHomeomorph c e
  refine ⟨fun {e₁ e₂} he₁ he₂ => ?_⟩
  change e₁ ∈ c.atlas.image (fun f => e.symm.toOpenPartialHomeomorph ≫ₕ f) at he₁
  change e₂ ∈ c.atlas.image (fun f => e.symm.toOpenPartialHomeomorph ≫ₕ f) at he₂
  rw [Set.mem_image] at he₁ he₂
  obtain ⟨f₁, hf₁, rfl⟩ := he₁
  obtain ⟨f₂, hf₂, rfl⟩ := he₂
  have hEE : e.symm.toOpenPartialHomeomorph.symm ≫ₕ e.symm.toOpenPartialHomeomorph ≈
      OpenPartialHomeomorph.refl M := by
    simpa using OpenPartialHomeomorph.symm_trans_self e.symm.toOpenPartialHomeomorph
  have hinner : e.symm.toOpenPartialHomeomorph.symm ≫ₕ
      (e.symm.toOpenPartialHomeomorph ≫ₕ f₂) ≈ f₂ := by
    rw [(OpenPartialHomeomorph.trans_assoc e.symm.toOpenPartialHomeomorph.symm
      e.symm.toOpenPartialHomeomorph f₂).symm]
    refine Setoid.trans (EqOnSource.trans' hEE (eqOnSource_refl _)) ?_
    rw [OpenPartialHomeomorph.refl_trans]
  have hstep : f₁.symm ≫ₕ (e.symm.toOpenPartialHomeomorph.symm ≫ₕ
      (e.symm.toOpenPartialHomeomorph ≫ₕ f₂)) ≈ f₁.symm ≫ₕ f₂ :=
    EqOnSource.trans' (eqOnSource_refl _) hinner
  refine G.mem_of_eqOnSource (G.compatible hf₁ hf₂) ?_
  calc (e.symm.toOpenPartialHomeomorph ≫ₕ f₁).symm ≫ₕ
        (e.symm.toOpenPartialHomeomorph ≫ₕ f₂)
      ≈ (f₁.symm ≫ₕ e.symm.toOpenPartialHomeomorph.symm) ≫ₕ
          (e.symm.toOpenPartialHomeomorph ≫ₕ f₂) := by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    _ ≈ f₁.symm ≫ₕ (e.symm.toOpenPartialHomeomorph.symm ≫ₕ
          (e.symm.toOpenPartialHomeomorph ≫ₕ f₂)) := by
        rw [OpenPartialHomeomorph.trans_assoc]
    _ ≈ f₁.symm ≫ₕ f₂ := hstep

/-- **A change of model space preserves the structure groupoid**, provided conjugation by the model
homeomorphism `Φ` maps the old groupoid into the new one. -/
theorem hasGroupoid_chartedSpaceOfModelHomeo (c : ChartedSpace H' M) (Φ : H ≃ₜ H')
    (G : StructureGroupoid H) (G' : StructureGroupoid H') [HasGroupoid M G']
    (h : ∀ f : OpenPartialHomeomorph H' H', f ∈ G' →
      Φ.toOpenPartialHomeomorph ≫ₕ f ≫ₕ Φ.symm.toOpenPartialHomeomorph ∈ G) :
    letI := chartedSpaceOfModelHomeo c Φ
    HasGroupoid M G := by
  letI := chartedSpaceOfModelHomeo c Φ
  refine ⟨fun {e₁ e₂} he₁ he₂ => ?_⟩
  change e₁ ∈ c.atlas.image (fun f => f ≫ₕ Φ.symm.toOpenPartialHomeomorph) at he₁
  change e₂ ∈ c.atlas.image (fun f => f ≫ₕ Φ.symm.toOpenPartialHomeomorph) at he₂
  rw [Set.mem_image] at he₁ he₂
  obtain ⟨f₁, hf₁, rfl⟩ := he₁
  obtain ⟨f₂, hf₂, rfl⟩ := he₂
  refine G.mem_of_eqOnSource (h (f₁.symm ≫ₕ f₂) (G'.compatible hf₁ hf₂)) ?_
  calc (f₁ ≫ₕ Φ.symm.toOpenPartialHomeomorph).symm ≫ₕ
        (f₂ ≫ₕ Φ.symm.toOpenPartialHomeomorph)
      ≈ (Φ.toOpenPartialHomeomorph ≫ₕ f₁.symm) ≫ₕ
          (f₂ ≫ₕ Φ.symm.toOpenPartialHomeomorph) := by
        rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
        simp
    _ ≈ Φ.toOpenPartialHomeomorph ≫ₕ (f₁.symm ≫ₕ f₂) ≫ₕ
          Φ.symm.toOpenPartialHomeomorph := by
        rw [OpenPartialHomeomorph.trans_assoc]
        rw [← OpenPartialHomeomorph.trans_assoc f₁.symm f₂ Φ.symm.toOpenPartialHomeomorph]

end

end Work.Tubular
