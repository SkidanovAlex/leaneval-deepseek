import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

/-- Naturality of the explicit left homology data of a short complex of modules, evaluated on
the quotient of a cycle: the induced map on left homology sends the class of a cycle `w`
to the class of `ψ.τ₂ w`. -/
theorem moduleCatLeftHomologyMap_mkQ {R : Type} [CommRing R]
    {S₁ S₂ : ShortComplex (ModuleCat R)} (ψ : S₁ ⟶ S₂)
    (w : ↥(LinearMap.ker S₁.g.hom)) :
    (ShortComplex.leftHomologyMap' ψ S₁.moduleCatLeftHomologyData
        S₂.moduleCatLeftHomologyData).hom
        ((LinearMap.range S₁.moduleCatToCycles).mkQ w)
      = (LinearMap.range S₂.moduleCatToCycles).mkQ
          ⟨ψ.τ₂.hom w, by
            rw [LinearMap.mem_ker]
            have h : S₂.g.hom (ψ.τ₂.hom (w : S₁.X₂))
                = ψ.τ₃.hom (S₁.g.hom (w : S₁.X₂)) := by
              have h' := congrArg ModuleCat.Hom.hom ψ.comm₂₃
              rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h'
              exact LinearMap.congr_fun h' (w : S₁.X₂)
            have hw : S₁.g.hom (w : S₁.X₂) = 0 := LinearMap.mem_ker.mp w.2
            rw [h, hw, map_zero]⟩ := by
  -- The image of `w` under `ψ.τ₂` is again a cycle.
  have key : ∀ w : ↥(LinearMap.ker S₁.g.hom),
      ψ.τ₂.hom (w : S₁.X₂) ∈ LinearMap.ker S₂.g.hom := by
    intro w
    rw [LinearMap.mem_ker]
    have h : S₂.g.hom (ψ.τ₂.hom (w : S₁.X₂)) = ψ.τ₃.hom (S₁.g.hom (w : S₁.X₂)) := by
      have h' := congrArg ModuleCat.Hom.hom ψ.comm₂₃
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h'
      exact LinearMap.congr_fun h' (w : S₁.X₂)
    have hw : S₁.g.hom (w : S₁.X₂) = 0 := LinearMap.mem_ker.mp w.2
    rw [h, hw, map_zero]
  -- Commutation with the projection onto homology: `π ≫ leftHomologyMap' = cyclesMap' ≫ π`.
  have hπ := congrArg ModuleCat.Hom.hom (ShortComplex.leftHomologyπ_naturality' ψ
      S₁.moduleCatLeftHomologyData S₂.moduleCatLeftHomologyData)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp,
      ShortComplex.moduleCatLeftHomologyData_π_hom,
      ShortComplex.moduleCatLeftHomologyData_π_hom] at hπ
  have hπ' := LinearMap.congr_fun hπ w
  simp only [LinearMap.comp_apply] at hπ'
  -- Commutation with the inclusion of cycles: `cyclesMap' ≫ i = i ≫ ψ.τ₂`, which pins down
  -- `cyclesMap'` on elements because `i` is injective.
  have hc := congrArg ModuleCat.Hom.hom (ShortComplex.cyclesMap'_i ψ
      S₁.moduleCatLeftHomologyData S₂.moduleCatLeftHomologyData)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp,
      ShortComplex.moduleCatLeftHomologyData_i_hom,
      ShortComplex.moduleCatLeftHomologyData_i_hom] at hc
  have hc' := LinearMap.congr_fun hc w
  simp only [LinearMap.comp_apply] at hc'
  have hcw : (ShortComplex.cyclesMap' ψ S₁.moduleCatLeftHomologyData
      S₂.moduleCatLeftHomologyData).hom w = ⟨ψ.τ₂.hom (w : S₁.X₂), key w⟩ := Subtype.ext hc'
  refine hπ'.trans ?_
  rw [hcw]
  exact congrArg _ (Subtype.ext rfl)

end Work.Serre
