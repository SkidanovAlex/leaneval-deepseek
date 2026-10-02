import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric

theorem sigmaCongr_homeo_spec {ι κ : Type*} {X : ι → Type*} {Y : κ → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ j, TopologicalSpace (Y j)]
    (e : ι ≃ κ) (h : ∀ i, X i ≃ₜ Y (e i)) :
    ∃ H : (Σ i, X i) ≃ₜ (Σ j, Y j), ∀ u : Σ i, X i, H u = ⟨e u.1, h u.1 u.2⟩ := by
  refine ⟨(IsHomeomorph.sigmaMap (g := fun i => ⇑(h i)) e.bijective
      (fun i => (h i).isHomeomorph)).homeomorph (Sigma.map (⇑e) fun i => ⇑(h i)), ?_⟩
  intro u
  rcases u with ⟨i, x⟩
  rfl

end Work.PTGeometric
