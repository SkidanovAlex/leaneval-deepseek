import Mathlib

namespace Work.Topology.Covering

lemma sheet_mem_iff_of_saturated {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace I] {f : X → Y} {U' : Set Y} (hU'conn : IsPreconnected U')
    (H : ↥(f ⁻¹' U') ≃ₜ ↥U' × I) {X₀ : Set X}
    (hsat : ∀ C : Set X, IsPreconnected C → C ⊆ f ⁻¹' U' → (C ∩ X₀).Nonempty → C ⊆ X₀) :
    ∀ q : ↥U' × I, ((H.symm q : ↥(f ⁻¹' U')) : X) ∈ X₀ ↔
      ∃ u : ↥U', ((H.symm (u, q.2) : ↥(f ⁻¹' U')) : X) ∈ X₀ := by
  intro q
  constructor
  · -- If the point over `q` lies in `X₀`, take `u = q.1`.
    intro hq
    exact ⟨q.1, hq⟩
  · -- The "sheet" `S = {H.symm (u, q.2) : u ∈ ↥U'}` is the image of the preconnected space
    -- `↥U'` under the continuous map `u ↦ H.symm (u, q.2)`; it lies in `f ⁻¹' U'` and, if any
    -- of its points is in `X₀`, saturation forces `S ⊆ X₀`, giving the point over `q`.
    rintro ⟨u, hu⟩
    have hcont : Continuous fun u : ↥U' => ((H.symm (u, q.2) : ↥(f ⁻¹' U')) : X) :=
      continuous_subtype_val.comp (H.symm.continuous.comp
        (continuous_id.prodMk continuous_const))
    have hconn : IsPreconnected (Set.range fun u : ↥U' => ((H.symm (u, q.2) : ↥(f ⁻¹' U')) : X)) :=
      @isPreconnected_range ↥U' X _ _ (Subtype.preconnectedSpace hU'conn)
        (fun u : ↥U' => ((H.symm (u, q.2) : ↥(f ⁻¹' U')) : X)) hcont
    have hsub : (Set.range fun u : ↥U' => ((H.symm (u, q.2) : ↥(f ⁻¹' U')) : X)) ⊆ f ⁻¹' U' := by
      rintro x ⟨u', rfl⟩
      exact (H.symm (u', q.2)).2
    have hne : ((Set.range fun u : ↥U' => ((H.symm (u, q.2) : ↥(f ⁻¹' U')) : X)) ∩ X₀).Nonempty :=
      ⟨_, ⟨⟨u, rfl⟩, hu⟩⟩
    exact hsat _ hconn hsub hne ⟨q.1, rfl⟩

end Work.Topology.Covering
