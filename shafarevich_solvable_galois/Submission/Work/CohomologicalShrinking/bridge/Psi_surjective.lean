import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.CohomologicalShrinking.Bridge.Psi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.bridge

open CategoryTheory

/-- **Surjectivity of `H₁` along a surjection of groups.**  For a surjective group homomorphism
`φ : Γ →* X` and an `X`-representation `B`, the map `H₁(Γ, Res(φ)(B)) → H₁(X, B)` induced by `φ`
and the identity coefficient morphism is surjective. -/
theorem map_res_id_surjective {k : Type} [CommRing k] {Γ X : Type} [Group Γ] [Group X]
    (φ : Γ →* X) (hφ : Function.Surjective φ) (B : Rep k X) :
    Function.Surjective (groupHomology.map φ (𝟙 (Rep.res φ B)) 1).hom := by
  classical
  -- a section of `φ`
  obtain ⟨s, hs⟩ : ∃ s : X → Γ, ∀ x : X, φ (s x) = x :=
    ⟨fun x => Classical.choose (hφ x), fun x => Classical.choose_spec (hφ x)⟩
  -- surjectivity on the `1`-cycles
  have hmc : Function.Surjective (groupHomology.mapCycles₁ φ (𝟙 (Rep.res φ B))).hom := by
    intro c
    have hcyc : Finsupp.mapDomain s (c : X →₀ ↥B) ∈ groupHomology.cycles₁ (Rep.res φ B) := by
      rw [groupHomology.mem_cycles₁_iff]
      rw [Finsupp.sum_mapDomain_index (fun b => by simp) (fun b m₁ m₂ => by simp),
        Finsupp.sum_mapDomain_index (fun b => by simp) (fun b m₁ m₂ => by simp)]
      simp only [MonoidHom.comp_apply, map_inv, hs]
      exact (groupHomology.mem_cycles₁_iff (A := B) (c : X →₀ ↥B)).1 c.2
    refine ⟨⟨Finsupp.mapDomain s (c : X →₀ ↥B), hcyc⟩, ?_⟩
    apply Subtype.ext
    rw [groupHomology.coe_mapCycles₁]
    simp only [groupHomology.chainsMap₁, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Function.comp_apply, Finsupp.lmapDomain_apply]
    rw [← Finsupp.mapDomain_comp, show (⇑φ) ∘ s = id from funext hs, Finsupp.mapDomain_id,
      Rep.hom_id]
    simp
  -- surjectivity on `H₁`, using that `H₁π : Z₁ → H₁` is onto and commutes with `map`
  intro y
  have hsurj : Function.Surjective (groupHomology.H1π B).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨c, hc⟩ := hsurj y
  obtain ⟨d, hd⟩ := hmc c
  refine ⟨(groupHomology.H1π (Rep.res φ B)).hom d, ?_⟩
  rw [groupHomology.H1π_comp_map_apply, hd, hc]

/-- **The canonical coinflation `H₁(F(m)/F(m)^{(ν)} ⋊ G, E(m,τ)⊗T) → H₁(G, E(m,τ)⊗T)` is
surjective** (Schmidt–Wingberg, Proposition 7 (i): the homological Hochschild–Serre sequence ends
with `H₁(G, E⊗T) → 0`). -/
theorem Psi_surjective (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (i j : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (m : ℕ) :
    Function.Surjective (Work.Bridge.Psi (p := p) (G := G) (i := i) (j := j) (T := T) m) := by
  rw [Work.Bridge.Psi]
  show Function.Surjective (groupHomology.map (Work.CohomologicalShrinking.flowQuot p G m i j)
    (𝟙 (Work.CohomologicalShrinking.flowRep p G m i j T)) 1).hom
  exact map_res_id_surjective (k := ZMod p)
    (φ := Work.CohomologicalShrinking.flowQuot p G m i j)
    (Work.CohomologicalShrinking.flowQuot_surjective p G m i j)
    (Work.CohomologicalShrinking.flowRepG p G m i j T)

end Work.CohomologicalShrinking.bridge
