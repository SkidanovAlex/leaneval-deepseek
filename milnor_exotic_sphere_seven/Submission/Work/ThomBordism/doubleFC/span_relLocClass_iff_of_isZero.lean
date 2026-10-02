import Mathlib
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.pd_plumbing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.ThomBordism.doubleFC

/-- **Transfer of a singleton spanning condition along a bijective map of `ℤ`-modules.**
If `φ : A ⟶ B` is a morphism in `ModuleCat ℤ` whose underlying linear map is bijective, then
`span{φ a} = ⊤ ↔ span{a} = ⊤`. -/
private lemma span_singleton_iff_of_bijective {A B : ModuleCat ℤ} (φ : A ⟶ B) (a : A)
    (hinj : Function.Injective (ModuleCat.Hom.hom φ))
    (hsurj : Function.Surjective (ModuleCat.Hom.hom φ)) :
    Submodule.span ℤ {(ModuleCat.Hom.hom φ) a} = ⊤ ↔ Submodule.span ℤ {a} = ⊤ := by
  have hmap : Submodule.map (ModuleCat.Hom.hom φ) (Submodule.span ℤ {a}) =
      Submodule.span ℤ {(ModuleCat.Hom.hom φ) a} := by
    rw [Submodule.map_span]
    simp
  have hmap_top : Submodule.map (ModuleCat.Hom.hom φ) (⊤ : Submodule ℤ A) = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
  have hinjmap : Function.Injective (Submodule.map (ModuleCat.Hom.hom φ)) :=
    Submodule.map_injective_of_injective hinj
  constructor
  · intro h
    exact hinjmap ((hmap.trans h).trans hmap_top.symm)
  · intro h
    exact hmap.symm.trans ((congrArg (Submodule.map (ModuleCat.Hom.hom φ)) h).trans hmap_top)

/-- **Generation at a point and generation at a set `K ∋ z` are equivalent**, when the punctured
pair `(X∖{z}, X∖K)` has vanishing homology.  Route: `Work.Cohomology.relChains_triple_shortExact` for
the triple `Kᶜ ⊆ {z}ᶜ ⊆ X` (`g = relCokerMap X Kᶜ {z}ᶜ`, `tripleShort_g`), the vanishing in degrees
`N` and `N-1` makes `homologyMap g N` bijective, and `Work.Cohomology.relLocClass_restrict` says the
class at `K` maps to the class at `{z}` (the proof of `Work.Cohomology.local_generator_of_isZero` in
`Submission/Work/Cohomology/local_generator_convex.lean` carries out exactly this step). -/
theorem span_relLocClass_iff_of_isZero {X : TopCat} {N : ℕ}
    (c : (Work.Cohomology.singularChains ℤ X).homology N)
    {K : Set X} {z : X} (hzK : z ∈ K)
    (hvan : ∀ i, CategoryTheory.Limits.IsZero ((CategoryTheory.Limits.cokernel
      (Work.Cohomology.inclChainsSub X Kᶜ ({z} : Set X)ᶜ
        (fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK)))).homology i)) :
    Submodule.span ℤ {Work.Cohomology.relLocClass X N c K} = ⊤ ↔
      Submodule.span ℤ {Work.Cohomology.relLocClass X N c ({z} : Set X)} = ⊤ := by
  have hsub : Kᶜ ⊆ ({z} : Set X)ᶜ := fun x hx hxz => hx (Set.mem_singleton_iff.mp hxz ▸ hzK)
  have hKz : ({z} : Set X) ⊆ K := fun y hy => Set.mem_singleton_iff.mp hy ▸ hzK
  let S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
    Work.Cohomology.tripleShort X Kᶜ ({z} : Set X)ᶜ hsub
  have hSE : S.ShortExact :=
    Work.Cohomology.relChains_triple_shortExact X Kᶜ ({z} : Set X)ᶜ hsub
  have hSg : S.g = Work.Cohomology.relCokerMap X Kᶜ ({z} : Set X)ᶜ hsub :=
    Work.Cohomology.tripleShort_g X Kᶜ ({z} : Set X)ᶜ hsub
  have hvanS : ∀ i, IsZero (S.X₁.homology i) := fun i => hvan i
  haveI : Epi S.g := hSE.epi_g
  -- the map on homology in degree `N` is injective, from the vanishing of `H_N(X∖{z}, X∖K)`
  have hinj : Function.Injective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap X Kᶜ ({z} : Set X)ᶜ hsub) N) := by
    rw [← hSg]
    have hexact : (ShortComplex.mk (HomologicalComplex.homologyMap S.f N)
        (HomologicalComplex.homologyMap S.g N) _).Exact := hSE.homology_exact₂ N
    have hrange := ShortComplex.Exact.moduleCat_range_eq_ker hexact
    have hf0 : HomologicalComplex.homologyMap S.f N = 0 := IsZero.eq_zero_of_src (hvanS N) _
    have hrange0 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.f N)).range = ⊥ := by
      rw [hf0]
      exact LinearMap.range_zero
    have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g N)).ker = ⊥ := by
      rw [← hrange, hrange0]
    exact LinearMap.ker_eq_bot.mp hker
  -- and it is surjective, from the vanishing of `H_{N-1}(X∖{z}, X∖K)`
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap X Kᶜ ({z} : Set X)ᶜ hsub) N) := by
    rw [← hSg]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · -- in degree `0` there is no incoming differential
      subst hN
      haveI : Epi (S.g.f 0) := inferInstance
      exact (ModuleCat.epi_iff_surjective _).mp
        (HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0
          (fun j hj => Nat.succ_ne_zero j hj))
    · -- in degree `N = m+1` the connecting map `H_N(X₃) → H_m(X₁)` has vanishing target
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN)
      have hij : (ComplexShape.down ℕ).Rel (m + 1) m := ComplexShape.down_mk (m + 1) m rfl
      have hexact3 := hSE.homology_exact₃ (m + 1) m hij
      have hrange3 := ShortComplex.Exact.moduleCat_range_eq_ker hexact3
      have hz : IsZero (S.X₁.homology m) := hvanS m
      have hδ0 : hSE.δ (m + 1) m hij = 0 := IsZero.eq_zero_of_tgt hz _
      have hker0 : (ModuleCat.Hom.hom (hSE.δ (m + 1) m hij)).ker = ⊤ := by
        rw [hδ0]
        exact LinearMap.ker_zero
      have htop : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap S.g (m + 1))).range = ⊤ := by
        rw [hrange3, hker0]
      exact LinearMap.range_eq_top.mp htop
  -- the class at `K` maps to the class at `{z}`
  have hrestrict : HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap X Kᶜ ({z} : Set X)ᶜ hsub) N
      (Work.Cohomology.relLocClass X N c K) =
        Work.Cohomology.relLocClass X N c ({z} : Set X) :=
    Work.Cohomology.relLocClass_restrict X N c hKz
  have key := span_singleton_iff_of_bijective
    (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap X Kᶜ ({z} : Set X)ᶜ hsub) N)
    (Work.Cohomology.relLocClass X N c K) hinj hsurj
  rw [← hrestrict]
  exact key.symm

end Work.ThomBordism.doubleFC
