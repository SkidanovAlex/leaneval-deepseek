import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.phi1_defs
import Submission.Work.SSGRoute.eCoh_map
import Submission.Work.SSGRoute.groupCohomology_levelInf_nat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Injectivity of inflation for characters with trivial coefficients (node `E3`, step 4)

The target `Work.SSGRoute.PT.e3_character_inflation` states that for a tower `k ⊆ K ⊆ M` of finite
Galois number fields the inflation

`inflTriv : H¹(Gal(K/k), 𝔽_p) ⟶ H¹(Gal(M/k), 𝔽_p)`

along the surjection `galRes k K M : Gal(M/k) ↠ Gal(K/k)` kills no nonzero class.

The proof is structural and works for an *arbitrary* surjection of groups `f : H ↠ G` and *arbitrary*
coefficients `V` (with trivial action):

* `eCoh`: the degree-`n` isomorphism `Hⁿ(G, A) ≃+ Extⁿ_G(ℤ, A)` of the `E0b` bridge, with its
  group-change naturality `Work.SSGRoute.eCoh_map`
  (`eCoh (map f φ y) = extHMap f φ (eCoh y)`);
* `groupCohomology_inflTriv_injective`: on the group-cohomology side the map is injective, because
  a `1`-cocycle with trivial coefficients has a representative function `z : G → V`, the map
  `mapCocycles₁ f (trivResInv f V)` is precomposition with `f`, and the `1`-coboundaries of a
  trivial module are zero (`groupCohomology.coboundaries₁_eq_bot_of_isTrivial`).  Hence
  `map f φ 1 (H1π z) = 0` forces `z ∘ f = 0`, and `z = 0` since `f` is surjective.
-/

namespace Work.SSGRoute.PT

open CategoryTheory
open SSGRoute.PTExt

/-- **Inflation on `H¹` with trivial coefficients is injective in the group-cohomology model.**

For a surjective group homomorphism `f : H ↠ G` and any additive commutive group `V` (with the
trivial action of both groups), the induced map
`H¹(G, V) → H¹(H, V)` — which on the `Ext` side is `extHMap f (trivResInv f V)` — is injective.

The proof only uses the cocycle description: `H¹_induction_on` reduces a class to `H1π z` for a
`1`-cocycle `z : G → V`; `H1π_comp_map_apply` computes the image as `H1π (mapCocycles₁ f φ z)`;
`mapCocycles₁` along `trivResInv` is precomposition with `f`; and `coboundaries₁` of a trivial
module is `⊥`. -/
theorem groupCohomology_inflTriv_injective {G H : Type} [Group G] [Group H]
    (f : H →* G) (hf : Function.Surjective f) (V : Type) [AddCommGroup V]
    [Module SSGRoute.PTExt.Coeff V] :
    Function.Injective
      (ModuleCat.Hom.hom (groupCohomology.map f (trivResInv f V) 1)) := by
  -- the underlying function of `mapCocycles₁` along `trivResInv` is precomposition with `f`
  have coe_aux : ∀ z : ↥(groupCohomology.cocycles₁ (Rep.trivial Coeff G V)),
      ⇑((ConcreteCategory.hom (groupCohomology.mapCocycles₁ f (trivResInv f V))) z)
        = fun h : H => z (f h) := by
    intro z
    funext h
    rw [groupCohomology.coe_mapCocycles₁]
    rfl
  -- a class killed by inflation is zero
  have key : ∀ w : groupCohomology (Rep.trivial Coeff G V) 1,
      (groupCohomology.map f (trivResInv f V) 1).hom w = 0 → w = 0 := by
    intro w hw
    induction w using groupCohomology.H1_induction_on with
    | h z =>
      rw [groupCohomology.H1π_comp_map_apply f (trivResInv f V) z] at hw
      rw [groupCohomology.H1π_eq_zero_iff] at hw
      rw [groupCohomology.coboundaries₁_eq_bot_of_isTrivial] at hw
      rw [Submodule.mem_bot] at hw
      rw [coe_aux z] at hw
      have hz : z = 0 := by
        refine groupCohomology.cocycles₁_ext fun g => ?_
        obtain ⟨h, rfl⟩ := hf g
        exact congrFun hw h
      rw [hz, map_zero]
  intro x y hxy
  have h0 : (groupCohomology.map f (trivResInv f V) 1).hom (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key (x - y) h0)

/-- **Inflation along a surjection kills no nonzero class of `Ext¹_G(ℤ, V)` for trivial `V`.**

This is the `Ext`-side form of the level-inclusion step: for `f : H ↠ G` surjective and `V` a module
with trivial action, `extHMap f (trivResInv f V)` — the `Ext`-change-of-group map with the identity
coefficient map — is injective.  The proof transports the statement across the `E0b` isomorphism
`eCoh` using its group-change naturality `Work.SSGRoute.eCoh_map`, and applies
`groupCohomology_inflTriv_injective`. -/
theorem extHMap_trivResInv_injective {G H : Type} [Group G] [Group H]
    (f : H →* G) (hf : Function.Surjective f) (V : Type) [AddCommGroup V]
    [Module SSGRoute.PTExt.Coeff V]
    (h : extH (Rep.trivial Coeff G V) 1) (hne : h ≠ 0) :
    extHMap f (trivResInv f V) h ≠ 0 := by
  intro hzero
  apply hne
  -- `eCoh` intertwines the group-change maps, so the inflated class vanishes in group cohomology
  have hnat := Work.SSGRoute.eCoh_map 1 G H f (Rep.trivial Coeff G V)
    (Rep.trivial Coeff H V) (trivResInv f V)
    ((SSGRoute.PTExt.eCoh 1 G (Rep.trivial Coeff G V)).symm h)
  have hy0 : (groupCohomology.map f (trivResInv f V) 1).hom
      ((SSGRoute.PTExt.eCoh 1 G (Rep.trivial Coeff G V)).symm h) = 0 :=
    (SSGRoute.PTExt.eCoh 1 H (Rep.trivial Coeff H V)).injective (by
      rw [hnat, AddEquiv.apply_symm_apply, hzero]
      exact (map_zero _).symm)
  have hy : (SSGRoute.PTExt.eCoh 1 G (Rep.trivial Coeff G V)).symm h = 0 := by
    apply groupCohomology_inflTriv_injective (G := G) (H := H) f hf V
    rw [hy0, map_zero]
  calc h = SSGRoute.PTExt.eCoh 1 G (Rep.trivial Coeff G V)
              ((SSGRoute.PTExt.eCoh 1 G (Rep.trivial Coeff G V)).symm h) :=
        (AddEquiv.apply_symm_apply _ h).symm
    _ = SSGRoute.PTExt.eCoh 1 G (Rep.trivial Coeff G V) 0 := by rw [hy]
    _ = 0 := map_zero _

/-- **Inflation of a character along a level inclusion is injective (trivial coefficients).**

For a tower `k ⊆ K ⊆ M` of finite Galois number fields, the inflation
`inflTriv : H¹(Gal(K/k), 𝔽_p) → H¹(Gal(M/k), 𝔽_p)` (the `Ext`-change-of-group map along
`galRes k K M`, with the identity coefficient map) kills no nonzero class.

This is the step-4 input of node `E3` (`phi1_trivial_mono`) on its corrected route
(`Submission/Work/SSGRoute/PT/E3_PLAN.md`): the Kummer/CFT detection of a non-`p`-th-power `a ∈ C_k`
produces a nontrivial character over some level `L/k`; moving it into `Ω` and taking the compositum
`M := L₀ ⊔ K` requires that the character stays nonzero when inflated to the bigger level `M ⊇ K`,
which is what this states.  Mathematically it is the trivial-coefficient case of
inflation–restriction: `Gal(M/k) ↠ Gal(K/k)` acts trivially on `𝔽_p`, `H¹(-,𝔽_p) = Hom(-,𝔽_p)`, and
inflation is precomposition with the surjection.

Formally the argument is the general structural fact `extHMap_trivResInv_injective` above: the
`E0b` isomorphism `eCoh` (`Hⁿ(-,A) ≃+ Extⁿ(ℤ,A)`) is compatible with change of group
(`Work.SSGRoute.eCoh_map`), where the trivial-coefficient map is injective because it is
precomposition with a surjection on the level of `1`-cocycles. -/
theorem e3_character_inflation (p : ℕ) [Fact p.Prime] (k K M : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Field M] [NumberField M] [Algebra k K] [Algebra K M]
    [Algebra k M] [IsScalarTower k K M] [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k M] [IsGalois k M]
    (h : SSGRoute.PTExt.extH (Rep.trivial SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) (ZMod p)) 1)
    (hne : h ≠ 0) :
    SSGRoute.PTExt.inflTriv (k := k) (K := K) (L := M) (ZMod p) h ≠ 0 := by
  have hf : Function.Surjective (SSGRoute.PTExt.galRes k K M) :=
    AlgEquiv.restrictNormalHom_surjective M
  simpa only [SSGRoute.PTExt.inflTriv] using
    extHMap_trivResInv_injective (SSGRoute.PTExt.galRes k K M) hf (ZMod p) h hne

end Work.SSGRoute.PT
