import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.card_open_local
import Submission.NK.NUV2.LC.h2CardTransport
import Submission.NK.NUV2.LC.RouteB.isLive_of_isMuOpen
import Submission.NK.NUV2.LC.RouteB.card_h2P_of_isOpen_fixing

/-!
# Route B: the local Brauer cardinality at an open subgroup of a closed subgroup of local type

This file proves `NK.NUV2.LC.RouteB.card_h2P_of_open_le_localType`: if `V ≤ Gal(K'/K)` is a closed
subgroup *of local type* (i.e. continuously isomorphic, via `e`, to the fixing subgroup
`Gal(κ'/M)` of a finite Galois extension `M/κ` of the `p`-adic field `κ = 𝔮.adicCompletion L`, where
`M` contains a primitive `p`-th root of unity) and `V' = V ⊓ N ≤ V` is open in `V` (intersection
with an open subgroup `N`), then `H²(V', Z/p)` has exactly `p` elements.

The mathematics is a single transport.  The image `W` of `V'` under the continuous isomorphism `e`
(composed with the inclusion `↥M.fixingSubgroup ↪ Gal(κ'/κ)`) is an **open** subgroup of
`Gal(κ'/κ)` which still fixes `ζ_p` (because `W ≤ M.fixingSubgroup` and `ζ_p ∈ M`); and the
cardinality of the profinite cohomology is invariant under a topological isomorphism of the
subgroups (`NK.NUV2.LC.RouteB.natCard_h2Profinite_of_homeomorph`).  The local computation at the
open subgroup `W` is `NK.NUV2.LC.RouteB.card_h2P_of_isOpen_fixing`.

* `imageSubtypeEquiv` (namespace `OpenLeAux`) — the elementary topological isomorphism between a
  subgroup `V ≤ G` and its image under `e` followed by the inclusion `↥A ↪ H` of a subgroup
  `A ≤ H`;
* `card_h2P_of_open_le_localType` — the target.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.NUV2.LC.RouteB

universe u

namespace OpenLeAux

/-- **The image of a subgroup under a topological group isomorphism followed by the inclusion of a
subgroup.**  If `e : G ≃ₜ* ↥A` is a topological group isomorphism onto a subgroup `A ≤ H` and
`V ≤ G`, then `V` and its image `V.map (A.subtype ∘ e) ≤ H` are topologically isomorphic (the
isomorphism is `x ↦ e x`, with the canonical group structure on the image). -/
noncomputable def imageSubtypeEquiv {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] (A : Subgroup H) (e : G ≃ₜ* ↥A) (V : Subgroup G) :
    ↥V ≃ₜ* ↥(V.map ((Subgroup.subtype A).comp (e : G →* ↥A))) := by
  let f : G →* H := (Subgroup.subtype A).comp (e : G →* ↥A)
  have hmem : ∀ y : ↥(V.map f), (y : H) ∈ A := by
    intro y
    obtain ⟨a, -, ha⟩ := Subgroup.mem_map.mp y.2
    rw [← ha]
    exact (e a : ↥A).2
  have hmemV : ∀ y : ↥(V.map f), e.symm (⟨(y : H), hmem y⟩ : ↥A) ∈ V := by
    intro y
    obtain ⟨a, ha, ha'⟩ := Subgroup.mem_map.mp y.2
    have h : e a = ⟨(y : H), hmem y⟩ := Subtype.ext ha'
    rw [← h, ContinuousMulEquiv.symm_apply_apply e a]
    exact ha
  refine ContinuousMulEquiv.mk
    { toFun := fun x => ⟨f (x : G), ⟨(x : G), x.2, rfl⟩⟩
      invFun := fun y => ⟨e.symm ⟨(y : H), hmem y⟩, hmemV y⟩
      left_inv := fun x => Subtype.ext (by
        show e.symm (⟨(f (x : G)), hmem ⟨f (x : G), ⟨(x : G), x.2, rfl⟩⟩⟩ : ↥A) = (x : G)
        rw [show (⟨(f (x : G)), hmem ⟨f (x : G), ⟨(x : G), x.2, rfl⟩⟩⟩ : ↥A) = e x from
            Subtype.ext rfl,
          ContinuousMulEquiv.symm_apply_apply e x])
      right_inv := fun y => Subtype.ext (by
        show f (e.symm ⟨(y : H), hmem y⟩) = (y : H)
        rw [show f (e.symm ⟨(y : H), hmem y⟩)
          = ((e (e.symm ⟨(y : H), hmem y⟩) : ↥A) : H) from rfl,
          ContinuousMulEquiv.apply_symm_apply e ⟨(y : H), hmem y⟩])
      map_mul' := fun x y => Subtype.ext (by simp [map_mul]) } ?_ ?_
  · refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (e.continuous_toFun.comp continuous_subtype_val)
  · refine Continuous.subtype_mk ?_ _
    exact e.symm.continuous_toFun.comp (Continuous.subtype_mk continuous_subtype_val _)

end OpenLeAux

/-- **Route B: the local Brauer cardinality at an open subgroup of a subgroup of local type.**

Let `p` be a prime, `K` a number field with separable closure `K'` and `V ≤ Gal(K'/K)` a closed
subgroup which is continuously isomorphic (`e`) to the fixing subgroup `M.fixingSubgroup` of a
finite Galois extension `M/κ` of the `p`-adic field `κ = 𝔮.adicCompletion L`, where `M` contains a
primitive `p`-th root of unity.  Then every subgroup `V' = V ⊓ N` of `V` which is open in `V`
(`N` open in `Gal(K'/K)`) satisfies `Nat.card (H²(V', Z/p)) = p`.

Proof: the image `W` of `V'` under `e` (inside `Gal(κ'/κ)`) is open in `Gal(κ'/κ)` — it is the
image of the open subgroup `V' ≤ ↥V` under the homeomorphism `e` followed by the inclusion of the
open subgroup `M.fixingSubgroup` — and it still fixes `ζ_p`, since `W ≤ M.fixingSubgroup` and the
root of unity lies in `M`.  The topological isomorphism `↥V' ≃ₜ* ↥W`
(`OpenLeAux.imageSubtypeEquiv`, composed with `subgroupOfEquiv`) transports the cardinality
(`natCard_h2Profinite_of_homeomorph`), and the local computation at the open subgroup `W` is
`card_h2P_of_isOpen_fixing`. -/
theorem card_h2P_of_open_le_localType (p : ℕ) (hp : p.Prime) {K K' : Type} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K')
    (hζ : IsPrimitiveRoot ζ p) {L : Type} [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (M : FiniteGaloisIntermediateField (𝔮.adicCompletion L)
      (SeparableClosure (𝔮.adicCompletion L)))
    (hζM : ∃ ζ' : ↥M, IsPrimitiveRoot ζ' p) (V : Subgroup Gal(K'/K))
    (hVcl : IsClosed (V : Set Gal(K'/K))) (e : ↥V ≃ₜ* ↥(M.fixingSubgroup))
    (V' : Subgroup Gal(K'/K)) (hV'le : V' ≤ V)
    (hV'open : ∃ N : Subgroup Gal(K'/K), IsOpen (N : Set Gal(K'/K)) ∧ V' = V ⊓ N) :
    Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V') = p := by
  classical
  -- ### The image `W` of `V'` in the local Galois group `Gal(κ'/κ)`
  set W : Subgroup Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L) :=
    (V'.subgroupOf V).map
      ((Subgroup.subtype (M.fixingSubgroup)).comp (e : ↥V →* ↥M.fixingSubgroup)) with hWdef
  -- ### The topological isomorphism `↥V' ≃ₜ* ↥W`
  have hiso : ↥V' ≃ₜ* ↥W :=
    (NK.NUV2.LC.RouteB.subgroupOfEquiv V V' hV'le).trans
      (OpenLeAux.imageSubtypeEquiv (M.fixingSubgroup) e (V'.subgroupOf V))
  -- ### `W` is open in `Gal(κ'/κ)`
  have hV'sub_open : IsOpen ((V'.subgroupOf V : Subgroup ↥V) : Set ↥V) := by
    obtain ⟨N, hNopen, hNeq⟩ := hV'open
    have h1 : ((V'.subgroupOf V : Subgroup ↥V) : Set ↥V)
        = Subtype.val ⁻¹' ((N : Subgroup Gal(K'/K)) : Set Gal(K'/K)) := by
      rw [hNeq]
      ext x
      simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨x.2, h⟩
    rw [h1]
    exact hNopen.preimage continuous_subtype_val
  have hMopen : IsOpen ((M.fixingSubgroup :
      Subgroup Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) :
      Set Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) :=
    IntermediateField.fixingSubgroup_isOpen M.toIntermediateField
  have hWcoe : (W : Set Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L))
      = (fun x : ↥V => (((e x : ↥M.fixingSubgroup)) :
          Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)))
        '' ((V'.subgroupOf V : Subgroup ↥V) : Set ↥V) := by
    rw [hWdef, Subgroup.coe_map]
    exact Set.image_congr (fun x _ => rfl)
  have hWopen : IsOpen (W :
      Set Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) := by
    rw [hWcoe]
    exact ((hMopen.isOpenMap_subtype_val).comp (Homeomorph.isOpenMap e.toHomeomorph)) _
      hV'sub_open
  -- ### `W` fixes a primitive `p`-th root of unity
  have hζloc : IsPrimitiveRoot
      (algebraMap ↥M (SeparableClosure (𝔮.adicCompletion L)) hζM.choose) p :=
    hζM.choose_spec.map_of_injective
      (f := (algebraMap ↥M (SeparableClosure (𝔮.adicCompletion L))))
      (algebraMap ↥M (SeparableClosure (𝔮.adicCompletion L))).injective
  have hWle : W ≤ M.fixingSubgroup := by
    rw [hWdef]
    intro x hx
    obtain ⟨y, -, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    exact (e y).2
  have hadj : W ≤ (IntermediateField.adjoin (𝔮.adicCompletion L)
      {(algebraMap ↥M (SeparableClosure (𝔮.adicCompletion L)) hζM.choose)}).fixingSubgroup := by
    refine le_trans hWle (IntermediateField.fixingSubgroup_le ?_)
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hζM.choose.2
  -- ### Transport the cardinality to the open subgroup `W` and apply the local computation
  have hcard := NK.NUV2.LC.RouteB.natCard_h2Profinite_of_homeomorph (k := K) (k' := K')
    (κ := 𝔮.adicCompletion L) (κ' := SeparableClosure (𝔮.adicCompletion L)) V' W p hiso
  rw [hcard]
  exact card_h2P_of_isOpen_fixing p hp 𝔮 _ hζloc W hWopen hadj

end NK.NUV2.LC.RouteB
