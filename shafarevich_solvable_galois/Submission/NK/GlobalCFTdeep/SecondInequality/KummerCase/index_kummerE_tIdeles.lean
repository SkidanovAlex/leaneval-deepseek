import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The index of Milne's subgroup `E` inside the idèles supported on `S ∪ T`

Milne, *Class Field Theory*, Chapter VII §6 (the Kummer case of the second inequality) works
with the subgroup

`E := ∏_{v ∈ S} K_v^{×p} · ∏_{v ∈ T} K_v^× · ∏_{v ∉ S ∪ T} U_v ≤ 𝕀_K`

of the idèle group (`KummerCase.kummerE`).  The point of `E` is that
`𝕀_{K,S∪T} / E ≅ ∏_{v ∈ S} K_v^× / (K_v^×)^p`: the conditions defining `E` are imposed at the
places `v ∈ S` (where they cut out the `p`-th powers) and outside `S ∪ T` (where they cut out
the local units, exactly as for the `(S ∪ T)`-idèles), while at the places of `T` there is no
condition at all.

This file computes that index:

`[𝕀_{K,S∪T} : E] = ∏_{v ∈ S} #(K_v^× / (K_v^×)^p)`.

The proof is a direct construction of a bijection between the quotient
`𝕀_{K,S∪T} / E` and the product `∏_{v ∈ S} K_v^×/(K_v^×)^p`; no group structure on the product
is used.  The quotient map is the (multiplicatively written) componentwise reduction
`x ↦ (x_v (K_v^×)^p)_{v ∈ S}`, which is onto because an idèle may be prescribed arbitrarily at
the finitely many places of `S` and be `1` everywhere else.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped RestrictedProduct
open NumberField

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

open NK.GlobalCFT

/-- The local `p`-th power quotient `K_vˣ / (K_vˣ)^p` at a place `v`. -/
abbrev localPowQuot (K : Type) [Field K] [NumberField K] (p : ℕ) (v : Place K) : Type _ :=
  (Place.localField K v)ˣ ⧸ (localPow (K := K) p v)

theorem index_kummerE_tIdeles {K : Type} [Field K] [NumberField K] (p : ℕ)
    (S T : Finset (NK.GlobalCFT.Place K)) :
    ((KummerCase.kummerE (K := K) p S T).subgroupOf
        (NK.GlobalCFTdeep.TIdeles ((S : Set (NK.GlobalCFT.Place K)) ∪ (T : Set (NK.GlobalCFT.Place K))))).index
      = ∏ v ∈ S, Nat.card ((NK.GlobalCFT.Place.localField K v)ˣ ⧸ (KummerCase.localPow (K := K) p v)) := by
  classical
  -- The `(S ∪ T)`-idèles, viewed as a subgroup of the idèle group.
  set U : Subgroup (Idele K) := TIdeles ((S : Set (Place K)) ∪ (T : Set (Place K))) with hU
  -- Milne's subgroup `E`, as a subgroup of `𝕀_{K,S∪T}`.
  set H : Subgroup ↥U := (kummerE (K := K) p S T).subgroupOf U with hH
  have hUT : ∀ v : Place K, v ∉ S → v ∉ T →
      v ∉ ((S : Set (Place K)) ∪ (T : Set (Place K))) :=
    fun v hv hvT => by rw [Set.mem_union]; exact not_or.mpr ⟨hv, hvT⟩
  -- Membership in `E` inside `𝕀_{K,S∪T}`: only the conditions at the places of `S` matter.
  have memH : ∀ x : ↥U, x ∈ H ↔ ∀ v ∈ S, x.1 v ∈ localPow (K := K) p v := by
    intro x
    have hxT : x.1 ∈ TIdeles ((S : Set (Place K)) ∪ (T : Set (Place K))) := hU ▸ x.2
    rw [hH, Subgroup.mem_subgroupOf, mem_kummerE]
    exact ⟨fun h => h.1, fun h => ⟨h, fun v hv hvT => (mem_TIdeles.mp hxT) v (hUT v hv hvT)⟩⟩
  -- The componentwise reduction to the local power quotients at the places of `S`.
  let ϑ : ↥U → (∀ v : {v : Place K // v ∈ S}, localPowQuot K p v.1) :=
    fun x v => QuotientGroup.mk (x.1 v.1)
  -- Its fibres are the cosets of `E`.
  have hϑ : ∀ a b : ↥U, ϑ a = ϑ b ↔ a⁻¹ * b ∈ H := by
    intro a b
    constructor
    · intro h
      rw [memH]
      intro v hv
      have h1 : QuotientGroup.mk (a.1 v) = QuotientGroup.mk (b.1 v) := congrFun h ⟨v, hv⟩
      rw [QuotientGroup.eq] at h1
      have h2 : (a⁻¹ * b).1 v = (a.1 v)⁻¹ * (b.1 v) := rfl
      rw [h2]
      exact h1
    · intro h
      funext v
      rw [QuotientGroup.eq]
      have h1 := (memH (a⁻¹ * b)).mp h v v.2
      have h2 : (a⁻¹ * b).1 v.1 = (a.1 v.1)⁻¹ * (b.1 v.1) := rfl
      rwa [h2] at h1
  -- The reduction is onto: prescribe the components at `S` and take `1` elsewhere.
  have hϑsurj : Function.Surjective ϑ := by
    intro y
    choose a ha using fun v : {v : Place K // v ∈ S} => QuotientGroup.mk_surjective (y v)
    let xfun : (v : Place K) → (Place.localField K v)ˣ :=
      fun v => if h : v ∈ S then a ⟨v, h⟩ else 1
    have hxfun : ∀ v, v ∉ S → xfun v ∈ Place.localUnits K v := by
      intro v hv
      show (if h : v ∈ S then a ⟨v, h⟩ else 1) ∈ Place.localUnits K v
      rw [dif_neg hv]
      exact Subgroup.one_mem _
    have hxev : ∀ᶠ v in Filter.cofinite, xfun v ∈ Place.localUnits K v := by
      rw [Filter.eventually_cofinite]
      refine Set.Finite.subset S.finite_toSet ?_
      intro v hv
      by_contra hvS
      exact hv (hxfun v hvS)
    let x : Idele K := RestrictedProduct.mk xfun hxev
    have hxU : x ∈ U := by
      rw [hU, mem_TIdeles]
      intro v hv
      have hvS : v ∉ S := by
        intro h; exact hv (by rw [Set.mem_union]; exact Or.inl h)
      show x v ∈ Place.localUnits K v
      rw [show x v = xfun v from rfl]
      exact hxfun v hvS
    refine ⟨⟨x, hxU⟩, ?_⟩
    funext v
    show QuotientGroup.mk (x v.1) = y v
    rw [show x v.1 = xfun v.1 from rfl]
    rw [show xfun v.1 = a v from by simp only [xfun, dif_pos v.2]]
    exact ha v
  -- The induced map on the quotient is a bijection.
  let f : (↥U ⧸ H) → (∀ v : {v : Place K // v ∈ S}, localPowQuot K p v.1) :=
    Quotient.lift ϑ (fun a b hab => (hϑ a b).mpr (QuotientGroup.leftRel_apply.mp hab))
  have hfmk : ∀ a : ↥U, f (QuotientGroup.mk a) = ϑ a := fun a => rfl
  have hf_inj : Function.Injective f := by
    intro qa qb h
    obtain ⟨a, ha⟩ := Quotient.exists_rep qa
    obtain ⟨b, hb⟩ := Quotient.exists_rep qb
    rw [← ha, ← hb] at h ⊢
    rw [hfmk a, hfmk b] at h
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hϑ a b).mp h))
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hϑsurj y
    exact ⟨QuotientGroup.mk x, by rw [hfmk x]; exact hx⟩
  have hcard : Nat.card (↥U ⧸ H) =
      Nat.card (∀ v : {v : Place K // v ∈ S}, localPowQuot K p v.1) :=
    Nat.card_eq_of_bijective f ⟨hf_inj, hf_surj⟩
  calc H.index = Nat.card (↥U ⧸ H) := Subgroup.index_eq_card H
    _ = Nat.card (∀ v : {v : Place K // v ∈ S}, localPowQuot K p v.1) := hcard
    _ = ∏ v : {v : Place K // v ∈ S}, Nat.card (localPowQuot K p v.1) := Nat.card_pi
    _ = ∏ v ∈ S, Nat.card (localPowQuot K p v) := by
          rw [Finset.univ_eq_attach S]
          exact Finset.prod_attach S (fun v => Nat.card (localPowQuot K p v))

end NK.GlobalCFTdeep.SecondInequality.KummerCase
