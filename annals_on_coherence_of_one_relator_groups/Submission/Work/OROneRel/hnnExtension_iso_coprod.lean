import Mathlib

namespace Work.OROneRel

open Monoid

universe u

/-- An HNN extension whose base group is a free product `H ∗ K` and whose associated subgroups lie in the first factor is the free product of the HNN extension of `H` with `K`; the tracking says the isomorphism is the canonical one (`of (inl h) ↦ inl (of h)`, `of (inr k) ↦ inr k`, stable letter to `inl` of the small stable letter).  Proof sketch: forward map `HNNExtension.lift (Coprod.inl.comp HNNExtension.of) (Coprod.inl HNNExtension.t)` and inverse `Coprod.lift (HNNExtension.lift HNNExtension.of HNNExtension.t _) HNNExtension.of`, the conjugation condition being `HNNExtension.t_mul_of`; both compositions are the identity by `HNNExtension.hom_ext` and `Monoid.Coprod.hom_ext`.  One may take `A' = A.map Coprod.inl`, `B' = B.map Coprod.inl` with `φ'` the induced isomorphism. -/
theorem hnnExtension_iso_coprod {H K : Type u} [Group H] [Group K]
    (A B : Subgroup H) (φ : A ≃* B) :
    ∃ (A' B' : Subgroup (Monoid.Coprod H K)) (φ' : A' ≃* B')
      (E : HNNExtension (Monoid.Coprod H K) A' B' φ' ≃*
        Monoid.Coprod (HNNExtension H A B φ) K),
      (∀ h : H, E (HNNExtension.of (Monoid.Coprod.inl h)) =
        Monoid.Coprod.inl (HNNExtension.of h)) ∧
      (∀ k : K, E (HNNExtension.of (Monoid.Coprod.inr k)) = Monoid.Coprod.inr k) ∧
      E HNNExtension.t = Monoid.Coprod.inl HNNExtension.t := by
  -- The canonical injection of the first free factor
  let i : H →* Monoid.Coprod H K := Monoid.Coprod.inl
  have hi : Function.Injective i := Monoid.Coprod.inl_injective
  -- The associated subgroups of the free product, lying in the first factor
  let A' : Subgroup (Monoid.Coprod H K) := A.map i
  let B' : Subgroup (Monoid.Coprod H K) := B.map i
  -- and the induced isomorphism between them
  let eA : A ≃* A' := A.equivMapOfInjective i hi
  let eB : B ≃* B' := B.equivMapOfInjective i hi
  let φ' : A' ≃* B' := eA.symm.trans (φ.trans eB)
  have eA_apply : ∀ a : A, (eA a : Monoid.Coprod H K) = i (a : H) := fun a =>
    Subgroup.coe_equivMapOfInjective_apply A i hi a
  have eB_apply : ∀ b : B, (eB b : Monoid.Coprod H K) = i (b : H) := fun b =>
    Subgroup.coe_equivMapOfInjective_apply B i hi b
  have φ'_apply : ∀ a : A, φ' (eA a) = eB (φ a) := by
    intro a; simp only [φ', MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  -- The forward homomorphism: `of (inl h) ↦ inl (of h)`, `of (inr k) ↦ inr k`,
  -- and the stable letter of the big HNN extension to `inl` of the small stable letter
  let fwd : Monoid.Coprod H K →* Monoid.Coprod (HNNExtension H A B φ) K :=
    Monoid.Coprod.lift (Monoid.Coprod.inl.comp HNNExtension.of) Monoid.Coprod.inr
  have hfwd_inl : ∀ h : H, fwd (Monoid.Coprod.inl h) =
      Monoid.Coprod.inl (HNNExtension.of h) := fun h => rfl
  have hfwd_inr : ∀ k : K, fwd (Monoid.Coprod.inr k) = Monoid.Coprod.inr k := fun k => rfl
  let x : Monoid.Coprod (HNNExtension H A B φ) K := Monoid.Coprod.inl HNNExtension.t
  -- the conjugation relation is exactly Britton's relation in the small HNN extension
  have hc : ∀ a' : A', x * fwd (a' : Monoid.Coprod H K) =
      fwd (φ' a' : Monoid.Coprod H K) * x := by
    intro a'
    obtain ⟨a, rfl⟩ : ∃ a : A, eA a = a' := ⟨eA.symm a', by simp⟩
    rw [eA_apply, φ'_apply, eB_apply, hfwd_inl, hfwd_inl]
    show Monoid.Coprod.inl HNNExtension.t * Monoid.Coprod.inl (HNNExtension.of (a:H)) =
      Monoid.Coprod.inl (HNNExtension.of ((φ a : B) : H)) * Monoid.Coprod.inl HNNExtension.t
    rw [← map_mul, ← map_mul, HNNExtension.t_mul_of]
  let E : HNNExtension (Monoid.Coprod H K) A' B' φ' →* Monoid.Coprod (HNNExtension H A B φ) K :=
    HNNExtension.lift fwd x hc
  have hE_of : ∀ g : Monoid.Coprod H K, E (HNNExtension.of g) = fwd g := fun g =>
    HNNExtension.lift_of fwd x hc g
  have hE_t : E HNNExtension.t = x := HNNExtension.lift_t fwd x hc
  -- The backward homomorphism
  let ofI : H →* HNNExtension (Monoid.Coprod H K) A' B' φ' := HNNExtension.of.comp i
  let tI : HNNExtension (Monoid.Coprod H K) A' B' φ' := HNNExtension.t
  have hcInv : ∀ a : A, tI * ofI (a : H) = ofI ((φ a : B) : H) * tI := by
    intro a
    have h := HNNExtension.t_mul_of (φ := φ') (eA a)
    rw [eA_apply a] at h
    rw [φ'_apply a, eB_apply (φ a)] at h
    exact h
  let g1 : HNNExtension H A B φ →* HNNExtension (Monoid.Coprod H K) A' B' φ' :=
    HNNExtension.lift ofI tI hcInv
  let g2 : K →* HNNExtension (Monoid.Coprod H K) A' B' φ' :=
    HNNExtension.of.comp Monoid.Coprod.inr
  have hg1_of : ∀ a : H, g1 (HNNExtension.of a) = ofI a := fun a =>
    HNNExtension.lift_of ofI tI hcInv a
  have hg1_t : g1 HNNExtension.t = tI := HNNExtension.lift_t ofI tI hcInv
  have hg2 : ∀ k : K, g2 k = HNNExtension.of (Monoid.Coprod.inr k) := fun k => rfl
  let Einv : Monoid.Coprod (HNNExtension H A B φ) K →* HNNExtension (Monoid.Coprod H K) A' B' φ' :=
    Monoid.Coprod.lift g1 g2
  have hEinv_inl : ∀ y : HNNExtension H A B φ, Einv (Monoid.Coprod.inl y) = g1 y := fun y => rfl
  have hEinv_inr : ∀ k : K, Einv (Monoid.Coprod.inr k) = g2 k := fun k => rfl
  -- the two composites are the identity
  have hleft : Einv.comp E = MonoidHom.id _ := by
    apply HNNExtension.hom_ext
    · apply Monoid.Coprod.hom_ext
      · apply MonoidHom.ext; intro h
        change Einv (E (HNNExtension.of (Monoid.Coprod.inl h))) =
          HNNExtension.of (Monoid.Coprod.inl h)
        rw [hE_of, hfwd_inl h, hEinv_inl, hg1_of h]
        try rfl
      · apply MonoidHom.ext; intro k
        change Einv (E (HNNExtension.of (Monoid.Coprod.inr k))) =
          HNNExtension.of (Monoid.Coprod.inr k)
        rw [hE_of, hfwd_inr k, hEinv_inr k, hg2 k]
    · change Einv (E HNNExtension.t) = HNNExtension.t
      rw [hE_t]
      change Einv (Monoid.Coprod.inl HNNExtension.t) = HNNExtension.t
      rw [hEinv_inl, hg1_t]
  have hright : E.comp Einv = MonoidHom.id _ := by
    apply Monoid.Coprod.hom_ext
    · apply HNNExtension.hom_ext
      · apply MonoidHom.ext; intro a
        change E (Einv (Monoid.Coprod.inl (HNNExtension.of a))) =
          Monoid.Coprod.inl (HNNExtension.of a)
        rw [hEinv_inl, hg1_of]
        change E (HNNExtension.of (i a)) = Monoid.Coprod.inl (HNNExtension.of a)
        rw [hE_of, hfwd_inl]
      · change E (Einv (Monoid.Coprod.inl HNNExtension.t)) =
          Monoid.Coprod.inl HNNExtension.t
        rw [hEinv_inl, hg1_t]
        rw [hE_t]
    · apply MonoidHom.ext; intro k
      change E (Einv (Monoid.Coprod.inr k)) = Monoid.Coprod.inr k
      rw [hEinv_inr]
      change E (HNNExtension.of (Monoid.Coprod.inr k)) = Monoid.Coprod.inr k
      rw [hE_of, hfwd_inr]
  let Eeq : HNNExtension (Monoid.Coprod H K) A' B' φ' ≃*
      Monoid.Coprod (HNNExtension H A B φ) K :=
    MonoidHom.toMulEquiv E Einv hleft hright
  refine ⟨A', B', φ', Eeq, ?_, ?_, ?_⟩
  · intro h
    change E (HNNExtension.of (Monoid.Coprod.inl h)) = Monoid.Coprod.inl (HNNExtension.of h)
    rw [hE_of, hfwd_inl]
  · intro k
    change E (HNNExtension.of (Monoid.Coprod.inr k)) = Monoid.Coprod.inr k
    rw [hE_of, hfwd_inr]
  · change E HNNExtension.t = Monoid.Coprod.inl HNNExtension.t
    rw [hE_t]

end Work.OROneRel
