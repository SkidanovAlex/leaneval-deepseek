import Mathlib
import Submission.Work.OROneRel.presentedGroup_iso_coprod_of_supported

namespace Work.OROneRel

universe u

theorem iso_coprod_of_supported_spec {α : Type u} (r : FreeGroup α) (Z : Set α)
    (h : Work.OROneRel.SupportedOn r Z) :
    ∃ (r' : FreeGroup {a : α // a ∈ Z}) (e : PresentedGroup ({r} : Set (FreeGroup α)) ≃*
        Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup {a : α // a ∈ Z})))
          (FreeGroup {a : α // a ∉ Z})),
      FreeGroup.map (fun a : {a : α // a ∈ Z} => (a : α)) r' = r ∧
      (∀ (x : α) (hx : x ∈ Z), e (PresentedGroup.of x) =
        Monoid.Coprod.inl (PresentedGroup.of (⟨x, hx⟩ : {a : α // a ∈ Z}))) ∧
      (∀ (x : α) (hx : x ∉ Z), e (PresentedGroup.of x) =
        Monoid.Coprod.inr (FreeGroup.of (⟨x, hx⟩ : {a : α // a ∉ Z}))) := by
  classical
  obtain ⟨r', hr'⟩ := exists_map_subtype_val_eq_of_supportedOn r Z h
  let β : Type u := {a : α // a ∉ Z}
  let σ : FreeGroup ↥Z →* FreeGroup α := FreeGroup.map (fun a : ↥Z => (a : α))
  let τ : FreeGroup β →* FreeGroup α := FreeGroup.map (fun b : β => (b : α))
  have hσ : σ r' = r := hr'
  have hst : Set.MapsTo (⇑σ) ({r'} : Set (FreeGroup ↥Z)) ({r} : Set (FreeGroup α)) := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx ⊢
    rw [hx]; exact hσ
  -- the map `⟨Z | r'⟩ →* ⟨α | r⟩`
  let φ₁ : PresentedGroup ({r'} : Set (FreeGroup ↥Z)) →* PresentedGroup ({r} : Set (FreeGroup α)) :=
    PresentedGroup.map σ hst
  -- the map `F(α \ Z) →* ⟨α | r⟩`
  let φ₂ : FreeGroup β →* PresentedGroup ({r} : Set (FreeGroup α)) :=
    (PresentedGroup.mk ({r} : Set (FreeGroup α))).comp τ
  -- the map `⟨Z | r'⟩ ∗ F(α \ Z) →* ⟨α | r⟩`
  let φ : Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup β) →*
      PresentedGroup ({r} : Set (FreeGroup α)) := Monoid.Coprod.lift φ₁ φ₂
  -- the map `F(α) →* ⟨Z | r'⟩ ∗ F(α \ Z)` sending a generator to the factor containing it
  let θ' : α → Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup β) :=
    fun a => if ha : a ∈ Z then Monoid.Coprod.inl (PresentedGroup.of (⟨a, ha⟩ : ↥Z))
              else Monoid.Coprod.inr (FreeGroup.of (⟨a, ha⟩ : β))
  let θ : FreeGroup α →* Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup β) :=
    FreeGroup.lift θ'
  have hφ_inl : ∀ x, φ (Monoid.Coprod.inl x) = φ₁ x := fun x => Monoid.Coprod.lift_apply_inl φ₁ φ₂ x
  have hφ_inr : ∀ y, φ (Monoid.Coprod.inr y) = φ₂ y := fun y => Monoid.Coprod.lift_apply_inr φ₁ φ₂ y
  have hφ₁_of : ∀ x : ↥Z, φ₁ (PresentedGroup.of x) = PresentedGroup.of (x : α) := by
    intro x
    change PresentedGroup.map σ hst (PresentedGroup.of x) = PresentedGroup.of (x : α)
    rw [show PresentedGroup.map σ hst (PresentedGroup.of x) =
        PresentedGroup.mk ({r} : Set (FreeGroup α)) (σ (FreeGroup.of x)) from rfl]
    rw [show σ (FreeGroup.of x) = FreeGroup.of (x : α) from FreeGroup.map.of]
    rfl
  have hφ₂_of : ∀ y : β, φ₂ (FreeGroup.of y) = PresentedGroup.of (y : α) := by
    intro y
    change (PresentedGroup.mk ({r} : Set (FreeGroup α))).comp τ (FreeGroup.of y) =
      PresentedGroup.of (y : α)
    rw [MonoidHom.comp_apply, show τ (FreeGroup.of y) = FreeGroup.of (y : α) from FreeGroup.map.of]
    rfl
  have hθ_of : ∀ x : α, θ (FreeGroup.of x) = θ' x := fun x => FreeGroup.lift_apply_of
  -- `θ` kills the relator
  have hθσ : θ.comp σ = (Monoid.Coprod.inl : PresentedGroup ({r'} : Set (FreeGroup ↥Z)) →*
      Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup β)).comp
      (PresentedGroup.mk ({r'} : Set (FreeGroup ↥Z))) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    show θ (σ (FreeGroup.of a)) =
      Monoid.Coprod.inl (PresentedGroup.mk ({r'} : Set (FreeGroup ↥Z)) (FreeGroup.of a))
    rw [show σ (FreeGroup.of a) = FreeGroup.of (a : α) from FreeGroup.map.of, hθ_of]
    rw [show θ' (a : α) = Monoid.Coprod.inl (PresentedGroup.of (⟨(a : α), a.2⟩ : ↥Z)) from
      dif_pos a.2]
    rfl
  have hθr : θ r = 1 := by
    rw [← hσ, ← MonoidHom.comp_apply, hθσ]
    rw [MonoidHom.comp_apply, PresentedGroup.one_of_mem (Set.mem_singleton r'), map_one]
  -- the map `⟨α | r⟩ →* ⟨Z | r'⟩ ∗ F(α \ Z)`
  let ψ : PresentedGroup ({r} : Set (FreeGroup α)) →*
      Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup β) :=
    PresentedGroup.toGroup (f := θ') (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      change θ r = 1
      exact hθr)
  have hψ_of : ∀ x : α, ψ (PresentedGroup.of x) = θ' x := fun x => PresentedGroup.toGroup.of _
  -- `φ ∘ ψ = id`
  have hφψ : φ.comp ψ = MonoidHom.id (PresentedGroup ({r} : Set (FreeGroup α))) := by
    refine PresentedGroup.ext fun a => ?_
    show φ (ψ (PresentedGroup.of a)) = PresentedGroup.of a
    rw [hψ_of]
    by_cases ha : a ∈ Z
    · rw [show θ' a = Monoid.Coprod.inl (PresentedGroup.of (⟨a, ha⟩ : ↥Z)) from dif_pos ha,
        hφ_inl, hφ₁_of]
    · rw [show θ' a = Monoid.Coprod.inr (FreeGroup.of (⟨a, ha⟩ : β)) from dif_neg ha,
        hφ_inr, hφ₂_of]
  -- `ψ ∘ φ = id`
  have hψφ : ψ.comp φ =
      MonoidHom.id (Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup β)) := by
    refine Monoid.Coprod.hom_ext ?_ ?_
    · rw [MonoidHom.comp_assoc,
        show φ.comp Monoid.Coprod.inl = φ₁ from Monoid.Coprod.lift_comp_inl φ₁ φ₂,
        MonoidHom.id_comp]
      refine PresentedGroup.ext fun x => ?_
      show ψ (φ₁ (PresentedGroup.of x)) = Monoid.Coprod.inl (PresentedGroup.of x)
      rw [hφ₁_of, hψ_of]
      rw [show θ' (x : α) = Monoid.Coprod.inl (PresentedGroup.of (⟨(x : α), x.2⟩ : ↥Z)) from
        dif_pos x.2]
    · rw [MonoidHom.comp_assoc,
        show φ.comp Monoid.Coprod.inr = φ₂ from Monoid.Coprod.lift_comp_inr φ₁ φ₂,
        MonoidHom.id_comp]
      refine FreeGroup.ext_hom _ _ fun y => ?_
      show ψ (φ₂ (FreeGroup.of y)) = Monoid.Coprod.inr (FreeGroup.of y)
      rw [hφ₂_of, hψ_of]
      rw [show θ' (y : α) = Monoid.Coprod.inr (FreeGroup.of (⟨(y : α), y.2⟩ : β)) from dif_neg y.2]
  refine ⟨r', MonoidHom.toMulEquiv ψ φ hφψ hψφ, hσ, ?_, ?_⟩
  · intro x hx
    show ψ (PresentedGroup.of x) = Monoid.Coprod.inl (PresentedGroup.of (⟨x, hx⟩ : ↥Z))
    rw [hψ_of]
    rw [show θ' x = Monoid.Coprod.inl (PresentedGroup.of (⟨x, hx⟩ : ↥Z)) from dif_pos hx]
  · intro x hx
    show ψ (PresentedGroup.of x) = Monoid.Coprod.inr (FreeGroup.of (⟨x, hx⟩ : β))
    rw [hψ_of]
    rw [show θ' x = Monoid.Coprod.inr (FreeGroup.of (⟨x, hx⟩ : β)) from dif_neg hx]

end Work.OROneRel
