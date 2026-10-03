import Mathlib
import Submission.Work.OROneRel.presentedGroup_iso_coprod_of_supported
import Submission.Work.ORReductions.Basic

/-!
# A supported relator splits off a free factor
-/

namespace Work.ORReductions.OneRelator

theorem supported_freeFactor {α : Type*} (r : FreeGroup α) (Z : Set α)
    (h : Work.OROneRel.SupportedOn r Z) :
    ∃ (r' : FreeGroup ↥Z) (H T : Subgroup (PresentedGroup ({r} : Set (FreeGroup α)))),
      (∀ a : ↥Z, PresentedGroup.of (a : α) ∈ H) ∧
      Nonempty (PresentedGroup ({r'} : Set (FreeGroup ↥Z)) ≃* H) ∧
      Nonempty (PresentedGroup ({r} : Set (FreeGroup α)) ≃* Monoid.Coprod H T) := by
  classical
  obtain ⟨r', hr'⟩ := Work.OROneRel.exists_map_subtype_val_eq_of_supportedOn r Z h
  let β : Type _ := {a : α // a ∉ Z}
  let σ : FreeGroup ↥Z →* FreeGroup α := FreeGroup.map (fun a : ↥Z => (a : α))
  let τ : FreeGroup β →* FreeGroup α := FreeGroup.map (fun b : β => (b : α))
  have hσr' : σ r' = r := hr'
  have hst : Set.MapsTo (⇑σ) ({r'} : Set (FreeGroup ↥Z)) ({r} : Set (FreeGroup α)) := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx ⊢
    rw [hx, hσr']
  let φ₁ : PresentedGroup ({r'} : Set (FreeGroup ↥Z)) →*
      PresentedGroup ({r} : Set (FreeGroup α)) := PresentedGroup.map σ hst
  let φ₂ : FreeGroup β →* PresentedGroup ({r} : Set (FreeGroup α)) :=
    (PresentedGroup.mk ({r} : Set (FreeGroup α))).comp τ
  have hφ₁_of : ∀ a : ↥Z, φ₁ (PresentedGroup.of a) = PresentedGroup.of (a : α) := by
    intro a
    show PresentedGroup.map σ hst (PresentedGroup.of a) = PresentedGroup.of (a : α)
    rw [show PresentedGroup.map σ hst (PresentedGroup.of a) =
        PresentedGroup.mk ({r} : Set (FreeGroup α)) (σ (FreeGroup.of a)) from rfl,
      show σ (FreeGroup.of a) = FreeGroup.of (a : α) from FreeGroup.map.of]
    rfl
  have hφ₂_of : ∀ b : β, φ₂ (FreeGroup.of b) = PresentedGroup.of (b : α) := by
    intro b
    show (PresentedGroup.mk ({r} : Set (FreeGroup α))).comp τ (FreeGroup.of b) =
      PresentedGroup.of (b : α)
    rw [MonoidHom.comp_apply,
      show τ (FreeGroup.of b) = FreeGroup.of (b : α) from FreeGroup.map.of]
    rfl
  let f₁ : α → PresentedGroup ({r'} : Set (FreeGroup ↥Z)) :=
    fun a => if ha : a ∈ Z then PresentedGroup.of (⟨a, ha⟩ : ↥Z) else 1
  have hlift₁ : (FreeGroup.lift f₁).comp σ = PresentedGroup.mk ({r'} : Set (FreeGroup ↥Z)) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    rw [MonoidHom.comp_apply, show σ (FreeGroup.of a) = FreeGroup.of (a : α) from FreeGroup.map.of,
      FreeGroup.lift_apply_of]
    show f₁ (a : α) = PresentedGroup.of a
    rw [show f₁ (a : α) = PresentedGroup.of (⟨(a : α), a.2⟩ : ↥Z) from dif_pos a.2]
  have hker₁ : FreeGroup.lift f₁ r = 1 := by
    rw [← hσr', ← MonoidHom.comp_apply, hlift₁,
      PresentedGroup.one_of_mem (Set.mem_singleton r')]
  let ρ : PresentedGroup ({r} : Set (FreeGroup α)) →*
      PresentedGroup ({r'} : Set (FreeGroup ↥Z)) :=
    PresentedGroup.toGroup (f := f₁) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hker₁)
  have hρ_of : ∀ a : α, ρ (PresentedGroup.of a) = f₁ a := fun a => PresentedGroup.toGroup.of _
  have hρφ₁ : ρ.comp φ₁ = MonoidHom.id _ := by
    refine PresentedGroup.ext fun a => ?_
    rw [MonoidHom.comp_apply, hφ₁_of, hρ_of]
    show f₁ (a : α) = PresentedGroup.of a
    rw [show f₁ (a : α) = PresentedGroup.of (⟨(a : α), a.2⟩ : ↥Z) from dif_pos a.2]
  have hinj₁ : Function.Injective φ₁ := by
    intro x y hxy
    have hx : ρ (φ₁ x) = x := by rw [← MonoidHom.comp_apply, hρφ₁]; rfl
    have hy : ρ (φ₁ y) = y := by rw [← MonoidHom.comp_apply, hρφ₁]; rfl
    rw [← hx, ← hy, hxy]
  let f₂ : α → FreeGroup β := fun a => if ha : a ∈ Z then 1 else FreeGroup.of (⟨a, ha⟩ : β)
  have hlift₂ : (FreeGroup.lift f₂).comp σ = 1 := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    rw [MonoidHom.comp_apply, show σ (FreeGroup.of a) = FreeGroup.of (a : α) from FreeGroup.map.of,
      FreeGroup.lift_apply_of]
    show f₂ (a : α) = 1
    exact dif_pos a.2
  have hker₂ : FreeGroup.lift f₂ r = 1 := by
    rw [← hσr', ← MonoidHom.comp_apply, hlift₂, MonoidHom.one_apply]
  let ρ₂ : PresentedGroup ({r} : Set (FreeGroup α)) →* FreeGroup β :=
    PresentedGroup.toGroup (f := f₂) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hker₂)
  have hρ₂_of : ∀ a : α, ρ₂ (PresentedGroup.of a) = f₂ a := fun a => PresentedGroup.toGroup.of _
  have hρ₂φ₂ : ρ₂.comp φ₂ = MonoidHom.id _ := by
    refine FreeGroup.ext_hom _ _ fun b => ?_
    rw [MonoidHom.comp_apply, hφ₂_of, hρ₂_of]
    show f₂ (b : α) = FreeGroup.of b
    rw [show f₂ (b : α) = FreeGroup.of (⟨(b : α), b.2⟩ : β) from dif_neg b.2]
  have hinj₂ : Function.Injective φ₂ := by
    intro x y hxy
    have hx : ρ₂ (φ₂ x) = x := by rw [← MonoidHom.comp_apply, hρ₂φ₂]; rfl
    have hy : ρ₂ (φ₂ y) = y := by rw [← MonoidHom.comp_apply, hρ₂φ₂]; rfl
    rw [← hx, ← hy, hxy]
  -- Isomorphisms from the abstract factors onto their images.
  have hρH : (ρ.comp (φ₁.range).subtype).comp (MonoidHom.rangeRestrict φ₁) = MonoidHom.id _ := by
    rw [MonoidHom.comp_assoc, MonoidHom.subtype_comp_rangeRestrict, hρφ₁]
  have hHρ : (MonoidHom.rangeRestrict φ₁).comp (ρ.comp (φ₁.range).subtype) = MonoidHom.id _ := by
    refine MonoidHom.ext fun x => Subtype.ext ?_
    show φ₁ (ρ ↑x) = ↑x
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp x.2
    have h1 : ρ (φ₁ z) = z := by rw [← MonoidHom.comp_apply, hρφ₁]; rfl
    calc φ₁ (ρ ↑x) = φ₁ (ρ (φ₁ z)) := by rw [hz]
      _ = φ₁ z := by rw [h1]
      _ = ↑x := hz
  let heH : PresentedGroup ({r'} : Set (FreeGroup ↥Z)) ≃* φ₁.range :=
    MonoidHom.toMulEquiv (MonoidHom.rangeRestrict φ₁) (ρ.comp (φ₁.range).subtype) hρH hHρ
  have heH_apply : ∀ y : PresentedGroup ({r'} : Set (FreeGroup ↥Z)),
      (heH y : PresentedGroup ({r} : Set (FreeGroup α))) = φ₁ y := fun y => by simp [heH]
  have hρT : (ρ₂.comp (φ₂.range).subtype).comp (MonoidHom.rangeRestrict φ₂) = MonoidHom.id _ := by
    rw [MonoidHom.comp_assoc, MonoidHom.subtype_comp_rangeRestrict, hρ₂φ₂]
  have hTρ : (MonoidHom.rangeRestrict φ₂).comp (ρ₂.comp (φ₂.range).subtype) = MonoidHom.id _ := by
    refine MonoidHom.ext fun x => Subtype.ext ?_
    show φ₂ (ρ₂ ↑x) = ↑x
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp x.2
    have h1 : ρ₂ (φ₂ z) = z := by rw [← MonoidHom.comp_apply, hρ₂φ₂]; rfl
    calc φ₂ (ρ₂ ↑x) = φ₂ (ρ₂ (φ₂ z)) := by rw [hz]
      _ = φ₂ z := by rw [h1]
      _ = ↑x := hz
  let heT : FreeGroup β ≃* φ₂.range :=
    MonoidHom.toMulEquiv (MonoidHom.rangeRestrict φ₂) (ρ₂.comp (φ₂.range).subtype) hρT hTρ
  have heT_apply : ∀ y : FreeGroup β,
      (heT y : PresentedGroup ({r} : Set (FreeGroup α))) = φ₂ y := fun y => by simp [heT]
  -- The map recording which factor each generator of `α` lies in.
  let f₃ : α → Monoid.Coprod (φ₁.range) (φ₂.range) := fun a =>
    if ha : a ∈ Z then
      Monoid.Coprod.inl ⟨PresentedGroup.of a, ⟨PresentedGroup.of ⟨a, ha⟩, hφ₁_of ⟨a, ha⟩⟩⟩
    else
      Monoid.Coprod.inr ⟨PresentedGroup.of a, ⟨FreeGroup.of ⟨a, ha⟩, hφ₂_of ⟨a, ha⟩⟩⟩
  have hf₃pos : ∀ (a : α) (ha : a ∈ Z), f₃ a = Monoid.Coprod.inl
      ⟨PresentedGroup.of a, ⟨PresentedGroup.of ⟨a, ha⟩, hφ₁_of ⟨a, ha⟩⟩⟩ := by
    intro a ha
    simp only [f₃, dif_pos ha]
  have hf₃neg : ∀ (a : α) (ha : a ∉ Z), f₃ a = Monoid.Coprod.inr
      ⟨PresentedGroup.of a, ⟨FreeGroup.of ⟨a, ha⟩, hφ₂_of ⟨a, ha⟩⟩⟩ := by
    intro a ha
    simp only [f₃, dif_neg ha]
  have hker₃ : FreeGroup.lift f₃ r = 1 := by
    have key : (FreeGroup.lift f₃).comp σ =
        (Monoid.Coprod.inl : φ₁.range →* Monoid.Coprod (φ₁.range) (φ₂.range)).comp
          ((MonoidHom.rangeRestrict φ₁).comp (PresentedGroup.mk ({r'} : Set (FreeGroup ↥Z)))) := by
      refine FreeGroup.ext_hom _ _ fun a => ?_
      show FreeGroup.lift f₃ (σ (FreeGroup.of a)) = Monoid.Coprod.inl
        ((MonoidHom.rangeRestrict φ₁) ((PresentedGroup.mk ({r'} : Set (FreeGroup ↥Z))) (FreeGroup.of a)))
      rw [show σ (FreeGroup.of a) = FreeGroup.of (a : α) from FreeGroup.map.of,
        FreeGroup.lift_apply_of]
      rw [hf₃pos (a : α) a.2]
      refine congrArg Monoid.Coprod.inl (Subtype.ext ?_)
      rw [MonoidHom.coe_rangeRestrict]
      exact (hφ₁_of a).symm
    have hcomp : FreeGroup.lift f₃ (σ r') = 1 := by
      rw [← MonoidHom.comp_apply, key, MonoidHom.comp_apply, MonoidHom.comp_apply,
        PresentedGroup.one_of_mem (Set.mem_singleton r'), map_one, map_one]
    rw [show FreeGroup.lift f₃ r = FreeGroup.lift f₃ (σ r') from
      congrArg (fun t => FreeGroup.lift f₃ t) hσr'.symm, hcomp]
  let Ψ : PresentedGroup ({r} : Set (FreeGroup α)) →* Monoid.Coprod (φ₁.range) (φ₂.range) :=
    PresentedGroup.toGroup (f := f₃) (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact hker₃)
  have hΨ_of : ∀ a : α, Ψ (PresentedGroup.of a) = f₃ a := fun a => PresentedGroup.toGroup.of _
  have hΨφ₁ : Ψ.comp φ₁ = Monoid.Coprod.inl.comp (MonoidHom.rangeRestrict φ₁) := by
    refine PresentedGroup.ext fun a => ?_
    show Ψ (φ₁ (PresentedGroup.of a)) = Monoid.Coprod.inl
      ((MonoidHom.rangeRestrict φ₁) (PresentedGroup.of a))
    rw [hφ₁_of, hΨ_of]
    rw [hf₃pos (a : α) a.2]
    refine congrArg Monoid.Coprod.inl (Subtype.ext ?_)
    rw [MonoidHom.coe_rangeRestrict]
    exact (hφ₁_of a).symm
  have hΨφ₂ : Ψ.comp φ₂ = Monoid.Coprod.inr.comp (MonoidHom.rangeRestrict φ₂) := by
    refine FreeGroup.ext_hom _ _ fun b => ?_
    show Ψ (φ₂ (FreeGroup.of b)) = Monoid.Coprod.inr
      ((MonoidHom.rangeRestrict φ₂) (FreeGroup.of b))
    rw [hφ₂_of, hΨ_of]
    rw [hf₃neg (b : α) b.2]
    refine congrArg Monoid.Coprod.inr (Subtype.ext ?_)
    rw [MonoidHom.coe_rangeRestrict]
    exact (hφ₂_of b).symm
  let Φ : Monoid.Coprod (φ₁.range) (φ₂.range) →* PresentedGroup ({r} : Set (FreeGroup α)) :=
    Monoid.Coprod.lift (φ₁.range).subtype (φ₂.range).subtype
  have hΦ_inl : Φ.comp Monoid.Coprod.inl = (φ₁.range).subtype :=
    Monoid.Coprod.lift_comp_inl _ _
  have hΦ_inr : Φ.comp Monoid.Coprod.inr = (φ₂.range).subtype :=
    Monoid.Coprod.lift_comp_inr _ _
  have hΦΨ : Φ.comp Ψ = MonoidHom.id _ := by
    refine PresentedGroup.ext fun a => ?_
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hΨ_of]
    by_cases ha : a ∈ Z
    · rw [hf₃pos a ha]; rfl
    · rw [hf₃neg a ha]; rfl
  have hΨH : Ψ.comp (φ₁.range).subtype = Monoid.Coprod.inl := by
    refine MonoidHom.ext fun x => ?_
    have key : φ₁ (heH.symm x) = ↑x := by
      rw [← heH_apply (heH.symm x)]
      exact congrArg (Subtype.val) (heH.apply_symm_apply x)
    calc (Ψ.comp (φ₁.range).subtype) x = Ψ (↑x) := rfl
      _ = Ψ (φ₁ (heH.symm x)) := by rw [key]
      _ = (Ψ.comp φ₁) (heH.symm x) := rfl
      _ = (Monoid.Coprod.inl.comp (MonoidHom.rangeRestrict φ₁)) (heH.symm x) := by rw [hΨφ₁]
      _ = Monoid.Coprod.inl x := by
            rw [MonoidHom.comp_apply]
            exact congrArg Monoid.Coprod.inl
              (Subtype.ext (by rw [MonoidHom.coe_rangeRestrict]; exact key))
  have hΨT : Ψ.comp (φ₂.range).subtype = Monoid.Coprod.inr := by
    refine MonoidHom.ext fun x => ?_
    have key : φ₂ (heT.symm x) = ↑x := by
      rw [← heT_apply (heT.symm x)]
      exact congrArg (Subtype.val) (heT.apply_symm_apply x)
    calc (Ψ.comp (φ₂.range).subtype) x = Ψ (↑x) := rfl
      _ = Ψ (φ₂ (heT.symm x)) := by rw [key]
      _ = (Ψ.comp φ₂) (heT.symm x) := rfl
      _ = (Monoid.Coprod.inr.comp (MonoidHom.rangeRestrict φ₂)) (heT.symm x) := by rw [hΨφ₂]
      _ = Monoid.Coprod.inr x := by
            rw [MonoidHom.comp_apply]
            exact congrArg Monoid.Coprod.inr
              (Subtype.ext (by rw [MonoidHom.coe_rangeRestrict]; exact key))
  have hΨΦ : Ψ.comp Φ = MonoidHom.id _ := by
    refine Monoid.Coprod.hom_ext ?_ ?_
    · rw [MonoidHom.comp_assoc, hΦ_inl, MonoidHom.id_comp]; exact hΨH
    · rw [MonoidHom.comp_assoc, hΦ_inr, MonoidHom.id_comp]; exact hΨT
  refine ⟨r', φ₁.range, φ₂.range, ?_, ?_, ?_⟩
  · intro a
    exact ⟨PresentedGroup.of a, hφ₁_of a⟩
  · exact ⟨heH⟩
  · exact ⟨MonoidHom.toMulEquiv Ψ Φ hΦΨ hΨΦ⟩

end Work.ORReductions.OneRelator
