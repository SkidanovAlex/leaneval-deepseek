import Mathlib
import Submission.Work.OROneRel.presentedGroup_iso_coprod_of_supported
import Submission.Work.ORReductions.Basic

namespace Work.ORReductions.OneRelator

/-!
# Splitting off the free factor carried by the support of a relator

Let `r ∈ F(α)` be a relator supported on a set `Z ⊆ α` of generators.  Then `r` is the image
of a word `r' ∈ F(Z)` under the canonical map `F(Z) → F(α)`, and the one-relator group
`G = ⟨α | r⟩` splits as a free product `H ∗ T` where

* `H` is the image of the canonical map `⟨Z | r'⟩ →* G` (so `⟨Z | r'⟩ ≃* H`), and every
  generator `of a` with `a ∈ Z` lies in `H`;
* `T` is the free factor complementary to `H`.

The main technical ingredient is `exists_injective_iso_of_supportedOn`, which shows that the map
`⟨Z | r'⟩ →* G` is *injective* (a retraction argument) while at the same time exhibiting the
free-product decomposition `G ≃* ⟨Z | r'⟩ ∗ F(α \ Z)`.

This file is the `_alt` version of `Work.ORReductions.OneRelator.supported_freeFactor`; the
statement is identical.
-/

/-- **The support splitting, with the explicit injective map.**  If `r` is supported on `Z`, then
there is `r' ∈ F(Z)` with `F(Z) → F(α)`, `r' ↦ r`, such that the induced map
`φ₁ : ⟨Z | r'⟩ →* ⟨α | r⟩` is injective, sends generators to generators, and such that `⟨α | r⟩`
is the free product of `⟨Z | r'⟩` with the free group on the complementary generators. -/
lemma exists_injective_iso_of_supportedOn {α : Type*} (r : FreeGroup α) (Z : Set α)
    (h : Work.OROneRel.SupportedOn r Z) :
    ∃ (r' : FreeGroup ↥Z)
      (φ₁ : PresentedGroup ({r'} : Set (FreeGroup ↥Z)) →* PresentedGroup ({r} : Set (FreeGroup α))),
      Function.Injective φ₁ ∧
      (∀ a : ↥Z, φ₁ (PresentedGroup.of a) = PresentedGroup.of (a : α)) ∧
      Nonempty (PresentedGroup ({r} : Set (FreeGroup α)) ≃*
        Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup {a : α // a ∉ Z})) := by
  classical
  obtain ⟨r', hr'⟩ := Work.OROneRel.exists_map_subtype_val_eq_of_supportedOn r Z h
  let β : Type _ := {a : α // a ∉ Z}
  let σ : FreeGroup ↥Z →* FreeGroup α := FreeGroup.map (fun a : ↥Z => (a : α))
  have hσ : σ r' = r := hr'
  have hst : Set.MapsTo (⇑σ) ({r'} : Set (FreeGroup ↥Z)) ({r} : Set (FreeGroup α)) := by
    intro x hx
    simp only [Set.mem_singleton_iff] at hx ⊢
    rw [hx]; exact hσ
  let φ₁ : PresentedGroup ({r'} : Set (FreeGroup ↥Z)) →* PresentedGroup ({r} : Set (FreeGroup α)) :=
    PresentedGroup.map σ hst
  have hφ₁_of : ∀ x : ↥Z, φ₁ (PresentedGroup.of x) = PresentedGroup.of (x : α) := by
    intro x
    change PresentedGroup.map σ hst (PresentedGroup.of x) = PresentedGroup.of (x : α)
    rw [show PresentedGroup.map σ hst (PresentedGroup.of x) =
        PresentedGroup.mk ({r} : Set (FreeGroup α)) (σ (FreeGroup.of x)) from rfl]
    rw [show σ (FreeGroup.of x) = FreeGroup.of (x : α) from FreeGroup.map.of]
    rfl
  let τ : FreeGroup β →* FreeGroup α := FreeGroup.map (fun b : β => (b : α))
  let φ₂ : FreeGroup β →* PresentedGroup ({r} : Set (FreeGroup α)) :=
    (PresentedGroup.mk ({r} : Set (FreeGroup α))).comp τ
  have hφ₂_of : ∀ y : β, φ₂ (FreeGroup.of y) = PresentedGroup.of (y : α) := by
    intro y
    change (PresentedGroup.mk ({r} : Set (FreeGroup α))).comp τ (FreeGroup.of y) = _
    rw [MonoidHom.comp_apply, show τ (FreeGroup.of y) = FreeGroup.of (y : α) from FreeGroup.map.of]
    rfl
  let φ : Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup β) →*
      PresentedGroup ({r} : Set (FreeGroup α)) := Monoid.Coprod.lift φ₁ φ₂
  have hφ_inl : ∀ x, φ (Monoid.Coprod.inl x) = φ₁ x :=
    fun x => Monoid.Coprod.lift_apply_inl φ₁ φ₂ x
  have hφ_inr : ∀ y, φ (Monoid.Coprod.inr y) = φ₂ y :=
    fun y => Monoid.Coprod.lift_apply_inr φ₁ φ₂ y
  let θ' : α → Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup β) :=
    fun a => if ha : a ∈ Z then Monoid.Coprod.inl (PresentedGroup.of (⟨a, ha⟩ : ↥Z))
             else Monoid.Coprod.inr (FreeGroup.of (⟨a, ha⟩ : β))
  let θ : FreeGroup α →* Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup β) :=
    FreeGroup.lift θ'
  have hθ_of : ∀ x : α, θ (FreeGroup.of x) = θ' x := fun x => FreeGroup.lift_apply_of
  have hθσ : θ.comp σ =
      (Monoid.Coprod.inl : PresentedGroup ({r'} : Set (FreeGroup ↥Z)) →* _).comp
        (PresentedGroup.mk ({r'} : Set (FreeGroup ↥Z))) := by
    refine FreeGroup.ext_hom _ _ fun a => ?_
    show θ (σ (FreeGroup.of a)) =
      Monoid.Coprod.inl (PresentedGroup.mk ({r'} : Set (FreeGroup ↥Z)) (FreeGroup.of a))
    rw [show σ (FreeGroup.of a) = FreeGroup.of (a : α) from FreeGroup.map.of, hθ_of]
    rw [show θ' (a : α) =
      Monoid.Coprod.inl (PresentedGroup.of (⟨(a : α), a.2⟩ : ↥Z)) from dif_pos a.2]
    rfl
  have hθr : θ r = 1 := by
    rw [← hσ, ← MonoidHom.comp_apply, hθσ]
    rw [MonoidHom.comp_apply, PresentedGroup.one_of_mem (Set.mem_singleton r'), map_one]
  let ψ : PresentedGroup ({r} : Set (FreeGroup α)) →*
      Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup β) :=
    PresentedGroup.toGroup (f := θ') (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      change θ r = 1
      exact hθr)
  have hψ_of : ∀ x : α, ψ (PresentedGroup.of x) = θ' x := fun x => PresentedGroup.toGroup.of _
  have hφψ : φ.comp ψ = MonoidHom.id (PresentedGroup ({r} : Set (FreeGroup α))) := by
    refine PresentedGroup.ext fun a => ?_
    show φ (ψ (PresentedGroup.of a)) = PresentedGroup.of a
    rw [hψ_of]
    by_cases ha : a ∈ Z
    · rw [show θ' a = Monoid.Coprod.inl (PresentedGroup.of (⟨a, ha⟩ : ↥Z)) from dif_pos ha,
        hφ_inl, hφ₁_of]
    · rw [show θ' a = Monoid.Coprod.inr (FreeGroup.of (⟨a, ha⟩ : β)) from dif_neg ha,
        hφ_inr, hφ₂_of]
  have hψφ : ψ.comp φ =
      MonoidHom.id (Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup β)) := by
    refine Monoid.Coprod.hom_ext ?_ ?_
    · rw [MonoidHom.comp_assoc,
        show φ.comp Monoid.Coprod.inl = φ₁ from Monoid.Coprod.lift_comp_inl φ₁ φ₂,
        MonoidHom.id_comp]
      refine PresentedGroup.ext fun x => ?_
      show ψ (φ₁ (PresentedGroup.of x)) = Monoid.Coprod.inl (PresentedGroup.of x)
      rw [hφ₁_of, hψ_of]
      rw [show θ' (x : α) =
        Monoid.Coprod.inl (PresentedGroup.of (⟨(x : α), x.2⟩ : ↥Z)) from dif_pos x.2]
    · rw [MonoidHom.comp_assoc,
        show φ.comp Monoid.Coprod.inr = φ₂ from Monoid.Coprod.lift_comp_inr φ₁ φ₂,
        MonoidHom.id_comp]
      refine FreeGroup.ext_hom _ _ fun y => ?_
      show ψ (φ₂ (FreeGroup.of y)) = Monoid.Coprod.inr (FreeGroup.of y)
      rw [hφ₂_of, hψ_of]
      rw [show θ' (y : α) =
        Monoid.Coprod.inr (FreeGroup.of (⟨(y : α), y.2⟩ : β)) from dif_neg y.2]
  have hφ_inj : Function.Injective φ := (MonoidHom.toMulEquiv ψ φ hφψ hψφ).symm.injective
  have hφ₁_inj : Function.Injective φ₁ := by
    intro a b hab
    have h1 : φ (Monoid.Coprod.inl a) = φ (Monoid.Coprod.inl b) := by
      rw [hφ_inl a, hφ_inl b, hab]
    exact Monoid.Coprod.inl_injective (hφ_inj h1)
  exact ⟨r', φ₁, hφ₁_inj, hφ₁_of, ⟨MonoidHom.toMulEquiv ψ φ hφψ hψφ⟩⟩

theorem supported_freeFactor_alt {α : Type*} (r : FreeGroup α) (Z : Set α)
    (h : Work.OROneRel.SupportedOn r Z) :
    ∃ (r' : FreeGroup ↥Z) (H T : Subgroup (PresentedGroup ({r} : Set (FreeGroup α)))),
      (∀ a : ↥Z, PresentedGroup.of (a : α) ∈ H) ∧
      Nonempty (PresentedGroup ({r'} : Set (FreeGroup ↥Z)) ≃* H) ∧
      Nonempty (PresentedGroup ({r} : Set (FreeGroup α)) ≃* Monoid.Coprod H T) := by
  classical
  obtain ⟨r', φ₁, hφ₁_inj, hφ₁_of, ⟨e⟩⟩ := exists_injective_iso_of_supportedOn r Z h
  let κ : FreeGroup {a : α // a ∉ Z} →* PresentedGroup ({r} : Set (FreeGroup α)) :=
    e.symm.toMonoidHom.comp (Monoid.Coprod.inr :
      FreeGroup {a : α // a ∉ Z} →*
        Monoid.Coprod (PresentedGroup ({r'} : Set (FreeGroup ↥Z))) (FreeGroup {a : α // a ∉ Z}))
  have hκ_inj : Function.Injective κ := e.symm.injective.comp Monoid.Coprod.inr_injective
  refine ⟨r', φ₁.range, κ.range, ?_, ?_, ?_⟩
  · intro a
    exact MonoidHom.mem_range.mpr ⟨PresentedGroup.of a, hφ₁_of a⟩
  · exact ⟨MonoidHom.ofInjective hφ₁_inj⟩
  · exact ⟨e.trans (MulEquiv.coprodCongr
      (MonoidHom.ofInjective hφ₁_inj) (MonoidHom.ofInjective hκ_inj))⟩

end Work.ORReductions.OneRelator
