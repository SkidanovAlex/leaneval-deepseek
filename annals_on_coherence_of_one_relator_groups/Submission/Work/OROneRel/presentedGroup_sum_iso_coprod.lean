import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.iso_coprod_of_supported_spec

namespace Work.OROneRel

universe u

/-- A one-relator presentation on `β ⊕ γ` whose relator is the image under `Sum.inl` of a relator in `F(β)` splits as the free product of `⟨β | v ^ l⟩` with the free group on `γ`, with the canonical element tracking.  Proof sketch: the forward map is `PresentedGroup.toGroup` on the generator map `Sum.elim (Coprod.inl ∘ PresentedGroup.of) (Coprod.inr ∘ FreeGroup.of)` (it kills the relator since `(Coprod.inl (mk v)) ^ l = 1`), the inverse is `Coprod.lift (PresentedGroup.map (FreeGroup.map Sum.inl) _) (FreeGroup.lift (fun c => PresentedGroup.of (Sum.inr c)))`, and the two compositions are the identity by `PresentedGroup.ext` / `Monoid.Coprod.hom_ext` / `FreeGroup.ext_hom`.  The element tracking follows from the generator tracking (`PresentedGroup.toGroup.of`) by `FreeGroup.ext_hom`, since both sides are monoid homs in the argument.  Alternatively it is a specialisation of the already-proved `Work.OROneRel.iso_coprod_of_supported_spec` (with `Z = Set.range Sum.inl`), which additionally supplies the generator tracking. -/
theorem presentedGroup_sum_iso_coprod {β γ : Type u} (v : FreeGroup β) (l : ℕ) :
    ∃ (E : PresentedGroup ({(FreeGroup.map (Sum.inl : β → β ⊕ γ) v) ^ l} :
            Set (FreeGroup (β ⊕ γ))) ≃*
        Monoid.Coprod (PresentedGroup ({v ^ l} : Set (FreeGroup β))) (FreeGroup γ)),
      (∀ y : FreeGroup β, E (PresentedGroup.mk
          ({(FreeGroup.map (Sum.inl : β → β ⊕ γ) v) ^ l} : Set (FreeGroup (β ⊕ γ)))
            (FreeGroup.map (Sum.inl : β → β ⊕ γ) y)) =
        Monoid.Coprod.inl (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) y)) ∧
      (∀ k : FreeGroup γ, E (PresentedGroup.mk
          ({(FreeGroup.map (Sum.inl : β → β ⊕ γ) v) ^ l} : Set (FreeGroup (β ⊕ γ)))
            (FreeGroup.map (Sum.inr : γ → β ⊕ γ) k)) =
        Monoid.Coprod.inr k) := by
  classical
  -- The relator of the presentation on `β ⊕ γ`, the presented groups and the free product.
  let r : FreeGroup (β ⊕ γ) := (FreeGroup.map (Sum.inl : β → β ⊕ γ) v) ^ l
  let L := PresentedGroup ({r} : Set (FreeGroup (β ⊕ γ)))
  let P := PresentedGroup ({v ^ l} : Set (FreeGroup β))
  let R := Monoid.Coprod P (FreeGroup γ)
  -- the forward map `L →* R`, on generators `Sum.elim (inl ∘ of) (inr ∘ of)`
  let θ' : β ⊕ γ → R := Sum.elim (fun b => Monoid.Coprod.inl (PresentedGroup.of b))
    (fun c => Monoid.Coprod.inr (FreeGroup.of c))
  let θ : FreeGroup (β ⊕ γ) →* R := FreeGroup.lift θ'
  have hθ_of : ∀ a : β ⊕ γ, θ (FreeGroup.of a) = θ' a := fun a => FreeGroup.lift_apply_of
  -- `θ ∘ F(β) → F(β ⊕ γ) → R` is `Coprod.inl ∘ mk`
  have hθmap : θ.comp (FreeGroup.map (Sum.inl : β → β ⊕ γ)) =
      (Monoid.Coprod.inl : P →* R).comp (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β))) := by
    refine FreeGroup.ext_hom _ _ fun b => ?_
    show θ (FreeGroup.map Sum.inl (FreeGroup.of b)) =
      Monoid.Coprod.inl (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) (FreeGroup.of b))
    rw [FreeGroup.map.of, hθ_of]
    show θ' (Sum.inl b) =
      Monoid.Coprod.inl (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) (FreeGroup.of b))
    rw [show θ' (Sum.inl b) = Monoid.Coprod.inl (PresentedGroup.of b) from rfl]
    rfl
  -- hence `θ` kills the relator `r`
  have hθr : θ r = 1 := by
    show θ ((FreeGroup.map (Sum.inl : β → β ⊕ γ) v) ^ l) = 1
    have hmapv : θ (FreeGroup.map (Sum.inl : β → β ⊕ γ) v) =
        Monoid.Coprod.inl (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) :=
      DFunLike.congr_fun hθmap v
    have hrel : (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) ^ l = 1 := by
      have h1 := PresentedGroup.one_of_mem (rels := ({v ^ l} : Set (FreeGroup β)))
        (x := v ^ l) (Set.mem_singleton (v ^ l))
      rwa [map_pow] at h1
    rw [map_pow, hmapv, ← map_pow, hrel, map_one]
  -- the map `ψ : ⟨β ⊕ γ | r⟩ →* ⟨β | v ^ l⟩ ∗ F(γ)`
  let ψ : L →* R := PresentedGroup.toGroup (f := θ') (by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hθr)
  have hψ_of : ∀ a : β ⊕ γ, ψ (PresentedGroup.of a) = θ' a := fun a => PresentedGroup.toGroup.of _
  -- element tracking for the forward map
  have hψ_map_inl : ∀ y : FreeGroup β,
      ψ (PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ)))
        (FreeGroup.map (Sum.inl : β → β ⊕ γ) y)) =
      Monoid.Coprod.inl (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) y) := by
    have hcomp : ψ.comp ((PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ)))).comp
        (FreeGroup.map (Sum.inl : β → β ⊕ γ))) =
        (Monoid.Coprod.inl : P →* R).comp (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β))) := by
      refine FreeGroup.ext_hom _ _ fun b => ?_
      show ψ (PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ)))
          (FreeGroup.map Sum.inl (FreeGroup.of b))) =
        Monoid.Coprod.inl (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) (FreeGroup.of b))
      rw [FreeGroup.map.of]
      show ψ (PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ))) (FreeGroup.of (Sum.inl b))) =
        Monoid.Coprod.inl (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) (FreeGroup.of b))
      rw [show PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ))) (FreeGroup.of (Sum.inl b)) =
          PresentedGroup.of (Sum.inl b) from rfl, hψ_of]
      show θ' (Sum.inl b) =
        Monoid.Coprod.inl (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) (FreeGroup.of b))
      rw [show θ' (Sum.inl b) = Monoid.Coprod.inl (PresentedGroup.of b) from rfl]
      rfl
    intro y
    exact DFunLike.congr_fun hcomp y
  have hψ_map_inr : ∀ k : FreeGroup γ,
      ψ (PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ)))
        (FreeGroup.map (Sum.inr : γ → β ⊕ γ) k)) =
      Monoid.Coprod.inr k := by
    have hcomp : ψ.comp ((PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ)))).comp
        (FreeGroup.map (Sum.inr : γ → β ⊕ γ))) =
        (Monoid.Coprod.inr : FreeGroup γ →* R) := by
      refine FreeGroup.ext_hom _ _ fun c => ?_
      show ψ (PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ)))
          (FreeGroup.map Sum.inr (FreeGroup.of c))) = Monoid.Coprod.inr (FreeGroup.of c)
      rw [FreeGroup.map.of]
      show ψ (PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ))) (FreeGroup.of (Sum.inr c))) =
        Monoid.Coprod.inr (FreeGroup.of c)
      rw [show PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ))) (FreeGroup.of (Sum.inr c)) =
          PresentedGroup.of (Sum.inr c) from rfl, hψ_of]
      show θ' (Sum.inr c) = Monoid.Coprod.inr (FreeGroup.of c)
      rfl
    intro k
    exact DFunLike.congr_fun hcomp k
  -- the inverse map `R →* L`
  let g₁ : β → L := fun b => PresentedGroup.of (Sum.inl b)
  have hg₁ : ∀ x ∈ ({v ^ l} : Set (FreeGroup β)), FreeGroup.lift g₁ x = 1 := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hmap : FreeGroup.lift g₁ = (PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ)))).comp
        (FreeGroup.map (Sum.inl : β → β ⊕ γ)) := by
      refine FreeGroup.ext_hom _ _ fun b => ?_
      show FreeGroup.lift g₁ (FreeGroup.of b) =
        PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ))) (FreeGroup.map Sum.inl (FreeGroup.of b))
      rw [FreeGroup.lift_apply_of, FreeGroup.map.of]
      rfl
    rw [hmap, map_pow]
    have hrel : (PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ)))
        (FreeGroup.map (Sum.inl : β → β ⊕ γ) v)) ^ l = 1 := by
      have h1 := PresentedGroup.one_of_mem (rels := ({r} : Set (FreeGroup (β ⊕ γ))))
        (x := r) (Set.mem_singleton r)
      rwa [show r = (FreeGroup.map (Sum.inl : β → β ⊕ γ) v) ^ l from rfl, map_pow] at h1
    exact hrel
  let φ₁ : P →* L := PresentedGroup.toGroup (f := g₁) hg₁
  have hφ₁_of : ∀ b : β, φ₁ (PresentedGroup.of b) = PresentedGroup.of (Sum.inl b) :=
    fun b => PresentedGroup.toGroup.of _
  let φ₂ : FreeGroup γ →* L := (PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ)))).comp
    (FreeGroup.map (Sum.inr : γ → β ⊕ γ))
  have hφ₂_of : ∀ c : γ, φ₂ (FreeGroup.of c) = PresentedGroup.of (Sum.inr c) := by
    intro c
    show PresentedGroup.mk ({r} : Set (FreeGroup (β ⊕ γ))) (FreeGroup.map Sum.inr (FreeGroup.of c)) =
      PresentedGroup.of (Sum.inr c)
    rw [FreeGroup.map.of]
    rfl
  let φ : R →* L := Monoid.Coprod.lift φ₁ φ₂
  have hφ_inl : ∀ x, φ (Monoid.Coprod.inl x) = φ₁ x :=
    fun x => Monoid.Coprod.lift_apply_inl φ₁ φ₂ x
  have hφ_inr : ∀ y, φ (Monoid.Coprod.inr y) = φ₂ y :=
    fun y => Monoid.Coprod.lift_apply_inr φ₁ φ₂ y
  -- `φ ∘ ψ = id`
  have hφψ : φ.comp ψ = MonoidHom.id L := by
    refine PresentedGroup.ext fun a => ?_
    show φ (ψ (PresentedGroup.of a)) = PresentedGroup.of a
    rw [hψ_of]
    rcases a with b | c
    · show φ (θ' (Sum.inl b)) = PresentedGroup.of (Sum.inl b)
      rw [show θ' (Sum.inl b) = Monoid.Coprod.inl (PresentedGroup.of b) from rfl,
        hφ_inl, hφ₁_of]
    · show φ (θ' (Sum.inr c)) = PresentedGroup.of (Sum.inr c)
      rw [show θ' (Sum.inr c) = Monoid.Coprod.inr (FreeGroup.of c) from rfl,
        hφ_inr, hφ₂_of]
  -- `ψ ∘ φ = id`
  have hψφ : ψ.comp φ = MonoidHom.id R := by
    refine Monoid.Coprod.hom_ext ?_ ?_
    · rw [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inl, MonoidHom.id_comp]
      refine PresentedGroup.ext fun b => ?_
      show ψ (φ₁ (PresentedGroup.of b)) = Monoid.Coprod.inl (PresentedGroup.of b)
      rw [hφ₁_of, hψ_of]
      show θ' (Sum.inl b) = Monoid.Coprod.inl (PresentedGroup.of b)
      rfl
    · rw [MonoidHom.comp_assoc, Monoid.Coprod.lift_comp_inr, MonoidHom.id_comp]
      refine FreeGroup.ext_hom _ _ fun c => ?_
      show ψ (φ₂ (FreeGroup.of c)) = Monoid.Coprod.inr (FreeGroup.of c)
      rw [hφ₂_of, hψ_of]
      show θ' (Sum.inr c) = Monoid.Coprod.inr (FreeGroup.of c)
      rfl
  refine ⟨MonoidHom.toMulEquiv ψ φ hφψ hψφ, ?_, ?_⟩
  · intro y
    rw [MonoidHom.toMulEquiv_apply]
    exact hψ_map_inl y
  · intro k
    rw [MonoidHom.toMulEquiv_apply]
    exact hψ_map_inr k

end Work.OROneRel
