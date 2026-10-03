import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.iso_coprod_of_supported_spec
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.OROneRel.relatorLetters_pow_subset
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.OROneRel.hnnExtension_iso_of_baseMulEquiv
import Submission.Work.OROneRel.exists_hnnStepCore
import Submission.Work.OROneRel.presentedGroup_sum_iso_coprod
import Submission.Work.OROneRel.hnnExtension_iso_coprod

/-!
# The Magnus step transports along an injective relabelling of the generators

`Work.OROneRel.hasMagnusStepAt_map_of_injective` says: if the root `u ∈ F(σ)` has a Magnus step
inside the one-relator group `⟨σ | u ^ l⟩` (an HNN decomposition over a strictly shorter root `v`
with the class of `u` conjugate to the image of the class of `v`), then so does the image
`FreeGroup.map f u ∈ F(α)` of `u` under an injective relabelling `f : σ → α` of the generators,
inside `⟨α | (map f u) ^ l⟩`.

The two presentations differ by the free factor `F(α ∖ range f)`: since the relator `(map f u) ^ l`
only involves the generators in `range f`, the free product decomposition
`⟨α | (map f u) ^ l⟩ ≃* (⟨σ | u ^ l⟩ ∗ F(α ∖ range f))` holds, and — the point of the proof — an
HNN extension of a base group whose relator avoids extra generators splits over the corresponding
free factor, so the HNN data of the hypothesis can be pushed into the larger generating type.  The
strict decrease of the norm survives because an injective relabelling of the generators preserves
`relatorNorm`.

## The pieces

* `not_isProperPower_map_sumInl_hmsinj` : a proper-power witness cannot appear only after adding
  unused generators (project onto the old generators).
* `supportedOn_map_range_hmsinj` : the image of a word uses only the new generators.
* `mulEquiv_coprodCongr_apply_inl_hmsinj` : the value of `MulEquiv.coprodCongr` on the first factor.
* the coproduct splitting `iso_coprod_of_supported_spec` of the target presentation, with element
  tracking (`hE''_mk` in the main proof), and the isomorphism
  `⟨σ | u ^ l⟩ ≃* ⟨range f | r''⟩` induced by the bijection `σ ≃ range f` (`Ψ` in the main proof).
-/

namespace Work.OROneRel

universe u

/-- A proper-power witness for the image of `v` under an injective relabelling can be pulled back:
if `FreeGroup.map f v = w ^ k` with `k ≥ 2` then `v = (π w) ^ k` for the projection `π` that
retracts `f`, so `v` is a proper power.  Stated for the canonical inclusion `Sum.inl`, which is the
only case needed here. -/
theorem not_isProperPower_map_sumInl_hmsinj {β γ : Type u} (v : FreeGroup β)
    (h : ¬ IsProperPower v) : ¬ IsProperPower (FreeGroup.map (Sum.inl : β → β ⊕ γ) v) := by
  intro hpow
  obtain ⟨w, k, hk, hwk⟩ := hpow
  let π : FreeGroup (β ⊕ γ) →* FreeGroup β := FreeGroup.lift (Sum.elim FreeGroup.of (fun _ => 1))
  have hπ : ∀ y : FreeGroup β, π (FreeGroup.map Sum.inl y) = y := by
    intro y
    have hcomp : π.comp (FreeGroup.map Sum.inl) = MonoidHom.id (FreeGroup β) := by
      refine FreeGroup.ext_hom _ _ fun c => ?_
      rw [MonoidHom.comp_apply, FreeGroup.map.of, MonoidHom.id_apply]
      exact FreeGroup.lift_apply_of
    rw [← MonoidHom.comp_apply, hcomp, MonoidHom.id_apply]
  exact h ⟨π w, k, hk, by rw [← hπ v, hwk, map_pow]⟩

/-- The image of a word under a relabelling of the generators uses only the new generators. -/
theorem supportedOn_map_range_hmsinj {σ α : Type u} (f : σ → α) (hf : Function.Injective f)
    (u : FreeGroup σ) : SupportedOn (FreeGroup.map f u) (Set.range f) := by
  classical
  intro a ha
  simp only [relatorLetters, Set.mem_ofPred_eq] at ha
  obtain ⟨b, hb⟩ := ha
  rw [toWord_map_of_injective f hf u] at hb
  obtain ⟨p, _, hp⟩ := List.mem_map.mp hb
  exact ⟨p.1, congrArg Prod.fst hp⟩

/-- `MulEquiv.coprodCongr` acts on the first factor as the given isomorphism. -/
theorem mulEquiv_coprodCongr_apply_inl_hmsinj {M N M' N' : Type u}
    [MulOneClass M] [MulOneClass N] [MulOneClass M'] [MulOneClass N']
    (e : M ≃* N) (e' : M' ≃* N') (x : M) :
    MulEquiv.coprodCongr e e' (Monoid.Coprod.inl x) = Monoid.Coprod.inl (e x) := by
  show Monoid.Coprod.map (e : M →* N) (e' : M' →* N') (Monoid.Coprod.inl x) = _
  rw [Monoid.Coprod.map_apply_inl]
  rfl

theorem hasMagnusStepAt_map_of_injective {σ α : Type u} (f : σ → α) (hf : Function.Injective f)
    (u : FreeGroup σ) (l : ℕ) (hl : 1 ≤ l)
    (h : ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
        Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
        ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
          (e : PresentedGroup ({u ^ l} : Set (FreeGroup σ)) ≃*
            HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
          ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
            e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup σ)) u) =
              c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm (FreeGroup.map f u) ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({(FreeGroup.map f u) ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({(FreeGroup.map f u) ^ l} : Set (FreeGroup α)) (FreeGroup.map f u)) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  classical
  obtain ⟨β, v, hpp, hlt, A, B, φ, e, c, hc⟩ := h
  -- the exponent bound `hl` is not needed by the argument (it is uniform in `l`), but it is part
  -- of the requested statement; record it so that the hypothesis is not reported as unused
  have _hl : 1 ≤ l := hl
  -- ### the range of `f`, and the bijection `σ ≃ range f`
  let Z : Set α := Set.range f
  let γ : Type u := {a : α // a ∉ Z}
  let g : σ → Z := fun s => ⟨f s, ⟨s, rfl⟩⟩
  have hg_inj : Function.Injective g := by
    intro s t hst
    exact hf (congrArg Subtype.val hst)
  have hg_surj : Function.Surjective g := by
    rintro ⟨a, s, rfl⟩
    exact ⟨s, rfl⟩
  let gE : σ ≃ Z := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  have hgE_val : ∀ s : σ, ((gE s : Z) : α) = f s := by
    intro s
    show (g s : α) = f s
    rfl
  let ρ : FreeGroup σ ≃* FreeGroup Z := FreeGroup.freeGroupCongr gE
  -- the induced isomorphism `F(σ) ≃* F(Z)` followed by the inclusion of `Z` is `FreeGroup.map f`
  have hhom : ∀ x : FreeGroup σ, FreeGroup.map (Subtype.val : Z → α) (ρ x)
      = FreeGroup.map f x := by
    intro x
    rw [show ρ x = (FreeGroup.map (gE : σ → Z)) x from
      FreeGroup.freeGroupCongr_apply gE x]
    have h2 : (FreeGroup.map (Subtype.val : Z → α)).comp (FreeGroup.map (gE : σ → Z))
        = FreeGroup.map f := by
      refine FreeGroup.ext_hom _ _ fun s => ?_
      simp only [MonoidHom.comp_apply, FreeGroup.map.of, hgE_val s]
    rw [← MonoidHom.comp_apply, h2]
  -- ### the relator of the target presentation and its support
  let r : FreeGroup α := (FreeGroup.map f u) ^ l
  have hSupp : SupportedOn r Z := by
    intro a ha
    exact supportedOn_map_range_hmsinj f hf u
      (relatorLetters_pow_subset (FreeGroup.map f u) l ha)
  -- ### the coproduct splitting of `⟨α | r⟩`, with element tracking
  obtain ⟨r'', E'', hr'', hgen_inl, _⟩ := iso_coprod_of_supported_spec r Z hSupp
  have hE''_mk : ∀ w : FreeGroup Z, E'' (PresentedGroup.mk ({r} : Set (FreeGroup α))
      (FreeGroup.map (Subtype.val : Z → α) w)) =
      Monoid.Coprod.inl (PresentedGroup.mk ({r''} : Set (FreeGroup Z)) w) := by
    have h2 : ((E''.toMonoidHom.comp ((PresentedGroup.mk ({r} : Set (FreeGroup α))).comp
          (FreeGroup.map (Subtype.val : Z → α)))) : FreeGroup Z →* _) =
        Monoid.Coprod.inl.comp (PresentedGroup.mk ({r''} : Set (FreeGroup Z))) := by
      refine FreeGroup.ext_hom _ _ fun a => ?_
      simp only [MonoidHom.comp_apply, FreeGroup.map.of]
      exact hgen_inl (a : α) a.2
    intro w
    exact congrFun (congrArg DFunLike.coe h2) w
  -- the relator over `Z` is the image of `u ^ l`
  have hrel : ρ (u ^ l) = r'' := by
    apply FreeGroup.map_injective Subtype.val_injective
    rw [hhom (u ^ l), map_pow, hr'']
  -- ### the renaming isomorphism `⟨σ | u ^ l⟩ ≃* ⟨Z | r''⟩`
  have hmap : Subgroup.map (↑ρ) (Subgroup.normalClosure ({u ^ l} : Set (FreeGroup σ))) =
      Subgroup.normalClosure ({r''} : Set (FreeGroup Z)) := by
    have h1 : Subgroup.map (↑ρ) (Subgroup.normalClosure ({u ^ l} : Set (FreeGroup σ))) =
        Subgroup.normalClosure ({ρ (u ^ l)} : Set (FreeGroup Z)) := by
      rw [Subgroup.map_normalClosure ({u ^ l} : Set (FreeGroup σ))
        (↑ρ : FreeGroup σ →* FreeGroup Z) ρ.surjective]
      simp only [Set.image_singleton]
      congr 1
    rw [h1, hrel]
  let Ψ : PresentedGroup ({u ^ l} : Set (FreeGroup σ)) ≃*
      PresentedGroup ({r''} : Set (FreeGroup Z)) := QuotientGroup.congr _ _ ρ hmap
  have hΨ : ∀ x : FreeGroup σ, Ψ (PresentedGroup.mk ({u ^ l} : Set (FreeGroup σ)) x) =
      PresentedGroup.mk ({r''} : Set (FreeGroup Z)) (ρ x) := by
    intro x
    change (QuotientGroup.congr _ _ _ hmap) (QuotientGroup.mk x) = QuotientGroup.mk _
    rw [QuotientGroup.congr_mk]
  -- ### the two structural isomorphisms
  -- (i) the new base group splits off the added free factor
  obtain ⟨E₁, hE₁_inl, hE₁_inr⟩ := presentedGroup_sum_iso_coprod (β := β) (γ := γ) v l
  -- (ii) an HNN extension of a free product splits off the second factor
  obtain ⟨A₃, B₃, φ₃, E₃, hE₃_inl, hE₃_inr, hE₃_t⟩ :=
    hnnExtension_iso_coprod (K := FreeGroup γ) A B φ
  obtain ⟨A₄, B₄, φ₄, E₄, -, -, hE₄_of, hE₄_t⟩ :=
    hnnExtension_iso_of_baseMulEquiv E₁.symm A₃ B₃ φ₃
  -- ### the assembled isomorphism
  let J : PresentedGroup ({r} : Set (FreeGroup α)) ≃*
      Monoid.Coprod (PresentedGroup ({u ^ l} : Set (FreeGroup σ))) (FreeGroup γ) :=
    E''.trans (MulEquiv.coprodCongr Ψ.symm (MulEquiv.refl (FreeGroup γ)))
  let J₁ : PresentedGroup ({r} : Set (FreeGroup α)) ≃*
      Monoid.Coprod (HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ)
        (FreeGroup γ) :=
    J.trans (MulEquiv.coprodCongr e (MulEquiv.refl (FreeGroup γ)))
  let E₂ : HNNExtension (PresentedGroup ({(FreeGroup.map (Sum.inl : β → β ⊕ γ) v) ^ l} :
        Set (FreeGroup (β ⊕ γ)))) A₄ B₄ φ₄ ≃*
      Monoid.Coprod (HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ)
        (FreeGroup γ) :=
    E₄.symm.trans E₃
  let e' : PresentedGroup ({r} : Set (FreeGroup α)) ≃*
      HNNExtension (PresentedGroup ({(FreeGroup.map (Sum.inl : β → β ⊕ γ) v) ^ l} :
        Set (FreeGroup (β ⊕ γ)))) A₄ B₄ φ₄ :=
    J₁.trans E₂.symm
  -- ### the image of the class of `u` is the class of `v'`
  have hJ : J (PresentedGroup.mk ({r} : Set (FreeGroup α)) (FreeGroup.map f u)) =
      Monoid.Coprod.inl (PresentedGroup.mk ({u ^ l} : Set (FreeGroup σ)) u) := by
    rw [← hhom u]
    show (MulEquiv.coprodCongr Ψ.symm (MulEquiv.refl (FreeGroup γ)))
        (E'' (PresentedGroup.mk ({r} : Set (FreeGroup α))
          (FreeGroup.map (Subtype.val : Z → α) (ρ u)))) = _
    rw [hE''_mk (ρ u)]
    show (MulEquiv.coprodCongr Ψ.symm (MulEquiv.refl (FreeGroup γ)))
        (Monoid.Coprod.inl (PresentedGroup.mk ({r''} : Set (FreeGroup Z)) (ρ u))) = _
    rw [mulEquiv_coprodCongr_apply_inl_hmsinj]
    congr 1
    rw [← hΨ u, MulEquiv.symm_apply_apply]
  have hJ₁ : J₁ (PresentedGroup.mk ({r} : Set (FreeGroup α)) (FreeGroup.map f u)) =
      Monoid.Coprod.inl (e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup σ)) u)) := by
    show (MulEquiv.coprodCongr e (MulEquiv.refl (FreeGroup γ)))
        (J (PresentedGroup.mk ({r} : Set (FreeGroup α)) (FreeGroup.map f u))) = _
    rw [hJ, mulEquiv_coprodCongr_apply_inl_hmsinj]
  have hE₁_symm_inl : ∀ y : FreeGroup β,
      E₁.symm (Monoid.Coprod.inl (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) y)) =
        PresentedGroup.mk ({(FreeGroup.map (Sum.inl : β → β ⊕ γ) v) ^ l} :
            Set (FreeGroup (β ⊕ γ)))
          (FreeGroup.map (Sum.inl : β → β ⊕ γ) y) := by
    intro y
    rw [← hE₁_inl y, MulEquiv.symm_apply_apply]
  have hE₃_symm_inl : ∀ y : PresentedGroup ({v ^ l} : Set (FreeGroup β)),
      E₃.symm (Monoid.Coprod.inl (HNNExtension.of y)) =
        HNNExtension.of (Monoid.Coprod.inl y) := by
    intro y
    rw [← hE₃_inl y, MulEquiv.symm_apply_apply]
  have hkey : E₂.symm (Monoid.Coprod.inl
        (HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v))) =
      HNNExtension.of (PresentedGroup.mk
        ({(FreeGroup.map (Sum.inl : β → β ⊕ γ) v) ^ l} : Set (FreeGroup (β ⊕ γ)))
        (FreeGroup.map (Sum.inl : β → β ⊕ γ) v)) := by
    show E₄ (E₃.symm (Monoid.Coprod.inl
      (HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v)))) = _
    rw [hE₃_symm_inl, hE₄_of, hE₁_symm_inl]
  -- ### conclusion
  refine ⟨β ⊕ γ, FreeGroup.map (Sum.inl : β → β ⊕ γ) v,
    not_isProperPower_map_sumInl_hmsinj v hpp, ?_,
    A₄, B₄, φ₄, e', E₂.symm (Monoid.Coprod.inl c), ?_⟩
  · rw [relatorNorm_map_of_injective Sum.inl_injective v,
      relatorNorm_map_of_injective hf u]
    exact hlt
  · show e' (PresentedGroup.mk ({r} : Set (FreeGroup α)) (FreeGroup.map f u)) = _
    rw [show e' (PresentedGroup.mk ({r} : Set (FreeGroup α)) (FreeGroup.map f u)) =
        E₂.symm (J₁ (PresentedGroup.mk ({r} : Set (FreeGroup α)) (FreeGroup.map f u)))
        from rfl]
    rw [hJ₁, hc]
    simp only [map_mul, map_inv, hkey]

end Work.OROneRel
