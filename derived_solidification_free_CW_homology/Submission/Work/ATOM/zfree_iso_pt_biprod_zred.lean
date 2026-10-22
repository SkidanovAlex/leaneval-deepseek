import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ATOM

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

/-!
# `ℤ[S] ≅ ℤ[*] ⊞ ℤ̃[S]`

The augmentation `aug S = zmap (toPt S) : ℤ[S] ⟶ ℤ[*]` is a retraction of the map
`zmap (ptAt s₀) : ℤ[*] ⟶ ℤ[S]` induced by the point `s₀ ∈ S`; indeed
`toPt S ∘ ptAt s₀ = 𝟙 *`. Hence `zmap (ptAt s₀)` is a split monomorphism, and the general
splitting lemma for abelian (in fact preadditive) categories
(`CategoryTheory.biprod.uniqueUpToIso` combined with
`CategoryTheory.isBilimitBinaryBiconeOfIsSplitMonoOfCokernel`) identifies its source
`ℤ[S]` with `ℤ[*] ⊞ coker (zmap (ptAt s₀)) = ℤ[*] ⊞ ℤ̃[S]`.

No special property of light profinite sets beyond `S` being a concrete category over `Type`
and `*` being a subsingleton is used: this is the split short exact sequence
`0 → ℤ[*] --zmap (ptAt s₀)--> ℤ[S] --qred--> ℤ̃[S] → 0` of `NOTES_LEAD_solid_gaps1.md` §3.5.
-/

/-- `zmap` sends identities to identities. -/
lemma zmap_id_zfree (S : LightProfinite.{0}) : zmap (𝟙 S) = 𝟙 (zfree S) := by
  simp only [zmap]
  exact CategoryTheory.Functor.map_id _ _

/-- `zmap` is functorial. -/
lemma zmap_comp_zfree {S T U : LightProfinite.{0}} (f : S ⟶ T) (g : T ⟶ U) :
    zmap (f ≫ g) = zmap f ≫ zmap g := by
  simp only [zmap]
  exact CategoryTheory.Functor.map_comp _ _ _

/-- The point `ptAt s₀ : * ⟶ S` followed by the unique map `S ⟶ *` is the identity of `*`. -/
lemma ptAt_comp_toPt (S : LightProfinite.{0}) (s₀ : ↥S) : ptAt s₀ ≫ toPt S = 𝟙 pt := by
  apply ConcreteCategory.hom_ext
  intro x
  exact Subsingleton.elim _ _

/-- `aug = ℤ[toPt S]` is a retraction of `zmap (ptAt s₀)`. -/
lemma zmap_ptAt_comp_aug (S : LightProfinite.{0}) (s₀ : ↥S) :
    zmap (ptAt s₀) ≫ aug S = 𝟙 (zfree pt) := by
  rw [show aug S = zmap (toPt S) from rfl, ← zmap_comp_zfree, ptAt_comp_toPt, zmap_id_zfree]

/-- `zmap (ptAt s₀) : ℤ[*] ⟶ ℤ[S]` is a split monomorphism, with retraction `aug S`. -/
lemma isSplitMono_zmap_ptAt (S : LightProfinite.{0}) (s₀ : ↥S) :
    IsSplitMono (zmap (ptAt s₀)) :=
  ⟨⟨SplitMono.mk (aug S) (zmap_ptAt_comp_aug S s₀)⟩⟩

/-- **Splitting lemma.** In any preadditive category, a split monomorphism `f : X ⟶ Y` exhibits
`Y` as the biproduct of `X` and the cokernel of `f`: `Y ≅ X ⊞ coker f`. -/
lemma iso_biprod_cokernel_of_isSplitMono {X Y : LightCondAb} (f : X ⟶ Y) [IsSplitMono f] :
    Nonempty (Y ≅ X ⊞ cokernel f) := by
  have hw : f ≫ cokernel.π f = 0 := cokernel.condition f
  refine ⟨biprod.uniqueUpToIso X (cokernel f)
    (b := binaryBiconeOfIsSplitMonoOfCokernel (X := X) (Y := Y) (f := f)
      (c := CokernelCofork.ofπ (cokernel.π f) hw) (cokernelIsCokernel f)) ?_⟩
  exact isBilimitBinaryBiconeOfIsSplitMonoOfCokernel (X := X) (Y := Y) (f := f)
    (c := CokernelCofork.ofπ (cokernel.π f) hw) (cokernelIsCokernel f)

/-- `ℤ[S] ≅ ℤ[*] ⊞ ℤ̃[S]`: the short exact sequence
`0 → ℤ[*] --zmap(ptAt s₀)--> ℤ[S] --qred--> ℤ̃[S] → 0` splits, with retraction
`aug : ℤ[S] ⟶ ℤ[*]` (`NOTES_LEAD_solid_gaps1.md` §3.5, last step of the assembly). -/
theorem zfree_iso_pt_biprod_zred (S : LightProfinite.{0}) (s₀ : ↥S) :
    Nonempty (Work.ATOM.zfree S ≅ Work.ATOM.zfree Work.ATOM.pt ⊞ Work.ATOM.zred S s₀) := by
  have : IsSplitMono (zmap (ptAt s₀)) := isSplitMono_zmap_ptAt S s₀
  have hw : zmap (ptAt s₀) ≫ qred S s₀ = 0 := cokernel.condition _
  refine ⟨biprod.uniqueUpToIso (zfree pt) (zred S s₀)
    (b := binaryBiconeOfIsSplitMonoOfCokernel (X := zfree pt) (Y := zfree S)
      (f := zmap (ptAt s₀)) (c := CokernelCofork.ofπ (qred S s₀) hw)
      (cokernelIsCokernel (zmap (ptAt s₀)))) ?_⟩
  exact isBilimitBinaryBiconeOfIsSplitMonoOfCokernel (X := zfree pt) (Y := zfree S)
    (f := zmap (ptAt s₀)) (c := CokernelCofork.ofπ (qred S s₀) hw)
    (cokernelIsCokernel (zmap (ptAt s₀)))

end Work.ATOM
