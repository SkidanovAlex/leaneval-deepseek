import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.ORReductions.Basic
import Submission.Work.ORReductions.FreeGroupGens.freeGens_exists_injective_lift
import Submission.Work.ORReductions.FreeGroupGens.freeGens_mem_range_map_iff
import Submission.Work.ORReductions.FreeGroupGens.freeGens_mem_closure_iff
import Submission.Work.ORReductions.PresentedGroup.presentedGroup_single_equiv
import Submission.Work.ORReductions.OneRelator.supported_freeFactor_alt

/-!
# Free factors of one-relator groups (assembly, own copy)

Same statement as `Work.ORReductions.OneRelator.oneRelator_freeFactor`, assembled against the
locally requested leaf `supported_freeFactor_alt`.  Kept separate so that the final reduction
`coherent_of_oneRelator_of_fg` has a dependency closure under our own control.
-/

namespace Work.ORReductions.OneRelator

open Work.ORReductions.FreeGroupGens

/-- If `H` contains the image of every generator in `Z`, then `H` contains the image of every word
supported on `Z`. -/
lemma mem_of_gens_subset_alt {α : Type*} (r : FreeGroup α) (Z : Set α)
    (H : Subgroup (PresentedGroup ({r} : Set (FreeGroup α))))
    (hH : ∀ a : Z, PresentedGroup.of (a : α) ∈ H) (x : FreeGroup α)
    (hx : FreeGroup.gens x ⊆ Z) :
    PresentedGroup.mk ({r} : Set (FreeGroup α)) x ∈ H := by
  classical
  have hxcl : x ∈ Subgroup.closure (FreeGroup.of '' Z) :=
    (freeGens_mem_closure_iff x).mpr hx
  have h1 : PresentedGroup.mk ({r} : Set (FreeGroup α)) x ∈
      Subgroup.map (PresentedGroup.mk ({r} : Set (FreeGroup α)))
        (Subgroup.closure (FreeGroup.of '' Z)) :=
    Subgroup.mem_map.mpr ⟨x, hxcl, rfl⟩
  rw [MonoidHom.map_closure] at h1
  have hsub : Subgroup.closure
      (PresentedGroup.mk ({r} : Set (FreeGroup α)) '' (FreeGroup.of '' Z)) ≤ H := by
    rw [Subgroup.closure_le H]
    rintro y ⟨w, ⟨a, ha, rfl⟩, rfl⟩
    exact hH ⟨a, ha⟩
  exact hsub h1

/-- The free generators occurring in `FreeGroup.map φ y` all lie in the image of `φ`. -/
lemma gens_map_subset_alt {ι α : Type*} (φ : ι → α) (y : FreeGroup ι) :
    FreeGroup.gens (FreeGroup.map φ y) ⊆ Set.range φ := by
  classical
  have hy : y ∈ Subgroup.closure (FreeGroup.of '' (Set.univ : Set ι)) :=
    (freeGens_mem_closure_iff y).mpr (Set.subset_univ _)
  have h1 : FreeGroup.map φ y ∈
      Subgroup.map (FreeGroup.map φ)
        (Subgroup.closure (FreeGroup.of '' (Set.univ : Set ι))) :=
    Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  rw [MonoidHom.map_closure] at h1
  have hsub : (FreeGroup.map φ '' (FreeGroup.of '' (Set.univ : Set ι))) ⊆
      (FreeGroup.of '' Set.range φ) := by
    rintro z ⟨w, ⟨i, -, rfl⟩, rfl⟩
    rw [FreeGroup.map.of]
    exact ⟨φ i, ⟨i, rfl⟩, rfl⟩
  exact (freeGens_mem_closure_iff _).mp (Subgroup.closure_mono hsub h1)

/-- The abstract reduction: a finite set of words in `FreeGroup α` is carried by the one-relator
factor of a free-factor decomposition of `⟨α | r⟩`. -/
theorem presentedGroup_freeFactor_alt {α : Type*} (r : FreeGroup α) (X : Finset (FreeGroup α)) :
    ∃ (n : ℕ) (r₀ : FreeGroup (Fin n))
      (H T : Subgroup (PresentedGroup ({r} : Set (FreeGroup α)))),
      (∀ x ∈ X, PresentedGroup.mk ({r} : Set (FreeGroup α)) x ∈ H) ∧
      Nonempty (PresentedGroup ({r₀} : Set (FreeGroup (Fin n))) ≃* H) ∧
      Nonempty (PresentedGroup ({r} : Set (FreeGroup α)) ≃* Monoid.Coprod H T) := by
  classical
  obtain ⟨n, φ, hφinj, hφgen⟩ := freeGens_exists_injective_lift (insert r X)
  have hgens : ∀ y ∈ insert r X, FreeGroup.gens y ⊆ Set.range φ := by
    intro y hy
    obtain ⟨z, hz⟩ := hφgen y hy
    rw [← hz]
    exact gens_map_subset_alt φ z
  have hsupp : Work.OROneRel.SupportedOn r (Set.range φ) := by
    intro a ha
    simp only [Work.OROneRel.relatorLetters] at ha
    obtain ⟨b, hb⟩ := ha
    refine hgens r (Finset.mem_insert_self r X) ?_
    rw [mem_gens_iff]
    cases b
    · exact Or.inr hb
    · exact Or.inl hb
  obtain ⟨r', H, T, hHgen, hisoH, hisoP⟩ :=
    supported_freeFactor_alt r (Set.range φ) hsupp
  let ζ : ↥(Set.range φ) ≃ Fin n := (Equiv.ofInjective φ hφinj).symm
  refine ⟨n, FreeGroup.map (⇑ζ) r', H, T, ?_, ?_, hisoP⟩
  · intro x hx
    exact mem_of_gens_subset_alt r (Set.range φ) H hHgen x (hgens x (Finset.mem_insert_of_mem hx))
  · obtain ⟨iso⟩ := hisoH
    obtain ⟨h⟩ := Work.ORReductions.PresentedGroup.presentedGroup_single_equiv r' ζ
    exact ⟨h.symm.trans iso⟩

/-- **A finite subset of a one-relator group lies in a one-relator free factor.** -/
theorem oneRelator_freeFactor_alt (G : Type*) [Group G] (hG : Group.OneRelator G) (s : Finset G) :
    ∃ (n : ℕ) (r : FreeGroup (Fin n)) (H T : Subgroup G), (s : Set G) ⊆ (H : Set G) ∧
      Nonempty (PresentedGroup {r} ≃* H) ∧ Nonempty (G ≃* Monoid.Coprod H T) := by
  classical
  obtain ⟨α, rel, ⟨e⟩⟩ := hG
  have hsurj : ∀ g : G, ∃ w : FreeGroup α,
      PresentedGroup.mk ({rel} : Set (FreeGroup α)) w = e.symm g :=
    fun g => PresentedGroup.mk_surjective _ (e.symm g)
  let wfun : G → FreeGroup α := fun g => Classical.choose (hsurj g)
  have hwfun : ∀ g : G,
      PresentedGroup.mk ({rel} : Set (FreeGroup α)) (wfun g) = e.symm g :=
    fun g => Classical.choose_spec (hsurj g)
  let X : Finset (FreeGroup α) := insert rel (s.image wfun)
  obtain ⟨n, r₀, H, T, hHmem, ⟨hiso⟩, ⟨hcop⟩⟩ := presentedGroup_freeFactor_alt rel X
  refine ⟨n, r₀, Subgroup.map e.toMonoidHom H, Subgroup.map e.toMonoidHom T, ?_, ?_, ?_⟩
  · rintro g hg
    refine Subgroup.mem_map.mpr ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    have hmem : wfun g ∈ X :=
      Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨g, hg, rfl⟩))
    have h := hHmem (wfun g) hmem
    rwa [hwfun g] at h
  · exact ⟨hiso.trans (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective)⟩
  · exact ⟨e.symm.trans (hcop.trans (MulEquiv.coprodCongr
      (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective)
      (Subgroup.equivMapOfInjective T e.toMonoidHom e.injective)))⟩

end Work.ORReductions.OneRelator
