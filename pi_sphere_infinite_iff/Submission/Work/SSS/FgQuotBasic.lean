import Mathlib
import Submission.Work.SSS.baseRowDefs

/-!
# Generators of `FgQuot` and the extension of finitely generated quotients

`FgQuot B Z` (`Z/B` finitely generated, inside the lattice of submodules of an ambient module) is
characterised by the existence of a finite set `S ⊆ Z` with `Z ≤ B ⊔ span S`, and it is transitive
in `B ≤ Z ≤ W`: an extension of finitely generated modules is finitely generated.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

section

variable {R A : Type*} [CommRing R] [AddCommGroup A] [Module R A]

/-- `Z/B` is finitely generated iff `Z` is generated modulo `B` by a finite subset of `Z`. -/
theorem fgQuot_iff_generators {B Z : Submodule R A} :
    FgQuot B Z ↔ ∃ S : Set A, S.Finite ∧ S ⊆ Z ∧ Z ≤ B ⊔ Submodule.span R S := by
  constructor
  · intro h
    classical
    obtain ⟨t, htfin, ht⟩ := Submodule.fg_def.mp h
    have ht_sub' : ∀ w ∈ t, ∃ z ∈ Z, Submodule.mkQ B z = w := by
      intro w hw
      have hw' : w ∈ Z.map (Submodule.mkQ B) := by
        rw [← ht]
        exact Submodule.subset_span hw
      rwa [Submodule.mem_map] at hw'
    let z0 : A ⧸ B → A := fun w => if hw : w ∈ t then Classical.choose (ht_sub' w hw) else 0
    have hz0 : ∀ w ∈ t, Submodule.mkQ B (z0 w) = w := by
      intro w hw
      simp only [z0, dif_pos hw]
      exact (Classical.choose_spec (ht_sub' w hw)).2
    have hzZ0 : ∀ w ∈ t, z0 w ∈ Z := by
      intro w hw
      simp only [z0, dif_pos hw]
      exact (Classical.choose_spec (ht_sub' w hw)).1
    refine ⟨z0 '' t, htfin.image z0, ?_, ?_⟩
    · rintro a ⟨w, hw, rfl⟩
      exact hzZ0 w hw
    · have himg : (Submodule.mkQ B) '' (z0 '' t) = t := by
        ext w
        constructor
        · rintro ⟨a, ⟨w', hw', rfl⟩, rfl⟩
          rw [hz0 w' hw']
          exact hw'
        · intro hw
          exact ⟨z0 w, ⟨w, hw, rfl⟩, hz0 w hw⟩
      have hcomap : Submodule.comap (Submodule.mkQ B) (Submodule.span R t) =
          B ⊔ Submodule.span R (z0 '' t) := by
        have e : Submodule.span R t =
            Submodule.map (Submodule.mkQ B) (Submodule.span R (z0 '' t)) := by
          rw [Submodule.map_span, himg]
        rw [e, Submodule.comap_map_mkQ]
      intro a ha
      have h1 : a ∈ Submodule.comap (Submodule.mkQ B) (Z.map (Submodule.mkQ B)) := ⟨a, ha, rfl⟩
      rw [← ht, hcomap] at h1
      exact h1
  · rintro ⟨S, hSfin, hSsub, hle⟩
    have hmain : Z.map (Submodule.mkQ B) = Submodule.span R ((Submodule.mkQ B) '' S) := by
      apply le_antisymm
      · calc Z.map (Submodule.mkQ B) ≤ (B ⊔ Submodule.span R S).map (Submodule.mkQ B) :=
            Submodule.map_mono hle
          _ = Submodule.span R ((Submodule.mkQ B) '' S) := by
            rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_span]
      · rw [← Submodule.map_span]
        exact Submodule.map_mono (Submodule.span_le.mpr hSsub)
    show (Z.map (Submodule.mkQ B)).FG
    rw [hmain]
    exact Submodule.fg_span (hSfin.image _)

/-- Finitely generated quotients are transitive: an extension of `Z/B` by `W/Z` is `W/B`. -/
theorem FgQuot.of_le_of_le {B Z W : Submodule R A} (hZW : Z ≤ W) (h1 : FgQuot B Z)
    (h2 : FgQuot Z W) : FgQuot B W := by
  obtain ⟨S₁, hS₁fin, hS₁sub, hle₁⟩ := (fgQuot_iff_generators).mp h1
  obtain ⟨S₂, hS₂fin, hS₂sub, hle₂⟩ := (fgQuot_iff_generators).mp h2
  refine (fgQuot_iff_generators).mpr ⟨S₁ ∪ S₂, hS₁fin.union hS₂fin, ?_, ?_⟩
  · rintro a (h | h)
    exacts [hZW (hS₁sub h), hS₂sub h]
  · calc W ≤ Z ⊔ Submodule.span R S₂ := hle₂
      _ ≤ (B ⊔ Submodule.span R S₁) ⊔ Submodule.span R S₂ := sup_le_sup_right hle₁ _
      _ = B ⊔ Submodule.span R (S₁ ∪ S₂) := by rw [Submodule.span_union, sup_assoc]

end

end Work.SSS
