import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

theorem wTupZeroLemmas
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (K₁ K₂ : ℕ) (F : Fin (K₁ + K₂) → Work.Diff.EXT.TField (I := I) (M := M)) :
    ((Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ 0 Work.Diff.EXT.evolX.Word.nil F
        = fun i : Fin K₁ => F (Fin.castAdd K₂ i))
      ∧ (Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ 0 Work.Diff.EXT.evolX.Word.nil F
        = fun i : Fin K₂ => F (Fin.natAdd K₁ i))
      ∧ (∀ (ρ : Fin K₁) (v : Work.Diff.EXT.TField (I := I) (M := M)),
          Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ 0 Work.Diff.EXT.evolX.Word.nil
              (Function.update F (Fin.castAdd K₂ ρ) v)
            = Function.update (Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ 0
                Work.Diff.EXT.evolX.Word.nil F) ρ v)
      ∧ (∀ (ρ : Fin K₁) (v : Work.Diff.EXT.TField (I := I) (M := M)),
          Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ 0 Work.Diff.EXT.evolX.Word.nil
              (Function.update F (Fin.castAdd K₂ ρ) v)
            = Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ 0
                Work.Diff.EXT.evolX.Word.nil F)
      ∧ (∀ (ρ : Fin K₂) (v : Work.Diff.EXT.TField (I := I) (M := M)),
          Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ 0 Work.Diff.EXT.evolX.Word.nil
              (Function.update F (Fin.natAdd K₁ ρ) v)
            = Function.update (Work.Diff.EXT.evolX.wTupB (I := I) (M := M) K₁ K₂ 0
                Work.Diff.EXT.evolX.Word.nil F) ρ v)
      ∧ (∀ (ρ : Fin K₂) (v : Work.Diff.EXT.TField (I := I) (M := M)),
          Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ 0 Work.Diff.EXT.evolX.Word.nil
              (Function.update F (Fin.natAdd K₁ ρ) v)
            = Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ 0
                Work.Diff.EXT.evolX.Word.nil F)) := by
  -- At level `0` and with the empty word, the `A`-sub-tuple (resp. `B`-sub-tuple) of a tuple `G`
  -- is `G` re-indexed by `Fin.castAdd K₂` (resp. `Fin.natAdd K₁`).
  have hA : ∀ (G : Fin (K₁ + K₂) → Work.Diff.EXT.TField (I := I) (M := M)),
      wTupA (I := I) (M := M) K₁ K₂ 0 Word.nil G = fun i : Fin K₁ => G (Fin.castAdd K₂ i) := by
    intro G
    rw [wTupA.eq_1]
    funext i
    congr 1
  have hB : ∀ (G : Fin (K₁ + K₂) → Work.Diff.EXT.TField (I := I) (M := M)),
      wTupB (I := I) (M := M) K₁ K₂ 0 Word.nil G = fun i : Fin K₂ => G (Fin.natAdd K₁ i) := by
    intro G
    rw [wTupB.eq_1]
    funext i
    congr 1
  -- Updating `F` at a position of the form `Fin.castAdd K₂ ρ` (resp. `Fin.natAdd K₁ ρ`) is the
  -- same as updating the re-indexed tuple at `ρ`; on the other sub-tuple it is invisible.
  have keyAA : ∀ (ρ : Fin K₁) (v : Work.Diff.EXT.TField (I := I) (M := M)),
      (fun i : Fin K₁ => Function.update F (Fin.castAdd K₂ ρ) v (Fin.castAdd K₂ i))
        = Function.update (fun i : Fin K₁ => F (Fin.castAdd K₂ i)) ρ v := by
    intro ρ v
    funext i
    rw [Function.update_apply, Function.update_apply]
    by_cases h : i = ρ
    · subst h
      simp
    · rw [ite_eq_right h,
        ite_eq_right (fun hc => h (Fin.castAdd_inj.mp hc))]
  have keyAB : ∀ (ρ : Fin K₁) (v : Work.Diff.EXT.TField (I := I) (M := M)),
      (fun i : Fin K₂ => Function.update F (Fin.castAdd K₂ ρ) v (Fin.natAdd K₁ i))
        = fun i : Fin K₂ => F (Fin.natAdd K₁ i) := by
    intro ρ v
    funext i
    rw [Function.update_apply, ite_eq_right]
    intro hc
    have hv := congrArg Fin.val hc
    rw [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  have keyBB : ∀ (ρ : Fin K₂) (v : Work.Diff.EXT.TField (I := I) (M := M)),
      (fun i : Fin K₂ => Function.update F (Fin.natAdd K₁ ρ) v (Fin.natAdd K₁ i))
        = Function.update (fun i : Fin K₂ => F (Fin.natAdd K₁ i)) ρ v := by
    intro ρ v
    funext i
    rw [Function.update_apply, Function.update_apply]
    by_cases h : i = ρ
    · subst h
      simp
    · rw [ite_eq_right h,
        ite_eq_right (fun hc => h (Fin.natAdd_inj K₁ |>.mp hc))]
  have keyBA : ∀ (ρ : Fin K₂) (v : Work.Diff.EXT.TField (I := I) (M := M)),
      (fun i : Fin K₁ => Function.update F (Fin.natAdd K₁ ρ) v (Fin.castAdd K₂ i))
        = fun i : Fin K₁ => F (Fin.castAdd K₂ i) := by
    intro ρ v
    funext i
    rw [Function.update_apply, ite_eq_right]
    intro hc
    have hv := congrArg Fin.val hc
    rw [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  refine ⟨hA F, hB F, ?_, ?_, ?_, ?_⟩
  · intro ρ v
    rw [hA (Function.update F (Fin.castAdd K₂ ρ) v), hA F]
    exact keyAA ρ v
  · intro ρ v
    rw [hB (Function.update F (Fin.castAdd K₂ ρ) v), hB F]
    exact keyAB ρ v
  · intro ρ v
    rw [hB (Function.update F (Fin.natAdd K₁ ρ) v), hB F]
    exact keyBB ρ v
  · intro ρ v
    rw [hA (Function.update F (Fin.natAdd K₁ ρ) v), hA F]
    exact keyBA ρ v

end Work.Diff.EXT.evolX
