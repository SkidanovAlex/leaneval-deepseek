import Mathlib

namespace Work.Prop36SW

theorem blockInjFinSigma {ι : Type} [Fintype ι] [DecidableEq ι] (t : ι → ℕ) (T : ℕ)
    (ht : ∀ s, t s ≤ T) :
    ∃ e : Fin (Fintype.card (Σ s : ι, Fin (t s))) ↪ Fin (Fintype.card (Σ s : ι, Fin T)),
      ∀ i, ((Fintype.equivFin (Σ s : ι, Fin T)).symm (e i)).1
          = ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1 := by
  -- The fibre-wise inclusion `Σ s, Fin (t s) → Σ s, Fin T`, which preserves the index.
  let φ : (Σ s : ι, Fin (t s)) → (Σ s : ι, Fin T) :=
    fun x => ⟨x.1, ⟨x.2.1, lt_of_lt_of_le x.2.2 (ht x.1)⟩⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    obtain ⟨s, a⟩ := x
    obtain ⟨s', a'⟩ := y
    have h1 : s = s' := congrArg Sigma.fst hxy
    subst h1
    have h2 : (a : ℕ) = (a' : ℕ) := by
      have := congrArg (fun z : Σ s : ι, Fin T => (z.2 : Fin T).1) hxy
      simpa [φ] using this
    have h3 : a = a' := Fin.ext h2
    subst h3
    rfl
  -- Transport through the canonical enumerations of the two sigma types.
  let E₁ : (Σ s : ι, Fin (t s)) ≃ Fin (Fintype.card (Σ s : ι, Fin (t s))) :=
    Fintype.equivFin (Σ s : ι, Fin (t s))
  let E₂ : (Σ s : ι, Fin T) ≃ Fin (Fintype.card (Σ s : ι, Fin T)) :=
    Fintype.equivFin (Σ s : ι, Fin T)
  let F : Fin (Fintype.card (Σ s : ι, Fin (t s))) → Fin (Fintype.card (Σ s : ι, Fin T)) :=
    fun i => E₂ (φ (E₁.symm i))
  have hF : Function.Injective F := by
    intro i j hij
    exact E₁.symm.injective (hφ (E₂.injective hij))
  refine ⟨⟨F, hF⟩, ?_⟩
  intro i
  change (E₂.symm (E₂ (φ (E₁.symm i)))).1 = (E₁.symm i).1
  rw [E₂.symm_apply_apply]

end Work.Prop36SW
