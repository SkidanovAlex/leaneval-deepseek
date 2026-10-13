import Mathlib

namespace Work.WilC2

/-- Enumerating a finite set `s ⊆ γ ⊕ Fin k` that contains all of the `Sum.inr j`:
`s` splits as the disjoint union of the `k` elements `Sum.inr j` and `n` elements of the
form `Sum.inl (σ i)`. -/
theorem exists_equiv_fin_sum {γ : Type*} {k : ℕ} (s : Finset (γ ⊕ Fin k))
    (hs : ∀ j : Fin k, Sum.inr j ∈ s) :
    ∃ (n : ℕ) (σ : Fin n → γ) (E : ↥s ≃ (Fin n ⊕ Fin k)),
      (∀ j : Fin k, E ⟨Sum.inr j, hs j⟩ = Sum.inr j) ∧
      (∀ i : Fin n, (E.symm (Sum.inl i)).val = Sum.inl (σ i)) := by
  classical
  -- The `γ`-values occurring on the left of `s`.
  let LI : γ → γ ⊕ Fin k := fun a => Sum.inl a
  let hf : Set.InjOn LI (LI ⁻¹' (↑s : Set (γ ⊕ Fin k))) := by
    intro a _ b _ hab
    exact Sum.inl.inj hab
  let L : Finset γ := s.preimage LI hf
  have hLmem : ∀ a : γ, a ∈ L ↔ Sum.inl a ∈ s := fun a => Finset.mem_preimage
  let n : ℕ := L.card
  let eL : ↥L ≃ Fin n := L.equivFin
  let σ : Fin n → γ := fun i => (eL.symm i).val
  have hσmem : ∀ i : Fin n, Sum.inl (σ i) ∈ s := by
    intro i
    have hmem : (eL.symm i).val ∈ L := (eL.symm i).2
    simpa only [σ] using (hLmem ((eL.symm i).val)).mp hmem
  let h : (Fin n ⊕ Fin k) → ↥s :=
    Sum.elim (fun i => ⟨Sum.inl (σ i), hσmem i⟩) (fun j => ⟨Sum.inr j, hs j⟩)
  have hinj : Function.Injective h := by
    intro y y' hyy
    rcases y with i | j <;> rcases y' with i' | j'
    · have hσ : σ i = σ i' := by
        have hval : (Sum.inl (σ i) : γ ⊕ Fin k) = Sum.inl (σ i') := by
          have := congrArg Subtype.val hyy
          simpa only [h, Sum.elim_inl] using this
        exact Sum.inl.inj hval
      have : i = i' := by
        have h2 : eL.symm i = eL.symm i' := Subtype.ext (by simpa only [σ] using hσ)
        exact eL.symm.injective h2
      rw [this]
    · have hval : (Sum.inl (σ i) : γ ⊕ Fin k) = Sum.inr j' := by
        have := congrArg Subtype.val hyy
        simpa only [h, Sum.elim_inl, Sum.elim_inr] using this
      exact absurd hval Sum.inl_ne_inr
    · have hval : (Sum.inr j : γ ⊕ Fin k) = Sum.inl (σ i') := by
        have := congrArg Subtype.val hyy
        simpa only [h, Sum.elim_inl, Sum.elim_inr] using this
      exact absurd hval Sum.inr_ne_inl
    · have hval : (Sum.inr j : γ ⊕ Fin k) = Sum.inr j' := by
        have := congrArg Subtype.val hyy
        simpa only [h, Sum.elim_inr] using this
      have : j = j' := Sum.inr.inj hval
      rw [this]
  have hsurj : Function.Surjective h := by
    intro x
    rcases x with ⟨v, hv⟩
    rcases v with a | j
    · have ha : a ∈ L := (hLmem a).mpr hv
      refine ⟨Sum.inl (eL ⟨a, ha⟩), ?_⟩
      have hσa : σ (eL ⟨a, ha⟩) = a := by
        show (eL.symm (eL ⟨a, ha⟩)).val = a
        rw [Equiv.symm_apply_apply]
      show h (Sum.inl (eL ⟨a, ha⟩)) = ⟨Sum.inl a, hv⟩
      simp only [h, Sum.elim_inl, hσa]
    · refine ⟨Sum.inr j, ?_⟩
      show h (Sum.inr j) = ⟨Sum.inr j, hv⟩
      simp only [h, Sum.elim_inr]
  let F : (Fin n ⊕ Fin k) ≃ ↥s := Equiv.ofBijective h ⟨hinj, hsurj⟩
  refine ⟨n, σ, F.symm, ?_, ?_⟩
  · intro j
    have hF : F (Sum.inr j) = ⟨Sum.inr j, hs j⟩ := by
      show h (Sum.inr j) = ⟨Sum.inr j, hs j⟩
      simp only [h, Sum.elim_inr]
    rw [← hF]
    exact Equiv.symm_apply_apply F (Sum.inr j)
  · intro i
    show (F.symm.symm (Sum.inl i)).val = Sum.inl (σ i)
    show (h (Sum.inl i)).val = Sum.inl (σ i)
    simp only [h, Sum.elim_inl]

end Work.WilC2
