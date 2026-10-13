import Mathlib
import Submission.Work.WilC2.exists_equiv_fin_sum

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC5

theorem exists_fin_relabel_elim_uniform {L : FirstOrder.Language} {γ : Type*} {k : ℕ}
    (φ : L.Formula (γ ⊕ Fin k)) :
    ∃ (n : ℕ) (σ : Fin n → γ) (ψ : L.Formula (Fin n ⊕ Fin k)),
      ∀ {M : Type} [L.Structure M] (v : γ → M) (w : Fin k → M),
        ψ.Realize (Sum.elim (v ∘ σ) w) ↔ φ.Realize (Sum.elim v w) := by
  classical
  -- All variables of `φ`, plus the whole `Fin k`-block, fit into the finite set `s'`.
  set s' := φ.freeVarFinset ∪ Finset.univ.image (Sum.inr : Fin k → γ ⊕ Fin k) with hs'def
  obtain ⟨n, σ, E, hE1, hE2⟩ :=
    Work.WilC2.exists_equiv_fin_sum s' (by intro j; simp [hs'def])
  -- The construction of `n`, `σ`, `E` is purely syntactic, so it does not depend on `M`.
  refine ⟨n, σ,
    Formula.relabel E (φ.restrictFreeVar (Set.inclusion (by simp [hs'def] : ↑φ.freeVarFinset ⊆ ↑s'))),
    ?_⟩
  intro M _ v w
  rw [Formula.realize_relabel]
  refine BoundedFormula.realize_restrictFreeVar (φ := φ)
    (f := Set.inclusion (by simp [hs'def] : ↑φ.freeVarFinset ⊆ ↑s'))
    (v := (Sum.elim (v ∘ σ) w) ∘ (E : ↥s' → (Fin n ⊕ Fin k)))
    (xs := default) (Sum.elim v w) ?_
  intro a
  -- `E` sends `Sum.inl (σ i)` to `Fin n`-variable `i`, and `Sum.inr j` to `Fin k`-variable `j`;
  -- on the free variables of `φ` the two assignments therefore agree.
  change (Sum.elim (v ∘ σ) w) (E ⟨↑a, Finset.mem_union_left _ a.property⟩) = (Sum.elim v w) ↑a
  rcases hb : E ⟨↑a, Finset.mem_union_left _ a.property⟩ with i | j
  · have h3 : (E.symm (Sum.inl i)) = (⟨↑a, Finset.mem_union_left _ a.property⟩ : ↥s') :=
      (Equiv.symm_apply_eq E).mpr hb.symm
    have h4 : (↑a : γ ⊕ Fin k) = Sum.inl (σ i) :=
      (congrArg Subtype.val h3).symm.trans (hE2 i)
    simp only [h4, Sum.elim_inl, Function.comp_apply]
  · have h3 : (E.symm (Sum.inr j)) = (⟨↑a, Finset.mem_union_left _ a.property⟩ : ↥s') :=
      (Equiv.symm_apply_eq E).mpr hb.symm
    have h5 : E.symm (Sum.inr j) = ⟨Sum.inr j, by simp [hs'def]⟩ :=
      (Equiv.symm_apply_eq E).mpr (hE1 j).symm
    have h4 : (↑a : γ ⊕ Fin k) = Sum.inr j :=
      (congrArg Subtype.val h3).symm.trans (congrArg Subtype.val h5)
    simp only [h4, Sum.elim_inr]

end Work.WilC5
