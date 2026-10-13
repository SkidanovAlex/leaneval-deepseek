import Mathlib
import Submission.Work.WilkiesB.Defs

set_option linter.style.haveILetI false

namespace Work.WilkiesB

/-- Composing `Sum.elim z w` with the associativity reindexing
`(κ ⊕ Fin 1) ⊕ μ ≃ κ ⊕ (Fin 1 ⊕ μ)` splits the block `Fin 1 ⊕ μ` of `w` again. -/
theorem sumElim_comp_sumAssoc {κ ν μ : Type*} (z : κ → ℝ) (w : ν ⊕ μ → ℝ) :
    Sum.elim z w ∘ ⇑(Equiv.sumAssoc κ ν μ)
      = Sum.elim (Sum.elim z (w ∘ Sum.inl)) (w ∘ Sum.inr) := by
  funext q
  rcases q with (i | j) | m <;>
    simp [Equiv.sumAssoc_apply_inl_inl, Equiv.sumAssoc_apply_inl_inr, Equiv.sumAssoc_apply_inr]

/-- Projecting out the last (`Fin 1`-indexed) block of existential witnesses preserves
existential definability. This is `ExpExistI_existsBlock` in the special case of a single
witness. -/
theorem ExpExistI_projLast {κ : Type*} {X : Set ((κ ⊕ Fin 1) → ℝ)} (hX : ExpExistI X) :
    ExpExistI {z : κ → ℝ | ∃ a : ℝ, Sum.elim z (fun _ : Fin 1 => a) ∈ X} := by
  obtain ⟨μ, hμ, P, hP⟩ := hX
  letI := hμ
  refine ⟨Fin 1 ⊕ μ, inferInstance,
    MvPolynomial.rename (polyMap (Equiv.sumAssoc κ (Fin 1) μ)) P, ?_⟩
  rw [hP]
  ext z
  simp only [ExpZero]
  constructor
  · rintro ⟨a, y, hy⟩
    refine ⟨Sum.elim (fun _ : Fin 1 => a) y, ?_⟩
    rw [expEval_rename]
    have hcomp : Sum.elim z (Sum.elim (fun _ : Fin 1 => a) y)
          ∘ ⇑(Equiv.sumAssoc κ (Fin 1) μ)
        = Sum.elim (Sum.elim z (fun _ : Fin 1 => a)) y := by
      funext q
      rcases q with (i | j) | m <;>
        simp [Equiv.sumAssoc_apply_inl_inl, Equiv.sumAssoc_apply_inl_inr,
          Equiv.sumAssoc_apply_inr]
    rw [hcomp, hy]
  · rintro ⟨w, hw⟩
    rw [expEval_rename] at hw
    rw [sumElim_comp_sumAssoc] at hw
    refine ⟨w (Sum.inl 0), w ∘ Sum.inr, ?_⟩
    have hthis : (fun _ : Fin 1 => w (Sum.inl 0)) = w ∘ Sum.inl := by
      funext j; simp [Subsingleton.elim j 0]
    rw [hthis]
    exact hw

end Work.WilkiesB
