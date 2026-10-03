import Mathlib
import Submission.Work.Peluse.Ulower.StepLe.ddiSharp.Defs
import Submission.Work.Peluse.Ulower.lemma74_phase_split

namespace Work.Peluse.Ulower.StepLe.ddiSharp

/-- Splitting the mixed phase at the first coordinate: writing the triple of `Fin (σ+1)`-vectors
as `(Fin.cons c h₁, Fin.cons u h₂, Fin.cons v h₃)`, the signed `ω`-sum of `mixedPhase` reduces to
the difference of the two level-`σ` mixed phases in which the *first* coordinate is frozen
(`φ`'s first argument to `Fin.cons c ·`) and only the second argument is differenced, at `u`
(subtracted) and `v` (added). -/
theorem mixedPhase_cons {σ : ℕ}
    (φ : (Fin (σ+1) → ℤ) → (Fin (σ+1) → ℤ) → ℝ)
    (c u v : ℤ) (h₁ h₂ h₃ : Fin σ → ℤ) :
    Work.Peluse.Ulower.StepLe.mixedPhase φ (Fin.cons c h₁, Fin.cons u h₂, Fin.cons v h₃)
      = Work.Peluse.Ulower.StepLe.mixedPhase
          (fun a b => φ (Fin.cons c a) (Fin.cons v b)) (h₁, h₂, h₃)
        - Work.Peluse.Ulower.StepLe.mixedPhase
          (fun a b => φ (Fin.cons c a) (Fin.cons u b)) (h₁, h₂, h₃) := by
  rw [Work.Peluse.Ulower.StepLe.mixedPhase, Work.Peluse.Ulower.StepLe.mixedPhase,
    Work.Peluse.Ulower.StepLe.mixedPhase]
  have h :=
    Work.Peluse.Ulower.lemma74_phase_split φ (Fin.cons c h₁) (Fin.cons v h₃) (Fin.cons u h₂)
  simp only [Fin.cons_zero, Fin.cons_succ] at h ⊢
  rw [h]

end Work.Peluse.Ulower.StepLe.ddiSharp
