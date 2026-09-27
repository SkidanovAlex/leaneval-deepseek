import Mathlib
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.HeteroGerm
import Submission.Work.EQ.HeteroChain
import Submission.Work.EQ.fan_base
import Submission.Work.EQ.fwdC_germC

/-! ## The backward branch map `R` and its action on the unstable germ -/

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-- The mirror is an involution. -/
theorem eqMirror_eqMirror_hr (P : ℂ × ℂ) : eqMirror (eqMirror P) = P := by
  ext <;> simp [eqMirror]

/-- `R = eqMirror ∘ fwdC ∘ eqMirror` on the level of the principal branches. -/
theorem invBranch_eq_mirror_fwdC {a : ℝ} (Q : ℂ × ℂ) :
    invBranch a true Q = eqMirror (fwdC a (eqMirror Q)) := by
  rw [fwdC_mirror, eqMirror_eqMirror_hr]

/-- **The backward branch on the unstable germ.**  Near the origin, `invBranch a true` sends the
unstable germ with parameter `w` to the unstable germ with parameter `λ w`.  This follows from the
identity `fwdC (germC u) = germC (λ u)` (the delegated lemma `fwdC_germC`) by conjugating with the
mirror. -/
theorem invBranch_ugermC {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ} {Γ : ℝ → ℂ}
    (hh : IsStableGerm a h r) (hΓ : IsHeteroclinic a h r Γ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w ∈ Metric.ball (0 : ℂ) ρ,
      invBranch a true (ugermC a h w) = ugermC a h ((eqLam a : ℂ) * w) := by
  obtain ⟨ρf, hρf, hf⟩ := fwdC_germC ha0 ha1 hh hΓ
  refine ⟨ρf, hρf, fun w hw => ?_⟩
  have h1 : ugermC a h w = eqMirror (germC a h w) := rfl
  rw [invBranch_eq_mirror_fwdC, h1, eqMirror_eqMirror_hr, hf w hw]
  rfl

end

end Work.EQ
