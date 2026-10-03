import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup

/-!
# PERT · `Work.Pert.Qm_Qp`: the two gates are translates by `1/α`

`Qm ξ α + 1/α = Qp ξ α`: the deck translation `Tt α = · - 1/α` maps the upper gate `Qp ξ α`
exactly onto the lower gate `Qm ξ α`.  This is the (A.4.2) geometry used by
`Work.Pert.gate_T_relation` (`Φm (Tt α w) = Φp w + d₁`) and by the crux's `R_equiv`/`DR` block.

Both gates are `Qreg` with vertices `(ξ - 1/α, -ξ)` resp. `(ξ, -ξ + 1/α)`; shifting `z` by `1/α`
keeps `z + 1/α - ξ` unchanged, which is exactly the first `Qreg` condition, and the second
condition `(z + ξ).re < |(z + ξ).im|` is the same for both.
-/

namespace Work.Pert

open MandelDim Complex Set

noncomputable section

private lemma mem_Qreg_some_some {z a b : ℂ} :
    z ∈ MandelDim.Qreg (some a) (some b) ↔
      (-|(z - a).im| < (z - a).re ∧ (z - b).re < |(z - b).im|) := by
  simp [MandelDim.Qreg]

/-- `z + 1/α ∈ Qp ξ α ↔ z ∈ Qm ξ α`: the exact translation relation between the two gates. -/
theorem mem_Qp_add_inv_iff {ξ : ℝ} {α z : ℂ} :
    z + 1 / α ∈ Qp ξ α ↔ z ∈ Qm ξ α := by
  rw [Qp, Qm, mem_Qreg_some_some, mem_Qreg_some_some]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h : (z + 1 / α - (ξ : ℂ)) = (z - ((ξ : ℂ) - 1 / α)) := by ring
      rw [h] at h1; exact h1
    · have h : (z + 1 / α - (-(ξ : ℂ) + 1 / α)) = (z - (-(ξ : ℂ))) := by ring
      rw [h] at h2; exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h : (z + 1 / α - (ξ : ℂ)) = (z - ((ξ : ℂ) - 1 / α)) := by ring
      rw [h]; exact h1
    · have h : (z + 1 / α - (-(ξ : ℂ) + 1 / α)) = (z - (-(ξ : ℂ))) := by ring
      rw [h]; exact h2

/-- Set form of `mem_Qp_add_inv_iff`: the upper gate is the image of the lower gate under `+1/α`. -/
theorem Qm_image_add_inv_eq_Qp (ξ : ℝ) (α : ℂ) :
    (fun z : ℂ => z + 1 / α) '' (Qm ξ α) = Qp ξ α := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_Qp_add_inv_iff.mpr hy
  · intro hz
    exact ⟨z - 1 / α, mem_Qp_add_inv_iff.mp (by simpa using hz), by ring⟩

end

end Work.Pert
