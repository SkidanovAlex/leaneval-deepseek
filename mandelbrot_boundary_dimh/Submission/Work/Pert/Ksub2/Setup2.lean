import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Interfaces.Fatou
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.Engine

/-!
# `Work.Pert.Ksub2.Setup2`

The per-perturbation objects of the proof of `Work.Pert.Ksub_phi_close_v2` (see
`Ksub2/NOTES.md` §4): the pinned coordinate `Φm`, the level `nw` of a point `w` relative to the
deep strip `Dstrip M T` and the strip point `uw`.

All of the analysis happens at a *fixed* depth `M` (chosen from the datum `d`, the compact `K'`
and `Ξ`), so that the levels `nw w`, the orbit lengths and the z-plane orbit region are uniformly
bounded.
-/

namespace Work.Pert.Ksub2

open MandelDim Complex Set Metric

noncomputable section

/-- The pinning constant: `Φm = Φ + c` with `c` chosen so that `Φm (Xc d (-M)) = -M`. -/
def pinC {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (M : ℝ) (Φ : ℂ → ℂ) : ℂ :=
  -M - Φ (Xc d (((-M : ℝ)) : ℂ))

theorem pinC_pin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (M : ℝ)
    (Φ : ℂ → ℂ) :
    (fun z => Φ z + pinC d M Φ) (Xc d (((-M : ℝ)) : ℂ)) = (((-M : ℝ)) : ℂ) := by
  simp only [pinC]
  push_cast
  ring

/-- Shifting a Fatou coordinate by a constant preserves the property. -/
theorem isFatouCoordOn_add_const {F Φ : ℂ → ℂ} {Q : Set ℂ}
    (h : MandelDim.IsFatouCoordOn F Φ Q) (c : ℂ) :
    MandelDim.IsFatouCoordOn F (fun z => Φ z + c) Q := by
  refine ⟨h.1.add_const c, ?_, ?_⟩
  · intro a ha b hb hab
    exact h.2.1 ha hb (add_right_cancel hab)
  · intro z hz hFz
    show Φ (F z) + c = Φ z + c + 1
    rw [h.2.2 z hz hFz]; ring

/-- The level of `w` for the deep strip `Dstrip M T`: a nonnegative integer `n` (arbitrary when no
such `n` exists) with `w - n ∈ Dstrip M T`. -/
def nw (M T : ℝ) (w : ℂ) : ℕ := by
  classical
  exact if h : ∃ n : ℕ, w - (n : ℂ) ∈ Dstrip M T then h.choose else 0

theorem nw_spec {M T : ℝ} {w : ℂ} (h : ∃ n : ℕ, w - (n : ℂ) ∈ Dstrip M T) :
    w - (nw M T w : ℂ) ∈ Dstrip M T := by
  classical
  unfold nw
  rw [dite_eq_left h]
  exact h.choose_spec

/-- The strip point associated with `w`. -/
def uw (M T : ℝ) (w : ℂ) : ℂ := w - (nw M T w : ℂ)

theorem uw_mem_Dstrip {M T : ℝ} {w : ℂ} (h : ∃ n : ℕ, w - (n : ℂ) ∈ Dstrip M T) :
    uw M T w ∈ Dstrip M T := nw_spec h

theorem sub_nw_eq_uw (M T : ℝ) (w : ℂ) : w - (nw M T w : ℂ) = uw M T w := rfl

/-- The level is bounded by `Re w + M + 1`. -/
theorem nw_le {M T : ℝ} {w : ℂ} (h : ∃ n : ℕ, w - (n : ℂ) ∈ Dstrip M T) :
    (nw M T w : ℝ) ≤ w.re + M + 1 := by
  have hmem := nw_spec h
  obtain ⟨h1, h2, -⟩ := hmem
  have hcast : (w - (nw M T w : ℂ)).re = w.re - (nw M T w : ℝ) := by simp
  rw [hcast] at h1
  linarith

end

end Work.Pert.Ksub2
