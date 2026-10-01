/-
# ZeroFreeTables — HB4_1.lean

**HB Lemma 4.1** (the maximum principle on the half-plane `Re z ≥ 0`), in the form
used by the `P₃`/`F` methods of AREA 3: if `F₁`, `F₂` are holomorphic on the right
half-plane, continuous on its closure, both decaying at infinity there, and
`Re F₁ ≥ ‖F₂‖` on the imaginary axis, then `Re F₁ ≥ ‖F₂‖` throughout.

The shared library already proves this (`Commons.Analysis.Complex.re_ge_norm_of_boundary`,
the Phragmén–Lindelöf minimum principle step of HB §2/§4); this module only
restates it in the shape in which the engine quotes it — with the axis written
`(y : ℂ) * I` instead of `I * (y : ℂ)`, differentiability on the closed half-plane
(hence a fortiori on the open one), and the explicit form of the uniform decay.
-/
import Mathlib
import Submission.Commons.Analysis.Complex.re_ge_norm_of_boundary

open Complex
noncomputable section

namespace Work.ZeroFreeTables

/-- **HB Lemma 4.1.**  `Re F₁ ≥ ‖F₂‖` on the boundary `Re z = 0`, plus uniform
decay in the half-plane, gives `Re F₁ ≥ ‖F₂‖` everywhere in the half-plane. -/
theorem hb_lemma4_1 {F1 F2 : ℂ → ℂ}
    (h1 : DifferentiableOn ℂ F1 {z : ℂ | 0 ≤ z.re})
    (h2 : DifferentiableOn ℂ F2 {z : ℂ | 0 ≤ z.re})
    (hc1 : ContinuousOn F1 {z : ℂ | 0 ≤ z.re})
    (hc2 : ContinuousOn F2 {z : ℂ | 0 ≤ z.re})
    (hbd : ∀ y : ℝ, (F1 ((y : ℂ) * I)).re ≥ ‖F2 ((y : ℂ) * I)‖)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ →
      ‖F1 z‖ < ε ∧ ‖F2 z‖ < ε) :
    ∀ z : ℂ, 0 ≤ z.re → (F1 z).re ≥ ‖F2 z‖ := by
  refine Commons.Analysis.Complex.re_ge_norm_of_boundary (h1.mono ?_) (h2.mono ?_) hc1 hc2 ?_ ?_
  · intro z hz
    exact le_of_lt (show (0 : ℝ) < z.re from hz)
  · intro z hz
    exact le_of_lt (show (0 : ℝ) < z.re from hz)
  · intro t
    have h := hbd t
    rw [mul_comm] at h
    linarith
  · intro ε hε
    obtain ⟨R, hR⟩ := hdec ε hε
    exact ⟨R, fun z hz hRz => hR.2 z hz hRz⟩

end Work.ZeroFreeTables
