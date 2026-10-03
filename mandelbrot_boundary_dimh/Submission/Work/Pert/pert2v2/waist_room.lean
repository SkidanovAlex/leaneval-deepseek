import Mathlib
import Submission.Work.Pert.pert2v2.walk_Qp_waist
import Submission.Work.Pert.RBlock4.gate_walk_Qreg
import Submission.Work.Pert.Gates
import Submission.Work.Pert.waist_low

namespace Work.Pert.pert2v2

/-- **The room at a waist point.**  For `ς ∈ Qm Ξ α ∩ Qp Ξ α` with `Ξ ≤ ς.im` and
`(1/α).im ≤ ς.im`, the room to the `b`-boundary of `Qp Ξ α` (`b := -(Ξ : ℂ) + 1/α`) — exactly what
`Work.Pert.RBlock4.gate_walk_Qreg` consumes — is at least `(1/α).re - (1/α).im`:
`(17/16) m + 1 ≤ |(ς - b).im| - (ς - b).re` whenever `(17/16) m + 1 ≤ (1/α).re - (1/α).im`.

**Both height hypotheses are needed** (two reviewers refuted the version with only the second, with
explicit counterexamples at `ς.im < 0`, e.g. `Ξ = 0`, `1/α = -3 - 4i`, `ς = -5/2 - 3i`, `m = 0`):
`Ξ ≤ ς.im` resolves `|ς.re| < |ς.im| - Ξ` (`Work.Pert.Qm_inter_Qp` / `Work.Pert.mem_waist_iff`) into
`ς.re < ς.im - Ξ`, and `(1/α).im ≤ ς.im` resolves `|ς.im - (1/α).im|`.  Then the room equals
`((1/α).re - (1/α).im) + (ς.im - Ξ - ς.re)`, whose second bracket is positive by the waist inequality.
`hΞ : 0 < Ξ` is retained only to make `Ξ ≤ ς.im` meaningful alongside `hς`.

This is the *free* half of the low `R_close` row's last obligation: with `gate_walk_Qreg` it gives the
walk clause, with no deviation bound.  (The remaining, non-free case is `ς.im < Ξ`, i.e. the negative
`|ς.im|` branch of the waist — see `HANDOFF.md`.) -/
theorem waist_room {Ξ : ℝ} {α ς : ℂ} {m : ℕ}
    (hΞ : 0 < Ξ) (hς : ς ∈ Work.Pert.Qm Ξ α ∩ Work.Pert.Qp Ξ α)
    (him : Ξ ≤ ς.im) (himα : (1 / α).im ≤ ς.im)
    (hm : (17 / 16 : ℝ) * (m : ℝ) + 1 ≤ (1 / α).re - (1 / α).im) :
    (17 / 16 : ℝ) * (m : ℝ) + 1 ≤
      |(ς - (-(Ξ : ℂ) + 1 / α)).im| - (ς - (-(Ξ : ℂ) + 1 / α)).re := by
  -- `Ξ > 0`, so `Ξ ≤ ς.im` makes `ς.im` positive.
  have himpos : 0 < ς.im := lt_of_lt_of_le hΞ him
  -- The `b₂`-condition of `Qm Ξ α` (vertex `-Ξ`) reads `ς.re + Ξ < |ς.im|`.
  have hQm : ς ∈ MandelDim.Qreg (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))) := hς.1
  have hcond : ς.re + Ξ < ς.im := by
    have h := hQm.2 (-(Ξ : ℂ)) (by simp)
    have him'' : (ς - (-(Ξ : ℂ))).im = ς.im := by
      simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im]
      ring
    have hre'' : (ς - (-(Ξ : ℂ))).re = ς.re + Ξ := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
      ring
    rw [him'', hre'', abs_of_pos himpos] at h
    linarith
  -- hence `ς.im - Ξ - ς.re > 0`.
  have hgap : 0 < ς.im - Ξ - ς.re := by linarith
  -- `(1/α).im ≤ ς.im` removes the absolute value of the imaginary part of `ς - b`.
  have him1 : (ς - (-(Ξ : ℂ) + 1 / α)).im = ς.im - (1 / α).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.neg_im, Complex.ofReal_im]
    ring
  have hre1 : (ς - (-(Ξ : ℂ) + 1 / α)).re = ς.re + Ξ - (1 / α).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    ring
  have hkey : |(ς - (-(Ξ : ℂ) + 1 / α)).im| - (ς - (-(Ξ : ℂ) + 1 / α)).re
      = ((1 / α).re - (1 / α).im) + (ς.im - Ξ - ς.re) := by
    rw [him1, hre1, abs_of_nonneg (by linarith)]
    ring
  rw [hkey]
  linarith

end Work.Pert.pert2v2
