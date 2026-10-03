import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow

/-!
# `Work.Pert.pert2v2.PhiMinusDef` — the model **lower**-gate coordinate of the datum

`Work.Pert.Xc d u = τ₀ (d.φ u)` is the datum's curve (`Xc d (u+1) = F₀ (Xc d u)` with the model map
`F₀ w = τ₀ (f₀ (τ₀ w))`, `Work.Pert.Ksub2.Setup.Xc_add_one`); the datum's *lower gate* coordinate —
the paper's `Φ₋,₀` — is its inverse,

  `PhiMinus d := (Xc d)⁻¹ = d.φ⁻¹ ∘ τ₀`,

realised as `Work.Pert.invOn (Work.Pert.Xc d) d.Dφ` (junk off the image of `d.Dφ`; the statements
that use it carry the cover hypothesis explicitly).

It is the model coordinate of the *lower* gate in the sense that every perturbed coordinate
`Φm` on `Qm Ξ α` converges to it as `f → f₀` (`Work.Pert.pert2v2.gate_coord_close_minus`), and the
two model coordinates reproduce the datum's horn map: `(d.Φ ∘ τ₀) ∘ (PhiMinus d) = d.Φ ∘ d.φ = d.E`
on the waist, because `tau0 ∘ tau0 = id`.
-/

namespace Work.Pert.pert2v2

open MandelDim Complex Set

noncomputable section

/-- The **model lower-gate coordinate** `Φ̄₀ = (Xc d)⁻¹ = d.φ⁻¹ ∘ τ₀` of the datum `d`. -/
def PhiMinus {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) : ℂ → ℂ :=
  Work.Pert.invOn (Work.Pert.Xc d) d.Dφ

/-- On the image of `d.Dφ` under the curve, `PhiMinus d` is the genuine inverse. -/
theorem Xc_PhiMinus {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {v : ℂ}
    (h : ∃ u ∈ d.Dφ, Work.Pert.Xc d u = v) : Work.Pert.Xc d (PhiMinus d v) = v :=
  Work.Pert.invOn_spec h

end

end Work.Pert.pert2v2
