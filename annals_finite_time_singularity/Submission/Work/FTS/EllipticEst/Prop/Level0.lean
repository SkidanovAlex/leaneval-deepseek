/-
# `Prop.level0` — the level-`0` (`η`-weighted) estimate

Elgindi's `prop:L2` together with Steps 1–2 of `prop:H2` (Annals **194** (2021), tex 727–890),
in the weak hypothesis class `TT.EllWeakPos` of `TT/WeakDefs.lean`:

  `α⁴·HkSq α 0 (z²∂_zzΨ) + HkSq α 0 (∂_θθΨ) ≤ C·HkSq α 0 F`,   `C` universal in `α ∈ (0,1/4]`.

The three analytic inputs are supplied as separate lemmas (the paper's first-order estimates):

* `Prop.l0_first`  — `Ψ` and `Ψ/cos θ`;
* `Prop.l0_grad`   — `z ∂_zΨ`;
* `Prop.l0_second` — `∂_θθΨ` (conditional on the first two);
* `TT.weakAngularTermClean` (proved) — the angular term `∂_θ(tan θ·Ψ)`.

The assembly itself is `Prop.L0.l2eta_weak_of_pieces`, a copy (in a fresh namespace) of
`TT.l2eta_weak_of_pieces`; the copy is needed because the module `TT/l2eta_weak.lean` is above
the build guard's per-file size limit and can no longer be elaborated.

The only mismatch to bridge is that the assembly's conclusion is the *curried* form of the
hypotheses while `EllWeak0` uses the bundled `EllWeakPos`.-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.Prop.l2etaL0Asm
import Submission.Work.FTS.EllipticEst.TT.weakAngularTermClean
import Submission.Work.FTS.EllipticEst.Prop.l0_first
import Submission.Work.FTS.EllipticEst.Prop.l0_grad
import Submission.Work.FTS.EllipticEst.Prop.l0_second

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

open Work.FTS.EllipticEst.TT

/-- The level-`0` estimate of the elliptic chapter, assembled from the four first-order
inputs. -/
theorem level0 : ∃ C : ℝ, 0 < C ∧ EllWeak0 C := by
  obtain ⟨C, hC, h⟩ :=
    L0.l2eta_weak_of_pieces l0_first l0_grad
      (fun C₁ hC₁ => l0_second C₁ hC₁)
      (fun C₁ C_B h1 h2 => weakAngularTermClean C₁ C_B h1 h2)
  exact ⟨C, hC, fun α F Ψ hα hα4 hwk =>
    h α F Ψ hα hα4 hwk.eq hwk.zero hwk.pi_half hwk.orthF hwk.orthPsi hwk.smooth
      hwk.memF hwk.memA hwk.memB hwk.memZPth2⟩

end Work.FTS.EllipticEst.Prop
