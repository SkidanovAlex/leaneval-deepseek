/-
# `D_θ(𝓛_Γ^T f) = 𝓛̂(D_θ f) + E1 α f` — the transfer of the `D_θ`-commutator

The corrected coercivity operator of the fix of node N2 is

  `𝓛_Γ^T = 𝓛_Γ − 𝕡(Transport) = 𝓛̂ + Corr`,   `𝓛̂ = 𝓛 − Transport`,

with `Corr α f = Γ(θ)·radA α f z` (`Transfer.Corr_eq_radA`, `Transfer.Profiles`).  Since `Corr`
is a `θ`-dependent factor `Γ(θ)` times a `θ`-independent radial profile `radA α f z`, the
`D_θ`-derivative of `𝓛_Γ^T f` splits as

  `D_θ(𝓛_Γ^T f) = D_θ(𝓛̂ f) + (D_θΓ)(θ)·radA α f z`,

and `D_θ` commutes with the clean operator `𝓛̂` exactly (`LhatCalc.Dth_Lhat`), so on the open
quadrant (`SmoothQuad`)

  `D_θ(𝓛_Γ^T f) = 𝓛̂(D_θ f) + E1 α f`,   `E1 α f z θ = sin(2θ)·Γ'(θ)·radA α f z`

— the statement proved here.  `E1` is the *only* defect of the transfer under `D_θ`, and it is
`α`-small (`|D_θΓ| ≤ 2αΓ`, `Coer1T.gammaPointwiseBnd_fts`).

## Route

The `θ`-expansion of `D_θ(𝓛_Γ^T f)` in the interior class is already available as
`Coer1T.Dth_LGammaT_eq` (`Submission/Work/FTS/CoercivityFix/Coer1T/slotGam_LGammaT.lean`),
where the two `D_θΓ`-pieces are named `T2` and `T4`:

  `D_θ(𝓛_Γ^T f) = D_θ(𝓛̂ f) + T2 α f + T4 α f`.

Thus the proof is the three-line assembly

* `D_θ(𝓛̂ f) = 𝓛̂(D_θ f)` (`LhatCalc.Dth_Lhat`);
* `T2 α f + T4 α f = E1 α f` (unfold `T2`, `T4`, `DthGam`, `C0`, `E1`, `radA` and `ring`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat
import Submission.Work.FTS.CoercivityFix.Coer1T.slotGam_LGammaT
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

set_option autoImplicit false

/-- **The `T2`/`T4` pair of `Coer1T` is the defect `E1`**: the two `D_θΓ`-terms of the
`θ`-expansion of `D_θ(𝓛_Γ^T f)` add up to `sin(2θ)·Γ'(θ)·radA α f z`. -/
theorem T2_add_T4_eq_E1 (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.T2 α f z θ + Work.Coercivity.T4 α f z θ
      = Work.FTS.CoercivityFix.Transfer.E1 α f z θ := by
  rw [Work.Coercivity.T2, Work.Coercivity.T4, Work.Coercivity.C0,
    Work.FTS.CoercivityFix.Transfer.E1_eq, Work.FTS.CoercivityFix.Transfer.radA_eq,
    Work.Coercivity.DthGam_eq]
  ring

/-- **The transfer identity for the `D_θ`-commutator**:
`D_θ(𝓛_Γ^T f) = 𝓛̂(D_θ f) + E1 α f` on the open quadrant, for a `C^∞` datum `f`
(the interior class `Work.FTS.LocData.SmoothQuad`). -/
theorem Dth_LGammaT_eq (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dth (Work.Coercivity.LGammaT α f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ
        + Work.FTS.CoercivityFix.Transfer.E1 α f z θ := by
  have h1 := Work.FTS.CoercivityFix.Coer1T.Dth_LGammaT_eq α hsm hz ⟨hθ, hθ2⟩
  have h2 := Work.FTS.CoercivityFix.LhatCalc.Dth_Lhat hsm hz hθ hθ2
  rw [h1, h2]
  linarith [T2_add_T4_eq_E1 α f z θ]

end Work.FTS.CoercivityFix.Transfer

end
