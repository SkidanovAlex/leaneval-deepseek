/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.BoxDataH.Crux` — the `C^{2,β}` Arzelà–Ascoli crux

**Theorem.**  Let `H : ℕ → ℝ → ℝ → ℝ` be a family with the uniform box data `BoxUniform2 a b H`
(the abstract form of `PkgBoxH` along a sequence: `C²` within the box, within-derivatives of order
`≤ 2` bounded by one constant `K`, second within-derivative Hölder-`β` with constant `K`), and let
`G` be the pointwise limit of the values on the box.  Then `G` is `C²` within the box.

This is the finite-order replacement of `BoxReg_of_uniform`: the latter consumes families that are
`C^∞` on a *neighbourhood* of the box and whose jets of order `≤ 3` are bounded on the box, which
`PkgBoxH` does not supply (the members are only controlled *within* the box, and only up to order
`2`, with a Hölder modulus on the second derivative).  The Hölder modulus is exactly the
equicontinuity needed for the Arzelà–Ascoli extraction of the six within-partials, and the three
staircases of `CruxCore` turn that extraction into `ContDiffOn ℝ 2`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.BoxDataH.CruxCore
import Submission.Work.FTS_EllLimOK.BoxDataH.wJet_lip
import Submission.Work.FTS_EllLimOK.BoxDataH.wJet_slice
import Submission.Work.FTS_EllLimOK.BoxDataH.wJet_subseq_extract
import Submission.Work.FTS_EllLimOK.BoxDataH.contDiffOn_two_of_fderivWithin_data

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

set_option autoImplicit false

/-- **The `C^{2,β}` Arzelà–Ascoli crux.**  A family with the uniform box data `BoxUniform2`, whose
values converge pointwise on the box to `G`, has a limit `G` which is `C²` within the box. -/
theorem contDiffOn_two_of_boxUniform2 {H : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hU : BoxUniform2 a b H)
    (hconv : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      Filter.Tendsto (fun n => H n z θ) Filter.atTop (𝓝 (G z θ))) :
    ContDiffOn ℝ 2 (Function.uncurry G) (cbox a b) := by
  obtain ⟨K, β, hβ, hsm, hb, hh⟩ := hU
  have hU' : BoxUniform2 a b H := ⟨K, β, hβ, hsm, hb, hh⟩
  -- the Lipschitz bound of the two first-order components
  have hlip : ∀ n, ∀ p ∈ cbox a b, ∀ q ∈ cbox a b,
      (|wPz (cbox a b) (Function.uncurry (H n)) p
          - wPz (cbox a b) (Function.uncurry (H n)) q| ≤ K * ‖p - q‖ ∧
        |wPth (cbox a b) (Function.uncurry (H n)) p
          - wPth (cbox a b) (Function.uncurry (H n)) q| ≤ K * ‖p - q‖) :=
    fun n p hp q hq =>
      ⟨(wJet_lip hab (hsm n) (hb n 2 (by norm_num))).1 p hp q hq,
        (wJet_lip hab (hsm n) (hb n 2 (by norm_num))).2 p hp q hq⟩
  -- the Arzelà–Ascoli extraction of the six within-partials
  obtain ⟨φ, hφ, g, hcv, hcontg⟩ := wJet_subseq_extract hab hβ hsm hb hh hlip
  -- the three staircases
  obtain ⟨hS0, hS1, hS2⟩ :=
    staircase_data_of_boxUniform2_core hab hU' hφ.tendsto_atTop hcv hcontg hconv
      (fun n => wJet_slice hab (hsm (φ n)))
  -- continuity of the limit's components
  have hcontA : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 0)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 0) (cbox a b)
    exact (continuous_apply 0).comp_continuousOn hcontg
  have hcontB : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 1)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 1) (cbox a b)
    exact (continuous_apply 1).comp_continuousOn hcontg
  have hcontA₁ : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 2)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 2) (cbox a b)
    exact (continuous_apply 2).comp_continuousOn hcontg
  have hcontA₂ : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 3)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 3) (cbox a b)
    exact (continuous_apply 3).comp_continuousOn hcontg
  have hcontB₁ : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 4)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 4) (cbox a b)
    exact (continuous_apply 4).comp_continuousOn hcontg
  have hcontB₂ : ContinuousOn (Function.uncurry (fun z θ => g (z, θ) 5)) (cbox a b) := by
    change ContinuousOn (fun p : ℝ × ℝ => g p 5) (cbox a b)
    exact (continuous_apply 5).comp_continuousOn hcontg
  exact contDiffOn_two_of_fderivWithin_data (G := G)
    (A := fun z θ => g (z, θ) 0) (B := fun z θ => g (z, θ) 1)
    (A₁ := fun z θ => g (z, θ) 2) (A₂ := fun z θ => g (z, θ) 3)
    (B₁ := fun z θ => g (z, θ) 4) (B₂ := fun z θ => g (z, θ) 5)
    hab hcontA hcontB hcontA₁ hcontA₂ hcontB₁ hcontB₂ hS0 hS1 hS2

end Work.FTS_EllLimOK.BoxDataH
