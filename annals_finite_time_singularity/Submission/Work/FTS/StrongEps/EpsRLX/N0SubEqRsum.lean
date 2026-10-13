import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The telescoping identity of the `N₀`-difference.**

On the open quadrant `Qd`, the difference `N₀ α (F_*+W₁) W₁ − N₀ α (F_*+W₂) W₂` telescopes
exactly into the right-nested sum `Rsum α W₁ W₂ (W₁ − W₂) = P1 + (P2 + (P3 + (P4 + (P5 + (P6 +
(P7 + (P8 + P9)))))))` of the nine difference pieces `Work.FTS.GalFields.RHS.P1 … P9`
(`Submission/Work/FTS/GalFields/RHS/sharpN0_defs.lean`), where with `h := W₁ − W₂`:
`P1 = (1/α)·(L₁₂ W₁·h)`, `P2 = (1/α)·(L₁₂ h·W₂)`, `P3 = (3/2α)·(D_θF_*·L₁₂ h)`,
`P4 = (3/2α)·(L₁₂ W₁·D_θh)`, `P5 = (3/2α)·(L₁₂ h·D_θW₂)`, `P6 = -c2m·(D_zF_*·L₁₂ h)`,
`P7 = -c2m·(L₁₂ W₁·D_zh)`, `P8 = -c2m·(L₁₂ h·D_zW₂)`, `P9 = -(c2m·L₁₂F_*)·D_zh`.

Route (this is a pure algebraic identity; no estimates are needed):
* split each `N₀` with `Work.FTS.StrongEps.ClassCRHS.N0_split_open_aux hα hsm z θ hzθ` into
  `N0fix + (N03g + (N04aF + (N04bF + (N05aF + (N05bF + N06F)))))`;
* the six telescoping identities, all on `Qd`,
  `N03g α W₁ = N03g α W₂ + (P1 α W₁ h + P2 α W₂ h)`, `N04aF α W₁ = N04aF α W₂ + P3 α h`,
  `N04bF α W₁ = N04bF α W₂ + (P4 α W₁ h + P5 α W₂ h)`, `N05aF α W₁ = N05aF α W₂ + P6 α h`,
  `N05bF α W₁ = N05bF α W₂ + (P7 α W₁ h + P8 α W₂ h)`, `N06F α W₁ = N06F α W₂ + P9 α h`
  (copy the proofs from `Submission/Work/FTS/GalFields/RHS/sharp_N0_diff.lean`, `h3`, `h4a`,
  `h4b`, `h5a`, `h5b`, `h6`, or the same block in `SharpMod/N0_L12_diff.lean`; they only use
  `unfold`, `simp only`, `rw` and `ring`);
* the linearity inputs: `Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen` (needs `SmoothOpen`
  and `HkMem α 4` of both, and `z ≥ 0`), `pz_add_of_smoothOpen`, `pth_add_of_smoothOpen`
  (need only `SmoothOpen` and the pointwise decomposition `W₁ = W₂ + h`);
* finish with `simp only [Rsum, Pi.add_apply]` and `ring`. -/
theorem N0SubEqRsum {α : ℝ} (hα : 0 < α) {W₁ W₂ : Work.FTS.Galerkin.Fn}
    (hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁)
    (hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂)
    (hm₁ : Work.Spaces.HkMem α 4 W₁) (hm₂ : Work.Spaces.HkMem α 4 W₂) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
        - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ
      = Work.FTS.GalFields.RHS.Rsum α W₁ W₂ (fun z θ => W₁ z θ - W₂ z θ) z θ := by
  intro z θ hzθ
  have hz : 0 < z := hzθ.1
  have hθ0 : 0 < θ := hzθ.2.1
  have hθ1 : θ < π / 2 := hzθ.2.2
  set h : ℝ → ℝ → ℝ := fun z θ => W₁ z θ - W₂ z θ with hhdef
  have hsmh : Work.FTS.EllipticEst.SmoothOpen h := by
    rw [hhdef]
    exact Work.FTS.EllipticEst.smoothOpen_sub hsm₁ hsm₂
  have hgh : ∀ z' θ' : ℝ, W₁ z' θ' = W₂ z' θ' + h z' θ' := by
    intro z' θ'
    rw [hhdef]
    ring
  have hLadd : Work.Construction.L12 W₁ z
      = Work.Construction.L12 W₂ z + Work.Construction.L12 h z := by
    have hhfun : (fun z θ => W₁ z θ - W₂ z θ) = h := by rw [hhdef]
    have hsub := Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen hsm₁ hsm₂ hm₁ hm₂ z
      (le_of_lt hz)
    rw [hhfun] at hsub
    linarith
  have hpzadd : Work.Spaces.pz W₁ z θ
      = Work.Spaces.pz W₂ z θ + Work.Spaces.pz h z θ :=
    Work.FTS.GalFields.RHS.pz_add_of_smoothOpen hsm₂ hsmh hgh z θ hz hθ0 hθ1
  have hpthadd : Work.Spaces.pth W₁ z θ
      = Work.Spaces.pth W₂ z θ + Work.Spaces.pth h z θ :=
    Work.FTS.GalFields.RHS.pth_add_of_smoothOpen hsm₂ hsmh hgh z θ hz hθ0 hθ1
  have h3 : Work.FTS.Nonlin.N03g α W₁ z θ
      = Work.FTS.Nonlin.N03g α W₂ z θ
        + (Work.FTS.GalFields.RHS.P1 α W₁ h z θ + Work.FTS.GalFields.RHS.P2 α W₂ h z θ) := by
    unfold Work.FTS.GalFields.RHS.P1 Work.FTS.GalFields.RHS.P2
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    rw [hgh z θ, hLadd]
    ring
  have h4a : Work.FTS.Nonlin.N04aF α W₁ z θ
      = Work.FTS.Nonlin.N04aF α W₂ z θ + Work.FTS.GalFields.RHS.P3 α h z θ := by
    unfold Work.FTS.GalFields.RHS.P3
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Construction.s2,
      Work.Spaces.Dth]
    rw [hLadd]
    ring
  have h4b : Work.FTS.Nonlin.N04bF α W₁ z θ
      = Work.FTS.Nonlin.N04bF α W₂ z θ
        + (Work.FTS.GalFields.RHS.P4 α W₁ h z θ + Work.FTS.GalFields.RHS.P5 α W₂ h z θ) := by
    unfold Work.FTS.GalFields.RHS.P4 Work.FTS.GalFields.RHS.P5
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.s2,
      Work.Spaces.Dth]
    rw [hpthadd, hLadd]
    ring
  have h5a : Work.FTS.Nonlin.N05aF α W₁ z θ
      = Work.FTS.Nonlin.N05aF α W₂ z θ + Work.FTS.GalFields.RHS.P6 α h z θ := by
    unfold Work.FTS.GalFields.RHS.P6
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
    rw [hLadd]
    ring
  have h5b : Work.FTS.Nonlin.N05bF α W₁ z θ
      = Work.FTS.Nonlin.N05bF α W₂ z θ
        + (Work.FTS.GalFields.RHS.P7 α W₁ h z θ + Work.FTS.GalFields.RHS.P8 α W₂ h z θ) := by
    unfold Work.FTS.GalFields.RHS.P7 Work.FTS.GalFields.RHS.P8
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b, Work.Spaces.Dz]
    rw [hLadd, hpzadd]
    ring
  have h6 : Work.FTS.Nonlin.N06F α W₁ z θ
      = Work.FTS.Nonlin.N06F α W₂ z θ + Work.FTS.GalFields.RHS.P9 α h z θ := by
    unfold Work.FTS.GalFields.RHS.P9
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06, Work.Spaces.Dz]
    rw [hpzadd]
    ring
  rw [Work.FTS.StrongEps.ClassCRHS.N0_split_open_aux hα hsm₁ z θ hzθ,
    Work.FTS.StrongEps.ClassCRHS.N0_split_open_aux hα hsm₂ z θ hzθ]
  rw [h3, h4a, h4b, h5a, h5b, h6]
  simp only [Work.FTS.GalFields.RHS.Rsum, Pi.add_apply]
  ring

end Work.FTS.StrongEps.EpsRLX
