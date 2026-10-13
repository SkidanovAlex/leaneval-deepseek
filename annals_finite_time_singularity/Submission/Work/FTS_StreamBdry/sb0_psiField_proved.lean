import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.SB0.sb0_psiField

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sb0_psiField_proved` — the frozen SB0 producer `StreamBdryIface.sb0_psiField`

The gauge summand of `slice (PsiCan Φs E g) τ` (`SB1′`) and the jump-sheet extension contribute
nothing to `Cyl.psiField` on `Uax` (`x₂ ≠ 0`, `r ≠ 0`): the gauge part gives the potential-flow
profile `κA⁻¹B^{3/p}·sgn(z)/r`, whose `u_r = ∂_z ψ` and `u_z = -ψ/r - ∂_r ψ` both vanish there.
Consequently the firing family `psiFire` and the `U`-slot family `psiHatP` induce the same meridian
velocity field on `Uax` — the replacement for the (false) P3 function equality `merPsi_dict`.

Proved by `Work.FTS_StreamBdry.SB0.sb0_psiField` (with support `sb0_psiFieldAdd`,
`sb0_psiFieldJump`, `sb0_hsm_psiHatP`, `sb0_gauge_alg`).
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

set_option autoImplicit false

/-- **SB0 proved** (frozen type `sb0_psiField`). -/
theorem sb0_psiField_proved {a : ℝ} (ha : 0 < a) {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {A B : ℝ → ℝ} {C : Work.FTS.Physical.PhysClock}
    (hC3 : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 3
      (fun q : ℝ × ℝ => Work.FTS.Nonlin.PsiCan Φs E g q.1 q.2 τ) Work.Construction.Qd)
    (hdec : ∀ τ : ℝ, 0 ≤ τ → ∃ κ : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ z θ
        = Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
            (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ) z θ
          + κ * Work.FTS.StreamBdryIface.gaugeMode (Work.FTS.Regularity.pExp a) z θ)
    (hPsm : ∀ τ : ℝ, 0 ≤ τ → ContDiffOn ℝ 2
      (Function.uncurry (Work.FTS.StreamBdryIface.oddPerS
        (Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
          (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)))
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ) :
    ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Work.FTS.BSIdent.Uax,
      Work.Cyl.psiField (fun r z => Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp a) A B
          (Work.FTS.FinalV2.psiFire Φs E g) C r z t) x
        = Work.Cyl.psiField (fun r z => Work.FTS.BSIdent.merPsi a A B
          (Work.FTS.StreamBdryIface.psiHatP (Work.FTS.Regularity.pExp a) Φs E g) C r z t) x :=
  Work.FTS_StreamBdry.SB0.sb0_psiField ha hC3 hdec hPsm hB

end Work.FTS_StreamBdry
