import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS_StreamBdry.Inputs.slice_inputs
import Submission.Work.FTS_StreamBdry.Assembly.hid9_of_slot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `hid9''_of_parts_proved` — the frozen assembly `StreamBdryIface.hid9''_of_parts`

The (9″) producer: for the firing data of the strong route, the physical velocity built from the
vorticity `physOmega a A B (extG g)` agrees on `Uax` with `Cyl.psiField` of the meridian field of
the firing stream function `psiFire Φs E g`.

Assembly (see `Assembly/hid9_of_slot`): SB0 (`sb0_psiField_proved`) rewrites the field to
`BSIdent.merPsi a A B (psiHatP (pExp a) Φs E g)`; the BSIdent port `hid_of_corrected'_slim`
(delivered by `FTS_BSIdentP` and already wired into the frozen interface) is applied at
`Φ := psiHatP`, `g := extG G`; `hlaw` comes from `Sol` + `bslOp gaugeMode = 0`
(`SB25.gaugeMode_facts`) + `hG`; `hΦsm` is `sb2_c2_proved`; the plane/axis values come from
`oddPerS`; the rates are `sb6_rates_proved` fed by `Inputs.slice_inputs` (frozen, now proved by the
`RXT.velVanish2` route rather than `VelPkg.dbnd`) and `sb4_near0_proved`; the final rewrite
`physOmega (extG G) = physOmega (extG g)` uses `hG`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry

set_option autoImplicit false

/-- **(9″) proved** (frozen type `hid9''_of_parts`). -/
theorem hid9''_of_parts_proved {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp a) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs) :
    ∀ (g G : Work.FTS.Galerkin.Fam) (A B : ℝ → ℝ) (C : Work.FTS.Physical.PhysClock),
      Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp a) Φs E g →
      Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g →
      Work.FTS.Final.ClockData (Work.FTS.Regularity.pExp a)
        (Work.FTS.Nonlin.PsiCan Φs E g) g A B C →
      (∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G)) →
      (∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) →
      ∀ t ∈ Set.Ioo (0 : ℝ) C.T, ∀ x ∈ Work.FTS.BSIdent.Uax,
        Work.FTS.Physical.physVel
          (fun x s => - Work.FTS.Physical.physOmega a A B (Work.FTS.RegPkgGal.extG g) C x s) x t
          = Work.Cyl.psiField
              (fun r z => Work.FTS.MeridianDyn.merPsi (Work.FTS.Regularity.pExp a) A B
                (Work.FTS.FinalV2.psiFire Φs E g) C r z t) x := by
  intro g G A B C hSol hOK hClock hreg hG
  refine Assembly.hid9_of_slot ha ha13 hEll hEL hStar g G A B C hSol hOK hClock hreg ?_ hG
  intro τ hτ
  obtain ⟨M, L, Mf, _hC3, hslot, _hsrc⟩ :=
    Work.FTS_StreamBdry.Inputs.slice_inputs ha ha13 hEll hEL hStar hSol hOK hreg hG τ hτ
  exact ⟨M, hslot⟩

end Work.FTS_StreamBdry
