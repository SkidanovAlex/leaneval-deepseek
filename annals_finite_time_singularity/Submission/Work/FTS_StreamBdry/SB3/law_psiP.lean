import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB1.psiP_diff
import Submission.Work.FTS_StreamBdry.SB1.psiP_Vop_bnd
import Submission.Work.FTS_StreamBdry.SB25.law_Dform
import Submission.Work.FTS_StreamBdry.SB25.gaugeMode_facts
import Submission.Work.FTS_StreamBdry.SB25.bslOp_lincombQd
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS.H2.PhiStarE5.Locality
import Submission.Work.Elliptic.bslOp_add
import Submission.Work.FTS.BSIdent.OddExt.bslOp_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.law_psiP` — the elliptic law in `D`-form for `psiP`

The SB3 chain (`sb3_bounds`, `sb2_dthDV`, `sb6_rates`) needs the law

`∂_θ V(psiP) = -(αG² D_z² psiP + 5 αG D_z psiP + 6 psiP) - F`

of `SB25.law_Dform`, applied not to `Ψ` but to the `U`-slot part `psiP αG Ψ`.  The passage
`Ψ → psiP` is the gauge decomposition of SB1′

`Ψ = psiP αG Ψ + κ·gaugeMode αG`  on `Qd`,

together with the two facts supplied by `SB25`:

* `gaugeMode` is `bslOp`-harmonic on the quadrant (`SB25.gaugeMode_facts`);
* `bslOp` is additive (`Work.Elliptic.bslOp_add`) and homogeneous
  (`Work.FTS.BSIdent.OddExt.bslOp_const_mul`), and — crucially — *local*
  (`Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq`), so that the pointwise identity on the
  open quadrant may be used inside `bslOp`.

Conclusion: `bslOp αG (psiP αG Ψ) = F` on `Qd`, whence `SB25.law_Dform` at `P := psiP αG Ψ`
(`C²` is `SB3.psiP_c2`) gives the stated law.
-/

set_option autoImplicit false

open scoped Real Topology
open Filter Set

namespace Work.FTS_StreamBdry.SB3

theorem law_psiP {αG M : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ)) z θ
        = -(αG ^ 2 * Work.Spaces.DzIter 2 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
            + 5 * αG * Work.Spaces.Dz (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
            + 6 * Work.FTS.StreamBdryIface.psiP αG Ψ z θ) - F z θ := by
  -- SB1′: on the open quadrant, `Ψ = psiP αG Ψ + κ·gaugeMode αG`
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M)
    hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  -- `psiP` is `C²` on the quadrant, and so is the gauge summand
  have hC2 : ContDiffOn ℝ 2
      (Function.uncurry (Work.FTS.StreamBdryIface.psiP αG Ψ)) Work.Construction.Qd :=
    psiP_c2 hαG h3 hslot
  have hgau : ContDiffOn ℝ 2
      (Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode αG)) Work.Construction.Qd :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode αG).of_le le_top
  -- the elliptic law for `psiP`: `bslOp αG (psiP αG Ψ) = F` on `Qd`
  have hlaw : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ = F z θ := by
    intro z θ hmem
    obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
    have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem)
    have hnbhd : Work.Construction.Qd ∈ 𝓝 (z, θ) :=
      Work.FTS_StreamBdry.SB25.qd_isOpen.mem_nhds ⟨hz, hθ1, hθ2⟩
    -- the gauge decomposition holds near `(z,θ)`, hence `bslOp` cannot see the difference
    have hev : ∀ᶠ q in 𝓝 (z, θ),
        Ψ q.1 q.2 = (Work.FTS.StreamBdryIface.psiP αG Ψ q.1 q.2
          + κ * Work.FTS.StreamBdryIface.gaugeMode αG q.1 q.2) :=
      Filter.mem_of_superset hnbhd (fun q hq => hκ q.1 q.2 hq)
    have hcongr : Work.Elliptic.bslOp αG Ψ z θ
        = Work.Elliptic.bslOp αG (fun z θ =>
            Work.FTS.StreamBdryIface.psiP αG Ψ z θ
              + κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ :=
      Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq αG hev
    -- additivity of `bslOp` at `(z,θ)`
    have hg2 : ContDiffAt ℝ 2
        (Function.uncurry (fun z θ => κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ))
        (z, θ) :=
      (hgau.contDiffAt hnbhd).const_smul κ
    have hadd : Work.Elliptic.bslOp αG (fun z θ =>
          Work.FTS.StreamBdryIface.psiP αG Ψ z θ
            + κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ
        = Work.Elliptic.bslOp αG (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
          + Work.Elliptic.bslOp αG (fun z θ =>
              κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ :=
      Work.Elliptic.bslOp_add αG (Work.FTS.StreamBdryIface.psiP αG Ψ)
        (fun z θ => κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ hcos
        (hC2.contDiffAt hnbhd) hg2
    -- the gauge summand is `bslOp`-harmonic
    have hD0 : Work.Elliptic.bslOp αG
        (fun z θ => κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ = 0 := by
      rw [Work.FTS.BSIdent.OddExt.bslOp_const_mul αG κ
            (Work.FTS.StreamBdryIface.gaugeMode αG) z θ,
        ((Work.FTS_StreamBdry.SB25.gaugeMode_facts hαG).2 z θ hmem).2, mul_zero]
    calc Work.Elliptic.bslOp αG (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ
        = Work.Elliptic.bslOp αG (fun z θ =>
            Work.FTS.StreamBdryIface.psiP αG Ψ z θ
              + κ * Work.FTS.StreamBdryIface.gaugeMode αG z θ) z θ := by
          rw [hadd, hD0, add_zero]
      _ = Work.Elliptic.bslOp αG Ψ z θ := hcongr.symm
      _ = F z θ := hsol.1 z hz θ hθ1 hθ2
  -- `SB25.law_Dform` for `P := psiP αG Ψ`
  exact Work.FTS_StreamBdry.SB25.law_Dform αG F (Work.FTS.StreamBdryIface.psiP αG Ψ) hC2 hlaw

end Work.FTS_StreamBdry.SB3
