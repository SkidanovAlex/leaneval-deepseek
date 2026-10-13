import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS_StreamBdry.SB25.gaugeMode_facts
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.GalBasis.GalApprox.poly2_aux1
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

open scoped Topology

set_option linter.unusedVariables false

/-- The second iterated derivative at `1` of the power function `z ↦ z ^ p`:
`∂_z²(z^p)(1) = p(p-1)`.  (`Real.deriv_rpow_const` twice.) -/
private lemma iteratedDeriv_two_rpow_one (p : ℝ) :
    iteratedDeriv 2 (fun z : ℝ => z ^ p) 1 = p * (p - 1) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (fun z : ℝ => z ^ p) = fun z => p * z ^ (p - 1) := by
    funext z; exact Real.deriv_rpow_const z p
  rw [h1, deriv_const_mul_field, Real.deriv_rpow_const, Real.one_rpow]
  ring

/-- **The second `z`-derivative of `PhiTil` at `z = 1` splits along the gauge decomposition.**
Given the pointwise identity `PhiTil α g Ψ = psiP α (PhiTil α g Ψ) + κ · gaugeMode α` on the open
quadrant (`Qd = Ioi 0 ×ˢ Ioo 0 (π/2)`, the SB1′ decomposition), we have at `z = 1`

`∂_z²(PhiTil) = ∂_z²(psiP) + κ · ((3/α)(3/α+1)/cos θ)`,

since `∂_z² (z^{-3/α}/cos θ) = (−3/α)(−3/α−1)·z^{-3/α−2}/cos θ`, which at `z = 1` equals
`(3/α)(3/α+1)/cos θ`.
Route: for fixed `θ ∈ (0,π/2)` the slice `{z | z > 0}` lies in `Qd`, so `hdec` gives equality of
the two `z`-slices on the neighbourhood `Ioi 0` of `1`; transfer `∂_z²` with
`Filter.EventuallyEq.deriv_eq` (twice), then split with `GalApprox.pzIter_add` (needs
`ContDiffAt ℝ 2` of the `z`-slice of `psiP` — from `hP` — and of the gauge slice, from the
analyticity of `z^{-3/α}/cos θ` on `Qd`, `SB25.contDiffOn_uncurry_gaugeMode`) and
`PhiStar.pzIter_const_mul` (constant `κ`); finish with two derivative computations for
`z ↦ z^{-3/α}/cos θ` (`Real.hasDerivAt_rpow_const`, `deriv_const_mul`).
Consumed by `Work.FTS_EllLimOK.ProducerH.kappa_eq_zero`. -/
theorem pzIterTwo_PhiTil_eq_psiP_add {α : ℝ} {g Ψ : ℝ → ℝ → ℝ} {κ : ℝ}
    (hΦ : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.PhiTil α g Ψ))
    (hP : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ)))
    (hdec : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.PhiTil α g Ψ z θ
        = Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ
          + κ * Work.FTS.StreamBdryIface.gaugeMode α z θ)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.pzIter 2 (Work.Construction.PhiTil α g Ψ) 1 θ
      = Work.Spaces.pzIter 2
          (Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ)) 1 θ
        + κ * ((3 / α) * (3 / α + 1) / Real.cos θ) := by
  -- The two `z`-slices agree on the neighbourhood `Ioi 0` of `1`, by `hdec` on `Qd`.
  have hXeq : (fun z => Work.Construction.PhiTil α g Ψ z θ)
      =ᶠ[nhds (1 : ℝ)]
        (fun z => Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ
          + κ * Work.FTS.StreamBdryIface.gaugeMode α z θ) := by
    refine Filter.eventually_of_mem
      (isOpen_Ioi.mem_nhds (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)) ?_
    intro z hz
    exact hdec z θ (by
      simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨hz, hθ.1, hθ.2⟩)
  -- `C²` of the `psiP` slice, from `SmoothOpen`.
  have hPc : ContDiffAt ℝ 2
      (fun z => Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ) 1 :=
    ((hP.curry_z hθ).contDiffAt (isOpen_Ioi.mem_nhds (by norm_num))).of_le (by decide)
  -- `C²` of the gauge slice, from analyticity on the open quadrant.
  have hGm : ContDiffAt ℝ 2 (fun z => Work.FTS.StreamBdryIface.gaugeMode α z θ) 1 := by
    have hmem : (1, θ) ∈ Work.Construction.Qd := by
      simp only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨by norm_num, hθ.1, hθ.2⟩
    have h1 : ContDiffAt ℝ 2
        (Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode α)) (1, θ) :=
      ((Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode α).of_le le_top).contDiffAt
        (Work.FTS_StreamBdry.SB25.qd_isOpen.mem_nhds hmem)
    have h2 : ContDiffAt ℝ 2 (fun z : ℝ => (z, θ)) 1 :=
      (contDiffAt_id (x := (1 : ℝ))).prodMk (contDiffAt_const (c := θ))
    have h3 := h1.comp 1 h2
    have hfun : (Function.uncurry (Work.FTS.StreamBdryIface.gaugeMode α))
          ∘ (fun z : ℝ => (z, θ))
        = fun z => Work.FTS.StreamBdryIface.gaugeMode α z θ := rfl
    rwa [hfun] at h3
  have hGmc : ContDiffAt ℝ 2 (fun z => κ * Work.FTS.StreamBdryIface.gaugeMode α z θ) 1 :=
    (contDiffAt_const (c := κ)).mul hGm
  -- `∂_z² (z^{-3/α}/cos θ)_1 = (3/α)(3/α+1)/cos θ`.
  have hGm2 : iteratedDeriv 2 (fun z => Work.FTS.StreamBdryIface.gaugeMode α z θ) 1
      = (3 / α) * (3 / α + 1) / Real.cos θ := by
    have hslice : (fun z => Work.FTS.StreamBdryIface.gaugeMode α z θ)
        = fun z => (Real.cos θ)⁻¹ * z ^ (-(3 / α)) := by
      funext z
      rw [Work.FTS.StreamBdryIface.gaugeMode, div_eq_inv_mul, mul_comm]
    rw [hslice,
      iteratedDeriv_const_mul ((Real.cos θ)⁻¹)
        (Real.contDiffAt_rpow_const_of_ne (x := 1) (p := -(3 / α)) (n := 2) (by norm_num)),
      iteratedDeriv_two_rpow_one]
    have hp : (-(3 / α)) * (-(3 / α) - 1) = (3 / α) * (3 / α + 1) := by ring
    rw [hp]
    ring
  have hsum : (fun z => Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ
        + κ * Work.FTS.StreamBdryIface.gaugeMode α z θ)
      = (fun z => Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ)
        + (fun z => κ * Work.FTS.StreamBdryIface.gaugeMode α z θ) := rfl
  have hPit : iteratedDeriv 2
      (fun z => Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ) z θ) 1
      = Work.Spaces.pzIter 2
          (Work.FTS.StreamBdryIface.psiP α (Work.Construction.PhiTil α g Ψ)) 1 θ :=
    (Work.Spaces.pzIter_eq_iteratedDeriv 2 _ 1 θ).symm
  rw [Work.Spaces.pzIter_eq_iteratedDeriv 2 _ 1 θ,
    Filter.EventuallyEq.iteratedDeriv_eq 2 hXeq, hsum,
    iteratedDeriv_add hPc hGmc, iteratedDeriv_const_mul κ hGm, hPit, hGm2]

end Work.FTS_EllLimOK.ProducerH
