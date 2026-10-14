import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.MeridianDyn.Bridge.ProfDerivData_of_regPkg_closed
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.PotTDeriv
import Submission.Work.FTS.PressureOn.PoissonAux.kernelGradIntegral
import Submission.Work.FTS.PressureOn.PoissonAux.kernelIntegral
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_offPlanes
import Submission.Work.FTS.PressureOn.normSlopePhysVelLe
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.tendsto_lamb_decay
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.PressureOn.weakDiv_timeDeriv
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
import Submission.Work.FTS.StrongEps.EpsRLX.WpUniformBound
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddPi
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_FinalLeaves.profDerivData_min_proved
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.SysAux.explicit_piece_bounds
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H2W.FstarDzIterFourPsiAe
-- ===== merged: Submission.Work.FTS.PressureOn.Connect.contDiffOn_potOn_uncurry_open =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint `C¹` of the reconstructed potential `q = potOn ω` on the half-open strip

`Work.FTS.PressureOn.Connect.contDiffOn_potOn_uncurry_open`: the uncurried potential
`(x,t) ↦ q x t = potOn ω x t = pressurePotential (lamb (physVel ω) ω · t) x` is jointly `C¹` on
`ℝ³ × (0,T)`.

## The route

The criterion used is the "continuous partials" one, in the corrected form of this area
(`hasFDerivAt_uncurry_of_partials'` + `contDiffWithinAt_one_of_hasFDerivAt`):

* **the spatial partial derivative** of the slice `q · t` is `innerSL ℝ (∂ₜu - u×ω)`
  (`potGradCLM ω x t`).  This is precisely the hypothesis `hgq` of the statement; its continuity
  on the strip is `continuousAt_potGradCLM_aux` (`ctu_aux.Grad`), which combines the joint
  continuity of `∂ₜu` (`timeDeriv_physVel_continuousOn_strip_aux`, `ctu_aux.Basic`) and of `ω`
  (`omega_strip_continuousOn_aux`, `ctu_aux.Basic`) with the continuity of `innerSL ℝ`.

* **the time partial derivative** is `potTDeriv ω x t = -∫ ⟪∇N(x-y), ∂ₜ(u×ω)(y,t)⟫`.
  Its existence at interior times is `hasDerivAt_potOn_time_aux` (`ctu_aux.PotOnTime`): clamp the
  fields to a strip `[0,S]`, `t < S < T`; the clamped Lamb vector is jointly continuous, uniformly
  supported, Lipschitz in time (bounds for `ω` from `omega_uniform_bound`, for `u = physVel ω` from
  `biotSavart_uniform_bound`, assembled by `lamb_lipschitz_near`) and differentiable in time at `t`
  (`hasDerivAt_lamb_time`, whose vorticity input is the *two-sided* differentiability of the
  vorticity slices `hasDerivAt_omega_slice_at_aux`, obtained from the one-sided data by the
  one-sided mean value theorem `hasDerivAt_of_hasDerivWithinAt_Ici`).  Then
  `hasDerivAt_pressurePotential_time_of_continuous` differentiates under the integral sign, and the
  clamping is invisible near `t`.
  Its continuity is `potTDeriv_continuousAt_aux` (`ctu_aux.PotTDeriv`): reparametrise time by a
  clamp into `[ε,S'] ∋ t`, which turns the Lamb time derivative into a *globally* continuous,
  uniformly supported field, and apply the dominated-convergence lemma
  `continuous_shifted_integral_joint`.

Finally `potFDeriv_eq_aux` writes the two partials as the derivative
`potFDeriv ω x t = (potGradCLM ω x t) ∘ fst + (potTDeriv ω x t) • snd` on `ℝ³ × ℝ`, and the
assembly above produces the `HasFDerivAt` whose continuity gives the `C¹` statement.
-/

open FiniteTimeSingularity Set Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

theorem contDiffOn_potOn_uncurry_open {α : NNReal}
    {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {T : ℝ}
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z t) x = ω x t)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ t ∈ Set.Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x t) (Set.Ici t) t)
    (hgq : ∀ t ∈ Set.Ioo 0 T, ∀ x, HasFDerivAt (Work.FTS.PressureOn.potOn ω · t)
      (innerSL ℝ (FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t
        - Work.FTS.PressureOn.crossVec (Work.FTS.Physical.physVel ω x t) (ω x t))) x) :
    ContDiffOn ℝ 1 (fun z : Work.FTS.PressureOn.R3 × ℝ => Work.FTS.PressureOn.potOn ω z.1 z.2)
      (Set.univ ×ˢ Set.Ioo 0 T) := by
  have hopen : IsOpen (Set.univ ×ˢ Set.Ioo (0 : ℝ) T) :=
    (isOpen_univ : IsOpen (Set.univ : Set R3)).prod isOpen_Ioo
  -- the candidate derivative at each interior point
  have hderivAt : ∀ z ∈ (Set.univ ×ˢ Set.Ioo (0 : ℝ) T),
      HasFDerivAt (fun z : R3 × ℝ => potOn ω z.1 z.2) (potFDeriv ω z.1 z.2) z := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have hx : HasFDerivAt (fun y => potOn ω y t) (potGradCLM ω x t) x := hgq t ht x
    have ht' : HasDerivAt (fun s => potOn ω x s) (potTDeriv ω x t) t :=
      hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv x ht
    have hnhds : (Set.univ ×ˢ Set.Ioo (0 : ℝ) T : Set (R3 × ℝ)) ∈ 𝓝 (x, t) :=
      prod_mem_nhds univ_mem (isOpen_Ioo.mem_nhds ht)
    have h2 : ∀ᶠ p in 𝓝 (x, t), HasDerivAt (fun s' => potOn ω p.1 s')
        (deriv (fun s' => potOn ω p.1 s') p.2) p.2 := by
      filter_upwards [hnhds] with p hp
      rw [(hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv p.1 hp.2).deriv]
      exact hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv p.1 hp.2
    have hcont2 : ContinuousAt (fun p : R3 × ℝ => deriv (fun s' => potOn ω p.1 s') p.2)
        (x, t) := by
      refine (potTDeriv_continuousAt_aux hstrips hcurl hsupp hcontDt hderiv x ht).congr ?_
      filter_upwards [hnhds] with p hp
      exact (hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv p.1 hp.2).deriv.symm
    have hmain := hasFDerivAt_uncurry_of_partials' (q := potOn ω) (x := x) (t := t)
      (L := potGradCLM ω x t) (c := potTDeriv ω x t) hx ht' h2 hcont2
    rw [potFDeriv_eq_aux]
    simpa only [smulRight_snd_eq_smul'] using hmain
  -- the derivative field is continuous on the strip
  have hcontF : ContinuousOn (fun z : R3 × ℝ => potFDeriv ω z.1 z.2)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) T) := by
    rw [hopen.continuousOn_iff]
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have h1 : ContinuousAt (fun z : R3 × ℝ =>
        (potGradCLM ω z.1 z.2).comp (ContinuousLinearMap.fst ℝ R3 ℝ)) (x, t) :=
      (continuousAt_potGradCLM_aux hstrips hcurl x ht).clm_comp continuousAt_const
    have h2 : ContinuousAt (fun z : R3 × ℝ =>
        (potTDeriv ω z.1 z.2) • (ContinuousLinearMap.snd ℝ R3 ℝ)) (x, t) :=
      (potTDeriv_continuousAt_aux hstrips hcurl hsupp hcontDt hderiv x ht).smul continuousAt_const
    refine (h1.add h2).congr ?_
    filter_upwards with z
    exact (potFDeriv_eq_aux ω z.1 z.2).symm
  intro z hz
  exact contDiffWithinAt_one_of_hasFDerivAt (hopen.mem_nhds hz) hderivAt hcontF

end Work.FTS.PressureOn.Connect
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.hardyHyp_of_coerAdmO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HardyHyp` for the *open* coercivity class `CoerAdmO`

This file proves `Work.FTS.StrongEps.EpsE4Thr.hardyHyp_of_coerAdmO`: the analytic hypothesis
package `Work.Coercivity.HardyHyp` (the hypotheses of Lemma `HardyWeight` of Elgindi's paper)
holds for every datum of the *open* interior class

  `CoerAdmO α f` = `RegQo α 5 f ∧ VanishTheta f ∧ axis ∧ L₁₂(f)(0) = 0`,

i.e. `C^∞` on the **open** quadrant `(0,∞) × (0,π/2)` (instead of the strip `z > -1`),
for `0 < α ≤ 10⁻¹⁴`.

This is the open-class companion of the sibling
`Work.FTS.CoercivityFix.Coer1T.hardyHyp_of_coerAdm` (which needs the stronger `SmoothQuad`),
and it is the version the level-four `ε`-chapter needs: the projected mollified slices of the
route are `SmoothOpen` (`coerAdmO_slice_JfamP`) but never `SmoothQuad`.

## The seven fields

* `hslice` — integrability of `θ ↦ K(θ) f z θ / z` on `Iθ`: the open-class
  `Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn`, whose only
  regularity input is `ContinuousOn (uncurry f) Q0` (from `SmoothOpen.forall 1`).
* `hcont` — continuity of the `L₁₂`-density at every `z > 0`: the open-class
  `Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk`.
* `hint` — `L12dens ∈ L¹((0,∞))`:
  `Work.FTS.MeridianDyn.Bridge.integrableOn_L12dens_of_smoothOpen_Hk`.
* `intA` — `(L₁₂ f)²/z^{2j} ∈ L¹((0,∞))` for `j ≤ 2`: the open-class ports
  `HardyOpen.L12f_sq_div_small_open` (on `(0,1]`) and `HardyOpen.L12f_sq_div_large_open`
  (on `(1,∞)`), glued with `Ioc 0 1 ∪ Ioi 1 = Ioi 0`.
* `intB` — `(∫_θ f z θ²)/z^{2j} ∈ L¹((0,∞))` for `j ≤ 2`: the open-class port
  `HardyOpen.intB_integrableOn_open`.
* `bd0`, `bdTop` — the boundary terms at `0⁺` and at `∞`: the open-class ports
  `HardyOpen.L12f_bd0_open` / `HardyOpen.L12f_bdTop_open`.

The `ℋ⁴`-membership used everywhere is `HkMem α 4 f`, obtained from the `ℋ⁵`-membership of
`RegQo α 5 f` via `Work.FTS.OpenPkg.HkMem_mono_open` (the open-class monotonicity).
-/

namespace Work.FTS.StrongEps.EpsE4Thr

open MeasureTheory Set Filter
open scoped Real Topology

theorem hardyHyp_of_coerAdmO {α : ℝ} {f : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hα1 : α ≤ 1 / 10 ^ 14) (hf : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α f) :
    Work.Coercivity.HardyHyp f := by
  obtain ⟨hreg, hvan, haxis, hl12⟩ := hf
  obtain ⟨hsm, hmem5, hbdry⟩ := hreg
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hmem5
  have hint : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) :=
    Work.FTS.MeridianDyn.Bridge.integrableOn_L12dens_of_smoothOpen_Hk hsm hmem
  have hcont : ∀ z ∈ Set.Ioi (0 : ℝ), ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
    fun z hz => Work.FTS.MeridianDyn.Bridge.continuousAt_L12dens_of_smoothOpen_Hk hsm hmem hz
  have hl12' : Work.Coercivity.L12f f 0 = 0 := by
    simpa [Work.Coercivity.L12f, Work.FM.L12, Work.Construction.L12] using hl12
  have hC : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 :=
    (hsm.forall 1).continuousOn
  have hU : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi (0 : ℝ) := by
    ext t
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith [h]
    · intro h
      rcases lt_trichotomy t 1 with h' | h' | h'
      · exact Or.inl ⟨h, h'.le⟩
      · exact Or.inl ⟨h, le_of_eq h'⟩
      · exact Or.inr h'
  refine ⟨?_, ?_, hint, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact Work.FTS.MeridianDyn.Bridge.Pieces.sliceK_integrableOn_of_continuousOn hC hmem z hz
  · exact hcont
  · intro j hj
    rw [← hU]
    exact MeasureTheory.IntegrableOn.union
      (HardyOpen.L12f_sq_div_small_open α hsm hmem hint hl12' hcont j hj)
      (HardyOpen.L12f_sq_div_large_open α hsm hmem hint hcont j)
  · intro j hj
    exact HardyOpen.intB_integrableOn_open α hsm hmem j hj
  · intro j hj
    exact HardyOpen.L12f_bd0_open α hsm hmem hint hl12' j hj
  · intro j hj
    exact HardyOpen.L12f_bdTop_open α hsm hmem j

end Work.FTS.StrongEps.EpsE4Thr
end
