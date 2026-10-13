import Submission.Work.FTS.PressureOn.Connect.ctu_aux.Basic

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.EulerAssembly
import Submission.Work.FTS.PressureOn.Connect.Deriv
import Submission.Work.FTS.PressureOn.Connect.contDiffWithinAt_one_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.Connect.hasFDerivAt_uncurry_of_partials_corrected
import Submission.Work.FTS.PressureOn.hasDerivAt_pressurePotential_time_of_continuous
import Submission.Work.FTS.PressureOn.continuous_timeDeriv_pressurePotential
import Submission.Work.FTS.PressureOn.Connect.Clamp
import Submission.Work.FTS.PressureOn.Connect.Data
import Submission.Work.FTS.PressureOn.Connect.lipschitz_extendTime
import Submission.Work.FTS.PressureOn.Connect.lamb_lipschitz_near
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_physVel_time
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_lamb_time
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_of_hasDerivWithinAt_Ici
import Submission.Work.FTS.PressureOn.Connect.biotSavart_uniform_bound
import Submission.Work.FTS.PressureOn.Connect.omega_uniform_bound
import Submission.Work.FTS.PressureOn.tendsto_lamb_decay
import Submission.Work.FTS.PressureOn.pressurePotential_basic
import Submission.Work.FTS.PressureOn.lipschitz_time_lamb_strips
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_slice_of_hasFDerivAt_uncurry
import Submission.Work.FTS.BSSwirl.CrossAux
import Submission.Work.FTS.Physical.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint `C¹` of the reconstructed potential `q = potOn ω` on the half-open strip

This module proves `Work.FTS.PressureOn.Connect.contDiffOn_potOn_uncurry_open`: the uncurried
potential `(x,t) ↦ q x t = potOn ω x t = pressurePotential (lamb (physVel ω) ω · t) x` is jointly
`C¹` on `ℝ³ × (0,T)`.

The route (the standard "continuous partials" criterion, in the corrected form
`hasFDerivAt_uncurry_of_partials'` of this area):

* the **spatial** partial derivative of the slice `q · t` is `innerSL ℝ (∂ₜu - u×ω)`
  — this is the hypothesis `hgq` of the target statement (`potGradCLM`);
* the **time** partial derivative is `potTDeriv ω x t = -∫ ⟪∇N(x-y), ∂ₜ(u×ω)(y,t)⟫`
  (`hasDerivAt_potOn_time`, the clamped-field argument of this file);
* both partial derivative fields are continuous on `ℝ³ × (0,T)`: the spatial one from the
  strip regularity (`hstrips`), the temporal one (`potTDeriv_continuousAt`) by differentiating
  under the integral sign.

`hasFDerivAt_uncurry_of_partials'` then furnishes the full derivative at each interior point and
`contDiffWithinAt_one_of_hasFDerivAt` converts this into the `C¹` statement (`ContDiffOn` is
definitionally `∀ z ∈ s, ContDiffWithinAt`).

The helper lemmas are stated with the *same* hypothesis blob as the target so that they can be
consumed verbatim; the `_aux` suffix keeps them apart from the sibling modules in which the
fleet is proving the individual pieces.
-/

open FiniteTimeSingularity Set Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect
/-- **Continuity of the time derivative of the potential.**  Reparametrise the time variable so
that the Lamb-vector time derivative becomes a globally continuous, uniformly supported field
agreeing with it near the window `(ε, S') ∋ t`; the dominated-convergence lemma
`continuous_shifted_integral_joint` then gives joint continuity of the resulting integral, and
`potTDeriv` agrees with it on the window. -/
theorem potTDeriv_continuousAt_aux {α : NNReal} {ω : R3 → ℝ → R3} {T : ℝ}
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ s ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z s) x = ω x s)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ s ∈ Set.Icc 0 S, ∀ y, ω y s ≠ 0 → ‖y‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ y, ∀ s ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω y) (timeDeriv ω y s) (Set.Ici s) s)
    (x : R3) {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    ContinuousAt (fun p : R3 × ℝ => potTDeriv ω p.1 p.2) (x, t) := by
  obtain ⟨ht0, htT⟩ := ht
  -- the time window
  obtain ⟨ε, hε0, hεt⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < t := ⟨t / 2, by linarith, by linarith⟩
  obtain ⟨S', htS', hS'T⟩ : ∃ S' : ℝ, t < S' ∧ S' < T := ⟨(t + T) / 2, by linarith, by linarith⟩
  obtain ⟨S, hS'S, hST⟩ : ∃ S : ℝ, S' < S ∧ S < T := ⟨(S' + T) / 2, by linarith, by linarith⟩
  have hS'0 : 0 < S' := lt_trans ht0 htS'
  have hS0 : 0 < S := lt_trans hS'0 hS'S
  have hSIoo : S ∈ Set.Ioo 0 T := ⟨hS0, hST⟩
  have hstripS : IsContDiffHolderOn ℝ α (physVel ω).uncurry
      (Set.univ ×ˢ Set.Icc 0 S) := hstrips S hSIoo
  have hcd : ContDiffOn ℝ 1 (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S) := hstripS.1
  -- a time reparametrisation clamping into `[ε,S']`
  set ψ : ℝ → ℝ := fun s => ε + clampt (S' - ε) (s - ε) with hψdef
  have hψcont : Continuous ψ := by
    rw [hψdef]
    exact continuous_const.add
      ((lipschitzWith_clampt (S' - ε)).continuous.comp (continuous_id.sub continuous_const))
  have hψmem : ∀ s : ℝ, ψ s ∈ Set.Icc ε S' := by
    intro s
    have h := clampt_mem_Icc (show (0 : ℝ) ≤ S' - ε by linarith) (s - ε)
    show ε + clampt (S' - ε) (s - ε) ∈ Set.Icc ε S'
    constructor <;> linarith [h.1, h.2]
  have hψself : ∀ s ∈ Set.Icc ε S', ψ s = s := by
    intro s hs
    show ε + clampt (S' - ε) (s - ε) = s
    have h : clampt (S' - ε) (s - ε) = s - ε :=
      clampt_eq_self_of_mem ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [h]; ring
  have hmk : Continuous fun p : R3 × ℝ => ((p.1, ψ p.2) : R3 × ℝ) :=
    continuous_fst.prodMk (hψcont.comp continuous_snd)
  have hmk_mem : ∀ p : R3 × ℝ, (p.1, ψ p.2) ∈ Set.univ ×ˢ Set.Icc (0 : ℝ) S :=
    fun p => ⟨trivial, ⟨le_trans hε0.le (hψmem p.2).1, le_trans (hψmem p.2).2 hS'S.le⟩⟩
  have hmk_mem_Ico : ∀ p : R3 × ℝ, (p.1, ψ p.2) ∈ Set.univ ×ˢ Set.Ico (0 : ℝ) T :=
    fun p => ⟨trivial, ⟨le_trans hε0.le (hψmem p.2).1,
      lt_of_le_of_lt (hψmem p.2).2 hS'T⟩⟩
  -- the within-derivative field on the closed strip
  set TDu : R3 → ℝ → R3 := fun y σ =>
    fderivWithin ℝ (Function.uncurry (physVel ω)) (Set.univ ×ˢ Set.Icc 0 S) (y, σ)
      ((0 : R3), (1 : ℝ)) with hTUdef
  -- the reparametrised field
  set G : R3 → ℝ → R3 := fun y s =>
    crossVec (TDu y (ψ s)) (ω y (ψ s))
      + crossVec (physVel ω y (ψ s)) (timeDeriv ω y (ψ s)) with hGdef
  -- ## joint continuity of `G`
  have hTDu_cont : Continuous fun p : R3 × ℝ => TDu p.1 (ψ p.2) := by
    have hU : UniqueDiffOn ℝ (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)) :=
      UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc hS0)
    have hcont : ContinuousOn
        (fderivWithin ℝ (Function.uncurry (physVel ω)) (Set.univ ×ˢ Set.Icc 0 S))
        (Set.univ ×ˢ Set.Icc 0 S) := hcd.continuousOn_fderivWithin hU le_rfl
    have h1 : Continuous ((fderivWithin ℝ (Function.uncurry (physVel ω))
        (Set.univ ×ˢ Set.Icc 0 S)) ∘ fun p : R3 × ℝ => ((p.1, ψ p.2) : R3 × ℝ)) :=
      hcont.comp_continuous hmk hmk_mem
    have h2 : Continuous (fun p : R3 × ℝ => (fderivWithin ℝ (Function.uncurry (physVel ω))
        (Set.univ ×ˢ Set.Icc 0 S) (p.1, ψ p.2)) ((0 : R3), (1 : ℝ))) :=
      h1.clm_apply continuous_const
    simpa only [hTUdef] using h2
  have hω_cont : Continuous fun p : R3 × ℝ => ω p.1 (ψ p.2) :=
    (omega_strip_continuousOn_aux hSIoo hstrips hcurl).comp_continuous hmk hmk_mem
  have hu_cont : Continuous fun p : R3 × ℝ => physVel ω p.1 (ψ p.2) :=
    hcd.continuousOn.comp_continuous hmk hmk_mem
  have hTDω_cont : Continuous fun p : R3 × ℝ => timeDeriv ω p.1 (ψ p.2) :=
    hcontDt.comp_continuous hmk hmk_mem_Ico
  have hG_cont : Continuous fun p : R3 × ℝ => G p.1 p.2 := by
    have hsum : Continuous fun p : R3 × ℝ =>
        crossVec (TDu p.1 (ψ p.2)) (ω p.1 (ψ p.2))
          + crossVec (physVel ω p.1 (ψ p.2)) (timeDeriv ω p.1 (ψ p.2)) :=
      ((BSSwirl.crossBilin.continuous.comp hTDu_cont).clm_apply hω_cont).add
        ((BSSwirl.crossBilin.continuous.comp hu_cont).clm_apply hTDω_cont)
    simpa only [hGdef] using hsum
  -- ## uniform support of `G`
  obtain ⟨R₀, hR₀⟩ := hsupp S hSIoo
  have hTDω_supp : ∀ y σ, σ ∈ Set.Ioo 0 S → timeDeriv ω y σ ≠ 0 → ‖y‖ ≤ R₀ := by
    intro y σ hσ hne
    by_contra hle
    rw [not_le] at hle
    have hzero : ∀ s' ∈ Set.Icc (0 : ℝ) S, ω y s' = 0 := by
      intro s' hs'
      by_contra h
      exact absurd (hR₀ s' hs' y h) (not_le.mpr hle)
    have hev : (fun s' => ω y s') =ᶠ[𝓝 σ] (fun _ => (0 : R3)) := by
      filter_upwards [Ioo_mem_nhds hσ.1 hσ.2] with s' hs'
      exact hzero s' ⟨hs'.1.le, hs'.2.le⟩
    exact hne (by
      rw [FiniteTimeSingularity.timeDeriv, Filter.EventuallyEq.deriv_eq hev]
      simp)
  have hG_supp : ∀ t' : ℝ, ∃ R, ∀ s ∈ Set.Ioo (t' - 1) (t' + 1), ∀ y, G y s ≠ 0 → ‖y‖ ≤ R := by
    refine fun _ => ⟨R₀, fun s _ y hy => ?_⟩
    by_contra hle
    rw [not_le] at hle
    have hψmem_le : ψ s ∈ Set.Icc (0 : ℝ) S :=
      ⟨le_trans hε0.le (hψmem s).1, le_trans (hψmem s).2 hS'S.le⟩
    have h1 : ω y (ψ s) = 0 := by
      by_contra h
      exact absurd (hR₀ (ψ s) hψmem_le y h) (not_le.mpr hle)
    have h2 : timeDeriv ω y (ψ s) = 0 := by
      by_contra h
      exact absurd (hTDω_supp y (ψ s)
        ⟨lt_of_lt_of_le hε0 (hψmem s).1, lt_of_le_of_lt (hψmem s).2 hS'S⟩ h) (not_le.mpr hle)
    exact hy (by
      show crossVec (TDu y (ψ s)) (ω y (ψ s))
        + crossVec (physVel ω y (ψ s)) (timeDeriv ω y (ψ s)) = 0
      rw [h1, h2, crossVec_zero_right', crossVec_zero_right', add_zero])
  have hcont_shift := continuous_shifted_integral_joint hG_cont hG_supp
  -- ## the field `G` is the Lamb time-derivative at the interior times
  have hTDu_eq : ∀ y σ, σ ∈ Set.Ioo (0 : ℝ) S →
      TDu y σ = timeDeriv (physVel ω) y σ := by
    intro y σ hσ
    have hnhds : (Set.univ ×ˢ Set.Icc (0 : ℝ) S : Set (R3 × ℝ)) ∈ 𝓝 (y, σ) := by
      rw [nhds_prod_eq]
      exact prod_mem_prod univ_mem (Icc_mem_nhds hσ.1 hσ.2)
    have hdiff : DifferentiableAt ℝ (Function.uncurry (physVel ω)) (y, σ) :=
      (hcd.contDiffAt hnhds).differentiableAt (by norm_num)
    show fderivWithin ℝ (Function.uncurry (physVel ω)) (Set.univ ×ˢ Set.Icc 0 S) (y, σ)
        ((0 : R3), (1 : ℝ)) = timeDeriv (physVel ω) y σ
    rw [fderivWithin_of_mem_nhds hnhds, FiniteTimeSingularity.timeDeriv,
      (hasDerivAt_slice_of_hasFDerivAt_uncurry (v := physVel ω) (x := y) (t := σ)
        hdiff.hasFDerivAt).deriv]
  have hprod : ∀ σ ∈ Set.Ioo (0 : ℝ) S', ∀ y, timeDeriv (lamb (physVel ω) ω) y σ
      = crossVec (timeDeriv (physVel ω) y σ) (ω y σ)
        + crossVec (physVel ω y σ) (timeDeriv ω y σ) := by
    intro σ hσ y
    refine timeDeriv_lamb ?_ ?_
    · exact hasDerivAt_physVel_time (x := y) hσ (hstrips S' ⟨hS'0, hS'T⟩)
    · exact hasDerivAt_omega_slice_at_aux hstrips hcurl hcontDt hderiv
        ⟨hσ.1, lt_trans hσ.2 hS'T⟩ y
  have hagree : ∀ p ∈ (Set.univ ×ˢ Set.Ioo ε S'), potTDeriv ω p.1 p.2
      = -∫ z, inner ℝ (nablaNfund z) (G (p.1 - z) p.2) := by
    rintro ⟨y, s⟩ ⟨-, hs⟩
    have hψs : ψ s = s := hψself s ⟨hs.1.le, hs.2.le⟩
    have hsS : s ∈ Set.Ioo (0 : ℝ) S := ⟨lt_trans hε0 hs.1, lt_trans hs.2 hS'S⟩
    have hGeq : ∀ u : R3, G u s = timeDeriv (lamb (physVel ω) ω) u s := by
      intro u
      have h2 : G u s = crossVec (timeDeriv (physVel ω) u s) (ω u s)
          + crossVec (physVel ω u s) (timeDeriv ω u s) := by
        show crossVec (TDu u (ψ s)) (ω u (ψ s))
          + crossVec (physVel ω u (ψ s)) (timeDeriv ω u (ψ s)) = _
        rw [hψs, hTDu_eq u s hsS]
      rw [h2]
      exact (hprod s ⟨lt_trans hε0 hs.1, hs.2⟩ u).symm
    have hval : (-∫ z, inner ℝ (nablaNfund (y - z))
          (timeDeriv (lamb (physVel ω) ω) z s))
        = -∫ z, inner ℝ (nablaNfund z) (G (y - z) s) := by
      rw [show (fun z => inner ℝ (nablaNfund (y - z))
            (timeDeriv (lamb (physVel ω) ω) z s))
          = fun z => inner ℝ (nablaNfund (y - z)) (G z s) from by
        funext z; rw [hGeq z]]
      rw [integral_shift_nablaNfund (fun z => G z s) y]
    rw [potTDeriv]
    exact hval
  -- ## conclude
  have hnear : (Set.univ ×ˢ Set.Ioo ε S') ∈ 𝓝 ((x, t) : R3 × ℝ) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod univ_mem (Ioo_mem_nhds hεt htS')
  have hcts : ContinuousAt (fun p : R3 × ℝ =>
      -∫ z, inner ℝ (nablaNfund z) (G (p.1 - z) p.2)) (x, t) :=
    hcont_shift.continuousAt.neg
  refine hcts.congr ?_
  filter_upwards [hnear] with p hp
  exact (hagree p hp).symm
end Work.FTS.PressureOn.Connect
