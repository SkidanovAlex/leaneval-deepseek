/-
# `Work.ConstructionInstance.selfSimNoLG_of_data` — the maximality (blow-up) residual, discharged

`Tie.lean` reduced `tie` to the four analytic residuals `SelfSimVorticityEquation`,
`SelfSimLGClass`, `SelfSimVortSmooth` and `SelfSimMaximal`, and `Maximality.lean` observed that
the last one is *not* an independent input.  This module proves the key mathematical step behind
that observation, in the form the construction instantiation needs:

> the cut-off Lichtenstein–Gunther datum `ω₀ = χ(ρ/L)·omegaS` of the profile data `P` admits no
> LG-class solution (`Work.LWP.LGClass`) past the self-similar blow-up time `P.T`.

This is `SelfSimNoLG P`, and it is the statement `selfSimNoLG_of_data`, from which
`SelfSimBlowUp P ⟸ SelfSimNoLG P` (`Tie.selfSimBlowUp_of_noLG`) gives finding (I),
`SelfSimMaximal P` and hence `tie`.

## The argument

The proof is the Beale–Kato–Majda dichotomy, read in the wrong direction: a solution in the
spacetime Lichtenstein–Gunther class has a *quantitatively bounded* derivative (the class
`IsContDiffHolderOn` carries `IsBoundedFunOn (fderivWithin ℝ · ·)`), hence bounded vorticity, on
every compact time strip; whereas the vorticity of the self-similar ansatz *blows up* like
`c/(P.T - t)` at the blow-up time (`St5`, `bkm_divergence_of_st5`).

Let then `(p',u')` be an `LGClass`-solution of the datum on `[0,T')` with `P.T < T'`:

* on `[0,P.T)` the ansatz `u = BS(solVort P ·)` is also an Euler solution with the same datum
  (`LWPInputs.pressure`, fed by residuals 1 and 2, and residual 3 for its `C¹` class), so
  `LWPInputs.uniqueness` forces `u' = u` there (`huniq`), hence
  `bkm u' t = bkm u t` for `t ∈ [0,P.T)` (`bkm_congr_of_eqOn_Ico`);
* on the strip `[0,(P.T+T')/2]`, which contains `[0,P.T]` in its interior in the time variable,
  the LG class bounds `∇u'` — and therefore `∇×u' = ∇×(ansatz) = solVort P` — by a constant `K`
  (`vorticity_bound_of_strip`); the `L∞`-norm of the vorticity of `u'` is thus bounded by `K` on
  `[0,P.T)`, and `bkm_le_of_vortLInf_bound` (together with the interval-integrability of the
  sup-norm along the ansatz, `intervalIntegrable_vortLInf_ansatzV`) gives
  `bkm u' t ≤ K·P.T` for `t ∈ [0,P.T)`;
* but `bkm (ansatzV P) t = bkm u' t → +∞` as `t → P.T⁻` (`bkm_divergence_of_st5`), so at some
  `t ∈ [0,P.T)` we have `bkm u' t > K·P.T` — contradiction.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.Tie
import Submission.Work.ConstructionInstance.norm_vorticity_le
import Submission.Work.ConstructionInstance.Reduced
import Submission.Work.ConstructionInstance.vorticity_biotSavart_solVort
import Submission.Work.ConstructionInstance.bkm_divergence_of_st5
import Submission.Work.ConstructionInstance.vorticity_bound_of_strip
import Submission.Work.ConstructionInstance.bkm_congr_of_eqOn_Ico
import Submission.Work.ConstructionInstance.bkm_le_of_vortLInf_bound
import Submission.Work.StabilityFar.Deriv.hasFDerivAt_uncurry_apply
import Submission.Work.StabilityFar.St5
import Submission.Work.LWP.Inputs
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

namespace Work.ConstructionInstance

theorem selfSimNoLG_of_data {α : NNReal} (P : Work.ConstructionInstance.ProfileData α)
    (hlwp : Work.LWP.LWPInputs α) (hv : Work.ConstructionInstance.SelfSimVorticityEquation α P)
    (hG : Work.ConstructionInstance.SelfSimLGClass α P)
    (hsm : Work.ConstructionInstance.SelfSimVortSmooth P) :
    Work.ConstructionInstance.SelfSimNoLG P := by
  -- an `LGClass` solution of the datum past the blow-up time is contradictory
  intro T' hT' ⟨p', u', hLG⟩
  obtain ⟨hsol', _hodd', hst'⟩ := hLG
  -- the ansatz is an Euler solution of the same datum on `[0,P.T)`
  obtain ⟨p, hpc, hpe⟩ := hlwp.pressure (ansatzV P) (solVort P) P.T
      ((selfSimLGClass_iff_spaceTimeHolder P).mp hG)
      (fun t ht x => vorticity_ansatzV P hlwp.law t ⟨by linarith [ht.1], ht.2⟩ x)
      (fun t ht => div_ansatzV P hlwp.law t ⟨by linarith [ht.1], ht.2⟩) hv
  have hsol : IsLocalEulerEquationSolution p
      (Work.LWP.biotSavart (omega₀ (profExp α) P.g P.L)) P.T (ansatzV P) :=
    { solContDiff := hsm.mono (fun q hq => ⟨trivial, ⟨by linarith [hq.2.1], hq.2.2⟩⟩)
      pressureContDiff := hpc
      eq := hpe
      div_free := fun t ht => div_ansatzV P hlwp.law t ⟨by linarith [ht.1], ht.2⟩
      init := ansatzV_zero P }
  -- uniqueness in the Lichtenstein–Gunther class
  have huniq : ∀ x t, t ∈ Set.Ico 0 P.T → ansatzV P x t = u' x t :=
    hlwp.uniqueness _ P.T p p' (ansatzV P) u' hsol
      (isLocalEulerEquationSolution_mono hsol' (le_of_lt hT'))
      (fun S hS => hG S hS)
      (fun S hS => hst' S ⟨hS.1, lt_trans hS.2 hT'⟩)
  -- the strip `[0,(P.T+T')/2]` lies past the blow-up time: the LG class bounds `∇×u'` there
  have hTS : P.T < (P.T + T') / 2 := by linarith
  have hSmem : (P.T + T') / 2 ∈ Set.Ioo (0 : ℝ) T' :=
    ⟨by linarith [P.hT, hT'], by linarith [hT']⟩
  obtain ⟨K, hK0, hK⟩ := vorticity_bound_of_strip (α := α) (u := u') (S := (P.T + T') / 2)
    (T := P.T) hTS (hst' _ hSmem)
  -- hence `bkm u'` is bounded on `[0,P.T)`
  have hbound : ∀ t ∈ Set.Ico 0 P.T, Work.LWP.bkm u' t ≤ K * P.T := by
    intro t ht
    rw [← bkm_congr_of_eqOn_Ico huniq t ht]
    refine bkm_le_of_vortLInf_bound P.hT.le hK0
      (intervalIntegrable_vortLInf_ansatzV P hlwp.law) ?_ t ht
    intro s hs
    apply ciSup_le
    intro x
    have heq : (fun y => ansatzV P y s) = (fun y => u' y s) :=
      funext (fun y => huniq y s hs)
    rw [heq]
    exact hK s hs x
  -- whereas `bkm (ansatzV P)` diverges at `P.T`
  have hdiv := bkm_divergence_of_st5 P hlwp.law
  haveI : NeBot (𝓝[<] P.T) := nhdsWithin_Iio_neBot le_rfl
  have hev : ∀ᶠ t in 𝓝[<] P.T, K * P.T + 1 < Work.LWP.bkm (ansatzV P) t :=
    hdiv.eventually (eventually_gt_atTop _)
  have hevIco : ∀ᶠ t in 𝓝[<] P.T, t ∈ Set.Ico 0 P.T :=
    Work.StabilityFar.BKM.eventually_mem_Ico_nhdsLT P.T P.hT
  obtain ⟨t, hgt, htIco⟩ := (hev.and hevIco).exists
  have h1 := hbound t htIco
  have h2 : Work.LWP.bkm (ansatzV P) t = Work.LWP.bkm u' t :=
    bkm_congr_of_eqOn_Ico huniq t htIco
  linarith

end Work.ConstructionInstance
