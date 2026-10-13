import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.EulerAssembly
import Submission.Work.FTS.PressureOn.weyl_pair
import Submission.Work.FTS.PressureOn.weakPoisson
import Submission.Work.FTS.PressureOn.weakDiv_timeDeriv
import Submission.Work.FTS.PressureOn.weakCurl_pair
import Submission.Work.FTS.PressureOn.Connect.Clamp
import Submission.Work.FTS.PressureOn.Connect.Data
import Submission.Work.FTS.PressureOn.Connect.weakDiv_pair
import Submission.Work.FTS.PressureOn.Connect.lipschitz_extendTime
import Submission.Work.FTS.PressureOn.Connect.lamb_lipschitz_near
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_physVel_time
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_lamb_time
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_of_hasDerivWithinAt_Ici
import Submission.Work.FTS.PressureOn.Connect.continuous_timeDeriv_slice
import Submission.Work.FTS.PressureOn.Connect.biotSavart_uniform_bound
import Submission.Work.FTS.PressureOn.tendsto_lamb_decay
import Submission.Work.FTS.PressureOn.pressurePotential_basic
import Submission.Work.FTS.PressureOn.lipschitz_time_lamb_strips
import Submission.Work.FTS.PressureOn.omegaSliceRegularPos
import Submission.Work.FTS.PressureOn.continuousOn_time_omega_of_strips
import Submission.Work.FTS.PressureOn.div_vorticity_mul_eq_zero
import Submission.Work.FTS.BSSwirl.CrossAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter
open Work.FTS.Physical (physVel)

namespace Work.FTS.PressureOn.Connect

/-- The directional derivative is unchanged when the time variable is clamped, at an interior
time.  Companion of `timeDeriv_extendTime`. -/
theorem directionalDeriv_extendTime {v w : R3 → ℝ → R3}
    {S t : ℝ} (ht : t ∈ Set.Ioo 0 S) (x : R3) :
    FiniteTimeSingularity.directionalDeriv (extendTime v S) (extendTime w S) x t
      = FiniteTimeSingularity.directionalDeriv v w x t := by
  have htIcc : t ∈ Set.Icc (0 : ℝ) S := ⟨ht.1.le, ht.2.le⟩
  unfold FiniteTimeSingularity.directionalDeriv
  rw [show (extendTime v S · t) = (v · t) from funext (fun y => by
        rw [extendTime_apply, clampt_eq_self_of_mem htIcc]),
      extendTime_apply, clampt_eq_self_of_mem htIcc]

theorem hasFDerivAt_potOn_slice {α : NNReal} {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {T : ℝ}
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z t) x = ω x t)
    (hdiv : ∀ t ∈ Set.Ico 0 T,
      FiniteTimeSingularity.div (fun z => Work.FTS.Physical.physVel ω z t) = 0)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ t ∈ Set.Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x t) (Set.Ici t) t)
    (hfderiv : ∀ t ∈ Set.Ioo 0 T, MeasureTheory.LocallyIntegrable (fun x => fderiv ℝ (ω · t) x))
    (hpointwise : ∀ t ∈ Set.Ioo 0 T, ∀ x ∈ Work.FTS.PressureOn.Uax,
      ContDiffAt ℝ 2 (fun z => Work.FTS.Physical.physVel ω z t) x ∧
      ContDiffAt ℝ 1 (fun z => ω z t) x ∧
      FiniteTimeSingularity.timeDeriv ω x t
        + FiniteTimeSingularity.directionalDeriv ω (Work.FTS.Physical.physVel ω) x t
        = FiniteTimeSingularity.directionalDeriv (Work.FTS.Physical.physVel ω) ω x t)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) (x : Work.FTS.PressureOn.R3) :
    HasFDerivAt (Work.FTS.PressureOn.potOn ω · t)
      (innerSL ℝ (FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) x t
        - Work.FTS.PressureOn.crossVec (Work.FTS.Physical.physVel ω x t) (ω x t))) x := by
  obtain ⟨ht0, htT⟩ := ht
  -- an interior time `S ∈ (t,T)`: all windowed machinery is used there
  obtain ⟨S, htS, hStT, hS0⟩ :
      ∃ S : ℝ, t < S ∧ S < T ∧ 0 < S := ⟨(t + T) / 2, by linarith, by linarith, by linarith⟩
  have hSIoo : S ∈ Set.Ioo 0 T := ⟨hS0, hStT⟩
  have hIoo : t ∈ Set.Ioo 0 S := ⟨ht0, htS⟩
  have hIcc : t ∈ Set.Icc (0 : ℝ) S := ⟨ht0.le, htS.le⟩
  have hIco : t ∈ Set.Ico (0 : ℝ) S := ⟨ht0.le, htS⟩
  have hstripS := hstrips S hSIoo
  -- ## Step 1: the slices at time `t`
  have hu_cd : ContDiff ℝ 1 (physVel ω · t) :=
    contDiff_slice_of_isContDiffHolderOn hstripS hIcc
  have hu_cont : Continuous (fun y => physVel ω y t) := hu_cd.continuous
  have hω_cont : Continuous (fun y => ω y t) :=
    continuous_vorticity_slice hStT hIcc hstripS hcurl
  have hcross_cont : Continuous (fun y => crossVec (physVel ω y t) (ω y t)) := by
    have h : (fun y => crossVec (physVel ω y t) (ω y t))
        = fun y => Work.FTS.BSSwirl.crossBilin (physVel ω y t) (ω y t) := rfl
    rw [h]
    exact (Work.FTS.BSSwirl.crossBilin.continuous.comp hu_cont).clm_apply hω_cont
  have hlamb_cont : Continuous (fun y => lamb (physVel ω) ω y t) := hcross_cont
  have htd_cont : Continuous (fun y => FiniteTimeSingularity.timeDeriv (physVel ω) y t) :=
    continuous_timeDeriv_slice hIoo hstripS
  -- ## Step 2: the potential `q = potOn ω · t` and the field `Φ = ∂ₜu - u×ω`
  obtain ⟨R0, hR0⟩ := hsupp S hSIoo
  have hlamb_cs : HasCompactSupport (fun y => lamb (physVel ω) ω y t) :=
    hasCompactSupport_lamb_slice (u := physVel ω) (fun y hy => hR0 t hIcc y hy)
  have hpb := pressurePotential_basic hlamb_cont hlamb_cs
  have hq : Continuous (potOn ω · t) := hpb.1
  have hq0 : Filter.Tendsto (potOn ω · t) (Filter.cocompact _) (nhds 0) := hpb.2.2
  have hΦ_cont : Continuous (fun y => FiniteTimeSingularity.timeDeriv (physVel ω) y t
      - crossVec (physVel ω y t) (ω y t)) := htd_cont.sub hcross_cont
  have hΦ0 : Filter.Tendsto (fun y => FiniteTimeSingularity.timeDeriv (physVel ω) y t
      - crossVec (physVel ω y t) (ω y t)) (Filter.cocompact _) (nhds 0) :=
    tendsto_lamb_decay hSIoo hIco hstrips hcurl (hsupp S hSIoo) hcontDt hderiv
  -- ## Step 3: the Lipschitz-in-time bounds, transferred to the clamped fields
  obtain ⟨hωLipIcc, huLipIcc⟩ :=
    lipschitz_time_lamb_strips hSIoo hIcc hstrips hcurl (hsupp S hSIoo) hcontDt hderiv
  obtain ⟨Cu, hCulip⟩ := huLipIcc
  obtain ⟨Cω, hCωlip⟩ := hωLipIcc
  have hCulip' : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      ‖extendTime (physVel ω) S y s - extendTime (physVel ω) S y t‖ ≤ Cu * |s - t| :=
    fun y s _ => lipschitz_extendTime hS0.le (nonneg_of_lipschitz ht0.le htS hCulip) hIcc hCulip y s
  have hCωlip' : ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      ‖extendTime ω S y s - extendTime ω S y t‖ ≤ Cω * |s - t| :=
    fun y s _ => lipschitz_extendTime hS0.le (nonneg_of_lipschitz ht0.le htS hCωlip) hIcc hCωlip y s
  -- ## Step 4: the weak divergence identity for `(q, Φ)`
  have hweakDiv : ∀ φ : R3 → ℝ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
      ∫ y, inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t
          - crossVec (physVel ω y t) (ω y t)) (gradient φ y)
        = -∫ y, potOn ω y t * laplaceTrace φ y := by
    intro φ hφ hφcs
    -- `∫ ⟪∂ₜu, ∇φ⟫ = 0`, from the divergence-free condition on the clamped field
    have hcore : ∫ y, inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t)
        (gradient φ y) = 0 := by
      have h := weakDiv_timeDeriv (u := extendTime (physVel ω) S) (t := t) (φ := φ) hφ hφcs
        (Filter.Eventually.of_forall fun s => ⟨contDiff_extendTime_slice hS0.le hstripS s,
          div_extendTime hSIoo hdiv s⟩)
        (fun y => hasDerivWithinAt_extendTime hIoo
          (fun y => (hasDerivAt_physVel_time hIoo hstripS).hasDerivWithinAt) y)
        ⟨Cu, hCulip'⟩
      simpa only [timeDeriv_extendTime hIoo] using h
    exact weakDiv_pair (u := physVel ω) (ω := ω) (t := t) (φ := φ) hφ hφcs
      hlamb_cont htd_cont hcore (weakPoisson hlamb_cont hlamb_cs hφ hφcs)
  -- ## Step 5: the weak curl identity for `(q, Φ)`
  have hweakCurl : ∀ ψ : R3 → R3, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      ∫ y, inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t
          - crossVec (physVel ω y t) (ω y t)) (FiniteTimeSingularity.vorticity ψ y) = 0 := by
    intro ψ hψ hψcs
    have hclampωt : (fun z => extendTime ω S z t) = fun z => ω z t :=
      funext fun z => by rw [extendTime_apply, clampt_eq_self_of_mem hIcc]
    have hclampedt : (fun z => extendTime (physVel ω) S z t) = fun z => physVel ω z t :=
      funext fun z => by rw [extendTime_apply, clampt_eq_self_of_mem hIcc]
    have hRclamp : ∃ R : ℝ, 0 ≤ R ∧ ∀ s ∈ Set.Ioo (t - 1) (t + 1),
        ∀ y, extendTime ω S y s ≠ 0 → ‖y‖ ≤ R :=
      ⟨max R0 0, le_max_right _ _, fun s _ y hy => by
        rw [extendTime_apply] at hy
        exact le_trans (hR0 (clampt S s) (clampt_mem_Icc hS0.le s) y hy) (le_max_left _ _)⟩
    have hwc := weakCurl_pair (u := extendTime (physVel ω) S) (ω := extendTime ω S)
      (t := t) (A := ψ) hψ hψcs hRclamp
      (fun s _ => contDiff_extendTime_slice hS0.le hstripS s)
      (fun s _ y => congrFun (vorticity_extendTime hSIoo hcurl s) y)
      (fun s _ => div_extendTime hSIoo hdiv s)
      (by rw [hclampωt]; exact hω_cont)
      (fun y hy0 hy2 => by
        rw [hclampωt]
        have hxU : y ∈ Uax := ⟨hy2, by
          intro hsum
          have h2 : 0 < y 0 ^ 2 := sq_pos_of_ne_zero hy0
          nlinarith [sq_nonneg (y 1)]⟩
        exact ((hpointwise t ⟨ht0, htT⟩ y hxU).2.1.differentiableAt (by simp)).hasFDerivAt)
      (by rw [hclampωt]; exact hfderiv t ⟨ht0, htT⟩)
      (fun y => hasDerivWithinAt_extendTime hIoo
        (fun y => (hasDerivAt_physVel_time hIoo hstripS).hasDerivWithinAt) y)
      (fun y => hasDerivWithinAt_extendTime hIoo
        (fun y => hderiv y t ⟨ht0.le, htT⟩) y)
      ⟨Cu, hCulip'⟩ ⟨Cω, hCωlip'⟩
      (fun y hy => by
        rw [timeDeriv_extendTime hIoo y,
          directionalDeriv_extendTime (v := ω) (w := physVel ω) hIoo y,
          directionalDeriv_extendTime (v := physVel ω) (w := ω) hIoo y]
        exact (hpointwise t ⟨ht0, htT⟩ y hy).2.2)
    -- undo the clamping inside the two integrals
    have h1 : (fun y => inner ℝ (FiniteTimeSingularity.timeDeriv (extendTime (physVel ω) S) y t)
          (FiniteTimeSingularity.vorticity ψ y))
        = fun y => inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t)
          (FiniteTimeSingularity.vorticity ψ y) :=
      funext fun y => by rw [timeDeriv_extendTime hIoo y]
    have h2 : (fun y => inner ℝ (crossVec (extendTime (physVel ω) S y t) (extendTime ω S y t))
          (FiniteTimeSingularity.vorticity ψ y))
        = fun y => inner ℝ (crossVec (physVel ω y t) (ω y t))
          (FiniteTimeSingularity.vorticity ψ y) :=
      funext fun y => by rw [congrFun hclampedt y, congrFun hclampωt y]
    rw [h1, h2] at hwc
    -- integrability of the two pairings
    have hvort := Work.FTS.BSSwirl.contDiff_vorticity_and_support hψ hψcs
    have hint1 : Integrable (fun y => inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t)
        (FiniteTimeSingularity.vorticity ψ y)) :=
      (htd_cont.inner (hvort.1 0).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_inner_right _ hvort.2 _)
    have hint2 : Integrable (fun y => inner ℝ (crossVec (physVel ω y t) (ω y t))
        (FiniteTimeSingularity.vorticity ψ y)) :=
      (hcross_cont.inner (hvort.1 0).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_inner_right _ hvort.2 _)
    have hpt : (fun y => inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t
          - crossVec (physVel ω y t) (ω y t)) (FiniteTimeSingularity.vorticity ψ y))
        = fun y => inner ℝ (FiniteTimeSingularity.timeDeriv (physVel ω) y t)
            (FiniteTimeSingularity.vorticity ψ y)
          - inner ℝ (crossVec (physVel ω y t) (ω y t)) (FiniteTimeSingularity.vorticity ψ y) :=
      funext fun y => inner_sub_left _ _ _
    rw [hpt, integral_sub hint1 hint2, hwc]
    ring
  -- ## Step 6: the Weyl/Liouville pair lemma
  exact weyl_pair (potOn ω · t)
    (fun y => FiniteTimeSingularity.timeDeriv (physVel ω) y t
      - crossVec (physVel ω y t) (ω y t))
    hq hΦ_cont hq0 hΦ0 hweakDiv hweakCurl x

end Work.FTS.PressureOn.Connect
