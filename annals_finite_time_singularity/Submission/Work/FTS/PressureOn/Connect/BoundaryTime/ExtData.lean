/-
# The pieces of `q = potOn ω` on the strip `ℝ³ × [0,T/2]`

This module collects the (easy) continuity statements on the strip used by the boundary `C¹`
analysis of `Connect.contDiffWithinAt_potOn_at_zero`:

* `bstripO` — the half open strip `ℝ³ × [0,T/2)`, and `bbox` — the closed box
  `B(x₀,1) × [0,T/2)`;
* `lambExt_eq_lamb_on_strip`, `potTDerivExt_eq_potTDeriv` — the identifications of the retracted
  objects of `Connect/BoundaryTime.lean` with the original ones at nonnegative times;
* `velocity_timeblock_continuousOn_strip` — continuity of the `(0,1)` block of the within
  derivative of the velocity on the half open strip (at interior times it is the two sided
  `timeDeriv`, at the boundary time `0` it is the right derivative `tblock`);
* `potGradExt_continuousOn_strip` — the continuity of the space gradient `∂ₜu - u×ω` up to the
  boundary time;
* `potOn_uncurry_continuousOn_strip` — the joint continuity of the potential itself on the closed
  strip, from the Newtonian potential of the time-clamped Lamb vector.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.EulerAssembly
import Submission.Work.FTS.PressureOn.Connect.Deriv
import Submission.Work.FTS.PressureOn.Connect.Clamp
import Submission.Work.FTS.PressureOn.Connect.Data
import Submission.Work.FTS.PressureOn.continuous_timeDeriv_pressurePotential
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.Basic
import Submission.Work.FTS.PressureOn.Connect.omega_strip_continuousOn
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.velocity_strip_blocks

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

noncomputable section

/-- The half open strip `ℝ³ × [0,T/2)` on which the boundary analysis is carried out. -/
def bstripO (T : ℝ) : Set (R3 × ℝ) := Set.univ ×ˢ Set.Ico 0 (T / 2)

/-- The box `B(x₀,1) × [0,T/2)` on which the boundary `C¹` statement is proved. -/
def bbox (x₀ : R3) (T : ℝ) : Set (R3 × ℝ) := Metric.ball x₀ 1 ×ˢ Set.Ico 0 (T / 2)

theorem bstripO_subset_bstrip (T : ℝ) : bstripO T ⊆ bstrip T :=
  Set.prod_mono (subset_refl _) fun _ hx => ⟨hx.1, hx.2.le⟩

theorem bbox_subset_bstripO (x₀ : R3) (T : ℝ) : bbox x₀ T ⊆ bstripO T :=
  Set.prod_mono (Set.subset_univ _) (subset_refl _)

/-! ## Elementary identifications -/

/-- On the closed strip `bstrip T` the retracted Lamb vector agrees with the Lamb vector. -/
theorem lambExt_eq_lamb_on_strip (ω : R3 → ℝ → R3) (T : ℝ) :
    ∀ p ∈ bstrip T, lambExt ω T p.1 p.2 = lamb (physVel ω) ω p.1 p.2 := by
  rintro ⟨y, t⟩ ⟨-, ht⟩
  rw [lambExt]
  by_cases h : t ≤ 0
  · rw [if_pos h, le_antisymm h ht.1, zero_smul, add_zero]
  · rw [if_neg h]

/-- The extended time derivative of the potential agrees with `potTDeriv` at positive times. -/
theorem potTDerivExt_eq_potTDeriv (ω : R3 → ℝ → R3) (T : ℝ) (x : R3) {t : ℝ} (ht : 0 < t) :
    potTDerivExt ω T x t = potTDeriv ω x t := by
  rw [potTDerivExt, potTDeriv]
  congr 1
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun y => ?_)
  refine congrArg (fun z => inner ℝ (nablaNfund (x - y)) z) ?_
  have hev : (fun s => lambExt ω T y s) =ᶠ[𝓝 t] (fun s => lamb (physVel ω) ω y s) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    rw [lambExt, if_neg (not_le.mpr hs)]
  simpa only [timeDeriv] using hev.deriv_eq

variable {α : NNReal} {ω : R3 → ℝ → R3} {T : ℝ}

/-! ## Continuity of the pieces -/

/-- The uncurried potential is continuous on the closed strip: it is the Newtonian potential of the
clamped Lamb vector, and the clamping is invisible there. -/
theorem potOn_uncurry_continuousOn_strip (hT : 0 < T)
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z t) x = ω x t)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ t ∈ Set.Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R) :
    ContinuousOn (fun p : R3 × ℝ => potOn ω p.1 p.2) (bstrip T) := by
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  have hT2Ioo : T / 2 ∈ Set.Ioo 0 T := ⟨hT2, by linarith⟩
  have hcd : ContDiffOn ℝ 1 (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 (T / 2)) :=
    (hstrips (T / 2) hT2Ioo).1
  have hωc : ContinuousOn (Function.uncurry ω) (Set.univ ×ˢ Set.Icc 0 (T / 2)) :=
    omega_strip_continuousOn_aux hT2Ioo hstrips hcurl
  have hlambc : ContinuousOn (fun p : R3 × ℝ => lamb (physVel ω) ω p.1 p.2)
      (Set.univ ×ˢ Set.Icc 0 (T / 2)) := by
    have h1 : (fun p : R3 × ℝ => lamb (physVel ω) ω p.1 p.2)
        = fun p => BSSwirl.crossBilin (physVel ω p.1 p.2) (ω p.1 p.2) := rfl
    rw [h1]
    exact (BSSwirl.crossBilin.continuous.comp_continuousOn hcd.continuousOn).clm_apply hωc
  have hclamp : Continuous (Function.uncurry (extendTime (lamb (physVel ω) ω) (T / 2))) :=
    continuous_uncurry_extendTime_aux hT2.le hlambc
  obtain ⟨R, hR⟩ := hsupp (T / 2) hT2Ioo
  have hsupp' : ∀ t : ℝ, ∃ R' : ℝ, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ x,
      extendTime (lamb (physVel ω) ω) (T / 2) x s ≠ 0 → ‖x‖ ≤ R' := by
    refine fun t => ⟨R, fun s _ x hx => ?_⟩
    rw [extendTime_apply] at hx
    refine hR _ (clampt_mem_Icc hT2.le s) x fun h => hx ?_
    exact lamb_eq_zero_of_right_eq_zero h
  have hmain := continuous_pressurePotential_joint_of_supported hclamp hsupp'
  refine hmain.continuousOn.congr fun p hp => ?_
  obtain ⟨x, t⟩ := p
  obtain ⟨-, ht⟩ := hp
  show potOn ω x t = pressurePotential (fun y => extendTime (lamb (physVel ω) ω) (T / 2) y t) x
  rw [potOn]
  congr 1
  funext y
  rw [extendTime_apply, clampt_eq_self_of_mem ht]

/-- The time block of the velocity is continuous on the half open strip, in the form of the
function which is `timeDeriv` at positive times and the right derivative `tblock` at `t = 0`. -/
theorem velocity_timeblock_continuousOn_strip (hT : 0 < T)
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z t) x = ω x t) :
    ContinuousOn (fun p : R3 × ℝ =>
      if p.2 = 0 then tblock ω T p.1 else timeDeriv (physVel ω) p.1 p.2) (bstripO T) := by
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  have hT2Ioo : T / 2 ∈ Set.Ioo 0 T := ⟨hT2, by linarith⟩
  have hblocks := BoundaryTime.velocity_strip_blocks (ω := ω) (T := T) (S := T / 2)
    hT2Ioo hstrips hcurl
  refine (hblocks.1.mono (bstripO_subset_bstrip T)).congr fun p hp => ?_
  obtain ⟨y, s⟩ := p
  obtain ⟨-, hs⟩ := hp
  by_cases h : s = 0
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h]
    exact (hblocks.2.1 y s ⟨lt_of_le_of_ne hs.1 (Ne.symm h), hs.2⟩).symm

/-- The extended space gradient is continuous on the half open strip. -/
theorem potGradExt_continuousOn_strip (hT : 0 < T)
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z t) x = ω x t) :
    ContinuousOn (potGradExt ω T) (bstripO T) := by
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  have hT2Ioo : T / 2 ∈ Set.Ioo 0 T := ⟨hT2, by linarith⟩
  have hcd : ContDiffOn ℝ 1 (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 (T / 2)) :=
    (hstrips (T / 2) hT2Ioo).1
  have hωc : ContinuousOn (Function.uncurry ω) (bstrip T) :=
    omega_strip_continuousOn_aux hT2Ioo hstrips hcurl
  have huc : ContinuousOn (Function.uncurry (physVel ω)) (bstrip T) := hcd.continuousOn
  have hcross : ContinuousOn (fun p : R3 × ℝ => crossVec (physVel ω p.1 p.2) (ω p.1 p.2))
      (bstrip T) := by
    have h : (fun p : R3 × ℝ => crossVec (physVel ω p.1 p.2) (ω p.1 p.2))
        = fun p => BSSwirl.crossBilin (physVel ω p.1 p.2) (ω p.1 p.2) := rfl
    rw [h]
    exact (BSSwirl.crossBilin.continuous.comp_continuousOn huc).clm_apply hωc
  have htb := velocity_timeblock_continuousOn_strip (ω := ω) (T := T) hT hstrips hcurl
  refine (htb.sub (hcross.mono (bstripO_subset_bstrip T))).congr fun p hp => ?_
  obtain ⟨y, s⟩ := p
  simp only [potGradExt, Pi.sub_apply]
  by_cases h : s = 0
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h]

/-- The time block of the velocity is continuous on the *closed* strip, in the form of the function
which is `timeDeriv` at positive times and the right derivative `tblock` at `t = 0`.  (At the
boundary time the two descriptions differ only on the hyperplane `t = T/2`, which is not
approached; at positive times the within strip agrees locally with the open strip on which the
joint `timeDeriv` is continuous.) -/
theorem velocity_timeblock_continuousOn_closedStrip (hT : 0 < T)
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z t) x = ω x t) :
    ContinuousOn (fun p : R3 × ℝ =>
      if p.2 = 0 then tblock ω T p.1 else timeDeriv (physVel ω) p.1 p.2) (bstrip T) := by
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  have hT2Ioo : T / 2 ∈ Set.Ioo 0 T := ⟨hT2, by linarith⟩
  obtain ⟨S', hS'g, hS'l⟩ : ∃ S' : ℝ, T / 2 < S' ∧ S' < T :=
    ⟨(T / 2 + T) / 2, by linarith, by linarith⟩
  have hS'0 : 0 < S' := by linarith
  have hblocks := BoundaryTime.velocity_strip_blocks (ω := ω) (T := T) (S := T / 2)
    hT2Ioo hstrips hcurl
  have hF : ContinuousOn (fun p : R3 × ℝ =>
      fderivWithin ℝ (physVel ω).uncurry (bstrip T) p (0, 1)) (bstrip T) := hblocks.1
  have htd : ContinuousOn (fun p : R3 × ℝ => timeDeriv (physVel ω) p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 S') :=
    timeDeriv_physVel_continuousOn_strip_aux hS'0 (hstrips S' ⟨hS'0, hS'l⟩)
  intro p hp
  have hpT : p.2 ≤ T / 2 := hp.2.2
  rcases eq_or_lt_of_le hp.2.1 with h0 | hpos
  · have hsub : Set.univ ×ˢ Set.Ioo (-1) (T / 2) ∈ 𝓝 p :=
      prod_mem_nhds univ_mem (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
    have hev : (fun q : R3 × ℝ =>
          if q.2 = 0 then tblock ω T q.1 else timeDeriv (physVel ω) q.1 q.2)
        =ᶠ[𝓝[bstrip T] p] (fun q : R3 × ℝ =>
          fderivWithin ℝ (physVel ω).uncurry (bstrip T) q (0, 1)) := by
      filter_upwards [mem_of_superset (mem_nhdsWithin_of_mem_nhds hsub)
          (show (Set.univ ×ˢ Set.Ioo (-1) (T / 2)) ⊆ {q : R3 × ℝ | q.2 < T / 2} from
            fun q hq => hq.2.2),
        self_mem_nhdsWithin] with q hqT hqb
      by_cases hq0 : q.2 = 0
      · rw [if_pos hq0]
        have hqeq : q = (q.1, 0) := Prod.ext rfl hq0
        rw [hqeq]
        rfl
      · rw [if_neg hq0]
        exact (hblocks.2.1 q.1 q.2 ⟨lt_of_le_of_ne hqb.2.1 (Ne.symm hq0), hqT⟩).symm
    exact (hF.continuousWithinAt hp).congr_of_eventuallyEq_of_mem hev hp
  · have hmem : Set.univ ×ˢ Set.Ioo (0 : ℝ) S' ∈ 𝓝[bstrip T] p := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨Set.univ ×ˢ Set.Ioo (p.2 / 2) (S' + 1), ?_, ?_⟩
      · refine prod_mem_nhds univ_mem (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith [hpT, hS'g]⟩)
      · rintro ⟨z, s⟩ ⟨⟨-, hs⟩, ⟨-, hsb⟩⟩
        exact ⟨trivial, ⟨by linarith [hs.1, hpos],
          lt_of_le_of_lt hsb.2 (by linarith [hpT, hS'g])⟩⟩
    have hp' : p ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) S' :=
      ⟨trivial, hpos, lt_of_le_of_lt hpT hS'g⟩
    have hev : (fun q : R3 × ℝ =>
          if q.2 = 0 then tblock ω T q.1 else timeDeriv (physVel ω) q.1 q.2)
        =ᶠ[𝓝[bstrip T] p] (fun q : R3 × ℝ => timeDeriv (physVel ω) q.1 q.2) := by
      filter_upwards [mem_of_superset hmem
        (show (Set.univ ×ˢ Set.Ioo (0 : ℝ) S') ⊆ {q : R3 × ℝ | 0 < q.2} from
          fun q hq => hq.2.1)] with q hqpos
      rw [if_neg (ne_of_gt hqpos)]
    exact (ContinuousWithinAt.congr_of_eventuallyEq_of_mem
      (Filter.Tendsto.mono_left (htd.continuousWithinAt hp') (nhdsWithin_le_iff.mpr hmem))
      hev hp)

end

end Work.FTS.PressureOn.Connect
