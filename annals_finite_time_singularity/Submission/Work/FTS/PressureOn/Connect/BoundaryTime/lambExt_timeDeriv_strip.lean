import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.EulerAssembly
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.ExtData
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.velocity_strip_blocks
import Submission.Work.FTS.PressureOn.Connect.timeDeriv_physVel_continuousOn_strip
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_omega_slice_at
import Submission.Work.FTS.PressureOn.Connect.hasDerivAt_lamb_time
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.lamb_derivWithinAt_zero
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.lambExt_timeDeriv_zero
import Submission.Work.FTS.BSSwirl.CrossAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.PressureOn.Connect.BoundaryTime

noncomputable section

/-! ## Auxiliary facts about the boundary-time retraction of the Lamb vector -/

/-- Continuity of the cross product of two continuous functions with values in `ℝ³`. -/
theorem continuousOn_crossVec {X : Type*} [TopologicalSpace X] {s : Set X} {a b : X → R3}
    (ha : ContinuousOn a s) (hb : ContinuousOn b s) :
    ContinuousOn (fun x => crossVec (a x) (b x)) s := by
  have h1 : ContinuousOn (fun x => Work.FTS.BSSwirl.crossBilin (a x)) s :=
    Work.FTS.BSSwirl.crossBilin.continuous.comp_continuousOn ha
  have h2 := h1.clm_apply hb
  refine h2.congr fun x _ => ?_
  show Work.FTS.BSSwirl.crossBilin (a x) (b x) = crossVec (a x) (b x)
  rw [Work.FTS.BSSwirl.crossBilin_apply, crossVec_apply]
  rfl

/-- The cross product with `0` is `0`. -/
theorem crossVec_zero_right_strip (a : R3) : crossVec a (0 : R3) = 0 := by
  rw [crossVec_apply]
  simp

/-- The time block `tblock ω T` is continuous as a function of the space variable: it is the
evaluation at the fixed time direction `(0,1)` of the (continuous) within derivative of the
velocity on the closed strip `bstrip T`. -/
theorem continuous_tblock {α : NNReal} {ω : R3 → ℝ → R3} {T : ℝ} (hT : 0 < T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α (physVel ω).uncurry
      (Set.univ ×ˢ Set.Icc 0 S')) :
    Continuous (fun y : R3 => tblock ω T y) := by
  have hT2 : T / 2 ∈ Set.Ioo 0 T := ⟨by linarith, by linarith⟩
  obtain ⟨hcd, -, -⟩ := hstrips (T / 2) hT2
  have hU : UniqueDiffOn ℝ (bstrip T) :=
    UniqueDiffOn.prod uniqueDiffOn_univ (uniqueDiffOn_Icc (by linarith : (0 : ℝ) < T / 2))
  have hcont : ContinuousOn (fderivWithin ℝ (physVel ω).uncurry (bstrip T)) (bstrip T) :=
    hcd.continuousOn_fderivWithin hU le_rfl
  have hF : ContinuousOn (fun p : R3 × ℝ =>
      fderivWithin ℝ (physVel ω).uncurry (bstrip T) p ((0 : R3), (1 : ℝ))) (bstrip T) :=
    hcont.clm_apply continuousOn_const
  exact hF.comp_continuous (continuous_id.prodMk continuous_const)
    (fun y => ⟨trivial, ⟨by linarith, by linarith⟩⟩)

/-- **The interior identification of `∂ₜ(lambExt)`.**  At every time `t ∈ (0,T)` the retraction
`lambExt ω T` agrees with the Lamb vector near `t`, so its time derivative is the product rule
`(∂ₜu) × ω + u × (∂ₜω)`. -/
theorem lambExt_timeDeriv_eq_interior {α : NNReal} {ω : R3 → ℝ → R3} {T : ℝ} (hT : 0 < T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α (physVel ω).uncurry
      (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z t) x = ω x t)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2)
      (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x : R3, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (timeDeriv ω x t) (Set.Ici t) t) :
    ∀ (y : R3) (t : ℝ), t ∈ Set.Ioo 0 T →
      timeDeriv (lambExt ω T) y t
        = crossVec (timeDeriv (physVel ω) y t) (ω y t)
          + crossVec (physVel ω y t) (timeDeriv ω y t) := by
  intro y t ht
  obtain ⟨ht0, htT⟩ := ht
  -- the retraction is invisible on a neighbourhood of the positive time `t`
  have hev : (fun s => lambExt ω T y s) =ᶠ[𝓝 t] (fun s => lamb (physVel ω) ω y s) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht0] with s hs
    rw [lambExt, if_neg (not_le.mpr hs)]
  have h1 : timeDeriv (lambExt ω T) y t = timeDeriv (lamb (physVel ω) ω) y t := by
    simpa only [timeDeriv] using hev.deriv_eq
  -- the two factors have genuine two sided derivatives at the interior time `t`
  obtain ⟨S, htS, hST⟩ : ∃ S : ℝ, t < S ∧ S < T := ⟨(t + T) / 2, by linarith, by linarith⟩
  have hS : S ∈ Set.Ioo 0 T := ⟨lt_trans ht0 htS, hST⟩
  have hu : HasDerivAt (fun s => physVel ω y s) (timeDeriv (physVel ω) y t) t :=
    hasDerivAt_physVel_time (x := y) ⟨ht0, htS⟩ (hstrips S hS)
  have hω : HasDerivAt (fun s => ω y s) (timeDeriv ω y t) t :=
    hasDerivAt_omega_slice_at hstrips hcurl hcontDt hderiv ⟨ht0, htT⟩ y
  rw [h1, timeDeriv_lamb hu hω]

/-- **One sided uniqueness of the derivative at `0`.**  If the slice `f` has right derivative `f'`
at `0` (within `Ici 0`) and vanishes for all sufficiently small nonnegative times, then `f' = 0`.
This is what makes the support of `∂ₜω` at the boundary time controlled by the support of `ω`. -/
theorem eq_zero_of_hasDerivWithinAt_of_eventuallyEq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {f' : E} (hf : HasDerivWithinAt f f' (Set.Ici 0) 0)
    (h : f =ᶠ[nhdsWithin 0 (Set.Ici 0)] fun _ => 0) : f' = 0 := by
  have h0 : f 0 = 0 := by
    have h1 : Tendsto f (nhdsWithin 0 (Set.Ici 0)) (𝓝 (0 : E)) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm h)
    have h2 : Tendsto f (nhdsWithin 0 (Set.Ici 0)) (𝓝 (f 0)) := hf.continuousWithinAt
    exact tendsto_nhds_unique h2 h1
  have hc : HasDerivWithinAt (fun _ : ℝ => (0 : E)) f' (Set.Ici 0) 0 :=
    hf.congr_of_eventuallyEq h.symm h0.symm
  have hz : HasDerivWithinAt (fun _ : ℝ => (0 : E)) (0 : E) (Set.Ici 0) 0 :=
    hasDerivWithinAt_const 0 _ 0
  have hf' := UniqueDiffWithinAt.eq (uniqueDiffWithinAt_Ici 0) hc.hasFDerivWithinAt
    hz.hasFDerivWithinAt
  have := ContinuousLinearMap.toSpanSingleton_inj.mp hf'
  simpa using this

/-! ## The main statement -/

theorem lambExt_timeDeriv_strip {α : NNReal}
    {ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3} {T : ℝ} (hT : 0 < T)
    (hstrips : ∀ S' ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (Work.FTS.Physical.physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S'))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x,
      FiniteTimeSingularity.vorticity (fun z => Work.FTS.Physical.physVel ω z t) x = ω x t)
    (hsupp : ∃ R : ℝ, ∀ t ∈ Set.Icc 0 (T / 2), ∀ x : Work.FTS.PressureOn.R3, ω x t ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x : Work.FTS.PressureOn.R3, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (FiniteTimeSingularity.timeDeriv ω x t) (Set.Ici t) t)
    (hωcont : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ => ω p.1 p.2)
      (Work.FTS.PressureOn.Connect.bstrip T))
    (huc : ∀ x : Work.FTS.PressureOn.R3, HasDerivWithinAt
      (fun s => Work.FTS.Physical.physVel ω x s)
      (Work.FTS.PressureOn.Connect.tblock ω T x) (Set.Ici 0) 0)
    (htbc : ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ => if p.2 = 0
        then Work.FTS.PressureOn.Connect.tblock ω T p.1
        else FiniteTimeSingularity.timeDeriv (Work.FTS.Physical.physVel ω) p.1 p.2)
      (Work.FTS.PressureOn.Connect.bstrip T)) :
    ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
        Work.FTS.PressureOn.Connect.lambExt ω T p.1 p.2)
      (Work.FTS.PressureOn.Connect.bstrip T) ∧
    ContinuousOn (fun p : Work.FTS.PressureOn.R3 × ℝ =>
      FiniteTimeSingularity.timeDeriv (Work.FTS.PressureOn.Connect.lambExt ω T) p.1 p.2)
      (Work.FTS.PressureOn.Connect.bstrip T) ∧
    (∀ (y : Work.FTS.PressureOn.R3) (t : ℝ), t ∈ Set.Ioo 0 (T / 2) →
      FiniteTimeSingularity.timeDeriv (Work.FTS.PressureOn.Connect.lambExt ω T) y t
        = FiniteTimeSingularity.timeDeriv
            (Work.FTS.PressureOn.lamb (Work.FTS.Physical.physVel ω) ω) y t) ∧
    (∀ y : Work.FTS.PressureOn.R3, HasDerivWithinAt
      (fun s => Work.FTS.PressureOn.lamb (Work.FTS.Physical.physVel ω) ω y s)
      (Work.FTS.PressureOn.Connect.dtLamb ω T y) (Set.Ici 0) 0) ∧
    (∀ y : Work.FTS.PressureOn.R3,
      FiniteTimeSingularity.timeDeriv (Work.FTS.PressureOn.Connect.lambExt ω T) y 0
        = Work.FTS.PressureOn.Connect.dtLamb ω T y) ∧
    (∀ y : Work.FTS.PressureOn.R3, Work.FTS.PressureOn.Connect.lambExt ω T y 0
        = Work.FTS.PressureOn.lamb (Work.FTS.Physical.physVel ω) ω y 0) ∧
    ContinuousOn (fun y : Work.FTS.PressureOn.R3 => Work.FTS.PressureOn.Connect.dtLamb ω T y)
      Set.univ ∧
    (∀ R : ℝ, (∀ t ∈ Set.Icc 0 (T / 2), ∀ x : Work.FTS.PressureOn.R3, ω x t ≠ 0 → ‖x‖ ≤ R) →
      ∀ y : Work.FTS.PressureOn.R3, R < ‖y‖ →
        Work.FTS.PressureOn.Connect.dtLamb ω T y = 0) := by
  -- elementary time facts
  have hT2pos : (0 : ℝ) < T / 2 := by linarith
  have hT2Ioo : T / 2 ∈ Set.Ioo 0 T := ⟨hT2pos, by linarith⟩
  have hstrip2 : IsContDiffHolderOn ℝ α (physVel ω).uncurry
      (Set.univ ×ˢ Set.Icc 0 (T / 2)) := hstrips (T / 2) hT2Ioo
  have h0mem : (0 : ℝ) ∈ Set.Icc 0 (T / 2) := ⟨le_rfl, hT2pos.le⟩
  -- the elementary continuities on the closed strip
  have hu_c : ContinuousOn (fun p : R3 × ℝ => physVel ω p.1 p.2) (bstrip T) :=
    hstrip2.1.continuousOn
  have hdtω_c : ContinuousOn (fun p : R3 × ℝ => timeDeriv ω p.1 p.2) (bstrip T) :=
    hcontDt.mono fun p hp => ⟨trivial, ⟨hp.2.1, lt_of_le_of_lt hp.2.2 (by linarith)⟩⟩
  have hω_c : ContinuousOn (fun p : R3 × ℝ => ω p.1 p.2) (bstrip T) := hωcont
  -- `tblock` and `dtLamb` are continuous
  have htb_c : Continuous (fun y : R3 => tblock ω T y) := continuous_tblock hT hstrips
  have hdtLamb_c : ContinuousOn (fun y : R3 => dtLamb ω T y) Set.univ := by
    have hω0 : Continuous (fun y : R3 => ω y 0) := by
      have h := hωcont.comp_continuous (continuous_id.prodMk continuous_const)
        (fun y => ⟨trivial, h0mem⟩)
      exact h
    have hdtω0 : Continuous (fun y : R3 => timeDeriv ω y 0) := by
      have h := hcontDt.comp_continuous (continuous_id.prodMk continuous_const)
        (fun y => ⟨trivial, ⟨le_rfl, hT⟩⟩)
      exact h
    have hu0 : Continuous (fun y : R3 => physVel ω y 0) := by
      have h := hu_c.comp_continuous (continuous_id.prodMk continuous_const)
        (fun y => ⟨trivial, h0mem⟩)
      exact h
    have h1 : Continuous (fun y : R3 => crossVec (tblock ω T y) (ω y 0)) := by
      have h := (Work.FTS.BSSwirl.crossBilin.continuous.comp htb_c).clm_apply hω0
      refine h.congr fun y => ?_
      show Work.FTS.BSSwirl.crossBilin (tblock ω T y) (ω y 0)
        = crossVec (tblock ω T y) (ω y 0)
      rw [Work.FTS.BSSwirl.crossBilin_apply, crossVec_apply]
      rfl
    have h2 : Continuous (fun y : R3 => crossVec (physVel ω y 0) (timeDeriv ω y 0)) := by
      have h := (Work.FTS.BSSwirl.crossBilin.continuous.comp hu0).clm_apply hdtω0
      refine h.congr fun y => ?_
      show Work.FTS.BSSwirl.crossBilin (physVel ω y 0) (timeDeriv ω y 0)
        = crossVec (physVel ω y 0) (timeDeriv ω y 0)
      rw [Work.FTS.BSSwirl.crossBilin_apply, crossVec_apply]
      rfl
    have hdtLamb : (fun y : R3 => dtLamb ω T y)
        = fun y => crossVec (tblock ω T y) (ω y 0)
            + crossVec (physVel ω y 0) (timeDeriv ω y 0) := rfl
    rw [hdtLamb]
    exact (h1.add h2).continuousOn
  -- the assembled product field on the strip
  let dtu : R3 × ℝ → R3 := fun p =>
    if p.2 = 0 then tblock ω T p.1 else timeDeriv (physVel ω) p.1 p.2
  let ff : R3 × ℝ → R3 := fun p => crossVec (dtu p) (ω p.1 p.2)
    + crossVec (physVel ω p.1 p.2) (timeDeriv ω p.1 p.2)
  have hdtu_c : ContinuousOn dtu (bstrip T) := htbc
  have hff_c : ContinuousOn ff (bstrip T) :=
    (continuousOn_crossVec hdtu_c hω_c).add (continuousOn_crossVec hu_c hdtω_c)
  -- the pointwise identification of `∂ₜ(lambExt)` with the product field
  have hkey : ∀ p ∈ bstrip T, timeDeriv (lambExt ω T) p.1 p.2 = ff p := by
    rintro ⟨y, t⟩ hp
    obtain ⟨-, ht⟩ := hp
    change timeDeriv (lambExt ω T) y t = ff (y, t)
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · rw [show t = 0 from h0.symm]
      rw [lambExt_timeDeriv_zero huc (fun x => hderiv x 0 ⟨le_rfl, hT⟩) y]
      show dtLamb ω T y = crossVec (if (0 : ℝ) = 0 then tblock ω T y
          else timeDeriv (physVel ω) y 0) (ω y 0)
        + crossVec (physVel ω y 0) (timeDeriv ω y 0)
      rw [if_pos rfl]
      rfl
    · rw [lambExt_timeDeriv_eq_interior hT hstrips hcurl hcontDt hderiv y t
        ⟨hpos, lt_of_le_of_lt ht.2 (by linarith)⟩]
      show crossVec (timeDeriv (physVel ω) y t) (ω y t)
            + crossVec (physVel ω y t) (timeDeriv ω y t)
          = crossVec (if t = 0 then tblock ω T y else timeDeriv (physVel ω) y t) (ω y t)
            + crossVec (physVel ω y t) (timeDeriv ω y t)
      rw [if_neg (ne_of_gt hpos)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the Lamb vector itself
    refine (continuousOn_crossVec hu_c hω_c).congr fun p hp => ?_
    show lambExt ω T p.1 p.2 = crossVec (physVel ω p.1 p.2) (ω p.1 p.2)
    rw [Work.FTS.PressureOn.Connect.lambExt_eq_lamb_on_strip ω T p hp]
    rfl
  · -- the time derivative of the retracted Lamb vector
    exact hff_c.congr hkey
  · -- at positive times the retraction is invisible
    intro y t ht
    have hev : (fun s => lambExt ω T y s) =ᶠ[𝓝 t] (fun s => lamb (physVel ω) ω y s) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht.1] with s hs
      rw [lambExt, if_neg (not_le.mpr hs)]
    simpa only [timeDeriv] using hev.deriv_eq
  · -- the right derivative of the Lamb vector at the boundary time
    intro y
    exact lamb_derivWithinAt_zero (huc y) (hderiv y 0 ⟨le_rfl, hT⟩)
  · -- the two sided derivative of the retraction at the boundary time
    intro y
    exact lambExt_timeDeriv_zero huc (fun x => hderiv x 0 ⟨le_rfl, hT⟩) y
  · -- the retraction fixes the boundary time
    intro y
    rw [lambExt, if_pos le_rfl, zero_smul, add_zero]
  · -- continuity of `dtLamb`
    exact hdtLamb_c
  · -- the support of `dtLamb` is controlled by the support of `ω`
    intro R hR y hRy
    have hω0 : ω y 0 = 0 := by
      by_contra hne
      exact absurd (hR 0 h0mem y hne) (not_le.mpr hRy)
    have hωz : ∀ s ∈ Set.Icc (0 : ℝ) (T / 2), ω y s = 0 := by
      intro s hs
      by_contra hne
      exact absurd (hR s hs y hne) (not_le.mpr hRy)
    have hmem : Set.Icc (0 : ℝ) (T / 2) ∈ 𝓝[Set.Ici (0 : ℝ)] 0 := by
      rw [mem_nhdsWithin_iff_eventually]
      filter_upwards [Iio_mem_nhds hT2pos] with s hs h0
      exact ⟨h0, hs.le⟩
    have hev : (fun s => ω y s) =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0] (fun _ => 0) := by
      filter_upwards [hmem] with s hs
      exact hωz s hs
    have hdtω0 : timeDeriv ω y 0 = 0 :=
      eq_zero_of_hasDerivWithinAt_of_eventuallyEq_zero (hderiv y 0 ⟨le_rfl, hT⟩) hev
    rw [dtLamb, hω0, hdtω0, crossVec_zero_right_strip, crossVec_zero_right_strip, add_zero]

end

end Work.FTS.PressureOn.Connect.BoundaryTime
