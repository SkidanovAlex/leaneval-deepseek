import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.EulerAssembly
import Submission.Work.FTS.PressureOn.Connect.Deriv
import Submission.Work.FTS.PressureOn.Connect.hasFDerivAt_uncurry_of_partials_corrected
import Submission.Work.FTS.PressureOn.Connect.contDiffWithinAt_one_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.Basic
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.Grad
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.PotOnTime
import Submission.Work.FTS.PressureOn.Connect.ctu_aux.PotTDeriv
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.ExtData
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.lambExt_timeDeriv_strip
import Submission.Work.FTS.PressureOn.Connect.BoundaryTime.continuousOn_timeDeriv_strip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The extended derivative field of `q = potOn ω` on the closed strip

* `potTDerivExt_continuousOn_strip` — the time derivative of the potential, extended to the
  boundary time (via the retracted Lamb vector `lambExt` and the half open dominated convergence
  lemma `continuousOn_timeDeriv_strip`);
* `potFDerivExt_continuousOn_strip` — the resulting full derivative field, continuous on the
  closed strip;
* `hasFDerivAt_potOn_uncurry_interior` — at interior times the uncurried potential is
  differentiable with derivative `potFDerivExt` (the "continuous partials" criterion in the
  corrected form of this area).
-/

open FiniteTimeSingularity Set MeasureTheory Filter
open Work.FTS.Physical (physVel)
open scoped Topology NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.PressureOn.Connect

noncomputable section

variable {α : NNReal} {ω : R3 → ℝ → R3} {T : ℝ}

theorem potTDerivExt_continuousOn_strip (hT : 0 < T)
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z t) x = ω x t)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ t ∈ Set.Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (timeDeriv ω x t) (Set.Ici t) t) :
    ContinuousOn (fun p : R3 × ℝ => potTDerivExt ω T p.1 p.2) (bstrip T) := by
  have hT2 : (0 : ℝ) < T / 2 := by linarith
  have hT2Ioo : T / 2 ∈ Set.Ioo 0 T := ⟨hT2, by linarith⟩
  obtain ⟨R, hR⟩ := hsupp (T / 2) hT2Ioo
  have hωc : ContinuousOn (Function.uncurry ω) (bstrip T) :=
    omega_strip_continuousOn_aux hT2Ioo hstrips hcurl
  have htb := velocity_timeblock_continuousOn_closedStrip (ω := ω) (T := T) hT hstrips hcurl
  have huc : ∀ x : R3, HasDerivWithinAt (fun s => physVel ω x s) (tblock ω T x) (Set.Ici 0) 0 :=
    fun x => (BoundaryTime.velocity_strip_blocks (ω := ω) (T := T) (S := T / 2) hT2Ioo hstrips hcurl).2.2 x
  have hsuppE : ∃ R' : ℝ, ∀ s ∈ Set.Icc 0 (T / 2), ∀ y, lambExt ω T y s ≠ 0 → ‖y‖ ≤ R' := by
    refine ⟨R, fun s hs y hy => hR s hs y fun h => hy ?_⟩
    have h1 : lambExt ω T y s = lamb (physVel ω) ω y s :=
      lambExt_eq_lamb_on_strip ω T (y, s) ⟨trivial, hs⟩
    rw [h1]
    exact lamb_eq_zero_of_right_eq_zero h
  have hlamb := BoundaryTime.lambExt_timeDeriv_strip hT hstrips hcurl ⟨R, hR⟩ hcontDt hderiv hωc
    huc htb
  exact BoundaryTime.continuousOn_timeDeriv_strip hT2 hlamb.1 hlamb.2.1 hsuppE
/-- The full extended derivative field is continuous on the half open strip. -/
theorem potFDerivExt_continuousOn_strip (hT : 0 < T)
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z t) x = ω x t)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ t ∈ Set.Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (timeDeriv ω x t) (Set.Ici t) t) :
    ContinuousOn (potFDerivExt ω T) (bstripO T) := by
  have hgrad := potGradExt_continuousOn_strip (α := α) hT hstrips hcurl
  have hΦ := (potTDerivExt_continuousOn_strip (α := α) hT hstrips hcurl hsupp hcontDt
    hderiv).mono (bstripO_subset_bstrip T)
  have h1 : ContinuousOn (fun p : R3 × ℝ =>
      (innerSL ℝ (potGradExt ω T p)).comp (ContinuousLinearMap.fst ℝ R3 ℝ)) (bstripO T) :=
    ((innerSL ℝ).continuous.comp_continuousOn hgrad).clm_comp continuousOn_const
  have h2 : ContinuousOn (fun p : R3 × ℝ =>
      (potTDerivExt ω T p.1 p.2) • (ContinuousLinearMap.snd ℝ R3 ℝ)) (bstripO T) :=
    hΦ.smul continuousOn_const
  refine (h1.add h2).congr fun p hp => ?_
  rw [potFDerivExt, smulRight_snd_eq_smul']
  rfl

/-! ## The derivative at interior points -/

/-- At interior points the uncurried potential is differentiable with derivative `potFDerivExt`. -/
theorem hasFDerivAt_potOn_uncurry_interior
    (hstrips : ∀ S ∈ Set.Ioo 0 T, IsContDiffHolderOn ℝ α
      (physVel ω).uncurry (Set.univ ×ˢ Set.Icc 0 S))
    (hcurl : ∀ t ∈ Set.Ico 0 T, ∀ x, vorticity (fun z => physVel ω z t) x = ω x t)
    (hsupp : ∀ S ∈ Set.Ioo 0 T, ∃ R, ∀ t ∈ Set.Icc 0 S, ∀ x, ω x t ≠ 0 → ‖x‖ ≤ R)
    (hcontDt : ContinuousOn (fun q : R3 × ℝ => timeDeriv ω q.1 q.2) (Set.univ ×ˢ Set.Ico 0 T))
    (hderiv : ∀ x, ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (ω x) (timeDeriv ω x t) (Set.Ici t) t)
    (hgq : ∀ t ∈ Set.Ioo 0 T, ∀ x, HasFDerivAt (potOn ω · t) (potGradCLM ω x t) x)
    {y : R3} {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    HasFDerivAt (fun p : R3 × ℝ => potOn ω p.1 p.2) (potFDerivExt ω T (y, t)) (y, t) := by
  have hx : HasFDerivAt (fun z => potOn ω z t) (potGradCLM ω y t) y := hgq t ht y
  have ht' : HasDerivAt (fun s => potOn ω y s) (potTDeriv ω y t) t :=
    hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv y ht
  have hnhds : (Set.univ ×ˢ Set.Ioo (0 : ℝ) T : Set (R3 × ℝ)) ∈ 𝓝 (y, t) :=
    prod_mem_nhds univ_mem (isOpen_Ioo.mem_nhds ht)
  have h2 : ∀ᶠ p in 𝓝 (y, t), HasDerivAt (fun s' => potOn ω p.1 s')
      (deriv (fun s' => potOn ω p.1 s') p.2) p.2 := by
    filter_upwards [hnhds] with p hp
    rw [(hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv p.1 hp.2).deriv]
    exact hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv p.1 hp.2
  have hcont2 : ContinuousAt (fun p : R3 × ℝ => deriv (fun s' => potOn ω p.1 s') p.2) (y, t) := by
    refine (potTDeriv_continuousAt_aux hstrips hcurl hsupp hcontDt hderiv y ht).congr ?_
    filter_upwards [hnhds] with p hp
    exact (hasDerivAt_potOn_time_aux hstrips hcurl hsupp hcontDt hderiv p.1 hp.2).deriv.symm
  have hmain := hasFDerivAt_uncurry_of_partials' (q := potOn ω) (x := y) (t := t)
    (L := potGradCLM ω y t) (c := potTDeriv ω y t) hx ht' h2 hcont2
  have hid : potFDerivExt ω T (y, t)
      = (potGradCLM ω y t).comp (ContinuousLinearMap.fst ℝ R3 ℝ)
        + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ R3 ℝ) (potTDeriv ω y t) := by
    rw [potFDerivExt, potGradExt, if_neg (ne_of_gt ht.1), potTDerivExt_eq_potTDeriv ω T y ht.1]
    rfl
  rw [hid]
  exact hmain

end

end Work.FTS.PressureOn.Connect
