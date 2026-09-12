import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.GDelta.MetrizableSpace

namespace Commons.Analysis.Complex

open Metric Set Filter
open scoped Topology

theorem finite_zero_set_of_analytic_off_finset
    (f : ℂ → ℂ) (B : Finset ℂ) (z0 : ℂ)
    (hz0 : z0 ∈ Metric.ball (0:ℂ) 1) (hz0f : f z0 ≠ 0)
    (hB : ∀ b ∈ B, b ∈ Metric.sphere (0:ℂ) 1 ∧ f b ≠ 0)
    (hcont : ContinuousOn f (Metric.closedBall (0:ℂ) 1))
    (han : ∀ z ∈ Metric.closedBall (0:ℂ) 1, z ∉ B → AnalyticAt ℂ f z) :
    {z : ℂ | z ∈ Metric.closedBall (0:ℂ) 1 ∧ f z = 0}.Finite := by
  set S : Set ℂ := {z : ℂ | z ∈ Metric.closedBall (0:ℂ) 1 ∧ f z = 0} with hSdef
  -- Each point of the closed ball has an open neighbourhood meeting `S` finitely.
  have key : ∀ z : ↥(Metric.closedBall (0:ℂ) 1),
      ∃ U : Set ℂ, IsOpen U ∧ (z:ℂ) ∈ U ∧ (S ∩ U).Finite := by
    intro z
    by_cases hfz : f (z:ℂ) = 0
    · -- `z` is a zero; since `f b ≠ 0` for `b ∈ B`, it lies outside `B`, so `f` is analytic there.
      have hzB : (z:ℂ) ∉ B := fun hzB => (hB (z:ℂ) hzB).2 hfz
      have hanz : AnalyticAt ℂ f (z:ℂ) := han (z:ℂ) z.2 hzB
      rcases hanz.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
      · -- `f` vanishes on a neighbourhood of `z`; identity theorem contradicts `f z0 ≠ 0`.
        exfalso
        have hVmem : {w : ℂ | f w = 0} ∈ 𝓝 (z:ℂ) := hzero
        have hzV : (z:ℂ) ∈ interior {w : ℂ | f w = 0} :=
          mem_interior_iff_mem_nhds.mpr hVmem
        -- pick `w` in `interior {f = 0} ∩ ball` (the open ball is dense in the closed ball)
        have hzcl : (z:ℂ) ∈ closure (Metric.ball (0:ℂ) 1) := by
          rw [closure_ball (0:ℂ) (by norm_num)]
          exact z.2
        obtain ⟨w, hwV, hwb⟩ := (mem_closure_iff_nhds.mp hzcl)
          (interior {w : ℂ | f w = 0}) (isOpen_interior.mem_nhds hzV)
        -- `f` is analytic on the whole open ball
        have hfball : AnalyticOnNhd ℂ f (Metric.ball (0:ℂ) 1) := by
          intro x hx
          refine han x (Metric.ball_subset_closedBall hx) ?_
          intro hxB
          have h1 := (hB x hxB).1
          rw [Metric.mem_sphere] at h1
          rw [Metric.mem_ball] at hx
          linarith
        have hwZero : f =ᶠ[𝓝 w] 0 :=
          Filter.eventually_of_mem (isOpen_interior.mem_nhds hwV)
            (fun x hx => interior_subset (s := {y : ℂ | f y = 0}) hx)
        have hEqOn := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          hfball Metric.isPreconnected_ball hwb hwZero
        exact hz0f (hEqOn hz0)
      · -- `z` is an isolated zero.
        have hne' : ∀ᶠ w in 𝓝 (z:ℂ), w ≠ (z:ℂ) → f w ≠ 0 := by
          have := eventually_nhdsWithin_iff.mp hne
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using this
        refine ⟨interior {w : ℂ | w ≠ (z:ℂ) → f w ≠ 0}, isOpen_interior,
          mem_interior_iff_mem_nhds.mpr hne', ?_⟩
        apply Set.Finite.subset (Set.finite_singleton (z:ℂ))
        intro w hw
        rw [Set.mem_singleton_iff]
        by_contra hwz
        exact (interior_subset (s := {y : ℂ | y ≠ (z:ℂ) → f y ≠ 0}) hw.2) hwz hw.1.2
    · -- `f z ≠ 0`: continuity within the closed ball gives a neighbourhood free of zeros.
      have hcw : ContinuousWithinAt f (Metric.closedBall (0:ℂ) 1) (z:ℂ) := hcont (z:ℂ) z.2
      have hev : ∀ᶠ w in 𝓝[Metric.closedBall (0:ℂ) 1] (z:ℂ), f w ≠ 0 :=
        hcw.eventually_ne hfz
      rw [eventually_nhdsWithin_iff] at hev
      refine ⟨interior {w : ℂ | w ∈ Metric.closedBall (0:ℂ) 1 → f w ≠ 0}, isOpen_interior,
        mem_interior_iff_mem_nhds.mpr hev, ?_⟩
      have hemp : S ∩ interior {w : ℂ | w ∈ Metric.closedBall (0:ℂ) 1 → f w ≠ 0} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact (interior_subset
          (s := {y : ℂ | y ∈ Metric.closedBall (0:ℂ) 1 → f y ≠ 0}) hw.2) hw.1.1 hw.1.2
      rw [hemp]
      exact Set.finite_empty
  -- Compactness: finitely many of these neighbourhoods cover the closed ball.
  choose U hU using key
  have hcover : Metric.closedBall (0:ℂ) 1 ⊆ ⋃ i, U i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).2.1⟩
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0:ℂ) 1).elim_finite_subcover U
    (fun i => (hU i).1) hcover
  have hSsub : S ⊆ ⋃ i ∈ t, (S ∩ U i) := by
    intro x hx
    rcases mem_iUnion₂.mp (ht hx.1) with ⟨i, hit, hix⟩
    exact mem_iUnion₂.mpr ⟨i, hit, hx, hix⟩
  have hfin : (⋃ i ∈ t, (S ∩ U i)).Finite := by
    have := Set.Finite.biUnion (Finset.finite_toSet t) (fun i _ => (hU i).2.2)
    simpa using this
  exact hfin.subset hSsub

end Commons.Analysis.Complex