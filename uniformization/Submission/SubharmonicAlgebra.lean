import ChallengeDeps
import Submission.RiemannSurface

/-!
# Adding harmonic functions to subharmonic functions

The sum of a subharmonic function and a harmonic function is subharmonic (both on `X` at a point and
globally).  This is used to write Green functions as `h - log‖·‖` with `h` harmonic.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

section Algebra

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The sum of a subharmonic and a harmonic function is subharmonic at a point. -/
theorem SubharmonicOnXAt.add_harmonicOnXAt {u v : X → ℝ} {x : X} (hu : SubharmonicOnXAt u x)
    (hv : HarmonicOnXAt v x) : SubharmonicOnXAt (u + v) x := by
  rw [SubharmonicOnXAt, SubharmonicAtChart] at hu ⊢
  obtain ⟨hxsrc, ρu, hρu, htu, hcu, hmu⟩ := hu
  obtain ⟨ρv, hρv, htv⟩ :=
    Metric.mem_nhds_iff.mp ((InnerProductSpace.isOpen_setOfPred_harmonicAt
      (v ∘ (chartAt ℂ x).symm)).mem_nhds hv)
  obtain ⟨ρt, hρt, htt⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source hxsrc))
  have hρ : 0 < min (min ρu ρv) ρt := lt_min (lt_min hρu hρv) hρt
  have hleu : Metric.ball ((chartAt ℂ x) x) (min (min ρu ρv) ρt)
      ⊆ Metric.ball ((chartAt ℂ x) x) ρu := by
    refine (Metric.ball_subset_ball (min_le_left _ _)).trans
      (Metric.ball_subset_ball (min_le_left _ _))
  have hlev : Metric.ball ((chartAt ℂ x) x) (min (min ρu ρv) ρt)
      ⊆ Metric.ball ((chartAt ℂ x) x) ρv := by
    refine (Metric.ball_subset_ball (min_le_left _ _)).trans
      (Metric.ball_subset_ball (min_le_right _ _))
  have hlet : Metric.ball ((chartAt ℂ x) x) (min (min ρu ρv) ρt)
      ⊆ Metric.ball ((chartAt ℂ x) x) ρt := Metric.ball_subset_ball (min_le_right _ _)
  have hcv : ContinuousOn (v ∘ (chartAt ℂ x).symm) (Metric.ball ((chartAt ℂ x) x) ρv) :=
    continuousOn_of_forall_continuousAt fun z hz => (htv hz).1.continuousAt
  refine ⟨hxsrc, min (min ρu ρv) ρt, hρ, fun z hz => htt (hlet hz), ?_, ?_⟩
  · have heq : (u + v) ∘ (chartAt ℂ x).symm
        = (u ∘ (chartAt ℂ x).symm) + (v ∘ (chartAt ℂ x).symm) := rfl
    rw [heq]
    exact (hcu.mono hleu).add (hcv.mono hlev)
  · intro p hp r hr hpr
    have hpu : p ∈ Metric.ball ((chartAt ℂ x) x) ρu := hleu hp
    have hpv : p ∈ Metric.ball ((chartAt ℂ x) x) ρv := hlev hp
    have hprv : Metric.closedBall p r ⊆ Metric.ball ((chartAt ℂ x) x) ρv := hpr.trans hlev
    have heq : (u + v) ∘ (chartAt ℂ x).symm
        = (u ∘ (chartAt ℂ x).symm) + (v ∘ (chartAt ℂ x).symm) := rfl
    have hharm : InnerProductSpace.HarmonicOnNhd (v ∘ (chartAt ℂ x).symm)
        (Metric.closedBall p |r|) := by
      rw [abs_of_pos hr]
      exact fun z hz => htv (hprv hz)
    have hIu : CircleIntegrable (u ∘ (chartAt ℂ x).symm) p r :=
      (hcu.mono (fun z hz => hleu (hpr (Metric.sphere_subset_closedBall hz)))).circleIntegrable
        (le_of_lt hr)
    have hIv : CircleIntegrable (v ∘ (chartAt ℂ x).symm) p r :=
      (hcv.mono (fun z hz => hlev (hpr (Metric.sphere_subset_closedBall hz)))).circleIntegrable
        (le_of_lt hr)
    have h1 : (u ∘ (chartAt ℂ x).symm) p ≤ Real.circleAverage (u ∘ (chartAt ℂ x).symm) p r :=
      hmu p hpu r hr (hpr.trans hleu)
    have h2 : Real.circleAverage (v ∘ (chartAt ℂ x).symm) p r = (v ∘ (chartAt ℂ x).symm) p :=
      InnerProductSpace.HarmonicOnNhd.circleAverage_eq hharm
    have h3 : Real.circleAverage ((u ∘ (chartAt ℂ x).symm) + (v ∘ (chartAt ℂ x).symm)) p r
        = Real.circleAverage (u ∘ (chartAt ℂ x).symm) p r
          + Real.circleAverage (v ∘ (chartAt ℂ x).symm) p r :=
      Real.circleAverage_add hIu hIv
    rw [heq, h3, h2]
    have : (u ∘ (chartAt ℂ x).symm) p + (v ∘ (chartAt ℂ x).symm) p
        ≤ Real.circleAverage (u ∘ (chartAt ℂ x).symm) p r + (v ∘ (chartAt ℂ x).symm) p := by
      linarith
    exact this

/-- The sum of a subharmonic and a harmonic function is subharmonic. -/
theorem SubharmonicOnX.add_harmonicOnX {u v : X → ℝ} (hu : SubharmonicOnX u univ)
    (hv : HarmonicOnX v univ) : SubharmonicOnX (u + v) univ :=
  ⟨hu.1.add (HarmonicOnX_continuous hv).continuousOn,
    fun x _ => (hu.2 x (mem_univ x)).add_harmonicOnXAt (hv x (mem_univ x))⟩

/-- Subtracting a harmonic function from a subharmonic function keeps it subharmonic. -/
theorem SubharmonicOnX.sub_harmonicOnX {u v : X → ℝ} (hu : SubharmonicOnX u univ)
    (hv : HarmonicOnX v univ) : SubharmonicOnX (u - v) univ := by
  have h := hu.add_harmonicOnX hv.neg
  simpa [sub_eq_add_neg] using h

/-- Constant functions are subharmonic. -/
theorem subharmonicOnX_const (c : ℝ) : SubharmonicOnX (fun _ : X => c) univ :=
  (harmonicOnX_const c).subharmonic continuousOn_const

theorem subharmonicOnX_add_const {u : X → ℝ} (hu : SubharmonicOnX u univ) (c : ℝ) :
    SubharmonicOnX (fun x => u x + c) univ :=
  hu.add_harmonicOnX (harmonicOnX_const c)

theorem subharmonicOnX_const_add {u : X → ℝ} (hu : SubharmonicOnX u univ) (c : ℝ) :
    SubharmonicOnX (fun x => c + u x) univ := by
  have h : (fun x : X => c + u x) = (fun x : X => u x + c) := by funext x; ring
  rw [h]
  exact subharmonicOnX_add_const hu c

theorem SubharmonicOnXAt.sub_harmonicOnXAt {u v : X → ℝ} {x : X} (hu : SubharmonicOnXAt u x)
    (hv : HarmonicOnXAt v x) : SubharmonicOnXAt (u - v) x := by
  have h := SubharmonicOnXAt.add_harmonicOnXAt hu hv.neg
  simpa [sub_eq_add_neg] using h

end Algebra

end Submission
