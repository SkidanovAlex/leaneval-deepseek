import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData
import Submission.Work.Drive.Mono.SphereFaceDefs
import Submission.Work.Drive.Mono.IsLocallyEuclidean_trace_spherePoint_holds
import Submission.Work.Smooth.OneManifold.Plane.Vertex
import Submission.Work.Smooth.OneManifold.Plane.Corner
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_three_tangent
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param
import Submission.Work.Smooth.Morse.Immersion.isImmersion
import Submission.Work.Smooth.Morse.Surface.param_local_injective
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.SliceArcs.Components
import Submission.Work.Smooth.BoxGeneric.LocalSurface.isLocalArcAt_of_uniqueActiveFace
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_sphereFace
import Submission.Work.Drive.Mono.isLocallyArc_corner_sphereFace
import Submission.Work.Drive.Mono.closure_and_uniqueness_of_sphereFace

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open Set Filter

noncomputable section

theorem isLocallyEuclidean_trace_of_sphereFaceJunction {ψ : Submission.Diffeo} {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ} {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ} {z : LeanEval.KnotTheory.PardonDistortion.R3}
    (hs : 0 < s) (hv : v ≠ 0) (hh : 0 < h)
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzsphere : Submission.boxNorm c σ z = s)
    (hzface : inner ℝ v z = inner ℝ v c + u + h) (hzl : ℓ z < lam)
    (htrans : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) :
    ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam))) := by
  classical
  obtain ⟨p, hp, hd1, hd2, hd3⟩ := htrans
  -- ### the two consequences of the transversality: `z` is in the closure of the region and is
  -- the unique point of the surface with both level conditions nearby
  have haux : (z ∈ closure (Submission.PBox s c σ ∩ {y : R3 | inner ℝ v c + u + h < inner ℝ v y})) ∧
      (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ y : R3, y ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        dist y z < ρ₀ → Submission.boxNorm c σ y = s →
        inner ℝ v y = inner ℝ v c + u + h → y = z) :=
    closure_and_uniqueness_of_sphereFace hp hzsphere hzface hd1 hd2 hd3
  obtain ⟨hcl, hsep⟩ := haux
  -- ### the geometric identity: the frontier of the removed set is the corner, near `z`
  obtain ⟨ρ, hρpos, hρeq⟩ :=
    frontier_tiltedLevelRemoved_sphereFace ψ hs hv hh hzsphere hzface hzl hcl hsep
  -- ### the plane model: the corner is locally an arc in the parameter plane
  obtain ⟨V, hVopen, hpV, hVloc⟩ :=
    isLocallyArc_corner_sphereFace hp hzsphere hzface hd1 hd2 hd3
  -- ### a small parameter ball, inside `V`, inside the injectivity radius, and mapping into the
  -- ball around `z` on which the corner identity holds
  have hnhds_ball : {q : ℝ × ℝ | Work.BoxShrink.Pinch.par ψ q ∈ Metric.ball z ρ} ∈
      nhds p := by
    have hmem : Metric.ball z ρ ∈ nhds (Work.BoxShrink.Pinch.par ψ p) := by
      rw [hp]
      exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρpos)
    exact (Work.BoxShrink.Pinch.par_continuous ψ).continuousAt hmem
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhds_iff.mp hnhds_ball
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ := Metric.mem_nhds_iff.mp (hVopen.mem_nhds hpV)
  obtain ⟨ε₀, hε₀pos, hε₀inj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  set δ : ℝ := min (min δ₁ δ₂) ε₀ with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₁pos hδ₂pos) hε₀pos
  have hδ1 : δ ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ0 : δ ≤ ε₀ := min_le_right _ _
  set B : Set (ℝ × ℝ) := Metric.ball p δ with hBdef
  have hBopen : IsOpen B := by rw [hBdef]; exact Metric.isOpen_ball
  have hpB : p ∈ B := by rw [hBdef]; exact Metric.mem_ball_self hδpos
  have hBV : B ⊆ V := by
    intro q hq
    have hq' : q ∈ Metric.ball p δ := by rwa [hBdef] at hq
    exact hδ₂sub (Metric.ball_subset_ball hδ2 hq')
  have hBinj : Set.InjOn (Work.BoxShrink.Pinch.par ψ) B := by
    intro x hx y hy hxy
    have hx' : x ∈ Metric.ball p δ := by rwa [hBdef] at hx
    have hy' : y ∈ Metric.ball p δ := by rwa [hBdef] at hy
    exact hε₀inj (Metric.ball_subset_ball hδ0 hx') (Metric.ball_subset_ball hδ0 hy') hxy
  have hBball : ∀ q ∈ B, Work.BoxShrink.Pinch.par ψ q ∈ Metric.ball z ρ := by
    intro q hq
    have hq' : q ∈ Metric.ball p δ := by rwa [hBdef] at hq
    exact hδ₁sub (Metric.ball_subset_ball hδ1 hq')
  -- ### the pointwise identification of the trace with the plane corner on `B`
  have hpoint : ∀ q ∈ B, (max (boxH ψ s c σ q) (-(planeG ψ c v u h q)) = 0 ↔
      Work.BoxShrink.Pinch.par ψ q ∈
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
    intro q hqB
    have hqball := hBball q hqB
    have hfr : Work.BoxShrink.Pinch.par ψ q ∈
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) ↔
        (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) ≤ s ∧
          inner ℝ v c + u + h ≤ inner ℝ v (Work.BoxShrink.Pinch.par ψ q) ∧
          (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) = s ∨
            inner ℝ v (Work.BoxShrink.Pinch.par ψ q) = inner ℝ v c + u + h)) := by
      constructor
      · intro hfr'
        have h1 : Work.BoxShrink.Pinch.par ψ q ∈ Metric.ball z ρ ∩
            ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
              frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) :=
          ⟨hqball, Work.BoxShrink.Pinch.par_mem_carrier ψ q, hfr'⟩
        rw [hρeq] at h1
        exact h1.2.2
      · intro hc
        have h1 : Work.BoxShrink.Pinch.par ψ q ∈ Metric.ball z ρ ∩
            ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
              {y : R3 | Submission.boxNorm c σ y ≤ s ∧ inner ℝ v c + u + h ≤ inner ℝ v y ∧
                (Submission.boxNorm c σ y = s ∨ inner ℝ v y = inner ℝ v c + u + h)}) :=
          ⟨hqball, Work.BoxShrink.Pinch.par_mem_carrier ψ q, hc⟩
        rw [← hρeq] at h1
        exact h1.2.2
    rw [hfr, Work.Smooth.BoxGeneric.LocalArc.max_eq_zero_iff]
    rw [boxH_apply, planeG_apply]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by linarith, by linarith, ?_⟩
      rcases h3 with h3 | h3
      · left; linarith
      · right; linarith
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by linarith, by linarith, ?_⟩
      rcases h3 with h3 | h3
      · left; linarith
      · right; linarith
  -- ### the plane model restricted to `B`
  set M : Set (ℝ × ℝ) := {q : ℝ × ℝ | max (boxH ψ s c σ q) (-(planeG ψ c v u h q)) = 0}
    with hMdef
  set P : Set (ℝ × ℝ) := B ∩ M with hPdef
  have hPB : P ⊆ B := by rw [hPdef]; exact inter_subset_left
  have hlocB : Work.Smooth.OneManifold.IsLocallyArcP (B ∩ P) := by
    have h1 : Work.Smooth.SphereJordan.IsLocallyArc ↥((V ∩ M) ∩ B) :=
      Work.Smooth.OneManifold.isLocallyArc_inter_of_isOpen hVloc hBopen
    refine Work.Smooth.OneManifold.isLocallyArc_of_eq ?_ h1
    ext q
    constructor
    · rintro ⟨⟨hqV, hqM⟩, hqB⟩
      exact ⟨hqB, hqB, hqM⟩
    · rintro ⟨hqB, -, hqM⟩
      exact ⟨⟨hBV hqB, hqM⟩, hqB⟩
  set Z : Set R3 := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) with hZdef
  have hZc : Z ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := fun y hy => hy.1
  have hident : ∀ B' : Set (ℝ × ℝ), IsOpen B' → B' ⊆ B →
      Work.BoxShrink.Pinch.par ψ '' (B' ∩ P) = Work.BoxShrink.Pinch.par ψ '' B' ∩ Z := by
    intro B' _ hB'sub
    ext y
    constructor
    · rintro ⟨q, ⟨hqB', hqP⟩, rfl⟩
      refine ⟨⟨q, hqB', rfl⟩, ?_⟩
      refine ⟨Work.BoxShrink.Pinch.par_mem_carrier ψ q, ?_⟩
      exact (hpoint q (hB'sub hqB')).mp hqP.2
    · rintro ⟨⟨q, hqB', rfl⟩, hyZ⟩
      exact ⟨q, ⟨hqB', ⟨hB'sub hqB', (hpoint q (hB'sub hqB')).mpr hyZ.2⟩⟩, rfl⟩
  have hlocE : Work.Smooth.OneManifold.IsLocallyEuclidean
      (Work.BoxShrink.Pinch.par ψ '' B ∩ Z) :=
    Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param hZc hBopen hPB hident hBinj hlocB
  -- ### the trace is the trace of an open set of `ℝ³`
  have hVopenC : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (Work.BoxShrink.Pinch.par ψ '' B) := by
    have h := Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hBopen
    simpa only [Work.Drive.EpsSphere.torusOf, Work.BoxShrink.Pinch.par_def] using h
  obtain ⟨W, hWopen, hWeq⟩ := Work.SliceArcs.exists_isOpen_inter_carrier hVopenC
  refine ⟨W, hWopen, ?_, ?_⟩
  · have hzmem : z ∈ Work.BoxShrink.Pinch.par ψ '' B ∩
        (Work.Drive.EpsSphere.torusOf ψ).carrier :=
      ⟨⟨p, hpB, hp⟩, by rw [← hp]; exact Work.BoxShrink.Pinch.par_mem_carrier ψ p⟩
    rw [hWeq] at hzmem
    exact hzmem.1
  · have hsub : Work.BoxShrink.Pinch.par ψ '' B ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier :=
      Set.image_subset_range _ _
    have hWc : W ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier =
        Work.BoxShrink.Pinch.par ψ '' B := by
      rw [← hWeq, Set.inter_eq_left.mpr hsub]
    have hset : W ∩ ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) =
        Work.BoxShrink.Pinch.par ψ '' B ∩ Z := by
      rw [hZdef]
      ext y
      constructor
      · rintro ⟨hyW, hyC, hyfr⟩
        exact ⟨hWc ▸ ⟨hyW, hyC⟩, hyC, hyfr⟩
      · rintro ⟨hyB, hyC, hyfr⟩
        exact ⟨(hWc.symm ▸ hyB).1, hyC, hyfr⟩
    exact Work.Smooth.OneManifold.isLocallyEuclidean_of_eq hset.symm hlocE

end

end Work.Drive.Mono
