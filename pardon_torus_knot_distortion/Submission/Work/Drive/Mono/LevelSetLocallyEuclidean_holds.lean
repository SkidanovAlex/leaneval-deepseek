import Mathlib
import Submission.Work.Drive.Mono.Residual
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param
import Submission.Work.Smooth.OneManifold.isLocallyArc_levelSet_of_fderiv_ne_zero
import Submission.Work.Smooth.Morse.Surface.param_local_injective
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen
import Submission.Work.SliceArcs.Components

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.Mono

theorem LevelSetLocallyEuclidean_holds
    (ψ : Submission.Diffeo) (ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ)
    {z : LeanEval.KnotTheory.PardonDistortion.R3} {lam : ℝ}
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier) (hzl : ℓ z = lam)
    (hreg : ∀ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠ 0) :
    ∃ O : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen O ∧ z ∈ O ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        (O ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          {y : LeanEval.KnotTheory.PardonDistortion.R3 | ℓ y = lam}) := by
  -- a parameter point above `z`
  obtain ⟨p₀, hp₀⟩ : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = z := hz
  -- regularity at `p₀`
  have hreg₀ : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p₀ ≠ 0 :=
    hreg p₀ (by rw [Work.BoxShrink.Pinch.par_def]; exact hp₀)
  have hsw₀ : Work.Drive.EpsForm.sweepHeight ψ ℓ p₀ = lam := by
    show ℓ (Work.Smooth.Morse.param ψ p₀) = lam
    rw [hp₀]; exact hzl
  -- smoothness of the sweep height
  have hswDiff : ContDiff ℝ 1 (Work.Drive.EpsForm.sweepHeight ψ ℓ) :=
    Work.Smooth.Morse.pullback_contDiff_one ψ
      (ℓ.contDiff : ContDiff ℝ 1 (fun y : R3 => ℓ y))
  -- the level set of the sweep height is locally an arc near `p₀`
  obtain ⟨B₁, hB₁open, hp₀B₁, hloc₁⟩ :=
    Work.Smooth.OneManifold.isLocallyArc_levelSet_of_fderiv_ne_zero
      (f := Work.Drive.EpsForm.sweepHeight ψ ℓ) (p := p₀) (t := lam)
      hswDiff.contDiffAt hsw₀ hreg₀
  -- a ball on which the parametrisation is injective
  obtain ⟨εp, hεppos, hεpinj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p₀
  set B : Set (ℝ × ℝ) := B₁ ∩ Metric.ball p₀ εp with hBdef
  have hBopen : IsOpen B := hB₁open.inter Metric.isOpen_ball
  have hp₀B : p₀ ∈ B := ⟨hp₀B₁, Metric.mem_ball_self hεppos⟩
  have hinjB : Set.InjOn (Work.Smooth.Morse.param ψ) B :=
    fun a ha b hb hab => hεpinj ha.2 hb.2 hab
  -- the plane level set inside the ball is locally an arc
  have hlocB : Work.Smooth.OneManifold.IsLocallyArcP
      (B ∩ {q : ℝ × ℝ | Work.Drive.EpsForm.sweepHeight ψ ℓ q = lam}) := by
    have h1 := Work.Smooth.OneManifold.isLocallyArc_inter_of_isOpen hloc₁
      (Metric.isOpen_ball : IsOpen (Metric.ball p₀ εp))
    refine Work.Smooth.OneManifold.isLocallyArc_of_eq ?_ h1
    ext q
    simp only [hBdef, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  -- the target level set on the surface
  set Z : Set R3 := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ {y : R3 | ℓ y = lam} with hZdef
  set Pl : Set (ℝ × ℝ) := B ∩ {q : ℝ × ℝ | Work.Drive.EpsForm.sweepHeight ψ ℓ q = lam}
    with hPldef
  have hPB : Pl ⊆ B := inter_subset_left
  have hZc : Z ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := inter_subset_left
  have hident : ∀ B' : Set (ℝ × ℝ), IsOpen B' → B' ⊆ B →
      Work.Smooth.Morse.param ψ '' (B' ∩ Pl) = Work.Smooth.Morse.param ψ '' B' ∩ Z := by
    intro B' _ hB'sub
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      have hqPl : Work.Drive.EpsForm.sweepHeight ψ ℓ q = lam := by
        rw [hPldef] at hq; exact hq.2.2
      refine ⟨⟨q, hq.1, rfl⟩, ⟨Work.Smooth.Morse.param_mem ψ q, ?_⟩⟩
      show ℓ (Work.Smooth.Morse.param ψ q) = lam
      exact hqPl
    · rintro ⟨⟨q, hqB', rfl⟩, hyZ⟩
      refine ⟨q, ⟨hqB', ?_⟩, rfl⟩
      rw [hPldef]
      exact ⟨hB'sub hqB', by
        show ℓ (Work.Smooth.Morse.param ψ q) = lam
        exact hyZ.2⟩
  have hlocB' : Work.Smooth.OneManifold.IsLocallyArcP (B ∩ Pl) :=
    Work.Smooth.OneManifold.isLocallyArc_of_eq (Set.inter_eq_right.mpr hPB).symm hlocB
  have hlocZ : Work.Smooth.OneManifold.IsLocallyEuclidean
      (Work.Smooth.Morse.param ψ '' B ∩ Z) :=
    Work.Smooth.OneManifold.isLocallyEuclidean_image_of_param hZc hBopen hPB hident hinjB hlocB'
  -- an ambient open set whose trace on the surface is the chart image
  have hVopen : Work.SurgeryInvariance.IsOpenInCarrier (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Smooth.Morse.param ψ '' B) :=
    Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ hBopen
  obtain ⟨W, hWopen, hWeq⟩ :=
    Work.SliceArcs.exists_isOpen_inter_carrier (P := Work.Drive.EpsSphere.torusOf ψ) hVopen
  refine ⟨W, hWopen, ?_, ?_⟩
  · -- `z ∈ W`
    have hzcar : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier := by
      rw [← hp₀]; exact Work.Smooth.Morse.param_mem ψ p₀
    have hzmem : z ∈ Work.Smooth.Morse.param ψ '' B
        ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier := ⟨⟨p₀, hp₀B, hp₀⟩, hzcar⟩
    rw [hWeq] at hzmem
    exact hzmem.1
  · -- the trace is locally Euclidean
    have hsub : Work.Smooth.Morse.param ψ '' B
        ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier := by
      rw [show (Work.Drive.EpsSphere.torusOf ψ).carrier
          = Set.range (Work.Smooth.Morse.param ψ) from Work.Smooth.Morse.torus_carrier ψ]
      exact Set.image_subset_range _ _
    have hWc : W ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier
        = Work.Smooth.Morse.param ψ '' B := by
      rw [← hWeq]
      exact Set.inter_eq_left.mpr hsub
    have h1 : Work.Smooth.Morse.param ψ '' B ∩ Z
        = Work.Smooth.Morse.param ψ '' B ∩ {y : R3 | ℓ y = lam} := by
      rw [hZdef, ← Set.inter_assoc, Set.inter_eq_left.mpr hsub]
    have h2 : W ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ {y : R3 | ℓ y = lam}
        = Work.Smooth.Morse.param ψ '' B ∩ {y : R3 | ℓ y = lam} := by
      rw [hWc]
    refine Work.Smooth.OneManifold.isLocallyEuclidean_of_eq ?_ hlocZ
    rw [h1, h2]

end Work.Drive.Mono
