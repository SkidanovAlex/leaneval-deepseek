import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.Surface.param_local_injective
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen
import Submission.Work.Smooth.Morse.Regular.pullback_local_arc

/-!
# A regular level set of `g|_F` is locally an arc

`Work.Smooth.Morse.Surface.param ψ : ℝ × ℝ → ℝ³` parametrises the embedded torus
`F = ψ(standard torus)` and `Work.Smooth.Morse.pullback ψ g = g ∘ param ψ` is `g` read in the
parameter plane.  At a regular value `t` of `g|_F` (`Work.Smooth.Morse.IsRegularValue`) the
level set `Work.Smooth.Morse.levelSet ψ g t = F ∩ {g = t}` is a one-dimensional submanifold of the
surface; this file proves the local form of that statement, `Work.Smooth.Morse.IsLocalArc`.

The proof has two inputs:

* `Work.Smooth.Morse.Regular.pullback_local_arc` (the implicit function theorem in the parameter
  plane): at a parameter point `p` with `pullback ψ g p = t` and nonzero derivative, there is an
  injective continuous arc `σ` through `p` whose image is exactly the level set of `pullback ψ g`
  in a ball around `p`;
* `Work.Smooth.Morse.Surface.param_local_injective`: the parametrisation is injective on a ball
  around each parameter point.

Since `param ψ` is a local homeomorphism, a neighbourhood of `x = param ψ p` in the surface on
which the arc `param ψ ∘ σ` exhausts the level set is obtained by taking the image under `param ψ`
of a ball `B` around `p` which is small enough that (a) `param ψ` is injective on it and (b) every
level point of `B` lies on the arc.  The arc is then read on the interval of parameters `s` with
`σ s ∈ B`, which is open because `σ` is continuous.

The result feeds the classification of compact one-manifolds
(`Work.Smooth.Morse.CompactOneManifoldInput`) through `IsCircleUnion`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse.Regular

noncomputable section

open scoped Topology

theorem levelSet_isLocalArc_of_regularValue (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : ContDiff ℝ 1 g) {t : ℝ} (hreg : Work.Smooth.Morse.IsRegularValue ψ g t) : Work.Smooth.Morse.IsLocalArc ψ (Work.Smooth.Morse.levelSet ψ g t) := by
  -- a point of the level set, together with a parameter over it
  intro x hx
  rw [Work.Smooth.Morse.mem_levelSet] at hx
  obtain ⟨hxcarrier, hxt⟩ := hx
  obtain ⟨p, hp⟩ := hxcarrier
  have hhp : Work.Smooth.Morse.pullback ψ g p = t := by
    show g (Work.Smooth.Morse.param ψ p) = t
    exact (congrArg g hp).trans hxt
  -- the derivative at `p` does not vanish, because `t` is a regular value
  have hd : fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p ≠ 0 :=
    (Work.Smooth.Morse.isRegularValue_iff ψ g t).mp hreg p hhp
  -- the arc of the level set of the pull-back through `p`
  obtain ⟨ε, hεpos, σ, hσ0, hσcont, hσinj, hσlev, hσcov⟩ :=
    pullback_local_arc ψ hg t p hhp hd
  -- a ball around `p` on which the parametrisation is injective
  obtain ⟨εp, hεppos, hεpinj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  -- a smaller ball `B`, contained in both balls above
  set δ : ℝ := min ε εp with hδdef
  have hδpos : 0 < δ := lt_min hεpos hεppos
  have hδε : δ ≤ ε := min_le_left _ _
  have hδεp : δ ≤ εp := min_le_right _ _
  -- the interval of parameters whose image lies in `B`
  set I : Set ℝ := Set.Ioo (-1 : ℝ) 1 ∩ σ ⁻¹' Metric.ball p δ with hIdef
  have hIopen : IsOpen I := by
    rw [hIdef]
    exact hσcont.isOpen_inter_preimage isOpen_Ioo Metric.isOpen_ball
  have h0I : (0 : ℝ) ∈ I := by
    rw [hIdef]
    refine ⟨by norm_num, ?_⟩
    show σ 0 ∈ Metric.ball p δ
    rw [hσ0]
    exact Metric.mem_ball_self hδpos
  refine ⟨Work.Smooth.Morse.param ψ '' Metric.ball p δ,
    Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ Metric.isOpen_ball,
    ⟨p, Metric.mem_ball_self hδpos, hp⟩, I, 0, fun s => Work.Smooth.Morse.param ψ (σ s),
    hIopen, h0I, ?_, ?_, ?_, ?_, ?_⟩
  · -- `param ψ ∘ σ` is continuous on `I`
    exact ((Work.Smooth.Morse.param_continuous ψ).continuousOn.comp hσcont
      (Set.mapsTo_univ _ _)).mono (by rw [hIdef]; exact inter_subset_left)
  · -- the arc passes through `x`
    show Work.Smooth.Morse.param ψ (σ 0) = x
    rw [hσ0]
    exact hp
  · -- the arc is injective on `I`
    intro s hs s' hs' heq
    rw [hIdef] at hs hs'
    have hsB : σ s ∈ Metric.ball p εp := Metric.ball_subset_ball hδεp hs.2
    have hsB' : σ s' ∈ Metric.ball p εp := Metric.ball_subset_ball hδεp hs'.2
    exact hσinj hs.1 hs'.1 (hεpinj hsB hsB' heq)
  · -- the arc lies in the level set
    intro s hs
    rw [Work.Smooth.Morse.mem_levelSet]
    exact ⟨Work.Smooth.Morse.param_mem ψ (σ s), hσlev s (by rw [hIdef] at hs; exact hs.1)⟩
  · -- the arc exhausts the level set in the surface neighbourhood
    intro y hy hyU
    rw [Work.Smooth.Morse.mem_levelSet] at hy
    obtain ⟨-, hyt⟩ := hy
    obtain ⟨q, hqB, hqy⟩ := hyU
    have hqε : ‖q - p‖ < ε := by
      rw [Metric.mem_ball, dist_eq_norm] at hqB
      exact lt_of_lt_of_le hqB hδε
    have hqt : Work.Smooth.Morse.pullback ψ g q = t := by
      show g (Work.Smooth.Morse.param ψ q) = t
      exact (congrArg g hqy).trans hyt
    obtain ⟨s, hs, hσs⟩ := hσcov q hqt hqε
    refine ⟨s, ?_, ?_⟩
    · rw [hIdef]
      refine ⟨hs, ?_⟩
      show σ s ∈ Metric.ball p δ
      rw [hσs]
      exact hqB
    · show Work.Smooth.Morse.param ψ (σ s) = y
      rw [hσs]
      exact hqy

end

end Work.Smooth.Morse.Regular
