import Mathlib
import Submission.Work.Drive.Mono.exists_badLevels
import Submission.Work.Drive.Mono.TiltedTraceDataWExists_holds
import Submission.Work.Drive.Final.tls_rest_crux
import Submission.Work.Drive.Mono.WindowCase.tls_window_oneSphere

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set in
open scoped ENNReal Topology in
/-- **The level frontier of the tilted sweep is a disjoint union of embedded spheres, off a finite
set of levels.**

Given tilt data with a genuinely thin slab cutting the box (`SlabCutsBox`) and a window containing
the `ℓ`-range of the **closed** box, there is a finite set `B` of levels, contained in the window,
such that at every level `lam ∈ Icc lam0 lam1` with `lam ∉ exc ∪ B` the frontier of the level's
removed set `tiltedLevelRemoved s c σ u v h ℓ lam` is a finite disjoint union of embedded spheres.

This is the geometric input `Work.Drive.Mono.LevelSphereDecomposition` of the trace-data residual of
the tilted sweep.  The proof is the bookkeeping of `Work.Drive.Mono.exists_badLevels` (which produces
`B` and the three genericity conditions `hedge`/`hvertex`/`hseam` off it) glued to the
disjoint-spheres results for the two regimes of the level: `Work.Drive.Final.tls_rest_crux` outside
the one-sphere window of `Work.Drive.Final.OneSphereWindow`, and
`Work.Drive.Mono.WindowCase.tls_window_oneSphere` inside it.  Note `v ≠ 0` follows from `‖v‖ = 1`. -/
theorem levelSphereDecomposition_of_data
    {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ}
    {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hs : 0 < s) (hh : 0 < h) (hv : ‖v‖ = 1) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hcut : Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ v c + u) h v)
    (hwin : ∀ y ∈ closure (Submission.PBox s c σ), lam0 < ℓ y ∧ ℓ y < lam1) :
    ∃ B : Finset ℝ, (∀ t ∈ B, lam0 < t ∧ t < lam1) ∧
      Work.Drive.Mono.LevelSphereDecomposition ψ s c σ u v h ℓ (exc ∪ B) lam0 lam1 := by
  obtain ⟨B, hBwin, hBgen⟩ := exists_badLevels hh hℓv hℓne hcut hwin
  have hv0 : v ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hv
    exact absurd hv.symm (by norm_num)
  refine ⟨B, hBwin, ?_⟩
  intro lam hlam hne
  obtain ⟨hedge, hvertex, hseam⟩ := hBgen lam hlam hne
  by_cases hwindow : Work.Drive.Final.OneSphereWindow s c σ u h lam v ℓ
  · -- inside the one-sphere window the frontier is a single embedded sphere
    obtain ⟨hwallP, hwallM, hwinP, hwinM⟩ := hwindow
    have hsphere : Work.InnermostDisk.IsEmbeddedSphere
        (frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) :=
      Work.Drive.Mono.WindowCase.tls_window_oneSphere s hs c σ u h lam v ℓ hh hℓv hℓne
        hedge hvertex hwallP hwallM hwinP hwinM
    refine ⟨1, fun _ => frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam),
      fun _ => hsphere, ?_, ?_⟩
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij
    · rw [Set.iUnion_const]
  · -- outside it the decomposition is the rest case of the level
    exact Work.Drive.Final.tls_rest_crux s hs c σ u h lam v ℓ hv0 hh hℓv hℓne
      hedge hvertex hseam hwindow

end Work.Drive.Mono
