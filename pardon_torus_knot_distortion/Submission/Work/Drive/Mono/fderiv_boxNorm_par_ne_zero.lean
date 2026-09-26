import Mathlib
import Submission.Work.Drive.Mono.JunctionGenC

/-!
# The box norm composed with the parametrisation is regular at an interior face point

Let `z = par ψ p` be a point of the surface `F = ψ(standard torus)` at which a *single* signed
face of Pardon's box is tight: `faceLin c σ i ε z = s` with `ε = ±1`, every face norm is `≤ s`,
and the two other face norms are *strictly* below `s` (`hact`, `huniq`).  Then `z` is a point of
the box sphere `{boxNorm c σ = s}` lying in the relative interior of the face `(i, ε)`:

* `faceNorm c σ i z = |signedFace c σ i z| = |ε s| = s` because `s > 0` and `|ε| = 1`, so the
  active face really is tight (this is where `hε : ε = 1 ∨ ε = -1` is used: for an unrestricted
  `ε : ℝ` the hypothesis `faceLin c σ i ε z = s` says nothing about `faceNorm c σ i z` — see
  `Work.Drive.Mono.Cex.counterexample` in `Mono/_cex_parallel_boxNorm.lean`);
* no other face can overtake it nearby, so on a whole neighbourhood of `z` the (piecewise smooth)
  box norm coincides with the smooth affine function `faceLin c σ i ε`
  (`Work.Smooth.BoxGeneric.LocalSurface.eventually_boxNorm_eq_faceLin`).

Pulling this neighbourhood back along the continuous parametrisation gives that
`boxNorm c σ ∘ par ψ` and `faceLin c σ i ε ∘ par ψ = pullback ψ (faceLin c σ i ε)` are equal
near `p`, hence have the same Fréchet derivative at `p`
(`Filter.EventuallyEq.fderiv_eq`).  So the regularity of the pull-back of the active face at `p`
(`hreg`) transfers to the pull-back of the box norm: the latter derivative is nonzero, which is the
clause of the junction bundles (`JunctionGen`/`JunctionGenB`/`JunctionGenC`) asserting that the
box-sphere trace is a regular level curve at `z`.

The statement is stated for an arbitrary `z` and `p` with `par ψ p = z`; note that `par ψ` is the
periodic parametrisation of the torus surface, so `p` runs over the parameter plane.
-/

open scoped Topology

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Filter

theorem fderiv_boxNorm_par_ne_zero {ψ : Submission.Diffeo} {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {i : Fin 3} {ε : ℝ} {z : LeanEval.KnotTheory.PardonDistortion.R3}
    {p : ℝ × ℝ}
    (hs : 0 < s) (hε : ε = 1 ∨ ε = -1)
    (hp : Work.BoxShrink.Pinch.par ψ p = z)
    (hact : Work.Smooth.BoxGeneric.IsActiveSignedFace c σ s i ε z)
    (huniq : ∀ j : Fin 3, j ≠ i → Work.Smooth.BoxGeneric.faceNorm c σ j z < s)
    (hreg : fderiv ℝ (Work.Smooth.Morse.pullback ψ
      (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p ≠ 0) :
    fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 := by
  -- On a neighbourhood of `z` the box norm is the active signed face function ...
  have heq : (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q))
      =ᶠ[𝓝 p] (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
        (Work.BoxShrink.Pinch.par ψ q)) := by
    have h : (fun x : LeanEval.KnotTheory.PardonDistortion.R3 => Submission.boxNorm c σ x)
        =ᶠ[𝓝 z] (fun x : LeanEval.KnotTheory.PardonDistortion.R3 =>
          Work.Smooth.BoxGeneric.faceLin c σ i ε x) :=
      Work.Smooth.BoxGeneric.LocalSurface.eventually_boxNorm_eq_faceLin hs hε hact huniq
    -- ... and the parametrisation is continuous at `p`, sending `p` to `z`.
    have htend : Filter.Tendsto (Work.BoxShrink.Pinch.par ψ) (𝓝 p) (𝓝 z) := by
      have hc : Filter.Tendsto (Work.BoxShrink.Pinch.par ψ) (𝓝 p)
          (𝓝 (Work.BoxShrink.Pinch.par ψ p)) := by
        rw [Work.BoxShrink.Pinch.par_def]
        exact (Work.Smooth.Morse.param_continuous ψ).continuousAt
      rwa [hp] at hc
    exact h.comp_tendsto htend
  -- Equal nearby ⟹ same Fréchet derivative.
  rw [Filter.EventuallyEq.fderiv_eq heq]
  have hfun : (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
      (Work.BoxShrink.Pinch.par ψ q))
      = Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i ε) := rfl
  rw [hfun]
  exact hreg

end Work.Drive.Mono
