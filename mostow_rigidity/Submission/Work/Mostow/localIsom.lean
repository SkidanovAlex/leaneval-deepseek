import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.localIsomDefs
import Submission.Work.Mostow.betweenVec
import Submission.Work.Mostow.segfunHdist
import Submission.Work.Mostow.segfunHasDerivAt
import Submission.Work.Mostow.segfunSpeed
import Submission.Work.Mostow.compSegfunDeriv
import Submission.Work.Mostow.gH_eq_zero_iff
import Submission.Work.Mostow.ballConvex
import Submission.Work.Mostow.diniEstimate
import Submission.Work.Mostow.propagate
import Submission.Work.Mostow.isometryLipschitz
import Submission.Work.Mostow.localInverse
import Submission.Work.Mostow.uniformLocal
import Submission.Work.Mostow.gluing

/-!
# Area L — `localIsom` : a `C¹` map with isometric differential is an isometry of `ℍⁿ`

Let `F : E n → E n` be `C¹` and suppose its differential is an isometry for the hyperbolic
quadratic form `gH` at every point (`gH (F u) (fderiv ℝ F u v) = gH u v`).  Then `F` preserves
the hyperbolic distance `hdist`.

The proof has three steps.

* `isometryLipschitz` : such a map is `1`-Lipschitz.  Along the image of the explicit unit-speed
  geodesic segment `segfun u v`, the chain rule plus the hypothesis give a curve of unit
  hyperbolic speed; the local estimate `diniEstimate` turns into the global bound
  `hdist (F u) (F v) ≤ hdist u v` through `propagate` (a Dini-derivative argument).

* `localInverse` : it is a local isometry.  The differential is injective (`gH` is positive
  definite), so the inverse function theorem produces a local inverse `G`, whose differential is
  again `gH`-isometric; `G` is `1`-Lipschitz on a ball by the same argument as above, and the
  convexity of hyperbolic balls (`ballConvex`) supplies the geodesic segment inside its domain.

* `uniformLocal` + `gluing` : the local information gives a uniform `δ > 0` along the compact
  segment, and a curve with `hdist (γ s) (γ s') = |s - s'|` for `|s - s'| < δ` is a global
  geodesic (betweenness transitivity `betweenTrans`), so `hdist (F u) (F v) = hdist u v`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

theorem localIsom (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n) :
    LocalIsomProp n := by
  intro F hF hiso u v
  obtain ⟨h1, h2, h3, htri, hcont, -, -, -, -, -, -, -, -⟩ := hI
  have h1lip := isometryLipschitz F hF hiso hcont htri
  rcases eq_or_ne u v with h | huv
  · subst h
    rw [hdist_self', hdist_self']
  · have hdne : hdist u v ≠ 0 := fun h => huv ((h3 u v).mp h)
    -- `F` is an isometry on a ball around each point
    have hloc : ∀ z, ∃ ρ > 0, ∀ x y, hdist z x < ρ → hdist z y < ρ →
        hdist (F x) (F y) = hdist x y := by
      intro z
      obtain ⟨ρ, G, hρ, -, hleft, -, hGlip⟩ := localInverse F hF hiso hcont htri h1lip z
      refine ⟨ρ, hρ, ?_⟩
      intro x y hx hy
      have hFx : hdist (F z) (F x) < ρ := lt_of_le_of_lt (h1lip z x) hx
      have hFy : hdist (F z) (F y) < ρ := lt_of_le_of_lt (h1lip z y) hy
      refine le_antisymm (h1lip x y) ?_
      calc hdist x y = hdist (G (F x)) (G (F y)) := by rw [hleft x hx, hleft y hy]
        _ ≤ hdist (F x) (F y) := hGlip (F x) (F y) hFx hFy
    -- the local information is uniform along the compact segment from `u` to `v`
    obtain ⟨δ, hδ, hloc'⟩ := uniformLocal F u v huv hloc htri
      (fun s s' hs hs' => segfunHdist u v huv s s' hs hs')
    -- a curve whose increments are locally realised is a global geodesic
    have hg := gluing (fun s => F (segfun u v s)) (hdist u v) δ (h1 u v) hδ htri h3 hloc'
    have h0 : (fun s => F (segfun u v s)) 0 = F u := by simp [segfun_zero u v hdne]
    have hd2 : (fun s => F (segfun u v s)) (hdist u v) = F v := by simp [segfun_end u v hdne]
    simpa [h0, hd2] using hg

end Work.Mostow
