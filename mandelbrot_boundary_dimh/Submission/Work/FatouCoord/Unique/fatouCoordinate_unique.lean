import Mathlib
import Submission.Work.FatouCoord.Setup

namespace Work.FatouCoord.Unique

open Work.FatouCoord Set Filter

/-- **Uniqueness of the Fatou coordinate.**

If `φ₁` and `φ₂` are both Fatou coordinates for the same map `f` on the same forward-invariant
set `P`, the orbit of every point of `P` converges to `0`, and the two coordinates agree to
first order at `0` (their difference tends to `0` along `P`), then they agree on all of `P`.

The point is that the difference `φ₁ - φ₂` is invariant under `f`
(`IsFatouCoordinateOn.difference_invariant`), so `φ₁ (f^[n] z) - φ₂ (f^[n] z)` is the constant
sequence `φ₁ z - φ₂ z`; since `f^[n] z → 0` while staying in `P`, this constant sequence must
converge to the limiting value `0` of `φ₁ - φ₂` at `0`. -/
theorem fatouCoordinate_unique {f φ₁ φ₂ : ℂ → ℂ} {P : Set ℂ} (h₁ : IsFatouCoordinateOn f φ₁ P) (h₂ : IsFatouCoordinateOn f φ₂ P) (hP : MapsTo f P P) (hP0 : ∀ z ∈ P, Tendsto (fun n : ℕ => f^[n] z) atTop (nhds 0)) (hlim : Tendsto (fun z => φ₁ z - φ₂ z) (nhdsWithin 0 P) (nhds 0)) : ∀ z ∈ P, φ₁ z = φ₂ z := by
  intro z hz
  -- the orbit of `z` stays in the forward-invariant set `P`
  have horb : ∀ n : ℕ, f^[n] z ∈ P := fun n => mapsTo_iterate_of_mapsTo hP n hz
  -- hence it converges to `0` *within* `P`, so the difference converges to `0` along the orbit
  have hg : Tendsto (fun n : ℕ => f^[n] z) atTop (nhdsWithin 0 P) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hP0 z hz)
      (Eventually.of_forall horb)
  have hcomp := hlim.comp hg
  -- the difference is constant along the orbit, so the limit is `φ₁ z - φ₂ z`
  have hcomp2 : Tendsto (fun _ : ℕ => φ₁ z - φ₂ z) atTop (nhds 0) :=
    hcomp.congr (fun n => by
      simp only [Function.comp_apply]
      exact h₁.difference_invariant_iterate h₂ hP hz n)
  exact sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hcomp2)

end Work.FatouCoord.Unique
