/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.SignObstruction` — why the MATCH height comparisons have the wrong sign

The formal core of `NOTES_FALSE_match_in.md` / `NOTES_FALSE_match_out.md`.

The model's approximate perturbed Fatou coordinate `Ũ = approxEcal` is a **decreasing** Abel
coordinate of the local model: `Work.PARIMPL.approxEcal_step_rot` says
`approxEcal a κ (u + modelDisp a h u) = approxEcal a κ u − τ + O(‖ζ‖² + λ²)` with
`‖τ‖ = 1`, `‖τ − 1‖ ≤ 1/2` (so `Re τ > 0`), i.e. one iterate *decreases* it.  Both coordinates of
the flower are **increasing**:

* `Work.FatouCoord.IsFatouCoordinateOn f φ P := DifferentiableOn ℂ φ P ∧ ∀ z ∈ P, φ (f z) = φ z + 1`
  (the flower's `φa`), and
* `Work.FatouCoord.ParabolicFlower.Ψ_shift : Ψ (w + 1) = F (Ψ w)` (the flower's `Ψ`).

Consequently an affine comparison `u = c·φ + d` between such a coordinate `u` and a flower
coordinate `φ` has `c = -1`: the two coordinates are **reflections** of one another, and their
Écalle heights compare with opposite signs.  This is corroborated by the (T-e) field of
`Work.PARIMPL.MatchData` itself: it states `Ũ ∘ g = conj ∘ Ũ + β` with `Re β = −1/2`, whereas the
flower's `φa` satisfies `φa ∘ g = conj ∘ φa + 1/2`
(`Work.FatouCoord.IsAntiholomorphicFatouOn`); the two constants are *different*, so `Ũ` and `φa`
cannot differ by an additive constant, and `c = −1` is forced.

The last lemma is the refutation: with `c = -1` the *stated* (M-in) comparison
`Im Ũ = Im φa` on the window forces `Im φa` to be **constant** on it.  Since `Im φa` is not
constant on the (two-dimensional) incoming window, the stated orientation cannot hold; the
corrected orientation `Im Ũ = -Im φa + Im d` does.  See `NOTES_FALSE_match_in.md` §4 for the
numerical certification of an instance.
-/
import Submission.Work.PARIMPL2.ExitTracking

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The affine comparison is a reflection -/

/-- **The Abel step signs force the reflection.**  Let `u` be a *decreasing* Abel coordinate of
`f` on `P` (`u (f z) = u z - 1`) and `φ` an *increasing* one (`φ (f z) = φ z + 1`).  If `u` is
affine in `φ` on `P`, then the coefficient is `-1`.

(The two coordinates are both determined by `f` up to an additive constant and the choice of the
orientation; the orientation is exactly the sign of the Abel step, and it is opposite for the
model's `Ũ` and for the flower's coordinates.) -/
theorem coeff_eq_neg_one_of_abel {f u φ : ℂ → ℂ} {P : Set ℂ} {c d : ℂ}
    (hfmaps : ∀ z ∈ P, f z ∈ P)
    (hu_step : ∀ z ∈ P, u (f z) = u z - 1)
    (hφ_step : ∀ z ∈ P, φ (f z) = φ z + 1)
    (haff : ∀ z ∈ P, u z = c * φ z + d) {z : ℂ} (hz : z ∈ P) :
    c = -1 := by
  have h1 : u (f z) = c * φ (f z) + d := haff (f z) (hfmaps z hz)
  rw [hφ_step z hz, hu_step z hz, haff z hz] at h1
  have h6 : (c * (φ z + 1) + d) - (c * φ z + d - 1) = 0 := sub_eq_zero.mpr h1.symm
  have h7 : (c * (φ z + 1) + d) - (c * φ z + d - 1) = c + 1 := by ring
  rw [h7] at h6
  exact eq_neg_of_add_eq_zero_right (by simpa [add_comm] using h6)

/-- The **reflection** relation: with the coefficient forced to `-1`, the imaginary parts are
opposite up to the constant `Im d`. -/
theorem im_eq_neg_add_of_coeff {u φ : ℂ → ℂ} {P : Set ℂ} {d : ℂ}
    (haff : ∀ z ∈ P, u z = -φ z + d) {z : ℂ} (hz : z ∈ P) :
    (u z).im = -(φ z).im + d.im := by
  rw [haff z hz]
  simp

/-- **The refutation of the stated orientation.**  Under the reflection relation
`u = -φ + d` on `P`, the stated comparison `Im u = Im φ` forces `Im φ = Im d / 2` at every point
of `P`: the stated orientation can only hold on a level set of `Im φ`.  On the incoming window
`Win P R c` of `Work.PARIMPL.MatchData` (a two-dimensional region, `R ≥ 4`), `Im φa` is not
constant — see `NOTES_FALSE_match_in.md` §3–§4 — so `match_in` cannot hold there; the corrected
orientation `|(approxUin P c z).im + (φa z).im| ≤ η` does. -/
theorem im_const_of_im_eq_of_coeff {u φ : ℂ → ℂ} {P : Set ℂ} {d : ℂ}
    (haff : ∀ z ∈ P, u z = -φ z + d) {z z' : ℂ} (hz : z ∈ P) (hz' : z' ∈ P)
    (h : (u z).im = (φ z).im) (h' : (u z').im = (φ z').im) :
    (φ z).im = (φ z').im := by
  have e1 := im_eq_neg_add_of_coeff haff hz
  have e2 := im_eq_neg_add_of_coeff haff hz'
  rw [h] at e1
  rw [h'] at e2
  linarith

/-- The same as a refutation: with the reflection relation, the stated comparison and the
non-constancy of `Im φ` on `P` are contradictory. -/
theorem false_of_stated_orientation {u φ : ℂ → ℂ} {P : Set ℂ} {d : ℂ}
    (haff : ∀ z ∈ P, u z = -φ z + d) {z z' : ℂ} (hz : z ∈ P) (hz' : z' ∈ P)
    (h : (u z).im = (φ z).im) (h' : (u z').im = (φ z').im)
    (hvar : (φ z).im ≠ (φ z').im) :
    False :=
  hvar (im_const_of_im_eq_of_coeff haff hz hz' h h')

end Work.PARIMPL2

end
