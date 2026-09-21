import Mathlib
import Submission.Work.OddCurve.LowSlope.Datum
import Submission.Work.OddCurve.LowSlope.radonInverse_radonPsi
import Submission.Work.OddCurve.LowSlope.contDiffOn_radonPhi_Icc

/-!
# The glued Radon data of the low-slope step of the odd case (paper Step 3)

The paper's Step 3 keeps the anchor's Radon data on the cap `|c| < 4/5` and replaces them by the
ball's below (`LowSlope/Datum.lean`, `gluedPhi`, `gluedPsi`), then reconstructs the radial
functions `R, r` of the new body from the *inverse* Radon transform of the glued data, through
the two-power system

`R^{2n+2} + r^{2n+2} = Φ_h(α)/cos²α`,  `R^{2n+1} - r^{2n+1} = Ψ_h(α)/cos α`.

This file fixes the notation: with `ρ` the radial function of the anchor body,

* `GlueF n ρ` is the glued datum as an *even* function of `u = cos α`,
* `GluePhi n ρ`, `GluePsi n ρ` are `2 𝓡^{-1}` of the two glued data at the normal of angle `α`,
* `GlueA n ρ`, `GlueB n ρ` are the deviations `Φ_h/cos² - 2`, `Ψ_h/cos` of the two-power system.

The two identifications that make the construction work are `GlueA_eq` and `GlueB_eq` below (to be
proved): on the cap `cos α < 4/5` the glued datum is the anchor's, so the reconstructed
combination is the anchor's radial function, i.e.

`GlueA α = ρ (cos α)^{2n+2} + ρ (-cos α)^{2n+2} - 2`,
`GlueB α = ρ (cos α)^{2n+1} - ρ (-cos α)^{2n+1}`,

and consequently the smallness of `GlueA`, `GlueB` is exactly the `C²`-closeness of the anchor's
radial function to `1` (i.e. of the anchor's curve to the semicircle's).
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The glued first datum as an even function of `u = cos α`. -/
def GlueF (n : ℕ) (ρ : ℝ → ℝ) : ℝ → ℝ := fun u => gluedPhi n (radonPhi n ρ) |u|

/-- The glued second datum as an even function of `u = cos α`. -/
def GlueG (n : ℕ) (ρ : ℝ → ℝ) : ℝ → ℝ := fun u => gluedPsi (radonPsi n ρ) |u|

/-- `2 𝓡^{-1}` of the glued first datum, at the normal of angle `α`. -/
def GluePhi (n : ℕ) (ρ : ℝ → ℝ) (α : ℝ) : ℝ :=
  2 * Work.OddRadon.radonInverse n (GlueF n ρ) (Real.cos α)

/-- `2 𝓡^{-1}` of the glued second datum, at the normal of angle `α`. -/
def GluePsi (n : ℕ) (ρ : ℝ → ℝ) (α : ℝ) : ℝ :=
  2 * Work.OddRadon.radonInverse n (GlueG n ρ) (Real.cos α)

/-- The deviation `Φ_h(α)/cos²α - 2` of the first two-power equation. -/
def GlueA (n : ℕ) (ρ : ℝ → ℝ) (α : ℝ) : ℝ := GluePhi n ρ α / Real.cos α ^ 2 - 2

/-- The deviation `Ψ_h(α)/cos α` of the second two-power equation. -/
def GlueB (n : ℕ) (ρ : ℝ → ℝ) (α : ℝ) : ℝ := GluePsi n ρ α / Real.cos α

/-- **The radial function of the reconstructed body** from the solution `(R,r)` of the two-power
system: `ρ u = R (arccos u)` for `u ≥ 0` and `ρ u = r (arccos (-u))` for `u ≤ 0`. -/
def rhoNew (R r : ℝ → ℝ) : ℝ → ℝ := fun u => if 0 ≤ u then R (Real.arccos u) else r (Real.arccos (-u))

lemma rhoNew_of_nonneg {R r : ℝ → ℝ} {u : ℝ} (hu : 0 ≤ u) : rhoNew R r u = R (Real.arccos u) :=
  if_pos hu

lemma rhoNew_of_neg {R r : ℝ → ℝ} {u : ℝ} (hu : u < 0) :
    rhoNew R r u = r (Real.arccos (-u)) := if_neg (not_le.mpr hu)

lemma GlueF_even (n : ℕ) (ρ : ℝ → ℝ) : ∀ u, GlueF n ρ (-u) = GlueF n ρ u := by
  intro u; simp [GlueF]

lemma GlueG_even (n : ℕ) (ρ : ℝ → ℝ) : ∀ u, GlueG n ρ (-u) = GlueG n ρ u := by
  intro u; simp [GlueG]

end

end Work.OddCurve.LowSlope
