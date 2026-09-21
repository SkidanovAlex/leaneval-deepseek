import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDefs
import Submission.Work.OddEnvelope.Defs

/-!
# The quantitative objects of the low-slope step

This file fixes the vocabulary of the quantitative part of the paper's Step 3 (the low-slope
step of the odd case), so that the estimates can be stated and delegated independently of the
assembly.

* `gammaDev n ρ` is the *even profile deviation* of the radial function `ρ`:
  `u ↦ u²((ρ u^{2n+2} + ρ(-u)^{2n+2})/2 - 1)`.  For the anchor's radial function `ρ_a` this is
  the even function whose `(2n+1)`-dimensional Radon profile is the anchor's datum deviation
  `radonPhi n ρ_a - ballPhiData`; it is supported (as a *function*) on the gap
  `[tStar, 5/√41]`, and **its sup on the gap is the single number that the crux estimate
  costs** (see `_lsa/NOTES_session.md`).
* `gammaPsi n ρ` is the *even profile deviation* of the second datum:
  `u ↦ u(ρ u^{2n+1} - ρ(-u)^{2n+1})/2`, whose Radon profile is `radonPsi n ρ`.
* `deltaA n ρ = GlueF n ρ - ballPhiData` and `deltaB n ρ = GlueG n ρ` are the *glued datum
  deviations* which the inverse Radon transform has to convert into the radial functions of the
  reconstructed body.
* `cStar = (√(1+(4/5)²))⁻¹ = 5/√41` is the right end of the gap.
-/

namespace Work.OddCurve.LowSlope

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

/-- The right end of the gap: the `c`-image of the slope `4/5`, i.e. `5/√41`. -/
def cStar : ℝ := (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹

/-- The flatness radius of the gap.  The anchor's profile deviation vanishes on the waist
`(0, tStar)`, so on the gap it is bounded by `(profile-derivative bound) * gapR^(n+1)/(n+1)!`
by Taylor's theorem at `tStar`; `gapR` is `cStar - tStar` plus a small safety margin (the radial
point `ρ u * u` may exceed `cStar` by an amount of the order of the radial deviation). -/
def gapR : ℝ := cStar - Work.OddEnvelope.tStar + 1 / 1000

/-- **The even profile deviation** of the radial function `ρ` at the exponent `2n+2` (the first
datum's power). -/
def gammaDev (n : ℕ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  fun u => u ^ 2 * ((ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)) / 2 - 1)

/-- **The even profile deviation** of the radial function `ρ` at the exponent `2n+1` (the second
datum's power). -/
def gammaPsi (n : ℕ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  fun u => u * (ρ u ^ (2 * n + 1) - ρ (-u) ^ (2 * n + 1)) / 2

/-- The deviation of the glued first datum from the ball's datum. -/
def deltaA (n : ℕ) (ρ : ℝ → ℝ) : ℝ → ℝ := fun c => GlueF n ρ c - ballPhiData n c

/-- The glued second datum (the ball's second datum is `0`, so this *is* the deviation). -/
def deltaB (n : ℕ) (ρ : ℝ → ℝ) : ℝ → ℝ := GlueG n ρ

lemma gammaDev_even (n : ℕ) (ρ : ℝ → ℝ) : ∀ u, gammaDev n ρ (-u) = gammaDev n ρ u := by
  intro u
  simp only [gammaDev, neg_sq, neg_neg]
  ring

lemma gammaPsi_even (n : ℕ) (ρ : ℝ → ℝ) : ∀ u, gammaPsi n ρ (-u) = gammaPsi n ρ u := by
  intro u
  simp only [gammaPsi, neg_mul, neg_neg]
  ring

lemma deltaA_def (n : ℕ) (ρ : ℝ → ℝ) (c : ℝ) :
    deltaA n ρ c = GlueF n ρ c - ballPhiData n c := rfl

lemma deltaB_def (n : ℕ) (ρ : ℝ → ℝ) (c : ℝ) : deltaB n ρ c = GlueG n ρ c := rfl

/-- `cStar = 5/√41 < 4/5`: the gap ends strictly before the glue point `4/5`. -/
lemma cStar_lt_four_fifths : cStar < 4 / 5 := by
  have h : Real.sqrt (1 + (4 / 5 : ℝ) ^ 2) ^ 2 = 1 + (4 / 5 : ℝ) ^ 2 :=
    Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt (1 + (4 / 5 : ℝ) ^ 2) := Real.sqrt_pos.mpr (by norm_num)
  rw [cStar, inv_lt_iff_one_lt_mul₀ hpos]
  nlinarith [h, hpos]

/-- `cStar = 5/√41 > 0`. -/
lemma cStar_pos : 0 < cStar := by
  rw [cStar]; positivity

/-- `tStar < cStar`. -/
lemma tStar_lt_cStar : Work.OddEnvelope.tStar < cStar := by
  have h1 : Work.OddEnvelope.tStar = (Real.sqrt (1 + (9 / 10 : ℝ) ^ 2))⁻¹ := by
    simp only [Work.OddEnvelope.tStar, Work.OddEnvelope.profileX, Work.OddEnvelope.tau]
    norm_num
  have h2 : cStar = (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ := rfl
  rw [h1, h2]
  refine (inv_lt_inv₀ (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))).mpr ?_
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

end

end Work.OddCurve.LowSlope
