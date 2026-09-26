import Mathlib
import Submission.Work.Drive.needleLowEnd
import Submission.Work.Drive.polarDataOfStarShaped
import Submission.Work.Drive.sweepFam_close_chamfer
import Submission.Work.Drive.sweepLoop_injective
import Submission.Work.Drive.chamferVelBranch

/-!
# Auxiliaries for the needle's star-shapedness (`Work.Drive.needleLowEndStarShaped`)

The low end of the chord sweep (`Work.Drive.lowEnd_of_projection_starShaped`,
`Work.Drive.needleToCircle_of_starShaped`) consumes the *geometric* data of a curve: a flattening
direction along which the projection is injective and regular, and a planar star-shapedness datum
(direction map injective on one period, positive angular velocity) about a centre off the curve.

This module holds the vocabulary and (incrementally) the proved geometric lemmas about the
**needle** `t ↦ Work.Drive.sweepFam r D lam δ₁ δ₂ ε t` — the thin lens at the low end of the
sweep — that feed that data.  See `Submission/Work/Drive/NOTES_needle_starShaped.md`.

## Vocabulary

* `Work.Drive.needleFam r D lam δ₁ δ₂ ε` — the needle as a curve `ℝ → Space` (definitionally the
  slice `Work.Drive.sweepFam r D lam δ₁ δ₂ ε`), so that the geometric statements below can mention
  one name instead of repeating the lambda.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- **The needle** at the low end of the chord sweep: the fully smoothed sweep slice at sweep
parameter `ε`.  This is `Work.Drive.sweepFam r D lam δ₁ δ₂ ε` as an element of `ℝ → Space`. -/
def needleFam (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ ε : ℝ) : ℝ → Space :=
  fun t => sweepFam r D lam δ₁ δ₂ ε t

lemma needleFam_apply (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lam δ₁ δ₂ ε t : ℝ) :
    needleFam r D lam δ₁ δ₂ ε t = sweepFam r D lam δ₁ δ₂ ε t := rfl

/-! ## The angular velocity of a concave or convex graph

The polar-starshapedness datum consumed by `Work.Drive.polarData_of_starShaped` contains the
condition that the *angular velocity* `⟪z, J z'⟫` of the curve seen from the centre be positive
(here `z = M - c` is the position relative to the centre and `J` the quarter turn).  For a curve
that is the graph of a concave (or convex) function above a centre lying below (or above) it, that
condition is exactly the elementary "secant versus tangent" inequality for concave functions, proved
here from Mathlib's slope API (`ConcaveOn.slope_le_deriv`, `ConcaveOn.deriv_le_slope`).

The lemma is stated for a real function `f` on a set `S`, with the centre `(xc, yc)`, and the
quantity `⟪z, J z'⟫ = (f x - yc) - deriv f x * (x - xc)` (the coordinate expression of the
cross product of the graph's position and its tangent, both relative to the centre). -/

/-- **A concave graph has positive angular velocity about a centre below it.**
If `f` is concave on `S`, differentiable at every point of `S`, and `yc < f xc`, then for every
`x ∈ S`, `x ≠ xc`, the "angular velocity numerator" `(f x - yc) - deriv f x * (x - xc)` (that is
`⟪z x, J z' x⟫` for `z x = (x - xc, f x - yc)`) is positive. -/
theorem angularVelocity_num_pos_of_concaveOn {f : ℝ → ℝ} {S : Set ℝ} {xc yc : ℝ}
    (hfc : ConcaveOn ℝ S f) (hxd : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hxc : xc ∈ S) (hyc : yc < f xc) :
    ∀ x ∈ S, x ≠ xc → 0 < (f x - yc) - deriv f x * (x - xc) := by
  -- tangent line at the left endpoint is above the graph: `f b - f a ≤ deriv f a * (b - a)`
  have hleft : ∀ a b : ℝ, a ∈ S → b ∈ S → a < b → f b - f a ≤ deriv f a * (b - a) := by
    intro a b ha hb hab
    have h1 := hfc.slope_le_deriv ha hb hab (hxd a ha)
    rw [slope_def_field] at h1
    have h2 : 0 < b - a := sub_pos.mpr hab
    have h3 := mul_le_mul_of_nonneg_right h1 h2.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h2)] at h3
  -- secant is above the derivative at the right endpoint: `deriv f b * (b - a) ≤ f b - f a`
  have hright : ∀ a b : ℝ, a ∈ S → b ∈ S → a < b → deriv f b * (b - a) ≤ f b - f a := by
    intro a b ha hb hab
    have h1 := hfc.deriv_le_slope ha hb hab (hxd b hb)
    rw [slope_def_field] at h1
    have h2 : 0 < b - a := sub_pos.mpr hab
    have h3 := mul_le_mul_of_nonneg_right h1 h2.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h2)] at h3
  intro x hx hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := hleft x xc hx hxc hlt
    nlinarith [hyc, h]
  · have h := hright xc x hxc hx hgt
    nlinarith [hyc, h]

/-- **A convex graph has negative angular velocity numerator about a centre above it.**
If `f` is convex on `S`, differentiable at every point of `S`, and `f xc < yc`, then for every
`x ∈ S`, `x ≠ xc`, the angular velocity numerator `(f x - yc) - deriv f x * (x - xc)` is negative. -/
theorem angularVelocity_num_neg_of_convexOn {f : ℝ → ℝ} {S : Set ℝ} {xc yc : ℝ}
    (hfc : ConvexOn ℝ S f) (hxd : ∀ x ∈ S, DifferentiableAt ℝ f x)
    (hxc : xc ∈ S) (hyc : f xc < yc) :
    ∀ x ∈ S, x ≠ xc → (f x - yc) - deriv f x * (x - xc) < 0 := by
  have hleft : ∀ a b : ℝ, a ∈ S → b ∈ S → a < b → deriv f a * (b - a) ≤ f b - f a := by
    intro a b ha hb hab
    have h1 := hfc.deriv_le_slope ha hb hab (hxd a ha)
    rw [slope_def_field] at h1
    have h2 : 0 < b - a := sub_pos.mpr hab
    have h3 := mul_le_mul_of_nonneg_right h1 h2.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h2)] at h3
  have hright : ∀ a b : ℝ, a ∈ S → b ∈ S → a < b → f b - f a ≤ deriv f b * (b - a) := by
    intro a b ha hb hab
    have h1 := hfc.slope_le_deriv ha hb hab (hxd b hb)
    rw [slope_def_field] at h1
    have h2 : 0 < b - a := sub_pos.mpr hab
    have h3 := mul_le_mul_of_nonneg_right h1 h2.le
    rwa [div_mul_cancel₀ _ (ne_of_gt h2)] at h3
  intro x hx hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := hleft x xc hx hxc hlt
    nlinarith [hyc, h]
  · have h := hright xc x hxc hx hgt
    nlinarith [hyc, h]



/-- **Ray uniqueness for a concave graph** (the star-shapedness half of the polar datum).
If `f` is concave on `S` and the centre `(xc, yc)` lies strictly below the graph (`yc < f xc`), then
for every slope `m` the line `y = yc + m * (x - xc)` meets the graph of `f` in at most one point on
each side of `xc`.  Equivalently: every ray from such a centre meets the graph at most once. -/
theorem eq_unique_on_side_of_concaveOn {f : ℝ → ℝ} {S : Set ℝ} {xc yc m : ℝ}
    (hfc : ConcaveOn ℝ S f) (hxc : xc ∈ S) (hyc : yc < f xc) :
    (∀ x₁ ∈ S, ∀ x₂ ∈ S, xc < x₁ → x₁ < x₂ →
        f x₁ ≠ yc + m * (x₁ - xc) ∨ f x₂ ≠ yc + m * (x₂ - xc)) ∧
    (∀ x₁ ∈ S, ∀ x₂ ∈ S, x₂ < x₁ → x₁ < xc →
        f x₁ ≠ yc + m * (x₁ - xc) ∨ f x₂ ≠ yc + m * (x₂ - xc)) := by
  -- the affine comparison function and the concave difference `G`
  have haff : ConvexOn ℝ S (fun x : ℝ => m * x + (yc - m * xc)) := by
    refine ⟨hfc.1, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    have key : a * (m * x + (yc - m * xc)) + b * (m * y + (yc - m * xc))
        = m * (a * x + b * y) + (yc - m * xc) := by
      linear_combination (yc - m * xc) * hab
    exact le_of_eq key.symm
  set G : ℝ → ℝ := fun x => f x - (m * x + (yc - m * xc)) with hGdef
  have hG : ConcaveOn ℝ S G := hfc.sub haff
  have hGxc : 0 < G xc := by
    show 0 < f xc - (m * xc + (yc - m * xc))
    linarith
  -- a concave function with two zeros is `≤ 0` outside them
  have key : ∀ z₁ ∈ S, ∀ z₂ ∈ S, z₁ < z₂ → G z₁ = 0 → G z₂ = 0 →
      (∀ x ∈ S, x < z₁ → G x ≤ 0) ∧ (∀ x ∈ S, z₂ < x → G x ≤ 0) := by
    intro z₁ hz₁ z₂ hz₂ hlt h₁ h₂
    constructor
    · intro x hx hxz₁
      have hden : 0 < z₂ - x := by linarith
      set t : ℝ := (z₂ - z₁) / (z₂ - x) with ht
      have ht0 : 0 < t := div_pos (by linarith) hden
      have ht1 : t < 1 := by
        rw [ht, div_lt_one hden]; linarith
      have hcomb : t * x + (1 - t) * z₂ = z₁ := by
        rw [ht]; field_simp; ring
      have hmem : t * x + (1 - t) * z₂ ∈ S := by rw [hcomb]; exact hz₁
      have hineq := hG.2 hx hz₂ ht0.le (by linarith : (0:ℝ) ≤ 1 - t) (by ring : t + (1 - t) = 1)
      simp only [smul_eq_mul] at hineq
      rw [hcomb, h₁] at hineq
      nlinarith [hineq, h₂, ht0]
    · intro x hx hz₂x
      have hden : 0 < x - z₁ := by linarith
      set t : ℝ := (z₂ - z₁) / (x - z₁) with ht
      have ht0 : 0 < t := div_pos (by linarith) hden
      have ht1 : t < 1 := by
        rw [ht, div_lt_one hden]; linarith
      have hcomb : (1 - t) * z₁ + t * x = z₂ := by
        rw [ht]; field_simp; ring
      have hmem : (1 - t) * z₁ + t * x ∈ S := by rw [hcomb]; exact hz₂
      have hineq := hG.2 hz₁ hx (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring : (1 - t) + t = 1)
      simp only [smul_eq_mul] at hineq
      rw [hcomb, h₂] at hineq
      nlinarith [hineq, h₁, ht0]
  constructor
  · -- right of `xc`: two solutions would force `G xc ≤ 0`
    intro x₁ hx₁ x₂ hx₂ hxcx₁ hx₁x₂
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hG₁ : G x₁ = 0 := by
      show f x₁ - (m * x₁ + (yc - m * xc)) = 0
      rw [h1]; ring
    have hG₂ : G x₂ = 0 := by
      show f x₂ - (m * x₂ + (yc - m * xc)) = 0
      rw [h2]; ring
    have hle := (key x₁ hx₁ x₂ hx₂ hx₁x₂ hG₁ hG₂).1 xc hxc hxcx₁
    linarith
  · -- left of `xc`: the mirror argument
    intro x₁ hx₁ x₂ hx₂ hx₂x₁ hx₁xc
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hG₁ : G x₁ = 0 := by
      show f x₁ - (m * x₁ + (yc - m * xc)) = 0
      rw [h1]; ring
    have hG₂ : G x₂ = 0 := by
      show f x₂ - (m * x₂ + (yc - m * xc)) = 0
      rw [h2]; ring
    have hle := (key x₂ hx₂ x₁ hx₁ hx₂x₁ hG₂ hG₁).2 xc hxc hx₁xc
    linarith

end Work.Drive
