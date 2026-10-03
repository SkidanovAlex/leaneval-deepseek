/-
# `Submission.Work.FIArea7.cardFilterGnormLe`

The number of Gaussian integers in the box `gBox R` whose norm is at most `X` is `≤ 25 X²`
(for `X ≥ 1`):

  `#{z ∈ gBox R : |z|² ≤ X} ≤ 25 X²`.

*Route.*  The condition `|z|² ≤ X` confines `z` to the disc of radius `√X` about the origin;
in coordinates, both `|Re z|` and `|Im z|` are at most `⌊√X⌋`.  Since `z ↦ (Re z, Im z)` is
injective, the count is at most the number of pairs in a square of side `2⌊√X⌋ + 1`:

  `#A ≤ (2⌊√X⌋ + 1)² ≤ (2√X + 1)² ≤ 9X ≤ 25X²`   for `X ≥ 1`

(the middle step uses `⌊√X⌋ ≤ √X` and `2√X + 1 ≤ 3√X`, i.e. `√X ≥ 1`).  The bound holds for
*every* `R`, including `R < 0` (empty box); the box condition is not used at all.
-/
import Mathlib
import Submission.Work.FIPlan.Interface

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Coordinates of `gnorm` and of the box -/

/-- `gnorm` in coordinates: `|z|² = (Re z)² + (Im z)²`. -/
private lemma gnorm_eq_coords (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  simp only [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, pow_two]

/-- The coordinate map `z ↦ (Re z, Im z)` is injective on `ℤ[i]`. -/
private lemma coords_injective : Function.Injective (fun z : GaussianInt => (z.re, z.im)) :=
  fun _a _b h => Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A disc of radius `√X` contains at most `(2√X + 1)²` Gaussian integers: if `|z|² ≤ X` then
both coordinates of `z` lie in `[-⌊√X⌋, ⌊√X⌋]`, and the coordinate map is injective. -/
private lemma card_le_of_gnorm_le (A : Finset GaussianInt) {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ z ∈ A, (Work.FIPlan.gnorm z : ℝ) ≤ X) :
    (A.card : ℝ) ≤ (2 * Real.sqrt X + 1) ^ 2 := by
  set s : ℕ := ⌊Real.sqrt X⌋₊ with hs
  -- each coordinate is at most `√X` in absolute value
  have hcoord : ∀ z ∈ A, ((z.re.natAbs : ℝ)) ≤ Real.sqrt X ∧
      ((z.im.natAbs : ℝ)) ≤ Real.sqrt X := by
    intro z hz
    have h1 : (Work.FIPlan.gnorm z : ℝ) ≤ X := h z hz
    have h2 : ((z.re.natAbs : ℝ)) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
      rw [gnorm_eq_coords z]; push_cast; nlinarith [sq_nonneg ((z.im.natAbs : ℝ))]
    have h3 : ((z.im.natAbs : ℝ)) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
      rw [gnorm_eq_coords z]; push_cast; nlinarith [sq_nonneg ((z.re.natAbs : ℝ))]
    exact ⟨(Real.le_sqrt (by positivity) hX).mpr (le_trans h2 h1),
      (Real.le_sqrt (by positivity) hX).mpr (le_trans h3 h1)⟩
  -- hence the coordinates are bounded by `s = ⌊√X⌋`
  have hs_coord : ∀ z ∈ A, z.re.natAbs ≤ s ∧ z.im.natAbs ≤ s := by
    intro z hz
    obtain ⟨h1, h2⟩ := hcoord z hz
    exact ⟨Nat.le_floor h1, Nat.le_floor h2⟩
  -- so the image of `A` under the coordinate map lies in the square of side `2s+1`
  have hsub : A.image (fun z : GaussianInt => (z.re, z.im)) ⊆
      (Finset.Icc (-(s : ℤ)) (s : ℤ)) ×ˢ (Finset.Icc (-(s : ℤ)) (s : ℤ)) := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨h1, h2⟩ := hs_coord z hz
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_, Finset.mem_Icc.mpr ?_⟩
    · exact abs_le.mp (by rw [Int.abs_eq_natAbs]; exact_mod_cast h1)
    · exact abs_le.mp (by rw [Int.abs_eq_natAbs]; exact_mod_cast h2)
  -- the square has `(2s+1)²` elements
  have hcardIcc : (Finset.Icc (-(s : ℤ)) (s : ℤ)).card = 2 * s + 1 := by
    rw [Int.card_Icc]
    have h' : ((s : ℤ) + 1 - -(s : ℤ)) = ((2 * s + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h', Int.toNat_natCast]
  have hcardprod : ((Finset.Icc (-(s : ℤ)) (s : ℤ)) ×ˢ
      (Finset.Icc (-(s : ℤ)) (s : ℤ))).card = (2 * s + 1) ^ 2 := by
    rw [Finset.card_product, hcardIcc, sq]
  -- numeric comparison `(2⌊√X⌋+1)² ≤ (2√X+1)²`
  have hnum : (((2 * s + 1) ^ 2 : ℕ) : ℝ) ≤ (2 * Real.sqrt X + 1) ^ 2 := by
    have hsle : (s : ℝ) ≤ Real.sqrt X := by
      rw [hs]; exact Nat.floor_le (Real.sqrt_nonneg X)
    have hcast : (((2 * s + 1) ^ 2 : ℕ) : ℝ) = (2 * (s : ℝ) + 1) ^ 2 := by push_cast; ring
    rw [hcast]
    have h1 : 2 * (s : ℝ) + 1 ≤ 2 * Real.sqrt X + 1 := by linarith
    exact pow_le_pow_left₀ (by positivity) h1 2
  calc (A.card : ℝ) = ((A.image (fun z : GaussianInt => (z.re, z.im))).card : ℝ) := by
        rw [Finset.card_image_of_injective _ coords_injective]
    _ ≤ (((Finset.Icc (-(s : ℤ)) (s : ℤ)) ×ˢ (Finset.Icc (-(s : ℤ)) (s : ℤ))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (((2 * s + 1) ^ 2 : ℕ) : ℝ) := by rw [hcardprod]
    _ ≤ (2 * Real.sqrt X + 1) ^ 2 := hnum

/-! ## 2. The count of the boxed disc -/

/-- **The number of Gaussian integers of norm `≤ X` in a box is `≤ 25X²`.**  Only the disc
condition is used: `#A ≤ (2√X+1)² ≤ 9X ≤ 25X²` for `X ≥ 1`. -/
theorem cardFilterGnormLe (R : ℤ) (X : ℝ) (hX : 1 ≤ X) :
    ((Work.FIPlan.gBox R).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ X)).card ≤ 25 * X ^ 2 := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hcard := card_le_of_gnorm_le
    ((Work.FIPlan.gBox R).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ X)) hX0
    (fun z hz => (Finset.mem_filter.mp hz).2)
  -- `(2√X + 1)² ≤ 25X²` for `X ≥ 1`
  have hs : (1 : ℝ) ≤ Real.sqrt X := Real.one_le_sqrt.mpr hX
  have hsquare : (2 * Real.sqrt X + 1) ^ 2 ≤ 25 * X ^ 2 := by
    have h1 : 2 * Real.sqrt X + 1 ≤ 3 * Real.sqrt X := by linarith
    have h4 := pow_le_pow_left₀ (by positivity) h1 2
    have h5 : (3 * Real.sqrt X) ^ 2 = 9 * X := by
      rw [mul_pow, Real.sq_sqrt hX0]; norm_num
    rw [h5] at h4
    nlinarith [h4, hX]
  exact le_trans hcard hsquare

end

end Work.FIArea7
