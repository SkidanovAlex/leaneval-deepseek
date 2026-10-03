import Mathlib
import Submission.Work.FIPlan.Interface

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Counting the Gaussian integers of a disc inside a box

Only the disc condition `|z|² ≤ X` is used: it forces both coordinates of `z` into
`[-⌊√X⌋, ⌊√X⌋]`, and the coordinate map is injective, so the count is at most
`(2⌊√X⌋+1)² ≤ (2√X+1)² ≤ 9X` for `X ≥ 1`. -/

/-- `gnorm` in coordinates: `|z|² = (Re z)² + (Im z)²`. -/
private lemma gnorm_eq_coords' (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  simp only [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, pow_two]

/-- The coordinate map `z ↦ (Re z, Im z)` is injective on `ℤ[i]`. -/
private lemma coords_injective' : Function.Injective (fun z : GaussianInt => (z.re, z.im)) :=
  fun _a _b h => Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A finite set of Gaussian integers all of norm `≤ X` has at most `(2√X + 1)²` elements:
if `|z|² ≤ X` then both coordinates are at most `√X` in absolute value, hence bounded by
`⌊√X⌋`, and the coordinate map is injective. -/
private lemma card_le_of_gnorm_le' (A : Finset GaussianInt) {X : ℝ} (hX : 0 ≤ X)
    (h : ∀ z ∈ A, (Work.FIPlan.gnorm z : ℝ) ≤ X) :
    (A.card : ℝ) ≤ (2 * Real.sqrt X + 1) ^ 2 := by
  set s : ℕ := ⌊Real.sqrt X⌋₊ with hs
  have hcoord : ∀ z ∈ A, ((z.re.natAbs : ℝ)) ≤ Real.sqrt X ∧
      ((z.im.natAbs : ℝ)) ≤ Real.sqrt X := by
    intro z hz
    have h1 : (Work.FIPlan.gnorm z : ℝ) ≤ X := h z hz
    have h2 : ((z.re.natAbs : ℝ)) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
      rw [gnorm_eq_coords' z]; push_cast; nlinarith [sq_nonneg ((z.im.natAbs : ℝ))]
    have h3 : ((z.im.natAbs : ℝ)) ^ 2 ≤ (Work.FIPlan.gnorm z : ℝ) := by
      rw [gnorm_eq_coords' z]; push_cast; nlinarith [sq_nonneg ((z.re.natAbs : ℝ))]
    exact ⟨(Real.le_sqrt (by positivity) hX).mpr (le_trans h2 h1),
      (Real.le_sqrt (by positivity) hX).mpr (le_trans h3 h1)⟩
  have hs_coord : ∀ z ∈ A, z.re.natAbs ≤ s ∧ z.im.natAbs ≤ s := by
    intro z hz
    obtain ⟨h1, h2⟩ := hcoord z hz
    exact ⟨Nat.le_floor h1, Nat.le_floor h2⟩
  have hsub : A.image (fun z : GaussianInt => (z.re, z.im)) ⊆
      (Finset.Icc (-(s : ℤ)) (s : ℤ)) ×ˢ (Finset.Icc (-(s : ℤ)) (s : ℤ)) := by
    intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨h1, h2⟩ := hs_coord z hz
    refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_, Finset.mem_Icc.mpr ?_⟩
    · exact abs_le.mp (by rw [Int.abs_eq_natAbs]; exact_mod_cast h1)
    · exact abs_le.mp (by rw [Int.abs_eq_natAbs]; exact_mod_cast h2)
  have hcardIcc : (Finset.Icc (-(s : ℤ)) (s : ℤ)).card = 2 * s + 1 := by
    rw [Int.card_Icc]
    have h' : ((s : ℤ) + 1 - -(s : ℤ)) = ((2 * s + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h', Int.toNat_natCast]
  have hcardprod : ((Finset.Icc (-(s : ℤ)) (s : ℤ)) ×ˢ
      (Finset.Icc (-(s : ℤ)) (s : ℤ))).card = (2 * s + 1) ^ 2 := by
    rw [Finset.card_product, hcardIcc, sq]
  have hnum : (((2 * s + 1) ^ 2 : ℕ) : ℝ) ≤ (2 * Real.sqrt X + 1) ^ 2 := by
    have hsle : (s : ℝ) ≤ Real.sqrt X := by
      rw [hs]; exact Nat.floor_le (Real.sqrt_nonneg X)
    have hcast : (((2 * s + 1) ^ 2 : ℕ) : ℝ) = (2 * (s : ℝ) + 1) ^ 2 := by push_cast; ring
    rw [hcast]
    have h1 : 2 * (s : ℝ) + 1 ≤ 2 * Real.sqrt X + 1 := by linarith
    exact pow_le_pow_left₀ (by positivity) h1 2
  calc (A.card : ℝ) = ((A.image (fun z : GaussianInt => (z.re, z.im))).card : ℝ) := by
        rw [Finset.card_image_of_injective _ coords_injective']
    _ ≤ (((Finset.Icc (-(s : ℤ)) (s : ℤ)) ×ˢ (Finset.Icc (-(s : ℤ)) (s : ℤ))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = (((2 * s + 1) ^ 2 : ℕ) : ℝ) := by rw [hcardprod]
    _ ≤ (2 * Real.sqrt X + 1) ^ 2 := hnum

/-- **The number of Gaussian integers of norm `≤ X` in any box `gBox R` is at most `9X`
(for `X ≥ 1`).**
Only the disc condition matters: if `|z|² ≤ X` then both coordinates of `z` are at most `√X`, so the
count is at most `(2⌊√X⌋+1)² ≤ (2√X+1)² ≤ 9X`. -/
theorem cardDiscBoxLe (R : ℤ) (X : ℝ) (hX : 1 ≤ X) :
    ((Work.FIPlan.gBox R).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ X)).card ≤ 9 * X := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hcard := card_le_of_gnorm_le'
    ((Work.FIPlan.gBox R).filter (fun z => (Work.FIPlan.gnorm z : ℝ) ≤ X)) hX0
    (fun z hz => (Finset.mem_filter.mp hz).2)
  have hs : (1 : ℝ) ≤ Real.sqrt X := Real.one_le_sqrt.mpr hX
  have hsq : Real.sqrt X ^ 2 = X := Real.sq_sqrt hX0
  have hsquare : (2 * Real.sqrt X + 1) ^ 2 ≤ 9 * X := by nlinarith [hs, hsq]
  exact le_trans hcard hsquare

end

end Work.FIArea7
