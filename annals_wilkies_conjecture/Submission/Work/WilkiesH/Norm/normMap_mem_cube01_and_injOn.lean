import Mathlib
import Submission.Work.WilkiesH.Norm.Defs

/-!
# The normalisation map: image in the unit cube, and injectivity on a piece

This file proves the two elementary facts about the coordinatewise normalisation
`normMap σ` (built in `Norm/Defs.lean`) that the counting induction consumes:

* every point of a piece is mapped into the unit cube `cube01 n = [0,1]ⁿ`;
* `normMap σ` is injective on the piece.

Both reduce to the corresponding statement for the single-coordinate map
`shapeMap s` on its region `shapeSet s`, by the case analysis over the four
shapes:

* `pos`    : `t ↦ t`      on `[0,1]`   — image `[0,1]`, injective;
* `neg`    : `t ↦ -t`     on `[-1,0]`  — image `[0,1]`, injective;
* `big`    : `t ↦ t⁻¹`    on `(1,∞)`   — image `(0,1)`, injective (`Inv.inv`);
* `bigNeg` : `t ↦ -t⁻¹`   on `(-∞,-1)` — image `(0,1)`, injective (`Inv.inv`).

Injectivity is exactly why four shapes are used rather than the two regions
`|t| ≤ 1` and `|t| > 1`: the sign of each coordinate is recorded in the piece
and is therefore recoverable from the image.
-/

set_option autoImplicit false

namespace Work.WilkiesH.Norm

/-- Each shape map sends its region into `[0,1]`. -/
lemma shapeMap_mem_Icc {s : NormShape} {t : ℝ} (ht : t ∈ shapeSet s) :
    shapeMap s t ∈ Set.Icc (0 : ℝ) 1 := by
  cases s
  · -- `pos`: the identity on `[0,1]`
    simpa [shapeSet, shapeMap, Set.mem_Icc] using ht
  · -- `neg`: `t ↦ -t` on `[-1,0]`
    simp only [shapeSet, Set.mem_Icc] at ht
    simp only [shapeMap, Set.mem_Icc]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · -- `big`: `t ↦ t⁻¹` on `(1,∞)`
    simp only [shapeSet, Set.mem_Ioi] at ht
    simp only [shapeMap, Set.mem_Icc]
    exact ⟨le_of_lt (inv_pos_of_pos (by linarith)),
      le_of_lt (inv_lt_one_of_one_lt₀ ht)⟩
  · -- `bigNeg`: `t ↦ -t⁻¹` on `(-∞,-1)`, i.e. `t ↦ (-t)⁻¹` with `-t ∈ (1,∞)`
    simp only [shapeSet, Set.mem_Iio] at ht
    have h : (1 : ℝ) < -t := by linarith
    have h2 : (-t)⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_of_lt (inv_pos_of_pos (by linarith)), le_of_lt (inv_lt_one_of_one_lt₀ h)⟩
    show -t⁻¹ ∈ Set.Icc (0 : ℝ) 1
    rw [neg_inv]
    exact h2

/-- Each shape map is injective on its region. -/
lemma shapeMap_injOn (s : NormShape) : Set.InjOn (shapeMap s) (shapeSet s) := by
  cases s
  · -- `pos`: the identity
    intro a _ b _ h
    simpa [shapeMap] using h
  · -- `neg`: `t ↦ -t`
    intro a _ b _ h
    simp only [shapeMap] at h
    linarith
  · -- `big`: `t ↦ t⁻¹`, and `Inv.inv` is injective
    intro a ha b hb h
    simp only [shapeSet, Set.mem_Ioi] at ha hb
    simp only [shapeMap] at h
    exact inv_injective h
  · -- `bigNeg`: `t ↦ -t⁻¹`
    intro a ha b hb h
    simp only [shapeSet, Set.mem_Iio] at ha hb
    simp only [shapeMap] at h
    have h' : a⁻¹ = b⁻¹ := by linarith
    exact inv_injective h'

theorem normMap_mem_cube01_and_injOn {n : ℕ} (σ : Fin n → NormShape) : (∀ x ∈ normPiece σ, normMap σ x ∈ WilkiesDesign.cube01 n) ∧ Set.InjOn (normMap σ) (normPiece σ) := by
  constructor
  · -- coordinatewise application of `shapeMap_mem_Icc`
    intro x hx i
    exact shapeMap_mem_Icc (hx i)
  · -- coordinatewise application of `shapeMap_injOn`
    intro x hx y hy h
    funext i
    exact shapeMap_injOn (σ i) (hx i) (hy i) (by simpa [normMap] using congrFun h i)

end Work.WilkiesH.Norm
