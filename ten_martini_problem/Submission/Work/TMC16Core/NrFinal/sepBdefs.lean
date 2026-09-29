import Mathlib
import Submission.Work.Basic.UniNonres.Defs
import Submission.Work.TMC16Core.Core.uni_nonres3_support

/-!
# Auxiliary lemmas for `sepB_bound`

`sepB_bound` bounds `∑ -log |sin (π (ξ + k i · α))|` over `M` phases whose distance to `ℤ` is
`≥ c` and whose signed representatives are `δ`-separated *inside each sign class*.

The proof splits the index set according to the sign of the signed representative
`ρ i = z i - round (z i) ∈ [-1/2, 1/2]`, applies the single-cluster estimate to each class (the
values `|ρ i|` are then pairwise `δ`-separated and lie in `[c, 1/2]`) and combines the two
classes using `a! b! ≥ (⌊(a+b)/2⌋!)²`.

This file collects the pieces shared by that argument:

* `cls c δ m`: the single-cluster bound (`cls c δ 0 = 0`,
  `cls c δ (m+1) = log (1/(2c)) + m log (1/(2δ)) - log (m!)`);
* `cluster_le_cls`: the single-cluster estimate `cluster_single`/`minsum_finset` phrased with
  `cls`;
* `fracDist_neg` and `fracDist_sub_eq_abs_sub_abs`: elementary manipulations of `fracDist`
  used to transfer the separation hypothesis to the values `|ρ i|` inside a sign class.
-/

namespace Work.TMC16Core.NrFinal

open Work.TMC16Core

/-- Single-cluster bound for `∑ -log (sin (π v))` over `m` points `v ∈ [c,1/2]` that are
pairwise `δ`-separated.  `cls c δ 0 = 0` (an empty cluster costs nothing) and for `m = m' + 1`
points, `cls c δ (m'+1) = log (1/(2c)) + m' log (1/(2δ)) - log (m'!)`. -/
noncomputable def cls (c δ : ℝ) : ℕ → ℝ
  | 0 => 0
  | (m + 1) => Real.log (1 / (2 * c)) + (m : ℝ) * Real.log (1 / (2 * δ))
      - Real.log ((m.factorial : ℕ) : ℝ)

@[simp] theorem cls_zero (c δ : ℝ) : cls c δ 0 = 0 := rfl

theorem cls_succ (c δ : ℝ) (m : ℕ) :
    cls c δ (m + 1) = Real.log (1 / (2 * c)) + (m : ℝ) * Real.log (1 / (2 * δ))
      - Real.log ((m.factorial : ℕ) : ℝ) := rfl

/-- **Single-cluster estimate**, in the form used by `sepB_bound`: for a finite set of indices
whose values lie in `[c, 1/2]` and are pairwise `δ`-separated, the sum of the logarithmic
weights is at most `cls c δ (card)`. -/
theorem cluster_le_cls {ι : Type*} [DecidableEq ι] {S : Finset ι} {v : ι → ℝ} {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ)
    (hb : ∀ p ∈ S, c ≤ v p ∧ v p ≤ 1 / 2)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → δ ≤ |v p - v q|) :
    ∑ p ∈ S, -Real.log (Real.sin (Real.pi * (v p))) ≤ cls c δ S.card := by
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0]; simp
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hmin := Work.TMC16Core.Core.minsum_finset hpos hc hδ hb hsep
    rw [hm] at hmin ⊢
    simpa [cls_succ] using hmin

/-- `fracDist` is an even function. -/
theorem fracDist_neg (x : ℝ) : fracDist (-x) = fracDist x := by
  refine le_antisymm ?_ ?_
  · have h := round_le (-x) (-(round x))
    have h2 : |(-x) - ((-(round x) : ℤ) : ℝ)| = fracDist x := by
      have hc : (-x) - ((-(round x) : ℤ) : ℝ) = -(x - ((round x : ℤ) : ℝ)) := by
        push_cast; ring
      rw [hc, abs_neg]
      rfl
    rw [h2] at h
    exact h
  · have h := round_le x (-(round (-x)))
    have h2 : |x - ((-(round (-x)) : ℤ) : ℝ)| = fracDist (-x) := by
      have hc : x - ((-(round (-x)) : ℤ) : ℝ) = -((-x) - ((round (-x) : ℤ) : ℝ)) := by
        push_cast; ring
      rw [hc, abs_neg]
      rfl
    rw [h2] at h
    exact h

/-- If `x`, `y` have the same strict sign and `|x|, |y| ≤ 1/2`, then
`fracDist (x - y) = ||x| - |y||`. -/
theorem fracDist_sub_eq_abs_sub_abs {x y : ℝ} (hxy : 0 < x * y) (hx : |x| ≤ 1 / 2)
    (hy : |y| ≤ 1 / 2) : fracDist (x - y) = |(|x| - |y|)| := by
  rcases mul_pos_iff.mp hxy with ⟨hx0, hy0⟩ | ⟨hx0, hy0⟩
  · have hxb : x ≤ 1 / 2 := (abs_le.mp hx).2
    have hyb : y ≤ 1 / 2 := (abs_le.mp hy).2
    have hlt : |x - y| < 1 / 2 := by
      rw [abs_lt]; exact ⟨by linarith, by linarith⟩
    have hround : round (x - y) = 0 :=
      round_eq_zero_iff.mpr ⟨by linarith [(abs_lt.mp hlt).1], (abs_lt.mp hlt).2⟩
    rw [Work.TMC16Core.fracDist, hround, Int.cast_zero, sub_zero,
      abs_of_pos hx0, abs_of_pos hy0]
  · have hxa : -(1 / 2 : ℝ) ≤ x := (abs_le.mp hx).1
    have hya : -(1 / 2 : ℝ) ≤ y := (abs_le.mp hy).1
    have hlt : |(|x| - |y|)| < 1 / 2 := by
      rw [abs_lt]
      constructor
      · rw [abs_of_neg hx0, abs_of_neg hy0]; linarith
      · rw [abs_of_neg hx0, abs_of_neg hy0]; linarith
    have hround : round (|x| - |y|) = 0 :=
      round_eq_zero_iff.mpr ⟨by linarith [(abs_lt.mp hlt).1], (abs_lt.mp hlt).2⟩
    have h1 : fracDist (|x| - |y|) = |(|x| - |y|)| := by
      rw [Work.TMC16Core.fracDist, hround, Int.cast_zero, sub_zero]
    have h2 : x - y = -(|x| - |y|) := by
      rw [abs_of_neg hx0, abs_of_neg hy0]; ring
    rw [h2, fracDist_neg, h1]

end Work.TMC16Core.NrFinal
