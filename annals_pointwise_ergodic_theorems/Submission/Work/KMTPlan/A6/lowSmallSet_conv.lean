import Mathlib
import Submission.Work.KMTPlan.A6.RandSymbAux

/-!
# `lowSmallSet` is order-convex

The admissible small-scale index set of the low case,

`lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n = I^{max(l₁,l₂),k₁,k₂}(⌊a n⌋) ∧ ⌊a n⌋ ≤ splitCut ρ L`,

is the intersection of a set which is *upward closed* in `n` with one which is *downward
closed* in `n`:

* `I^{l,s₁,s₂}(N) = {N | l, s₁, s₂ ≤ l_{(N)}}` with `l_{(N)} = C₀ LogLog N` is upward closed in
  the scale `N` (the height scale is monotone), and `n ↦ ⌊a n⌋` is monotone for a `Λ`-lacunary
  `a` with `Λ > 1`, so `I^{max(l₁,l₂),k₁,k₂}(⌊a ·⌋)` is upward closed in `n`;
* `⌊a ·⌋ ≤ splitCut ρ L` is downward closed in `n`, again by monotonicity of `n ↦ ⌊a n⌋`.

Hence the set is order-convex, which is the statement `lowSmallSet_conv`: the indicator of
`lowSmallSet` is an interval indicator, as used by `card_jump_le_two`.
-/

namespace Work.KMTPlan.A6

open scoped NNReal

/-- **The index set `I^{l,s₁,s₂}(N)` is upward closed in the scale `N`**: it is the conjunction
of the three inequalities `l, s₁, s₂ ≤ heightScale C₀ N`, and `heightScale C₀` is monotone. -/
theorem lowSmallSet_inIndexSet_mono_scale {C₀ : ℕ} {l s₁ s₂ : ℤ} {N M : ℕ} (hNM : N ≤ M)
    (h : Work.Analysis.EndVar.inIndexSet C₀ l s₁ s₂ N) :
    Work.Analysis.EndVar.inIndexSet C₀ l s₁ s₂ M := by
  obtain ⟨h1, h2, h3⟩ := h
  have hh : (Work.Analysis.EndVar.heightScale C₀ N : ℤ)
      ≤ (Work.Analysis.EndVar.heightScale C₀ M : ℤ) := by
    exact_mod_cast Work.Analysis.EndVar.heightScale_mono C₀ hNM
  exact ⟨le_trans h1 hh, le_trans h2 hh, le_trans h3 hh⟩

/-- **Order-convexity of the admissible small-scale index set of the low case.**

Between two admissible scales every scale is admissible: the index-set part is upward closed
in `n` (so it propagates from the smaller index `n` to `j`), and the cut `⌊a n⌋ ≤ splitCut ρ L`
is downward closed in `n` (so it propagates from the larger index `m` to `j`).  Only the
monotonicity of `n ↦ ⌊a n⌋` is used, hence no lower bound `1 ≤ a n` is needed. -/
theorem lowSmallSet_conv (Λ : NNReal) (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) {ρ : ℝ} {C₀ : ℕ} {l₁ l₂ k₁ k₂ : ℕ}
    {n j m : ℕ} (hnj : n ≤ j) (hjm : j ≤ m)
    (hn : Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n)
    (hm : Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m) :
    Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ j := by
  have hmono : Monotone (fun n : ℕ => Nat.floor (a n)) := lacunary_floor_mono Λ hΛ ha
  rw [lowSmallSet_iff] at hn hm ⊢
  exact ⟨lowSmallSet_inIndexSet_mono_scale (hmono hnj) hn.1,
    le_trans (hmono hjm) hm.2⟩

end Work.KMTPlan.A6
