import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.simple_valuation_binary_union

open Set

namespace Commons.Geometry.Convex.Hadwiger

/-- A simple valuation (vanishing on empty-interior convex bodies) on convex
bodies of the real line is additive over a split of an interval:
splitting `[a, b] = [a, c] ∪ [c, b]` at `c` (with `a ≤ c ≤ b`) gives
`φ [a,b] = φ [a,c] + φ [c,b]`.  The overlap `[a,c] ∩ [c,b] = {c}` is a
single point, whose convex body has empty interior, so simplicity makes its
valuation zero and the additivity law reduces to ordinary additivity. -/
theorem valuation_split_interval
    (φ : ConvexBody ℝ → ℝ)
    (hadd : ∀ A B C D : ConvexBody ℝ,
        (A : Set ℝ) = (C : Set ℝ) ∪ (D : Set ℝ) →
        (B : Set ℝ) = (C : Set ℝ) ∩ (D : Set ℝ) → φ A + φ B = φ C + φ D)
    (hsimple : ∀ K : ConvexBody ℝ, interior (K : Set ℝ) = ∅ → φ K = 0)
    {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (Kab : ConvexBody ℝ) (hKab : (Kab : Set ℝ) = Set.Icc a b)
    (Kac : ConvexBody ℝ) (hKac : (Kac : Set ℝ) = Set.Icc a c)
    (Kcb : ConvexBody ℝ) (hKcb : (Kcb : Set ℝ) = Set.Icc c b) :
    φ Kab = φ Kac + φ Kcb := by
  -- the degenerate overlap body `{c} = [c, c]`
  let Kcc : ConvexBody ℝ :=
    ⟨Set.Icc c c, convex_Icc c c, isCompact_Icc, ⟨c, le_rfl, le_rfl⟩⟩
  have hKcc : (Kcc : Set ℝ) = Set.Icc c c := rfl
  have hU : (Kab : Set ℝ) = (Kac : Set ℝ) ∪ (Kcb : Set ℝ) := by
    rw [hKab, hKac, hKcb]
    rw [Set.Icc_union_Icc_eq_Icc hac hcb]
  have hI : (Kcc : Set ℝ) = (Kac : Set ℝ) ∩ (Kcb : Set ℝ) := by
    rw [hKcc, hKac, hKcb]
    rw [Set.Icc_inter_Icc_eq_singleton hac hcb]
    simp
  have hB_int : interior (Kcc : Set ℝ) = ∅ := by
    rw [hKcc]
    rw [interior_Icc]
    simp
  exact simple_valuation_binary_union (V := ℝ) φ hadd hsimple
    (A := Kab) (B := Kcc) (C := Kac) (D := Kcb) hU hI hB_int

end Commons.Geometry.Convex.Hadwiger
