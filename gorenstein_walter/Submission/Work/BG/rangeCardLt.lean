import Mathlib
import Submission.Work.BG.Glauberman

namespace Work.BG

/-- **BG-L4, proved.**  The restricted action `φ₁` on `U₁ = fixedSubgroup (φ s₀)` has strictly
smaller image than `φ`, because `ker φ ≤ ker φ₁` and `s₀ ∈ ker φ₁ \ ker φ` as soon as
`φ s₀ ≠ 1`.

`φ₁ s₀ = 1` is forced by the hypotheses: `φ₁ s₀` acts on `U₁` as `φ s₀`, which fixes `U₁`
pointwise.  Hence `ker φ ≤ ker φ₁` while `s₀ ∉ ker φ`, so `ker φ < ker φ₁`.  Now
`S ⧸ ker φ ≃* φ.range` (both `φ` and `φ₁`) and `H.index = Nat.card (S ⧸ H)`, while
`Subgroup.index_strictAnti` says a strictly larger subgroup has strictly smaller index. -/
theorem rangeCardLt : Work.BG.RangeCardLtProp := by
  intro S U _ _ _ φ s₀ hs₀ φ₁ hφ₁
  -- `ker φ ≤ ker φ₁`: on `ker φ` the restricted action is trivial.
  have hker_le : φ.ker ≤ φ₁.ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    ext u
    rw [hφ₁, hs]
    rfl
  -- `s₀` lies in `ker φ₁`: `φ₁ s₀` restricts `φ s₀`, which fixes `U₁` pointwise.
  have hs₀_mem : s₀ ∈ φ₁.ker := by
    rw [MonoidHom.mem_ker]
    ext u
    rw [hφ₁]
    simpa using Work.BG.mem_fixedSubgroup.mp u.2
  -- but `s₀ ∉ ker φ` by hypothesis.
  have hs₀_notmem : s₀ ∉ φ.ker := by
    rw [MonoidHom.mem_ker]; exact hs₀
  have hlt : φ.ker < φ₁.ker :=
    lt_of_le_of_ne hker_le (fun h => hs₀_notmem (h ▸ hs₀_mem))
  have hcard := Subgroup.index_strictAnti hlt
  simp only [Subgroup.index_eq_card] at hcard
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ₁).toEquiv,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at hcard
  exact hcard

end Work.BG
