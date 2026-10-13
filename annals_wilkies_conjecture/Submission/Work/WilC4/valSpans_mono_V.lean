import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- The value set of a subset: `ValOf` is monotone in the set. -/
lemma valOf_mono {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {V V' : Set M} (h : V ⊆ V') {y : M} (hy : ValOf V y) : ValOf V' y := by
  obtain ⟨c, hcV, hcne, heq⟩ := hy
  exact ⟨c, h hcV, hcne, heq⟩

theorem valSpans_mono_V {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {S V V' : Set M} {r : ℕ} (h : V ⊆ V') (hs : ValSpans S V' r) : ValSpans S V r := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨x, fun y hy hyV => hx y hy (valOf_mono h hyV)⟩

end Work.WilC4
