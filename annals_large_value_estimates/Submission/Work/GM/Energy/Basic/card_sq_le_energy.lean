import Mathlib
import Submission.Work.GM.Energy.Defs

namespace Work.GM.Energy.Basic

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- The energy of any finite set of reals is at least `|W|²`
(the quadruples `(t₁,t₂,t₁,t₂)` all satisfy `|t₁+t₂-t₁-t₂| = 0 ≤ 1`). -/
theorem card_sq_le_energy (W : Finset ℝ) :
    (W.card : ℝ) ^ 2 ≤ (Submission.GM.energy W : ℝ) := by
  -- Work with the underlying `ℕ`-valued inequality and cast at the end.
  have hc : (W ×ˢ W).card = W.card ^ 2 := by rw [Finset.card_product, sq]
  have h : W.card ^ 2 ≤ Submission.GM.energy W := by
    unfold Submission.GM.energy
    rw [← hc]
    -- The diagonal map `(t₁,t₂) ↦ (t₁,t₂,t₁,t₂)` is injective into the quadruples
    -- satisfying `|t₁+t₂-t₁-t₂| = 0 ≤ 1`.
    apply Finset.card_le_card_of_injOn (fun p : ℝ × ℝ => (p.1, p.2, p.1, p.2))
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_product] at hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp.1, hp.2, hp.1, hp.2⟩, by norm_num⟩
    · intro p hp q hq hpq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 hpq.2.1
  calc (W.card : ℝ) ^ 2 = ((W.card ^ 2 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ (Submission.GM.energy W : ℝ) := by exact_mod_cast h

end Work.GM.Energy.Basic
