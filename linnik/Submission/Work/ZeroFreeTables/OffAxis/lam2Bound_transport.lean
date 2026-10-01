/-
# ZeroFreeTables/OffAxis — `lam2Bound_transport`

The height-`L` `λ₂`-bound of the off-axis engine (`Lam2BoundH L χ' c`, `L ≥ 50`) implies the
contract's round-1 `λ₂`-bound `Lam2Bound χ₁ c` for the frozen wide minimiser `(χ₁, ρ₁)`.

No character identification is needed.  `Lam2BoundH L χ' c` excludes the pair
`{χ', χ'⁻¹}`, while `Lam2Bound χ₁ c` excludes `{χ₁, χ₁⁻¹}`; there are two cases.

* `χ' ∈ {χ₁, χ₁⁻¹}`: the two excluded pairs coincide, so `Lam2BoundH L χ' c` applied at
  `(χ, ρ)` gives the conclusion outright (`|Im| ≤ 1 ≤ L` moves `IsZ` into `IsZAt L`).
* `χ' ∉ {χ₁, χ₁⁻¹}`: the numbered pair `(χ₁, ρ₁)` is itself admissible for `Lam2BoundH L χ' c`
  — it is non-principal (`IsMin1`), its zero lies at height `|Im ρ₁| ≤ 50 ≤ L`, and its
  character is neither `χ'` nor `χ'⁻¹`.  Hence `c ≤ λ(ρ₁)`, and the wide minimality of
  `IsMin1` (`|Im| ≤ 1 ≤ 50`) gives `λ(ρ₁) ≤ λ(ρ)` for every working-region zero.

This is the second case that makes the `hL : 50 ≤ L` hypothesis essential: it is exactly what
puts `ρ₁` inside the height-`L` region of the rectangle-height engine.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract.Defs

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

theorem lam2Bound_transport {q : ℕ} [NeZero q] {L : ℝ} (hL : 50 ≤ L)
    {χ₁ χ' : DirichletCharacter ℂ q} {ρ₁ : ℂ} {c : ℝ}
    (hm : Work.LinnikContract2.IsMin1 χ₁ ρ₁)
    (h2 : Work.ZeroFreeTables.Lam2BoundH L χ' c) :
    Work.LinnikContract.Lam2Bound χ₁ c := by
  intro χ ρ hZ hχ1 hχ1'
  have hL1 : (1 : ℝ) ≤ L := by linarith
  -- `IsZ` sits inside `IsZAt L`, since `L ≥ 1`.
  have hZAt : IsZAt L χ ρ := ⟨hZ.1, hZ.2.1, hZ.2.2.trans hL1⟩
  by_cases hc1 : χ' = χ₁
  · -- the two excluded pairs coincide: the height-`L` bound is exactly what is needed
    refine h2 χ ρ hZAt ?_ ?_
    · rw [hc1]; exact hχ1
    · rw [hc1]; exact hχ1'
  · by_cases hc2 : χ' = χ₁⁻¹
    · refine h2 χ ρ hZAt ?_ ?_
      · rw [hc2]; exact hχ1'
      · rw [hc2, inv_inv]; exact hχ1
    · -- the numbered pair itself is admissible for the height-`L` bound
      have hZAt1 : IsZAt L χ₁ ρ₁ := ⟨hm.1.1, hm.1.2.1, hm.1.2.2.trans hL⟩
      have hneχ : χ₁ ≠ χ' := fun h => hc1 h.symm
      have hneχinv : χ₁ ≠ χ'⁻¹ := fun h => hc2 (by rw [h, inv_inv])
      have hc : c ≤ lamOf q ρ₁ := h2 χ₁ ρ₁ hZAt1 hneχ hneχinv
      have hmin : lamOf q ρ₁ ≤ lamOf q ρ :=
        hm.2 χ ρ ⟨hZ.1, hZ.2.1, hZ.2.2.trans (by norm_num)⟩
      exact hc.trans hmin

end Work.ZeroFreeTables.OffAxis
