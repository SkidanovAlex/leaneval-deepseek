/-
# ZeroFreeTables/OffAxis — `lam3Bound_transport`

The height-`L` `λ₃`-bound of the off-axis engine (`Lam3BoundH L χ' c`, `L ≥ 50`) implies the
contract's round-1 `λ₃`-bound `Lam3Bound χ₁ c` for the frozen wide minimiser `(χ₁, ρ₁)`.

`Lam3BoundH L χ' c` supplies a character `χ₂` and excludes the **two** conjugate pairs
`{χ', χ'⁻¹}` and `{χ₂, χ₂⁻¹}`; `Lam3Bound χ₁ c` excludes `{χ₁, χ₁⁻¹}` and a pair of our own
choosing.  The same two cases as in `lam2Bound_transport` arise, now with a witness to carry.

* `χ' ∈ {χ₁, χ₁⁻¹}`: the two numbered pairs coincide; take `χ₂' := χ₂` and apply the height-`L`
  bound outright (`|Im| ≤ 1 ≤ L` moves `IsZ` into `IsZAt L`).
* `χ' ∉ {χ₁, χ₁⁻¹}`: split on whether `χ₂` is one of `χ₁^{±1}`.
  - `χ₂ ∈ {χ₁, χ₁⁻¹}`: then `{χ₂^{±1}} = {χ₁^{±1}}`, so the *only* pair of `Lam3BoundH L χ'` not
    already excluded by the goal's hypotheses is `{χ'^{±1}}`; take `χ₂' := χ'` and the goal's own
    exclusions `χ ≠ χ'`, `χ ≠ χ'⁻¹` complete the four hypotheses of the height-`L` bound.
  - `χ₂ ∉ {χ₁, χ₁⁻¹}`: then the numbered pair `(χ₁, ρ₁)` is itself admissible for
    `Lam3BoundH L χ' c` — it is non-principal (`IsMin1`), its zero lies at height `|Im ρ₁| ≤ 50 ≤ L`,
    and its character is neither `χ'`, `χ'⁻¹`, `χ₂` nor `χ₂⁻¹`.  Hence `c ≤ λ(ρ₁)`, and the wide
    minimality of `IsMin1` (`|Im| ≤ 1 ≤ 50`) gives `λ(ρ₁) ≤ λ(ρ)` for every working-region zero
    `(χ, ρ)`, whether or not `χ ∈ {χ'^{±1}}`.  Take `χ₂' := χ₂`.

The hypothesis `hL : 50 ≤ L` is used exactly as in `lam2Bound_transport`: it puts the numbered
zero `ρ₁` inside the height-`L` region of the rectangle-height engine, which is what makes the
second case work.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract.Defs

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

/-- `a` is not `b⁻¹` iff `b` is not `a⁻¹` (inversion is injective). -/
private lemma inv_ne_iff {q : ℕ} [NeZero q] {a b : DirichletCharacter ℂ q} :
    a ≠ b⁻¹ ↔ b ≠ a⁻¹ := by
  constructor
  · intro h hb
    exact h (by rw [hb, inv_inv])
  · intro h ha
    exact h (by rw [ha, inv_inv])

theorem lam3Bound_transport {q : ℕ} [NeZero q] {L : ℝ} (hL : 50 ≤ L)
    {χ₁ χ' : DirichletCharacter ℂ q} {ρ₁ : ℂ} {c : ℝ}
    (hm : Work.LinnikContract2.IsMin1 χ₁ ρ₁)
    (h3 : Work.ZeroFreeTables.Lam3BoundH L χ' c) :
    Work.LinnikContract.Lam3Bound χ₁ c := by
  obtain ⟨χ₂, hχ₂⟩ := h3
  have hL1 : (1 : ℝ) ≤ L := by linarith
  -- `IsZ` sits inside `IsZAt L`, since `L ≥ 1`.
  have hmem : ∀ {χ : DirichletCharacter ℂ q} {ρ : ℂ}, IsZ χ ρ → IsZAt L χ ρ :=
    fun hZ => ⟨hZ.1, hZ.2.1, hZ.2.2.trans hL1⟩
  by_cases hc1 : χ' = χ₁
  · -- the two numbered pairs coincide
    refine ⟨χ₂, fun χ ρ hZ h1 h2 h5 h6 => hχ₂ χ ρ (hmem hZ) ?_ ?_ h5 h6⟩
    · rw [hc1]; exact h1
    · rw [hc1]; exact h2
  · by_cases hc2 : χ' = χ₁⁻¹
    · refine ⟨χ₂, fun χ ρ hZ h1 h2 h5 h6 => hχ₂ χ ρ (hmem hZ) ?_ ?_ h5 h6⟩
      · rw [hc2]; exact h2
      · rw [hc2, inv_inv]; exact h1
    · by_cases hχ₂m : χ₂ = χ₁ ∨ χ₂ = χ₁⁻¹
      · -- `{χ₂^{±1}} = {χ₁^{±1}}`: choose `χ₂' := χ'`
        refine ⟨χ', fun χ ρ hZ h1 h2 h5 h6 => hχ₂ χ ρ (hmem hZ) h5 h6 ?_ ?_⟩
        · rcases hχ₂m with h | h
          · rw [h]; exact h1
          · rw [h]; exact h2
        · rcases hχ₂m with h | h
          · rw [h]; exact h2
          · rw [h, inv_inv]; exact h1
      · -- `χ₂` is outside `{χ₁^{±1}}`: the numbered zero itself is admissible
        have hm1 : χ₂ ≠ χ₁ := fun h => hχ₂m (Or.inl h)
        have hm2 : χ₂ ≠ χ₁⁻¹ := fun h => hχ₂m (Or.inr h)
        have hc : c ≤ lamOf q ρ₁ :=
          hχ₂ χ₁ ρ₁ ⟨hm.1.1, hm.1.2.1, hm.1.2.2.trans hL⟩
            (fun h => hc1 h.symm)
            (inv_ne_iff.mpr hc2)
            (fun h => hm1 h.symm)
            (inv_ne_iff.mpr hm2)
        refine ⟨χ₂, fun χ ρ hZ h1 h2 h5 h6 => ?_⟩
        by_cases hχ'in : χ = χ' ∨ χ = χ'⁻¹
        · -- `χ ∈ {χ'^{±1}}`: the wide minimality of `IsMin1` supplies the bound
          have hmin : lamOf q ρ₁ ≤ lamOf q ρ :=
            hm.2 χ ρ ⟨hZ.1, hZ.2.1, hZ.2.2.trans (by norm_num)⟩
          exact hc.trans hmin
        · have hχ'1 : χ ≠ χ' := fun h => hχ'in (Or.inl h)
          have hχ'2 : χ ≠ χ'⁻¹ := fun h => hχ'in (Or.inr h)
          exact hχ₂ χ ρ (hmem hZ) hχ'1 hχ'2 h5 h6

end Work.ZeroFreeTables.OffAxis
