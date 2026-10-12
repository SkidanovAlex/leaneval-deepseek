import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.SmallBoxSliding.Geom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSWE

/-- **Combinatorial core of the clipped-box volume bound.**  Three reals, each `≥ δ` and `≤ L`,
with at most one of them `< L`: the product is at least `L ^ 2 * δ`.  Indeed at least two of the
three equal `L`, and the remaining one is at least `δ`. -/
lemma prod_three_ge {a : Fin 3 → ℝ} {δ L : ℝ} (hδ : ∀ j, δ ≤ a j) (hle : ∀ j, a j ≤ L)
    (hnotwo : ¬ ∃ j j' : Fin 3, j ≠ j' ∧ a j < L ∧ a j' < L) :
    L ^ 2 * δ ≤ ∏ j : Fin 3, a j := by
  rw [Fin.prod_univ_three]
  have h01 : ¬ (a 0 < L ∧ a 1 < L) := fun h => hnotwo ⟨0, 1, by decide, h.1, h.2⟩
  have h02 : ¬ (a 0 < L ∧ a 2 < L) := fun h => hnotwo ⟨0, 2, by decide, h.1, h.2⟩
  have h12 : ¬ (a 1 < L ∧ a 2 < L) := fun h => hnotwo ⟨1, 2, by decide, h.1, h.2⟩
  by_cases h0 : a 0 < L
  · -- coordinate `0` is the (unique) clipped one; `1` and `2` both equal `L`
    have ha1 : a 1 = L := le_antisymm (hle 1) (not_lt.mp fun h1 => h01 ⟨h0, h1⟩)
    have ha2 : a 2 = L := le_antisymm (hle 2) (not_lt.mp fun h2 => h02 ⟨h0, h2⟩)
    rw [ha1, ha2]
    nlinarith [hδ 0, sq_nonneg L]
  · have ha0 : a 0 = L := le_antisymm (hle 0) (not_lt.mp h0)
    rw [ha0]
    by_cases h1 : a 1 < L
    · have ha2 : a 2 = L := le_antisymm (hle 2) (not_lt.mp fun h2 => h12 ⟨h1, h2⟩)
      rw [ha2]
      nlinarith [hδ 1, sq_nonneg L]
    · have ha1 : a 1 = L := le_antisymm (hle 1) (not_lt.mp h1)
      rw [ha1]
      nlinarith [hδ 2, sq_nonneg L]

/-- **The clipped-box volume bound.**  Every side of the sliding box is at least `μ^{-1/3}`
(`hside`), the small-box side `ℓd` dominates `μ^{-1/3}` (`hcℓd`), and at most one of the three
coordinates is *clipped* (`shortSide ℓ d u j < ℓ d`).  Then the volume `∏_j max 0 (shortSide ℓ d u j)`
of `B(u)` is at least `(ℓd)² · μ^{-1/3}`: the (at least) two unclipped coordinates contribute `ℓd`
each, the third at least `μ^{-1/3}`. -/
theorem prod_shortSide_ge {ℓ d μ : ℝ} (hμ : 0 < μ) (hℓd : 0 < ℓ * d)
    (hcℓd : μ ^ (-(1 / 3 : ℝ)) ≤ ℓ * d) {u : EuclideanSpace ℝ (Fin 3)}
    (hside : ∀ j : Fin 3, μ ^ (-(1 / 3 : ℝ)) ≤ Work.SmallBoxSliding.shortSide ℓ d u j)
    (hnotwo : ¬ ∃ j j' : Fin 3, j ≠ j' ∧
      Work.SmallBoxSliding.shortSide ℓ d u j < ℓ * d ∧
      Work.SmallBoxSliding.shortSide ℓ d u j' < ℓ * d) :
    (ℓ * d) ^ 2 * μ ^ (-(1 / 3 : ℝ))
      ≤ ∏ j : Fin 3, max 0 (Work.SmallBoxSliding.shortSide ℓ d u j) := by
  have hδpos : 0 < μ ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hμ _
  -- every side is positive, so the `max 0` is redundant
  have hmax : ∀ j : Fin 3, max 0 (Work.SmallBoxSliding.shortSide ℓ d u j)
      = Work.SmallBoxSliding.shortSide ℓ d u j :=
    fun j => max_eq_right (le_trans (le_of_lt hδpos) (hside j))
  -- every side is at most `ℓd`
  have hle : ∀ j : Fin 3, Work.SmallBoxSliding.shortSide ℓ d u j ≤ ℓ * d := by
    intro j
    rw [Work.SmallBoxSliding.shortSide]
    exact min_le_left _ _
  simp only [hmax]
  exact prod_three_ge hside hle hnotwo

end Work.BoseSWE
