import Mathlib
import Submission.Work.Tame.ft10_4

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

/-- An irreducible complex character of a finite group takes a rational value at every
involution (`t ^ 2 = 1`).

Proof sketch: `t ^ 2 = 1` gives `orderOf t ∣ 2`; `Work.Tame.irr_apply_mem_adjoin` with `a = 2`
places `χ t` in `Algebra.adjoin ℚ {z : ℂ | z ^ 2 = 1}`, and this adjoin is `⊥` because
`z ^ 2 = 1` forces `z = ±1`. -/
theorem step7a_rat_involution {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) {t : G} (ht : t ^ 2 = 1) : ∃ q : ℚ, χ t = (q : ℂ) := by
  have hg : orderOf t ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ht
  have hmem : χ t ∈ Algebra.adjoin ℚ ({z : ℂ | z ^ 2 = 1} : Set ℂ) :=
    Work.Tame.irr_apply_mem_adjoin hχ (by norm_num : (0 : ℕ) < 2) hg
  -- `{z : ℂ | z ^ 2 = 1} = {1, -1}`, so the adjoin is the prime subfield `⊥`.
  have hadj : Algebra.adjoin ℚ ({z : ℂ | z ^ 2 = 1} : Set ℂ) = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [Algebra.adjoin_le_iff]
    intro z hz
    rw [Set.mem_ofPred_eq] at hz
    have h : (z - 1) * (z + 1) = 0 := by linear_combination hz
    rcases mul_eq_zero.mp h with h | h
    · have hz1 : z = 1 := by linear_combination h
      rw [hz1]; exact Subalgebra.one_mem _
    · have hz1 : z = -1 := by linear_combination h
      rw [hz1]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
  rw [hadj, Algebra.mem_bot] at hmem
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, hq.symm⟩

end Work.BrauerSuzuki.Q8
