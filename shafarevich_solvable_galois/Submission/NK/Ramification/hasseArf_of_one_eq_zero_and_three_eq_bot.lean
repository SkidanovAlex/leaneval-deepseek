import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

/-- **Hasse–Arf under `G_1 = G_0` and `G_3 = ⊥`.**

If the ramification filtration is constant between levels `0` and `1` (so `i = 1` is *not* a
lower break) and vanishes from level `3` on (so no `i ≥ 3` is a lower break), then the only
possible lower breaks are `i ∈ {0, 1, 2}`.  At these the Herbrand function takes the values

* `φ(0) = 0`,
* `φ(1) = 1`,
* `φ(2) = (g_0 + g_1)/g_0 = (g_0 + g_0)/g_0 = 2`, using `g_1 = g_0`,

all of which are natural numbers; hence `HasseArf` holds.  This is a variant of
`hasseArf_of_ramificationSubgroup_two_eq_bot` in which `G_2` is allowed to be nontrivial: the
hypothesis `G_1 = G_0` supplies the integrality of `φ(2)` instead of `G_2 = ⊥`. -/
theorem hasseArf_of_one_eq_zero_and_three_eq_bot {K L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)]
    (h1 : NK.Ramification.ramificationSubgroup (K := K) A 1 =
      NK.Ramification.ramificationSubgroup (K := K) A 0)
    (h3 : NK.Ramification.ramificationSubgroup (K := K) A 3 = ⊥) :
    NK.Ramification.HasseArf (K := K) A := by
  intro i hi
  rcases lt_or_ge i 3 with hlt | hge
  · interval_cases i
    · exact ⟨0, by simp [herbrand_zero]⟩
    · refine ⟨1, ?_⟩
      rw [herbrand_one A]
      norm_num
    · -- `i = 2`: here `φ(2) = (g_0 + g_1)/g_0 = 2` because `g_1 = g_0`.
      refine ⟨2, ?_⟩
      have hg : lowerIndex (K := K) A 1 = lowerIndex (K := K) A 0 := by
        simp only [lowerIndex, h1]
      rw [herbrand, Finset.sum_range_succ, Finset.sum_range_one, hg]
      have hne : (lowerIndex (K := K) A 0 : ℚ) ≠ 0 := by
        exact_mod_cast Nat.pos_iff_ne_zero.mp (lowerIndex_zero_pos (K := K) A)
      field_simp
      norm_num
  · -- `i ≥ 3`: both `G_i` and `G_{i+1}` are trivial, contradicting `LowerBreak A i`.
    exfalso
    apply hi
    have hb1 : ramificationSubgroup (K := K) A i = ⊥ :=
      le_bot_iff.mp ((ramificationSubgroup_antitone A hge).trans_eq h3)
    have hb2 : ramificationSubgroup (K := K) A (i + 1) = ⊥ :=
      le_bot_iff.mp ((ramificationSubgroup_antitone A (by omega)).trans_eq h3)
    rw [hb1, hb2]

end NK.Ramification
