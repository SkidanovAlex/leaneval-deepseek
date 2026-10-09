import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

/-- **Hasse–Arf when the filtration vanishes at level `2`**: if `G_2 = ⊥` then the only lower
breaks of the ramification filtration can be `i = 0` and `i = 1`, and `φ(0) = 0`, `φ(1) = 1` are
both integers, so the Hasse–Arf condition is satisfied vacuously beyond the first two levels.
This is the analogue of `hasseArf_of_tame` one level further up. -/
theorem hasseArf_of_ramificationSubgroup_two_eq_bot {K L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)]
    (h : NK.Ramification.ramificationSubgroup (K := K) A 2 = ⊥) :
    NK.Ramification.HasseArf (K := K) A := by
  intro i hi
  by_cases h0 : i = 0
  · subst h0
    exact ⟨0, by simp [herbrand_zero]⟩
  by_cases h1 : i = 1
  · subst h1
    refine ⟨1, ?_⟩
    rw [herbrand_one A]
    norm_num
  · -- `i ≥ 2`, so both `G_i` and `G_{i+1}` are trivial, contradicting `LowerBreak A i`.
    exfalso
    apply hi
    have hle2 : 2 ≤ i := by omega
    have hb1 : ramificationSubgroup (K := K) A i = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ramificationSubgroup (K := K) A i
          ≤ ramificationSubgroup (K := K) A 2 := ramificationSubgroup_antitone A hle2
        _ = ⊥ := h
    have hb2 : ramificationSubgroup (K := K) A (i + 1) = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ramificationSubgroup (K := K) A (i + 1)
          ≤ ramificationSubgroup (K := K) A 2 := ramificationSubgroup_antitone A (by omega)
        _ = ⊥ := h
    rw [hb1, hb2]

end NK.Ramification
