import Mathlib
import Submission.Work.HP.ConicsDefs
import Submission.Work.HP.ConicsLiftDefs

namespace Work.HP.ConicFail

/-- For the prime `p`, reduction modulo `p` detects units of `ZMod (p^2)`: an element is a unit
iff its reduction in `ZMod p` is nonzero. -/
theorem red_unit (p : ℕ) [Fact p.Prime] (T : ZMod (p ^ 2)) (h : Work.HP.Conics.red p T ≠ 0) :
    IsUnit T := by
  have hp : p.Prime := Fact.out
  have hne : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  -- the reduction of `T` is the class of `T.val` modulo `p`
  have h1 : (T.val : ZMod p) ≠ 0 := by
    rw [Work.HP.Conics.red_val] at h
    exact h
  -- hence `p` does not divide `T.val`
  have h2 : ¬ p ∣ T.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact h1
  -- so `T.val` is coprime to `p ^ 2`
  have h3 : (T.val).Coprime (p ^ 2) := by
    rw [Nat.coprime_pow_right_iff (by norm_num : 0 < 2), Nat.coprime_comm,
      hp.coprime_iff_not_dvd]
    exact h2
  -- and an integer coprime to the modulus is a unit
  rwa [← ZMod.natCast_zmod_val T, ZMod.isUnit_iff_coprime]

end Work.HP.ConicFail
