import Mathlib
import Submission.Work.Step7Comm.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Step7Comm

theorem commCQCase_of_arithmetic {f m b c : ℕ} (hA : Work.ThmF.ArithmeticNineTwoSeven)
    (hm : 1 ≤ m) (hf : f = 3 ∨ f = 5) (hcq : c + 1 = f ^ m) (hc : c = 2 ^ b) :
    Work.Step7Comm.CommCQCase f c := by
  have hfodd : Odd f := by rcases hf with h | h <;> · rw [h]; norm_num
  have hf2 : 2 ≤ f := by rcases hf with h | h <;> · rw [h]; norm_num
  have hpow : f ^ m = 2 ^ b + 1 := by rw [← hcq, hc]
  have hkey := hA f m b hfodd hf2 (by omega) hpow
  rcases hf with h3 | h5
  · subst h3
    rcases hkey with h1 | h9
    · rw [h1, pow_one] at hcq
      exact Or.inl ⟨by omega, rfl⟩
    · exact Or.inr (Or.inr ⟨by omega, rfl⟩)
  · subst h5
    rcases hkey with h1 | h9
    · rw [h1, pow_one] at hcq
      exact Or.inr (Or.inl ⟨by omega, rfl⟩)
    · exfalso
      have hmle : m ≤ 1 := by
        by_contra h
        push Not at h
        have h25 : 5 ^ 2 ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) h
        omega
      have hm1 : m = 1 := by omega
      rw [hm1, pow_one] at h9
      omega

end Work.Step7Comm
