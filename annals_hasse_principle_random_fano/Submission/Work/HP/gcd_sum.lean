import Mathlib
import Submission.Work.HP.GonLib

namespace Work.HP

/-- The `ℤ`-valued gcd from the `NormalizedGCDMonoid` structure is the cast of `Int.gcd`. -/
lemma int_gcd_cast (x y : ℤ) : ((Int.gcd x y : ℤ)) = gcd x y := by
  rw [← Int.natAbs_gcd x y]
  exact Int.natAbs_of_nonneg (Int.gcd_nonneg x y)

/-- Bézout for `ℤ`: the gcd of two integers is an integer combination of them. -/
lemma gcd_comb (x y : ℤ) : ∃ a b : ℤ, a * x + b * y = gcd x y := by
  have h := Int.gcd_eq_gcd_ab x y
  rw [int_gcd_cast x y] at h
  exact ⟨Int.gcdA x y, Int.gcdB x y, by rw [h]; ring⟩

/-- For any finite set `s`, the gcd of `u` over `s` is a `ℤ`-linear combination
of the `u i`, `i ∈ s`. -/
private lemma gcd_sum_aux {ι : Type*} [DecidableEq ι] (u : ι → ℤ) (s : Finset ι) :
    ∃ c : ι → ℤ, ∑ i ∈ s, c i * u i = s.gcd u := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨x, y, hxy⟩ := gcd_comb (u a) (s.gcd u)
    refine ⟨fun i => if i = a then x else y * c i, ?_⟩
    have hsum : ∑ i ∈ s, (if i = a then x else y * c i) * u i
        = y * ∑ i ∈ s, c i * u i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_right (by rintro rfl; exact ha hi)]
      ring
    rw [Finset.sum_insert ha, hsum, hc, Finset.gcd_insert]
    simpa using hxy

theorem gcd_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → ℤ) :
    ∃ c : ι → ℤ, ∑ i, c i * u i = Finset.univ.gcd u := by
  obtain ⟨c, hc⟩ := gcd_sum_aux u Finset.univ
  exact ⟨c, hc⟩

end Work.HP
