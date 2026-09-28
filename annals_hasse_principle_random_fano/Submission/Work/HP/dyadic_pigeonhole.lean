import Mathlib

namespace Work.HP

/-- Dyadic pigeonhole: for any `0 < t ≤ M` there is a dyadic scale `M / 2 ^ ℓ`
lying in the window `[t/2, t)`. -/
theorem dyadic_pigeonhole (M t : ℝ) (hM : 0 < M) (ht : 0 < t) (htM : t ≤ M) :
    ∃ ℓ : ℕ, M / 2 ^ ℓ < t ∧ t ≤ 2 * (M / 2 ^ ℓ) := by
  have hex : ∃ l : ℕ, M / 2 ^ l < t := by
    obtain ⟨n, hn⟩ :=
      pow_unbounded_of_one_lt (M / t) (y := (2 : ℝ)) (show (1 : ℝ) < 2 by norm_num)
    exact ⟨n, by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)]
      have h2 : M < 2 ^ n * t := (div_lt_iff₀ ht).1 hn
      linarith⟩
  let P : ℕ → Prop := fun l => M / 2 ^ l < t
  have hP : ∃ l, P l := hex
  set l := Nat.find hP with hl
  have hspec : P l := Nat.find_spec hP
  have hl0 : l ≠ 0 := by
    intro h
    have hp := hspec
    simp only [P, h, pow_zero, div_one] at hp
    linarith
  have hprev : ¬ P (l - 1) := Nat.find_min hP (Nat.pred_lt hl0)
  have htle : t ≤ M / 2 ^ (l - 1) := not_lt.mp hprev
  have hpow : (2 : ℝ) ^ l = 2 ^ (l - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hl0)]
  have heq : 2 * (M / 2 ^ l) = M / 2 ^ (l - 1) := by
    rw [hpow, div_mul_eq_div_div]
    ring
  exact ⟨l, hspec, by rw [heq]; exact htle⟩

end Work.HP
