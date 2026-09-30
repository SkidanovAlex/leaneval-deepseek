import Mathlib
import Submission.Work.BMF.liouville.prime_power_twist_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open ArithmeticFunction

/-- When `n` is a prime, the correction term vanishes: the von Mangoldt factor `Λ n / log n`
equals `1`, so the two summands defining `corr` coincide. -/
lemma corr_eq_zero_of_prime {u : ℝ} {n : ℕ} (hp : n.Prime) : corr u n = 0 := by
  have hlog : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
  simp only [corr, vonMangoldt_apply_prime hp, hp, ↓reduceIte]
  rw [div_self (by exact_mod_cast hlog), one_mul, sub_self]

/-- When `n` is not a prime power, the correction term vanishes: `Λ n = 0` and `n` is prime
neither, so both summands defining `corr` are zero. -/
lemma corr_eq_zero_of_not_isPrimePow {u : ℝ} {n : ℕ} (hnp : ¬ IsPrimePow n) : corr u n = 0 := by
  have hΛ : vonMangoldt n = 0 := vonMangoldt_eq_zero_iff.mpr hnp
  have hnp' : ¬ n.Prime := fun hp => hnp hp.isPrimePow
  simp [corr, hΛ, hnp']

theorem corr_ne_zero_imp (u : ℝ) (n : ℕ) (h : corr u n ≠ 0) : IsPrimePow n ∧ ¬ n.Prime :=
  ⟨by_contra fun hnp => h (corr_eq_zero_of_not_isPrimePow hnp),
   fun hp => h (corr_eq_zero_of_prime hp)⟩

end Work.BMF.liouville
