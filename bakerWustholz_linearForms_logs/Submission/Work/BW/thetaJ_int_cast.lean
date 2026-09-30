import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.tijdeman_rat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem thetaJ_int_cast {K : Type*} [Field K] [NumberField K] {r : ℕ} (h D0 : ℕ)
    (Dj : Fin r → ℕ) (J t0 : ℕ) (s : ℤ) (lm : AuxIdx r h D0 Dj) :
    ∃ N : ℤ, (2 : K) ^ (J * (2 * h * ((lm.2.1 : ℕ) + 1))) * (((ulcm h : ℚ) : K)) ^ t0 *
      (((thetaJ h D0 Dj J t0 s lm : ℚ) : K)) = ((N : ℤ) : K) := by
  obtain ⟨N, hN⟩ := tijdeman_rat (2^J) (Nat.one_le_two_pow)
      (s + (2:ℤ)^J * ((lm.1:ℕ):ℤ)) h ((lm.2.1:ℕ)+1) t0
  refine ⟨N, ?_⟩
  have hpt : (((s + (2:ℤ)^J * ((lm.1:ℕ):ℤ) : ℤ) : ℚ) / ((2^J : ℕ) : ℚ))
      = (s:ℚ)/(2:ℚ)^J + ((lm.1:ℕ):ℚ) := by
    push_cast
    field_simp
  have hqpow : (((2^J : ℕ) : ℚ)) ^ (2 * h * ((lm.2.1:ℕ)+1))
      = (2:ℚ) ^ (J * (2*h*((lm.2.1:ℕ)+1))) := by
    push_cast
    rw [← pow_mul]
  have hth : Polynomial.aeval (((s + (2:ℤ)^J * ((lm.1:ℕ):ℤ) : ℤ) : ℚ) / ((2^J : ℕ) : ℚ))
      (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1:ℕ)+1))) = thetaJ h D0 Dj J t0 s lm := by
    rw [thetaJ, thetaRatQ, hpt]
  rw [hqpow, hth] at hN
  exact_mod_cast hN

end Work.BW
