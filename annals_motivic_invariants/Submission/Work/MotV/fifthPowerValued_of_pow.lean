import Mathlib
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

/-- **Bezout for `5`.**  If `5 ∤ k` then `k` admits a multiplicative inverse `n` modulo `5` with
quotient `c`: `n * k = 5 * c + 1`.  (`k = 0` is excluded by the hypothesis, so `n ≥ 1`
automatically.)  Proof by the four possible residues of `k` mod `5`. -/
private lemma exists_mul_eq_five_mul_add_one {k : ℕ} (hk : ¬ (5 : ℕ) ∣ k) :
    ∃ n c : ℕ, n * k = 5 * c + 1 := by
  have hkmod : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by
    have hlt : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
    have hne : k % 5 ≠ 0 := fun h => hk (Nat.dvd_of_mod_eq_zero h)
    omega
  have hd := Nat.div_add_mod k 5
  rcases hkmod with h | h | h | h
  · exact ⟨1, k / 5, by omega⟩
  · exact ⟨3, 3 * (k / 5) + 1, by omega⟩
  · exact ⟨2, 2 * (k / 5) + 1, by omega⟩
  · exact ⟨4, 4 * (k / 5) + 3, by omega⟩

/-- **Fifth-power-valuedness descends through powers coprime to `5`.**

If `g ^ k` has a fifth-power value at every `ℤᵐ⁰`-valued valuation trivial on the constants `𝕜`,
and `5 ∤ k`, then so does `g`.

Route.  `FifthPowerValued 𝕜 g` is `∀ v : Valuation F ℤᵐ⁰, TrivOn 𝕜 v → ∃ u, v g = (v u) ^ 5`
(`Submission/Work/MotV/Defs.lean`); `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`.  Fix `v` and `u` with
`(v g) ^ k = (v u) ^ 5` (from `h` and `Valuation.map_pow`).  Since `5 ∤ k` there are `n ≥ 1`,
`c ≥ 0` with `n * k = 5 * c + 1` (e.g. `n` the representative of `k⁻¹` mod `5` in `{1,2,3,4}`,
`c = (n*k - 1)/5`); then `u ^ n / g ^ c` is the required fifth root:
`(v (u ^ n / g ^ c)) ^ 5 = (v u) ^ (5*n) / (v g) ^ (5*c) = (v g) ^ (n*k - 5*c) = v g`
(using `Valuation.map_mul`, `map_div`, `map_inv`, `map_pow`, `zpow`/`pow` bookkeeping).
The case `g = 0` is separate: then `v g = 0` and `u = 0` works. -/
theorem fifthPowerValued_of_pow {𝕜 F : Type*} [Field 𝕜] [Field F] [Algebra 𝕜 F]
    {k : ℕ} (hk : ¬ (5 : ℕ) ∣ k) {g : F}
    (h : FifthPowerValued 𝕜 (g ^ k)) : FifthPowerValued 𝕜 g := by
  intro v hv
  obtain ⟨u, hu⟩ := h v hv
  rw [Valuation.map_pow] at hu
  -- `hu : (v g) ^ k = (v u) ^ 5`
  by_cases hg : g = 0
  · -- the zero case: `v g = 0 = (v 0) ^ 5`
    subst hg
    exact ⟨0, by simp⟩
  · -- `g ≠ 0`, so `v g ≠ 0` and `u ^ n / g ^ c` is a fifth root of `g`
    have hA : v g ≠ 0 := fun hz => hg ((Valuation.zero_iff v).mp hz)
    obtain ⟨n, c, hn⟩ := exists_mul_eq_five_mul_add_one hk
    refine ⟨u ^ n / g ^ c, ?_⟩
    rw [Valuation.map_div, Valuation.map_pow, Valuation.map_pow]
    -- `(v g) ^ k = (v u) ^ 5` and `n * k = 5 * c + 1` give `(v u) ^ (5 * n) = (v g) ^ (5 * c + 1)`
    have hkey : (v u) ^ (5 * n) = (v g) ^ (5 * c + 1) := by
      rw [pow_mul, ← hu, ← pow_mul, mul_comm k n, hn]
    rw [div_eq_mul_inv, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm n 5,
      mul_comm c 5, hkey, pow_succ, mul_comm (v g ^ (5 * c)) (v g),
      mul_inv_cancel_right₀ (pow_ne_zero (5 * c) hA) (v g)]

end Work.MotV
