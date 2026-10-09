import Mathlib
import Submission.Work.SSGRoute.LocalFieldArith.Prelude
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Approximation of units of a local completion by elements of the number field

For a number field `K`, a height-one prime `Q` of `𝓞 K` and a unit `b` of the `Q`-adic completion
`Q.adicCompletion K`, and for any `M ≥ 1` and `e : ℕ`, there is `t ∈ K`, `t ≠ 0`, such that

* `t` has the same `Q`-adic valuation as `b` (as elements of the completion), and
* `t` approximates `b` to precision `v(b) * exp (-(M + e))`.

The proof is the standard sharpening of the density of `K` in its completion: one first approximates
`b` in the value group (the valuation of `K` at `Q` is surjective onto `ℤ`, hence onto the non-zero
elements of `ℤᵐ⁰`), which produces an element `s ∈ K` with `v s = v b`; then `u = b / s` has
valuation `1`, and one approximates the unit `u` by an element of `K` inside the ball
`{y | v (y - u) < exp (-(M + e))}`.  Since the radius is `< 1`, the approximant automatically has
valuation `1`, so that `t = s * t'` has valuation `v b` and approximates `b`.
-/

namespace Work.SSGRoute

theorem exists_algebraMap_approx (K : Type) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {M : ℕ} (hM : 1 ≤ M)
    (e : ℕ) (b : (Q.adicCompletion K)ˣ) :
    ∃ t : K, t ≠ 0 ∧
      Valued.v (algebraMap K (Q.adicCompletion K) t) = Valued.v ((b : Q.adicCompletion K)) ∧
      Valued.v (algebraMap K (Q.adicCompletion K) t - (b : Q.adicCompletion K)) <
        Valued.v ((b : Q.adicCompletion K)) * WithZero.exp (-(((M + e : ℕ) : ℤ))) := by
  set N : ℤ := -(((M + e : ℕ) : ℤ)) with hN
  set β : Q.adicCompletion K := (b : Q.adicCompletion K) with hβ
  have hβ0 : β ≠ 0 := b.ne_zero
  have hvβ0 : Valued.v β ≠ 0 := (Valuation.ne_zero_iff _).2 hβ0
  have hvβpos : 0 < Valued.v β := lt_of_le_of_ne' zero_le hvβ0
  -- Step A: an element of `K` with the same valuation as `b`.
  obtain ⟨s, hs⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective K Q (Valued.v β)
  have hvs : Valued.v (algebraMap K (Q.adicCompletion K) s) = Valued.v β := by
    rw [Commons.NumberTheory.NumberField.Completion.valued_alg_eq Q s, hs]
  have hφs0 : algebraMap K (Q.adicCompletion K) s ≠ 0 := by
    intro h; rw [h, map_zero] at hvs; exact hvβ0 hvs.symm
  -- Step B: the unit `u = b / s` of the completion.
  set u : Q.adicCompletion K := β / algebraMap K (Q.adicCompletion K) s with hu
  have huval : Valued.v u = 1 := by
    rw [hu, map_div₀, hvs, div_self hvβ0]
  have hmul : algebraMap K (Q.adicCompletion K) s * u = β := by
    rw [hu, ← mul_div_assoc, mul_div_cancel_left₀ β hφs0]
  -- Step C: approximate the unit `u` by an element of `K` to precision `exp N`.
  obtain ⟨t', ht'⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algebraMap_mem_exp_ball Q u N
  have hNneg : N < 0 := by
    rw [hN]
    have : (1 : ℤ) ≤ ((M + e : ℕ) : ℤ) := by exact_mod_cast (by omega : 1 ≤ M + e)
    omega
  have hexpNlt : WithZero.exp N < 1 := by
    rw [← WithZero.exp_zero]
    exact (WithZero.exp_lt_exp).mpr hNneg
  -- The approximant has valuation `1` because the radius is `< v u = 1`.
  have ht'lt : Valued.v (algebraMap K (Q.adicCompletion K) t' - u) < Valued.v u := by
    rw [huval]
    exact lt_of_lt_of_le ht' (le_of_lt hexpNlt)
  have hvalt' : Valued.v (algebraMap K (Q.adicCompletion K) t') = 1 := by
    have hsplit : algebraMap K (Q.adicCompletion K) t' =
        (algebraMap K (Q.adicCompletion K) t' - u) + u := by abel
    rw [hsplit, Valuation.map_add_eq_of_lt_right _ ht'lt, huval]
  have hval1 : Valued.v (algebraMap K (Q.adicCompletion K) (s * t')) = Valued.v β := by
    rw [map_mul, Valuation.map_mul, hvs, hvalt', mul_one]
  have hval2 : Valued.v (algebraMap K (Q.adicCompletion K) (s * t') - β) <
      Valued.v β * WithZero.exp N := by
    have heq : algebraMap K (Q.adicCompletion K) (s * t') - β =
        algebraMap K (Q.adicCompletion K) s * (algebraMap K (Q.adicCompletion K) t' - u) := by
      rw [map_mul, ← hmul]; ring
    rw [heq, Valuation.map_mul, hvs]
    exact mul_lt_mul_of_pos_left ht' hvβpos
  refine ⟨s * t', ?_, ?_, ?_⟩
  · intro h0
    rw [h0] at hval1
    simp only [map_zero] at hval1
    exact hvβ0 hval1.symm
  · simpa [hβ] using hval1
  · simpa [hβ, hN] using hval2

end Work.SSGRoute
