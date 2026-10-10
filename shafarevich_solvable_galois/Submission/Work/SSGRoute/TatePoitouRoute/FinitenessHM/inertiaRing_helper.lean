import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# General helper lemmas for the inertia-ring maximality lemma

This file collects elementary ring-theoretic facts used in
`Work.SSGRoute.TatePoitouRoute.FinitenessHM.inertiaRing_span_p_isMaximal`.

The main content is the elementary fact that in a local domain, a root of unity whose order
is invertible and which is congruent to `1` modulo the maximal ideal must be `1`.  This is the
"reduction is injective on prime-to-`p` roots of unity" statement in its cleanest form.
-/

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

/-- **Reduction is injective on roots of unity of invertible order.**

Let `B` be a local domain, `N` a natural number which is a unit of `B` (e.g. `p ∤ N` in a
`p`-adic ring).  If `η ∈ B` satisfies `η ^ N = 1` and `η ≡ 1` modulo the maximal ideal, then
`η = 1`.

The proof is the classical one: writing `η = 1 + δ` with `δ` in the maximal ideal,
`0 = η^N - 1 = (η - 1) * ∑_{i<N} η^i`; the cyclotomic sum is congruent to `N` modulo the maximal
ideal, hence a unit, so `η - 1 = 0`. -/
theorem eq_one_of_pow_eq_one_of_sub_mem_maximalIdeal {B : Type*} [CommRing B] [IsLocalRing B]
    [IsDomain B] {N : ℕ} (hN : IsUnit (N : B)) {η : B} (hpow : η ^ N = 1)
    (hη : η - 1 ∈ IsLocalRing.maximalIdeal B) : η = 1 := by
  set 𝔪 := IsLocalRing.maximalIdeal B with h𝔪
  have hSmem : (∑ i ∈ Finset.range N, η ^ i) - (N : B) ∈ 𝔪 := by
    have h1 : (∑ i ∈ Finset.range N, η ^ i) - (N : B) =
        ∑ i ∈ Finset.range N, (η ^ i - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [h1]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    rw [(mul_geom_sum η i).symm]
    exact 𝔪.mul_mem_right _ hη
  have hSunit : IsUnit (∑ i ∈ Finset.range N, η ^ i) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hS
    have hNmem : (N : B) ∈ 𝔪 := by
      have h2 : (∑ i ∈ Finset.range N, η ^ i) - ((∑ i ∈ Finset.range N, η ^ i) - (N : B))
          ∈ 𝔪 := 𝔪.sub_mem hS hSmem
      simpa using h2
    exact (IsLocalRing.notMem_maximalIdeal.mpr hN) hNmem
  have hS : (η - 1) * (∑ i ∈ Finset.range N, η ^ i) = 0 := by
    rw [mul_geom_sum, hpow, sub_self]
  rcases hSunit with ⟨u, hu⟩
  rw [← hu] at hS
  rcases mul_eq_zero.mp hS with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h u.ne_zero

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
