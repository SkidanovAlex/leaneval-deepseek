import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The congruence ("unique minimum") argument for the exponent of the different

Let `R` be a Dedekind domain, `P` a nonzero prime ideal and `ordAt P x` the `P`-adic order of
`x : R` (the exponent of `P` in the factorisation of the principal ideal `(x)`).

The classical bound on the exponent of `P` in a different ideal reduces to the following elementary
fact.  If `τ 0, …, τ (e-1) : R` are such that the orders of the non-zero ones are pairwise *distinct*
modulo `e`, then the order of the sum `Σ τ j` equals the minimum of the orders, and is therefore at
most the order of any particular summand.  In the application the `τ j` are the summands
`(j+1) · f.coeff (j+1) · π^j` of `f'(π)` for a monic polynomial `f` of degree `e` whose coefficients
(and whose `j+1`) have `P`-adic order divisible by `e`, and `π` a uniformiser (`ordAt P π = 1`);
then `ordAt P (τ j) ≡ j (mod e)`, so the hypothesis is met, and the order of `f'(π)` is bounded by
the order of the leading summand `e · π^(e-1)`.
-/

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open WithZero Multiplicative

section Ord

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- The `P`-adic order of an element of a Dedekind domain: the exponent of the prime ideal `P` in
the factorisation of the principal ideal `(x)`.  For `x = 0` this is `0` by convention. -/
noncomputable def ordAt (P : Ideal R) (x : R) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {x})).count P

variable (v : IsDedekindDomain.HeightOneSpectrum R)

lemma ordAt_zero : ordAt v.asIdeal (0 : R) = 0 := by
  rw [ordAt, Ideal.span_singleton_eq_bot.mpr rfl, ← Ideal.zero_eq_bot,
    UniqueFactorizationMonoid.normalizedFactors_zero, Multiset.count_zero]

lemma ordAt_one : ordAt v.asIdeal (1 : R) = 0 := by
  rw [ordAt, Ideal.span_singleton_one, ← Ideal.one_eq_top,
    UniqueFactorizationMonoid.normalizedFactors_one, Multiset.count_zero]

lemma ordAt_eq_multiplicity {x : R} (hx : x ≠ 0) :
    ordAt v.asIdeal x = multiplicity v.asIdeal (Ideal.span {x}) :=
  IsDedekindDomain.HeightOneSpectrum.count_normalizedFactors_eq_multiplicity
    (show Ideal.span {x} ≠ ⊥ by simpa [Ideal.span_singleton_eq_bot] using hx) v

/-- Membership in the powers of `P` is the same as a lower bound on the `P`-adic order. -/
lemma mem_pow_iff_le_ordAt {x : R} (hx : x ≠ 0) (n : ℕ) :
    x ∈ v.asIdeal ^ n ↔ n ≤ ordAt v.asIdeal x := by
  rw [← v.intValuation_le_pow_iff_mem x n, v.intValuation_eq_exp_neg_multiplicity hx,
    ordAt_eq_multiplicity v hx]
  constructor
  · intro h
    have h' : -(multiplicity v.asIdeal (Ideal.span {x}) : ℤ) ≤ -(n : ℤ) := exp_le_exp.mp h
    omega
  · intro h
    exact exp_le_exp.mpr (by omega)

/-- The `P`-adic order of a product is the sum of the orders. -/
lemma ordAt_mul {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordAt v.asIdeal (x * y) = ordAt v.asIdeal x + ordAt v.asIdeal y := by
  have h1 : Ideal.span {x} ≠ (0 : Ideal R) := by
    intro h
    rw [Ideal.zero_eq_bot] at h
    exact hx (Ideal.span_singleton_eq_bot.mp h)
  have h2 : Ideal.span {y} ≠ (0 : Ideal R) := by
    intro h
    rw [Ideal.zero_eq_bot] at h
    exact hy (Ideal.span_singleton_eq_bot.mp h)
  rw [ordAt, ← Ideal.span_singleton_mul_span_singleton x y,
    UniqueFactorizationMonoid.normalizedFactors_mul h1 h2, Multiset.count_add]
  rfl

/-- The `P`-adic order of a power. -/
lemma ordAt_pow {x : R} (hx : x ≠ 0) (n : ℕ) :
    ordAt v.asIdeal (x ^ n) = n * ordAt v.asIdeal x := by
  induction n with
  | zero => rw [pow_zero, ordAt_one, Nat.zero_mul]
  | succ n ih =>
    rw [pow_succ, ordAt_mul v (pow_ne_zero _ hx) hx, ih, Nat.succ_mul]

end Ord

section Sum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- **The congruence ("unique minimum") argument.**  Let `τ 0, …, τ (e-1)` be elements of a
Dedekind domain whose `P`-adic orders are pairwise distinct modulo `e` (for the non-zero ones), and
suppose the last summand has order `e * k + e - 1`.  Then the order of the sum `Σ τ j` is at most
`e * k + e - 1`. -/
theorem ordAt_sum_le {e k : ℕ} (he : 0 < e) (v : IsDedekindDomain.HeightOneSpectrum R)
    (τ : ℕ → R)
    (hcong : ∀ j, j < e → τ j ≠ 0 → ordAt v.asIdeal (τ j) % e = j % e)
    (hlast : ordAt v.asIdeal (τ (e - 1)) = e * k + e - 1) :
    ordAt v.asIdeal (∑ j ∈ Finset.range e, τ j) ≤ e * k + e - 1 := by
  classical
  rcases eq_or_ne (τ (e - 1)) 0 with hlast0 | hlastne
  · -- then `e = 1`, `k = 0` and the sum vanishes
    rw [hlast0, ordAt_zero] at hlast
    have hk1 : e * (k + 1) = 1 := by
      rw [Nat.mul_succ]; omega
    have he1 : e = 1 := by
      have h2 : e ≤ e * (k + 1) := Nat.le_mul_of_pos_right e (by omega)
      rw [hk1] at h2
      omega
    subst he1
    rw [Finset.sum_range_one]
    rw [show τ 0 = 0 from by simpa using hlast0, ordAt_zero]
    omega
  · set S : Finset ℕ := (Finset.range e).filter (fun j => τ j ≠ 0) with hS
    have hmemS : ∀ j, j ∈ S ↔ j < e ∧ τ j ≠ 0 := by
      intro j; rw [hS, Finset.mem_filter, Finset.mem_range]
    have hmemLast : e - 1 ∈ S := (hmemS _).mpr ⟨by omega, hlastne⟩
    obtain ⟨j₀, hj₀S, hj₀min⟩ := Finset.exists_min_image S (fun j => ordAt v.asIdeal (τ j))
      ⟨e - 1, hmemLast⟩
    have hj₀lt : j₀ < e := ((hmemS j₀).mp hj₀S).1
    have hj₀ne : τ j₀ ≠ 0 := ((hmemS j₀).mp hj₀S).2
    set N : ℕ := ordAt v.asIdeal (τ j₀) with hN
    -- every summand lies in `P ^ N`
    have hall : ∀ j ∈ Finset.range e, τ j ∈ v.asIdeal ^ N := by
      intro j hj
      rw [Finset.mem_range] at hj
      rcases eq_or_ne (τ j) 0 with h0 | h0
      · rw [h0]; exact (v.asIdeal ^ N).zero_mem
      · rw [mem_pow_iff_le_ordAt v h0]
        by_cases hje : j = j₀
        · rw [hje]
        · exact hj₀min j ((hmemS j).mpr ⟨hj, h0⟩)
    have hsum_mem : (∑ j ∈ Finset.range e, τ j) ∈ v.asIdeal ^ N :=
      Submodule.sum_mem _ fun j hj => hall j hj
    -- and not in `P ^ (N+1)`, since the minimal summand is not
    have hj₀_not : τ j₀ ∉ v.asIdeal ^ (N + 1) := by
      intro h
      have := (mem_pow_iff_le_ordAt v hj₀ne (N + 1)).mp h
      omega
    have hsum_not : (∑ j ∈ Finset.range e, τ j) ∉ v.asIdeal ^ (N + 1) := by
      intro hsum
      refine hj₀_not ?_
      have hrest : (∑ j ∈ (Finset.range e).erase j₀, τ j) ∈ v.asIdeal ^ (N + 1) := by
        refine Submodule.sum_mem _ fun j hj => ?_
        rw [Finset.mem_erase] at hj
        obtain ⟨hjj, hjrange⟩ := hj
        rw [Finset.mem_range] at hjrange
        rcases eq_or_ne (τ j) 0 with h0 | h0
        · rw [h0]; exact (v.asIdeal ^ (N + 1)).zero_mem
        · rw [mem_pow_iff_le_ordAt v h0]
          have hle : N ≤ ordAt v.asIdeal (τ j) := hj₀min j ((hmemS j).mpr ⟨hjrange, h0⟩)
          have hne : ordAt v.asIdeal (τ j) ≠ N := by
            intro hcon
            have h1 := hcong j hjrange h0
            have h2 := hcong j₀ hj₀lt hj₀ne
            have h3 : j % e = j₀ % e := by
              rw [← h1, hcon, hN, h2]
            rw [Nat.mod_eq_of_lt hjrange, Nat.mod_eq_of_lt hj₀lt] at h3
            exact hjj h3
          omega
      have hsum' : (∑ j ∈ (Finset.range e).erase j₀, τ j) + τ j₀ ∈ v.asIdeal ^ (N + 1) := by
        rw [Finset.sum_erase_add (Finset.range e) τ (Finset.mem_range.mpr hj₀lt)]
        exact hsum
      have hdecomp : τ j₀ = ((∑ j ∈ (Finset.range e).erase j₀, τ j) + τ j₀) -
          (∑ j ∈ (Finset.range e).erase j₀, τ j) :=
        (add_sub_cancel_left _ _).symm
      have := Submodule.sub_mem (v.asIdeal ^ (N + 1)) hsum' hrest
      rwa [← hdecomp] at this
    -- conclude
    rcases eq_or_ne (∑ j ∈ Finset.range e, τ j) 0 with hzero | hne
    · rw [hzero, ordAt_zero]; omega
    · have h1 : N ≤ ordAt v.asIdeal (∑ j ∈ Finset.range e, τ j) :=
        (mem_pow_iff_le_ordAt v hne N).mp hsum_mem
      have h2 : ordAt v.asIdeal (∑ j ∈ Finset.range e, τ j) ≤ N := by
        by_contra hcon
        exact hsum_not ((mem_pow_iff_le_ordAt v hne (N + 1)).mpr (by omega))
      have h3 : N ≤ e * k + e - 1 := by
        calc N ≤ ordAt v.asIdeal (τ (e - 1)) := hj₀min (e - 1) hmemLast
          _ = e * k + e - 1 := hlast
      exact le_trans h2 h3

end Sum

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
