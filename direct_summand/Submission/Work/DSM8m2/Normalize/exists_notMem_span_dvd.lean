import Mathlib

/-!
# Normalising a denominator at `p`

For a Noetherian local ring `A` of characteristic `0` whose residue field has characteristic
`p`, every non-zero element `c` can be written `c = p ^ K · u` with `u ∉ (p)`: indeed by
Krull's intersection theorem (`Ideal.iInf_pow_eq_bot_of_isLocalRing`) the `p`-adic powers of
`(p)` intersect to `0`, so there is a largest exponent carrying `c`.  Consequently

`c ∣ (p · u) ^ (K + 1) = p ^ (K + 1) · u ^ (K + 1) = c · (p · u ^ K)`,

with `u ∉ (p)`: an element outside `(p)` by which `c` divides a power of `p · u`.
-/

namespace Work.DSM8m2.Normalize

open IsLocalRing

/-- **Denominator normalisation at `p`.** In a Noetherian local ring `A` of characteristic `0`
with residue field of characteristic `p`, for every non-zero `c` there is `g ∉ (p)` and `m`
with `c ∣ (p · g) ^ m`.

Proof: `p` lies in the maximal ideal (its residue is `0`), hence generates a proper ideal, so
Krull's intersection theorem gives `⋂_k (p)^k = 0`.  Since `c ≠ 0` there is a *minimal* `k` with
`c ∉ (p)^k`; putting `K = k - 1` we have `c ∈ (p)^K`, say `c = p ^ K · u`.  Then `u ∉ (p)`
(otherwise `c ∈ (p)^(K+1) = (p)^k`), and with `g = u`, `m = K + 1` we get
`(p · u) ^ (K + 1) = c · (p · u ^ K)`. -/
theorem exists_notMem_span_dvd {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (p : ℕ) [Fact p.Prime] [CharZero A] [CharP (IsLocalRing.ResidueField A) p] {c : A} (hc : c ≠ 0) :
    ∃ g : A, g ∉ Ideal.span {(p : A)} ∧ ∃ m : ℕ, c ∣ ((p : A) * g) ^ m := by
  classical
  -- `p` is a non-unit, because it dies in the residue field.
  have hp_mem : (p : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    rw [map_natCast, CharP.cast_eq_zero]
  have hp_notUnit : ¬ IsUnit (p : A) :=
    fun h => (IsLocalRing.notMem_maximalIdeal).mpr h hp_mem
  have hne : Ideal.span {(p : A)} ≠ ⊤ :=
    fun h => hp_notUnit ((Ideal.span_singleton_eq_top).mp h)
  -- Krull's intersection theorem: `⋂_k (p)^k = 0`.
  have hKrull := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {(p : A)}) hne
  have hcI : c ∉ (⨅ i : ℕ, Ideal.span {(p : A)} ^ i) := by
    rw [hKrull]
    exact fun h => hc (Ideal.mem_bot.mp h)
  have hex : ∃ k, c ∉ Ideal.span {(p : A)} ^ k := by
    by_contra h
    rw [not_exists] at h
    simp only [not_not] at h
    exact hcI ((Ideal.mem_iInf).mpr h)
  -- the minimal such exponent is positive, since `c ∈ (p)^0`.
  have hkne : Nat.find hex ≠ 0 := by
    intro h
    have hk0 := Nat.find_spec hex
    rw [h, pow_zero, Ideal.one_eq_top] at hk0
    exact hk0 Submodule.mem_top
  let K := (Nat.find hex).pred
  have hkK : K + 1 = Nat.find hex := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hkne)
  -- `c ∈ (p)^K = (p^K)`, so `c = p ^ K * u`.
  have hcK : c ∈ Ideal.span {(p : A)} ^ K := by
    have hlt : K < Nat.find hex := Nat.pred_lt hkne
    have h := Nat.find_min hex hlt
    simpa only [not_not] using h
  rw [Ideal.span_singleton_pow] at hcK
  rw [Ideal.mem_span_singleton, dvd_def] at hcK
  obtain ⟨u, hu⟩ := hcK
  refine ⟨u, ?_, K + 1, ?_⟩
  · -- `u ∉ (p)`: otherwise `c ∈ (p)^(K+1) = (p)^k`, contradicting minimality of `k`.
    intro humem
    rw [Ideal.mem_span_singleton, dvd_def] at humem
    obtain ⟨v, hv⟩ := humem
    have hc_succ : c ∈ Ideal.span {(p : A)} ^ (Nat.find hex) := by
      rw [← hkK, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact ⟨v, by rw [hu, hv]; ring⟩
    exact Nat.find_spec hex hc_succ
  · -- `(p · u) ^ (K + 1) = c · (p · u ^ K)`.
    exact ⟨(p : A) * u ^ K, by rw [hu]; ring⟩

end Work.DSM8m2.Normalize
