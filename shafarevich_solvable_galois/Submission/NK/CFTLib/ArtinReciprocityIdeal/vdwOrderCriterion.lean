import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Two steps of the van der Waerden prime-existence argument

This module proves the two elementary ingredients of the `Q`-construction of
`NK.CFTLib.ArtinReciprocityIdeal.vdwPrimeExists`
(see `NOTES_vdwPrimeExists.md`, whose critical path has stalled):

* `geomSum_mul` — the geometric-sum identity `Q * (x^{ℓ^e} - 1) = x^{ℓ^{e+1}} - 1` for
  `Q = ∑_{i<ℓ} x^{i ℓ^e}`;
* `orderOf_eq_prime_pow_of_dvd_geomSum` — if a prime `p ≠ ℓ` divides `Q` (with `ℓ` prime, `e ≥ 1`,
  `b ≥ 2`), then `orderOf (b : ZMod p) = ℓ^(e+1)`; in particular `ℓ^e ∣ orderOf (b : ZMod p)`.

These are used as follows in the `vdwPrimeExists` argument: with `b := a^M` and
`M := ∏_{q ∈ F} (q-1)` (so that `b ≡ 1 mod q` for every small prime `q`), every prime `p ∣ Q`
outside the small set has `ℓ^e ∣ orderOf (b : ZMod p) ∣ orderOf (a : ZMod p)`.
-/

namespace NK.CFTLib.ArtinReciprocityIdeal

/-- `Q = ∑_{i<ℓ} x^{i ℓ^e}` satisfies `Q * (x^{ℓ^e} - 1) = x^{ℓ^{e+1}} - 1`. -/
theorem geomSum_mul (R : Type*) [Ring R] (x : R) (ℓ e : ℕ) :
    (∑ i ∈ Finset.range ℓ, x ^ (i * ℓ ^ e)) * (x ^ (ℓ ^ e) - 1) = x ^ (ℓ ^ (e + 1)) - 1 := by
  have h1 : (∑ i ∈ Finset.range ℓ, x ^ (i * ℓ ^ e))
      = ∑ i ∈ Finset.range ℓ, (x ^ (ℓ ^ e)) ^ i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_mul']
  rw [h1, geom_sum_mul, ← pow_mul, ← pow_succ]

/-- **The order criterion.** If a prime `p ≠ ℓ` divides `∑_{i<ℓ} b^{i ℓ^e}` (`ℓ` prime, `e ≥ 1`,
`b ≥ 2`), then `b` has order `ℓ^(e+1)` modulo `p`. -/
theorem orderOf_eq_prime_pow_of_dvd_geomSum {b ℓ e p : ℕ} (hb : 1 < b) (hℓ : ℓ.Prime)
    (he : 0 < e) (hp : p.Prime)
    (hpdvd : p ∣ ∑ i ∈ Finset.range ℓ, b ^ (i * ℓ ^ e)) (hpne : p ≠ ℓ) :
    orderOf ((b : ZMod p)) = ℓ ^ (e + 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- the sum vanishes in `ZMod p`
  have hzero : (∑ i ∈ Finset.range ℓ, ((b : ZMod p)) ^ (i * ℓ ^ e)) = 0 := by
    have hcast : ((∑ i ∈ Finset.range ℓ, b ^ (i * ℓ ^ e) : ℕ) : ZMod p)
        = ∑ i ∈ Finset.range ℓ, ((b : ZMod p)) ^ (i * ℓ ^ e) := by push_cast; rfl
    rw [← hcast, ZMod.natCast_eq_zero_iff]
    exact hpdvd
  -- hence `b^(ℓ^(e+1)) = 1`
  have hmul := geomSum_mul (ZMod p) ((b : ZMod p)) ℓ e
  rw [hzero, zero_mul] at hmul
  have hpow : ((b : ZMod p)) ^ (ℓ ^ (e + 1)) = 1 := by
    rw [← sub_eq_zero]
    exact hmul.symm
  -- and `b^(ℓ^e) ≠ 1`
  have hnot : ((b : ZMod p)) ^ (ℓ ^ e) ≠ 1 := by
    intro h
    have hsum : (∑ i ∈ Finset.range ℓ, ((b : ZMod p)) ^ (i * ℓ ^ e)) = (ℓ : ZMod p) := by
      have h2 : (∑ i ∈ Finset.range ℓ, ((b : ZMod p)) ^ (i * ℓ ^ e))
          = ∑ i ∈ Finset.range ℓ, (((b : ZMod p)) ^ (ℓ ^ e)) ^ i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_mul']
      rw [h2, h]
      simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hzero] at hsum
    have hdvd : p ∣ ℓ := (ZMod.natCast_eq_zero_iff ℓ p).mp hsum.symm
    exact hpne ((hℓ.dvd_iff_eq hp.ne_one).mp hdvd).symm
  have hdvd : orderOf ((b : ZMod p)) ∣ ℓ ^ (e + 1) := orderOf_dvd_of_pow_eq_one hpow
  have hndvd : ¬ orderOf ((b : ZMod p)) ∣ ℓ ^ e := fun h =>
    hnot ((orderOf_dvd_iff_pow_eq_one).mp h)
  rcases (Nat.dvd_prime_pow hℓ).mp hdvd with ⟨k, hk, hkord⟩
  have hk1 : k = e + 1 := by
    by_contra hkne
    exact hndvd (hkord ▸ pow_dvd_pow ℓ (by omega))
  rw [hk1] at hkord
  exact hkord

end NK.CFTLib.ArtinReciprocityIdeal
