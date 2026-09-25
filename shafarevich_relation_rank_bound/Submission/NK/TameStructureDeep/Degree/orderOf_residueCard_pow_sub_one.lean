/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The order of the residue cardinality in `ZMod (q ^ m - 1)`

Let `K` be a number field, `𝔭` a finite prime of `K` and `q = residueCard K 𝔭 = #(𝒪_κ/𝔪_κ)` the
cardinality of the residue field of the `𝔭`-adic completion `κ = K_𝔭`.  This file proves that the
image of `q` in `ZMod (q ^ m - 1)` has multiplicative order exactly `m`:

`NK.TameStructureDeep.Degree.orderOf_residueCard_pow_sub_one`.

The content is elementary: `q` is a unit modulo `q ^ m - 1` (indeed `q ^ m ≡ 1`), and no smaller
positive power of `q` is `1`, because for `0 < d < m` one has `0 < q ^ d - 1 < q ^ m - 1`, so
`q ^ m - 1` cannot divide `q ^ d - 1`.  The only arithmetic input is `q ≥ 2`, which holds because
the residue field is a finite field of prime characteristic `p` and `q = p ^ f` with `f ≥ 1`.

This is the order-theoretic heart of the identification
`Gal(κ^{ur}/κ) ≅ Ẑ`, `Frob ↦ 1`: the Frobenius acts on `μ_n`, `(n, p) = 1`, by `ζ ↦ ζ ^ q`, so the
`n`-th cyclotomic extension of `κ` has degree `ord_n(q)` (see
`NK.TameStructureDeep.Degree.natDegree_minpoly_le_orderOf` and
`...orderOf_dvd_natDegree_minpoly`), and hence the unramified extension of degree `m` is
`κ(μ_{q ^ m - 1})`.
-/
import Mathlib
import Submission.NK.LocalStructure.Defs
import Submission.NK.LocalStructure.Tame.residueCard_eq_pow_of_charP
import Submission.NK.Mine.ResidueCharAutomatic

open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructureDeep.Degree

/-- **The order of `q` in `ZMod (q ^ m - 1)` is `m`, for `q ≥ 2` and `m ≠ 0`.**

This is the elementary arithmetic underlying `orderOf_residueCard_pow_sub_one`; it is stated for an
arbitrary `q` so that it can be applied to `q = residueCard K 𝔭`. -/
theorem orderOf_natCast_zmod_pow_sub_one {q m : ℕ} (hq : 2 ≤ q) (hm : m ≠ 0) :
    orderOf ((q : ℕ) : ZMod (q ^ m - 1)) = m := by
  rw [orderOf_eq_iff (Nat.pos_of_ne_zero hm)]
  constructor
  · -- `q ^ m ≡ 1 (mod q ^ m - 1)`
    have hle : 1 ≤ q ^ m := Nat.one_le_pow m q (by omega)
    have key : ((q ^ m : ℕ) : ZMod (q ^ m - 1)) = 1 := by
      have hcast : ((q ^ m : ℕ) : ZMod (q ^ m - 1))
          = ((q ^ m - 1 : ℕ) : ZMod (q ^ m - 1)) + ((1 : ℕ) : ZMod (q ^ m - 1)) := by
        rw [← Nat.cast_add]
        congr 1
        exact (Nat.sub_add_cancel hle).symm
      rw [ZMod.natCast_self, Nat.cast_one, zero_add] at hcast
      exact hcast
    simpa [Nat.cast_pow] using key
  · -- and no smaller positive power is `1`
    intro d hdlt hdpos hcontra
    have hcast : ((q ^ d : ℕ) : ZMod (q ^ m - 1)) = 1 := by
      rw [Nat.cast_pow]
      exact hcontra
    have hmod : (1 : ℕ) ≡ q ^ d [MOD (q ^ m - 1)] :=
      (ZMod.natCast_eq_natCast_iff (1 : ℕ) (q ^ d) (q ^ m - 1)).mp (by simpa using hcast.symm)
    have hdvd : (q ^ m - 1) ∣ q ^ d - 1 := hmod.dvd'
    have hlt : q ^ d < q ^ m := Nat.pow_lt_pow_right (by omega) hdlt
    have hsub : q ^ d - 1 < q ^ m - 1 :=
      Nat.sub_lt_sub_right (Nat.one_le_pow d q (by omega)) hlt
    have hzero : q ^ d - 1 = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hsub
    have hge : 2 ≤ q ^ d := le_trans hq (Nat.le_self_pow (n := d) (a := q) (by omega))
    omega

/-- **The residue cardinality has order `m` modulo `q ^ m - 1`.**

For a number field `K`, a finite prime `𝔭` and `m ≠ 0`, the image of `q = residueCard K 𝔭` in
`ZMod (q ^ m - 1)` has multiplicative order `m`.  This is the unit-group form of the statement that
the unramified extension of `κ = K_𝔭` of degree `m` is cut out by the `(q ^ m - 1)`-th roots of
unity. -/
theorem orderOf_residueCard_pow_sub_one {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (m : ℕ) (hm : m ≠ 0) :
    orderOf ((NK.LocalStructure.residueCard K 𝔭 :
      ZMod (NK.LocalStructure.residueCard K 𝔭 ^ m - 1))) = m := by
  -- `q` is a positive power of the residue characteristic, hence `q ≥ 2`
  have hp := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hchar := NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
  obtain ⟨f, hfpos, hqeq⟩ :=
    NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hp hchar
  have hq : 2 ≤ NK.LocalStructure.residueCard K 𝔭 := by
    rw [hqeq]
    calc 2 ≤ ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := hp.two_le
      _ = (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ 1 :=
            (pow_one _).symm
      _ ≤ (ringChar (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ f :=
            Nat.pow_le_pow_right hp.pos (by omega)
  exact orderOf_natCast_zmod_pow_sub_one hq hm

end NK.TameStructureDeep.Degree
