/-
# The fixed field of the `2ⁿ`-power Frobenius in `GF(2^(2n))`

The `n`-th iterate `σ = x ↦ x ^ 2ⁿ` of the `2`-power Frobenius on `E = GF(2^(2n))` is the
distinguished involution of the unitary model: it is the Frobenius of `E` over its subfield
`F = GF(2ⁿ)`, and `F` is exactly the fixed field of `σ`.  This file computes its cardinality:
`|E^σ| = 2ⁿ`.

The two inequalities are obtained as follows.

* `2ⁿ ≤ |E^σ|`: since `[GF(2ⁿ) : GF(2)] = n` divides `[GF(2^(2n)) : GF(2)] = 2n`, there is an
  `F₂`-algebra embedding `ι : GF(2ⁿ) → GF(2^(2n))` (`FiniteField.nonempty_algHom_of_finrank_dvd`).
  For `y ∈ GF(2ⁿ)` one has `y ^ 2ⁿ = y` (`FiniteField.pow_card`), so `ι y ^ 2ⁿ = ι y`: the image of
  `ι` lies in the fixed field.  As `ι` is injective, `|E^σ| ≥ |GF(2ⁿ)| = 2ⁿ`.

* `|E^σ| ≤ 2ⁿ`: the fixed field is the root set in `E` of the polynomial `X ^ 2ⁿ - X`, which has
  degree `2ⁿ`; a nonzero polynomial has at most as many roots as its degree
  (`Polynomial.ncard_rootSet_le`).
-/
import Mathlib
import Submission.Work.PSU3.GaloisField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.PSU3.GaloisField

open Polynomial

/-- The fixed field of the `n`-th iterate of the `2`-power Frobenius on `GF(2^(2n))`
(namely `x ↦ x ^ 2ⁿ`) has exactly `2 ^ n` elements. -/
theorem fixedField_card (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {x : GaloisField 2 (2 * n) //
      iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x} = 2 ^ n := by
  classical
  have hn0 : n ≠ 0 := by omega
  have h2n0 : 2 * n ≠ 0 := by omega
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  letI : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  -- The polynomial whose roots in `E` are the fixed points of `σ`.
  have hp0 : (X ^ 2 ^ n - X : (GaloisField 2 (2 * n))[X]) ≠ 0 := by
    intro h
    have h1 : (X : (GaloisField 2 (2 * n))[X]) ^ 2 ^ n = X := sub_eq_zero.mp h
    have h2 := congrArg Polynomial.natDegree h1
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at h2
    have := Nat.one_lt_pow hn0 (by norm_num : 1 < 2)
    omega
  -- Lower bound: an `F₂`-embedding `GF(2ⁿ) → GF(2^(2n))` lands inside the fixed field.
  have hlower : 2 ^ n ≤ Nat.card {x : GaloisField 2 (2 * n) //
      iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x} := by
    have hdvd : Module.finrank (ZMod 2) (GaloisField 2 n) ∣
        Module.finrank (ZMod 2) (GaloisField 2 (2 * n)) := by
      rw [GaloisField.finrank 2 hn0, GaloisField.finrank 2 h2n0]
      exact ⟨2, by ring⟩
    obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdvd
    have hcardn : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
    have hφinj : Function.Injective φ := φ.toRingHom.injective
    have hfix : ∀ y : GaloisField 2 n,
        iterateFrobenius (GaloisField 2 (2 * n)) 2 n (φ y) = φ y := by
      intro y
      have hc : Fintype.card (GaloisField 2 n) = 2 ^ n := by
        rw [← Nat.card_eq_fintype_card]; exact hcardn
      rw [iterateFrobenius_def, ← map_pow, show y ^ 2 ^ n = y from by
        rw [← hc]; exact FiniteField.pow_card y]
    rw [← hcardn]
    refine Nat.card_le_card_of_injective
      (fun y => (⟨φ y, hfix y⟩ : {x : GaloisField 2 (2 * n) //
        iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x})) ?_
    intro a b hab
    exact hφinj (Subtype.ext_iff.mp hab)
  -- Upper bound: the fixed field is the root set of `X ^ 2ⁿ - X`, a polynomial of degree `2ⁿ`.
  have hupper : Nat.card {x : GaloisField 2 (2 * n) //
      iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x} ≤ 2 ^ n := by
    have hroot : (X ^ 2 ^ n - X : (GaloisField 2 (2 * n))[X]).rootSet
          (GaloisField 2 (2 * n))
        = {x | iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x} := by
      ext x
      rw [mem_rootSet']
      constructor
      · rintro ⟨-, h⟩
        simpa [iterateFrobenius_def, sub_eq_zero] using h
      · intro h
        exact ⟨by simpa using hp0, by simpa [iterateFrobenius_def, sub_eq_zero] using h⟩
    have hroot' : Set.ncard {x : GaloisField 2 (2 * n) |
          iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x}
        = Set.ncard ((X ^ 2 ^ n - X : (GaloisField 2 (2 * n))[X]).rootSet
            (GaloisField 2 (2 * n))) := by
      rw [hroot]
    calc Nat.card {x : GaloisField 2 (2 * n) //
            iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x}
        = Set.ncard {x : GaloisField 2 (2 * n) |
            iterateFrobenius (GaloisField 2 (2 * n)) 2 n x = x} := Nat.card_coe_set_eq _
      _ = Set.ncard ((X ^ 2 ^ n - X : (GaloisField 2 (2 * n))[X]).rootSet
            (GaloisField 2 (2 * n))) := hroot'
      _ ≤ (X ^ 2 ^ n - X : (GaloisField 2 (2 * n))[X]).natDegree :=
          Polynomial.ncard_rootSet_le _ _
      _ ≤ 2 ^ n := by
          refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
          · exact Polynomial.natDegree_X_pow_le _
          · exact Polynomial.natDegree_X_le.trans Nat.one_le_two_pow
  exact le_antisymm hupper hlower

end Work.PSU3.GaloisField
