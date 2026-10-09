import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The trivial Frobenius at `𝔮` forces residue degree one

For a finite extension `K/k` of number fields and a nonzero prime `𝔮` of `𝓞 K`, if `1 ∈ Gal(K/k)`
is an *arithmetic* Frobenius at `𝔮` (i.e. `x ≡ x ^ #(𝓞 k ⧸ 𝔮 ∩ 𝓞 k) (mod 𝔮)` for all
`x ∈ 𝓞 K`), then the residue fields of `𝔮` and of `𝔮 ∩ 𝓞 k` are equinumerous:

`#(𝓞 K ⧸ 𝔮) = #(𝓞 k ⧸ 𝔮.under (𝓞 k))`.

The mathematical content is the counting argument for finite fields: writing `M` for the cardinality
of the residue field `E = 𝓞 k ⧸ 𝔮.under (𝓞 k)` of the base and `N` for that of the residue field
`F = 𝓞 K ⧸ 𝔮`, the fundamental identity `Ideal.cardQuot_pow_inertiaDeg` gives `M ^ f = N` with
`f = 𝔮.inertiaDeg (𝓞 k) ≥ 1`, while the Frobenius hypothesis says that every `y ∈ F` satisfies
`y ^ M = y`, i.e. `F` consists of roots of the polynomial `X ^ M - X`.  A nonzero polynomial of
degree `≤ M` has at most `M` roots, so `N ≤ M`; together with `M ≤ M ^ f = N` this gives `N = M`.

No Galois-theoretic input beyond the hypothesis is used: the argument is purely about the residue
field and the `M`-power map.

## Contents

* `card_residue_eq_of_isFrobAt_one` — the statement above;
* `inertiaDeg_eq_one_of_isFrobAt_one` — the companion form `𝔮.inertiaDeg (𝓞 k) = 1`.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.EscapeCoreLib

open NumberField
open scoped Polynomial

/-- **A trivial Frobenius has residue degree one.**  If the identity is an arithmetic Frobenius at
`𝔮`, then the residue field of `K` at `𝔮` has the same cardinality as the residue field of `k` at
`𝔮 ∩ 𝓞 k`. -/
theorem card_residue_eq_of_isFrobAt_one {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] (𝔮 : NK.Chebotarev.PrimeIdeal K)
    (h : NK.Chebotarev.IsFrobAt (K := k) (L := K) 𝔮 (1 : Gal(K/k))) :
    Nat.card (NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) =
      Nat.card (NumberField.RingOfIntegers k ⧸ 𝔮.asIdeal.under (NumberField.RingOfIntegers k)) := by
  -- `𝓞 K` is a finite `𝓞 k`-module, and `𝔮` (a nonzero prime of a Dedekind domain) is maximal.
  haveI : Module.Finite (𝓞 k) (𝓞 K) := inferInstance
  haveI : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
  haveI : 𝔮.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot 𝔮.asIdeal 𝔮.ne_bot
  haveI : (𝔮.asIdeal.under (𝓞 k)).IsMaximal := inferInstance
  change Submodule.cardQuot 𝔮.asIdeal = Submodule.cardQuot (𝔮.asIdeal.under (𝓞 k))
  set M := Submodule.cardQuot (𝔮.asIdeal.under (𝓞 k))
  set N := Submodule.cardQuot 𝔮.asIdeal
  set f := 𝔮.asIdeal.inertiaDeg (𝓞 k)
  -- The fundamental identity: `M ^ f = N`, with `f` the inertia degree of `𝔮` over `𝓞 k`.
  have hcard' : M ^ f = N := Ideal.cardQuot_pow_inertiaDeg (𝔮.asIdeal.under (𝓞 k)) 𝔮.asIdeal
  have hf1 : 1 ≤ f := Nat.one_le_iff_ne_zero.mpr (Ideal.inertiaDeg_pos 𝔮.asIdeal (𝓞 k)).ne'
  -- The Frobenius hypothesis, read in the residue field `𝓞 K ⧸ 𝔮`: the `M`-power map is the
  -- identity.
  have hroot : ∀ y : 𝓞 K ⧸ 𝔮.asIdeal, y ^ M = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx := (NK.Chebotarev.isFrobAt_def (K := k) (L := K) 𝔮 (1 : Gal(K/k))).mp h x
    have h0 : Ideal.Quotient.mk 𝔮.asIdeal
        (galRestrict (𝓞 k) k K (𝓞 K) (1 : Gal(K/k)) x -
          x ^ Submodule.cardQuot (𝔮.asIdeal.under (𝓞 k))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hx
    rw [map_sub, map_pow] at h0
    have h1 : galRestrict (𝓞 k) k K (𝓞 K) (1 : Gal(K/k)) x = x := by simp
    rw [h1] at h0
    exact (sub_eq_zero.mp h0).symm
  by_cases hM : M ≤ 1
  · -- Degenerate cases: `M = 0` or `M = 1`, where `M ^ f = M` for any `f ≥ 1`.
    rcases (by omega : M = 0 ∨ M = 1) with h0 | h0
    · rw [h0] at hcard' ⊢
      rw [← hcard']
      exact zero_pow (by omega)
    · rw [h0] at hcard' ⊢
      rw [← hcard']
      exact one_pow f
  · -- Main case: `2 ≤ M`.  Every element of the residue field is a root of `X ^ M - X`.
    have hM2 : 2 ≤ M := by omega
    have hNM : N ≤ M := by
      letI : Field (𝓞 K ⧸ 𝔮.asIdeal) := Ideal.Quotient.field 𝔮.asIdeal
      have hne : (Polynomial.X ^ M - Polynomial.X : (𝓞 K ⧸ 𝔮.asIdeal)[X]) ≠ 0 := by
        intro hzero
        have h1 : (Polynomial.X ^ M : (𝓞 K ⧸ 𝔮.asIdeal)[X]) = Polynomial.X :=
          sub_eq_zero.mp hzero
        have h2 := congrArg Polynomial.natDegree h1
        rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at h2
        omega
      have hrootset : (Polynomial.X ^ M - Polynomial.X : (𝓞 K ⧸ 𝔮.asIdeal)[X]).rootSet
          (𝓞 K ⧸ 𝔮.asIdeal) = Set.univ := by
        rw [Set.eq_univ_iff_forall]
        intro y
        rw [Polynomial.mem_rootSet]
        refine ⟨hne, ?_⟩
        simp only [map_sub, map_pow, Polynomial.aeval_X]
        rw [hroot y, sub_self]
      calc N = Nat.card (𝓞 K ⧸ 𝔮.asIdeal) := rfl
        _ = (Set.univ : Set (𝓞 K ⧸ 𝔮.asIdeal)).ncard := (Set.ncard_univ _).symm
        _ = ((Polynomial.X ^ M - Polynomial.X : (𝓞 K ⧸ 𝔮.asIdeal)[X]).rootSet
              (𝓞 K ⧸ 𝔮.asIdeal)).ncard := by rw [hrootset]
        _ ≤ (Polynomial.X ^ M - Polynomial.X : (𝓞 K ⧸ 𝔮.asIdeal)[X]).natDegree :=
              Polynomial.ncard_rootSet_le _ _
        _ ≤ M := by
          have h3 := Polynomial.natDegree_sub_le
            (Polynomial.X ^ M : (𝓞 K ⧸ 𝔮.asIdeal)[X]) Polynomial.X
          rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at h3
          omega
    have hMN : M ≤ N := by
      rw [← hcard']
      simpa using Nat.pow_le_pow_right (by omega : 0 < M) hf1
    exact le_antisymm hNM hMN

/-- **Companion form: the inertia degree is one.**  The hypothesis of
`card_residue_eq_of_isFrobAt_one` in fact says that the residue degree of `𝔮` over `k` is `1` (the
residue fields are equal, not merely equinumerous).  This is the form in which the condition is
usually consumed, e.g. by `NK.Reconstruct.natCard_quot_eq_of_inertiaDeg_eq_one`. -/
theorem inertiaDeg_eq_one_of_isFrobAt_one {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] (𝔮 : NK.Chebotarev.PrimeIdeal K)
    (h : NK.Chebotarev.IsFrobAt (K := k) (L := K) 𝔮 (1 : Gal(K/k))) :
    𝔮.asIdeal.inertiaDeg (𝓞 k) = 1 := by
  haveI : Module.Finite (𝓞 k) (𝓞 K) := inferInstance
  haveI : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
  haveI : 𝔮.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot 𝔮.asIdeal 𝔮.ne_bot
  haveI : (𝔮.asIdeal.under (𝓞 k)).IsMaximal := inferInstance
  have hcard := Ideal.cardQuot_pow_inertiaDeg (𝔮.asIdeal.under (𝓞 k)) 𝔮.asIdeal
  -- The residue field of `k` at `𝔮 ∩ 𝓞 k` is a finite field, hence has at least two elements.
  have hM2 : 2 ≤ Submodule.cardQuot (𝔮.asIdeal.under (𝓞 k)) := by
    haveI : Field (𝓞 k ⧸ 𝔮.asIdeal.under (𝓞 k)) := Ideal.Quotient.field _
    change 2 ≤ Nat.card (𝓞 k ⧸ 𝔮.asIdeal.under (𝓞 k))
    have hlt := Finite.one_lt_card (α := 𝓞 k ⧸ 𝔮.asIdeal.under (𝓞 k))
    omega
  -- `card_residue_eq_of_isFrobAt_one` identifies the two sides of the fundamental identity.
  have hpow : Submodule.cardQuot (𝔮.asIdeal.under (𝓞 k)) ^ 𝔮.asIdeal.inertiaDeg (𝓞 k) =
      Submodule.cardQuot (𝔮.asIdeal.under (𝓞 k)) ^ 1 := by
    rw [pow_one]
    exact hcard.trans (card_residue_eq_of_isFrobAt_one 𝔮 h)
  exact Nat.pow_right_injective hM2 hpow

end Work.SSGRoute.EscapeCoreLib
