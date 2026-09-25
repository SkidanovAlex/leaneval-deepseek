/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Weak approximation for a number field at a finite set of finite primes

Let `K` be a number field and `S` a finite set of finite primes of `K`.  **Weak approximation**
(Neukirch, *Algebraic Number Theory*, Chap. II, 5.7; the "Chinese remainder theorem" quoted in the
proof of §5's Proposition `K^x/K^ell local surjection`, see
`Submission/Work/UchidaKummer/Defs.lean`) says that the diagonal image of `K` in the product
`∏_{𝔮 ∈ S} K_𝔮` of the completions at the primes of `S` is dense:

`NK.UchidaKummer.IsWeakApproximation K S`.

The proof has three ingredients.

* **Simultaneous approximation (the CRT step).**  For a pairwise independent family of valuation
  subrings `A i` of a field and arbitrary targets `a i` and radii `γ i > 0`, there is `x` with
  `(A i).valuation (x - a i) < γ i`
  (`Commons.RingTheory.Valuation.exists_valuation_sub_lt_of_pairwise_independent`).  The hypothesis
  of pairwise independence holds for the valuation rings `valuationSubringAtPrime K 𝔮` at distinct
  primes `𝔮`: as soon as `A ≠ B` are valuation subrings and `A` has Krull dimension `≤ 1`
  (true for the localisation of the ring of integers at a prime), `A ⊔ B = ⊤`
  (`sup_valuationSubringAtPrime_eq_top`, via `ValuationSubring.eq_self_or_eq_top_of_le`).
* **Passing from `A.valuation` to the global prime valuation.**  The valuation of
  `valuationSubringAtPrime K 𝔮` is equivalent to `𝔮.valuation K`
  (`valuationSubringAtPrime_valuation_lt_iff`), so the radii can be prescribed as the `𝔮`-adic
  values `exp n` of the discrete value group `Zstar0 = WithZero (Multiplicative ℤ)`.
* **Topology of the completion.**  Every neighbourhood of a point of `𝔮.adicCompletion K` contains
  an `exp`-ball (`exists_exp_ball_subset`), and the diagonal map is continuous, so the levelwise
  statement upgrades to density in the product.

-/

import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
import Submission.Commons.RingTheory.Valuation.exists_valuation_sub_lt_of_pairwise_independent
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers

namespace NK.UchidaKummer.Approximation

open IsDedekindDomain Filter Set
open scoped Topology WithZero NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The valuation rings at two distinct primes generate the field.**

If `p ≠ q` are finite primes of a number field `K`, the localisations `𝒪_p` and `𝒪_q` of the ring
of integers generate `K` as a ring, i.e. their join as valuation subrings of `K` is everything.
(With `A := 𝒪_p` of Krull dimension `≤ 1`, `ValuationSubring.eq_self_or_eq_top_of_le` says that an
overring of `A` is `A` or everything; applied to `A ⊔ B` and to `B` this forces `A ⊔ B = ⊤` as
soon as `A ≠ B`.) -/
theorem sup_valuationSubringAtPrime_eq_top (p q : HeightOneSpectrum (𝓞 K)) (hpq : p ≠ q) :
    HeightOneSpectrum.valuationSubringAtPrime K p ⊔
      HeightOneSpectrum.valuationSubringAtPrime K q = ⊤ := by
  have hne : HeightOneSpectrum.valuationSubringAtPrime K p ≠
      HeightOneSpectrum.valuationSubringAtPrime K q := fun h =>
    hpq (Commons.RingTheory.Valuation.valuationSubringAtPrime_injective h)
  rcases ValuationSubring.eq_self_or_eq_top_of_le
      (A := HeightOneSpectrum.valuationSubringAtPrime K p)
      (B := HeightOneSpectrum.valuationSubringAtPrime K p ⊔
        HeightOneSpectrum.valuationSubringAtPrime K q) le_sup_left with h | h
  · rcases ValuationSubring.eq_self_or_eq_top_of_le
        (A := HeightOneSpectrum.valuationSubringAtPrime K q)
        (B := HeightOneSpectrum.valuationSubringAtPrime K p) (h.symm ▸ le_sup_right) with h2 | h2
    · exact absurd h2.symm hne
    · exact absurd h2 (Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top p)
  · exact h

/-- **The valuation of `valuationSubringAtPrime` is equivalent to the global prime valuation.**

For `d ≠ 0` and every `y : K`, the comparison of the two `y`-values in the value group of
`valuationSubringAtPrime K p` is the comparison of the two `p`-adic values of `y` and `d`. -/
theorem valuationSubringAtPrime_valuation_lt_iff (p : HeightOneSpectrum (𝓞 K)) {y d : K}
    (hd : d ≠ 0) :
    (HeightOneSpectrum.valuationSubringAtPrime K p).valuation y <
      (HeightOneSpectrum.valuationSubringAtPrime K p).valuation d ↔
      p.valuation K y < p.valuation K d := by
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  have hposA : (0 : ((p.valuation K).valuationSubring).ValueGroup) <
      (p.valuation K).valuationSubring.valuation d := (Valuation.pos_iff _).mpr hd
  have hposv : (0 : Zstar0) < p.valuation K d := (Valuation.pos_iff _).mpr hd
  have hiff : ∀ z : K, (p.valuation K).valuationSubring.valuation z < 1 ↔ p.valuation K z < 1 :=
    fun z => (Valuation.isEquiv_iff_val_lt_one.mp
      (Valuation.isEquiv_valuation_valuationSubring (p.valuation K)) (x := z)).symm
  have h1 : (p.valuation K).valuationSubring.valuation y <
      (p.valuation K).valuationSubring.valuation d ↔
      (p.valuation K).valuationSubring.valuation y /
        (p.valuation K).valuationSubring.valuation d < 1 := by
    rw [div_lt_iff₀ hposA, one_mul]
  have h2 : (p.valuation K).valuationSubring.valuation y /
        (p.valuation K).valuationSubring.valuation d < 1 ↔
      (p.valuation K).valuationSubring.valuation (y / d) < 1 := by
    rw [Valuation.map_div]
  have h4 : p.valuation K (y / d) < 1 ↔ p.valuation K y / p.valuation K d < 1 := by
    rw [Valuation.map_div]
  have h5 : p.valuation K y / p.valuation K d < 1 ↔ p.valuation K y < p.valuation K d := by
    rw [div_lt_iff₀ hposv, one_mul]
  exact h1.trans (h2.trans ((hiff (y / d)).trans (h4.trans h5)))

/-- **Every neighbourhood in a completion contains an `exp`-ball.**

The sets `{y | v (y - x) < exp n}` for `n : ℤ` (where `v` is the `𝔮`-adic valuation of the
completion) are a basis of neighbourhoods of `x`.  This combines the basis of neighbourhoods
`{y | v.restrict (y - x) < γ}` of the valuation topology with `WithZero.exp_log`. -/
theorem exists_exp_ball_subset (p : HeightOneSpectrum (𝓞 K))
    (x : p.adicCompletion K) {T : Set (p.adicCompletion K)} (hT : T ∈ 𝓝 x) :
    ∃ n : ℤ, {y | Valued.v (y - x) < WithZero.exp n} ⊆ T := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hT
  set g : Zstar0 := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg_def
  have hg0 : g ≠ 0 := by
    intro h
    have h1 : γ.1 = 0 := MonoidWithZeroHom.ValueGroup₀.embedding_injective
      (by rw [hg_def] at h; exact h.trans (map_zero _).symm)
    exact Units.ne_zero γ h1
  refine ⟨WithZero.log g, ?_⟩
  intro y hy
  apply hγ
  change Valued.v.restrict (y - x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding]
  rw [← hg_def, ← WithZero.exp_log hg0]
  exact hy

/-- **Simultaneous approximation at finitely many primes, at prescribed `exp`-levels.**

Given targets `a 𝔮 : K` and levels `n 𝔮 : ℤ` at the primes of a finite set `S` of finite primes
whose valuation rings are pairwise independent, there is a single `x : K` with
`𝔮.valuation K (x - a 𝔮) < exp (n 𝔮)` for every `𝔮 ∈ S`.

The radii `exp (n 𝔮)` are realised as the `𝔮`-adic values of auxiliary elements `d 𝔮`
(`HeightOneSpectrum.valuation_surjective`), and the theorem
`Commons.RingTheory.Valuation.exists_valuation_sub_lt_of_pairwise_independent` produces `x`. -/
theorem exists_valuation_sub_lt_exp (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hind : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      HeightOneSpectrum.valuationSubringAtPrime K p ⊔
        HeightOneSpectrum.valuationSubringAtPrime K q = ⊤)
    (a : S → K) (n : S → ℤ) :
    ∃ x : K, ∀ 𝔮 : S, 𝔮.1.valuation K (x - a 𝔮) < WithZero.exp (n 𝔮) := by
  choose d hd using fun 𝔮 : S =>
    HeightOneSpectrum.valuation_surjective K 𝔮.1 (WithZero.exp (n 𝔮))
  have hdne : ∀ 𝔮 : S, d 𝔮 ≠ 0 := fun 𝔮 h => by
    have h' := hd 𝔮
    rw [h, Valuation.map_zero] at h'
    exact WithZero.exp_ne_zero h'.symm
  obtain ⟨x, hx⟩ := Commons.RingTheory.Valuation.exists_valuation_sub_lt_of_pairwise_independent
    (A := fun 𝔮 : S => HeightOneSpectrum.valuationSubringAtPrime K 𝔮.1)
    (fun 𝔮 => Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top 𝔮.1)
    (fun 𝔮 𝔮' h => hind 𝔮.1 𝔮.2 𝔮'.1 𝔮'.2 (fun he => h (Subtype.ext he)))
    a (fun 𝔮 => (HeightOneSpectrum.valuationSubringAtPrime K 𝔮.1).valuation (d 𝔮))
    (fun 𝔮 => (Valuation.pos_iff _).mpr (hdne 𝔮))
  refine ⟨x, fun 𝔮 => ?_⟩
  have h := hx 𝔮
  rwa [valuationSubringAtPrime_valuation_lt_iff 𝔮.1 (hdne 𝔮), hd 𝔮] at h

/-- **Weak approximation** for a number field `K` at a finite set `S` of finite primes: the
diagonal image of `K` in `∏_{𝔮 ∈ S} K_𝔮` is dense.

This is Neukirch, *Algebraic Number Theory*, Chap. II, 5.7 — the approximation theorem behind
`IsKummerSurjective`.  Given a point `x` of the product and a neighbourhood `U` of `x`, the product
topology supplies a finite product of neighbourhoods `t 𝔮 ⊆ U`; each `t 𝔮` contains an `exp`-ball
around `x 𝔮` (`exists_exp_ball_subset`), each of which contains the image of an element `b 𝔮 : K`
(`exists_algebraMap_mem_exp_ball`, i.e. density of `K` in a single completion).  The CRT step
`exists_valuation_sub_lt_exp` then replaces `b` by a single `c : K`, and the ultrametric inequality
finishes. -/
theorem isWeakApproximation (K : Type*) [Field K] [NumberField K]
    (S : Finset (NK.Chebotarev.PrimeIdeal K)) :
    NK.UchidaKummer.IsWeakApproximation K S := by
  rw [NK.UchidaKummer.IsWeakApproximation]
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [nhds_pi] at hU
  obtain ⟨I, t, ht, hIt⟩ := Filter.mem_pi'.mp hU
  choose n hn using fun 𝔮 : S => exists_exp_ball_subset 𝔮.1 (x 𝔮) (ht 𝔮)
  choose b hb using fun 𝔮 : S =>
    Commons.NumberTheory.NumberField.Completion.exists_algebraMap_mem_exp_ball 𝔮.1 (x 𝔮) (n 𝔮)
  have hind : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      HeightOneSpectrum.valuationSubringAtPrime K p ⊔
        HeightOneSpectrum.valuationSubringAtPrime K q = ⊤ :=
    fun p _ q _ hpq => sup_valuationSubringAtPrime_eq_top p q hpq
  obtain ⟨c, hc⟩ := exists_valuation_sub_lt_exp S hind b n
  refine ⟨fun 𝔮 : S => algebraMap K (𝔮.1.adicCompletion K) c, ?_, ⟨c, rfl⟩⟩
  · refine hIt ?_
    rw [Set.mem_pi]
    intro 𝔮 _
    refine hn 𝔮 ?_
    change Valued.v (algebraMap K (𝔮.1.adicCompletion K) c - x 𝔮) < WithZero.exp (n 𝔮)
    have hsub : algebraMap K (𝔮.1.adicCompletion K) c - x 𝔮 =
        (algebraMap K (𝔮.1.adicCompletion K) c -
            algebraMap K (𝔮.1.adicCompletion K) (b 𝔮)) +
          (algebraMap K (𝔮.1.adicCompletion K) (b 𝔮) - x 𝔮) := by ring
    rw [hsub]
    refine lt_of_le_of_lt
      (Commons.NumberTheory.NumberField.Completion.val_add_le_max 𝔮.1 _ _) (max_lt ?_ ?_)
    · rw [← map_sub, Commons.NumberTheory.NumberField.Completion.valued_alg_eq 𝔮.1 (c - b 𝔮)]
      exact hc 𝔮
    · exact hb 𝔮

end NK.UchidaKummer.Approximation
