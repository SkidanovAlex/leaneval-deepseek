import Mathlib
import Submission.Work.FIArea7.KStarDefs
import Submission.Work.FIArea7.KStarDivs.PrimDefs
import Submission.Work.FIArea7.KStarDivs.SumLemmas
import Submission.Work.FIArea7.KStarDivs.eq_prod_filter_dvd

set_option autoImplicit false

namespace Work.FIArea7.KStarDivs

open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

open Finset
open scoped BigOperators

/--
**Gaussian Möbius summation over the primary divisors of a primary `w`.**

`∑_{e ∈ gaussPrimDivs w} μ(e) [e ∣ z] = [z, w are coprime]`.  The sum runs over the primary
representatives of the divisor classes of `w`; since `w` is primary, every divisor of `w` is
coprime to `1+i` and hence has a unique primary representative, so this is Möbius inversion over
the divisors of `w`: only the squarefree ones contribute, and they correspond bijectively to
subsets of the primary prime divisors `primPrimes w` of `w`.  This turns the sum into the Euler
product `∏_{p ∈ primPrimes w} (1 - [p ∣ z])`, which is `1` iff no primary prime dividing `w`
divides `z` — i.e. iff `z` and `w` are coprime.
-/
theorem gauss_divs_moebius (w z : GaussianInt) (hw : Work.FIPlan.IsPrimary w) :
    (∑ e ∈ gaussPrimDivs w,
        (UniqueFactorizationMonoid.moebius e : ℂ) * (if e ∣ z then (1 : ℂ) else 0))
      = if IsCoprime z w then 1 else 0 := by
  -- Step 1: only the squarefree divisors contribute.
  have step1 :
      (∑ e ∈ gaussPrimDivs w,
          (UniqueFactorizationMonoid.moebius e : ℂ) * (if e ∣ z then (1 : ℂ) else 0))
        = ∑ e ∈ (gaussPrimDivs w).filter Squarefree,
            (UniqueFactorizationMonoid.moebius e : ℂ) * (if e ∣ z then (1 : ℂ) else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases h : Squarefree e
    · simp [h]
    · simp [h]
  -- Step 2: reindex the squarefree primary divisors by subsets of `primPrimes w`
  -- via `S ↦ ∏_{p ∈ S} p`.
  have step2 :
      (∑ e ∈ (gaussPrimDivs w).filter Squarefree,
          (UniqueFactorizationMonoid.moebius e : ℂ) * (if e ∣ z then (1 : ℂ) else 0))
        = ∑ S ∈ (primPrimes w).powerset,
            (UniqueFactorizationMonoid.moebius (∏ p ∈ S, p) : ℂ)
              * (if (∏ p ∈ S, p) ∣ z then (1 : ℂ) else 0) := by
    refine Finset.sum_bij (fun a _ => primPrimeDivs w a) ?_ ?_ ?_ ?_
    · intro a _
      exact Finset.mem_powerset.mpr (primPrimeDivs_subset w a)
    · intro a1 h1 a2 h2 heq
      have ha1 : a1 ∈ gaussPrimDivs w := (Finset.mem_filter.mp h1).1
      have ha2 : a2 ∈ gaussPrimDivs w := (Finset.mem_filter.mp h2).1
      have hs1 : Squarefree a1 := (Finset.mem_filter.mp h1).2
      have hs2 : Squarefree a2 := (Finset.mem_filter.mp h2).2
      rw [eq_prod_filter_dvd w a1 hw ha1 hs1, eq_prod_filter_dvd w a2 hw ha2 hs2, heq]
    · intro b hb
      have hb' : b ⊆ primPrimes w := Finset.mem_powerset.mp hb
      refine ⟨∏ p ∈ b, p, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨(mem_gaussPrimDivs hw).mpr
          ⟨prod_primPrimes_dvd hb', prod_primPrimes_isPrimary hb'⟩,
          prod_primPrimes_squarefree hb'⟩
      · simpa only [primPrimeDivs] using filter_dvd_prod_primPrimes_eq hb'
    · intro a ha
      have ha' : a ∈ gaussPrimDivs w := (Finset.mem_filter.mp ha).1
      have hs : Squarefree a := (Finset.mem_filter.mp ha).2
      rw [(eq_prod_filter_dvd w a hw ha' hs).symm]
  -- Step 3: evaluate the summand and use `∑_{S ⊆ P} ∏_{p ∈ S} f p = ∏_{p ∈ P} (1 + f p)`.
  have step3 :
      (∑ S ∈ (primPrimes w).powerset,
          (UniqueFactorizationMonoid.moebius (∏ p ∈ S, p) : ℂ)
            * (if (∏ p ∈ S, p) ∣ z then (1 : ℂ) else 0))
        = ∏ p ∈ primPrimes w, (1 - (if p ∣ z then (1 : ℂ) else 0)) := by
    rw [show (∏ p ∈ primPrimes w, (1 - (if p ∣ z then (1 : ℂ) else 0)))
          = ∏ p ∈ primPrimes w, (1 + (-(if p ∣ z then (1 : ℂ) else 0))) from
        Finset.prod_congr rfl (fun p _ => by rw [sub_eq_add_neg])]
    rw [← sum_powerset_prod (primPrimes w) (fun p => -(if p ∣ z then (1 : ℂ) else 0))]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    have hS' : S ⊆ primPrimes w := Finset.mem_powerset.mp hS
    rw [moebius_prod_primPrimes hS', ind_dvd_prod hS', Finset.prod_neg, Int.cast_pow]
    norm_num
  -- Step 4: the Euler product is the coprimality indicator.
  have step4 :
      (∏ p ∈ primPrimes w, (1 - (if p ∣ z then (1 : ℂ) else 0)))
        = if IsCoprime z w then 1 else 0 := by
    rw [show (∏ p ∈ primPrimes w, (1 - (if p ∣ z then (1 : ℂ) else 0)))
          = ∏ p ∈ primPrimes w, (if p ∣ z then (0 : ℂ) else 1) from
        Finset.prod_congr rfl (fun p _ => by by_cases h : p ∣ z <;> simp [h])]
    rw [prod_ite_zero_one]
    by_cases h : ∀ p ∈ primPrimes w, ¬ p ∣ z
    · rw [if_pos h, if_pos ((isCoprime_iff_no_primPrime_dvd hw).mpr h)]
    · rw [if_neg h, if_neg (fun hc => h ((isCoprime_iff_no_primPrime_dvd hw).mp hc))]
  exact step1.trans (step2.trans (step3.trans step4))

end

end Work.FIArea7.KStarDivs
