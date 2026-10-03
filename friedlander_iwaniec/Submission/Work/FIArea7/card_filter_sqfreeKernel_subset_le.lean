import Mathlib
import Submission.Work.FIArea4.SqfreeKernel
import Submission.Work.FIArea4.sqfree_kernel
import Submission.Work.FIArea4.card_sqfreeKernel_eq_le_sqrt

namespace Work.FIArea7

open scoped BigOperators

/-- Auxiliary counting step: the `n ∈ [1,M]` whose squarefree kernel has all prime factors in `P`
are split into the fibres of the map `n ↦ (sqfreeKernel n).primeFactors`, each fibre being
contained in the set of `n` with a prescribed squarefree kernel, which is counted by
`Work.FIArea4.card_sqfreeKernel_eq_le_sqrt`.  This gives the bound
`#{n} ≤ ∑_{t ⊆ P} √(M / ∏_{p ∈ t} p)`. -/
lemma card_filter_sqfreeKernel_subset_le_sum (M : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (((Finset.Icc 1 M).filter
        (fun n : ℕ => (Work.FIArea4.sqfreeKernel n).primeFactors ⊆ P)).card : ℝ)
      ≤ ∑ t ∈ P.powerset, Real.sqrt ((M : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ)) := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 M).filter
      (fun n : ℕ => (Work.FIArea4.sqfreeKernel n).primeFactors ⊆ P) with hS
  have hmap : Set.MapsTo (fun n : ℕ => (Work.FIArea4.sqfreeKernel n).primeFactors)
      ↑S ↑P.powerset := by
    intro n hn
    rw [Finset.mem_coe, hS, Finset.mem_filter] at hn
    exact Finset.mem_powerset.mpr hn.2
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := fun n : ℕ => (Work.FIArea4.sqfreeKernel n).primeFactors) hmap
  have hcardR : ((S.card : ℕ) : ℝ)
      = ∑ t ∈ P.powerset,
          (((S.filter (fun n : ℕ => (Work.FIArea4.sqfreeKernel n).primeFactors = t)).card : ℕ) : ℝ) := by
    rw [hcard]; push_cast; rfl
  rw [hcardR]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.mem_powerset] at ht
  have hd1 : 1 ≤ ∏ p ∈ t, p := by
    apply Finset.one_le_prod₀
    intro p hp
    exact (hP p (ht hp)).one_le
  have hsub : S.filter (fun n : ℕ => (Work.FIArea4.sqfreeKernel n).primeFactors = t) ⊆
      (Finset.Icc 1 M).filter (fun n : ℕ => Work.FIArea4.sqfreeKernel n = ∏ p ∈ t, p) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnS, hnt⟩ := hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hnS
    obtain ⟨⟨hn1, hnM⟩, _⟩ := hnS
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hn1, hnM⟩, ?_⟩
    have hn0 : n ≠ 0 := by omega
    have hsf := (Work.FIArea4.sqfree_kernel n hn0).2.2.2.2
    have hp := Nat.prod_primeFactors_of_squarefree hsf
    rw [← hnt]
    exact hp.symm
  calc (((S.filter (fun n : ℕ => (Work.FIArea4.sqfreeKernel n).primeFactors = t)).card : ℕ) : ℝ)
      ≤ (((Finset.Icc 1 M).filter (fun n : ℕ => Work.FIArea4.sqfreeKernel n = ∏ p ∈ t, p)).card : ℕ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ Real.sqrt ((M : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ)) :=
        Work.FIArea4.card_sqfreeKernel_eq_le_sqrt M (∏ p ∈ t, p) hd1

/-- Auxiliary product/sum identity: `∑_{t ⊆ P} √(M / ∏_{p ∈ t} p) = √M · ∏_{p ∈ P}(1 + 1/√p)`.
Each term is rewritten as `√M · ∏_{p ∈ t} 1/√p` via `Real.sqrt_div`, `Real.sqrt_prod` and
`Finset.prod_inv_distrib`; the `√M` factors out and `Finset.prod_add_one` evaluates the sum of
sub-products. -/
lemma sum_powerset_sqrt_div_eq (M : ℕ) (P : Finset ℕ) :
    (∑ t ∈ P.powerset, Real.sqrt ((M : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ)))
      = Real.sqrt (M : ℝ) * ∏ p ∈ P, (1 + 1 / Real.sqrt (p : ℝ)) := by
  have hterm : ∀ t ∈ P.powerset,
      Real.sqrt ((M : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ))
        = Real.sqrt (M : ℝ) * ∏ p ∈ t, (1 / Real.sqrt (p : ℝ)) := by
    intro t ht
    rw [Nat.cast_prod, Real.sqrt_div (Nat.cast_nonneg M),
        Real.sqrt_prod t (fun p _ => Nat.cast_nonneg p)]
    rw [div_eq_mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [inv_eq_one_div]
  calc (∑ t ∈ P.powerset, Real.sqrt ((M : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ)))
      = ∑ t ∈ P.powerset, (Real.sqrt (M : ℝ) * ∏ p ∈ t, (1 / Real.sqrt (p : ℝ))) :=
        Finset.sum_congr rfl hterm
    _ = Real.sqrt (M : ℝ) * ∑ t ∈ P.powerset, ∏ p ∈ t, (1 / Real.sqrt (p : ℝ)) := by
        rw [Finset.mul_sum]
    _ = Real.sqrt (M : ℝ) * ∏ p ∈ P, (1 + 1 / Real.sqrt (p : ℝ)) := by
        congr 1
        rw [← Finset.prod_add_one (f := fun p : ℕ => 1 / Real.sqrt (p : ℝ)) P]
        refine Finset.prod_congr rfl fun p hp => ?_
        rw [add_comm]

/-- Count of `n ∈ [1,M]` whose squarefree kernel has all its prime factors in a finite set `P` of
primes: at most `√M · ∏_{p ∈ P} (1 + 1/√p)`.

Proof: let `S = (Icc 1 M).filter (fun n => (sqfreeKernel n).primeFactors ⊆ P)`.  The map
`n ↦ (sqfreeKernel n).primeFactors` sends `S` into `P.powerset`, so
`Finset.card_eq_sum_card_fiberwise` gives `S.card = ∑ t ∈ P.powerset, #{n ∈ S : ... = t}`, and each
fiber is contained in `(Icc 1 M).filter (fun n => sqfreeKernel n = ∏ p ∈ t, p)`: for `n ∈ S`, use
`Nat.prod_primeFactors_of_squarefree` with `Squarefree (sqfreeKernel n)`.  Since
`1 ≤ ∏ p ∈ t, p` (each `p ∈ t ⊆ P` is prime hence `≥ 1`), the fiber bound
`Work.FIArea4.card_sqfreeKernel_eq_le_sqrt M (∏ p ∈ t, p) h` gives
`S.card ≤ ∑ t ∈ P.powerset, √(M / ∏_{p∈t} p)`.
Then rewrite each term: `√((M:ℝ)/d) = √M / √d`, `√d = ∏_{p∈t} √p` (`Real.sqrt_prod`,
`Nat.cast_prod`), `1/∏√p = ∏ (1/√p)` (`Finset.prod_inv_distrib`, each `√p ≠ 0` since `p ≥ 2`), and
pull `√M` out of the sum.  Finally `∑_{t ⊆ P} ∏_{p∈t} (1/√p) = ∏_{p∈P}(1 + 1/√p)` by
`Finset.prod_add` with `f p = 1/√p` and `g = 1` (the complement product is `1`). -/
theorem card_filter_sqfreeKernel_subset_le (M : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (((Finset.Icc 1 M).filter
        (fun n : ℕ => (Work.FIArea4.sqfreeKernel n).primeFactors ⊆ P)).card : ℝ)
      ≤ Real.sqrt (M : ℝ) * ∏ p ∈ P, (1 + 1 / Real.sqrt (p : ℝ)) := by
  calc (((Finset.Icc 1 M).filter
        (fun n : ℕ => (Work.FIArea4.sqfreeKernel n).primeFactors ⊆ P)).card : ℝ)
      ≤ ∑ t ∈ P.powerset, Real.sqrt ((M : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ)) :=
        card_filter_sqfreeKernel_subset_le_sum M P hP
    _ = Real.sqrt (M : ℝ) * ∏ p ∈ P, (1 + 1 / Real.sqrt (p : ℝ)) :=
        sum_powerset_sqrt_div_eq M P

end Work.FIArea7
