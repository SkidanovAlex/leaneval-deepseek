import Mathlib
import Submission.Work.LinnikAreas.CIDeps

/-!
# Decomposition of the class-`Λ` sum into its prime and prime-power parts

`Work.LinnikAreas.ClassLambdaSumDecomp` is a purely arithmetic bookkeeping identity: the
tent-weighted sum of `ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q)` over
`n ≤ X` splits, term by term, into

* the primes `p ≡ a [MOD q]`, where `Λ p = log p`, and
* the non-primes `n ≡ a [MOD q]` (i.e. the higher prime powers), carrying `Λ n`.

The two pieces are exactly the sums appearing in `Setup.lean`, so this lemma is the bridge
between the "class von Mangoldt sum" used by the Dirichlet-polynomial technology and the
prime / prime-power sums used by the analytic estimates.

The proof is elementary: unfold `residueClass` as an indicator, filter by the residue class,
split the filter according to primality, and use `Λ p = log p` on the prime part.
-/

namespace Work.LinnikAreas

open scoped BigOperators

/-- On the residue class `a mod q`, the restricted von Mangoldt function is `Λ`. -/
private lemma residueClass_eq_vonMangoldt_of_modEq {q : ℕ} (a n : ℕ) (h : n ≡ a [MOD q]) :
    ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n = ArithmeticFunction.vonMangoldt n := by
  have hz : n ∈ {m : ℕ | (m : ZMod q) = (a : ZMod q)} := modEq_iff_zmod_eq.mp h
  rw [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_of_mem hz]

/-- Off the residue class `a mod q`, the restricted von Mangoldt function vanishes. -/
private lemma residueClass_eq_zero_of_not_modEq {q : ℕ} (a n : ℕ) (h : ¬ n ≡ a [MOD q]) :
    ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n = 0 := by
  have hz : n ∉ {m : ℕ | (m : ZMod q) = (a : ZMod q)} := fun hh => h (modEq_iff_zmod_eq.mpr hh)
  rw [ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_of_notMem hz]

/-- The real form of the decomposition: the class von Mangoldt sum equals the prime sum plus
the non-prime sum. -/
private lemma real_classLambda_decomp {q : ℕ} [NeZero q] (a X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X,
        ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n *
          (Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
            (Real.log (n : ℝ) / Real.log (q : ℝ)) / (n : ℝ)))
      = (∑ p ∈ (Finset.Icc 1 X).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]),
            Real.log (p : ℝ) / (p : ℝ) *
              Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
                (Real.log (p : ℝ) / Real.log (q : ℝ)))
        + (∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
            ArithmeticFunction.vonMangoldt n / (n : ℝ) *
              Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
                (Real.log (n : ℝ) / Real.log (q : ℝ))) := by
  rw [← Icc_one_eq_Ioc_zero X]
  -- filter the (unfiltered) sum down to the residue class
  have h1 : (∑ n ∈ Finset.Icc 1 X,
        ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n *
          (Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
            (Real.log (n : ℝ) / Real.log (q : ℝ)) / (n : ℝ)))
      = ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => n ≡ a [MOD q]),
          ArithmeticFunction.vonMangoldt n *
            (Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
              (Real.log (n : ℝ) / Real.log (q : ℝ)) / (n : ℝ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h : n ≡ a [MOD q]
    · rw [if_pos h, residueClass_eq_vonMangoldt_of_modEq a n h]
    · rw [if_neg h, residueClass_eq_zero_of_not_modEq a n h, zero_mul]
  rw [h1]
  -- split the residue-class filter into primes and non-primes
  have hdisj : Disjoint ((Finset.Icc 1 X).filter (fun n : ℕ => n.Prime ∧ n ≡ a [MOD q]))
      ((Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q])) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    exact (Finset.mem_filter.mp hn2).2.1 (Finset.mem_filter.mp hn1).2.1
  have hfilter : (Finset.Icc 1 X).filter (fun n : ℕ => n.Prime ∧ n ≡ a [MOD q]) ∪
      (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q])
      = (Finset.Icc 1 X).filter (fun n : ℕ => n ≡ a [MOD q]) := by
    ext n
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) <;> exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      by_cases hp : n.Prime
      · exact Or.inl ⟨h1, hp, h3⟩
      · exact Or.inr ⟨h1, hp, h3⟩
  rw [← hfilter, Finset.sum_union hdisj]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨-, hp, _⟩ := Finset.mem_filter.mp hn
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    ring
  · refine Finset.sum_congr rfl fun _ _ => ?_
    ring

/-- Coercing the real class von Mangoldt sum to `ℂ` termwise. -/
private lemma ofReal_classLambda_sum {q : ℕ} (a X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X,
        ((ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n : ℝ) : ℂ) *
          (((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
            (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) / (n : ℂ)))
      = ((∑ n ∈ Finset.Ioc 0 X,
            ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n *
              (Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
                (Real.log (n : ℝ) / Real.log (q : ℝ)) / (n : ℝ)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast]

/-- **Decomposition of the tent-weighted class von Mangoldt sum.**
The complex class-`Λ` sum over `n ≤ X` is the sum of its prime part and of its
higher-prime-power part, both restricted to the residue class `a mod q`. -/
theorem ClassLambdaSumDecomp {q : ℕ} [NeZero q] (a : ℕ) (X : ℕ) :
    (∑ n ∈ Finset.Ioc 0 X,
        ((ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n : ℝ) : ℂ) *
          (((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
            (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) / (n : ℂ)))
      = (((∑ p ∈ (Finset.Icc 1 X).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]),
            Real.log (p : ℝ) / (p : ℝ) *
              Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
                (Real.log (p : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)
         + ((∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
            ArithmeticFunction.vonMangoldt n / (n : ℝ) *
              Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
                (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)) := by
  rw [ofReal_classLambda_sum (q := q) a X, real_classLambda_decomp (q := q) a X,
    Complex.ofReal_add]

end Work.LinnikAreas
