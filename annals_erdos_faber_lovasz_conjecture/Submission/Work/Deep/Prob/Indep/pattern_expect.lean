import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Prob.Basic
import Submission.Work.Deep.Prob.Spaces

namespace Work.Deep.Prob.Indep

open scoped BigOperators

/-- The law of a single outcome pattern of an independent family of events: the probability
that the pattern of `ω` is exactly `s` is the product of the marginal probabilities of the
coordinates.  (The joint atom `⋂ i, if s i then A i else (A i)ᶜ` is the preimage of `s`
under `pattern A`, and independence makes its probability the product of the marginals.) -/
theorem prob_pattern_atom {Ω : Type*} [Fintype Ω] (P : FinProbSpace Ω) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : ι → Set Ω} (h : FinProbSpace.IndepEvents P A) (s : ι → Bool) :
    P.prob {ω | FinProbSpace.pattern A ω = s}
      = ∏ i, if s i then P.prob (A i) else 1 - P.prob (A i) := by
  have hset : {ω | FinProbSpace.pattern A ω = s} = ⋂ i, if s i then A i else (A i)ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [funext_iff]
    refine forall_congr' fun i => ?_
    by_cases hs : s i = true
    · simp [hs, FinProbSpace.pattern_eq_true_iff]
    · simp [hs, FinProbSpace.pattern_eq_false_iff, Set.mem_compl_iff]
  have hh := h s
  rw [hset, hh]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hs : s i = true
  · simp [hs]
  · simp [hs, FinProbSpace.prob_compl]

/-- Decomposition of an expectation along the pattern: `Ω` is partitioned into the atoms
`{ω | pattern A ω = s}`, and the expectation of a function of the pattern is the sum over
atoms of the atom mass times the value of `F` at that atom. -/
theorem expect_pattern_sum {Ω : Type*} [Fintype Ω] (P : FinProbSpace Ω) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : ι → Set Ω} (F : (ι → Bool) → ℝ) :
    P.expect (fun ω => F (FinProbSpace.pattern A ω))
      = ∑ s : ι → Bool, P.prob {ω | FinProbSpace.pattern A ω = s} * F s := by
  rw [FinProbSpace.expect]
  have hfib : ∀ ω : Ω,
      ∑ s : ι → Bool, {ω' | FinProbSpace.pattern A ω' = s}.indicator P.mass ω * F s
        = P.mass ω * F (FinProbSpace.pattern A ω) := by
    intro ω
    have h0 : ∀ s ∈ (Finset.univ : Finset (ι → Bool)), s ≠ FinProbSpace.pattern A ω →
        {ω' | FinProbSpace.pattern A ω' = s}.indicator P.mass ω * F s = 0 := by
      intro s _ hs
      rw [Set.indicator_of_notMem (fun hmem => hs (Set.mem_ofPred_eq.mp hmem).symm)]
      ring
    have h1 : FinProbSpace.pattern A ω ∉ (Finset.univ : Finset (ι → Bool)) →
        {ω' | FinProbSpace.pattern A ω' = FinProbSpace.pattern A ω}.indicator P.mass ω
          * F (FinProbSpace.pattern A ω) = 0 :=
      fun hmem => absurd (Finset.mem_univ _) hmem
    rw [Finset.sum_eq_single (FinProbSpace.pattern A ω) h0 h1,
      Set.indicator_of_mem (show ω ∈ {ω' | FinProbSpace.pattern A ω' = FinProbSpace.pattern A ω}
        from rfl)]
  calc ∑ ω : Ω, P.mass ω * F (FinProbSpace.pattern A ω)
      = ∑ ω : Ω, ∑ s : ι → Bool,
          {ω' | FinProbSpace.pattern A ω' = s}.indicator P.mass ω * F s := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        exact (hfib ω).symm
    _ = ∑ s : ι → Bool, ∑ ω : Ω,
          {ω' | FinProbSpace.pattern A ω' = s}.indicator P.mass ω * F s :=
        Finset.sum_comm
    _ = ∑ s : ι → Bool, P.prob {ω | FinProbSpace.pattern A ω = s} * F s := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [FinProbSpace.prob, Finset.sum_mul]

theorem pattern_expect {Ω : Type*} [Fintype Ω] (P : FinProbSpace Ω) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : ι → Set Ω} (h : FinProbSpace.IndepEvents P A) (F : (ι → Bool) → ℝ) :
    P.expect (fun ω => F (FinProbSpace.pattern A ω))
      = ∑ s : ι → Bool,
          (∏ i, if s i then P.prob (A i) else 1 - P.prob (A i)) * F s := by
  rw [expect_pattern_sum P F]
  exact Finset.sum_congr rfl fun s _ => by rw [prob_pattern_atom P h s]

end Work.Deep.Prob.Indep
