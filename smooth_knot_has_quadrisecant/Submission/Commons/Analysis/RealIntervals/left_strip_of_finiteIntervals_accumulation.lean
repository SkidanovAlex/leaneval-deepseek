import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Instances.Real.Lemmas

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

namespace Commons.Analysis.RealIntervals

/-- **T2 analytic core (left side)**: if the left part `S ∩ (−∞, c)` of a real
set `S` is a FINITE union of open intervals `Ioo p.1 p.2` (`p ∈ F`, each
`p.2 ≤ c`) and `S` has points in every left-neighbourhood of `c`
(`hacc`: for every `ε > 0` there is a point of `S` in `(c−ε, c)`), then `S`
contains an open strip `(p, c)` reaching `c` from the left.

This is the analytic content of the "no-infinite-oscillation" principle T2
of the one-dimensional classification: infinite oscillation would let the
overlap accumulate at `c` through infinitely many components without any
single component reaching `c`; a FINITE component structure forces an end
strip.  (The one-sided terminal-attachment analysis of topological
1-manifolds consumes exactly this: one-sided accumulation + finite local
component structure ⇒ an end strip, from which the attaching arc is cut.)

Proof outline: (1) `hacc` gives `c ∈ closure (S ∩ Iio c)` (for an open
neighbourhood `U` of `c` take `ε` with `(c−ε, c) ⊆ U` from the metric
openness, pick the witness of `hacc ε`, it lies in `S ∩ Iio c ∩ U`); (2) by
`hF` this is `c ∈ closure (⋃ p ∈ F, Ioo p.1 p.2)`; (3) closure of a FINITE
union is the union of the closures (`closure_biUnion` / induction over the
Finset `F`), so `∃ p ∈ F, c ∈ closure (Ioo p.1 p.2)`; (4) in ℝ,
`closure (Ioo p.1 p.2) ⊆ Icc p.1 p.2` (or `closure_Ioo`), giving
`p.1 ≤ c ≤ p.2`, hence with `hvle` (`p.2 ≤ c`): `p.2 = c`; (5) `c ∈ closure
(Ioo p.1 p.2)` and the interval is open forces `p.1 < p.2` (an empty open
interval has empty closure), so `p.1 < c`; (6) `Ioo p.1 c = Ioo p.1 p.2` is
one of the finitely many intervals, hence `⊆ S ∩ Iio c ⊆ S`. -/
theorem left_strip_of_finiteIntervals_accumulation (S : Set ℝ) (c : ℝ)
    (F : Finset (ℝ × ℝ))
    (hF : S ∩ Set.Iio c = ⋃ p ∈ F, Set.Ioo p.1 p.2)
    (hvle : ∀ p ∈ F, p.2 ≤ c)
    (hacc : ∀ ε : ℝ, 0 < ε → (S ∩ Set.Ioo (c - ε) c).Nonempty) :
    ∃ p : ℝ, p < c ∧ Set.Ioo p c ⊆ S := by
  -- (1) c ∈ closure (S ∩ Iio c)
  have hcl1 : c ∈ closure (S ∩ Set.Iio c) := by
    rw [Real.mem_closure_iff]
    intro ε hε
    rcases hacc ε hε with ⟨x, hxS, hxI⟩
    refine ⟨x, ?_, ?_⟩
    · exact ⟨hxS, hxI.2⟩
    · have hxc : x < c := hxI.2
      have hcεx : c - ε < x := hxI.1
      have hle : 0 ≤ c - x := sub_nonneg.mpr (le_of_lt hxc)
      have hlt : c - x < ε := by linarith
      calc
        |x - c| = |c - x| := abs_sub_comm x c
        _ = c - x := abs_of_nonneg hle
        _ < ε := hlt
  -- (2)+(3) closure of the finite union
  have hclF : c ∈ closure (⋃ p ∈ F, Set.Ioo p.1 p.2) := by
    rw [← hF]
    exact hcl1
  have hclo : closure (⋃ p ∈ F, Set.Ioo p.1 p.2) =
      ⋃ p ∈ F, closure (Set.Ioo p.1 p.2) := by
    simpa using (Finset.closure_biUnion F (fun p : ℝ × ℝ => Set.Ioo p.1 p.2))
  have hcIn : c ∈ ⋃ p ∈ F, closure (Set.Ioo p.1 p.2) := by
    rw [hclo] at hclF
    exact hclF
  rcases (Set.mem_iUnion₂.mp hcIn) with ⟨q, hqF, hqc⟩
  -- (4) closure (Ioo q.1 q.2) ⊆ Icc q.1 q.2
  have hIccSub : closure (Set.Ioo q.1 q.2) ⊆ Set.Icc q.1 q.2 := by
    refine closure_minimal ?_ isClosed_Icc
    intro x hx
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hqcc : c ∈ Set.Icc q.1 q.2 := hIccSub hqc
  have hq2 : q.2 = c := le_antisymm (hvle q hqF) hqcc.2
  -- (5) the interval is nonempty (its closure contains c), so q.1 < c
  have hne : (Set.Ioo q.1 q.2).Nonempty := by
    by_contra h
    have hEmpty : Set.Ioo q.1 q.2 = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hcEmpty : c ∈ (∅ : Set ℝ) := by
      rw [hEmpty, closure_empty] at hqc
      exact hqc
    simpa using hcEmpty
  have hq1lt : q.1 < c := by
    have hq1lt2 : q.1 < q.2 := (Set.nonempty_Ioo).mp hne
    simpa [hq2] using hq1lt2
  -- (6) the interval (q.1, c) = (q.1, q.2) is one member of the finite union
  refine ⟨q.1, hq1lt, ?_⟩
  intro x hx
  have hxI : x ∈ Set.Ioo q.1 q.2 := by
    simpa [hq2] using hx
  have hxU : x ∈ ⋃ p ∈ F, Set.Ioo p.1 p.2 := Set.mem_iUnion₂.mpr ⟨q, hqF, hxI⟩
  have hxS : x ∈ S ∩ Set.Iio c := by
    rw [← hF] at hxU
    exact hxU
  exact hxS.1

end Commons.Analysis.RealIntervals