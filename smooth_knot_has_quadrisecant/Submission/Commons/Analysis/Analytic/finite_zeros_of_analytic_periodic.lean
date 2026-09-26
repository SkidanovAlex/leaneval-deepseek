import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.InnerProductSpace.Basic

open Filter
open scoped Topology

set_option linter.unusedVariables false

namespace Commons.Analysis.Analytic

theorem finite_zeros_of_analytic_periodic {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : AnalyticOnNhd ℝ f Set.univ) (hper : Function.Periodic f p)
    (hne : ∃ x ∈ Set.Icc 0 p, f x ≠ 0) :
    {x : ℝ | x ∈ Set.Icc 0 p ∧ f x = 0}.Finite := by
  by_contra hfin
  obtain ⟨x, -, hx⟩ :=
    (show {x : ℝ | x ∈ Set.Icc 0 p ∧ f x = 0}.Infinite from hfin).exists_accPt_of_subset_isCompact
      isCompact_Icc (fun y hy => hy.1)
  have hfreq : ∃ᶠ z in 𝓝[≠] x, f z = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hx).mono fun z hz => hz.2
  have hzero : Set.EqOn f 0 Set.univ :=
    hf.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ x) hfreq
  obtain ⟨y, -, hyne⟩ := hne
  exact hyne (hzero (Set.mem_univ y))

end Commons.Analysis.Analytic