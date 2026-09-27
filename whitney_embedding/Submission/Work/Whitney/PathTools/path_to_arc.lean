import Mathlib
import Submission.Work.Topology.PeanoContinuum.arc_of_path
import Submission.Work.Topology.PeanoContinuum.arc_extract

/-!
# From a path to an arc in a metric space

`Work.Whitney.PathTools.exists_arc_of_path`: if `f : ℝ → X` is continuous into a metric space and
`f 0 ≠ f 1`, then there is a continuous `γ : ℝ → X`, injective on `[0,1]`, with `γ 0 = f 0` and
`γ 1 = f 1`.

This packages the two halves of the classical Nadler argument that are already in the workspace:

* `Work.Topology.PeanoContinuum.exists_minimal_admissible` (Zorn) gives a minimal admissible
  `K ⊆ [0,1]`;
* `Work.Topology.PeanoContinuum.continuous_collapse` and
  `Work.Topology.PeanoContinuum.collapse_fibre_interval` show that the collapse `collapse f K` is
  continuous with interval fibres (this is where minimality of `K` is used), and its endpoints are
  `f 0`, `f 1`;
* `Work.Topology.PeanoContinuum.exists_arc_of_interval_fibres` then reparametrises it to an
  injective map on `[0,1]`.
-/

namespace Work.Whitney.PathTools

open Set

/-- **A path between distinct points contains an arc between them.** -/
theorem exists_arc_of_path {X : Type*} [MetricSpace X] {f : ℝ → X} (hf : Continuous f)
    (hne : f 0 ≠ f 1) :
    ∃ γ : ℝ → X, Continuous γ ∧ Set.InjOn γ (Set.Icc (0:ℝ) 1) ∧ γ 0 = f 0 ∧ γ 1 = f 1 := by
  obtain ⟨K, hK, hmin⟩ := Work.Topology.PeanoContinuum.exists_minimal_admissible f hf
  have hfib : Work.Topology.PeanoContinuum.IsFibreInterval
      (Work.Topology.PeanoContinuum.collapse f K) := by
    intro s t u hs hu hsu hst htu
    exact Work.Topology.PeanoContinuum.collapse_fibre_interval f hf hK hmin hst htu hsu
  have hne' : Work.Topology.PeanoContinuum.collapse f K 0
      ≠ Work.Topology.PeanoContinuum.collapse f K 1 := by
    rw [Work.Topology.PeanoContinuum.collapse_zero f hK,
      Work.Topology.PeanoContinuum.collapse_one f hK]
    exact hne
  obtain ⟨γ, hγc, hγinj, hγ0, hγ1⟩ := Work.Topology.PeanoContinuum.exists_arc_of_interval_fibres
    (g := Work.Topology.PeanoContinuum.collapse f K)
    (Work.Topology.PeanoContinuum.continuous_collapse f hf hK) hfib hne'
  exact ⟨γ, hγc, hγinj, by rw [hγ0, Work.Topology.PeanoContinuum.collapse_zero f hK],
    by rw [hγ1, Work.Topology.PeanoContinuum.collapse_one f hK]⟩

end Work.Whitney.PathTools
