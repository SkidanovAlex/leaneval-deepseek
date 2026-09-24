import Mathlib.Topology.Homotopy.Equiv
import Submission.Commons.Topology.CWComplex.exists_cwComplex_homeomorph_univ

set_option linter.style.haveILetI false

namespace Commons.Topology.CWComplex

open Set Function

universe u

/-- **Universe lifting of a countable one-dimensional CW complex.**

A Hausdorff, second countable CW complex `Y` all of whose cells are countable and which has no
cells in dimension `≥ 2` admits a model in any universe `u`: there are `Y' : Type u` with a
topology `tY'`, a CW complex structure on all of `Y'` with countably many cells and no cells in
dimension `≥ 2`, and a homotopy equivalence `Y ≃ Y'`.

The construction is the natural one: the countability hypotheses produce a surjection onto `Y`
from the small type `Σ n, (hC.cell n) × (Fin n → ℝ)`, so `Y` is `u`-small; take a `u`-small model
`Y'` of `Y` and transport the topology and the CW structure along the resulting bijection. -/
theorem exists_cwComplex_univ_lift_universe {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] (hC : Topology.CWComplex (X := Y) Set.univ)
    (hcnt : ∀ n : ℕ, Countable (hC.cell n))
    (hdim : ∀ n : ℕ, 2 ≤ n → IsEmpty (hC.cell n)) :
    ∃ (Y' : Type u) (tY' : TopologicalSpace Y'), @T2Space Y' tY' ∧
      ∃ (hC' : @Topology.CWComplex Y' tY' Set.univ),
        (∀ n : ℕ, Countable (@Topology.CWComplex.cell Y' tY' Set.univ hC' n)) ∧
        (∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell Y' tY' Set.univ hC' n)) ∧
        Nonempty (@ContinuousMap.HomotopyEquiv Y Y' _ tY') := by
  classical
  -- ## Step 1: `Y` is a quotient of a small type.
  let g : (Σ n : ℕ, hC.cell n × (Fin n → ℝ)) → Y :=
    fun p => hC.map p.1 p.2.1 p.2.2
  have hg : Function.Surjective g := by
    intro y
    have hy : y ∈ (⋃ (n : ℕ) (j : hC.cell n),
        hC.map n j '' Metric.closedBall (0 : Fin n → ℝ) 1) := by
      rw [hC.union']
      exact mem_univ y
    rw [mem_iUnion] at hy
    obtain ⟨n, hy⟩ := hy
    rw [mem_iUnion] at hy
    obtain ⟨j, x, _hx, hxj⟩ := hy
    exact ⟨⟨n, j, x⟩, hxj⟩
  -- ## Step 2: the small type surjects onto `Y`, so `Y` is `u`-small.
  haveI hN : Small.{u} ℕ := small_max ℕ
  haveI hc : ∀ n : ℕ, Small.{u} (hC.cell n) := fun n => Countable.toSmall (hC.cell n)
  haveI hr : ∀ n : ℕ, Small.{u} (Fin n → ℝ) := fun n => small_zero _
  haveI hp : ∀ n : ℕ, Small.{u} (hC.cell n × (Fin n → ℝ)) := fun n => small_prod
  haveI hsmall_dom : Small.{u} (Σ n : ℕ, hC.cell n × (Fin n → ℝ)) :=
    small_sigma (fun n => hC.cell n × (Fin n → ℝ))
  have hsmallY : Small.{u} Y := small_of_surjective (f := g) hg
  -- ## Step 3: pick a model in `Type u` and transport the topology.
  obtain ⟨Y', he⟩ := hsmallY.equiv_small
  obtain ⟨e⟩ := he
  let tY' : TopologicalSpace Y' := TopologicalSpace.induced e.symm ‹TopologicalSpace Y›
  letI : TopologicalSpace Y' := tY'
  have hInd : Topology.IsInducing (e.symm : Y' → Y) := ⟨rfl⟩
  have hE : Y' ≃ₜ Y := (e.symm).toHomeomorphOfIsInducing hInd
  have hE' : Y ≃ₜ Y' := hE.symm
  -- ## Step 4: transport the CW structure and record the counts.
  obtain ⟨hC', hcell'⟩ :=
    Commons.Topology.CWComplex.exists_cwComplex_homeomorph_univ hC hE'
  refine ⟨Y', tY', ?_, hC', ?_, ?_, ?_⟩
  · -- `Y'` is Hausdorff, being homeomorphic to `Y`.
    exact Topology.IsEmbedding.t2Space hE.isEmbedding
  · -- countably many cells in each dimension
    intro n
    obtain ⟨φ⟩ := hcell' n
    haveI := hcnt n
    exact φ.injective.countable
  · -- no cells in dimension `≥ 2`
    intro n hn
    obtain ⟨φ⟩ := hcell' n
    exact ⟨fun a => (hdim n hn).false (φ a)⟩
  · -- a homeomorphism induces a homotopy equivalence
    exact ⟨hE'.toHomotopyEquiv⟩

end Commons.Topology.CWComplex