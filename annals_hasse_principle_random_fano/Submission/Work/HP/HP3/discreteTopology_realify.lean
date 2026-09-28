import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero

namespace Work.HP.HP3

open Work.HP

/-- The integer vectors form the standard lattice `ℤ^ι ⊆ ℝ^ι`, i.e. every element of `ℤ^ι` lies in
the `ℤ`-span of the coordinate functions. -/
private theorem mem_span_basisFun_of_int {ι : Type*} [Fintype ι] (v : ι → ℤ) :
    (fun i => (v i : ℝ)) ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) := by
  classical
  have h : (fun i => (v i : ℝ)) = ∑ i, v i • (Pi.basisFun ℝ ι i) := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · simp [Pi.basisFun_apply, Pi.single_eq_same]
    · intro b _ hb; simp [Pi.basisFun_apply, Pi.single_eq_of_ne' hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The realification of an integral lattice `Λ ⊆ ℤ^ι` is discrete in `ℝ^ι` (its points are
integer vectors, pairwise at distance `≥ 1`).  Suggested route: `DiscreteTopology.of_continuous_injective`
with the continuous injective map `↥(realify Λ) → ↥(span ℤ (Pi.basisFun ℝ ι))`; an identical proof
exists at lines 90–106 of `Submission/Work/HP/veronese_key.lean` (`Work.HP.discreteTopology_realify`)
and at `scratch/chk3.lean` — reuse it. -/
theorem discreteTopology_realify {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ (ι → ℤ)) : DiscreteTopology (realify Λ) := by
  classical
  -- every point of `realify Λ` is an integer vector, hence lies in the standard lattice `ℤ^ι`
  have hmem : ∀ x : ↥(realify Λ), (x : ι → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) := by
    intro x
    obtain ⟨v, _, hvx⟩ := Submodule.mem_map.mp x.2
    rw [← hvx]
    exact mem_span_basisFun_of_int v
  -- the inclusion of `↥(realify Λ)` into the discrete standard lattice is continuous and injective
  refine DiscreteTopology.of_continuous_injective
    (f := fun x : ↥(realify Λ) =>
      (⟨(x : ι → ℝ), hmem x⟩ : ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))))) ?_ ?_
  · exact Continuous.subtype_mk continuous_subtype_val _
  · intro a b hab
    exact Subtype.ext (congrArg
      (fun z : ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))) => (z : ι → ℝ)) hab)

end Work.HP.HP3
