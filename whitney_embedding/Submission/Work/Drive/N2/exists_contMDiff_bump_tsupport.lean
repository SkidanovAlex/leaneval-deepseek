import Mathlib
import Submission.Work.Drive.N2.ModelDefs

/-!
# A smooth bump with *closed* support on a compact surface

`Work.Drive.N2.exists_contMDiff_bump_tsupport`: for a compact set `K` contained in an open set `U` of a
compact surface there is a smooth `χ : M → ℝ` with `0 ≤ χ ≤ 1`, `χ ≡ 1` on `K` and
`tsupport χ ⊆ U` (the *topological* support, i.e. the closure of the support, inside `U`).

This is the closed-support variant of `exists_contMDiffMap_one_nhds_of_subset_interior`, and it is
what the picture brick `Work.Drive.N2.exists_picture_of_chartBalls` needs: there the bumps have to
*vanish on neighbourhoods* of the complement of the chart source, not merely *at* its points.
Proof: shrink `U` to an open `W` with `closure W ⊆ U` (`normal_exists_closure_subset`), apply
Mathlib's bump lemma with `s := K`, `t := W`, and use `tsupport χ = closure (support χ) ⊆ closure W`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology

theorem exists_contMDiff_bump_tsupport {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {K U : Set M} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : M → ℝ) (V : Set M),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      tsupport χ ⊆ U ∧ IsOpen V ∧ K ⊆ V ∧ (∀ x ∈ V, χ x = 1) ∧
      (∀ x : M, 0 ≤ χ x ∧ χ x ≤ 1) := by
  haveI : NormalSpace M := inferInstance
  obtain ⟨W, hWopen, hKW, hWcl⟩ := normal_exists_closure_subset hK.isClosed hU hKU
  obtain ⟨f, hf1, hf2, hf3⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (n := (⊤ : ℕ∞)) hK.isClosed
      (by rw [hWopen.interior_eq]; exact hKW)
  obtain ⟨W', hW'open, hKW', hW'one⟩ := eventually_nhdsSet_iff_exists.mp hf1
  refine ⟨(f : M → ℝ), W', f.contMDiff, ?_, hW'open, hKW', hW'one,
    fun x => ⟨(hf3 x).1, (hf3 x).2⟩⟩
  · have hsupp : Function.support (f : M → ℝ) ⊆ W := fun x hx => by
      by_contra hxW
      exact hx (hf2 x hxW)
    rw [show tsupport (f : M → ℝ) = closure (Function.support (f : M → ℝ)) from rfl]
    exact (closure_mono hsupp).trans hWcl

end Work.Drive.N2
