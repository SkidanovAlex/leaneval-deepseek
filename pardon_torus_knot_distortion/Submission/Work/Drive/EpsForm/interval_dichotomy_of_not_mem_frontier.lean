import Mathlib
import Submission.Work.SurgeryInvariance.Defs

namespace Work.Drive.EpsForm

/-- If a continuous (indeed any) parametrised family `γ ⁻¹' B` is an open subset of `ℝ`, and no
point of the interval `(u, v)` lies on its frontier, then on that interval `γ` is either everywhere
in `B` or everywhere outside `B`.  The point is simply that `(u, v)` is preconnected, while the
outside of the frontier forces the two open pieces `γ ⁻¹' B` and `(closure (γ ⁻¹' B))ᶜ` to cover it
with no room left over. -/
theorem interval_dichotomy_of_not_mem_frontier {γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    {B : Set LeanEval.KnotTheory.PardonDistortion.R3} {u v : ℝ}
    (hSopen : IsOpen (γ ⁻¹' B))
    (hfront : ∀ t ∈ Set.Ioo u v, t ∉ frontier (γ ⁻¹' B)) :
    (∀ t ∈ Set.Ioo u v, γ t ∈ B) ∨ (∀ t ∈ Set.Ioo u v, γ t ∉ B) := by
  obtain hS | hS := IsPreconnected.subset_or_subset (s := Set.Ioo u v) hSopen
    isClosed_closure.isOpen_compl
    (Disjoint.mono_right (Set.compl_subset_compl.mpr subset_closure) disjoint_compl_right)
    (by
      intro t ht
      by_cases htS : t ∈ γ ⁻¹' B
      · exact Or.inl htS
      · refine Or.inr ?_
        rw [Set.mem_compl_iff]
        intro hcl
        exact absurd (by
          rw [hSopen.frontier_eq]
          exact ⟨hcl, htS⟩) (hfront t ht))
    isPreconnected_Ioo
  · exact Or.inl fun t ht => hS ht
  · exact Or.inr fun t ht hB => hS ht (subset_closure hB)

end Work.Drive.EpsForm
