import Mathlib
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.levelField_spec

/-!
# Auxiliary smoothness lemmas for the ambient model field
-/

open scoped Manifold ContDiff Topology
open Set Function

namespace Work.Drive.N2

/-- If `g` is smooth and supported inside an open set on which `f` is smooth, then `g • f` is
smooth. -/
lemma contDiff_smul_of_contDiffOn_aux {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {O : Set E} (hO : IsOpen O) {g : E → ℝ} {f : E → F}
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O) (hsupp : tsupport g ⊆ O) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => g z • f z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ O
  · exact hg.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds hz))
  · have hz' : z ∉ tsupport g := fun h => hz (hsupp h)
    have hmem : ∀ᶠ w in 𝓝 z, g w = 0 :=
      Filter.mem_of_superset ((isClosed_tsupport g).isOpen_compl.mem_nhds hz')
        (fun w hw => Function.notMem_support.mp (fun h => hw (subset_tsupport g h)))
    have hEv : (fun w => g w • f w) =ᶠ[𝓝 z] fun _ => (0 : F) := by
      filter_upwards [hmem] with w hw
      simp [hw]
    exact contDiffAt_const.congr_of_eventuallyEq hEv

end Work.Drive.N2
