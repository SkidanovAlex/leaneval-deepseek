import Mathlib
import Submission.Work.Drive.psgValDefs

/-!
# The corner subspace of a pair of distinct coordinates has dimension `3`

`Work.Drive.cornerSub j k` is the subspace `{z : Amb 4 // z j = 0 ∧ z k = 0}` of the five-dimensional
box `Amb 4 = 𝔼^5`, i.e. the kernel of the coordinate pair `z ↦ (z j, z k)`.  For `j ≠ k` that map is
onto `ℝ × ℝ` (the `j`-th and `k`-th standard basis vectors generate the target), so the rank–nullity
identity `finrank range + finrank ker = finrank (𝔼^5)` gives `finrank (cornerSub j k) = 5 - 2 = 3`.

This is the dimension fact behind the "corner" parametrisation of the codimension-two skeleton of the
box used in the avoidance clause of `Work.Drive.psg_family_regular`: the corner `z j = a`, `z k = b`
is a copy of `cornerSub j k`, hence a three-dimensional affine subspace, and the analytic Sard lemmas
apply to its parametrisation `Work.Drive.cornerPt j k a b`.
-/

namespace Work.Drive

/-- **The coordinate pair `z ↦ (z j, z k)` is surjective for `j ≠ k`**: the two standard basis
vectors `e5 j`, `e5 k` already span the target `ℝ × ℝ`. -/
lemma cornerLM_surjective (j k : Fin 5) (hjk : j ≠ k) :
    Function.Surjective (cornerLM j k) := by
  intro p
  refine ⟨(p.1 • e5 j + p.2 • e5 k : Amb 4), ?_⟩
  simp [cornerLM, LinearMap.prod_apply, e5, hjk, PiLp.add_apply]

theorem cornerSub_finrank (j k : Fin 5) (hjk : j ≠ k) :
    Module.finrank ℝ (Work.Drive.cornerSub j k) = 3 := by
  have hsurj : Function.Surjective (cornerLM j k) := cornerLM_surjective j k hjk
  have hrange : Module.finrank ℝ (LinearMap.range (cornerLM j k)) = 2 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_prod]
    norm_num
  have h := LinearMap.finrank_range_add_finrank_ker (cornerLM j k)
  have hamb : Module.finrank ℝ (Amb 4) = 5 := by simp [Amb, finrank_euclideanSpace]
  change Module.finrank ℝ (LinearMap.ker (cornerLM j k)) = 3
  omega

end Work.Drive
