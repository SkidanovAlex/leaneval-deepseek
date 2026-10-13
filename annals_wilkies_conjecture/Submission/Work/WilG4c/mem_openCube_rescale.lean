import Mathlib
import Submission.Work.Wilkies.CG.Spec

namespace Work.WilG4c

/-- A grid point `v` with `0 ≤ v i ≤ lam - 1` and a point `x` of the open cube give a point
`(v + x)/lam` of the open cube, for `lam > 0`. -/
theorem mem_openCube_rescale {N : ℕ} {lam : ℝ} (hlam : 0 < lam) {v x : Fin N → ℝ}
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ lam - 1) (hx : x ∈ WilkiesDesign.openCube N) :
    (fun i => (v i + x i) / lam) ∈ WilkiesDesign.openCube N := by
  intro i
  obtain ⟨hv0, hvl⟩ := hv i
  obtain ⟨hx0, hx1⟩ := hx i
  refine ⟨div_pos (by linarith) hlam, ?_⟩
  rw [div_lt_one hlam]
  linarith

end Work.WilG4c
