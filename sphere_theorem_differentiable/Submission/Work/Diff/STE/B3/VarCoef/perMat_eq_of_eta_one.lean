import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.perMatDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

/-- **The periodised cut-off chart matrix equals the chart matrix at a point where the cut-off is
`1`.**

Because `tsupport η` lies inside the open centred cube, the point `z` itself lies in that cube
(`η z = 1 ≠ 0`), and every non-zero lattice translate `z + iVec m` of `z` leaves the cube, hence
`η` vanishes there.  So the periodisation `∑' m, η (z + iVec m) · D.mat l h a b (z + iVec m)`
reduces to its `m = 0` term, which is `D.mat l h a b z` since `η z = 1`.

This is the `η z = 1`-variant of `Work.Diff.STE.B3.perMat_eq_of_mem_ball`, where the unit value of
`η` is assumed at an arbitrary point of the cube rather than on the ball `‖z‖ ≤ 1/4`. -/
theorem perMat_eq_of_eta_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (l : ι₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : η z = 1) :
    Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h a b z
      = ((D.mat l h a b z : ℝ) : ℂ) := by
  -- `z` lies in the open centred cube: `η z = 1` makes it a point of the support of `η`, whose
  -- closure is contained in the cube by hypothesis.
  have hcube : ∀ j : Fin (Module.finrank ℝ E), z j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    have hzmem := hηt (subset_tsupport η (Function.mem_support.mpr (by rw [hz]; norm_num)))
    rw [Set.mem_pi] at hzmem
    exact fun j => hzmem j (Set.mem_univ j)
  rw [Work.Diff.STE.B3.perMat]
  rw [tsum_eq_single (0 : Fin (Module.finrank ℝ E) → ℤ)]
  · -- the `m = 0` term is `η z · D.mat l h a b z = D.mat l h a b z`
    have h0 : z + Work.Diff.STE.iVec (0 : Fin (Module.finrank ℝ E) → ℤ) = z := by
      funext j
      simp [Work.Diff.STE.iVec]
    rw [h0, hz, one_mul]
  · -- every non-zero lattice translate leaves the cube, hence is outside `tsupport η`
    intro m hm
    have hzero : η (z + Work.Diff.STE.iVec m) = 0 := by
      by_contra hne
      have hmem := hηt (subset_closure (Function.mem_support.mpr hne))
      rw [Set.mem_pi] at hmem
      exact hm (Work.Diff.STE.B3.lattice_add_eq_zero_of_mem_cube hcube
        (fun j => hmem j (Set.mem_univ j)))
    simp [hzero]

end Work.Diff.STE.B3.VarCoef
