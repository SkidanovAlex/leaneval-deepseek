import Mathlib
import Submission.Work.Drive.ProjectiveChartDefs

namespace Work.Drive

open Set

/-- Each coordinate `x ↦ (projSection i x).ofLp k` of the standard section is a smooth (indeed
affine) function of `x`: it is either the constant `1` (for `k = i`) or a coordinate projection. -/
lemma contDiff_projSection_ofLp (n : ℕ) (i : Fin (n + 1)) (k : Fin (n + 1)) :
    ContDiff ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) => (projSection i x).ofLp k) := by
  rcases eq_or_ne k i with rfl | hk
  · simpa using contDiff_const (c := (1 : ℝ))
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp only [projSection_apply_succAbove]
    exact contDiff_piLp_apply (p := 2) (𝕜 := ℝ) (n := ⊤)
      (E := fun _ : Fin n => ℝ) (i := j)

open scoped LinearAlgebra.Projectivization ContDiff in
/-- **The changes of coordinates of the classical projective charts are smooth.**  `projTransFun i i'` is the
change of coordinates from the `i`-th to the `i'`-th classical projective chart on `ℝPⁿ`, written in coordinates
on the model space `ℝⁿ = EuclideanSpace ℝ (Fin n)`: it is `x ↦ ((projSection i x)_j / (projSection i x)_{i'})_{j ≠ i'}`,
where `projSection i x` is the vector `(x, 1)` with a `1` in the `i`-th slot (definitions in
`Submission/Work/Drive/ProjectiveChartDefs.lean`).  On its domain `projTransSource i i'`, where that denominator
does not vanish, it is a rational function of `x` and hence smooth. -/
theorem contDiffOn_projTransFun (n : ℕ) (i i' : Fin (n + 1)) :
    ContDiffOn ℝ ⊤ (projTransFun (n := n) i i') (projTransSource i i') := by
  rw [contDiffOn_piLp]
  intro j
  have hnum : ContDiffOn ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) =>
      (projSection i x).ofLp (i'.succAbove j)) (projTransSource i i') :=
    (contDiff_projSection_ofLp n i _).contDiffOn
  have hden : ContDiffOn ℝ ⊤ (fun x : EuclideanSpace ℝ (Fin n) =>
      (projSection i x).ofLp i') (projTransSource i i') :=
    (contDiff_projSection_ofLp n i i').contDiffOn
  have hne : ∀ x ∈ projTransSource (n := n) i i', (projSection i x).ofLp i' ≠ 0 :=
    fun x hx => hx
  exact ContDiffOn.div hnum hden hne

end Work.Drive
