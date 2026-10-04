import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The weight `ψ i · √dens i` of the B3 localised components

Layer B3 writes the localised component of a section `h` as

`D.R i h a b z = D.psi i z * Real.sqrt (D.dens i z) * D.mat i h a b z`,

where `D.mat i h a b` is the chart matrix of `h` in the `g₀`-orthonormal frame `e i a`.

The *weight* `D.psi i z * Real.sqrt (D.dens i z)` — defined here as `matA D i z` — is independent
of `h`.  To bound the derivatives of the chart matrix `D.mat i h a b` in terms of the composite norm
`D.BNorm k h` one divides the component `D.R i h a b` by this weight; the crude estimates for the
weight and its first two derivatives on the `σ i`-ball (`matA_jets`, `psi_le_const`) are collected in
this file's siblings.
-/

noncomputable section

namespace Work.Diff.STE.Lead

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The **weight** of the localised component of chart `i`: `ψ i z · √(dens i z)`, with
`ψ i = χ i · ζ i ∘ pt i` the localised weight of `B3Data` and `dens i` the chart volume density.
For this weight, `D.R i h a b z = matA D i z * D.mat i h a b z`. -/
def matA (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) : ℝ :=
  D.psi i z * Real.sqrt (D.dens i z)

@[simp] lemma matA_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    matA D i z = D.psi i z * Real.sqrt (D.dens i z) := rfl

/-- The defining relation of the weight: the localised component is the weight times the chart
matrix. -/
lemma R_eq_matA_mul_mat (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    D.R i h a b z = matA D i z * D.mat i h a b z := rfl

end Work.Diff.STE.Lead
