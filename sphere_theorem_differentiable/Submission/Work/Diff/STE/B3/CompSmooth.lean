import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: smoothness of the localised weights and of the periodised components

`Work.Diff.STE.B3Data.psi i` is the product of the flat cut-off `χ i` with the smooth function
`ζ i ∘ pt i`; it is supported in the `2σ i`-ball, on which `pt i = (extChartAt I (x₀ i)).symm ∘
flatToE` is smooth (the chart target is open and `extChartAt I (x₀ i)⁻¹` is smooth there).  Hence
`ψ i` is `C^∞`, and so is the localised component `R i h a b = ψ i · mat i h a b` whenever the chart
matrix is smooth on the chart target.  Its support lies in the open unit cube, so the periodisation
`Rper i h a b` is `C^∞` and `1`-periodic by `periodization_contDiff_periodic`.

This is the Layer B3 transcription of the B2 sibling `Work.Diff.STE.fill.contDiff_bilPer_of_bump`;
the only new ingredient is the smoothness of the weight `ψ i`.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

/-- `flatToE x₀` is smooth (it is affine). -/
lemma contDiff_flatToE (x₀ : M) : ContDiff ℝ (⊤ : ℕ∞) (flatToE (I := I) x₀) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z) :=
    contDiff_const.add contDiff_id
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun w : Fin (Module.finrank ℝ E) → ℝ =>
      (Module.finBasis ℝ E).equivFun.symm w) :=
    (((Module.finBasis ℝ E).equivFun.symm :
        (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E) :
        (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E).toContinuousLinearMap.contDiff
  exact h2.comp h1

namespace B3Data

variable (D : B3Data (I := I) (M := M) ι₀ g₀)

/-- The parametrisation `z ↦ pt i z = (extChartAt I (x₀ i)).symm (flatToE (x₀ i) z)` is smooth at
every point of the `2σ i`-ball. -/
lemma contMDiffAt_pt (i : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target) :
    ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) I ∞ (D.pt i) z := by
  have h1 : ContMDiffAt 𝓘(ℝ, E) I ∞ ((extChartAt I (D.x₀ i)).symm)
      (flatToE (I := I) (D.x₀ i) z) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) (D.x₀ i)).contMDiffAt
      ((isOpen_extChartAt_target (I := I) (D.x₀ i)).mem_nhds hz)
  have h2 : ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) 𝓘(ℝ, E) ∞
      (flatToE (I := I) (D.x₀ i)) z :=
    contMDiffAt_iff_contDiffAt.mpr ((contDiff_flatToE (I := I) (x₀ := D.x₀ i)).contDiffAt)
  exact h1.comp z h2

/-- **The localised weight is smooth.** -/
theorem psi_contDiff (i : ι₀) : ContDiff ℝ (⊤ : ℕ∞) (D.psi i) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport (D.χ i)
  · have hzt : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
      D.hχtsup i z hz
    have hpt := D.contMDiffAt_pt i hzt
    have hζ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (D.ζ i) (D.pt i z) := (D.hζsm i).contMDiffAt
    have hcomp : ContMDiffAt 𝓘(ℝ, Fin (Module.finrank ℝ E) → ℝ) 𝓘(ℝ, ℝ) ∞
        (fun z => D.ζ i (D.pt i z)) z := hζ.comp z hpt
    have hcomp' : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => D.ζ i (D.pt i z)) z :=
      contMDiffAt_iff_contDiffAt.mp hcomp
    exact ((D.hχsm i).contDiffAt).mul hcomp'
  · have hz' : ∀ᶠ y in 𝓝 z, y ∉ tsupport (D.χ i) :=
      (isClosed_tsupport (D.χ i)).isOpen_compl.mem_nhds hz
    have h0 : D.psi i =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hz'] with y hy
      simp only [psi, image_eq_zero_of_notMem_tsupport hy, zero_mul]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h0

/-- The volume density is smooth and positive on the chart target (this is the statement about
`√det` of the Gram matrix of the coordinate frame, delegated as `Diff/STE/B3/dens_contDiff_pos`;
it is stated as a hypothesis here so that the smoothness of the components does not depend on it). -/
def DensGood (i : ι₀) : Prop :=
  ∀ z : Fin (Module.finrank ℝ E) → ℝ,
    flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target →
      0 < D.dens i z ∧ ContDiffAt ℝ (⊤ : ℕ∞) (D.dens i) z

/-- The square root of the volume density is smooth on the chart target. -/
lemma sqrt_dens_contDiffAt (i : ι₀) (hd : D.DensGood i)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => Real.sqrt (D.dens i z)) z :=
  (Real.contDiffAt_sqrt (hd z hz).1.ne').comp z (hd z hz).2

/-- The localised component is smooth, given smoothness of the chart matrix on the chart target. -/
theorem R_contDiff (i : ι₀) (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (hd : D.DensGood i)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i h a b) (extChartAt I (D.x₀ i)).target) :
    ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport (D.χ i)
  · have hzt : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
      D.hχtsup i z hz
    have hfl : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        D.matChart i h a b (flatToE (I := I) (D.x₀ i) z)) z :=
      (hsm.contDiffAt ((isOpen_extChartAt_target (I := I) (D.x₀ i)).mem_nhds hzt)).comp z
        ((contDiff_flatToE (I := I) (x₀ := D.x₀ i)).contDiffAt)
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (D.psi i) z := (D.psi_contDiff i).contDiffAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => Real.sqrt (D.dens i z)) z :=
      D.sqrt_dens_contDiffAt i hd hzt
    have h3 : ContDiffAt ℝ (⊤ : ℕ∞) (D.mat i h a b) z := by
      simpa only [B3Data.mat_eq] using hfl
    exact (h1.mul h2).mul h3
  · have hz' : ∀ᶠ y in 𝓝 z, y ∉ tsupport (D.χ i) :=
      (isClosed_tsupport (D.χ i)).isOpen_compl.mem_nhds hz
    have h0 : D.R i h a b =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hz'] with y hy
      simp only [R, psi, image_eq_zero_of_notMem_tsupport hy, zero_mul, mul_zero]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h0

/-- The support of the localised component lies in the open unit cube. -/
lemma R_support (i : ι₀) (h : Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E)) :
    Function.support (D.R i h a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
  fun z hz => D.psi_supp i (fun h0 => hz (by simp only [R, h0, zero_mul, mul_zero]))

/-- **The periodised localised component is smooth and `1`-periodic.** -/
theorem Rper_contDiff_periodic (i : ι₀) (h : Bil (I := I) (M := M))
    (a b : Fin (Module.finrank ℝ E)) (hd : D.DensGood i)
    (hsm : ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i h a b) (extChartAt I (D.x₀ i)).target) :
    ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b) ∧ Periodic1 (D.Rper i h a b) := by
  set F : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    fun z => ((D.R i h a b z : ℝ) : ℂ) with hFdef
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    have hh := Complex.ofRealCLM.contDiff.comp (D.R_contDiff i h a b hd hsm)
    have heq : (⇑Complex.ofRealCLM ∘ (D.R i h a b)) = F := by
      rw [hFdef]
      funext z
      exact Complex.ofRealCLM_apply _
    rwa [heq] at hh
  have hFsup : Function.support F ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    exact D.R_support i h a b (by simpa only [hFdef, Function.mem_support, Complex.ofReal_ne_zero]
      using hz)
  have hEq : D.Rper i h a b =
      (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ∑' m : Fin (Module.finrank ℝ E) → ℤ, F (x + iVec m)) := rfl
  obtain ⟨hcd, hper, -⟩ := periodization_contDiff_periodic F hF hFsup
  rw [hEq]
  exact ⟨hcd, hper⟩

end B3Data

end Work.Diff.STE
