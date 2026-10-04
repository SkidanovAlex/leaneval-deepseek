import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.Lead.fderiv_flatAffine_pdR
import Submission.Work.Diff.STE.Lead.fderiv2_flatAffine_pdR
import Submission.Work.Diff.Calc.fderiv2_entry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The jet of `Gf` in flat coordinates

`Work.Diff.STE.B3.transport_jet_data` identifies the spatial `2`-jet of the chart matrix
`Work.Diff.STE.B3.Gf D h j z = chartMatOf h (D.x₀ j) (yf D j z)` of a section, *read in the flat
coordinates* `z`, with the coordinate partial derivatives of the entries:
`(chartJetOf h (D.x₀ j) (yf D j z)).1 i k = Gf … i k`,
`(…).2.1 (bB c) i k = pdR c (Gf … · i k) z` and
`(…).2.2 (bB c) (bB d) i k = pdR c (pdR d (Gf … · i k)) z`.

The mathematical content is the chain rule for the affine flat coordinate map
`flatToE x₀ = flatAffine c₀` (the identification `Fin (finrank ℝ E) → ℝ ≃ E` through the
canonical basis `bB = finBasis`), together with the extraction of the `(i,k)`-components of the
`MatE`-valued Fréchet derivatives.  The two ingredients are
`Work.Diff.STE.Lead.fderiv_flatAffine_pdR` (first order),
`Work.Diff.STE.Lead.fderiv2_flatAffine_pdR` (second order, in the *swapped* argument order,
converted here with the symmetry of the second derivative), and the elementary component lemma
`fderiv2_entry_aux` proved below.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-! ## Component extraction for Fréchet derivatives -/

private lemma fderiv_apply_entry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E → (ι → F)) {y : E} (hA : DifferentiableAt ℝ A y) (i : ι) (v : E) :
    fderiv ℝ (fun x : E => A x i) y v = (fderiv ℝ A y v) i := by
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i).hasFDerivAt.comp y
    hA.hasFDerivAt
  have h' : (fun x : E => A x i)
      = ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i) ∘ A) := rfl
  rw [h', h.fderiv]
  rfl

private lemma differentiableAt_entry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E → (ι → F)) {y : E} (hA : DifferentiableAt ℝ A y) (i : ι) :
    DifferentiableAt ℝ (fun x : E => A x i) y :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i).hasFDerivAt).comp y
    hA.hasFDerivAt).differentiableAt

private lemma contDiffAt_entry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : E → (ι → F)} {y : E} {n : WithTop ℕ∞} (hA : ContDiffAt ℝ n A y) (i : ι) :
    ContDiffAt ℝ n (fun x : E => A x i) y :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => F) i).contDiff.contDiffAt).comp y hA)

private lemma fderiv_entry2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    (A : E → (Fin n → Fin n → ℝ)) {y : E} (hA : DifferentiableAt ℝ A y) (i k : Fin n) (v : E) :
    fderiv ℝ (fun x : E => A x i k) y v = (fderiv ℝ A y v) i k := by
  have h1 := fderiv_apply_entry A hA i v
  have h2 := fderiv_apply_entry (fun x : E => A x i) (differentiableAt_entry A hA i) k v
  rw [h2, h1]

private lemma contDiffAt_entry2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {A : E → (Fin n → Fin n → ℝ)} {y : E} {m : WithTop ℕ∞} (hA : ContDiffAt ℝ m A y)
    (i k : Fin n) :
    ContDiffAt ℝ m (fun x : E => A x i k) y :=
  contDiffAt_entry (contDiffAt_entry hA i) k

/-! ## The target -/

theorem transport_jet_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    (∀ (i k : Fin (Module.finrank ℝ E)),
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).1 i k
          = Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k) ∧
    (∀ (c : Fin (Module.finrank ℝ E)) (i k : Fin (Module.finrank ℝ E)),
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.1 (Work.Diff.EXT.bB c) i k
          = Work.Diff.STE.pdR c (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z) ∧
    (∀ (c d : Fin (Module.finrank ℝ E)) (i k : Fin (Module.finrank ℝ E)),
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) h (D.x₀ j)
          (Work.Diff.STE.B3.yf (I := I) (M := M) D j z)).2.2 (Work.Diff.EXT.bB c)
            (Work.Diff.EXT.bB d) i k
          = Work.Diff.STE.pdR c
              (Work.Diff.STE.pdR d (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z) := by
  classical
  -- the flat coordinate map of the chart at `x₀ j`, as an affine map of the model space
  let c₀ : Fin (Module.finrank ℝ E) → ℝ :=
    (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ j)) (D.x₀ j))
  have hy : Work.Diff.STE.B3.yf (I := I) (M := M) D j z
      ∈ (extChartAt I (D.x₀ j)).target := D.htarget j z hz
  have hA : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y)
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) :=
    (hsmooth (D.x₀ j)).contDiffAt ((isOpen_extChartAt_target (I := I) (D.x₀ j)).mem_nhds hy)
  have hA2 : ContDiffAt ℝ 2
      (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y)
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) := hA.of_le (by norm_num)
  have hdA : DifferentiableAt ℝ
      (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y)
      (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) := hA2.differentiableAt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · -- the value of the jet
    intro i k
    show Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j)
        (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) i k
      = Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k
    rfl
  · -- the first derivative
    intro c i k
    have hF : ContDiffAt ℝ 2
        (fun x : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) x i k)
        (Work.Diff.STE.Lead.flatAffine (E := E) c₀ z) := contDiffAt_entry2 hA2 i k
    show (fderiv ℝ
        (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y)
        (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) (Work.Diff.EXT.bB (E := E) c)) i k
      = Work.Diff.STE.pdR c (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z
    rw [← fderiv_entry2
      (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y) hdA i k
      (Work.Diff.EXT.bB (E := E) c)]
    change fderiv ℝ
        (fun x : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) x i k)
        (Work.Diff.STE.Lead.flatAffine (E := E) c₀ z) (Work.Diff.EXT.bB (E := E) c)
      = Work.Diff.STE.pdR c (fun w =>
          (fun x : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) x i k)
            (Work.Diff.STE.Lead.flatAffine (E := E) c₀ w)) z
    rw [Work.Diff.STE.Lead.fderiv_flatAffine_pdR (E := E) c₀ hF c]
  · -- the second derivative
    intro c d i k
    have hF : ContDiffAt ℝ 2
        (fun x : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) x i k)
        (Work.Diff.STE.Lead.flatAffine (E := E) c₀ z) := contDiffAt_entry2 hA2 i k
    have hsymm : IsSymmSndFDerivAt ℝ
        (fun x : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) x i k)
        (Work.Diff.STE.Lead.flatAffine (E := E) c₀ z) :=
      hF.isSymmSndFDerivAt (by norm_num)
    show ((fderiv ℝ (fun y : E => fderiv ℝ
        (fun y' : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y') y)
        (Work.Diff.STE.B3.yf (I := I) (M := M) D j z) (Work.Diff.EXT.bB (E := E) c))
        (Work.Diff.EXT.bB (E := E) d)) i k
      = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
          (fun y => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z
    rw [Work.Diff.Calc.fderiv2_entry
      (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y) i k
      (Work.Diff.EXT.bB (E := E) c) (Work.Diff.EXT.bB (E := E) d) hA2]
    change (fderiv ℝ (fun y' : E => fderiv ℝ
        (fun y'' : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) y'' i k) y')
        (Work.Diff.STE.Lead.flatAffine (E := E) c₀ z) (Work.Diff.EXT.bB (E := E) c))
        (Work.Diff.EXT.bB (E := E) d)
      = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun w =>
          (fun x : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) h (D.x₀ j) x i k)
            (Work.Diff.STE.Lead.flatAffine (E := E) c₀ w))) z
    rw [hsymm.eq (Work.Diff.EXT.bB (E := E) c) (Work.Diff.EXT.bB (E := E) d)]
    rw [Work.Diff.STE.Lead.fderiv2_flatAffine_pdR (E := E) c₀ hF d c]

end Work.Diff.STE.B3
