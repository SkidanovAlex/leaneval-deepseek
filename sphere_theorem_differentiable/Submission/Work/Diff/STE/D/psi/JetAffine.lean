/-
# Layer D: the joint (coefficient, chart coordinate) jets of the Galerkin family

This module collects the elementary structural facts about the pair of jets

  `W (c, y) = jetPairOf g₀ D ε x₀ c (flatToE x₀ y)`

that the Lipschitz estimate `Work.Diff.STE.D.psi.abs_Ufun_sub_le` needs:

* `jetPairOf_eq_affine` — `W` is *affine* in the coefficients: it is the constant jet pair
  `(chartJetOf g₀.inner x₀ y, chartJetOf g₀.inner x₀ y)` plus the linear combination
  `Σ_z c z • jetDir g₀ D ε x₀ z y`;
* `sum_single_smul` — the evaluation of that linear combination at a basis vector of the
  coefficient space;
* the compact set `Ky D i = closedBall (0) (σ i) ∩ tsupport (χ i)` — the region in which the
  localised weight `ψ i` can be nonzero — with its basic properties (compactness, the chart target
  condition, the identification of the chart coordinate of `pt i y`);
* the smoothness of the individual pieces of the jet pair along `y ↦ flatToE x₀ y`.

The file also records the (few) instances and zero-multiplication lemmas of the jet space that the
elaborator cannot reliably synthesise by itself: they are the canonical ones, restated so that
instance search finds them immediately instead of running into the nested-product instance puzzle.
-/
import Mathlib
import Submission.Work.Diff.STE.D.psi.Core
import Submission.Work.Diff.STE.D.psi.chartJetOf_genMap_affine
import Submission.Work.Diff.STE.D.psi.chartJetOf_jSym_bound
import Submission.Work.Diff.STE.D.psi.contDiffOn_secChartVal_chart
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.CompSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D.psi

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 8000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

/-! ## 0. Instances and zero-multiplication facts for the jet space -/

/-- The space of chart `2`-jets of a matrix-valued function. -/
abbrev Tri (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :=
  Work.Diff.EXT.MatE (E := E) × Work.Diff.STE.DeTurck.LinMat E × Work.Diff.STE.DeTurck.BilMat E

noncomputable instance instModuleJetPair :
    Module ℝ (Work.Diff.STE.deTurck.JetPair (E := E)) := inferInstance

noncomputable instance instNormedAddCommGroupJetPair :
    NormedAddCommGroup (Work.Diff.STE.deTurck.JetPair (E := E)) := inferInstance

noncomputable instance instNormedSpaceJetPair :
    NormedSpace ℝ (Work.Diff.STE.deTurck.JetPair (E := E)) := inferInstance

noncomputable instance instNormedAddCommGroupCLM :
    NormedAddCommGroup (Work.Diff.STE.deTurck.JetPair (E := E) →L[ℝ]
      Work.Diff.EXT.MatE (E := E)) := inferInstance

noncomputable instance instNormedSpaceCLM :
    NormedSpace ℝ (Work.Diff.STE.deTurck.JetPair (E := E) →L[ℝ]
      Work.Diff.EXT.MatE (E := E)) := inferInstance

/-- Scalar multiples of the zero bilinear jet vanish. -/
lemma smul_zero_bil (c : ℝ) : c • (0 : Work.Diff.STE.DeTurck.BilMat (E := E)) = 0 := by
  ext v
  rw [smul_apply, zero_apply]
  exact smul_zero c

/-- Scalar multiples of the zero jet triple vanish. -/
lemma smul_zero_tri (c : ℝ) : c • (0 : Tri (E := E)) = 0 := by
  refine Prod.ext ?_ ?_
  · show c • (0 : Work.Diff.EXT.MatE (E := E)) = 0
    exact smul_zero c
  · refine Prod.ext ?_ ?_
    · show c • (0 : Work.Diff.STE.DeTurck.LinMat (E := E)) = 0
      exact smul_zero c
    · show c • (0 : Work.Diff.STE.DeTurck.BilMat (E := E)) = 0
      exact smul_zero_bil c

/-- Scalar multiples of the zero jet pair vanish. -/
lemma smul_zero_jetPair (c : ℝ) :
    c • (0 : Work.Diff.STE.deTurck.JetPair (E := E)) = 0 := by
  refine Prod.ext ?_ ?_
  · show c • (0 : Tri (E := E)) = 0
    exact smul_zero_tri c
  · show c • (0 : Tri (E := E)) = 0
    exact smul_zero_tri c

/-- The scalar zero acts trivially on the bilinear jets. -/
lemma zero_smul_bil (x : Work.Diff.STE.DeTurck.BilMat (E := E)) : (0 : ℝ) • x = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  refine ContinuousLinearMap.ext fun w => ?_
  funext i j
  simp

/-- The scalar zero acts trivially on the jet triples. -/
lemma zero_smul_tri (x : Tri (E := E)) : (0 : ℝ) • x = 0 := by
  refine Prod.ext ?_ ?_
  · show (0 : ℝ) • x.1 = 0
    exact zero_smul ℝ x.1
  · refine Prod.ext ?_ ?_
    · show (0 : ℝ) • x.2.1 = 0
      exact zero_smul ℝ x.2.1
    · show (0 : ℝ) • x.2.2 = 0
      exact zero_smul_bil x.2.2

noncomputable instance instFintypeJIdx {ι₀ : Type*} [Fintype ι₀] (n : ℕ) (ε : ℝ) :
    Fintype (Work.Diff.STE.B3.JIdx ι₀ n ε) := inferInstance

noncomputable instance instDecidableEqJIdx {ι₀ : Type*} [Fintype ι₀] (n : ℕ) (ε : ℝ) :
    DecidableEq (Work.Diff.STE.B3.JIdx ι₀ n ε) := Classical.decEq _

noncomputable instance instNormedAddCommGroupCS {ι₀ : Type*} [Fintype ι₀] (n : ℕ) (ε : ℝ) :
    NormedAddCommGroup (Work.Diff.STE.B3.JIdx ι₀ n ε → ℝ) := inferInstance

noncomputable instance instNormedSpaceCS {ι₀ : Type*} [Fintype ι₀] (n : ℕ) (ε : ℝ) :
    NormedSpace ℝ (Work.Diff.STE.B3.JIdx ι₀ n ε → ℝ) := inferInstance

noncomputable instance instProperSpaceCS {ι₀ : Type*} [Fintype ι₀] (n : ℕ) (ε : ℝ) :
    ProperSpace (Work.Diff.STE.B3.JIdx ι₀ n ε → ℝ) := inferInstance

noncomputable instance instFintypeCS {ι₀ : Type*} [Fintype ι₀] (n : ℕ) (ε : ℝ) :
    Fintype (Work.Diff.STE.B3.JIdx ι₀ n ε) := inferInstance

/-! ## 1. The affine structure of the jet pair in the coefficients -/

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M} {ε : ℝ}

/-- The first component of the pair of jets is the background chart jet. -/
@[simp] lemma jetPairOf_fst (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c y).1 =
      Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y := rfl

/-- The second component of the pair of jets is the chart jet of `g₀ + genMap D ε c`. -/
@[simp] lemma jetPairOf_snd (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    (Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c y).2 =
      Work.Diff.STE.D.chartJetOf (I := I) (M := M)
        (Work.Diff.STE.D.addSec (I := I) g₀ (Work.Diff.STE.D.genMap (I := I) (M := M) D ε c))
        x₀ y := rfl

/-- The first component of the direction vector `jetDir` vanishes. -/
@[simp] lemma jetDir_fst (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) (y : E) :
    (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z y).1 = 0 := rfl

/-- The second component of the direction vector `jetDir` is the chart jet of the spanning
vector. -/
@[simp] lemma jetDir_snd (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) (y : E) :
    (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z y).2 =
      Work.Diff.STE.D.chartJetOf (I := I) (M := M)
        (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀ y := rfl

/-- **The linear combination of the direction vectors, componentwise.** -/
theorem sum_smul_jetDir (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (y : E) :
    (∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
        c z • Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z y)
      = (0, ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          c z • Work.Diff.STE.D.chartJetOf (I := I) (M := M)
            (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀ y) := by
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
    refine Finset.sum_eq_zero (fun z _ => ?_)
    rw [Prod.smul_fst, jetDir_fst]
    exact smul_zero_tri (E := E) (c z)
  · rw [Prod.snd_sum]
    exact Finset.sum_congr rfl (fun z _ => by rw [Prod.smul_snd, jetDir_snd])

/-- **The pair of spatial `2`-jets is affine in the coefficients**, in the explicit form of the
two components: the first (background) component is independent of `c`, and the second is the
background chart jet plus the linear combination `Σ_z c z • (chart jet of the spanning vector)`. -/
theorem jetPairOf_eq_pair
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c y =
      (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y,
       Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y
        + ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
            c z • Work.Diff.STE.D.chartJetOf (I := I) (M := M)
              (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀ y) := by
  rw [Work.Diff.STE.D.jetPairOf]
  exact congrArg (fun u => (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y, u))
    (Work.Diff.STE.D.psi.chartJetOf_genMap_affine (I := I) (M := M) hg D ε x₀ c hy)

/-- **The pair of spatial `2`-jets is affine in the coefficients**, in the form of the pair of the
background chart jet with the linear combination of the direction vectors. -/
theorem jetPairOf_eq_dir
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c y =
      (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y,
       Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y)
      + ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          c z • Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z y := by
  unfold Work.Diff.STE.D.jetPairOf Work.Diff.STE.D.jetDir
  rw [Work.Diff.STE.D.psi.chartJetOf_genMap_affine (I := I) (M := M) hg D ε x₀ c hy]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_mk, smul_zero_tri,
      Finset.sum_const_zero, add_zero]
  · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_mk, Finset.sum_apply, Pi.smul_apply,
      Pi.zero_apply, smul_zero, zero_add]

/-- **The linear part of the jet pair map**: the (constant) Fréchet derivative of
`c ↦ jetPairOf g₀ D ε x₀ c y` at any coefficient. -/
noncomputable def jetDirLin (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) (y : E) :
    (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →L[ℝ]
      Work.Diff.STE.deTurck.JetPair (E := E) :=
  ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
    (ContinuousLinearMap.proj z).smulRight
      (Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z y)

/-- The linear part computes the sum of the directions. -/
@[simp] lemma jetDirLin_apply (g₀ : Submission.Diff.SMet I M)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M) (y : E)
    (δ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) :
    jetDirLin (I := I) (M := M) g₀ D ε x₀ y δ
      = ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          δ z • Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z y := by
  simp only [jetDirLin, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

/-- **The jet pair is affine in the coefficients**: its Fréchet derivative is the constant linear
part `jetDirLin`. -/
lemma hasFDerivAt_jetPairOf
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) (x₀ : M)
    (c₀ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    HasFDerivAt (fun c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
        Work.Diff.STE.D.jetPairOf (I := I) (M := M) g₀ D ε x₀ c y)
      (jetDirLin (I := I) (M := M) g₀ D ε x₀ y) c₀ := by
  have hconst : HasFDerivAt
      (fun _ : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
        (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y,
         Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀ y))
      (0 : (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →L[ℝ]
        Work.Diff.STE.deTurck.JetPair (E := E)) c₀ :=
    hasFDerivAt_const _ _
  have hlin : HasFDerivAt
      (fun c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
        ∑ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
          c z • Work.Diff.STE.D.jetDir (I := I) (M := M) g₀ D ε x₀ z y)
      (jetDirLin (I := I) (M := M) g₀ D ε x₀ y) c₀ := by
    have h := (jetDirLin (I := I) (M := M) g₀ D ε x₀ y :
      (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) →L[ℝ]
        Work.Diff.STE.deTurck.JetPair (E := E)).hasFDerivAt (x := c₀)
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun c => ?_)
    simp only [jetDirLin_apply]
  have hsum := (hconst.add hlin).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun c =>
      (jetPairOf_eq_dir (I := I) (M := M) hg D x₀ c hy))
  simpa only [zero_add] using hsum

/-- **Evaluation of a finite linear combination of jets at a basis vector** of the coefficient
space. -/
theorem sum_single_smul {ι₀ : Type*} [Fintype ι₀] {ε : ℝ}
    (z' : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε)
    (V : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε →
      Work.Diff.STE.deTurck.JetPair (E := E)) :
    (∑ z, (Pi.single z' (1 : ℝ) : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ)
        z • V z) = V z' := by
  classical
  rw [Finset.sum_eq_single z']
  · rw [Pi.single_eq_same, one_smul]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ z') h

/-! ## 2. The compact region of the localised weight -/

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The region in which the localised weight `ψ i` can be nonzero**: the closed flat ball of
radius `σ i` intersected with the topological support of the cut-off `χ i`. -/
def Ky (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  Metric.closedBall 0 (D.σ i) ∩ tsupport (D.χ i)

/-- The region `Ky D i` is compact. -/
lemma isCompact_Ky (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    IsCompact (Ky (I := I) (M := M) D i) := by
  refine (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i)).of_isClosed_subset
    ?_ Set.inter_subset_left
  exact isClosed_closedBall.inter (isClosed_tsupport (D.χ i))

/-- Membership in `Ky` from the nonvanishing of the localised weight. -/
lemma mem_Ky_of_psi_ne_zero (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) {i : ι₀}
    {y : Fin (Module.finrank ℝ E) → ℝ} (h : D.psi i y ≠ 0) :
    y ∈ Ky (I := I) (M := M) D i := by
  refine ⟨?_, subset_closure (fun h0 => h (by simp only [Work.Diff.STE.B3Data.psi, h0, zero_mul]))⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_lt (Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) (M := M) D h)

/-- On `Ky D i` the chart is genuine. -/
lemma flatToE_mem_target_of_mem_Ky (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) {i : ι₀}
    {y : Fin (Module.finrank ℝ E) → ℝ} (h : y ∈ Ky (I := I) (M := M) D i) :
    Work.Diff.STE.flatToE (I := I) (D.x₀ i) y ∈ (extChartAt I (D.x₀ i)).target :=
  D.hχtsup i y h.2

/-- On `Ky D i` the flat coordinate is bounded by `σ i`. -/
lemma norm_le_sigma_of_mem_Ky (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) {i : ι₀}
    {y : Fin (Module.finrank ℝ E) → ℝ} (h : y ∈ Ky (I := I) (M := M) D i) :
    ‖y‖ ≤ D.σ i := by
  rw [← dist_zero_right, ← Metric.mem_closedBall]
  exact h.1

/-- On `Ky D i` the chart coordinate of `pt i y` is the flat coordinate `y` itself. -/
lemma coord_pt_eq_of_mem_Ky (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) {i : ι₀}
    {y : Fin (Module.finrank ℝ E) → ℝ} (h : y ∈ Ky (I := I) (M := M) D i) :
    Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt i y) = y := by
  have hpt : (extChartAt I (D.x₀ i)) (D.pt i y)
      = Work.Diff.STE.flatToE (I := I) (D.x₀ i) y :=
    (extChartAt I (D.x₀ i)).right_inv (flatToE_mem_target_of_mem_Ky (I := I) (M := M) D h)
  have hL : (Module.finBasis ℝ E).equivFun (Work.Diff.STE.flatToE (I := I) (D.x₀ i) y)
      = (Module.finBasis ℝ E).equivFun ((extChartAt I (D.x₀ i)) (D.x₀ i)) + y := by
    simp only [Work.Diff.STE.flatToE]
    rw [LinearEquiv.apply_symm_apply]
  simp only [Work.Diff.STE.coord, hpt, hL, add_sub_cancel_left]

/-! ## 3. Smoothness along the chart coordinate -/

/-- The set of flat coordinates whose image lies in the chart target is open. -/
lemma isOpen_flatToE_preimage_target (x₀ : M) :
    IsOpen {y : Fin (Module.finrank ℝ E) → ℝ |
      Work.Diff.STE.flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target} :=
  (isOpen_extChartAt_target (I := I) x₀).preimage
    (Work.Diff.STE.contDiff_flatToE (I := I) x₀).continuous

/-- **The background chart jet is smooth along the chart coordinate.** -/
lemma contDiffOn_chartJetOf_inner_flatToE
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner) (x₀ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner x₀
          (Work.Diff.STE.flatToE (I := I) x₀ y))
      {y : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target} :=
  (contDiffOn_chartJetOf (I := I) (M := M) g₀.inner x₀ (hg x₀)).comp
    (Work.Diff.STE.contDiff_flatToE (I := I) x₀).contDiffOn (fun _ hy => hy)

/-- **The chart jet of a spanning vector is smooth along the chart coordinate.** -/
lemma contDiffOn_chartJetOf_jSym_flatToE
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (x₀ : M)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.D.chartJetOf (I := I) (M := M)
          (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀
          (Work.Diff.STE.flatToE (I := I) x₀ y))
      {y : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) x₀ y ∈ (extChartAt I x₀).target} :=
  (contDiffOn_chartJetOf (I := I) (M := M)
      (Work.Diff.STE.D.jSym (I := I) (M := M) D ε z) x₀
      (jSym_chartData (I := I) (M := M) D ε z x₀)).comp
    (Work.Diff.STE.contDiff_flatToE (I := I) x₀).contDiffOn (fun _ hy => hy)

end Work.Diff.STE.D.psi
