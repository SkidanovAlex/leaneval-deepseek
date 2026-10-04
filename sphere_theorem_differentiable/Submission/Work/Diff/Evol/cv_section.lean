import Mathlib
import Submission.Work.Diff.Evol.cv_prelim
import Submission.Work.Diff.EXT.kosDefs
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.ChartConnection
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of a section from the smoothness of its pairings

If a section `A` of the tangent bundle has `C^∞` pairings `y ↦ g(A y, Z y)` with every smooth
field `Z`, then `A` is `C^∞`: in the coordinate frame of the chart at `x` its coordinates are
`Γ⁻¹` times the pairing vector, and both factors are smooth.

Main results:

* `cv_metric_pairing_at` — smoothness of a metric pairing of two smooth fields;
* `cv_jointSmooth_const` — a constant family of metrics is `JointSmooth`;
* `cv_chartFrame_gram_det_ne_zero` — the Gram matrix of the chart frame at `x` is invertible;
* `cv_eq_sum_frame_of_pairings` — the reconstruction of `A` from its pairings;
* `cv_section_smooth_of_pairings` — the smoothness of `A`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

/-- A constant family of metrics is jointly smooth. -/
theorem cv_jointSmooth_const (g : SMet I M) :
    Submission.Diff.JointSmooth (fun _ : ℝ ↦ g) Set.univ := by
  rw [Submission.Diff.JointSmooth, Set.univ_prod_univ, contMDiffOn_univ]
  have h1 : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun m : M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) m (g.inner m)) :=
    g.contMDiff
  exact h1.comp contMDiff_snd

/-- **Smoothness of a metric pairing of two smooth sections.** -/
theorem cv_metric_pairing_at {g : SMet I M} {Y Z : Π y : M, TangentSpace I y}
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    CMDiffAt ∞ (fun y : M ↦ g.inner y (Y y) (Z y)) x := by
  have hJ := Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M)
    (G := fun _ : ℝ ↦ g) (J := Set.univ) isOpen_univ (cv_jointSmooth_const (I := I) (M := M) g)
    (t₀ := 0) trivial (x := x) hY.contMDiffAt hZ.contMDiffAt
  exact cv_slice_of_joint (I := I) (M := M) hJ

/-- **The Gram matrix of the chart frame at the base point is invertible.** -/
theorem cv_chartFrame_gram_det_ne_zero (g : SMet I M) (x : M) :
    (Matrix.of (fun i j : Fin (Module.finrank ℝ E) ↦
      g.inner x (Work.Diff.GE.cFrame (I := I) x i x)
        (Work.Diff.GE.cFrame (I := I) x j x))).det ≠ 0 := by
  classical
  haveI : Bundle.Trivialization.IsLinear ℝ (trivializationAt E (TangentSpace I) x) := inferInstance
  set L : E ≃ₗ[ℝ] TangentSpace I x :=
    (Bundle.Trivialization.linearEquivAt ℝ (trivializationAt E (TangentSpace I) x) x
      (mem_baseSet_trivializationAt E (TangentSpace I) x)).symm with hLdef
  have hL : ∀ v : E, L v = Submission.Geodesic.frameVector (I := I) x x v := by
    intro v
    rw [hLdef, Bundle.Trivialization.linearEquivAt_symm_apply]
    exact (Bundle.Trivialization.symmL_apply (R := ℝ) (trivializationAt E (TangentSpace I) x)
      (mem_baseSet_trivializationAt E (TangentSpace I) x) v).symm
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    (Module.finBasis ℝ E).map L with hbdef
  have hb : ∀ i, b i = Work.Diff.GE.cFrame (I := I) x i x := by
    intro i
    show ((Module.finBasis ℝ E).map L) i = _
    rw [Module.Basis.map_apply, hL]
    rfl
  set B : LinearMap.BilinForm ℝ (TangentSpace I x) :=
    LinearMap.mk₂ ℝ (fun u v : TangentSpace I x ↦ g.inner x u v)
      (fun u v w ↦ by simp) (fun c u v ↦ by simp) (fun u v w ↦ by simp) (fun c u v ↦ by simp)
    with hBdef
  have hBapp : ∀ u v : TangentSpace I x, B u v = g.inner x u v := fun u v => rfl
  have hnd : B.Nondegenerate := by
    constructor
    · intro v hv
      by_contra hne
      have h0 : B v v = 0 := hv v
      rw [hBapp] at h0
      exact absurd h0 (ne_of_gt (g.pos x v hne))
    · intro v hv
      by_contra hne
      have h0 : B v v = 0 := hv v
      rw [hBapp] at h0
      exact absurd h0 (ne_of_gt (g.pos x v hne))
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd
  have hmat : Matrix.of (fun i j : Fin (Module.finrank ℝ E) ↦
        g.inner x (Work.Diff.GE.cFrame (I := I) x i x) (Work.Diff.GE.cFrame (I := I) x j x))
      = LinearMap.BilinForm.toMatrix b B := by
    ext i j
    rw [Matrix.of_apply, LinearMap.BilinForm.toMatrix_apply, hBapp, ← hb i, ← hb j]
  rwa [hmat]

/-- **Reconstruction of a section from its pairings with smooth fields.**  If all pairings of `A`
with globally smooth fields are smooth at `x`, then near `x` the section is a finite combination of
the coordinate frame of the chart at `x` with smooth coefficients. -/
theorem cv_eq_sum_frame_of_pairings {g : SMet I M} {A : Π y : M, TangentSpace I y} {x : M}
    (h : ∀ Z : Π y : M, TangentSpace I y, CMDiff ∞ (T% Z) →
        CMDiffAt ∞ (fun y : M ↦ g.inner y (A y) (Z y)) x) :
    ∃ (ψ : Fin (Module.finrank ℝ E) → M → ℝ),
      (∀ k, CMDiffAt ∞ (ψ k) x) ∧
      (A =ᶠ[𝓝 x] fun y : M ↦ ∑ k, ψ k y • Work.Diff.GE.cFrame (I := I) x k y) := by
  classical
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) := inferInstance
  -- the pairings with the coordinate frame
  have hpair : ∀ k, CMDiffAt ∞
      (fun y : M ↦ g.inner y (A y) (Work.Diff.GE.cFrame (I := I) x k y)) x := by
    intro k
    obtain ⟨S, hSsm, hSeq⟩ :=
      Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection
        (I := I) (M := M) x (Work.Diff.GE.cBasis (E := E) k) (mem_chart_source H x)
    refine (h S hSsm).congr_of_eventuallyEq ?_
    filter_upwards [hSeq] with y hy
    rw [hy]
    rfl
  -- the Gram matrix of the coordinate frame
  set Γ : M → (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
    fun y i j ↦ g.inner y (Work.Diff.GE.cFrame (I := I) x i y)
      (Work.Diff.GE.cFrame (I := I) x j y) with hΓdef
  have hΓentry : ∀ i j, CMDiffAt ∞ (fun y : M ↦ Γ y i j) x := by
    intro i j
    obtain ⟨Si, hSism, hSiseq⟩ :=
      Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection
        (I := I) (M := M) x (Work.Diff.GE.cBasis (E := E) i) (mem_chart_source H x)
    obtain ⟨Sj, hSjsm, hSjseq⟩ :=
      Submission.ChartConnection.exists_contMDiff_section_eventuallyEq_frameSection
        (I := I) (M := M) x (Work.Diff.GE.cBasis (E := E) j) (mem_chart_source H x)
    have h3 : CMDiffAt ∞ (fun y : M ↦ g.inner y (Si y) (Sj y)) x :=
      cv_metric_pairing_at (I := I) (M := M) hSism hSjsm x
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hSiseq, hSjseq] with y hyi hyj
    simp only [hΓdef, Work.Diff.GE.cFrame, hyi, hyj]
  have hΓsm : ContMDiffAt (I := I)
      (I' := 𝓘(ℝ, Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) (n := ∞) (f := Γ) (x := x) :=
    contMDiffAt_pi_space.2 (fun i ↦ contMDiffAt_pi_space.2 (fun j ↦ hΓentry i j))
  have hdet : (Matrix.of (Γ x)).det ≠ 0 := by
    have h0 := cv_chartFrame_gram_det_ne_zero (I := I) (M := M) g x
    rw [hΓdef]
    exact h0
  have hinv : ∀ k j, CMDiffAt ∞ (fun y : M ↦ (Matrix.of (Γ y))⁻¹ k j) x := by
    intro k j
    have h1 : ContDiffAt ℝ ∞ (fun A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ ↦
        fun i l ↦ (Matrix.of A)⁻¹ i l) (Γ x) :=
      Work.Diff.EXT.contDiffAt_matrix_inv_pi (M := Γ x) hdet
    have h2 : ContMDiffAt (I := I)
        (I' := 𝓘(ℝ, Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) (n := ∞)
        (f := fun y : M ↦ fun i l ↦ (Matrix.of (Γ y))⁻¹ i l) (x := x) :=
      h1.comp_contMDiffAt hΓsm
    exact contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp h2 k) j
  refine ⟨fun k y ↦ ∑ j, (Matrix.of (Γ y))⁻¹ k j *
    g.inner y (A y) (Work.Diff.GE.cFrame (I := I) x j y), ?_, ?_⟩
  · intro k
    refine ContMDiffAt.sum (t := Finset.univ) (f := fun j y ↦ (Matrix.of (Γ y))⁻¹ k j *
      g.inner y (A y) (Work.Diff.GE.cFrame (I := I) x j y)) (fun j _ ↦ ?_)
    exact (hinv k j).mul (hpair j)
  · have hchart : ∀ᶠ y in 𝓝 x, y ∈ (chartAt H x).source :=
      (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    filter_upwards [hchart] with y hy
    have hpt := Work.Diff.EXT.eq_sum_frameVector_of_pairing (g := g) (x₀ := x) hy (A y)
    conv_lhs => rw [hpt]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    simp only [Matrix.mulVec, dotProduct, ← Work.Diff.GE.cFrame_apply (I := I), hΓdef]
    try rfl

/-- **A section with smooth pairings with all smooth fields is smooth.** -/
theorem cv_section_smooth_of_pairings {g : SMet I M} {A : Π y : M, TangentSpace I y} {x : M}
    (h : ∀ Z : Π y : M, TangentSpace I y, CMDiff ∞ (T% Z) →
        CMDiffAt ∞ (fun y : M ↦ g.inner y (A y) (Z y)) x) :
    CMDiffAt ∞ (T% A) x := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) := inferInstance
  obtain ⟨ψ, hψsm, heq⟩ := cv_eq_sum_frame_of_pairings (I := I) (M := M) h
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
      ContMDiffAt I I.tangent ∞ (T% (fun y : M ↦ ψ k y • Work.Diff.GE.cFrame (I := I) x k y)) x := by
    intro k _
    exact (hψsm k).smul_section (Work.Diff.EXT.smoothFieldAt_cFrame (I := I) (M := M) x k)
  have hsum : ContMDiffAt I I.tangent ∞
      (T% (fun y : M ↦ ∑ k, ψ k y • Work.Diff.GE.cFrame (I := I) x k y)) x := by
    have h := ContMDiffAt.sum_section
      (t := fun k : Fin (Module.finrank ℝ E) ↦ fun y : M ↦ ψ k y • Work.Diff.GE.cFrame (I := I) x k y)
      (s := Finset.univ) hterm
    simpa only [Finset.sum_apply] using h
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [heq] with y hy
  simp only [hy]
  try rfl

end Work.Diff.Evol
