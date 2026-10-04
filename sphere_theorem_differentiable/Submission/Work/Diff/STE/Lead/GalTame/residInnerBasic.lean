import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.residGn.BoxDefs
import Submission.Work.Diff.STE.B3.tmA_props
import Submission.Work.Diff.STE.B3.tmPer_eq_self
import Submission.Work.Diff.STE.B3.mat_jet_bound_global
import Submission.Work.Diff.STE.B3.jet_bound_of_tsupport
import Submission.Work.Diff.STE.B3.Mf_sandwich

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `residInnerBasic`: the basic properties of the two inner components of the residual

The state at which the outer function of the sharp residual estimate is evaluated is
`(z, Mper D h j z, Nper D h j z)`, where

* `Mper D h j z p q = ∑' k, boxChi D j (z + k) · mat j h p q (z + k)` is the **periodisation of the
  cut-off chart matrix**, and
* `Nper D h j z p q r = ∑' k, ∂_r (boxChi D j · mat j h p q) (z + k)` is the periodisation of its
  first jet.

This file proves `Work.Diff.STE.Lead.GalTame.residInnerBasic`, that is: there is a constant `B ≥ 0`,
depending only on `D`, `j`, `lam`, `K`, such that for **every** section `h` with smooth chart data,
symmetric, with quadratic form sandwiched between `lam * g₀` and `K * g₀` and with a jet bound `K` on
the partial derivatives of its chart matrices on the closed `2σ`-balls:

* `Mper` and `Nper` are globally `C^∞`,
* `Mper` and `Nper` are `1`-periodic in every coordinate,
* `|Mper|` and `|Nper|` are everywhere bounded by `B`,
* on the open `σ_j`-ball `Mper` coincides with the chart matrix `D.mat j h` and `Nper` with its
  first jet `pdR r (D.mat j h)`.

The proof is an assembly of already proved ingredients:

* `Work.Diff.STE.B3.contDiff_tmPer` / `periodic_tmPer`: the real periodisation of a smooth function
  supported in the open unit cube is smooth and `1`-periodic (via the complex periodisation of
  `Work.Diff.STE.periodization_contDiff_periodic`);
* `Work.Diff.STE.B3.abs_tmPer_le`: at most one lattice translate contributes, so the periodisation is
  bounded by the pointwise bound of the summand;
* `Work.Diff.STE.B3.tmPer_eq_self`: on the fundamental cube the periodisation is the function
  itself;
* `Work.Diff.STE.B3.jet_bound_of_tsupport`: a cut-off with compact support has uniformly bounded
  partial derivatives (this supplies the constant `C` on `∂ (boxChi)`);
* `Work.Diff.STE.B3.Mf_sandwich`: for a **symmetric** section sandwiched between `lam * g₀` and
  `K * g₀`, the chart matrix of `h` obeys the entrywise bound `|D.mat i h c d z| ≤ K` on the closed
  `2σ_i`-ball.  This is the only place where the symmetry hypothesis `hsym` is used — without it the
  statement is *false* (a quadratic-form sandwich cannot bound the antisymmetric part of a bilinear
  form; e.g. on `ℝ²`, `B_c(u,v) = ⟪u,v⟫ + c (u₁v₂ - u₂v₁)` has `B_c(v,v) = ‖v‖²` for all `c` while
  `B_c(e₁,e₂) = c`), and the call sites in `ResidGn` pass `hsym` exactly for this reason;
* `Work.Diff.STE.B3.pdR_mul_eq`: the product rule for the partial derivative `pdR`.

The final bound is `B = K * (1 + C)` with `C` the uniform bound on `|∂ (boxChi D j)|`.
-/

namespace Work.Diff.STE.Lead.GalTame

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

noncomputable section

/-! ## 0. The `tmPer` dictionary for `Mper` and `Nper` -/

/-- The real periodisation `tmPer` is the plain translate sum (the complexification and the real
part are cosmetic). -/
lemma tmPer_eq_tsum {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) :
    Work.Diff.STE.B3.tmPer f z = ∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m) := by
  rw [Work.Diff.STE.B3.tmPer]
  rw [← Complex.ofReal_tsum (fun m : Fin n → ℤ => f (z + Work.Diff.STE.iVec m))]
  exact Complex.ofReal_re _

/-- `Mper` is the real periodisation of the cut-off chart matrix. -/
lemma Mper_eq_tmPer_apply
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (j : ι₀) (p q : Idx) (z : Idx → ℝ) :
    ResidGn.Mper (I := I) (M := M) D h j z p q
      = Work.Diff.STE.B3.tmPer (fun w : Idx → ℝ => ResidGn.boxChi (I := I) (M := M) D j w
          * D.mat j h p q w) z := by
  rw [tmPer_eq_tsum]
  rfl

/-- `Nper` is the real periodisation of the first jet of the cut-off chart matrix. -/
lemma Nper_eq_tmPer_apply
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (j : ι₀) (p q r : Idx) (z : Idx → ℝ) :
    ResidGn.Nper (I := I) (M := M) D h j z p q r
      = Work.Diff.STE.B3.tmPer (fun w : Idx → ℝ => Work.Diff.STE.pdR r
          (fun y : Idx → ℝ => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) w) z := by
  rw [tmPer_eq_tsum]
  rfl

/-! ## 1. Smoothness and support of the cut-off chart matrix -/

/-- The cut-off chart matrix is globally `C^∞`: its chart matrix is smooth at every point of the
closed `2σ_j`-ball (`Work.Diff.STE.B3.mat_contDiffAt_of_chartData`), and off the topological
support of the box cut-off the product vanishes identically on a neighbourhood. -/
lemma contDiff_boxChi_mul_mat
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀) (p q : Idx) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Idx → ℝ => ResidGn.boxChi (I := I) (M := M) D j z * D.mat j h p q z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport (ResidGn.boxChi (I := I) (M := M) D j)
  · have hzle : ‖z‖ ≤ 2 * D.σ j := by
      have h' : z ∈ Metric.closedBall (0 : Idx → ℝ) (2 * D.σ j) := by
        rw [← ResidGn.boxChi_tsupport (I := I) (M := M) D j]
        exact hz
      rwa [Metric.mem_closedBall, dist_zero_right] at h'
    exact ((ResidGn.boxChi_contDiff (I := I) (M := M) D j).contDiffAt).mul
      (Work.Diff.STE.B3.mat_contDiffAt_of_chartData D h hsm j p q z (D.htarget j z hzle))
  · have hnear : ∀ᶠ y in nhds z, y ∉ tsupport (ResidGn.boxChi (I := I) (M := M) D j) :=
      (isClosed_tsupport _).isOpen_compl.mem_nhds hz
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

/-- The topological support of the cut-off chart matrix is contained in the ball of radius `1/2`. -/
lemma tsupport_boxChi_mul_mat_subset_ball
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (j : ι₀) (p q : Idx) :
    tsupport (fun z : Idx → ℝ => ResidGn.boxChi (I := I) (M := M) D j z * D.mat j h p q z)
      ⊆ Metric.ball (0 : Idx → ℝ) (1 / 2 : ℝ) := by
  intro z hz
  have h1 : z ∈ tsupport (ResidGn.boxChi (I := I) (M := M) D j) := tsupport_mul_subset_left hz
  rw [ResidGn.boxChi_tsupport (I := I) (M := M) D j, Metric.mem_closedBall,
    dist_zero_right] at h1
  rw [Metric.mem_ball, dist_zero_right]
  have h3 : 2 * D.σ j ≤ 1 / 4 := D.hσ2 j
  linarith

/-- The topological support of the cut-off chart matrix lies in the open unit cube. -/
lemma tsupport_boxChi_mul_mat_subset_cube
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (j : ι₀) (p q : Idx) :
    tsupport (fun z : Idx → ℝ =>
        ResidGn.boxChi (I := I) (M := M) D j z * D.mat j h p q z)
      ⊆ Set.pi Set.univ (fun _ : Idx => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
  fun z hz => Work.Diff.STE.B3.ball_subset_cube (le_refl (1 / 2 : ℝ))
    (tsupport_boxChi_mul_mat_subset_ball D h j p q hz)

/-- The support of the cut-off chart matrix lies in the open unit cube. -/
lemma support_boxChi_mul_mat_subset_cube
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (j : ι₀) (p q : Idx) :
    Function.support (fun z : Idx → ℝ =>
        ResidGn.boxChi (I := I) (M := M) D j z * D.mat j h p q z)
      ⊆ Set.pi Set.univ (fun _ : Idx => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
  fun z hz => tsupport_boxChi_mul_mat_subset_cube D h j p q (subset_tsupport _ hz)

/-- The support of a partial derivative is contained in the topological support of the function:
off `tsupport g` the function vanishes on a neighbourhood, hence so does its derivative. -/
lemma support_pdR_subset_tsupport {n : ℕ} {g : (Fin n → ℝ) → ℝ} (r : Fin n) :
    Function.support (fun w : Fin n → ℝ => Work.Diff.STE.pdR r g w) ⊆ tsupport g := by
  intro w hw
  by_contra hw'
  have h0 : g =ᶠ[nhds w] (fun _ : Fin n → ℝ => (0 : ℝ)) :=
    notMem_tsupport_iff_eventuallyEq.mp hw'
  have hz : Work.Diff.STE.pdR r g w = 0 := by
    rw [Work.Diff.STE.pdR, h0.fderiv_eq]
    simp
  exact hw hz

/-- The support of the first jet of the cut-off chart matrix lies in the open unit cube. -/
lemma support_pdR_boxChi_mul_mat_subset_cube
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (j : ι₀) (p q r : Idx) :
    Function.support (fun w : Idx → ℝ => Work.Diff.STE.pdR r
        (fun y : Idx → ℝ => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) w)
      ⊆ Set.pi Set.univ (fun _ : Idx => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
  fun w hw => tsupport_boxChi_mul_mat_subset_cube D h j p q
    (support_pdR_subset_tsupport r hw)

/-- The first jet of the cut-off chart matrix is globally `C^∞`. -/
lemma contDiff_pdR_boxChi_mul_mat
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀) (p q r : Idx) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : Idx → ℝ => Work.Diff.STE.pdR r
        (fun y : Idx → ℝ => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) w) := by
  have hg := contDiff_boxChi_mul_mat (I := I) (M := M) D h hsm j p q
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun y : Idx → ℝ =>
      ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y)) :=
    hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun w : Idx → ℝ => fderiv ℝ
      (fun y : Idx → ℝ => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) w
        (Pi.single r (1 : ℝ))) :=
    hfd.clm_apply contDiff_const
  simpa only [Work.Diff.STE.pdR] using h1

/-! ## 2. Smoothness and periodicity of `Mper` and `Nper` -/

lemma Mper_contDiff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀) (p q : Idx) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Idx → ℝ => ResidGn.Mper (I := I) (M := M) D h j z p q) := by
  have hper := Work.Diff.STE.B3.contDiff_tmPer
    (contDiff_boxChi_mul_mat (I := I) (M := M) D h hsm j p q)
    (support_boxChi_mul_mat_subset_cube (I := I) (M := M) D h j p q)
  rwa [← funext fun z => Mper_eq_tmPer_apply (I := I) (M := M) D h j p q z] at hper

lemma Nper_contDiff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀) (p q r : Idx) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Idx → ℝ => ResidGn.Nper (I := I) (M := M) D h j z p q r) := by
  have hper := Work.Diff.STE.B3.contDiff_tmPer
    (contDiff_pdR_boxChi_mul_mat (I := I) (M := M) D h hsm j p q r)
    (support_pdR_boxChi_mul_mat_subset_cube (I := I) (M := M) D h j p q r)
  rwa [← funext fun z => Nper_eq_tmPer_apply (I := I) (M := M) D h j p q r z] at hper

lemma Mper_periodic (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀) (p q : Idx) :
    Work.Diff.STE.Periodic1 (fun z : Idx → ℝ => ResidGn.Mper (I := I) (M := M) D h j z p q) := by
  have hper := Work.Diff.STE.B3.periodic_tmPer
    (contDiff_boxChi_mul_mat (I := I) (M := M) D h hsm j p q)
    (support_boxChi_mul_mat_subset_cube (I := I) (M := M) D h j p q)
  rwa [← funext fun z => Mper_eq_tmPer_apply (I := I) (M := M) D h j p q z] at hper

lemma Nper_periodic (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀) (p q r : Idx) :
    Work.Diff.STE.Periodic1 (fun z : Idx → ℝ => ResidGn.Nper (I := I) (M := M) D h j z p q r) := by
  have hper := Work.Diff.STE.B3.periodic_tmPer
    (contDiff_pdR_boxChi_mul_mat (I := I) (M := M) D h hsm j p q r)
    (support_pdR_boxChi_mul_mat_subset_cube (I := I) (M := M) D h j p q r)
  rwa [← funext fun z => Nper_eq_tmPer_apply (I := I) (M := M) D h j p q r z] at hper

/-! ## 3. The sup bounds -/

/-- The box cut-off has bounded first partial derivatives, uniformly in the direction: a constant
depending only on `D` and `j`. -/
lemma exists_pdR_boxChi_bound (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Idx → ℝ) (r : Idx),
      |Work.Diff.STE.pdR r (ResidGn.boxChi (I := I) (M := M) D j) w| ≤ C := by
  obtain ⟨M, hM0, -, hM⟩ := Work.Diff.STE.B3.jet_bound_of_tsupport (N := 1)
    (ResidGn.boxChi (I := I) (M := M) D j) (2 * D.σ j)
    (ResidGn.boxChi_contDiff (I := I) (M := M) D j)
    (le_of_eq (ResidGn.boxChi_tsupport (I := I) (M := M) D j))
  refine ⟨M, hM0, fun w r => ?_⟩
  simpa only [Work.Diff.STE.pdRVec, Work.Diff.STE.pdRList, List.ofFn_succ, List.ofFn_zero,
    List.foldr_cons, List.foldr_nil] using hM 1 le_rfl (fun _ : Fin 1 => r) w

/-- The box cut-off takes values in `[0,1]`. -/
lemma abs_boxChi_le_one (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (w : Idx → ℝ) : |ResidGn.boxChi (I := I) (M := M) D j w| ≤ 1 := by
  have h0 : 0 ≤ ResidGn.boxChi (I := I) (M := M) D j w :=
    (ResidGn.boxChiBump (I := I) (M := M) D j).nonneg
  rw [abs_of_nonneg h0]
  exact ContDiffBump.le_one _

/-- **The `Mper` bound**: on the closed `2σ_j`-ball `Mf_sandwich` bounds the chart matrix by `K`, and
at most one lattice translate of the cut-off can contribute. -/
lemma Mper_abs_le (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
    (p q : Idx) (z : Idx → ℝ) :
    |ResidGn.Mper (I := I) (M := M) D h j z p q| ≤ K := by
  rw [Mper_eq_tmPer_apply (I := I) (M := M) D h j p q z]
  refine Work.Diff.STE.B3.abs_tmPer_le (R := 2 * D.σ j) (B := K) ?_ ?_ ?_ z
  · linarith [D.hσ2 j]
  · intro w hw
    exact ResidGn.boxChi_support (I := I) (M := M) D j
      (fun h0 => (Function.mem_support.mp hw) (by rw [h0, zero_mul]))
  · intro w
    by_cases h0 : ResidGn.boxChi (I := I) (M := M) D j w = 0
    · rw [h0, zero_mul, abs_zero]
      exact hK.le
    · have hz : ‖w‖ ≤ 2 * D.σ j := by
        have h1 := ResidGn.boxChi_support (I := I) (M := M) D j h0
        rw [Metric.mem_ball, dist_zero_right] at h1
        exact le_of_lt h1
      have hMf := (Work.Diff.STE.B3.Mf_sandwich D j lam K hlam hK h hsym hell hub w hz).2.2.1 p q
      calc |ResidGn.boxChi (I := I) (M := M) D j w * D.mat j h p q w|
          = |ResidGn.boxChi (I := I) (M := M) D j w| * |D.mat j h p q w| := abs_mul _ _
        _ ≤ 1 * K := mul_le_mul (abs_boxChi_le_one (I := I) (M := M) D j w) hMf
            (abs_nonneg _) (by norm_num)
        _ = K := one_mul K

/-- **The `Nper` bound**: the derivative of the cut-off chart matrix is bounded by `K` (the jet
hypothesis) plus `K` times the bound `C` on the derivative of the cut-off. -/
lemma Nper_abs_le (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (lam K C : ℝ) (hlam : 0 < lam) (hK : 0 < K) (hC0 : 0 ≤ C)
    (hC : ∀ (w : Idx → ℝ) (r : Idx),
      |Work.Diff.STE.pdR r (ResidGn.boxChi (I := I) (M := M) D j) w| ≤ C)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
    (hjet : ∀ (i : ι₀) (c d r : Idx) (z : Idx → ℝ), ‖z‖ ≤ 2 * D.σ i →
      |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K)
    (p q r : Idx) (z : Idx → ℝ) :
    |ResidGn.Nper (I := I) (M := M) D h j z p q r| ≤ K * (1 + C) := by
  rw [Nper_eq_tmPer_apply (I := I) (M := M) D h j p q r z]
  refine Work.Diff.STE.B3.abs_tmPer_le (R := 1 / 2) (B := K * (1 + C)) (le_refl (1 / 2)) ?_ ?_ z
  · intro w hw
    exact tsupport_boxChi_mul_mat_subset_ball (I := I) (M := M) D h j p q
      (support_pdR_subset_tsupport r hw)
  · intro w
    by_cases h0 : Work.Diff.STE.pdR r
        (fun y : Idx → ℝ => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) w = 0
    · rw [h0, abs_zero]
      nlinarith [hK, hC0]
    · have hwmem : w ∈ Function.support (fun w : Idx → ℝ => Work.Diff.STE.pdR r
          (fun y : Idx → ℝ => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) w) :=
        Function.mem_support.mpr h0
      have hts : w ∈ tsupport (fun y : Idx → ℝ =>
          ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y) :=
        support_pdR_subset_tsupport r hwmem
      have hz : ‖w‖ ≤ 2 * D.σ j := by
        have h1 : w ∈ tsupport (ResidGn.boxChi (I := I) (M := M) D j) :=
          tsupport_mul_subset_left hts
        rw [ResidGn.boxChi_tsupport (I := I) (M := M) D j, Metric.mem_closedBall,
          dist_zero_right] at h1
        exact h1
      have hdchi : DifferentiableAt ℝ (ResidGn.boxChi (I := I) (M := M) D j) w :=
        (ResidGn.boxChi_contDiff (I := I) (M := M) D j).contDiffAt.differentiableAt (by simp)
      have hdmat : DifferentiableAt ℝ (D.mat j h p q) w :=
        (Work.Diff.STE.B3.mat_contDiffAt_of_chartData D h hsm j p q w
          (D.htarget j w hz)).differentiableAt (by simp)
      rw [Work.Diff.STE.B3.pdR_mul_eq hdchi hdmat]
      have hmatK : |D.mat j h p q w| ≤ K :=
        (Work.Diff.STE.B3.Mf_sandwich D j lam K hlam hK h hsym hell hub w hz).2.2.1 p q
      have hjetK : |Work.Diff.STE.pdR r (D.mat j h p q) w| ≤ K := hjet j p q r w hz
      have hCχ : |Work.Diff.STE.pdR r (ResidGn.boxChi (I := I) (M := M) D j) w| ≤ C := hC w r
      calc |ResidGn.boxChi (I := I) (M := M) D j w * Work.Diff.STE.pdR r (D.mat j h p q) w
              + D.mat j h p q w * Work.Diff.STE.pdR r (ResidGn.boxChi (I := I) (M := M) D j) w|
          ≤ |ResidGn.boxChi (I := I) (M := M) D j w * Work.Diff.STE.pdR r (D.mat j h p q) w|
            + |D.mat j h p q w * Work.Diff.STE.pdR r
                (ResidGn.boxChi (I := I) (M := M) D j) w| := abs_add_le _ _
        _ = |ResidGn.boxChi (I := I) (M := M) D j w| * |Work.Diff.STE.pdR r (D.mat j h p q) w|
            + |D.mat j h p q w| * |Work.Diff.STE.pdR r
                (ResidGn.boxChi (I := I) (M := M) D j) w| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * K + K * C := by
            exact add_le_add
              (mul_le_mul (abs_boxChi_le_one (I := I) (M := M) D j w) hjetK (abs_nonneg _)
                (by norm_num))
              (mul_le_mul hmatK hCχ (abs_nonneg _) hK.le)
        _ = K * (1 + C) := by ring

/-! ## 4. The agreement with the chart matrix on the open `σ_j`-ball -/

lemma Mper_agree (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) {z : Idx → ℝ} (hz : ‖z‖ < D.σ j)
    (p q : Idx) :
    ResidGn.Mper (I := I) (M := M) D h j z p q = D.mat j h p q z := by
  have hzcube : ∀ i : Idx, z i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    intro i
    rw [Set.mem_Ioo]
    have h1 : |z i| ≤ ‖z‖ := by simpa using norm_le_pi_norm z i
    have h2 : ‖z‖ < 1 / 2 := by
      have hσ : D.σ j ≤ 1 / 8 := by linarith [D.hσ2 j]
      linarith
    exact abs_lt.mp (lt_of_le_of_lt h1 h2)
  rw [Mper_eq_tmPer_apply (I := I) (M := M) D h j p q z,
    Work.Diff.STE.B3.tmPer_eq_self (support_boxChi_mul_mat_subset_cube (I := I) (M := M) D h j p q)
      hzcube,
    ResidGn.boxChi_one (I := I) (M := M) D j (by linarith [D.hσ j, hz]), one_mul]

lemma Nper_agree (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) {z : Idx → ℝ} (hz : ‖z‖ < D.σ j)
    (p q r : Idx) :
    ResidGn.Nper (I := I) (M := M) D h j z p q r = Work.Diff.STE.pdR r (D.mat j h p q) z := by
  have hzcube : ∀ i : Idx, z i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    intro i
    rw [Set.mem_Ioo]
    have h1 : |z i| ≤ ‖z‖ := by simpa using norm_le_pi_norm z i
    have h2 : ‖z‖ < 1 / 2 := by
      have hσ : D.σ j ≤ 1 / 8 := by linarith [D.hσ2 j]
      linarith
    exact abs_lt.mp (lt_of_le_of_lt h1 h2)
  rw [Nper_eq_tmPer_apply (I := I) (M := M) D h j p q r z,
    Work.Diff.STE.B3.tmPer_eq_self
      (support_pdR_boxChi_mul_mat_subset_cube (I := I) (M := M) D h j p q r) hzcube]
  have hnear : (fun y : Idx → ℝ => ResidGn.boxChi (I := I) (M := M) D j y * D.mat j h p q y)
      =ᶠ[nhds z] (D.mat j h p q) := by
    have hε : 0 < 3 * D.σ j / 2 - ‖z‖ := by linarith [D.hσ j]
    filter_upwards [Metric.ball_mem_nhds z hε] with y hy
    have hy' : ‖y‖ ≤ 3 * D.σ j / 2 := by
      have h1 : ‖y - z‖ < 3 * D.σ j / 2 - ‖z‖ := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hy
      have h2 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
        calc ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
      linarith
    rw [ResidGn.boxChi_one (I := I) (M := M) D j hy', one_mul]
  simp only [Work.Diff.STE.pdR]
  rw [hnear.fderiv_eq]

/-! ## 5. The statement -/

theorem residInnerBasic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
        (hjet : ∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
          |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K),
        (∀ (p q : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
            (fun z : Fin (Module.finrank ℝ E) → ℝ =>
              Work.Diff.STE.Lead.GalTame.ResidGn.Mper (I := I) (M := M) D h j z p q)) ∧
        (∀ (p q r : Fin (Module.finrank ℝ E)),
          ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
            (fun z : Fin (Module.finrank ℝ E) → ℝ =>
              Work.Diff.STE.Lead.GalTame.ResidGn.Nper (I := I) (M := M) D h j z p q r)) ∧
        (∀ (p q : Fin (Module.finrank ℝ E)),
          Work.Diff.STE.Periodic1 (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.Lead.GalTame.ResidGn.Mper (I := I) (M := M) D h j z p q)) ∧
        (∀ (p q r : Fin (Module.finrank ℝ E)),
          Work.Diff.STE.Periodic1 (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.Lead.GalTame.ResidGn.Nper (I := I) (M := M) D h j z p q r)) ∧
        (∀ (z : Fin (Module.finrank ℝ E) → ℝ) (p q : Fin (Module.finrank ℝ E)),
          |Work.Diff.STE.Lead.GalTame.ResidGn.Mper (I := I) (M := M) D h j z p q| ≤ B) ∧
        (∀ (z : Fin (Module.finrank ℝ E) → ℝ) (p q r : Fin (Module.finrank ℝ E)),
          |Work.Diff.STE.Lead.GalTame.ResidGn.Nper (I := I) (M := M) D h j z p q r| ≤ B) ∧
        (∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ < D.σ j →
          ∀ (p q : Fin (Module.finrank ℝ E)),
            Work.Diff.STE.Lead.GalTame.ResidGn.Mper (I := I) (M := M) D h j z p q
              = D.mat j h p q z) ∧
        (∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ < D.σ j →
          ∀ (p q r : Fin (Module.finrank ℝ E)),
            Work.Diff.STE.Lead.GalTame.ResidGn.Nper (I := I) (M := M) D h j z p q r
              = Work.Diff.STE.pdR r (D.mat j h p q) z) := by
  obtain ⟨C, hC0, hC⟩ := exists_pdR_boxChi_bound (I := I) (M := M) D j
  refine ⟨K * (1 + C), by positivity, ?_⟩
  intro h hsym hsm hell hub hjet
  refine ⟨fun p q => Mper_contDiff (I := I) (M := M) D h hsm j p q,
    fun p q r => Nper_contDiff (I := I) (M := M) D h hsm j p q r,
    fun p q => Mper_periodic (I := I) (M := M) D h hsm j p q,
    fun p q r => Nper_periodic (I := I) (M := M) D h hsm j p q r,
    fun z p q => ?_, fun z p q r => ?_,
    fun z hz p q => Mper_agree (I := I) (M := M) D h j hz p q,
    fun z hz p q r => Nper_agree (I := I) (M := M) D h j hz p q r⟩
  · have h1 := Mper_abs_le (I := I) (M := M) D j lam K hlam hK h hsym hell hub p q z
    calc |ResidGn.Mper (I := I) (M := M) D h j z p q| ≤ K := h1
      _ ≤ K * (1 + C) := by nlinarith [hK, hC0]
  · exact Nper_abs_le (I := I) (M := M) D j lam K C hlam hK hC0 hC h hsym hsm hell hub hjet p q r z

end

end Work.Diff.STE.Lead.GalTame
