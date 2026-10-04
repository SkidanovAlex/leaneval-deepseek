import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.tmPsi_exists
import Submission.Work.Diff.STE.Lead.GalTame.GalCenter

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The box data of the sharp residual estimate

This module fixes the vocabulary on which the assembly of `Work.Diff.STE.Lead.GalTame.sharpResid`
runs.

* `boxChi D j` is a `C^∞` bump on the flat coordinate, equal to `1` on the closed `3σ_j/2`-ball
  and supported in the *open* ball of radius `2σ_j`.  This is the cut-off multiplying the chart
  matrix before periodisation.
* `Mper D h j z p q` is the **periodisation of the cut-off chart matrix**:
  `z ↦ ∑' k, χ(z+k) · mat(z+k)`.  It is a smooth `1`-periodic function of `z`, and on the open
  `σ_j`-ball it agrees with the chart matrix `D.mat j h p q`.
* `Nper D h j z p q r` is the periodisation of the first jet of the cut-off chart matrix; it is
  the second component of the state at which the outer function is evaluated, and on the open
  `σ_j`-ball it agrees with `∂_r (D.mat j h p q)`.
* `boxEta D j` is the bump of radii `2σ_j < 3σ_j`, and `boxZeta D j ζ = ζ · boxEta D j` is the
  coordinate separator of the outer function: it is `1` on the closed `2σ_j`-ball (where `ζ` is
  `1` by `tms_exists_zeta`) and it is *compactly supported* in the closed `3σ_j`-ball, so that the
  outer function `boxPhi` vanishes identically off the compact box of states of radius `3σ_j`.
-/

noncomputable section

open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set MeasureTheory

namespace Work.Diff.STE.Lead.GalTame.ResidGn

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-- The box cut-off: a `C^∞` bump equal to `1` on the closed `3σ_j/2`-ball, supported in the open
ball of radius `2σ_j` (hence, since `2σ_j ≤ 1/4`, in the open unit cube). -/
def boxChiBump (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    ContDiffBump (0 : Idx → ℝ) :=
  ⟨3 * D.σ j / 2, 2 * D.σ j, by linarith [D.hσ j], by linarith [D.hσ j]⟩

/-- The separator bump of the outer function: radii `2σ_j < 3σ_j`. -/
def boxEtaBump (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    ContDiffBump (0 : Idx → ℝ) :=
  ⟨2 * D.σ j, 3 * D.σ j, by linarith [D.hσ j], by linarith [D.hσ j]⟩

/-- The box cut-off, as a function. -/
def boxChi (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    (Idx → ℝ) → ℝ :=
  ⇑(boxChiBump (I := I) (M := M) D j)

/-- The separator bump, as a function. -/
def boxEta (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    (Idx → ℝ) → ℝ :=
  ⇑(boxEtaBump (I := I) (M := M) D j)

/-- The compactly supported coordinate separator of the outer function: the function `ζ` of
`tms_exists_zeta` (equal to `1` on the closed `2σ_j`-ball, supported in `tmsGood D j`) multiplied by
`boxEta D j`.  It is `1` on the closed `2σ_j`-ball and vanishes off the closed `3σ_j`-ball. -/
def boxZeta (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (ζ : (Idx → ℝ) → ℝ) : (Idx → ℝ) → ℝ :=
  fun z => ζ z * boxEta (I := I) (M := M) D j z

/-- The **outer function** of the residual: `tmsPhiFun` with the compactly supported separator
`boxZeta`.  It is globally `C^∞` and reproduces `residualLow` on the closed `σ_j`-ball. -/
def boxPhi (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (cl ch : ℝ) (hcl : 0 < cl) (hch : cl < ch) (ζ : (Idx → ℝ) → ℝ) :
    ((Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)) → Idx → Idx → ℝ :=
  Work.Diff.STE.B3.tmsPhiFun (I := I) (M := M) D j cl ch hcl hch
    (boxZeta (I := I) (M := M) D j ζ)

/-- **The periodised cut-off chart matrix**: the first inner component of the outer function. -/
def Mper (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Idx → ℝ) (p q : Idx) : ℝ :=
  ∑' k : Idx → ℤ,
    boxChi (I := I) (M := M) D j (z + Work.Diff.STE.iVec k)
      * D.mat j h p q (z + Work.Diff.STE.iVec k)

/-- **The periodised first jet of the cut-off chart matrix**: the second inner component of the
outer function (`r` is the derivative direction, `p q` the matrix indices). -/
def Nper (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Idx → ℝ) (p q r : Idx) : ℝ :=
  ∑' k : Idx → ℤ,
    Work.Diff.STE.pdR r
      (fun y : Idx → ℝ => boxChi (I := I) (M := M) D j y * D.mat j h p q y)
      (z + Work.Diff.STE.iVec k)

@[simp] lemma boxChi_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Idx → ℝ) :
    boxChi (I := I) (M := M) D j z = boxChiBump (I := I) (M := M) D j z := rfl

@[simp] lemma boxEta_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Idx → ℝ) :
    boxEta (I := I) (M := M) D j z = boxEtaBump (I := I) (M := M) D j z := rfl

@[simp] lemma boxZeta_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (ζ : (Idx → ℝ) → ℝ) (z : Idx → ℝ) :
    boxZeta (I := I) (M := M) D j ζ z
      = ζ z * boxEta (I := I) (M := M) D j z := rfl

@[simp] lemma boxPhi_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (cl ch : ℝ) (hcl : 0 < cl) (hch : cl < ch) (ζ : (Idx → ℝ) → ℝ)
    (w : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)) (a' b' : Idx) :
    boxPhi (I := I) (M := M) D j cl ch hcl hch ζ w a' b'
      = Work.Diff.STE.B3.tmsPhiFun (I := I) (M := M) D j cl ch hcl hch
          (boxZeta (I := I) (M := M) D j ζ) w a' b' := rfl

/-- `boxChiBump` has radii `3σ_j/2` and `2σ_j`. -/
@[simp] lemma boxChiBump_rIn (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    (boxChiBump (I := I) (M := M) D j).rIn = 3 * D.σ j / 2 := rfl

@[simp] lemma boxChiBump_rOut (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    (boxChiBump (I := I) (M := M) D j).rOut = 2 * D.σ j := rfl

@[simp] lemma boxEtaBump_rIn (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    (boxEtaBump (I := I) (M := M) D j).rIn = 2 * D.σ j := rfl

@[simp] lemma boxEtaBump_rOut (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    (boxEtaBump (I := I) (M := M) D j).rOut = 3 * D.σ j := rfl

/-- The box cut-off is smooth. -/
lemma boxChi_contDiff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (boxChi (I := I) (M := M) D j) :=
  ContDiffBump.contDiff (boxChiBump (I := I) (M := M) D j)

/-- The box cut-off equals `1` on the closed `3σ_j/2`-ball. -/
lemma boxChi_one (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Idx → ℝ} (hz : ‖z‖ ≤ 3 * D.σ j / 2) :
    boxChi (I := I) (M := M) D j z = 1 :=
  ContDiffBump.one_of_mem_closedBall (boxChiBump (I := I) (M := M) D j)
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)

/-- The box cut-off is supported in the open ball of radius `2σ_j`. -/
lemma boxChi_support (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    Function.support (boxChi (I := I) (M := M) D j)
      ⊆ Metric.ball (0 : Idx → ℝ) (2 * D.σ j) :=
  (ContDiffBump.support_eq (boxChiBump (I := I) (M := M) D j)).le

/-- The topological support of the box cut-off is the closed ball of radius `2σ_j`. -/
lemma boxChi_tsupport (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    tsupport (boxChi (I := I) (M := M) D j) = Metric.closedBall (0 : Idx → ℝ) (2 * D.σ j) :=
  ContDiffBump.tsupport_eq (boxChiBump (I := I) (M := M) D j)

/-- The topological support of the box cut-off is contained in the closed ball of radius
`2σ_j`. -/
lemma boxChi_tsupport_subset (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    tsupport (boxChi (I := I) (M := M) D j)
      ⊆ Metric.closedBall (0 : Idx → ℝ) (2 * D.σ j) :=
  (boxChi_tsupport (I := I) (M := M) D j).le

/-- The support of the box cut-off is contained in the open unit cube `(-1/2,1/2)^n`: this is what
makes the periodisation of the cut-off chart matrix a *single*-translate sum inside the fundamental
cube. -/
lemma boxChi_support_openCube (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    Function.support (boxChi (I := I) (M := M) D j)
      ⊆ Set.pi Set.univ (fun _ : Idx => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
  intro z hz i _
  have hz' : ‖z‖ < 2 * D.σ j := by
    have := boxChi_support (I := I) (M := M) D j hz
    rwa [Metric.mem_ball, dist_zero_right] at this
  have h4 : 2 * D.σ j ≤ 1 / 4 := D.hσ2 j
  have hi : |z i| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
  have hlt : |z i| < (1 : ℝ) / 2 := by linarith
  exact abs_lt.mp hlt

/-- The separator bump is smooth. -/
lemma boxEta_contDiff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (boxEta (I := I) (M := M) D j) :=
  ContDiffBump.contDiff (boxEtaBump (I := I) (M := M) D j)

/-- The separator bump equals `1` on the closed `2σ_j`-ball. -/
lemma boxEta_one (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Idx → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    boxEta (I := I) (M := M) D j z = 1 :=
  ContDiffBump.one_of_mem_closedBall (boxEtaBump (I := I) (M := M) D j)
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)

/-- The topological support of the separator bump is the closed ball of radius `3σ_j`. -/
lemma boxEta_tsupport (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    tsupport (boxEta (I := I) (M := M) D j) = Metric.closedBall (0 : Idx → ℝ) (3 * D.σ j) :=
  ContDiffBump.tsupport_eq (boxEtaBump (I := I) (M := M) D j)

/-- The compact separator `boxZeta` is smooth when `ζ` is. -/
lemma boxZeta_contDiff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {ζ : (Idx → ℝ) → ℝ} (hζ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ζ) :
    ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (boxZeta (I := I) (M := M) D j ζ) :=
  hζ.mul (boxEta_contDiff (I := I) (M := M) D j)

/-- The compact separator equals `1` on the closed `2σ_j`-ball, when `ζ` does. -/
lemma boxZeta_one (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {ζ : (Idx → ℝ) → ℝ} (hζ1 : ∀ z : Idx → ℝ, ‖z‖ ≤ 2 * D.σ j → ζ z = 1)
    {z : Idx → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) :
    boxZeta (I := I) (M := M) D j ζ z = 1 := by
  rw [boxZeta_apply, hζ1 z hz, boxEta_one (I := I) (M := M) D j hz, one_mul]

/-- The compact separator is supported in the closed ball of radius `3σ_j`. -/
lemma boxZeta_tsupport_subset (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (ζ : (Idx → ℝ) → ℝ) :
    tsupport (boxZeta (I := I) (M := M) D j ζ)
      ⊆ Metric.closedBall (0 : Idx → ℝ) (3 * D.σ j) := by
  have h2 : tsupport (fun z => ζ z * boxEta (I := I) (M := M) D j z)
      ⊆ tsupport (boxEta (I := I) (M := M) D j) :=
    closure_mono (Function.support_mul_subset_right ζ (boxEta (I := I) (M := M) D j))
  rw [boxEta_tsupport (I := I) (M := M) D j] at h2
  exact fun z hz => h2 hz

/-- The compact separator is supported in the topological support of `ζ`. -/
lemma boxZeta_tsupport_subset_tsupport (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) (ζ : (Idx → ℝ) → ℝ) :
    tsupport (boxZeta (I := I) (M := M) D j ζ) ⊆ tsupport ζ :=
  closure_mono (Function.support_mul_subset_left ζ (boxEta (I := I) (M := M) D j))

/-- If the compact separator vanishes at `z`, the outer function vanishes at every state whose
first coordinate is `z`. -/
lemma boxPhi_eq_zero_of_boxZeta_eq_zero (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) (cl ch : ℝ) (hcl : 0 < cl) (hch : cl < ch) (ζ : (Idx → ℝ) → ℝ)
    {z : Idx → ℝ} (hz : boxZeta (I := I) (M := M) D j ζ z = 0)
    (V : Idx → Idx → ℝ) (W : Idx → Idx → Idx → ℝ) (a' b' : Idx) :
    boxPhi (I := I) (M := M) D j cl ch hcl hch ζ (z, V, W) a' b' = 0 := by
  simp only [boxPhi, Work.Diff.STE.B3.tmsPhiFun, hz, zero_mul]

end Work.Diff.STE.Lead.GalTame.ResidGn
