import Mathlib
import Submission.Work.Diff.GE.CFQDefs
import Submission.Work.Diff.GE.qPair_rot_eq_qPairGen
import Submission.Work.Diff.GE.gramInv_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of `qPairGen` in a jointly smooth general-basis frame

`Work.Diff.GE.qPairGen Γ C` is the general-basis form of the frozen curvature quantity
`⟪Rm, Q(Rm)⟫ = qPair`: for a frame whose Gram matrix is `Γ` and whose curvature components are `C`,
it is `qPairAt` computed in that frame.  In the applications (`Work.Diff.GE.continuous_flow_quantities`)
the frame is the chart coordinate frame of a Ricci flow, so it is the *inverse* Gram matrix `Γ⁻¹`
and the curvature components `C` that are known to be jointly `C^∞`.

The target lemma says: if each entry of `Γ⁻¹` and each entry of `C` is jointly `C^∞` near
`(t₀, x)`, then so is `qPairGen (Γ ·) (C ·)`.

The point is that `qPairGen` is a **polynomial** in the entries of `Γ⁻¹` and of `C`: the three
groupings `rqM`, `rqN`, `rqP` are linear projections of the entries of `C`, `rqKr` is bilinear in
the entries of the matrix, and `Matrix.trace` of a product of matrices is a finite sum of products
of entries.  So we introduce `qPairGenA A C`, the same expression with `A` standing in for the
(already inverted) Gram matrix; it is a polynomial, hence `C^∞`, in its arguments.  Then

* `p ↦ ((Γ p)⁻¹, C p)` is jointly `C^∞` by `contMDiffAt_pi_space` (four times for the curvature
  components) and `ContMDiffAt.prodMk_space`;
* `(A, C) ↦ qPairGenA A C` is `C^∞` (`contDiff_qPairGenA`, proved by expanding the definition
  entrywise and calling `fun_prop`);
* `qPairGen Γ C = qPairGenA (Γ⁻¹) C` holds definitionally,
so the composition is jointly `C^∞`.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {n : ℕ}

/-- **The general-basis form of `qPair` with the inverse Gram matrix as an explicit argument.**
`qPairGenA A C` is `qPairGen Γ C` for `A = Γ⁻¹`: the same expression, but with `A` itself in place
of `Γ⁻¹`.  This is the version which is a *polynomial* (hence `C^∞`) in its arguments. -/
noncomputable def qPairGenA (A : Matrix (Fin n) (Fin n) ℝ) (C : Curv4 n) : ℝ :=
  Matrix.trace ((rqM C)ᵀ * rqKr A * rqM C * rqKr A * (rqM C)ᵀ * rqKr A)
    + 2 * Matrix.trace ((rqN C)ᵀ * rqKr A * rqN C * rqKr A * (rqN C)ᵀ * rqKr A)
    - 2 * Matrix.trace ((rqP C)ᵀ * rqKr A * rqN C * rqKr A * (rqN C)ᵀ * rqKr A)

/-- `qPairGen Γ C` is `qPairGenA` applied to the inverse Gram matrix (definitionally). -/
lemma qPairGen_eq_qPairGenA (Γ : Matrix (Fin n) (Fin n) ℝ) (C : Curv4 n) :
    qPairGen Γ C = qPairGenA (Γ⁻¹) C := by
  simp only [qPairGen, qPairGenA]

set_option maxHeartbeats 2000000 in
/-- `qPairGenA` is a polynomial in the entries of `A` and of `C`, hence `C^∞`.  The proof expands
`Matrix.trace`, `Matrix.mul`, `Matrix.transpose`, `rqM`, `rqN`, `rqP` and `rqKr`
(`Matrix.kroneckerMap`) entrywise, leaving a nested finite sum of products of coordinate functions,
which `fun_prop` closes. -/
theorem contDiff_qPairGenA :
    ContDiff ℝ ∞ (fun q : (Fin n → Fin n → ℝ) × Curv4 n => qPairGenA q.1 q.2) := by
  simp only [qPairGenA, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    rqM, rqN, rqP, rqKr, Matrix.kroneckerMap, Matrix.of_apply]
  fun_prop

theorem qPairGen_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    {n : ℕ} {Γ : ℝ × M → Matrix (Fin n) (Fin n) ℝ}
    {C : ℝ × M → Submission.Diff.Alg.Curv4 n} {t₀ : ℝ} {x : M}
    (hΓ : ∀ i j, Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ (Γ p)⁻¹ i j) t₀ x)
    (hC : ∀ i j k l, Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ C p i j k l) t₀ x) :
    Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M ↦ Work.Diff.GE.qPairGen (Γ p) (C p)) t₀ x := by
  classical
  -- The inverse Gram matrix is jointly `C^∞` as a matrix-valued function (its entries are `hΓ`).
  have hA : Work.Diff.EXT.JointSmoothAt I M (fun p : ℝ × M => fun i j => (Γ p)⁻¹ i j) t₀ x := by
    show ContMDiffAt _ _ _ (fun p : ℝ × M => fun i j => (Γ p)⁻¹ i j) _
    rw [contMDiffAt_pi_space]
    intro i
    rw [contMDiffAt_pi_space]
    intro j
    exact hΓ i j
  -- The curvature components are jointly `C^∞` as a tensor-valued function (entries are `hC`).
  have hCc : Work.Diff.EXT.JointSmoothAt I M
      (fun p : ℝ × M => fun i j k l => C p i j k l) t₀ x := by
    show ContMDiffAt _ _ _ (fun p : ℝ × M => fun i j k l => C p i j k l) _
    rw [contMDiffAt_pi_space]; intro i
    rw [contMDiffAt_pi_space]; intro j
    rw [contMDiffAt_pi_space]; intro k
    rw [contMDiffAt_pi_space]; intro l
    exact hC i j k l
  -- Pairing the two jointly smooth families.
  have hprod : ContMDiffAt (𝓘(ℝ,ℝ).prod I) (𝓘(ℝ, (Fin n → Fin n → ℝ) × Curv4 n)) ∞
      (fun p : ℝ × M => ((fun i j => (Γ p)⁻¹ i j), (fun i j k l => C p i j k l))) (t₀, x) :=
    ContMDiffAt.prodMk_space hA hCc
  -- The polynomial `qPairGenA` is `C^∞` at the relevant point, so composition applies.
  have hg : ContDiffAt ℝ ∞ (fun q : (Fin n → Fin n → ℝ) × Curv4 n => qPairGenA q.1 q.2)
      ((fun i j => (Γ (t₀, x))⁻¹ i j), (fun i j k l => C (t₀, x) i j k l)) :=
    contDiff_qPairGenA.contDiffAt
  have hcomp := hg.comp_contMDiffAt
    (f := fun p : ℝ × M => ((fun i j => (Γ p)⁻¹ i j), (fun i j k l => C p i j k l))) hprod
  show ContMDiffAt (𝓘(ℝ,ℝ).prod I) (𝓘(ℝ,ℝ)) ∞ (fun p : ℝ × M => qPairGen (Γ p) (C p)) (t₀, x)
  change ContMDiffAt (𝓘(ℝ,ℝ).prod I) (𝓘(ℝ,ℝ)) ∞
      ((fun q : (Fin n → Fin n → ℝ) × Curv4 n => qPairGenA q.1 q.2) ∘
        (fun p : ℝ × M => ((fun i j => (Γ p)⁻¹ i j), (fun i j k l => C p i j k l)))) (t₀, x)
  exact hcomp

end Work.Diff.GE
