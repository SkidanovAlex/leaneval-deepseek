import Mathlib
import Submission.Work.Diff.EXT.reconDefs
import Submission.Work.Diff.EXT.kosDefs
import Submission.Work.Diff.EXT.continuousAt_mvfderiv_family
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.EXT.lcFree

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity in `t` of the reconstruction coefficients of `∇_{Xdir} Z`

`Work.Diff.EXT.reconCoef G x Xdir Z j t y` is the `j`-th coefficient of `∇_{Xdir} Z` in the
coordinate frame of the chart at `x`, for the metric `G t`:

`∇_{Xdir} Z (y) = ∑_j reconCoef j • fr j (y)`   (`Work.Diff.EXT.lcOf_eq_sum_reconCoef`).

This file proves that, for a jointly smooth family of metrics `G` on an open time set `J ∋ t₀`,
fixed smooth-at-`x` fields `Xdir`, `Z` and a fixed point `x`, the coefficient
`t ↦ reconCoef G x Xdir Z j t x` is continuous at `t₀`.

The coefficient is `(gramM (G t) x x)⁻¹ *ᵥ (fun i => kosGen … i t x)`.  Both factors are continuous:
the inverse Gram matrix because the Gram matrix entries are the metric pairings of the (smooth at
`x`) coordinate frame fields with `G`, and inversion of a matrix is continuous at an invertible
matrix; the Koszul coefficients because the Koszul expression is built from metric pairings of
fields smooth at `x` (whose spatial derivatives are continuous in the parameter by
`Work.Diff.EXT.continuousAt_mvfderiv_family`) and from metric pairings with Lie brackets of such
fields.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

set_option linter.unusedSectionVars false

theorem reconCoef_continuousAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x : M)
    {Xdir Z : Π y : M, TangentSpace I y}
    (hX : Work.Diff.EXT.SmoothFieldAt I M Xdir x)
    (hZ : Work.Diff.EXT.SmoothFieldAt I M Z x) (j : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun t : ℝ ↦ Work.Diff.EXT.reconCoef (I := I) G x Xdir Z j t x) t₀ := by
  classical
  -- the diagonal inclusion `t ↦ (t, x)`
  have hpair : ContinuousAt (fun t : ℝ ↦ (t, x)) t₀ :=
    continuousAt_id.prodMk continuousAt_const
  -- ### Step 1: the coordinate frame fields are `C^∞` at `x`
  have hfr : ∀ i : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.SmoothFieldAt I M (Work.Diff.EXT.fr (I := I) x i) x := by
    intro i
    have h := Work.Diff.EXT.contMDiffAt_frameVector (I := I) x (Module.finBasis ℝ E i)
      (mem_chart_source H x)
    simpa only [Work.Diff.EXT.SmoothFieldAt, Work.Diff.EXT.fr] using h
  -- ### Step 2: continuity of the Koszul pairings `kosGen … (fr x i) t x`
  have hkos : ∀ i : Fin (Module.finrank ℝ E),
      ContinuousAt (fun t : ℝ ↦ Work.Diff.EXT.kosGen (I := I) G Xdir Z
        (Work.Diff.EXT.fr (I := I) x i) t x) t₀ := by
    intro i
    -- the Lie brackets appearing in the Koszul expression are smooth at `x`
    have hW₁ : Work.Diff.EXT.SmoothFieldAt I M
        (mlieBracket I Xdir (Work.Diff.EXT.fr (I := I) x i)) x :=
      Work.Diff.EXT.LC.mlieBracket_contMDiffAt (I := I) hX (hfr i)
    have hW₂ : Work.Diff.EXT.SmoothFieldAt I M (mlieBracket I Z Xdir) x :=
      Work.Diff.EXT.LC.mlieBracket_contMDiffAt (I := I) hZ hX
    have hW₃ : Work.Diff.EXT.SmoothFieldAt I M
        (mlieBracket I (Work.Diff.EXT.fr (I := I) x i) Z) x :=
      Work.Diff.EXT.LC.mlieBracket_contMDiffAt (I := I) (hfr i) hZ
    -- the three spatial-derivative terms
    have hA : ContinuousAt (fun t : ℝ ↦ mvfderiv I
        (fun y : M ↦ (G t).inner y (Z y) (Work.Diff.EXT.fr (I := I) x i y))
        x (Xdir x)) t₀ :=
      Work.Diff.EXT.continuousAt_mvfderiv_family (I := I) (M := M) (F := ℝ)
        (Φ := fun p : ℝ × M ↦ (G p.1).inner p.2 (Z p.2) (Work.Diff.EXT.fr (I := I) x i p.2))
        (Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJ hG ht₀ hZ (hfr i))
        (Xdir x)
    have hB : ContinuousAt (fun t : ℝ ↦ mvfderiv I
        (fun y : M ↦ (G t).inner y (Work.Diff.EXT.fr (I := I) x i y) (Xdir y))
        x (Z x)) t₀ :=
      Work.Diff.EXT.continuousAt_mvfderiv_family (I := I) (M := M) (F := ℝ)
        (Φ := fun p : ℝ × M ↦ (G p.1).inner p.2 (Work.Diff.EXT.fr (I := I) x i p.2) (Xdir p.2))
        (Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJ hG ht₀ (hfr i) hX)
        (Z x)
    have hC : ContinuousAt (fun t : ℝ ↦ mvfderiv I
        (fun y : M ↦ (G t).inner y (Xdir y) (Z y))
        x (Work.Diff.EXT.fr (I := I) x i x)) t₀ :=
      Work.Diff.EXT.continuousAt_mvfderiv_family (I := I) (M := M) (F := ℝ)
        (Φ := fun p : ℝ × M ↦ (G p.1).inner p.2 (Xdir p.2) (Z p.2))
        (Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJ hG ht₀ hX hZ)
        (Work.Diff.EXT.fr (I := I) x i x)
    -- the three Lie-bracket pairing terms
    have hD : ContinuousAt (fun t : ℝ ↦ (G t).inner x (Z x)
        (mlieBracket I Xdir (Work.Diff.EXT.fr (I := I) x i) x)) t₀ := by
      have h : ContinuousAt (fun p : ℝ × M ↦ (G p.1).inner p.2 (Z p.2)
          (mlieBracket I Xdir (Work.Diff.EXT.fr (I := I) x i) p.2)) (t₀, x) :=
        (Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJ hG ht₀ hZ hW₁).continuousAt
      have hc : ContinuousAt ((fun p : ℝ × M ↦ (G p.1).inner p.2 (Z p.2)
          (mlieBracket I Xdir (Work.Diff.EXT.fr (I := I) x i) p.2))
            ∘ (fun t : ℝ ↦ (t, x))) t₀ :=
        h.tendsto.comp hpair.tendsto
      simpa only [Function.comp_def] using hc
    have hE : ContinuousAt (fun t : ℝ ↦ (G t).inner x (Work.Diff.EXT.fr (I := I) x i x)
        (mlieBracket I Z Xdir x)) t₀ := by
      have h : ContinuousAt (fun p : ℝ × M ↦ (G p.1).inner p.2
          (Work.Diff.EXT.fr (I := I) x i p.2) (mlieBracket I Z Xdir p.2)) (t₀, x) :=
        (Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJ hG ht₀ (hfr i) hW₂).continuousAt
      have hc : ContinuousAt ((fun p : ℝ × M ↦ (G p.1).inner p.2
          (Work.Diff.EXT.fr (I := I) x i p.2) (mlieBracket I Z Xdir p.2))
            ∘ (fun t : ℝ ↦ (t, x))) t₀ :=
        h.tendsto.comp hpair.tendsto
      simpa only [Function.comp_def] using hc
    have hF : ContinuousAt (fun t : ℝ ↦ (G t).inner x (Xdir x)
        (mlieBracket I (Work.Diff.EXT.fr (I := I) x i) Z x)) t₀ := by
      have h : ContinuousAt (fun p : ℝ × M ↦ (G p.1).inner p.2 (Xdir p.2)
          (mlieBracket I (Work.Diff.EXT.fr (I := I) x i) Z p.2)) (t₀, x) :=
        (Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJ hG ht₀ hX hW₃).continuousAt
      have hc : ContinuousAt ((fun p : ℝ × M ↦ (G p.1).inner p.2 (Xdir p.2)
          (mlieBracket I (Work.Diff.EXT.fr (I := I) x i) Z p.2))
            ∘ (fun t : ℝ ↦ (t, x))) t₀ :=
        h.tendsto.comp hpair.tendsto
      simpa only [Function.comp_def] using hc
    -- combine
    have hsum : ContinuousAt (fun t : ℝ ↦
        mvfderiv I (fun y : M ↦ (G t).inner y (Z y) (Work.Diff.EXT.fr (I := I) x i y))
          x (Xdir x)
        + mvfderiv I (fun y : M ↦ (G t).inner y (Work.Diff.EXT.fr (I := I) x i y) (Xdir y))
          x (Z x)
        - mvfderiv I (fun y : M ↦ (G t).inner y (Xdir y) (Z y))
          x (Work.Diff.EXT.fr (I := I) x i x)
        - (G t).inner x (Z x) (mlieBracket I Xdir (Work.Diff.EXT.fr (I := I) x i) x)
        - (G t).inner x (Work.Diff.EXT.fr (I := I) x i x) (mlieBracket I Z Xdir x)
        + (G t).inner x (Xdir x) (mlieBracket I (Work.Diff.EXT.fr (I := I) x i) Z x)) t₀ :=
      (((hA.add hB).sub hC).sub hD).sub hE |>.add hF
    simpa only [Work.Diff.EXT.kosGen] using hsum.const_mul (1 / 2 : ℝ)
  -- ### Step 3: the entries of the inverse Gram matrix are continuous in `t`
  have hentry : ∀ i j : Fin (Module.finrank ℝ E),
      Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M ↦ Work.Diff.EXT.gramM (I := I) (G p.1) x p.2 i j) t₀ x := by
    intro i j
    have h := Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJ hG ht₀
      (hfr i) (hfr j)
    simpa only [Work.Diff.EXT.gramM, Matrix.of_apply] using h
  -- the whole matrix family `t ↦ Gram(t)` is continuous at `t₀`
  have hgmat : ContinuousAt (fun t : ℝ ↦ fun i j ↦
      Work.Diff.EXT.gramM (I := I) (G t) x x i j) t₀ := by
    rw [continuousAt_pi]
    intro i
    rw [continuousAt_pi]
    intro j
    have h1 : ContinuousAt ((fun p : ℝ × M ↦
        Work.Diff.EXT.gramM (I := I) (G p.1) x p.2 i j)
          ∘ (fun t : ℝ ↦ (t, x))) t₀ :=
      (hentry i j).continuousAt.tendsto.comp hpair.tendsto
    simpa only [Function.comp_def] using h1
  -- the Gram matrix of the coordinate frame is invertible
  have hdet : (Matrix.of (fun i j ↦ Work.Diff.EXT.gramM (I := I) (G t₀) x x i j)).det ≠ 0 := by
    have h := Work.Diff.EXT.gramM_det_ne_zero (I := I) (G t₀) x
    simpa only [Work.Diff.EXT.gramM, Matrix.of_apply] using h
  -- the entries of the inverse depend `C^∞` on the entries of the matrix, and continuously on `t`
  have hMinv : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousAt (fun t : ℝ ↦
        ((Matrix.of (fun i j ↦ Work.Diff.EXT.gramM (I := I) (G t) x x i j))⁻¹) a b) t₀ := by
    intro a b
    have hF0 := Work.Diff.EXT.contDiffAt_matrix_inv_pi
      (fun i j ↦ Work.Diff.EXT.gramM (I := I) (G t₀) x x i j) hdet
    have hF : ContDiffAt ℝ ∞
        (fun A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ ↦ (Matrix.of A)⁻¹ a b)
        (fun i j ↦ Work.Diff.EXT.gramM (I := I) (G t₀) x x i j) := by
      simpa only [Function.comp_def] using
        (contDiff_apply_apply ℝ ℝ a b).contDiffAt.comp _ hF0
    have hc : ContinuousAt ((fun A : Fin (Module.finrank ℝ E) →
          Fin (Module.finrank ℝ E) → ℝ ↦ (Matrix.of A)⁻¹ a b)
          ∘ (fun t : ℝ ↦ fun i j ↦ Work.Diff.EXT.gramM (I := I) (G t) x x i j)) t₀ :=
      hF.continuousAt.comp hgmat
    simpa only [Function.comp_def] using hc
  -- ### Step 4: assemble
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      ContinuousAt (fun t : ℝ ↦
        ((Matrix.of (fun a b ↦ Work.Diff.EXT.gramM (I := I) (G t) x x a b))⁻¹) j i *
        Work.Diff.EXT.kosGen (I := I) G Xdir Z (Work.Diff.EXT.fr (I := I) x i) t x) t₀ :=
    fun i ↦ (hMinv j i).mul (hkos i)
  have hcont : ContinuousAt (fun t : ℝ ↦ ∑ i : Fin (Module.finrank ℝ E),
      ((Matrix.of (fun a b ↦ Work.Diff.EXT.gramM (I := I) (G t) x x a b))⁻¹) j i *
        Work.Diff.EXT.kosGen (I := I) G Xdir Z (Work.Diff.EXT.fr (I := I) x i) t x) t₀ := by
    exact tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun i _ ↦ (hterm i).tendsto)
  have heq : (fun t : ℝ ↦ Work.Diff.EXT.reconCoef (I := I) G x Xdir Z j t x)
      = (fun t : ℝ ↦ ∑ i : Fin (Module.finrank ℝ E),
          ((Matrix.of (fun a b ↦ Work.Diff.EXT.gramM (I := I) (G t) x x a b))⁻¹) j i *
            Work.Diff.EXT.kosGen (I := I) G Xdir Z (Work.Diff.EXT.fr (I := I) x i) t x) := by
    funext t
    simp only [Work.Diff.EXT.reconCoef, Matrix.mulVec, dotProduct, Work.Diff.EXT.gramM,
      Matrix.of_apply]
  rw [heq]
  exact hcont

end Work.Diff.GE
