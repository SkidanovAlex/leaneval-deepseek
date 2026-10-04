import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.EXT.ricCore
import Submission.Work.Diff.EXT.ricDeps
import Submission.Work.Diff.EXT.contDiffAt_chartMat_of_jointSmooth
import Submission.Work.Diff.EXT.eq_sum_frameVector_of_pairing
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.koszul
import Submission.Work.Diff.GE.cGram_chrB_eq_koszulPair

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic Submission.ChartCurv
open Work.Diff.GE

namespace Work.Diff.EXT

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ## The Koszul formula for the Levi-Civita connection of an explicit metric -/

omit [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- **Koszul formula** for `lcOf g`, written with the explicit bilinear form `g.inner`, with the
smoothness hypotheses only at the point `x`.  This is Mathlib's
`CovariantDerivative.leviCivitaConnection_apply_inner`, transported along the definitional
identifications `lcOf g = leviCivitaConnection I M` and `inner ℝ = g.inner` that hold once the
Riemannian bundle instance of `g` is installed.  The local form is what the coordinate frame of a
chart (smooth only on the chart) requires. -/
theorem lcOf_pairing_at (g : SMet I M) (X Y Z : Π y : M, TangentSpace I y) (x : M)
    (hX : SmoothFieldAt I M X x) (hY : SmoothFieldAt I M Y x) (hZ : SmoothFieldAt I M Z x) :
    g.inner x (lcOf g Y x (X x)) (Z x) =
      (1 / 2 : ℝ) * (mvfderiv I (fun y : M => g.inner y (Y y) (Z y)) x (X x)
        + mvfderiv I (fun y : M => g.inner y (Z y) (X y)) x (Y x)
        - mvfderiv I (fun y : M => g.inner y (X y) (Y y)) x (Z x)
        - g.inner x (Y x) (mlieBracket I X Z x)
        - g.inner x (Z x) (mlieBracket I Y X x)
        + g.inner x (X x) (mlieBracket I Z Y x)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hinner : ∀ (y : M) (u v : TangentSpace I y), inner ℝ u v = g.inner y u v :=
    fun y u v => rfl
  have hYZ : (fun y : M => inner ℝ (Y y) (Z y)) = (fun y : M => g.inner y (Y y) (Z y)) := rfl
  have hZX : (fun y : M => inner ℝ (Z y) (X y)) = (fun y : M => g.inner y (Z y) (X y)) := rfl
  have hXY : (fun y : M => inner ℝ (X y) (Y y)) = (fun y : M => g.inner y (X y) (Y y)) := rfl
  have h := CovariantDerivative.leviCivitaConnection_apply_inner (I := I) (M := M)
    (X := X) (Y := Y) (Z := Z) (x := x) ((hX.mdifferentiableAt (by simp)))
    ((hY.mdifferentiableAt (by simp))) ((hZ.mdifferentiableAt (by simp)))
  rw [hYZ, hZX, hXY] at h
  simpa [lcOf, hinner, mvfderiv, div_eq_mul_inv, mul_comm] using h

/-! ## The coordinate frame of the chart at the base point -/

section Frame

variable (x : M)

/-- The `i`-th coordinate frame vector of the chart at `x`, evaluated at `x`, is the basis vector. -/
lemma cFrame_self (i : Fin (Module.finrank ℝ E)) :
    cFrame (I := I) x i x = cBasis (E := E) i := by
  exact Submission.Gauss.frameVector_self x (cBasis (E := E) i)

/-- The coordinate frame vector of the chart at `x` is a smooth section at `x`. -/
lemma smoothFieldAt_cFrame (i : Fin (Module.finrank ℝ E)) :
    SmoothFieldAt I M (cFrame (I := I) x i) x := by
  have h := contMDiffAt_frameVector (I := I) x (cBasis (E := E) i) (mem_chart_source H x)
  simp only [cFrame, frameSection_eq_frameVector, frameVector, SmoothFieldAt]
  exact h

/-- Coordinate frame vectors have vanishing Lie bracket. -/
lemma mlieBracket_cFrame_cFrame (i k : Fin (Module.finrank ℝ E)) :
    mlieBracket I (cFrame (I := I) x i) (cFrame (I := I) x k) x = 0 := by
  have h := Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth
    (I := I) x (cBasis (E := E) i) (cBasis (E := E) k) (mem_chart_source H x)
  simp only [cFrame, frameSection_eq_frameVector, frameVector]
  exact h

end Frame

/-! ## The Koszul pairing of the chart frame -/

section Koszul

/-- The Koszul pairing of `∇_{Xdir} Z` with the `k`-th coordinate frame vector, as an explicit
function of `(t, y)`: the right-hand side of the Koszul formula. -/
noncomputable def kos (G : ℝ → SMet I M) (x : M) (Xdir Z : Π y : M, TangentSpace I y)
    (k : Fin (Module.finrank ℝ E)) (t : ℝ) (y : M) : ℝ :=
  (1 / 2 : ℝ) * (mvfderiv I (fun y' : M => (G t).inner y' (Z y') (cFrame (I := I) x k y'))
      y (Xdir y)
    + mvfderiv I (fun y' : M => (G t).inner y' (cFrame (I := I) x k y') (Xdir y')) y (Z y)
    - mvfderiv I (fun y' : M => (G t).inner y' (Xdir y') (Z y')) y (cFrame (I := I) x k y)
    - (G t).inner y (Z y) (mlieBracket I Xdir (cFrame (I := I) x k) y)
    - (G t).inner y (cFrame (I := I) x k y) (mlieBracket I Z Xdir y)
    + (G t).inner y (Xdir y) (mlieBracket I (cFrame (I := I) x k) Z y))

/-- **The pointwise Koszul identity for the chart frame.**  For `y` in the chart at `x` and
sections `Xdir`, `Z` smooth at `y`, the pairing of `∇_{Xdir} Z` with the `k`-th coordinate frame
vector is the explicit function `kos`. -/
lemma lcOf_pairing_eq_kos (G : ℝ → SMet I M) (x : M) (Xdir Z : Π y : M, TangentSpace I y)
    (t : ℝ) {y : M} (hy : y ∈ (chartAt H x).source)
    (hX : CMDiffAt ∞ (T% Xdir) y) (hZ : CMDiffAt ∞ (T% Z) y)
    (k : Fin (Module.finrank ℝ E)) :
    (G t).inner y (lcOf (G t) Z y (Xdir y)) (cFrame (I := I) x k y)
      = kos (I := I) G x Xdir Z k t y := by
  have hk : SmoothFieldAt I M (cFrame (I := I) x k) y := by
    have h := contMDiffAt_frameVector (I := I) x (cBasis (E := E) k) hy
    simp only [SmoothFieldAt, cFrame, frameSection_eq_frameVector, frameVector]
    exact h
  have h := lcOf_pairing_at (I := I) (G t) Xdir Z (cFrame (I := I) x k) y
    (by simpa [SmoothFieldAt] using hX) (by simpa [SmoothFieldAt] using hZ) hk
  simpa [kos] using h

end Koszul


omit [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The Koszul expression for the pairing of `∇_{Xdir} Z` with an arbitrary test field `Test`. -/
noncomputable def kosGen (G : ℝ → SMet I M) (Xdir Z Test : Π y : M, TangentSpace I y)
    (t : ℝ) (y : M) : ℝ :=
  (1 / 2 : ℝ) * (mvfderiv I (fun y' : M => (G t).inner y' (Z y') (Test y')) y (Xdir y)
    + mvfderiv I (fun y' : M => (G t).inner y' (Test y') (Xdir y')) y (Z y)
    - mvfderiv I (fun y' : M => (G t).inner y' (Xdir y') (Z y')) y (Test y)
    - (G t).inner y (Z y) (mlieBracket I Xdir Test y)
    - (G t).inner y (Test y) (mlieBracket I Z Xdir y)
    + (G t).inner y (Xdir y) (mlieBracket I Test Z y))

omit [I.Boundaryless] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- **The pointwise Koszul identity, general test field.** -/
lemma lcOf_pairing_eq_kosGen (G : ℝ → SMet I M) (Xdir Z Test : Π y : M, TangentSpace I y)
    (t : ℝ) {y : M} (hX : CMDiffAt ∞ (T% Xdir) y) (hZ : CMDiffAt ∞ (T% Z) y)
    (hT : CMDiffAt ∞ (T% Test) y) :
    (G t).inner y (lcOf (G t) Z y (Xdir y)) (Test y) = kosGen (I := I) G Xdir Z Test t y := by
  have h := lcOf_pairing_at (I := I) (G t) Xdir Z Test y
    (by simpa [SmoothFieldAt] using hX) (by simpa [SmoothFieldAt] using hZ)
    (by simpa [SmoothFieldAt] using hT)
  simpa [kosGen] using h

/-- `kos` is the special case of `kosGen` with the `k`-th coordinate frame as test field. -/
lemma kos_eq_kosGen (G : ℝ → SMet I M) (x : M) (Xdir Z : Π y : M, TangentSpace I y)
    (k : Fin (Module.finrank ℝ E)) (t : ℝ) (y : M) :
    kos (I := I) G x Xdir Z k t y
      = kosGen (I := I) G Xdir Z (cFrame (I := I) x k) t y := rfl

end

end Work.Diff.EXT
