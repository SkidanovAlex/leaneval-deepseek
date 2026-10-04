import Mathlib
import Submission.Work.Diff.Evol.Vocab
import Submission.Work.Diff.GE.smooth_onframe
import Submission.Work.Diff.GE.onFrameONfield
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame
import Submission.Work.Diff.Evol.gsNorm_contMDiffAt_of_smoothAt
import Submission.Work.Diff.Evol.isONFrame_sum_smul
import Submission.Work.Diff.Evol.sum_inner_mul_inner_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# An orthonormal frame on a chart, with prescribed value at the centre

`Work.Diff.Evol.onframe_chart`: given a smooth Riemannian metric `g` on a smooth manifold `M`, a
point `x` and a `g`-orthonormal frame `e` of `T_xM`, there is a family of tangent fields `F i`
which is `C^∞` on the chart source of `x`, is `g`-orthonormal at every point of that source, and
takes the prescribed values `e i` at `x`.

Construction: take the coordinate frame `fr i` of the chart at `x`
(`(trivializationAt E (TangentSpace I) x).symmL ℝ · (b i)`, a basis of `T_yM` for every `y` in the
chart source, `Work.Diff.GE.Pieces.coordframe_li`), orthonormalise it pointwise by Gram–Schmidt
(`Work.Diff.GE.gsNorm`, `Work.Diff.GE.isONFrame_gsNorm`); by
`Work.Diff.Evol.gsNorm_contMDiffAt_of_smoothAt` the result is `C^∞` at every point of the chart
source, where all coefficients of the Gram–Schmidt recursion are defined (the chart frame is a
basis there).  This produces a smooth orthonormal frame `B` on the whole chart source; it does not
take the prescribed value at `x`, so it is corrected by the constant matrix
`Q i j = g.inner x (e i) (B j x)`: since both `B · x` and `e` are orthonormal frames, `Q` is
orthogonal (`Work.Diff.Evol.sum_inner_mul_inner_eq`), so `F i = ∑ j Q i j • B j` is still
orthonormal (`Work.Diff.Evol.isONFrame_sum_smul`) and smooth, while
`F i x = ∑ j g.inner x (e i) (B j x) • B j x = e i` by the expansion of a vector in an orthonormal
frame (`Work.EXT.sum_inner_smul_eq_self_of_isONFrame`).
-/

namespace Work.Diff.Evol

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

theorem onframe_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : Submission.Diff.IsONFrame g x e) :
    ∃ F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, F i x = e i) ∧
      (∀ i, ContMDiffOn I I.tangent (((⊤ : ℕ∞) : WithTop ℕ∞))
              (fun y : M => Bundle.TotalSpace.mk' E y (F i y)) (chartAt H x).source) ∧
      (∀ y ∈ (chartAt H x).source, Submission.Diff.IsONFrame g y (fun i => F i y)) := by
  classical
  -- the coordinate frame of the chart at `x`
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  let fr : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun i y => (trivializationAt E (TangentSpace I) x).symmL ℝ y (b i)
  have hfr_at : ∀ (i : Fin (Module.finrank ℝ E)) (y : M), y ∈ (chartAt H x).source →
      CMDiffAt ∞ (T% (fr i)) y := by
    intro i y hy
    exact Work.Diff.GE.coordFrame_contMDiffAt (I := I) (M := M) x (b i) hy
  have hfr_li : ∀ y ∈ (chartAt H x).source,
      LinearIndependent ℝ (fun j : Fin (Module.finrank ℝ E) => fr j y) :=
    fun y hy => Work.Diff.GE.Pieces.coordframe_li (I := I) (M := M) x b hy
  -- Gram–Schmidt orthonormalisation of the coordinate frame
  let B : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun i => Work.Diff.GE.gsNorm g fr i
  have hB_at : ∀ (i : Fin (Module.finrank ℝ E)) (y : M), y ∈ (chartAt H x).source →
      CMDiffAt ∞ (T% (B i)) y :=
    fun i y hy => gsNorm_contMDiffAt_of_smoothAt (I := I) (M := M) g fr y
      (fun j => hfr_at j y hy) i (hfr_li y hy)
  have hB_on : ∀ y ∈ (chartAt H x).source, Submission.Diff.IsONFrame g y (fun i => B i y) :=
    fun y hy => Work.Diff.GE.isONFrame_gsNorm (g := g) (F := fr) (y := y) (hfr_li y hy)
  have hBx : Submission.Diff.IsONFrame g x (fun j => B j x) := hB_on x (mem_chart_source H x)
  -- the change-of-frame matrix
  have hQ0 : ∀ i k, (∑ j, (g.inner x (e i) (B j x)) * (g.inner x (e k) (B j x))) =
      if i = k then 1 else 0 := by
    intro i k
    rw [sum_inner_mul_inner_eq (I := I) (M := M) g x (fun j => B j x) hBx e i k]
    exact he i k
  let Q : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => g.inner x (e i) (B j x)
  have hQ : ∀ i k, ∑ j, Q i j * Q k j = if i = k then 1 else 0 := fun i k => hQ0 i k
  let F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun i y => ∑ j, Q i j • B j y
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    exact Work.EXT.sum_inner_smul_eq_self_of_isONFrame (I := I) (M := M) g x
      (fun j => B j x) hBx (e i)
  · intro i
    refine fun y hy => ?_
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        CMDiffAt ∞ (T% (fun z : M => Q i j • B j z)) y :=
      fun j _ => (contMDiffAt_const (c := Q i j)).smul_section (hB_at j y hy)
    have hsum : CMDiffAt ∞ (T% (fun z : M => ∑ j, Q i j • B j z)) y :=
      ContMDiffAt.sum_section (s := Finset.univ) hterm
    exact hsum.contMDiffWithinAt
  · intro y hy
    exact isONFrame_sum_smul (I := I) (M := M) g y (fun j => B j y) (hB_on y hy) Q hQ

end Work.Diff.Evol
