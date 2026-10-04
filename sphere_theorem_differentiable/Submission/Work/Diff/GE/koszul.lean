import Submission.Work.Diff.GE.deps
import Submission.Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Koszul formula for the coordinate frame of a chart

For a smooth metric `g` on `M` the Levi-Civita connection is determined by the Koszul formula

`2 ⟨∇_X Y, Z⟩ = X⟨Y,Z⟩ + Y⟨Z,X⟩ - Z⟨X,Y⟩ - ⟨Y,[X,Z]⟩ - ⟨Z,[Y,X]⟩ + ⟨X,[Z,Y]⟩`.

In the coordinate frame `σ_i y = frameVector x₀ y (bb i)` of the chart at `x₀` the Lie brackets
vanish (`Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth`), hence for
every `(t, y)` with `y` in the chart

`⟨∇_{σ_a}σ_b, σ_c⟩ = ½ (∂_a G_{bc} + ∂_b G_{ac} - ∂_c G_{ab})`

(`fPair_eq` below), where `∂_a` is the derivative in the coordinate direction `a` (`dOp`).  This is
the pointwise input for the coordinate formula of the curvature components `rmC4`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic

namespace Work.Diff.GE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The coordinate-frame metric components are symmetric. -/
theorem mComp_comm (G : ℝ → SMet I M) (x₀ : M) (i j : Fin (Module.finrank ℝ E))
    (t : ℝ) (y : M) : mComp (I := I) G x₀ i j t y = mComp (I := I) G x₀ j i t y := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  show Inner.inner ℝ (cFrame (I := I) x₀ i y) (cFrame (I := I) x₀ j y)
      = Inner.inner ℝ (cFrame (I := I) x₀ j y) (cFrame (I := I) x₀ i y)
  exact real_inner_comm _ _

/-- **Koszul in the coordinate frame.**  The Christoffel pairings of the Levi-Civita connection of
`G t` in the coordinate frame are first derivatives of the metric components (written here in the
fully unfolded form, which is the form produced by `dOp`/`mComp`). -/
theorem fPair_eq (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (a b c : Fin (Module.finrank ℝ E)) :
    fPair (I := I) G x₀ a b c t y
      = (1 / 2) * (mvfderiv I (fun y' : M ↦ (G t).inner y'
              (cFrame (I := I) x₀ b y') (cFrame (I := I) x₀ c y')) y (cFrame (I := I) x₀ a y)
          + mvfderiv I (fun y' : M ↦ (G t).inner y'
              (cFrame (I := I) x₀ c y') (cFrame (I := I) x₀ a y')) y (cFrame (I := I) x₀ b y)
          - mvfderiv I (fun y' : M ↦ (G t).inner y'
              (cFrame (I := I) x₀ a y') (cFrame (I := I) x₀ b y')) y (cFrame (I := I) x₀ c y)) := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hl := CovariantDerivative.leviCivitaConnection_apply_inner (I := I) (M := M)
      (X := frameSection (I := I) x₀ (cBasis (E := E) a))
      (Y := frameSection (I := I) x₀ (cBasis (E := E) b))
      (Z := frameSection (I := I) x₀ (cBasis (E := E) c))
      (mdiffAt_frameSection x₀ (cBasis (E := E) a) hy)
      (mdiffAt_frameSection x₀ (cBasis (E := E) b) hy)
      (mdiffAt_frameSection x₀ (cBasis (E := E) c) hy)
  have hbr1 : mlieBracket I (frameSection (I := I) x₀ (cBasis (E := E) a))
      (frameSection (I := I) x₀ (cBasis (E := E) c)) y = 0 :=
    Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth
      (I := I) x₀ _ _ hy
  have hbr2 : mlieBracket I (frameSection (I := I) x₀ (cBasis (E := E) b))
      (frameSection (I := I) x₀ (cBasis (E := E) a)) y = 0 :=
    Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth
      (I := I) x₀ _ _ hy
  have hbr3 : mlieBracket I (frameSection (I := I) x₀ (cBasis (E := E) c))
      (frameSection (I := I) x₀ (cBasis (E := E) b)) y = 0 :=
    Commons.Geometry.Manifold.VectorField.mlieBracket_trivializationAt_symmL_smooth
      (I := I) x₀ _ _ hy
  simp only [hbr1, hbr2, hbr3, inner_zero_right, sub_zero, add_zero] at hl
  have hinn : ∀ (y' : M) (u v : TangentSpace I y'), Inner.inner ℝ u v = (G t).inner y' u v :=
    fun _ _ _ => rfl
  have hlc : (lcOf (G t)) = CovariantDerivative.leviCivitaConnection I M := rfl
  simpa only [fPair, cFrame, cBasis, frameSection, frameVector, hlc,
    div_eq_inv_mul, one_div, mul_one, hinn] using hl

/-- The Koszul expression `koszulPair` is the coordinate Christoffel pairing `fPair`. -/
theorem fPair_eq_koszul (G : ℝ → SMet I M) (x₀ : M) (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (a b c : Fin (Module.finrank ℝ E)) :
    fPair (I := I) G x₀ a b c t y = koszulPair (I := I) G x₀ a b c t y := by
  rw [fPair_eq G x₀ t hy a b c]
  rfl

end Work.Diff.GE
