import ChallengeDeps
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_second_along_fields
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff
import Submission.Commons.Analysis.InnerProductSpace.inner_gram_basis_change
import Submission.Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
import Submission.Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq
import Submission.Commons.LinearAlgebra.exists_basis_change_of_span_eq
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
import Submission.Commons.Geometry.Manifold.VectorField.mlieBracket_cyclic_sum

/-!
# Algebraic curvature identities for the sphere-theorem setup

The trusted file `ChallengeDeps` defines, for a smooth manifold `M` carrying a
covariant derivative `cov` on its tangent bundle, the Riemann curvature tensor

    curv cov X Y Z := ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z .

This module opens the (still missing) Riemannian-geometry library needed for the
topological sphere theorem by establishing the first algebraic identities of that
tensor directly from the raw definition.

Nothing in the first three lemmas needs smoothness of the fields or
metric-compatibility: they are pure pointwise algebra of the covariant derivative
(ℝ-linearity in the direction) and antisymmetry of the manifold Lie bracket.
The last lemma (`torsion_zero_bracket`) records torsion-freeness as the classical
identity `∇_X Y - ∇_Y X = [X,Y]` on smooth fields, which is how torsion-freeness
enters every subsequent computation with `curv`.

These statements are local to this challenge because they are about the trusted
definition `LeanEval.Geometry.SphereTheorem.curv`.  Once Mathlib grows its own
Riemann curvature tensor (with the same definition), the same facts should be
lifted to the shared commons.

## Status note (project-wide)

The target theorem `sphere_theorem` is the genuine Berger–Klingenberg–Rauch
topological sphere theorem.  Its proof needs the full curvature-comparison
chapter (geodesics and the exponential map for this covariant derivative,
Klingenberg's injectivity-radius estimate, Toponogov triangle comparison,
Rauch comparison) and the topological recognition of a two-disk decomposition
as a sphere — none of which exists anywhere in Mathlib at the pinned revision.
This file is the first, purely algebraic step of that development.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField
open Commons.Geometry.Manifold.VectorBundle.CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.Curvature

/-- `R(X,Y)Z = - R(Y,X)Z`: the curvature tensor of any connection is skew-symmetric
in its first two slots.  Pure algebra from the definition, the antisymmetry of the
Lie bracket, and ℝ-linearity of the covariant derivative in the direction. -/
lemma curv_antisymm
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (X Y Z : Π x : M, TangentSpace I x) :
    curv cov X Y Z = - curv cov Y X Z := by
  funext x
  unfold curv
  simp only [Pi.neg_apply]
  rw [VectorField.mlieBracket_swap_apply]
  rw [map_neg]
  abel

/-- Pointwise version of `curv_antisymm`. -/
lemma curv_antisymm_apply
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    curv cov X Y Z x = - curv cov Y X Z x :=
  congrFun (curv_antisymm cov X Y Z) x

/-- `R(X,X)Z = 0`, a direct consequence of skew-symmetry (the tangent spaces are real
vector spaces, hence have no 2-torsion). -/
lemma curv_self_zero
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (X Z : Π x : M, TangentSpace I x) :
    curv cov X X Z = 0 := by
  funext x
  have hx := curv_antisymm_apply cov X X Z x
  have hvv : curv cov X X Z x + curv cov X X Z x = 0 := by
    simpa using (congrArg (fun w : TangentSpace I x => w + curv cov X X Z x) hx)
  have hv : (2 : ℝ) • (curv cov X X Z x) = 0 := by
    simpa [two_smul] using hvv
  exact (smul_eq_zero.mp hv).resolve_left (by norm_num)

/-- Torsion-freeness as the classical bracket identity `∇_X Y - ∇_Y X = [X,Y]`
(equality of sections), for smooth fields.  This is the form in which the
hypothesis `cov.torsion = 0` enters computations with `curv`. -/
lemma torsion_zero_bracket
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (htor : cov.torsion = 0) {X Y : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) :
    (fun x => cov Y x (X x) - cov X x (Y x)) = mlieBracket I X Y := by
  funext x
  have hX' : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY' : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  exact (CovariantDerivative.torsion_eq_zero_iff (𝕜 := ℝ) (E := E) (I := I) (M := M) cov).mp
    htor hX' hY'

/-- From metric compatibility with `Y = Z = Z`: for any smooth section `Z` and any direction
vector `v`, `d⟨Z,Z⟩(v) = 2⟨∇_v Z, Z⟩`.  Equivalently `⟨∇_V Z, Z⟩ = ½ V⟨Z,Z⟩`, the identity
that starts the proof that the curvature endomorphism `R(X,Y)` is skew-adjoint. -/
lemma hmet_inner_self_along
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov)
    {Z X : Π x : M, TangentSpace I x} (hZ : CMDiff ∞ (T% Z)) (x : M) :
    mvfderiv I (fun y : M => inner ℝ (Z y) (Z y)) x (X x) =
      2 * inner ℝ (cov Z x (X x)) (Z x) := by
  have h := hmet Z Z hZ hZ x (X x)
  linarith [h, real_inner_comm (Z x) (cov Z x (X x))]

/-- `curv` is additive in its third (section) slot, for smooth sections.  This uses
smoothness of the connection to know that the sections `∇_Y Z₁`, `∇_Y Z₂`, ... are
differentiable, which is what the additivity axiom of a covariant derivative requires. -/
lemma curv_add_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (X Y Z₁ Z₂ : Π x : M, TangentSpace I x)
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ₁ : CMDiff ∞ (T% Z₁)) (hZ₂ : CMDiff ∞ (T% Z₂)) :
    curv cov X Y (Z₁ + Z₂) = curv cov X Y Z₁ + curv cov X Y Z₂ := by
  funext x
  unfold curv
  have hcovadd (y : M) : cov (Z₁ + Z₂) y = cov Z₁ y + cov Z₂ y :=
    cov.isCovariantDerivativeOn.add
      ((hZ₁ y).mdifferentiableAt (by simp)) ((hZ₂ y).mdifferentiableAt (by simp))
  have hcovadd_apply (y : M) (v : TangentSpace I y) :
      cov (Z₁ + Z₂) y v = cov Z₁ y v + cov Z₂ y v := by
    simpa using congrArg (fun L : TangentSpace I y →L[ℝ] TangentSpace I y => L v) (hcovadd y)
  have hsectY : (fun y => cov (Z₁ + Z₂) y (Y y)) = fun y => cov Z₁ y (Y y) + cov Z₂ y (Y y) := by
    funext y; exact hcovadd_apply y (Y y)
  have hsectX : (fun y => cov (Z₁ + Z₂) y (X y)) = fun y => cov Z₁ y (X y) + cov Z₂ y (X y) := by
    funext y; exact hcovadd_apply y (X y)
  rw [hsectY, hsectX]
  have hζ₁ : CMDiff ∞ (T% (fun y : M => cov Z₁ y (Y y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov (Z := Z₁) (Y := Y) hZ₁ hY
  have hζ₂ : CMDiff ∞ (T% (fun y : M => cov Z₂ y (Y y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov (Z := Z₂) (Y := Y) hZ₂ hY
  have hζX₁ : CMDiff ∞ (T% (fun y : M => cov Z₁ y (X y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov (Z := Z₁) (Y := X) hZ₁ hX
  have hζX₂ : CMDiff ∞ (T% (fun y : M => cov Z₂ y (X y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov (Z := Z₂) (Y := X) hZ₂ hX
  have hc1 : cov (fun y => cov Z₁ y (Y y) + cov Z₂ y (Y y)) x =
      cov (fun y => cov Z₁ y (Y y)) x + cov (fun y => cov Z₂ y (Y y)) x :=
    cov.isCovariantDerivativeOn.add ((hζ₁ x).mdifferentiableAt (by simp))
      ((hζ₂ x).mdifferentiableAt (by simp))
  have hc2 : cov (fun y => cov Z₁ y (X y) + cov Z₂ y (X y)) x =
      cov (fun y => cov Z₁ y (X y)) x + cov (fun y => cov Z₂ y (X y)) x :=
    cov.isCovariantDerivativeOn.add ((hζX₁ x).mdifferentiableAt (by simp))
      ((hζX₂ x).mdifferentiableAt (by simp))
  have hc3 : cov (Z₁ + Z₂) x = cov Z₁ x + cov Z₂ x := hcovadd x
  simp only [hc1, hc2, hc3, add_apply, Pi.add_apply]
  abel

/-- **Skew-adjointness, self form.**  For a metric-compatible connection, the curvature
endomorphism `R(X,Y)` is skew-adjoint, hence in particular `⟨R(X,Y)Z, Z⟩ = 0`.  This is
the second-derivative core of the Riemannian curvature algebra: the proof expands the
inner products with metric compatibility and reduces to the identity
`X(Y⟨Z,Z⟩) - Y(X⟨Z,Z⟩) = [X,Y]⟨Z,Z⟩` (`mvfderiv_second_along_fields`). -/
lemma curv_inner_self_zero
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmet : IsMetricCompatible cov)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    inner ℝ (curv cov X Y Z x) (Z x) = 0 := by
  have hζY : CMDiff ∞ (T% (fun y : M => cov Z y (Y y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov (Z := Z) (Y := Y) hZ hY
  have hζX : CMDiff ∞ (T% (fun y : M => cov Z y (X y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov (Z := Z) (Y := X) hZ hX
  have hg : CMDiff ∞ (fun y : M => inner ℝ (Z y) (Z y)) :=
    ContMDiff.inner_bundle (F := E) (E := (fun x : M => TangentSpace I x)) (b := (id : M → M))
      (v := Z) (w := Z) hZ hZ
  have hhY : CMDiff ∞ (fun y : M => inner ℝ ((fun y : M => cov Z y (Y y)) y) (Z y)) :=
    ContMDiff.inner_bundle (F := E) (E := (fun x : M => TangentSpace I x)) (b := (id : M → M))
      (v := fun y : M => cov Z y (Y y)) (w := Z) hζY hZ
  have hhX : CMDiff ∞ (fun y : M => inner ℝ ((fun y : M => cov Z y (X y)) y) (Z y)) :=
    ContMDiff.inner_bundle (F := E) (E := (fun x : M => TangentSpace I x)) (b := (id : M → M))
      (v := fun y : M => cov Z y (X y)) (w := Z) hζX hZ
  have hmet1 := hmet (fun y : M => cov Z y (Y y)) Z hζY hZ x (X x)
  have hmet2 := hmet (fun y : M => cov Z y (X y)) Z hζX hZ x (Y x)
  have hmet3 : mvfderiv I (fun y : M => inner ℝ (Z y) (Z y)) x (mlieBracket I X Y x)
      = 2 * inner ℝ (cov Z x (mlieBracket I X Y x)) (Z x) :=
    hmet_inner_self_along cov hmet hZ x
  have hA := mvfderiv_second_along_fields (I := I)
    (f := fun y : M => inner ℝ (Z y) (Z y)) (X := X) (Y := Y) (x := x) hg hX hY
  have hF1 : (fun y : M => mvfderiv I (fun y : M => inner ℝ (Z y) (Z y)) y (Y y))
      = (fun y : M => 2 * inner ℝ (cov Z y (Y y)) (Z y)) := by
    funext y
    exact hmet_inner_self_along cov hmet hZ y
  have hF2 : (fun y : M => mvfderiv I (fun y : M => inner ℝ (Z y) (Z y)) y (X y))
      = (fun y : M => 2 * inner ℝ (cov Z y (X y)) (Z y)) := by
    funext y
    exact hmet_inner_self_along cov hmet hZ y
  have hcross : inner ℝ ((fun y : M => cov Z y (Y y)) x) ((fun y : M => cov Z y (X y)) x)
      = inner ℝ ((fun y : M => cov Z y (X y)) x) ((fun y : M => cov Z y (Y y)) x) :=
    real_inner_comm _ _
  have hD1 : mvfderiv I (fun y : M => mvfderiv I (fun y : M => inner ℝ (Z y) (Z y)) y (Y y)) x (X x)
      = 2 * mvfderiv I (fun y : M => inner ℝ (cov Z y (Y y)) (Z y)) x (X x) := by
    rw [hF1]
    rw [show (fun y : M => 2 * inner ℝ (cov Z y (Y y)) (Z y))
        = (fun _ : M => (2 : ℝ)) * (fun y : M => inner ℝ (cov Z y (Y y)) (Z y)) from by
      funext y; rw [Pi.mul_apply]]
    rw [mvfderiv_mul (x := x) mdifferentiableAt_const ((hhY x).mdifferentiableAt (by simp)),
      mvfderiv_const]
    simp [smul_apply, smul_eq_mul]
  have hD2 : mvfderiv I (fun y : M => mvfderiv I (fun y : M => inner ℝ (Z y) (Z y)) y (X y)) x (Y x)
      = 2 * mvfderiv I (fun y : M => inner ℝ (cov Z y (X y)) (Z y)) x (Y x) := by
    rw [hF2]
    rw [show (fun y : M => 2 * inner ℝ (cov Z y (X y)) (Z y))
        = (fun _ : M => (2 : ℝ)) * (fun y : M => inner ℝ (cov Z y (X y)) (Z y)) from by
      funext y; rw [Pi.mul_apply]]
    rw [mvfderiv_mul (x := x) mdifferentiableAt_const ((hhX x).mdifferentiableAt (by simp)),
      mvfderiv_const]
    simp [smul_apply, smul_eq_mul]
  unfold curv
  rw [inner_sub_left, inner_sub_left]
  linarith [hmet1, hmet2, hmet3, hA, hD1, hD2, hcross]

/-- **Skew-adjointness of the curvature operator, bilinear form.**  For a metric-compatible
connection `cov`, `⟨R(X,Y)Z, W⟩ = -⟨Z, R(X,Y)W⟩`: the curvature endomorphism `R(X,Y)` is
skew-adjoint for the Riemannian metric.  This is obtained from the self-form
`curv_inner_self_zero` applied to `Z + W` together with additivity `curv_add_right`.

Together with `curv_antisymm` this makes the curvature a genuine curvature tensor of a
Riemannian metric; it is the form in which metric compatibility is used in all
comparison-geometry arguments (and in making sectional curvature well defined). -/
lemma curv_inner_skew
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmet : IsMetricCompatible cov)
    {X Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (hW : CMDiff ∞ (T% W)) :
    inner ℝ (curv cov X Y Z x) (W x) = - inner ℝ (Z x) (curv cov X Y W x) := by
  have hZW : CMDiff ∞ (T% (Z + W)) := hZ.add_section hW
  have h0 := curv_inner_self_zero cov hcov hmet hX hY hZW (x := x)
  rw [curv_add_right cov hcov X Y Z W hX hY hZ hW] at h0
  simp only [Pi.add_apply, inner_add_left, inner_add_right] at h0
  have hZ0 := curv_inner_self_zero cov hcov hmet hX hY hZ (x := x)
  have hW0 := curv_inner_self_zero cov hcov hmet hX hY hW (x := x)
  linarith [h0, hZ0, hW0, real_inner_comm (Z x) (curv cov X Y W x)]

/-- `curv` is additive in its first slot. -/
lemma curv_add_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (X₁ X₂ Y Z : Π x : M, TangentSpace I x)
    (hX₁ : CMDiff ∞ (T% X₁)) (hX₂ : CMDiff ∞ (T% X₂))
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    curv cov (X₁ + X₂) Y Z = curv cov X₁ Y Z + curv cov X₂ Y Z := by
  funext x
  unfold curv
  have hζX₁Z : CMDiff ∞ (T% (fun y : M => cov Z y (X₁ y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hX₁
  have hζX₂Z : CMDiff ∞ (T% (fun y : M => cov Z y (X₂ y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hX₂
  have hsect : (fun y : M => cov Z y ((X₁ + X₂) y))
      = (fun y : M => cov Z y (X₁ y)) + (fun y : M => cov Z y (X₂ y)) := by
    funext y
    simp only [Pi.add_apply, map_add]
  have hsum : cov ((fun y : M => cov Z y (X₁ y)) + (fun y : M => cov Z y (X₂ y))) x
      = cov (fun y : M => cov Z y (X₁ y)) x + cov (fun y : M => cov Z y (X₂ y)) x :=
    cov.isCovariantDerivativeOn.add ((hζX₁Z x).mdifferentiableAt (by simp))
      ((hζX₂Z x).mdifferentiableAt (by simp))
  have hbr : mlieBracket I (X₁ + X₂) Y x = mlieBracket I X₁ Y x + mlieBracket I X₂ Y x :=
    mlieBracket_add_left ((hX₁ x).mdifferentiableAt (by simp)) ((hX₂ x).mdifferentiableAt (by simp))
  have hbr' : cov Z x (mlieBracket I (X₁ + X₂) Y x)
      = cov Z x (mlieBracket I X₁ Y x) + cov Z x (mlieBracket I X₂ Y x) := by
    rw [hbr, map_add]
  have hlin : cov (fun y : M => cov Z y (Y y)) x ((X₁ + X₂) x)
      = cov (fun y : M => cov Z y (Y y)) x (X₁ x) + cov (fun y : M => cov Z y (Y y)) x (X₂ x) := by
    rw [show (X₁ + X₂) x = X₁ x + X₂ x from rfl, map_add]
  rw [hlin, hsect, hsum, hbr']
  simp only [Pi.add_apply, add_apply]
  abel

/-- `curv` is additive in its second slot. -/
lemma curv_add_middle
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (X Y₁ Y₂ Z : Π x : M, TangentSpace I x)
    (hX : CMDiff ∞ (T% X)) (hY₁ : CMDiff ∞ (T% Y₁)) (hY₂ : CMDiff ∞ (T% Y₂))
    (hZ : CMDiff ∞ (T% Z)) :
    curv cov X (Y₁ + Y₂) Z = curv cov X Y₁ Z + curv cov X Y₂ Z := by
  funext x
  unfold curv
  have hζY₁Z : CMDiff ∞ (T% (fun y : M => cov Z y (Y₁ y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hY₁
  have hζY₂Z : CMDiff ∞ (T% (fun y : M => cov Z y (Y₂ y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hY₂
  have hsect : (fun y : M => cov Z y ((Y₁ + Y₂) y))
      = (fun y : M => cov Z y (Y₁ y)) + (fun y : M => cov Z y (Y₂ y)) := by
    funext y
    simp only [Pi.add_apply, map_add]
  have hsum : cov ((fun y : M => cov Z y (Y₁ y)) + (fun y : M => cov Z y (Y₂ y))) x
      = cov (fun y : M => cov Z y (Y₁ y)) x + cov (fun y : M => cov Z y (Y₂ y)) x :=
    cov.isCovariantDerivativeOn.add ((hζY₁Z x).mdifferentiableAt (by simp))
      ((hζY₂Z x).mdifferentiableAt (by simp))
  have hbr : mlieBracket I X (Y₁ + Y₂) x = mlieBracket I X Y₁ x + mlieBracket I X Y₂ x :=
    mlieBracket_add_right ((hY₁ x).mdifferentiableAt (by simp)) ((hY₂ x).mdifferentiableAt (by simp))
  have hbr' : cov Z x (mlieBracket I X (Y₁ + Y₂) x)
      = cov Z x (mlieBracket I X Y₁ x) + cov Z x (mlieBracket I X Y₂ x) := by
    rw [hbr, map_add]
  have hlin : cov (fun y : M => cov Z y (X y)) x ((Y₁ + Y₂) x)
      = cov (fun y : M => cov Z y (X y)) x (Y₁ x) + cov (fun y : M => cov Z y (X y)) x (Y₂ x) := by
    rw [show (Y₁ + Y₂) x = Y₁ x + Y₂ x from rfl, map_add]
  rw [hsect, hsum, hlin, hbr']
  simp only [Pi.add_apply, add_apply]
  abel

/-- **First Bianchi identity.**  For a torsion-free connection,
`R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`.

The proof rewrites each curvature term using torsion-freeness `∇_A B - ∇_B A = [A,B]`
applied both to the inner sections `∇_A B` and to the pairs `(A, [B,C])`, reducing the
cyclic sum to the cyclic Jacobi identity `[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0`. -/
lemma curv_bianchi
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (htor : cov.torsion = 0)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    curv cov X Y Z x + curv cov Y Z X x + curv cov Z X Y x = 0 := by
  have mb : ∀ {A B : Π x : M, TangentSpace I x}, CMDiff ∞ (T% A) → CMDiff ∞ (T% B) →
      CMDiff ∞ (T% (mlieBracket I A B)) := by
    intro A B hA hB
    haveI : IsManifold I (minSmoothness ℝ 2) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    haveI : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
      have h : (∞ : ℕ∞ω) + 1 = ∞ := by simp
      rw [h]; infer_instance
    intro y
    exact (hA y).mlieBracket_vectorField (hB y) (by simp)
  have hbYZ : CMDiff ∞ (T% (mlieBracket I Y Z)) := mb hY hZ
  have hbZX : CMDiff ∞ (T% (mlieBracket I Z X)) := mb hZ hX
  have hbXY : CMDiff ∞ (T% (mlieBracket I X Y)) := mb hX hY
  have hSYZ : CMDiff ∞ (T% (fun y : M => cov Z y (Y y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hY
  have hSXZ : CMDiff ∞ (T% (fun y : M => cov Z y (X y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hX
  have hSZX : CMDiff ∞ (T% (fun y : M => cov X y (Z y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hX hZ
  have hSYX : CMDiff ∞ (T% (fun y : M => cov X y (Y y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hX hY
  have hSXY : CMDiff ∞ (T% (fun y : M => cov Y y (X y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hY hX
  have hSZY : CMDiff ∞ (T% (fun y : M => cov Y y (Z y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hY hZ
  have tYZ : (fun y : M => cov Z y (Y y) - cov Y y (Z y)) = mlieBracket I Y Z :=
    torsion_zero_bracket cov htor hY hZ
  have tZX : (fun y : M => cov X y (Z y) - cov Z y (X y)) = mlieBracket I Z X :=
    torsion_zero_bracket cov htor hZ hX
  have tXY : (fun y : M => cov Y y (X y) - cov X y (Y y)) = mlieBracket I X Y :=
    torsion_zero_bracket cov htor hX hY
  have e1 : cov (fun y : M => cov Z y (Y y)) x (X x)
      = cov (fun y : M => cov Y y (Z y)) x (X x) + cov (mlieBracket I Y Z) x (X x) := by
    have h1 : (fun y : M => cov Z y (Y y)) = (fun y : M => cov Y y (Z y)) + mlieBracket I Y Z := by
      funext y
      simp only [Pi.add_apply]
      exact sub_eq_iff_eq_add'.mp (congrFun tYZ y)
    rw [h1]
    rw [cov.isCovariantDerivativeOn.add ((hSZY x).mdifferentiableAt (by simp))
      ((hbYZ x).mdifferentiableAt (by simp))]
    simp
  have e3 : cov (fun y : M => cov X y (Z y)) x (Y x)
      = cov (fun y : M => cov Z y (X y)) x (Y x) + cov (mlieBracket I Z X) x (Y x) := by
    have h1 : (fun y : M => cov X y (Z y)) = (fun y : M => cov Z y (X y)) + mlieBracket I Z X := by
      funext y
      simp only [Pi.add_apply]
      exact sub_eq_iff_eq_add'.mp (congrFun tZX y)
    rw [h1]
    rw [cov.isCovariantDerivativeOn.add ((hSXZ x).mdifferentiableAt (by simp))
      ((hbZX x).mdifferentiableAt (by simp))]
    simp
  have e5 : cov (fun y : M => cov Y y (X y)) x (Z x)
      = cov (fun y : M => cov X y (Y y)) x (Z x) + cov (mlieBracket I X Y) x (Z x) := by
    have h1 : (fun y : M => cov Y y (X y)) = (fun y : M => cov X y (Y y)) + mlieBracket I X Y := by
      funext y
      simp only [Pi.add_apply]
      exact sub_eq_iff_eq_add'.mp (congrFun tXY y)
    rw [h1]
    rw [cov.isCovariantDerivativeOn.add ((hSYX x).mdifferentiableAt (by simp))
      ((hbXY x).mdifferentiableAt (by simp))]
    simp
  have e6 : cov (mlieBracket I Y Z) x (X x)
      = cov X x (mlieBracket I Y Z x) + mlieBracket I X (mlieBracket I Y Z) x := by
    have t : (fun y : M => cov (mlieBracket I Y Z) y (X y) - cov X y (mlieBracket I Y Z y))
        = mlieBracket I X (mlieBracket I Y Z) := torsion_zero_bracket cov htor hX hbYZ
    exact sub_eq_iff_eq_add'.mp (congrFun t x)
  have e7 : cov (mlieBracket I Z X) x (Y x)
      = cov Y x (mlieBracket I Z X x) + mlieBracket I Y (mlieBracket I Z X) x := by
    have t : (fun y : M => cov (mlieBracket I Z X) y (Y y) - cov Y y (mlieBracket I Z X y))
        = mlieBracket I Y (mlieBracket I Z X) := torsion_zero_bracket cov htor hY hbZX
    exact sub_eq_iff_eq_add'.mp (congrFun t x)
  have e8 : cov (mlieBracket I X Y) x (Z x)
      = cov Z x (mlieBracket I X Y x) + mlieBracket I Z (mlieBracket I X Y) x := by
    have t : (fun y : M => cov (mlieBracket I X Y) y (Z y) - cov Z y (mlieBracket I X Y y))
        = mlieBracket I Z (mlieBracket I X Y) := torsion_zero_bracket cov htor hZ hbXY
    exact sub_eq_iff_eq_add'.mp (congrFun t x)
  have hjac : mlieBracket I X (mlieBracket I Y Z) x + mlieBracket I Y (mlieBracket I Z X) x
      + mlieBracket I Z (mlieBracket I X Y) x = 0 := by
    have hX2 : CMDiff (minSmoothness ℝ 2) (T% X) :=
      hX.of_le (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
    have hY2 : CMDiff (minSmoothness ℝ 2) (T% Y) :=
      hY.of_le (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
    have hZ2 : CMDiff (minSmoothness ℝ 2) (T% Z) :=
      hZ.of_le (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
    exact congrFun (mlieBracket_cyclic_sum hX2 hY2 hZ2) x
  unfold curv
  rw [e1, e3, e5, e6, e7, e8]
  abel_nf at hjac ⊢
  exact hjac

/-- **Tensoriality in the first slot**: `R(fX, Y)Z = f R(X,Y)Z`.

This (and its two companions below) is what makes `R(X,Y)Z` depend only on the values
`X x, Y x, Z x`: the curvature is a tensor, not just a trilinear differential operator. -/
lemma curv_smul_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (f : M → ℝ) (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hf : CMDiff ∞ f) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    curv cov (f • X) Y Z x = f x • curv cov X Y Z x := by
  unfold curv
  have hζXZ : CMDiff ∞ (T% (fun y : M => cov Z y (X y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hX
  have h1 : cov (fun y : M => cov Z y (Y y)) x ((f • X) x)
      = f x • cov (fun y : M => cov Z y (Y y)) x (X x) := by
    rw [show (f • X) x = f x • X x from rfl, map_smul]
  have hsect : (fun y : M => cov Z y ((f • X) y)) = f • (fun y : M => cov Z y (X y)) := by
    funext y
    rw [show (f • X) y = f y • X y from rfl, map_smul]
    rfl
  have h2 : cov (fun y : M => cov Z y ((f • X) y)) x (Y x)
      = f x • cov (fun y : M => cov Z y (X y)) x (Y x)
        + (mvfderiv I f x (Y x)) • (cov Z x (X x)) := by
    rw [hsect]
    have hL := cov.isCovariantDerivativeOn.leibniz (σ := fun y : M => cov Z y (X y))
      ((hζXZ x).mdifferentiableAt (by simp)) ((hf x).mdifferentiableAt (by simp))
    have hL' := congrArg (fun (L : TangentSpace I x →L[ℝ] TangentSpace I x) => L (Y x)) hL
    rw [hL']
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have h3 : cov Z x (mlieBracket I (f • X) Y x)
      = f x • cov Z x (mlieBracket I X Y x) - (mvfderiv I f x (Y x)) • (cov Z x (X x)) := by
    rw [mlieBracket_smul_left ((hf x).mdifferentiableAt (by simp))
      ((hX x).mdifferentiableAt (by simp))]
    rw [map_add, map_smul, map_smul]
    module
  rw [h1, h2, h3]
  simp only [smul_sub]
  module

/-- **Tensoriality in the second slot**: `R(X, fY)Z = f R(X,Y)Z`. -/
lemma curv_smul_middle
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (f : M → ℝ) (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hf : CMDiff ∞ f) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    curv cov X (f • Y) Z x = f x • curv cov X Y Z x := by
  unfold curv
  have hζYZ : CMDiff ∞ (T% (fun y : M => cov Z y (Y y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hY
  have hsect : (fun y : M => cov Z y ((f • Y) y)) = f • (fun y : M => cov Z y (Y y)) := by
    funext y
    rw [show (f • Y) y = f y • Y y from rfl, map_smul]
    rfl
  have h1 : cov (fun y : M => cov Z y ((f • Y) y)) x (X x)
      = f x • cov (fun y : M => cov Z y (Y y)) x (X x)
        + (mvfderiv I f x (X x)) • (cov Z x (Y x)) := by
    rw [hsect]
    have hL := cov.isCovariantDerivativeOn.leibniz (σ := fun y : M => cov Z y (Y y))
      ((hζYZ x).mdifferentiableAt (by simp)) ((hf x).mdifferentiableAt (by simp))
    have hL' := congrArg (fun (L : TangentSpace I x →L[ℝ] TangentSpace I x) => L (X x)) hL
    rw [hL']
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  have h2 : cov (fun y : M => cov Z y (X y)) x ((f • Y) x)
      = f x • cov (fun y : M => cov Z y (X y)) x (Y x) := by
    rw [show (f • Y) x = f x • Y x from rfl, map_smul]
  have h3 : cov Z x (mlieBracket I X (f • Y) x)
      = f x • cov Z x (mlieBracket I X Y x)
        + (mvfderiv I f x (X x)) • (cov Z x (Y x)) := by
    rw [mlieBracket_smul_right ((hf x).mdifferentiableAt (by simp))
      ((hY x).mdifferentiableAt (by simp))]
    rw [map_add, map_smul, map_smul]
    module
  rw [h1, h2, h3]
  simp only [smul_sub]
  module

/-- **Tensoriality in the third slot**: `R(X,Y)(fZ) = f R(X,Y)Z`. -/
lemma curv_smul_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (f : M → ℝ) (X Y Z : Π x : M, TangentSpace I x) (x : M)
    (hf : CMDiff ∞ f) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    curv cov X Y (f • Z) x = f x • curv cov X Y Z x := by
  unfold curv
  have hζYZ : CMDiff ∞ (T% (fun y : M => cov Z y (Y y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hY
  have hζXZ : CMDiff ∞ (T% (fun y : M => cov Z y (X y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hX
  have hYf : CMDiff ∞ (fun y : M => mvfderiv I f y (Y y)) :=
    mvfderiv_apply_contMDiff (I := I) hf hY
  have hXf : CMDiff ∞ (fun y : M => mvfderiv I f y (X y)) :=
    mvfderiv_apply_contMDiff (I := I) hf hX
  -- section identity for the first term
  have hsectY : (fun y : M => cov (f • Z) y (Y y))
      = f • (fun y : M => cov Z y (Y y)) + (fun y : M => mvfderiv I f y (Y y)) • Z := by
    funext y
    rw [cov.isCovariantDerivativeOn.leibniz (σ := Z) ((hZ y).mdifferentiableAt (by simp))
      ((hf y).mdifferentiableAt (by simp))]
    rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rfl
  have hsectX : (fun y : M => cov (f • Z) y (X y))
      = f • (fun y : M => cov Z y (X y)) + (fun y : M => mvfderiv I f y (X y)) • Z := by
    funext y
    rw [cov.isCovariantDerivativeOn.leibniz (σ := Z) ((hZ y).mdifferentiableAt (by simp))
      ((hf y).mdifferentiableAt (by simp))]
    rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rfl
  -- first curvature term
  have hT1 : cov (fun y : M => cov (f • Z) y (Y y)) x (X x)
      = (f x • cov (fun y : M => cov Z y (Y y)) x (X x)
          + (mvfderiv I f x (X x)) • (cov Z x (Y x)))
        + ((mvfderiv I f x (Y x)) • (cov Z x (X x))
          + (mvfderiv I (fun y : M => mvfderiv I f y (Y y)) x (X x)) • (Z x)) := by
    rw [hsectY]
    rw [cov.isCovariantDerivativeOn.add
      ((hf.smul_section hζYZ x).mdifferentiableAt (by simp))
      ((hYf.smul_section hZ x).mdifferentiableAt (by simp))]
    have hL1 := cov.isCovariantDerivativeOn.leibniz (σ := fun y : M => cov Z y (Y y))
      ((hζYZ x).mdifferentiableAt (by simp)) ((hf x).mdifferentiableAt (by simp))
    have hL2 := cov.isCovariantDerivativeOn.leibniz (σ := Z)
      ((hZ x).mdifferentiableAt (by simp)) ((hYf x).mdifferentiableAt (by simp))
    rw [show (cov (f • fun y => cov Z y (Y y)) x + cov ((fun y => mvfderiv I f y (Y y)) • Z) x) (X x)
        = (cov (f • fun y => cov Z y (Y y)) x) (X x)
          + (cov ((fun y => mvfderiv I f y (Y y)) • Z) x) (X x) from by rw [add_apply]]
    rw [show (cov (f • fun y => cov Z y (Y y)) x) (X x) = _ from congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (X x)) hL1,
        show (cov ((fun y => mvfderiv I f y (Y y)) • Z) x) (X x) = _ from congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (X x)) hL2]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  -- second curvature term
  have hT2 : cov (fun y : M => cov (f • Z) y (X y)) x (Y x)
      = (f x • cov (fun y : M => cov Z y (X y)) x (Y x)
          + (mvfderiv I f x (Y x)) • (cov Z x (X x)))
        + ((mvfderiv I f x (X x)) • (cov Z x (Y x))
          + (mvfderiv I (fun y : M => mvfderiv I f y (X y)) x (Y x)) • (Z x)) := by
    rw [hsectX]
    rw [cov.isCovariantDerivativeOn.add
      ((hf.smul_section hζXZ x).mdifferentiableAt (by simp))
      ((hXf.smul_section hZ x).mdifferentiableAt (by simp))]
    have hL1 := cov.isCovariantDerivativeOn.leibniz (σ := fun y : M => cov Z y (X y))
      ((hζXZ x).mdifferentiableAt (by simp)) ((hf x).mdifferentiableAt (by simp))
    have hL2 := cov.isCovariantDerivativeOn.leibniz (σ := Z)
      ((hZ x).mdifferentiableAt (by simp)) ((hXf x).mdifferentiableAt (by simp))
    rw [show (cov (f • fun y => cov Z y (X y)) x + cov ((fun y => mvfderiv I f y (X y)) • Z) x) (Y x)
        = (cov (f • fun y => cov Z y (X y)) x) (Y x)
          + (cov ((fun y => mvfderiv I f y (X y)) • Z) x) (Y x) from by rw [add_apply]]
    rw [show (cov (f • fun y => cov Z y (X y)) x) (Y x) = _ from congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (Y x)) hL1,
        show (cov ((fun y => mvfderiv I f y (X y)) • Z) x) (Y x) = _ from congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (Y x)) hL2]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  -- third curvature term
  have hT3 : cov (f • Z) x (mlieBracket I X Y x)
      = f x • (cov Z x (mlieBracket I X Y x))
        + (mvfderiv I f x (mlieBracket I X Y x)) • (Z x) := by
    have hL := cov.isCovariantDerivativeOn.leibniz (σ := Z)
      ((hZ x).mdifferentiableAt (by simp)) ((hf x).mdifferentiableAt (by simp))
    rw [show (cov (f • Z) x) (mlieBracket I X Y x) = _ from congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L (mlieBracket I X Y x)) hL]
    rw [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  -- the second-derivative identity for the scalar function f
  have hbrF : mvfderiv I (fun y : M => mvfderiv I f y (Y y)) x (X x)
      = mvfderiv I (fun y : M => mvfderiv I f y (X y)) x (Y x)
        + mvfderiv I f x (mlieBracket I X Y x) :=
    mvfderiv_second_along_fields (I := I) hf hX hY
  rw [hT1, hT2, hT3]
  rw [hbrF, add_smul]
  module


/-- **Germ reduction, X slot (vanishing form)**: if the section `X` vanishes
near `x`, then `R(X,Y)Z x = 0`.  (This is the germ statement behind value-dependence: `curv`
is insensitive to what the fields do away from the point.) -/
lemma curv_eq_zero_of_eventuallyEq_zero_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hX0 : X =ᶠ[𝓝 x] 0) :
    curv cov X Y Z x = 0 := by
  -- smoothness of the zero section
  have hzeroMD : MDiffAt (T% (0 : Π x : M, TangentSpace I x)) x :=
    (Bundle.contMDiffAt_zeroSection (IB := I) (F := E)
      (E := fun x : M => TangentSpace I x) (𝕜 := ℝ) (n := ∞) (x := x)).mdifferentiableAt (by simp)
  unfold curv
  have hXx : X x = 0 := hX0.eq_of_nhds
  have h1 : cov (fun y : M => cov Z y (Y y)) x (X x) = 0 := by rw [hXx, map_zero]
  have hζXZ : CMDiff ∞ (T% (fun y : M => cov Z y (X y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hX
  have hsect0 : (fun y : M => cov Z y (X y)) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hX0] with y hy
    rw [hy]
    exact map_zero (cov Z y)
  have h2 : cov (fun y : M => cov Z y (X y)) x (Y x) = 0 := by
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq ((hζXZ x).mdifferentiableAt (by simp))
      hzeroMD Filter.univ_mem hsect0]
    simp
  have h3 : cov Z x (mlieBracket I X Y x) = 0 := by
    have hb : mlieBracket I X Y x = mlieBracket I (0 : Π x : M, TangentSpace I x) Y x :=
      hX0.mlieBracket_vectorField_eq (Filter.EventuallyEq.refl (𝓝 x) Y)
    rw [hb]
    simp only [mlieBracket_zero_left, Pi.zero_apply, map_zero]
  rw [h1, h2, h3]
  abel

/-- **Germ reduction, Y slot (vanishing form)**: if the section `Y` vanishes
near `x`, then `R(X,Y)Z x = 0`.  (This is the germ statement behind value-dependence: `curv`
is insensitive to what the fields do away from the point.) -/
lemma curv_eq_zero_of_eventuallyEq_zero_middle
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hY0 : Y =ᶠ[𝓝 x] 0) :
    curv cov X Y Z x = 0 := by
  have hzeroMD : MDiffAt (T% (0 : Π x : M, TangentSpace I x)) x :=
    (Bundle.contMDiffAt_zeroSection (IB := I) (F := E)
      (E := fun x : M => TangentSpace I x) (𝕜 := ℝ) (n := ∞) (x := x)).mdifferentiableAt (by simp)
  unfold curv
  have hζYZ : CMDiff ∞ (T% (fun y : M => cov Z y (Y y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hY
  have hsect0 : (fun y : M => cov Z y (Y y)) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hY0] with y hy
    rw [hy]
    exact map_zero (cov Z y)
  have h1 : cov (fun y : M => cov Z y (Y y)) x (X x) = 0 := by
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq ((hζYZ x).mdifferentiableAt (by simp))
      hzeroMD Filter.univ_mem hsect0]
    simp
  have hYx : Y x = 0 := hY0.eq_of_nhds
  have h2 : cov (fun y : M => cov Z y (X y)) x (Y x) = 0 := by rw [hYx, map_zero]
  have h3 : cov Z x (mlieBracket I X Y x) = 0 := by
    have hb : mlieBracket I X Y x = mlieBracket I X (0 : Π x : M, TangentSpace I x) x :=
      (Filter.EventuallyEq.refl (𝓝 x) X).mlieBracket_vectorField_eq hY0
    rw [hb]
    simp only [mlieBracket_zero_right, Pi.zero_apply, map_zero]
  rw [h1, h2, h3]
  abel

/-- **Germ reduction, Z slot (vanishing form)**: if the section `Z` vanishes
near `x`, then `R(X,Y)Z x = 0`.  (This is the germ statement behind value-dependence: `curv`
is insensitive to what the fields do away from the point.) -/
lemma curv_eq_zero_of_eventuallyEq_zero_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hZ0 : Z =ᶠ[𝓝 x] 0) :
    curv cov X Y Z x = 0 := by
  have hzeroMD : MDiffAt (T% (0 : Π x : M, TangentSpace I x)) x :=
    (Bundle.contMDiffAt_zeroSection (IB := I) (F := E)
      (E := fun x : M => TangentSpace I x) (𝕜 := ℝ) (n := ∞) (x := x)).mdifferentiableAt (by simp)
  have hzeroS : CMDiff ∞ (T% (0 : Π x : M, TangentSpace I x)) := by
    intro y
    exact Bundle.contMDiffAt_zeroSection (IB := I) (F := E)
      (E := fun x : M => TangentSpace I x) (𝕜 := ℝ) (n := ∞) (x := y)
  have hcovgerm : ∀ᶠ y in 𝓝 x, cov Z y = cov (0 : Π x : M, TangentSpace I x) y := by
    filter_upwards [hZ0.eventuallyEq_nhds] with y hy
    exact cov.isCovariantDerivativeOn.congr_of_eventuallyEq ((hZ y).mdifferentiableAt (by simp))
      ((hzeroS y).mdifferentiableAt (by simp)) Filter.univ_mem hy
  unfold curv
  have hζYZ : CMDiff ∞ (T% (fun y : M => cov Z y (Y y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hY
  have hζXZ : CMDiff ∞ (T% (fun y : M => cov Z y (X y))) :=
    contMDiff_cov_apply (E := E) (H := H) (I := I) (M := M) cov hcov hZ hX
  have hsect1 : (fun y : M => cov Z y (Y y)) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hcovgerm] with y hy
    have h0 : cov (0 : Π x : M, TangentSpace I x) y
        = (0 : TangentSpace I y →L[ℝ] TangentSpace I y) :=
      congrFun (CovariantDerivative.zero cov) y
    rw [hy, h0]
    exact zero_apply (Y y)
  have h1 : cov (fun y : M => cov Z y (Y y)) x (X x) = 0 := by
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq ((hζYZ x).mdifferentiableAt (by simp))
      hzeroMD Filter.univ_mem hsect1]
    simp
  have hsect2 : (fun y : M => cov Z y (X y)) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hcovgerm] with y hy
    have h0 : cov (0 : Π x : M, TangentSpace I x) y
        = (0 : TangentSpace I y →L[ℝ] TangentSpace I y) :=
      congrFun (CovariantDerivative.zero cov) y
    rw [hy, h0]
    exact zero_apply (X y)
  have h2 : cov (fun y : M => cov Z y (X y)) x (Y x) = 0 := by
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq ((hζXZ x).mdifferentiableAt (by simp))
      hzeroMD Filter.univ_mem hsect2]
    simp
  have h3 : cov Z x (mlieBracket I X Y x) = 0 := by
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq ((hZ x).mdifferentiableAt (by simp))
      hzeroMD Filter.univ_mem hZ0]
    simp
  rw [h1, h2, h3]
  abel


/-- **Germ reduction, first slot (equality form)**: if `X` and `X'` agree near `x` then
`R(X,Y)Z x = R(X',Y)Z x`.  Derived from the vanishing form and additivity. -/
lemma curv_eq_of_eventuallyEq_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X X' Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hX' : CMDiff ∞ (T% X'))
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (h : X =ᶠ[𝓝 x] X') :
    curv cov X Y Z x = curv cov X' Y Z x := by
  have hsub : (X - X') =ᶠ[𝓝 x] (0 : Π x : M, TangentSpace I x) := by
    filter_upwards [h] with y hy
    show X y - X' y = (0 : TangentSpace I y)
    rw [hy, sub_self]
  have hh := curv_eq_zero_of_eventuallyEq_zero_left cov hcov (hX.sub_section hX') hY hZ hsub (x := x)
  have hadd := curv_add_left cov hcov (X - X') X' Y Z (hX.sub_section hX') hX' hY hZ
  rw [show (X - X') + X' = X from by
        funext y
        show (X - X') y + X' y = X y
        rw [show (X - X') y = X y - X' y from rfl]
        abel] at hadd
  have hsum : curv cov X Y Z x = curv cov (X - X') Y Z x + curv cov X' Y Z x := by
    simpa [Pi.add_apply] using congrFun hadd x
  rw [hsum, hh, zero_add]

/-- **Germ reduction, second slot (equality form)**: `Y =ᶠ Y'` near `x` gives
`R(X,Y)Z x = R(X,Y')Z x`. -/
lemma curv_eq_of_eventuallyEq_middle
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Y' Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y'))
    (hZ : CMDiff ∞ (T% Z))
    (h : Y =ᶠ[𝓝 x] Y') :
    curv cov X Y Z x = curv cov X Y' Z x := by
  have hsub : (Y - Y') =ᶠ[𝓝 x] (0 : Π x : M, TangentSpace I x) := by
    filter_upwards [h] with y hy
    show Y y - Y' y = (0 : TangentSpace I y)
    rw [hy, sub_self]
  have hh := curv_eq_zero_of_eventuallyEq_zero_middle cov hcov hX (hY.sub_section hY') hZ hsub (x := x)
  have hadd := curv_add_middle cov hcov X (Y - Y') Y' Z hX (hY.sub_section hY') hY' hZ
  rw [show (Y - Y') + Y' = Y from by
        funext y
        show (Y - Y') y + Y' y = Y y
        rw [show (Y - Y') y = Y y - Y' y from rfl]
        abel] at hadd
  have hsum : curv cov X Y Z x = curv cov X (Y - Y') Z x + curv cov X Y' Z x := by
    simpa [Pi.add_apply] using congrFun hadd x
  rw [hsum, hh, zero_add]

/-- **Germ reduction, third slot (equality form)**: `Z =ᶠ Z'` near `x` gives
`R(X,Y)Z x = R(X,Y)Z' x`. -/
lemma curv_eq_of_eventuallyEq_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z Z' : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (hZ' : CMDiff ∞ (T% Z'))
    (h : Z =ᶠ[𝓝 x] Z') :
    curv cov X Y Z x = curv cov X Y Z' x := by
  have hsub : (Z - Z') =ᶠ[𝓝 x] (0 : Π x : M, TangentSpace I x) := by
    filter_upwards [h] with y hy
    show Z y - Z' y = (0 : TangentSpace I y)
    rw [hy, sub_self]
  have hh := curv_eq_zero_of_eventuallyEq_zero_right cov hcov hX hY (hZ.sub_section hZ') hsub (x := x)
  have hadd := curv_add_right cov hcov X Y (Z - Z') Z' hX hY (hZ.sub_section hZ') hZ'
  rw [show (Z - Z') + Z' = Z from by
        funext y
        show (Z - Z') y + Z' y = Z y
        rw [show (Z - Z') y = Z y - Z' y from rfl]
        abel] at hadd
  have hsum : curv cov X Y Z x = curv cov X Y (Z - Z') x + curv cov X Y Z' x := by
    simpa [Pi.add_apply] using congrFun hadd x
  rw [hsum, hh, zero_add]

/-- The curvature vanishes when the first argument is the zero field; from additivity. -/
lemma curv_zero_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (Y Z : Π x : M, TangentSpace I x) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) :
    curv cov 0 Y Z = 0 := by
  have h0 : CMDiff ∞ (T% (0 : Π x : M, TangentSpace I x)) := by
    intro y
    exact Bundle.contMDiffAt_zeroSection (IB := I) (F := E)
      (E := fun x : M => TangentSpace I x) (𝕜 := ℝ) (n := ∞) (x := y)
  have hadd := curv_add_left cov hcov (0 : Π x : M, TangentSpace I x) 0 Y Z h0 h0 hY hZ
  have h00 : (0 : Π x : M, TangentSpace I x) + 0 = 0 := by
    funext x; simp
  rw [h00] at hadd
  have h1 : curv cov 0 Y Z + curv cov 0 Y Z = curv cov 0 Y Z + 0 := by
    rw [← hadd, add_zero]
  exact add_left_cancel h1
/-- Finite linearity in the first slot: `R(∑ f_i Y_i, Y)Z = ∑ f_i R(Y_i, Y)Z`. -/
lemma curv_sum_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (Y' : ι → Π x : M, TangentSpace I x)
    (Y Z : Π x : M, TangentSpace I x)
    (hf : ∀ i ∈ s, CMDiff ∞ (f i)) (hY' : ∀ i ∈ s, CMDiff ∞ (T% (Y' i)))
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    curv cov (∑ i ∈ s, f i • Y' i) Y Z x = ∑ i ∈ s, (f i x) • curv cov (Y' i) Y Z x := by
  classical
  revert hf hY'
  induction s using Finset.induction_on with
  | empty =>
    intro hf hY'
    have h := congrFun (curv_zero_left cov hcov Y Z hY hZ) x
    simpa using h
  | insert j s hjs ih =>
    intro hf hY'
    have hfj : CMDiff ∞ (f j) := hf j (Finset.mem_insert_self j s)
    have hY'j : CMDiff ∞ (T% (Y' j)) := hY' j (Finset.mem_insert_self j s)
    have hfs : ∀ i ∈ s, CMDiff ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hY's : ∀ i ∈ s, CMDiff ∞ (T% (Y' i)) := fun i hi => hY' i (Finset.mem_insert_of_mem hi)
    have hsum : CMDiff ∞ (T% (∑ i ∈ s, f i • Y' i)) := by
      simpa using (ContMDiff.sum_section (fun i hi => (hfs i hi).smul_section (hY's i hi)))
    rw [Finset.sum_insert hjs, Finset.sum_insert hjs]
    have hadd := congrFun (curv_add_left cov hcov (f j • Y' j) (∑ i ∈ s, f i • Y' i) Y Z
      (hfj.smul_section hY'j) hsum hY hZ) x
    rw [show curv cov (f j • Y' j + ∑ i ∈ s, f i • Y' i) Y Z x
        = curv cov (f j • Y' j) Y Z x + curv cov (∑ i ∈ s, f i • Y' i) Y Z x from by
      simpa [Pi.add_apply] using hadd]
    rw [curv_smul_left cov hcov (f j) (Y' j) Y Z x hfj hY'j hY hZ, ih hfs hY's]
/-- The curvature vanishes when the second argument is the zero field; from additivity. -/
lemma curv_zero_middle
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (X Z : Π x : M, TangentSpace I x) (hX : CMDiff ∞ (T% X)) (hZ : CMDiff ∞ (T% Z)) :
    curv cov X 0 Z = 0 := by
  have h0 : CMDiff ∞ (T% (0 : Π x : M, TangentSpace I x)) := by
    intro y
    exact Bundle.contMDiffAt_zeroSection (IB := I) (F := E)
      (E := fun x : M => TangentSpace I x) (𝕜 := ℝ) (n := ∞) (x := y)
  have hadd := curv_add_middle cov hcov X 0 0 Z hX h0 h0 hZ
  have h00 : (0 : Π x : M, TangentSpace I x) + 0 = 0 := by funext x; simp
  rw [h00] at hadd
  have h1 : curv cov X 0 Z + curv cov X 0 Z = curv cov X 0 Z + 0 := by
    rw [← hadd, add_zero]
  exact add_left_cancel h1
/-- Finite linearity in the second slot. -/
lemma curv_sum_middle
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (Y' : ι → Π x : M, TangentSpace I x)
    (X Z : Π x : M, TangentSpace I x)
    (hf : ∀ i ∈ s, CMDiff ∞ (f i)) (hY' : ∀ i ∈ s, CMDiff ∞ (T% (Y' i)))
    (hX : CMDiff ∞ (T% X)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    curv cov X (∑ i ∈ s, f i • Y' i) Z x = ∑ i ∈ s, (f i x) • curv cov X (Y' i) Z x := by
  classical
  revert hf hY'
  induction s using Finset.induction_on with
  | empty =>
    intro hf hY'
    have h := congrFun (curv_zero_middle cov hcov X Z hX hZ) x
    simpa using h
  | insert j s hjs ih =>
    intro hf hY'
    have hfj : CMDiff ∞ (f j) := hf j (Finset.mem_insert_self j s)
    have hY'j : CMDiff ∞ (T% (Y' j)) := hY' j (Finset.mem_insert_self j s)
    have hfs : ∀ i ∈ s, CMDiff ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hY's : ∀ i ∈ s, CMDiff ∞ (T% (Y' i)) := fun i hi => hY' i (Finset.mem_insert_of_mem hi)
    have hsum : CMDiff ∞ (T% (∑ i ∈ s, f i • Y' i)) := by
      simpa using (ContMDiff.sum_section (fun i hi => (hfs i hi).smul_section (hY's i hi)))
    rw [Finset.sum_insert hjs, Finset.sum_insert hjs]
    have hadd := congrFun (curv_add_middle cov hcov X (f j • Y' j) (∑ i ∈ s, f i • Y' i) Z
      hX (hfj.smul_section hY'j) hsum hZ) x
    rw [show curv cov X (f j • Y' j + ∑ i ∈ s, f i • Y' i) Z x
        = curv cov X (f j • Y' j) Z x + curv cov X (∑ i ∈ s, f i • Y' i) Z x from by
      simpa [Pi.add_apply] using hadd]
    rw [curv_smul_middle cov hcov (f j) X (Y' j) Z x hfj hX hY'j hZ, ih hfs hY's]
/-- The curvature vanishes when the third argument is the zero field; from additivity. -/
lemma curv_zero_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    (X Y : Π x : M, TangentSpace I x) (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) :
    curv cov X Y 0 = 0 := by
  have h0 : CMDiff ∞ (T% (0 : Π x : M, TangentSpace I x)) := by
    intro y
    exact Bundle.contMDiffAt_zeroSection (IB := I) (F := E)
      (E := fun x : M => TangentSpace I x) (𝕜 := ℝ) (n := ∞) (x := y)
  have hadd := curv_add_right cov hcov X Y 0 0 hX hY h0 h0
  have h00 : (0 : Π x : M, TangentSpace I x) + 0 = 0 := by funext x; simp
  rw [h00] at hadd
  have h1 : curv cov X Y 0 + curv cov X Y 0 = curv cov X Y 0 + 0 := by
    rw [← hadd, add_zero]
  exact add_left_cancel h1
/-- Finite linearity in the third slot. -/
lemma curv_sum_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (Y' : ι → Π x : M, TangentSpace I x)
    (X Y : Π x : M, TangentSpace I x)
    (hf : ∀ i ∈ s, CMDiff ∞ (f i)) (hY' : ∀ i ∈ s, CMDiff ∞ (T% (Y' i)))
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (x : M) :
    curv cov X Y (∑ i ∈ s, f i • Y' i) x = ∑ i ∈ s, (f i x) • curv cov X Y (Y' i) x := by
  classical
  revert hf hY'
  induction s using Finset.induction_on with
  | empty =>
    intro hf hY'
    have h := congrFun (curv_zero_right cov hcov X Y hX hY) x
    simpa using h
  | insert j s hjs ih =>
    intro hf hY'
    have hfj : CMDiff ∞ (f j) := hf j (Finset.mem_insert_self j s)
    have hY'j : CMDiff ∞ (T% (Y' j)) := hY' j (Finset.mem_insert_self j s)
    have hfs : ∀ i ∈ s, CMDiff ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hY's : ∀ i ∈ s, CMDiff ∞ (T% (Y' i)) := fun i hi => hY' i (Finset.mem_insert_of_mem hi)
    have hsum : CMDiff ∞ (T% (∑ i ∈ s, f i • Y' i)) := by
      simpa using (ContMDiff.sum_section (fun i hi => (hfs i hi).smul_section (hY's i hi)))
    rw [Finset.sum_insert hjs, Finset.sum_insert hjs]
    have hadd := congrFun (curv_add_right cov hcov X Y (f j • Y' j) (∑ i ∈ s, f i • Y' i)
      hX hY (hfj.smul_section hY'j) hsum) x
    rw [show curv cov X Y (f j • Y' j + ∑ i ∈ s, f i • Y' i) x
        = curv cov X Y (f j • Y' j) x + curv cov X Y (∑ i ∈ s, f i • Y' i) x from by
      simpa [Pi.add_apply] using hadd]
    rw [curv_smul_right cov hcov (f j) X Y (Y' j) x hfj hX hY hY'j, ih hfs hY's]

/-- Germ decomposition of the X slot with all coefficients vanishing at `x`
forces `R(X,Y)Z x = 0`.  (Private: the public form obtains the decomposition from
`exists_frame_decomposition_of_apply_eq_zero`.) -/
private lemma curv_eq_zero_of_decomp_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {ι : Type*} [Fintype ι] {f : ι → M → ℝ} {Y' : ι → Π x : M, TangentSpace I x}
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hf : ∀ i, CMDiff ∞ (f i)) (hY' : ∀ i, CMDiff ∞ (T% (Y' i)))
    (hfx : ∀ i, f i x = 0) (hdec : X =ᶠ[𝓝 x] ∑ i, f i • Y' i) :
    curv cov X Y Z x = 0 := by
  have hsum : CMDiff ∞ (T% (∑ i, f i • Y' i)) := by
    simpa using (ContMDiff.sum_section (fun i _ => (hf i).smul_section (hY' i)))
  rw [curv_eq_of_eventuallyEq_left cov hcov hX hsum hY hZ hdec]
  rw [curv_sum_left cov hcov Finset.univ f Y' Y Z (fun i _ => hf i) (fun i _ => hY' i) hY hZ x]
  exact Finset.sum_eq_zero (fun i _ => by rw [hfx i, zero_smul])

/-- Germ decomposition of the Y slot with all coefficients vanishing at `x`
forces `R(X,Y)Z x = 0`.  (Private: the public form obtains the decomposition from
`exists_frame_decomposition_of_apply_eq_zero`.) -/
private lemma curv_eq_zero_of_decomp_middle
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {ι : Type*} [Fintype ι] {f : ι → M → ℝ} {Y' : ι → Π x : M, TangentSpace I x}
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hf : ∀ i, CMDiff ∞ (f i)) (hY' : ∀ i, CMDiff ∞ (T% (Y' i)))
    (hfx : ∀ i, f i x = 0) (hdec : Y =ᶠ[𝓝 x] ∑ i, f i • Y' i) :
    curv cov X Y Z x = 0 := by
  have hsum : CMDiff ∞ (T% (∑ i, f i • Y' i)) := by
    simpa using (ContMDiff.sum_section (fun i _ => (hf i).smul_section (hY' i)))
  rw [curv_eq_of_eventuallyEq_middle cov hcov hX hY hsum hZ hdec]
  rw [curv_sum_middle cov hcov Finset.univ f Y' X Z (fun i _ => hf i) (fun i _ => hY' i) hX hZ x]
  exact Finset.sum_eq_zero (fun i _ => by rw [hfx i, zero_smul])

/-- Germ decomposition of the Z slot with all coefficients vanishing at `x`
forces `R(X,Y)Z x = 0`.  (Private: the public form obtains the decomposition from
`exists_frame_decomposition_of_apply_eq_zero`.) -/
private lemma curv_eq_zero_of_decomp_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {ι : Type*} [Fintype ι] {f : ι → M → ℝ} {Y' : ι → Π x : M, TangentSpace I x}
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hf : ∀ i, CMDiff ∞ (f i)) (hY' : ∀ i, CMDiff ∞ (T% (Y' i)))
    (hfx : ∀ i, f i x = 0) (hdec : Z =ᶠ[𝓝 x] ∑ i, f i • Y' i) :
    curv cov X Y Z x = 0 := by
  have hsum : CMDiff ∞ (T% (∑ i, f i • Y' i)) := by
    simpa using (ContMDiff.sum_section (fun i _ => (hf i).smul_section (hY' i)))
  rw [curv_eq_of_eventuallyEq_right cov hcov hX hY hZ hsum hdec]
  rw [curv_sum_right cov hcov Finset.univ f Y' X Y (fun i _ => hf i) (fun i _ => hY' i) hX hY x]
  exact Finset.sum_eq_zero (fun i _ => by rw [hfx i, zero_smul])


/-! ## Value-dependence: `curv` depends only on the values at the point

Using the local-frame expansion `exists_frame_decomposition_of_apply_eq_zero` together with
germ reduction, additivity and tensoriality, we obtain the classical tensoriality conclusion:
`R(X,Y)Z x` depends only on `X x`, `Y x`, `Z x`. -/

/-- If `X x = 0` then `R(X,Y)Z x = 0` (value-dependence in the first slot). -/
lemma curv_eq_zero_of_apply_eq_zero_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hXx : X x = 0) : curv cov X Y Z x = 0 := by
  obtain ⟨f, Y', hf, hY', hfx, hdec⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
      (I := I) (M := M) (X := X) (x := x) hX hXx
  exact curv_eq_zero_of_decomp_left cov hcov hX hY hZ hf hY' hfx hdec

/-- If `Y x = 0` then `R(X,Y)Z x = 0` (value-dependence in the second slot). -/
lemma curv_eq_zero_of_apply_eq_zero_middle
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hYx : Y x = 0) : curv cov X Y Z x = 0 := by
  obtain ⟨f, Y', hf, hY', hfx, hdec⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
      (I := I) (M := M) (X := Y) (x := x) hY hYx
  exact curv_eq_zero_of_decomp_middle cov hcov hX hY hZ hf hY' hfx hdec

/-- If `Z x = 0` then `R(X,Y)Z x = 0` (value-dependence in the third slot). -/
lemma curv_eq_zero_of_apply_eq_zero_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hZx : Z x = 0) : curv cov X Y Z x = 0 := by
  obtain ⟨f, Y', hf, hY', hfx, hdec⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
      (I := I) (M := M) (X := Z) (x := x) hZ hZx
  exact curv_eq_zero_of_decomp_right cov hcov hX hY hZ hf hY' hfx hdec

/-- Value-dependence in the first slot: `X x = X' x` implies `R(X,Y)Z x = R(X',Y)Z x`. -/
lemma curv_eq_of_apply_eq_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X X' Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hX' : CMDiff ∞ (T% X'))
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hx : X x = X' x) : curv cov X Y Z x = curv cov X' Y Z x := by
  have hsub : (X - X') x = 0 := by
    rw [show (X - X') x = X x - X' x from rfl, hx, sub_self]
  have h0 := curv_eq_zero_of_apply_eq_zero_left cov hcov (hX.sub_section hX') hY hZ hsub
  have hadd := curv_add_left cov hcov (X - X') X' Y Z (hX.sub_section hX') hX' hY hZ
  rw [show (X - X') + X' = X from by
        funext y
        show (X - X') y + X' y = X y
        rw [show (X - X') y = X y - X' y from rfl]
        abel] at hadd
  have hsum : curv cov X Y Z x = curv cov (X - X') Y Z x + curv cov X' Y Z x := by
    simpa [Pi.add_apply] using congrFun hadd x
  rw [hsum, h0, zero_add]

/-- Value-dependence in the second slot. -/
lemma curv_eq_of_apply_eq_middle
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Y' Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y'))
    (hZ : CMDiff ∞ (T% Z))
    (hy : Y x = Y' x) : curv cov X Y Z x = curv cov X Y' Z x := by
  have hsub : (Y - Y') x = 0 := by
    rw [show (Y - Y') x = Y x - Y' x from rfl, hy, sub_self]
  have h0 := curv_eq_zero_of_apply_eq_zero_middle cov hcov hX (hY.sub_section hY') hZ hsub
  have hadd := curv_add_middle cov hcov X (Y - Y') Y' Z hX (hY.sub_section hY') hY' hZ
  rw [show (Y - Y') + Y' = Y from by
        funext y
        show (Y - Y') y + Y' y = Y y
        rw [show (Y - Y') y = Y y - Y' y from rfl]
        abel] at hadd
  have hsum : curv cov X Y Z x = curv cov X (Y - Y') Z x + curv cov X Y' Z x := by
    simpa [Pi.add_apply] using congrFun hadd x
  rw [hsum, h0, zero_add]

/-- Value-dependence in the third slot. -/
lemma curv_eq_of_apply_eq_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y Z Z' : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (hZ' : CMDiff ∞ (T% Z'))
    (hz : Z x = Z' x) : curv cov X Y Z x = curv cov X Y Z' x := by
  have hsub : (Z - Z') x = 0 := by
    rw [show (Z - Z') x = Z x - Z' x from rfl, hz, sub_self]
  have h0 := curv_eq_zero_of_apply_eq_zero_right cov hcov hX hY (hZ.sub_section hZ') hsub
  have hadd := curv_add_right cov hcov X Y (Z - Z') Z' hX hY (hZ.sub_section hZ') hZ'
  rw [show (Z - Z') + Z' = Z from by
        funext y
        show (Z - Z') y + Z' y = Z y
        rw [show (Z - Z') y = Z y - Z' y from rfl]
        abel] at hadd
  have hsum : curv cov X Y Z x = curv cov X Y (Z - Z') x + curv cov X Y Z' x := by
    simpa [Pi.add_apply] using congrFun hadd x
  rw [hsum, h0, zero_add]

/-- **Tensoriality conclusion**: `R(X,Y)Z x` depends only on the values `X x`, `Y x`, `Z x`. -/
theorem curv_eq_of_apply_eq
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X X' Y Y' Z Z' : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hX' : CMDiff ∞ (T% X'))
    (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y'))
    (hZ : CMDiff ∞ (T% Z)) (hZ' : CMDiff ∞ (T% Z'))
    (hx : X x = X' x) (hy : Y x = Y' x) (hz : Z x = Z' x) :
    curv cov X Y Z x = curv cov X' Y' Z' x := by
  rw [curv_eq_of_apply_eq_left cov hcov hX hX' hY hZ hx,
      curv_eq_of_apply_eq_middle cov hcov hX' hY hY' hZ hy,
      curv_eq_of_apply_eq_right cov hcov hX' hY' hZ hZ' hz]


/-! ## The curvature (sectional) numerator form

`curvForm cov X Y x = ⟨R(X,Y)Y, X⟩` is the numerator of the sectional curvature of the
plane spanned by `X x` and `Y x`.  We prove that it is symmetric, invariant under the
elementary (shear) changes of basis, scales as a quadratic form, and finally transforms by
`(ad - bc)^2` under an arbitrary change of basis — i.e. the ratio with the Gram determinant
`‖X x‖² ‖Y x‖² - ⟨X x, Y x⟩²` is a function of the plane only. -/

/-- The numerator of the sectional curvature: `⟨R(X,Y)Y, X⟩` at `x`. -/
noncomputable def curvForm (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (X Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  inner ℝ (curv cov X Y Y x) (X x)

/-- Value-dependence of the curvature form. -/
lemma curvForm_eq_of_apply_eq
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X X' Y Y' : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiff ∞ (T% X)) (hX' : CMDiff ∞ (T% X'))
    (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y'))
    (hx : X x = X' x) (hy : Y x = Y' x) :
    curvForm cov X Y x = curvForm cov X' Y' x := by
  unfold curvForm
  rw [curv_eq_of_apply_eq cov hcov hX hX' hY hY' hY hY' hx hy hy, hx]

/-- Constant scalar multiplication of a smooth section is smooth. -/
private lemma smul_section_const {Y : Π x : M, TangentSpace I x} (hY : CMDiff ∞ (T% Y))
    (α : ℝ) : CMDiff ∞ (T% (α • Y)) := by
  simpa using (contMDiff_const (c := α)).smul_section hY

/-- `curv` is linear over constant scalars in its first slot. -/
lemma curv_const_smul_left (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (c : ℝ)
    {X Y Z : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) : curv cov (c • X) Y Z = c • curv cov X Y Z := by
  funext x
  exact curv_smul_left cov hcov (fun _ : M => c) X Y Z x contMDiff_const hX hY hZ

/-- `curv` is linear over constant scalars in its second slot. -/
lemma curv_const_smul_middle (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (c : ℝ)
    {X Y Z : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) : curv cov X (c • Y) Z = c • curv cov X Y Z := by
  funext x
  exact curv_smul_middle cov hcov (fun _ : M => c) X Y Z x contMDiff_const hX hY hZ

/-- `curv` is linear over constant scalars in its third slot. -/
lemma curv_const_smul_right (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (c : ℝ)
    {X Y Z : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) : curv cov X Y (c • Z) = c • curv cov X Y Z := by
  funext x
  exact curv_smul_right cov hcov (fun _ : M => c) X Y Z x contMDiff_const hX hY hZ

/-- The curvature numerator is symmetric: `⟨R(X,Y)Y, X⟩ = ⟨R(Y,X)X, Y⟩`. -/
lemma curvForm_comm
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    {X Y : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (x : M) : curvForm cov X Y x = curvForm cov Y X x := by
  unfold curvForm
  have hskew := curv_inner_skew cov hcov hmet hX hY hY hX (x := x)
  have hx : curv cov X Y X x = - curv cov Y X X x := congrFun (curv_antisymm cov X Y X) x
  rw [hskew, hx, inner_neg_right, neg_neg]
  exact real_inner_comm _ _

/-- Shear invariance in the first slot: `⟨R(X + αY, Y)Y, X + αY⟩ = ⟨R(X,Y)Y, X⟩`. -/
lemma curvForm_shear_left
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    {X Y : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (α : ℝ) (x : M) : curvForm cov (X + α • Y) Y x = curvForm cov X Y x := by
  unfold curvForm
  have h1 : curv cov (X + α • Y) Y Y = curv cov X Y Y + α • curv cov Y Y Y := by
    rw [curv_add_left cov hcov X (α • Y) Y Y hX (smul_section_const hY α) hY hY]
    rw [curv_const_smul_left cov hcov α hY hY hY]
  rw [h1, curv_self_zero, smul_zero, add_zero]
  rw [show (X + α • Y) x = X x + α • Y x from rfl, inner_add_right, inner_smul_right]
  rw [show inner ℝ (curv cov X Y Y x) (Y x) = 0 from
    curv_inner_self_zero cov hcov hmet hX hY hY (x := x)]
  ring

/-- Shear invariance in the second slot: `⟨R(X, Y + βX)(Y + βX), X⟩ = ⟨R(X,Y)Y, X⟩`. -/
lemma curvForm_shear_right
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    {X Y : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (β : ℝ) (x : M) : curvForm cov X (Y + β • X) x = curvForm cov X Y x := by
  unfold curvForm
  have hYβ : CMDiff ∞ (T% (Y + β • X)) := hY.add_section (smul_section_const hX β)
  have h1 : curv cov X (Y + β • X) (Y + β • X) = curv cov X Y Y + β • curv cov X Y X := by
    rw [curv_add_middle cov hcov X Y (β • X) (Y + β • X) hX hY (smul_section_const hX β) hYβ]
    rw [curv_const_smul_middle cov hcov β hX hX hYβ]
    rw [curv_self_zero, smul_zero, add_zero]
    rw [curv_add_right cov hcov X Y Y (β • X) hX hY hY (smul_section_const hX β)]
    rw [curv_const_smul_right cov hcov β hX hY hX]
  rw [h1]
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [inner_add_left, inner_smul_left]
  rw [show inner ℝ (curv cov X Y X x) (X x) = 0 from
    curv_inner_self_zero cov hcov hmet hX hY hX (x := x)]
  ring

/-- The curvature numerator scales as the square of the area: `Q(lX, mY) = l²m²Q(X,Y)`. -/
lemma curvForm_smul_smul
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {X Y : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (l m : ℝ) (x : M) :
    curvForm cov (l • X) (m • Y) x = l^2 * m^2 * curvForm cov X Y x := by
  unfold curvForm
  have h1 : curv cov (l • X) (m • Y) (m • Y) = (l * m * m) • curv cov X Y Y := by
    rw [curv_const_smul_left cov hcov l hX (smul_section_const hY m) (smul_section_const hY m)]
    rw [curv_const_smul_middle cov hcov m hX hY (smul_section_const hY m)]
    rw [curv_const_smul_right cov hcov m hX hY hY]
    rw [smul_smul, smul_smul]
  rw [h1, Pi.smul_apply]
  rw [show (l • X) x = l • X x from rfl]
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial]
  ring

/-- **Basis-independence of the curvature numerator**, up to the square of the area:
`Q(aX + bY, cX + dY) = (ad - bc)^2 Q(X,Y)`. -/
lemma curvForm_basis_change
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    {X Y : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (a b c d : ℝ) (x : M) :
    curvForm cov (a • X + b • Y) (c • X + d • Y) x
      = (a * d - b * c)^2 * curvForm cov X Y x := by
  unfold curvForm
  have hXc : CMDiff ∞ (T% (c • X)) := smul_section_const hX c
  have hXd : CMDiff ∞ (T% (d • Y)) := smul_section_const hY d
  have haX : CMDiff ∞ (T% (a • X)) := smul_section_const hX a
  have hbY : CMDiff ∞ (T% (b • Y)) := smul_section_const hY b
  have hcXdY : CMDiff ∞ (T% (c • X + d • Y)) := hXc.add_section hXd
  have haXbY : CMDiff ∞ (T% (a • X + b • Y)) := haX.add_section hbY
  have hV3 : curv cov (a • X + b • Y) (c • X + d • Y) (c • X + d • Y)
      = c • curv cov (a • X + b • Y) (c • X + d • Y) X
        + d • curv cov (a • X + b • Y) (c • X + d • Y) Y := by
    rw [curv_add_right cov hcov (a • X + b • Y) (c • X + d • Y) (c • X) (d • Y)
      haXbY hcXdY hXc hXd]
    rw [curv_const_smul_right cov hcov c haXbY hcXdY hX]
    rw [curv_const_smul_right cov hcov d haXbY hcXdY hY]
  have hmid : ∀ {Z : Π x : M, TangentSpace I x}, CMDiff ∞ (T% Z) →
      curv cov (a • X + b • Y) (c • X + d • Y) Z
        = c • curv cov (a • X + b • Y) X Z + d • curv cov (a • X + b • Y) Y Z := by
    intro Z hZ
    rw [curv_add_middle cov hcov (a • X + b • Y) (c • X) (d • Y) Z haXbY hXc hXd hZ]
    rw [curv_const_smul_middle cov hcov c haXbY hX hZ]
    rw [curv_const_smul_middle cov hcov d haXbY hY hZ]
  have hfst : ∀ {W Z : Π x : M, TangentSpace I x}, CMDiff ∞ (T% W) → CMDiff ∞ (T% Z) →
      curv cov (a • X + b • Y) W Z = a • curv cov X W Z + b • curv cov Y W Z := by
    intro W Z hW hZ
    rw [curv_add_left cov hcov (a • X) (b • Y) W Z haX hbY hW hZ]
    rw [curv_const_smul_left cov hcov a hX hW hZ]
    rw [curv_const_smul_left cov hcov b hY hW hZ]
  have hExp : curv cov (a • X + b • Y) (c • X + d • Y) (c • X + d • Y)
      = (c * c * b) • curv cov Y X X + (c * d * a) • curv cov X Y X
        + (c * d * b) • curv cov Y X Y + (d * d * a) • curv cov X Y Y := by
    rw [hV3, hmid hX, hmid hY]
    rw [hfst hX hX, hfst hY hX, hfst hX hY, hfst hY hY]
    simp only [curv_self_zero, smul_zero, zero_add, add_zero, smul_smul]
    module
  rw [hExp]
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [inner_add_left, inner_smul_left, inner_add_right, inner_smul_right]
  have hz1 : inner ℝ (curv cov Y X X x) (X x) = 0 :=
    curv_inner_self_zero cov hcov hmet hY hX hX (x := x)
  have hz2 : inner ℝ (curv cov X Y X x) (X x) = 0 :=
    curv_inner_self_zero cov hcov hmet hX hY hX (x := x)
  have hz3 : inner ℝ (curv cov Y X Y x) (Y x) = 0 :=
    curv_inner_self_zero cov hcov hmet hY hX hY (x := x)
  have hz4 : inner ℝ (curv cov X Y Y x) (Y x) = 0 :=
    curv_inner_self_zero cov hcov hmet hX hY hY (x := x)
  have hA : inner ℝ (curv cov Y X Y x) (X x) = - inner ℝ (curv cov X Y Y x) (X x) := by
    rw [show curv cov Y X Y x = - curv cov X Y Y x from congrFun (curv_antisymm cov Y X Y) x,
      inner_neg_left]
  have hB : inner ℝ (curv cov Y X X x) (Y x) = inner ℝ (curv cov X Y Y x) (X x) := by
    rw [show curv cov Y X X x = - curv cov X Y X x from congrFun (curv_antisymm cov Y X X) x,
      inner_neg_left]
    rw [curv_inner_skew cov hcov hmet hX hY hX hY (x := x)]
    rw [real_inner_comm (X x) (curv cov X Y Y x)]
    ring
  have hC : inner ℝ (curv cov X Y X x) (Y x) = - inner ℝ (curv cov X Y Y x) (X x) := by
    rw [curv_inner_skew cov hcov hmet hX hY hX hY (x := x)]
    rw [real_inner_comm (X x) (curv cov X Y Y x)]
  rw [hz1, hz2, hz3, hz4, hA, hB, hC]
  simp only [starRingEnd_apply, star_trivial]
  ring


/-! ## The Gram determinant and the sectional curvature ratio

Together with the basis-change formula for `curvForm`, the multiplicativity of the Gram
determinant shows that the ratio `⟨R(X,Y)Y,X⟩ / (‖X‖²‖Y‖² - ⟨X,Y⟩²)` is a function of the
2-plane spanned by `X x, Y x` alone. -/

/-- The Gram determinant `‖X x‖² ‖Y x‖² - ⟨X x, Y x⟩²` (the squared area of the parallelogram). -/
noncomputable def gramForm (X Y : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  ‖X x‖^2 * ‖Y x‖^2 - (inner ℝ (X x) (Y x))^2

/-- The Gram determinant scales by the square of the determinant of the change of basis. -/
lemma gramForm_basis_change {X Y : Π x : M, TangentSpace I x} (a b c d : ℝ) (x : M) :
    gramForm (a • X + b • Y) (c • X + d • Y) x
      = (a * d - b * c)^2 * gramForm X Y x := by
  unfold gramForm
  simp only [Pi.add_apply, Pi.smul_apply]
  exact Commons.Analysis.InnerProductSpace.inner_gram_basis_change (X x) (Y x) a b c d

/-- **Basis-independence of the sectional curvature ratio**: the quotient
`⟨R(X,Y)Y,X⟩ / (‖X‖²‖Y‖² - ⟨X,Y⟩²)` is invariant under an invertible change of basis of the
plane.  This is the content of "sectional curvature is a function of the 2-plane". -/
lemma sectional_ratio_basis_change
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    {X Y : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (a b c d : ℝ) {x : M} (hdet : a * d - b * c ≠ 0) (hG : gramForm X Y x ≠ 0) :
    curvForm cov (a • X + b • Y) (c • X + d • Y) x
        / gramForm (a • X + b • Y) (c • X + d • Y) x
      = curvForm cov X Y x / gramForm X Y x := by
  rw [curvForm_basis_change cov hcov hmet hX hY a b c d x, gramForm_basis_change a b c d x]
  field_simp


/-! ## The sectional curvature form on tangent vectors and on 2-planes -/

/-- The Gram determinant of two tangent vectors (squared area of the parallelogram). -/
noncomputable def gramFormVec (x : M) (u v : TangentSpace I x) : ℝ :=
  ‖u‖^2 * ‖v‖^2 - (inner ℝ u v)^2

/-- The curvature numerator as a function of tangent vectors, obtained by extending the
vectors to globally smooth fields (the value is independent of the extension by
`curvForm_eq_of_apply_eq`). -/
noncomputable def curvFormVec (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x : M)
    (u v : TangentSpace I x) : ℝ :=
  curvForm cov
    (Classical.choose (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u))
    (Classical.choose (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v)) x

/-- `curvFormVec` agrees with `curvForm` for any choice of smooth extensions. -/
lemma curvFormVec_eq
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞)
    {x : M} {u v : TangentSpace I x} {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hux : X x = u) (hvy : Y x = v) :
    curvFormVec cov x u v = curvForm cov X Y x := by
  unfold curvFormVec
  refine curvForm_eq_of_apply_eq cov hcov ?_ hX ?_ hY ?_ ?_
  · exact (Classical.choose_spec
      (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u)).1
  · exact (Classical.choose_spec
      (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v)).1
  · rw [(Classical.choose_spec
      (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u)).2, hux]
  · rw [(Classical.choose_spec
      (Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v)).2, hvy]

/-- Value-dependence of `curvFormVec` (automatic: it is a function of vectors). -/
lemma gramFormVec_basis_change {x : M} {u v : TangentSpace I x} (a b c d : ℝ) :
    gramFormVec x (a • u + b • v) (c • u + d • v)
      = (a * d - b * c)^2 * gramFormVec x u v :=
  Commons.Analysis.InnerProductSpace.inner_gram_basis_change u v a b c d

/-- The vector-valued curvature numerator transforms by `(ad - bc)^2` under a change of basis. -/
lemma curvFormVec_basis_change
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    {x : M} {u v : TangentSpace I x} (a b c d : ℝ) :
    curvFormVec cov x (a • u + b • v) (c • u + d • v)
      = (a * d - b * c)^2 * curvFormVec cov x u v := by
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  have hX' : CMDiff ∞ (T% (a • X + b • Y)) :=
    (smul_section_const hX a).add_section (smul_section_const hY b)
  have hY' : CMDiff ∞ (T% (c • X + d • Y)) :=
    (smul_section_const hX c).add_section (smul_section_const hY d)
  have hvalX : (a • X + b • Y) x = a • u + b • v := by
    simp only [Pi.add_apply, Pi.smul_apply, hXx, hYx]
  have hvalY : (c • X + d • Y) x = c • u + d • v := by
    simp only [Pi.add_apply, Pi.smul_apply, hXx, hYx]
  rw [curvFormVec_eq cov hcov hX' hY' hvalX hvalY, curvFormVec_eq cov hcov hX hY hXx hYx]
  exact curvForm_basis_change cov hcov hmet hX hY a b c d x

/-- **Basis-independence of the sectional curvature on tangent vectors.**  The quotient
`⟨R(u,v)v,u⟩ / (‖u‖²‖v‖² - ⟨u,v⟩²)` is invariant under an invertible change of basis. -/
lemma sectional_ratio_vec_basis_change
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    {x : M} {u v : TangentSpace I x} (a b c d : ℝ) (hdet : a * d - b * c ≠ 0)
    (hG : gramFormVec x u v ≠ 0) :
    curvFormVec cov x (a • u + b • v) (c • u + d • v) / gramFormVec x (a • u + b • v) (c • u + d • v)
      = curvFormVec cov x u v / gramFormVec x u v := by
  rw [curvFormVec_basis_change cov hcov hmet a b c d, gramFormVec_basis_change a b c d]
  field_simp


/-! ## Sectional curvature of a 2-plane

With the change-of-basis invariance of the quotient `⟨R(u,v)v,u⟩ / (‖u‖²‖v‖² - ⟨u,v⟩²)`, the
sectional curvature is well defined on 2-dimensional subspaces of a tangent space. -/

/-- The Gram determinant of a pair of vectors, as the determinant of the 2×2 Gram matrix. -/
lemma gramFormVec_eq_det {x : M} (u v : TangentSpace I x) :
    gramFormVec x u v = (Matrix.gram ℝ (fun i : Fin 2 => ![u, v] i)).det := by
  unfold gramFormVec
  rw [Matrix.det_fin_two]
  simp only [Matrix.gram, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    real_inner_self_eq_norm_sq, real_inner_comm]
  ring

/-- A linearly independent `Fin 2`-family is linearly independent in the `![_, _]` form. -/
private lemma linearIndependent_cons_of {V : Type*} [AddCommGroup V] [Module ℝ V]
    {f : Fin 2 → V} (h : LinearIndependent ℝ f) : LinearIndependent ℝ ![f 0, f 1] := by
  have hfun : f = ![f 0, f 1] := by
    funext i; fin_cases i <;> rfl
  rwa [hfun] at h

/-- Nonvanishing Gram determinant means linear independence. -/
lemma linearIndependent_of_gramFormVec_ne_zero {x : M} {u v : TangentSpace I x}
    (h : gramFormVec x u v ≠ 0) : LinearIndependent ℝ ![u, v] := by
  rw [gramFormVec_eq_det] at h
  exact (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)
    (v := fun i : Fin 2 => ![u, v] i)).mp h

/-- Linear independence means nonvanishing Gram determinant. -/
lemma gramFormVec_ne_zero_of_linearIndependent {x : M} {u v : TangentSpace I x}
    (h : LinearIndependent ℝ ![u, v]) : gramFormVec x u v ≠ 0 := by
  have hdet := (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)
    (v := fun i : Fin 2 => ![u, v] i)).mpr h
  rwa [gramFormVec_eq_det]

/-- The ratio `⟨R(u,v)v,u⟩ / Gram(u,v)` is invariant under an invertible change of basis. -/
lemma sectional_ratio_of_change
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    {x : M} {u v u' v' : TangentSpace I x} {a b c d : ℝ}
    (hu' : u' = a • u + b • v) (hv' : v' = c • u + d • v)
    (hdet : a * d - b * c ≠ 0) (hG : gramFormVec x u v ≠ 0) :
    curvFormVec cov x u' v' / gramFormVec x u' v'
      = curvFormVec cov x u v / gramFormVec x u v := by
  have hd2 : (a * d - b * c)^2 ≠ 0 := pow_ne_zero 2 hdet
  rw [hu', hv', curvFormVec_basis_change cov hcov hmet a b c d, gramFormVec_basis_change a b c d]
  field_simp

section SectionalCurvature

local instance instFDTangent (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-- The sectional curvature of a 2-dimensional subspace `σ` of a tangent space,
`K(σ) = ⟨R(u,v)v,u⟩ / (‖u‖²‖v‖² - ⟨u,v⟩²)` for any basis `u, v` of `σ`. -/
noncomputable def sectionalCurvature (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x : M) (σ : Submodule ℝ (TangentSpace I x)) (hσ : Module.finrank ℝ σ = 2) : ℝ :=
  curvFormVec cov x ((Module.finBasisOfFinrankEq ℝ σ hσ) 0 : TangentSpace I x)
      ((Module.finBasisOfFinrankEq ℝ σ hσ) 1 : TangentSpace I x)
    / gramFormVec x ((Module.finBasisOfFinrankEq ℝ σ hσ) 0 : TangentSpace I x)
      ((Module.finBasisOfFinrankEq ℝ σ hσ) 1 : TangentSpace I x)

/-- A basis of `σ` spans it as a subspace of the ambient tangent space. -/
private lemma span_basis_pair_eq (x : M) (σ : Submodule ℝ (TangentSpace I x))
    (b : Module.Basis (Fin 2) ℝ σ) :
    Submodule.span ℝ ({(b 0 : TangentSpace I x), (b 1 : TangentSpace I x)} : Set (TangentSpace I x)) = σ := by
  have hrange : Set.range b = ({b 0, b 1} : Set σ) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · exact ⟨0, hz.symm⟩
      · exact ⟨1, hz.symm⟩
  have himg : σ.subtype '' Set.range b = ({↑(b 0), ↑(b 1)} : Set (TangentSpace I x)) := by
    rw [hrange]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      rcases hw with hw | hw
      · exact Or.inl (congrArg Subtype.val hw)
      · exact Or.inr (congrArg Subtype.val hw)
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · exact ⟨b 0, by simp, hz.symm⟩
      · exact ⟨b 1, by simp, hz.symm⟩
  calc Submodule.span ℝ ({↑(b 0), ↑(b 1)} : Set (TangentSpace I x))
      = Submodule.span ℝ (σ.subtype '' Set.range b) := by rw [himg]
    _ = Submodule.map σ.subtype (Submodule.span ℝ (Set.range b)) := by rw [Submodule.map_span]
    _ = Submodule.map σ.subtype ⊤ := by rw [b.span_eq]
    _ = σ := Submodule.map_subtype_top σ

/-- A basis of `σ`, viewed in the ambient tangent space, is a linearly independent pair. -/
private lemma linearIndependent_cons_basis_pair (x : M) (σ : Submodule ℝ (TangentSpace I x))
    (b : Module.Basis (Fin 2) ℝ σ) :
    LinearIndependent ℝ ![(b 0 : TangentSpace I x), (b 1 : TangentSpace I x)] := by
  have hker : σ.subtype.ker = ⊥ := LinearMap.ker_eq_bot.mpr Subtype.coe_injective
  have h' : LinearIndependent ℝ (fun i : Fin 2 => (b i : TangentSpace I x)) :=
    b.linearIndependent.map' σ.subtype hker
  have hfun : (fun i : Fin 2 => (b i : TangentSpace I x))
      = ![(b 0 : TangentSpace I x), (b 1 : TangentSpace I x)] := by
    funext i; fin_cases i <;> rfl
  rwa [hfun] at h'

/-- The pair given by a basis of `σ` has nonzero Gram determinant. -/
private lemma gramFormVec_basis_pair_ne_zero (x : M) (σ : Submodule ℝ (TangentSpace I x))
    (b : Module.Basis (Fin 2) ℝ σ) :
    gramFormVec x (b 0 : TangentSpace I x) (b 1 : TangentSpace I x) ≠ 0 :=
  gramFormVec_ne_zero_of_linearIndependent (linearIndependent_cons_basis_pair x σ b)

/-- **The sectional curvature of a plane is independent of the chosen spanning pair**: for any
pair `u, v` with nonzero Gram determinant spanning `σ`, the quotient `⟨R(u,v)v,u⟩ / Gram(u,v)`
equals `K(σ)`. -/
theorem sectionalCurvature_eq_ratio
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    {x : M} (σ : Submodule ℝ (TangentSpace I x)) (hσ : Module.finrank ℝ σ = 2)
    {u v : TangentSpace I x} (hspan : Submodule.span ℝ {u, v} = σ)
    (hG : gramFormVec x u v ≠ 0) :
    sectionalCurvature cov x σ hσ = curvFormVec cov x u v / gramFormVec x u v := by
  set b := Module.finBasisOfFinrankEq ℝ σ hσ with hb
  have hbspan := span_basis_pair_eq x σ b
  have hbG := gramFormVec_basis_pair_ne_zero x σ b
  have hspan' : Submodule.span ℝ {u, v}
      = Submodule.span ℝ ({(b 0 : TangentSpace I x), (b 1 : TangentSpace I x)} : Set (TangentSpace I x)) := by
    rw [hspan, hbspan]
  have hind : LinearIndependent ℝ ![u, v] := linearIndependent_of_gramFormVec_ne_zero hG
  have hind' : LinearIndependent ℝ ![(b 0 : TangentSpace I x), (b 1 : TangentSpace I x)] :=
    linearIndependent_cons_basis_pair x σ b
  obtain ⟨a, bb, c, d, h0, h1, hdet⟩ :=
    Commons.LinearAlgebra.exists_basis_change_of_span_eq hind hind' hspan'
  have hratio := sectional_ratio_of_change cov hcov hmet h0 h1 hdet hG
  rw [sectionalCurvature, ← hb]
  exact hratio

/-- **Well-definedness of the sectional curvature of a plane**: its value does not depend on the
chosen basis of the plane. -/
theorem sectionalCurvature_basis_independent
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    {x : M} (σ : Submodule ℝ (TangentSpace I x)) (hσ : Module.finrank ℝ σ = 2)
    (b' : Module.Basis (Fin 2) ℝ σ) :
    sectionalCurvature cov x σ hσ
      = curvFormVec cov x (b' 0 : TangentSpace I x) (b' 1 : TangentSpace I x)
        / gramFormVec x (b' 0 : TangentSpace I x) (b' 1 : TangentSpace I x) :=
  sectionalCurvature_eq_ratio cov hcov hmet σ hσ
    (span_basis_pair_eq x σ b') (gramFormVec_basis_pair_ne_zero x σ b')


/-! ## The pinching hypothesis in plane language and its quadratic-form form -/

/-- **Quarter pinching on 2-planes**: under the pinching hypothesis, the sectional curvature of
every 2-plane at every point lies in `(1, 4]`. -/
theorem quarterPinched_sectionalCurvature
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) {x : M}
    (σ : Submodule ℝ (TangentSpace I x)) (hσ : Module.finrank ℝ σ = 2) :
    (1 : ℝ) < sectionalCurvature cov x σ hσ ∧ sectionalCurvature cov x σ hσ ≤ 4 := by
  set e := (stdOrthonormalBasis ℝ σ).reindex (finCongr hσ) with he
  have hee : ∀ i j : Fin 2,
      inner ℝ ((e i : σ) : TangentSpace I x) ((e j : σ) : TangentSpace I x)
        = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h := (orthonormal_iff_ite.mp e.orthonormal) i j
    simpa [Submodule.coe_inner] using h
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M)
      ((e 0 : σ) : TangentSpace I x)
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M)
      ((e 1 : σ) : TangentSpace I x)
  have hpin := hpinch X Y hX hY x
    (by rw [hXx, hee 0 0, if_pos rfl])
    (by rw [hYx, hee 1 1, if_pos rfl])
    (by rw [hXx, hYx, hee 0 1, if_neg (by decide : (0 : Fin 2) ≠ 1)])
  have hgram : gramFormVec x ((e 0 : σ) : TangentSpace I x) ((e 1 : σ) : TangentSpace I x) = 1 := by
    unfold gramFormVec
    have h0 : ‖((e 0 : σ) : TangentSpace I x)‖ = 1 := by
      rw [← Submodule.coe_norm]
      exact e.orthonormal.norm_eq_one 0
    have h1 : ‖((e 1 : σ) : TangentSpace I x)‖ = 1 := by
      rw [← Submodule.coe_norm]
      exact e.orthonormal.norm_eq_one 1
    have h01 : inner ℝ ((e 0 : σ) : TangentSpace I x) ((e 1 : σ) : TangentSpace I x) = 0 := by
      rw [← Submodule.coe_inner]
      exact e.orthonormal.inner_eq_zero (by decide : (0 : Fin 2) ≠ 1)
    rw [h0, h1, h01]
    norm_num
  have hspan : Submodule.span ℝ
      ({((e 0 : σ) : TangentSpace I x), ((e 1 : σ) : TangentSpace I x)} : Set (TangentSpace I x))
      = σ := by
    simpa using span_basis_pair_eq x σ e.toBasis
  have hG : gramFormVec x ((e 0 : σ) : TangentSpace I x) ((e 1 : σ) : TangentSpace I x) ≠ 0 := by
    rw [hgram]; exact one_ne_zero
  have hK : sectionalCurvature cov x σ hσ = curvForm cov X Y x := by
    rw [sectionalCurvature_eq_ratio cov hcov hmet σ hσ hspan hG]
    rw [curvFormVec_eq cov hcov hX hY hXx hYx, hgram, div_one]
  rw [hK]
  exact hpin

/-- **Quadratic-form form of quarter pinching**: for any pair of tangent vectors with nonzero
Gram determinant, `Gram < ⟨R(u,v)v,u⟩ ≤ 4 · Gram`. -/
theorem quarterPinched_curvForm_bounds
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov)
    {X Y : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    {x : M} (hG : gramFormVec x (X x) (Y x) ≠ 0) :
    gramFormVec x (X x) (Y x) < curvForm cov X Y x ∧
      curvForm cov X Y x ≤ 4 * gramFormVec x (X x) (Y x) := by
  have hind : LinearIndependent ℝ ![X x, Y x] := linearIndependent_of_gramFormVec_ne_zero hG
  have hrange : Set.range (fun i : Fin 2 => ![X x, Y x] i)
      = ({X x, Y x} : Set (TangentSpace I x)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · exact ⟨0, hz.symm⟩
      · exact ⟨1, hz.symm⟩
  have hσ : Module.finrank ℝ (Submodule.span ℝ ({X x, Y x} : Set (TangentSpace I x))) = 2 := by
    have hcard := finrank_span_eq_card hind
    rw [hrange] at hcard
    simpa using hcard
  obtain ⟨hlo, hhi⟩ := quarterPinched_sectionalCurvature cov hcov hmet hpinch
    (Submodule.span ℝ ({X x, Y x} : Set (TangentSpace I x))) hσ
  have hK : sectionalCurvature cov x (Submodule.span ℝ ({X x, Y x} : Set (TangentSpace I x))) hσ
      = curvForm cov X Y x / gramFormVec x (X x) (Y x) := by
    rw [sectionalCurvature_eq_ratio cov hcov hmet _ hσ rfl hG,
      curvFormVec_eq cov hcov hX hY rfl rfl]
  rw [hK] at hlo hhi
  have hGpos : 0 < gramFormVec x (X x) (Y x) := by
    have hnn : 0 ≤ gramFormVec x (X x) (Y x) := by
      unfold gramFormVec
      have hcs := abs_real_inner_le_norm (X x) (Y x)
      have hsq : (inner ℝ (X x) (Y x))^2 ≤ ‖X x‖^2 * ‖Y x‖^2 := by
        calc (inner ℝ (X x) (Y x))^2 = |inner ℝ (X x) (Y x)|^2 := by rw [sq_abs]
          _ ≤ (‖X x‖ * ‖Y x‖)^2 := by gcongr
          _ = ‖X x‖^2 * ‖Y x‖^2 := by ring
      linarith
    exact lt_of_le_of_ne hnn (Ne.symm hG)
  constructor
  · have := mul_lt_mul_of_pos_right hlo hGpos
    simpa [div_mul_cancel₀ (curvForm cov X Y x) hG] using this
  · have := mul_le_mul_of_nonneg_right hhi (le_of_lt hGpos)
    simpa [div_mul_cancel₀ (curvForm cov X Y x) hG] using this



/-- The pinching hypothesis for an orthonormal pair, in terms of `curvForm`. -/
theorem quarterPinched_curvForm_unit
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov)
    {X Y : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    {x : M} (h1 : ‖X x‖ = 1) (h2 : ‖Y x‖ = 1) (h3 : inner ℝ (X x) (Y x) = 0) :
    (1 : ℝ) < curvForm cov X Y x ∧ curvForm cov X Y x ≤ 4 := by
  have hG : gramFormVec x (X x) (Y x) = 1 := by
    unfold gramFormVec
    rw [h1, h2, h3]
    norm_num
  have hb := quarterPinched_curvForm_bounds cov hcov hmet hpinch hX hY
    (x := x) (by rw [hG]; exact one_ne_zero)
  rw [hG] at hb
  simpa using hb


end SectionalCurvature

end Submission.Curvature
