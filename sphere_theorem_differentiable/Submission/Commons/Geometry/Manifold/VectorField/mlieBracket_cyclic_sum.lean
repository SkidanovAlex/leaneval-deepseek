import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Geometry.Manifold.VectorField

open scoped _root_.Manifold _root_.ContDiff
open _root_.VectorField

set_option linter.style.haveILetI false

/-- A `C²` pair of vector fields has a `C¹` Lie bracket.  This is a thin wrapper around
`ContDiff.mlieBracket_vectorField` which takes care of the coercions between `ℕ∞` and `ℕ∞ω`
and of the `IsManifold` instances. -/
private lemma cMDiff_one_mlieBracket
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {U V : Π x : M, TangentSpace I x}
    (hU : CMDiff (minSmoothness ℝ 2) (T% U)) (hV : CMDiff (minSmoothness ℝ 2) (T% V)) :
    CMDiff 1 (T% (mlieBracket I U V)) := by
  haveI : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
  haveI : IsManifold I ((↑(2 : ENat) : ℕ∞ω) + 1) M :=
    IsManifold.of_le (n := ∞)
      (by rw [show ((↑(2 : ENat) : ℕ∞ω) + 1) = (3 : ℕ∞ω) from rfl]; decide)
  have hU' : CMDiff (2 : ℕ∞ω) (T% U) := by simpa using hU
  have hV' : CMDiff (2 : ℕ∞ω) (T% V) := by simpa using hV
  exact ContDiff.mlieBracket_vectorField (n := 2) hU' hV' (by norm_num)

/-- The Lie bracket is antilinear in its second argument: `[V, -W] = -[V, W]`.
Smoothness of `W` is needed because Mathlib's product rule for Lie brackets requires
differentiability of the second field. -/
private lemma mlieBracket_neg_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {V W : Π x : M, TangentSpace I x} (hW : CMDiff 1 (T% W)) :
    mlieBracket I V (-W) = - mlieBracket I V W := by
  ext x
  rw [show (-W) = (-1 : ℝ) • W by ext y; simp]
  rw [mlieBracket_const_smul_right (c := -1) (hW := (hW x).mdifferentiableAt one_ne_zero)]
  simp

/-- The Jacobi identity in cyclic form for the manifold Lie bracket:
`[U,[V,W]] + [V,[W,U]] + [W,[U,V]] = 0`. -/
theorem mlieBracket_cyclic_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {U V W : Π x : M, TangentSpace I x}
    (hU : CMDiff (minSmoothness ℝ 2) (T% U)) (hV : CMDiff (minSmoothness ℝ 2) (T% V))
    (hW : CMDiff (minSmoothness ℝ 2) (T% W)) :
    mlieBracket I U (mlieBracket I V W) + mlieBracket I V (mlieBracket I W U)
      + mlieBracket I W (mlieBracket I U V) = 0 := by
  haveI : IsManifold I (minSmoothness ℝ 3) M :=
    IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)
  have hWU := cMDiff_one_mlieBracket hW hU
  ext x
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [leibniz_identity_mlieBracket_apply (hU x) (hV x) (hW x)]
  rw [show mlieBracket I (mlieBracket I U V) W x = - mlieBracket I W (mlieBracket I U V) x from
    mlieBracket_swap_apply]
  rw [show mlieBracket I U W = - mlieBracket I W U from mlieBracket_swap]
  rw [mlieBracket_neg_right hWU]
  rw [Pi.neg_apply]
  abel

end Commons.Geometry.Manifold.VectorField