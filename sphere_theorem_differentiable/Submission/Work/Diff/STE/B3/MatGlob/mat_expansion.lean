import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.MatGlob

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Expansion of a bilinear form in an orthonormal frame.**  If `F` is a `g`-orthonormal family in
`TₓM` (so, by `Work.EXT.sum_inner_smul_eq_self_of_isONFrame`, a `g`-orthonormal *basis*), then every
bilinear form `B` on `TₓM` expands as
`B X Y = ∑ c ∑ d ⟪X, F c⟫ ⟪Y, F d⟫ · B (F c) (F d)`.

This is the purely linear-algebraic content of `Work.Diff.STE.B3.MatGlob.mat_expansion`: the
orthonormality of the frame `e i` (available on the `2σ i`-ball by `B3Data.heON`) turns the matrix of
a section in the frame `e i` into the matrix in the frame `e j` multiplied by the two changes of
frame on either side. -/
theorem bil_expansion_of_isONFrame (g : Submission.Diff.SMet I M) (x : M)
    (F : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hF : Submission.Diff.IsONFrame g x F)
    (B : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (X Y : TangentSpace I x) :
    B X Y = ∑ c, ∑ d, (g.inner x X (F c)) * (g.inner x Y (F d)) * B (F c) (F d) := by
  have hX : ∑ c, g.inner x X (F c) • F c = X :=
    Work.EXT.sum_inner_smul_eq_self_of_isONFrame g x F hF X
  have hY : ∑ d, g.inner x Y (F d) • F d = Y :=
    Work.EXT.sum_inner_smul_eq_self_of_isONFrame g x F hF Y
  -- only the two arguments of `B` may be expanded: `X` also occurs inside the coordinates
  -- `g.inner x X (F c)`, which must be left alone
  conv_lhs => rw [← hX, ← hY]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => by ring))

theorem mat_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ)
    (hsrc : D.pt j z ∈ (extChartAt I (D.x₀ i)).source)
    (hτ : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)‖ ≤ 2 * D.σ i) :
    D.mat j h a b z
      = ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        (g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z)))
          * (g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d (D.pt j z)))
          * D.mat i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) := by
  -- the flat coordinate of `D.pt j z` in the chart `i`, and the point of `M` it designates
  have hpt : D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) = D.pt j z :=
    D.pt_coord i hsrc
  -- the frame `e i` is `g₀`-orthonormal at `D.pt j z` (it is so on the whole `2σ i`-ball)
  have he : Submission.Diff.IsONFrame g₀ (D.pt j z) (fun c => D.e i c (D.pt j z)) := by
    have h0 : Submission.Diff.IsONFrame g₀
        (D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)))
        (fun c => D.e i c (D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)))) :=
      D.heON i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)) hτ
    rwa [hpt] at h0
  -- the expansion of `h` in the frame `e i` at that point
  have key := bil_expansion_of_isONFrame (I := I) (M := M) g₀ (D.pt j z)
    (fun c => D.e i c (D.pt j z)) he (h (D.pt j z))
    (D.e j a (D.pt j z)) (D.e j b (D.pt j z))
  rw [show D.mat j h a b z
      = h (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z)) from rfl, key]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
  rw [show D.mat i h c d (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))
      = h (D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)))
          (D.e i c (D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z))))
          (D.e i d (D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)))) from rfl,
    hpt]

end Work.Diff.STE.B3.MatGlob
