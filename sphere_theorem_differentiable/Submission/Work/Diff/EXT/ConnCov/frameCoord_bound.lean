import Mathlib
import Submission.Work.Diff.EXT.sum_chartMatFun_eq_inner

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The frame-coordinate bound from uniform ellipticity of the chart matrix

Fix a smooth metric `g` on `M`, a chart centre `x₀`, a chart coordinate `y` in the target of the
extended chart at `x₀` (write `q = (extChartAt I x₀).symm y`) and a constant `δ > 0`.

The chart matrix
`chartMatFun g x₀ y i j = g_q (σ_i) (σ_j)`,  `σ_i = frameVector I x₀ q (bB i)`,
where `bB` is the canonical basis of the model space `E`, is the Gram matrix of the coordinate
frame of the chart at `x₀`.  The hypothesis `hell` says that this matrix dominates `δ · 1` as a
quadratic form, i.e. that the chart at `x₀` is `δ`-elliptic at the point `q`.

The lemma bounds the **coordinates** of a tangent vector `v ∈ T_qM` in that frame by the metric
norm of `v`:

`∑_p |coord_p (v)| ≤ √(n/δ) · √(g_q(v,v))`,  `n = finrank ℝ E`.

Indeed the trivialization `trivializationAt E (TangentSpace I) x₀` is inverse to the frame at `q`
as soon as `q` lies in the chart source at `x₀` (which holds here because `q` is the image of a
chart *coordinate*), so
`v = ∑_i c_i • σ_i` with `c_i = (bB.coord i) ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ q v)`.
Then the quadratic form of the chart matrix is the metric of the combination
(`Work.Diff.EXT.sum_chartMatFun_eq_inner`), so `hell` gives `δ ∑_i c_i² ≤ g_q(v,v)`, while
Cauchy–Schwarz gives `(∑_i |c_i|)² ≤ n ∑_i c_i²`.  Combining and taking square roots concludes.

Note that no smoothness of `g` beyond the ambient `SMet` structure, no `I.Boundaryless`, no
`T2Space M` and no compactness is used.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle

namespace Work.Diff.EXT.ConnCov

theorem frameCoord_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x₀ : M) (y : E)
    (hy : y ∈ (extChartAt I x₀).target)
    {δ : ℝ} (hδ : 0 < δ)
    (hell : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
      δ * ∑ i, (w i) ^ 2
        ≤ ∑ i, ∑ j, w i * w j * Work.Diff.EXT.chartMatFun g x₀ y i j)
    (v : TangentSpace I ((extChartAt I x₀).symm y)) :
    (∑ p, |((Work.Diff.EXT.bB (E := E)).coord p)
        ((FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
          ((extChartAt I x₀).symm y) v)|)
      ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) / δ)
          * Real.sqrt (g.inner ((extChartAt I x₀).symm y) v v) := by
  classical
  -- notation: the chart point `q`, the trivialization at `x₀`, and the coordinates of `v` in it
  let q : M := (extChartAt I x₀).symm y
  let triv := FiberBundle.trivializationAt E (TangentSpace I) x₀
  let W : E := triv.continuousLinearMapAt ℝ q v
  let c : Fin (Module.finrank ℝ E) → ℝ := fun i => (Work.Diff.EXT.bB (E := E)).coord i W
  change (∑ i, |c i|) ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) / δ) * Real.sqrt (g.inner q v v)
  -- `q` lies in the source of the chart at `x₀`, hence in the base set of the trivialization
  have hqc : q ∈ (chartAt H x₀).source := by
    have h1 : q ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hy
    rwa [extChartAt_source] at h1
  have hbase : q ∈ triv.baseSet := by
    show q ∈ (FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet
    rw [TangentBundle.trivializationAt_baseSet]
    exact hqc
  -- the trivialization is inverse to the frame
  have hsym : triv.symmL ℝ q W = v :=
    Trivialization.symmL_continuousLinearMapAt _ (R := ℝ) hbase v
  -- the coefficients of `W` in the basis `bB`
  have hrepr : (∑ i, (Work.Diff.EXT.bB (E := E)).coord i W
      • (Work.Diff.EXT.bB (E := E)) i) = W := by
    rw [show (∑ i, (Work.Diff.EXT.bB (E := E)).coord i W • (Work.Diff.EXT.bB (E := E)) i)
        = ∑ i, ((Work.Diff.EXT.bB (E := E)).repr W) i • (Work.Diff.EXT.bB (E := E)) i from
      Finset.sum_congr rfl (fun i _ => by rw [Module.Basis.coord_apply])]
    exact Module.Basis.sum_repr _ W
  -- `v` is the combination of the frame vectors with the coefficients `c`
  have hsum : (∑ i, c i • Submission.Geodesic.frameVector (I := I) x₀ q
      (Work.Diff.EXT.bB (E := E) i)) = v := by
    have h1 : (∑ i, c i • Submission.Geodesic.frameVector (I := I) x₀ q
        (Work.Diff.EXT.bB (E := E) i))
        = ∑ i, triv.symmL ℝ q (c i • Work.Diff.EXT.bB (E := E) i) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul]
      rfl
    rw [h1, ← map_sum]
    show triv.symmL ℝ q (∑ i, (Work.Diff.EXT.bB (E := E)).coord i W
      • (Work.Diff.EXT.bB (E := E)) i) = v
    rw [hrepr, hsym]
  -- the metric of `v` is the quadratic form of the chart matrix
  have hmetric : (∑ i, ∑ j, c i * c j * Work.Diff.EXT.chartMatFun g x₀ y i j)
      = g.inner q v v := by
    have h := Work.Diff.EXT.sum_chartMatFun_eq_inner (I := I) (M := M) g x₀ y c
    rw [hsum] at h
    exact h
  -- hence the ellipticity hypothesis controls the sum of the squares of the coefficients
  have hbound : δ * ∑ i, (c i) ^ 2 ≤ g.inner q v v := by
    have h := hell c
    rw [hmetric] at h
    exact h
  -- Cauchy–Schwarz
  have hCS : (∑ i, |c i|) ^ 2 ≤ (Module.finrank ℝ E : ℝ) * ∑ i, (c i) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
      (fun _ : Fin (Module.finrank ℝ E) => (1 : ℝ)) (fun i => |c i|)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, sq_abs, mul_assoc] using h
  have hS_le : ∑ i, (c i) ^ 2 ≤ g.inner q v v / δ := by
    rw [le_div_iff₀ hδ]
    simpa [mul_comm] using hbound
  have hmain : (∑ i, |c i|) ^ 2 ≤ (Module.finrank ℝ E : ℝ) / δ * g.inner q v v := by
    calc (∑ i, |c i|) ^ 2 ≤ (Module.finrank ℝ E : ℝ) * ∑ i, (c i) ^ 2 := hCS
      _ ≤ (Module.finrank ℝ E : ℝ) * (g.inner q v v / δ) :=
          mul_le_mul_of_nonneg_left hS_le (Nat.cast_nonneg _)
      _ = (Module.finrank ℝ E : ℝ) / δ * g.inner q v v := by ring
  calc (∑ i, |c i|) ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) / δ * g.inner q v v) :=
        Real.le_sqrt_of_sq_le hmain
    _ = Real.sqrt ((Module.finrank ℝ E : ℝ) / δ) * Real.sqrt (g.inner q v v) :=
        Real.sqrt_mul (by positivity) _

end Work.Diff.EXT.ConnCov
