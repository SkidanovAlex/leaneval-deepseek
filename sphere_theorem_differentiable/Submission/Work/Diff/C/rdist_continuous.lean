import Mathlib
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the Riemannian distance `rdist q ·`

`Work.Diff.C.rdist I q y` is by definition `(Manifold.riemannianEDist I q y).toReal`, where
`Manifold.riemannianEDist I q y : ℝ≥0∞` is Mathlib's extended Riemannian distance (the infimum of
the lengths of `C¹` paths from `q` to `y`, hence `⊤` when no such path exists).

`ENNReal.toReal` is discontinuous at `⊤`, so the only obstruction to continuity of `rdist q ·` is
a point where `riemannianEDist I q ·` jumps between finite values and `⊤`.  The two observations
that rule this out are both *local* and use only Mathlib's
`eventually_riemannianEDist_le_edist_extChartAt`:

* for every `a`, `riemannianEDist I a z` is finite for all `z` in a neighbourhood of `a`, because
  it is bounded there by `C * edist (extChartAt I a a) (extChartAt I a z)` for a constant `C` and
  `edist` of points of the model space `E` is finite;
* consequently both `S := {y | riemannianEDist I q y < ⊤}` and its complement
  `F := {y | riemannianEDist I q y = ⊤}` are open: if `y ∈ S` then `q`-reachability spreads to a
  neighbourhood of `y` (triangle inequality and finiteness near `y`), and if `y ∈ F` then the
  triangle inequality forces `∈ F` for every point in a neighbourhood of `y` (a finite-distance
  neighbour would make `y` itself finite).

Hence `rdist q ·` is continuous: it vanishes identically on the open set `F`, while on the open
set `S` the triangle inequality gives `|rdist q y - rdist q x| ≤ rdist x y` and `rdist x · → 0` at
`x`.  No connectedness, completeness, compactness or regularity of `M` is needed.
-/

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Mathlib gives `IsContinuousRiemannianBundle` for free from the smooth Riemannian bundle
(only the smoothness level cannot be guessed by the instance search). -/
private instance isContinuousRiemannianBundle_i :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  Submission.EDist.isContinuousRiemannianBundle_infty (I := I) (M := M)

/-- **The extended Riemannian distance from a fixed point is locally finite.**  This is the
content of the local chart bound `eventually_riemannianEDist_le_edist_extChartAt`: the bound
involves `edist` in the (finite dimensional, complete) model space, hence is finite. -/
private theorem rdist_eventually_lt_top (a : M) :
    ∀ᶠ z in 𝓝 a, Manifold.riemannianEDist I a z < ⊤ := by
  obtain ⟨C, _hCpos, hC⟩ := eventually_riemannianEDist_le_edist_extChartAt (I := I) (M := M) a
  filter_upwards [hC] with z hz
  exact lt_of_le_of_lt hz (ENNReal.mul_lt_top ENNReal.coe_lt_top (edist_lt_top _ _))

/-- **The set of points at infinite Riemannian distance from `q` is open.**  Indeed, if
`riemannianEDist I q a = ⊤` and `z` is a point with `riemannianEDist I a z < ⊤` (which holds on a
neighbourhood of `a`), then `riemannianEDist I q z = ⊤`, for otherwise the triangle inequality
`riemannianEDist I q a ≤ riemannianEDist I q z + riemannianEDist I z a` would make
`riemannianEDist I q a` finite. -/
private theorem isOpen_setOf_riemannianEDist_eq_top (q : M) :
    IsOpen {y : M | Manifold.riemannianEDist I q y = ⊤} := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  filter_upwards [rdist_eventually_lt_top (I := I) (M := M) a] with z hz
  by_contra hz'
  have hza : Manifold.riemannianEDist I z a < ⊤ := by
    rw [Manifold.riemannianEDist_comm]; exact hz
  have hsum : Manifold.riemannianEDist I q z + Manifold.riemannianEDist I z a < ⊤ :=
    ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hz', hza⟩
  have htri := Manifold.riemannianEDist_triangle (I := I) (x := q) (y := z) (z := a)
  rw [ha] at htri
  exact absurd htri (not_le.mpr hsum)

/-- **`rdist q ·` is continuous**, for every metric manifold `M` and every base point `q`
(no connectedness, compactness or regularity of `M` is required). -/
theorem rdist_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (q : M) : Continuous (fun y : M => Work.Diff.C.rdist (I := I) q y) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : Manifold.riemannianEDist I q x = ⊤
  · -- Case `x` at infinite distance from `q`: `rdist q ·` vanishes on a neighbourhood of `x`.
    have hmem : {y : M | Manifold.riemannianEDist I q y = ⊤} ∈ 𝓝 x :=
      (isOpen_setOf_riemannianEDist_eq_top (I := I) (M := M) q).mem_nhds hx
    have hev : (fun y : M => Work.Diff.C.rdist (I := I) q y)
        =ᶠ[𝓝 x] (fun _ => Work.Diff.C.rdist (I := I) q x) := by
      filter_upwards [hmem] with y hy
      unfold Work.Diff.C.rdist
      rw [hy, hx]
    exact tendsto_const_nhds.congr' hev.symm
  · -- Case `x` at finite distance from `q`: the triangle inequality bounds the variation of
    -- `rdist q ·` by `rdist x ·`, which tends to `0` at `x`.
    have hbound : ∀ᶠ y in 𝓝 x,
        |Work.Diff.C.rdist (I := I) q y - Work.Diff.C.rdist (I := I) q x|
          ≤ Work.Diff.C.rdist (I := I) x y := by
      filter_upwards [rdist_eventually_lt_top (I := I) (M := M) x] with y hyx
      have hyq : Manifold.riemannianEDist I q y < ⊤ := by
        refine lt_of_le_of_lt
          (Manifold.riemannianEDist_triangle (I := I) (x := q) (y := x) (z := y)) ?_
        exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hx, hyx⟩
      have h1 : Work.Diff.C.rdist (I := I) q y
          ≤ Work.Diff.C.rdist (I := I) q x + Work.Diff.C.rdist (I := I) x y := by
        unfold Work.Diff.C.rdist
        calc (Manifold.riemannianEDist I q y).toReal
            ≤ (Manifold.riemannianEDist I q x + Manifold.riemannianEDist I x y).toReal :=
              ENNReal.toReal_mono (by rw [ENNReal.add_ne_top]; exact ⟨hx, hyx.ne⟩)
                (Manifold.riemannianEDist_triangle (I := I))
          _ ≤ (Manifold.riemannianEDist I q x).toReal
                + (Manifold.riemannianEDist I x y).toReal := ENNReal.toReal_add_le
      have h2 : Work.Diff.C.rdist (I := I) q x
          ≤ Work.Diff.C.rdist (I := I) q y + Work.Diff.C.rdist (I := I) x y := by
        unfold Work.Diff.C.rdist
        have hcomm : Manifold.riemannianEDist I y x = Manifold.riemannianEDist I x y :=
          Manifold.riemannianEDist_comm (I := I)
        calc (Manifold.riemannianEDist I q x).toReal
            ≤ (Manifold.riemannianEDist I q y + Manifold.riemannianEDist I y x).toReal :=
              ENNReal.toReal_mono
                (by rw [ENNReal.add_ne_top]; exact ⟨hyq.ne, by rw [hcomm]; exact hyx.ne⟩)
                (Manifold.riemannianEDist_triangle (I := I))
          _ = (Manifold.riemannianEDist I q y + Manifold.riemannianEDist I x y).toReal := by
                rw [hcomm]
          _ ≤ (Manifold.riemannianEDist I q y).toReal
                + (Manifold.riemannianEDist I x y).toReal := ENNReal.toReal_add_le
      rw [abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    -- `rdist x · → 0` at `x`, through the local chart bound.
    obtain ⟨C, _hCpos, hC⟩ := eventually_riemannianEDist_le_edist_extChartAt (I := I) (M := M) x
    have hH : Tendsto (fun y : M =>
        (↑C * edist (extChartAt I x x) (extChartAt I x y) : ℝ≥0∞).toReal) (𝓝 x) (𝓝 0) := by
      have hchart : ContinuousAt (fun y : M => dist (extChartAt I x x) (extChartAt I x y)) x :=
        continuousAt_const.dist (continuousAt_extChartAt x)
      have h2c : ContinuousAt
          (fun y : M => (C : ℝ) * dist (extChartAt I x x) (extChartAt I x y)) x :=
        hchart.const_mul (C : ℝ)
      have h3 : Tendsto
          (fun y : M => (C : ℝ) * dist (extChartAt I x x) (extChartAt I x y)) (𝓝 x) (𝓝 0) := by
        have := h2c.tendsto
        simpa using this
      refine h3.congr' ?_
      filter_upwards with y
      rw [ENNReal.toReal_mul, ENNReal.coe_toReal, edist_dist, ENNReal.toReal_ofReal dist_nonneg]
    have hG : Tendsto (fun y : M => Work.Diff.C.rdist (I := I) x y) (𝓝 x) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hH ?_ ?_
      · exact Eventually.of_forall fun y => ENNReal.toReal_nonneg
      · filter_upwards [hC] with y hy
        unfold Work.Diff.C.rdist
        exact ENNReal.toReal_mono (ENNReal.mul_lt_top ENNReal.coe_lt_top (edist_lt_top _ _)).ne hy
    have habs : Tendsto (fun y : M =>
        |Work.Diff.C.rdist (I := I) q y - Work.Diff.C.rdist (I := I) q x|) (𝓝 x) (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hG
        (Eventually.of_forall fun y => abs_nonneg _) hbound
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using habs)

end Work.Diff.C
