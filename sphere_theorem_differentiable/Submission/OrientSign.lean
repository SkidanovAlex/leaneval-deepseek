import Submission.FundSol
import Submission.Commons.Topology.exists_grid_forall_mapsTo_chartAt_of_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sign of the chart transitions, and the sign of a chart-covered loop

This is the combinatorial chapter of the determinant theorem `det P = 1` for the holonomy of a closed
curve in a simply connected manifold (Roadmap §115, §116).

## §1–3 The sign of a chart transition

* `chartTransition z z' x` — the change of fibre coordinates of the tangent bundle between the charts
  `z` and `z'` at the point `x`; `chartDet z z' x` — its determinant; **`chartSign z z' x`** — its
  sign (`+1` when the transition preserves the orientation, `-1` otherwise).  It is always `±1`.
* The basic properties: `chartTransition_apply` (the bridge to the tangent-bundle core
  `tangentCoordChange`), `chartDet_ne_zero` (the transition is a linear equivalence),
  `chartDet_self`, `chartDet_mul` and, at the level of signs, **`chartSign_mul`**, **`chartSign_self`**,
  **`chartSign_inv`**, and the **local constancy** `chartSign_const_of_continuousOn` (a chart
  transition's sign is constant along a continuous path staying in the overlap of the two charts).

## §4 The sign of a chart-covered loop

* `Partition a b` (a partition `a = t 0 < ⋯ < t N = b`), `IsChartLoop P γ z` (a family of charts, one
  per piece, each covering its piece and the far junction, cyclic: `z N = z 0`),
  **`loopSignOf P γ z`** — the product of the transition signs at the junctions.
* **`loopSignOf_eq_one_of_const`** — telescoping when all junctions map to the same point.
* **`loopSignOf_congr`** — the sign does not depend on the choice of the charts (fixed partition).

## §5 The grid argument

* **`loopSignOf_eq_one_of_grid`** — for a continuous map `F` of the square `Icc 0 1 ×ˢ Icc 0 1` with
  `F (σ, 0) = F (σ, 1) = p`, `F (1, τ) = p` and a grid whose cells map into the sources of the
  corresponding `chartAt`, the chart-covered loop `τ ↦ F (0, τ)` has sign `1`.  This is the
  combinatorial content of "the holonomy of a closed curve in a simply connected manifold is
  orientation preserving": each column of the grid has constant sign in the horizontal parameter,
  adjacent columns agree at the shared boundary, and the last column is the constant loop.

## §6–7 The subdivision lemma, and a null-homotopic loop has sign `1`

* **`loopSignOf_refine`** — the sign of a chart-covered loop is unchanged when the partition is
  refined and the *coarser* charts are reused on the pieces (the new junctions contribute
  `chartSign_self = 1` and the surviving factors are the coarse ones, reindexed along the jumps).
  Together with `loopSignOf_congr` this gives partition independence as soon as a common refinement
  is constructed.
* **`exists_chartLoop_of_simplyConnected`** — for `[SimplyConnectedSpace M]`, `p : M` and a loop
  `γ : Path p p`, there is a partition and a chart family covering `γ` whose loop sign is `1`:
  the `Path.Homotopy` of `γ` with the constant loop is turned into a continuous map `F` of the
  square (via `Set.projIcc`, so that `F` is total), the grid lemma
  `Commons.Topology.exists_grid_forall_mapsTo_chartAt_of_le` produces a grid, and
  `loopSignOf_eq_one_of_grid` closes the argument.  **This is the combinatorial content of "the
  holonomy of a closed curve in a simply connected manifold is orientation preserving".**

The remaining input for `det P = 1` — the identification of `loopSignOf` with the sign of the
determinant of the parallel transport, and the reconstruction of the transport from the grid's own
chart family (which is what the partition of `exists_chartLoop_of_simplyConnected` provides) — is
analysed in `Submission/Roadmap.lean` §§115–117.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Submission.OrientSign

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]

variable [I.Boundaryless] [Nontrivial E]

/-- The change of fibre coordinates of the tangent bundle between the chart `z` and the chart `z'`,
at the point `x`. -/
def chartTransition (z z' x : M) : E →L[ℝ] E :=
  Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) z)
    (trivializationAt E (TangentSpace I) z') x

/-- The determinant of the chart transition `z → z'` at `x`. -/
def chartDet (z z' x : M) : ℝ := LinearMap.det ((chartTransition (I := I) z z' x) : E →ₗ[ℝ] E)

/-- The **sign of the chart transition** `z → z'` at `x`: `+1` if the transition preserves the
orientation, `-1` otherwise.  It is always `±1` (the value `-1` is also taken outside the overlap of
the two charts, where the determinant vanishes). -/
def chartSign (z z' x : M) : ℝ := if 0 < chartDet (I := I) z z' x then 1 else -1

theorem chartSign_eq_ite (z z' x : M) :
    chartSign (I := I) z z' x = if 0 < chartDet (I := I) z z' x then 1 else -1 := rfl

theorem chartSign_eq_one_or_neg_one (z z' x : M) :
    chartSign (I := I) z z' x = 1 ∨ chartSign (I := I) z z' x = -1 := by
  rw [chartSign]; split <;> simp

theorem chartSign_ne_zero (z z' x : M) : chartSign (I := I) z z' x ≠ 0 := by
  rcases chartSign_eq_one_or_neg_one (I := I) z z' x with h | h <;> rw [h] <;> norm_num

/-! ## §1 The determinant of a chart transition -/

theorem mem_baseSet_chartTriv (z : M) :
    (trivializationAt E (TangentSpace I) z).baseSet = (chartAt H z).source :=
  TangentBundle.trivializationAt_baseSet z

/-- **The bridge between the fibre trivialization and the tangent-bundle core**: on the overlap of
the two charts, the change of fibre coordinates of the tangent bundle is the derivative of the chart
transition. -/
theorem chartTransition_apply {z z' x : M}
    (hx : x ∈ (chartAt H z).source ∩ (chartAt H z').source) (v : E) :
    chartTransition (I := I) z z' x v = tangentCoordChange I z z' x v := by
  have hb : x ∈ (trivializationAt E (TangentSpace I) z).baseSet ∩
      (trivializationAt E (TangentSpace I) z').baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  have key := VectorBundleCore.trivializationAt_coordChange_eq (tangentBundleCore I M) hb v
  change (Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) z)
    (trivializationAt E (TangentSpace I) z') x) v = tangentCoordChange I z z' x v
  exact key

theorem chartDet_eq (z z' x : M)
    (hx : x ∈ (chartAt H z).source ∩ (chartAt H z').source) :
    chartDet (I := I) z z' x = LinearMap.det (tangentCoordChange I z z' x).toLinearMap := by
  have h : (chartTransition (I := I) z z' x) = tangentCoordChange I z z' x := by
    ext v; exact chartTransition_apply (I := I) hx v
  rw [chartDet, h]

theorem chartDet_ne_zero {z z' x : M}
    (hx : x ∈ (chartAt H z).source ∩ (chartAt H z').source) :
    chartDet (I := I) z z' x ≠ 0 := by
  have h := LinearEquiv.isUnit_det'
    (Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) z)
      (trivializationAt E (TangentSpace I) z') x).toLinearEquiv
  exact h.ne_zero

theorem chartDet_self {z x : M} (hx : x ∈ (chartAt H z).source) :
    chartDet (I := I) z z x = 1 := by
  have hx' : x ∈ (chartAt H z).source ∩ (chartAt H z).source := ⟨hx, hx⟩
  have hb : x ∈ (trivializationAt E (TangentSpace I) z).baseSet ∩
      (trivializationAt E (TangentSpace I) z).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx'
  have hcoe : ⇑(Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) z)
      (trivializationAt E (TangentSpace I) z) x) = ⇑(LinearEquiv.refl ℝ E) := by
    rw [Trivialization.coe_coordChangeL _ _ hb, LinearEquiv.symm_trans_self]
  have hfun : (Trivialization.coordChangeL ℝ (trivializationAt E (TangentSpace I) z)
      (trivializationAt E (TangentSpace I) z) x) = 1 := by
    ext v
    exact congr_fun hcoe v
  rw [chartDet, chartTransition, hfun]
  exact map_one LinearMap.det

/-- **The determinant of the composite chart transition is the product.** -/
theorem chartDet_mul {z z' z'' x : M}
    (hx : x ∈ (chartAt H z).source ∩ (chartAt H z').source ∩ (chartAt H z'').source) :
    chartDet (I := I) z z' x * chartDet (I := I) z' z'' x = chartDet (I := I) z z'' x := by
  have hx1 : x ∈ (chartAt H z).source ∩ (chartAt H z').source := ⟨hx.1.1, hx.1.2⟩
  have hx2 : x ∈ (chartAt H z').source ∩ (chartAt H z'').source := ⟨hx.1.2, hx.2⟩
  have hx3 : x ∈ (chartAt H z).source ∩ (chartAt H z'').source := ⟨hx.1.1, hx.2⟩
  rw [chartDet_eq (I := I) z z' x hx1, chartDet_eq (I := I) z' z'' x hx2,
    chartDet_eq (I := I) z z'' x hx3]
  have hcomp : (tangentCoordChange I z z'' x).toLinearMap
      = (tangentCoordChange I z' z'' x).toLinearMap.comp (tangentCoordChange I z z' x).toLinearMap := by
    ext v
    change (tangentCoordChange I z z'' x) v
      = (tangentCoordChange I z' z'' x) ((tangentCoordChange I z z' x) v)
    exact (VectorBundleCore.coordChange_comp (tangentBundleCore I M) (i := achart H z) (j := achart H z')
      (k := achart H z'') (x := x) (v := v) ⟨⟨by exact hx.1.1, by exact hx.1.2⟩, by exact hx.2⟩).symm
  rw [hcomp, LinearMap.det_comp, mul_comm]


/-! ## §2 Multiplicativity and the sign -/

theorem ite_pos_mul_ite {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (if 0 < a * b then (1 : ℝ) else -1)
      = (if 0 < a then (1 : ℝ) else -1) * (if 0 < b then (1 : ℝ) else -1) := by
  rcases lt_trichotomy a 0 with h | h | h
  · rcases lt_trichotomy b 0 with h' | h' | h'
    · have hp : 0 < a * b := mul_pos_of_neg_of_neg h h'
      rw [if_pos hp, if_neg (not_lt.mpr h.le), if_neg (not_lt.mpr h'.le)]; norm_num
    · exact absurd h' hb
    · have hp : ¬ 0 < a * b := not_lt.mpr (mul_neg_of_neg_of_pos h h').le
      rw [if_neg hp, if_neg (not_lt.mpr h.le), if_pos h']; norm_num
  · exact absurd h ha
  · rcases lt_trichotomy b 0 with h' | h' | h'
    · have hp : ¬ 0 < a * b := not_lt.mpr (mul_neg_of_pos_of_neg h h').le
      rw [if_neg hp, if_pos h, if_neg (not_lt.mpr h'.le)]; norm_num
    · exact absurd h' hb
    · have hp : 0 < a * b := mul_pos h h'
      rw [if_pos hp, if_pos h, if_pos h']; norm_num

/-- **Multiplicativity of the sign of chart transitions** at a point of the triple overlap. -/
theorem chartSign_mul {z z' z'' x : M}
    (hx : x ∈ (chartAt H z).source ∩ (chartAt H z').source ∩ (chartAt H z'').source) :
    chartSign (I := I) z z' x * chartSign (I := I) z' z'' x = chartSign (I := I) z z'' x := by
  have hx1 : x ∈ (chartAt H z).source ∩ (chartAt H z').source := ⟨hx.1.1, hx.1.2⟩
  have hx2 : x ∈ (chartAt H z').source ∩ (chartAt H z'').source := ⟨hx.1.2, hx.2⟩
  rw [chartSign_eq_ite, chartSign_eq_ite, chartSign_eq_ite,
    ← ite_pos_mul_ite (chartDet_ne_zero (I := I) hx1) (chartDet_ne_zero (I := I) hx2),
    chartDet_mul (I := I) hx]

/-- The sign of the transition of a chart with itself is `1`. -/
theorem chartSign_self {z x : M} (hx : x ∈ (chartAt H z).source) :
    chartSign (I := I) z z x = 1 := by
  rw [chartSign_eq_ite, chartDet_self (I := I) hx]; norm_num

/-- The signs of the two opposite transitions are inverse to each other. -/
theorem chartSign_inv {z z' x : M} (hx : x ∈ (chartAt H z).source ∩ (chartAt H z').source) :
    chartSign (I := I) z z' x * chartSign (I := I) z' z x = 1 := by
  have hx' : x ∈ (chartAt H z).source ∩ (chartAt H z').source ∩ (chartAt H z).source :=
    ⟨hx, hx.1⟩
  rw [chartSign_mul (I := I) hx', chartSign_self (I := I) hx.1]

/-! ## §3 Constancy along a continuous path in the overlap -/

theorem continuousOn_chartDet {z z' : M} :
    ContinuousOn (fun x => chartDet (I := I) z z' x)
      ((chartAt H z).source ∩ (chartAt H z').source) := by
  have hb : (trivializationAt E (TangentSpace I) z).baseSet ∩
      (trivializationAt E (TangentSpace I) z').baseSet
      = (chartAt H z).source ∩ (chartAt H z').source := by
    rw [TangentBundle.trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet]
  rw [← hb]
  exact Submission.FundSol.continuous_linearMap_det.comp_continuousOn
    (continuousOn_coordChange (R := ℝ) _ _)

theorem continuousOn_chartDet_comp {z z' : M} {γ : ℝ → M} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b))
    (hsub : ∀ t ∈ Icc a b, γ t ∈ (chartAt H z).source ∩ (chartAt H z').source) :
    ContinuousOn (fun t => chartDet (I := I) z z' (γ t)) (Icc a b) :=
  (continuousOn_chartDet (I := I) (z := z) (z' := z')).comp hγ (fun t ht => hsub t ht)

/-- The sign of a continuous never-vanishing real function on a closed interval is constant. -/
theorem ite_pos_const_of_continuousOn_nonzero {f : ℝ → ℝ} {a b t : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hne : ∀ x ∈ Icc a b, f x ≠ 0) (ht : t ∈ Icc a b) :
    (if 0 < f t then (1 : ℝ) else -1) = (if 0 < f a then (1 : ℝ) else -1) := by
  have hiff : 0 < f t ↔ 0 < f a := by
    constructor
    · intro hft
      by_contra hfa
      rw [not_lt] at hfa
      have hfa' : f a < 0 := lt_of_le_of_ne hfa ((hne a ⟨le_rfl, hab⟩))
      have him := intermediate_value_Icc (show a ≤ t from ht.1)
        (hf.mono (fun x hx => ⟨hx.1, le_trans hx.2 ht.2⟩)) ⟨hfa'.le, hft.le⟩
      obtain ⟨c, hc, hfc⟩ := him
      exact hne c ⟨hc.1, le_trans hc.2 ht.2⟩ hfc
    · intro hfa
      by_contra hft
      rw [not_lt] at hft
      have hft' : f t < 0 := lt_of_le_of_ne hft (hne t ht)
      have him := intermediate_value_Icc' (show a ≤ t from ht.1)
        (hf.mono (fun x hx => ⟨hx.1, le_trans hx.2 ht.2⟩)) ⟨hft'.le, hfa.le⟩
      obtain ⟨c, hc, hfc⟩ := him
      exact hne c ⟨hc.1, le_trans hc.2 ht.2⟩ hfc
  by_cases h : 0 < f t
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]


/-- **The sign of a chart transition is constant along a path contained in the overlap.** -/
theorem chartSign_const_of_continuousOn {z z' : M} {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b))
    (hsub : ∀ t ∈ Icc a b, γ t ∈ (chartAt H z).source ∩ (chartAt H z').source) :
    ∀ t ∈ Icc a b, chartSign (I := I) z z' (γ t) = chartSign (I := I) z z' (γ a) := by
  intro t ht
  rw [chartSign_eq_ite, chartSign_eq_ite]
  exact ite_pos_const_of_continuousOn_nonzero hab
    (continuousOn_chartDet_comp (I := I) (z := z) (z' := z') hγ hsub)
    (fun x hx => chartDet_ne_zero (I := I) (hsub x hx)) ht

/-! ## §4 A partition of a closed curve and the sign of a chart-covered loop -/

variable {a b : ℝ} {γ : ℝ → M}

/-- A partition `a = t 0 < ⋯ < t N = b` of the parameter interval of a closed curve. -/
structure Partition (a b : ℝ) where
  N : ℕ
  t : ℕ → ℝ
  t_zero : t 0 = a
  t_last : t N = b
  mono : ∀ k < N, t k < t (k+1)

/-- `z` is a **chart family** for the partition `P` of the closed curve `γ`: the chart `z k` covers
the piece `[t k, t (k+1)]`, the chart `z (k+1)` covers the junction `t (k+1)` from the other side,
and the family is cyclic (`z N = z 0`). -/
def IsChartLoop (P : Partition a b) (γ : ℝ → M) (z : ℕ → M) : Prop :=
  (∀ k < P.N, ∀ x ∈ Icc (P.t k) (P.t (k+1)), γ x ∈ (chartAt H (z k)).source) ∧
  (∀ k < P.N, γ (P.t (k+1)) ∈ (chartAt H (z (k+1))).source) ∧
  z P.N = z 0

/-- **The sign of a chart-covered loop**: the product of the signs of the chart transitions at the
junctions of the partition. -/
def loopSignOf (P : Partition a b) (γ : ℝ → M) (z : ℕ → M) : ℝ :=
  ∏ k ∈ Finset.range P.N, chartSign (I := I) (z k) (z (k+1)) (γ (P.t (k+1)))

variable {P : Partition a b} {z z' : ℕ → M} {p : M}

theorem isChartLoop_src_left (hP : IsChartLoop (H := H) P γ z) {k : ℕ} (hk : k < P.N) :
    γ (P.t k) ∈ (chartAt H (z k)).source :=
  hP.1 k hk (P.t k) ⟨le_rfl, (P.mono k hk).le⟩

theorem isChartLoop_src_right (hP : IsChartLoop (H := H) P γ z) {k : ℕ} (hk : k < P.N) :
    γ (P.t (k+1)) ∈ (chartAt H (z k)).source :=
  hP.1 k hk (P.t (k+1)) ⟨(P.mono k hk).le, le_rfl⟩

theorem isChartLoop_junction (hP : IsChartLoop (H := H) P γ z) {k : ℕ} (hk : k < P.N) :
    γ (P.t (k+1)) ∈ (chartAt H (z k)).source ∩ (chartAt H (z (k+1))).source :=
  ⟨isChartLoop_src_right hP hk, hP.2.1 k hk⟩

/-- **Telescoping**: if all junctions of the partition map to the same point `p`, the sign of the
loop is `1`. -/
theorem loopSignOf_eq_one_of_const (hP : IsChartLoop (H := H) P γ z) {p : M}
    (hp : ∀ k, k ≤ P.N → γ (P.t k) = p)
    (hsrc : ∀ k, k ≤ P.N → p ∈ (chartAt H (z k)).source) : loopSignOf (I := I) P γ z = 1 := by
  have htel : ∀ m, m ≤ P.N → (∏ k ∈ Finset.range m, chartSign (I := I) (z k) (z (k+1)) p)
      = chartSign (I := I) (z 0) (z m) p := by
    intro m
    induction m with
    | zero => intro _; exact (chartSign_self (I := I) (hsrc 0 (Nat.zero_le _))).symm
    | succ n ih =>
      intro hn
      have hn' : n ≤ P.N := by omega
      rw [Finset.prod_range_succ, ih hn',
        chartSign_mul (I := I) (z := z 0) (z' := z n) (z'' := z (n+1))
          ⟨⟨hsrc 0 (Nat.zero_le _), hsrc n hn'⟩, hsrc (n+1) hn⟩]
  rw [loopSignOf, Finset.prod_congr rfl (fun k hk => ?_), htel P.N le_rfl,
    show z P.N = z 0 from hP.2.2]
  · exact chartSign_self (I := I) (hsrc 0 (Nat.zero_le _))
  · rw [hp (k+1) (by have := Finset.mem_range.mp hk; omega)]


theorem Partition.mono_le (P : Partition a b) : ∀ {i j : ℕ}, i ≤ j → j ≤ P.N → P.t i ≤ P.t j := by
  intro i j hij hj
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ n ih =>
    rcases Nat.lt_or_eq_of_le hij with h | h
    · exact le_trans (ih (by omega) (by omega)) (P.mono n (by omega)).le
    · rw [h]

theorem prod_range_succ_shift {f : ℕ → ℝ} {N : ℕ} (hN : f N = f 0) (h0 : f 0 ≠ 0) :
    (∏ j ∈ Finset.range N, f (j+1)) = ∏ j ∈ Finset.range N, f j := by
  have h1 : (∏ j ∈ Finset.range (N+1), f j) = (∏ j ∈ Finset.range N, f (j+1)) * f 0 :=
    Finset.prod_range_succ' f N
  have h2 : (∏ j ∈ Finset.range (N+1), f j) = (∏ j ∈ Finset.range N, f j) * f N :=
    Finset.prod_range_succ f N
  have h : f 0 * (∏ j ∈ Finset.range N, f (j+1)) = f 0 * (∏ j ∈ Finset.range N, f j) := by
    rw [mul_comm (f 0) (∏ j ∈ Finset.range N, f (j+1)), ← h1, h2, hN, mul_comm]
  exact mul_left_cancel₀ h0 h

/-- **The sign of the loop does not depend on the choice of the charts** (for a fixed partition). -/
theorem loopSignOf_congr {P : Partition a b} {z z' : ℕ → M}
    (hclosed : γ a = γ b) (hγcont : ContinuousOn γ (Icc a b))
    (hz : IsChartLoop (H := H) P γ z) (hz' : IsChartLoop (H := H) P γ z') :
    loopSignOf (I := I) P γ z = loopSignOf (I := I) P γ z' := by
  have hzr : ∀ k < P.N, γ (P.t (k+1)) ∈ (chartAt H (z k)).source :=
    fun k hk => isChartLoop_src_right hz hk
  have hz1r : ∀ k < P.N, γ (P.t (k+1)) ∈ (chartAt H (z' k)).source :=
    fun k hk => isChartLoop_src_right hz' hk
  have hzl : ∀ k < P.N, γ (P.t (k+1)) ∈ (chartAt H (z (k+1))).source :=
    fun k hk => hz.2.1 k hk
  have hz1l : ∀ k < P.N, γ (P.t (k+1)) ∈ (chartAt H (z' (k+1))).source :=
    fun k hk => hz'.2.1 k hk
  -- the insertion
  have hA : ∀ k < P.N, chartSign (I := I) (z k) (z (k+1)) (γ (P.t (k+1)))
      = chartSign (I := I) (z k) (z' k) (γ (P.t (k+1)))
        * chartSign (I := I) (z' k) (z' (k+1)) (γ (P.t (k+1)))
        * chartSign (I := I) (z' (k+1)) (z (k+1)) (γ (P.t (k+1))) := by
    intro k hk
    rw [← chartSign_mul (I := I) (z := z k) (z' := z' k) (z'' := z (k+1))
        ⟨⟨hzr k hk, hz1r k hk⟩, hzl k hk⟩,
      ← chartSign_mul (I := I) (z := z' k) (z' := z' (k+1)) (z'' := z (k+1))
        ⟨⟨hz1r k hk, hz1l k hk⟩, hzl k hk⟩, mul_assoc _ _ _]
  -- the constancy along the pieces, on the left
  have hfirst : (∏ k ∈ Finset.range P.N,
        chartSign (I := I) (z k) (z' k) (γ (P.t (k+1))))
      = ∏ k ∈ Finset.range P.N, chartSign (I := I) (z k) (z' k) (γ (P.t k)) := by
    refine Finset.prod_congr rfl (fun k hk => ?_)
    have hk' := Finset.mem_range.mp hk
    have hmono : Icc (P.t k) (P.t (k+1)) ⊆ Icc a b := fun x hx =>
      ⟨le_trans (le_trans (le_of_eq P.t_zero.symm) (P.mono_le (Nat.zero_le k) hk'.le)) hx.1,
        le_trans hx.2 (le_trans (P.mono_le (by omega) le_rfl) (le_of_eq P.t_last))⟩
    exact chartSign_const_of_continuousOn (I := I) (z := z k) (z' := z' k) (γ := γ)
      (a := P.t k) (b := P.t (k+1)) (P.mono k hk').le
      (hγcont.mono (fun x hx => hmono hx))
      (fun x hx => ⟨hz.1 k hk' x hx, hz'.1 k hk' x hx⟩)
      (P.t (k+1)) ⟨(P.mono k hk').le, le_rfl⟩
  -- the reindexing, on the right
  have hthird : (∏ k ∈ Finset.range P.N,
        chartSign (I := I) (z' (k+1)) (z (k+1)) (γ (P.t (k+1))))
      = ∏ k ∈ Finset.range P.N, chartSign (I := I) (z' k) (z k) (γ (P.t k)) := by
    refine prod_range_succ_shift (N := P.N)
      (f := fun j => chartSign (I := I) (z' j) (z j) (γ (P.t j))) ?_ ?_
    · rw [hz'.2.2, hz.2.2, P.t_last, P.t_zero, hclosed]
    · exact chartSign_ne_zero (I := I) (z' 0) (z 0) (γ (P.t 0))
  -- the correction factors cancel
  have hpair : (∏ k ∈ Finset.range P.N, chartSign (I := I) (z k) (z' k) (γ (P.t k)))
      * (∏ k ∈ Finset.range P.N, chartSign (I := I) (z' k) (z k) (γ (P.t k))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one (fun k hk => ?_)
    have hk' := Finset.mem_range.mp hk
    exact chartSign_inv (I := I)
      ⟨isChartLoop_src_left hz hk', isChartLoop_src_left hz' hk'⟩
  -- assemble
  have hprod : (∏ k ∈ Finset.range P.N,
        chartSign (I := I) (z k) (z (k+1)) (γ (P.t (k+1))))
      = (∏ k ∈ Finset.range P.N,
        chartSign (I := I) (z' k) (z' (k+1)) (γ (P.t (k+1)))) := by
    rw [Finset.prod_congr rfl (fun k hk => hA k (Finset.mem_range.mp hk)),
      Finset.prod_mul_distrib, Finset.prod_mul_distrib, hfirst, hthird]
    set U : ℝ := ∏ k ∈ Finset.range P.N, chartSign (I := I) (z k) (z' k) (γ (P.t k))
    set V : ℝ := ∏ k ∈ Finset.range P.N, chartSign (I := I) (z' k) (z k) (γ (P.t k))
    set W : ℝ := ∏ k ∈ Finset.range P.N, chartSign (I := I) (z' k) (z' (k+1)) (γ (P.t (k+1)))
    have hUV : U * V = 1 := hpair
    change U * W * V = W
    rw [mul_assoc, mul_comm W V, ← mul_assoc, hUV, one_mul]
  simpa only [loopSignOf] using hprod

/-! ## §5 The grid argument -/

variable {F : ℝ × ℝ → M} {p : M}

/-- The chart family of the `i`-th column of a grid: the charts of the cells of that column, with
the last one identified with the first (so that the family is cyclic). -/
def colFamily (y : ℕ → ℕ → M) (L i : ℕ) : ℕ → M := fun j => if j < L then y i j else y i 0

theorem colFamily_of_lt {y : ℕ → ℕ → M} {L i j : ℕ} (hj : j < L) :
    colFamily y L i j = y i j := dif_pos hj

theorem colFamily_of_ge {y : ℕ → ℕ → M} {L i j : ℕ} (hj : ¬ j < L) :
    colFamily y L i j = y i 0 := dif_neg hj

/-- The sign of the `i`-th column of the grid: the sign of the chart-covered loop `F (σ, ·)`, with
the charts of the cells of that column. -/
def colSign (F : ℝ × ℝ → M) (y : ℕ → ℕ → M) (L i : ℕ) (t : ℕ → ℝ) (σ : ℝ) : ℝ :=
  ∏ k ∈ Finset.range L,
    chartSign (I := I) (colFamily y L i k) (colFamily y L i (k+1)) (F (σ, t (k+1)))

/-- A cell condition: the cells of the grid map into the sources of the corresponding charts. -/
def GridCells (F : ℝ × ℝ → M) (Ps Pt : Partition 0 1) (y : ℕ → ℕ → M) : Prop :=
  ∀ i < Ps.N, ∀ j < Pt.N, ∀ q ∈ Icc (Ps.t i) (Ps.t (i+1)) ×ˢ Icc (Pt.t j) (Pt.t (j+1)),
    F q ∈ (chartAt H (y i j)).source

theorem Partition.pos_N (P : Partition 0 1) : 0 < P.N := by
  by_contra h
  have hN : P.N = 0 := Nat.eq_zero_of_not_pos h
  have h := P.t_last
  rw [hN, P.t_zero] at h
  norm_num at h

variable {Ps Pt : Partition 0 1} {y : ℕ → ℕ → M}

theorem isChartLoop_colFamily (hcell : GridCells (H := H) F Ps Pt y)
    (hbase : ∀ σ : ℝ, F (σ, 0) = p) (htop : ∀ σ : ℝ, F (σ, 1) = p)
    {i : ℕ} (hi : i < Ps.N) {σ : ℝ} (hσ : σ ∈ Icc (Ps.t i) (Ps.t (i+1))) :
    IsChartLoop (H := H) Pt (fun τ => F (σ, τ)) (colFamily y Pt.N i) := by
  have hcfL : ∀ k, k < Pt.N → colFamily y Pt.N i k = y i k := fun k hk => colFamily_of_lt hk
  have hcfG : ∀ k, ¬ k < Pt.N → colFamily y Pt.N i k = y i 0 := fun k hk => colFamily_of_ge hk
  refine ⟨?_, ?_, ?_⟩
  · intro k hk q hq
    rw [hcfL k hk]
    exact hcell i hi k hk (σ, q) ⟨hσ, hq⟩
  · intro k hk
    rcases lt_or_ge (k+1) Pt.N with h | h
    · rw [hcfL (k+1) h]
      exact hcell i hi (k+1) h (σ, Pt.t (k+1)) ⟨hσ, ⟨le_rfl, (Pt.mono (k+1) h).le⟩⟩
    · have hkL : k + 1 = Pt.N := by omega
      have h0 : (0 : ℕ) < Pt.N := by omega
      rw [hcfG (k+1) (not_lt.mpr h)]
      show F (σ, Pt.t (k+1)) ∈ (chartAt H (y i 0)).source
      rw [hkL, Pt.t_last, htop σ, ← hbase σ]
      exact hcell i hi 0 h0 (σ, 0) ⟨hσ, ⟨le_of_eq Pt.t_zero,
        le_trans (le_of_eq Pt.t_zero.symm) (Pt.mono 0 h0).le⟩⟩
  · have h0 : (0 : ℕ) < Pt.N := Pt.pos_N
    rw [hcfG Pt.N (not_lt.mpr le_rfl), hcfL 0 h0]

theorem colSign_eq_loopSignOf {i : ℕ} (σ : ℝ) :
    colSign (I := I) F y Pt.N i Pt.t σ
      = loopSignOf (I := I) Pt (fun τ => F (σ, τ)) (colFamily y Pt.N i) := rfl

theorem Partition.t_nonneg (P : Partition 0 1) {j : ℕ} (hj : j ≤ P.N) : 0 ≤ P.t j :=
  le_trans (le_of_eq P.t_zero.symm) (P.mono_le (Nat.zero_le j) hj)

theorem Partition.t_le_one (P : Partition 0 1) {j : ℕ} (hj : j ≤ P.N) : P.t j ≤ 1 :=
  le_trans (P.mono_le (by omega) le_rfl) (le_of_eq P.t_last)

/-- **Constancy of the column sign in the horizontal parameter.** -/
theorem colSign_const (hcell : GridCells (H := H) F Ps Pt y)
    (hF : ContinuousOn F (Icc 0 1 ×ˢ Icc 0 1))
    (hbase : ∀ σ : ℝ, F (σ, 0) = p) (htop : ∀ σ : ℝ, F (σ, 1) = p)
    {i : ℕ} (hi : i < Ps.N) :
    ∀ σ ∈ Icc (Ps.t i) (Ps.t (i+1)),
      colSign (I := I) F y Pt.N i Pt.t σ = colSign (I := I) F y Pt.N i Pt.t (Ps.t i) := by
  intro σ hσ
  refine Finset.prod_congr rfl (fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  have hi1 : i + 1 ≤ Ps.N := hi
  have hslice : ContinuousOn (fun τ : ℝ => F (τ, Pt.t (k+1))) (Icc (Ps.t i) (Ps.t (i+1))) :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn (fun τ hτ =>
      ⟨⟨le_trans (Ps.t_nonneg hi.le) hτ.1, le_trans hτ.2 (Ps.t_le_one hi1)⟩,
        Pt.t_nonneg (by omega), Pt.t_le_one (by omega)⟩)
  have hsub : ∀ τ ∈ Icc (Ps.t i) (Ps.t (i+1)),
      (fun τ : ℝ => F (τ, Pt.t (k+1))) τ ∈ (chartAt H (colFamily y Pt.N i k)).source ∩
        (chartAt H (colFamily y Pt.N i (k+1))).source := by
    intro τ hτ
    have h1 : (τ, Pt.t (k+1)) ∈ Icc (Ps.t i) (Ps.t (i+1)) ×ˢ
        Icc (Pt.t k) (Pt.t (k+1)) := ⟨hτ, ⟨(Pt.mono k hk').le, le_rfl⟩⟩
    refine ⟨?_, ?_⟩
    · rw [colFamily_of_lt (y := y) (L := Pt.N) (i := i) hk']
      exact hcell i hi k hk' (τ, Pt.t (k+1)) h1
    · rcases lt_or_ge (k+1) Pt.N with h | h
      · rw [colFamily_of_lt (y := y) (L := Pt.N) (i := i) h]
        exact hcell i hi (k+1) h (τ, Pt.t (k+1)) ⟨hτ, ⟨le_rfl, (Pt.mono (k+1) h).le⟩⟩
      · have hkL : k + 1 = Pt.N := by omega
        have h0 : (0 : ℕ) < Pt.N := by omega
        rw [colFamily_of_ge (y := y) (L := Pt.N) (i := i) (not_lt.mpr h)]
        show F (τ, Pt.t (k+1)) ∈ (chartAt H (y i 0)).source
        rw [hkL, Pt.t_last, htop τ, ← hbase τ]
        exact hcell i hi 0 h0 (τ, 0) ⟨hτ, ⟨le_of_eq Pt.t_zero,
          le_trans (le_of_eq Pt.t_zero.symm) (Pt.mono 0 h0).le⟩⟩
  exact chartSign_const_of_continuousOn (I := I) (z := colFamily y Pt.N i k)
    (z' := colFamily y Pt.N i (k+1)) (γ := fun τ : ℝ => F (τ, Pt.t (k+1)))
    (a := Ps.t i) (b := Ps.t (i+1)) (Ps.mono i hi).le hslice hsub σ hσ

/-- **The column signs of two adjacent columns agree at the shared boundary.** -/
theorem colSign_eq_colSign_succ (hcell : GridCells (H := H) F Ps Pt y)
    (hF : ContinuousOn F (Icc 0 1 ×ˢ Icc 0 1))
    (hbase : ∀ σ : ℝ, F (σ, 0) = p) (htop : ∀ σ : ℝ, F (σ, 1) = p)
    {i : ℕ} (hi : i + 1 < Ps.N) :
    colSign (I := I) F y Pt.N i Pt.t (Ps.t (i+1))
      = colSign (I := I) F y Pt.N (i+1) Pt.t (Ps.t (i+1)) := by
  have hilt : i < Ps.N := Nat.lt_of_succ_lt hi
  have hi1 : i + 1 ≤ Ps.N := hi.le
  have hσ : Ps.t (i+1) ∈ Icc 0 1 :=
    ⟨Ps.t_nonneg hi1, Ps.t_le_one hi1⟩
  have hslice : ContinuousOn (fun τ : ℝ => F (Ps.t (i+1), τ)) (Icc 0 1) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun τ hτ =>
      ⟨hσ, hτ⟩)
  have hclosed : (fun τ : ℝ => F (Ps.t (i+1), τ)) 0 = (fun τ : ℝ => F (Ps.t (i+1), τ)) 1 := by
    show F (Ps.t (i+1), 0) = F (Ps.t (i+1), 1)
    rw [htop, hbase]
  rw [colSign_eq_loopSignOf (I := I) (i := i) (Ps.t (i+1)),
    colSign_eq_loopSignOf (I := I) (i := i+1) (Ps.t (i+1))]
  exact loopSignOf_congr (I := I) hclosed hslice
    (isChartLoop_colFamily hcell hbase htop hilt ⟨(Ps.mono i hilt).le, le_rfl⟩)
    (isChartLoop_colFamily hcell hbase htop hi ⟨le_rfl, (Ps.mono (i+1) hi).le⟩)

/-- For a chart-covered constant loop the sign is `1`. -/
theorem loopSignOf_const_loop {z : ℕ → M}
    (hloop : IsChartLoop (H := H) Pt (fun τ => F (1, τ)) z) (hend : ∀ τ : ℝ, F (1, τ) = p) :
    loopSignOf (I := I) Pt (fun τ => F (1, τ)) z = 1 := by
  have hpos := Pt.pos_N
  refine loopSignOf_eq_one_of_const (I := I) hloop (fun k _ => hend _) (fun k hk => ?_)
  rcases lt_or_eq_of_le hk with h | h
  · have hk1 : k < Pt.N := h
    have hmem := hloop.1 k hk1 (Pt.t k) ⟨le_rfl, (Pt.mono k hk1).le⟩
    simpa only [hend] using hmem
  · subst h
    have h0 : (0 : ℕ) < Pt.N := hpos
    have hmem := hloop.1 0 h0 (Pt.t 0) ⟨le_rfl, (Pt.mono 0 h0).le⟩
    have hmem' : p ∈ (chartAt H (z 0)).source := by
      simpa only [Pt.t_zero, hend] using hmem
    rwa [hloop.2.2]

/-- **The sign of the last column of the grid is `1`** (the loop there is the constant loop). -/
theorem colSign_one_eq_one (hcell : GridCells (H := H) F Ps Pt y)
    (hbase : ∀ σ : ℝ, F (σ, 0) = p) (htop : ∀ σ : ℝ, F (σ, 1) = p)
    (hend : ∀ τ : ℝ, F (1, τ) = p) :
    colSign (I := I) F y Pt.N (Ps.N - 1) Pt.t 1 = 1 := by
  have hpos := Ps.pos_N
  have hlast : Ps.N - 1 + 1 = Ps.N := Nat.succ_pred_eq_of_pos hpos
  have hlastle : Ps.N - 1 ≤ Ps.N := Nat.sub_le _ _
  have h1 : (1 : ℝ) ∈ Icc (Ps.t (Ps.N - 1)) (Ps.t (Ps.N - 1 + 1)) := by
    rw [hlast, Ps.t_last]
    exact ⟨le_trans (Ps.mono_le hlastle le_rfl) (le_of_eq Ps.t_last), le_rfl⟩
  rw [colSign_eq_loopSignOf (I := I) (i := Ps.N - 1) (1 : ℝ)]
  exact loopSignOf_const_loop (I := I)
    (isChartLoop_colFamily hcell hbase htop (Nat.sub_lt hpos (by norm_num)) h1) hend

/-- **The grid argument**: for a continuous map `F` of the square whose vertical sides are constant
at `p` and whose value at `(1, τ)` is `p`, the chart-covered loop `τ ↦ F (0, τ)` has sign `1`. -/
theorem loopSignOf_eq_one_of_grid (hcell : GridCells (H := H) F Ps Pt y)
    (hF : ContinuousOn F (Icc 0 1 ×ˢ Icc 0 1))
    (hbase : ∀ σ : ℝ, F (σ, 0) = p) (htop : ∀ σ : ℝ, F (σ, 1) = p)
    (hend : ∀ τ : ℝ, F (1, τ) = p) :
    loopSignOf (I := I) Pt (fun τ => F (0, τ)) (colFamily y Pt.N 0) = 1 := by
  have hconst : ∀ i, i < Ps.N → colSign (I := I) F y Pt.N i Pt.t (Ps.t i)
      = colSign (I := I) F y Pt.N i Pt.t (Ps.t (i+1)) :=
    fun i hi => (colSign_const (I := I) hcell hF hbase htop hi (Ps.t (i+1))
      ⟨(Ps.mono i hi).le, le_rfl⟩).symm
  have hcross : ∀ i, i + 1 < Ps.N → colSign (I := I) F y Pt.N i Pt.t (Ps.t (i+1))
      = colSign (I := I) F y Pt.N (i+1) Pt.t (Ps.t (i+1)) :=
    fun i hi => colSign_eq_colSign_succ (I := I) hcell hF hbase htop hi
  have hmain : ∀ i, i < Ps.N → colSign (I := I) F y Pt.N i Pt.t (Ps.t (i+1)) = 1 := by
    have hP := Nat.decreasingInduction' (n := Ps.N) (m := 0)
      (P := fun k => ∀ j, k ≤ j → j < Ps.N →
        colSign (I := I) F y Pt.N j Pt.t (Ps.t (j+1)) = 1)
      (fun k hk _ hP j hkj hj => ?_) (Nat.zero_le _)
      (fun j hj hj' => absurd hj' (not_lt.mpr hj))
    exact fun i hi => hP i (Nat.zero_le i) hi
    rcases lt_or_eq_of_le hkj with hlt | heq
    · exact hP j (by omega) hj
    · subst heq
      by_cases hk1 : k + 1 < Ps.N
      · rw [hcross k hk1, hconst (k+1) hk1]
        exact hP (k+1) (by omega) hk1
      · have hkN : k + 1 = Ps.N := by omega
        have hk' : k = Ps.N - 1 := by omega
        rw [hkN, Ps.t_last, hk']
        exact colSign_one_eq_one (I := I) hcell hbase htop hend
  rw [← colSign_eq_loopSignOf (I := I) (i := 0) (0 : ℝ)]
  rw [show colSign (I := I) F y Pt.N 0 Pt.t 0
      = colSign (I := I) F y Pt.N 0 Pt.t (Ps.t 0) from
    congrArg (fun σ => colSign (I := I) F y Pt.N 0 Pt.t σ) Ps.t_zero.symm]
  rw [hconst 0 Ps.pos_N]
  exact hmain 0 Ps.pos_N

/-! ## §6 The subdivision lemma -/

variable {P Q : Partition 0 1} {z Z : ℕ → M} {γ : ℝ → M} {ψ : ℕ → ℕ}

theorem loopSignOf_refine
    (hP : IsChartLoop (H := H) P γ z) (hQ : IsChartLoop (H := H) Q γ Z)
    (hψ0 : ψ 0 = 0) (hψN : ψ Q.N = P.N) (hmono : Monotone ψ)
    (hstep : ∀ k < Q.N, ψ (k+1) ≤ ψ k + 1)
    (hlow : ∀ k ≤ Q.N, P.t (ψ k) ≤ Q.t k)
    (hhigh : ∀ k < Q.N, Q.t (k+1) ≤ P.t (min (ψ k + 1) P.N))
    (hZ : ∀ k ≤ Q.N, Z k = z (ψ k)) :
    loopSignOf (I := I) Q γ Z = loopSignOf (I := I) P γ z := by
  have hψle : ∀ k ≤ Q.N, ψ k ≤ P.N := fun k hk => (hmono hk).trans_eq hψN
  have hfac : ∀ k < Q.N,
      chartSign (I := I) (Z k) (Z (k+1)) (γ (Q.t (k+1)))
        = (if ψ (k+1) = ψ k + 1 then
            chartSign (I := I) (z (ψ k)) (z (ψ k + 1)) (γ (P.t (ψ k + 1))) else 1) := by
    intro k hk
    rw [hZ k hk.le, hZ (k+1) (by omega)]
    have hstep' : ψ (k+1) ≤ ψ k + 1 := hstep k hk
    have hmono' : ψ k ≤ ψ (k+1) := hmono (by omega)
    rcases lt_or_eq_of_le hmono' with hlt | heq
    · have hk1 : ψ (k+1) = ψ k + 1 := by omega
      rw [if_pos hk1, hk1]
      have hPk : ψ k + 1 ≤ P.N := by rw [← hk1]; exact hψle (k+1) (by omega)
      have hle1 : Q.t (k+1) ≤ P.t (ψ k + 1) := by
        have h := hhigh k hk
        rwa [min_eq_left hPk] at h
      have hge1 : P.t (ψ k + 1) ≤ Q.t (k+1) := by
        have h := hlow (k+1) (by omega)
        rwa [hk1] at h
      rw [le_antisymm hle1 hge1]
    · rw [if_neg (by omega), heq]
      exact chartSign_self (I := I) (by
        have h := hQ.2.1 k hk
        rwa [hZ (k+1) (by omega)] at h)
  have hprod : (∏ k ∈ Finset.range Q.N, chartSign (I := I) (Z k) (Z (k+1)) (γ (Q.t (k+1))))
      = ∏ k ∈ (Finset.range Q.N).filter (fun k => ψ (k+1) = ψ k + 1),
          chartSign (I := I) (z (ψ k)) (z (ψ k + 1)) (γ (P.t (ψ k + 1))) := by
    rw [Finset.prod_congr rfl (fun k hk => hfac k (Finset.mem_range.mp hk)), ← Finset.prod_filter]
  have hreind : (∏ k ∈ (Finset.range Q.N).filter (fun k => ψ (k+1) = ψ k + 1),
        chartSign (I := I) (z (ψ k)) (z (ψ k + 1)) (γ (P.t (ψ k + 1))))
      = ∏ i ∈ Finset.range P.N, chartSign (I := I) (z i) (z (i+1)) (γ (P.t (i+1))) := by
    refine Finset.prod_bij (fun k _ => ψ k) ?_ ?_ ?_ ?_
    · intro k hk
      have hk' : k < Q.N := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
      have hjump : ψ (k + 1) = ψ k + 1 := (Finset.mem_filter.mp hk).2
      have hle : ψ (k+1) ≤ P.N := hψle (k+1) (by omega)
      exact Finset.mem_range.mpr (by omega)
    · intro k₁ h₁ k₂ h₂ heq
      have h1 := Finset.mem_filter.mp h₁
      have h2 := Finset.mem_filter.mp h₂
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hm : ψ (k₁ + 1) ≤ ψ k₂ := hmono (Nat.succ_le_of_lt hlt)
        rw [h1.2, heq] at hm
        omega
      · have hm : ψ (k₂ + 1) ≤ ψ k₁ := hmono (Nat.succ_le_of_lt hlt)
        rw [h2.2, heq] at hm
        omega
    · intro i hi
      have hi' : i < P.N := Finset.mem_range.mp hi
      have hex : ∃ k, i + 1 ≤ ψ k := ⟨Q.N, by rw [hψN]; omega⟩
      have hspec : i + 1 ≤ ψ (Nat.find hex) := Nat.find_spec hex
      have hpos : 0 < Nat.find hex := by
        by_contra h
        have h0 : Nat.find hex = 0 := Nat.eq_zero_of_not_pos h
        rw [h0, hψ0] at hspec
        omega
      have hle : Nat.find hex ≤ Q.N :=
        Nat.find_min' hex (show i + 1 ≤ ψ Q.N by rw [hψN]; omega)
      have h2 := hstep (Nat.find hex - 1) (by omega)
      rw [Nat.sub_add_cancel hpos] at h2
      have hmin : ¬ (i + 1 ≤ ψ (Nat.find hex - 1)) :=
        Nat.find_min hex (by omega)
      have hprev : ψ (Nat.find hex - 1) = i := by omega
      refine ⟨Nat.find hex - 1, ?_, hprev⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      have hval : ψ (Nat.find hex) = i + 1 := by omega
      exact ⟨by omega, by rw [Nat.sub_add_cancel hpos, hval, hprev]⟩
    · intro k hk
      rfl
  rw [loopSignOf, hprod, hreind, loopSignOf]

/-! ## §7 A null-homotopic loop has sign `1` -/

theorem exists_chartLoop_of_simplyConnected [SimplyConnectedSpace M] {p : M} (γ : Path p p) :
    ∃ (P : Partition 0 1) (z : ℕ → M),
      IsChartLoop (H := H) P (fun τ : ℝ => γ (Set.projIcc 0 1 zero_le_one τ)) z ∧
      loopSignOf (I := I) P (fun τ : ℝ => γ (Set.projIcc 0 1 zero_le_one τ)) z = 1 := by
  classical
  have hv : Path.Homotopic γ (Path.refl p) :=
    Quotient.exact (@Subsingleton.elim (Path.Homotopic.Quotient p p) _ _ _)
  obtain ⟨Hh⟩ := hv
  set F : ℝ × ℝ → M :=
    fun q => Hh (Set.projIcc 0 1 zero_le_one q.1, Set.projIcc 0 1 zero_le_one q.2) with hFdef
  have hFcont : Continuous F :=
    Hh.continuous.comp ((continuous_projIcc.comp continuous_fst).prodMk
      (continuous_projIcc.comp continuous_snd))
  have hbase : ∀ σ : ℝ, F (σ, 0) = p := by
    intro σ
    show Hh (Set.projIcc 0 1 zero_le_one σ, Set.projIcc 0 1 zero_le_one 0) = p
    rw [Set.projIcc_left]
    exact (ContinuousMap.HomotopyRel.eq_fst Hh _ (by simp)).trans γ.source
  have htop : ∀ σ : ℝ, F (σ, 1) = p := by
    intro σ
    show Hh (Set.projIcc 0 1 zero_le_one σ, Set.projIcc 0 1 zero_le_one 1) = p
    rw [Set.projIcc_right]
    exact (ContinuousMap.HomotopyRel.eq_fst Hh _ (by simp)).trans γ.target
  have hproj1 : Set.projIcc 0 1 zero_le_one (1 : ℝ) = (1 : Set.Icc (0 : ℝ) 1) := by
    rw [Set.projIcc_right]
    exact Subtype.ext rfl
  have hend : ∀ τ : ℝ, F (1, τ) = p := by
    intro τ
    show Hh (Set.projIcc 0 1 zero_le_one 1, Set.projIcc 0 1 zero_le_one τ) = p
    rw [hproj1]
    exact (Hh.map_one_left (Set.projIcc 0 1 zero_le_one τ)).trans rfl
  obtain ⟨n, m, s, t, hs0, hsn, ht0, htm, hsmono, htmono, hcell⟩ :=
    Commons.Topology.exists_grid_forall_mapsTo_chartAt_of_le (E := E) (H := H) (I := I) (M := M)
      (a := 0) (b := 1) (c := 0) (d := 1) zero_le_one zero_le_one hFcont.continuousOn
  let y : ℕ → ℕ → M := fun i j =>
    if h : i < n ∧ j < m then Classical.choose (hcell i h.1 j h.2) else p
  have hy : ∀ i < n, ∀ j < m, ∀ q ∈ Icc (s i) (s (i+1)) ×ˢ Icc (t j) (t (j+1)),
      F q ∈ (chartAt H (y i j)).source := by
    intro i hi j hj q hq
    have hyy : y i j = Classical.choose (hcell i hi j hj) := by
      show (if h : i < n ∧ j < m then _ else _) = _
      rw [dif_pos ⟨hi, hj⟩]
    rw [hyy]
    exact Classical.choose_spec (hcell i hi j hj) q hq
  have hcurve : (fun τ : ℝ => F (0, τ)) = fun τ : ℝ => γ (Set.projIcc 0 1 zero_le_one τ) := by
    funext τ
    show Hh (Set.projIcc 0 1 zero_le_one 0, Set.projIcc 0 1 zero_le_one τ) =
      γ (Set.projIcc 0 1 zero_le_one τ)
    rw [Set.projIcc_left]
    exact Hh.map_zero_left _
  have hpos : 0 < n := (⟨n, s, hs0, hsn, hsmono⟩ : Partition 0 1).pos_N
  have hcell' : GridCells (H := H) F ⟨n, s, hs0, hsn, hsmono⟩ ⟨m, t, ht0, htm, htmono⟩ y :=
    fun i hi j hj q hq => hy i hi j hj q hq
  have hloop := isChartLoop_colFamily hcell' hbase htop (i := 0) hpos
    (show (0 : ℝ) ∈ Icc (s 0) (s (0+1)) from by
      rw [hs0]; exact ⟨le_rfl, by rw [← hs0]; exact (hsmono 0 hpos).le⟩)
  have hgrid := loopSignOf_eq_one_of_grid (I := I) hcell' hFcont.continuousOn hbase htop hend
  refine ⟨⟨m, t, ht0, htm, htmono⟩, colFamily y m 0, ?_, ?_⟩
  · rw [← hcurve]; exact hloop
  · rw [← hcurve]; exact hgrid

end
end Submission.OrientSign
