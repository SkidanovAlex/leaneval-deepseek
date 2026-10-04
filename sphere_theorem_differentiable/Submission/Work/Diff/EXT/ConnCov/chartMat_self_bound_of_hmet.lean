import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.EXT.christoffel_bounds_of_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

/-!
A uniform bound for the chart matrix of `G t` on `[T/2,T) × K'` from a two-sided equivalence of
the quadratic forms of `G t` and `G 0` (no smoothness of `t ↦ G t` is used).

Route.  The diagonal entries of the chart matrix in the coordinate frame are bounded directly by
`hmet` (applied to the frame vector `frameVector I x₀ p (bB i)`) together with the boundedness of
the corresponding `G 0` entries on the compact `K'` (continuity of the chart data, e.g.
`Work.Diff.EXT.CBound.GramM_contDiffAt_of_target`).  The off-diagonal entries are then reduced to
the diagonal ones with the parallelogram identity
`2 g_{ij} = g(σ_i+σ_j, σ_i+σ_j) − g(σ_i,σ_i) − g(σ_j,σ_j)`, using the bilinearity of `SMet.inner`
and `Submission.Geodesic.frameVector_add`.

Proof (as implemented).  `(G t).inner x · ·` is a *continuous linear* map in both slots, so it is
additive; positivity of the quadratic form (`g.pos`, junk `0` at `0`) gives `0 ≤ g.inner x u u`.
Two algebraic identities follow:

* `2 * g u w = g (u+w) (u+w) - g u u - g w w` (parallelogram),
* `g (u-w) (u-w) = g u u - 2 * g u w + g w w`.

Hence, from *entrywise* bounds `|g₀ u u| ≤ B`, `|g₀ w w| ≤ B`, `|g₀ u w| ≤ B` for the initial
metric `g₀ = G 0`, one gets `g₀ (u+w) (u+w) ≤ 4B` and `g₀ (u-w) (u-w) ≤ 4B`.  The `G 0`-bounds on
`K'` come from compactness: the entries `y ↦ (G 0).inner (pt x₀ y) (σ i) (σ j)` are continuous on
`K'` (`Work.Diff.EXT.CBound.GramM_contDiffAt_of_target` + `IsCompact.bddAbove_image` applied to
the sum of the absolute values), and a single constant `B ≥ 0` bounds all of them.

The two-sided hypothesis `hmet` then converts `g₀`-bounds into `G t`-bounds: the factor
`Real.exp (2 * (finrank ℝ E * C) * t)` is increasing in `t` on `Ico (T/2) T`, so it is dominated by
`Real.exp (2 * (finrank ℝ E * C) * T)` (here `t ≥ T/2 > 0` and `C ≥ 0`).  Applying this to
`u ± w` gives `± 2 g_t u w ≤ 4 Ef B` with `Ef = Real.exp (2 * (finrank ℝ E * C) * T)`;
`abs_le'` turns this into `|2 g_t u w| ≤ 4 Ef B`, hence `|g_t u w| ≤ 2 Ef B ≤ 4 Ef B = C'`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace ChartMatSelfBoundAux

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The quadratic form of a smooth Riemannian metric is nonnegative. -/
theorem cmsb_inner_self_nonneg (g : Submission.Diff.SMet I M) (x : M) (u : TangentSpace I x) :
    0 ≤ g.inner x u u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · exact le_of_lt (g.pos x u hu)

/-- The **parallelogram identity** for the inner product of a smooth Riemannian metric (the first
slot of `g.inner x` is additive, the second slot is additive as well). -/
theorem cmsb_two_mul_inner (g : Submission.Diff.SMet I M) (x : M) (u w : TangentSpace I x) :
    2 * g.inner x u w = g.inner x (u + w) (u + w) - g.inner x u u - g.inner x w w := by
  simp only [map_add, add_apply]
  rw [g.symm x u w]
  ring

/-- The **subtracted** form of the parallelogram identity. -/
theorem cmsb_inner_sub_sub (g : Submission.Diff.SMet I M) (x : M) (u w : TangentSpace I x) :
    g.inner x (u - w) (u - w) = g.inner x u u - 2 * g.inner x u w + g.inner x w w := by
  simp only [map_sub, sub_apply]
  rw [g.symm x w u]
  ring

/-- From entrywise bounds for `u, w` (diagonal and mixed) one gets a bound for the quadratic form
at `u + w`. -/
theorem cmsb_inner_add_add_le (g : Submission.Diff.SMet I M) (x : M) (u w : TangentSpace I x)
    {B : ℝ} (hu : |g.inner x u u| ≤ B) (hw : |g.inner x w w| ≤ B)
    (huw : |g.inner x u w| ≤ B) :
    g.inner x (u + w) (u + w) ≤ 4 * B := by
  have h := cmsb_two_mul_inner g x u w
  have h1 : g.inner x u u ≤ B := le_trans (le_abs_self _) hu
  have h2 : g.inner x w w ≤ B := le_trans (le_abs_self _) hw
  have h3 : g.inner x u w ≤ B := le_trans (le_abs_self _) huw
  linarith

/-- From entrywise bounds for `u, w` (diagonal and mixed) one gets a bound for the quadratic form
at `u - w`. -/
theorem cmsb_inner_sub_sub_le (g : Submission.Diff.SMet I M) (x : M) (u w : TangentSpace I x)
    {B : ℝ} (hu : |g.inner x u u| ≤ B) (hw : |g.inner x w w| ≤ B)
    (huw : |g.inner x u w| ≤ B) :
    g.inner x (u - w) (u - w) ≤ 4 * B := by
  have h := cmsb_inner_sub_sub g x u w
  have h1 : g.inner x u u ≤ B := le_trans (le_abs_self _) hu
  have h2 : g.inner x w w ≤ B := le_trans (le_abs_self _) hw
  have h3 : -(g.inner x u w) ≤ B := le_trans (neg_le_abs _) huw
  linarith

/-- **The entries of the initial chart matrix are bounded on a compact set.**  For `K'` compact in
the chart target of `x₀` there is `B ≥ 0` with
`|(G 0).inner (pt x₀ y) (σ i) (σ j)| ≤ B` for all `y ∈ K'` and all `i, j` in the coordinate frame
`σ i = frameVector I x₀ (pt x₀ y) (bB i)`. -/
theorem cmsb_G0_entry_bound [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (K' : Set E)
    (hK'c : IsCompact K') (hK't : K' ⊆ (extChartAt I x₀).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y ∈ K', ∀ (i j : Fin (Module.finrank ℝ E)),
      |(G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y))| ≤ B := by
  have hcont : ContinuousOn (fun y' : E =>
      ∑ i, ∑ j, ‖Work.Diff.GE.GramM G x₀ 0 (Work.Diff.EXT.pt (I := I) x₀ y') i j‖) K' := by
    refine continuousOn_finsetSum Finset.univ (fun i _ => ?_)
    refine continuousOn_finsetSum Finset.univ (fun j _ => ?_)
    intro y hy
    exact ((Work.Diff.EXT.CBound.GramM_contDiffAt_of_target (I := I) (M := M) G x₀ 0
      (hK't hy) i j).continuousAt.norm).continuousWithinAt
  obtain ⟨C0, hC0⟩ := hK'c.bddAbove_image hcont
  have hC0' : ∀ y ∈ K', (∑ i, ∑ j, ‖Work.Diff.GE.GramM G x₀ 0
        (Work.Diff.EXT.pt (I := I) x₀ y) i j‖) ≤ C0 := by
    intro y hy
    exact hC0 ⟨y, hy, rfl⟩
  refine ⟨max C0 0, le_max_right _ _, ?_⟩
  intro y hy i j
  have h1 : ‖Work.Diff.GE.GramM G x₀ 0 (Work.Diff.EXT.pt (I := I) x₀ y) i j‖
      ≤ ∑ j', ‖Work.Diff.GE.GramM G x₀ 0 (Work.Diff.EXT.pt (I := I) x₀ y) i j'‖ :=
    Finset.single_le_sum (fun j' _ => norm_nonneg _) (Finset.mem_univ j)
  have h2 : (∑ j', ‖Work.Diff.GE.GramM G x₀ 0 (Work.Diff.EXT.pt (I := I) x₀ y) i j'‖)
      ≤ ∑ i', ∑ j', ‖Work.Diff.GE.GramM G x₀ 0 (Work.Diff.EXT.pt (I := I) x₀ y) i' j'‖ :=
    Finset.single_le_sum (fun i' _ => Finset.sum_nonneg (fun j' _ => norm_nonneg _))
      (Finset.mem_univ i)
  have h3 : ‖Work.Diff.GE.GramM G x₀ 0 (Work.Diff.EXT.pt (I := I) x₀ y) i j‖ ≤ max C0 0 :=
    le_trans (le_trans h1 h2) (le_trans (hC0' y hy) (le_max_left _ _))
  rwa [Real.norm_eq_abs] at h3

/-- **Pointwise bound.**  Given the `G 0`-entry bound `hB` at the chart point `y` and
`t ∈ Ico (T/2) T`, every entry of the chart matrix of `G t` at `y` is bounded by
`4 * Real.exp (2 * (finrank ℝ E * C) * T) * B`. -/
theorem cmsb_pointwise (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (x₀ : M) {B : ℝ} (hB0 : 0 ≤ B) {y : E}
    (hB : ∀ (i j : Fin (Module.finrank ℝ E)),
      |(G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y)
        (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
        (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y))| ≤ B)
    {t : ℝ} (ht : t ∈ Set.Ico (T / 2) T) :
    ∀ (i j : Fin (Module.finrank ℝ E)),
      |Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y i j|
        ≤ 4 * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * B) := by
  have hT2 : 0 < T / 2 := by linarith
  have ht0 : 0 ≤ t := le_trans hT2.le ht.1
  have hth : t ∈ Set.Ico 0 T := ⟨ht0, ht.2⟩
  -- the exponential factor is monotone in the time variable
  have hmono : ∀ (x : M) (u : TangentSpace I x),
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * (G 0).inner x u u := by
    intro x u
    have h1 := (hmet t hth x u).1
    have hnn : 0 ≤ (G 0).inner x u u := cmsb_inner_self_nonneg (G 0) x u
    have h2 : 0 ≤ 2 * ((Module.finrank ℝ E : ℝ) * C) := by
      have hf : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
      have : 0 ≤ (Module.finrank ℝ E : ℝ) * C := mul_nonneg hf hC
      linarith
    have hexp : Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t)
        ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) := by
      rw [Real.exp_le_exp]
      exact mul_le_mul_of_nonneg_left ht.2.le h2
    exact le_trans h1 (mul_le_mul_of_nonneg_right hexp hnn)
  have key : ∀ (u w : TangentSpace I (Work.Diff.EXT.pt (I := I) x₀ y)),
      |(G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y) u u| ≤ B →
      |(G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y) w w| ≤ B →
      |(G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y) u w| ≤ B →
      |(G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) u w|
        ≤ 4 * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * B) := by
    intro u w hu hw huw
    have hplus : (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) (u + w) (u + w)
        ≤ 4 * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * B) :=
      calc (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) (u + w) (u + w)
          ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T)
              * (G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y) (u + w) (u + w) :=
            hmono _ _
        _ ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * (4 * B) :=
            mul_le_mul_of_nonneg_left (cmsb_inner_add_add_le (G 0) _ u w hu hw huw)
              (Real.exp_pos _).le
        _ = 4 * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * B) := by ring
    have hminus : (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) (u - w) (u - w)
        ≤ 4 * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * B) :=
      calc (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) (u - w) (u - w)
          ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T)
              * (G 0).inner (Work.Diff.EXT.pt (I := I) x₀ y) (u - w) (u - w) :=
            hmono _ _
        _ ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * (4 * B) :=
            mul_le_mul_of_nonneg_left (cmsb_inner_sub_sub_le (G 0) _ u w hu hw huw)
              (Real.exp_pos _).le
        _ = 4 * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * B) := by ring
    have hDi : 0 ≤ (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) u u :=
      cmsb_inner_self_nonneg (G t) _ u
    have hDj : 0 ≤ (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) w w :=
      cmsb_inner_self_nonneg (G t) _ w
    have hfwd : 2 * (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) u w
        ≤ 4 * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * B) := by
      have h := cmsb_two_mul_inner (G t) (Work.Diff.EXT.pt (I := I) x₀ y) u w
      linarith
    have hbwd : -(2 * (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) u w)
        ≤ 4 * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * B) := by
      have h := cmsb_inner_sub_sub (G t) (Work.Diff.EXT.pt (I := I) x₀ y) u w
      linarith
    have habs2 : |2 * (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) u w|
        ≤ 4 * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * B) :=
      abs_le'.mpr ⟨hfwd, hbwd⟩
    have hEB : 0 ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * B :=
      mul_nonneg (Real.exp_pos _).le hB0
    have h2 : |(2 : ℝ) * ((G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) u w)|
        = 2 * |(G t).inner (Work.Diff.EXT.pt (I := I) x₀ y) u w| := by
      rw [abs_mul]; norm_num
    rw [h2] at habs2
    linarith
  intro i j
  have hcm : Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y i j
      = (G t).inner (Work.Diff.EXT.pt (I := I) x₀ y)
          (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y))
          (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y)) := rfl
  rw [hcm]
  exact key _ _ (hB i i) (hB j j) (hB i j)

end ChartMatSelfBoundAux

theorem chartMat_self_bound_of_hmet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (x₀ : M) (K' : Set E) (hK'c : IsCompact K') (hK't : K' ⊆ (extChartAt I x₀).target) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (i j : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
      |Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y i j| ≤ C' := by
  obtain ⟨B, hB0, hB⟩ := ChartMatSelfBoundAux.cmsb_G0_entry_bound (I := I) (M := M) G x₀ K' hK'c hK't
  refine ⟨4 * (Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * T) * B), ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le hB0)
  · intro t ht i j y hy
    exact ChartMatSelfBoundAux.cmsb_pointwise (I := I) (M := M) G T C hT hC hmet x₀ hB0
      (fun i j => hB y hy i j) ht i j

end Work.Diff.EXT.ConnCov
