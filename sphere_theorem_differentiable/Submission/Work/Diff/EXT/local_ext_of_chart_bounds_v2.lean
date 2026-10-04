import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.chartMat_jets_bounded
import Submission.Work.Diff.EXT.det_ge_pow_of_quadForm_ge
import Submission.ChartBounds
import Submission.Work.Diff.EXT.isVonNBounded_quadForm_lt2
import Submission.Work.Diff.EXT.ext_of_bounded_jets_v2
import Submission.Work.Diff.EXT.glue_seam_T_self
import Submission.Work.Diff.EXT.jets_clean
import Submission.Work.Diff.EXT.posDef_tube_of_continuous_seam

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-!
# Local smooth extension of a Ricci flow across a time where the chart matrices are bounded

Target: `Work.Diff.EXT.local_ext_of_chart_bounds_v2`.

Given a Ricci flow `G` on `[0,T)`, a priori chart bounds `ChartBounds G (T/2) T` for the chart
matrices of the metrics `G t` and a uniform lower bound `a • (G 0).inner ≤ (G t).inner` for
`t ∈ [T/2,T)`, the family extends to a jointly smooth family `H₁` of metrics on a whole
neighbourhood `(T-δ, T+δ)` of `T`, agreeing with `G` on `[T-δ, T)`.

## The proof

* **The local chart pieces** (`chart_piece_at_T`, below).  Fix a chart centre `x₀`.  The chart
  matrix `u = (t,y) ↦ chartMat G x₀ t y` has bounds on *all* its ambient jets on the slab
  `[T/2,T) × U` (`ambient_jets_bounded`: the Ricci flow equation in the chart, the chart Ricci
  matrix being a smooth function of the spatial `2`-jet, cut off in the determinant, together with
  the parabolic bootstrap `Jets2.jets_bounded_of_pde`), so `ext_of_bounded_jets` produces a smooth
  two-sided extension `V₁` of the chart matrix past `T`.  The metric is uniformly positive definite
  on the slab (the lower bound `hnd` together with the uniform positive definiteness of the chart
  matrix of `G 0` near the chart centre); symmetrising (`symmFam`) and propagating this ellipticity
  across the seam by continuity (`posDef_tube_of_continuous_seam`) gives a two-sided smooth *matrix
  family* `W` which agrees with the chart matrix on the left of `T`, is symmetric everywhere and
  positive definite on the whole two-sided slab.

* **The gluing** (`glue_seam_T_self`, a self-contained adaptation of `glue_local_metric_families`):
  a finite family of chart balls covering the compact manifold, a subordinate smooth partition of
  unity and the local matrix families produce the jointly smooth two-sided family of metrics.
-/

namespace Work.Diff.EXT

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## Symmetrisation of a matrix family -/

/-- The symmetrisation `(A + Aᵀ)/2` of a family of matrices. -/
noncomputable def symmFam (V : ℝ × E → MatE (E := E)) : ℝ × E → MatE (E := E) :=
  fun p i j => (V p i j + V p j i) / 2

lemma contDiffOn_symmFam {V : ℝ × E → MatE (E := E)} {s : Set (ℝ × E)}
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V s) :
    ContDiffOn ℝ (⊤ : ℕ∞) (symmFam V) s := by
  refine contDiffOn_pi.mpr (fun i => contDiffOn_pi.mpr (fun j => ?_))
  exact (((contDiffOn_pi.mp (contDiffOn_pi.mp hV i)) j).add
    ((contDiffOn_pi.mp (contDiffOn_pi.mp hV j)) i)).div_const 2

/-- The quadratic form of the symmetrisation is the quadratic form of the original matrix. -/
lemma symmFam_quadForm (V : ℝ × E → MatE (E := E)) (p : ℝ × E)
    (v : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ i, ∑ j, v i * v j * symmFam V p i j)
      = ∑ i, ∑ j, v i * v j * V p i j := by
  have hswap : (∑ i, ∑ j, v i * v j * V p j i)
      = ∑ i, ∑ j, v i * v j * V p i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  calc (∑ i, ∑ j, v i * v j * symmFam V p i j)
      = ∑ i, ∑ j, ((v i * v j * V p i j) / 2 + (v i * v j * V p j i) / 2) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        simp only [symmFam]
        ring
    _ = (∑ i, ∑ j, v i * v j * V p i j) / 2
          + (∑ i, ∑ j, v i * v j * V p j i) / 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_div]
    _ = ∑ i, ∑ j, v i * v j * V p i j := by rw [hswap]; ring

/-! ## Clean local versions of the a priori chart lemmas -/

/-- **The chart matrix of a smooth metric is positive definite on the whole chart target.** -/
theorem chartMatFun_posDef_target
    [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) {v : Fin (Module.finrank ℝ E) → ℝ} (hv : v ≠ 0) :
    0 < ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun g x₀ y i j := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hWne : (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
      ((extChartAt I x₀).symm y) (Work.Diff.EXT.bB (E := E) i)) ≠ 0 := by
    intro hzero
    have h1 : Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
        (∑ i, v i • Work.Diff.EXT.bB (E := E) i) = 0 := by
      rw [Submission.Geodesic.frameVector_sum Finset.univ x₀ ((extChartAt I x₀).symm y) v
        (Work.Diff.EXT.bB (E := E))]
      exact hzero
    have h2 : (∑ i, v i • Work.Diff.EXT.bB (E := E) i) = 0 :=
      (Submission.ChartBounds.frameVector_eq_zero_iff (I := I) hp _).mp h1
    have h3 : ∀ i, v i = 0 :=
      (Fintype.linearIndependent_iffₛ.mp (Work.Diff.EXT.bB (E := E)).linearIndependent) v 0
        (by simpa using h2)
    exact hv (funext h3)
  rw [Work.Diff.EXT.chartMatFun_quadForm g x₀ y v]
  exact g.pos ((extChartAt I x₀).symm y) _ hWne

/-- **The chart matrix of a fixed smooth metric is continuous at the chart centre.** -/
theorem continuousAt_chartMatFun_centre'
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContinuousAt (fun y : E => Work.Diff.EXT.chartMatFun g x₀ y i j) ((extChartAt I x₀) x₀) := by
  have hJ : Submission.Diff.JointSmooth (fun _ : ℝ => g) Set.univ :=
    Work.Diff.EXT.jointSmooth_const g
  have hy₀ : (extChartAt I x₀) x₀ ∈ (extChartAt I x₀).target :=
    PartialEquiv.map_source _ (mem_extChartAt_source x₀)
  have hcd := Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth_gen (I := I) (M := M)
    (J := Set.univ) hJ (Set.mem_univ (0 : ℝ)) x₀ hy₀
  have hopen : IsOpen ((Set.univ : Set ℝ) ×ˢ (extChartAt I x₀).target) :=
    isOpen_univ.prod (isOpen_extChartAt_target (I := I) x₀)
  have hcont1 : ContinuousAt (fun p : ℝ × E =>
      Work.Diff.EXT.chartMat (fun _ : ℝ => g) x₀ p.1 p.2)
      ((0 : ℝ), (extChartAt I x₀) x₀) :=
    hcd.continuousWithinAt.continuousAt (hopen.mem_nhds ⟨Set.mem_univ _, hy₀⟩)
  have hcont2 : ContinuousAt (fun y : E => Work.Diff.EXT.chartMat (fun _ : ℝ => g) x₀ 0 y)
      ((extChartAt I x₀) x₀) :=
    hcont1.comp (continuous_const.prodMk continuous_id).continuousAt
  have hcont3 : ContinuousAt (fun y : E =>
      (Work.Diff.EXT.chartMat (fun _ : ℝ => g) x₀ 0 y) i j) ((extChartAt I x₀) x₀) :=
    ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hcont2))
  simpa only [Work.Diff.EXT.chartMat, Work.Diff.EXT.chartMatFun] using hcont3


theorem uniform_posDef_of_continuous'
    {n : ℕ} {X : Type*} [TopologicalSpace X] (M' : X → Fin n → Fin n → ℝ) {y₀ : X}
    (hcont : ∀ i j, ContinuousAt (fun y => M' y i j) y₀)
    (hpos : ∀ v : Fin n → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * v j * M' y₀ i j) :
    ∃ δ > 0, ∃ U : Set X, IsOpen U ∧ y₀ ∈ U ∧
      ∀ y ∈ U, ∀ v : Fin n → ℝ, δ * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * M' y i j := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, Set.univ, isOpen_univ, Set.mem_univ _, fun y _ v => ?_⟩
    have hv0 : v = 0 := Subsingleton.elim v 0
    rw [hv0]
    simp
  · obtain ⟨c, hcpos, hc⟩ := exists_pos_le_quadForm n (M' y₀) hpos
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hc2 : 0 < c / (2 * (n : ℝ) ^ 2) := by positivity
    have hUne : ∀ᶠ y in 𝓝 y₀, ∀ i j : Fin n, |M' y i j - M' y₀ i j| < c / (2 * (n : ℝ) ^ 2) := by
      rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro j
      have ht : Filter.Tendsto (fun y : X => |M' y i j - M' y₀ i j|) (𝓝 y₀) (𝓝 0) := by
        have h2 : ContinuousAt (fun y : X => M' y i j - M' y₀ i j) y₀ :=
          (hcont i j).sub continuousAt_const
        have h1 : Filter.Tendsto (fun y : X => M' y i j - M' y₀ i j) (𝓝 y₀) (𝓝 (0 : ℝ)) := by
          simpa using h2.tendsto
        simpa using h1.abs
      exact ht.eventually (isOpen_Iio.mem_nhds hc2)
    obtain ⟨U, hUsub, hUopen, hy₀U⟩ := mem_nhds_iff.mp hUne
    refine ⟨c / (2 * (n : ℝ)), by positivity, U, hUopen, hy₀U, fun y hy v => ?_⟩
    have hΔ : ∀ i j, |M' y i j - M' y₀ i j| < c / (2 * (n : ℝ) ^ 2) := hUsub hy
    have hsq : (∑ i, (v i) ^ 2) ≤ (n : ℝ) * ‖v‖ ^ 2 := by
      calc (∑ i, (v i) ^ 2) ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            have h1 : |v i| ≤ ‖v‖ := by simpa using norm_le_pi_norm v i
            rw [← sq_abs (v i)]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = (n : ℝ) * ‖v‖ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcross : (∑ i, ∑ j, |v i| * |v j|) ≤ (n : ℝ) * ∑ i, (v i) ^ 2 := by
      have h1 : ∀ i j, |v i| * |v j| ≤ ((v i) ^ 2 + (v j) ^ 2) / 2 := by
        intro i j
        have h2 : 0 ≤ (|v i| - |v j|) ^ 2 := sq_nonneg _
        rw [sub_sq, sq_abs, sq_abs] at h2
        linarith
      have hsum : (∑ i, ∑ j, ((v i) ^ 2 + (v j) ^ 2) / 2) = (n : ℝ) * ∑ i, (v i) ^ 2 := by
        conv_lhs => enter [2, i]; rw [← Finset.sum_div]
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← Finset.mul_sum]
        ring
      calc (∑ i, ∑ j, |v i| * |v j|) ≤ ∑ i, ∑ j, ((v i) ^ 2 + (v j) ^ 2) / 2 :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h1 i j))
        _ = (n : ℝ) * ∑ i, (v i) ^ 2 := hsum
    have hsplit : (∑ i, ∑ j, v i * v j * M' y i j)
        = (∑ i, ∑ j, v i * v j * M' y₀ i j)
          + ∑ i, ∑ j, v i * v j * (M' y i j - M' y₀ i j) := by
      have h : ∀ i j, v i * v j * M' y i j
          = v i * v j * M' y₀ i j + v i * v j * (M' y i j - M' y₀ i j) := fun i j => by ring
      simp only [h, Finset.sum_add_distrib]
    have hΔQ : |∑ i, ∑ j, v i * v j * (M' y i j - M' y₀ i j)|
        ≤ (c / (2 * (n : ℝ))) * ∑ i, (v i) ^ 2 := by
      calc |∑ i, ∑ j, v i * v j * (M' y i j - M' y₀ i j)|
          ≤ ∑ i, ∑ j, |v i| * |v j| * (c / (2 * (n : ℝ) ^ 2)) := by
            calc |∑ i, ∑ j, v i * v j * (M' y i j - M' y₀ i j)|
                ≤ ∑ i, |∑ j, v i * v j * (M' y i j - M' y₀ i j)| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i, ∑ j, |v i * v j * (M' y i j - M' y₀ i j)| :=
                  Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
              _ ≤ ∑ i, ∑ j, |v i| * |v j| * (c / (2 * (n : ℝ) ^ 2)) := by
                  refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
                  rw [abs_mul, abs_mul]
                  exact mul_le_mul_of_nonneg_left (le_of_lt (hΔ i j)) (by positivity)
        _ = (c / (2 * (n : ℝ) ^ 2)) * (∑ i, ∑ j, |v i| * |v j|) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun j _ => by ring)
        _ ≤ (c / (2 * (n : ℝ) ^ 2)) * ((n : ℝ) * ∑ i, (v i) ^ 2) :=
            mul_le_mul_of_nonneg_left hcross (by positivity)
        _ = (c / (2 * (n : ℝ))) * ∑ i, (v i) ^ 2 := by
            field_simp
    have hQ0 : (c / (n : ℝ)) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * M' y₀ i j := by
      have h1 : c * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, v i * v j * M' y₀ i j := hc v
      have h2 : (c / (n : ℝ)) * (∑ i, (v i) ^ 2) ≤ c * ‖v‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hnpos]
        nlinarith [hsq, hcpos, norm_nonneg v]
      linarith
    have hcoef : c / (n : ℝ) = c / (2 * (n : ℝ)) + c / (2 * (n : ℝ)) := by
      field_simp
      ring
    have hQ0' : (c / (2 * (n : ℝ))) * ∑ i, (v i) ^ 2 + (c / (2 * (n : ℝ))) * ∑ i, (v i) ^ 2
        ≤ ∑ i, ∑ j, v i * v j * M' y₀ i j := by
      rw [← add_mul, ← hcoef]
      exact hQ0
    have h2 : -(∑ i, ∑ j, v i * v j * (M' y i j - M' y₀ i j))
        ≤ (c / (2 * (n : ℝ))) * ∑ i, (v i) ^ 2 := by
      linarith [neg_le_abs (∑ i, ∑ j, v i * v j * (M' y i j - M' y₀ i j)), hΔQ]
    linarith [hsplit, hQ0', h2]


/-- **Uniform positive definiteness of the chart matrix of a fixed smooth metric, near the chart
centre.** -/
theorem chartMatFun_posDef_nhds'
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set E, IsOpen U ∧ (extChartAt I x₀) x₀ ∈ U ∧
      ∀ y ∈ U, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        δ * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun g x₀ y i j :=
  Work.Diff.EXT.uniform_posDef_of_continuous' (X := E) (n := Module.finrank ℝ E)
    (fun y : E => Work.Diff.EXT.chartMatFun g x₀ y) (y₀ := (extChartAt I x₀) x₀)
    (fun i j => Work.Diff.EXT.continuousAt_chartMatFun_centre' g x₀ i j)
    (fun v hv => Work.Diff.EXT.chartMatFun_posDef_target g x₀
      (PartialEquiv.map_source _ (mem_extChartAt_source x₀)) hv)

/-! ## The a priori estimates in a chart: bounds on all jets of the chart matrix -/

/-- **Bounds on the spatial jets of the chart matrix, and uniform ellipticity** (from the a priori
chart bounds `hb` and the metric lower bound `hnd`), **together with bounds on all ambient jets**.
The latter are obtained from the parabolic bootstrap `Jets2.jets_bounded_of_pde`: the chart matrix
solves the quasilinear system `∂ₜ u = Φ (·, J u)`, where `Φ` is the chart Ricci matrix read off the
spatial `2`-jet (`chartRic_partial_jet`), cut off with a smooth function of the determinant which is
`≡ 1` wherever the matrix is positive definite with constant `ε > 0` (`det_ge_pow_of_quadForm_ge`),
i.e. on the whole slab. -/
theorem ambient_jets_bounded
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hb : Work.Diff.EXT.ChartBounds G (T / 2) T)
    (hnd : ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
        a * (G 0).inner x u u ≤ (G t).inner x u u)
    (x₀ : M) :
    ∃ U : Set E, IsOpen U ∧ (extChartAt I x₀) x₀ ∈ U ∧ Bornology.IsBounded U ∧
      U ⊆ (extChartAt I x₀).target ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
        ((Set.Ico (T / 2) T) ×ˢ U) ∧
      (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ (Set.Ioo (T / 2) T) ×ˢ U,
        ‖iteratedFDeriv ℝ k (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2) p‖ ≤ C) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
        ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMat G x₀ t y i j) := by
  classical
  -- ## The a priori chart data
  obtain ⟨Ucb, hUcbo, hUcbm, hUcbb⟩ := hb x₀
  obtain ⟨a, ha_pos, ha_le⟩ := hnd
  obtain ⟨δe, hδe_pos, Ve, hVeo, hy₀Ve, hVell⟩ :=
    Work.Diff.EXT.chartMatFun_posDef_nhds' (I := I) (M := M) (G 0) x₀
  set y₀ : E := (extChartAt I x₀) x₀ with hy₀
  set U : Set E := Ucb ∩ Ve ∩ Metric.ball y₀ 1 ∩ (extChartAt I x₀).target with hU
  have hUo : IsOpen U :=
    ((hUcbo.inter hVeo).inter Metric.isOpen_ball).inter (isOpen_extChartAt_target (I := I) x₀)
  have hy₀U : (extChartAt I x₀) x₀ ∈ U :=
    ⟨⟨⟨hUcbm, hy₀Ve⟩, Metric.mem_ball_self zero_lt_one⟩,
      PartialEquiv.map_source _ (mem_extChartAt_source x₀)⟩
  have hUtgt : U ⊆ (extChartAt I x₀).target := fun y hy => hy.2
  have hUb : Bornology.IsBounded U :=
    (Metric.isBounded_ball (x := y₀) (r := 1)).subset (fun y hy => hy.1.2)
  have hspat' : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
      ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.EXT.chartMat G x₀ t y') y‖ ≤ C := by
    intro k
    obtain ⟨C, hC0, hC⟩ := hUcbb k
    exact ⟨C, hC0, fun t ht y hy => hC t ht y hy.1.1.1⟩
  have hell' : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
      ∀ v : Fin (Module.finrank ℝ E) → ℝ,
      ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMat G x₀ t y i j := by
    refine ⟨a * δe, mul_pos ha_pos hδe_pos, fun t ht y hy v => ?_⟩
    have hyVe : y ∈ Ve := hy.1.1.2
    have hδe : δe * ∑ i, (v i) ^ 2
        ≤ ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun (G 0) x₀ y i j := hVell y hyVe v
    calc a * δe * ∑ i, (v i) ^ 2
        = a * (δe * ∑ i, (v i) ^ 2) := by ring
      _ ≤ a * (∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun (G 0) x₀ y i j) :=
          mul_le_mul_of_nonneg_left hδe (le_of_lt ha_pos)
      _ = a * (G 0).inner ((extChartAt I x₀).symm y)
            (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (Work.Diff.EXT.bB (E := E) i))
            (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (Work.Diff.EXT.bB (E := E) i)) := by
          rw [Work.Diff.EXT.chartMatFun_quadForm (G 0) x₀ y v]
      _ ≤ (G t).inner ((extChartAt I x₀).symm y)
            (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (Work.Diff.EXT.bB (E := E) i))
            (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (Work.Diff.EXT.bB (E := E) i)) :=
          ha_le t ht ((extChartAt I x₀).symm y) _
      _ = ∑ i, ∑ j, v i * v j * Work.Diff.EXT.chartMatFun (G t) x₀ y i j :=
          (Work.Diff.EXT.chartMatFun_quadForm (G t) x₀ y v).symm
  obtain ⟨ε, hεpos, hell⟩ := hell'
  -- ## The smooth Ricci matrix as a function of the scalar `2`-jet, cut off in the determinant
  obtain ⟨Ψ, hΨsm, hΨeq⟩ := Work.Diff.EXT.chartRic_partial_jet (I := I) (M := M)
  set δ : ℝ := ε ^ Module.finrank ℝ E with hδdef
  have hδ_pos : 0 < δ := pow_pos hεpos _
  set Φ : E × JetC (E := E) → Work.Diff.EXT.MatE (E := E) :=
    fun z => Work.Diff.EXT.jetCut δ ((Matrix.of z.2.1).det) • ((-2 : ℝ) • Ψ z) with hΦ
  have hdetA : ContDiff ℝ (⊤ : ℕ∞) (fun A : Work.Diff.EXT.MatE (E := E) =>
      (Matrix.of A).det) := by
    simp only [Matrix.det_apply, Matrix.of_apply]
    fun_prop
  have hdet_sm : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : E × JetC (E := E) => (Matrix.of z.2.1).det) :=
    hdetA.comp (by fun_prop)
  have hΦ_sm : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : E × JetC (E := E) => (-2 : ℝ) • Ψ z)
        {z | (Matrix.of z.2.1).det ≠ 0} := hΨsm.const_smul (-2)
    exact Work.Diff.EXT.contDiff_smul_of_det_cutoff (E := E) (c := δ / 2) (half_pos hδ_pos)
      (Work.Diff.EXT.contDiff_jetCut δ) (fun x hx => Work.Diff.EXT.jetCut_eq_zero hδ_pos hx)
      hdet_sm h1
  -- ## The determinant stays away from `0` on the slab
  have hdetbound : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
      δ ≤ (Matrix.of (Work.Diff.EXT.chartMat G x₀ t y)).det := by
    intro t ht y hy
    have h := Work.Diff.EXT.det_ge_pow_of_quadForm_ge
      (M := Matrix.of (Work.Diff.EXT.chartMat G x₀ t y))
      (fun i j => Work.Diff.EXT.chartMatFun_symm (G t) x₀ y i j)
      hεpos (fun v => by simpa using hell t ht y hy v)
    simpa only [hδdef] using h
  -- ## The chart matrix solves the (cut off) quasilinear system
  have hpde : ∀ p ∈ (Set.Ico (T / 2) T) ×ˢ U,
      deriv (fun s : ℝ => Work.Diff.EXT.chartMat G x₀ s p.2) p.1 =
        Φ (p.2, Work.Diff.EXT.sJetData
          (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2) p) := by
    rintro ⟨t, y⟩ hp
    have ht : t ∈ Set.Ioo 0 T := ⟨by linarith [hT, hp.1.1], hp.1.2⟩
    have hy : y ∈ (extChartAt I x₀).target := hUtgt hp.2
    have hder := (Work.Diff.EXT.hasDerivAt_chartMat_of_isRicciFlow (I := I) (M := M)
      hflow ht x₀ y).deriv
    have hcut1 : Work.Diff.EXT.jetCut δ ((Matrix.of ((Work.Diff.EXT.sJetData
        (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2) (t, y)).1)).det) = 1 := by
      show Work.Diff.EXT.jetCut δ ((Matrix.of (Work.Diff.EXT.chartMat G x₀ t y)).det) = 1
      exact Work.Diff.EXT.jetCut_eq_one hδ_pos (hdetbound t hp.1 y hp.2)
    rw [hder, hΦ]
    show (-2 : ℝ) • Work.Diff.EXT.chartRicMat (G t) x₀ y
        = Work.Diff.EXT.jetCut δ ((Matrix.of ((Work.Diff.EXT.sJetData
            (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2) (t, y)).1)).det)
          • ((-2 : ℝ) • Ψ (y, Work.Diff.EXT.sJetData
              (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2) (t, y)))
    rw [hcut1, one_smul, hΨeq x₀ (G t) y hy]
    simp only [Work.Diff.EXT.sJetData, Work.Diff.EXT.dPart, Work.Diff.EXT.chartMat]
  -- ## Smoothness on the slab
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      ((Set.Ico (T / 2) T) ×ˢ U) := by
    intro p hp
    have ht0 : p.1 ∈ Set.Ico 0 T := ⟨by linarith [hp.1.1, hT], hp.1.2⟩
    exact (Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth_gen (I := I) (M := M) hflow.1
      ht0 x₀ (hUtgt hp.2)).mono
      (Set.prod_mono (fun s hs => ⟨by linarith [hs.1, hT], hs.2⟩) (fun y hy => hUtgt hy))
  -- ## The parabolic bootstrap (bounds on the *open* slab)
  have hjets := JetsClean.interior_jets_bounded (E := E) (σ := T / 2) (T := T)
    (by linarith) hUo hUb hu hspat' hΦ_sm hpde
  exact ⟨U, hUo, hy₀U, hUb, hUtgt, hu, hjets, ⟨ε, hεpos, hell⟩⟩

/-! ## The local chart piece at the seam `T` -/

/-- **The local piece of the extension at `T`.**  For every chart centre `x₀` there are `δ > 0`, an
open `U ∋ (extChartAt I x₀) x₀` and a smooth matrix family `W` on `(Ioo (T-δ) (T+δ)) ×ˢ U` which
agrees with the chart matrix of `G` on `Ico (T-δ) T`, is symmetric everywhere and positive definite
on the whole two-sided slab. -/
theorem chart_piece_at_T
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hb : Work.Diff.EXT.ChartBounds G (T / 2) T)
    (hnd : ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
        a * (G 0).inner x u u ≤ (G t).inner x u u)
    (x₀ : M) :
    ∃ δ > 0, ∃ U : Set E, IsOpen U ∧ (extChartAt I x₀) x₀ ∈ U ∧
      ∃ W : ℝ × E → Work.Diff.EXT.MatE (E := E),
        ContDiffOn ℝ (⊤ : ℕ∞) W ((Set.Ioo (T - δ) (T + δ)) ×ˢ U) ∧
        (∀ t ∈ Set.Ico (T - δ) T, ∀ y ∈ U, W (t, y) = Work.Diff.EXT.chartMat G x₀ t y) ∧
        (∀ t ∈ Set.Ioo (T - δ) (T + δ), ∀ y ∈ U,
          (∀ i j, W (t, y) i j = W (t, y) j i) ∧
          ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
            0 < ∑ i, ∑ j, v i * v j * W (t, y) i j) := by
  classical
  -- ## The a priori data in the chart at `x₀`: ambient jet bounds and ellipticity
  obtain ⟨U₀, hU₀o, hy₀U₀, _hU₀b, _hU₀tgt, hU₀sm, hU₀bd, hell₀⟩ :=
    Work.Diff.EXT.ambient_jets_bounded (I := I) (M := M) hT hflow hb hnd x₀
  obtain ⟨ε, hεpos, hell⟩ := hell₀
  have hT2 : T / 2 < T := by linarith
  -- ## The smooth extension of the chart matrix past `T` (from the open-slab bounds)
  set σ' : ℝ := 3 * T / 4 with hσ'def
  have hσ'T : σ' < T := by rw [hσ'def]; linarith
  have hbnd' : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ (Set.Ico σ' T) ×ˢ U₀,
      ‖iteratedFDeriv ℝ k (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2) p‖ ≤ C := by
    intro k
    obtain ⟨C, hC0, hC⟩ := hU₀bd k
    exact ⟨C, hC0, fun p hp => hC p ⟨⟨by rw [hσ'def] at hp; linarith [hp.1.1, hT], hp.1.2⟩, hp.2⟩⟩
  have hu' : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      ((Set.Ico σ' T) ×ˢ U₀) :=
    hU₀sm.mono (Set.prod_mono (fun s hs => ⟨by rw [hσ'def] at hs; linarith [hs.1, hT], hs.2⟩)
      (fun y hy => hy))
  obtain ⟨U₁, hU₁o, hy₀U₁, _hU₁sub, δ₁, hδ₁, V₁, hV₁sm, hV₁eq⟩ :=
    Work.Diff.EXT.ext_of_bounded_jets_v2 (σ := σ') (Z := Work.Diff.EXT.MatE (E := E))
      hσ'T hU₀o (u := fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      hu' hbnd' hy₀U₀
  -- symmetrise
  set W : ℝ × E → Work.Diff.EXT.MatE (E := E) := symmFam V₁ with hWdef
  have hWsm : ContDiffOn ℝ (⊤ : ℕ∞) W ((Set.Ioo (T - δ₁) (T + δ₁)) ×ˢ U₁) :=
    contDiffOn_symmFam hV₁sm
  have hsymm₁ : ∀ t ∈ Set.Ico (T - δ₁) T, ∀ y ∈ U₁, ∀ i j,
      V₁ (t, y) i j = V₁ (t, y) j i := by
    intro t ht y hy i j
    rw [hV₁eq t ht y hy]
    exact Work.Diff.EXT.chartMatFun_symm (G t) x₀ y i j
  have hWeq : ∀ t ∈ Set.Ico (T - δ₁) T, ∀ y ∈ U₁, W (t, y) = Work.Diff.EXT.chartMat G x₀ t y := by
    intro t ht y hy
    have hsym : ∀ i j, V₁ (t, y) i j = V₁ (t, y) j i := hsymm₁ t ht y hy
    calc W (t, y) = symmFam V₁ (t, y) := by rw [hWdef]
      _ = V₁ (t, y) := by
          funext i j
          simp only [symmFam]
          rw [hsym i j]
          ring
      _ = Work.Diff.EXT.chartMat G x₀ t y := hV₁eq t ht y hy
  -- ## Positive definiteness at the seam `t = T`
  have hseam : ∀ y ∈ U₁ ∩ U₀, ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 →
      0 < ∑ i, ∑ j, v i * v j * W (T, y) i j := by
    intro y hy v hv
    have hy₁ : y ∈ U₁ := hy.1
    have hye : y ∈ U₀ := hy.2
    -- the quadratic form at the seam is the limit of the quadratic forms on the left
    have hQcont : Continuous (fun A : Work.Diff.EXT.MatE (E := E) =>
        ∑ i, ∑ j, v i * v j * A i j) := by fun_prop
    have hV₁at : ContinuousAt (fun p : ℝ × E => V₁ p) (T, y) :=
      hV₁sm.continuousOn.continuousAt
        (((isOpen_Ioo).prod hU₁o).mem_nhds
          ⟨⟨by linarith, by linarith⟩, hy₁⟩)
    have hcont : ContinuousAt (fun p : ℝ × E => ∑ i, ∑ j, v i * v j * V₁ p i j) (T, y) :=
      hQcont.continuousAt.comp hV₁at
    have hpair : Tendsto (fun t : ℝ => (t, y)) (𝓝[Set.Iio T] T) (𝓝 (T, y)) := by
      rw [nhds_prod_eq]
      exact (tendsto_id.prodMk tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    have hpath : Tendsto (fun t : ℝ => ∑ i, ∑ j, v i * v j * V₁ (t, y) i j)
        (𝓝[Set.Iio T] T) (𝓝 (∑ i, ∑ j, v i * v j * V₁ (T, y) i j)) :=
      hcont.tendsto.comp hpair
    have hev : ∀ᶠ t : ℝ in 𝓝[Set.Iio T] T,
        ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * V₁ (t, y) i j := by
      have hmem : Set.Ioo (max (T - δ₁) (T / 2)) T ∈ 𝓝[Set.Iio T] T := by
        have h1 : Set.Ioo (max (T - δ₁) (T / 2)) (T + 1) ∈ 𝓝 T :=
          isOpen_Ioo.mem_nhds ⟨max_lt (by linarith) (by linarith), by linarith⟩
        have hv' : Set.Ioo (max (T - δ₁) (T / 2)) (T + 1) ∈ 𝓝[Set.Iio T] T :=
          nhdsWithin_le_nhds h1
        have hw : Set.Iio T ∈ 𝓝[Set.Iio T] T := self_mem_nhdsWithin
        refine Filter.mem_of_superset (Filter.inter_mem hv' hw) ?_
        rintro x ⟨hx1, hx2⟩
        exact ⟨hx1.1, hx2⟩
      filter_upwards [hmem] with t ht
      have ht₁ : t ∈ Set.Ico (T - δ₁) T :=
        ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) ht.1), ht.2⟩
      have ht₂ : t ∈ Set.Ico (T / 2) T :=
        ⟨le_of_lt (lt_of_le_of_lt (le_max_right _ _) ht.1), ht.2⟩
      rw [hV₁eq t ht₁ y hy₁]
      exact hell t ht₂ y hye v
    have hlim := ge_of_tendsto hpath hev
    have hv2 : 0 < ∑ i, (v i) ^ 2 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      exact Finset.sum_pos' (fun j _ => sq_nonneg (v j))
        ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    have hWval := symmFam_quadForm V₁ (T, y) v
    rw [← hWval] at hlim
    exact lt_of_lt_of_le (mul_pos hεpos hv2) hlim
  -- ## The positivity tube across the seam
  have hU₁eo : IsOpen (U₁ ∩ U₀) := hU₁o.inter hU₀o
  have hy₀₁e : (extChartAt I x₀) x₀ ∈ U₁ ∩ U₀ := ⟨hy₀U₁, hy₀U₀⟩
  have hshiftc : ContinuousOn (fun p : ℝ × E => W (T + p.1, p.2))
      ((Set.Ioo (-δ₁) δ₁) ×ˢ (U₁ ∩ U₀)) := by
    have hmap : MapsTo (fun p : ℝ × E => (T + p.1, p.2))
        ((Set.Ioo (-δ₁) δ₁) ×ˢ (U₁ ∩ U₀)) ((Set.Ioo (T - δ₁) (T + δ₁)) ×ˢ U₁) := by
      rintro ⟨t, y⟩ ⟨ht, hy⟩
      exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hy.1⟩
    exact hWsm.continuousOn.comp (by fun_prop) hmap
  obtain ⟨a', ha'pos, U₃, hU₃o, hy₀₃, hU₃sub, htube⟩ :=
    Work.Diff.EXT.posDef_tube_of_continuous_seam (E := E) (a := δ₁) hδ₁ hU₁eo hy₀₁e hshiftc
      (fun y hy v hv => by simpa using hseam y hy v hv)
  -- ## The local piece
  have hminδ : min a' δ₁ ≤ δ₁ := min_le_right _ _
  have hmina : min a' δ₁ ≤ a' := min_le_left _ _
  refine ⟨min a' δ₁, lt_min ha'pos hδ₁, U₃, hU₃o, hy₀₃, W, ?_, ?_, ?_⟩
  · -- smoothness on the smaller two-sided slab
    refine hWsm.mono (fun p hp => ⟨⟨?_, ?_⟩, (hU₃sub hp.2).1⟩)
    · linarith [hp.1.1, hminδ]
    · linarith [hp.1.2, hminδ]
  · -- agreement with the chart matrix on `Ico (T - min a' δ₁) T`
    intro t ht y hy
    exact hWeq t ⟨by linarith [ht.1, hminδ], ht.2⟩ y (hU₃sub hy).1
  · -- symmetry and positive definiteness
    intro t ht y hy
    constructor
    · intro i j
      simp only [hWdef, symmFam]
      ring
    · intro v hv
      have ht' : t - T ∈ Set.Ioo (-a') a' :=
        ⟨by linarith [ht.1, hmina], by linarith [ht.2, hmina]⟩
      have h := htube (t - T) ht' y hy v hv
      have htT : T + (t - T) = t := by ring
      simpa only [htT] using h

/-! ## The target -/

theorem local_ext_of_chart_bounds_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hb : Work.Diff.EXT.ChartBounds G (T / 2) T)
    (hnd : ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
        a * (G 0).inner x u u ≤ (G t).inner x u u) :
    ∃ δ > 0, ∃ H₁ : ℝ → Submission.Diff.SMet I M,
      Submission.Diff.JointSmooth H₁ (Set.Ioo (T - δ) (T + δ)) ∧
        ∀ t ∈ Set.Ico (T - δ) T, H₁ t = G t :=
  Work.Diff.EXT.glue_seam_T_self (I := I) (M := M) G T hT hflow.1
    (fun x₀ => Work.Diff.EXT.chart_piece_at_T (I := I) (M := M) hT hflow hb hnd x₀)

end Work.Diff.EXT
