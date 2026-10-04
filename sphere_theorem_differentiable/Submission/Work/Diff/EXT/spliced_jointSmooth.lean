import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.chartMat_halfspace
import Submission.Work.Diff.EXT.contMDiffAt_section_of_chartMat
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.EXT.pde_splice_local_E
import Submission.Work.Diff.EXT.chartMat_twoSided
import Submission.Work.Diff.EXT.chartRicMat_ricPhi
import Submission.Work.Diff.EXT.ricPhi_contDiffOn
import Submission.Work.Diff.EXT.chartMatFun_det_ne_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

/-- The section of the bundle of bilinear forms associated with a family of metrics, written as a
map into the total space (this is the function appearing in `Submission.Diff.JointSmooth`). -/
noncomputable def secOf (F : ℝ → Submission.Diff.SMet I M) :
    ℝ × M → TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :=
  fun p ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
    (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2 ((F p.1).inner p.2)

lemma jointSmooth_iff (F : ℝ → Submission.Diff.SMet I M) (J : Set ℝ) :
    Submission.Diff.JointSmooth F J ↔
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞) (secOf F)
        (J ×ˢ univ) := Iff.rfl

lemma secOf_congr {F F' : ℝ → Submission.Diff.SMet I M} {t t' : ℝ} {x : M} (h : F t = F' t') :
    secOf F (t, x) = secOf F' (t', x) := by
  simp only [secOf, h]

/-- **The time derivative of the chart matrix of a Ricci flow is minus twice the chart Ricci
matrix**: this is the Ricci flow equation `∂ₜg = -2 Ric` read in the coordinate frame of the chart
at `x₀`, together with the definition of the chart matrices. -/
lemma hasDerivAt_chartMat_of_isRicciFlow
    {G : ℝ → Submission.Diff.SMet I M} {τ : ℝ} (h : Submission.Diff.IsRicciFlow G τ)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 τ) (x₀ : M) (y : E) :
    HasDerivAt (fun s : ℝ ↦ chartMat G x₀ s y) ((-2 : ℝ) • chartRicMat (G t) x₀ y) t := by
  have hmem : Set.Ico 0 τ ∈ 𝓝 t :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Ico_self
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  have hflow := (h.2 t ⟨le_of_lt ht.1, ht.2⟩ ((extChartAt I x₀).symm y)
    (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) (bB (E := E) i))
    (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
      (bB (E := E) j))).hasDerivAt hmem
  convert hflow using 1
  · funext s
    rfl
  · simp only [Pi.smul_apply, chartRicMat, smul_eq_mul]

lemma deriv_chartMat_of_isRicciFlow
    {G : ℝ → Submission.Diff.SMet I M} {τ : ℝ} (h : Submission.Diff.IsRicciFlow G τ)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 τ) (x₀ : M) (y : E) :
    deriv (fun s : ℝ ↦ chartMat G x₀ s y) t = (-2 : ℝ) • chartRicMat (G t) x₀ y :=
  (hasDerivAt_chartMat_of_isRicciFlow h ht x₀ y).deriv

/-- The spatial `2`-jet of the time-shifted chart matrix is the jet of the chart matrix of the
metric at the corresponding time. -/
lemma jet2_shift_chartMat (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (T σ : ℝ) (y : E) :
    jet2 (fun p : ℝ × E ↦ chartMat G x₀ (T + p.1) p.2) (σ, y) =
      jet2 (fun p : ℝ × E ↦ chartMatFun (G (T + σ)) x₀ p.2) (0, y) := by
  simp only [jet2, chartMat, chartMatFun]

/-- The time derivative of the time-shifted chart matrix of a Ricci flow. -/
lemma deriv_chartMat_shift_of_isRicciFlow
    {G : ℝ → Submission.Diff.SMet I M} {τ T : ℝ} (h : Submission.Diff.IsRicciFlow G τ)
    {σ : ℝ} (hσ : T + σ ∈ Set.Ioo 0 τ) (x₀ : M) (y : E) :
    deriv (fun s : ℝ ↦ chartMat G x₀ (T + s) y) σ =
      (-2 : ℝ) • chartRicMat (G (T + σ)) x₀ y := by
  rw [deriv_comp_const_add (fun t : ℝ ↦ chartMat G x₀ t y) T σ,
    deriv_chartMat_of_isRicciFlow h hσ x₀ y]

/-- **Translation of the time coordinate**: `f` is `C^∞` at `(T, y₀)` if and only if the function
`(σ, y) ↦ f (T + σ, y)` is `C^∞` at `(0, y₀)`. -/
lemma contDiffAt_comp_add_fst_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} {T : ℝ} {y₀ : E} :
    ContDiffAt ℝ (⊤ : ℕ∞) f (T, y₀) ↔
      ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E ↦ f (T + p.1, p.2)) (0, y₀) := by
  constructor
  · intro h
    have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E ↦ (T + p.1, p.2)) (0, y₀) := by fun_prop
    have h' : ContDiffAt ℝ (⊤ : ℕ∞) f ((fun p : ℝ × E ↦ (T + p.1, p.2)) (0, y₀)) := by
      simpa using h
    exact h'.comp (0, y₀) hs
  · intro h
    have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × E ↦ (q.1 - T, q.2)) (T, y₀) := by fun_prop
    have h' : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E ↦ f (T + p.1, p.2))
        ((fun q : ℝ × E ↦ (q.1 - T, q.2)) (T, y₀)) := by
      have : ((T : ℝ), y₀).1 - T = 0 := by simp
      simpa only [this] using h
    refine (h'.comp (T, y₀) hs).congr_of_eventuallyEq ?_
    filter_upwards with q
    have hq : (T + (q.1 - T), q.2) = q := by
      ext
      · ring
      · rfl
    simp only [Function.comp_apply]
    rw [hq]

/-- Smoothness of the time-shifted chart matrix of a family that is jointly smooth near `T`. -/
lemma contDiffOn_chartMat_shift [I.Boundaryless] {G : ℝ → Submission.Diff.SMet I M} {T ε : ℝ}
    (hG : Submission.Diff.JointSmooth G (Set.Ioo (T - ε) (T + ε))) (x₀ : M) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E ↦ chartMat G x₀ (T + p.1) p.2)
      (Set.Ioo (-ε) ε ×ˢ (extChartAt I x₀).target) := by
  intro p hp
  have htarget : (extChartAt I x₀).target ∈ 𝓝 p.2 :=
    (isOpen_extChartAt_target (I := I) x₀).mem_nhds hp.2
  have hJ : Set.Ioo (T - ε) (T + ε) ∈ 𝓝 (T + p.1) :=
    (isOpen_Ioo).mem_nhds (by constructor <;> linarith [hp.1.1, hp.1.2])
  have hwithin := contDiffWithinAt_chartMat_of_jointSmooth_gen (I := I) hG (t₀ := T + p.1) (x₀ := x₀)
    (y := p.2) (by constructor <;> linarith [hp.1.1, hp.1.2]) hp.2
  have hat : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × E ↦ chartMat G x₀ q.1 q.2) (T + p.1, p.2) :=
    hwithin.contDiffAt (by rw [nhds_prod_eq]; exact Filter.prod_mem_prod hJ htarget)
  have hshift : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × E ↦ (T + q.1, q.2)) p := by fun_prop
  have hcomp := hat.comp p hshift
  exact hcomp.contDiffWithinAt

/-- The slice at `t = T` of the `G`-branch agrees with the extended `H`-branch. -/
lemma slice_chartMat_eq {G H : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hval : H 0 = G T)
    {x₀ : M} {w : ℝ × E → MatE (E := E)} {Bw : Set (ℝ × E)}
    (hBw : Bw ∈ 𝓝 ((0 : ℝ), (extChartAt I x₀) x₀))
    (hw : ∀ p ∈ Bw, 0 ≤ p.1 → w p = chartMat H x₀ p.1 p.2) :
    (fun y : E ↦ chartMat G x₀ (T + 0) y) =ᶠ[𝓝 ((extChartAt I x₀) x₀)] fun y : E ↦ w (0, y) := by
  have hpre : {y : E | ((0 : ℝ), y) ∈ Bw} ∈ 𝓝 ((extChartAt I x₀) x₀) :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hBw
  filter_upwards [hpre] with y hy
  have h1 : w (0, y) = chartMat H x₀ 0 y := hw (0, y) hy le_rfl
  have h2 : chartMat H x₀ 0 y = chartMat G x₀ (T + 0) y := by
    simp only [chartMat, chartMatFun, hval, add_zero]
  rw [h1, h2]

/-- A uniform positive lower bound for the absolute determinant of a non-degenerate continuous
family of matrices on a compact set. -/
lemma exists_pos_le_abs_det {f : ℝ × E → MatE (E := E)} {s : Set (ℝ × E)}
    (hs : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s)
    (h0 : ∀ z ∈ s, (Matrix.of (f z)).det ≠ 0) :
    ∃ δ > 0, ∀ z ∈ s, δ ≤ |(Matrix.of (f z)).det| := by
  have hcont : ContinuousOn (fun z : ℝ × E ↦ |(Matrix.of (f z)).det|) s := by
    refine ContinuousOn.abs ?_
    refine Continuous.comp_continuousOn ?_ hf
    exact (contDiff_matrix_det_pi (n := Module.finrank ℝ E)).continuous
  obtain ⟨z₀, hz₀, hmin⟩ := hs.exists_isMinOn hne hcont
  exact ⟨|(Matrix.of (f z₀)).det|, abs_pos.mpr (h0 z₀ hz₀), fun z hz => hmin hz⟩

/-- The splice in the time-shifted chart coordinates, as the splice of the two branches. -/
lemma chartMat_spliced_shift_eq (G H : ℝ → Submission.Diff.SMet I M) (T : ℝ) (x₀ : M)
    (p : ℝ × E) :
    chartMat (fun t : ℝ ↦ if t ≤ T then G t else H (t - T)) x₀ (T + p.1) p.2 =
      (if p.1 ≤ 0 then chartMat G x₀ (T + p.1) p.2 else chartMat H x₀ p.1 p.2) := by
  by_cases h : p.1 ≤ 0
  · have hT : T + p.1 ≤ T := by linarith
    simp only [chartMat, chartMatFun, hT, h, ite_true]
  · have hT : ¬ (T + p.1 ≤ T) := by linarith
    have h2 : (T + p.1) - T = p.1 := by ring
    simp only [chartMat, chartMatFun, hT, h, ite_false, h2]

/-- `jet2` only depends on the germ of the function. -/
lemma jet2_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : ℝ × E → F}
    {p : ℝ × E} (h : f =ᶠ[𝓝 p] g) : jet2 f p = jet2 g p := by
  have hp : f p = g p := h.eq_of_nhds
  have hslice : (fun y : E ↦ f (p.1, y)) =ᶠ[𝓝 p.2] (fun y : E ↦ g (p.1, y)) :=
    h.comp_tendsto (by rw [nhds_prod_eq]; exact tendsto_const_nhds.prodMk tendsto_id)
  have h1 : fderiv ℝ (fun y : E ↦ f (p.1, y)) p.2 = fderiv ℝ (fun y : E ↦ g (p.1, y)) p.2 :=
    hslice.fderiv.eq_of_nhds
  have h2 : fderiv ℝ (fun w : E ↦ fderiv ℝ (fun y : E ↦ f (p.1, y)) w) p.2
      = fderiv ℝ (fun w : E ↦ fderiv ℝ (fun y : E ↦ g (p.1, y)) w) p.2 := by
    have h3 : (fun w : E ↦ fderiv ℝ (fun y : E ↦ f (p.1, y)) w) =ᶠ[𝓝 p.2]
        (fun w : E ↦ fderiv ℝ (fun y : E ↦ g (p.1, y)) w) := hslice.fderiv
    exact h3.fderiv.eq_of_nhds
  rw [jet2, jet2, hp, h1, h2]

/-- **The chart matrix of the spliced family is smooth at the seam.**  Coordinate form of the
restart step: the splice of a Ricci flow `G` on `[0,T)` (jointly smooth on a neighbourhood of `T`)
with a Ricci flow `H` on `[0,τ)` starting at `G T` has a `C^∞` chart matrix at the seam. -/
theorem chartMat_spliced_contDiffAt
    [I.Boundaryless] [T2Space M] (G H : ℝ → Submission.Diff.SMet I M) {T τ ε : ℝ}
    (hTpos : 0 < T) (hτpos : 0 < τ) (hε : 0 < ε)
    (hG : Submission.Diff.JointSmooth G (Set.Ioo (T - ε) (T + ε)))
    (hGflow : Submission.Diff.IsRicciFlow G T)
    (hH : Submission.Diff.IsRicciFlow H τ) (hval : H 0 = G T) (x₀ : M) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : ℝ × E ↦ chartMat (fun t : ℝ ↦ if t ≤ T then G t else H (t - T)) x₀ p.1 p.2)
      (T, (extChartAt I x₀) x₀) := by
  set S : ℝ → Submission.Diff.SMet I M := fun t ↦ if t ≤ T then G t else H (t - T) with hSdef
  set y₀ : E := (extChartAt I x₀) x₀ with hy₀def
  rw [contDiffAt_comp_add_fst_iff]
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E ↦ chartMat S x₀ (T + p.1) p.2) (0, y₀)
  -- the two branches
  set u : ℝ × E → MatE (E := E) := fun p ↦ chartMat G x₀ (T + p.1) p.2 with hudef
  obtain ⟨Bw, hBw_open, hBw_mem, w, hw_smooth, hw_eq⟩ := chartMat_twoSided H hτpos hH.1 x₀
  -- the radius
  have hBw_nhds : Bw ∈ 𝓝 ((0 : ℝ), y₀) := hBw_open.mem_nhds hBw_mem
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp hBw_nhds
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := I) x₀).mem_nhds
      ((extChartAt I x₀).map_source (mem_extChartAt_source x₀)))
  set r : ℝ := min (min δ₁ δ₂) (min ε (min T τ)) / 2 with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    have h : 0 < min (min δ₁ δ₂) (min ε (min T τ)) :=
      lt_min (lt_min hδ₁pos hδ₂pos) (lt_min hε (lt_min hTpos hτpos))
    linarith
  have hrδ₁ : r < δ₁ := by
    have h : min (min δ₁ δ₂) (min ε (min T τ)) ≤ δ₁ :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    rw [hrdef]; linarith
  have hrδ₂ : r < δ₂ := by
    have h : min (min δ₁ δ₂) (min ε (min T τ)) ≤ δ₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    rw [hrdef]; linarith
  have hrε : r < ε := by
    have h : min (min δ₁ δ₂) (min ε (min T τ)) ≤ ε :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    rw [hrdef]; linarith
  have hrT : r < T := by
    have h : min (min δ₁ δ₂) (min ε (min T τ)) ≤ T :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    rw [hrdef]; linarith
  have hrτ : r < τ := by
    have h : min (min δ₁ δ₂) (min ε (min T τ)) ≤ τ :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [hrdef]; linarith
  -- every point of the closed ball lies in the good regions
  have hclosed : ∀ z ∈ Metric.closedBall ((0 : ℝ), y₀) r,
      z.2 ∈ (extChartAt I x₀).target ∧ z.1 ∈ Set.Ioo (-ε) ε ∧ z.1 ∈ Set.Ioo (-T) T ∧ z.1 < τ := by
    intro z hz
    have hz' : dist z ((0 : ℝ), y₀) ≤ r := Metric.mem_closedBall.mp hz
    rw [Prod.dist_eq] at hz'
    have h1 : dist z.1 0 ≤ r := le_trans (le_max_left _ _) hz'
    have h2 : dist z.2 y₀ ≤ r := le_trans (le_max_right _ _) hz'
    have habs : |z.1| ≤ r := by simpa [Real.dist_eq] using h1
    exact ⟨hδ₂ (Metric.mem_ball.mpr (lt_of_le_of_lt h2 hrδ₂)),
      ⟨(abs_lt.mp (lt_of_le_of_lt habs hrε)).1, (abs_lt.mp (lt_of_le_of_lt habs hrε)).2⟩,
      ⟨(abs_lt.mp (lt_of_le_of_lt habs hrT)).1, (abs_lt.mp (lt_of_le_of_lt habs hrT)).2⟩,
      lt_of_le_of_lt (le_abs_self z.1) (lt_of_le_of_lt habs hrτ)⟩
  set B : Set (ℝ × E) := Metric.ball ((0 : ℝ), y₀) r with hBdef
  have hB_open : IsOpen B := Metric.isOpen_ball
  have hB_mem : ((0 : ℝ), y₀) ∈ B := Metric.mem_ball_self hrpos
  have hB_closed : B ⊆ Metric.closedBall ((0 : ℝ), y₀) r := Metric.ball_subset_closedBall
  have hBw_sub : B ⊆ Bw := fun z hz =>
    hδ₁ (Metric.mem_ball.mpr (lt_trans (Metric.mem_ball.mp hz) hrδ₁))
  have hclosed_subBw : Metric.closedBall ((0 : ℝ), y₀) r ⊆ Bw := fun z hz =>
    hδ₁ (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hrδ₁))
  -- smoothness of the two branches
  have hu_smooth : ContDiffOn ℝ (⊤ : ℕ∞) u B := by
    refine (contDiffOn_chartMat_shift (I := I) hG x₀).mono ?_
    intro z hz
    obtain ⟨hzt, hzσ, -, -⟩ := hclosed z (hB_closed hz)
    exact ⟨hzσ, hzt⟩
  have hw_smoothB : ContDiffOn ℝ (⊤ : ℕ∞) w B := hw_smooth.mono hBw_sub
  have hu_cont : ContinuousOn u (Metric.closedBall ((0 : ℝ), y₀) r) := by
    refine (contDiffOn_chartMat_shift (I := I) hG x₀).continuousOn.mono ?_
    intro z hz
    obtain ⟨hzt, hzσ, -, -⟩ := hclosed z hz
    exact ⟨hzσ, hzt⟩
  have hw_cont : ContinuousOn w (Metric.closedBall ((0 : ℝ), y₀) r) :=
    (hw_smooth.continuousOn).mono hclosed_subBw
  -- lower bounds for the determinants on the closed ball
  obtain ⟨δu, hδupos, hδu⟩ : ∃ δ > 0,
      ∀ z ∈ Metric.closedBall ((0 : ℝ), y₀) r, z.1 ≤ 0 → δ ≤ |(Matrix.of (u z)).det| := by
    have hne : (Metric.closedBall ((0 : ℝ), y₀) r ∩ {z : ℝ × E | z.1 ≤ 0}).Nonempty :=
      ⟨((0 : ℝ), y₀), Metric.mem_closedBall_self (le_of_lt hrpos), le_refl (0 : ℝ)⟩
    have hK : IsCompact (Metric.closedBall ((0 : ℝ), y₀) r ∩ {z : ℝ × E | z.1 ≤ 0}) :=
      (isCompact_closedBall _ _).inter_right (isClosed_Iic.preimage continuous_fst)
    obtain ⟨δ, hδpos, hδ⟩ := exists_pos_le_abs_det hK hne (hu_cont.mono Set.inter_subset_left)
      (fun z hz => by
        have hzt : z.2 ∈ (extChartAt I x₀).target := (hclosed z hz.1).1
        simpa [hudef, chartMat] using chartMatFun_det_ne_zero (I := I) (G (T + z.1)) x₀ hzt)
    exact ⟨δ, hδpos, fun z hz hz0 => hδ z ⟨hz, hz0⟩⟩
  obtain ⟨δw, hδwpos, hδw⟩ : ∃ δ > 0,
      ∀ z ∈ Metric.closedBall ((0 : ℝ), y₀) r, 0 ≤ z.1 → δ ≤ |(Matrix.of (w z)).det| := by
    have hne : (Metric.closedBall ((0 : ℝ), y₀) r ∩ {z : ℝ × E | 0 ≤ z.1}).Nonempty :=
      ⟨((0 : ℝ), y₀), Metric.mem_closedBall_self (le_of_lt hrpos), le_refl (0 : ℝ)⟩
    have hK : IsCompact (Metric.closedBall ((0 : ℝ), y₀) r ∩ {z : ℝ × E | 0 ≤ z.1}) :=
      (isCompact_closedBall _ _).inter_right (isClosed_Ici.preimage continuous_fst)
    obtain ⟨δ, hδpos, hδ⟩ := exists_pos_le_abs_det hK hne (hw_cont.mono Set.inter_subset_left)
      (fun z hz => by
        have hzt : z.2 ∈ (extChartAt I x₀).target := (hclosed z hz.1).1
        have hzw : w z = chartMatFun (H z.1) x₀ z.2 := by
          rw [hw_eq z (hclosed_subBw hz.1) hz.2, chartMat]
        rw [hzw]
        exact chartMatFun_det_ne_zero (I := I) (H z.1) x₀ hzt)
    exact ⟨δ, hδpos, fun z hz hz0 => hδ z ⟨hz, hz0⟩⟩
  set δ : ℝ := min δu δw with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hδupos hδwpos
  -- the cutoff and the regularised right hand side
  set χ : ℝ → ℝ := fun t ↦ Real.smoothTransition (2 * t / δ - 1) with hχdef
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χ := by
    rw [hχdef]
    exact Real.smoothTransition.contDiff.comp (by fun_prop)
  have hχ_one : ∀ t : ℝ, δ ≤ t → χ t = 1 := by
    intro t ht
    rw [hχdef]
    refine Real.smoothTransition.one_of_one_le ?_
    have : (2 : ℝ) ≤ 2 * t / δ := by
      rw [le_div_iff₀ hδpos]; linarith
    linarith
  have hχ_zero : ∀ t : ℝ, t ≤ δ / 2 → χ t = 0 := by
    intro t ht
    rw [hχdef]
    refine Real.smoothTransition.zero_of_nonpos ?_
    have : 2 * t / δ ≤ 1 := by
      rw [div_le_iff₀ hδpos]; linarith
    linarith
  set Φ : E × (MatE (E := E) × (E →L[ℝ] MatE (E := E)) × (E →L[ℝ] E →L[ℝ] MatE (E := E))) →
      MatE (E := E) :=
    fun z ↦ χ |(Matrix.of z.2.1).det| • ((-2 : ℝ) • ricPhi z) with hΦdef
  have hΦ_smooth : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    rw [contDiff_iff_contDiffAt]
    intro z
    have hproj : ContinuousAt
        (fun z' : E × (MatE (E := E) × (E →L[ℝ] MatE (E := E)) × (E →L[ℝ] E →L[ℝ] MatE (E := E))) ↦
          z'.2.1) z :=
      (continuous_fst.comp continuous_snd).continuousAt
    have hdetcont : ContinuousAt
        (fun z' : E × (MatE (E := E) × (E →L[ℝ] MatE (E := E)) × (E →L[ℝ] E →L[ℝ] MatE (E := E))) ↦
          (Matrix.of z'.2.1).det) z :=
      (((contDiff_matrix_det_pi (n := Module.finrank ℝ E)).continuous).continuousAt).comp hproj
    by_cases hz : (Matrix.of z.2.1).det = 0
    · have hzabs : |(Matrix.of z.2.1).det| = 0 := by rw [hz, abs_zero]
      have hev : ∀ᶠ z' in 𝓝 z,
          |(Matrix.of z'.2.1).det| ≤ δ / 2 := by
        have hlt : |(Matrix.of z.2.1).det| < δ / 2 := by
          rw [hzabs]; linarith
        have hmem : |(Matrix.of z.2.1).det| ∈ {b : ℝ | b < δ / 2} := hlt
        have := hdetcont.abs.tendsto.eventually
          ((isOpen_lt continuous_id continuous_const).mem_nhds hmem)
        filter_upwards [this] with z' hz'
        exact le_of_lt hz'
      refine (contDiffAt_const (c := (0 : MatE (E := E)))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with z' hz'
      change χ |(Matrix.of z'.2.1).det| • ((-2 : ℝ) • ricPhi z') = 0
      rw [hχ_zero _ hz', zero_smul]
    · have hopen : {z' : E × (MatE (E := E) × (E →L[ℝ] MatE (E := E)) ×
            (E →L[ℝ] E →L[ℝ] MatE (E := E))) | (Matrix.of z'.2.1).det ≠ 0} ∈ 𝓝 z := by
        have hcl : IsClosed {z' : E × (MatE (E := E) × (E →L[ℝ] MatE (E := E)) ×
              (E →L[ℝ] E →L[ℝ] MatE (E := E))) | (Matrix.of z'.2.1).det = 0} :=
          IsClosed.preimage
            (((contDiff_matrix_det_pi (n := Module.finrank ℝ E)).continuous).comp
              (continuous_fst.comp continuous_snd))
            (isClosed_singleton : IsClosed ({(0 : ℝ)} : Set ℝ))
        exact hcl.isOpen_compl.mem_nhds hz
      have hproj : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun z' : E × (MatE (E := E) × (E →L[ℝ] MatE (E := E)) ×
            (E →L[ℝ] E →L[ℝ] MatE (E := E))) ↦ z'.2.1) z :=
        contDiffAt_fst.comp z contDiffAt_snd
      have hdet_at : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun z' : E × (MatE (E := E) × (E →L[ℝ] MatE (E := E)) ×
            (E →L[ℝ] E →L[ℝ] MatE (E := E))) ↦ (Matrix.of z'.2.1).det) z :=
        ((contDiff_matrix_det_pi (n := Module.finrank ℝ E)).contDiffAt).comp z hproj
      have habs : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun z' : E × (MatE (E := E) × (E →L[ℝ] MatE (E := E)) ×
            (E →L[ℝ] E →L[ℝ] MatE (E := E))) ↦ |(Matrix.of z'.2.1).det|) z :=
        hdet_at.abs hz
      have hric : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun z' : E × (MatE (E := E) × (E →L[ℝ] MatE (E := E)) ×
            (E →L[ℝ] E →L[ℝ] MatE (E := E))) ↦ ricPhi z') z :=
        (ricPhi_contDiffOn (E := E)).contDiffAt hopen
      exact (hχ_smooth.contDiffAt.comp z habs).smul
        ((contDiffAt_const (c := (-2 : ℝ))).smul hric)
  -- the equations satisfied by the two branches
  have huS : ∀ z ∈ B, z.1 < 0 → deriv (fun s : ℝ ↦ u (s, z.2)) z.1 = Φ (z.2, jet2 u z) := by
    intro z hz hz0
    obtain ⟨hzt, -, hzT, -⟩ := hclosed z (hB_closed hz)
    have hjet : jet2 u z =
        jet2 (fun p : ℝ × E ↦ chartMatFun (G (T + z.1)) x₀ p.2) (0, z.2) := by
      rw [hudef]
      exact jet2_shift_chartMat G x₀ T z.1 z.2
    have hL : deriv (fun s : ℝ ↦ u (s, z.2)) z.1 =
        (-2 : ℝ) • chartRicMat (G (T + z.1)) x₀ z.2 := by
      rw [hudef]
      exact deriv_chartMat_shift_of_isRicciFlow hGflow
        ⟨by linarith [hzT.1], by linarith⟩ x₀ z.2
    have hχ1 : χ |(Matrix.of (jet2 (fun p : ℝ × E ↦ chartMatFun (G (T + z.1)) x₀ p.2)
        (0, z.2)).1).det| = 1 := by
      apply hχ_one
      have hb : δ ≤ |(Matrix.of (u z)).det| :=
        le_trans (by rw [hδdef]; exact min_le_left _ _)
          (hδu z (hB_closed hz) (le_of_lt hz0))
      simpa [jet2, hudef, chartMat] using hb
    rw [hL, hjet, hΦdef]
    dsimp only
    rw [hχ1, one_smul, chartRicMat_ricPhi x₀ (G (T + z.1)) z.2 hzt]
  have hwS : ∀ z ∈ B, 0 < z.1 → deriv (fun s : ℝ ↦ w (s, z.2)) z.1 = Φ (z.2, jet2 w z) := by
    intro z hz hz0
    obtain ⟨hzt, -, -, hzτ⟩ := hclosed z (hB_closed hz)
    have hzBw : z ∈ Bw := hBw_sub hz
    have hwg : w =ᶠ[𝓝 z] (fun p : ℝ × E ↦ chartMat H x₀ p.1 p.2) := by
      filter_upwards [hBw_open.mem_nhds hzBw,
        continuous_fst.continuousAt.preimage_mem_nhds
          ((isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ))).mem_nhds hz0)] with p hp hppos
      exact hw_eq p hp (le_of_lt hppos)
    have hjet : jet2 w z = jet2 (fun p : ℝ × E ↦ chartMatFun (H z.1) x₀ p.2) (0, z.2) := by
      rw [jet2_congr hwg]
      simp only [jet2, chartMat, chartMatFun]
    have hL : deriv (fun s : ℝ ↦ w (s, z.2)) z.1 =
        (-2 : ℝ) • chartRicMat (H z.1) x₀ z.2 := by
      have hsl : (fun s : ℝ ↦ w (s, z.2)) =ᶠ[𝓝 z.1]
          (fun s : ℝ ↦ chartMat H x₀ s z.2) :=
        hwg.comp_tendsto (by rw [nhds_prod_eq]; exact tendsto_id.prodMk tendsto_const_nhds)
      rw [hsl.deriv_eq]
      exact deriv_chartMat_of_isRicciFlow hH ⟨hz0, hzτ⟩ x₀ z.2
    have hwz : w z = chartMatFun (H z.1) x₀ z.2 := by
      rw [hw_eq z hzBw (le_of_lt hz0), chartMat]
    have hb : δ ≤ |(Matrix.of (w z)).det| :=
      le_trans (by rw [hδdef]; exact min_le_right _ _)
        (hδw z (hB_closed hz) (le_of_lt hz0))
    have hχ1 : χ |(Matrix.of (jet2 (fun p : ℝ × E ↦ chartMatFun (H z.1) x₀ p.2)
        (0, z.2)).1).det| = 1 := by
      apply hχ_one
      simpa [jet2, hwz] using hb
    rw [hL, hjet, hΦdef]
    dsimp only
    rw [hχ1, one_smul, chartRicMat_ricPhi x₀ (H z.1) z.2 hzt]
  have hslice : (fun y : E ↦ u (0, y)) =ᶠ[𝓝 y₀] (fun y : E ↦ w (0, y)) := by
    rw [hudef]
    exact slice_chartMat_eq hval hBw_nhds hw_eq
  -- the local splicing result
  have hcore := pde_splice_local_E (E := E) (T := 0) hB_open hB_mem Φ hΦ_smooth hu_smooth
    hw_smoothB huS hwS hslice
  refine hcore.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds ((0 : ℝ), y₀) hrpos] with z hz
  rw [hSdef, chartMat_spliced_shift_eq]
  by_cases hz0 : z.1 ≤ 0
  · rw [if_pos hz0, if_pos hz0, hudef]
  · have hw' : w z = chartMat H x₀ z.1 z.2 :=
      hw_eq z (hBw_sub hz) (le_of_lt (lt_of_not_ge hz0))
    rw [if_neg hz0, if_neg hz0, hw']

/-- **Smoothness of the spliced family (the restart step).**  Let `G` be a family of metrics which is
jointly smooth on a neighbourhood of `[0,T]` and solves the Ricci flow equation `∂ₜg = -2Ric` on
`[0,T)`, and let `H` be a Ricci flow on `[0,τ)` whose initial metric `H 0` is the limit metric
`G T` of `G`.  Then the spliced family `t ↦ (if t ≤ T then G t else H (t-T))` is jointly smooth on
`(0, T+τ)`.  (The point is the compatibility at `t = T`: both sides solve the same equation and
attain the same metric at `T`, so their spatial jets at `T` agree, hence by the determinacy of the
`t`-jets for a quasilinear parabolic system the splice is `C^∞` there.) -/
theorem spliced_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G H : ℝ → Submission.Diff.SMet I M) (T τ ε : ℝ) (hε : 0 < ε)
    (hG : Submission.Diff.JointSmooth G (Set.Ioo (T - ε) (T + ε)))
    (hGflow : Submission.Diff.IsRicciFlow G T)
    (hH : Submission.Diff.IsRicciFlow H τ) (hval : H 0 = G T) :
    Submission.Diff.JointSmooth (fun t : ℝ => if t ≤ T then G t else H (t - T))
      (Set.Ioo 0 (T + τ)) := by
  set S : ℝ → Submission.Diff.SMet I M := fun t ↦ if t ≤ T then G t else H (t - T) with hSdef
  rw [jointSmooth_iff]
  intro p hp
  obtain ⟨t₀, x⟩ := p
  rcases lt_trichotomy t₀ T with hlt | heq | hgt
  · -- the splice agrees with `G` near `(t₀, x)`
    have hmem : Set.Ico 0 T ×ˢ (univ : Set M) ∈ 𝓝 (t₀, x) := by
      have hIoo : Set.Ioo (0 : ℝ) T ∈ 𝓝 t₀ := isOpen_Ioo.mem_nhds ⟨hp.1.1, hlt⟩
      have hIco : Set.Ico (0 : ℝ) T ∈ 𝓝 t₀ := Filter.mem_of_superset hIoo Set.Ioo_subset_Ico_self
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod hIco Filter.univ_mem
    have hGat : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
        (secOf G) (t₀, x) :=
      (hGflow.1 (t₀, x) ⟨⟨le_of_lt hp.1.1, hlt⟩, mem_univ x⟩).contMDiffAt hmem
    refine (hGat.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [continuousAt_fst.preimage_mem_nhds (isOpen_Iio.mem_nhds hlt)] with q hq
    rw [Set.mem_preimage, Set.mem_Iio] at hq
    show secOf S (q.1, q.2) = secOf G (q.1, q.2)
    exact secOf_congr (by rw [hSdef]; simp only [if_pos (le_of_lt hq)])
  · -- the seam `t₀ = T`
    have hTpos : 0 < T := by rw [← heq]; exact hp.1.1
    have hτpos : 0 < τ := by linarith [hp.1.2]
    refine (contMDiffAt_section_of_chartMat (G := S) (t₀ := t₀) (x₀ := x) ?_).contMDiffWithinAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E ↦ chartMat S x p.1 p.2)
        (T, (extChartAt I x) x) := by
      rw [hSdef]
      exact chartMat_spliced_contDiffAt G H hTpos hτpos hε hG hGflow hH hval x
    simpa only [heq] using h2
  · -- the splice agrees with `H (· - T)` near `(t₀, x)`
    have hpos : 0 < t₀ - T := sub_pos.mpr hgt
    have hltτ : t₀ - T < τ := by linarith [hp.1.2]
    have hmem : Set.Ico 0 τ ×ˢ (univ : Set M) ∈ 𝓝 (t₀ - T, x) := by
      have hIoo : Set.Ioo (0 : ℝ) τ ∈ 𝓝 (t₀ - T) := isOpen_Ioo.mem_nhds ⟨hpos, hltτ⟩
      have hIco : Set.Ico (0 : ℝ) τ ∈ 𝓝 (t₀ - T) :=
        Filter.mem_of_superset hIoo Set.Ioo_subset_Ico_self
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod hIco Filter.univ_mem
    have hHat : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
        (secOf H) (t₀ - T, x) :=
      (hH.1 (t₀ - T, x) ⟨⟨le_of_lt hpos, hltτ⟩, mem_univ x⟩).contMDiffAt hmem
    have hshift : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) ((𝓘(ℝ, ℝ)).prod I) (⊤ : ℕ∞)
        (fun q : ℝ × M ↦ (q.1 - T, q.2)) (t₀, x) :=
      (contMDiffAt_fst.sub (contMDiffAt_const (c := T))).prodMk contMDiffAt_snd
    have hHat' : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
        (fun q : ℝ × M ↦ secOf H (q.1 - T, q.2)) (t₀, x) :=
      hHat.comp (t₀, x) hshift
    refine (hHat'.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [continuousAt_fst.preimage_mem_nhds (isOpen_Ioi.mem_nhds hgt)] with q hq
    rw [Set.mem_preimage, Set.mem_Ioi] at hq
    show secOf S (q.1, q.2) = secOf H (q.1 - T, q.2)
    exact secOf_congr (by rw [hSdef]; simp only [if_neg (not_le.mpr hq)])

end Work.Diff.EXT
