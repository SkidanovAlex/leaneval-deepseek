import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.jets_bounded_of_pde
import Submission.Work.Diff.EXT.contDiffWithinAt_chartMat_of_jointSmooth
import Submission.Work.Diff.EXT.chartRic_partial_jet
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.EXT.AuxL.det_lower_bound_of_quadForm
import Submission.Work.Diff.EXT.uniform_posDef_of_continuous_v2
import Submission.Work.Diff.EXT.AuxL.chartMatFun_continuousAt_centre
import Submission.Work.Diff.EXT.AuxL.chartMatFun_centre_posDef
import Submission.Work.Diff.EXT.Jets2.JetsBounded

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The chart matrix: symmetry and the quadratic-form identity -/

/-- The chart matrix of a metric is symmetric. -/
lemma chartMatFun_symm (g : Submission.Diff.SMet I M) (x₀ : M) (y : E)
    (i j : Fin (Module.finrank ℝ E)) :
    chartMatFun g x₀ y i j = chartMatFun g x₀ y j i :=
  g.symm _ _ _

/-- **The quadratic form of the chart matrix is the metric of the combination**: for coefficients
`v`, the double sum `∑ i, ∑ j, v i * v j * chartMatFun g x₀ y i j` is the `g`-square of the tangent
vector `∑ i, v i • σᵢ` (with `σᵢ = frameVector I x₀ p (bB i)` the coordinate frame at
`p = (extChartAt I x₀).symm y`). -/
lemma chartMatFun_quadForm (g : Submission.Diff.SMet I M) (x₀ : M) (y : E)
    (v : Fin (Module.finrank ℝ E) → ℝ) :
    (∑ i, ∑ j, v i * v j * chartMatFun g x₀ y i j)
      = g.inner ((extChartAt I x₀).symm y)
          (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
            ((extChartAt I x₀).symm y) (bB (E := E) i))
          (∑ j, v j • Submission.Geodesic.frameVector (I := I) x₀
            ((extChartAt I x₀).symm y) (bB (E := E) j)) := by
  simp only [chartMatFun]
  have h1 : (g.inner ((extChartAt I x₀).symm y))
        (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
          ((extChartAt I x₀).symm y) (bB (E := E) i))
      = ∑ i, v i • ((g.inner ((extChartAt I x₀).symm y))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (bB (E := E) i))) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  have h2 : ∀ w, ((g.inner ((extChartAt I x₀).symm y)) w)
        (∑ j, v j • Submission.Geodesic.frameVector (I := I) x₀
          ((extChartAt I x₀).symm y) (bB (E := E) j))
      = ∑ j, v j * (((g.inner ((extChartAt I x₀).symm y)) w)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (bB (E := E) j))) := by
    intro w
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
  rw [h2, h1]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## The Ricci-flow equation in the chart -/

/-- **The time derivative of the chart matrix of a Ricci flow is minus twice the chart Ricci
matrix** (the Ricci flow equation `∂ₜ g = -2 Ric` read in the coordinate frame of the chart at
`x₀`). -/
lemma hasDerivAt_chartMat_of_isRicciFlow
    {G : ℝ → Submission.Diff.SMet I M} {τ : ℝ} (h : Submission.Diff.IsRicciFlow G τ)
    {t : ℝ} (ht : t ∈ Set.Ioo 0 τ) (x₀ : M) (y : E) :
    HasDerivAt (fun s : ℝ => chartMat G x₀ s y) ((-2 : ℝ) • chartRicMat (G t) x₀ y) t := by
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

/-! ## A smooth cutoff in the determinant, and global smoothness of the product -/

/-- The smooth step `0` for `x ≤ δ/2`, `1` for `x ≥ δ`. -/
noncomputable def jetCut (δ : ℝ) (x : ℝ) : ℝ := Real.smoothTransition (2 * x / δ - 1)

lemma contDiff_jetCut (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (jetCut δ) := by
  unfold jetCut
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma jetCut_eq_zero {δ x : ℝ} (hδ : 0 < δ) (hx : x ≤ δ / 2) : jetCut δ x = 0 := by
  rw [jetCut, Real.smoothTransition.zero_of_nonpos]
  have h : 2 * x / δ - 1 = (2 * x - δ) / δ := by field_simp
  rw [h]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hδ)

lemma jetCut_eq_one {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) : jetCut δ x = 1 := by
  rw [jetCut, Real.smoothTransition.one_of_one_le]
  have h : 2 * x / δ - 1 = (2 * x - δ) / δ := by field_simp
  rw [h, le_div_iff₀ hδ]
  linarith

/-- **Global smoothness of `z ↦ θ (det z) • Ψ z`.**  If `det` is smooth, `Ψ` is smooth on the open
set where `det ≠ 0`, and `θ` is a smooth function vanishing for `x ≤ c` with `c > 0`, then the
product is smooth everywhere (the cutoff `θ ∘ det` kills `Ψ` in an open neighbourhood of the
singular set). -/
theorem contDiff_smul_of_det_cutoff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ψ : X → MatE (E := E)} {det : X → ℝ} {θ : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθ0 : ∀ x, x ≤ c → θ x = 0)
    (hdet : ContDiff ℝ (⊤ : ℕ∞) det)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ {z | det z ≠ 0}) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => θ (det z) • Ψ z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : det z < c
  · have hopen : {z' | det z' < c} ∈ 𝓝 z :=
      (isOpen_lt hdet.continuous continuous_const).mem_nhds hz
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : MatE (E := E)))) ?_
    filter_upwards [hopen] with z' hz'
    rw [hθ0 (det z') (le_of_lt hz'), zero_smul]
  · push_neg at hz
    have hz0 : det z ≠ 0 := ne_of_gt (lt_of_lt_of_le hc hz)
    have hopen : {z' | det z' ≠ 0} ∈ 𝓝 z :=
      (isOpen_ne.preimage hdet.continuous).mem_nhds hz0
    exact (((hθ.contDiffAt).comp z hdet.contDiffAt).smul (hΨ.contDiffAt hopen))

/-! ## Uniform ellipticity of the chart matrix near the chart centre -/

/-- **The chart matrix of a smooth metric is uniformly positive definite near the chart centre.** -/
lemma exists_elliptic_nhds [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set E, IsOpen U ∧ (extChartAt I x₀) x₀ ∈ U ∧
      ∀ y ∈ U, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        δ * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * chartMatFun g x₀ y i j :=
  uniform_posDef_of_continuous_v2 (fun y : E => chartMatFun g x₀ y)
    (fun i j => AuxL.chartMatFun_continuousAt_centre g x₀ i j)
    (fun v hv => AuxL.chartMatFun_centre_posDef g x₀ v hv)

/-! ## The target -/

/-- **The chart matrix of a Ricci flow has uniformly bounded spatial jets of every order on the
slab, jointly in space and time.**  Under the a priori chart bounds `ChartBounds G (T/2) T` and the
two-sided metric lower bound `hnd` (`a • (G 0).inner ≤ (G t).inner` on `[T/2,T)`), every chart
centre `x₀` has a bounded open chart neighbourhood `U` of `(extChartAt I x₀) x₀` on which
`(t,y) ↦ chartMat G x₀ t y` is jointly `C^∞` on `(Ico (T/2) T) ×ˢ U` and all of whose iterated
Fréchet derivatives are uniformly bounded there. -/
theorem chartMat_jets_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hb : Work.Diff.EXT.ChartBounds (I := I) (M := M) G (T / 2) T)
    (hnd : ∃ a : ℝ, 0 < a ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ (x : M) (u : TangentSpace I x),
        a * (G 0).inner x u u ≤ (G t).inner x u u)
    (x₀ : M) :
    ∃ U : Set E, IsOpen U ∧ (extChartAt I x₀) x₀ ∈ U ∧ Bornology.IsBounded U ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E =>
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ p.1 p.2) ((Set.Ico (T / 2) T) ×ˢ U) ∧
      (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ (Set.Ico (T / 2) T) ×ˢ U,
        ‖iteratedFDeriv ℝ k (fun p : ℝ × E =>
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ p.1 p.2) p‖ ≤ C) := by
  classical
  obtain ⟨a, ha_pos, ha_le⟩ := hnd
  obtain ⟨Ucb, hUcb_open, hUcb_mem, hUcbb⟩ := hb x₀
  obtain ⟨δe, hδe_pos, V, hV_open, hV_mem, hV_ell⟩ := exists_elliptic_nhds (G 0) x₀
  obtain ⟨C₀, hC₀0, hC₀⟩ := hUcbb 0
  obtain ⟨δ, hδ_pos, hδdet⟩ :=
    AuxL.det_lower_bound_of_quadForm (n := Module.finrank ℝ E) (a * δe) C₀
      (mul_pos ha_pos hδe_pos) hC₀0
  obtain ⟨Ψ, hΨsm, hΨeq⟩ := chartRic_partial_jet (I := I) (M := M)
  set y₀ : E := (extChartAt I x₀) x₀ with hy₀
  set U : Set E := Ucb ∩ V ∩ Metric.ball y₀ 1 ∩ (extChartAt I x₀).target with hU
  -- the cutoff function
  set Φ : E × JetC (E := E) → MatE (E := E) :=
    fun z => jetCut δ ((Matrix.of z.2.1).det) • ((-2 : ℝ) • Ψ z) with hΦ
  -- the elliptic bound
  have hdetA : ContDiff ℝ (⊤ : ℕ∞) (fun A : MatE (E := E) => (Matrix.of A).det) := by
    simp only [Matrix.det_apply, Matrix.of_apply]
    fun_prop
  have hdet_sm : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : E × JetC (E := E) => (Matrix.of z.2.1).det) :=
    hdetA.comp (by fun_prop)
  have hΦ_sm : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : E × JetC (E := E) => (-2 : ℝ) • Ψ z)
        {z | (Matrix.of z.2.1).det ≠ 0} := hΨsm.const_smul (-2)
    exact contDiff_smul_of_det_cutoff (c := δ / 2) (half_pos hδ_pos)
      (contDiff_jetCut δ) (fun x hx => jetCut_eq_zero hδ_pos hx) hdet_sm h1
  -- the uniform quadratic-form bound on `V`
  have hell' : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ V, ∀ v : Fin (Module.finrank ℝ E) → ℝ,
      (a * δe) * ∑ i, (v i) ^ 2 ≤
        ∑ i, ∑ j, v i * v j * chartMat G x₀ t y i j := by
    intro t ht y hy v
    have h0 : δe * ∑ i, (v i) ^ 2 ≤ (G 0).inner ((extChartAt I x₀).symm y)
        (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (bB (E := E) i))
        (∑ j, v j • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
          (bB (E := E) j)) := by
      rw [← chartMatFun_quadForm (G 0) x₀ y v]
      exact hV_ell y hy v
    calc (a * δe) * ∑ i, (v i) ^ 2 = a * (δe * ∑ i, (v i) ^ 2) := by ring
      _ ≤ a * (G 0).inner ((extChartAt I x₀).symm y)
            (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (bB (E := E) i))
            (∑ j, v j • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (bB (E := E) j)) := mul_le_mul_of_nonneg_left h0 (le_of_lt ha_pos)
      _ ≤ (G t).inner ((extChartAt I x₀).symm y)
            (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (bB (E := E) i))
            (∑ j, v j • Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
              (bB (E := E) j)) :=
          ha_le t ht ((extChartAt I x₀).symm y)
            (∑ i, v i • Submission.Geodesic.frameVector (I := I) x₀
              ((extChartAt I x₀).symm y) (bB (E := E) i))
      _ = ∑ i, ∑ j, v i * v j * chartMat G x₀ t y i j :=
          (chartMatFun_quadForm (G t) x₀ y v).symm
  have hell : ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
      ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        ε * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, v i * v j * chartMat G x₀ t y i j :=
    ⟨a * δe, mul_pos ha_pos hδe_pos, fun t ht y hy v => hell' t ht y hy.1.1.2 v⟩
  -- the spatial jet bounds
  have hspat : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
      ‖iteratedFDeriv ℝ k (fun y' : E => chartMat G x₀ t y') y‖ ≤ C := by
    intro k
    obtain ⟨C, hC0, hC⟩ := hUcbb k
    exact ⟨C, hC0, fun t ht y hy => hC t ht y hy.1.1.1⟩
  -- the determinant bound on the jets
  have hdetbound : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ U,
      δ ≤ (Matrix.of (chartMat G x₀ t y)).det := by
    intro t ht y hy
    have hnorm : ‖chartMat G x₀ t y‖ ≤ C₀ := by
      simpa only [norm_iteratedFDeriv_zero] using hC₀ t ht y hy.1.1.1
    refine hδdet (chartMat G x₀ t y) (fun i j => chartMatFun_symm (G t) x₀ y i j)
      (fun v => hell' t ht y hy.1.1.2 v) (fun i j => ?_)
    have h1 : ‖chartMat G x₀ t y i‖ ≤ ‖chartMat G x₀ t y‖ := norm_le_pi_norm _ i
    have h2 : ‖chartMat G x₀ t y i j‖ ≤ ‖chartMat G x₀ t y i‖ := norm_le_pi_norm _ j
    rw [← Real.norm_eq_abs]
    linarith
  -- the pde
  have hpde : ∀ p ∈ (Set.Ico (T / 2) T) ×ˢ U,
      deriv (fun s : ℝ => chartMat G x₀ s p.2) p.1 =
        Φ (p.2, sJetData (fun p : ℝ × E => chartMat G x₀ p.1 p.2) p) := by
    rintro ⟨t, y⟩ hp
    have ht : t ∈ Set.Ioo 0 T := ⟨by linarith [hT, hp.1.1], hp.1.2⟩
    have hy : y ∈ (extChartAt I x₀).target := hp.2.2
    have hder := (hasDerivAt_chartMat_of_isRicciFlow (I := I) (M := M) hflow ht x₀ y).deriv
    have hcut1 : jetCut δ ((Matrix.of ((sJetData (fun p : ℝ × E => chartMat G x₀ p.1 p.2)
        (t, y)).1)).det) = 1 := by
      show jetCut δ ((Matrix.of (chartMat G x₀ t y)).det) = 1
      exact jetCut_eq_one hδ_pos (hdetbound t hp.1 y hp.2)
    rw [hder, hΦ]
    show (-2 : ℝ) • chartRicMat (G t) x₀ y
        = jetCut δ ((Matrix.of ((sJetData (fun p : ℝ × E => chartMat G x₀ p.1 p.2)
            (t, y)).1)).det)
          • ((-2 : ℝ) • Ψ (y, sJetData (fun p : ℝ × E => chartMat G x₀ p.1 p.2) (t, y)))
    rw [hcut1, one_smul, hΨeq x₀ (G t) y hy]
    simp only [sJetData, dPart, chartMat]
  -- the smoothness on the slab
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => chartMat G x₀ p.1 p.2)
      ((Set.Ico (T / 2) T) ×ˢ U) := by
    intro p hp
    have ht0 : p.1 ∈ Set.Ico 0 T := ⟨by linarith [hp.1.1, hT], hp.1.2⟩
    have hy : p.2 ∈ (extChartAt I x₀).target := hp.2.2
    exact (contDiffWithinAt_chartMat_of_jointSmooth_gen (I := I) (M := M) hflow.1 ht0 x₀
      hy).mono (Set.prod_mono (fun s hs => ⟨by linarith [hs.1, hT], hs.2⟩) (fun y hy => hy.2))
  -- the properties of `U`
  have hU_open' : IsOpen U := by
    rw [hU]
    exact ((hUcb_open.inter hV_open).inter Metric.isOpen_ball).inter
      (isOpen_extChartAt_target (I := I) x₀)
  have hU_mem' : (extChartAt I x₀) x₀ ∈ U := by
    rw [hU, hy₀]
    exact ⟨⟨⟨hUcb_mem, hV_mem⟩, Metric.mem_ball_self zero_lt_one⟩,
      PartialEquiv.map_source (extChartAt I x₀) (mem_extChartAt_source (I := I) x₀)⟩
  have hU_bdd : Bornology.IsBounded U := by
    rw [hU]
    exact (Metric.isBounded_ball (x := y₀) (r := 1)).subset (fun y hy => hy.1.2)
  -- apply the parabolic bootstrap
  have hjets := Jets2.jets_bounded_of_pde (E := E) (σ := T / 2) (T := T)
    (by linarith) hU_open' hU_bdd hu hspat hell hΦ_sm hpde
  exact ⟨U, hU_open', hU_mem', hU_bdd, hu, hjets⟩

end Work.Diff.EXT
