import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.germF0_base
import Submission.Work.Horn.germ_expansion_free
import Submission.Work.Horn.critPoint_of_component_of_ne_critval
import Submission.Work.Horn.flower_q_component_nz
import Submission.Work.Horn.flower_q_simplyConnected
import Submission.Work.Horn.hopen_Dg
import Submission.Work.Horn.Dg_pieces
import Submission.Work.Horn.zero_not_mem_basin_pushdown
import Submission.Work.Horn.chain_onto_of_proper
import Submission.Work.Horn.abel_extension_to_spread
import Submission.Work.Horn.spreadChain_bijOn_structure
import Submission.Work.Horn.FatouQ.chartdict
import Submission.Work.Horn.FatouQ.chart_facts
import Submission.Work.Horn.FatouQ.Acorr_defect
import Submission.Work.Horn.FatouQ.Efun_bound
import Submission.Work.Horn.FatouQ.zBranch_contDiff
import Submission.Work.Horn.FatouQ.nearTranslation_abel

namespace Work.Horn

open Set Filter Topology
open scoped Topology

noncomputable section

/-!
# Conjunct 1 of `Work.Horn.horn_germ_F0` (Shishikura, Lemma 5.4, first half)

`deriv (deriv (pushdown d.E)) 0 ≠ 0`: the pushed-down horn map of an `𝓕₀` germ has non-vanishing
second derivative at `0`, i.e. its Leau–Fatou exponent is `q = 1`.

Suppose `g''(0) = 0`.  Then the Leau–Fatou exponent of the germ `g = pushdown d.E` is `q ≥ 2`, so
the flower has `q ≥ 2` petals; their spreads `B i = ⋃ₙ W n i` are pairwise disjoint `g`-invariant
subsets of the parabolic basin.  The only critical value of `g` on `D_g` is `v = π (Φ₀ c)`
(`Work.Horn.pushdown_critval_global_eq`), so it lies in at most one spread, and some spread misses
it.  On that spread `Work.Horn.spreadChain_bijOn_structure` makes every level map a biholomorphism,
the spread simply connected and `g` proper on it, while the petal Fatou coordinate extends to a
global Abel coordinate (`Work.Horn.abel_extension_to_spread`);
`Work.Horn.critPoint_of_component_of_ne_critval` then produces a critical point of `g` inside the
spread, whose value must be `v` — contradiction.
-/

/-- **The petals of the Leau–Fatou flower of `g = pushdown d.E` at level `M`, together with their
Fatou coordinate.**  `Work.Horn.FatouQ` provides the coordinate on the concrete petal
`Flower.petal q a M j`; this is the interface used by `Work.Horn.pushdown_second_deriv_ne_zero`. -/
theorem flower_petal_fatouCoord {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {a : ℂ} {ρ M : ℝ}
    (hS : Flower.Setup f D q a) (hb : Flower.Bounds f D q a ρ)
    (hM : 0 < M) (hRM : ‖Flower.cc q a‖ / M < ρ ^ q)
    (hgeo : Flower.PetalFacts q a M) (hMeps : ‖Flower.cc q a‖ / M ≤ (1 / 4 : ℝ) ^ q)
    (j : Fin q) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ (Flower.petal q a M j) ∧
      (∀ z ∈ Flower.petal q a M j, Φ (f z) = Φ z + 1) ∧
      Set.InjOn Φ (Flower.petal q a M j) ∧
      (∀ b : ℝ, ∃ C : ℝ, ∀ w : ℂ, C < w.re → |w.im| ≤ b →
        ∃ z ∈ Flower.petal q a M j, Φ z = w) := by
  classical
  have hq : 1 ≤ q := hb.hq
  have ha : a ≠ 0 := hb.ha
  have hρ : 0 < ρ := hb.hρ
  have hfix : f 0 = 0 := hb.hfix
  have hcc : Flower.cc q a ≠ 0 := hgeo.cc_ne_zero
  have hccpos : 0 < ‖Flower.cc q a‖ := norm_pos_iff.mpr hcc
  have hd : Work.Horn.FatouQ.PetalDatum f D q a ρ M := ⟨hS, hρ, hb, hM, hRM, hgeo⟩
  -- the z-plane defect of the approximate coordinate
  obtain ⟨Cdef, hCdefnn, hdef⟩ := Work.Horn.FatouQ.Acorr_defect hd hMeps j
  -- the chart dictionary
  obtain ⟨hzb_petal, hzb_chart, _hzb_ne, hzb_idd, hg_diff, hg_mem, hg_step, hg_inj,
    hX_diff, hX_growth, hX_deriv⟩ := Work.Horn.FatouQ.chart_facts hd j
  obtain ⟨C0, C1, θ, hC0, hC1, hθ, hXcl⟩ := hX_growth
  obtain ⟨Nd, _hMNd, hXd⟩ := hX_deriv
  -- the defect in the chart
  obtain ⟨B, hBnn, hEbnd⟩ := Work.Horn.FatouQ.Efun_bound hd j hCdefnn hzb_petal hzb_chart
    hzb_idd hdef
  set N : ℝ := max M Nd with hNdef
  have hMN : M ≤ N := le_max_left _ _
  have hNdN : Nd ≤ N := le_max_right _ _
  have hNpos : 0 < N := lt_of_lt_of_le hM hMN
  have hδ : 1 < 1 + 1 / (q : ℝ) := by
    have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr (by omega)
    have : 0 < 1 / (q : ℝ) := div_pos one_pos hqpos
    linarith
  have hgdiff_on : DifferentiableOn ℂ (Work.Horn.FatouQ.gfun f q a j) {w : ℂ | N < w.re} :=
    fun w hw => (hg_diff w (lt_of_le_of_lt hMN hw)).differentiableWithinAt
  have hgstep_on : ∀ w : ℂ, N < w.re → w.re + 1 / 2 ≤ (Work.Horn.FatouQ.gfun f q a j w).re :=
    fun w hw => hg_step w (lt_of_le_of_lt hMN hw)
  have hginj_on : Set.InjOn (Work.Horn.FatouQ.gfun f q a j) {w : ℂ | N < w.re} :=
    hg_inj.mono (fun w hw => lt_of_le_of_lt hMN hw)
  have hXdiff_on : DifferentiableOn ℂ (Work.Horn.FatouQ.Xfun f q a j) {w : ℂ | N < w.re} :=
    fun w hw => (hX_diff w (lt_of_le_of_lt hMN hw)).differentiableWithinAt
  have hXderiv_on : ∀ w : ℂ, N < w.re →
      ‖deriv (Work.Horn.FatouQ.Xfun f q a j) w - 1‖ ≤ 1 / 4 :=
    fun w hw => hXd w (lt_of_le_of_lt hNdN hw)
  have hXclose_on : ∀ w : ℂ, N < w.re →
      ‖Work.Horn.FatouQ.Xfun f q a j w - w‖ ≤ C0 * ‖w‖ ^ θ + C1 :=
    fun w hw => hXcl w (lt_of_le_of_lt hMN hw)
  have hEdiff_on : DifferentiableOn ℂ (Work.Horn.FatouQ.Efun f q a j) {w : ℂ | N < w.re} := by
    intro w hw
    have hwm : M < w.re := lt_of_le_of_lt hMN hw
    have hgm : M < (Work.Horn.FatouQ.gfun f q a j w).re := hg_mem w hwm
    have h1 : DifferentiableAt ℂ (Work.Horn.FatouQ.Xfun f q a j)
        (Work.Horn.FatouQ.gfun f q a j w) := hX_diff (Work.Horn.FatouQ.gfun f q a j w) hgm
    have h2 : DifferentiableAt ℂ (Work.Horn.FatouQ.gfun f q a j) w := hg_diff w hwm
    have h3 : DifferentiableAt ℂ (Work.Horn.FatouQ.Xfun f q a j) w := hX_diff w hwm
    have h4 : DifferentiableAt ℂ (Work.Horn.FatouQ.Efun f q a j) w := by
      show DifferentiableAt ℂ
        (fun w => Work.Horn.FatouQ.Xfun f q a j (Work.Horn.FatouQ.gfun f q a j w)
          - Work.Horn.FatouQ.Xfun f q a j w - 1) w
      exact ((h1.comp w h2).sub h3).sub_const 1
    exact h4.differentiableWithinAt
  have hEabel_on : ∀ w : ℂ, N < w.re →
      Work.Horn.FatouQ.Efun f q a j w =
        Work.Horn.FatouQ.Xfun f q a j (Work.Horn.FatouQ.gfun f q a j w)
          - Work.Horn.FatouQ.Xfun f q a j w - 1 := fun w _ => rfl
  have hEbound_on : ∀ w : ℂ, N < w.re →
      ‖Work.Horn.FatouQ.Efun f q a j w‖ ≤ B / w.re ^ (1 + 1 / (q : ℝ)) :=
    fun w hw => hEbnd w (lt_of_le_of_lt hMN hw)
  -- the Fatou coordinate in the chart
  obtain ⟨N', φ, hNle, hφdiff, hφabel, hφinj, hφimg⟩ :=
    Work.Horn.FatouQ.nearTranslation_abel (N := N) (B := B) (C0 := C0) (C1 := C1) (θ := θ)
      (δ := 1 + 1 / (q : ℝ)) (g := Work.Horn.FatouQ.gfun f q a j)
      (X := Work.Horn.FatouQ.Xfun f q a j) (E := Work.Horn.FatouQ.Efun f q a j)
      hNpos hδ hBnn hθ hC0 hC1 hgdiff_on hgstep_on hginj_on hXdiff_on hXderiv_on
      hXclose_on hEdiff_on hEabel_on hEbound_on
  have hMN' : M ≤ N' := le_trans hMN hNle
  -- the truncated petal and its coordinate
  set V0 : Set ℂ := {z : ℂ | z ∈ Flower.petal q a M j ∧ N' < (Flower.chartQ q a z).re}
    with hV0def
  set Φ0 : ℂ → ℂ := fun z => φ (Flower.chartQ q a z) with hΦ0def
  have hN'pos : 0 < N' := lt_of_lt_of_le hNpos hNle
  have hconv : Convex ℝ {w : ℂ | N' < w.re} := by
    have h : Convex ℝ (Complex.reLm ⁻¹' (Set.Ioi N')) :=
      (convex_Ioi N').linear_preimage Complex.reLm
    convert h using 1
    ext z
    simp [Complex.reLm, Set.mem_Ioi]
  have hV0eq : V0 = Work.Horn.FatouQ.zBranch q a j '' {w : ℂ | N' < w.re} := by
    rw [hV0def]
    ext z
    constructor
    · rintro ⟨hzp, hzN⟩
      exact ⟨Flower.chartQ q a z, hzN, Work.Horn.FatouQ.zBranch_chartQ hgeo j hzp⟩
    · rintro ⟨w, hw, rfl⟩
      have hwM : M < w.re := lt_of_le_of_lt hMN' hw
      exact ⟨hzb_petal w hwM, by rw [hzb_chart w hwM]; exact hw⟩
  have hzb_cont : ∀ w : ℂ, N' < w.re →
      ContinuousAt (Work.Horn.FatouQ.zBranch q a j) w := fun w hw =>
    (Work.Horn.FatouQ.zBranch_contDiff hq ha j w (lt_trans hN'pos hw)).2
  have hV0nonempty : V0.Nonempty := by
    refine ⟨Work.Horn.FatouQ.zBranch q a j ((N' + 1 : ℝ) : ℂ), ?_⟩
    rw [hV0eq]
    exact ⟨((N' + 1 : ℝ) : ℂ), by simp, rfl⟩
  have hV0conn : IsConnected V0 := by
    refine ⟨hV0nonempty, ?_⟩
    rw [hV0eq]
    exact hconv.isPreconnected.image (Work.Horn.FatouQ.zBranch q a j)
      (fun w hw => (hzb_cont w hw).continuousWithinAt)
  have hV0open : IsOpen V0 := by
    rw [hV0def]
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨hzp, hzN⟩ := hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ((hgeo.mem_petal_iff j z).mp hzp).1)
    have hcontQ : ContinuousAt (Flower.chartQ q a) z := by
      have h1 : ContinuousAt (fun z : ℂ => z ^ q) z := continuousAt_id.pow q
      have h2 : ContinuousAt (fun z : ℂ => Flower.cc q a / z ^ q) z :=
        continuousAt_const.div h1 (pow_ne_zero q hz0)
      change ContinuousAt (fun z : ℂ => Flower.cc q a / z ^ q) z
      exact h2
    have hcont : ContinuousAt (fun z : ℂ => (Flower.chartQ q a z).re) z :=
      Complex.continuous_re.continuousAt.comp hcontQ
    have hmem : Flower.petal q a M j ∩ {z : ℂ | N' < (Flower.chartQ q a z).re} ∈ nhds z :=
      Filter.inter_mem ((hgeo.isOpen_petal j).mem_nhds hzp)
        (hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hzN))
    exact hmem
  -- the petal lies in the disc of the quantitative bounds
  have hpetal_ball : ∀ z ∈ Flower.petal q a M j, ‖z‖ < ρ := by
    intro z hz
    have h1 : ‖z‖ ^ q < ‖Flower.cc q a‖ / M := hgeo.petal_norm_pow_lt j z hz
    exact lt_of_pow_lt_pow_left₀ q hρ.le (lt_trans h1 hRM)
  have hpetal_D : ∀ z ∈ Flower.petal q a M j, z ∈ D := fun z hz =>
    hb.hsub (by simpa [Metric.mem_ball, dist_zero_right] using hpetal_ball z hz)
  have hlogpow : ∀ u : ℂ, u ≠ 0 → |u.arg| * (q : ℝ) < Real.pi →
      Complex.log (u ^ q) = (q : ℂ) * Complex.log u :=
    fun u hu hu' => log_pow_eq hq hu hu'
  have hmaps_petal := petal_mapsTo hb hM hRM hgeo hlogpow
  have hinj_ball' : Set.InjOn f (Metric.ball (0 : ℂ) ρ) := injOn_ball hb
  -- forward invariance of the petal (the image avoids `0`)
  have hfz_ne : ∀ z ∈ Flower.petal q a M j, f z ≠ 0 := by
    intro z hz hzero
    have hballz : z ∈ Metric.ball (0 : ℂ) ρ := by
      simpa [Metric.mem_ball, dist_zero_right] using hpetal_ball z hz
    have hball0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by
      simpa [Metric.mem_ball, dist_zero_right] using hρ
    have heq : z = 0 := hinj_ball' hballz hball0 (by rw [hzero, hfix])
    exact hgeo.not_mem_petal_zero j (heq ▸ hz)
  have hmapV : Set.MapsTo f (Flower.petal q a M j) (Flower.petal q a M j) := by
    intro z hz
    rcases hmaps_petal j hz with h | h
    · exact h
    · exact absurd h (hfz_ne z hz)
  -- forward invariance of the truncated petal
  have hmapV0 : Set.MapsTo f V0 V0 := by
    intro z hz
    obtain ⟨hzp, hzN⟩ := hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ((hgeo.mem_petal_iff j z).mp hzp).1)
    refine ⟨hmapV hzp, ?_⟩
    have hchart := hb.hchart z (norm_pos_iff.mpr hz0) (hpetal_ball z hzp)
    have habs : |(Flower.chartQ q a (f z) - Flower.chartQ q a z - 1).re| ≤ 1 / 4 :=
      le_trans (Complex.abs_re_le_norm _) hchart
    have h3 := (abs_le.mp habs).1
    simp only [Complex.sub_re, Complex.one_re] at h3
    linarith
  -- the orbit of a petal point enters `V0`
  have henter0 : ∀ z ∈ Flower.petal q a M j,
      ∃ n : ℕ, (∀ k ≤ n, f^[k] z ∈ Flower.petal q a M j) ∧ f^[n] z ∈ V0 := by
    intro z hz
    have hstay : ∀ n : ℕ, f^[n] z ∈ Flower.petal q a M j := by
      intro n
      induction n with
      | zero => simpa using hz
      | succ n ih => simpa [Function.iterate_succ_apply'] using hmapV ih
    have hstep : ∀ n : ℕ, (Flower.chartQ q a (f^[n] z)).re + 3 / 4 ≤
        (Flower.chartQ q a (f^[n + 1] z)).re := by
      intro n
      have hzn : f^[n] z ≠ 0 := fun h => hgeo.not_mem_petal_zero j (h ▸ hstay n)
      have hchart := hb.hchart (f^[n] z) (norm_pos_iff.mpr hzn) (hpetal_ball _ (hstay n))
      have habs : |(Flower.chartQ q a (f (f^[n] z)) - Flower.chartQ q a (f^[n] z) - 1).re| ≤ 1 / 4 :=
        le_trans (Complex.abs_re_le_norm _) hchart
      have h3 := (abs_le.mp habs).1
      rw [show f^[n + 1] z = f (f^[n] z) from Function.iterate_succ_apply' f n z]
      simp only [Complex.sub_re, Complex.one_re] at h3
      linarith
    have hgrow : ∀ n : ℕ, (Flower.chartQ q a z).re + 3 * (n : ℝ) / 4 ≤
        (Flower.chartQ q a (f^[n] z)).re := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have h := hstep n
        have hs : f^[n + 1] z = f (f^[n] z) := Function.iterate_succ_apply' f n z
        rw [hs] at h ⊢
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        have hsplit : 3 * ((n : ℝ) + 1) / 4 = 3 * (n : ℝ) / 4 + 3 / 4 := by ring
        rw [hsplit]
        linarith
    obtain ⟨n, hn⟩ : ∃ n : ℕ, N' - (Flower.chartQ q a z).re < 3 * (n : ℝ) / 4 := by
      obtain ⟨n, hn⟩ := exists_nat_gt (4 * (N' - (Flower.chartQ q a z).re) / 3)
      exact ⟨n, by linarith⟩
    refine ⟨n, fun k _ => hstay k, hstay n, ?_⟩
    linarith [hn, hgrow n]
  -- the coordinate on the truncated petal
  have hchartQ_diffOn : ∀ z ∈ Flower.petal q a M j, DifferentiableAt ℂ (Flower.chartQ q a) z := by
    intro z hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ((hgeo.mem_petal_iff j z).mp hz).1)
    have h2 : DifferentiableAt ℂ (fun z : ℂ => Flower.cc q a / z ^ q) z :=
      (differentiableAt_const _).div (differentiableAt_id.pow q) (pow_ne_zero q hz0)
    change DifferentiableAt ℂ (fun z : ℂ => Flower.cc q a / z ^ q) z
    exact h2
  have hV0diff : DifferentiableOn ℂ Φ0 V0 := by
    intro z hz
    have h2 : DifferentiableAt ℂ φ (Flower.chartQ q a z) :=
      (hφdiff (Flower.chartQ q a z) hz.2).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz.2)
    exact (h2.comp z (hchartQ_diffOn z hz.1)).differentiableWithinAt
  have hV0abel : ∀ z ∈ V0, Φ0 (f z) = Φ0 z + 1 := by
    intro z hz
    have hkey : Flower.chartQ q a (f z) =
        Work.Horn.FatouQ.gfun f q a j (Flower.chartQ q a z) := by
      rw [Work.Horn.FatouQ.gfun, Work.Horn.FatouQ.zBranch_chartQ hgeo j hz.1]
    have h1 : Φ0 (f z) = φ (Work.Horn.FatouQ.gfun f q a j (Flower.chartQ q a z)) := by
      rw [hΦ0def]; exact congrArg φ hkey
    have h2 : Φ0 z = φ (Flower.chartQ q a z) := rfl
    rw [h1, h2, hφabel (Flower.chartQ q a z) hz.2]
  have hV0inj : Set.InjOn Φ0 V0 := by
    intro z hz z' hz' h
    have h1 : Flower.chartQ q a z = Flower.chartQ q a z' := hφinj hz.2 hz'.2 h
    exact Work.Horn.FatouQ.chartQ_injOn_petal hgeo j hz.1 hz'.1 h1
  have hV0img : ∀ b : ℝ, ∃ C : ℝ, ∀ w : ℂ, C < w.re → |w.im| ≤ b →
      ∃ z ∈ V0, Φ0 z = w := by
    intro b
    obtain ⟨C, hC⟩ := hφimg b
    refine ⟨C, fun w hw hwim => ?_⟩
    obtain ⟨w', hw'N, hw'⟩ := hC w hw hwim
    have hw'M : M < w'.re := lt_of_le_of_lt hMN' hw'N
    refine ⟨Work.Horn.FatouQ.zBranch q a j w', ⟨hzb_petal w' hw'M,
      by rw [hzb_chart w' hw'M]; exact hw'N⟩, ?_⟩
    change φ (Flower.chartQ q a (Work.Horn.FatouQ.zBranch q a j w')) = w
    rw [hzb_chart w' hw'M]
    exact hw'
  -- extend to the whole petal
  obtain ⟨Φ, hΦdiff, hΦabel, hΦeq⟩ :=
    abel_extension_to_spread (hgeo.isOpen_petal j) (hS.hf.mono hpetal_D) hV0open
      (fun z hz => hz.1) hmapV0 hV0diff hV0abel henter0
  refine ⟨Φ, hΦdiff, hΦabel, ?_, ?_⟩
  · -- injectivity on the whole petal
    intro z hz z' hz' hzz'
    have hstay : ∀ w ∈ Flower.petal q a M j, ∀ n : ℕ, f^[n] w ∈ Flower.petal q a M j := by
      intro w hw n
      induction n with
      | zero => simpa using hw
      | succ n ih => simpa [Function.iterate_succ_apply'] using hmapV ih
    obtain ⟨n, hn⟩ := henter0 z hz
    obtain ⟨m, hm⟩ := henter0 z' hz'
    set L : ℕ := max n m with hLdef
    have hLn : n ≤ L := le_max_left _ _
    have hLm : m ≤ L := le_max_right _ _
    have h1 : f^[n] z ∈ V0 := hn.2
    have h2 : f^[L] z ∈ V0 := by
      have hsub : ∀ k : ℕ, f^[k] (f^[n] z) ∈ V0 := fun k => hmapV0.iterate k h1
      have : f^[L] z = f^[L - n] (f^[n] z) := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hLn]
      rw [this]; exact hsub (L - n)
    have h3 : f^[m] z' ∈ V0 := hm.2
    have h4 : f^[L] z' ∈ V0 := by
      have hsub : ∀ k : ℕ, f^[k] (f^[m] z') ∈ V0 := fun k => hmapV0.iterate k h3
      have : f^[L] z' = f^[L - m] (f^[m] z') := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hLm]
      rw [this]; exact hsub (L - m)
    -- the Abel equation along the orbit
    have habel_iter : ∀ (w : ℂ) (hw : w ∈ Flower.petal q a M j) (k : ℕ),
        Φ (f^[k] w) = Φ w + k := by
      intro w hw k
      induction k with
      | zero => simp
      | succ k ih =>
        have hstayk := hstay w hw k
        rw [Function.iterate_succ_apply']
        rw [hΦabel (f^[k] w) hstayk, ih]
        push_cast; ring
    have e1 : Φ (f^[L] z) = Φ z + L := habel_iter z hz L
    have e2 : Φ (f^[L] z') = Φ z' + L := habel_iter z' hz' L
    have hEq1 : Φ (f^[L] z) = Φ0 (f^[L] z) := hΦeq h2
    have hEq2 : Φ (f^[L] z') = Φ0 (f^[L] z') := hΦeq h4
    have hww : Φ0 (f^[L] z) = Φ0 (f^[L] z') := by
      rw [← hEq1, ← hEq2, e1, e2, hzz']
    have hchartEq : Flower.chartQ q a (f^[L] z) = Flower.chartQ q a (f^[L] z') :=
      hφinj h2.2 h4.2 hww
    have heq : f^[L] z = f^[L] z' :=
      Work.Horn.FatouQ.chartQ_injOn_petal hgeo j h2.1 h4.1 hchartEq
    -- `f^[L]` is injective on the petal
    have hinj_iter : Set.InjOn (f^[L]) (Flower.petal q a M j) := by
      have key : ∀ k : ℕ, Set.InjOn (f^[k]) (Flower.petal q a M j) := by
        intro k
        induction k with
        | zero => exact fun a _ b _ h => h
        | succ k ih =>
          intro a ha b hb hab
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at hab
          have ha' := hstay a ha k
          have hb' := hstay b hb k
          refine ih ha hb (hinj_ball' ?_ ?_ hab)
          · simpa [Metric.mem_ball, dist_zero_right] using hpetal_ball _ ha'
          · simpa [Metric.mem_ball, dist_zero_right] using hpetal_ball _ hb'
      exact key L
    exact hinj_iter hz hz' heq
  · -- the image contains the tails of all horizontal strips
    intro b
    obtain ⟨C, hC⟩ := hV0img b
    refine ⟨C, fun w hw hwim => ?_⟩
    obtain ⟨z, hz, hzw⟩ := hC w hw hwim
    exact ⟨z, hz.1, by rw [hΦeq hz, hzw]⟩

theorem pushdown_second_deriv_ne_zero {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hBne : B.Nonempty) {η : ℝ} {Bu Bl : Set ℂ}
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl) :
    deriv (deriv (MandelDim.pushdown d.E)) 0 ≠ 0 := by
  classical
  obtain ⟨c, hsetup⟩ := isF0Setup_of_immediateBasin hF0 d hB hBne
  obtain ⟨hBuO, hBlO, _, _, hup₀, hlo₀, _⟩ := horn_topo_facts hF0 d hB hBne hBu hBl hup hlo
  set g : ℂ → ℂ := MandelDim.pushdown d.E with hgdef
  set Dg : Set ℂ := insert 0 (MandelDim.piExp '' (Bu ∪ Bl)) with hDgdef
  have hDg : IsOpen Dg := isOpen_insert_piExp hBuO hBlO hup hlo
  have hg : DifferentiableOn ℂ g Dg := pushdown_g_holo hF0 d hB hBne hBu hBl hsub hup hlo
  have h0 : (0 : ℂ) ∈ Dg := Set.mem_insert _ _
  have hfix : g 0 = 0 := MandelDim.pushdown_zero d.E
  have hd1 : deriv g 0 = 1 := Work.Horn.MandelDim.deriv_pushdown_E d
  have h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin g Dg :=
    zero_not_mem_basin_pushdown hF0 d hB hBne hBu hBl hsub hup hlo
  have hopen : ∀ z ∈ Dg, ∀ U ∈ nhds z, g '' U ∈ nhds (g z) := by
    have hset : Dg = insert 0 (MandelDim.piExp ''
        (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) := by
      rw [hDgdef, Bu_eq_BuOf d hBu hup hup₀, Bl_eq_BlOf d hBl hlo hlo₀]
    rw [hset]
    exact hopen_Dg hF0 d hB hBne
  intro h2
  -- #### the germ expansion, with exponent `q ≥ 2`
  obtain ⟨ρb, hρb, hball⟩ := Metric.mem_nhds_iff.mp (hDg.mem_nhds h0)
  obtain ⟨q, hq2, a, ha, hgerm⟩ :=
    germ_expansion_free hρb (hg.mono hball) hfix hd1 h2 (pushdown_not_eventually_id d hsetup)
  have hq1 : 1 ≤ q := by omega
  -- #### the flower: the petals are the concrete sets `Flower.petal q a M j`
  obtain ⟨ρ, hρ, hb⟩ := bounds_exists_of_open hDg h0 hg hq1 ha hfix hgerm
  have hcc : Flower.cc q a ≠ 0 := by
    rw [Flower.cc]
    exact div_ne_zero (by norm_num) (mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) ha)
  have hccpos : 0 < ‖Flower.cc q a‖ := norm_pos_iff.mpr hcc
  have hρq : 0 < ρ ^ q := pow_pos hρ q
  set M : ℝ := max ((4 : ℝ) ^ q * ‖Flower.cc q a‖ + 1) (‖Flower.cc q a‖ / ρ ^ q + 1) with hMdef
  have hMge1 : ‖Flower.cc q a‖ / ρ ^ q + 1 ≤ M := le_max_right _ _
  have hMge2 : (4 : ℝ) ^ q * ‖Flower.cc q a‖ + 1 ≤ M := le_max_left _ _
  have hMpos : 0 < M := by
    refine lt_of_lt_of_le ?_ hMge2
    have : (0 : ℝ) ≤ (4 : ℝ) ^ q * ‖Flower.cc q a‖ := by positivity
    linarith
  have hRM : ‖Flower.cc q a‖ / M < ρ ^ q := by
    have h1 : ‖Flower.cc q a‖ / ρ ^ q < M := by linarith
    have h2 : ‖Flower.cc q a‖ / M < ‖Flower.cc q a‖ / (‖Flower.cc q a‖ / ρ ^ q) :=
      div_lt_div_of_pos_left hccpos (div_pos hccpos hρq) h1
    have h3 : ‖Flower.cc q a‖ / (‖Flower.cc q a‖ / ρ ^ q) = ρ ^ q := by field_simp
    rwa [h3] at h2
  have hMeps : ‖Flower.cc q a‖ / M ≤ (1 / 4 : ℝ) ^ q := by
    have h1 : (4 : ℝ) ^ q * ‖Flower.cc q a‖ < M := by linarith
    have h2 : ‖Flower.cc q a‖ / M < ‖Flower.cc q a‖ / ((4 : ℝ) ^ q * ‖Flower.cc q a‖) :=
      div_lt_div_of_pos_left hccpos (by positivity) h1
    have h3 : ‖Flower.cc q a‖ / ((4 : ℝ) ^ q * ‖Flower.cc q a‖) = (1 / 4 : ℝ) ^ q := by
      rw [div_pow, one_pow, one_div]
      field_simp
    linarith [h3 ▸ h2.le]
  have hgeo : Flower.PetalFacts q a M := petal_facts hq1 ha hMpos
  have hlogpow : ∀ u : ℂ, u ≠ 0 → |u.arg| * (q : ℝ) < Real.pi →
      Complex.log (u ^ q) = (q : ℂ) * Complex.log u :=
    fun u hu hu' => log_pow_eq hq1 hu hu'
  have hmaps : ∀ j : Fin q, Set.MapsTo g (Flower.petal q a M j)
      (Flower.petal q a M j ∪ {0}) := petal_mapsTo hb hMpos hRM hgeo hlogpow
  have hbasin : Flower.BasinFacts g Dg :=
    basin_facts_of_open hDg h0 hg hopen hq1 hfix hgerm
  have hballM : ∀ j : Fin q, Flower.petal q a M j ⊆ Metric.ball (0 : ℂ) ρ := by
    intro j z hz
    have h1 : ‖z‖ ^ q < ‖Flower.cc q a‖ / M := hgeo.petal_norm_pow_lt j z hz
    have h2 : ‖z‖ ^ q < ρ ^ q := lt_trans h1 hRM
    have h3 : ‖z‖ < ρ := by
      by_contra hcon
      push Not at hcon
      exact absurd h2 (not_lt.mpr (pow_le_pow_left₀ hρ.le hcon q))
    simpa [Metric.mem_ball, dist_zero_right] using h3
  have hinjV : ∀ j : Fin q, Set.InjOn g (Flower.petal q a M j) :=
    fun j => (injOn_ball hb).mono (hballM j)
  have hcap : ∀ z ∈ MandelDim.ParabolicBasin g Dg,
      ∃ n : ℕ, g^[n] z ∈ ⋃ j, Flower.petal q a M j := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_iterate_mem_bigPetal hb hMpos (hbasin.orbit_ne_zero z hz)
      (hbasin.tendsto_zero z hz)
    refine ⟨n, ?_⟩
    rw [hgeo.iUnion_petal_eq_bigPetal]
    exact hn
  have hsubV : ∀ j : Fin q, Flower.petal q a M j ⊆ MandelDim.ParabolicBasin g Dg :=
    petal_subset_basin hb hMpos hRM hgeo hmaps
  have hloc := petal_index_locally_const hDg hg hb hMpos hgeo hmaps hcap
  have hVsc : ∀ j : Fin q, SimplyConnectedSpace (Flower.petal q a M j) :=
    flower_petal_simplyConnected hMpos hgeo
  have hVsubDg : ∀ j : Fin q, Flower.petal q a M j ⊆ Dg := fun j z hz => hb.hsub (hballM j hz)
  have hreach : ∀ z ∈ Dg,
      (∃ n : ℕ, (∀ k < n, g^[k] z ∈ Dg) ∧ g^[n] z ∈ ⋃ j, Flower.petal q a M j) →
      z ∈ MandelDim.ParabolicBasin g Dg := by
    intro z hzD hn
    obtain ⟨n, hstay, hmem⟩ := hn
    have hmem' : g^[n] z ∈ MandelDim.ParabolicBasin g Dg := by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
      exact hsubV i hi
    exact hbasin.mem_of_iterate z hzD n hstay hmem'
  -- #### the bounded upper piece of `D_g`
  obtain ⟨hUopen, hUbdd, hUconn, hUVeq, hUVdisj, hcross⟩ := Dg_pieces hF0 d hB hBne
  have hBueq : Bu = MandelDim.BuOf d B := Bu_eq_BuOf d hBu hup hup₀
  have hBleq : Bl = MandelDim.BlOf d B := Bl_eq_BlOf d hBl hlo hlo₀
  have hVmeetU : ∀ j : Fin q,
      (Flower.petal q a M j ∩ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B))).Nonempty := by
    intro j
    by_contra hcon
    have hVsubV : Flower.petal q a M j ⊆ MandelDim.piExp '' (MandelDim.BlOf d B) := by
      intro z hz
      have hz' : z ∈ insert 0 (MandelDim.piExp ''
          (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)) := by
        rw [← hBueq, ← hBleq]
        exact hVsubDg j hz
      rw [hUVeq] at hz'
      rcases hz' with hU | hL
      · exact absurd ⟨z, hz, hU⟩ hcon
      · exact hL
    have h0in : (0 : ℂ) ∈ closure (MandelDim.piExp '' (MandelDim.BlOf d B)) :=
      closure_mono hVsubV (hgeo.zero_mem_closure_petal j)
    have hclsub : closure (MandelDim.piExp '' (MandelDim.BlOf d B)) ⊆
        (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)))ᶜ := by
      intro x hx hxU
      rw [Metric.mem_closure_iff] at hx
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hUopen x hxU
      obtain ⟨y, hyS, hyx⟩ := hx ε hε
      exact Set.disjoint_left.mp hUVdisj
        (hεU (Metric.mem_ball.mpr (by rw [dist_comm]; exact hyx))) hyS
    exact hclsub h0in (Set.mem_insert _ _)
  -- #### the concrete chain and its `spec` bundle
  set V : Fin q → Set ℂ := fun j => Flower.petal q a M j with hVdef
  have hVopen : ∀ j : Fin q, IsOpen (V j) := fun j => hgeo.isOpen_petal j
  have hVconn : ∀ j : Fin q, IsConnected (V j) := fun j => hgeo.isConnected_petal j
  have hVsc' : ∀ j : Fin q, SimplyConnectedSpace (V j) := hVsc
  have hVdisj : ∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j) := hgeo.disjoint_petal
  have hVcl : ∀ j : Fin q, (0 : ℂ) ∈ closure (V j) := hgeo.zero_mem_closure_petal
  have hVne : ∀ j : Fin q, (0 : ℂ) ∉ V j := hgeo.not_mem_petal_zero
  have hVmapV : ∀ j : Fin q, ∀ z ∈ V j, g z ∈ V j ∪ {0} := hmaps
  have hspec := spreadChain_spec hF0 d hB hBne hBu hBl hsub hup hlo hVopen hVconn hVsubDg hVmapV
    hVne hVdisj hVcl hcap hreach
  dsimp only at hspec
  obtain ⟨hSopen, hSconn, hSsub, hS0, hSmono, hSmap, _hSsat, _hSmax, hSdisj⟩ := hspec
  set W : ℕ → Fin q → Set ℂ := Work.Horn.spreadChain g Dg V with hWdef
  have hWopen : ∀ (n : ℕ) (i : Fin q), IsOpen (W n i) :=
    fun n i => by rw [hWdef]; exact hSopen n i
  have hWconn : ∀ (n : ℕ) (i : Fin q), IsConnected (W n i) :=
    fun n i => by rw [hWdef]; exact hSconn n i
  have hWsub : ∀ (n : ℕ) (i : Fin q), W n i ⊆ Dg :=
    fun n i => by rw [hWdef]; exact hSsub n i
  have hW0 : ∀ i : Fin q, W 0 i = V i := fun i => by rw [hWdef]; exact hS0 i
  have hWmono : ∀ (n : ℕ) (i : Fin q), W n i ⊆ W (n + 1) i :=
    fun n i => by rw [hWdef]; exact hSmono n i
  have hWmap : ∀ (n : ℕ) (i : Fin q), Set.MapsTo g (W (n + 1) i) (W n i ∪ {0}) :=
    fun n i => by rw [hWdef]; exact hSmap n i
  have hWdisj : ∀ (n : ℕ) (i j : Fin q), i ≠ j → Disjoint (W n i) (W n j) :=
    fun n i j h => by rw [hWdef]; exact hSdisj n i j h
  have hWmono' : ∀ (i : Fin q) {m M : ℕ}, m ≤ M → W m i ⊆ W M i := by
    intro i m M hmM
    induction hmM with
    | refl => exact subset_rfl
    | step hle ih => exact ih.trans (hWmono _ i)
  have h0W : ∀ (i : Fin q) (n : ℕ), (0 : ℂ) ∉ W n i := by
    intro i n
    induction n with
    | zero => rw [hW0 i]; exact hVne i
    | succ n ih =>
      intro h0
      have h := Work.Horn.spreadChain_succ_subset_preimage (G := g) (D := Dg) (V := V) n i
        (show (0 : ℂ) ∈ Work.Horn.spreadChain g Dg V (n + 1) i from h0)
      have h2 : g 0 ∈ W n i := by rw [hWdef]; exact h.2
      exact ih (by rw [hfix] at h2; exact h2)
  -- the critical value of `g` on `D_g`
  have hcritval := pushdown_critval_global_eq hF0 d hB hBne hsetup hBu hBl hsub hup hlo
  set v : ℂ := MandelDim.piExp (d.Φ c) with hvdef
  -- #### the per-spread contradiction away from the critical value
  have key : ∀ i : Fin q, v ∉ ⋃ n, W n i → False := by
    intro i hv
    obtain ⟨hBij, hSC, hproper, honto, henter0⟩ :=
      spreadChain_bijOn_structure hF0 d hB hBne hBu hBl hsub hup hlo c hsetup hVopen hVconn
        hVsc' hVsubDg hVmapV hVne hVdisj hVcl hcap hreach i
        (show MandelDim.piExp (d.Φ c) ∉ ⋃ n, Work.Horn.spreadChain g Dg V n i from hv)
    -- the spread is `g`-invariant
    have hmapB : Set.MapsTo g (⋃ n, W n i) (⋃ n, W n i) := by
      intro z hz
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hz
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        have hzV : z ∈ V i := hW0 i ▸ hm
        rcases hVmapV i z hzV with h | h
        · exact Set.mem_iUnion.mpr ⟨0, (hW0 i).symm ▸ h⟩
        · exact absurd h (petal_image_ne_zero hDg hg hVconn hVsubDg hVcl hreach h0out i z hzV)
      · obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hmpos)
        refine Set.mem_iUnion.mpr ⟨m', ?_⟩
        have h1 := hWmap m' i (by rwa [hm'] at hm)
        rcases h1 with h | h
        · exact h
        · have hz0 : z ≠ 0 := by
            intro hzeq
            exact h0W i m (by rw [← hzeq]; exact hm)
          exact absurd (Set.mem_singleton_iff.mp h) (pushdown_ne_zero_of_ne_zero d.E hz0)
    -- the spread is bounded (it lies in the bounded upper piece)
    have hWsubU : ∀ n : ℕ, W n i ⊆ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B)) := by
      intro n
      refine hcross (W n i) (hWconn n i).isPreconnected ?_ ?_
      · rw [← hBueq, ← hBleq]; exact hWsub n i
      · obtain ⟨z, hzV, hzU⟩ := hVmeetU i
        refine ⟨z, ?_, hzU⟩
        induction n with
        | zero => rwa [hW0 i]
        | succ n ih => exact hWmono n i ih
    have hbdd : Bornology.IsBounded (⋃ n, W n i) := by
      refine Bornology.IsBounded.subset hUbdd ?_
      intro z hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      exact hWsubU n hn
    -- the Fatou coordinate on the petal, extended to the whole spread
    have hcoord : ∃ Φ : ℂ → ℂ,
        DifferentiableOn ℂ Φ (⋃ n, W n i) ∧
        (∀ z ∈ ⋃ n, W n i, Φ (g z) = Φ z + 1) ∧
        Set.InjOn Φ (V i) ∧
        (∀ b : ℝ, ∃ C : ℝ, ∀ w : ℂ, C < w.re → |w.im| ≤ b → ∃ z ∈ V i, Φ z = w) := by
      have hSb : Flower.Setup g (Metric.ball (0 : ℂ) ρ) q a :=
        { hD := Metric.isOpen_ball
          hconn := (convex_ball (0 : ℂ) ρ).isPreconnected
          h0 := Metric.mem_ball_self hρ
          hf := hg.mono hb.hsub
          hq := hq1
          ha := ha
          hfix := hfix
          hgerm := hgerm }
      have hbB : Flower.Bounds g (Metric.ball (0 : ℂ) ρ) q a ρ :=
        { hρ := hρ
          hsub := subset_rfl
          hq := hb.hq
          ha := hb.ha
          hfix := hb.hfix
          hf_eq := hb.hf_eq
          hderiv := hb.hderiv
          hchart := hb.hchart
          hunit_ne := hb.hunit_ne
          hunit_re := hb.hunit_re
          hunit_arg := hb.hunit_arg }
      obtain ⟨Φ₀, hΦ₀diff, hΦ₀abel, hΦ₀inj, hΦ₀strip⟩ :=
        flower_petal_fatouCoord hSb hbB hMpos hRM hgeo hMeps i
      have hVmapVi : Set.MapsTo g (V i) (V i) := by
        intro z hz
        rcases hVmapV i z hz with h | h
        · exact h
        · exact absurd h (petal_image_ne_zero hDg hg hVconn hVsubDg hVcl hreach h0out i z hz)
      have hVsubB : V i ⊆ ⋃ n, W n i :=
        fun z hz => Set.mem_iUnion.mpr ⟨0, (hW0 i).symm ▸ hz⟩
      have hBsubDg : (⋃ n, W n i) ⊆ Dg := by
        intro z hz
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
        exact hWsub n i hn
      have henter : ∀ z ∈ ⋃ n, W n i,
          ∃ m : ℕ, (∀ k ≤ m, g^[k] z ∈ ⋃ n, W n i) ∧ g^[m] z ∈ V i := by
        intro z hz
        obtain ⟨m, hm⟩ := henter0 z hz
        exact ⟨m, fun k _ => hmapB.iterate k hz, hm⟩
      obtain ⟨Φ, hΦdiff, hΦabel, hΦeq⟩ :=
        abel_extension_to_spread (isOpen_iUnion fun n => hWopen n i) (hg.mono hBsubDg)
          (hVopen i) hVsubB hVmapVi hΦ₀diff hΦ₀abel henter
      refine ⟨Φ, hΦdiff, hΦabel, hΦ₀inj.congr hΦeq.symm, ?_⟩
      intro b
      obtain ⟨C, hC⟩ := hΦ₀strip b
      refine ⟨C, fun w hw hb2 => ?_⟩
      obtain ⟨z, hz, hzw⟩ := hC w hw hb2
      exact ⟨z, hz, by rw [hΦeq hz, hzw]⟩
    -- the critical point produced inside the spread, and its value
    obtain ⟨z, hzB, hzd⟩ :=
      critPoint_of_component_of_ne_critval hF0 d hB hBne hBu hBl hsub hup hlo c hsetup
        hVopen hVsubDg hVmapV hVne i hBij hSC hbdd hcoord henter0
        (show MandelDim.piExp (d.Φ c) ∉ ⋃ n, Work.Horn.spreadChain g Dg V n i from hv)
    have hzDg : z ∈ Dg := by
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hzB
      exact hWsub m i hm
    have hzv : g z = v := hcritval z hzDg hzd
    exact hv (by rw [← hzv]; exact hmapB hzB)
  -- #### pigeonhole over the petals
  have hpigeon : ∃ i : Fin q, v ∉ ⋃ n, W n i := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, j, hij⟩ : ∃ i j : Fin q, i ≠ j := by
      refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
      intro h
      have : (0 : ℕ) = 1 := by simpa using congrArg Fin.val h
      omega
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (hcon i)
    obtain ⟨m', hm'⟩ := Set.mem_iUnion.mp (hcon j)
    have h1 : v ∈ W (max m m') i := hWmono' i (le_max_left _ _) hm
    have h2 : v ∈ W (max m m') j := hWmono' j (le_max_right _ _) hm'
    exact Set.disjoint_left.mp (hWdisj (max m m') i j hij) h1 h2
  obtain ⟨i, hi⟩ := hpigeon
  exact key i hi

end

end Work.Horn
