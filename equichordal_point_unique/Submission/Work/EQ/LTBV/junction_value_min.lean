import Mathlib
import Submission.Work.EQ.la_tail_bound_value
import Submission.Work.EQ.H0_junction_value_of_cluster
import Submission.Work.EQ.LaTB.la_fan_trichotomy_v2
import Submission.Work.EQ.H0_step5_aux
import Submission.Work.EQ.tb_fan_run
import Submission.Work.EQ.stable_trichotomy_v2_of_minimal_words
import Submission.Work.EQ.minimal_word_last_letter
import Submission.Work.EQ.LTBV.minimal_word_last_letter_bounded

/-!
# `Work.EQ.LTBV.junction_value_min`

`Work.EQ.H0_junction_value_of_cluster` (proved) produces, from a cluster of chains of `⁰H` whose
`ψ₁` tend to every point of an uncountable set `Z` and whose values tend to `c₀ ≠ 0`, a depth `N`,
words `ε, η, s` and characteristic values `μ₁, μ₂` with `μ₁μ₂ ≠ 0` such that the *labelled* junction
set of `μ₁μ₂c₀` is uncountable.  Its stable half uses `FanTrich` (the trichotomy with `Set.EqOn`
case (i)), whose case (i) yields `μ₁ = 1`, and nothing in that statement excludes `μ₁ = 1`.

This file proves the **non-trivial** version: when in addition the tails of the chains fail at
arbitrarily large depths (`∀ z ∈ Z, ∀ M, ∃ k, M ≤ tailIdx a h (X z k)`), the trichotomy can be run
on the chains' **minimal** words, for which

* case (i) (literally constant words) is impossible, because the minimal words have unbounded
  length, and
* in case (ii) the trailing word `C k` of the decomposition `ε k = ε₀ ++ true^(s k) ++ C k`
  contains a `false` letter (the minimal word ends in `false`), so
  `μ₁ = charVal a h (C k) ≠ 1` by `Work.EQ.ltbv_charVal_ne_one_of_false`.

Hence `μ₁ ≠ 1`, which is exactly what the descent hypothesis in Rychlik's Lemma 5.1 needs.

The stable trichotomy on minimal words is `Work.EQ.stable_trichotomy_v2_of_minimal_words`
(proved); the unstable half, the discard of the countable degenerate set, the limit-segment reading
`Work.EQ.junction_limit_segment` and the two pigeonholes are the ones of
`Work.EQ.H0_junction_value_of_cluster`, copied here unchanged.
-/

namespace Work.EQ.LTBV

open Filter _root_.Topology

noncomputable section

/-! ## Elementary helpers -/

theorem ltbv_norm_lamC_pow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) :
    ‖(((eqLam a : ℝ) : ℂ) ^ N)‖ = (eqLam a) ^ N := by
  rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos (eqLam_pos' ha0 ha1) N)]

/-- A real characteristic value with positive real part has modulus equal to its real part. -/
theorem ltbv_norm_charVal_eq_re {a : ℝ} {h : ℂ → ℂ} {ε : List Bool}
    (him : (charVal a h ε).im = 0) (hre0 : 0 < (charVal a h ε).re) :
    ‖charVal a h ε‖ = (charVal a h ε).re := by
  have h2 : ‖charVal a h ε‖ ^ 2 = (charVal a h ε).re ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him]
    ring
  nlinarith [norm_nonneg (charVal a h ε), hre0, h2]

/-- **Every characteristic value has modulus at most `1`.** (Case (i) of `charValSet` is `1`; in
case (ii) the value is real with `0 < re ≤ 1`.) -/
theorem ltbv_charValSet_norm_le_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {μ : ℂ} (hμ : μ ∈ charValSet a h) : ‖μ‖ ≤ 1 := by
  obtain ⟨δc, hδc, hprops, hfin⟩ := charVal_props ha0 ha1 hh
  rcases hμ with h1 | ⟨ε, hε, rfl⟩
  · rw [h1, norm_one]
  · obtain ⟨him, hpos, hle, -⟩ := hprops ε hε
    rw [ltbv_norm_charVal_eq_re him hpos]; exact hle

/-- **Every characteristic value is nonzero.** -/
theorem ltbv_charValSet_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {μ : ℂ} (hμ : μ ∈ charValSet a h) : μ ≠ 0 := by
  obtain ⟨δc, hδc, hprops, hfin⟩ := charVal_props ha0 ha1 hh
  rcases hμ with rfl | ⟨ε, hε, rfl⟩
  · exact one_ne_zero
  · obtain ⟨-, hre, -, -⟩ := hprops ε hε
    intro h0
    rw [h0] at hre
    simp at hre

/-- `CharSet` and `charValSet` are the same set of characteristic values. -/
theorem ltbv_CharSet_subset_charValSet {a : ℝ} {h : ℂ → ℂ} :
    CharSet a h ⊆ charValSet a h := by
  rintro μ (h1 | ⟨ε, hε, rfl⟩)
  · exact Or.inl h1
  · exact Or.inr ⟨ε, hε, rfl⟩

/-- `FanTrich` is monotone in the radius. -/
theorem ltbv_fanTrich_mono {a : ℝ} {h : ℂ → ℂ} {δ δ' : ℝ} (hδ' : δ' ≤ δ)
    (H : FanTrich a h δ) : FanTrich a h δ' := by
  intro ε
  obtain ⟨φ, hφ, hcase⟩ := H ε
  refine ⟨φ, hφ, ?_⟩
  rcases hcase with h1 | h2 | h3
  · obtain ⟨ε₀, hε₀⟩ := h1
    exact Or.inl ⟨ε₀, fun k => (hε₀ k).mono (Metric.ball_subset_ball hδ')⟩
  · obtain ⟨ε₀, ε₁, s, C, hs, hword, hC, he₁, him, hpos, hlt, huni⟩ := h2
    exact Or.inr (Or.inl ⟨ε₀, ε₁, s, C, hs, hword, hC, he₁, him, hpos, hlt,
      huni.mono (Metric.ball_subset_ball hδ')⟩)
  · refine Or.inr (Or.inr ⟨h3.1, fun η hη => ?_⟩)
    filter_upwards [h3.2 η hη] with k hk
    exact fun u hu => hk u (Metric.ball_subset_ball hδ' hu)

/-- **A fan value at a small parameter is stable-near its centre**, with the explicit constant
`max Ke Lam`.  (Uniform first-order fan estimates plus the axis-centre parity.) -/
theorem ltbv_snNear_fan {a : ℝ} {h : ℂ → ℂ} {δE Ke Lam : ℝ}
    (hest : ∀ (ε : List Bool) (u : ℂ), ‖u‖ < δE →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖)
    (hctr : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k)
    {η : List Bool} {w : ℂ} (hw : ‖w‖ < δE) :
    LaNnas.SnNear a (fan a h η w) (max Ke Lam * ‖w‖) := by
  obtain ⟨h1, h2⟩ := hest η w hw
  obtain ⟨k, hk⟩ := hctr η
  refine ⟨k, ?_, ?_⟩
  · rw [hk] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg w))
  · calc ‖(fan a h η w).2‖
        ≤ Lam * ‖w‖ * ‖(fan a h η w).1 - ((a / 2 : ℝ) : ℂ)‖ := h2
      _ ≤ max Ke Lam * ‖w‖ * ‖(fan a h η w).1 - ((a / 2 : ℝ) : ℂ)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg w)

/-- The bisector reflection turns a stable-near point into an unstable-near one. -/
theorem ltbv_unNear_eqMirror {a : ℝ} {P : ℂ × ℂ} {r : ℝ} (h : LaNnas.SnNear a P r) :
    LaNnas.UnNear a (eqMirror P) r := by
  obtain ⟨Y, h1, h2⟩ := h
  refine ⟨-Y, ?_, ?_⟩
  · have hc : (1 / 2 + 2 * ((-Y : ℤ) : ℂ)) = -((-1 / 2 : ℂ) + 2 * (Y : ℂ)) := by push_cast; ring
    simp only [eqMirror]
    rw [hc]
    rw [show -(P.1) - (-((-1 / 2 : ℂ) + 2 * (Y : ℂ))) = -(P.1 - ((-1 / 2 : ℂ) + 2 * (Y : ℂ)))
      by ring, norm_neg]
    exact h1
  · simp only [eqMirror]
    rw [show -(P.1) + ((a / 2 : ℝ) : ℂ) = -(P.1 - ((a / 2 : ℝ) : ℂ)) by ring, norm_neg]
    exact h2

/-- **The unstable reading of a chain at depth `N`.**  The index `-N` point of a chain is the
mirrored fan value of some word at the parameter `λ^N ψ₂`. -/
theorem ltbv_mirror_reading {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ}
    {p : ChainData} (hp : IsChain a h p) :
    ∃ η : List Bool,
      p.1 (-(N : ℤ)) = eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * p.2.2)) := by
  obtain ⟨η, hη⟩ := chain_eq_fan' ha0 ha1
    (p := shiftZ a (N : ℤ) (mirrorChain p))
    (isChain_shiftZ ha0 ha1 (isChain_mirrorChain hp) (N : ℤ))
  refine ⟨η, ?_⟩
  have h2 : (shiftZ a (N : ℤ) (mirrorChain p)).1 0 = eqMirror (p.1 (-(N : ℤ))) := by
    simp only [shiftZ_fst, mirrorChain_fst, zero_add]
  have h3 : (shiftZ a (N : ℤ) (mirrorChain p)).2.1 = ((eqLam a : ℝ) : ℂ) ^ N * p.2.2 := by
    rw [shiftZ_psi1, mirrorChain_psi1, zpow_natCast]
  rw [h2, h3] at hη
  rw [← hη, eqMirror_invol]

/-- The far end of a chain is unstable-near the axis, at the `λ^N`-scaled unstable parameter. -/
theorem ltbv_farend_unNear {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {δE Ke Lam : ℝ}
    (hest : ∀ (ε : List Bool) (u : ℂ), ‖u‖ < δE →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖)
    (hctr : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k)
    {N : ℕ} {p : ChainData} (hp : IsChain a h p)
    (hw : ‖(((eqLam a : ℝ) : ℂ) ^ N * p.2.2)‖ < δE) :
    LaNnas.UnNear a (p.1 (-(N : ℤ)))
      (max Ke Lam * ‖(((eqLam a : ℝ) : ℂ) ^ N * p.2.2)‖) := by
  obtain ⟨η, hη⟩ := ltbv_mirror_reading ha0 ha1 hp
  rw [hη]
  exact ltbv_unNear_eqMirror (ltbv_snNear_fan hest hctr hw)

/-- The near end of a chain is stable-near the axis at its own stable parameter. -/
theorem ltbv_near_snNear {a : ℝ} {h : ℂ → ℂ} {δE Ke Lam : ℝ}
    (hest : ∀ (ε : List Bool) (u : ℂ), ‖u‖ < δE →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖)
    (hctr : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k)
    {p : ChainData} {ε : List Bool} (hread : p.1 0 = fan a h ε p.2.1)
    (hu : ‖p.2.1‖ < δE) :
    LaNnas.SnNear a (p.1 0) (max Ke Lam * ‖p.2.1‖) := by
  rw [hread]
  exact ltbv_snNear_fan hest hctr hu

/-! ## The main theorem -/

theorem junction_value_min {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ δ₀ → Work.EQ.ltbvTrich a h δ →
      ∀ {c₀ : ℂ}, c₀ ≠ 0 → ∀ {r₁ r₂ : ℝ}, 0 < r₁ → r₂ < δ →
      ∀ {Z : Set ℂ}, ¬ Z.Countable → (∀ z ∈ Z, r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂) →
      ∀ X : ℂ → ℕ → Work.EQ.ChainData,
        (∀ z ∈ Z, ∀ k, X z k ∈ Work.EQ.H0 a h) →
        (∀ z ∈ Z, Filter.Tendsto (fun k => (X z k).2.1) Filter.atTop (nhds z)) →
        (∀ z ∈ Z, Filter.Tendsto (fun k => (X z k).2.1 * (X z k).2.2) Filter.atTop
          (nhds c₀)) →
        (∀ z ∈ Z, ∀ M : ℕ, ∃ k, M ≤ Work.EQ.tailIdx a h (X z k)) →
        ∃ (N : ℕ) (ε η s : List Bool) (μ₁ μ₂ : ℂ),
          μ₁ ∈ Work.EQ.charValSet a h ∧ μ₂ ∈ Work.EQ.charValSet a h ∧ μ₁ ≠ 1 ∧
          μ₁ * μ₂ ≠ 0 ∧
          ¬ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ ∧
              ‖((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (μ₁ * μ₂ * c₀ / w)‖ < δ ∧
              Work.EQ.bwdP a s (Work.EQ.fan a h ε w) =
                Work.EQ.eqMirror (Work.EQ.fan a h η
                  (((Work.EQ.eqLam a : ℝ) : ℂ) ^ N * (μ₁ * μ₂ * c₀ / w)))}.Countable := by
  obtain ⟨δf, Ke, Lam, hδf, hKe, hLam, hfan⟩ := FanUniform.fan_uniform_estimates ha0 ha1 hh
  have hfan_an : ∀ ε : List Bool, AnalyticOnNhd ℂ (fan a h ε) (Metric.ball (0 : ℂ) δf) :=
    fun ε => (hfan ε).1
  have hfan_est : ∀ (ε : List Bool) (u : ℂ), u ∈ Metric.ball (0 : ℂ) δf →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
    fun ε => (hfan ε).2
  have hctr : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k :=
    fun ε => (FanSep.axis_walk ha0 ha1 hh).2 ε |>.2
  obtain ⟨δ₂, hδ₂, hdeg⟩ := bwdP_fan_degenerate_countable ha0 ha1 hh
  obtain ⟨δgap, hδgap, hgap0⟩ := FanTri.fan_gap_unif ha0 ha1 hh
  obtain ⟨δT, hδT, hFtri⟩ := fan_trichotomy' ha0 ha1 hh
  obtain ⟨δmw, hδmw, hmw⟩ := minimal_word_last_letter_bounded ha0 ha1 hh
  have hlam0 : (0 : ℝ) < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  set K : ℝ := max Ke Lam with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le hKe (le_max_left _ _)
  refine ⟨min (min δf δ₂) (min (min δgap (min δT δmw)) (1 / (16 * K))),
    lt_min (lt_min hδf hδ₂) (lt_min (lt_min hδgap (lt_min hδT hδmw))
      (div_pos one_pos (by linarith))), ?_⟩
  intro δ hδ hδδ₀ htri c₀ hc₀ r₁ r₂ hr₁ hr₂ Z hZ hZann X hX hX1 hX2 htails
  have hδA : δ ≤ min δf δ₂ := le_trans hδδ₀ (min_le_left _ _)
  have hδB : δ ≤ min (min δgap (min δT δmw)) (1 / (16 * K)) :=
    le_trans hδδ₀ (min_le_right _ _)
  have hδC : δ ≤ min δgap (min δT δmw) := le_trans hδB (min_le_left _ _)
  have hδD : δ ≤ min δT δmw := le_trans hδC (min_le_right _ _)
  have hδf' : δ ≤ δf := le_trans hδA (min_le_left _ _)
  have hδ₂' : δ ≤ δ₂ := le_trans hδA (min_le_right _ _)
  have hδgap' : δ ≤ δgap := le_trans hδC (min_le_left _ _)
  have hδT' : δ ≤ δT := le_trans hδD (min_le_left _ _)
  have hδmw' : δ ≤ δmw := le_trans hδD (min_le_right _ _)
  have hδK : δ ≤ 1 / (16 * K) := le_trans hδB (min_le_right _ _)
  have hKδ : K * δ ≤ 1 / 16 := by
    have h1 : K * δ ≤ K * (1 / (16 * K)) := mul_le_mul_of_nonneg_left hδK hKpos.le
    have h2 : K * (1 / (16 * K)) = 1 / 16 := by field_simp
    linarith
  have htriFan : FanTrich a h δ := ltbv_fanTrich_mono hδT' hFtri
  have hcont : ∀ ε : List Bool, ContinuousOn (fan a h ε) (Metric.ball (0 : ℂ) δ) := fun ε =>
    (hfan_an ε).continuousOn.mono (Metric.ball_subset_ball hδf')
  have hest : ∀ (ε : List Bool) (u : ℂ), ‖u‖ < δf →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
    fun ε u hu => hfan_est ε u (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hu)
  have hgap : ∀ (ε₀ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool) (μ : ℂ),
      Tendsto s atTop atTop → (∀ k, fan a h (C k) 0 = ltbvA1) →
      (∀ k, charVal a h (C k) = μ) →
      TendstoUniformlyOn (fun k => fan a h (ε₀ ++ List.replicate (s k) true ++ C k))
        (fun u => fan a h ε₀ (μ * u)) atTop (Metric.ball (0 : ℂ) δ) :=
    fun ε₀ s C μ hs hC hμ => (hgap0 ε₀ s C μ hs hC hμ).mono (Metric.ball_subset_ball hδgap')
  -- the depth `N`, chosen so that the far arguments stay inside the discs
  set R : ℝ := ‖c₀‖ / r₁ + 1 with hRdef
  obtain ⟨N, hNδ, hNK⟩ : ∃ N : ℕ, (eqLam a) ^ N * R < δ ∧ K * ((eqLam a) ^ N * R) ≤ 1 / 16 := by
    have hlim : Tendsto (fun n : ℕ => (eqLam a) ^ n * R) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const R
    have hpos : 0 < min δ (1 / (16 * K)) := lt_min hδ (div_pos one_pos (by linarith))
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hpos)).exists
    refine ⟨n, lt_of_lt_of_le hn (min_le_left _ _), ?_⟩
    have h2 : (eqLam a) ^ n * R < 1 / (16 * K) := lt_of_lt_of_le hn (min_le_right _ _)
    have h3 : K * ((eqLam a) ^ n * R) < 1 / 16 := by
      rw [lt_div_iff₀ (by linarith)] at h2
      linarith
    exact le_of_lt h3
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hbound : ∀ z : ℂ, r₁ ≤ ‖z‖ → (eqLam a) ^ N * ‖c₀ / z‖ < (eqLam a) ^ N * R := by
    intro z hzr
    have hbnd : ‖c₀ / z‖ ≤ ‖c₀‖ / r₁ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hr₁ hzr
    calc (eqLam a) ^ N * ‖c₀ / z‖ ≤ (eqLam a) ^ N * (‖c₀‖ / r₁) :=
          mul_le_mul_of_nonneg_left hbnd (pow_nonneg hlam0.le N)
      _ < (eqLam a) ^ N * R := by
          apply mul_lt_mul_of_pos_left _ (pow_pos hlam0 N)
          rw [hRdef]; linarith
  have hW_lt : ∀ z : ℂ, r₁ ≤ ‖z‖ → ‖(((eqLam a : ℝ) : ℂ) ^ N * (c₀ / z))‖ < δ := by
    intro z hzr
    rw [norm_mul, ltbv_norm_lamC_pow ha0 ha1 N]
    exact lt_of_lt_of_le (hbound z hzr) hNδ.le
  have hW_small : ∀ z : ℂ, r₁ ≤ ‖z‖ → K * ‖(((eqLam a : ℝ) : ℂ) ^ N * (c₀ / z))‖ ≤ 1 / 8 := by
    intro z hzr
    have hbnd : ‖c₀ / z‖ ≤ ‖c₀‖ / r₁ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hr₁ hzr
    rw [norm_mul, ltbv_norm_lamC_pow ha0 ha1 N]
    calc K * ((eqLam a) ^ N * ‖c₀ / z‖)
        ≤ K * ((eqLam a) ^ N * (‖c₀‖ / r₁)) := by
          apply mul_le_mul_of_nonneg_left _ hKpos.le
          exact mul_le_mul_of_nonneg_left hbnd (pow_nonneg hlam0.le N)
      _ ≤ K * ((eqLam a) ^ N * R) := by
          apply mul_le_mul_of_nonneg_left _ hKpos.le
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hlam0.le N)
          rw [hRdef]; linarith
      _ ≤ 1 / 16 := hNK
      _ ≤ 1 / 8 := by norm_num
  -- the `ψ₂`-convergence of the cluster
  have hψ₂lim : ∀ z ∈ Z, Tendsto (fun k => (X z k).2.2) atTop (nhds (c₀ / z)) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h0
      have h1 := (hZann z hz).1
      rw [h0, norm_zero] at h1
      linarith
    have hdiv : Tendsto (fun k => (X z k).2.1 * (X z k).2.2 / (X z k).2.1) atTop
        (nhds (c₀ / z)) := (hX2 z hz).div (hX1 z hz) hz0
    refine hdiv.congr' ?_
    filter_upwards with k
    exact mul_div_cancel_left₀ _ (Work.EQ.isChain_of_mem_H0 (hX z hz k)).2.1
  -- the cutoff beyond which all the smallness conditions hold
  have hcut : ∀ z ∈ Z, ∃ K₀ : ℕ, ∀ k ≥ K₀,
      ‖(X z k).2.1‖ < δ ∧
      ‖(((eqLam a : ℝ) : ℂ) ^ N * (X z k).2.2)‖ < δ ∧
      LaNnas.UnNear a ((X z k).1 (-(N : ℤ))) (1 / 4) := by
    intro z hz
    have hzann := hZann z hz
    have hzδ : ‖z‖ < δ := lt_of_le_of_lt hzann.2 hr₂
    have hψ₁ : Tendsto (fun k => (X z k).2.1) atTop (nhds z) := hX1 z hz
    have hψ₂ : Tendsto (fun k => (X z k).2.2) atTop (nhds (c₀ / z)) := hψ₂lim z hz
    have hLnorm := hW_lt z hzann.1
    have hKnorm := hW_small z hzann.1
    have hev1 : ∀ᶠ k in atTop, ‖(X z k).2.1‖ < δ := hψ₁.norm.eventually (eventually_lt_nhds hzδ)
    have hev2 : ∀ᶠ k in atTop, ‖(((eqLam a : ℝ) : ℂ) ^ N * (X z k).2.2)‖ < δ :=
      ((hψ₂.const_mul (((eqLam a : ℝ) : ℂ) ^ N)).norm).eventually (eventually_lt_nhds hLnorm)
    have hev4 : ∀ᶠ k in atTop, ‖(((eqLam a : ℝ) : ℂ) ^ N * (X z k).2.2)‖ < δf :=
      ((hψ₂.const_mul (((eqLam a : ℝ) : ℂ) ^ N)).norm).eventually
        (eventually_lt_nhds (lt_of_lt_of_le hLnorm hδf'))
    have hev3 : ∀ᶠ k in atTop,
        K * ‖(((eqLam a : ℝ) : ℂ) ^ N * (X z k).2.2)‖ < 1 / 4 :=
      (((hψ₂.const_mul (((eqLam a : ℝ) : ℂ) ^ N)).norm).const_mul K).eventually
        (eventually_lt_nhds (lt_of_le_of_lt hKnorm (by norm_num)))
    have hev5 : ∀ᶠ k in atTop, LaNnas.UnNear a ((X z k).1 (-(N : ℤ))) (1 / 4) := by
      filter_upwards [hev3, hev4] with k hk3 hk4
      exact (ltbv_farend_unNear ha0 ha1 hest hctr
        (Work.EQ.isChain_of_mem_H0 (hX z hz k)) hk4).mono (le_of_lt hk3)
    obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (hev1.and (hev2.and hev5))
    exact ⟨K₀, fun k hk => ⟨(hK₀ k hk).1, (hK₀ k hk).2.1, (hK₀ k hk).2.2⟩⟩
  have hcutT : ∀ z : ℂ, ∃ K₀ : ℕ, z ∈ Z → (∀ k ≥ K₀,
      ‖(X z k).2.1‖ < δ ∧
      ‖(((eqLam a : ℝ) : ℂ) ^ N * (X z k).2.2)‖ < δ ∧
      LaNnas.UnNear a ((X z k).1 (-(N : ℤ))) (1 / 4)) := by
    intro z
    by_cases hz : z ∈ Z
    · obtain ⟨K₀, hK⟩ := hcut z hz
      exact ⟨K₀, fun _ => hK⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose Kz hKz using hcutT
  -- *** the stable half: minimal words, literal trichotomy, `μ₁ ≠ 1` ***
  have hstable : ∀ z ∈ Z, ∃ (εs : ℕ → List Bool) (ε₀ : List Bool) (μ₁ : ℂ) (Φ : ℕ → ℕ),
      μ₁ ∈ charValSet a h ∧ μ₁ ≠ 1 ∧ ‖μ₁‖ ≤ 1 ∧ StrictMono Φ ∧ (∀ k, Kz z ≤ Φ k) ∧
      (∀ k, (X z (Φ k)).1 0 = fan a h (εs k) ((X z (Φ k)).2.1)) ∧
      (∀ k, (εs k).length = tailIdx a h (X z (Φ k))) ∧
      (∀ k, (εs k).getLast? = some false) ∧
      Tendsto (fun k => fan a h (εs k) ((X z (Φ k)).2.1)) atTop
        (nhds (fan a h ε₀ (μ₁ * z))) := by
    intro z hz
    have hzδ : ‖z‖ < δ := lt_of_le_of_lt (hZann z hz).2 hr₂
    obtain ⟨ψ, hψmono, hψle⟩ := exists_strictMono_length
      (ε := fun k => List.replicate (tailIdx a h (X z k)) false)
      (fun B => by obtain ⟨k, hk⟩ := htails z hz B; exact ⟨k, by simpa using hk⟩)
    set j : ℕ → ℕ := fun k => ψ (k + Kz z + 1) with hj
    have hjmono : StrictMono j := fun p q h => hψmono (by omega)
    have hjge : ∀ k, Kz z ≤ j k := fun k => by
      have h1 : k + Kz z + 1 ≤ j k := hψmono.id_le _
      omega
    have hjle : ∀ k, k + 1 ≤ tailIdx a h (X z (j k)) := fun k => by
      have h1 : k + Kz z + 1 ≤ tailIdx a h (X z (ψ (k + Kz z + 1))) := by
        simpa using hψle (k + Kz z + 1)
      have h2 : j k = ψ (k + Kz z + 1) := rfl
      rw [h2]
      omega
    have hw : ∀ k, ∃ ε : List Bool,
        (X z (j k)).1 0 = fan a h ε ((X z (j k)).2.1) ∧
        ε.length = tailIdx a h (X z (j k)) ∧ ε.getLast? = some false := by
      intro k
      have hchain : IsChain a h (X z (j k)) := Work.EQ.isChain_of_mem_H0 (hX z hz _)
      have hsmall : ‖(X z (j k)).2.1‖ < δmw :=
        lt_of_lt_of_le (hKz z hz (j k) (hjge k)).1 hδmw'
      obtain ⟨ε, h1, h2, h3⟩ := hmw hchain hsmall
      exact ⟨ε, h1, h2, h3 (lt_of_lt_of_le (Nat.succ_pos k) (hjle k))⟩
    choose εs hεs using hw
    obtain ⟨ε₀, μ₁, hμ₁C, hμ₁ne, φ, hφmono, hconv⟩ :=
      stable_trichotomy_v2_of_minimal_words ha0 ha1 hh hδ hcont htri hgap
        (N := N) (W := z) (x := fun k => X z (j k)) (ε := εs)
        (fun k => Work.EQ.isChain_of_mem_H0 (hX z hz _))
        (fun k => (hεs k).1)
        (fun k => (hKz z hz (j k) (hjge k)).1)
        (fun k => (hεs k).2.2)
        (fun B => ⟨B, le_trans (Nat.le_succ B) (by rw [(hεs B).2.1]; exact hjle B)⟩)
        (fun k => (hKz z hz (j k) (hjge k)).2.2)
        ((hX1 z hz).comp hjmono.tendsto_atTop)
        hzδ
    have hμ₁mem : μ₁ ∈ charValSet a h := ltbv_CharSet_subset_charValSet hμ₁C
    have hμ₁le : ‖μ₁‖ ≤ 1 := ltbv_charValSet_norm_le_one ha0 ha1 hh hμ₁mem
    refine ⟨fun k => εs (φ k), ε₀, μ₁, fun k => j (φ k), hμ₁mem, hμ₁ne, hμ₁le,
      hjmono.comp hφmono, ?_, ?_, ?_, ?_, ?_⟩
    · intro k; exact hjge (φ k)
    · intro k; exact (hεs (φ k)).1
    · intro k; exact (hεs (φ k)).2.1
    · intro k; exact (hεs (φ k)).2.2
    · exact hconv
  have hstableT : ∀ z : ℂ, ∃ (εs : ℕ → List Bool) (ε₀ : List Bool) (μ₁ : ℂ) (Φ : ℕ → ℕ),
      z ∈ Z → (μ₁ ∈ charValSet a h ∧ μ₁ ≠ 1 ∧ ‖μ₁‖ ≤ 1 ∧ StrictMono Φ ∧ (∀ k, Kz z ≤ Φ k) ∧
        (∀ k, (X z (Φ k)).1 0 = fan a h (εs k) ((X z (Φ k)).2.1)) ∧
        (∀ k, (εs k).length = tailIdx a h (X z (Φ k))) ∧
        (∀ k, (εs k).getLast? = some false) ∧
        Tendsto (fun k => fan a h (εs k) ((X z (Φ k)).2.1)) atTop
          (nhds (fan a h ε₀ (μ₁ * z)))) := by
    intro z
    by_cases hz : z ∈ Z
    · obtain ⟨εs, ε₀, μ₁, Φ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hstable z hz
      exact ⟨εs, ε₀, μ₁, Φ, fun _ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩
    · exact ⟨(fun _ => []), [], 0, id, fun h => absurd h hz⟩
  choose εsz ε₀z μ₁z Φz hdata using hstableT
  -- pigeonhole over `(ε₀, μ₁)` (with `μ₁ ≠ 1` built into the countable index set)
  have hZ₁ex : ∃ (ε₀ : List Bool) (μ₁ : ℂ), μ₁ ∈ charValSet a h ∧ μ₁ ≠ 1 ∧
      ¬ {z | z ∈ Z ∧ ε₀z z = ε₀ ∧ μ₁z z = μ₁}.Countable := by
    by_contra hcon
    have hcon' : ∀ (ε₀ : List Bool) (μ₁ : ℂ), μ₁ ∈ charValSet a h → μ₁ ≠ 1 →
        {z | z ∈ Z ∧ ε₀z z = ε₀ ∧ μ₁z z = μ₁}.Countable := by
      intro ε₀ μ₁ hmem hne
      by_contra hc
      exact hcon ⟨ε₀, μ₁, hmem, hne, hc⟩
    have hsub : Z ⊆ ⋃ (p : List Bool × ℂ),
        ⋃ (_ : p ∈ Set.univ ×ˢ (charValSet a h \ {1})),
          {z | z ∈ Z ∧ ε₀z z = p.1 ∧ μ₁z z = p.2} := by
      intro z hz
      refine Set.mem_iUnion.mpr ⟨(ε₀z z, μ₁z z), ?_⟩
      exact Set.mem_iUnion.mpr ⟨⟨trivial, (hdata z hz).1, (hdata z hz).2.1⟩, hz, rfl, rfl⟩
    have hc : (⋃ (p : List Bool × ℂ),
        ⋃ (_ : p ∈ Set.univ ×ˢ (charValSet a h \ {1})),
          {z | z ∈ Z ∧ ε₀z z = p.1 ∧ μ₁z z = p.2}).Countable := by
      refine Set.Countable.biUnion
        (Set.countable_univ.prod ((countable_charValSet a h).mono ?_)) ?_
      · rintro x ⟨hx, -⟩
        exact hx
      · rintro p ⟨-, hp⟩
        exact hcon' p.1 p.2 hp.1 hp.2
    exact hZ (hc.mono hsub)
  obtain ⟨ε₀, μ₁, hμ₁mem, hμ₁ne1, hZ₁unc⟩ := hZ₁ex
  have hμ₁ne : μ₁ ≠ 0 := ltbv_charValSet_ne_zero ha0 ha1 hh hμ₁mem
  have hμ₁norm : ‖μ₁‖ ≤ 1 := ltbv_charValSet_norm_le_one ha0 ha1 hh hμ₁mem
  -- the (countable) degenerate locus of the first `N` backward steps
  set Z₁ : Set ℂ := {z | z ∈ Z ∧ ε₀z z = ε₀ ∧ μ₁z z = μ₁} with hZ₁def
  set D : Set ℂ := {w : ℂ | ‖w‖ < δ₂ ∧ ∃ σ : List Bool, σ.length ≤ N ∧
    bsq (subO1 a (bwdP a σ (fan a h ε₀ w))) = 0} with hDdef
  have hDc : D.Countable := hdeg ε₀ N
  set Bad : Set ℂ := {z : ℂ | ∃ σ : List Bool, σ.length ≤ N ∧
    bsq (subO1 a (bwdP a σ (fan a h ε₀ (μ₁ * z)))) = 0} with hBaddef
  have hpre : ((fun z : ℂ => μ₁ * z) ⁻¹' D).Countable := by
    have hsub : ((fun z : ℂ => μ₁ * z) ⁻¹' D) ⊆ (fun w : ℂ => w / μ₁) '' D := by
      rintro z hz
      exact ⟨μ₁ * z, hz, by show μ₁ * z / μ₁ = z; exact mul_div_cancel_left₀ _ hμ₁ne⟩
    exact (hDc.image _).mono hsub
  have hbadZ : (Bad ∩ Z₁).Countable := by
    refine hpre.mono ?_
    rintro z ⟨hb, hzZ, hzε, hzμ⟩
    have hlt : ‖μ₁ * z‖ < δ₂ := by
      calc ‖μ₁ * z‖ = ‖μ₁‖ * ‖z‖ := norm_mul _ _
        _ ≤ 1 * r₂ := mul_le_mul hμ₁norm (hZann z hzZ).2 (norm_nonneg _) zero_le_one
        _ = r₂ := one_mul _
        _ < δ := hr₂
        _ ≤ δ₂ := hδ₂'
    exact ⟨hlt, hb⟩
  have hZ₂unc : ¬ (Z₁ ∩ Badᶜ).Countable := by
    intro h
    refine hZ₁unc ((h.union hbadZ).mono ?_)
    intro z hz
    by_cases hb : z ∈ Bad
    · exact Or.inr ⟨hb, hz⟩
    · exact Or.inl ⟨hz, hb⟩
  have hgood : ∀ z ∈ Z₁ ∩ Badᶜ, ∀ σ : List Bool, σ.length ≤ N →
      bsq (subO1 a (bwdP a σ (fan a h ε₀ (μ₁ * z)))) ≠ 0 := by
    intro z hz σ hσ h0
    exact hz.2 ⟨σ, hσ, h0⟩
  -- the unstable half: the far end of a good `z` is a mirrored fan value
  have hcore : ∀ z ∈ Z₁ ∩ Badᶜ, ∃ (η₀ : List Bool) (μ₂ : ℂ) (s : List Bool),
      μ₂ ∈ charValSet a h ∧ ‖μ₂‖ ≤ 1 ∧ s.length ≤ N ∧
      bwdP a s (fan a h ε₀ (μ₁ * z)) =
        eqMirror (fan a h η₀ (((eqLam a : ℝ) : ℂ) ^ N * (μ₂ * (c₀ / z)))) := by
    intro z hz
    have hzZ : z ∈ Z := hz.1.1
    have hzε : ε₀z z = ε₀ := hz.1.2.1
    have hzμ : μ₁z z = μ₁ := hz.1.2.2
    have hzr : r₁ ≤ ‖z‖ := (hZann z hzZ).1
    obtain ⟨hμ₁zmem, hμ₁zne, hμ₁zle, hΦmono, hΦge, hread, hlen, hlast, hconv⟩ := hdata z hzZ
    have hxchain : ∀ k, IsChain a h (X z (Φz z k)) :=
      fun k => Work.EQ.isChain_of_mem_H0 (hX z hzZ _)
    have hψ₂comp : Tendsto (fun k => (X z (Φz z k)).2.2) atTop (nhds (c₀ / z)) :=
      (hψ₂lim z hzZ).comp hΦmono.tendsto_atTop
    have hmr : ∀ k : ℕ, ∃ η : List Bool,
        (X z (Φz z k)).1 (-(N : ℤ)) = eqMirror (fan a h η
          (((eqLam a : ℝ) : ℂ) ^ N * (X z (Φz z k)).2.2)) :=
      fun k => ltbv_mirror_reading ha0 ha1 (hxchain k)
    choose ηw hηw using hmr
    have hsn : ∀ k, LaNnas.SnNear a ((X z (Φz z k)).1 0) (1 / 4) := by
      intro k
      have hk := (hKz z hzZ (Φz z k) (hΦge k)).1
      refine (ltbv_near_snNear hest hctr (hread k) (lt_of_lt_of_le hk hδf')).mono ?_
      calc max Ke Lam * ‖(X z (Φz z k)).2.1‖ ≤ K * δ := by
            rw [hKdef]
            exact mul_le_mul (le_refl _) hk.le (norm_nonneg _) hKpos.le
        _ ≤ 1 / 16 := hKδ
        _ ≤ 1 / 4 := by norm_num
    have hwlt : ∀ k, ‖(((eqLam a : ℝ) : ℂ) ^ N * (X z (Φz z k)).2.2)‖ < δ :=
      fun k => (hKz z hzZ (Φz z k) (hΦge k)).2.1
    have hwtend : Tendsto (fun k => (((eqLam a : ℝ) : ℂ) ^ N * (X z (Φz z k)).2.2))
        atTop (nhds (((eqLam a : ℝ) : ℂ) ^ N * (c₀ / z))) := hψ₂comp.const_mul _
    obtain ⟨η₀, μ₂, hμ₂mem, hμ₂norm, ψ', hψ'mono, hψ'tend⟩ :=
      unstable_trichotomy_of_cluster ha0 ha1 hh hδ htriFan hcont (N := N)
        (W := (((eqLam a : ℝ) : ℂ) ^ N * (c₀ / z)))
        (x := fun k => X z (Φz z k))
        (w := fun k => (((eqLam a : ℝ) : ℂ) ^ N * (X z (Φz z k)).2.2))
        (η := ηw) (fun k => hxchain k) (fun k => hηw k) hwlt hsn hwtend
        (hW_lt z hzr)
    obtain ⟨s, hslen, hsT⟩ := junction_limit_segment (a := a) (N := N)
      (q := fun k => X z (Φz z (ψ' k)))
      (S := fan a h ε₀ (μ₁ * z))
      (T := eqMirror (fan a h η₀ (μ₂ * (((eqLam a : ℝ) : ℂ) ^ N * (c₀ / z)))))
      (fun k i hi => by
        have h := (hxchain (ψ' k)).1 (-((i : ℤ) + 1))
        rwa [show -((i : ℤ) + 1) + 1 = -(i : ℤ) by ring] at h)
      (hgood z hz)
      (by
        have h0t : Tendsto (fun k => fan a h (εsz z (ψ' k)) ((X z (Φz z (ψ' k))).2.1)) atTop
            (nhds (fan a h ε₀ (μ₁ * z))) := by
          have h1 := hconv.comp hψ'mono.tendsto_atTop
          simpa [Function.comp_def, hzε, hzμ] using h1
        have hfun : (fun k => (X z (Φz z (ψ' k))).1 0) =
            (fun k => fan a h (εsz z (ψ' k)) ((X z (Φz z (ψ' k))).2.1)) := by
          funext k
          exact hread (ψ' k)
        rw [hfun]
        exact h0t)
      (by
        have hcontm : Continuous (eqMirror : ℂ × ℂ → ℂ × ℂ) := by
          unfold eqMirror
          fun_prop
        have h2 := (hcontm.tendsto
          (fan a h η₀ (μ₂ * (((eqLam a : ℝ) : ℂ) ^ N * (c₀ / z))))).comp hψ'tend
        refine h2.congr' ?_
        filter_upwards with k
        exact (hηw (ψ' k)).symm)
    refine ⟨η₀, μ₂, s, hμ₂mem, hμ₂norm, hslen, ?_⟩
    rw [← hsT]
    congr 1
    congr 1
    ring
  -- pigeonhole over the remaining data
  have hcoreT : ∀ z : ℂ, ∃ (η₀ : List Bool) (μ₂ : ℂ) (s : List Bool), z ∈ Z₁ ∩ Badᶜ →
      (μ₂ ∈ charValSet a h ∧ ‖μ₂‖ ≤ 1 ∧ s.length ≤ N ∧
        bwdP a s (fan a h ε₀ (μ₁ * z)) =
          eqMirror (fan a h η₀ (((eqLam a : ℝ) : ℂ) ^ N * (μ₂ * (c₀ / z))))) := by
    intro z
    by_cases hz : z ∈ Z₁ ∩ Badᶜ
    · obtain ⟨η₀, μ₂, s, h1, h2, h3, h4⟩ := hcore z hz
      exact ⟨η₀, μ₂, s, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨[], 0, [], fun h => absurd h hz⟩
  choose ηz μ₂z sz hcorez using hcoreT
  have hKex : ∃ (η₀ : List Bool) (μ₂ : ℂ) (s : List Bool), μ₂ ∈ charValSet a h ∧
      ¬ {z | z ∈ Z₁ ∩ Badᶜ ∧ ηz z = η₀ ∧ μ₂z z = μ₂ ∧ sz z = s}.Countable := by
    by_contra hcon
    have hcon' : ∀ (η₀ : List Bool) (μ₂ : ℂ) (s : List Bool), μ₂ ∈ charValSet a h →
        {z | z ∈ Z₁ ∩ Badᶜ ∧ ηz z = η₀ ∧ μ₂z z = μ₂ ∧ sz z = s}.Countable := by
      intro η₀ μ₂ s hmem
      by_contra hc
      exact hcon ⟨η₀, μ₂, s, hmem, hc⟩
    have hsub : Z₁ ∩ Badᶜ ⊆ ⋃ (p : List Bool × ℂ × List Bool),
        ⋃ (_ : p ∈ Set.univ ×ˢ charValSet a h ×ˢ Set.univ),
          {z | z ∈ Z₁ ∩ Badᶜ ∧ ηz z = p.1 ∧ μ₂z z = p.2.1 ∧ sz z = p.2.2} := by
      intro z hz
      refine Set.mem_iUnion.mpr ⟨(ηz z, μ₂z z, sz z), ?_⟩
      exact Set.mem_iUnion.mpr ⟨⟨trivial, (hcorez z hz).1, trivial⟩, hz, rfl, rfl, rfl⟩
    have hc : (⋃ (p : List Bool × ℂ × List Bool),
        ⋃ (_ : p ∈ Set.univ ×ˢ charValSet a h ×ˢ Set.univ),
          {z | z ∈ Z₁ ∩ Badᶜ ∧ ηz z = p.1 ∧ μ₂z z = p.2.1 ∧ sz z = p.2.2}).Countable := by
      refine Set.Countable.biUnion
        (Set.countable_univ.prod ((countable_charValSet a h).prod Set.countable_univ)) ?_
      rintro p ⟨-, hp⟩
      exact hcon' p.1 p.2.1 p.2.2 hp.1
    exact hZ₂unc (hc.mono hsub)
  obtain ⟨η₀, μ₂, s, hμ₂mem, hKunc⟩ := hKex
  have hμ₂ne : μ₂ ≠ 0 := ltbv_charValSet_ne_zero ha0 ha1 hh hμ₂mem
  refine ⟨N, ε₀, η₀, s, μ₁, μ₂, hμ₁mem, hμ₂mem, hμ₁ne1, mul_ne_zero hμ₁ne hμ₂ne, ?_⟩
  intro hcount
  set Kk : Set ℂ := {z | z ∈ Z₁ ∩ Badᶜ ∧ ηz z = η₀ ∧ μ₂z z = μ₂ ∧ sz z = s} with hKkdef
  have hsub : (fun z : ℂ => μ₁ * z) '' Kk ⊆ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ ∧
      ‖(((eqLam a : ℝ) : ℂ) ^ N * (μ₁ * μ₂ * c₀ / w))‖ < δ ∧
      bwdP a s (fan a h ε₀ w) = eqMirror (fan a h η₀
        (((eqLam a : ℝ) : ℂ) ^ N * (μ₁ * μ₂ * c₀ / w)))} := by
    rintro w ⟨z, hz, rfl⟩
    dsimp only
    have hzZ : z ∈ Z := hz.1.1.1
    have hzr : r₁ ≤ ‖z‖ := (hZann z hzZ).1
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hzr
      linarith
    have hη : ηz z = η₀ := hz.2.1
    have hμ₂ : μ₂z z = μ₂ := hz.2.2.1
    have hs : sz z = s := hz.2.2.2
    obtain ⟨h1, h2, h3, h4⟩ := hcorez z hz.1
    rw [hs] at h3
    rw [hs, hη, hμ₂] at h4
    have hfield : μ₁ * μ₂ * c₀ / (μ₁ * z) = μ₂ * (c₀ / z) := by
      rw [show μ₁ * μ₂ * c₀ = (μ₂ * c₀) * μ₁ by ring,
        show μ₁ * z = z * μ₁ by ring, mul_div_mul_right _ _ hμ₁ne]
      rw [mul_div_assoc]
    have h2' : ‖μ₂‖ ≤ 1 := by rw [← hμ₂]; exact h2
    have hle : ‖μ₂ * (c₀ / z)‖ ≤ ‖c₀ / z‖ := by
      rw [norm_mul]
      calc ‖μ₂‖ * ‖c₀ / z‖ ≤ 1 * ‖c₀ / z‖ :=
            mul_le_mul_of_nonneg_right h2' (norm_nonneg _)
        _ = ‖c₀ / z‖ := one_mul _
    refine ⟨mul_ne_zero hμ₁ne hz0, ?_, ?_, ?_⟩
    · calc ‖μ₁ * z‖ = ‖μ₁‖ * ‖z‖ := norm_mul _ _
        _ ≤ 1 * r₂ := mul_le_mul hμ₁norm (hZann z hzZ).2 (norm_nonneg _) zero_le_one
        _ = r₂ := one_mul _
        _ < δ := hr₂
    · rw [hfield, norm_mul, ltbv_norm_lamC_pow ha0 ha1 N]
      calc (eqLam a) ^ N * ‖μ₂ * (c₀ / z)‖ ≤ (eqLam a) ^ N * ‖c₀ / z‖ :=
            mul_le_mul_of_nonneg_left hle (pow_nonneg hlam0.le N)
        _ ≤ (eqLam a) ^ N * R := le_of_lt (hbound z hzr)
        _ < δ := hNδ
    · rw [hfield]
      exact h4
  have hKc : Kk.Countable := by
    have h1 : ((fun z : ℂ => μ₁ * z) '' Kk).Countable := hcount.mono hsub
    have h2 : Kk ⊆ (fun w : ℂ => w / μ₁) '' ((fun z : ℂ => μ₁ * z) '' Kk) := by
      intro z hz
      exact ⟨μ₁ * z, ⟨z, hz, rfl⟩, by show μ₁ * z / μ₁ = z; exact mul_div_cancel_left₀ _ hμ₁ne⟩
    exact (h1.image _).mono h2
  exact hKunc hKc

end

end Work.EQ.LTBV
