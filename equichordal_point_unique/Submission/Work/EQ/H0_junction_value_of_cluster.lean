import Mathlib
import Submission.Work.EQ.H0_step5_aux
import Submission.Work.EQ.bwdP_fan_degenerate_countable
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.charVal_set
import Submission.Work.EQ.charVal_props
import Submission.Work.EQ.la_nnas
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.FanUniform.fan_uniform_estimates
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.junction_limit_segment
import Submission.Work.EQ.stable_trichotomy_of_cluster
import Submission.Work.EQ.unstable_trichotomy_of_cluster

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN_HANA.md (the lead's restructuring of step 5 of H0_regular). Siblings run in parallel.

# H0_junction_value_of_cluster: step 5a in counting form (3–6k; replaces H0_junction_of_cluster)

**Why the statement changes.** The delegated `H0_junction_of_cluster` is almost right. What
changes:
* **(i)** Its conclusion does not record that `N` is large (`λᴺ‖c₀‖/r₁ < δ`). Without that, the
  far fan argument can leave the analyticity disc, and no counting is possible.
* **(ii)** Its route reads the sign list `s` from the approximating chains `x_k`. At a limit on
  the `cpow` branch cut the labels jump, so `bwdP s (limit) ≠ lim bwdP s (x_k)`. **Read `s` at the
  limit segment instead.**
* **(iii)** Step 6 ("discard the branch locus, a countable set") needs a proof. That proof is
  `bwdP_fan_degenerate_countable`.

The new conclusion is exactly the hypothesis shape of `junction_values_countable`, with
`w = μ₁z` and `c = μ₁μ₂c₀`.

**Imports:** `Submission.Work.EQ.H0_step5_aux,Submission.Work.EQ.CycleDefs,Submission.Work.EQ.charVal_set,Submission.Work.EQ.bwdP_fan_degenerate_countable,Submission.Work.EQ.la_nnas,Submission.Work.EQ.fan_estimates,Submission.Work.EQ.germC_facts,Submission.Work.EQ.HeteroAlgebra`

**Route.** Let `δ₀ := min(δf, δ₂)`.

1. **Per `z ∈ Z`, as in the existing route steps 1–5.**
   * Stable words `ε_k`, via `FanTrich`. Case (iii) is refuted by `no_near_axis_segment`. This
     gives `(ε₀, μ₁)` with `fan ε_k → fan ε₀(μ₁·)` uniformly.
   * Unstable words, read at a fixed `N` chosen so that `λᴺ‖c₀‖ < δ r₁` (route step 5). This gives
     `(η₀, μ₂)`.
   * `μ₁μ₂ ≠ 0`: case (i) gives `μ = 1`, case (ii) gives `0 < Re μ`.
   * `|μᵢ| ≤ 1` (FanTrich: `Re < 1`, `Im = 0`), so `‖μ₁z‖ < δ` and `‖λᴺμ₂c₀/z‖ < δ`.
2. **Bad points are countable.** Call `z` *bad* if `μ₁z ∈ D_N(ε₀)` (from
   `bwdP_fan_degenerate_countable`). The data `(ε₀, μ₁)` are countable, so the bad points form a
   countable set. Drop them.
3. **The limit segment for a good `z`.** Let `Pᵢ := lim (x_k).1(−i)` along a subsequence. By
   induction on `i ≤ N`:
   * `Pᵢ` is finite, `Pᵢ = bwdP σᵢ (S z)` with `S z := fan ε₀(μ₁z)`, and `R(Pᵢ) ≠ 0`, since `z`
     is good.
   * Hence the next points `(x_k).1(−i−1)` are bounded. The key algebra: `EqRelC P Q` gives
     `P + Q = e`, `e·e = 1`, `e ∥ Q − O₁`. So if `Q_k → Q` with `bsq (subO1 Q) ≠ 0`, then `e_k` is
     bounded, hence so is `P_k`.
   * A limit point satisfies `EqRelC` (a closed condition), so it is `invBranch t Pᵢ` for the
     label `t` read **at the limit** (backward dichotomy in `HeteroAlgebra`).
   * Let `s_z` be these limit labels. Then `P_N = bwdP s_z (S z)`, and `P_N` is the limit of the
     unstable end, `eqMirror (fan η₀ (λᴺμ₂c₀/z))`.
4. **Pigeonhole.** The tuples `(N, ε₀, η₀, s_z, μ₁, μ₂)` range over a countable set, so one tuple
   is shared by uncountably many good `z`. The map `z ↦ w = μ₁z` is injective, which gives the
   uncountable junction set.

**Risk: medium.** It is mostly existing delegated work. The new parts are the bad-set discard and
the limit-label reading; the latter is simpler than the `x_k`-label bookkeeping.

## Implementation (this file)

The three analytic inputs are delegated in parallel and imported here:
* `Work.EQ.junction_limit_segment` — the limit-segment reading (the labels are read at the limit,
  so the branch cut of `cpow` causes no difficulty);
* `Work.EQ.stable_trichotomy_of_cluster` — the stable-word trichotomy with case (iii) excluded
  (using the far end of the chain and `LaNnas.no_near_axis_segment`);
* `Work.EQ.unstable_trichotomy_of_cluster` — the same for the unstable (mirrored) words.

The discrete bookkeeping below is the lead's route: fix `N` first, extract `(ε₀, μ₁)` by
pigeonhole, discard the countable degenerate set (goodness of `z`), then repeat the trichotomy on
the unstable side and read the sign list off the limit segment.
-/

namespace Work.EQ

open Filter _root_.Topology

noncomputable section

/-! ## Elementary helpers -/

theorem h0jc_isChain_of_mem_H0 {a : ℝ} {h : ℂ → ℂ} {q : ChainData} (hq : q ∈ H0 a h) :
    IsChain a h q := by
  obtain ⟨ε, hε, f, hcont, hf0, hf⟩ := hq
  have hmem : q.2.1 ∈ Metric.ball q.2.1 ε := by rw [Metric.mem_ball, dist_self]; exact hε
  rw [← hf0]
  exact (hf q.2.1 hmem).1

/-- The norm of a real integer power of `λ`. -/
theorem h0jc_norm_lamC_zpow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℤ) :
    ‖(((eqLam a : ℝ) : ℂ) ^ j)‖ = (eqLam a) ^ j := by
  rw [← Complex.ofReal_zpow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zpow_pos (eqLam_pos' ha0 ha1) j)]

/-- The norm of a natural power of `λ`. -/
theorem h0jc_norm_lamC_pow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (N : ℕ) :
    ‖(((eqLam a : ℝ) : ℂ) ^ N)‖ = (eqLam a) ^ N := by
  rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos (eqLam_pos' ha0 ha1) N)]

/-- **A fan value at a small parameter is stable-near its centre**, with the explicit constant
`max Ke Lam`.  (Uniform first-order fan estimates plus the axis-centre parity.) -/
theorem h0jc_snNear_fan {a : ℝ} {h : ℂ → ℂ} {δE Ke Lam : ℝ}
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
theorem h0jc_unNear_eqMirror {a : ℝ} {P : ℂ × ℂ} {r : ℝ} (h : LaNnas.SnNear a P r) :
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
theorem h0jc_mirror_reading {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ}
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
theorem h0jc_farend_unNear {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {δE Ke Lam : ℝ}
    (hest : ∀ (ε : List Bool) (u : ℂ), ‖u‖ < δE →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖)
    (hctr : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k)
    {N : ℕ} {p : ChainData} (hp : IsChain a h p)
    (hw : ‖(((eqLam a : ℝ) : ℂ) ^ N * p.2.2)‖ < δE) :
    LaNnas.UnNear a (p.1 (-(N : ℤ)))
      (max Ke Lam * ‖(((eqLam a : ℝ) : ℂ) ^ N * p.2.2)‖) := by
  obtain ⟨η, hη⟩ := h0jc_mirror_reading ha0 ha1 hp
  rw [hη]
  exact h0jc_unNear_eqMirror (h0jc_snNear_fan hest hctr hw)

/-- The near end of a chain is stable-near the axis at its own stable parameter. -/
theorem h0jc_near_snNear {a : ℝ} {h : ℂ → ℂ} {δE Ke Lam : ℝ}
    (hest : ∀ (ε : List Bool) (u : ℂ), ‖u‖ < δE →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖)
    (hctr : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k)
    {p : ChainData} {ε : List Bool} (hread : p.1 0 = fan a h ε p.2.1)
    (hu : ‖p.2.1‖ < δE) :
    LaNnas.SnNear a (p.1 0) (max Ke Lam * ‖p.2.1‖) := by
  rw [hread]
  exact h0jc_snNear_fan hest hctr hu

/-- **Every characteristic value is nonzero.**  Case (i) of `charValSet` is `1`; in case (ii) the
characteristic value is real with positive real part (`charVal_props`). -/
theorem h0jc_charValSet_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {μ : ℂ} (hμ : μ ∈ charValSet a h) : μ ≠ 0 := by
  obtain ⟨δc, hδc, hprops, hfin⟩ := charVal_props ha0 ha1 hh
  rcases hμ with rfl | ⟨ε, hε, rfl⟩
  · exact one_ne_zero
  · obtain ⟨-, hre, -, -⟩ := hprops ε hε
    intro h0
    rw [h0] at hre
    simp at hre

/-- **Step 5a of `H0_regular` in counting form (replaces `H0_junction_of_cluster`).** For a
small trichotomy radius `δ`, an uncountable cluster set `Z` in an annulus of outer radius
`< δ`, and chains of `H0` with `ψ₁ → z` and `ψ → c₀ ≠ 0`, there are a depth `N`, words
`ε, η, s` and characteristic values `μ₁, μ₂` with `μ₁μ₂ ≠ 0` such that the value
`μ₁μ₂c₀` has an uncountable junction set with both fan arguments inside `B(0,δ)`. -/
theorem H0_junction_value_of_cluster {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ {δ : ℝ}, 0 < δ → δ ≤ δ₀ → FanTrich a h δ →
      ∀ {c₀ : ℂ}, c₀ ≠ 0 → ∀ {r₁ r₂ : ℝ}, 0 < r₁ → r₂ < δ →
      ∀ {Z : Set ℂ}, ¬ Z.Countable → (∀ z ∈ Z, r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂) →
      ∀ X : ℂ → ℕ → ChainData, (∀ z ∈ Z, ∀ k, X z k ∈ H0 a h) →
        (∀ z ∈ Z, Tendsto (fun k => (X z k).2.1) atTop (𝓝 z)) →
        (∀ z ∈ Z, Tendsto (fun k => (X z k).2.1 * (X z k).2.2) atTop (𝓝 c₀)) →
        ∃ (N : ℕ) (ε η s : List Bool) (μ₁ μ₂ : ℂ),
          μ₁ ∈ charValSet a h ∧ μ₂ ∈ charValSet a h ∧ μ₁ * μ₂ ≠ 0 ∧
          ¬ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δ ∧
              ‖((eqLam a : ℝ) : ℂ) ^ N * (μ₁ * μ₂ * c₀ / w)‖ < δ ∧
              bwdP a s (fan a h ε w) =
                eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * (μ₁ * μ₂ * c₀ / w)))}.Countable := by
  obtain ⟨δf, Ke, Lam, hδf, hKe, hLam, hfan⟩ :=
    FanUniform.fan_uniform_estimates ha0 ha1 hh
  have hfan_an : ∀ ε : List Bool, AnalyticOnNhd ℂ (fan a h ε) (Metric.ball (0 : ℂ) δf) :=
    fun ε => (hfan ε).1
  have hfan_est : ∀ (ε : List Bool) (u : ℂ), u ∈ Metric.ball (0 : ℂ) δf →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
    fun ε => (hfan ε).2
  have hctr : ∀ ε : List Bool, ∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k :=
    fun ε => (FanSep.axis_walk ha0 ha1 hh).2 ε |>.2
  obtain ⟨δ₂, hδ₂, hdeg⟩ := bwdP_fan_degenerate_countable ha0 ha1 hh
  have hlam0 : (0 : ℝ) < eqLam a := eqLam_pos' ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  set K : ℝ := max Ke Lam with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le hKe (le_max_left _ _)
  refine ⟨min (min δf δ₂) (1 / (16 * K)),
    lt_min (lt_min hδf hδ₂) (div_pos one_pos (by linarith)), ?_⟩
  intro δ hδ hδδ₀ htri c₀ hc₀ r₁ r₂ hr₁ hr₂ Z hZ hZann X hX hX1 hX2
  have hδf' : δ ≤ δf := le_trans hδδ₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₂' : δ ≤ δ₂ := le_trans hδδ₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδK : δ ≤ 1 / (16 * K) := le_trans hδδ₀ (min_le_right _ _)
  have hKδ : K * δ ≤ 1 / 16 := by
    have h1 : K * δ ≤ K * (1 / (16 * K)) := mul_le_mul_of_nonneg_left hδK hKpos.le
    have h2 : K * (1 / (16 * K)) = 1 / 16 := by field_simp
    linarith
  have hcont : ∀ ε : List Bool, ContinuousOn (fan a h ε) (Metric.ball (0 : ℂ) δ) := fun ε =>
    (hfan_an ε).continuousOn.mono (Metric.ball_subset_ball hδf')
  have hest : ∀ (ε : List Bool) (u : ℂ), ‖u‖ < δf →
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ Ke * ‖u‖ ∧
      ‖(fan a h ε u).2‖ ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
    fun ε u hu => hfan_est ε u (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hu)
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
    rw [norm_mul, h0jc_norm_lamC_pow ha0 ha1 N]
    exact lt_of_lt_of_le (hbound z hzr) hNδ.le
  have hW_small : ∀ z : ℂ, r₁ ≤ ‖z‖ → K * ‖(((eqLam a : ℝ) : ℂ) ^ N * (c₀ / z))‖ ≤ 1 / 8 := by
    intro z hzr
    have hbnd : ‖c₀ / z‖ ≤ ‖c₀‖ / r₁ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hr₁ hzr
    rw [norm_mul, h0jc_norm_lamC_pow ha0 ha1 N]
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
  -- readings of the chains
  have hread : ∀ z ∈ Z, ∀ k, ∃ ε : List Bool, (X z k).1 0 = fan a h ε ((X z k).2.1) :=
    fun z hz k => chain_eq_fan' ha0 ha1 (h0jc_isChain_of_mem_H0 (hX z hz k))
  choose εr hεr using hread
  have hreadT : ∀ z : ℂ, ∃ ε : ℕ → List Bool,
      z ∈ Z → ∀ k, (X z k).1 0 = fan a h (ε k) ((X z k).2.1) := by
    intro z
    by_cases hz : z ∈ Z
    · exact ⟨fun k => εr z hz k, fun _ => hεr z hz⟩
    · exact ⟨fun _ => [], fun h => absurd h hz⟩
  choose εT hεT using hreadT
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
    exact mul_div_cancel_left₀ _ ((h0jc_isChain_of_mem_H0 (hX z hz k)).2.1)
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
      exact (h0jc_farend_unNear ha0 ha1 hest hctr (h0jc_isChain_of_mem_H0 (hX z hz k)) hk4).mono
        (le_of_lt hk3)
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
  -- the stable trichotomy in `z`
  have hL2 : ∀ z ∈ Z, ∃ w : (List Bool × ℂ) × (ℕ → ℕ),
      w.1.2 ∈ charValSet a h ∧ ‖w.1.2‖ ≤ 1 ∧ StrictMono w.2 ∧
      Tendsto (fun k => fan a h (εT z (w.2 k + Kz z)) ((X z (w.2 k + Kz z)).2.1)) atTop
        (nhds (fan a h w.1.1 (w.1.2 * z))) := by
    intro z hz
    have hzδ : ‖z‖ < δ := lt_of_le_of_lt (hZann z hz).2 hr₂
    obtain ⟨ε₀, μ₁, h1, h2, φ, h3, h4⟩ :=
      stable_trichotomy_of_cluster ha0 ha1 hh hδ htri hcont (N := N) (W := z)
        (x := fun k => X z (k + Kz z)) (ε := fun k => εT z (k + Kz z))
        (fun k => h0jc_isChain_of_mem_H0 (hX z hz (k + Kz z)))
        (fun k => hεT z hz (k + Kz z))
        (fun k => (hKz z hz (k + Kz z) (le_add_of_nonneg_left (Nat.zero_le k))).1)
        (fun k => (hKz z hz (k + Kz z) (le_add_of_nonneg_left (Nat.zero_le k))).2.2)
        ((hX1 z hz).comp (tendsto_add_atTop_nat (Kz z))) hzδ
    exact ⟨((ε₀, μ₁), φ), h1, h2, h3, h4⟩
  have hL2T : ∀ z : ℂ, ∃ w : (List Bool × ℂ) × (ℕ → ℕ), z ∈ Z →
      (w.1.2 ∈ charValSet a h ∧ ‖w.1.2‖ ≤ 1 ∧ StrictMono w.2 ∧
        Tendsto (fun k => fan a h (εT z (w.2 k + Kz z)) ((X z (w.2 k + Kz z)).2.1)) atTop
          (nhds (fan a h w.1.1 (w.1.2 * z)))) := by
    intro z
    by_cases hz : z ∈ Z
    · obtain ⟨w, hw⟩ := hL2 z hz
      exact ⟨w, fun _ => hw⟩
    · exact ⟨(([], 0), id), fun h => absurd h hz⟩
  choose w2 hw2 using hL2T
  let εz : ℂ → List Bool := fun z => (w2 z).1.1
  let μz : ℂ → ℂ := fun z => (w2 z).1.2
  let φz : ℂ → ℕ → ℕ := fun z => (w2 z).2
  have hL2z : ∀ z ∈ Z, μz z ∈ charValSet a h ∧ ‖μz z‖ ≤ 1 ∧ StrictMono (φz z) ∧
      Tendsto (fun k => fan a h (εT z (φz z k + Kz z)) ((X z (φz z k + Kz z)).2.1)) atTop
        (nhds (fan a h (εz z) (μz z * z))) := fun z hz => hw2 z hz
  -- pigeonhole over `(ε₀, μ₁)`
  have hZ₁ex : ∃ (ε₀ : List Bool) (μ₁ : ℂ), μ₁ ∈ charValSet a h ∧
      ¬ {z | z ∈ Z ∧ εz z = ε₀ ∧ μz z = μ₁}.Countable := by
    by_contra hcon
    have hcon' : ∀ (ε₀ : List Bool) (μ₁ : ℂ), μ₁ ∈ charValSet a h →
        {z | z ∈ Z ∧ εz z = ε₀ ∧ μz z = μ₁}.Countable := by
      intro ε₀ μ₁ hmem
      by_contra hc
      exact hcon ⟨ε₀, μ₁, hmem, hc⟩
    have hsub : Z ⊆ ⋃ (p : List Bool × ℂ),
        ⋃ (_ : p ∈ Set.univ ×ˢ charValSet a h), {z | z ∈ Z ∧ εz z = p.1 ∧ μz z = p.2} := by
      intro z hz
      refine Set.mem_iUnion.mpr ⟨(εz z, μz z), ?_⟩
      exact Set.mem_iUnion.mpr ⟨⟨trivial, (hL2z z hz).1⟩, hz, rfl, rfl⟩
    have hc : (⋃ (p : List Bool × ℂ), ⋃ (_ : p ∈ Set.univ ×ˢ charValSet a h),
        {z | z ∈ Z ∧ εz z = p.1 ∧ μz z = p.2}).Countable := by
      refine Set.Countable.biUnion (Set.countable_univ.prod (countable_charValSet a h)) ?_
      rintro p ⟨-, hp⟩
      exact hcon' p.1 p.2 hp
    exact hZ (hc.mono hsub)
  obtain ⟨ε₀, μ₁, hμ₁mem, hZ₁unc⟩ := hZ₁ex
  have hμ₁ne : μ₁ ≠ 0 := h0jc_charValSet_ne_zero ha0 ha1 hh hμ₁mem
  set Z₁ : Set ℂ := {z | z ∈ Z ∧ εz z = ε₀ ∧ μz z = μ₁} with hZ₁def
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
    have hnormμ : ‖μ₁‖ ≤ 1 := by
      have h := (hL2z z hzZ).2.1
      rwa [hzμ] at h
    have hlt : ‖μ₁ * z‖ < δ₂ := by
      calc ‖μ₁ * z‖ = ‖μ₁‖ * ‖z‖ := norm_mul _ _
        _ ≤ 1 * r₂ := by
            exact mul_le_mul hnormμ (hZann z hzZ).2 (norm_nonneg _) zero_le_one
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
  -- the core: for a good `z`, the unstable trichotomy plus the limit segment
  have hcore : ∀ z ∈ Z₁ ∩ Badᶜ, ∃ (η₀ : List Bool) (μ₂ : ℂ) (s : List Bool),
      μ₂ ∈ charValSet a h ∧ ‖μ₂‖ ≤ 1 ∧ s.length ≤ N ∧
      bwdP a s (fan a h ε₀ (μ₁ * z)) =
        eqMirror (fan a h η₀ (((eqLam a : ℝ) : ℂ) ^ N * (μ₂ * (c₀ / z)))) := by
    intro z hz
    have hzZ : z ∈ Z := hz.1.1
    have hzε : εz z = ε₀ := hz.1.2.1
    have hzμ : μz z = μ₁ := hz.1.2.2
    have hzann := hZann z hzZ
    have hzr : r₁ ≤ ‖z‖ := hzann.1
    have hphimono : StrictMono (φz z) := (hL2z z hzZ).2.2.1
    have hxchain : ∀ k, IsChain a h (X z (φz z k + Kz z)) :=
      fun k => h0jc_isChain_of_mem_H0 (hX z hzZ _)
    have hindex : Tendsto (fun k : ℕ => φz z k + Kz z) atTop atTop := by
      refine tendsto_atTop_atTop.mpr (fun n => ⟨n, ?_⟩)
      intro k hk
      have h1 : k ≤ φz z k := hphimono.le_apply
      omega
    have hψ₂comp : Tendsto (fun k => (X z (φz z k + Kz z)).2.2) atTop (nhds (c₀ / z)) :=
      (hψ₂lim z hzZ).comp hindex
    have hmr : ∀ k : ℕ, ∃ η : List Bool,
        (X z (φz z k + Kz z)).1 (-(N : ℤ)) = eqMirror (fan a h η
          (((eqLam a : ℝ) : ℂ) ^ N * (X z (φz z k + Kz z)).2.2)) :=
      fun k => h0jc_mirror_reading ha0 ha1 (hxchain k)
    choose ηw hηw using hmr
    have hsn : ∀ k, LaNnas.SnNear a ((X z (φz z k + Kz z)).1 0) (1 / 4) := by
      intro k
      have hk := (hKz z hzZ (φz z k + Kz z) (le_add_of_nonneg_left (Nat.zero_le _))).1
      refine (h0jc_near_snNear hest hctr (hεT z hzZ _) (lt_of_lt_of_le hk hδf')).mono ?_
      calc max Ke Lam * ‖(X z (φz z k + Kz z)).2.1‖ ≤ K * δ := by
            rw [hKdef]
            exact mul_le_mul (le_refl _) hk.le (norm_nonneg _) hKpos.le
        _ ≤ 1 / 16 := hKδ
        _ ≤ 1 / 4 := by norm_num
    have hwlt : ∀ k, ‖(((eqLam a : ℝ) : ℂ) ^ N * (X z (φz z k + Kz z)).2.2)‖ < δ :=
      fun k => (hKz z hzZ (φz z k + Kz z) (le_add_of_nonneg_left (Nat.zero_le _))).2.1
    have hwtend : Tendsto (fun k => (((eqLam a : ℝ) : ℂ) ^ N * (X z (φz z k + Kz z)).2.2))
        atTop (nhds (((eqLam a : ℝ) : ℂ) ^ N * (c₀ / z))) := hψ₂comp.const_mul _
    obtain ⟨η₀, μ₂, hμ₂mem, hμ₂norm, ψ', hψ'mono, hψ'tend⟩ :=
      unstable_trichotomy_of_cluster ha0 ha1 hh hδ htri hcont (N := N)
        (W := (((eqLam a : ℝ) : ℂ) ^ N * (c₀ / z)))
        (x := fun k => X z (φz z k + Kz z))
        (w := fun k => (((eqLam a : ℝ) : ℂ) ^ N * (X z (φz z k + Kz z)).2.2))
        (η := ηw) (fun k => hxchain k) (fun k => hηw k) hwlt hsn hwtend
        (hW_lt z hzr)
    -- the limit segment, with the far end at the mirror of the unstable fan
    obtain ⟨s, hslen, hsT⟩ := junction_limit_segment (a := a) (N := N)
      (q := fun k => X z (φz z (ψ' k) + Kz z))
      (S := fan a h ε₀ (μ₁ * z))
      (T := eqMirror (fan a h η₀ (μ₂ * (((eqLam a : ℝ) : ℂ) ^ N * (c₀ / z)))))
      (fun k i hi => by
        have h := (hxchain (ψ' k)).1 (-((i : ℤ) + 1))
        rwa [show -((i : ℤ) + 1) + 1 = -(i : ℤ) by ring] at h)
      (hgood z hz)
      (by
        have h0t : Tendsto (fun k => fan a h (εT z (φz z (ψ' k) + Kz z))
            ((X z (φz z (ψ' k) + Kz z)).2.1)) atTop (nhds (fan a h ε₀ (μ₁ * z))) := by
          simpa [Function.comp_def, hzε, hzμ] using
            ((hL2z z hzZ).2.2.2).comp hψ'mono.tendsto_atTop
        have hfun : (fun k => (X z (φz z (ψ' k) + Kz z)).1 0) =
            (fun k => fan a h (εT z (φz z (ψ' k) + Kz z))
              ((X z (φz z (ψ' k) + Kz z)).2.1)) := by
          funext k
          exact hεT z hzZ _
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
  -- pigeonhole over the remaining data
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
  have hμ₂ne : μ₂ ≠ 0 := h0jc_charValSet_ne_zero ha0 ha1 hh hμ₂mem
  refine ⟨N, ε₀, η₀, s, μ₁, μ₂, hμ₁mem, hμ₂mem, mul_ne_zero hμ₁ne hμ₂ne, ?_⟩
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
    have hnormμ : ‖μ₁‖ ≤ 1 := by
      have h := (hL2z z hzZ).2.1
      rwa [hz.1.1.2.2] at h
    have hη : ηz z = η₀ := hz.2.1
    have hμ₂ : μ₂z z = μ₂ := hz.2.2.1
    have hs : sz z = s := hz.2.2.2
    obtain ⟨h1, h2, h3, h4⟩ := hcorez z hz.1
    have hμ₂norm : ‖μ₂‖ ≤ 1 := by rw [← hμ₂]; exact h2
    rw [hs] at h3
    rw [hs, hη, hμ₂] at h4
    have hfield : μ₁ * μ₂ * c₀ / (μ₁ * z) = μ₂ * (c₀ / z) := by
      rw [show μ₁ * μ₂ * c₀ = (μ₂ * c₀) * μ₁ by ring,
        show μ₁ * z = z * μ₁ by ring, mul_div_mul_right _ _ hμ₁ne]
      rw [mul_div_assoc]
    have hle : ‖μ₂ * (c₀ / z)‖ ≤ ‖c₀ / z‖ := by
      rw [norm_mul]
      calc ‖μ₂‖ * ‖c₀ / z‖ ≤ 1 * ‖c₀ / z‖ :=
            mul_le_mul_of_nonneg_right hμ₂norm (norm_nonneg _)
        _ = ‖c₀ / z‖ := one_mul _
    refine ⟨mul_ne_zero hμ₁ne hz0, ?_, ?_, ?_⟩
    · calc ‖μ₁ * z‖ = ‖μ₁‖ * ‖z‖ := norm_mul _ _
        _ ≤ 1 * r₂ := mul_le_mul hnormμ (hZann z hzZ).2 (norm_nonneg _) zero_le_one
        _ = r₂ := one_mul _
        _ < δ := hr₂
    · rw [hfield, norm_mul, h0jc_norm_lamC_pow ha0 ha1 N]
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

end Work.EQ
