import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.H0_countable_fibre
import Submission.Work.EQ.H0_secondCountable
import Submission.Work.EQ.EquiLocalDefs
import Submission.Work.EQ.sections_eqOn_of_preconnected
import Submission.Work.EQ.isChartData_normalized
import Submission.Work.Analysis.Complex.punctured_ball_connected

namespace Work.EQ

open Filter _root_.Topology

noncomputable section

/-! ## Elementary auxiliary lemmas -/

/-- `ζ ↦ ζ / ω` sends the punctured neighbourhood filter of `0` to itself. -/
theorem tendsto_div_const_nhdsWithin_ne {ω : ℂ} (hω : ω ≠ 0) :
    Tendsto (fun ζ : ℂ => ζ / ω) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h : ContinuousAt (fun ζ : ℂ => ζ / ω) 0 := continuousAt_id.div_const ω
    have h2 : Tendsto (fun ζ : ℂ => ζ / ω) (𝓝 0) (𝓝 0) := by simpa using h.tendsto
    exact h2.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ζ hζ
    exact div_ne_zero hζ hω

/-- The punctured disc `ball 0 ρ \ {0}` is preconnected. -/
theorem isPreconnected_punctured_ball_aux {ρ : ℝ} (hρ : 0 < ρ) :
    IsPreconnected (Metric.ball (0 : ℂ) ρ \ {0}) := by
  have h := (Work.Analysis.Complex.isConnected_punctured_ball_at (0 : ℂ) hρ).isPreconnected
  have hset : {z : ℂ | 0 < ‖z - 0‖ ∧ ‖z - 0‖ < ρ} = Metric.ball (0 : ℂ) ρ \ {0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Metric.mem_ball, dist_zero_right,
      Set.mem_singleton_iff, sub_zero, norm_pos_iff]
    tauto
  rwa [hset] at h

/-- Membership in the punctured disc. -/
theorem mem_ball_zero_sdiff_singleton {ρ : ℝ} {ζ : ℂ} :
    ζ ∈ Metric.ball (0 : ℂ) ρ \ {0} ↔ ζ ≠ 0 ∧ ‖ζ‖ < ρ := by
  simp only [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]
  tauto

/-- Membership in the punctured disc, in terms of `0 < ‖ζ‖`. -/
theorem mem_ball_zero_sdiff_singleton' {ρ : ℝ} {ζ : ℂ} :
    ζ ∈ Metric.ball (0 : ℂ) ρ \ {0} ↔ 0 < ‖ζ‖ ∧ ‖ζ‖ < ρ := by
  rw [mem_ball_zero_sdiff_singleton, norm_pos_iff]

/-! ## Counting lemma: bounded charts of a fixed exponent -/

theorem countable_psi2_limits_kappa_bdd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {r : ℝ} (hh : IsStableGerm a h r) (u₀ : ℂ) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Set.Countable {v₀ : ℂ | ∃ (e : ℂ → ChainData) (κ : ℂ), IsChartData a h e u₀ κ k ∧
      ε ≤ ‖κ‖ ∧ Tendsto (fun ζ : ℂ => (e ζ).2.2) (𝓝[≠] (0 : ℂ)) (𝓝 v₀)} := by
  classical
  rcases lt_or_ge 0 k with hk | hk
  · -- a reference radius `ζ₀` with `ζ₀ ^ k < ε`
    obtain ⟨ζ₀, hζ₀pos, hζ₀k⟩ : ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ^ k < ε := by
      refine ⟨min ε 1 / 2, by positivity, ?_⟩
      have h1 : min ε 1 / 2 ≤ 1 := by have := min_le_right (ε) 1; linarith
      have h2 : min ε 1 / 2 < ε := by have := min_le_left (ε) 1; linarith
      calc (min ε 1 / 2) ^ k ≤ (min ε 1 / 2) ^ 1 :=
            pow_le_pow_of_le_one (by positivity) h1 (by omega)
        _ = min ε 1 / 2 := pow_one _
        _ < ε := h2
    have hLI : LocalInj a h := localInj_of_localHomeomorph (H0_structure ha0 ha1 hh).1
    -- the countable set of witness points
    set W : Set ChainData := {p : ChainData | p ∈ H0 a h ∧ p.2.1 = u₀ + (ζ₀ : ℂ) ^ k} with hWdef
    have hWc : W.Countable := H0_countable_fibre ha0 ha1 hh (u₀ + (ζ₀ : ℂ) ^ k)
    -- the fibre of the witness map `(e, κ) ↦ e (ζ₀ / κ^{1/k})`
    set V : ChainData → Set ℂ := fun p => {v₀ : ℂ | ∃ (e : ℂ → ChainData) (κ : ℂ),
        IsChartData a h e u₀ κ k ∧ ε ≤ ‖κ‖ ∧
        e ((ζ₀ : ℂ) / (κ ^ ((k : ℂ)⁻¹))) = p ∧
        Tendsto (fun ζ : ℂ => (e ζ).2.2) (𝓝[≠] (0 : ℂ)) (𝓝 v₀)} with hVdef
    have hVsub : ∀ p : ChainData, (V p).Subsingleton := by
      intro p v₀ hv v₀' hv'
      rw [hVdef] at hv hv'
      obtain ⟨e, κ, hE, hκε, hΦ, htend⟩ := hv
      obtain ⟨e', κ', hE', hκ'ε, hΦ', htend'⟩ := hv'
      have hκne : κ ≠ 0 := hE.2.1
      have hκ'ne : κ' ≠ 0 := hE'.2.1
      set ω : ℂ := κ ^ ((k : ℂ)⁻¹) with hωdef
      set ω' : ℂ := κ' ^ ((k : ℂ)⁻¹) with hω'def
      have hωk : ω ^ k = κ := by rw [hωdef]; exact Complex.cpow_nat_inv_pow κ hk.ne'
      have hω'k : ω' ^ k = κ' := by rw [hω'def]; exact Complex.cpow_nat_inv_pow κ' hk.ne'
      have hωne : ω ≠ 0 := fun hh => hκne (by rw [← hωk, hh, zero_pow hk.ne'])
      have hω'ne : ω' ≠ 0 := fun hh => hκ'ne (by rw [← hω'k, hh, zero_pow hk.ne'])
      have hnormk : ‖ω‖ ^ k = ‖κ‖ := by rw [← norm_pow, hωk]
      have hnorm'k : ‖ω'‖ ^ k = ‖κ'‖ := by rw [← norm_pow, hω'k]
      have hζω : ζ₀ < ‖ω‖ := lt_of_pow_lt_pow_left₀ k (norm_nonneg ω)
        (by rw [hnormk]; exact lt_of_lt_of_le hζ₀k hκε)
      have hζω' : ζ₀ < ‖ω'‖ := lt_of_pow_lt_pow_left₀ k (norm_nonneg ω')
        (by rw [hnorm'k]; exact lt_of_lt_of_le hζ₀k hκ'ε)
      set ρ : ℝ := min ‖ω‖ ‖ω'‖ with hρdef
      have hρpos : 0 < ρ := by
        rw [hρdef]
        exact lt_min (norm_pos_iff.mpr hωne) (norm_pos_iff.mpr hω'ne)
      have hζ₀ρ : ζ₀ < ρ := by rw [hρdef]; exact lt_min hζω hζω'
      -- the normalised legs
      obtain ⟨hFn, hFc⟩ := isChartData_normalized hE hωk
      obtain ⟨hGn, hGc⟩ := isChartData_normalized hE' hω'k
      have hUω : Metric.ball (0 : ℂ) ρ \ {0} ⊆ {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < ‖ω‖} := by
        intro ζ hζ
        rw [mem_ball_zero_sdiff_singleton'] at hζ
        exact ⟨hζ.1, lt_of_lt_of_le hζ.2 (by rw [hρdef]; exact min_le_left _ _)⟩
      have hUω' : Metric.ball (0 : ℂ) ρ \ {0} ⊆ {ζ : ℂ | 0 < ‖ζ‖ ∧ ‖ζ‖ < ‖ω'‖} := by
        intro ζ hζ
        rw [mem_ball_zero_sdiff_singleton'] at hζ
        exact ⟨hζ.1, lt_of_lt_of_le hζ.2 (by rw [hρdef]; exact min_le_right _ _)⟩
      have hFmem : ∀ u ∈ Metric.ball (0 : ℂ) ρ \ {0},
          (fun ζ : ℂ => e (ζ / ω)) u ∈ H0 a h ∧
            ((fun ζ : ℂ => e (ζ / ω)) u).2.1 = u₀ + u ^ k :=
        fun u hu => hFn u (hUω hu).1 (hUω hu).2
      have hGmem : ∀ u ∈ Metric.ball (0 : ℂ) ρ \ {0},
          (fun ζ : ℂ => e' (ζ / ω')) u ∈ H0 a h ∧
            ((fun ζ : ℂ => e' (ζ / ω')) u).2.1 = u₀ + u ^ k :=
        fun u hu => hGn u (hUω' hu).1 (hUω' hu).2
      have hζ₀mem : (ζ₀ : ℂ) ∈ Metric.ball (0 : ℂ) ρ \ {0} := by
        rw [mem_ball_zero_sdiff_singleton']
        refine ⟨?_, ?_⟩
        · simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hζ₀pos] using hζ₀pos
        · simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hζ₀pos] using hζ₀ρ
      have heq₀ : (fun ζ : ℂ => e (ζ / ω)) (ζ₀ : ℂ) = (fun ζ : ℂ => e' (ζ / ω')) (ζ₀ : ℂ) := by
        show e ((ζ₀ : ℂ) / ω) = e' ((ζ₀ : ℂ) / ω')
        rw [hΦ, hΦ']
      have hEqOn := sections_eqOn_of_preconnected hLI
        (isPreconnected_punctured_ball_aux hρpos) (w := fun u : ℂ => u₀ + u ^ k)
        (hFc.mono hUω) (hGc.mono hUω') hFmem hGmem hζ₀mem heq₀
      -- agreement near `0` turns the limit of the second leg into the limit of the first
      have hball_ev : ∀ᶠ ζ : ℂ in 𝓝[≠] (0 : ℂ), ζ ∈ Metric.ball (0 : ℂ) ρ \ {0} := by
        have h1 : ∀ᶠ ζ : ℂ in 𝓝[≠] (0 : ℂ), ζ ∈ Metric.ball (0 : ℂ) ρ := by
          rw [eventually_nhdsWithin_iff]
          filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hρpos] with ζ hζ _
          exact hζ
        have h2 : ∀ᶠ ζ : ℂ in 𝓝[≠] (0 : ℂ), ζ ≠ 0 := by
          filter_upwards [self_mem_nhdsWithin] with ζ hζ
          simpa using hζ
        filter_upwards [h1, h2] with ζ hζ1 hζ2
        exact ⟨hζ1, hζ2⟩
      have hlim1 : Tendsto (fun ζ : ℂ => (e (ζ / ω)).2.2) (𝓝[≠] (0 : ℂ)) (𝓝 v₀) :=
        htend.comp (tendsto_div_const_nhdsWithin_ne hωne)
      have hlim2 : Tendsto (fun ζ : ℂ => (e (ζ / ω)).2.2) (𝓝[≠] (0 : ℂ)) (𝓝 v₀') := by
        refine ((htend'.comp (tendsto_div_const_nhdsWithin_ne hω'ne)).congr' ?_)
        filter_upwards [hball_ev] with ζ hζ
        exact congrArg (fun q : ChainData => q.2.2) (hEqOn ζ hζ).symm
      exact tendsto_nhds_unique hlim1 hlim2
    -- the fibre cover
    have hcov : {v₀ : ℂ | ∃ (e : ℂ → ChainData) (κ : ℂ), IsChartData a h e u₀ κ k ∧
        ε ≤ ‖κ‖ ∧ Tendsto (fun ζ : ℂ => (e ζ).2.2) (𝓝[≠] (0 : ℂ)) (𝓝 v₀)} ⊆
        ⋃ p ∈ W, V p := by
      rintro v₀ ⟨e, κ, hE, hκε, htend⟩
      have hκne : κ ≠ 0 := hE.2.1
      have hωk : (κ ^ ((k : ℂ)⁻¹)) ^ k = κ := Complex.cpow_nat_inv_pow κ hk.ne'
      have hωne : κ ^ ((k : ℂ)⁻¹) ≠ 0 := by
        intro hh
        exact hκne (by rw [← hωk, hh, zero_pow hk.ne'])
      have hnormk : ‖κ ^ ((k : ℂ)⁻¹)‖ ^ k = ‖κ‖ := by rw [← norm_pow, hωk]
      have hζω : ζ₀ < ‖κ ^ ((k : ℂ)⁻¹)‖ := lt_of_pow_lt_pow_left₀ k (norm_nonneg _)
        (by rw [hnormk]; exact lt_of_lt_of_le hζ₀k hκε)
      have hmem : (ζ₀ : ℂ) / (κ ^ ((k : ℂ)⁻¹)) ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
        rw [mem_ball_zero_sdiff_singleton']
        have hnorm : ‖(ζ₀ : ℂ) / (κ ^ ((k : ℂ)⁻¹))‖ = ζ₀ / ‖κ ^ ((k : ℂ)⁻¹)‖ := by
          rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hζ₀pos]
        rw [hnorm]
        refine ⟨div_pos hζ₀pos (norm_pos_iff.mpr hωne), ?_⟩
        exact (div_lt_one (norm_pos_iff.mpr hωne)).mpr hζω
      have hWmem : e ((ζ₀ : ℂ) / (κ ^ ((k : ℂ)⁻¹))) ∈ W := by
        refine ⟨(hE.2.2.1 _ hmem).1, ?_⟩
        rw [(hE.2.2.1 _ hmem).2, div_pow, hωk, mul_div_cancel₀ _ hκne]
      exact Set.mem_biUnion hWmem ⟨e, κ, hE, hκε, rfl, htend⟩
    exact Set.Countable.mono hcov (Set.Countable.biUnion hWc (fun p _ => (hVsub p).countable))
  · -- `k = 0` is impossible for chart data
    refine Set.Countable.mono ?_ Set.countable_empty
    rintro v₀ ⟨e, κ, hE, -, -⟩
    exact absurd hE.1 (by omega)

end

/-! ## The target theorem -/

/-- **Countably many `ψ₂`-limits of genuine punctures over a fixed `ψ₁`-limit (Rychlik §6 step 3,
second half).**  For a fixed `u₀`, the set of `v₀` such that there is a genuine punctured chart
`e` with `ψ₁`-limit `u₀` and `ψ₂ ∘ e → v₀` is countable.

Route.  The image of such a chart lies in one component of `⁰H ∩ ψ₁⁻¹(D)` for a small punctured
disc `D` around `u₀`; that component is an analytic sheet over `D` and `ψ₂` is an analytic function
of `ψ₁` on it (`⁰H` is a spread over the `ψ₁`-plane, `Work.EQ.H0_structure`), so it has at most one
finite limit at `u₀`.  The components of `⁰H ∩ ψ₁⁻¹(D)` form a disjoint family of open sets and
`⁰H` is second countable, so there are countably many of them.

**Proof as formalised** (the sketch above is not literally available: a chart of exponent `k ≥ 2`
has `e ζ ≠ e (ζ ω)` for a `k`-th root of unity `ω ≠ 1` even though `ψ₁` agrees at the two points, so
`ψ₁` is *not* injective on a component of `⁰H ∩ ψ₁⁻¹(D)`).  The argument below only uses the
rigidity of the spread and the countability of the `ψ₁`-fibres of `⁰H`:

* a chart of exponent `k` and scale `κ ≠ 0` is normalised by `ωᵏ = κ` (`ω = κ ^ (1/k : ℂ)`): the leg
  `ζ ↦ e (ζ / ω)` then satisfies `ψ₁ = u₀ + ζᵏ` (`Work.EQ.isChartData_normalized`), i.e. all charts of
  exponent `k` are parametrised lifts of one and the same map;
* two continuous legs of `⁰H` parametrised by the same `ψ₁`-map and agreeing at one parameter agree
  on the whole (preconnected) domain (`Work.EQ.sections_eqOn_of_preconnected`, the rigidity of the
  spread from `Work.EQ.H0_structure` clause 1);
* hence for `ε > 0` and `ζ₀ > 0` with `ζ₀ᵏ < ε`: the `ψ₂`-limit of a chart with `ε ≤ ‖κ‖` and
  exponent `k` depends only on the single chain `e (ζ₀ / ω) ∈ H0`, whose `ψ₁`-value is the *fixed*
  number `u₀ + ζ₀ᵏ`; by `Work.EQ.H0_countable_fibre` there are only countably many such chains, so
  for each `(k, ε)` only countably many limits occur (`countable_psi2_limits_kappa_bdd`);
* the countably many lower bounds `ε = (eqLam a)ⁿ` (which tend to `0` inside `(0,1)`) cover every
  `κ ≠ 0`, and `k` ranges over `ℕ` (`k = 0` is impossible for chart data), giving the union
  decomposition used in the proof of the theorem. -/
theorem countable_puncture_psi2_limits {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {h : ℂ → ℂ} {r : ℝ} (hh : IsStableGerm a h r) (u₀ : ℂ) :
    Set.Countable {v₀ : ℂ | ∃ (e : ℂ → ChainData) (k : ℕ),
      IsPuncturedChart a h e u₀ k ∧
      (¬ ∃ q ∈ H0 a h, Filter.Tendsto e (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds q)) ∧
      Filter.Tendsto (fun ζ : ℂ => (e ζ).2.2)
        (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ : Set ℂ)) (nhds v₀)} := by
  classical
  have hlam0 : 0 < eqLam a := eqLam_pos_of ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one_of ha0 ha1
  refine Set.Countable.mono ?_
    (Set.countable_iUnion (fun n : ℕ => Set.countable_iUnion (fun k : ℕ =>
      countable_psi2_limits_kappa_bdd ha0 ha1 hh u₀ k (pow_pos hlam0 n))))
  rintro v₀ ⟨e, k, hchart, hgen, htend⟩
  obtain ⟨hk, -, κ, hκ, heq, hinj, hcont, -, -⟩ := hchart
  have hkle : ∃ n : ℕ, (eqLam a) ^ n ≤ ‖κ‖ := by
    have hlim : Tendsto (fun n : ℕ => (eqLam a) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds (norm_pos_iff.mpr hκ))).exists
    exact ⟨n, le_of_lt hn⟩
  obtain ⟨n, hn⟩ := hkle
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨k,
    ⟨e, κ, ⟨hk, hκ, heq, hinj, hcont⟩, hn, htend⟩⟩⟩

end Work.EQ
