import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit

open MeasureTheory
open Filter

/-- **Diagonal selection.**  From the two-variable convergence of the weighted squared
differences to `0` one extracts a strictly increasing `φ : ℕ → ℕ` along which the *consecutive*
weighted `L²`-differences are dominated by the summable (indeed geometrically decaying) sequence
`((1/2)^{k+1})²`.

At stage `k` the hypothesis produces a threshold `N k` beyond which the weighted squared
difference is `< ((1/2)^{k+1})²`; the running maximum `M k = max_{j ≤ k} N j` is monotone, and
`φ k = M k + k` is strictly increasing while still exceeding the threshold `N k` at *both*
indices `φ k` and `φ (k+1)`. -/
theorem exists_strictMono_geometric_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {v : ℕ → α → ℝ} {g : α → ℝ}
    (hconv : Filter.Tendsto (fun nm : ℕ × ℕ =>
        ∫ x, (v nm.1 x - v nm.2 x) ^ 2 * g x ∂μ)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ k, (∫ x, (v (φ (k + 1)) x - v (φ k) x) ^ 2 * g x ∂μ)
        ≤ ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 := by
  have hε : ∀ k : ℕ, (0 : ℝ) < ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 := fun k => by positivity
  have hex : ∀ k : ℕ, ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      (∫ x, (v n x - v m x) ^ 2 * g x ∂μ) ≤ ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 := by
    intro k
    have hev : ∀ᶠ nm : ℕ × ℕ in (Filter.atTop ×ˢ Filter.atTop),
        (∫ x, (v nm.1 x - v nm.2 x) ^ 2 * g x ∂μ) < ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 := by
      filter_upwards [hconv.eventually (Metric.ball_mem_nhds (0 : ℝ) (hε k))] with nm hnm
      have h1 : dist (∫ x, (v nm.1 x - v nm.2 x) ^ 2 * g x ∂μ) 0
          < ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 := hnm
      rw [dist_zero_right, Real.norm_eq_abs, abs_lt] at h1
      exact h1.2
    rw [Filter.eventually_prod_iff] at hev
    obtain ⟨pa, hpa, pb, hpb, hprod⟩ := hev
    rw [Filter.eventually_atTop] at hpa hpb
    obtain ⟨N1, hN1⟩ := hpa
    obtain ⟨N2, hN2⟩ := hpb
    exact ⟨max N1 N2, fun n m hn hm =>
      le_of_lt (hprod (hN1 n (le_trans (le_max_left _ _) hn))
        (hN2 m (le_trans (le_max_right _ _) hm)))⟩
  choose N hN using hex
  set M : ℕ → ℕ := fun k => (Finset.range (k + 1)).sup N with hMdef
  have hMmono : Monotone M := by
    intro a b hab
    rw [hMdef]
    simp only
    refine Finset.sup_le fun c hc => Finset.le_sup ?_
    simp only [Finset.mem_range] at hc ⊢
    omega
  have hMN : ∀ k, N k ≤ M k := by
    intro k
    rw [hMdef]
    exact Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self k))
  refine ⟨fun k => M k + k, ?_, ?_⟩
  · refine strictMono_nat_of_lt_succ fun k => ?_
    have h : M k ≤ M (k + 1) := hMmono (Nat.le_add_right k 1)
    omega
  · intro k
    have h1 : N k ≤ M k := hMN k
    have h2 : N k ≤ M (k + 1) := le_trans (hMN k) (hMmono (Nat.le_add_right k 1))
    exact hN k (M (k + 1) + (k + 1)) (M k + k) (by omega) (by omega)

/-- **Almost-everywhere convergence from geometrically decaying weighted `L²`-differences.**
If the consecutive differences of the sequence `k ↦ v (φ k)` have weighted `L²`-norm (`L²(g dμ)`)
bounded by the geometric sequence `(1/2)^{k+1}`, then the sequence converges `μ`-almost everywhere.

The point is that the *norms* of the summands are summable, so by
`MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top` the `√g`-weighted differences are absolutely
summable a.e.; dividing by the a.e. positive `√g` gives absolute summability of the differences
themselves, and the telescoping series converges.  The limit is `AEStronglyMeasurable` as an a.e.
limit of the `AEStronglyMeasurable` functions `v (φ k)`. -/
theorem ae_tendsto_of_geometric_weighted {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {v : ℕ → α → ℝ} {g : α → ℝ} {φ : ℕ → ℕ}
    (hgpos : ∀ᵐ x ∂μ, 0 < g x) (hgmeas : AEMeasurable g μ)
    (hvmeas : ∀ n, AEStronglyMeasurable (v n) μ)
    (hint : ∀ k, Integrable (fun x => (v (φ (k + 1)) x - v (φ k) x) ^ 2 * g x) μ)
    (hbd : ∀ k, (∫ x, (v (φ (k + 1)) x - v (φ k) x) ^ 2 * g x ∂μ)
        ≤ ((1 / 2 : ℝ) ^ (k + 1)) ^ 2) :
    ∃ u : α → ℝ, (∀ᵐ x ∂μ, Filter.Tendsto (fun k => v (φ k) x) Filter.atTop (nhds (u x)))
      ∧ AEStronglyMeasurable u μ := by
  set D : ℕ → α → ℝ := fun k x => (v (φ (k + 1)) x - v (φ k) x) * Real.sqrt (g x) with hDdef
  have hw_sm : AEStronglyMeasurable (fun x => Real.sqrt (g x)) μ :=
    hgmeas.sqrt.aestronglyMeasurable
  have hDsm : ∀ k, AEStronglyMeasurable (D k) μ := by
    intro k
    rw [hDdef]
    exact ((hvmeas (φ (k + 1))).sub (hvmeas (φ k))).mul hw_sm
  have hEq : ∀ k, (fun x => (D k x) ^ 2) =ᵐ[μ]
      (fun x => (v (φ (k + 1)) x - v (φ k) x) ^ 2 * g x) := by
    intro k
    filter_upwards [hgpos] with x hx
    rw [hDdef, mul_pow, Real.sq_sqrt hx.le]
  have hDint : ∀ k, Integrable (fun x => (D k x) ^ 2) μ :=
    fun k => (hint k).congr (hEq k).symm
  have hDmem : ∀ k, MemLp (D k) 2 μ :=
    fun k => (memLp_two_iff_integrable_sq (hDsm k)).mpr (hDint k)
  have hnormeq : ∀ k, (∫ x, ‖D k x‖ ^ 2 ∂μ)
      = (∫ x, (v (φ (k + 1)) x - v (φ k) x) ^ 2 * g x ∂μ) := by
    intro k
    rw [← integral_congr_ae (hEq k)]
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.norm_eq_abs, sq_abs]
  have hnorm : ∀ k, eLpNorm (D k) 2 μ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) := by
    intro k
    have heq : eLpNorm (D k) 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, ‖D k x‖ ^ 2 ∂μ)) := by
      rw [(hDmem k).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      congr 1
      rw [show (2 : ENNReal).toReal = 2 by norm_num,
        show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
      simp only [Real.rpow_natCast]
    rw [heq]
    apply ENNReal.ofReal_le_ofReal
    rw [hnormeq k]
    calc Real.sqrt (∫ x, (v (φ (k + 1)) x - v (φ k) x) ^ 2 * g x ∂μ)
        ≤ Real.sqrt (((1 / 2 : ℝ) ^ (k + 1)) ^ 2) := Real.sqrt_le_sqrt (hbd k)
      _ = (1 / 2 : ℝ) ^ (k + 1) := Real.sqrt_sq (by positivity)
  have hsum : (∑' k, eLpNorm (D k) 2 μ) ≠ ⊤ := by
    have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
      simpa [pow_succ, mul_comm] using
        (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left (1 / 2 : ℝ)
    have htsum : (∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)))
        = ENNReal.ofReal (∑' k, (1 / 2 : ℝ) ^ (k + 1)) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hgeom).symm
    have hle : (∑' k, eLpNorm (D k) 2 μ) ≤ ENNReal.ofReal (∑' k, (1 / 2 : ℝ) ^ (k + 1)) := by
      rw [← htsum]
      exact ENNReal.tsum_le_tsum hnorm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hae_sum : ∀ᵐ x ∂μ, Summable (fun k => ‖D k x‖) :=
    MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top (p := 2) (by norm_num) hsum
  have hae_sum_d : ∀ᵐ x ∂μ, Summable (fun k => v (φ (k + 1)) x - v (φ k) x) := by
    filter_upwards [hgpos, hae_sum] with x hx hxsum
    have hs : Real.sqrt (g x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
    have h1 : (fun k => ‖D k x‖) =
        (fun k => Real.sqrt (g x) * |v (φ (k + 1)) x - v (φ k) x|) := by
      funext k
      rw [hDdef, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg (g x))]
      ring
    have hsum1 : Summable (fun k => Real.sqrt (g x) * |v (φ (k + 1)) x - v (φ k) x|) := by
      rw [← h1]; exact hxsum
    exact ((summable_mul_left_iff hs).mp hsum1).of_abs
  have hae_lim : ∀ᵐ x ∂μ, Tendsto (fun K => v (φ K) x) atTop
      (nhds (v (φ 0) x + ∑' k, (v (φ (k + 1)) x - v (φ k) x))) := by
    filter_upwards [hae_sum_d] with x hx
    have h1 : Tendsto (fun K => ∑ i ∈ Finset.range K, (v (φ (i + 1)) x - v (φ i) x)) atTop
        (nhds (∑' k, (v (φ (k + 1)) x - v (φ k) x))) := hx.hasSum.tendsto_sum_nat
    refine (h1.const_add (v (φ 0) x)).congr' (Eventually.of_forall fun K => ?_)
    rw [Finset.sum_range_sub (fun i => v (φ i) x) K]
    ring
  exact ⟨fun x => v (φ 0) x + ∑' k, (v (φ (k + 1)) x - v (φ k) x), hae_lim,
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => hvmeas (φ k)) hae_lim⟩

/-- **Fatou's lemma for the weighted `L²`-bound.**  If the `v n` are integrable against `g dμ` with
uniform bound `B` and the subsequence `v (φ k)` converges `μ`-almost everywhere to `u`, then
`u² g` is integrable and `∫ u² g dμ ≤ B`.  (Fatou applied to the `ℝ≥0∞`-valued integrands
`ENNReal.ofReal ((v (φ k))² g)`; the `ℝ≥0∞`-integral of the limit is rewritten with
`ofReal_integral_eq_lintegral_ofReal`.) -/
theorem fatou_weighted_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {v : ℕ → α → ℝ} {g : α → ℝ} {B : ℝ} {φ : ℕ → ℕ} {u : α → ℝ}
    (hgpos : ∀ᵐ x ∂μ, 0 < g x) (hgmeas : AEMeasurable g μ)
    (hvmeas : ∀ n, AEStronglyMeasurable (v n) μ)
    (hint : ∀ n, Integrable (fun x => (v n x) ^ 2 * g x) μ)
    (hb : ∀ n, (∫ x, (v n x) ^ 2 * g x ∂μ) ≤ B)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun k => v (φ k) x) Filter.atTop (nhds (u x))) :
    Integrable (fun x => (u x) ^ 2 * g x) μ ∧
      (∫ x, (u x) ^ 2 * g x ∂μ) ≤ B := by
  have hu_sm : AEStronglyMeasurable u μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => hvmeas (φ k)) hlim
  have hFmeas : ∀ k, AEMeasurable (fun x => ENNReal.ofReal ((v (φ k) x) ^ 2 * g x)) μ :=
    fun k => (((hvmeas (φ k)).aemeasurable.pow_const 2).mul hgmeas).ennreal_ofReal
  have hnn_v : ∀ k, 0 ≤ᵐ[μ] fun x => (v (φ k) x) ^ 2 * g x :=
    fun k => hgpos.mono fun x hx => mul_nonneg (sq_nonneg _) hx.le
  have hbnd : ∀ k, (∫⁻ x, ENNReal.ofReal ((v (φ k) x) ^ 2 * g x) ∂μ) ≤ ENNReal.ofReal B := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hint (φ k)) (hnn_v k)]
    exact ENNReal.ofReal_le_ofReal (hb (φ k))
  have hlimF : ∀ᵐ x ∂μ, Tendsto (fun k => ENNReal.ofReal ((v (φ k) x) ^ 2 * g x)) atTop
      (nhds (ENNReal.ofReal ((u x) ^ 2 * g x))) := by
    filter_upwards [hlim] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp (((hx.pow 2).mul_const (g x)))
  have hFatou : (∫⁻ x, liminf (fun k => ENNReal.ofReal ((v (φ k) x) ^ 2 * g x)) atTop ∂μ)
      ≤ liminf (fun k => ∫⁻ x, ENNReal.ofReal ((v (φ k) x) ^ 2 * g x) ∂μ) atTop :=
    lintegral_liminf_le' (u := atTop) hFmeas
  have hLHS : (∫⁻ x, ENNReal.ofReal ((u x) ^ 2 * g x) ∂μ)
      ≤ (∫⁻ x, liminf (fun k => ENNReal.ofReal ((v (φ k) x) ^ 2 * g x)) atTop ∂μ) :=
    lintegral_mono_ae (hlimF.mono fun x hx => le_of_eq hx.liminf_eq.symm)
  have hRHS : (liminf (fun k => ∫⁻ x, ENNReal.ofReal ((v (φ k) x) ^ 2 * g x) ∂μ) atTop)
      ≤ ENNReal.ofReal B :=
    liminf_le_of_frequently_le' (Eventually.of_forall hbnd).frequently
  have hfin : (∫⁻ x, ENNReal.ofReal ((u x) ^ 2 * g x) ∂μ) < ⊤ :=
    lt_of_le_of_lt (le_trans hLHS (le_trans hFatou hRHS)) ENNReal.ofReal_lt_top
  have hnn_u : 0 ≤ᵐ[μ] fun x => (u x) ^ 2 * g x :=
    hgpos.mono fun x hx => mul_nonneg (sq_nonneg _) hx.le
  have hBnn : 0 ≤ B := le_trans (integral_nonneg_of_ae (hgpos.mono fun x hx =>
      mul_nonneg (sq_nonneg _) hx.le)) (hb 0)
  have hfinint : Integrable (fun x => (u x) ^ 2 * g x) μ := by
    refine ⟨hu_sm.aemeasurable.pow_const 2 |>.mul hgmeas |>.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn_u]
    exact hfin
  refine ⟨hfinint, ?_⟩
  have h2 : ENNReal.ofReal (∫ x, (u x) ^ 2 * g x ∂μ) ≤ ENNReal.ofReal B := by
    rw [ofReal_integral_eq_lintegral_ofReal hfinint hnn_u]
    exact le_trans hLHS (le_trans hFatou hRHS)
  exact (ENNReal.ofReal_le_ofReal_iff hBnn).mp h2

/-- **Almost-everywhere extraction from an `L²`-Cauchy family bounded in `L²`.**  A sequence `v n`
that is uniformly bounded in `L²(g dμ)` and Cauchy in `L²(g dμ)` (stated as the two-variable limit
of the squared differences) has a strictly monotone subsequence converging `μ`-almost everywhere
to a limit `u` whose `L²(g dμ)`-norm is still bounded by the same bound.  The positivity of the
weight `g` a.e. is needed: the convergence is first obtained `g dμ`-a.e. and `μ`-a.e. follows from
it. -/
theorem exists_subseq_ae_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {v : ℕ → α → ℝ} {g : α → ℝ} {B : ℝ}
    (hgpos : ∀ᵐ x ∂μ, 0 < g x) (hgmeas : AEMeasurable g μ)
    (hvmeas : ∀ n, AEStronglyMeasurable (v n) μ)
    (hint : ∀ n, Integrable (fun x => (v n x) ^ 2 * g x) μ)
    (hint2 : ∀ n m, Integrable (fun x => (v n x - v m x) ^ 2 * g x) μ)
    (hb : ∀ n, (∫ x, (v n x) ^ 2 * g x ∂μ) ≤ B)
    (hconv : Filter.Tendsto (fun nm : ℕ × ℕ =>
        ∫ x, (v nm.1 x - v nm.2 x) ^ 2 * g x ∂μ)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0)) :
    ∃ (φ : ℕ → ℕ) (u : α → ℝ), StrictMono φ ∧
      (∀ᵐ x ∂μ, Filter.Tendsto (fun k => v (φ k) x) Filter.atTop (nhds (u x))) ∧
      Integrable (fun x => (u x) ^ 2 * g x) μ ∧
      (∫ x, (u x) ^ 2 * g x ∂μ) ≤ B := by
  -- Step 1: extract a strictly increasing subsequence along which the weighted `L²`-differences
  -- of consecutive terms decay geometrically.
  obtain ⟨φ, hφ, hbd⟩ := exists_strictMono_geometric_L2 (v := v) (g := g) hconv
  -- Step 2: those differences are then absolutely summable `μ`-a.e., so the sequence converges.
  have hintφ : ∀ k, Integrable (fun x => (v (φ (k + 1)) x - v (φ k) x) ^ 2 * g x) μ :=
    fun k => hint2 _ _
  obtain ⟨u, hu, _husm⟩ := ae_tendsto_of_geometric_weighted hgpos hgmeas hvmeas hintφ hbd
  -- Step 3: Fatou gives the `L²(g dμ)`-bound for the limit (and its integrability).
  obtain ⟨huint, hub⟩ := fatou_weighted_sq_le hgpos hgmeas hvmeas hint hb hu
  exact ⟨φ, u, hφ, hu, huint, hub⟩

end Work.FTS.PhiStar.Honesty.SlotsLimit
