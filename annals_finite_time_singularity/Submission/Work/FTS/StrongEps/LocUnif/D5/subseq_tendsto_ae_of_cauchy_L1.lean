import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Order.Group.Lattice

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif.D5

open MeasureTheory Filter
open scoped ENNReal Topology

/-! ### Auxiliary measure-theoretic facts

These are the two general ingredients of the main theorem, proved here so that the file is
self-contained. -/

/-- If the successive differences of `u` are summable in the `L¹`-seminorm measured by `eLpNorm`,
then `u` converges almost everywhere. -/
theorem ae_tendsto_of_summable_eLpNorm_sub_aux {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {u : ℕ → α → ℝ}
    (hsum : (∑' n : ℕ, MeasureTheory.eLpNorm (fun x : α => u (n + 1) x - u n x) (1 : ENNReal) μ)
      ≠ ⊤) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Filter.Tendsto (fun n : ℕ => u n x) Filter.atTop (nhds L) := by
  have hnorm := MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top (μ := μ) (p := (1 : ENNReal))
    (f := fun n (x : α) => u (n + 1) x - u n x) le_rfl hsum
  filter_upwards [hnorm] with x hx
  have hs : Summable (fun n : ℕ => u (n + 1) x - u n x) := hx.of_norm
  have h1 : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (u (n + 1) x - u n x))
      Filter.atTop (nhds (∑' n : ℕ, (u (n + 1) x - u n x))) := hs.hasSum.tendsto_sum_nat
  have h2 : Filter.Tendsto (fun N : ℕ => u N x - u 0 x)
      Filter.atTop (nhds (∑' n : ℕ, (u (n + 1) x - u n x))) := by
    refine h1.congr' ?_
    filter_upwards with N
    exact Finset.sum_range_sub (fun n : ℕ => u n x) N
  refine ⟨u 0 x + ∑' n : ℕ, (u (n + 1) x - u n x), ?_⟩
  have h3 : Filter.Tendsto (fun N : ℕ => (u N x - u 0 x) + u 0 x) Filter.atTop
      (nhds ((∑' n : ℕ, (u (n + 1) x - u n x)) + u 0 x)) := h2.add tendsto_const_nhds
  have h4 : Filter.Tendsto (fun N : ℕ => u N x) Filter.atTop
      (nhds ((∑' n : ℕ, (u (n + 1) x - u n x)) + u 0 x)) := by
    refine h3.congr' ?_
    filter_upwards with N
    ring
  simpa [add_comm] using h4

/-- Fatou: an `L¹`-Cauchy sequence converging almost everywhere converges in `L¹` to its a.e.
limit (stated with `lintegral`s, so no integrability hypothesis is needed). -/
theorem lintegral_sub_le_of_tendsto_ae_of_cauchy_aux {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {u : ℕ → α → ℝ} {w : α → ℝ}
    (hu : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (u n) μ)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n : ℕ => u n x) Filter.atTop (nhds (w x)))
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ x, ENNReal.ofReal |u n x - u m x| ∂μ ≤ ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∫⁻ x, ENNReal.ofReal |u k x - w x| ∂μ ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy ε hε
  refine ⟨N, fun k hk => ?_⟩
  have hFatou : ∫⁻ x, Filter.liminf (fun j : ℕ => ENNReal.ofReal |u k x - u j x|) Filter.atTop ∂μ
      ≤ Filter.liminf (fun j : ℕ => ∫⁻ x, ENNReal.ofReal |u k x - u j x| ∂μ) Filter.atTop :=
    MeasureTheory.lintegral_liminf_le' (μ := μ) (u := Filter.atTop)
      (f := fun (j : ℕ) (x : α) => ENNReal.ofReal |u k x - u j x|)
      (fun j => (((hu k).aemeasurable.sub (hu j).aemeasurable).abs).ennreal_ofReal)
  have hae : ∀ᵐ x ∂μ, Filter.liminf (fun j : ℕ => ENNReal.ofReal |u k x - u j x|) Filter.atTop
      = ENNReal.ofReal |u k x - w x| := by
    filter_upwards [hlim] with x hx
    have h1 : Filter.Tendsto (fun j : ℕ => u k x - u j x) Filter.atTop (nhds (u k x - w x)) :=
      tendsto_const_nhds.sub hx
    have h2 : Filter.Tendsto (fun j : ℕ => ENNReal.ofReal |u k x - u j x|) Filter.atTop
        (nhds (ENNReal.ofReal |u k x - w x|)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp h1.abs
    exact h2.liminf_eq
  have hstep1 : ∫⁻ x, ENNReal.ofReal |u k x - w x| ∂μ
      ≤ ∫⁻ x, Filter.liminf (fun j : ℕ => ENNReal.ofReal |u k x - u j x|) Filter.atTop ∂μ :=
    MeasureTheory.lintegral_mono_ae (hae.mono fun x hx => le_of_eq hx.symm)
  refine le_trans hstep1 ?_
  have hev : ∀ᶠ j : ℕ in Filter.atTop,
      (∫⁻ x, ENNReal.ofReal |u k x - u j x| ∂μ) ≤ ENNReal.ofReal ε := by
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    rw [MeasureTheory.lintegral_congr (fun x => by rw [abs_sub_comm])]
    exact hN j k hj hk
  exact le_trans hFatou (Filter.liminf_le_of_frequently_le' hev.frequently)

theorem subseq_tendsto_ae_of_cauchy_L1 {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ] {W : ℕ → α → ℝ}
    (hW : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (W n) μ)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ x, ENNReal.ofReal |W n x - W m x| ∂μ ≤ ENNReal.ofReal ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : α → ℝ, Measurable w ∧
      (∀ᵐ x ∂μ, Filter.Tendsto (fun k : ℕ => W (φ k) x) Filter.atTop (nhds (w x))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
        ∫⁻ x, ENNReal.ofReal |W (φ k) x - w x| ∂μ ≤ ENNReal.ofReal ε) := by
  -- Step 1: extract a strictly monotone subsequence whose successive differences are summable.
  have hεpos : ∀ k : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 2) := fun k => by positivity
  let Nk : ℕ → ℕ := fun k => Classical.choose (hcauchy ((1 / 2 : ℝ) ^ (k + 2)) (hεpos k))
  have hNk : ∀ k : ℕ, ∀ n m : ℕ, Nk k ≤ n → Nk k ≤ m →
      ∫⁻ x, ENNReal.ofReal |W n x - W m x| ∂μ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2)) :=
    fun k => Classical.choose_spec (hcauchy ((1 / 2 : ℝ) ^ (k + 2)) (hεpos k))
  let φ : ℕ → ℕ := fun k => Nat.rec (Nk 0) (fun k ih => max (ih + 1) (Nk (k + 1))) k
  have hφ0 : φ 0 = Nk 0 := rfl
  have hφs : ∀ k : ℕ, φ (k + 1) = max (φ k + 1) (Nk (k + 1)) := fun k => rfl
  have hφlt : ∀ k : ℕ, φ k < φ (k + 1) := fun k => by
    rw [hφs]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hφge : ∀ k : ℕ, k ≤ φ k := by
    intro k
    induction k with
    | zero => simp [hφ0]
    | succ k ih => rw [hφs]; exact le_trans (Nat.succ_le_succ ih) (le_max_left _ _)
  have hφNk : ∀ k : ℕ, Nk k ≤ φ k := by
    intro k
    induction k with
    | zero => simp [hφ0]
    | succ k _ => rw [hφs]; exact le_max_right _ _
  have hstrict : StrictMono φ := strictMono_nat_of_lt_succ hφlt
  have hbnd : ∀ k : ℕ,
      ∫⁻ x, ENNReal.ofReal |W (φ (k + 1)) x - W (φ k) x| ∂μ
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2)) := by
    intro k
    exact hNk k (φ (k + 1)) (φ k) (le_trans (hφNk k) (le_of_lt (hφlt k))) (hφNk k)
  -- Step 2: the `L¹`-norms of the successive differences are summable.
  have hLp : ∀ k : ℕ,
      MeasureTheory.eLpNorm (fun x : α => W (φ (k + 1)) x - W (φ k) x) (1 : ENNReal) μ
        ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2)) := by
    intro k
    have h1 : MeasureTheory.eLpNorm (fun x : α => W (φ (k + 1)) x - W (φ k) x) (1 : ENNReal) μ
        = ∫⁻ x, ENNReal.ofReal |W (φ (k + 1)) x - W (φ k) x| ∂μ := by
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm
        (f := fun x : α => W (φ (k + 1)) x - W (φ k) x) ((hW (φ (k + 1))).sub (hW (φ k)))]
      exact MeasureTheory.lintegral_congr (fun x => Real.enorm_eq_ofReal_abs _)
    rw [h1]
    exact hbnd k
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have htsumgeom : (∑' k : ℕ, (1 / 2 : ℝ) ^ k) = 2 := by
    rw [tsum_geometric_of_norm_lt_one (show ‖(1 / 2 : ℝ)‖ < 1 by norm_num)]
    norm_num
  have hfingeom : (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) = ENNReal.ofReal 2 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hgeom, htsumgeom]
  have hle : (∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 2))) ≤ ENNReal.ofReal 2 := by
    rw [← hfingeom]
    refine ENNReal.tsum_le_tsum (fun k => ?_)
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
  have hsum_ne_top : (∑' k : ℕ,
      MeasureTheory.eLpNorm (fun x : α => W (φ (k + 1)) x - W (φ k) x) (1 : ENNReal) μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans (ENNReal.tsum_le_tsum hLp) hle)
  -- Step 3: a.e. convergence along the subsequence, and a measurable limit.
  have hu : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (fun x : α => W (φ n) x) μ :=
    fun n => hW (φ n)
  have hconv : ∀ᵐ x ∂μ, ∃ L : ℝ,
      Filter.Tendsto (fun k : ℕ => W (φ k) x) Filter.atTop (nhds L) :=
    ae_tendsto_of_summable_eLpNorm_sub_aux hsum_ne_top
  obtain ⟨w, hwsm, hwlim⟩ := exists_stronglyMeasurable_limit_of_tendsto_ae hu hconv
  refine ⟨φ, hstrict, w, hwsm.measurable, hwlim, ?_⟩
  -- Step 4: the tail of the subsequence converges in `L¹` to its a.e. limit (Fatou).
  have hcau' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ x, ENNReal.ofReal |W (φ n) x - W (φ m) x| ∂μ ≤ ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    exact ⟨N, fun n m hn hm => hN (φ n) (φ m) (le_trans hn (hφge n)) (le_trans hm (hφge m))⟩
  exact lintegral_sub_le_of_tendsto_ae_of_cauchy_aux hu hwlim hcau'

end Work.FTS.StrongEps.LocUnif.D5
