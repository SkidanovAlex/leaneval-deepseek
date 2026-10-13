import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25Aux

/-- **Uniform smallness out of pointwise smallness plus an equi-Lipschitz bound.**

Given a family `F z θ` that is (i) pointwise in `θ` tending to `0` as `z → ∞` and
(ii) Lipschitz in `θ` with a constant `K` *independent of* `z`, on the compact
interval `[a,b]`, the convergence is uniform: eventually in `z` all values on
`[a,b]` are `≤ ε` in absolute value.

Proof: cover the compact interval `[a,b]` by finitely many balls of radius
`δ = ε / (2 (K+1))` (centred at points of `[a,b]`).  For each centre `θᵢ` the
pointwise convergence gives `|F z θᵢ| < ε/2` eventually, and there are finitely
many centres, so eventually this holds simultaneously for all of them.  For an
arbitrary `θ ∈ [a,b]` pick a centre `θᵢ` with `|θ - θᵢ| ≤ δ` and split
`|F z θ| ≤ |F z θ - F z θᵢ| + |F z θᵢ| ≤ K δ + ε/2 ≤ ε`, using
`K δ = K ε / (2(K+1)) ≤ ε/2` (valid since `K ≥ 0`).  (The hypothesis `hab` is
not needed: for `a > b` the interval is empty and the claim is vacuous.) -/
theorem eventually_uniform_abs_le {F : ℝ → ℝ → ℝ} {K a b ε : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K)
    (hlip : ∀ z, ∀ θ ∈ Set.Icc a b, ∀ θ' ∈ Set.Icc a b, |F z θ - F z θ'| ≤ K * |θ - θ'|)
    (hpt : ∀ θ ∈ Set.Icc a b, Filter.Tendsto (fun z => F z θ) Filter.atTop (nhds 0)) (hε : 0 < ε) :
    ∀ᶠ z in Filter.atTop, ∀ θ ∈ Set.Icc a b, |F z θ| ≤ ε := by
  -- `a ∈ [a,b]` (this is the only use of `hab`; the argument also works for the empty interval).
  have hmem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  -- The mesh size of the finite cover, chosen so that `K δ ≤ ε/2`.
  set δ : ℝ := ε / (2 * (K + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; positivity
  have hKδ : K * δ ≤ ε / 2 := by
    rw [hδdef]
    field_simp
    nlinarith
  -- Cover `[a,b]` by finitely many δ-balls centred at points of `[a,b]`.
  obtain ⟨t, ht_sub, ht_fin, ht_cov⟩ :=
    finite_cover_balls_of_compact (s := Set.Icc a b) isCompact_Icc hδpos
  -- Simultaneously, for all centres, `|F z θᵢ| < ε/2` eventually.
  have hcov : ∀ᶠ z in Filter.atTop, ∀ i ∈ t, |F z i| < ε / 2 := by
    rw [Set.Finite.eventually_all ht_fin]
    intro i hi
    have hp : ∀ᶠ y in nhds (0 : ℝ), |y| < ε / 2 :=
      IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) (by simp; positivity)
    exact (hpt i (ht_sub hi)).eventually hp
  filter_upwards [hcov] with z hz
  intro θ hθ
  -- Pick a centre `i` of the cover with `θ` in its ball.
  rcases Set.mem_iUnion₂.mp (ht_cov hθ) with ⟨i, hi, hiθ⟩
  have hdist : |θ - i| ≤ δ := by
    rw [Metric.mem_ball, Real.dist_eq] at hiθ
    linarith
  have h1 : |F z θ| ≤ |F z θ - F z i| + |F z i| := by
    have := dist_triangle (F z θ) (F z i) 0
    simpa [Real.dist_eq, sub_zero] using this
  calc |F z θ| ≤ |F z θ - F z i| + |F z i| := h1
    _ ≤ K * δ + ε / 2 := add_le_add
        ((hlip z θ hθ i (ht_sub hi)).trans (mul_le_mul_of_nonneg_left hdist hK))
        (le_of_lt (hz i hi))
    _ ≤ ε / 2 + ε / 2 := add_le_add hKδ le_rfl
    _ = ε := by ring

end Work.FTS_StreamBdry.SB25Aux
