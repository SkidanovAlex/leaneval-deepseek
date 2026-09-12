import Mathlib

/-! # Metric foundations for the Hopf–Rinow proof

Pure metric-space theory, no Riemannian structure.  We study paths which are
*locally linear* (locally the `edist` between images equals a constant times
the parameter distance), exactly as in the challenge's `IsGeodesicallyComplete`.

Central results, proved by pure metric arguments:
* a locally linear path is globally `c`-Lipschitz on `(a,b)` (bounded by `c`
  times the parameter distance); hence it is continuous, and uniformly Cauchy
  near the endpoints.
-/

open scoped ENNReal
open Set Filter Metric

namespace Submission.Metric

/-- `γ` is locally linear with speed `c` on the open interval `(a,b)`: around each
`t₀ ∈ (a,b)` there is a window inside `(a,b)` on which the edist between images is
`c` times the parameter distance. -/
def IsLocLinear {M : Type*} [PseudoEMetricSpace M] (a b : ℝ) (c : NNReal) (γ : ℝ → M) : Prop :=
  ∀ t₀ ∈ Ioo a b, ∃ δ > (0 : ℝ),
    ∀ s t : ℝ,
      s ∈ Ioo (max a (t₀ - δ)) (min b (t₀ + δ)) →
      t ∈ Ioo (max a (t₀ - δ)) (min b (t₀ + δ)) →
      edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s|

namespace IsLocLinear

variable {M : Type*} [PseudoEMetricSpace M] {a b : ℝ} {c : NNReal} {γ : ℝ → M}

lemma window_mem_iff {t₀ δ s : ℝ} (hs : s ∈ Ioo a b) (hδ : 0 < δ) :
    s ∈ Ioo (max a (t₀ - δ)) (min b (t₀ + δ)) ↔ t₀ - δ < s ∧ s < t₀ + δ := by
  constructor
  · intro h
    constructor
    · exact lt_of_le_of_lt (le_max_right a (t₀ - δ)) h.1
    · exact lt_of_lt_of_le h.2 (min_le_right b (t₀ + δ))
  · intro h
    constructor
    · exact max_lt hs.1 h.1
    · exact lt_min hs.2 h.2

lemma mem_window_self {t₀ δ : ℝ} (ht : t₀ ∈ Ioo a b) (hδ : 0 < δ) :
    t₀ ∈ Ioo (max a (t₀ - δ)) (min b (t₀ + δ)) := by
  constructor
  · exact max_lt ht.1 (by linarith)
  · exact lt_min ht.2 (by linarith)

/-- Sum of `N` equal ENNReal terms of the form `c * ofReal step`. -/
lemma sum_const_enreal (N : ℕ) (c : NNReal) (step : ℝ) :
    (∑ i ∈ Finset.range N, ((c : ℝ≥0∞) * ENNReal.ofReal step)) =
      (c : ℝ≥0∞) * ENNReal.ofReal ((N : ℝ) * step) := by
  rw [Finset.sum_const, Finset.card_range]
  rw [nsmul_eq_mul]
  have hN : (N : ℝ≥0∞) = ENNReal.ofReal (N : ℝ) := by
    rw [← ENNReal.ofReal_natCast]
  calc
    (N : ℝ≥0∞) * ((c : ℝ≥0∞) * ENNReal.ofReal step)
        = ENNReal.ofReal (N : ℝ) * ((c : ℝ≥0∞) * ENNReal.ofReal step) := by rw [hN]
    _ = (c : ℝ≥0∞) * (ENNReal.ofReal (N : ℝ) * ENNReal.ofReal step) := by ring
    _ = (c : ℝ≥0∞) * ENNReal.ofReal ((N : ℝ) * step) := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (N:ℝ))]

/-- The global `c`-Lipschitz bound: for `u ≤ v` both in `(a,b)`,
`edist (γ u) (γ v) ≤ c * (v-u)`. -/
lemma edist_le_of_le (hγ : IsLocLinear a b c γ) {u v : ℝ} (hu : u ∈ Ioo a b)
    (hv : v ∈ Ioo a b) (huv : u ≤ v) :
    edist (γ u) (γ v) ≤ (c : ℝ≥0∞) * ENNReal.ofReal (v - u) := by
  classical
  by_cases huv' : u = v
  · subst v; simp
  have hlt : u < v := lt_of_le_of_ne huv huv'
  let s : Set ℝ := Icc u v
  have hs_compact : IsCompact s := isCompact_Icc
  let ι := {x : ℝ // x ∈ s}
  let hγ' : ∀ x : ι, ∃ δ, δ > 0 ∧ ∀ s t : ℝ,
      s ∈ Ioo (max a (x.1 - δ)) (min b (x.1 + δ)) →
      t ∈ Ioo (max a (x.1 - δ)) (min b (x.1 + δ)) →
      edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
    intro x
    exact hγ x.1 (by
      have hxu : u ≤ x.1 := x.2.1
      have hxv : x.1 ≤ v := x.2.2
      exact ⟨lt_of_lt_of_le hu.1 hxu, lt_of_le_of_lt hxv hv.2⟩)
  let δx : ι → ℝ := fun x => Classical.choose (hγ' x)
  let W : ι → Set ℝ := fun x => Ioo (max a (x.1 - δx x)) (min b (x.1 + δx x))
  have hδx_pos : ∀ x : ι, 0 < δx x := by
    intro x
    exact (Classical.choose_spec (hγ' x)).1
  have hδx_spec : ∀ x : ι, ∀ s t : ℝ,
      s ∈ W x → t ∈ W x →
      edist (γ s) (γ t) = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
    intro x
    exact (Classical.choose_spec (hγ' x)).2
  have hW_open : ∀ x : ι, IsOpen (W x) := by
    intro x; exact isOpen_Ioo
  have hcover : s ⊆ ⋃ x : ι, W x := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
    exact mem_window_self (a := a) (b := b) (t₀ := x) (δ := δx ⟨x, hx⟩)
      (by
        have hxu : u ≤ x := hx.1
        have hxv : x ≤ v := hx.2
        exact ⟨lt_of_lt_of_le hu.1 hxu, lt_of_le_of_lt hxv hv.2⟩)
      (hδx_pos ⟨x, hx⟩)
  rcases lebesgue_number_lemma_of_metric (α := ℝ) hs_compact hW_open hcover with ⟨δ, hδ, hleb⟩
  have hpos : 0 < (v - u) / δ := div_pos (sub_pos.mpr hlt) hδ
  rcases exists_nat_gt ((v - u) / δ) with ⟨N, hN⟩
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hpos (le_of_lt hN)
  have hNstep : (N : ℝ) * ((v - u) / (N : ℝ)) = v - u := by
    field_simp [ne_of_gt hN0]
  let step : ℝ := (v - u) / (N : ℝ)
  have hstep_pos : 0 < step := by
    dsimp [step]; exact div_pos (sub_pos.mpr hlt) hN0
  have hstepδ : step < δ := by
    dsimp [step]
    rw [div_lt_iff₀ hN0]
    exact (by simpa [mul_comm] using (div_lt_iff₀ hδ).mp hN)
  let x : ℕ → ℝ := fun k => u + (k : ℝ) * step
  have hx0 : x 0 = u := by simp [x]
  have hxN : x N = v := by
    dsimp [x, step]
    field_simp [ne_of_gt hN0]
    ring
  have hx_step {k : ℕ} (hk : k < N) : |x (k + 1) - x k| = step := by
    have hk1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by norm_num
    have : x (k + 1) - x k = step := by
      dsimp [x]
      rw [hk1]
      ring
    have hnonneg : 0 ≤ x (k + 1) - x k := by
      rw [this]; exact le_of_lt hstep_pos
    rw [abs_of_nonneg hnonneg, this]
  have hx_ge_u {k : ℕ} : u ≤ x k := by
    dsimp [x]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ)) (le_of_lt hstep_pos)]
  have hx_le_v {k : ℕ} (hk : k ≤ N) : x k ≤ v := by
    have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    have hb : (k : ℝ) * ((v - u) / (N : ℝ)) ≤ v - u := by
      calc
        (k : ℝ) * ((v - u) / (N : ℝ)) ≤ (N : ℝ) * ((v - u) / (N : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hk' (le_of_lt (div_pos (sub_pos.mpr hlt) hN0))
        _ = v - u := hNstep
    dsimp [x, step]
    nlinarith
  have hpiece (k : ℕ) (hk : k < N) :
      edist (γ (x k)) (γ (x (k + 1))) = (c : ℝ≥0∞) * ENNReal.ofReal step := by
    have hxk_in_s : x k ∈ s := ⟨hx_ge_u, hx_le_v (le_of_lt hk)⟩
    rcases hleb (x k) hxk_in_s with ⟨j, hj⟩
    have hxk1_ball : x (k + 1) ∈ ball (x k) δ := by
      rw [mem_ball]
      rw [Real.dist_eq]
      rw [hx_step hk]
      exact hstepδ
    have hxj : x k ∈ W j := hj (mem_ball_self hδ)
    have hxj1 : x (k + 1) ∈ W j := hj hxk1_ball
    have hw := hδx_spec j (x k) (x (k + 1)) hxj hxj1
    rw [hx_step hk] at hw
    exact hw
  have hchain : edist (γ (x 0)) (γ (x N)) ≤
      ∑ i ∈ Finset.range N, ((c : ℝ≥0∞) * ENNReal.ofReal step) := by
    exact edist_le_range_sum_of_edist_le (f := fun k => γ (x k)) N
      (d := fun _ => (c : ℝ≥0∞) * ENNReal.ofReal step) (fun {k} hk => le_of_eq (hpiece k hk))
  calc
    edist (γ u) (γ v) = edist (γ (x 0)) (γ (x N)) := by rw [hx0, hxN]
    _ ≤ ∑ i ∈ Finset.range N, ((c : ℝ≥0∞) * ENNReal.ofReal step) := hchain
    _ = (c : ℝ≥0∞) * ENNReal.ofReal ((N : ℝ) * step) := sum_const_enreal N c step
    _ = (c : ℝ≥0∞) * ENNReal.ofReal (v - u) := by
      congr 1
      dsimp [step]
      rw [hNstep]

/-- The global `c`-Lipschitz bound with absolute value (un-ordered version). -/
lemma edist_le (hγ : IsLocLinear a b c γ) {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    edist (γ s) (γ t) ≤ (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
  by_cases hst : s ≤ t
  · have := edist_le_of_le hγ hs ht hst
    convert this using 1
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]
  · have h := edist_le_of_le hγ ht hs (le_of_not_ge hst)
    calc
      edist (γ s) (γ t) = edist (γ t) (γ s) := edist_comm (γ s) (γ t)
      _ ≤ (c : ℝ≥0∞) * ENNReal.ofReal (s - t) := h
      _ = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
        congr 1
        have hts_neg : t - s < 0 := sub_neg.mpr (lt_of_not_ge hst)
        rw [abs_of_neg hts_neg]
        ring

/-- `c * ofReal x` can be made `< ε` by taking `x` small enough (when `0 ≤ x`). -/
lemma exists_lt_of_mul_ofReal {ε : ℝ≥0∞} (hε : 0 < ε) (c : NNReal) :
    ∃ δ > (0 : ℝ), ∀ x : ℝ, 0 ≤ x → x < δ → (c : ℝ≥0∞) * ENNReal.ofReal x < ε := by
  by_cases hc : c = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx0 hx
    simpa [hc]
  by_cases hεtop : ε = ⊤
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx0 hx
    rw [hεtop]
    apply ENNReal.mul_lt_top
    · exact ENNReal.coe_lt_top
    · exact ENNReal.ofReal_lt_top
  · have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hc)
    have hr : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) hεtop
    let δ : ℝ := ε.toReal / (2 * (c : ℝ))
    have hden : (0 : ℝ) < 2 * (c : ℝ) := by positivity
    have hδpos : 0 < δ := div_pos hr hden
    refine ⟨δ, hδpos, ?_⟩
    intro x hx0 hx
    have hmono : (c : ℝ≥0∞) * ENNReal.ofReal x ≤ (c : ℝ≥0∞) * ENNReal.ofReal δ := by
      exact mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (le_of_lt hx)) bot_le bot_le
    have hc' : (c : ℝ≥0∞) = ENNReal.ofReal (c : ℝ) := by
      rw [ENNReal.ofReal_coe_nnreal]
    calc
      (c : ℝ≥0∞) * ENNReal.ofReal x ≤ (c : ℝ≥0∞) * ENNReal.ofReal δ := hmono
      _ = ENNReal.ofReal ((c : ℝ) * δ) := by
        rw [hc', ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (c : ℝ) from c.2)]
      _ = ENNReal.ofReal (ε.toReal / 2) := by
        congr 1
        dsimp [δ]
        field_simp [ne_of_gt hcpos]
      _ < ε := by
        rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity : 0 ≤ ε.toReal / 2) hεtop]
        linarith
/-- Restricting the interval preserves local linearity. -/
lemma restrict (hγ : IsLocLinear a b c γ) {a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    IsLocLinear a' b' c γ := by
  intro t₀ ht₀
  rcases hγ t₀ ⟨lt_of_le_of_lt ha ht₀.1, lt_of_lt_of_le ht₀.2 hb⟩ with ⟨δ, hδ, hwin⟩
  refine ⟨δ, hδ, ?_⟩
  intro s t hs ht
  have hs_in : s ∈ Ioo (max a (t₀ - δ)) (min b (t₀ + δ)) := by
    constructor
    · exact lt_of_le_of_lt (max_le_max ha le_rfl) hs.1
    · exact lt_of_lt_of_le hs.2 (min_le_min hb le_rfl)
  have ht_in : t ∈ Ioo (max a (t₀ - δ)) (min b (t₀ + δ)) := by
    constructor
    · exact lt_of_le_of_lt (max_le_max ha le_rfl) ht.1
    · exact lt_of_lt_of_le ht.2 (min_le_min hb le_rfl)
  exact hwin s t hs_in ht_in



end IsLocLinear
end Submission.Metric
