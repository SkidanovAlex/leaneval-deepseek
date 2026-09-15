import Submission.FUP.HilbertLine
import Submission.Commons.Algebra.BigOperators.geom_sum_le_div_sub_one
import Submission.Commons.Measure.EuclideanSpace.volume_line_ball

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 3200000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Section 4 of the paper, X: the Hilbert transform estimate at an arbitrary base point

The paper's estimate `eq:estimate_H_tilde_omega_k_sum` reads

  `∑_{k ≥ 0} |H[ω̃_k|_ℓ'](x)| ≲ C_reg + C_gr`

where `ℓ = {x + t ŷ}` is an **arbitrary** line and the value of the Hilbert transform is taken at
the base point `x` of the line.  Equivalently (ℓ being arbitrary, so `x` ranges over the whole
line): for every line `ℓ`,

  `‖ H[ω̃_k|_ℓ'] ‖_∞ ≤ C_reg + C_gr`,

which is the hypothesis (i) of Proposition `prop:Ew_is_psh`, i.e. precisely what is needed in
`modify_weight_statement`.

The earlier module `HilbertLine` proved this estimate for the *special* base point `x₀ ⊥ ŷ` (the
foot of the perpendicular from the origin), which is what the second-derivative estimate needs.
Here we prove it for an arbitrary base point `x`, replacing the three regimes of the paper by

* `2^{k+3} ≤ ‖x‖` ("far"): the piece `ω̃_k` vanishes on a neighbourhood of `x`, so that
  integration by parts gives `|H| ≤ δ⁻² ∫|ω̃_k(x + tŷ)|dt` with `δ ≃ ‖x‖`, hence the decaying
  bound `≲ C_reg C̃ (2^k/‖x‖)²`;
* `m₀ - 3 ≤ k ≤ m₀ + 6` (with `2^{m₀} < ‖x‖ ≤ 2^{m₀+1}`): the crude bound `≲ C_reg C̃`;
* `m₀ + 7 ≤ k`: integration by parts with the identity `∫_ℝ ⟨D²ω̃_k(ty)v,v⟩dt = 2q_k`.
-/

/-- `2^(k+n) = 2^k · 2^n`, as an explicitly instantiable rewrite. -/
lemma pow2_add (k n : ℕ) : (2 : ℝ) ^ (k + n) = (2 : ℝ) ^ k * (2 : ℝ) ^ n :=
  pow_add 2 k n

/-- `2^(k+1) = 2 · 2^k`. -/
lemma pow2_succ (k : ℕ) : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
  rw [pow_succ]; ring

/-! ## Pointwise bounds and ray integrals -/

/-- The supremum bound for a single modified piece: `|ω̃_k| ≤ C_reg C̃ 2^k`. -/
lemma abs_omegaTildePiece_le (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x : ℝᵈ) :
    |omegaTildePiece (d := d) k w x| ≤ Creg * tildeConst d * (2 : ℝ) ^ k := by
  have h := norm_iteratedFDeriv_omegaTildePiece_le (d := d) hd k 0 (by norm_num) hk1 hw hwzero
    hCreg hwbound x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  refine le_trans h (le_of_eq ?_)
  have h2 : (1 - ((0 : ℕ) : ℝ)) * (k : ℝ) = (k : ℝ) := by norm_num
  rw [h2, Real.rpow_natCast]

/-- The shifted ray restriction `t ↦ ω̃_k(x + t ŷ)` is compactly supported. -/
lemma hasCompactSupport_omegaTildePiece_shift (k : ℕ) (w : ℝᵈ → ℝ) (x y : ℝᵈ) (hy : ‖y‖ = 1) :
    HasCompactSupport (fun t : ℝ => omegaTildePiece (d := d) k w (x + t • y)) := by
  have hsub : tsupport (fun t : ℝ => omegaTildePiece (d := d) k w (x + t • y))
      ⊆ Set.Icc (-((2 : ℝ) ^ (k + 1) + ‖x‖)) ((2 : ℝ) ^ (k + 1) + ‖x‖) := by
    rw [tsupport]
    refine closure_minimal ?_ isClosed_Icc
    intro t ht
    rw [Function.mem_support] at ht
    have hle : ‖x + t • y‖ ≤ (2 : ℝ) ^ (k + 1) := by
      by_contra hc
      push Not at hc
      exact ht (omegaTildePiece_eq_zero_of_norm_ge k w (le_of_lt hc))
    have hb : |t| ≤ (2 : ℝ) ^ (k + 1) + ‖x‖ := by
      have h1 : ‖t • y‖ = |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
      calc |t| = ‖t • y‖ := h1.symm
        _ = ‖(x + t • y) - x‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖x + t • y‖ + ‖x‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    exact Set.mem_Icc.mpr (abs_le.mp hb)
  exact (isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hsub

/-- **The ray integral of a modified piece.**  The integral of `|ω̃_k|` along the line
`{x + t ŷ}` is at most `‖ω̃_k‖_∞` times the measure `2^{k+2}` of the intersection of the line
with the ball of radius `2^{k+1}` containing the support. -/
lemma integral_abs_omegaTildePiece_shift_le (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x y : ℝᵈ) (hy : ‖y‖ = 1) :
    (∫ t : ℝ, |omegaTildePiece (d := d) k w (x + t • y)|)
      ≤ Creg * tildeConst d * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2) := by
  set M : ℝ := Creg * tildeConst d * (2 : ℝ) ^ k with hM
  set g : ℝ → ℝ := fun t => omegaTildePiece (d := d) k w (x + t • y) with hg
  set s : Set ℝ := {t : ℝ | ‖x + t • y‖ ≤ (2 : ℝ) ^ (k + 1)} with hs
  have hcontg : Continuous g :=
    (contDiff_omegaTildePiece k hw hk1).continuous.comp (by fun_prop)
  have hcsg : HasCompactSupport g := hasCompactSupport_omegaTildePiece_shift k w x y hy
  have hintg : Integrable (fun t : ℝ => |g t|) :=
    (hcontg.abs).integrable_of_hasCompactSupport (hcsg.abs)
  have hs_meas : MeasurableSet s :=
    (isClosed_le ((continuous_const.add (continuous_id.smul continuous_const)).norm)
      continuous_const).measurableSet
  have hvol : volume s ≤ ENNReal.ofReal (2 * (2 : ℝ) ^ (k + 1)) :=
    Commons.Measure.EuclideanSpace.volume_line_ball x y hy ((2 : ℝ) ^ (k + 1))
  have hs_ne : volume s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvol
  have hEq : (∫ t : ℝ, |g t|) = ∫ t in s, |g t| := by
    rw [← integral_indicator hs_meas]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ s
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, abs_eq_zero]
      rw [hs, Set.mem_ofPred_eq, not_le] at ht
      exact omegaTildePiece_eq_zero_of_norm_ge k w (le_of_lt ht)
  rw [hEq]
  have hMconst : IntegrableOn (fun _ : ℝ => M) s volume :=
    integrableOn_const (C := M) hs_ne (by finiteness)
  have hmono : (∫ t in s, |g t|) ≤ ∫ t in s, M :=
    setIntegral_mono_on (f := fun t : ℝ => |g t|) (g := fun _ : ℝ => M) (μ := volume)
      hs_meas (fun t _ => abs_omegaTildePiece_le hd k hk1 hw hwzero hCreg hwbound (x + t • y))
      (hf := hintg.integrableOn) (hg := hMconst)
  rw [setIntegral_const, smul_eq_mul] at hmono
  have hreal : (volume : Measure ℝ).real s ≤ (2 : ℝ) ^ (k + 2) := by
    have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
    rwa [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ (k + 1)),
      show 2 * (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 2) from by rw [pow_succ]; ring] at h1
  have hMnn : 0 ≤ M := by
    rw [hM]; have := tildeConst_nonneg d; positivity
  calc (∫ t in s, |g t|) ≤ (volume : Measure ℝ).real s * M := hmono
    _ ≤ (2 : ℝ) ^ (k + 2) * M := mul_le_mul_of_nonneg_right hreal hMnn
    _ = Creg * tildeConst d * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2) := by rw [hM]; ring

/-! ## Regime 1 ("far"): the piece vanishes near the base point -/

/-- Arithmetic for the far regime: `(1/π) δ⁻² C ≤ 4 C (2^k/x)²` when `δ ≥ 3x/4`. -/
lemma far_arith {δ x C : ℝ} (hδ : 0 < δ) (hx : 0 < x) (hδge : 3 * x / 4 ≤ δ)
    (hC : 0 ≤ C) (k : ℕ) :
    (1 / π) * (δ⁻¹ ^ 2 * (C * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2)))
      ≤ 4 * C * ((2 : ℝ) ^ k / x) ^ 2 := by
  have hinv1 : δ⁻¹ ≤ 4 / (3 * x) := by
    have hpos : (0 : ℝ) < 4 / (3 * x) := by positivity
    rw [inv_le_comm₀ hδ hpos, inv_div]
    linarith
  have hinv2 : δ⁻¹ ^ 2 ≤ (4 / (3 * x)) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hinv1 2
  have hsq : (4 / (3 * x)) ^ 2 = (16 / 9) * (x ^ 2)⁻¹ := by field_simp; ring
  rw [hsq] at hinv2
  have hp : (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2) = 4 * ((2 : ℝ) ^ k) ^ 2 := by
    rw [pow2_add k 2]; ring
  have hP2 : C * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2) = 4 * C * ((2 : ℝ) ^ k) ^ 2 := by
    rw [pow2_add k 2]; ring
  have hP : (0 : ℝ) ≤ C * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2) := by
    rw [hP2]; positivity
  have hstep : δ⁻¹ ^ 2 * (C * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2))
      ≤ ((16 / 9) * (x ^ 2)⁻¹) * (C * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2)) :=
    mul_le_mul_of_nonneg_right hinv2 hP
  have hkey : ((16 / 9) * (x ^ 2)⁻¹) * (C * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2))
      = 4 * C * ((2 : ℝ) ^ k / x) ^ 2 * (16 / 9) := by
    rw [hP2]; ring
  have hnonneg : (0 : ℝ) ≤ 4 * C * ((2 : ℝ) ^ k / x) ^ 2 := by positivity
  calc (1 / π) * (δ⁻¹ ^ 2 * (C * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2)))
      ≤ (1 / π) * (((16 / 9) * (x ^ 2)⁻¹) * (C * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2))) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 4 * C * ((2 : ℝ) ^ k / x) ^ 2 * ((1 / π) * (16 / 9)) := by rw [hkey]; ring
    _ ≤ 4 * C * ((2 : ℝ) ^ k / x) ^ 2 := by
        have hπ : (1 / π) * (16 / 9) ≤ 1 := by
          rw [div_mul_eq_mul_div, div_le_one (by positivity : (0 : ℝ) < π)]
          nlinarith [Real.pi_gt_three]
        nlinarith [hπ, hnonneg]

/-- **The decaying bound.**  If the base point satisfies `2^{k+3} ≤ ‖x‖` then the support of `ω̃_k`
misses a neighbourhood of `x` of radius comparable to `‖x‖`, and integration by parts gives
`|H[ω̃_k'](x)| ≲ C_reg C̃ (2^k/‖x‖)²`. -/
theorem abs_hilbertLine_omegaTildePiece_le_far (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x y : ℝᵈ) (hy : ‖y‖ = 1) (hx : (2 : ℝ) ^ (k + 3) ≤ ‖x‖) :
    |hilbertLine (omegaTildePiece (d := d) k w) x y|
      ≤ 4 * (Creg * tildeConst d) * ((2 : ℝ) ^ k / ‖x‖) ^ 2 := by
  set δ : ℝ := ‖x‖ - (2 : ℝ) ^ (k + 1) with hδ
  have h2k : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hxpos : 0 < ‖x‖ := lt_of_lt_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k + 3)) hx
  have hδpos : 0 < δ := by
    have hlt : (2 : ℝ) ^ (k + 1) < (2 : ℝ) ^ (k + 3) :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    rw [hδ]; linarith
  have hδge : 3 * ‖x‖ / 4 ≤ δ := by
    have h4 : 4 * (2 : ℝ) ^ (k + 1) ≤ ‖x‖ := by
      calc 4 * (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ (k + 3) := by
            rw [pow2_add k 3, pow2_add k 1]; ring
        _ ≤ ‖x‖ := hx
    rw [hδ]; linarith
  have hsupp : ∀ z : ℝᵈ, (2 : ℝ) ^ (k + 1) < ‖z‖ → omegaTildePiece (d := d) k w z = 0 :=
    fun z hz => omegaTildePiece_eq_zero_of_norm_ge k w (le_of_lt hz)
  have hzero : ∀ t : ℝ, |t| ≤ δ → omegaTildePiece (d := d) k w (x + t • y) = 0 := by
    intro t ht
    refine omegaTildePiece_eq_zero_of_norm_ge k w ?_
    have h1 : ‖x‖ - |t| ≤ ‖x + t • y‖ := by
      have hnorm : ‖t • y‖ = |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
      have h2 : ‖x‖ ≤ ‖x + t • y‖ + ‖t • y‖ := by
        calc ‖x‖ = ‖(x + t • y) - t • y‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖x + t • y‖ + ‖t • y‖ := norm_sub_le _ _
      linarith
    rw [hδ] at ht
    linarith
  have hstep1 : |hilbertLine (omegaTildePiece (d := d) k w) x y|
      ≤ (1 / π) * ∫ t : ℝ, |omegaTildePiece (d := d) k w (x + t • y)| / t ^ 2 :=
    abs_hilbertLine_le_integral (omegaTildePiece (d := d) k w)
      (contDiff_omegaTildePiece k hw hk1) x y hy (ρ := (2 : ℝ) ^ (k + 1))
      (by positivity) hδpos hsupp hzero
  set g : ℝ → ℝ := fun t => omegaTildePiece (d := d) k w (x + t • y) with hg
  have hcontg : Continuous g :=
    (contDiff_omegaTildePiece k hw hk1).continuous.comp (by fun_prop)
  have hcsg : HasCompactSupport g := hasCompactSupport_omegaTildePiece_shift k w x y hy
  have hintg : Integrable (fun t : ℝ => |g t|) :=
    (hcontg.abs).integrable_of_hasCompactSupport (hcsg.abs)
  have hδ1 : (1 : ℝ) ≤ δ := by
    calc (1 : ℝ) = (2 : ℝ) ^ 0 := (pow_zero 2).symm
      _ ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ ≤ δ := by rw [hδ]; linarith
  have hzero1 : ∀ t : ℝ, |t| ≤ 1 → g t = 0 := fun t ht => hzero t (le_trans ht hδ1)
  have hint_sq : Integrable (fun t : ℝ => g t / t ^ 2) :=
    Commons.Analysis.Calculus.integrable_div_sq_of_continuous_hasCompactSupport hcontg hcsg hzero1
  have hint_lhs : Integrable (fun t : ℝ => |g t| / t ^ 2) := by
    refine (hint_sq.abs).congr ?_
    filter_upwards with t
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t ^ 2)]
  have hint_rhs : Integrable (fun t : ℝ => δ⁻¹ ^ 2 * |g t|) := hintg.const_mul _
  have hpoint : ∀ t : ℝ, |g t| / t ^ 2 ≤ δ⁻¹ ^ 2 * |g t| := by
    intro t
    rcases lt_or_ge |t| δ with h | h
    · have h0 : g t = 0 := by rw [hg]; exact hzero t (le_of_lt h)
      rw [h0, abs_zero, zero_div]
      positivity
    · have ht2 : δ ^ 2 ≤ t ^ 2 := by
        have := sq_abs t
        nlinarith [abs_nonneg t, hδpos, h]
      have h1 : (t ^ 2)⁻¹ ≤ (δ ^ 2)⁻¹ := inv_anti₀ (by positivity) ht2
      have h2 : δ⁻¹ ^ 2 = (δ ^ 2)⁻¹ := by rw [inv_pow]
      rw [div_eq_mul_inv, h2, mul_comm (|g t|) ((t ^ 2)⁻¹)]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hstep2 : (∫ t : ℝ, |g t| / t ^ 2) ≤ δ⁻¹ ^ 2 * ∫ t : ℝ, |g t| := by
    have h := integral_mono hint_lhs hint_rhs hpoint
    rwa [integral_const_mul] at h
  have hstep3 : (∫ t : ℝ, |g t|) ≤ Creg * tildeConst d * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2) :=
    integral_abs_omegaTildePiece_shift_le hd k hk1 hw hwzero hCreg hwbound x y hy
  have hCnn : (0 : ℝ) ≤ Creg * tildeConst d := mul_nonneg hCreg.le (tildeConst_nonneg d)
  calc |hilbertLine (omegaTildePiece (d := d) k w) x y|
      ≤ (1 / π) * ∫ t : ℝ, |omegaTildePiece (d := d) k w (x + t • y)| / t ^ 2 := hstep1
    _ = (1 / π) * ∫ t : ℝ, |g t| / t ^ 2 := rfl
    _ ≤ (1 / π) * (δ⁻¹ ^ 2 * ∫ t : ℝ, |g t|) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ ≤ (1 / π) * (δ⁻¹ ^ 2
          * (Creg * tildeConst d * (2 : ℝ) ^ k * (2 : ℝ) ^ (k + 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 (by positivity))
          (by positivity)
    _ ≤ 4 * (Creg * tildeConst d) * ((2 : ℝ) ^ k / ‖x‖) ^ 2 :=
        far_arith hδpos hxpos hδge hCnn k

/-! ## Regime 2: the crude bound -/

/-- **The crude bound with the constants of §4**: `|H[ω̃_k'](x)| ≤ 36 C_reg C̃` whenever
`‖x‖ ≤ 2^{k+4}`. -/
lemma abs_hilbertLine_omegaTildePiece_le_crude (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k)
    {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x y : ℝᵈ) (hy : ‖y‖ = 1) (hx : ‖x‖ ≤ (2 : ℝ) ^ (k + 4)) :
    |hilbertLine (omegaTildePiece (d := d) k w) x y| ≤ 36 * (Creg * tildeConst d) := by
  have h := abs_hilbertLine_omegaTildePiece_le (d := d) hd k hk1 hw hwzero hCreg hwbound x y hy
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have h1 : (2 : ℝ) ^ (k + 1) + ‖x‖ ≤ (2 : ℝ) ^ (k + 1) + (2 : ℝ) ^ (k + 4) := by linarith
  have h2 : (2 : ℝ) ^ (k + 1) + (2 : ℝ) ^ (k + 4) = (2 : ℝ) ^ k * 18 := by
    rw [pow2_add k 1, pow2_add k 4]; ring
  have hCT : (0 : ℝ) ≤ Creg * tildeConst d := mul_nonneg hCreg.le (tildeConst_nonneg d)
  have hk_inv : (2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ k = 1 := by
    rw [← inv_two_pow]; exact inv_mul_cancel₀ (ne_of_gt h2k)
  have h3eq : 2 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ)))
        * ((2 : ℝ) ^ (k + 1) + (2 : ℝ) ^ (k + 4)) = 36 * (Creg * tildeConst d) := by
    rw [h2]
    calc 2 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ))) * ((2 : ℝ) ^ k * 18)
        = 36 * (Creg * tildeConst d) * ((2 : ℝ) ^ (-(k : ℝ)) * (2 : ℝ) ^ k) := by ring
      _ = 36 * (Creg * tildeConst d) := by rw [hk_inv, mul_one]
  have h3 : 2 * (Creg * tildeConst d * (2 : ℝ) ^ (-(k : ℝ)))
        * ((2 : ℝ) ^ (k + 1) + (2 : ℝ) ^ (k + 4)) ≤ 36 * (Creg * tildeConst d) :=
    le_of_eq h3eq
  refine le_trans (le_trans h ?_) h3
  exact mul_le_mul_of_nonneg_left h1
    (mul_nonneg (by norm_num) (mul_nonneg hCT (by positivity)))

/-! ## The main estimate -/

/-- Arithmetic for the far regime of the sum: `Σ_{k ∈ SA} (2^k/‖x‖)² ≤ 1/3` when every `k ∈ SA`
satisfies `k + 4 ≤ m₀` and `2^{m₀} < ‖x‖`. -/
lemma far_sum_le {m₀ : ℕ} {SA : Finset ℕ} {x : ℝᵈ}
    (hSA : ∀ k ∈ SA, k + 4 ≤ m₀) (hx : (2 : ℝ) ^ m₀ < ‖x‖) :
    (∑ k ∈ SA, ((2 : ℝ) ^ k / ‖x‖) ^ 2) ≤ 1 / 3 := by
  have h2m : (0 : ℝ) < (2 : ℝ) ^ m₀ := by positivity
  have hsq : ((2 : ℝ) ^ m₀) ^ 2 ≤ ‖x‖ ^ 2 :=
    le_of_lt (pow_lt_pow_left₀ hx (le_of_lt h2m) (by norm_num : (2 : ℕ) ≠ 0))
  have hterm : ∀ k ∈ SA, ((2 : ℝ) ^ k / ‖x‖) ^ 2
      ≤ ((2 : ℝ) ^ k) ^ 2 * (((2 : ℝ) ^ m₀) ^ 2)⁻¹ := by
    intro k _
    rw [div_pow, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hsq) (by positivity)
  have hsub : SA ⊆ Finset.range m₀ :=
    fun k hk => Finset.mem_range.mpr (by have := hSA k hk; omega)
  have hfour : ∀ k : ℕ, ((2 : ℝ) ^ k) ^ 2 = (4 : ℝ) ^ k := by
    intro k
    have h1 : ((2 : ℝ) ^ k) ^ 2 = (2 : ℝ) ^ (k * 2) := (pow_mul (2 : ℝ) k 2).symm
    have h2 : (4 : ℝ) ^ k = (2 : ℝ) ^ (2 * k) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [h1, h2, Nat.mul_comm]
  calc (∑ k ∈ SA, ((2 : ℝ) ^ k / ‖x‖) ^ 2)
      ≤ ∑ k ∈ SA, ((2 : ℝ) ^ k) ^ 2 * (((2 : ℝ) ^ m₀) ^ 2)⁻¹ := Finset.sum_le_sum hterm
    _ = (((2 : ℝ) ^ m₀) ^ 2)⁻¹ * ∑ k ∈ SA, ((2 : ℝ) ^ k) ^ 2 := by
        rw [Finset.mul_sum]; ring
    _ = (((2 : ℝ) ^ m₀) ^ 2)⁻¹ * ∑ k ∈ SA, (4 : ℝ) ^ k := by
        rw [Finset.sum_congr rfl (fun k _ => hfour k)]
    _ ≤ (((2 : ℝ) ^ m₀) ^ 2)⁻¹ * ∑ k ∈ Finset.range m₀, (4 : ℝ) ^ k := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    _ ≤ (((2 : ℝ) ^ m₀) ^ 2)⁻¹ * ((4 : ℝ) ^ m₀ / (4 - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Commons.Algebra.BigOperators.geom_sum_le_div_sub_one (by norm_num) m₀
    _ = 1 / 3 := by
        have h4 : (4 : ℝ) ^ m₀ = ((2 : ℝ) ^ m₀) ^ 2 := by
          have h1 : (4 : ℝ) ^ m₀ = (2 : ℝ) ^ (2 * m₀) := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
          have h2 : ((2 : ℝ) ^ m₀) ^ 2 = (2 : ℝ) ^ (m₀ * 2) := (pow_mul (2 : ℝ) m₀ 2).symm
          rw [h1, h2, Nat.mul_comm]
        rw [h4]
        field_simp
        ring

/-- **The paper's Hilbert transform estimate at an arbitrary point.**
For every line `{x + t ŷ}`,

  `∑_{k ≥ 1} |H[ω̃_k|_ℓ'](x)| ≤ 400 C_reg C̃(d) + 256 C_gr`,

which is the hypothesis (i) of Proposition `prop:Ew_is_psh` for the modified pieces. -/
theorem sum_abs_hilbertLine_le_any (hd : 1 ≤ d) {K : ℕ} {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwnonpos : ∀ x, w x ≤ 0) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg Cgr : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (hgrowth : HasFiniteGrowth w Cgr)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0)
    (x y : ℝᵈ) (hy : ‖y‖ = 1) :
    (∑ k ∈ Finset.Icc 1 K, |hilbertLine (omegaTildePiece (d := d) k w) x y|)
      ≤ 400 * (Creg * tildeConst d) + 256 * Cgr := by
  obtain ⟨hint, hgrle⟩ := hgrowth
  have hreg : ∀ z : ℝᵈ, ‖w z‖ ≤ Creg * (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    intro z
    have h := hwbound 0 (by norm_num) z
    simpa [norm_iteratedFDeriv_zero] using h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖x‖ ≤ (2 : ℝ) ^ (m + 1) := by
    obtain ⟨n, hn⟩ := exists_pow_gt_norm (d := d) x
    refine ⟨n, le_of_lt (lt_of_lt_of_le hn ?_)⟩
    rw [pow_succ]
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ n by positivity]
  have hex : ∃ m : ℕ, ‖x‖ ≤ (2 : ℝ) ^ (m + 1) := ⟨m, hm⟩
  set m₀ := Nat.find hex with hm₀def
  have hm₀ : ‖x‖ ≤ (2 : ℝ) ^ (m₀ + 1) := Nat.find_spec hex
  have hm₀min : ∀ k : ℕ, k < m₀ → (2 : ℝ) ^ (k + 1) < ‖x‖ := by
    intro k hk
    refine lt_of_not_ge fun hc => ?_
    exact absurd (Nat.find_min' hex hc) (not_le.mpr hk)
  have hCT : (0 : ℝ) ≤ Creg * tildeConst d := mul_nonneg hCreg.le (tildeConst_nonneg d)
  set f : ℕ → ℝ := fun k => |hilbertLine (omegaTildePiece (d := d) k w) x y| with hf
  set SA := (Finset.Icc 1 K).filter (fun k => k + 4 ≤ m₀) with hSA
  set SB := ((Finset.Icc 1 K).filter (fun k => ¬ k + 4 ≤ m₀)).filter
    (fun k => ¬ m₀ + 7 ≤ k) with hSB
  set SC := ((Finset.Icc 1 K).filter (fun k => ¬ k + 4 ≤ m₀)).filter
    (fun k => m₀ + 7 ≤ k) with hSC
  -- regime A: the far, decaying terms
  have hA : (∑ k ∈ SA, f k) ≤ 4 * (Creg * tildeConst d) / 3 := by
    rcases Nat.eq_zero_or_pos m₀ with h0 | h0
    · have hempty : SA = ∅ := by
        rw [hSA]
        refine Finset.eq_empty_iff_forall_notMem.mpr fun k hk => ?_
        simp only [Finset.mem_filter, Finset.mem_Icc] at hk
        omega
      rw [hempty, Finset.sum_empty]
      linarith [hCT]
    · have hxgt : (2 : ℝ) ^ m₀ < ‖x‖ := by
        have := hm₀min (m₀ - 1) (by omega)
        rwa [show m₀ - 1 + 1 = m₀ by omega] at this
      have hterm : ∀ k ∈ SA, f k ≤ 4 * (Creg * tildeConst d) * ((2 : ℝ) ^ k / ‖x‖) ^ 2 := by
        intro k hk
        rw [hSA, Finset.mem_filter, Finset.mem_Icc] at hk
        obtain ⟨⟨hk1, _⟩, hk4⟩ := hk
        have hk1' : 1 ≤ k := hk1
        refine abs_hilbertLine_omegaTildePiece_le_far (d := d) hd k hk1' hw hwzero hCreg hwbound
          x y hy ?_
        have h1 : (2 : ℝ) ^ (k + 3) ≤ (2 : ℝ) ^ (m₀ - 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h2 : (2 : ℝ) ^ (m₀ - 1) < (2 : ℝ) ^ m₀ :=
          pow_lt_pow_right₀ (by norm_num) (by omega)
        linarith
      calc (∑ k ∈ SA, f k)
          ≤ ∑ k ∈ SA, 4 * (Creg * tildeConst d) * ((2 : ℝ) ^ k / ‖x‖) ^ 2 :=
            Finset.sum_le_sum hterm
        _ = 4 * (Creg * tildeConst d) * ∑ k ∈ SA, ((2 : ℝ) ^ k / ‖x‖) ^ 2 := by
            rw [Finset.mul_sum]
        _ ≤ 4 * (Creg * tildeConst d) * (1 / 3) :=
            mul_le_mul_of_nonneg_left (far_sum_le (fun k hk => by
              rw [hSA, Finset.mem_filter] at hk; exact hk.2) hxgt) (by positivity)
        _ = 4 * (Creg * tildeConst d) / 3 := by ring
  -- regime B: the crude bound
  have hB : (∑ k ∈ SB, f k) ≤ 360 * (Creg * tildeConst d) := by
    have hcard : SB.card ≤ 10 := by
      have hsub : SB ⊆ Finset.Icc (m₀ - 3) (m₀ + 6) := by
        intro k hk
        rw [hSB, Finset.mem_filter, Finset.mem_filter] at hk
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have h10 : (Finset.Icc (m₀ - 3) (m₀ + 6)).card ≤ 10 := by
        rw [Nat.card_Icc]
        rcases Nat.lt_or_ge m₀ 3 with hlt | hge
        · have hz : m₀ - 3 = 0 := by omega
          omega
        · have hz : m₀ - 3 + 3 = m₀ := by omega
          omega
      exact le_trans (Finset.card_le_card hsub) h10
    have hterm : ∀ k ∈ SB, f k ≤ 36 * (Creg * tildeConst d) := by
      intro k hk
      rw [hSB, Finset.mem_filter, Finset.mem_filter] at hk
      obtain ⟨⟨hk1, hkm⟩, hk7⟩ := hk
      have hk1' : 1 ≤ k := (Finset.mem_Icc.mp hk1).1
      refine abs_hilbertLine_omegaTildePiece_le_crude (d := d) hd k hk1' hw hwzero hCreg
        hwbound x y hy ?_
      calc ‖x‖ ≤ (2 : ℝ) ^ (m₀ + 1) := hm₀
        _ ≤ (2 : ℝ) ^ (k + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (∑ k ∈ SB, f k) ≤ ∑ k ∈ SB, 36 * (Creg * tildeConst d) := Finset.sum_le_sum hterm
      _ = 36 * (Creg * tildeConst d) * SB.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 36 * (Creg * tildeConst d) * 10 := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hCT)
          exact_mod_cast hcard
      _ = 360 * (Creg * tildeConst d) := by ring
  -- regime C: integration by parts
  have hC : (∑ k ∈ SC, f k)
      ≤ (2 / π) * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2))
        + Creg * tildeConst d := by
    have hterm : ∀ k ∈ SC, f k ≤ (1 / π) * (2 * |qk k w|
        + Creg * tildeConst d * ‖x‖ * (8 * ((2 : ℝ) ^ k)⁻¹)) := by
      intro k hk
      rw [hSC, Finset.mem_filter, Finset.mem_filter] at hk
      obtain ⟨⟨hk1, _⟩, hk7⟩ := hk
      have hk1' : 1 ≤ k := (Finset.mem_Icc.mp hk1).1
      have hk2 : 2 ≤ k := by omega
      have hsup' := pow_two_arith hk7 hm₀
      have hstep1 : f k ≤ (1 / π) *
          ∫ t : ℝ, |omegaTildePiece (d := d) k w (x + t • y)| / t ^ 2 := by
        rw [hf]
        refine abs_hilbertLine_le_integral (omegaTildePiece (d := d) k w)
          (contDiff_omegaTildePiece k hw hk1') x y hy (ρ := (2 : ℝ) ^ (k + 1))
          (δ := (2 : ℝ) ^ (k - 2)) (by positivity) (by positivity) ?_ ?_
        · intro z hz
          exact omegaTildePiece_eq_zero_of_norm_ge k w (le_of_lt hz)
        · intro t ht
          refine omegaTildePiece_eq_zero_of_norm_le_pred k hk1' w ?_
          have h3 : ‖x + t • y‖ ≤ ‖x‖ + |t| := by
            calc ‖x + t • y‖ ≤ ‖x‖ + ‖t • y‖ := norm_add_le _ _
              _ = ‖x‖ + |t| := by rw [norm_smul, Real.norm_eq_abs, hy, mul_one]
          linarith
      have hδ1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k - 2) := by
        calc (1 : ℝ) = (2 : ℝ) ^ 0 := (pow_zero 2).symm
          _ ≤ (2 : ℝ) ^ (k - 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hstep2 := integral_abs_line_div_sq_le (d := d) hd k hk2 hw hwzero (hwk k) hCreg
        hwbound x y hy (δ := (2 : ℝ) ^ (k - 2)) hδ1 hsup'
      calc f k ≤ (1 / π) * ∫ t : ℝ, |omegaTildePiece (d := d) k w (x + t • y)| / t ^ 2 :=
            hstep1
        _ ≤ (1 / π) * (2 * |qk k w| + Creg * tildeConst d * ‖x‖ * (2 / (2 : ℝ) ^ (k - 2))) :=
            mul_le_mul_of_nonneg_left hstep2 (by positivity)
        _ = (1 / π) * (2 * |qk k w|
              + Creg * tildeConst d * ‖x‖ * (8 * ((2 : ℝ) ^ k)⁻¹)) := by
            rw [show (2 : ℝ) / (2 : ℝ) ^ (k - 2) = 8 * ((2 : ℝ) ^ k)⁻¹ from by
              rw [div_eq_mul_inv]
              exact inv_pow_two_sub_two k hk2]
    have hsum1 : (∑ k ∈ SC, (1 / π) * (2 * |qk k w|)) = (2 / π) * ∑ k ∈ SC, |qk k w| := by
      rw [show (2 / π) * (∑ k ∈ SC, |qk k w|) = ∑ k ∈ SC, (2 / π) * |qk k w| from by
        rw [Finset.mul_sum]]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have hsum2 : (∑ k ∈ SC, (1 / π) * (Creg * tildeConst d * ‖x‖ * (8 * ((2 : ℝ) ^ k)⁻¹)))
        = (8 / π * (Creg * tildeConst d * ‖x‖)) * ∑ k ∈ SC, ((2 : ℝ) ^ k)⁻¹ := by
      rw [show (8 / π * (Creg * tildeConst d * ‖x‖)) * (∑ k ∈ SC, ((2 : ℝ) ^ k)⁻¹)
          = ∑ k ∈ SC, (8 / π * (Creg * tildeConst d * ‖x‖)) * ((2 : ℝ) ^ k)⁻¹ from by
        rw [Finset.mul_sum]]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have hSCsub : SC ⊆ Finset.Icc (m₀ + 7) K := by
      intro k hk
      rw [hSC, Finset.mem_filter, Finset.mem_filter] at hk
      obtain ⟨⟨hk1, _⟩, hk7⟩ := hk
      exact Finset.mem_Icc.mpr ⟨hk7, (Finset.mem_Icc.mp hk1).2⟩
    have hsum3 : (∑ k ∈ SC, ((2 : ℝ) ^ k)⁻¹) ≤ 2 * ((2 : ℝ) ^ (m₀ + 7))⁻¹ := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hSCsub (fun k _ _ => by positivity)) ?_
      exact sum_Icc_inv_pow_two_le (m₀ + 7) K
    have hsum4 : (∑ k ∈ SC, |qk k w|) ≤ 128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2) := by
      have hsub : SC ⊆ Finset.Icc 1 K := by
        intro k hk
        rw [hSC, Finset.mem_filter, Finset.mem_filter] at hk
        exact hk.1.1
      exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg _))
        (sum_abs_qk_le_growth (d := d) hd hw.continuous hwnonpos hCreg.le hreg hint)
    have hkey : 8 / π * (Creg * tildeConst d * ‖x‖) * (2 * ((2 : ℝ) ^ (m₀ + 7))⁻¹)
        ≤ Creg * tildeConst d := by
      have hpow : (2 : ℝ) ^ (m₀ + 7) = (2 : ℝ) ^ (m₀ + 1) * 64 := by
        rw [show m₀ + 7 = (m₀ + 1) + 6 from by omega, pow2_add]
        norm_num
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (m₀ + 1) := by positivity
      have h2 : ‖x‖ * ((2 : ℝ) ^ (m₀ + 7))⁻¹ ≤ (64 : ℝ)⁻¹ := by
        have h3 : ‖x‖ * ((2 : ℝ) ^ (m₀ + 1))⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hpos]
          exact hm₀
        rw [hpow, mul_inv_rev]
        calc ‖x‖ * ((64 : ℝ)⁻¹ * ((2 : ℝ) ^ (m₀ + 1))⁻¹)
            = (‖x‖ * ((2 : ℝ) ^ (m₀ + 1))⁻¹) * (64 : ℝ)⁻¹ := by ring
          _ ≤ 1 * (64 : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h3 (by norm_num)
          _ = (64 : ℝ)⁻¹ := by ring
      have hCT : (0 : ℝ) ≤ Creg * tildeConst d := mul_nonneg hCreg.le (tildeConst_nonneg d)
      calc 8 / π * (Creg * tildeConst d * ‖x‖) * (2 * ((2 : ℝ) ^ (m₀ + 7))⁻¹)
          = (16 / π) * (Creg * tildeConst d) * (‖x‖ * ((2 : ℝ) ^ (m₀ + 7))⁻¹) := by ring
        _ ≤ (16 / π) * (Creg * tildeConst d) * (64 : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (1 / (4 * π)) * (Creg * tildeConst d) := by ring
        _ ≤ 1 * (Creg * tildeConst d) := by
            refine mul_le_mul_of_nonneg_right ?_ hCT
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * π)]
            nlinarith [Real.pi_gt_three]
        _ = Creg * tildeConst d := by ring
    calc (∑ k ∈ SC, f k)
        ≤ ∑ k ∈ SC, (1 / π) * (2 * |qk k w|
            + Creg * tildeConst d * ‖x‖ * (8 * ((2 : ℝ) ^ k)⁻¹)) := Finset.sum_le_sum hterm
      _ = (2 / π) * (∑ k ∈ SC, |qk k w|)
            + (8 / π * (Creg * tildeConst d * ‖x‖)) * ∑ k ∈ SC, ((2 : ℝ) ^ k)⁻¹ := by
          rw [show (∑ k ∈ SC, (1 / π) * (2 * |qk k w|
                + Creg * tildeConst d * ‖x‖ * (8 * ((2 : ℝ) ^ k)⁻¹)))
              = ∑ k ∈ SC, ((1 / π) * (2 * |qk k w|)
                  + (1 / π) * (Creg * tildeConst d * ‖x‖ * (8 * ((2 : ℝ) ^ k)⁻¹))) from
            Finset.sum_congr rfl (fun k _ => by ring)]
          rw [Finset.sum_add_distrib, hsum1, hsum2]
      _ ≤ (2 / π) * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2))
            + (8 / π * (Creg * tildeConst d * ‖x‖)) * (2 * ((2 : ℝ) ^ (m₀ + 7))⁻¹) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hsum4 (by positivity)
          · exact mul_le_mul_of_nonneg_left hsum3 (by positivity)
      _ ≤ (2 / π) * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2))
            + Creg * tildeConst d := add_le_add le_rfl hkey
  -- assemble
  have hsplit1 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 K)
    (fun k => k + 4 ≤ m₀) f
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((Finset.Icc 1 K).filter (fun k => ¬ k + 4 ≤ m₀)) (fun k => m₀ + 7 ≤ k) f
  rw [← hsplit1, ← hsplit2]
  refine le_trans (add_le_add hA (add_le_add hC hB)) ?_
  have hQ : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr := by
    rw [← growthFunctional_eq_Gstar]
    exact hgrle
  have hCgr0 : (0 : ℝ) ≤ Cgr := by
    have h1 : (0 : ℝ) ≤ ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2) :=
      setIntegral_nonneg measurableSet_Ioi (fun r _ => div_nonneg (Gstar_nonneg w r) (by positivity))
    rw [← growthFunctional_eq_Gstar] at h1
    linarith
  have hπ2 : (2 / π * 128 : ℝ) ≤ 256 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < π)]
    nlinarith [Real.pi_gt_three]
  have hbig : (2 / π) * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ 256 * Cgr := by
    have h := mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ 2 / π * 128)
    calc (2 / π) * (128 * ∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2))
        = (2 / π * 128) * (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) := by ring
      _ ≤ (2 / π * 128) * Cgr := h
      _ ≤ 256 * Cgr := mul_le_mul_of_nonneg_right hπ2 hCgr0
  linarith [hbig, hCT]

end Submission.FUP
