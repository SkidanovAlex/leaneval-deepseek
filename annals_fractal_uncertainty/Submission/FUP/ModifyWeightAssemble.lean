import Submission.FUP.Section4Bounds

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Section 4 of the paper, VI: assembling the modified weight `ω̃`

The paper's §4 constructs, for a weight `ω` satisfying the Beurling–Malliavin hypotheses
(nonpositive, vanishing on `B₂`, Kohn–Nirenberg regularity) a modified weight

  `ω̃ = ∑_k ω̃_k`,  `ω̃_k = ω_k + g_k` (`k ≥ 2`),  `ω̃_k = ω_k` (`k < 2`),

whose spherical projections `π ω̃_k` are the constants `q_k`, and which satisfies

* `ω̃ ≤ ω`, `ω̃ = 0` on `B₂`, `ω̃ ∈ C³`, `ω̃` Lipschitz with constant `≲ C_reg`;

these are the properties (iii)–(iv) of `lem:modify_weight_lemma` used by the rest of the proof.

The threshold `2` (rather than the paper's `5`) is what makes `ω̃ = 0` on `B₂`: for `k ≥ 2` the
piece `ψ_k` is supported in `[2^{k-1}, 2^{k+1}] ⊆ (2,∞)`, while for `k < 2` we have
`ω̃_k = ω_k = ψ_k·ω` with `ω` vanishing on `B₂`.

This module proves all the structural properties of `ω̃` needed for `modify_weight_statement`,
except the two analytic conditions (the Hilbert transform bound and the second derivative bound),
which are proved in `ModifyWeightPSH`.
-/

/-! ## 1. The pieces and the sum -/

/-- The `k`-th piece of the modified weight: `ω̃_k = ω_k` for `k < 2` and `ω̃_k = ω_k + g_k`
for `k ≥ 2`. -/
noncomputable def omegaTildePiece (k : ℕ) (w : ℝᵈ → ℝ) : ℝᵈ → ℝ :=
  fun x => if k < 2 then omegaPiece k w x else omegaTilde k w x

/-- The modified weight `ω̃ = ∑_k ω̃_k` (sum of the locally finite family `(ω̃_k)`). -/
noncomputable def omegaTildeSum (w : ℝᵈ → ℝ) (x : ℝᵈ) : ℝ := ∑' k, omegaTildePiece k w x

lemma omegaTildePiece_of_lt (k : ℕ) (w : ℝᵈ → ℝ) (hk : k < 2) (x : ℝᵈ) :
    omegaTildePiece k w x = omegaPiece k w x := by
  simp only [omegaTildePiece]; exact if_pos hk

lemma omegaTildePiece_of_le (k : ℕ) (w : ℝᵈ → ℝ) (hk : 2 ≤ k) (x : ℝᵈ) :
    omegaTildePiece k w x = omegaTilde k w x := by
  simp only [omegaTildePiece]; exact if_neg (by omega)

/-- Pointwise factorisation of the modified piece `ω̃_k = ω_k + g_k`. -/
lemma omegaTilde_eq (k : ℕ) (w : ℝᵈ → ℝ) (x : ℝᵈ) :
    omegaTilde k w x = radialPsi (d := d) k x * (w x + (pk k)⁻¹ * (qk k w - hk k w x)) := by
  rw [omegaTilde]
  simp only [omegaPiece_apply, gk]
  ring

/-- `ψ_k(0) = 0` for `k ≥ 1`. -/
lemma radialPsi_zero_at_zero (k : ℕ) (hk : 1 ≤ k) : radialPsi (d := d) k (0 : ℝᵈ) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  show dyadPsi (j + 1) ‖(0 : ℝᵈ)‖ = 0
  rw [norm_zero]
  exact dyadPsi_succ_zero_of_le_one j zero_le_one

/-- Pointwise factorisation of a piece: everything is a multiple of `ψ_k(‖·‖)`. -/
lemma omegaTildePiece_eq (k : ℕ) (w : ℝᵈ → ℝ) (x : ℝᵈ) :
    omegaTildePiece k w x = radialPsi (d := d) k x *
      (w x + (if k < 2 then 0 else (pk k)⁻¹ * (qk k w - hk k w x))) := by
  rw [omegaTildePiece]
  split_ifs with hk
  · rw [omegaPiece_apply]; ring
  · rw [omegaTilde_eq]

lemma omegaPiece_eq_zero_of_radialPsi_eq_zero (k : ℕ) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (h : radialPsi (d := d) k x = 0) : omegaPiece k w x = 0 := by
  rw [omegaPiece_apply, h, zero_mul]

lemma omegaTilde_eq_zero_of_radialPsi_eq_zero (k : ℕ) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (h : radialPsi (d := d) k x = 0) : omegaTilde k w x = 0 := by
  rw [omegaTilde_eq, h, zero_mul]

lemma omegaTildePiece_eq_zero_of_radialPsi_eq_zero (k : ℕ) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (h : radialPsi (d := d) k x = 0) : omegaTildePiece k w x = 0 := by
  rw [omegaTildePiece_eq, h, zero_mul]

/-! ## 2. The support condition and local finiteness of the sum -/

/-- `ω̃_{k+1}` vanishes for `‖x‖ ≤ 2^k`. -/
lemma omegaTildePiece_succ_eq_zero_of_norm_le (k : ℕ) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (hx : ‖x‖ ≤ (2 : ℝ) ^ k) : omegaTildePiece (k + 1) w x = 0 :=
  omegaTildePiece_eq_zero_of_radialPsi_eq_zero (k + 1) w (radialPsi_zero_of_norm_le k hx)

/-- `ω_k` vanishes for `‖x‖ ≤ 2^k`. -/
lemma omegaPiece_succ_eq_zero_of_norm_le (k : ℕ) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (hx : ‖x‖ ≤ (2 : ℝ) ^ k) : omegaPiece (k + 1) w x = 0 :=
  omegaPiece_eq_zero_of_radialPsi_eq_zero (k + 1) w (radialPsi_zero_of_norm_le k hx)

/-- Local finiteness: below scale `2^n` only the pieces `k ≤ n` contribute. -/
lemma omegaTildeSum_eq_sum_range (n : ℕ) (w : ℝᵈ → ℝ) {x : ℝᵈ} (hx : ‖x‖ < (2 : ℝ) ^ n) :
    omegaTildeSum w x = ∑ k ∈ Finset.range (n + 1), omegaTildePiece k w x := by
  rw [omegaTildeSum, tsum_eq_sum]
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact omegaTildePiece_succ_eq_zero_of_norm_le j w
    (le_of_lt (lt_of_lt_of_le hx (pow_le_pow_right₀ (by norm_num) (by omega))))

/-- The same local finiteness for the dyadic pieces `ω_k` of `ω`. -/
lemma tsum_omegaPiece_eq_sum_range (n : ℕ) (w : ℝᵈ → ℝ) {x : ℝᵈ} (hx : ‖x‖ < (2 : ℝ) ^ n) :
    ∑' k, omegaPiece k w x = ∑ k ∈ Finset.range (n + 1), omegaPiece k w x := by
  rw [tsum_eq_sum]
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact omegaPiece_succ_eq_zero_of_norm_le j w
    (le_of_lt (lt_of_lt_of_le hx (pow_le_pow_right₀ (by norm_num) (by omega))))

/-- The dyadic pieces sum to the weight. -/
lemma tsum_omegaPiece_eq (w : ℝᵈ → ℝ) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) (x : ℝᵈ) :
    ∑' k, omegaPiece k w x = w x := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : ∀ k, omegaPiece k w 0 = 0 := fun k => by
      rw [omegaPiece_apply, hwzero 0 (by simp)]; ring
    have hfun : (fun k => omegaPiece k w 0) = fun _ => (0 : ℝ) := funext h0
    rw [hfun, tsum_zero, hwzero 0 (by simp)]
  · have hsum : HasSum (fun k => radialPsi (d := d) k x) 1 :=
      dyadPsi_hasSum (norm_pos_iff.mpr hx)
    have h2 := hsum.mul_right (w x)
    rw [one_mul] at h2
    have h3 : (fun k => radialPsi (d := d) k x * w x) = fun k => omegaPiece k w x := by
      funext k; rw [omegaPiece_apply]
    rw [h3] at h2
    exact h2.tsum_eq

/-! ## 3. Nonpositivity of the correction `g_k` -/

/-- Positivity of the constant `p_k` for `k ≥ 1`. -/
lemma pk_pos (k : ℕ) (hk1 : 1 ≤ k) : 0 < pk k := by
  rw [pk_eq k hk1]
  exact mul_pos (by positivity) (by have := pkConst_pos; linarith)

/-- **`g_k ≤ 0`.**  The correction only lowers the weight: `π ω_k ≥ q_k` pointwise (with
`q_k = ⨅ π ω_k`) and `p_k > 0`, `ψ_k ≥ 0`. -/
lemma gk_nonpos (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ} {Creg : ℝ} (hCreg : 0 ≤ Creg)
    (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2)) (x : ℝᵈ) :
    gk k w x ≤ 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [gk, radialPsi_zero_at_zero k hk1]
    simp
  · have hq : qk k w ≤ hk k w x := by
      have hc : (0 : ℝ) < (‖x‖)⁻¹ := by positivity
      have hu : ‖((‖x‖)⁻¹ : ℝ) • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
      have h1 : qk k w ≤ sphProj (omegaPiece k w) (((‖x‖)⁻¹ : ℝ) • x) :=
        qk_le k w (bddBelow_sphProj_omegaPiece k hk1 hCreg hreg) ⟨_, hu⟩
      rwa [sphProj_omegaPiece_eq_hk k w hu, hk_smul k w hc x] at h1
    rw [gk]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (inv_nonneg.mpr (pk_pos k hk1).le) (radialPsi_nonneg k x))
      (sub_nonpos.mpr hq)

/-- Every real number is below some power of `2`. -/
lemma exists_pow_gt_norm (x : ℝᵈ) : ∃ n : ℕ, ‖x‖ < (2 : ℝ) ^ n :=
  ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_gt_atTop
    ‖x‖).exists

/-! ## 4. The three structural properties of `ω̃` -/

/-- **`ω̃ ≤ ω`.** -/
theorem omegaTildeSum_le_self (w : ℝᵈ → ℝ) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 ≤ Creg)
    (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2)) (x : ℝᵈ) :
    omegaTildeSum w x ≤ w x := by
  obtain ⟨n, hn⟩ := exists_pow_gt_norm x
  have h1 : omegaTildeSum w x = ∑ k ∈ Finset.range (n + 1), omegaTildePiece k w x :=
    omegaTildeSum_eq_sum_range n w hn
  have h2 : w x = ∑ k ∈ Finset.range (n + 1), omegaPiece k w x := by
    rw [← tsum_omegaPiece_eq w hwzero x, tsum_omegaPiece_eq_sum_range n w hn]
  rw [h1, h2]
  refine Finset.sum_le_sum fun k _ => ?_
  rcases lt_or_ge k 2 with hk2 | hk2
  · rw [omegaTildePiece_of_lt k w hk2]
  · rw [omegaTildePiece_of_le k w hk2, omegaTilde]
    have := gk_nonpos k (by omega) hCreg hreg x
    linarith

/-- **`ω̃ = 0` on `B₂`.** -/
theorem omegaTildeSum_eq_zero_of_norm_le (w : ℝᵈ → ℝ) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {x : ℝᵈ} (hx : ‖x‖ ≤ 2) : omegaTildeSum w x = 0 := by
  have hpiece : ∀ k : ℕ, omegaTildePiece k w x = 0 := by
    intro k
    rw [omegaTildePiece_eq]
    rcases lt_or_ge k 2 with hk2 | hk2
    · rw [if_pos hk2, hwzero x hx, add_zero, mul_zero]
    · rw [if_neg (by omega)]
      have h0 : radialPsi (d := d) k x = 0 := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        exact radialPsi_zero_of_norm_le j (by
          have : (1 : ℕ) ≤ j := by omega
          calc ‖x‖ ≤ 2 := hx
            _ ≤ (2 : ℝ) ^ j := by
                calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one 2).symm
                  _ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) this)
      rw [h0, zero_mul]
  simp [omegaTildeSum, hpiece]


/-! ## 5. Smoothness of the pieces -/

/-- `ψ_k(‖x‖) = 0` when `‖x‖ ≤ 2^{k-1}` (`k ≥ 1`). -/
lemma radialPsi_eq_zero_of_norm_le_pred (k : ℕ) (hk1 : 1 ≤ k) {x : ℝᵈ}
    (h : ‖x‖ ≤ (2 : ℝ) ^ (k - 1)) : radialPsi (d := d) k x = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact radialPsi_zero_of_norm_le j (by simpa using h)

/-- `g_k(x) = 0` when `ψ_k(‖x‖) = 0`. -/
lemma gk_eq_zero_of_radialPsi_eq_zero (k : ℕ) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (h : radialPsi (d := d) k x = 0) : gk k w x = 0 := by
  rw [gk, h]; ring

/-- `ω̃_k(x) = 0` when `‖x‖ ≤ 2^{k-1}` (`k ≥ 1`). -/
lemma omegaTildePiece_eq_zero_of_norm_le_pred (k : ℕ) (hk1 : 1 ≤ k) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (h : ‖x‖ ≤ (2 : ℝ) ^ (k - 1)) : omegaTildePiece k w x = 0 :=
  omegaTildePiece_eq_zero_of_radialPsi_eq_zero k w (radialPsi_eq_zero_of_norm_le_pred k hk1 h)

/-- `ω̃_k(x) = 0` when `2^{k+1} ≤ ‖x‖`. -/
lemma omegaTildePiece_eq_zero_of_norm_ge (k : ℕ) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (h : (2 : ℝ) ^ (k + 1) ≤ ‖x‖) : omegaTildePiece k w x = 0 :=
  omegaTildePiece_eq_zero_of_radialPsi_eq_zero k w (radialPsi_eq_zero_of_norm_ge k h)

/-- `g_k(x) = 0` when `‖x‖ ≤ 2^{k-1}` (`k ≥ 1`). -/
lemma gk_eq_zero_of_norm_le_pred (k : ℕ) (hk1 : 1 ≤ k) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (h : ‖x‖ ≤ (2 : ℝ) ^ (k - 1)) : gk k w x = 0 :=
  gk_eq_zero_of_radialPsi_eq_zero k w (radialPsi_eq_zero_of_norm_le_pred k hk1 h)

/-- On the annulus `annOpen k` the correction `g_k` agrees with a manifestly smooth expression. -/
lemma contDiffOn_gk_annOpen (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) :
    ContDiffOn ℝ 3 (gk k w) (annOpen (d := d) k) := by
  have hHk : ContDiffOn ℝ 3 (hkW k w) (annOpen (d := d) k) := by
    show ContDiffOn ℝ 3 (fun x : ℝᵈ => (‖x‖)⁻¹ * gwin k w x) (annOpen (d := d) k)
    exact (contDiffOn_inv_norm_annOpen (d := d) k).mul (contDiffOn_gwin (d := d) k hw)
  have hm : ContDiffOn ℝ 3 (fun x : ℝᵈ => (pk k)⁻¹ *
      (radialPsi (d := d) k x * (qk k w - hkW k w x))) (annOpen (d := d) k) :=
    contDiffOn_const.mul (((contDiff_radialPsi (d := d) k).contDiffOn).mul
      (contDiffOn_const.sub hHk))
  refine hm.congr fun x hx => ?_
  simp only [gk]
  rw [hk_eq_hkW k hk1 w hx]
  ring

/-- `g_k` vanishes in a neighbourhood of any point outside the open annulus `annOpen k`. -/
lemma gk_eventuallyEq_zero_of_notMem_annOpen (k : ℕ) (hk1 : 1 ≤ k) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (hx : x ∉ annOpen (d := d) k) : gk k w =ᶠ[𝓝 x] 0 := by
  rw [annOpen, Set.mem_ofPred_eq, not_and_or, not_lt, not_lt] at hx
  rcases hx with hlo | hhi
  · have hlt : (2 : ℝ) ^ k / 4 < (2 : ℝ) ^ (k - 1) := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have h1 : (2 : ℝ) ^ (j + 1) / 4 = (2 : ℝ) ^ j / 2 := by ring
      have h2 : (2 : ℝ) ^ (j + 1 - 1) = (2 : ℝ) ^ j := by simp
      rw [h1, h2]
      have := pow_pos (by norm_num : (0 : ℝ) < 2) j
      linarith
    have hε : 0 < (2 : ℝ) ^ (k - 1) - ‖x‖ := sub_pos.mpr (lt_of_le_of_lt hlo hlt)
    filter_upwards [Metric.ball_mem_nhds x hε] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact gk_eq_zero_of_norm_le_pred k hk1 w (le_of_lt (calc
      ‖y‖ ≤ ‖x‖ + ‖y - x‖ := norm_le_norm_add_norm_sub' y x
      _ < ‖x‖ + ((2 : ℝ) ^ (k - 1) - ‖x‖) := by linarith
      _ = (2 : ℝ) ^ (k - 1) := by ring))
  · have hε : 0 < ‖x‖ - (2 : ℝ) ^ (k + 1) := by
      have h4 : 4 * (2 : ℝ) ^ k = (2 : ℝ) ^ (k + 2) := by rw [pow_succ']; ring
      rw [h4] at hhi
      have hlt : (2 : ℝ) ^ (k + 1) < (2 : ℝ) ^ (k + 2) :=
        pow_lt_pow_right₀ (by norm_num) (by omega)
      linarith
    filter_upwards [Metric.ball_mem_nhds x hε] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    refine gk_eq_zero_of_radialPsi_eq_zero k w (radialPsi_eq_zero_of_norm_ge k (le_of_lt ?_))
    have hsub : ‖x‖ - ‖y - x‖ ≤ ‖y‖ := by
      have h := dist_triangle x y 0
      simp only [dist_eq_norm, sub_zero] at h
      have h2 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev x y
      linarith
    linarith

/-- `g_k` is `C³` everywhere. -/
theorem contDiff_gk (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) :
    ContDiff ℝ 3 (gk k w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ annOpen (d := d) k
  · exact (contDiffOn_gk_annOpen k hk1 hw).contDiffAt ((isOpen_annOpen (d := d) k).mem_nhds hx)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (gk_eventuallyEq_zero_of_notMem_annOpen k hk1 w hx)

/-- Each piece `ω̃_k` of the modified weight is `C³`. -/
theorem contDiff_omegaTildePiece (k : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hk1 : 1 ≤ k) : ContDiff ℝ 3 (omegaTildePiece (d := d) k w) := by
  rcases lt_or_ge k 2 with hk2 | hk2
  · have hfun : omegaTildePiece (d := d) k w = omegaPiece k w :=
      funext fun x => omegaTildePiece_of_lt k w hk2 x
    rw [hfun]
    exact contDiff_omegaPiece hw k le_rfl
  · rw [contDiff_iff_contDiffAt]
    intro x
    have hsum : ContDiffAt ℝ 3 (fun y => omegaPiece k w y + gk k w y) x :=
      ((contDiff_omegaPiece hw k le_rfl).contDiffAt).add
        ((contDiff_gk k (by omega) hw).contDiffAt)
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [omegaTildePiece_of_le k w hk2]
    rfl

/-! ## 6. Uniform derivative bounds for the pieces -/

/-- The uniform Lipschitz constant of the correction `g_k`. -/
noncomputable def gkLipConst (d : ℕ) : ℝ :=
  (2 * pkConst)⁻¹ * rpsCps d * 512000 * 2 * invNormConst d * pieceConst d

/-- The uniform Lipschitz constant of a single piece `ω̃_k`. -/
noncomputable def tildeLipConst (d : ℕ) : ℝ := pieceConst d + gkLipConst d

lemma gkLipConst_nonneg (d : ℕ) : 0 ≤ gkLipConst d := by
  have h1 : (0 : ℝ) ≤ (2 * pkConst)⁻¹ := by
    rw [inv_nonneg]; linarith [pkConst_pos]
  have h2 : (0 : ℝ) ≤ rpsCps d := (rpsCps_pos d).le
  have h3 : (0 : ℝ) ≤ invNormConst d := (invNormConst_pos d).le
  have h4 : (0 : ℝ) ≤ pieceConst d := (pieceConst_pos d).le
  rw [gkLipConst]
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 h2)
    (by norm_num)) (by norm_num)) h3) h4

lemma pieceConst_le_tildeLipConst (d : ℕ) : pieceConst d ≤ tildeLipConst d := by
  rw [tildeLipConst]; linarith [gkLipConst_nonneg d]

/-- `(2^k)·((2^k)^1)^{-1} = 1`. -/
lemma gk_growth_factor (k : ℕ) : ((2 : ℝ) ^ k) * (((2 : ℝ) ^ k) ^ 1)⁻¹ = 1 := by
  rw [pow_one, mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ k ≠ 0)]

/-- **Uniform bound on `‖D g_k‖`.**  The derivative of the correction is bounded by
`C_reg · C(d)`, uniformly in `k` and `x`. -/
theorem iteratedFDeriv_one_gk_le (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x : ℝᵈ) :
    ‖iteratedFDeriv ℝ 1 (gk k w) x‖ ≤ Creg * gkLipConst d := by
  by_cases hx : x ∈ annOpen (d := d) k
  · have h := norm_iteratedFDeriv_gk_le_Creg (d := d) hd k 1 (by norm_num) hk1 hw hwzero hCreg
      hwbound hx
    calc ‖iteratedFDeriv ℝ 1 (gk k w) x‖
        ≤ (2 * pkConst)⁻¹ * rpsCps d * 512000 * 2 ^ 1 * invNormConst d * Creg * pieceConst d
            * (2 : ℝ) ^ k * (((2 : ℝ) ^ k) ^ 1)⁻¹ := h
      _ = ((2 * pkConst)⁻¹ * rpsCps d * 512000 * 2 * invNormConst d * Creg * pieceConst d)
            * (((2 : ℝ) ^ k) * (((2 : ℝ) ^ k) ^ 1)⁻¹) := by ring
      _ = (2 * pkConst)⁻¹ * rpsCps d * 512000 * 2 * invNormConst d * Creg * pieceConst d := by
            rw [gk_growth_factor k, mul_one]
      _ = Creg * gkLipConst d := by
            rw [gkLipConst]; ring
  · have hev := (gk_eventuallyEq_zero_of_notMem_annOpen k hk1 w hx).iteratedFDeriv ℝ 1
    have hzero : iteratedFDeriv ℝ 1 (gk k w) x = 0 := by
      rw [hev.self_of_nhds]
      simp
    rw [hzero, norm_zero]
    exact mul_nonneg hCreg.le (gkLipConst_nonneg d)

/-- **Uniform bound on `‖D ω̃_k‖`.**  The derivative of every piece of the modified weight is
bounded by `C_reg · C_lip(d)`, uniformly in `k` and `x`. -/
theorem iteratedFDeriv_one_omegaTildePiece_le (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x : ℝᵈ) :
    ‖iteratedFDeriv ℝ 1 (omegaTildePiece k w) x‖ ≤ Creg * tildeLipConst d := by
  have hpow : (2 : ℝ) ^ ((k : ℝ) * (1 - ((1 : ℕ) : ℝ))) = 1 := by
    have h : ((k : ℝ) * (1 - ((1 : ℕ) : ℝ))) = 0 := by norm_num
    rw [h, Real.rpow_zero]
  rcases lt_or_ge k 2 with hk2 | hk2
  · have hfun : omegaTildePiece (d := d) k w = omegaPiece k w :=
      funext fun y => omegaTildePiece_of_lt k w hk2 y
    rw [hfun]
    refine le_trans (omegaPiece_iteratedFDeriv_le (d := d) k 1 (by norm_num) hCreg hw hwzero
      hwbound x) ?_
    rw [hpow, mul_one]
    exact mul_le_mul_of_nonneg_left (pieceConst_le_tildeLipConst d) hCreg.le
  · have hfun : omegaTildePiece (d := d) k w = omegaPiece k w + gk k w :=
      funext fun y => by rw [omegaTildePiece_of_le k w hk2]; rfl
    rw [hfun]
    have h1 : DifferentiableAt ℝ (omegaPiece k w) x :=
      ((contDiff_omegaPiece hw k le_rfl).contDiffAt).differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (gk k w) x :=
      ((contDiff_gk k (by omega) hw).contDiffAt).differentiableAt (by norm_num)
    rw [norm_iteratedFDeriv_one, fderiv_add h1 h2]
    refine le_trans (norm_add_le _ _) ?_
    have hP := omegaPiece_iteratedFDeriv_le (d := d) k 1 (by norm_num) hCreg hw hwzero hwbound x
    rw [norm_iteratedFDeriv_one, hpow, mul_one] at hP
    have h2' := iteratedFDeriv_one_gk_le (d := d) hd k hk1 hw hwzero hCreg hwbound x
    rw [norm_iteratedFDeriv_one] at h2'
    refine le_trans (add_le_add hP h2') ?_
    rw [tildeLipConst]
    nlinarith [hCreg.le, gkLipConst_nonneg d]

/-! ## 7. Lipschitz continuity of the modified weight -/

/-- A finset of natural numbers in which any two elements differ by at most one has at most two
elements. -/
lemma card_le_two_of_within_one (S : Finset ℕ)
    (h : ∀ a ∈ S, ∀ b ∈ S, a ≤ b → b ≤ a + 1) : S.card ≤ 2 := by
  rcases S.eq_empty_or_nonempty with hS | hne
  · simp [hS]
  · calc S.card ≤ ({S.min' hne, S.min' hne + 1} : Finset ℕ).card :=
        Finset.card_le_card (by
          intro k hk
          have hk' : S.min' hne ≤ k ∧ k ≤ S.min' hne + 1 := by
            refine ⟨S.min'_le k hk, ?_⟩
            rcases eq_or_lt_of_le (S.min'_le k hk) with heq | hlt
            · omega
            · exact h (S.min' hne) (S.min'_mem hne) k hk hlt.le
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega)
      _ ≤ 2 := by
        have h1 := Finset.card_insert_le (S.min' hne) ({S.min' hne + 1} : Finset ℕ)
        simp only [Finset.card_singleton] at h1
        omega

/-- At a given point at most four pieces of the modified weight are non-zero. -/
lemma card_omegaTildePiece_support_le (N : ℕ) (w : ℝᵈ → ℝ) (x : ℝᵈ) :
    ((Finset.range N).filter (fun k => omegaTildePiece k w x ≠ 0)).card ≤ 4 := by
  classical
  have hB : (((Finset.range N).filter (fun k => omegaTildePiece k w x ≠ 0)).filter
      (fun k => 2 ≤ k)).card ≤ 2 := by
    refine card_le_two_of_within_one _ fun a ha b hb hab => ?_
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    obtain ⟨haN, hap⟩ := Finset.mem_filter.mp ha1
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbN, hbp⟩ := Finset.mem_filter.mp hb1
    by_contra hcon
    push Not at hcon
    have hax : ‖x‖ < (2 : ℝ) ^ (a + 1) := by
      by_contra hle
      push Not at hle
      exact hap (omegaTildePiece_eq_zero_of_norm_ge a w hle)
    have hbx : (2 : ℝ) ^ (b - 1) < ‖x‖ := by
      by_contra hle
      push Not at hle
      exact hbp (omegaTildePiece_eq_zero_of_norm_le_pred b (by omega) w hle)
    have : (2 : ℝ) ^ (a + 1) ≤ (2 : ℝ) ^ (b - 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hsub : (Finset.range N).filter (fun k => omegaTildePiece k w x ≠ 0) ⊆
      ({0, 1} : Finset ℕ) ∪ (((Finset.range N).filter (fun k => omegaTildePiece k w x ≠ 0)).filter
        (fun k => 2 ≤ k)) := by
    intro k hk
    have hk' : k < N ∧ omegaTildePiece k w x ≠ 0 := by
      simpa only [Finset.mem_filter, Finset.mem_range] using hk
    rw [Finset.mem_union]
    rcases Nat.lt_or_ge k 2 with h | h
    · left
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    · right
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hk'.1, hk'.2⟩, h⟩
  calc ((Finset.range N).filter (fun k => omegaTildePiece k w x ≠ 0)).card
      ≤ (({0, 1} : Finset ℕ) ∪ (((Finset.range N).filter
          (fun k => omegaTildePiece k w x ≠ 0)).filter (fun k => 2 ≤ k))).card :=
        Finset.card_le_card hsub
    _ ≤ ({0, 1} : Finset ℕ).card + (((Finset.range N).filter
          (fun k => omegaTildePiece k w x ≠ 0)).filter (fun k => 2 ≤ k)).card :=
        Finset.card_union_le _ _
    _ ≤ 2 + 2 := by
        have h1 : ({0, 1} : Finset ℕ).card ≤ 2 := by decide
        omega

/-- The uniform Lipschitz constant of the modified weight. -/
noncomputable def omegaLipConst (d : ℕ) : ℝ := 8 * tildeLipConst d

lemma tildeLipConst_nonneg (d : ℕ) : 0 ≤ tildeLipConst d := by
  rw [tildeLipConst]; linarith [pieceConst_pos d, gkLipConst_nonneg d]

/-- **Each piece of the modified weight is Lipschitz**, with a constant uniform in `k`. -/
theorem lipschitz_omegaTildePiece (hd : 1 ≤ d) (k : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2)) (x₁ x₂ : ℝᵈ) :
    |omegaTildePiece k w x₁ - omegaTildePiece k w x₂| ≤ Creg * tildeLipConst d * ‖x₁ - x₂‖ := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · have h0 : omegaTildePiece (d := d) 0 w = fun _ => (0 : ℝ) := by
      rw [show omegaTildePiece (d := d) 0 w = omegaPiece 0 w from
        funext fun x => omegaTildePiece_of_lt 0 w (by norm_num) x, omegaPiece_zero w hwzero]
    rw [h0]
    simp only [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg hCreg.le (tildeLipConst_nonneg d)) (norm_nonneg _)
  · have hdiff : ∀ x ∈ (Set.univ : Set ℝᵈ), DifferentiableAt ℝ (omegaTildePiece k w) x :=
      fun x _ => ((contDiff_omegaTildePiece k hw hkpos).contDiffAt).differentiableAt (by norm_num)
    have hbound : ∀ x ∈ (Set.univ : Set ℝᵈ),
        ‖fderiv ℝ (omegaTildePiece k w) x‖ ≤ Creg * tildeLipConst d := by
      intro x _
      rw [← norm_iteratedFDeriv_one]
      exact iteratedFDeriv_one_omegaTildePiece_le hd k hkpos hw hwzero hCreg hwbound x
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_univ)
      (Set.mem_univ x₂) (Set.mem_univ x₁)
    rw [← Real.norm_eq_abs]
    exact h

/-- **The modified weight is Lipschitz**, with a constant depending only on `d` and `C_reg`. -/
theorem lipschitz_omegaTildeSum (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2)) (x₁ x₂ : ℝᵈ) :
    |omegaTildeSum w x₁ - omegaTildeSum w x₂| ≤ Creg * omegaLipConst d * ‖x₁ - x₂‖ := by
  classical
  obtain ⟨n, hn⟩ := exists_pow_gt_norm x₁
  obtain ⟨m, hm⟩ := exists_pow_gt_norm x₂
  set N := max n m with hN
  have hn' : ‖x₁‖ < (2 : ℝ) ^ N :=
    lt_of_lt_of_le hn (pow_le_pow_right₀ (by norm_num) (le_max_left n m))
  have hm' : ‖x₂‖ < (2 : ℝ) ^ N :=
    lt_of_lt_of_le hm (pow_le_pow_right₀ (by norm_num) (le_max_right n m))
  rw [omegaTildeSum_eq_sum_range N w hn', omegaTildeSum_eq_sum_range N w hm',
    ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  set A := (Finset.range (N + 1)).filter
    (fun k => omegaTildePiece k w x₁ ≠ 0 ∨ omegaTildePiece k w x₂ ≠ 0) with hA
  have hAsub : A ⊆ Finset.range (N + 1) := Finset.filter_subset _ _
  have hzero : ∀ k ∈ Finset.range (N + 1), k ∉ A →
      |omegaTildePiece k w x₁ - omegaTildePiece k w x₂| = 0 := by
    intro k hk hkA
    have hne : ¬(omegaTildePiece k w x₁ ≠ 0 ∨ omegaTildePiece k w x₂ ≠ 0) :=
      fun hc => hkA (Finset.mem_filter.mpr ⟨hk, hc⟩)
    push Not at hne
    rw [hne.1, hne.2, sub_self, abs_zero]
  rw [← Finset.sum_subset hAsub hzero]
  have hterm : ∀ k ∈ A, |omegaTildePiece k w x₁ - omegaTildePiece k w x₂|
      ≤ Creg * tildeLipConst d * ‖x₁ - x₂‖ := fun k _ =>
    lipschitz_omegaTildePiece hd k hw hwzero hCreg hwbound x₁ x₂
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : A.card ≤ 8 := by
    set T₁ := (Finset.range (N + 1)).filter (fun k => omegaTildePiece k w x₁ ≠ 0) with hT₁
    set T₂ := (Finset.range (N + 1)).filter (fun k => omegaTildePiece k w x₂ ≠ 0) with hT₂
    have hsub : A ⊆ T₁ ∪ T₂ := by
      intro k hk
      have hk' : k ∈ Finset.range (N + 1) ∧
          (omegaTildePiece k w x₁ ≠ 0 ∨ omegaTildePiece k w x₂ ≠ 0) := by
        rw [hA] at hk
        simpa only [Finset.mem_filter] using hk
      rw [hT₁, hT₂, Finset.mem_union]
      rcases hk'.2 with h | h
      · left; exact Finset.mem_filter.mpr ⟨hk'.1, h⟩
      · right; exact Finset.mem_filter.mpr ⟨hk'.1, h⟩
    have h1 : T₁.card ≤ 4 := by
      rw [hT₁]; exact card_omegaTildePiece_support_le (N + 1) w x₁
    have h2 : T₂.card ≤ 4 := by
      rw [hT₂]; exact card_omegaTildePiece_support_le (N + 1) w x₂
    calc A.card ≤ (T₁ ∪ T₂).card := Finset.card_le_card hsub
      _ ≤ T₁.card + T₂.card := Finset.card_union_le _ _
      _ ≤ 4 + 4 := by omega
  have hnn : (0 : ℝ) ≤ Creg * tildeLipConst d * ‖x₁ - x₂‖ :=
    mul_nonneg (mul_nonneg hCreg.le (tildeLipConst_nonneg d)) (norm_nonneg _)
  calc (A.card : ℝ) * (Creg * tildeLipConst d * ‖x₁ - x₂‖)
      ≤ 8 * (Creg * tildeLipConst d * ‖x₁ - x₂‖) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnn
    _ = Creg * omegaLipConst d * ‖x₁ - x₂‖ := by rw [omegaLipConst]; ring

end Submission.FUP
