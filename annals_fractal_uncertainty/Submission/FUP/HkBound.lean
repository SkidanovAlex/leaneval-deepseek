import Submission.FUP.ModifyWeight2
import Submission.FUP.GrowthSum
import Submission.Commons.Analysis.Calculus.iteratedFDeriv_intervalIntegral_comp_smul

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option maxHeartbeats 1600000

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Section 4 of the paper, IV: the derivative bounds for `h_k` and `g_k`

This module proves the last quantitative ingredient of `lem:modify_weight_lemma`: the estimate

`‖D^a g_k‖_∞ ≲ C_reg 2^{(1-a)k}`  (`0 ≤ a ≤ 3`),

by combining

* the support condition on the dyadic piece `ω_k = ψ_k(‖·‖)·ω` (`[2^{k-1}, 2^{k+1}]`),
* the exact formula for the derivatives of a windowed spherical average,
  `iteratedFDeriv_intervalIntegral_comp_smul`,
* the bound `‖D^b ω_k‖ ≤ C_reg C 2^{(1-b)k}` of `WeightPiece.norm_iteratedFDeriv_omegaPiece_le`,
* the Leibniz rule `norm_iteratedFDerivWithin_mul_le` and the homogeneity of `h_k`.

The key observation is that on the annulus `{2^k/4 < ‖x‖ < 4·2^k}` the spherical projection
`π ω_k(x) = ∫_0^∞ ω_k(tx) t^{-2}dt` collapses to the fixed window `∫_{1/8}^8`, so that the
`x`-dependence is confined to the argument `t•x` and the derivative formula applies verbatim.
-/

/-! ## 1. Support of the dyadic piece -/

/-- `ω_k(x) = 0` when `‖x‖ < 2^{k-1}` (for `k ≥ 1`). -/
lemma omegaPiece_eq_zero_of_norm_lt (k : ℕ) (hk : 1 ≤ k) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (h : ‖x‖ < (2 : ℝ) ^ k / 2) : omegaPiece k w x = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hle : ‖x‖ ≤ (2 : ℝ) ^ j := by
    have : (2 : ℝ) ^ (j + 1) / 2 = (2 : ℝ) ^ j := by
      rw [pow_succ]; ring
    rw [this] at h
    exact h.le
  rw [omegaPiece_apply, radialPsi_zero_of_norm_le j hle, zero_mul]

/-- `ω_k(x) = 0` when `2^{k+1} ≤ ‖x‖`. -/
lemma omegaPiece_eq_zero_of_norm_ge (k : ℕ) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (h : (2 : ℝ) ^ (k + 1) ≤ ‖x‖) : omegaPiece k w x = 0 := by
  rw [omegaPiece_apply, radialPsi_eq_zero_of_norm_ge k h, zero_mul]

/-- The dyadic piece is `C^b` for `b ≤ 3` when the weight is. -/
lemma contDiff_omegaPiece {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (k : ℕ) {b : ℕ} (hb : b ≤ 3) :
    ContDiff ℝ b (omegaPiece (d := d) k w) := by
  have hb3 : (b : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hb
  have h : ContDiff ℝ 3 (omegaPiece (d := d) k w) :=
    (contDiff_radialPsi (d := d) k).mul hw
  exact h.of_le hb3

/-! ## 2. The windowed spherical projection -/


/-- The weight of the windowed spherical average, `t ↦ (max t² (1/64))⁻¹`: it agrees with
`t^{-2}` on `[1/8, 8]` and is globally continuous (which is what
`iteratedFDeriv_intervalIntegral_comp_smul` requires). -/
noncomputable def winPhi (t : ℝ) : ℝ := (max (t ^ 2) (1 / 64))⁻¹

lemma winPhi_def (t : ℝ) : winPhi t = (max (t ^ 2) (1 / 64))⁻¹ := rfl

lemma continuous_winPhi : Continuous winPhi := by
  unfold winPhi
  exact ((continuous_id.pow 2).max continuous_const).inv₀
    (fun t => ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right _ _)))

lemma winPhi_nonneg (t : ℝ) : 0 ≤ winPhi t := by
  rw [winPhi_def]; positivity

lemma winPhi_eq_of_mem {t : ℝ} (ht : t ∈ Set.Icc (1 / 8 : ℝ) 8) : winPhi t = (t ^ 2)⁻¹ := by
  rw [winPhi_def, max_eq_left]
  nlinarith [ht.1]

lemma winPhi_mul_pow_le (b : ℕ) (hb : b ≤ 3) {t : ℝ} (ht : t ∈ Set.Icc (1 / 8 : ℝ) 8) :
    |winPhi t * t ^ b| ≤ 64 := by
  have ht1 : (1 / 8 : ℝ) ≤ t := ht.1
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le (by norm_num) ht1
  rw [winPhi_eq_of_mem ht]
  interval_cases b
  · rw [pow_zero, mul_one]
    have hnn : (0 : ℝ) ≤ (t ^ 2)⁻¹ := by positivity
    rw [abs_of_nonneg hnn]
    have h2 : ((1 : ℝ) / 64) ≤ t ^ 2 := by nlinarith
    have h3 : (t ^ 2)⁻¹ ≤ ((1 : ℝ) / 64)⁻¹ := inv_anti₀ (by norm_num) h2
    have h4 : ((1 : ℝ) / 64)⁻¹ = 64 := by norm_num
    linarith [h3, h4.le, h4.ge]
  · have h2 : ((t ^ 2)⁻¹) * t = t⁻¹ := by field_simp
    rw [pow_one, h2]
    have hnn : (0 : ℝ) ≤ t⁻¹ := by positivity
    rw [abs_of_nonneg hnn]
    have h3 : t⁻¹ ≤ ((1 : ℝ) / 8)⁻¹ := inv_anti₀ (by norm_num) ht1
    have h4 : ((1 : ℝ) / 8)⁻¹ = 8 := by norm_num
    linarith [h3, h4.le, h4.ge]
  · have h2 : (t ^ 2)⁻¹ * t ^ 2 = 1 := by field_simp
    rw [h2, abs_one]; norm_num
  · have h2 : (t ^ 2)⁻¹ * t ^ 3 = t := by field_simp
    rw [h2, abs_of_pos htpos]
    linarith [ht.2]

/-- The windowed spherical projection `x ↦ ∫_{1/8}^8 ω_k(tx) t^{-2}dt`, which agrees with
`‖x‖⁻¹·sphProj (ω_k) x` on the annulus `{2^k/4 < ‖·‖ < 4·2^k}`. -/
noncomputable def gwin (k : ℕ) (w : ℝᵈ → ℝ) (x : ℝᵈ) : ℝ :=
  ∫ t in (1 / 8 : ℝ)..8, omegaPiece k w (t • x) * winPhi t

lemma gwin_def (k : ℕ) (w : ℝᵈ → ℝ) (x : ℝᵈ) :
    gwin k w x = ∫ t in (1 / 8 : ℝ)..8, omegaPiece k w (t • x) * winPhi t := rfl

lemma eight_mul_div_four (k : ℕ) : 8 * ((2 : ℝ) ^ k / 4) = (2 : ℝ) ^ (k + 1) := by
  rw [pow_succ]; ring

/-- On the annulus `{2^k/4 < ‖x‖ < 4·2^k}` the half-line integral defining the spherical
projection can be replaced by the fixed window `[1/8, 8]`. -/
lemma sphProj_omegaPiece_eq_gwin (k : ℕ) (hk : 1 ≤ k) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (hlo : (2 : ℝ) ^ k / 4 < ‖x‖) (hhi : ‖x‖ < 4 * (2 : ℝ) ^ k) :
    sphProj (omegaPiece k w) x = gwin k w x := by
  have hsub : Set.Icc (1 / 8 : ℝ) 8 ⊆ Set.Ioi (0 : ℝ) :=
    fun t ht => lt_of_lt_of_le (by norm_num) ht.1
  have hzero : ∀ t ∈ Set.Ioi (0 : ℝ), t ∉ Set.Icc (1 / 8 : ℝ) 8 →
      omegaPiece k w (t • x) * (t ^ 2)⁻¹ = 0 := by
    intro t ht hnt
    have ht0 : 0 < t := ht
    have hcases : t < 1 / 8 ∨ 8 < t := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hnt
      exact hnt
    have hnorm : ‖t • x‖ = t * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    rcases hcases with h | h
    · have hlt : ‖t • x‖ < (2 : ℝ) ^ k / 2 := by
        rw [hnorm]
        have h1 : t * ‖x‖ < (1 / 8) * ‖x‖ := by nlinarith
        have h2 : (1 / 8) * ‖x‖ < (1 / 8) * (4 * (2 : ℝ) ^ k) := by nlinarith
        have h3 : (1 / 8) * (4 * (2 : ℝ) ^ k) = (2 : ℝ) ^ k / 2 := by ring
        linarith
      rw [omegaPiece_eq_zero_of_norm_lt k hk w hlt, zero_mul]
    · have hge : (2 : ℝ) ^ (k + 1) ≤ ‖t • x‖ := by
        rw [hnorm]
        have h1 : 8 * ((2 : ℝ) ^ k / 4) < 8 * ‖x‖ := by nlinarith
        have h2 : 8 * ‖x‖ < t * ‖x‖ := by nlinarith
        rw [eight_mul_div_four] at h1
        linarith
      rw [omegaPiece_eq_zero_of_norm_ge k w hge, zero_mul]
  rw [sphProj,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub
      (fun t ht => hzero t ht.1 ht.2),
    setIntegral_Icc_eq_intervalIntegral _ (by norm_num : (1 / 8 : ℝ) ≤ 8)]
  refine (intervalIntegral.integral_congr fun t ht => ?_).symm
  rw [uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 8)] at ht
  rw [winPhi_eq_of_mem ht]


/-! ## 3. Derivative bounds for the windowed spherical average -/

/-- **Derivative bound for the windowed spherical average.**  If the derivatives of `ω_k` up to
order `b ≤ 3` are bounded by `M` (globally), then so are those of `x ↦ ∫_{1/8}^8 ω_k(tx)t^{-2}dt`,
with a universal constant. -/
lemma norm_iteratedFDeriv_gwin_le (k b : ℕ) (hb : b ≤ 3) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    {M : ℝ} (hpiece : ∀ z : ℝᵈ, ‖iteratedFDeriv ℝ b (omegaPiece k w) z‖ ≤ M) (x : ℝᵈ) :
    ‖iteratedFDeriv ℝ b (gwin k w) x‖ ≤ 512 * M := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hpiece 0)
  have hformula : ∀ m : Fin b → ℝᵈ,
      (iteratedFDeriv ℝ b (gwin k w) x) m
        = ∫ t in (1 / 8 : ℝ)..8,
            (winPhi t * t ^ b) • (iteratedFDeriv ℝ b (omegaPiece k w) (t • x)) m := by
    intro m
    exact Commons.Analysis.Calculus.iteratedFDeriv_intervalIntegral_comp_smul
      (omegaPiece k w) winPhi b (1 / 8) 8 (contDiff_omegaPiece hw k hb) continuous_winPhi x m
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  rw [hformula m]
  have hpt : ∀ t ∈ Set.Icc (1 / 8 : ℝ) 8,
      ‖(winPhi t * t ^ b) • (iteratedFDeriv ℝ b (omegaPiece k w) (t • x)) m‖
        ≤ 64 * M * ∏ i, ‖m i‖ := by
    intro t ht
    have hsc : |winPhi t * t ^ b| ≤ 64 := winPhi_mul_pow_le b hb ht
    calc ‖(winPhi t * t ^ b) • (iteratedFDeriv ℝ b (omegaPiece k w) (t • x)) m‖
        = ‖winPhi t * t ^ b‖ * ‖(iteratedFDeriv ℝ b (omegaPiece k w) (t • x)) m‖ :=
          norm_smul _ _
      _ ≤ 64 * ‖(iteratedFDeriv ℝ b (omegaPiece k w) (t • x)) m‖ := by
          rw [Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right hsc (norm_nonneg _)
      _ ≤ 64 * (‖iteratedFDeriv ℝ b (omegaPiece k w) (t • x)‖ * ∏ i, ‖m i‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact ContinuousMultilinearMap.le_opNorm _ m
      _ ≤ 64 * (M * ∏ i, ‖m i‖) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hpiece _) ?_) (by norm_num)
          exact Finset.prod_nonneg (fun i _ => norm_nonneg _)
      _ = 64 * M * ∏ i, ‖m i‖ := by ring
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := 64 * M * ∏ i, ‖m i‖) fun t ht => ?_) ?_
  · have ht' : t ∈ Set.Icc (1 / 8 : ℝ) 8 := by
      have h : t ∈ Set.uIcc (1 / 8 : ℝ) 8 := uIoc_subset_uIcc ht
      rwa [uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 8)] at h
    exact hpt t ht'
  · have hprod : (0 : ℝ) ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
    have h2 : (64 * M * ∏ i, ‖m i‖) * |8 - (1 / 8 : ℝ)| ≤ 512 * M * ∏ i, ‖m i‖ := by
      rw [show |8 - (1 / 8 : ℝ)| = 63 / 8 from by norm_num]
      nlinarith [hM, hprod]
    exact h2


/-! ## 4. The derivative bound for `h_k` -/

/-- The open annulus on which the windowed spherical average and the exact spherical projection
agree: `{y | 2^k/4 < ‖y‖ < 4·2^k}`. -/
def annOpen (k : ℕ) : Set ℝᵈ := {y | (2 : ℝ) ^ k / 4 < ‖y‖ ∧ ‖y‖ < 4 * (2 : ℝ) ^ k}

lemma isOpen_annOpen (k : ℕ) : IsOpen (annOpen (d := d) k) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

/-- The support annulus of the dyadic piece is contained in the open annulus. -/
lemma annulus_subset_annOpen {k : ℕ} (hk : 1 ≤ k) :
    {x : ℝᵈ | (2 : ℝ) ^ (k - 1) ≤ ‖x‖ ∧ ‖x‖ ≤ (2 : ℝ) ^ (k + 1)} ⊆ annOpen (d := d) k := by
  intro x hx
  have hkpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  constructor
  · have h : (2 : ℝ) ^ k / 2 = (2 : ℝ) ^ (k - 1) := by
      have h' : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
        conv_lhs => rw [show k = (k - 1) + 1 from by omega]
        rw [pow_succ]
      rw [h']; ring
    nlinarith [hx.1, h.le, h.ge, hkpos]
  · have h : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ']
    nlinarith [hx.2, h.le, h.ge, hkpos]

/-- The windowed version of `h_k`: `‖x‖⁻¹ ∫_{1/8}^8 ω_k(tx)t^{-2}dt`.  It agrees with the
spherical projection `h_k` of the paper on the annulus `annOpen k`. -/
noncomputable def hkW (k : ℕ) (w : ℝᵈ → ℝ) (x : ℝᵈ) : ℝ := (‖x‖)⁻¹ * gwin k w x

lemma hkW_def (k : ℕ) (w : ℝᵈ → ℝ) (x : ℝᵈ) :
    hkW k w x = (‖x‖)⁻¹ * gwin k w x := rfl

/-- `h_k` agrees with its windowed version on the open annulus. -/
lemma hk_eq_hkW (k : ℕ) (hk1 : 1 ≤ k) (w : ℝᵈ → ℝ) {x : ℝᵈ}
    (hx : x ∈ annOpen (d := d) k) : hk k w x = hkW k w x := by
  have h := sphProj_omegaPiece_eq_gwin k hk1 w hx.1 hx.2
  rw [show hk k w x = sphProj (omegaPiece k w) x / ‖x‖ from rfl, h, hkW_def, div_eq_inv_mul]

/-- `(‖·‖)⁻¹` is `C³` on the open annulus. -/
lemma contDiffOn_inv_norm_annOpen (k : ℕ) : ContDiffOn ℝ 3 (fun y : ℝᵈ => (‖y‖)⁻¹)
    (annOpen (d := d) k) := by
  have hnorm : ∀ y ∈ annOpen (d := d) k, (0 : ℝ) < ‖y‖ := by
    intro y hy
    have hkpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    linarith [hy.1]
  have h1 : ContDiffOn ℝ 3 (fun y : ℝᵈ => y) (annOpen (d := d) k) := contDiffOn_id
  exact (h1.norm ℝ (fun y hy => norm_pos_iff.mp (hnorm y hy))).inv
    (fun y hy => ne_of_gt (hnorm y hy))

/-! ### Arithmetic of the dyadic powers -/

lemma inv_pow_two_pow (k m : ℕ) :
    (((2 : ℝ) ^ k) ^ m)⁻¹ = (2 : ℝ) ^ (-(((k * m : ℕ)) : ℝ)) := by
  rw [← pow_mul, ← Real.rpow_natCast]
  exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _).symm

lemma inv_two_pow (k : ℕ) : ((2 : ℝ) ^ k)⁻¹ = (2 : ℝ) ^ (-(k : ℝ)) := by
  rw [← Real.rpow_natCast]
  exact (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) _).symm

/-- Arithmetic: `(2^k)⁻¹ · 2^{k(1-b)} = ((2^k)^b)⁻¹`. -/
lemma inv_mul_rpow_one_sub (k b : ℕ) :
    ((2 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ ((k : ℝ) * (1 - (b : ℝ))) = (((2 : ℝ) ^ k) ^ b)⁻¹ := by
  rw [inv_pow_two_pow k b, inv_two_pow k, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring


/-- Arithmetic: the two families of dyadic powers agree. -/
lemma dyadic_factor_eq (k i b : ℕ) :
    (((2 : ℝ) ^ k) ^ (i + 1))⁻¹ * (2 : ℝ) ^ ((k : ℝ) * (1 - (b : ℝ) + (i : ℝ)))
      = ((2 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ ((k : ℝ) * (1 - (b : ℝ))) := by
  rw [inv_pow_two_pow k (i + 1), inv_two_pow k, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

/-- **Derivative bound for `h_k`.**  On the support annulus of `ω_k` the derivatives of `h_k` up
to order `3` are bounded by `C_reg C 2^{-bk}`. -/
lemma norm_iteratedFDeriv_hk_le (k b : ℕ) (hb : b ≤ 3) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w)
    (hcd : ContDiffOn ℝ 3 (gwin k w) (annOpen (d := d) k))
    {Creg Cinv Cp : ℝ} (hCinv : 0 < Cinv) (hCreg : 0 ≤ Creg) (hCp : 0 ≤ Cp)
    (hinv : ∀ n : ℕ, n ≤ 3 → ∀ x : ℝᵈ, x ≠ 0 →
      ‖iteratedFDeriv ℝ n (fun y : ℝᵈ => (‖y‖)⁻¹) x‖ ≤ Cinv * (‖x‖ ^ (n + 1))⁻¹)
    (hpiece : ∀ n : ℕ, n ≤ 3 → ∀ z : ℝᵈ,
      ‖iteratedFDeriv ℝ n (omegaPiece k w) z‖
        ≤ Creg * Cp * (2 : ℝ) ^ ((k : ℝ) * (1 - (n : ℝ))))
    {x : ℝᵈ} (hx : x ∈ annOpen (d := d) k) :
    ‖iteratedFDeriv ℝ b (hk k w) x‖
      ≤ 256000 * Cinv * Creg * Cp * (((2 : ℝ) ^ k) ^ b)⁻¹ := by
  set U := annOpen (d := d) k with hUdef
  have hUopen : IsOpen U := isOpen_annOpen (d := d) k
  have hU : UniqueDiffOn ℝ U := hUopen.uniqueDiffOn
  have hxpos : (0 : ℝ) < ‖x‖ := by
    have hkpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    linarith [hx.1]
  have hxne : x ≠ 0 := norm_pos_iff.mp hxpos
  have hCregCp : 0 ≤ Creg * Cp := mul_nonneg hCreg hCp
  -- Leibniz on the open annulus
  have hleib : ‖iteratedFDerivWithin ℝ b (fun y : ℝᵈ => (‖y‖)⁻¹ * gwin k w y) U x‖ ≤
      ∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i (fun y : ℝᵈ => (‖y‖)⁻¹) U x‖ *
        ‖iteratedFDerivWithin ℝ (b - i) (gwin k w) U x‖ :=
    norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (E := ℝᵈ) (A := ℝ) (s := U)
      (f := fun y : ℝᵈ => (‖y‖)⁻¹) (g := gwin k w) (N := (3 : ℕ∞ω))
      (contDiffOn_inv_norm_annOpen (d := d) k) hcd hU hx (by exact_mod_cast hb)
  have hglob : iteratedFDeriv ℝ b (hk k w) x
      = iteratedFDerivWithin ℝ b (fun y : ℝᵈ => (‖y‖)⁻¹ * gwin k w y) U x := by
    have e1 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (n := b) (f := hk k w) hUopen
    have e2 := iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (n := b)
      (f := fun y : ℝᵈ => (‖y‖)⁻¹ * gwin k w y) hUopen
    have e3 := iteratedFDerivWithin_congr (𝕜 := ℝ) (E := ℝᵈ) (s := U)
      (f₁ := hk k w) (f := fun y : ℝᵈ => (‖y‖)⁻¹ * gwin k w y)
      (fun y hy => hk_eq_hkW k hk1 w hy) hx b
    rw [← e1 hx, e3, e2 hx]
  rw [hglob]
  refine le_trans hleib ?_
  set F : ℝ := ((2 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ ((k : ℝ) * (1 - (b : ℝ))) with hF
  have hFnn : 0 ≤ F := mul_nonneg (by positivity) (Real.rpow_pos_of_pos (by norm_num) _).le
  have hsum : ∀ i ∈ Finset.range (b + 1),
      (b.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun y : ℝᵈ => (‖y‖)⁻¹) U x‖ *
        ‖iteratedFDerivWithin ℝ (b - i) (gwin k w) U x‖
      ≤ (b.choose i : ℝ) * 4 ^ (i + 1) * (Cinv * 512 * (Creg * Cp) * F) := by
    intro i hi
    have hib : i ≤ b := by have := Finset.mem_range.mp hi; omega
    have hbmi : b - i ≤ 3 := by omega
    have hi3 : i ≤ 3 := by omega
    have h1 : ‖iteratedFDerivWithin ℝ i (fun y : ℝᵈ => (‖y‖)⁻¹) U x‖
        ≤ Cinv * (‖x‖ ^ (i + 1))⁻¹ := by
      rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (n := i)
        (f := fun y : ℝᵈ => (‖y‖)⁻¹) hUopen) hx]
      exact hinv i hi3 x hxne
    have h2 : ‖iteratedFDerivWithin ℝ (b - i) (gwin k w) U x‖ ≤ 512 * (Creg * Cp *
        (2 : ℝ) ^ ((k : ℝ) * (1 - ((b - i : ℕ) : ℝ)))) := by
      rw [(iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (n := b - i) (f := gwin k w) hUopen) hx]
      exact norm_iteratedFDeriv_gwin_le (d := d) (w := w) k (b - i) hbmi hw
        (fun z => hpiece (b - i) hbmi z) x
    have hxinv : (‖x‖ ^ (i + 1))⁻¹ ≤ 4 ^ (i + 1) * (((2 : ℝ) ^ k) ^ (i + 1))⁻¹ := by
      have hlt : ((2 : ℝ) ^ k / 4) ^ (i + 1) < ‖x‖ ^ (i + 1) :=
        pow_lt_pow_left₀ hx.1 (show (0 : ℝ) ≤ (2 : ℝ) ^ k / 4 by positivity)
          (by omega : i + 1 ≠ 0)
      have hpos : (0 : ℝ) < ((2 : ℝ) ^ k / 4) ^ (i + 1) := by positivity
      have h1' : (‖x‖ ^ (i + 1))⁻¹ < (((2 : ℝ) ^ k / 4) ^ (i + 1))⁻¹ :=
        (inv_lt_inv₀ (show (0 : ℝ) < ‖x‖ ^ (i + 1) by positivity) hpos).2 hlt
      have h2' : (((2 : ℝ) ^ k / 4) ^ (i + 1))⁻¹
          = 4 ^ (i + 1) * (((2 : ℝ) ^ k) ^ (i + 1))⁻¹ := by
        rw [div_pow, inv_div, div_eq_mul_inv]
      rw [h2'] at h1'
      exact h1'.le
    have hexp : (2 : ℝ) ^ ((k : ℝ) * (1 - ((b - i : ℕ) : ℝ)))
        = (2 : ℝ) ^ ((k : ℝ) * (1 - (b : ℝ) + (i : ℝ))) := by
      congr 1
      push_cast [Nat.cast_sub hib]
      ring
    have hfac : (‖x‖ ^ (i + 1))⁻¹ * (2 : ℝ) ^ ((k : ℝ) * (1 - ((b - i : ℕ) : ℝ)))
        ≤ 4 ^ (i + 1) * F := by
      have h3 := mul_le_mul_of_nonneg_right hxinv
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
          ((k : ℝ) * (1 - (b : ℝ) + (i : ℝ)))).le
      calc (‖x‖ ^ (i + 1))⁻¹ * (2 : ℝ) ^ ((k : ℝ) * (1 - ((b - i : ℕ) : ℝ)))
          = (‖x‖ ^ (i + 1))⁻¹ * (2 : ℝ) ^ ((k : ℝ) * (1 - (b : ℝ) + (i : ℝ))) := by rw [hexp]
        _ ≤ (4 ^ (i + 1) * (((2 : ℝ) ^ k) ^ (i + 1))⁻¹)
              * (2 : ℝ) ^ ((k : ℝ) * (1 - (b : ℝ) + (i : ℝ))) := h3
        _ = 4 ^ (i + 1) * ((((2 : ℝ) ^ k) ^ (i + 1))⁻¹
              * (2 : ℝ) ^ ((k : ℝ) * (1 - (b : ℝ) + (i : ℝ)))) := by ring
        _ = 4 ^ (i + 1) * F := by rw [dyadic_factor_eq k i b, hF]
    have hchoose : (0 : ℝ) ≤ (b.choose i : ℝ) := by positivity
    have hCnn : (0 : ℝ) ≤ Cinv * (‖x‖ ^ (i + 1))⁻¹ :=
      mul_nonneg hCinv.le (by positivity)
    have h2nn : (0 : ℝ) ≤ 512 * (Creg * Cp *
        (2 : ℝ) ^ ((k : ℝ) * (1 - ((b - i : ℕ) : ℝ)))) :=
      mul_nonneg (by norm_num)
        (mul_nonneg hCregCp (Real.rpow_pos_of_pos (by norm_num) _).le)
    calc (b.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (fun y : ℝᵈ => (‖y‖)⁻¹) U x‖ *
          ‖iteratedFDerivWithin ℝ (b - i) (gwin k w) U x‖
        ≤ (b.choose i : ℝ) * (Cinv * (‖x‖ ^ (i + 1))⁻¹) *
            (512 * (Creg * Cp * (2 : ℝ) ^ ((k : ℝ) * (1 - ((b - i : ℕ) : ℝ))))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hchoose) h2 (norm_nonneg _)
            (mul_nonneg hchoose hCnn)
      _ = (b.choose i : ℝ) * (Cinv * 512 * (Creg * Cp)) *
            ((‖x‖ ^ (i + 1))⁻¹ * (2 : ℝ) ^ ((k : ℝ) * (1 - ((b - i : ℕ) : ℝ)))) := by ring
      _ ≤ (b.choose i : ℝ) * (Cinv * 512 * (Creg * Cp)) * F * 4 ^ (i + 1) := by
          have := mul_le_mul_of_nonneg_left hfac (by positivity : (0 : ℝ) ≤
            (b.choose i : ℝ) * (Cinv * 512 * (Creg * Cp)))
          linarith [this]
      _ = (b.choose i : ℝ) * 4 ^ (i + 1) * (Cinv * 512 * (Creg * Cp) * F) := by ring
  refine le_trans (Finset.sum_le_sum hsum) ?_
  have hbinom : (∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ) * 4 ^ (i + 1)) ≤ 500 := by
    have h1 : (∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ) * 4 ^ i) = 5 ^ b := by
      have h := add_pow (4 : ℝ) 1 b
      rw [show (4 : ℝ) + 1 = 5 from by norm_num] at h
      rw [h]
      exact Finset.sum_congr rfl fun i _ => by
        simp only [one_pow, mul_one]; ring
    have h2 : (∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ) * 4 ^ (i + 1)) = 4 * 5 ^ b := by
      rw [← h1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
    rw [h2]
    have : (5 : ℝ) ^ b ≤ 125 := by interval_cases b <;> norm_num
    linarith
  have hfact : (∑ i ∈ Finset.range (b + 1),
        (b.choose i : ℝ) * 4 ^ (i + 1) * (Cinv * 512 * (Creg * Cp) * F))
      = (∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ) * 4 ^ (i + 1))
        * (Cinv * 512 * (Creg * Cp) * F) := by
    rw [Finset.sum_mul]
  rw [hfact]
  have hCn : (0 : ℝ) ≤ Cinv * 512 * (Creg * Cp) * F :=
    mul_nonneg (mul_nonneg (mul_nonneg hCinv.le (by norm_num)) hCregCp) hFnn
  have hsum2 : (∑ i ∈ Finset.range (b + 1), (b.choose i : ℝ) * 4 ^ (i + 1))
        * (Cinv * 512 * (Creg * Cp) * F) ≤ 500 * (Cinv * 512 * (Creg * Cp) * F) :=
    mul_le_mul_of_nonneg_right hbinom hCn
  refine le_trans hsum2 (le_of_eq ?_)
  rw [hF, inv_mul_rpow_one_sub k b]
  ring



/-! ## 5. The bound on the constants `q_k` -/

/-- If all the spherical projections are bounded by `C`, so is their infimum `q_k`. -/
lemma bddBelow_sphProj_omegaPiece_of_bound {k : ℕ} {w : ℝᵈ → ℝ} {C : ℝ}
    (h : ∀ v : {v : ℝᵈ // ‖v‖ = 1}, |sphProj (omegaPiece k w) v| ≤ C) :
    BddBelow (Set.range fun v : {v : ℝᵈ // ‖v‖ = 1} => sphProj (omegaPiece k w) v) :=
  ⟨-C, by rintro y ⟨v, rfl⟩; exact (abs_le.mp (h v)).1⟩

lemma abs_qk_le_of_proj_bound (hd : 1 ≤ d) {k : ℕ} {w : ℝᵈ → ℝ} {C : ℝ}
    (h : ∀ v : {v : ℝᵈ // ‖v‖ = 1}, |sphProj (omegaPiece k w) v| ≤ C) : |qk k w| ≤ C := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · refine le_qk hd k w fun v => (abs_le.mp (h v)).1
  · refine le_trans (qk_le k w (bddBelow_sphProj_omegaPiece_of_bound h) (unitVec hd)) ?_
    exact (abs_le.mp (h (unitVec hd))).2

/-- The spherical projection at a unit vector is a value of `h_k` on the support annulus. -/
lemma abs_sphProj_le_of_hk_bound {k : ℕ} {w : ℝᵈ → ℝ} {C : ℝ}
    (hbd : ∀ x ∈ annOpen (d := d) k, ‖hk k w x‖ ≤ C) {v : ℝᵈ} (hv : ‖v‖ = 1) :
    |sphProj (omegaPiece k w) v| ≤ C := by
  have hc : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hnorm : ‖(2 : ℝ) ^ k • v‖ = (2 : ℝ) ^ k := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, hv, mul_one]
  have hmem : (2 : ℝ) ^ k • v ∈ annOpen (d := d) k := by
    refine ⟨?_, ?_⟩ <;> rw [hnorm] <;> linarith
  rw [sphProj_omegaPiece_eq_hk k w hv, ← hk_smul k w hc v]
  simpa [Real.norm_eq_abs] using hbd _ hmem

/-- **The constants `q_k` are bounded by the regularity constant.**  This is the estimate
`|q_k| ≲ C_reg` of §4, obtained from the derivative bound for `h_k` at order `0`. -/
lemma abs_qk_le_hk_bound (hd : 1 ≤ d) {k : ℕ} {w : ℝᵈ → ℝ} {C : ℝ}
    (hbd : ∀ x ∈ annOpen (d := d) k, ‖hk k w x‖ ≤ C) : |qk k w| ≤ C :=
  abs_qk_le_of_proj_bound hd fun v => abs_sphProj_le_of_hk_bound hbd v.2

/-- The explicit form with the constants of `norm_iteratedFDeriv_hk_le`. -/
lemma abs_qk_le_regular (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w)
    (hcd : ContDiffOn ℝ 3 (gwin k w) (annOpen (d := d) k))
    {Creg Cinv Cp : ℝ} (hCinv : 0 < Cinv) (hCreg : 0 ≤ Creg) (hCp : 0 ≤ Cp)
    (hinv : ∀ n : ℕ, n ≤ 3 → ∀ x : ℝᵈ, x ≠ 0 →
      ‖iteratedFDeriv ℝ n (fun y : ℝᵈ => (‖y‖)⁻¹) x‖ ≤ Cinv * (‖x‖ ^ (n + 1))⁻¹)
    (hpiece : ∀ n : ℕ, n ≤ 3 → ∀ z : ℝᵈ,
      ‖iteratedFDeriv ℝ n (omegaPiece k w) z‖
        ≤ Creg * Cp * (2 : ℝ) ^ ((k : ℝ) * (1 - (n : ℝ)))) :
    |qk k w| ≤ 256000 * Cinv * Creg * Cp := by
  refine abs_qk_le_hk_bound hd fun x hx => ?_
  have h := norm_iteratedFDeriv_hk_le (k := k) (b := 0) (by norm_num) hk1 hw hcd hCinv hCreg
    hCp hinv hpiece hx
  simpa [norm_iteratedFDeriv_zero] using h

end Submission.FUP
