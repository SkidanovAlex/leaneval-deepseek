import Submission.FUP.ModifyWeight

open MeasureTheory Metric Filter
open scoped Real BigOperators Topology

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# Section 4 of the paper, II: the pieces `ω̃_k`

This module carries out the construction of §4 of Cohen's paper.  With

* `ω_k = ψ_k(‖·‖)·ω` (`omegaPiece`),
* `h_k(x) = π_{S^{d-1}} ω_k(x̂) = sphProj (ω_k) x / ‖x‖` (`hk`),
* `q_k = ⨅_{‖v̂‖=1} π ω_k(v̂)` (`qk`),
* `g_k(x) = (p_k)⁻¹ ψ_k(‖x‖)(q_k - h_k(x))` (`gk`),
* `ω̃_k = ω_k + g_k` (`omegaTilde`),

the central point is that `π_{S^{d-1}} ω̃_k = q_k` is constant (`sphProj_omegaTilde`), so that
Lemma 4.1 of the paper telescopes over the dyadic pieces.
-/

/-! ## 1. Integrability of ray integrals -/

/-- A function on `(0,∞)` which vanishes outside a compact subinterval of `(0,∞)` and is bounded
there is integrable. -/
lemma integrableOn_Ioi_of_bound_Icc {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hmeas : AEStronglyMeasurable g (volume.restrict (Set.Icc a b))) (C : ℝ)
    (hbd : ∀ t ∈ Set.Icc a b, ‖g t‖ ≤ C)
    (hzero : ∀ t, 0 < t → (t < a ∨ b < t) → g t = 0) :
    IntegrableOn g (Set.Ioi 0) volume := by
  have hμ : volume (Set.Icc a b) < ⊤ := measure_Icc_lt_top
  have hbound : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖g t‖ ≤ C := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Eventually.of_forall (fun t ht => hbd t ht)
  have h1 : IntegrableOn g (Set.Icc a b) volume := IntegrableOn.of_bound hμ hmeas C hbound
  have h2 : Integrable ((Set.Icc a b).indicator g) volume :=
    h1.integrable_indicator measurableSet_Icc
  have h3 : Integrable ((Set.Icc a b).indicator g) (volume.restrict (Set.Ioi 0)) :=
    h2.mono_measure Measure.restrict_le_self
  have h4 : (Set.Icc a b).indicator g =ᵐ[volume.restrict (Set.Ioi 0)] g := by
    show ∀ᵐ t ∂volume.restrict (Set.Ioi 0), (Set.Icc a b).indicator g t = g t
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    by_cases hmem : t ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      have hmem' : t < a ∨ b < t := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hmem
        exact hmem
      exact (hzero t ht hmem').symm
  exact h3.congr h4

/-- As above, with the boundedness supplied by continuity. -/
lemma integrableOn_Ioi_of_continuousOn_compact {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hcont : ContinuousOn g (Set.Icc a b))
    (hzero : ∀ t, 0 < t → (t < a ∨ b < t) → g t = 0) :
    IntegrableOn g (Set.Ioi 0) volume := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  exact integrableOn_Ioi_of_bound_Icc ha (hcont.aestronglyMeasurable measurableSet_Icc) C hC hzero

/-! ## 2. Support and smoothness of the dyadic pieces -/

lemma contDiff_dyadPsi (k : ℕ) : ContDiff ℝ 3 (dyadPsi k) :=
  ((contDiff_dyadPhi k).sub (contDiff_dyadPhi (k + 1))).of_le (WithTop.coe_le_coe.mpr le_top)

/-- `ψ_k` vanishes for `t ≤ 2^{k-1}`, `k ≥ 1`. -/
lemma dyadPsi_eq_zero_of_le_pow (k : ℕ) (hk : 1 ≤ k) {t : ℝ} (h : t ≤ (2 : ℝ) ^ (k - 1)) :
    dyadPsi k t = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h' : t ≤ (2 : ℝ) ^ j := by simpa using h
  exact dyadPsi_zero_of_le j h'

/-- `ψ_k` vanishes for `2^{k+1} ≤ t`, `k ≥ 1`. -/
lemma dyadPsi_eq_zero_of_ge_pow (k : ℕ) (hk : 1 ≤ k) {t : ℝ} (h : (2 : ℝ) ^ (k + 1) ≤ t) :
    dyadPsi k t = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h' : (2 : ℝ) ^ (j + 2) ≤ t := by simpa using h
  exact dyadPsi_zero_of_ge j h'

/-- On a ray `t • v` with `t > 0` and `‖v‖ = 1` the radial cutoff is `ψ_k(t)`. -/
lemma radialPsi_smul_unit (k : ℕ) {v : ℝᵈ} (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 < t) :
    radialPsi (d := d) k (t • v) = dyadPsi k t := by
  rw [radialPsi, norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv, mul_one]

/-- `t ↦ ψ_k(t)·u(t)·t^{-2}` is integrable on `(0,∞)` for `k ≥ 1` and continuous `u`. -/
lemma integrableOn_dyadPsi_mul (k : ℕ) (hk : 1 ≤ k) {u : ℝ → ℝ} (hu : Continuous u) :
    IntegrableOn (fun t : ℝ => dyadPsi k t * u t * (t ^ 2)⁻¹) (Set.Ioi 0) := by
  have ha : (0:ℝ) < (2:ℝ) ^ (k - 1) := by positivity
  refine integrableOn_Ioi_of_continuousOn_compact (b := (2:ℝ) ^ (k + 1)) ha ?_ ?_
  · have h0 : ContinuousOn (fun t : ℝ => dyadPsi k t * u t) (Set.Icc ((2:ℝ)^(k-1)) ((2:ℝ)^(k+1))) :=
      ((contDiff_dyadPsi k).continuous.continuousOn).mul hu.continuousOn
    have h1 : ContinuousOn (fun t : ℝ => t ^ 2) (Set.Icc ((2:ℝ)^(k-1)) ((2:ℝ)^(k+1))) :=
      continuousOn_id.pow 2
    exact h0.mul (h1.inv₀ (fun t ht => by
      have : (0:ℝ) < t := lt_of_lt_of_le ha ht.1
      positivity))
  · intro t ht hlt
    rw [hlt.elim (fun h => dyadPsi_eq_zero_of_le_pow k hk (le_of_lt h))
      (fun h => dyadPsi_eq_zero_of_ge_pow k hk (le_of_lt h))]
    ring

/-! ## 3. The weight `h_k = π ω_k` and its bound -/

/-- The (weighted) spherical projection of `ω_k` along the ray through `x`:
`h_k(x) = π_{S^{d-1}} ω_k(x̂) = sphProj (ω_k) x / ‖x‖`. -/
noncomputable def hk (k : ℕ) (w : ℝᵈ → ℝ) (x : ℝᵈ) : ℝ :=
  sphProj (omegaPiece k w) x / ‖x‖

/-- `h_k` is homogeneous of degree zero on the positive rays. -/
lemma hk_smul (k : ℕ) (w : ℝᵈ → ℝ) {c : ℝ} (hc : 0 < c) (x : ℝᵈ) :
    hk k w (c • x) = hk k w x := by
  unfold hk
  rw [sphProj_smul _ _ hc, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  field_simp

/-- On the unit sphere `h_k` is the spherical projection. -/
lemma sphProj_omegaPiece_eq_hk (k : ℕ) (w : ℝᵈ → ℝ) {v : ℝᵈ} (hv : ‖v‖ = 1) :
    sphProj (omegaPiece k w) v = hk k w v := by
  unfold hk
  rw [hv, div_one]

/-- A crude bound for the spherical projection of a dyadic piece: it is controlled by `C_reg`
(and *not* by the growth functional — that refinement is the content of §4's `Σ|q_k|` estimate). -/
lemma abs_sphProj_omegaPiece_le (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ} {Creg : ℝ}
    (hCreg : 0 ≤ Creg) (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {v : ℝᵈ} (hv : ‖v‖ = 1) :
    |sphProj (omegaPiece k w) v| ≤ Creg * (2 : ℝ) ^ (k + 2) := by
  have ha : (0 : ℝ) < (2 : ℝ) ^ (k - 1) := by positivity
  have ha1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k - 1) := one_le_pow₀ (by norm_num)
  have hab : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hsub : Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)) ⊆ Set.Ioi (0 : ℝ) :=
    fun t ht => lt_of_lt_of_le ha ht.1
  have hzero : ∀ t ∈ Set.Ioi (0 : ℝ), t ∉ Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)) →
      omegaPiece k w (t • v) * (t ^ 2)⁻¹ = 0 := by
    intro t ht hnot
    have hlt : t < (2 : ℝ) ^ (k - 1) ∨ (2 : ℝ) ^ (k + 1) < t := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hnot
      exact hnot
    rw [omegaPiece_apply, radialPsi_smul_unit k hv ht,
      hlt.elim (fun h => dyadPsi_eq_zero_of_le_pow k hk1 (le_of_lt h))
        (fun h => dyadPsi_eq_zero_of_ge_pow k hk1 (le_of_lt h))]
    ring
  have hbd : ∀ t ∈ Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)),
      ‖omegaPiece k w (t • v) * (t ^ 2)⁻¹‖ ≤ 2 * Creg := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le ha ht.1
    have ht1 : (1 : ℝ) ≤ t := le_trans ha1 ht.1
    have hnorm : ‖t • v‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hv, mul_one]
    have h1 : ‖radialPsi (d := d) k (t • v)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (radialPsi_nonneg k (t • v))]
      exact radialPsi_le_one k (t • v)
    have h2 : ‖(t ^ 2)⁻¹‖ = (t ^ 2)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h3 : (1 + t ^ 2) ^ ((1 : ℝ) / 2) ≤ 1 + t ^ 2 := by
      have hx1 : (1 : ℝ) ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
      have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 : ℝ) / 2 ≤ 1)
      simpa using this
    have hw_t : ‖w (t • v)‖ ≤ Creg * (1 + t ^ 2) := by
      have h := hreg (t • v)
      rw [hnorm] at h
      exact le_trans h (mul_le_mul_of_nonneg_left h3 hCreg)
    have hkey : (1 + t ^ 2) * (t ^ 2)⁻¹ ≤ 2 := by
      have h0 : (0 : ℝ) < t ^ 2 := by positivity
      have hle : (1 + t ^ 2) ≤ 2 * t ^ 2 := by nlinarith
      calc (1 + t ^ 2) * (t ^ 2)⁻¹ ≤ (2 * t ^ 2) * (t ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = 2 := by rw [mul_assoc, mul_inv_cancel₀ h0.ne', mul_one]
    have h0 : (0 : ℝ) ≤ (t ^ 2)⁻¹ := by positivity
    have hn : (0 : ℝ) ≤ ‖w (t • v)‖ := norm_nonneg _
    calc ‖omegaPiece k w (t • v) * (t ^ 2)⁻¹‖
        = ‖radialPsi (d := d) k (t • v)‖ * ‖w (t • v)‖ * (t ^ 2)⁻¹ := by
          rw [omegaPiece_apply, norm_mul, norm_mul, h2]
      _ ≤ 1 * ‖w (t • v)‖ * (t ^ 2)⁻¹ := by
          have hbc : (0 : ℝ) ≤ ‖w (t • v)‖ * (t ^ 2)⁻¹ := mul_nonneg hn h0
          have := mul_le_mul_of_nonneg_right h1 hbc
          linarith
      _ ≤ 1 * (Creg * (1 + t ^ 2)) * (t ^ 2)⁻¹ := by
          have := mul_le_mul_of_nonneg_right hw_t h0
          linarith
      _ = Creg * ((1 + t ^ 2) * (t ^ 2)⁻¹) := by ring
      _ ≤ Creg * 2 := mul_le_mul_of_nonneg_left hkey hCreg
      _ = 2 * Creg := by ring
  have hba : (2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ (k - 1) = 3 * (2 : ℝ) ^ (k - 1) := by
    rw [show k + 1 = (k - 1) + 2 from by omega, pow_add]
    norm_num
    ring
  have hpow : (2 : ℝ) ^ (k + 2) = (2 : ℝ) ^ (k - 1) * 8 := by
    rw [show k + 2 = (k - 1) + 3 from by omega, pow_add]
    norm_num
  rw [sphProj, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume)
    measurableSet_Ioi hsub (fun x hx => hzero x hx.1 hx.2)]
  calc |∫ t in Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1)),
        omegaPiece k w (t • v) * (t ^ 2)⁻¹|
      ≤ (2 * Creg) * volume.real (Set.Icc ((2 : ℝ) ^ (k - 1)) ((2 : ℝ) ^ (k + 1))) :=
        norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top hbd
    _ = 2 * Creg * ((2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ (k - 1)) := by
        rw [Real.volume_real_Icc_of_le hab]
    _ = 2 * Creg * (3 * (2 : ℝ) ^ (k - 1)) := by rw [hba]
    _ ≤ Creg * (2 : ℝ) ^ (k + 2) := by
        rw [hpow]
        nlinarith [hCreg, pow_pos (by norm_num : (0 : ℝ) < 2) (k - 1)]

/-! ## 4. The constants `q_k` -/

lemma exists_unit_vector (hd : 1 ≤ d) : ∃ v : ℝᵈ, ‖v‖ = 1 := by
  refine ⟨PiLp.single 2 ⟨0, hd⟩ (1 : ℝ), ?_⟩
  rw [PiLp.norm_single]
  simp

/-- A chosen unit vector, available when `d ≥ 1`. -/
noncomputable def unitVec (hd : 1 ≤ d) : {v : ℝᵈ // ‖v‖ = 1} :=
  ⟨Classical.choose (exists_unit_vector hd), Classical.choose_spec (exists_unit_vector hd)⟩

/-- `q_k = ⨅_{‖v̂‖=1} π ω_k(v̂)`. -/
noncomputable def qk (k : ℕ) (w : ℝᵈ → ℝ) : ℝ :=
  ⨅ v : {v : ℝᵈ // ‖v‖ = 1}, sphProj (omegaPiece k w) v

lemma bddBelow_sphProj_omegaPiece (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ} {Creg : ℝ}
    (hCreg : 0 ≤ Creg) (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2)) :
    BddBelow (Set.range (fun v : {v : ℝᵈ // ‖v‖ = 1} => sphProj (omegaPiece k w) v)) :=
  ⟨-(Creg * (2 : ℝ) ^ (k + 2)), fun y hy => by
    obtain ⟨v, rfl⟩ := hy
    exact (abs_le.mp (abs_sphProj_omegaPiece_le k hk1 hCreg hreg v.2)).1⟩

lemma qk_le (k : ℕ) (w : ℝᵈ → ℝ)
    (hB : BddBelow (Set.range (fun v : {v : ℝᵈ // ‖v‖ = 1} => sphProj (omegaPiece k w) v)))
    (v : {v : ℝᵈ // ‖v‖ = 1}) : qk k w ≤ sphProj (omegaPiece k w) v :=
  ciInf_le hB v

lemma le_qk (hd : 1 ≤ d) (k : ℕ) (w : ℝᵈ → ℝ) {c : ℝ}
    (h : ∀ v : {v : ℝᵈ // ‖v‖ = 1}, c ≤ sphProj (omegaPiece k w) v) : c ≤ qk k w := by
  haveI : Nonempty {v : ℝᵈ // ‖v‖ = 1} := ⟨unitVec hd⟩
  exact le_ciInf h

lemma abs_qk_le (hd : 1 ≤ d) (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ} {Creg : ℝ}
    (hCreg : 0 ≤ Creg) (hreg : ∀ x, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2)) :
    |qk k w| ≤ Creg * (2 : ℝ) ^ (k + 2) := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · refine le_qk hd k w (fun v => ?_)
    exact (abs_le.mp (abs_sphProj_omegaPiece_le k hk1 hCreg hreg v.2)).1
  · refine le_trans (qk_le k w (bddBelow_sphProj_omegaPiece k hk1 hCreg hreg) (unitVec hd)) ?_
    exact (abs_le.mp (abs_sphProj_omegaPiece_le k hk1 hCreg hreg (unitVec hd).2)).2

/-! ## 5. The correction `g_k` and the identity `π ω̃_k = q_k` -/

/-- The correction term of §4: `g_k(x) = (p_k)⁻¹ ψ_k(‖x‖)(q_k - h_k(x))`. -/
noncomputable def gk (k : ℕ) (w : ℝᵈ → ℝ) (x : ℝᵈ) : ℝ :=
  (pk k)⁻¹ * radialPsi (d := d) k x * (qk k w - hk k w x)

/-- The modified dyadic piece `ω̃_k = ω_k + g_k`. -/
noncomputable def omegaTilde (k : ℕ) (w : ℝᵈ → ℝ) : ℝᵈ → ℝ :=
  fun x => omegaPiece k w x + gk k w x

lemma sphProj_sub (f g : ℝᵈ → ℝ) (v : ℝᵈ)
    (hf : IntegrableOn (fun t : ℝ => f (t • v) * (t ^ 2)⁻¹) (Set.Ioi 0))
    (hg : IntegrableOn (fun t : ℝ => g (t • v) * (t ^ 2)⁻¹) (Set.Ioi 0)) :
    sphProj (fun x => f x - g x) v = sphProj f v - sphProj g v := by
  simp only [sphProj]
  rw [show (fun t : ℝ => (f (t • v) - g (t • v)) * (t ^ 2)⁻¹)
      = fun t : ℝ => f (t • v) * (t ^ 2)⁻¹ - g (t • v) * (t ^ 2)⁻¹ from by
        funext t; ring]
  rw [integral_sub hf hg]

lemma integrableOn_omegaPiece_ray (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ} (hw : Continuous w)
    {v : ℝᵈ} (hv : ‖v‖ = 1) :
    IntegrableOn (fun t : ℝ => omegaPiece k w (t • v) * (t ^ 2)⁻¹) (Set.Ioi 0) := by
  have h := integrableOn_dyadPsi_mul k hk1 (u := fun t : ℝ => w (t • v))
    (hw.comp (continuous_id.smul continuous_const))
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  show dyadPsi k t * w (t • v) * (t ^ 2)⁻¹ = omegaPiece k w (t • v) * (t ^ 2)⁻¹
  rw [omegaPiece_apply, radialPsi_smul_unit k hv ht]

lemma integrableOn_gk_ray (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ} {v : ℝᵈ} (hv : ‖v‖ = 1) :
    IntegrableOn (fun t : ℝ => gk k w (t • v) * (t ^ 2)⁻¹) (Set.Ioi 0) := by
  have h := integrableOn_dyadPsi_mul k hk1
    (u := fun _ : ℝ => (pk k)⁻¹ * (qk k w - hk k w v)) continuous_const
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp only [gk]
  rw [radialPsi_smul_unit k hv ht, hk_smul k w ht v]
  ring

lemma sphProj_radialPsi_mul_const (k : ℕ) (c : ℝ) {v : ℝᵈ} (hv : ‖v‖ = 1) :
    sphProj (fun x : ℝᵈ => radialPsi (d := d) k x * c) v = c * pk k := by
  rw [sphProj_congr (g := fun x : ℝᵈ => c * radialPsi (d := d) k x)
    (fun x => mul_comm _ _) v, sphProj_const_mul, sphProj_radialPsi_eq_pk k hv]

lemma sphProj_radialPsi_mul_hk (k : ℕ) {w : ℝᵈ → ℝ} {v : ℝᵈ} (hv : ‖v‖ = 1) :
    sphProj (fun x : ℝᵈ => radialPsi (d := d) k x * hk k w x) v = hk k w v * pk k := by
  rw [sphProj]
  have hcongr : ∫ t in Set.Ioi 0, radialPsi (d := d) k (t • v) * hk k w (t • v) * (t ^ 2)⁻¹
      = ∫ t in Set.Ioi 0, dyadPsi k t * hk k w v * (t ^ 2)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [radialPsi_smul_unit k hv ht, hk_smul k w ht v]
  rw [hcongr]
  rw [show (fun t : ℝ => dyadPsi k t * hk k w v * (t ^ 2)⁻¹)
      = fun t : ℝ => hk k w v * (dyadPsi k t * (t ^ 2)⁻¹) from by funext t; ring]
  rw [integral_const_mul]
  rfl

lemma sphProj_gk (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ} (hw : Continuous w) {v : ℝᵈ}
    (hv : ‖v‖ = 1) :
    sphProj (gk k w) v = qk k w - sphProj (omegaPiece k w) v := by
  have hI1 : IntegrableOn
      (fun t : ℝ => radialPsi (d := d) k (t • v) * qk k w * (t ^ 2)⁻¹) (Set.Ioi 0) := by
    have h := integrableOn_dyadPsi_mul k hk1 (u := fun _ : ℝ => qk k w) continuous_const
    refine h.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [radialPsi_smul_unit k hv ht]
  have hI2 : IntegrableOn
      (fun t : ℝ => radialPsi (d := d) k (t • v) * hk k w (t • v) * (t ^ 2)⁻¹) (Set.Ioi 0) := by
    have h := integrableOn_dyadPsi_mul k hk1 (u := fun _ : ℝ => hk k w v) continuous_const
    refine h.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [radialPsi_smul_unit k hv ht, hk_smul k w ht v]
  have hgk : gk k w = fun x : ℝᵈ =>
      (pk k)⁻¹ * (radialPsi (d := d) k x * qk k w - radialPsi (d := d) k x * hk k w x) := by
    funext x; simp only [gk]; ring
  rw [hgk, sphProj_const_mul,
    sphProj_sub _ _ _ hI1 hI2, sphProj_radialPsi_mul_const k (qk k w) hv,
    sphProj_radialPsi_mul_hk k hv, sphProj_omegaPiece_eq_hk k w hv]
  have hpk : pk k ≠ 0 := pk_ne_zero k hk1
  field_simp

/-- **The defining property of the modified piece**: `π_{S^{d-1}} ω̃_k = q_k` is constant on the
unit sphere. -/
theorem sphProj_omegaTilde (k : ℕ) (hk1 : 1 ≤ k) {w : ℝᵈ → ℝ} (hw : Continuous w) {v : ℝᵈ}
    (hv : ‖v‖ = 1) :
    sphProj (omegaTilde k w) v = qk k w := by
  have hI1 := integrableOn_omegaPiece_ray k hk1 hw hv
  have hI2 := integrableOn_gk_ray (w := w) k hk1 hv
  have hfun : omegaTilde k w = fun x : ℝᵈ => omegaPiece k w x + gk k w x := rfl
  rw [hfun, sphProj_add _ _ _ hI1 hI2, sphProj_gk k hk1 hw hv]
  ring

end Submission.FUP
