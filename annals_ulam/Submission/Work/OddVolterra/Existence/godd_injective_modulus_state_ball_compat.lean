import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.base_volterra
import Submission.Work.OddCurve.detKernel_ne_zero
import Submission.Work.OddVolterra.KernelExt.KvecM_eq_Kvec
import Submission.Work.OddVolterra.Existence.krad_pos_state_region
import Submission.Work.OddVolterra.Existence.Godd_zero_diag
import Submission.Work.OddVolterra.Kernel.Diag
import Submission.Work.Geometry.Ulam.AbelBeta

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam

noncomputable section

/-! ## The diagonal form of the Abel kernels and of `Godd` -/

/-- The diagonal value of the common denominator `Kden`. -/
lemma Kden_diag_c (h : ℝ → ℝ) (s t : ℝ) :
    Kden h s s t = Real.sqrt (lineSlope h s t * (2 * line h s t)) := by
  unfold Kden lineSlope line
  rw [hquot_self]
  congr 1
  ring

/-- The diagonal value of the first Abel kernel, in explicit closed form. -/
def K1d_c (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (Nat.doubleFactorial (2 * n + 1) : ℝ) *
    (-(line h s t * lineSlope h s t)) ^ (n + 1) /
    Real.sqrt (lineSlope h s t * (2 * line h s t))

/-- The diagonal value of the second Abel kernel, in explicit closed form. -/
def K2d_c (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (Nat.doubleFactorial (2 * n - 1) : ℝ) *
    (-(line h s t * lineSlope h s t)) ^ n * lineSlope h s t /
    Real.sqrt (lineSlope h s t * (2 * line h s t))

lemma K1_eq_K1d_c (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) :
    K1 n h s s t = K1d_c n h s t := by
  unfold K1d_c K1
  rw [Kden_diag_c, J1, if_pos rfl]

lemma K2_eq_K2d_c (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) :
    K2 n h s s t = K2d_c n h s t := by
  unfold K2d_c K2
  rw [Kden_diag_c, J2, if_pos rfl]

/-- The constant `∫₀¹ dτ/√(τ(1-τ)) = π`, in the shape produced by `G2_self`. -/
lemma integral_inv_sqrt_eq_pi_c :
    (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹) = Real.pi := by
  have h1 : (fun τ : ℝ => (Real.sqrt (τ * (1 - τ)))⁻¹)
      = fun τ : ℝ => 1 / Real.sqrt (τ * (1 - τ)) := by
    funext τ
    exact (one_div _).symm
  rw [h1]
  exact Commons.Geometry.Ulam.integral_one_div_sqrt_tau_one_sub_tau_eq_pi

/-- **The diagonal (`σ = s`) form of `Godd`.**  At `σ = s` the `τ`-integrand of `G2` is
constant, so `G2` collapses to `π • Kvec`, and the last two components of `Godd` are the
explicit `2 × 2` linear expressions in `(z 2, z 3)`. -/
lemma Godd_eq_diag_c (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (z : St) :
    Godd n h s z = ![z 0, z 1,
      Real.pi * (K1 n h s s (-(z 0)) * z 2 + K1 n h s s (z 1) * z 3),
      Real.pi * (K2 n h s s (-(z 0)) * z 2 + K2 n h s s (z 1) * z 3)] := by
  funext i
  fin_cases i <;>
    simp only [Godd, G2_self, Kvec, integral_inv_sqrt_eq_pi_c, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]
  all_goals ring

/-! ## Bounds on the base state and on the state ball -/

lemma deriv_profileX_formula_c (s : ℝ) :
    deriv profileX s = -(s / (Real.sqrt (1 + s ^ 2)) ^ 3) := by
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * s) s := by
    have h := ((hasDerivAt_id (x := s)).pow 2).const_add 1
    simpa using h
  have hsqrt : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
      ((2 * s) / (2 * Real.sqrt (1 + s ^ 2))) s :=
    hinner.sqrt (by positivity)
  have hne : Real.sqrt (1 + s ^ 2) ≠ 0 := by positivity
  have hfun : profileX = (fun t : ℝ => Real.sqrt (1 + t ^ 2))⁻¹ := by
    funext t
    simp [profileX]
  have hd : HasDerivAt profileX
      (-((2 * s) / (2 * Real.sqrt (1 + s ^ 2))) / (Real.sqrt (1 + s ^ 2)) ^ 2) s := by
    rw [hfun]
    exact hsqrt.inv hne
  rw [hd.deriv]
  field_simp

lemma abs_deriv_profileX_le_c {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |deriv profileX s| ≤ 1 / 2 := by
  rw [deriv_profileX_formula_c, abs_neg]
  have hsq : (Real.sqrt (1 + s ^ 2)) ^ 2 = 1 + s ^ 2 := Real.sq_sqrt (by positivity)
  have hpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos_of_pos (by positivity)
  have hcube : (Real.sqrt (1 + s ^ 2)) ^ 3 = (1 + s ^ 2) * Real.sqrt (1 + s ^ 2) := by
    rw [show (Real.sqrt (1 + s ^ 2)) ^ 3
        = (Real.sqrt (1 + s ^ 2)) ^ 2 * Real.sqrt (1 + s ^ 2) by ring, hsq]
  have hle1 : 1 + s ^ 2 ≤ (Real.sqrt (1 + s ^ 2)) ^ 3 := by
    rw [hcube]
    nlinarith [hpos]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ s / (Real.sqrt (1 + s ^ 2)) ^ 3)]
  have hstep : s / (Real.sqrt (1 + s ^ 2)) ^ 3 ≤ s / (1 + s ^ 2) :=
    div_le_div_of_nonneg_left hs (by positivity : (0:ℝ) < 1 + s ^ 2) hle1
  have hfin : s / (1 + s ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + s ^ 2)]
    nlinarith [sq_nonneg (s - 1)]
  linarith

lemma one_div_sqrt_two_sub_half_gt_one_fifth_c :
    (1 : ℝ) / 5 < 1 / Real.sqrt 2 - 1 / 2 := by
  have h7 : (7 : ℝ) / 10 < 1 / Real.sqrt 2 := by
    rw [lt_div_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2))]
    have hkey : (7 : ℝ) / 10 * Real.sqrt 2 < 1 ↔ Real.sqrt 2 < 10 / 7 := by
      rw [show (1 : ℝ) = (7 / 10) * (10 / 7) by norm_num,
        mul_lt_mul_iff_of_pos_left (by norm_num : (0:ℝ) < 7 / 10)]
    rw [hkey]
    exact (Real.sqrt_lt' (by norm_num : (0:ℝ) < 10 / 7)).mpr (by norm_num)
  linarith

lemma profileX_lower_c {s : ℝ} (hs : |s| ≤ 1) :
    1 / Real.sqrt 2 ≤ profileX s := by
  have h1 : 1 + s ^ 2 ≤ 2 := by
    have := abs_le.mp hs
    nlinarith [this.1, this.2]
  have hpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos_of_pos (by positivity)
  have h2 : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h1
  simp only [profileX, one_div]
  exact (inv_le_inv₀ (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2)) hpos).mpr h2

lemma profileX_le_one_c (s : ℝ) : profileX s ≤ 1 := by
  have hpos : 0 < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos_of_pos (by positivity)
  have h1 : 1 ≤ Real.sqrt (1 + s ^ 2) := by
    have h : (1 : ℝ) ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg s]
    simpa using Real.sqrt_le_sqrt h
  simp only [profileX, one_div]
  exact inv_le_one_of_one_le₀ h1

lemma baseState_apply_c (s : ℝ) :
    baseState s 0 = profileX s ∧ baseState s 1 = profileX s ∧
    baseState s 2 = deriv profileX s ∧ baseState s 3 = deriv profileX s := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [baseState]

lemma coord_bound_of_mem_closedBall_c {s : ℝ} {z : St}
    (hz : z ∈ Metric.closedBall (baseState s) (1 / 2)) (i : Fin 4) :
    |z i - baseState s i| ≤ 1 / 2 := by
  have h := Metric.mem_closedBall.mp hz
  rw [dist_pi_le_iff (by norm_num)] at h
  simpa [Real.dist_eq] using h i

/-- The coordinate bounds furnished by membership in the state ball. -/
lemma state_ball_bounds_c {s : ℝ} (hs : s ∈ Set.Icc 0 1) {z : St}
    (hz : z ∈ Metric.closedBall (baseState s) (1 / 2)) :
    1 / 5 ≤ z 0 ∧ 1 / 5 ≤ z 1 ∧ z 0 ≤ 3 / 2 ∧ z 1 ≤ 3 / 2 ∧
      |z 2| ≤ 1 ∧ |z 3| ≤ 1 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := baseState_apply_c s
  have hsabs : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hpx_lo := profileX_lower_c hsabs
  have hpx_hi := profileX_le_one_c s
  have hd := abs_le.mp (abs_deriv_profileX_le_c hs.1 hs.2)
  have h0 := abs_le.mp (coord_bound_of_mem_closedBall_c hz 0)
  have h1 := abs_le.mp (coord_bound_of_mem_closedBall_c hz 1)
  have h2 := abs_le.mp (coord_bound_of_mem_closedBall_c hz 2)
  have h3 := abs_le.mp (coord_bound_of_mem_closedBall_c hz 3)
  rw [hb0] at h0
  rw [hb1] at h1
  rw [hb2] at h2
  rw [hb3] at h3
  have hgt := one_div_sqrt_two_sub_half_gt_one_fifth_c
  refine ⟨by linarith [h0.1], by linarith [h1.1], by linarith [h0.2], by linarith [h1.2],
    ?_, ?_⟩
  · rw [abs_le]
    exact ⟨by linarith [hd.1, h2.1], by linarith [hd.2, h2.2]⟩
  · rw [abs_le]
    exact ⟨by linarith [hd.1, h3.1], by linarith [hd.2, h3.2]⟩

/-! ## The `2 × 2` Cramer estimate -/

/-- The triangle inequality for a difference, in the shape needed below. -/
private lemma abs_sub_le' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  simpa [sub_eq_add_neg, abs_neg] using h

/-- Solving a nonsingular `2 × 2` linear system by Cramer's rule gives a bound on the solution,
in terms of the size of the right-hand side, the size of the entries and the lower bound on the
determinant. -/
private lemma cramer2_bound {A Bb Cc Dd P Q δ Cap R : ℝ} (hδ : 0 < δ) (hCap : 0 < Cap)
    (hΔ : δ ≤ |A * Dd - Bb * Cc|) (hA : |A| ≤ Cap) (hBb : |Bb| ≤ Cap)
    (hCc : |Cc| ≤ Cap) (hDd : |Dd| ≤ Cap) (hP : |P| ≤ R) (hQ : |Q| ≤ R) :
    |(Dd * P - Bb * Q) / (A * Dd - Bb * Cc)| ≤ 2 * Cap * R / δ ∧
      |(A * Q - Cc * P) / (A * Dd - Bb * Cc)| ≤ 2 * Cap * R / δ := by
  have hΔpos : 0 < |A * Dd - Bb * Cc| := lt_of_lt_of_le hδ hΔ
  have hR : 0 ≤ R := le_trans (abs_nonneg P) hP
  have hle : (1 : ℝ) ≤ |A * Dd - Bb * Cc| / δ := (one_le_div hδ).mpr hΔ
  have hnum1 : |Dd * P - Bb * Q| ≤ 2 * Cap * R := by
    refine le_trans (abs_sub_le' _ _) ?_
    have h1 : |Dd * P| ≤ Cap * R := by
      rw [abs_mul]
      exact mul_le_mul hDd hP (abs_nonneg _) (le_of_lt hCap)
    have h2 : |Bb * Q| ≤ Cap * R := by
      rw [abs_mul]
      exact mul_le_mul hBb hQ (abs_nonneg _) (le_of_lt hCap)
    linarith
  have hnum2 : |A * Q - Cc * P| ≤ 2 * Cap * R := by
    refine le_trans (abs_sub_le' _ _) ?_
    have h1 : |A * Q| ≤ Cap * R := by
      rw [abs_mul]
      exact mul_le_mul hA hQ (abs_nonneg _) (le_of_lt hCap)
    have h2 : |Cc * P| ≤ Cap * R := by
      rw [abs_mul]
      exact mul_le_mul hCc hP (abs_nonneg _) (le_of_lt hCap)
    linarith
  have htail : 2 * Cap * R ≤ (2 * Cap * R / δ) * |A * Dd - Bb * Cc| := by
    have h1 : (0 : ℝ) ≤ 2 * Cap * R := by positivity
    have h2 : 2 * Cap * R * (|A * Dd - Bb * Cc| / δ)
        = (2 * Cap * R / δ) * |A * Dd - Bb * Cc| := by ring
    rw [← h2]
    nlinarith [hle, h1]
  constructor
  · rw [abs_div, div_le_iff₀ hΔpos]
    exact le_trans hnum1 htail
  · rw [abs_div, div_le_iff₀ hΔpos]
    exact le_trans hnum2 htail

/-! ## The modulus of `Godd` on the state ball from uniform kernel bounds -/

/-- **The state-space modulus of `Godd` from uniform bounds on the diagonal Abel kernels.**
`Godd n h s z = (z 0, z 1, π M(z 0,z 1) · (z 2, z 3))` with `M(a,c)` the `2 × 2` matrix of
diagonal Abel kernels; the first two coordinates are controlled by the two rows of `Godd` and
the last two by Cramer's rule applied to `M(z 0,z 1)`, using the Lipschitz bound on `M` to absorb
the discrepancy `M(z 0,z 1) - M(z' 0,z' 1)`. -/
lemma godd_modulus_of_bounds_c (n : ℕ) {h : ℝ → ℝ} {b B δ ℓ : ℝ}
    (hb : 0 < b) (hB : 0 < B) (hδ : 0 < δ) (hℓ : 0 ≤ ℓ)
    (hbound : ∀ s ∈ Set.Icc b 1, ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 3 / 2 →
      |K1d_c n h s t| ≤ B ∧ |K2d_c n h s t| ≤ B)
    (hdet : ∀ s ∈ Set.Icc b 1, ∀ a ∈ Set.Icc (1 / 5) (3 / 2), ∀ c ∈ Set.Icc (1 / 5) (3 / 2),
      δ ≤ |K1d_c n h s (-a) * K2d_c n h s c - K1d_c n h s c * K2d_c n h s (-a)|)
    (hlip : ∀ s ∈ Set.Icc b 1, ∀ t ∈ Set.Icc (1 / 5) (3 / 2), ∀ t' ∈ Set.Icc (1 / 5) (3 / 2),
      |K1d_c n h s t - K1d_c n h s t'| ≤ ℓ * |t - t'| ∧
      |K2d_c n h s t - K2d_c n h s t'| ≤ ℓ * |t - t'|)
    (hlip' : ∀ s ∈ Set.Icc b 1, ∀ t ∈ Set.Icc (-3 / 2) (-1 / 5), ∀ t' ∈ Set.Icc (-3 / 2) (-1 / 5),
      |K1d_c n h s t - K1d_c n h s t'| ≤ ℓ * |t - t'| ∧
      |K2d_c n h s t - K2d_c n h s t'| ≤ ℓ * |t - t'|) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ Set.Icc b 1,
      ∀ z ∈ Metric.closedBall (baseState s) (1 / 2),
      ∀ z' ∈ Metric.closedBall (baseState s) (1 / 2),
      c * ‖z - z'‖ ≤ ‖Godd n h s z - Godd n h s z'‖ := by
  set KK : ℝ := max 1 (2 * B * (1 / Real.pi + 2 * ℓ) / δ) with hKK
  have hKKpos : 0 < KK := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK1 : (1 : ℝ) ≤ KK := le_max_left _ _
  have hK2 : 2 * B * (1 / Real.pi + 2 * ℓ) / δ ≤ KK := le_max_right _ _
  refine ⟨1 / KK, by positivity, ?_⟩
  intro s hs z hz z' hz'
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans (le_of_lt hb) hs.1, hs.2⟩
  obtain ⟨hz0, hz1, hz0u, hz1u, hz2, hz3⟩ := state_ball_bounds_c hs01 hz
  obtain ⟨hz0', hz1', hz0u', hz1u', hz2', hz3'⟩ := state_ball_bounds_c hs01 hz'
  set G := ‖Godd n h s z - Godd n h s z'‖ with hG
  have hGnn : 0 ≤ G := norm_nonneg _
  set A0 := K1d_c n h s (-(z 0)) with hA0
  set B0 := K1d_c n h s (z 1) with hB0
  set C0 := K2d_c n h s (-(z 0)) with hC0
  set D0 := K2d_c n h s (z 1) with hD0
  set A1 := K1d_c n h s (-(z' 0)) with hA1
  set B1 := K1d_c n h s (z' 1) with hB1
  set C1 := K2d_c n h s (-(z' 0)) with hC1
  set D1 := K2d_c n h s (z' 1) with hD1
  have hmem_pos : ∀ w : ℝ, 1 / 5 ≤ w → w ≤ 3 / 2 → w ∈ Set.Icc (1 / 5) (3 / 2) :=
    fun w h1 h2 => ⟨h1, h2⟩
  have hmem_neg : ∀ w : ℝ, 1 / 5 ≤ w → w ≤ 3 / 2 →
      -(w) ∈ Set.Icc (-3 / 2) (-1 / 5) := fun w h1 h2 => ⟨by linarith, by linarith⟩
  have hbound_pos : ∀ w : ℝ, 1 / 5 ≤ w → w ≤ 3 / 2 →
      |K1d_c n h s w| ≤ B ∧ |K2d_c n h s w| ≤ B := by
    intro w h1 h2
    have hw : 1 / 5 ≤ |w| ∧ |w| ≤ 3 / 2 := by
      rw [abs_of_pos (by linarith : (0:ℝ) < w)]
      exact ⟨h1, h2⟩
    exact hbound s hs w hw.1 hw.2
  have hbound_neg : ∀ w : ℝ, 1 / 5 ≤ w → w ≤ 3 / 2 →
      |K1d_c n h s (-w)| ≤ B ∧ |K2d_c n h s (-w)| ≤ B := by
    intro w h1 h2
    have hw : 1 / 5 ≤ |-(w)| ∧ |-(w)| ≤ 3 / 2 := by
      rw [abs_neg, abs_of_pos (by linarith : (0:ℝ) < w)]
      exact ⟨h1, h2⟩
    exact hbound s hs (-w) hw.1 hw.2
  have hA0b : |A0| ≤ B := by rw [hA0]; exact (hbound_neg (z 0) hz0 hz0u).1
  have hC0b : |C0| ≤ B := by rw [hC0]; exact (hbound_neg (z 0) hz0 hz0u).2
  have hB0b : |B0| ≤ B := by rw [hB0]; exact (hbound_pos (z 1) hz1 hz1u).1
  have hD0b : |D0| ≤ B := by rw [hD0]; exact (hbound_pos (z 1) hz1 hz1u).2
  have hdiff_neg : ∀ w w' : ℝ, 1 / 5 ≤ w → w ≤ 3 / 2 → 1 / 5 ≤ w' → w' ≤ 3 / 2 →
      |K1d_c n h s (-w) - K1d_c n h s (-w')| ≤ ℓ * |w - w'| ∧
      |K2d_c n h s (-w) - K2d_c n h s (-w')| ≤ ℓ * |w - w'| := by
    intro w w' h1 h2 h1' h2'
    have h := hlip' s hs (-w) (hmem_neg w h1 h2) (-w') (hmem_neg w' h1' h2')
    have he : |-(w) - -(w')| = |w - w'| := by
      rw [show -(w) - -(w') = -(w - w') by ring, abs_neg]
    rwa [he] at h
  have hdiff_pos : ∀ w w' : ℝ, 1 / 5 ≤ w → w ≤ 3 / 2 → 1 / 5 ≤ w' → w' ≤ 3 / 2 →
      |K1d_c n h s w - K1d_c n h s w'| ≤ ℓ * |w - w'| ∧
      |K2d_c n h s w - K2d_c n h s w'| ≤ ℓ * |w - w'| :=
    fun w w' h1 h2 h1' h2' => hlip s hs w (hmem_pos w h1 h2) w' (hmem_pos w' h1' h2')
  have hrow0 : (Godd n h s z - Godd n h s z') 0 = z 0 - z' 0 := by
    rw [Godd_eq_diag_c, Godd_eq_diag_c]
    simp only [Pi.sub_apply, Matrix.cons_val_zero]
  have hrow1 : (Godd n h s z - Godd n h s z') 1 = z 1 - z' 1 := by
    rw [Godd_eq_diag_c, Godd_eq_diag_c]
    simp only [Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
  have hrow2 : (Godd n h s z - Godd n h s z') 2 =
      Real.pi * ((A0 * z 2 + B0 * z 3) - (A1 * z' 2 + B1 * z' 3)) := by
    rw [Godd_eq_diag_c, Godd_eq_diag_c]
    simp only [K1_eq_K1d_c, Pi.sub_apply, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
    rw [← hA0, ← hB0, ← hA1, ← hB1]
    ring
  have hrow3 : (Godd n h s z - Godd n h s z') 3 =
      Real.pi * ((C0 * z 2 + D0 * z 3) - (C1 * z' 2 + D1 * z' 3)) := by
    rw [Godd_eq_diag_c, Godd_eq_diag_c]
    simp only [K2_eq_K2d_c, Pi.sub_apply, Matrix.cons_val_three, Matrix.tail_cons,
      Matrix.head_cons]
    rw [← hC0, ← hD0, ← hC1, ← hD1]
    ring
  have hc0 : |z 0 - z' 0| ≤ G := by
    have h := norm_le_pi_norm (Godd n h s z - Godd n h s z') (0 : Fin 4)
    rw [hrow0] at h
    simpa [Real.norm_eq_abs, hG] using h
  have hc1 : |z 1 - z' 1| ≤ G := by
    have h := norm_le_pi_norm (Godd n h s z - Godd n h s z') (1 : Fin 4)
    rw [hrow1] at h
    simpa [Real.norm_eq_abs, hG] using h
  have hc2 : |(Godd n h s z - Godd n h s z') 2| ≤ G := by
    have h := norm_le_pi_norm (Godd n h s z - Godd n h s z') (2 : Fin 4)
    simpa [Real.norm_eq_abs, hG] using h
  have hc3 : |(Godd n h s z - Godd n h s z') 3| ≤ G := by
    have h := norm_le_pi_norm (Godd n h s z - Godd n h s z') (3 : Fin 4)
    simpa [Real.norm_eq_abs, hG] using h
  have he0 : |(A0 - A1) * z' 2 + (B0 - B1) * z' 3| ≤ 2 * ℓ * G := by
    have h1 : |(A0 - A1) * z' 2| ≤ ℓ * G := by
      rw [abs_mul]
      have hd : |A0 - A1| ≤ ℓ * G := by
        refine le_trans (hdiff_neg (z 0) (z' 0) hz0 hz0u hz0' hz0u').1 ?_
        exact mul_le_mul_of_nonneg_left hc0 hℓ
      calc |A0 - A1| * |z' 2| ≤ (ℓ * G) * 1 := mul_le_mul hd hz2' (abs_nonneg _) (by positivity)
        _ = ℓ * G := by ring
    have h2 : |(B0 - B1) * z' 3| ≤ ℓ * G := by
      rw [abs_mul]
      have hd : |B0 - B1| ≤ ℓ * G := by
        refine le_trans (hdiff_pos (z 1) (z' 1) hz1 hz1u hz1' hz1u').1 ?_
        exact mul_le_mul_of_nonneg_left hc1 hℓ
      calc |B0 - B1| * |z' 3| ≤ (ℓ * G) * 1 := mul_le_mul hd hz3' (abs_nonneg _) (by positivity)
        _ = ℓ * G := by ring
    refine le_trans (abs_add_le _ _) ?_
    linarith
  have he1 : |(C0 - C1) * z' 2 + (D0 - D1) * z' 3| ≤ 2 * ℓ * G := by
    have h1 : |(C0 - C1) * z' 2| ≤ ℓ * G := by
      rw [abs_mul]
      have hd : |C0 - C1| ≤ ℓ * G := by
        refine le_trans (hdiff_neg (z 0) (z' 0) hz0 hz0u hz0' hz0u').2 ?_
        exact mul_le_mul_of_nonneg_left hc0 hℓ
      calc |C0 - C1| * |z' 2| ≤ (ℓ * G) * 1 := mul_le_mul hd hz2' (abs_nonneg _) (by positivity)
        _ = ℓ * G := by ring
    have h2 : |(D0 - D1) * z' 3| ≤ ℓ * G := by
      rw [abs_mul]
      have hd : |D0 - D1| ≤ ℓ * G := by
        refine le_trans (hdiff_pos (z 1) (z' 1) hz1 hz1u hz1' hz1u').2 ?_
        exact mul_le_mul_of_nonneg_left hc1 hℓ
      calc |D0 - D1| * |z' 3| ≤ (ℓ * G) * 1 := mul_le_mul hd hz3' (abs_nonneg _) (by positivity)
        _ = ℓ * G := by ring
    refine le_trans (abs_add_le _ _) ?_
    linarith
  have hX0 : A0 * (z 2 - z' 2) + B0 * (z 3 - z' 3)
      = (Godd n h s z - Godd n h s z') 2 / Real.pi
        - ((A0 - A1) * z' 2 + (B0 - B1) * z' 3) := by
    rw [hrow2, mul_div_cancel_left₀ _ (ne_of_gt Real.pi_pos)]
    ring
  have hX1 : C0 * (z 2 - z' 2) + D0 * (z 3 - z' 3)
      = (Godd n h s z - Godd n h s z') 3 / Real.pi
        - ((C0 - C1) * z' 2 + (D0 - D1) * z' 3) := by
    rw [hrow3, mul_div_cancel_left₀ _ (ne_of_gt Real.pi_pos)]
    ring
  have hPb : |A0 * (z 2 - z' 2) + B0 * (z 3 - z' 3)| ≤ (1 / Real.pi + 2 * ℓ) * G := by
    rw [hX0]
    have hnum : |(Godd n h s z - Godd n h s z') 2 / Real.pi
        - ((A0 - A1) * z' 2 + (B0 - B1) * z' 3)| ≤ G / Real.pi + 2 * ℓ * G := by
      refine le_trans (abs_sub_le' _ _) ?_
      refine add_le_add ?_ he0
      rw [abs_div, abs_of_pos Real.pi_pos]
      exact div_le_div_of_nonneg_right hc2 (le_of_lt Real.pi_pos)
    calc |(Godd n h s z - Godd n h s z') 2 / Real.pi
          - ((A0 - A1) * z' 2 + (B0 - B1) * z' 3)| ≤ G / Real.pi + 2 * ℓ * G := hnum
      _ = (1 / Real.pi + 2 * ℓ) * G := by ring
  have hQb : |C0 * (z 2 - z' 2) + D0 * (z 3 - z' 3)| ≤ (1 / Real.pi + 2 * ℓ) * G := by
    rw [hX1]
    have hnum : |(Godd n h s z - Godd n h s z') 3 / Real.pi
        - ((C0 - C1) * z' 2 + (D0 - D1) * z' 3)| ≤ G / Real.pi + 2 * ℓ * G := by
      refine le_trans (abs_sub_le' _ _) ?_
      refine add_le_add ?_ he1
      rw [abs_div, abs_of_pos Real.pi_pos]
      exact div_le_div_of_nonneg_right hc3 (le_of_lt Real.pi_pos)
    calc |(Godd n h s z - Godd n h s z') 3 / Real.pi
          - ((C0 - C1) * z' 2 + (D0 - D1) * z' 3)| ≤ G / Real.pi + 2 * ℓ * G := hnum
      _ = (1 / Real.pi + 2 * ℓ) * G := by ring
  have hΔ : δ ≤ |A0 * D0 - B0 * C0| := by
    rw [hA0, hB0, hC0, hD0]
    exact hdet s hs (z 0) (hmem_pos (z 0) hz0 hz0u) (z 1) (hmem_pos (z 1) hz1 hz1u)
  set PP := A0 * (z 2 - z' 2) + B0 * (z 3 - z' 3) with hPP
  set QQ := C0 * (z 2 - z' 2) + D0 * (z 3 - z' 3) with hQQ
  have hPab : |PP| ≤ (1 / Real.pi + 2 * ℓ) * G := by rw [hPP]; exact hPb
  have hQab : |QQ| ≤ (1 / Real.pi + 2 * ℓ) * G := by rw [hQQ]; exact hQb
  have hsysP : A0 * (z 2 - z' 2) + B0 * (z 3 - z' 3) = PP := by rw [hPP]
  have hsysQ : C0 * (z 2 - z' 2) + D0 * (z 3 - z' 3) = QQ := by rw [hQQ]
  have hΔne : A0 * D0 - B0 * C0 ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hΔ
    linarith
  have hu2 : z 2 - z' 2 = (D0 * PP - B0 * QQ) / (A0 * D0 - B0 * C0) := by
    rw [eq_div_iff hΔne]
    linear_combination D0 * hsysP - B0 * hsysQ
  have hu3 : z 3 - z' 3 = (A0 * QQ - C0 * PP) / (A0 * D0 - B0 * C0) := by
    rw [eq_div_iff hΔne]
    linear_combination A0 * hsysQ - C0 * hsysP
  obtain ⟨hb2, hb3⟩ := cramer2_bound hδ hB hΔ hA0b hB0b hC0b hD0b hPab hQab
  have hc2' : |z 2 - z' 2| ≤ KK * G := by
    rw [hu2]
    calc |(D0 * PP - B0 * QQ) / (A0 * D0 - B0 * C0)|
        ≤ 2 * B * ((1 / Real.pi + 2 * ℓ) * G) / δ := hb2
      _ = (2 * B * (1 / Real.pi + 2 * ℓ) / δ) * G := by ring
      _ ≤ KK * G := mul_le_mul_of_nonneg_right hK2 hGnn
  have hc3' : |z 3 - z' 3| ≤ KK * G := by
    rw [hu3]
    calc |(A0 * QQ - C0 * PP) / (A0 * D0 - B0 * C0)|
        ≤ 2 * B * ((1 / Real.pi + 2 * ℓ) * G) / δ := hb3
      _ = (2 * B * (1 / Real.pi + 2 * ℓ) / δ) * G := by ring
      _ ≤ KK * G := mul_le_mul_of_nonneg_right hK2 hGnn
  have hc0' : |z 0 - z' 0| ≤ KK * G := by
    calc |z 0 - z' 0| ≤ G := hc0
      _ = 1 * G := by ring
      _ ≤ KK * G := mul_le_mul_of_nonneg_right hK1 hGnn
  have hc1' : |z 1 - z' 1| ≤ KK * G := by
    calc |z 1 - z' 1| ≤ G := hc1
      _ = 1 * G := by ring
      _ ≤ KK * G := mul_le_mul_of_nonneg_right hK1 hGnn
  have hnorm : dist z z' ≤ KK * G := by
    rw [dist_pi_le_iff (mul_nonneg (le_of_lt hKKpos) hGnn)]
    intro i
    fin_cases i
    · simpa [Real.dist_eq] using hc0'
    · simpa [Real.dist_eq] using hc1'
    · simpa [Real.dist_eq] using hc2'
    · simpa [Real.dist_eq] using hc3'
  rw [dist_eq_norm] at hnorm
  calc (1 / KK) * ‖z - z'‖ ≤ (1 / KK) * (KK * G) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = G := by rw [one_div, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hKKpos), one_mul]

/-! ## Uniform bounds for the diagonal Abel kernels -/

/-- The product `L(s,t) · ∂_sL(s,t)`, as a function of `(s,t)`. -/
def llprod_c (h : ℝ → ℝ) (p : ℝ × ℝ) : ℝ := line h p.1 p.2 * lineSlope h p.1 p.2

lemma llprod_apply_c (h : ℝ → ℝ) (s t : ℝ) :
    llprod_c h (s, t) = line h s t * lineSlope h s t := rfl

/-- The diagonal first Abel kernel, as a function of `(s,t)`. -/
def k1fun_c (n : ℕ) (h : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Nat.doubleFactorial (2 * n + 1) : ℝ) *
    (-(line h p.1 p.2 * lineSlope h p.1 p.2)) ^ (n + 1) /
    Real.sqrt (lineSlope h p.1 p.2 * (2 * line h p.1 p.2))

/-- The diagonal second Abel kernel, as a function of `(s,t)`. -/
def k2fun_c (n : ℕ) (h : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (Nat.doubleFactorial (2 * n - 1) : ℝ) *
    (-(line h p.1 p.2 * lineSlope h p.1 p.2)) ^ n * lineSlope h p.1 p.2 /
    Real.sqrt (lineSlope h p.1 p.2 * (2 * line h p.1 p.2))

lemma k1fun_apply_c (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) : k1fun_c n h (s, t) = K1d_c n h s t := rfl

lemma k2fun_apply_c (n : ℕ) (h : ℝ → ℝ) (s t : ℝ) : k2fun_c n h (s, t) = K2d_c n h s t := rfl

lemma h_abs_le_c {h : ℝ → ℝ}
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => hsmall 0 (by norm_num) x

lemma deriv_h_abs_le_c {h : ℝ → ℝ}
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := fun x => by simpa using hsmall 1 (by norm_num) x

/-- `h` vanishes strictly to the left of the transition window. -/
lemma h_eq_zero_of_lt_c {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    {x : ℝ} (hx : x < 4 / 5) : h x = 0 := by
  by_contra hne
  have hmem := hsupp (Function.mem_support.mpr hne)
  have e1 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by
    rw [Work.OddVolterra.tau]; norm_num
  rw [e1] at hmem
  linarith [hmem.1]

/-- `h` is bounded by `1/100` on the transition window. -/
lemma h_le_window_c {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s : ℝ} (hs : h s ≠ 0) : 4 / 5 ≤ s := by
  have hmem := hsupp (Function.mem_support.mpr hs)
  have e1 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by
    rw [Work.OddVolterra.tau]; norm_num
  rw [e1] at hmem
  exact hmem.1

lemma line_pos_of_ge_c {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s t : ℝ} (hs : 0 < s) (ht : 1 / 5 ≤ t) : 0 < line h s t := by
  have hh0 := h_abs_le_c hsmall s
  rcases eq_or_ne (h s) 0 with hz | hn
  · rw [line, hz, add_zero]; nlinarith
  · have hs' : (4 : ℝ) / 5 ≤ s := h_le_window_c hsupp hsmall hn
    have hle : h s ≤ 1 / 100 := (abs_le.mp hh0).2
    have hge : -(1 / 100) ≤ h s := (abs_le.mp hh0).1
    have hmul : ((4 : ℝ) / 5) * (1 / 5) ≤ s * t := mul_le_mul hs' ht (by norm_num) (le_of_lt hs)
    rw [line]
    nlinarith

lemma line_neg_of_le_c {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s t : ℝ} (hs : 0 < s) (ht : t ≤ -(1 / 5)) : line h s t < 0 := by
  have hh0 := h_abs_le_c hsmall s
  rcases eq_or_ne (h s) 0 with hz | hn
  · rw [line, hz, add_zero]; nlinarith
  · have hs' : (4 : ℝ) / 5 ≤ s := h_le_window_c hsupp hsmall hn
    have hle : h s ≤ 1 / 100 := (abs_le.mp hh0).2
    have hge : -(1 / 100) ≤ h s := (abs_le.mp hh0).1
    have hmul : ((4 : ℝ) / 5) * (1 / 5) ≤ s * (-t) :=
      mul_le_mul hs' (by linarith) (by norm_num) (le_of_lt hs)
    rw [line]
    nlinarith

lemma lineSlope_pos_of_ge_c {h : ℝ → ℝ}
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s t : ℝ} (ht : 1 / 5 ≤ t) : 0 < lineSlope h s t := by
  have hd := deriv_h_abs_le_c hsmall s
  rw [lineSlope]
  linarith [(abs_le.mp hd).1]

lemma lineSlope_neg_of_le_c {h : ℝ → ℝ}
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s t : ℝ} (ht : t ≤ -(1 / 5)) : lineSlope h s t < 0 := by
  have hd := deriv_h_abs_le_c hsmall s
  rw [lineSlope]
  linarith [(abs_le.mp hd).2]

/-- The radicand `L · ∂_sL` of the diagonal kernels is positive as soon as `|t| ≥ 1/5`
and `s > 0`. -/
lemma llprod_pos_of_abs_c {h : ℝ → ℝ}
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s t : ℝ} (hs : 0 < s) (ht : 1 / 5 ≤ |t|) : 0 < llprod_c h (s, t) := by
  rcases le_or_gt (1 / 5 : ℝ) t with htp | htn
  · rw [llprod_apply_c]
    exact mul_pos (line_pos_of_ge_c hsupp hsmall hs htp) (lineSlope_pos_of_ge_c hsmall htp)
  · have htneg : t < 0 := by
      by_contra hcon
      rw [abs_of_nonneg (le_of_not_gt hcon)] at ht
      linarith
    have htle : t ≤ -(1 / 5) := by
      rw [abs_of_neg htneg] at ht
      linarith
    rw [llprod_apply_c]
    exact mul_pos_of_neg_of_neg (line_neg_of_le_c hsupp hsmall hs htle)
      (lineSlope_neg_of_le_c hsmall htle)

lemma contDiffOn_k1fun_c {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (k1fun_c n h) {p : ℝ × ℝ | 0 < llprod_c h p} := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => line h p.1 p.2) := line_contDiff hh
  have hS : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => lineSlope h p.1 p.2) := lineSlope_contDiff hh
  have hnum : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ =>
      (Nat.doubleFactorial (2 * n + 1) : ℝ) *
        (-(line h p.1 p.2 * lineSlope h p.1 p.2)) ^ (n + 1)) :=
    contDiff_const.mul ((hL.mul hS).neg.pow _)
  have hden : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => Real.sqrt (lineSlope h p.1 p.2 * (2 * line h p.1 p.2)))
      {p : ℝ × ℝ | 0 < llprod_c h p} := by
    refine ContDiffOn.sqrt ((hS.mul (contDiff_const.mul hL)).contDiffOn) ?_
    intro p hp
    have hp' : 0 < llprod_c h p := hp
    have e : lineSlope h p.1 p.2 * (2 * line h p.1 p.2) = 2 * llprod_c h p := by
      rw [llprod_apply_c]; ring
    rw [e]
    exact ne_of_gt (by linarith)
  rw [show k1fun_c n h = fun p : ℝ × ℝ =>
      (Nat.doubleFactorial (2 * n + 1) : ℝ) *
        (-(line h p.1 p.2 * lineSlope h p.1 p.2)) ^ (n + 1) /
        Real.sqrt (lineSlope h p.1 p.2 * (2 * line h p.1 p.2)) from rfl]
  refine ContDiffOn.div hnum.contDiffOn hden ?_
  intro p hp
  have hp' : 0 < llprod_c h p := hp
  have e : lineSlope h p.1 p.2 * (2 * line h p.1 p.2) = 2 * llprod_c h p := by
    rw [llprod_apply_c]; ring
  rw [e]
  exact ne_of_gt (Real.sqrt_pos_of_pos (by linarith))

lemma contDiffOn_k2fun_c {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (k2fun_c n h) {p : ℝ × ℝ | 0 < llprod_c h p} := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => line h p.1 p.2) := line_contDiff hh
  have hS : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => lineSlope h p.1 p.2) := lineSlope_contDiff hh
  have hnum : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ =>
      (Nat.doubleFactorial (2 * n - 1) : ℝ) *
        (-(line h p.1 p.2 * lineSlope h p.1 p.2)) ^ n * lineSlope h p.1 p.2) :=
    (contDiff_const.mul ((hL.mul hS).neg.pow _)).mul hS
  have hden : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => Real.sqrt (lineSlope h p.1 p.2 * (2 * line h p.1 p.2)))
      {p : ℝ × ℝ | 0 < llprod_c h p} := by
    refine ContDiffOn.sqrt ((hS.mul (contDiff_const.mul hL)).contDiffOn) ?_
    intro p hp
    have hp' : 0 < llprod_c h p := hp
    have e : lineSlope h p.1 p.2 * (2 * line h p.1 p.2) = 2 * llprod_c h p := by
      rw [llprod_apply_c]; ring
    rw [e]
    exact ne_of_gt (by linarith)
  rw [show k2fun_c n h = fun p : ℝ × ℝ =>
      (Nat.doubleFactorial (2 * n - 1) : ℝ) *
        (-(line h p.1 p.2 * lineSlope h p.1 p.2)) ^ n * lineSlope h p.1 p.2 /
        Real.sqrt (lineSlope h p.1 p.2 * (2 * line h p.1 p.2)) from rfl]
  refine ContDiffOn.div hnum.contDiffOn hden ?_
  intro p hp
  have hp' : 0 < llprod_c h p := hp
  have e : lineSlope h p.1 p.2 * (2 * line h p.1 p.2) = 2 * llprod_c h p := by
    rw [llprod_apply_c]; ring
  rw [e]
  exact ne_of_gt (Real.sqrt_pos_of_pos (by linarith))

/-- The `2 × 2` determinant of the diagonal kernels, as a function of `(s, a, c)`. -/
def detfn_c (n : ℕ) (h : ℝ → ℝ) (q : ℝ × ℝ × ℝ) : ℝ :=
  |k1fun_c n h (q.1, -(q.2.1)) * k2fun_c n h (q.1, q.2.2) -
    k1fun_c n h (q.1, q.2.2) * k2fun_c n h (q.1, -(q.2.1))|

open scoped Classical in
/-- **Uniform bounds for the diagonal Abel kernels.**  Assembled from the continuity of the
explicit closed forms `k1fun_c`, `k2fun_c` on the positivity region of `L · ∂_sL` by compactness
(for `B` and `δ`) and by `ContDiffOn.exists_lipschitzOnWith` (for `ℓ`). -/
lemma kernel_bounds_c (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ ℓ : ℝ, 0 ≤ ℓ ∧
      (∀ s ∈ Set.Icc b 1, ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 3 / 2 →
        |K1d_c n h s t| ≤ B ∧ |K2d_c n h s t| ≤ B) ∧
      (∀ s ∈ Set.Icc b 1, ∀ a ∈ Set.Icc (1 / 5) (3 / 2), ∀ c ∈ Set.Icc (1 / 5) (3 / 2),
        δ ≤ |K1d_c n h s (-a) * K2d_c n h s c - K1d_c n h s c * K2d_c n h s (-a)|) ∧
      (∀ s ∈ Set.Icc b 1, ∀ t ∈ Set.Icc (1 / 5) (3 / 2), ∀ t' ∈ Set.Icc (1 / 5) (3 / 2),
        |K1d_c n h s t - K1d_c n h s t'| ≤ ℓ * |t - t'| ∧
        |K2d_c n h s t - K2d_c n h s t'| ≤ ℓ * |t - t'|) ∧
      (∀ s ∈ Set.Icc b 1, ∀ t ∈ Set.Icc (-3 / 2) (-1 / 5), ∀ t' ∈ Set.Icc (-3 / 2) (-1 / 5),
        |K1d_c n h s t - K1d_c n h s t'| ≤ ℓ * |t - t'| ∧
        |K2d_c n h s t - K2d_c n h s t'| ≤ ℓ * |t - t'|) := by
  have hsub : ∀ s ∈ Set.Icc b 1, ∀ t : ℝ, 1 / 5 ≤ |t| → (s, t) ∈ {p : ℝ × ℝ | 0 < llprod_c h p} :=
    fun s hs t ht => llprod_pos_of_abs_c hsupp hsmall (lt_of_lt_of_le hb hs.1) ht
  have hPP : ∀ s ∈ Set.Icc b 1, ∀ t, t ∈ Set.Icc (1 / 5 : ℝ) (3 / 2) → 1 / 5 ≤ |t| := by
    intro s hs t ht
    rw [abs_of_pos (by linarith [ht.1] : (0:ℝ) < t)]
    exact ht.1
  have hNN : ∀ s ∈ Set.Icc b 1, ∀ t, t ∈ Set.Icc (-3 / 2 : ℝ) (-1 / 5) → 1 / 5 ≤ |t| := by
    intro s hs t ht
    rw [abs_of_neg (by linarith [ht.2] : t < 0)]
    linarith [ht.2]
  have hsubP : (Set.Icc b 1 ×ˢ Set.Icc (1 / 5 : ℝ) (3 / 2))
      ⊆ {p : ℝ × ℝ | 0 < llprod_c h p} :=
    fun p hp => hsub p.1 hp.1 p.2 (hPP p.1 hp.1 p.2 hp.2)
  have hsubN : (Set.Icc b 1 ×ˢ Set.Icc (-3 / 2 : ℝ) (-1 / 5))
      ⊆ {p : ℝ × ℝ | 0 < llprod_c h p} :=
    fun p hp => hsub p.1 hp.1 p.2 (hNN p.1 hp.1 p.2 hp.2)
  have hsubBox : (Set.Icc b 1 ×ˢ
      (Set.Icc (1 / 5 : ℝ) (3 / 2) ∪ Set.Icc (-3 / 2 : ℝ) (-1 / 5)))
      ⊆ {p : ℝ × ℝ | 0 < llprod_c h p} := by
    rintro ⟨s, t⟩ ⟨hs, ht | ht⟩
    · exact hsubP ⟨hs, ht⟩
    · exact hsubN ⟨hs, ht⟩
  -- Lipschitz constants on the four rectangles
  obtain ⟨C1p, hC1p⟩ := ContDiffOn.exists_lipschitzOnWith
    (f := k1fun_c n h) (s := Set.Icc b 1 ×ˢ Set.Icc (1 / 5 : ℝ) (3 / 2))
    ((contDiffOn_k1fun_c hh n).mono hsubP) (by simp)
    ((convex_Icc b 1).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C1n, hC1n⟩ := ContDiffOn.exists_lipschitzOnWith
    (f := k1fun_c n h) (s := Set.Icc b 1 ×ˢ Set.Icc (-3 / 2 : ℝ) (-1 / 5))
    ((contDiffOn_k1fun_c hh n).mono hsubN) (by simp)
    ((convex_Icc b 1).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C2p, hC2p⟩ := ContDiffOn.exists_lipschitzOnWith
    (f := k2fun_c n h) (s := Set.Icc b 1 ×ˢ Set.Icc (1 / 5 : ℝ) (3 / 2))
    ((contDiffOn_k2fun_c hh n).mono hsubP) (by simp)
    ((convex_Icc b 1).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C2n, hC2n⟩ := ContDiffOn.exists_lipschitzOnWith
    (f := k2fun_c n h) (s := Set.Icc b 1 ×ˢ Set.Icc (-3 / 2 : ℝ) (-1 / 5))
    ((contDiffOn_k2fun_c hh n).mono hsubN) (by simp)
    ((convex_Icc b 1).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  have hdist : ∀ s t t' : ℝ, dist ((s, t) : ℝ × ℝ) (s, t') = |t - t'| := by
    intro s t t'
    rw [Prod.dist_eq, dist_self, Real.dist_eq]
    exact max_eq_right (abs_nonneg _)
  have key1p : ∀ s ∈ Set.Icc b 1, ∀ t ∈ Set.Icc (1 / 5 : ℝ) (3 / 2),
      ∀ t' ∈ Set.Icc (1 / 5 : ℝ) (3 / 2),
      |K1d_c n h s t - K1d_c n h s t'| ≤ (C1p : ℝ) * |t - t'| := by
    intro s hs t ht t' ht'
    have h1 := hC1p.dist_le_mul (x := (s, t)) (y := (s, t')) ⟨hs, ht⟩ ⟨hs, ht'⟩
    rw [hdist s t t', Real.dist_eq, k1fun_apply_c, k1fun_apply_c] at h1
    exact h1
  have key1n : ∀ s ∈ Set.Icc b 1, ∀ t ∈ Set.Icc (-3 / 2 : ℝ) (-1 / 5),
      ∀ t' ∈ Set.Icc (-3 / 2 : ℝ) (-1 / 5),
      |K1d_c n h s t - K1d_c n h s t'| ≤ (C1n : ℝ) * |t - t'| := by
    intro s hs t ht t' ht'
    have h1 := hC1n.dist_le_mul (x := (s, t)) (y := (s, t')) ⟨hs, ht⟩ ⟨hs, ht'⟩
    rw [hdist s t t', Real.dist_eq, k1fun_apply_c, k1fun_apply_c] at h1
    exact h1
  have key2p : ∀ s ∈ Set.Icc b 1, ∀ t ∈ Set.Icc (1 / 5 : ℝ) (3 / 2),
      ∀ t' ∈ Set.Icc (1 / 5 : ℝ) (3 / 2),
      |K2d_c n h s t - K2d_c n h s t'| ≤ (C2p : ℝ) * |t - t'| := by
    intro s hs t ht t' ht'
    have h1 := hC2p.dist_le_mul (x := (s, t)) (y := (s, t')) ⟨hs, ht⟩ ⟨hs, ht'⟩
    rw [hdist s t t', Real.dist_eq, k2fun_apply_c, k2fun_apply_c] at h1
    exact h1
  have key2n : ∀ s ∈ Set.Icc b 1, ∀ t ∈ Set.Icc (-3 / 2 : ℝ) (-1 / 5),
      ∀ t' ∈ Set.Icc (-3 / 2 : ℝ) (-1 / 5),
      |K2d_c n h s t - K2d_c n h s t'| ≤ (C2n : ℝ) * |t - t'| := by
    intro s hs t ht t' ht'
    have h1 := hC2n.dist_le_mul (x := (s, t)) (y := (s, t')) ⟨hs, ht⟩ ⟨hs, ht'⟩
    rw [hdist s t t', Real.dist_eq, k2fun_apply_c, k2fun_apply_c] at h1
    exact h1
  -- the B bound
  have hboxC : IsCompact (Set.Icc b 1 ×ˢ
      (Set.Icc (1 / 5 : ℝ) (3 / 2) ∪ Set.Icc (-3 / 2 : ℝ) (-1 / 5))) :=
    isCompact_Icc.prod (isCompact_Icc.union isCompact_Icc)
  have hcont1 : ContinuousOn (k1fun_c n h) (Set.Icc b 1 ×ˢ
      (Set.Icc (1 / 5 : ℝ) (3 / 2) ∪ Set.Icc (-3 / 2 : ℝ) (-1 / 5))) :=
    ((contDiffOn_k1fun_c hh n).mono hsubBox).continuousOn
  have hcont2 : ContinuousOn (k2fun_c n h) (Set.Icc b 1 ×ˢ
      (Set.Icc (1 / 5 : ℝ) (3 / 2) ∪ Set.Icc (-3 / 2 : ℝ) (-1 / 5))) :=
    ((contDiffOn_k2fun_c hh n).mono hsubBox).continuousOn
  obtain ⟨Q1, hQ1⟩ := hboxC.exists_bound_of_continuousOn hcont1
  obtain ⟨Q2, hQ2⟩ := hboxC.exists_bound_of_continuousOn hcont2
  have hBpos : 0 < max 1 (max Q1 Q2) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hBconj : ∀ s ∈ Set.Icc b 1, ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 3 / 2 →
      |K1d_c n h s t| ≤ max 1 (max Q1 Q2) ∧ |K2d_c n h s t| ≤ max 1 (max Q1 Q2) := by
    intro s hs t ht1 ht2
    have htmem : t ∈ Set.Icc (1 / 5 : ℝ) (3 / 2) ∪ Set.Icc (-3 / 2 : ℝ) (-1 / 5) := by
      rcases le_or_gt (0 : ℝ) t with h0 | h0
      · left
        rw [abs_of_nonneg h0] at ht1 ht2
        exact ⟨ht1, ht2⟩
      · right
        rw [abs_of_neg h0] at ht1 ht2
        exact ⟨by linarith, by linarith⟩
    have hp : (s, t) ∈ Set.Icc b 1 ×ˢ
        (Set.Icc (1 / 5 : ℝ) (3 / 2) ∪ Set.Icc (-3 / 2 : ℝ) (-1 / 5)) := ⟨hs, htmem⟩
    have h1 := hQ1 (s, t) hp
    have h2 := hQ2 (s, t) hp
    rw [k1fun_apply_c] at h1
    rw [k2fun_apply_c] at h2
    constructor
    · calc |K1d_c n h s t| = ‖K1d_c n h s t‖ := (Real.norm_eq_abs _).symm
        _ ≤ Q1 := h1
        _ ≤ max 1 (max Q1 Q2) := le_trans (le_max_left _ _) (le_max_right _ _)
    · calc |K2d_c n h s t| = ‖K2d_c n h s t‖ := (Real.norm_eq_abs _).symm
        _ ≤ Q2 := h2
        _ ≤ max 1 (max Q1 Q2) := le_trans (le_max_right _ _) (le_max_right _ _)
  -- the determinant bound
  set K3 : Set (ℝ × ℝ × ℝ) := Set.Icc b 1 ×ˢ
    (Set.Icc (1 / 5 : ℝ) (3 / 2) ×ˢ Set.Icc (1 / 5 : ℝ) (3 / 2)) with hK3
  have hdetC : IsCompact K3 := by
    rw [hK3]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hdetcont : ContinuousOn (detfn_c n h) K3 := by
    have hK3' : K3 = Set.Icc b 1 ×ˢ
        (Set.Icc (1 / 5 : ℝ) (3 / 2) ×ˢ Set.Icc (1 / 5 : ℝ) (3 / 2)) := hK3
    have c1 : ContinuousOn (fun q : ℝ × ℝ × ℝ => k1fun_c n h (q.1, -(q.2.1))) K3 :=
      ((contDiffOn_k1fun_c hh n).continuousOn).comp (by fun_prop)
        (fun q hq => by
          rw [hK3] at hq
          exact hsub q.1 hq.1 (-(q.2.1)) (by
            rw [abs_neg, abs_of_pos (by linarith [hq.2.1.1] : (0:ℝ) < q.2.1)]
            exact hq.2.1.1))
    have c2 : ContinuousOn (fun q : ℝ × ℝ × ℝ => k2fun_c n h (q.1, q.2.2)) K3 :=
      ((contDiffOn_k2fun_c hh n).continuousOn).comp (by fun_prop)
        (fun q hq => by
          rw [hK3] at hq
          exact hsub q.1 hq.1 q.2.2 (hPP q.1 hq.1 q.2.2 hq.2.2))
    have c3 : ContinuousOn (fun q : ℝ × ℝ × ℝ => k1fun_c n h (q.1, q.2.2)) K3 :=
      ((contDiffOn_k1fun_c hh n).continuousOn).comp (by fun_prop)
        (fun q hq => by
          rw [hK3] at hq
          exact hsub q.1 hq.1 q.2.2 (hPP q.1 hq.1 q.2.2 hq.2.2))
    have c4 : ContinuousOn (fun q : ℝ × ℝ × ℝ => k2fun_c n h (q.1, -(q.2.1))) K3 :=
      ((contDiffOn_k2fun_c hh n).continuousOn).comp (by fun_prop)
        (fun q hq => by
          rw [hK3] at hq
          exact hsub q.1 hq.1 (-(q.2.1)) (by
            rw [abs_neg, abs_of_pos (by linarith [hq.2.1.1] : (0:ℝ) < q.2.1)]
            exact hq.2.1.1))
    exact (c1.mul c2).sub (c3.mul c4) |>.abs
  have hdetpos : ∀ q ∈ K3, 0 < detfn_c n h q := by
    intro q hq
    rw [hK3] at hq
    have hs : 0 < q.1 := lt_of_lt_of_le hb hq.1.1
    have ha : 0 < q.2.1 := by linarith [hq.2.1.1]
    have hc : 0 < q.2.2 := by linarith [hq.2.2.1]
    have hLx : q.1 * (-(q.2.1)) + h q.1 < 0 := by
      have hh' := line_neg_of_le_c hsupp hsmall (s := q.1) (t := -(q.2.1))
        (lt_of_lt_of_le hb hq.1.1) (by linarith [hq.2.1.1])
      simpa [line] using hh'
    have hLy : 0 < q.1 * q.2.2 + h q.1 := by
      have hh' := line_pos_of_ge_c hsupp hsmall (s := q.1) (t := q.2.2)
        (lt_of_lt_of_le hb hq.1.1) (by linarith [hq.2.2.1])
      simpa [line] using hh'
    have hDx : -(q.2.1) + deriv h q.1 < 0 := by
      have hh' := lineSlope_neg_of_le_c (h := h) hsmall (s := q.1) (t := -(q.2.1))
        (by linarith [hq.2.1.1])
      simpa [lineSlope] using hh'
    have hDy : 0 < q.2.2 + deriv h q.1 := by
      have hh' := lineSlope_pos_of_ge_c (h := h) hsmall (s := q.1) (t := q.2.2)
        (by linarith [hq.2.2.1])
      simpa [lineSlope] using hh'
    have hne := Work.OddCurve.detKernel_ne_zero n hh hs ha hc hLx hLy hDx hDy
    rw [K1_eq_K1d_c, K1_eq_K1d_c, K2_eq_K2d_c, K2_eq_K2d_c] at hne
    show 0 < |k1fun_c n h (q.1, -(q.2.1)) * k2fun_c n h (q.1, q.2.2) -
      k1fun_c n h (q.1, q.2.2) * k2fun_c n h (q.1, -(q.2.1))|
    rw [k1fun_apply_c, k1fun_apply_c, k2fun_apply_c, k2fun_apply_c]
    exact abs_pos.mpr hne
  obtain ⟨δ0, hδ0pos, hδ0le⟩ := hdetC.exists_forall_le' (f := detfn_c n h) hdetcont hdetpos
  have hδconj : ∀ s ∈ Set.Icc b 1, ∀ a ∈ Set.Icc (1 / 5 : ℝ) (3 / 2),
      ∀ c ∈ Set.Icc (1 / 5 : ℝ) (3 / 2),
      δ0 ≤ |K1d_c n h s (-a) * K2d_c n h s c - K1d_c n h s c * K2d_c n h s (-a)| := by
    intro s hs a ha c hc
    have hp : (s, (a, c)) ∈ K3 := by
      rw [hK3]
      exact ⟨hs, ha, hc⟩
    have h1 := hδ0le (s, (a, c)) hp
    rw [detfn_c, k1fun_apply_c, k1fun_apply_c, k2fun_apply_c, k2fun_apply_c] at h1
    exact h1
  -- assemble
  refine ⟨max 1 (max Q1 Q2), hBpos, δ0, hδ0pos,
    max (max (C1p : ℝ) (C1n : ℝ)) (max (C2p : ℝ) (C2n : ℝ)), ?_, hBconj, hδconj, ?_, ?_⟩
  · exact le_trans (by positivity : (0:ℝ) ≤ (C1p : ℝ))
      (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro s hs t ht t' ht'
    exact ⟨le_trans (key1p s hs t ht t' ht')
        (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _))
          (abs_nonneg _)),
      le_trans (key2p s hs t ht t' ht')
        (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _))
          (abs_nonneg _))⟩
  · intro s hs t ht t' ht'
    exact ⟨le_trans (key1n s hs t ht t' ht')
        (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _))
          (abs_nonneg _)),
      le_trans (key2n s hs t ht t' ht')
        (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _))
          (abs_nonneg _))⟩

/-- **Compatible re-packaging of `godd_injective_modulus_state_ball`.**  This is the *same*
statement as `Work.OddVolterra.Existence.godd_injective_modulus_state_ball` (proved in
`Submission/Work/OddVolterra/Existence/godd_injective_modulus_state_ball.lean`; porting that proof
is expected and encouraged --- copy the file and rename the colliding helpers), re-proved in a module
that can be imported together with `Submission.Work.OddVolterra.Existence.theta_integrable`.

Why a second module is needed: the existing file declares the top-level name
`Work.OddVolterra.Existence.h_eq_zero_of_lt`, which `theta_integrable` also declares, so any module
importing both fails with "environment already contains `Work.OddVolterra.Existence.h_eq_zero_of_lt`".
Therefore this file must `import Submission.Work.OddVolterra.Existence.base_volterra` (its closure
contains `theta_integrable`, so the collision is visible in your own build) and must **not** declare
any top-level name that already exists in that closure --- in particular rename
`h_eq_zero_of_lt` (or make it `private`).  Do **not** import
`Submission.Work.OddVolterra.Existence.godd_injective_modulus_state_ball`. -/
theorem godd_injective_modulus_state_ball_compat (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ s ∈ Set.Icc b 1,
      ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState s) (1 / 2),
      ∀ z' ∈ Metric.closedBall (Work.OddVolterra.baseState s) (1 / 2),
      c * ‖z - z'‖ ≤ ‖Work.OddVolterra.Godd n h s z - Work.OddVolterra.Godd n h s z'‖ := by
  obtain ⟨B, hB, δ, hδ, ℓ, hℓ, hbound, hdet, hlip, hlip'⟩ :=
    kernel_bounds_c n hn hh hsupp (fun k hk => hsmall k (le_trans hk (by norm_num))) hb hb1
  exact godd_modulus_of_bounds_c n hb hB hδ hℓ hbound hdet hlip hlip'


end

end Work.OddVolterra.Existence


