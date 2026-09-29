import Mathlib
import Submission.Work.RedProj.circleIntegral_param_holomorphic
import Submission.Work.RedProj.hasSum_sum_antidiagonal
import Submission.Work.RedProj.monomial_formalSeries

/-!
# Separate holomorphy implies joint real-analyticity (Hartogs)

If `F : ℂ → ℂ → ℂ` is continuous on `U ×ˢ V` (for open `U V : Set ℂ`) and holomorphic in each
variable separately, then `(z, w) ↦ F z w` is real-analytic on `U ×ˢ V`.

The proof shows the stronger statement that `(z, w) ↦ F z w` is *complex* analytic.  Fixing
`(z₀, w₀)`, we choose `ρ > 0` with `closedBall z₀ ρ ⊆ U`, `closedBall w₀ ρ ⊆ V`, set
`b n z` to the `n`-th Cauchy coefficient of the `w`-slice `w ↦ F z w`, and use the parametric
Cauchy integral to see that each `b n` is holomorphic in `z`.  Expanding in `w` and then in `z`
produces a doubly-indexed family of coefficients `c m n` with

  `F (z₀ + u) (w₀ + v) = Σ_{m,n} c m n u^m v^n`,

and the diagonal regrouping of this absolutely summable double series is packaged as a formal
power series `P` with `HasFPowerSeriesOnBall (fun p => F p.1 p.2) P (z₀, w₀) (ρ/2)`.
-/


open Set Metric Filter
open scoped Topology

noncomputable section

namespace Work.RedProj

lemma cauchyPowerSeries_apply_one (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (n : ℕ) (w : ℂ) :
    (cauchyPowerSeries f c R n) (fun _ => w) = w^n * (cauchyPowerSeries f c R n) (fun _ => 1) := by
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
    one_pow, smul_eq_mul, one_mul]

lemma cauchyPowerSeries_coeff_eq (f : ℂ → ℂ) (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (m : ℕ) :
    (cauchyPowerSeries f c ρ m) (fun _ => 1)
      = (2 * ↑Real.pi * Complex.I)⁻¹ * ∮ z in C(c, ρ), ((z - c)⁻¹)^m * (z - c)⁻¹ * f z := by
  rw [cauchyPowerSeries_apply]
  rw [show ρ = |ρ| from (abs_of_nonneg hρ).symm]
  congr 1
  apply circleIntegral.integral_congr (abs_nonneg ρ)
  intro z hz
  ring_nf

def cauchyCoeff (F : ℂ → ℂ → ℂ) (w₀ : ℂ) (ρ : ℝ) : ℕ → ℂ → ℂ :=
  fun n z => (cauchyPowerSeries (F z) w₀ ρ n) (fun _ => 1)

lemma cauchyCoeff_eq (F : ℂ → ℂ → ℂ) (w₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) (z : ℂ) :
    cauchyCoeff F w₀ ρ n z
      = (2 * ↑Real.pi * Complex.I)⁻¹ * ∮ w in C(w₀, ρ), ((w - w₀)⁻¹)^n * (w - w₀)⁻¹ * F z w :=
  cauchyPowerSeries_coeff_eq (F z) w₀ hρ n

lemma cauchyCoeff_bound_one {f : ℂ → ℂ} {c : ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ z ∈ sphere c ρ, ‖f z‖ ≤ M) (m : ℕ) :
    ‖(cauchyPowerSeries f c ρ m) (fun _ => 1)‖ ≤ M * ρ⁻¹ ^ m := by
  rw [cauchyPowerSeries_coeff_eq f c hρ.le m]
  refine (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
    (f := fun z => ((z - c)⁻¹)^m * (z - c)⁻¹ * f z) hρ.le (C := ρ⁻¹ ^ (m+1) * M) ?_).trans_eq ?_
  · intro z hz
    have hzc : ‖z - c‖ = ρ := mem_sphere_iff_norm.1 hz
    have hzci : ‖(z - c)⁻¹‖ = ρ⁻¹ := by rw [norm_inv, hzc]
    calc ‖((z - c)⁻¹)^m * (z - c)⁻¹ * f z‖
        = ‖(z - c)⁻¹‖^m * ‖(z - c)⁻¹‖ * ‖f z‖ := by rw [norm_mul, norm_mul, norm_pow]
      _ = (ρ⁻¹)^m * ρ⁻¹ * ‖f z‖ := by rw [hzci]
      _ ≤ (ρ⁻¹)^m * ρ⁻¹ * M := by gcongr; exact hM z hz
      _ = ρ⁻¹^(m+1) * M := by rw [pow_succ]
  · have hpow : ρ * ρ⁻¹ ^ (m+1) = ρ⁻¹ ^ m := by
      rw [pow_succ, ← mul_assoc, mul_comm ρ (ρ⁻¹^m), mul_assoc, mul_inv_cancel₀ hρ.ne', mul_one]
    rw [← mul_assoc, hpow, mul_comm]

lemma cauchyCoeff_bound_uniform {F : ℂ → ℂ → ℂ} {U V : Set ℂ} {w₀ z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (U ×ˢ V))
    (hzBall : closedBall z₀ ρ ⊆ U) (hsphere : sphere w₀ ρ ⊆ V) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (z : ℂ), z ∈ closedBall z₀ ρ →
      ‖cauchyCoeff F w₀ ρ n z‖ ≤ M * ρ⁻¹ ^ n := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ ρ).prod (isCompact_sphere w₀ ρ)
    |>.exists_bound_of_continuousOn (hcont.mono (Set.prod_mono hzBall hsphere))
  refine ⟨max M 0, le_max_right _ _, fun n z hz => ?_⟩
  have hbound : ∀ w ∈ sphere w₀ ρ, ‖F z w‖ ≤ max M 0 :=
    fun w hw => (hM (z, w) ⟨hz, hw⟩).trans (le_max_left _ _)
  simpa only [cauchyCoeff] using cauchyCoeff_bound_one (f := F z) (c := w₀) hρ hbound n

lemma cauchyCoeff_differentiableOn {U V : Set ℂ} (hU : IsOpen U)
    {F : ℂ → ℂ → ℂ} (hcont : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (U ×ˢ V))
    (hw : ∀ w ∈ V, DifferentiableOn ℂ (fun z => F z w) U)
    {w₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsphere : sphere w₀ ρ ⊆ V) (n : ℕ) :
    DifferentiableOn ℂ (cauchyCoeff F w₀ ρ n) U := by
  have h := circleIntegral_param_holomorphic hU hcont hw hρ hsphere n
  have heq : cauchyCoeff F w₀ ρ n
        = (fun z => (2 * ↑Real.pi * Complex.I)⁻¹ *
            (∮ w in C(w₀, ρ), ((w - w₀)⁻¹)^n * (w - w₀)⁻¹ * F z w)) :=
    funext (fun z => cauchyCoeff_eq F w₀ hρ.le n z)
  rw [heq]
  refine (h.const_smul (R := ℂ) ((2 * ↑Real.pi * Complex.I)⁻¹)).congr (fun z hz => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]

lemma hasSum_powerSeries_expansion {f : ℂ → ℂ} {c : ℂ} {R : NNReal} (hR : 0 < R)
    (hd : DifferentiableOn ℂ f (closedBall c (R:ℝ))) {u : ℂ} (hu : ‖u‖ < (R:ℝ)) :
    HasSum (fun m => (cauchyPowerSeries f c (R:ℝ) m) (fun _ => 1) * u^m) (f (c + u)) := by
  have hps := hd.hasFPowerSeriesOnBall hR
  have hmem : u ∈ Metric.eball (0:ℂ) (R:ENNReal) := by
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right]; exact hu
  have hsum := hps.hasSum hmem
  have he : (fun m => cauchyPowerSeries f c (R:ℝ) m (fun _ => u))
      = fun m => (cauchyPowerSeries f c (R:ℝ) m) (fun _ => 1) * u^m := by
    funext m; rw [cauchyPowerSeries_apply_one]; ring
  rw [he] at hsum
  exact hsum

lemma hasSum_slice_expansion {F : ℂ → ℂ → ℂ} {U V : Set ℂ} {w₀ : ℂ} {R : NNReal} (hR : 0 < R)
    (hB : closedBall w₀ (R:ℝ) ⊆ V) (hz : ∀ z ∈ U, DifferentiableOn ℂ (F z) V)
    {z : ℂ} (hzU : z ∈ U) {w : ℂ} (hw : ‖w - w₀‖ < (R:ℝ)) :
    HasSum (fun n => cauchyCoeff F w₀ (R:ℝ) n z * (w - w₀)^n) (F z w) := by
  have hd : DifferentiableOn ℂ (F z) (closedBall w₀ (R:ℝ)) := (hz z hzU).mono hB
  have hps := hd.hasFPowerSeriesOnBall hR
  have hmem : w - w₀ ∈ Metric.eball (0:ℂ) (R:ENNReal) := by
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right]
    exact hw
  have hsum := hps.hasSum hmem
  have h2 : w₀ + (w - w₀) = w := by ring
  rw [h2] at hsum
  have he : (fun n => cauchyPowerSeries (F z) w₀ (R:ℝ) n (fun _ => w - w₀))
      = fun n => cauchyCoeff F w₀ (R:ℝ) n z * (w - w₀)^n := by
    funext n
    rw [cauchyPowerSeries_apply_one, cauchyCoeff]
    ring
  rw [he] at hsum
  exact hsum

lemma summable_double {M ρ : ℝ} (hρ : 0 < ρ) {c : ℕ → ℕ → ℂ}
    (hc : ∀ m n, ‖c m n‖ ≤ M * ρ⁻¹^n * ρ⁻¹^m) {u v : ℂ} (hu : ‖u‖ < ρ) (hv : ‖v‖ < ρ) :
    Summable (fun p : ℕ × ℕ => c p.1 p.2 * u^p.1 * v^p.2) := by
  have hu1 : ‖u‖ * ρ⁻¹ < 1 := by
    rw [← div_eq_mul_inv]; exact (div_lt_one hρ).2 hu
  have hv1 : ‖v‖ * ρ⁻¹ < 1 := by
    rw [← div_eq_mul_inv]; exact (div_lt_one hρ).2 hv
  have hA0 : (0:ℝ) ≤ ‖u‖ * ρ⁻¹ := mul_nonneg (norm_nonneg _) (inv_nonneg.2 hρ.le)
  have hB0 : (0:ℝ) ≤ ‖v‖ * ρ⁻¹ := mul_nonneg (norm_nonneg _) (inv_nonneg.2 hρ.le)
  have hA : Summable (fun n : ℕ => (‖u‖ * ρ⁻¹)^n) :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hA0])
  have hB : Summable (fun n : ℕ => (‖v‖ * ρ⁻¹)^n) :=
    summable_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hB0])
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    ((Summable.mul_of_nonneg hA hB (fun n => pow_nonneg hA0 n) (fun n => pow_nonneg hB0 n)).mul_left M))
  calc ‖c p.1 p.2 * u^p.1 * v^p.2‖
      = ‖c p.1 p.2‖ * ‖u‖^p.1 * ‖v‖^p.2 := by rw [norm_mul, norm_mul, norm_pow, norm_pow]
    _ ≤ (M * ρ⁻¹^p.2 * ρ⁻¹^p.1) * ‖u‖^p.1 * ‖v‖^p.2 := by gcongr; exact hc p.1 p.2
    _ = M * ((‖u‖ * ρ⁻¹)^p.1 * (‖v‖ * ρ⁻¹)^p.2) := by rw [mul_pow, mul_pow]; ring


lemma coeff_sum_bound {M ρ : ℝ} {c : ℕ → ℕ → ℂ}
    (hc : ∀ m n, ‖c m n‖ ≤ M * ρ⁻¹^n * ρ⁻¹^m) (n : ℕ) :
    ∑ m ∈ Finset.range (n+1), ‖c m (n-m)‖ ≤ ((n+1 : ℕ) : ℝ) * (M * ρ⁻¹^n) := by
  calc ∑ m ∈ Finset.range (n+1), ‖c m (n-m)‖
      ≤ ∑ m ∈ Finset.range (n+1), M * ρ⁻¹^n := by
        apply Finset.sum_le_sum
        intro m hm
        have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
        calc ‖c m (n-m)‖ ≤ M * ρ⁻¹^(n-m) * ρ⁻¹^m := hc m (n-m)
          _ = M * ρ⁻¹^n := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]
    _ = ((n+1 : ℕ) : ℝ) * (M * ρ⁻¹^n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma Pbound {M ρ : ℝ} (hρ : 0 < ρ) {c : ℕ → ℕ → ℂ}
    (hc : ∀ m n, ‖c m n‖ ≤ M * ρ⁻¹^n * ρ⁻¹^m)
    {P : FormalMultilinearSeries ℂ (ℂ × ℂ) ℂ}
    (hPnorm : ∀ n, ‖P n‖ ≤ ∑ m ∈ Finset.range (n+1), ‖c m (n-m)‖) (n : ℕ) :
    ‖P n‖ * (ρ/2)^n ≤ ((n:ℝ)+1) * M * (1/2)^n := by
  have hhalf : ρ⁻¹ * (ρ/2) = 1/2 := by field_simp
  have h2 : (0:ℝ) ≤ ρ/2 := by positivity
  calc ‖P n‖ * (ρ/2)^n
      ≤ (∑ m ∈ Finset.range (n+1), ‖c m (n-m)‖) * (ρ/2)^n :=
        mul_le_mul_of_nonneg_right (hPnorm n) (pow_nonneg h2 n)
    _ ≤ (((n+1 : ℕ) : ℝ) * (M * ρ⁻¹^n)) * (ρ/2)^n :=
        mul_le_mul_of_nonneg_right (coeff_sum_bound hc n) (pow_nonneg h2 n)
    _ = ((n:ℝ)+1) * M * (ρ⁻¹^n * (ρ/2)^n) := by push_cast; ring
    _ = ((n:ℝ)+1) * M * (1/2)^n := by rw [← mul_pow, hhalf]

theorem separately_holomorphic_analytic {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    {F : ℂ → ℂ → ℂ}
    (hcont : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (U ×ˢ V))
    (hz : ∀ z ∈ U, DifferentiableOn ℂ (F z) V)
    (hw : ∀ w ∈ V, DifferentiableOn ℂ (fun z => F z w) U) :
    AnalyticOnNhd ℝ (fun p : ℂ × ℂ => F p.1 p.2) (U ×ˢ V) := by
  have hmain : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => F p.1 p.2) (U ×ˢ V) := by
    intro p₀ hp₀
    obtain ⟨z₀, w₀⟩ := p₀
    rw [mem_prod] at hp₀
    obtain ⟨hz₀, hw₀⟩ := hp₀
    obtain ⟨ρ, hρ, hzU, hwV⟩ : ∃ ρ : ℝ, 0 < ρ ∧ closedBall z₀ ρ ⊆ U ∧ closedBall w₀ ρ ⊆ V := by
      obtain ⟨r₁, hr₁, h₁⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hz₀)
      obtain ⟨r₂, hr₂, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hV.mem_nhds hw₀)
      exact ⟨min r₁ r₂, lt_min hr₁ hr₂,
        (closedBall_subset_closedBall (min_le_left _ _)).trans h₁,
        (closedBall_subset_closedBall (min_le_right _ _)).trans h₂⟩
    let R : NNReal := ⟨ρ, hρ.le⟩
    have hR : 0 < R := by exact_mod_cast hρ
    have hsphere : sphere w₀ (R:ℝ) ⊆ V := sphere_subset_closedBall.trans hwV
    have hb_diff : ∀ n, DifferentiableOn ℂ (cauchyCoeff F w₀ (R:ℝ) n) U :=
      fun n => cauchyCoeff_differentiableOn hU hcont hw hρ hsphere n
    obtain ⟨M, hM0, hM⟩ := cauchyCoeff_bound_uniform (F := F) hρ hcont hzU hsphere
    set c : ℕ → ℕ → ℂ :=
      fun m n => (cauchyPowerSeries (cauchyCoeff F w₀ (R:ℝ) n) z₀ (R:ℝ) m) (fun _ => 1) with hc
    have hcbound : ∀ m n, ‖c m n‖ ≤ M * (R:ℝ)⁻¹ ^ n * (R:ℝ)⁻¹ ^ m := by
      intro m n
      have hM' : ∀ z ∈ sphere z₀ (R:ℝ), ‖cauchyCoeff F w₀ (R:ℝ) n z‖ ≤ M * (R:ℝ)⁻¹ ^ n :=
        fun z hz => hM n z (sphere_subset_closedBall hz)
      have hh := cauchyCoeff_bound_one (f := cauchyCoeff F w₀ (R:ℝ) n) (c := z₀) (ρ := (R:ℝ))
        (M := M * (R:ℝ)⁻¹ ^ n) hρ hM' m
      rw [hc]
      exact hh
    obtain ⟨P, hPapply, hPnorm⟩ := monomial_formalSeries c
    have key : ∀ u v : ℂ, ‖u‖ < ρ → ‖v‖ < ρ →
        HasSum (fun n => P n (fun _ => (u, v))) (F (z₀ + u) (w₀ + v)) := by
      intro u v hu hv
      have hsumm := summable_double hρ hcbound hu hv
      have h1 := hasSum_sum_antidiagonal hsumm
      have step2 : ∀ n, (∑' m, c m n * u^m * v^n)
          = cauchyCoeff F w₀ (R:ℝ) n (z₀ + u) * v^n := by
        intro n
        rw [tsum_mul_right]
        congr 1
        exact (hasSum_powerSeries_expansion (f := cauchyCoeff F w₀ (R:ℝ) n) (c := z₀)
          hR ((hb_diff n).mono hzU) hu).tsum_eq
      have hsum2 : (∑' p : ℕ × ℕ, c p.1 p.2 * u^p.1 * v^p.2) = F (z₀ + u) (w₀ + v) := by
        have h1 : (∑' p : ℕ × ℕ, c p.1 p.2 * u^p.1 * v^p.2)
            = ∑' n : ℕ, ∑' m : ℕ, c m n * u^m * v^n := by
          rw [← Equiv.tsum_eq (Equiv.prodComm ℕ ℕ) (fun p : ℕ × ℕ => c p.1 p.2 * u^p.1 * v^p.2)]
          simp only [Equiv.prodComm_apply]
          rw [Summable.tsum_prod hsumm.prod_symm]
          apply tsum_congr; intro n
          apply tsum_congr; intro m
          simp
        rw [h1, tsum_congr step2]
        have hzu : z₀ + u ∈ U :=
          hzU (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hu.le)
        have hvR : ‖(w₀ + v) - w₀‖ < (R:ℝ) := by rw [add_sub_cancel_left]; exact hv
        have hkey := (hasSum_slice_expansion (F := F) (w₀ := w₀) (R := R) (z := z₀ + u)
          (w := w₀ + v) hR hwV hz hzu hvR).tsum_eq
        simpa only [add_sub_cancel_left] using hkey
      have he : (fun k => P k (fun _ => (u, v)))
          = fun k => ∑ m ∈ Finset.range (k+1), c m (k-m) * u^m * v^(k-m) := by
        funext k; exact hPapply k u v
      rw [← he, hsum2] at h1
      exact h1
    let R2 : NNReal := ⟨ρ/2, by positivity⟩
    have hR2 : 0 < R2 := by exact_mod_cast (show (0:ℝ) < ρ/2 by positivity)
    have hR2c : (R2 : ℝ) = ρ/2 := rfl
    have hmaj : Summable (fun n : ℕ => ((n:ℝ)+1) * M * (1/2:ℝ)^n) := by
      have h1 : Summable (fun n : ℕ => ((n:ℝ)) * (1/2:ℝ)^n) := by
        simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
          (r := (1/2:ℝ)) (by norm_num)
      have h2 : Summable (fun n : ℕ => ((1/2:ℝ))^n) :=
        summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)
      have h3 : Summable (fun n : ℕ => ((n:ℝ)+1) * (1/2)^n) := by
        simpa [add_mul, one_mul] using h1.add h2
      simpa [mul_assoc, mul_comm, mul_left_comm] using h3.mul_left M
    refine ⟨P, R2, { r_le := ?_, r_pos := ?_, hasSum := ?_ }⟩
    · apply P.le_radius_of_summable_norm (r := R2)
      refine Summable.of_nonneg_of_le
        (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _)) (fun n => ?_) hmaj
      have hb := Pbound hρ hcbound hPnorm n
      simpa only [hR2c] using hb
    · exact ENNReal.coe_pos.2 hR2
    · intro y hy
      rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right] at hy
      have hy' : ‖y‖ < ρ/2 := by simpa only [hR2c] using hy
      have hu : ‖y.1‖ < ρ := lt_of_le_of_lt (norm_fst_le y) (by linarith)
      have hv : ‖y.2‖ < ρ := lt_of_le_of_lt (norm_snd_le y) (by linarith)
      have hk := key y.1 y.2 hu hv
      simpa using hk
  exact hmain.restrictScalars


end Work.RedProj
