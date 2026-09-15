import Mathlib
import Submission.Commons.Analysis.Complex.divisor_subBall_factor
import Submission.Commons.Analysis.Complex.divisor_sum_le_circleAverage

namespace Commons.Analysis.Complex.Blaschke

open MeasureTheory Metric
open scoped ENNReal
open Polynomial

/-- Algebraic identity underlying the Blaschke factor: for `r : ℝ`, `u z : ℂ`,
`‖r² - conj u * z‖² - r² ‖z-u‖² = (r² - ‖z‖²)(r² - ‖u‖²)` (in `normSq` form). -/
private lemma normSq_blaschke_identity {r : ℝ} (u z : ℂ) :
    Complex.normSq ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)
      - (r ^ 2) * Complex.normSq (z - u)
      = (r ^ 2 - Complex.normSq z) * (r ^ 2 - Complex.normSq u) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, ← Complex.ofReal_pow]
  ring

/-- The Blaschke denominator does not vanish on the closed disk when `‖u‖ < r`. -/
private lemma blaschke_denom_aux {r : ℝ} (hr : 0 < r) {u z : ℂ} (hu : ‖u‖ < r)
    (hz : ‖z‖ ≤ r) : (r : ℂ) ^ 2 - (starRingEnd ℂ) u * z ≠ 0 := by
  have hr2 : ‖(r : ℂ) ^ 2‖ = r ^ 2 := by
    rw [norm_pow, show ‖(r : ℂ)‖ = r by simp [abs_of_pos hr]]
  have hbound : ‖(starRingEnd ℂ) u * z‖ < ‖(r : ℂ) ^ 2‖ := by
    rw [norm_mul, show ‖(starRingEnd ℂ) u‖ = ‖u‖ by simp, hr2]
    nlinarith [norm_nonneg u, norm_nonneg z, hu, hz]
  intro h
  have hzero : ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ = 0 := by rw [h, norm_zero]
  have htri : ‖(r : ℂ) ^ 2‖ - ‖(starRingEnd ℂ) u * z‖
      ≤ ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ :=
    le_trans (le_abs_self _) (abs_norm_sub_norm_le _ _)
  linarith [hbound]

/-- The Blaschke factor is bounded by `1` on the closed disk. -/
private lemma blaschke_norm_le_aux {r : ℝ} (hr : 0 < r) {u z : ℂ} (hu : ‖u‖ ≤ r)
    (hz : ‖z‖ ≤ r) :
    ‖(r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ ≤ 1 := by
  have hsq : (r * ‖z - u‖) ^ 2 ≤ ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm]
    have hid := normSq_blaschke_identity (r := r) u z
    have hnn : 0 ≤ (r ^ 2 - Complex.normSq z) * (r ^ 2 - Complex.normSq u) := by
      apply mul_nonneg <;> rw [Complex.normSq_eq_norm_sq] <;>
        nlinarith [norm_nonneg z, norm_nonneg u, hu, hz]
    linarith [hid]
  have hle : r * ‖z - u‖ ≤ ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ := by
    have h := sq_le_sq.mp hsq
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg (norm_nonneg _)] at h
  rcases eq_or_ne ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z) 0 with h | h
  · rw [h, div_zero, norm_zero]; norm_num
  · rw [norm_div, norm_mul, show ‖(r : ℂ)‖ = r by simp [abs_of_pos hr],
      div_le_one (norm_pos_iff.mpr h)]
    exact hle

/-- The Blaschke factor has modulus exactly `1` on the boundary circle. -/
private lemma blaschke_norm_eq_aux {r : ℝ} (hr : 0 < r) {u z : ℂ} (hu : ‖u‖ < r)
    (hz : ‖z‖ = r) :
    ‖(r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ = 1 := by
  have hden := blaschke_denom_aux hr hu hz.le
  have hsq : (r * ‖z - u‖) ^ 2 = ‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm]
    have hid := normSq_blaschke_identity (r := r) u z
    have hz2 : Complex.normSq z = r ^ 2 := by rw [Complex.normSq_eq_norm_sq, hz]
    rw [hz2, sub_self, zero_mul] at hid
    linarith [hid]
  have habs : |r * ‖z - u‖| = |‖(r : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖| :=
    (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (norm_nonneg _)] at habs
  rw [norm_div, norm_mul, show ‖(r : ℂ)‖ = r by simp [abs_of_pos hr]]
  rw [div_eq_one_iff_eq (ne_of_gt (norm_pos_iff.mpr hden))]
  exact habs

private theorem circleAverage_log_norm_le_log_of_bound_aux {φ : ℂ → ℂ} {M : ℝ} (hM : 1 ≤ M)
    (hφ : AnalyticOnNhd ℂ φ (Metric.ball 0 5))
    (hb : ∀ z : ℂ, z ∈ Metric.ball 0 4 → ‖φ z‖ ≤ M) :
    Real.circleAverage (fun z : ℂ => Real.log ‖φ z‖) 0 4 ≤ Real.log M := by
  have hcl4 : closure (Metric.ball (0:ℂ) (4:ℝ)) = Metric.closedBall 0 4 :=
    closure_ball 0 (by norm_num)
  have hcont : ContinuousOn (fun z : ℂ => ‖φ z‖) (closure (Metric.ball (0:ℂ) (4:ℝ))) := by
    rw [hcl4]
    exact (hφ.mono (Metric.closedBall_subset_ball (by norm_num))).continuousOn.norm
  have himg : ((fun z : ℂ => ‖φ z‖) '' Metric.ball (0:ℂ) (4:ℝ)) ⊆ Set.Iic M := by
    rintro y ⟨z, hz, rfl⟩
    exact hb z hz
  have hclosed : ∀ z ∈ Metric.closedBall (0:ℂ) 4, ‖φ z‖ ≤ M := by
    intro z hz
    rw [← hcl4] at hz
    exact closure_minimal himg isClosed_Iic (hcont.image_closure (s := Metric.ball (0:ℂ) 4) ⟨z, hz, rfl⟩)
  have hint : CircleIntegrable (fun z : ℂ => Real.log ‖φ z‖) 0 4 :=
    (hφ.mono (Metric.sphere_subset_closedBall.trans
      (Metric.closedBall_subset_ball (by norm_num)))).meromorphicOn.circleIntegrable_log_norm
  refine Real.circleAverage_mono_on_of_le_circle hint (fun z hz => ?_)
  rw [Metric.mem_sphere, dist_zero_right, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)] at hz
  rcases eq_or_ne (φ z) 0 with h0 | h0
  · rw [h0, norm_zero, Real.log_zero]; exact Real.log_nonneg hM
  · exact Real.log_le_log (norm_pos_iff.mpr h0)
      (hclosed z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz.le))

theorem kovrijkine_blaschke_core :
    ∀ (φ : ℂ → ℂ) (M : ℝ),
    AnalyticOnNhd ℂ φ (Metric.ball 0 5) → (∀ z : ℂ, z ∈ Metric.ball 0 4 → ‖φ z‖ ≤ M) →
    1 ≤ M → 1 ≤ ‖φ 0‖ →
    ∃ (N : ℕ) (A : ℝ) (b h : ℂ → ℂ) (P : Polynomial ℂ),
      0 < A ∧ P.Monic ∧ P.natDegree = N ∧
      AnalyticOnNhd ℂ b (Metric.ball 0 ((7:ℝ)/2)) ∧ AnalyticOnNhd ℂ h (Metric.ball 0 ((7:ℝ)/2)) ∧
      (∀ z : ℂ, z ∈ Metric.ball 0 ((7:ℝ)/2) → h z ≠ 0) ∧
      (∀ z : ℂ, z ∈ Metric.ball 0 ((7:ℝ)/2) → φ z = b z * h z) ∧
      (∀ z : ℂ, ‖z‖ = ((7:ℝ)/2) → ‖b z‖ = 1) ∧ (∀ z : ℂ, z ∈ Metric.ball 0 ((7:ℝ)/2) → ‖b z‖ ≤ 1) ∧
      (∀ x : ℝ, x ∈ Set.Icc (0:ℝ) 1 → ‖P.eval (x:ℂ)‖ ≤ A ^ N * ‖b (x:ℂ)‖) ∧
      (∀ z : ℂ, z ∈ Metric.ball 0 ((7:ℝ)/2) → ‖h z‖ ≤ M) ∧ 1 ≤ ‖h 0‖ ∧
      (N : ℝ) * Real.log (4 / ((7:ℝ)/2)) ≤ Real.log M := by
  intro φ M hφ hM hM1 hφ0
  classical
  set r : ℝ := 7/2 with hr_def
  have hr : (0:ℝ) < r := by rw [hr_def]; norm_num
  have hr5 : r < 5 := by rw [hr_def]; norm_num
  have hr4 : r < 4 := by rw [hr_def]; norm_num
  have hr1 : (1:ℝ) < r := by rw [hr_def]; norm_num
  have hφ0ne : φ 0 ≠ 0 := by intro h; rw [h, norm_zero] at hφ0; linarith
  -- (1) divisor support finite on ball 0 r
  have h3 : (MeromorphicOn.divisor φ (Metric.ball 0 r)).support.Finite :=
    MeromorphicOn.divisor_ball_support_finite ((hφ.mono (Metric.closedBall_subset_ball hr5)).meromorphicOn)
  -- (2) all orders are finite on ball 0 5
  have h0mem5 : (0:ℂ) ∈ Metric.ball 0 (5:ℝ) := by rw [Metric.mem_ball, dist_zero_right]; norm_num
  have h2 : ∀ z ∈ Metric.ball 0 (5:ℝ), meromorphicOrderAt φ z ≠ ⊤ := by
    have hconn : IsConnected (Metric.ball (0:ℂ) (5:ℝ)) := Metric.isConnected_ball (by norm_num : (0:ℝ) < 5)
    have hex := (MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall hφ.meromorphicOn hconn)
    intro z hz
    refine (hex.1 ⟨⟨0, h0mem5⟩, ?_⟩) ⟨z, hz⟩
    exact meromorphicOrderAt_ne_top_of_analytic_ne_zero (hφ 0 h0mem5) hφ0ne
  -- (3) factor out the zeros
  obtain ⟨g, hg_an, hg_nz, hg_eq⟩ :=
    factor_subBall_divisor (U := Metric.ball 0 (5:ℝ)) (V := Metric.ball 0 r)
      (Metric.ball_subset_ball (le_of_lt hr5)) hφ.meromorphicOn h2 hφ h3
  -- notation
  let D : ℂ → ℤ := fun u => MeromorphicOn.divisor φ (Metric.ball 0 r) u
  let S : Finset ℂ := h3.toFinset
  have hS_coe : (S : Set ℂ) = Function.support D := by
    simpa [S, D, Function.support] using h3.coe_toFinset
  let dn : ℂ → ℕ := fun u => (D u).toNat
  let N : ℕ := ∑ u ∈ S, dn u
  let P : Polynomial ℂ := ∏ u ∈ S, (X - C u) ^ dn u
  let Qf : ℂ → ℂ := fun z => ∏ u ∈ S, ((r:ℂ)^2 - (starRingEnd ℂ) u * z) ^ dn u
  let b : ℂ → ℂ := fun z => ∏ u ∈ S,
    ((r:ℂ) * (z - u) / ((r:ℂ)^2 - (starRingEnd ℂ) u * z)) ^ dn u
  let h : ℂ → ℂ := fun z => g z * Qf z / (r:ℂ)^N
  -- membership facts
  have hD_mem : ∀ u, D u ≠ 0 → u ∈ Metric.ball 0 r := by
    intro u hu
    by_contra hc
    apply hu
    show MeromorphicOn.divisor φ (Metric.ball 0 r) u = 0
    rw [MeromorphicOn.divisor_def]
    simp [hc]
  have hS_lt : ∀ u ∈ S, ‖u‖ < r := by
    intro u hu
    have hu' : u ∈ Function.support D := by rw [← hS_coe]; exact hu
    rw [Function.mem_support] at hu'
    have := hD_mem u hu'
    rwa [Metric.mem_ball, dist_zero_right] at this
  have hD_nonneg : ∀ u, 0 ≤ D u := by
    intro u
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hφ.mono (Metric.ball_subset_ball (le_of_lt hr5))) u
  have hQf_ne : ∀ z, ‖z‖ ≤ r → Qf z ≠ 0 := by
    intro z hz
    change (∏ u ∈ S, ((r:ℂ)^2 - (starRingEnd ℂ) u * z) ^ (dn u)) ≠ 0
    apply Finset.prod_ne_zero_iff.mpr
    intro u hu
    exact pow_ne_zero _ (blaschke_denom_aux hr (hS_lt u hu) hz)
  -- P.eval identity
  have hPz : ∀ z : ℂ, (∏ᶠ u : ℂ, (z - u) ^ (D u)) = P.eval z := by
    intro z
    rw [finprod_eq_prod_of_mulSupport_subset (fun u : ℂ => (z - u) ^ (D u)) ?_]
    · have hstep : ∀ u ∈ S, (z - u) ^ (D u) = (z - u) ^ (dn u) := by
        intro u hu
        have hdu : D u = (dn u : ℤ) := by
          show D u = ((D u).toNat : ℤ)
          exact (Int.toNat_of_nonneg (hD_nonneg u)).symm
        rw [hdu, zpow_natCast]
      rw [Finset.prod_congr rfl hstep]
      simp only [P, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
    · intro u hu
      rw [Function.mem_mulSupport] at hu
      rw [hS_coe, Function.mem_support]
      intro hD0
      exact hu (by rw [hD0, zpow_zero])
  -- phi = P.eval * g on ball 0 5
  have hφ_Pg : ∀ z ∈ Metric.ball 0 (5:ℝ), φ z = P.eval z * g z := by
    intro z hz
    rw [← hPz z]
    exact hg_eq z hz
  have hr2norm : ‖(r : ℂ) ^ 2‖ = r ^ 2 := by
    rw [norm_pow, show ‖(r : ℂ)‖ = r by simp [abs_of_pos hr]]
  -- explicit eval of P
  have hPeval : ∀ z : ℂ, P.eval z = ∏ u ∈ S, (z - u) ^ (dn u) := by
    intro z
    dsimp only [P]
    simp only [Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  have hPmonic : P.Monic := by
    dsimp only [P]
    exact Polynomial.monic_prod_of_monic S _ (fun u hu => (Polynomial.monic_X_sub_C u).pow _)
  have hPdeg : P.natDegree = N := by
    dsimp only [P, N]
    rw [Polynomial.natDegree_prod S _ (fun u hu => pow_ne_zero _ (Polynomial.monic_X_sub_C u).ne_zero)]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  -- b as quotient
  have hb_eq : ∀ z : ℂ, Qf z ≠ 0 → b z = (r : ℂ) ^ N * P.eval z / Qf z := by
    intro z hQz
    dsimp only [b, Qf]
    simp only [div_pow]
    rw [Finset.prod_div_distrib]
    congr 1
    · rw [Finset.prod_congr rfl (fun u hu => mul_pow (r : ℂ) (z - u) (dn u)),
        Finset.prod_mul_distrib, hPeval z, Finset.prod_pow_eq_pow_sum]
  -- analyticity
  have hb_an : AnalyticOnNhd ℂ b (Metric.ball 0 r) := by
    dsimp only [b]
    have key := Finset.analyticOnNhd_prod (𝕜 := ℂ) (s := Metric.ball 0 r)
      (f := fun u z => ((r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)) ^ dn u) S
      (fun u hu => by
        refine AnalyticOnNhd.pow ?_ (dn u)
        refine AnalyticOnNhd.div ?_ ?_ ?_
        · exact analyticOnNhd_const.mul (analyticOnNhd_id.sub analyticOnNhd_const)
        · exact analyticOnNhd_const.sub (analyticOnNhd_const.mul analyticOnNhd_id)
        · intro z hz
          rw [Metric.mem_ball, dist_zero_right] at hz
          exact blaschke_denom_aux hr (hS_lt u hu) (le_of_lt hz))
    rw [show (∏ n ∈ S, (fun u z =>
          ((r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)) ^ dn u) n)
        = (fun z => ∏ u ∈ S,
          ((r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)) ^ dn u) from
      by funext z; rw [Finset.prod_apply]] at key
    exact key
  have hQf_an5 : AnalyticOnNhd ℂ Qf (Metric.ball 0 (5:ℝ)) := by
    dsimp only [Qf]
    have key := Finset.analyticOnNhd_prod (𝕜 := ℂ) (s := Metric.ball 0 (5:ℝ))
      (f := fun u z => ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z) ^ dn u) S
      (fun u hu => AnalyticOnNhd.pow
        (analyticOnNhd_const.sub (analyticOnNhd_const.mul analyticOnNhd_id)) (dn u))
    rw [show (∏ n ∈ S, (fun u z => ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z) ^ dn u) n)
        = (fun z => ∏ u ∈ S, ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z) ^ dn u) from
      by funext z; rw [Finset.prod_apply]] at key
    exact key
  have hQf_an : AnalyticOnNhd ℂ Qf (Metric.ball 0 r) :=
    hQf_an5.mono (Metric.ball_subset_ball (le_of_lt hr5))
  have hrc_ne : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  have hh_an5 : AnalyticOnNhd ℂ h (Metric.ball 0 (5:ℝ)) := by
    dsimp only [h]
    exact (hg_an.mul hQf_an5).div analyticOnNhd_const (fun z hz => pow_ne_zero _ hrc_ne)
  have hh_an : AnalyticOnNhd ℂ h (Metric.ball 0 r) :=
    hh_an5.mono (Metric.ball_subset_ball (le_of_lt hr5))
  have hh_ne : ∀ z ∈ Metric.ball 0 r, h z ≠ 0 := by
    intro z hz
    have hzr : ‖z‖ ≤ r := le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hz)
    dsimp only [h]
    exact div_ne_zero (mul_ne_zero (hg_nz z hz) (hQf_ne z hzr)) (pow_ne_zero _ hrc_ne)
  -- phi = b * h on the closed ball
  have hφ_eq_bh_cl : ∀ z ∈ Metric.closedBall 0 r, φ z = b z * h z := by
    intro z hz
    have hzr : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    have hz5 : z ∈ Metric.ball 0 (5:ℝ) := Metric.closedBall_subset_ball hr5 hz
    have hQz := hQf_ne z hzr
    rw [hφ_Pg z hz5, hb_eq z hQz]
    dsimp only [h]
    field_simp
  -- boundary and disk values of b
  have hb_circ : ∀ z : ℂ, ‖z‖ = r → ‖b z‖ = 1 := by
    intro z hz
    dsimp only [b]
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro u hu
    rw [norm_pow, blaschke_norm_eq_aux hr (hS_lt u hu) hz, one_pow]
  have hb_le1 : ∀ z ∈ Metric.ball 0 r, ‖b z‖ ≤ 1 := by
    intro z hz
    have hzr : ‖z‖ ≤ r := le_of_lt (by rwa [Metric.mem_ball, dist_zero_right] at hz)
    dsimp only [b]
    rw [norm_prod]
    apply Finset.prod_le_one
    · intro u hu
      positivity
    · intro u hu
      calc ‖((r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)) ^ dn u‖
          = ‖(r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ ^ dn u := norm_pow _ _
        _ ≤ 1 ^ dn u :=
            pow_le_pow_left₀ (norm_nonneg _) (blaschke_norm_le_aux hr (hS_lt u hu).le hzr) (dn u)
        _ = 1 := one_pow _
  -- polynomial inequality
  have hpoly : ∀ x : ℝ, x ∈ Set.Icc (0:ℝ) 1 →
      ‖P.eval (x:ℂ)‖ ≤ (r+1)^N * ‖b (x:ℂ)‖ := by
    intro x hx
    have hxnn : 0 ≤ x := hx.1
    have hxle1 : x ≤ 1 := hx.2
    have hxr : ‖(x:ℂ)‖ ≤ r := by
      rw [show ‖(x:ℂ)‖ = |x| by simp, abs_of_nonneg hxnn]; linarith [hr1]
    have hxs : ‖(x:ℂ)‖ ≤ 1 := by
      rw [show ‖(x:ℂ)‖ = |x| by simp, abs_of_nonneg hxnn]; exact hxle1
    have hPx : ‖P.eval (x:ℂ)‖ = ∏ u ∈ S, ‖(x:ℂ) - u‖ ^ dn u := by
      rw [hPeval, norm_prod]
      simp [norm_pow]
    have hbx : ‖b (x:ℂ)‖ = ∏ u ∈ S,
        ‖(r:ℂ) * ((x:ℂ) - u) / ((r:ℂ)^2 - (starRingEnd ℂ) u * (x:ℂ))‖ ^ dn u := by
      dsimp only [b]
      rw [norm_prod]
      simp [norm_pow]
    rw [hPx, hbx, ← Finset.prod_pow_eq_pow_sum S dn (r+1), ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro u hu; positivity
    · intro u hu
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have hden := blaschke_denom_aux hr (hS_lt u hu) hxr
      have hdpos : 0 < ‖(r:ℂ)^2 - (starRingEnd ℂ) u * (x:ℂ)‖ := norm_pos_iff.mpr hden
      have hdle : ‖(r:ℂ)^2 - (starRingEnd ℂ) u * (x:ℂ)‖ ≤ (r+1) * r := by
        have h1 : ‖(r:ℂ)^2 - (starRingEnd ℂ) u * (x:ℂ)‖
            ≤ ‖(r:ℂ)^2‖ + ‖(starRingEnd ℂ) u * (x:ℂ)‖ := norm_sub_le _ _
        rw [hr2norm, norm_mul, show ‖(starRingEnd ℂ) u‖ = ‖u‖ by simp] at h1
        nlinarith [h1, hS_lt u hu, hxs, norm_nonneg u, norm_nonneg ((x:ℂ) - u)]
      rw [norm_div, norm_mul, show ‖(r:ℂ)‖ = r by simp [abs_of_pos hr], ← mul_div_assoc,
        le_div_iff₀ hdpos]
      nlinarith [hdle, norm_nonneg ((x:ℂ) - u)]
  -- bound on h by the maximum modulus principle
  have hDiffBall : DifferentiableOn ℂ h (Metric.ball 0 r) :=
    (hh_an5.differentiableOn).mono (Metric.ball_subset_ball (le_of_lt hr5))
  have hContCl : ContinuousOn h (Metric.closedBall 0 r) :=
    hh_an5.continuousOn.mono (Metric.closedBall_subset_ball hr5)
  have hDiffCl : DiffContOnCl ℂ h (Metric.ball 0 r) := DiffContOnCl.mk_ball hDiffBall hContCl
  have hhM : ∀ z ∈ Metric.ball 0 r, ‖h z‖ ≤ M := by
    intro z hz
    have hzcl : z ∈ closure (Metric.ball 0 r) := by
      rw [closure_ball 0 (ne_of_gt hr)]; exact Metric.ball_subset_closedBall hz
    exact Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball) hDiffCl
      (fun w hw => by
        rw [frontier_ball 0 (ne_of_gt hr), Metric.mem_sphere, dist_zero_right] at hw
        have hwm : w ∈ Metric.closedBall 0 r := by
          rw [Metric.mem_closedBall, dist_zero_right]; exact hw.le
        have heq := hφ_eq_bh_cl w hwm
        have hb1 : ‖b w‖ = 1 := hb_circ w hw
        have : ‖h w‖ = ‖φ w‖ := by rw [heq, norm_mul, hb1, one_mul]
        rw [this]
        exact hM w (by rw [Metric.mem_ball, dist_zero_right, hw]; exact hr4)) hzcl
  have hφ_eq_bh : ∀ z ∈ Metric.ball 0 r, φ z = b z * h z :=
    fun z hz => hφ_eq_bh_cl z (Metric.ball_subset_closedBall hz)
  have hh0 : 1 ≤ ‖h 0‖ := by
    have h0cl : (0:ℂ) ∈ Metric.closedBall 0 r := by
      rw [Metric.mem_closedBall, dist_zero_right]; simpa using hr.le
    have h0ball : (0:ℂ) ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_zero_right]; simpa using hr
    have heq := hφ_eq_bh_cl 0 h0cl
    have hb0ne : b 0 ≠ 0 := by intro hb0; rw [hb0, zero_mul] at heq; exact hφ0ne heq
    have hb0pos : 0 < ‖b 0‖ := norm_pos_iff.mpr hb0ne
    have hb0le : ‖b 0‖ ≤ 1 := hb_le1 0 h0ball
    have hnorm : ‖h 0‖ = ‖φ 0‖ / ‖b 0‖ := by
      rw [show ‖φ 0‖ = ‖b 0‖ * ‖h 0‖ by rw [heq, norm_mul],
        mul_div_cancel_left₀ ‖h 0‖ (ne_of_gt hb0pos)]
    rw [hnorm, le_div_iff₀ hb0pos]
    nlinarith [hb0le, hφ0]
  -- counting bound
  have hNreal : (N : ℝ) = ∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) := by
    have h1 : (N : ℝ) = ∑ u ∈ S, (dn u : ℝ) := by
      rw [show N = ∑ u ∈ S, dn u from rfl]
      push_cast
      rfl
    rw [h1, finsum_eq_sum_of_support_subset (fun u : ℂ => ((D u : ℤ) : ℝ)) ?_]
    · apply Finset.sum_congr rfl
      intro u hu
      dsimp only [dn]
      exact_mod_cast (Int.toNat_of_nonneg (hD_nonneg u))
    · intro u hu
      rw [Function.mem_support] at hu
      rw [hS_coe, Function.mem_support]
      exact fun h => hu (by exact_mod_cast h)
  have hDsupp : Function.HasFiniteSupport (fun u : ℂ => ((D u : ℤ) : ℝ)) := by
    show (Function.support (fun u : ℂ => ((D u : ℤ) : ℝ))).Finite
    exact h3.subset (fun u hu => by
      rw [Function.mem_support] at hu ⊢
      exact fun h => hu (by exact_mod_cast h))
  have hCdsupp : Function.HasFiniteSupport (fun u : ℂ =>
      ((MeromorphicOn.divisor φ (Metric.closedBall 0 r) u : ℤ) : ℝ)) := by
    show (Function.support (fun u : ℂ =>
      ((MeromorphicOn.divisor φ (Metric.closedBall 0 r) u : ℤ) : ℝ))).Finite
    refine (MeromorphicOn.divisor_support_finite_of_subset
      (hφ.mono (Metric.closedBall_subset_ball hr5)).meromorphicOn
      (isCompact_closedBall 0 r) (subset_refl _)).subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    exact fun h => hu (by exact_mod_cast h)
  have hsum_le : ∑ᶠ u : ℂ, ((D u : ℤ) : ℝ) ≤
      ∑ᶠ u : ℂ, ((MeromorphicOn.divisor φ (Metric.closedBall 0 r) u : ℤ) : ℝ) := by
    apply finsum_le_finsum' hDsupp hCdsupp
    intro u
    change ((D u : ℤ) : ℝ) ≤ ((MeromorphicOn.divisor φ (Metric.closedBall 0 r) u : ℤ) : ℝ)
    by_cases hu : u ∈ Metric.ball 0 r
    · have h1 : D u = (MeromorphicOn.divisor φ (Metric.closedBall 0 r)) u := by
        rw [show D u = MeromorphicOn.divisor φ (Metric.ball 0 r) u from rfl,
          MeromorphicOn.AnalyticOnNhd.divisor_apply (hφ.mono (Metric.ball_subset_ball (le_of_lt hr5))) hu,
          MeromorphicOn.AnalyticOnNhd.divisor_apply (hφ.mono (Metric.closedBall_subset_ball hr5))
            (Metric.ball_subset_closedBall hu)]
      exact_mod_cast le_of_eq h1
    · have h1 : D u = 0 := by
        rw [show D u = MeromorphicOn.divisor φ (Metric.ball 0 r) u from rfl,
          MeromorphicOn.divisor_def]
        simp [hu]
      have hle : D u ≤ (MeromorphicOn.divisor φ (Metric.closedBall 0 r)) u :=
        h1.symm ▸ MeromorphicOn.AnalyticOnNhd.divisor_nonneg
          (hφ.mono (Metric.closedBall_subset_ball hr5)) u
      exact_mod_cast hle
  have hcount : (N : ℝ) * Real.log (4 / r) ≤ Real.log M := by
    have havg := circleAverage_log_norm_le_log_of_bound_aux hM1 hφ hM
    have hJ := divisor_sum_le_circleAverage (c := 0) (r := r) (R := 4) (B := Real.log M)
      hr hr4 (hφ.mono (Metric.closedBall_subset_ball (by norm_num))) hφ0ne havg
    have hlogpos : 0 < Real.log (4 / r) := by
      apply Real.log_pos; rw [one_lt_div hr]; linarith
    rw [hNreal]
    calc (∑ᶠ u : ℂ, ((D u : ℤ) : ℝ)) * Real.log (4 / r)
        ≤ (∑ᶠ u : ℂ, ((MeromorphicOn.divisor φ (Metric.closedBall 0 r) u : ℤ) : ℝ))
            * Real.log (4 / r) := mul_le_mul_of_nonneg_right hsum_le hlogpos.le
      _ ≤ ((Real.log M - Real.log ‖φ 0‖) / Real.log (4 / r)) * Real.log (4 / r) :=
          mul_le_mul_of_nonneg_right hJ hlogpos.le
      _ = Real.log M - Real.log ‖φ 0‖ := div_mul_cancel₀ _ (ne_of_gt hlogpos)
      _ ≤ Real.log M := by have := Real.log_nonneg hφ0; linarith
  refine ⟨N, r+1, b, h, P, ?_, hPmonic, hPdeg, hb_an, hh_an, hh_ne, hφ_eq_bh,
    hb_circ, hb_le1, hpoly, hhM, hh0, hcount⟩
  linarith

end Commons.Analysis.Complex.Blaschke
