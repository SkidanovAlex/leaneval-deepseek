import Mathlib
import Submission.Commons.Analysis.Complex.Blaschke.kovrijkine_blaschke_core
import Submission.Commons.Analysis.Complex.Cartan.monic_level_set_volume_le
import Submission.Commons.Analysis.Complex.Harmonic.harnack_inequality_ball

namespace Commons.Analysis.Complex

open MeasureTheory Metric
open _root_.InnerProductSpace
open scoped BigOperators ENNReal

set_option maxHeartbeats 1600000

theorem harnack_lower_bound_zeroFree (h : ℂ → ℂ) (M : ℝ) (hM : 1 ≤ M)
    (han : AnalyticOnNhd ℂ h (Metric.ball 0 3))
    (hne : ∀ z ∈ Metric.ball 0 3, h z ≠ 0)
    (hMbd : ∀ z ∈ Metric.ball 0 3, ‖h z‖ ≤ M)
    (h0 : 1 ≤ ‖h 0‖) :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → (M^2)⁻¹ ≤ ‖h x‖ := by
  intro x hx
  have hxabs1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
  have hxnorm : ‖(x:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hxabs1
  set g : ℂ → ℂ := fun z => (M : ℂ) / h z with hg_def
  have hMpos : (0:ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hgan : AnalyticOnNhd ℂ g (Metric.ball 0 3) := by
    rw [hg_def]
    exact (analyticOnNhd_const).div han (fun z hz => hne z hz)
  have hgne : ∀ z ∈ Metric.ball 0 3, g z ≠ 0 := by
    intro z hz
    rw [hg_def]
    exact div_ne_zero (by exact_mod_cast ne_of_gt hMpos) (hne z hz)
  have hgnorm : ∀ z : ℂ, ‖g z‖ = M / ‖h z‖ := by
    intro z
    rw [hg_def, norm_div, Complex.norm_of_nonneg hMpos.le]
  have hharm : HarmonicOnNhd (fun z => Real.log ‖g z‖) (Metric.closedBall 0 (2:ℝ)) := by
    intro z hz
    have hz3 : z ∈ Metric.ball 0 3 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]; linarith
    exact (hgan z hz3).harmonicAt_log_norm (hgne z hz3)
  have hpos : ∀ z ∈ Metric.closedBall 0 (2:ℝ), 0 ≤ Real.log ‖g z‖ := by
    intro z hz
    have hz3 : z ∈ Metric.ball 0 3 := by
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]; linarith
    rw [hgnorm]
    apply Real.log_nonneg
    rw [le_div_iff₀ (norm_pos_iff.mpr (hne z hz3))]
    linarith [hMbd z hz3]
  have hxball : (x : ℂ) ∈ Metric.ball (0:ℂ) (2:ℝ) := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  obtain ⟨_, hub⟩ :=
    Harmonic.harnack_inequality_ball (a := (0:ℂ)) (R := (2:ℝ)) hharm hpos hxball
  simp only [sub_zero] at hub
  have hfac : ((2:ℝ) + ‖(x:ℂ)‖) / ((2:ℝ) - ‖(x:ℂ)‖) ≤ 3 := by
    have hden : 0 < (2:ℝ) - ‖(x:ℂ)‖ := by linarith [norm_nonneg (x:ℂ)]
    rw [div_le_iff₀ hden]
    nlinarith [norm_nonneg (x:ℂ), hxnorm]
  have h0pos : 0 < ‖h 0‖ := norm_pos_iff.mpr (by intro hc; rw [hc, norm_zero] at h0; linarith)
  have hf0 : Real.log ‖g 0‖ ≤ Real.log M := by
    rw [hgnorm]
    apply Real.log_le_log (div_pos hMpos h0pos)
    rw [div_le_iff₀ h0pos]; nlinarith [h0, hMpos]
  have hfx : Real.log ‖g x‖ ≤ 3 * Real.log M := by
    have h2 : ((2:ℝ) + ‖(x:ℂ)‖) / ((2:ℝ) - ‖(x:ℂ)‖) * Real.log ‖g 0‖ ≤ 3 * Real.log M :=
      mul_le_mul hfac hf0 (hpos 0 (by simp [Metric.mem_closedBall])) (by norm_num)
    linarith
  have hxr : (x:ℂ) ∈ Metric.ball 0 3 := by
    rw [Metric.mem_ball, dist_zero_right]; linarith
  have hhxne : h x ≠ 0 := hne (x:ℂ) hxr
  have hhxpos : 0 < ‖h x‖ := norm_pos_iff.mpr hhxne
  have hlogx : Real.log ‖g x‖ = Real.log M - Real.log ‖h x‖ := by
    rw [hgnorm, Real.log_div (ne_of_gt hMpos) (ne_of_gt hhxpos)]
  rw [hlogx] at hfx
  have hfin : -2 * Real.log M ≤ Real.log ‖h x‖ := by linarith
  have hexp : Real.exp (-2 * Real.log M) ≤ Real.exp (Real.log ‖h x‖) := Real.exp_le_exp.mpr hfin
  rw [Real.exp_log hhxpos] at hexp
  have hexp2 : Real.exp (2 * Real.log M) = M^2 := by
    have h : (2:ℝ) * Real.log M = Real.log (M^2) := by rw [Real.log_pow]; norm_num
    rw [h, Real.exp_log (by positivity)]
  have hgoal : Real.exp (-2 * Real.log M) = (M^2)⁻¹ := by
    rw [show -2 * Real.log M = -(2 * Real.log M) by ring, Real.exp_neg, hexp2]
  rwa [hgoal] at hexp



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

theorem kovrijkine_blaschke_core_Icc :
    ∀ (φ : ℂ → ℂ) (M : ℝ),
    AnalyticOnNhd ℂ φ (Metric.ball 0 5) → (∀ z : ℂ, z ∈ Metric.ball 0 4 → ‖φ z‖ ≤ M) →
    1 ≤ M → 1 ≤ ‖φ 0‖ →
    ∃ (N : ℕ) (b h : ℂ → ℂ) (P : Polynomial ℂ),
      P.Monic ∧ P.natDegree = N ∧
      AnalyticOnNhd ℂ b (Metric.ball 0 3) ∧ AnalyticOnNhd ℂ h (Metric.ball 0 3) ∧
      (∀ z : ℂ, z ∈ Metric.ball 0 3 → h z ≠ 0) ∧
      (∀ z : ℂ, z ∈ Metric.ball 0 3 → φ z = b z * h z) ∧
      (∀ z : ℂ, ‖z‖ = 3 → ‖b z‖ = 1) ∧ (∀ z : ℂ, z ∈ Metric.ball 0 3 → ‖b z‖ ≤ 1) ∧
      (∀ x : ℝ, x ∈ Set.Icc (-1:ℝ) 1 → ‖P.eval (x:ℂ)‖ ≤ (4:ℝ) ^ N * ‖b (x:ℂ)‖) ∧
      (∀ z : ℂ, z ∈ Metric.ball 0 3 → ‖h z‖ ≤ M) ∧ 1 ≤ ‖h 0‖ ∧
      (N : ℝ) * Real.log (4 / 3) ≤ Real.log M := by
  intro φ M hφ hM hM1 hφ0
  classical
  set r : ℝ := 3 with hr_def
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
    apply Finset.prod_le_one₀
    · intro u hu
      positivity
    · intro u hu
      calc ‖((r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)) ^ dn u‖
          = ‖(r : ℂ) * (z - u) / ((r : ℂ) ^ 2 - (starRingEnd ℂ) u * z)‖ ^ dn u := norm_pow _ _
        _ ≤ 1 ^ dn u :=
            pow_le_pow_left₀ (norm_nonneg _) (blaschke_norm_le_aux hr (hS_lt u hu).le hzr) (dn u)
        _ = 1 := one_pow _
  -- polynomial inequality
  have hpoly : ∀ x : ℝ, x ∈ Set.Icc (-1:ℝ) 1 →
      ‖P.eval (x:ℂ)‖ ≤ (r+1)^N * ‖b (x:ℂ)‖ := by
    intro x hx
    have hxabs : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have hxr : ‖(x:ℂ)‖ ≤ r := by
      rw [show ‖(x:ℂ)‖ = |x| by simp]; linarith [hr1]
    have hxs : ‖(x:ℂ)‖ ≤ 1 := by
      rw [show ‖(x:ℂ)‖ = |x| by simp]; exact hxabs
    have hPx : ‖P.eval (x:ℂ)‖ = ∏ u ∈ S, ‖(x:ℂ) - u‖ ^ dn u := by
      rw [hPeval, norm_prod]
      simp [norm_pow]
    have hbx : ‖b (x:ℂ)‖ = ∏ u ∈ S,
        ‖(r:ℂ) * ((x:ℂ) - u) / ((r:ℂ)^2 - (starRingEnd ℂ) u * (x:ℂ))‖ ^ dn u := by
      dsimp only [b]
      rw [norm_prod]
      simp [norm_pow]
    rw [hPx, hbx, ← Finset.prod_pow_eq_pow_sum S dn (r+1), ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
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
  refine ⟨N, b, h, P, hPmonic, hPdeg, hb_an, hh_an, hh_ne, hφ_eq_bh,
    hb_circ, hb_le1, ?_, hhM, hh0, hcount⟩
  intro x hx
  have hr4 : r + 1 = (4:ℝ) := by rw [hr_def]; norm_num
  have := hpoly x hx
  rwa [hr4] at this



theorem packing_separated_Icc (E : Set ℝ) (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-1:ℝ) 1)
    (Δ : ℝ) (hΔ : 0 < Δ) (N : ℕ) (hmeas : 2 * (N:ℝ) * Δ < (volume E).toReal) :
    ∃ x : Fin (N+1) → ℝ, StrictMono x ∧ (∀ i, x i ∈ E) ∧
      (∀ i : Fin N, x (Fin.castSucc i) + Δ ≤ x i.succ) := by
  have hfin : volume E ≠ ⊤ := by
    have hle : volume E ≤ (2 : ℝ≥0∞) := by
      calc volume E ≤ volume (Set.Icc (-1:ℝ) 1) := measure_mono hEsub
        _ = ENNReal.ofReal ((1:ℝ) - (-1)) := Real.volume_Icc
        _ = 2 := by norm_num
    exact ne_of_lt (lt_of_le_of_lt hle (by norm_num))
  obtain ⟨t, ht, hsep⟩ :=
    Commons.Measure.Real.separated_points_of_measure E hE hfin N Δ hΔ.le hmeas
  exact Commons.Analysis.Measure.exists_strictMono_of_separated hΔ t ht hsep

theorem monic_level_set_Icc_volume_le (N : ℕ) (hN : 1 ≤ N) (P : Polynomial ℂ) (hPmonic : P.Monic)
    (hPnatdeg : P.natDegree = N) (δ : ℝ) (hδ : 0 < δ) (E : Set ℝ) (hEmeas : MeasurableSet E)
    (hEsub : E ⊆ Set.Icc (-1:ℝ) 1) (hP : ∀ x ∈ E, ‖P.eval (x:ℂ)‖ ≤ δ) :
    (volume E).toReal ≤ 30 * δ ^ ((1:ℝ)/N) := by
  classical
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hPdeg : P.degree = (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hPne, hPnatdeg]
  have hPcoeff : P.coeff N = 1 := by
    have := hPmonic.coeff_natDegree
    rwa [hPnatdeg] at this
  set Δ : ℝ := 15 * δ ^ ((1:ℝ)/N) / N with hΔdef
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hΔpos : 0 < Δ := by
    rw [hΔdef]
    have : 0 < δ ^ ((1:ℝ)/N) := Real.rpow_pos_of_pos hδ _
    positivity
  have hDelta : 2 * (N:ℝ) * Δ = 30 * δ ^ ((1:ℝ)/N) := by
    rw [hΔdef]; field_simp; ring
  have hbound : (volume E).toReal ≤ 30 * δ ^ ((1:ℝ)/N) := by
    by_contra hcon
    rw [not_le] at hcon
    have hmeas : 2 * (N:ℝ) * Δ < (volume E).toReal := by rw [hDelta]; exact hcon
    obtain ⟨x, hxmono, hxmem, hxgap⟩ :=
      packing_separated_Icc E hEmeas hEsub Δ hΔpos N hmeas
    have hv : Set.InjOn (fun i : Fin (N+1) => ((x i : ℝ) : ℂ)) ↑(Finset.univ : Finset (Fin (N+1))) := by
      intro i _ j _ hij
      have hxij : x i = x j := Complex.ofReal_injective hij
      exact hxmono.injective hxij
    have hdeg : P.degree < ((Finset.univ : Finset (Fin (N+1))).card : WithBot ℕ) := by
      rw [hPdeg, Finset.card_univ, Fintype.card_fin]
      exact_mod_cast Nat.lt_succ_self N
    have hLag := Lagrange.coeff_eq_sum (s := (Finset.univ : Finset (Fin (N+1))))
      (v := fun i => ((x i : ℝ) : ℂ)) hv hdeg
    have hcard : (Finset.univ : Finset (Fin (N+1))).card = N+1 := by
      rw [Finset.card_univ, Fintype.card_fin]
    rw [hcard, Nat.add_sub_cancel] at hLag
    -- Lagrange bound
    have hstep1 : (1:ℝ) ≤ ∑ i : Fin (N+1),
        ‖P.eval ((x i : ℝ) : ℂ) /
          ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖ := by
      have hle := norm_sum_le (Finset.univ : Finset (Fin (N+1)))
        (fun i => P.eval ((x i : ℝ) : ℂ) /
          ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ)))
      rw [← hLag, hPcoeff, norm_one] at hle
      exact hle
    have hterm : ∀ i : Fin (N+1),
        ‖P.eval ((x i : ℝ) : ℂ) /
          ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖ ≤
        δ / ∏ j ∈ (Finset.univ.erase i), |x i - x j| := by
      intro i
      rw [norm_div]
      have hnum : ‖P.eval ((x i : ℝ) : ℂ)‖ ≤ δ := hP (x i) (hxmem i)
      have hden : ‖∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖
          = ∏ j ∈ (Finset.univ.erase i), |x i - x j| := by
        rw [norm_prod]
        apply Finset.prod_congr rfl
        intro j _
        rw [show ((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ) = ((x i - x j : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
      rw [hden]
      have hdenpos : 0 < ∏ j ∈ (Finset.univ.erase i), |x i - x j| := by
        apply Finset.prod_pos
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hxne : x i ≠ x j := fun h => hji (hxmono.injective h.symm)
        rw [abs_pos]
        exact sub_ne_zero.mpr hxne
      exact div_le_div_of_nonneg_right hnum hdenpos.le
    have hstep2 : ∑ i : Fin (N+1),
        ‖P.eval ((x i : ℝ) : ℂ) /
          ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖ ≤
        δ * ∑ i : Fin (N+1), (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) := by
      have hthis : ∀ i : Fin (N+1),
          ‖P.eval ((x i : ℝ) : ℂ) /
            ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖ ≤
          δ * (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) := by
        intro i
        calc ‖P.eval ((x i : ℝ) : ℂ) /
                ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖
            ≤ δ / ∏ j ∈ (Finset.univ.erase i), |x i - x j| := hterm i
          _ = δ * (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) := by rw [div_eq_mul_one_div]
      calc ∑ i : Fin (N+1), ‖P.eval ((x i : ℝ) : ℂ) /
              ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖
          ≤ ∑ i : Fin (N+1), δ * (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) :=
            Finset.sum_le_sum (fun i _ => hthis i)
        _ = δ * ∑ i : Fin (N+1), (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) := by
            rw [Finset.mul_sum]
    have hprod := fun i => Commons.Analysis.Complex.Cartan.prod_fin_erase_abs_sub_ge N x Δ hΔpos hxgap i
    have hstep3 : ∑ i : Fin (N+1), (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) ≤
        (Δ^N)⁻¹ * (2^N / ((Nat.factorial N : ℕ) : ℝ)) := by
      have h1 : ∑ i : Fin (N+1), (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) ≤
          ∑ i : Fin (N+1), (1 / (Δ^N * ((Nat.factorial i.val : ℕ) : ℝ) *
            ((Nat.factorial (N - i.val) : ℕ) : ℝ))) := by
        apply Finset.sum_le_sum
        intro i _
        apply one_div_le_one_div_of_le
        · positivity
        · exact hprod i
      have h2 : ∑ i : Fin (N+1), (1 / (Δ^N * ((Nat.factorial i.val : ℕ) : ℝ) *
            ((Nat.factorial (N - i.val) : ℕ) : ℝ)))
          = (Δ^N)⁻¹ * ∑ i : Fin (N+1), (1 / (((Nat.factorial i.val : ℕ) : ℝ) *
            ((Nat.factorial (N - i.val) : ℕ) : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        field_simp
      rw [h2] at h1
      refine le_trans h1 (le_of_eq ?_)
      rw [Commons.Analysis.Complex.Cartan.sum_inv_factorial_eq_two_pow_div]
    have hmain : (1:ℝ) ≤ δ * ((Δ^N)⁻¹ * (2^N / ((Nat.factorial N : ℕ) : ℝ))) := by
      calc (1:ℝ) ≤ ∑ i : Fin (N+1), ‖P.eval ((x i : ℝ) : ℂ) /
              ∏ j ∈ (Finset.univ.erase i), (((x i : ℝ) : ℂ) - ((x j : ℝ) : ℂ))‖ := hstep1
        _ ≤ δ * ∑ i : Fin (N+1), (1 / ∏ j ∈ (Finset.univ.erase i), |x i - x j|) := hstep2
        _ ≤ δ * ((Δ^N)⁻¹ * (2^N / ((Nat.factorial N : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hstep3 hδ.le
    -- contradiction
    have hDpow : Δ^N = 15^N * δ / (N:ℝ)^N := by
      rw [hΔdef, div_pow, mul_pow]
      have hrp : (δ ^ ((1:ℝ)/N))^N = δ := by
        rw [show (1:ℝ)/N = (N:ℝ)⁻¹ from by rw [one_div]]
        exact Real.rpow_inv_natCast_pow hδ.le (by omega)
      rw [hrp]
    have hval : δ * ((Δ^N)⁻¹ * (2^N / ((Nat.factorial N : ℕ) : ℝ)))
        = (2*(N:ℝ)/15)^N / ((Nat.factorial N : ℕ) : ℝ) := by
      rw [hDpow]
      have hNd : ((N:ℝ)) ≠ 0 := by positivity
      have hδne : δ ≠ 0 := hδ.ne'
      have hNfac : ((Nat.factorial N : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      rw [div_pow, mul_pow]
      field_simp
    rw [hval] at hmain
    have hlt1 : (2*(N:ℝ)/15)^N / ((Nat.factorial N : ℕ) : ℝ) < 1 := by
      rw [div_lt_one (by positivity)]
      have hsplit2 : 2*(N:ℝ)/15 = ((N:ℝ)/4) * ((8:ℝ)/15) := by ring
      rw [hsplit2, mul_pow]
      have hN4pos : (0:ℝ) < ((N:ℝ)/4)^N := by
        apply pow_pos; positivity
      have h8lt : ((8:ℝ)/15)^N < 1 := by
        apply pow_lt_one₀ (by norm_num) (by norm_num)
        omega
      have hfac := Commons.Analysis.Complex.Cartan.factorial_ge_div_pow N
      nlinarith [hfac, h8lt, hN4pos,
        show (0:ℝ) ≤ ((Nat.factorial N : ℕ) : ℝ) by positivity]
    linarith [hmain, hlt1]
  exact hbound


/-- Arithmetic core: with `N` the Blaschke degree and `(N : ℝ) * log (4/3) ≤ log M`, the
`(v/100) ^ (10 log M)` factor is dominated by `(v/240)^N`. -/
theorem ratio_arith (v M : ℝ) (hv0 : 0 < v) (hv2 : v ≤ 2) (hM1 : 1 ≤ M)
    (N : ℕ) (hN : (N:ℝ) * Real.log (4/3) ≤ Real.log M) :
    (v/100) ^ (10 * Real.log M) ≤ (v/240)^N := by
  have hLnn : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hK : (1:ℝ)/4 ≤ Real.log (4/3) := by
    have h1 : Real.log (3/4) ≤ (3:ℝ)/4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : Real.log (4/3) = -Real.log (3/4) := by
      rw [show (4:ℝ)/3 = ((3:ℝ)/4)⁻¹ by norm_num, Real.log_inv]
    rw [h2]; linarith
  have hKpos : 0 < Real.log (4/3) := by linarith
  have hℓ : Real.log (v/100) ≤ -(2/3) := by
    have h1 : v/100 ≤ 2/100 := by linarith
    have h2 : Real.log (v/100) ≤ Real.log ((2:ℝ)/100) := Real.log_le_log (by positivity) h1
    have h3 : Real.log ((2:ℝ)/100) = -Real.log 50 := by
      rw [show (2:ℝ)/100 = (50:ℝ)⁻¹ by norm_num, Real.log_inv]
    have h4 : (1:ℝ) ≤ Real.log 50 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 50)]
      linarith [Real.exp_one_lt_three]
    rw [h3] at h2; linarith
  have hc : Real.log (12/5) ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 12/5)]
    linarith [Real.exp_one_gt_d9]
  have hNle : (N:ℝ) ≤ Real.log M / Real.log (4/3) := by
    rw [le_div_iff₀ hKpos]; linarith [hN]
  have hlmc : Real.log (v/240) = Real.log (v/100) - Real.log (12/5) := by
    rw [show v/240 = (v/100)/(12/5) by field_simp; ring, Real.log_div (by positivity) (by norm_num)]
  have hnum : (10:ℝ) * Real.log (v/100) ≤ (Real.log (v/100) - Real.log (12/5)) / Real.log (4/3) := by
    rw [le_div_iff₀ hKpos]
    have h1 : Real.log (v/100) * (10 * Real.log (4/3) - 1) ≤ -Real.log (12/5) := by
      have hK2 : (3:ℝ)/2 ≤ 10 * Real.log (4/3) - 1 := by linarith [hK]
      have hpos : 0 ≤ 10 * Real.log (4/3) - 1 := by linarith [hK]
      have hmul : Real.log (v/100) * (10 * Real.log (4/3) - 1)
          ≤ (-(2/3)) * (10 * Real.log (4/3) - 1) := mul_le_mul_of_nonneg_right hℓ hpos
      nlinarith [hmul, hK2, hc]
    nlinarith [h1]
  have hstep2 : 10 * Real.log M * Real.log (v/100)
      ≤ (Real.log M / Real.log (4/3)) * (Real.log (v/100) - Real.log (12/5)) := by
    have he : (Real.log M / Real.log (4/3)) * (Real.log (v/100) - Real.log (12/5))
        = Real.log M * ((Real.log (v/100) - Real.log (12/5)) / Real.log (4/3)) := by ring
    rw [he]
    calc 10 * Real.log M * Real.log (v/100) = Real.log M * (10 * Real.log (v/100)) := by ring
      _ ≤ Real.log M * ((Real.log (v/100) - Real.log (12/5)) / Real.log (4/3)) :=
          mul_le_mul_of_nonneg_left hnum hLnn
  have hstep1 : (Real.log M / Real.log (4/3)) * (Real.log (v/100) - Real.log (12/5))
      ≤ (N:ℝ) * (Real.log (v/100) - Real.log (12/5)) := by
    have hc0 : 0 ≤ Real.log (12/5) := Real.log_nonneg (by norm_num)
    have hnonpos : Real.log (v/100) - Real.log (12/5) ≤ 0 := by linarith [hℓ, hc0]
    exact mul_le_mul_of_nonpos_right hNle hnonpos
  have hApos : 0 < (v/100) ^ (10 * Real.log M) := Real.rpow_pos_of_pos (by positivity) _
  have hBpos : 0 < (v/240)^N := by positivity
  rw [← Real.log_le_log_iff hApos hBpos]
  rw [Real.log_rpow (by positivity : (0:ℝ) < v/100)]
  rw [Real.log_pow, hlmc]
  have hkey : 10 * Real.log M * Real.log (v/100)
      ≤ (N:ℝ) * (Real.log (v/100) - Real.log (12/5)) := le_trans hstep2 hstep1
  linarith [hkey]

/-- **Kovrijkine ratio lemma.**  An analytic function on the ball of radius `5`, bounded by `M` on
the ball of radius `4` and with `‖φ 0‖ ≥ 1`, cannot be too small on a positive-measure subset `E` of
`[-1,1]`: on the whole interval it is controlled by `(100/|E|)^{10 log M} M³ sup_E ‖φ‖`. -/
theorem kovrijkine_ratio (φ : ℂ → ℂ) (M : ℝ) (hM : 1 ≤ M)
    (hφ : AnalyticOnNhd ℂ φ (closedBall 0 5))
    (hbound : ∀ z ∈ closedBall (0:ℂ) 4, ‖φ z‖ ≤ M)
    (h0 : 1 ≤ ‖φ 0‖)
    (E : Set ℝ) (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-1) 1) (hEpos : 0 < (volume E).toReal) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖φ x‖ ≤ (100 / (volume E).toReal) ^ (10 * Real.log M) * M ^ 3 *
      sSup ((fun t : ℝ => ‖φ t‖) '' E) := by
  intro x hx
  have hx4 : (x:ℂ) ∈ closedBall (0:ℂ) 4 := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    have : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    linarith
  have hφx : ‖φ x‖ ≤ M := hbound _ hx4
  have hφ' : AnalyticOnNhd ℂ φ (Metric.ball 0 5) := hφ.mono Metric.ball_subset_closedBall
  have hbound' : ∀ z : ℂ, z ∈ Metric.ball 0 4 → ‖φ z‖ ≤ M :=
    fun z hz => hbound z (Metric.ball_subset_closedBall hz)
  obtain ⟨N, b, h, P, hPmonic, hPdeg, _hb_an, _hh_an, hh_ne, hφ_eq_bh, _hb_circ, hb_le1,
    hpoly, hhM, hh0, hcount⟩ :=
    kovrijkine_blaschke_core_Icc φ M hφ' hbound' hM h0
  set v : ℝ := (volume E).toReal with hvdef
  have hvpos : 0 < v := hEpos
  have hv2 : v ≤ 2 := by
    rw [hvdef]
    have hIcc : volume (Set.Icc (-1:ℝ) 1) = (2 : ℝ≥0∞) := by
      rw [Real.volume_Icc]; norm_num
    have hle : volume E ≤ (2 : ℝ≥0∞) := hIcc ▸ measure_mono hEsub
    exact ENNReal.toReal_mono (by norm_num) hle
  have hharn : ∀ t : ℝ, t ∈ Set.Icc (-1:ℝ) 1 → (M^2)⁻¹ ≤ ‖h t‖ :=
    harnack_lower_bound_zeroFree h M hM _hh_an hh_ne hhM hh0
  have hBdd : BddAbove ((fun t : ℝ => ‖φ t‖) '' E) := by
    refine ⟨M, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    refine hbound (t:ℂ) ?_
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hEsub ht
    have : |t| ≤ 1 := by rw [abs_le]; exact ⟨h1.1, h1.2⟩
    linarith
  set S : ℝ := sSup ((fun t : ℝ => ‖φ t‖) '' E) with hSdef
  have hSbound : (M^2)⁻¹ * (v/240)^N ≤ S := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · -- N = 0
      obtain ⟨t, htE⟩ : E.Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro hEe
        have h0 : v = 0 := by rw [hvdef, hEe]; simp
        exact absurd h0 (ne_of_gt hEpos)
      have htIcc := hEsub htE
      have ht3 : (t:ℂ) ∈ Metric.ball 0 3 := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
        have : |t| ≤ 1 := by rw [abs_le]; exact ⟨htIcc.1, htIcc.2⟩
        linarith
      have hP1 : P = 1 := by
        have h := Polynomial.eq_C_of_natDegree_eq_zero (hPdeg.trans hN0)
        have hc0 : P.coeff 0 = 1 := by
          have := hPmonic.coeff_natDegree
          rw [hPdeg, hN0] at this
          exact this
        rw [h, hc0]; simp
      have hbt1 : (1:ℝ) ≤ ‖b (t:ℂ)‖ := by
        have h1 := hpoly t htIcc
        rw [hP1, hN0] at h1
        simpa using h1
      have hbt2 : ‖b (t:ℂ)‖ ≤ 1 := hb_le1 (t:ℂ) ht3
      have hbt : ‖b (t:ℂ)‖ = 1 := le_antisymm hbt2 hbt1
      have hle := le_csSup hBdd (show ‖φ t‖ ∈ ((fun s : ℝ => ‖φ s‖) '' E) from ⟨t, htE, rfl⟩)
      have hprod : ‖φ t‖ = ‖b (t:ℂ)‖ * ‖h t‖ := by
        rw [hφ_eq_bh (t:ℂ) ht3, norm_mul]
      rw [hprod, hbt, one_mul] at hle
      have ht' := hharn t htIcc
      rw [hN0, pow_zero, mul_one] at *
      linarith [hle, ht']
    · -- N ≥ 1
      have hN1 : 1 ≤ N := hNpos
      have hfind : ∃ t ∈ E, (v/240)^N < ‖b (t:ℂ)‖ := by
        by_contra hcon
        push_neg at hcon
        have hPbd : ∀ t ∈ E, ‖P.eval (t:ℂ)‖ ≤ (4:ℝ)^N * (v/240)^N := by
          intro t ht
          have h1 := hpoly t (hEsub ht)
          have h2 : (4:ℝ)^N * ‖b (t:ℂ)‖ ≤ (4:ℝ)^N * (v/240)^N :=
            mul_le_mul_of_nonneg_left (hcon t ht) (by positivity)
          linarith
        have hlev := monic_level_set_Icc_volume_le N hN1 P hPmonic hPdeg
          ((4:ℝ)^N * (v/240)^N) (by positivity) E hE hEsub hPbd
        rw [← hvdef] at hlev
        rw [← mul_pow] at hlev
        have hroot : ((4 * (v/240)) ^ N : ℝ) ^ ((1:ℝ)/N) = 4 * (v/240) := by
          rw [← Real.rpow_natCast (4 * (v/240)) N, ← Real.rpow_mul (by positivity)]
          have h1 : ((N:ℝ) * ((1:ℝ)/N)) = 1 := by field_simp
          rw [h1, Real.rpow_one]
        rw [hroot] at hlev
        have h2 : (30:ℝ) * (4 * (v/240)) = v/2 := by ring
        rw [h2] at hlev
        linarith [hvpos]
      obtain ⟨t, htE, hbτ⟩ := hfind
      have htIcc := hEsub htE
      have ht3 : (t:ℂ) ∈ Metric.ball 0 3 := by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
        have : |t| ≤ 1 := by rw [abs_le]; exact ⟨htIcc.1, htIcc.2⟩
        linarith
      have hle := le_csSup hBdd (show ‖φ t‖ ∈ ((fun s : ℝ => ‖φ s‖) '' E) from ⟨t, htE, rfl⟩)
      have hprod : ‖φ t‖ = ‖b (t:ℂ)‖ * ‖h t‖ := by
        rw [hφ_eq_bh (t:ℂ) ht3, norm_mul]
      rw [hprod] at hle
      have h1 : (v/240)^N * (M^2)⁻¹ ≤ ‖b (t:ℂ)‖ * ‖h t‖ :=
        mul_le_mul hbτ.le (hharn t htIcc) (by positivity) (by positivity)
      linarith [hle, h1]
  have hgoal : (1:ℝ) ≤ (100/v) ^ (10 * Real.log M) * (v/240)^N := by
    have hAB : (v/100) ^ (10 * Real.log M) ≤ (v/240)^N := ratio_arith v M hvpos hv2 hM N hcount
    have hApos : 0 < (v/100) ^ (10 * Real.log M) := Real.rpow_pos_of_pos (by positivity) _
    have hInv : (100/v) ^ (10 * Real.log M) = ((v/100) ^ (10 * Real.log M))⁻¹ := by
      rw [show (100:ℝ)/v = (v/100)⁻¹ by field_simp]
      exact Real.inv_rpow (by positivity) (10 * Real.log M)
    rw [hInv]
    have hdiv : ((v/100) ^ (10 * Real.log M))⁻¹ * (v/240)^N
          = (v/240)^N / ((v/100) ^ (10 * Real.log M)) := by
      rw [div_eq_mul_inv]; ring
    rw [hdiv, le_div_iff₀ hApos]
    linarith [hAB]
  have hfinal : M ≤ (100/v) ^ (10 * Real.log M) * M^3 * S := by
    have hstep : (100/v) ^ (10 * Real.log M) * M^3 * ((M^2)⁻¹ * (v/240)^N)
        ≤ (100/v) ^ (10 * Real.log M) * M^3 * S :=
      mul_le_mul_of_nonneg_left hSbound (by positivity)
    have hMne : M ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hM)
    have heq : (100/v) ^ (10 * Real.log M) * M^3 * ((M^2)⁻¹ * (v/240)^N)
        = M * ((100/v) ^ (10 * Real.log M) * (v/240)^N) := by
      field_simp
    rw [heq] at hstep
    have hMle : M ≤ M * ((100/v) ^ (10 * Real.log M) * (v/240)^N) := by
      nlinarith [hgoal, hM]
    linarith [hstep, hMle]
  calc ‖φ x‖ ≤ M := hφx
    _ ≤ (100/v) ^ (10 * Real.log M) * M^3 * S := hfinal
    _ = (100 / (volume E).toReal) ^ (10 * Real.log M) * M^3 * sSup ((fun t : ℝ => ‖φ t‖) '' E) := by
        rw [← hvdef, ← hSdef]


end Commons.Analysis.Complex
