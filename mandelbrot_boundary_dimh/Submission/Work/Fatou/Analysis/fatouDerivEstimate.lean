import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Analysis.exists_deriv_le_of_value_gap
import Submission.Work.Fatou.Analysis.derivBounds_of_nearTranslation
import Submission.Work.Fatou.Analysis.norm_sub_sub_mul_deriv_le

/-!
# Shishikura Lemma A.2.4(i): `Φ' ≈ 1/v`

Proof of `MandelDim.FatouDerivEstimate`.  The chain of estimates is

1. Koebe (weak Koebe + Landau): `‖Φ' z‖ ≤ 4CK/3` on `ball c (R-2)`
   (any univalent `Φ` on `ball c R` with `Φ (z + v z) = Φ z + 1`, `‖v z‖ > 3/4`).
2. Cauchy: `‖Φ''‖ ≤ 8CK/(3R)` on `ball c (R/2 - 7/2)`.
3. Second order Taylor + the Abel relation: `‖1 - v z * Φ' z‖ ≤ 25CK/(6R)` on `ball c (R/2 - 5)`.
4. Cauchy again: `‖(1 - Φ'·v)'‖ ≤ 50CK/(3R²)` on `ball c 4`.
5. Cauchy on `v`: `‖v'‖ ≤ CV/R`, `‖v''‖ ≤ CV/R²`, `‖v'z - v'c‖ ≤ CV/R²` on `ball c 4`.
6. Differentiating `Φ' = (1 - (1 - Φ'v))/v` gives `‖Φ''‖ ≤ K(‖v' c‖ + 1/R²)` on `ball c 4`.
7. Second order Taylor at `c` + the Abel relation at `c`: `‖1 - v c * Φ' c‖ ≤ (25/16)K(‖v'c‖+1/R²)`,
   and dividing by `‖v c‖ ≥ 3/4` gives the two claimed bounds.
-/

namespace Work.Fatou.Analysis

open Metric Set

noncomputable section

/-- Cauchy's estimate: a bound on an open ball gives a bound on the derivative at the centre. -/
private lemma norm_deriv_le_of_ball_bound {f : ℂ → ℂ} {c : ℂ} {R r M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hd : DifferentiableOn ℂ f (ball c R))
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ M) : ‖deriv f c‖ ≤ M / r := by
  have hd' : DiffContOnCl ℂ f (ball c r) :=
    hd.diffContOnCl_ball (fun z hz => Metric.closedBall_subset_ball hrR hz)
  have hs : ∀ z ∈ sphere c r, ‖f z‖ ≤ M := fun z hz =>
    hb z (Metric.closedBall_subset_ball hrR (Metric.sphere_subset_closedBall hz))
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd' hs

/-- The two bounds on `‖v z‖` implied by `‖v z - 1‖ < 1/4`. -/
private lemma norm_v_bounds {v : ℂ → ℂ} {c z : ℂ} {R : ℝ} (hz : z ∈ ball c R)
    (hv : ∀ z ∈ ball c R, ‖v z - 1‖ < 1/4) :
    ‖v z‖ < 5 / 4 ∧ 3 / 4 < ‖v z‖ := by
  have h := hv z hz
  have h1 : ‖v z‖ ≤ ‖v z - 1‖ + ‖(1 : ℂ)‖ := by
    calc ‖v z‖ = ‖(v z - 1) + 1‖ := by ring_nf
      _ ≤ ‖v z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
  rw [norm_one] at h1
  have h2 : (1 : ℝ) ≤ ‖v z‖ + ‖v z - 1‖ := by
    have hh := norm_sub_le (v z) (v z - 1)
    have h3 : v z - (v z - 1) = (1 : ℂ) := by ring
    rw [h3, norm_one] at hh
    exact hh
  constructor <;> linarith

/-- The constant controlling `Φ''` near the centre: `(16/9)·(125CK/6 + (5CK/3)(CV+1))`. -/
private def K2 (CK CV : ℝ) : ℝ := (16 / 9) * ((125 * CK) / 6 + (5 * CK / 3) * (CV + 1))

private lemma K2_ge (CK CV : ℝ) (hCK : 0 < CK) (hCV : 0 < CV) :
    (16 / 9) * (5 * CK / 3) ≤ K2 CK CV ∧
    (16 / 9) * ((125 * CK) / 6 + (5 * CK / 3) * CV) ≤ K2 CK CV ∧ 0 < K2 CK CV := by
  have h1 : (0:ℝ) < (125 * CK) / 6 := by nlinarith
  have h2 : (0:ℝ) ≤ (5 * CK / 3) * CV := by nlinarith
  have h3 : (0:ℝ) ≤ (5 * CK / 3) * 1 := by nlinarith
  simp only [K2]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · positivity

/-- The main chain of estimates.  `hKoebe`, `hvB`, `hTaylor` are the three external inputs. -/
private theorem main_estimate
    {CK CV : ℝ} (hCK : 0 < CK) (hCV : 0 < CV)
    (hKoebe : ∀ (Φ : ℂ → ℂ) (z a : ℂ) (ρ : ℝ), 0 < ρ →
      (∀ w ∈ Metric.ball z ρ, AnalyticAt ℂ Φ w) → Set.InjOn Φ (Metric.ball z ρ) →
      a ∈ Metric.ball z ρ → Φ a = Φ z + 1 → ‖deriv Φ z‖ ≤ CK / ‖a - z‖)
    (hvB : ∀ (v : ℂ → ℂ) (c : ℂ) (R : ℝ), 16 ≤ R →
      (∀ z ∈ Metric.ball c R, AnalyticAt ℂ v z) →
      (∀ z ∈ Metric.ball c R, ‖v z - 1‖ < 1/4) →
      (∀ z ∈ Metric.ball c (R/2), ‖deriv v z‖ ≤ CV / R) ∧
      (∀ z ∈ Metric.ball c (R/4), ‖deriv (deriv v) z‖ ≤ CV / R^2) ∧
      (∀ z ∈ Metric.ball c 4, ‖deriv v z - deriv v c‖ ≤ CV / R^2) ∧
      (∀ z ∈ Metric.ball c R, ‖v z‖ ≤ 5/4))
    (hTaylor : ∀ {f : ℂ → ℂ} {z a : ℂ} {M : ℝ},
      (∀ w ∈ segment ℝ z (z + a), AnalyticAt ℂ f w) →
      (∀ w ∈ segment ℝ z (z + a), ‖deriv (deriv f) w‖ ≤ M) →
      ‖f (z + a) - f z - a * deriv f z‖ ≤ M * ‖a‖ ^ 2)
    (Φ v : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 100 ≤ R)
    (hΦd : DifferentiableOn ℂ Φ (Metric.ball c R)) (hΦi : Set.InjOn Φ (Metric.ball c R))
    (hvd : DifferentiableOn ℂ v (Metric.ball c R))
    (hv1 : ∀ z ∈ Metric.ball c R, ‖v z - 1‖ < 1/4)
    (hAbel : ∀ z ∈ Metric.ball c R, z + v z ∈ Metric.ball c R → Φ (z + v z) = Φ z + 1) :
    ‖deriv Φ c - 1 / v c‖ ≤ ((25 / 12) * K2 CK CV + 1) * (1 / R ^ 2 + ‖deriv v c‖) ∧
    ‖deriv Φ c - 1 / v c‖ ≤ ((25 / 12) * K2 CK CV * (CV + 1) + 1) / R := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hR16 : (16 : ℝ) ≤ R := by linarith
  have hΦa : ∀ w ∈ ball c R, AnalyticAt ℂ Φ w :=
    fun w hw => hΦd.analyticAt (isOpen_ball.mem_nhds hw)
  have hva : ∀ w ∈ ball c R, AnalyticAt ℂ v w :=
    fun w hw => hvd.analyticAt (isOpen_ball.mem_nhds hw)
  -- ## Step 1: Koebe upper bound for `Φ'` on `ball c (R-2)`
  have hPhi' : ∀ z ∈ ball c (R - 2), ‖deriv Φ z‖ ≤ 4 * CK / 3 := by
    intro z hz
    have hzR : z ∈ ball c R := Metric.ball_subset_ball (by linarith) hz
    have hsub : ball z (3/2) ⊆ ball c R := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
      have h3 : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
        calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
          _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
      have h4 : ‖z - c‖ < R - 2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
      linarith
    obtain ⟨hvz_lt, _⟩ := norm_v_bounds hzR hv1
    have ha_mem : z + v z ∈ ball z (3/2) := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h4 : z + v z - z = v z := by ring
      rw [h4]; linarith
    have hAb : Φ (z + v z) = Φ z + 1 := hAbel z hzR (hsub ha_mem)
    have hk := hKoebe Φ z (z + v z) (3/2) (by norm_num)
      (fun w hw => hΦa w (hsub hw)) (hΦi.mono hsub) ha_mem hAb
    have h5 : (z + v z) - z = v z := by ring
    rw [h5] at hk
    have h6 : 3/4 ≤ ‖v z‖ := le_of_lt (norm_v_bounds hzR hv1).2
    calc ‖deriv Φ z‖ ≤ CK / ‖v z‖ := hk
      _ ≤ CK / (3/4) := div_le_div_of_nonneg_left hCK.le (by norm_num) h6
      _ = 4 * CK / 3 := by ring
  -- ## Step 2: Cauchy bound for `Φ''`
  have hPhi'' : ∀ z ∈ ball c (R/2 - 7/2), ‖deriv (deriv Φ) z‖ ≤ 8 * CK / (3 * R) := by
    intro z hz
    have hsub : closedBall z (R/2) ⊆ ball c (R - 2) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      rw [Metric.mem_ball, dist_eq_norm]
      have h3 : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
        calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
          _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
      have h4 : ‖z - c‖ < R/2 - 7/2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
      linarith
    have hd' : DiffContOnCl ℂ (deriv Φ) (ball z (R/2)) :=
      ((hΦd.deriv isOpen_ball).mono (Metric.ball_subset_ball (by linarith))).diffContOnCl_ball hsub
    have hs : ∀ w ∈ sphere z (R/2), ‖deriv Φ w‖ ≤ 4 * CK / 3 := fun w hw =>
      hPhi' w (hsub (Metric.sphere_subset_closedBall hw))
    have hk := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := deriv Φ)
      (c := z) (R := R/2) (C := 4 * CK / 3) (by linarith) hd' hs
    calc ‖deriv (deriv Φ) z‖ ≤ (4 * CK / 3) / (R/2) := hk
      _ = 8 * CK / (3 * R) := by field_simp; ring
  -- ## Step 3: the Abel relation gives `‖1 - v z * Φ' z‖ = O(1/R)` on `ball c (R/2-5)`
  set h : ℂ → ℂ := fun w => 1 - deriv Φ w * v w with hh
  have hhd : DifferentiableOn ℂ h (ball c R) := by
    rw [hh]
    exact (differentiableOn_const 1).sub ((hΦd.deriv isOpen_ball).mul hvd)
  have hh_bound : ∀ z ∈ ball c (R/2 - 5), ‖h z‖ ≤ 25 * CK / (6 * R) := by
    intro z hz
    have hzR : z ∈ ball c R := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h4 : ‖z - c‖ < R/2 - 5 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
      linarith
    obtain ⟨hvz_lt, hvz_gt⟩ := norm_v_bounds hzR hv1
    have hz_in : z ∈ ball c (R/2 - 7/2) := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h4 : ‖z - c‖ < R/2 - 5 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
      linarith
    have hzv_in : z + v z ∈ ball c (R/2 - 7/2) := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h3 : ‖z + v z - c‖ ≤ ‖z - c‖ + ‖v z‖ := by
        calc ‖z + v z - c‖ = ‖(z - c) + v z‖ := by ring_nf
          _ ≤ ‖z - c‖ + ‖v z‖ := norm_add_le _ _
      have h4 : ‖z - c‖ < R/2 - 5 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
      linarith
    have hseg : segment ℝ z (z + v z) ⊆ ball c (R/2 - 7/2) :=
      (convex_ball c (R/2 - 7/2)).segment_subset hz_in hzv_in
    have hT := hTaylor (f := Φ) (z := z) (a := v z) (M := 8 * CK / (3 * R))
      (fun w hw => hΦa w (Metric.ball_subset_ball (by linarith) (hseg hw)))
      (fun w hw => hPhi'' w (hseg hw))
    have hAb : Φ (z + v z) = Φ z + 1 :=
      hAbel z hzR (Metric.ball_subset_ball (by linarith) hzv_in)
    have hzval : h z = 1 - deriv Φ z * v z := by rw [hh]
    rw [hzval]
    have hsplit : 1 - deriv Φ z * v z = (Φ (z + v z) - Φ z) - v z * deriv Φ z := by
      rw [hAb]; ring
    rw [hsplit]
    refine le_trans hT ?_
    have hsq : ‖v z‖ ^ 2 ≤ 25/16 := by nlinarith [hvz_lt, norm_nonneg (v z)]
    calc (8 * CK / (3 * R)) * ‖v z‖ ^ 2 ≤ (8 * CK / (3 * R)) * (25/16) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 25 * CK / (6 * R) := by ring
  -- ## Step 4: Cauchy bound for `deriv h` on `ball c 4`
  have hh'_bound : ∀ z ∈ ball c 4, ‖deriv h z‖ ≤ 50 * CK / (3 * R^2) := by
    intro z hz
    have hsub : closedBall z (R/2 - 10) ⊆ ball c (R/2 - 5) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      rw [Metric.mem_ball, dist_eq_norm]
      have h3 : ‖w - c‖ ≤ ‖w - z‖ + ‖z - c‖ := by
        calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
          _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
      have h4 : ‖z - c‖ < 4 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
      linarith
    have hsubR : closedBall z (R/2 - 10) ⊆ ball c R :=
      fun w hw => Metric.ball_subset_ball (by linarith) (hsub hw)
    have hd' : DiffContOnCl ℂ h (ball z (R/2 - 10)) := hhd.diffContOnCl_ball hsubR
    have hs : ∀ w ∈ sphere z (R/2 - 10), ‖h w‖ ≤ 25 * CK / (6 * R) := fun w hw =>
      hh_bound w (hsub (Metric.sphere_subset_closedBall hw))
    have hk := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := h) (c := z)
      (R := R/2 - 10) (C := 25 * CK / (6 * R)) (by linarith) hd' hs
    have hρ : R/4 ≤ R/2 - 10 := by linarith
    calc ‖deriv h z‖ ≤ (25 * CK / (6 * R)) / (R/2 - 10) := hk
      _ ≤ (25 * CK / (6 * R)) / (R/4) :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) hρ
      _ = 50 * CK / (3 * R^2) := by field_simp; ring
  -- ## Step 5: the bounds on `v` and its derivatives
  obtain ⟨hvb1, hvb2, hvb3, hvb4⟩ := hvB v c R hR16 hva hv1
  -- ## Step 6: `Φ''` near the centre
  have hPhi2c : ∀ z ∈ ball c 4, ‖deriv (deriv Φ) z‖ ≤ K2 CK CV * (‖deriv v c‖ + 1 / R^2) := by
    intro z hz
    have hzR : z ∈ ball c R := Metric.ball_subset_ball (by linarith) hz
    obtain ⟨hvz_lt, hvz_gt⟩ := norm_v_bounds hzR hv1
    have hvw9 : 9/16 ≤ ‖v z‖ ^ 2 := by nlinarith [hvz_gt, norm_nonneg (v z)]
    have hvz_ne : v z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hvz_gt
      norm_num at hvz_gt
    have hcongr : (fun w => (1 - h w) / v w) =ᶠ[nhds z] deriv Φ := by
      filter_upwards [isOpen_ball.mem_nhds hzR] with w hw
      have hwne : v w ≠ 0 := by
        intro h0
        have hb := (norm_v_bounds hw hv1).2
        rw [h0, norm_zero] at hb
        norm_num at hb
      rw [hh]
      field_simp
      ring
    have hh_at : HasDerivAt h (deriv h z) z :=
      (hhd.differentiableAt (isOpen_ball.mem_nhds hzR)).hasDerivAt
    have hd1 : HasDerivAt (fun w => 1 - h w) (-(deriv h z)) z := hh_at.const_sub 1
    have hd2 : HasDerivAt v (deriv v z) z :=
      (hvd.differentiableAt (isOpen_ball.mem_nhds hzR)).hasDerivAt
    have hd3 : HasDerivAt (fun w => (1 - h w) / v w)
        ((-(deriv h z) * v z - (1 - h z) * deriv v z) / v z ^ 2) z := hd1.div hd2 hvz_ne
    have hderiv_eq : deriv (deriv Φ) z
        = ((-(deriv h z) * v z - (1 - h z) * deriv v z) / v z ^ 2) :=
      hcongr.deriv_eq.symm.trans hd3.deriv
    -- the pieces
    have h1 : ‖1 - h z‖ ≤ 5 * CK / 3 := by
      have hzeq : 1 - h z = deriv Φ z * v z := by rw [hh]; ring
      rw [hzeq, norm_mul]
      have hPz : ‖deriv Φ z‖ ≤ 4 * CK / 3 :=
        hPhi' z (Metric.ball_subset_ball (by linarith) hz)
      calc ‖deriv Φ z‖ * ‖v z‖ ≤ (4 * CK / 3) * (5 / 4) :=
            mul_le_mul hPz (hvb4 z hzR) (norm_nonneg _) (by positivity)
        _ = 5 * CK / 3 := by ring
    have h2 : ‖deriv h z‖ ≤ 50 * CK / (3 * R^2) := hh'_bound z hz
    have h3 : ‖deriv v z‖ ≤ ‖deriv v c‖ + CV / R^2 := by
      have h4 : ‖deriv v z - deriv v c‖ ≤ CV / R^2 := hvb3 z hz
      have h5 : ‖deriv v z‖ ≤ ‖deriv v c‖ + ‖deriv v z - deriv v c‖ := by
        calc ‖deriv v z‖ = ‖deriv v c + (deriv v z - deriv v c)‖ := by ring_nf
          _ ≤ ‖deriv v c‖ + ‖deriv v z - deriv v c‖ := norm_add_le _ _
      linarith
    -- abbreviations for the final arithmetic
    have hSnn : (0:ℝ) ≤ (125 * CK) / 6 + (5 * CK / 3) + (5 * CK / 3) * CV := by
      nlinarith [hCK, hCV]
    have ht_nn : (0:ℝ) ≤ 1 / R^2 + ‖deriv v c‖ := by
      have h5 : (0:ℝ) < 1 / R^2 := by positivity
      linarith [norm_nonneg (deriv v c)]
    have hK2S : K2 CK CV = (16/9) * ((125 * CK) / 6 + (5 * CK / 3) + (5 * CK / 3) * CV) := by
      rw [K2]; ring
    have hZ : ‖-(deriv h z) * v z - (1 - h z) * deriv v z‖
        ≤ ((125 * CK) / 6 + (5 * CK / 3) + (5 * CK / 3) * CV) * (1 / R^2 + ‖deriv v c‖) := by
      have e1 : ‖-(deriv h z) * v z‖ ≤ (50 * CK / (3 * R^2)) * (5/4) := by
        rw [norm_mul, norm_neg]
        exact mul_le_mul h2 (hvb4 z hzR) (norm_nonneg _) (by positivity)
      have e2 : ‖(1 - h z) * deriv v z‖ ≤ (5 * CK / 3) * (‖deriv v c‖ + CV / R^2) := by
        rw [norm_mul]
        exact mul_le_mul h1 h3 (norm_nonneg _) (by positivity)
      have e3 : ‖-(deriv h z) * v z - (1 - h z) * deriv v z‖
          ≤ (50 * CK / (3 * R^2)) * (5/4) + (5 * CK / 3) * (‖deriv v c‖ + CV / R^2) :=
        le_trans (norm_sub_le _ _) (add_le_add e1 e2)
      refine le_trans e3 ?_
      have h6 : (50 * CK / (3 * R^2)) * (5/4) = (125 * CK / 6) * (1 / R^2) := by
        field_simp; ring
      have h7 : (5 * CK / 3) * (‖deriv v c‖ + CV / R^2)
          = (5 * CK / 3) * CV * (1 / R^2) + (5 * CK / 3) * ‖deriv v c‖ := by
        field_simp; ring
      rw [h6, h7]
      have hA : (0:ℝ) ≤ (125 * CK) / 6 := by nlinarith [hCK]
      have hB : (0:ℝ) ≤ 5 * CK / 3 := by nlinarith [hCK]
      have hC : (0:ℝ) ≤ (5 * CK / 3) * CV := by nlinarith [hCK, hCV]
      have h8 : (0:ℝ) ≤ 1 / R^2 := by positivity
      nlinarith [hA, hB, hC, h8, norm_nonneg (deriv v c), ht_nn]
    have hSt : ((125 * CK) / 6 + (5 * CK / 3) + (5 * CK / 3) * CV) * (1 / R^2 + ‖deriv v c‖)
        ≤ K2 CK CV * (1 / R^2 + ‖deriv v c‖) * ‖v z‖ ^ 2 := by
      rw [hK2S]
      calc ((125 * CK) / 6 + (5 * CK / 3) + (5 * CK / 3) * CV) * (1 / R^2 + ‖deriv v c‖)
          = ((16/9) * ((125 * CK) / 6 + (5 * CK / 3) + (5 * CK / 3) * CV))
              * (1 / R^2 + ‖deriv v c‖) * (9/16) := by ring
        _ ≤ ((16/9) * ((125 * CK) / 6 + (5 * CK / 3) + (5 * CK / 3) * CV))
              * (1 / R^2 + ‖deriv v c‖) * ‖v z‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hvw9 (by nlinarith [hSnn, ht_nn])
    have hkey : ‖(-(deriv h z) * v z - (1 - h z) * deriv v z) / v z ^ 2‖
        ≤ K2 CK CV * (1 / R^2 + ‖deriv v c‖) := by
      rw [norm_div, norm_pow]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖v z‖ ^ 2)]
      exact le_trans hZ hSt
    calc ‖deriv (deriv Φ) z‖
        = ‖(-(deriv h z) * v z - (1 - h z) * deriv v z) / v z ^ 2‖ := by rw [hderiv_eq]
      _ ≤ K2 CK CV * (1 / R^2 + ‖deriv v c‖) := hkey
      _ = K2 CK CV * (‖deriv v c‖ + 1 / R^2) := by ring
  -- ## Step 7: the remainder at the centre
  have hcR : c ∈ ball c R := by rw [Metric.mem_ball, dist_self]; exact hRpos
  have hcR2 : c ∈ ball c (R/2) := by rw [Metric.mem_ball, dist_self]; linarith
  obtain ⟨hvc_lt, hvc_gt⟩ := norm_v_bounds hcR hv1
  have hcv_in : c + v c ∈ ball c R := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h3 : c + v c - c = v c := by ring
    rw [h3]; linarith
  have hAb_c : Φ (c + v c) = Φ c + 1 := hAbel c hcR hcv_in
  have hsegc : segment ℝ c (c + v c) ⊆ ball c 4 := by
    refine (convex_ball c 4).segment_subset ?_ ?_
    · rw [Metric.mem_ball, dist_self]; norm_num
    · rw [Metric.mem_ball, dist_eq_norm]
      have h3 : c + v c - c = v c := by ring
      rw [h3]; linarith
  have hT := hTaylor (f := Φ) (z := c) (a := v c) (M := K2 CK CV * (‖deriv v c‖ + 1/R^2))
    (fun w hw => hΦa w (Metric.ball_subset_ball (by linarith) (hsegc hw)))
    (fun w hw => hPhi2c w (hsegc hw))
  have hmain : ‖1 - deriv Φ c * v c‖ ≤ (25/16) * (K2 CK CV * (‖deriv v c‖ + 1 / R^2)) := by
    have hsplit : 1 - deriv Φ c * v c = (Φ (c + v c) - Φ c) - v c * deriv Φ c := by
      rw [hAb_c]; ring
    rw [hsplit]
    refine le_trans hT ?_
    have hsq : ‖v c‖ ^ 2 ≤ 25/16 := by nlinarith [hvc_lt, norm_nonneg (v c)]
    have hK2pos : 0 < K2 CK CV := (K2_ge CK CV hCK hCV).2.2
    have hX : 0 ≤ K2 CK CV * (‖deriv v c‖ + 1 / R^2) := by
      refine mul_nonneg hK2pos.le ?_
      have h5 : (0:ℝ) < 1 / R^2 := by positivity
      linarith [norm_nonneg (deriv v c)]
    calc (K2 CK CV * (‖deriv v c‖ + 1 / R^2)) * ‖v c‖ ^ 2
        ≤ (K2 CK CV * (‖deriv v c‖ + 1 / R^2)) * (25/16) :=
          mul_le_mul_of_nonneg_left hsq hX
      _ = (25/16) * (K2 CK CV * (‖deriv v c‖ + 1 / R^2)) := by ring
  have hvc_ne : v c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hvc_gt
    norm_num at hvc_gt
  have hvc_pos : (0:ℝ) < ‖v c‖ := by linarith
  have hfac : deriv Φ c - 1 / v c = -(1 - deriv Φ c * v c) / v c := by
    field_simp
    ring
  have hkey : ‖deriv Φ c - 1 / v c‖ ≤ (25/12) * K2 CK CV * (1 / R^2 + ‖deriv v c‖) := by
    rw [hfac, norm_div, norm_neg]
    rw [div_le_iff₀ hvc_pos]
    have hK2pos : 0 < K2 CK CV := (K2_ge CK CV hCK hCV).2.2
    have hX : 0 ≤ K2 CK CV * (1 / R^2 + ‖deriv v c‖) := by positivity
    have hstep : (25/16) * (K2 CK CV * (1 / R^2 + ‖deriv v c‖))
        ≤ ((25/12) * K2 CK CV * (1 / R^2 + ‖deriv v c‖)) * ‖v c‖ := by
      have h1 : (25/16 : ℝ) ≤ (25/12) * ‖v c‖ := by nlinarith [hvc_gt]
      calc (25/16) * (K2 CK CV * (1 / R^2 + ‖deriv v c‖))
          ≤ ((25/12) * ‖v c‖) * (K2 CK CV * (1 / R^2 + ‖deriv v c‖)) :=
            mul_le_mul_of_nonneg_right h1 hX
        _ = ((25/12) * K2 CK CV * (1 / R^2 + ‖deriv v c‖)) * ‖v c‖ := by ring
    linarith [hmain, hstep]
  -- ## Step 8: the two claimed bounds
  constructor
  · have hK2pos : 0 < K2 CK CV := (K2_ge CK CV hCK hCV).2.2
    have hnn : 0 ≤ 1 / R^2 + ‖deriv v c‖ := by
      have h5 : (0:ℝ) < 1 / R^2 := by positivity
      linarith [norm_nonneg (deriv v c)]
    calc ‖deriv Φ c - 1 / v c‖ ≤ (25/12) * K2 CK CV * (1 / R^2 + ‖deriv v c‖) := hkey
      _ ≤ ((25/12) * K2 CK CV + 1) * (1 / R^2 + ‖deriv v c‖) := by nlinarith
  · have hK2pos : 0 < K2 CK CV := (K2_ge CK CV hCK hCV).2.2
    have hvb : ‖deriv v c‖ ≤ CV / R := hvb1 c hcR2
    have hR1 : 1 ≤ R := by linarith
    have hsq : 1 / R^2 ≤ 1 / R := by
      rw [div_le_div_iff₀ (by positivity) hRpos]
      nlinarith
    have hstep : (25/12) * K2 CK CV * (1 / R^2 + ‖deriv v c‖)
        ≤ ((25/12) * K2 CK CV * (CV + 1) + 1) / R := by
      have h3 : 1 / R^2 + ‖deriv v c‖ ≤ (CV + 1) / R := by
        have h6 : (CV + 1) / R = CV / R + 1 / R := by rw [add_div]
        have h7 : CV / R ≤ (CV + 1) / R := by
          rw [h6]
          have h8 : (0:ℝ) ≤ 1 / R := by positivity
          linarith
        linarith
      have h2 : (25/12) * K2 CK CV * (1 / R^2 + ‖deriv v c‖)
          ≤ (25/12) * K2 CK CV * ((CV + 1) / R) := by
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      have h6 : (25/12) * K2 CK CV * ((CV + 1) / R) = ((25/12) * K2 CK CV * (CV + 1)) / R := by
        ring
      have h7 : ((25/12) * K2 CK CV * (CV + 1)) / R
          ≤ ((25/12) * K2 CK CV * (CV + 1) + 1) / R := by
        rw [div_le_div_iff₀ hRpos hRpos]; linarith
      linarith [h2, h6, h7]
    linarith [hkey, hstep]

theorem fatouDerivEstimate : MandelDim.FatouDerivEstimate := by
  obtain ⟨CK, hCKpos, hCK⟩ := exists_deriv_le_of_value_gap
  obtain ⟨CV, hCVpos, hCV⟩ := derivBounds_of_nearTranslation
  have hK2 : 0 < K2 CK CV := (K2_ge CK CV hCKpos hCVpos).2.2
  refine ⟨100, (25 / 12) * K2 CK CV + 1, (25 / 12) * K2 CK CV * (CV + 1) + 1,
    by norm_num, by nlinarith, by nlinarith, ?_⟩
  intro Φ v z₀ R hR hΦd hΦi hvd hv1 hAbel
  exact main_estimate hCKpos hCVpos hCK hCV norm_sub_sub_mul_deriv_le
    Φ v z₀ R hR hΦd hΦi hvd hv1 hAbel

end

end Work.Fatou.Analysis
