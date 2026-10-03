import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.FatouCH.koebeTwoSided
import Submission.Work.FatouCH.derivAbelEq
import Submission.Work.FatouCH.cauchyIteratedDerivThree
import Submission.Work.FatouCH.taylor2MeanValue
import Submission.Work.FatouCH.derivMiddleSubLe

/-!
# Shishikura Lemma A.2.4(i): the derivative estimate `Φ' ≈ 1/v`

`MandelDim.FatouDerivEstimate` (interface `Submission/Work/Interfaces/Fatou.lean`): there are
universal `R₁, C₁, C₂ > 0` such that for a univalent `Φ` on `ball z₀ R` (`R ≥ R₁`), a holomorphic
`v` with `‖v z - 1‖ < 1/4` on that ball and the Abel relation `Φ (z + v z) = Φ z + 1` whenever
`z, z + v z ∈ ball z₀ R`, one has

* `‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₁ * (1/R² + ‖deriv v z₀‖)`, and
* `‖deriv Φ z₀ - 1/v z₀‖ ≤ C₂ / R`.

The proof follows Shishikura's chain, made precise:

1. `koebeTwoSided`: on `ball z₀ (R-2)` (where the Abel relation always applies, since
   `‖v z - 1‖ < 1/4` gives `‖v z‖ < 5/4`) the derivative of `Φ` is pinched between universal
   constants: the upper bound from the weak Koebe inequality, the lower bound from the growth
   bound.
2. `derivAbelEq`: differentiating the Abel relation gives
   `deriv Φ (z + v z) * (1 + deriv v z) = deriv Φ z`.  At `z = z₀` this is what makes the mean
   slope `(deriv Φ (z₀ + w) - deriv Φ z₀)/w` (with `w = v z₀`) control `deriv Φ z₀`.
3. `cauchyIteratedDerivThree`: `‖Φ'''‖ ≤ 32 C / R²` on `ball z₀ (5/4)`.
4. `derivMiddleSubLe`: `Φ''(z₀)` differs from that mean slope by at most `(25/12) S`; combined
   with step 2 this bounds `Φ''(z₀)` by `C(|v'(z₀)| + 1/R²)`.
5. `taylor2MeanValue`: the second-order Taylor remainder at `z₀` is controlled by `S`, and the Abel
   relation `Φ(z₀ + w) - Φ z₀ = 1` turns this into `‖1 - w Φ'(z₀)‖ ≲ S + ‖Φ''(z₀)‖`.
6. Dividing by `‖w‖ > 3/4` and using Cauchy's estimate `‖v'(z₀)‖ ≤ 1/(2R)` (from `‖v - 1‖ < 1/4`
   on `ball z₀ R`) gives both claimed bounds with `C₁ = C₂ = 200 C`.
-/

namespace Work.FatouCH

open Set Metric Complex

noncomputable section

/-- Cauchy's estimate at the centre: if `‖v z - 1‖ < 1/4` on `ball z₀ R` then
`‖deriv v z₀‖ ≤ 1/(2R)`. -/
private theorem norm_deriv_le_of_bound_ball {v : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hv : DifferentiableOn ℂ v (ball z₀ R))
    (hv1 : ∀ z ∈ ball z₀ R, ‖v z - 1‖ < 1 / 4) :
    ‖deriv v z₀‖ ≤ 1 / (2 * R) := by
  have hR2pos : (0 : ℝ) < R / 2 := by linarith
  have hsub : closedBall z₀ (R / 2) ⊆ ball z₀ R := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_ball, dist_eq_norm]
    linarith
  have hd : DiffContOnCl ℂ (fun z => v z - 1) (ball z₀ (R / 2)) :=
    DifferentiableOn.diffContOnCl_ball (hv.sub_const 1) hsub
  have hsph : ∀ z ∈ sphere z₀ (R / 2), ‖v z - 1‖ ≤ 1 / 4 := by
    intro z hz
    refine le_of_lt (hv1 z ?_)
    rw [mem_sphere, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    linarith
  have hCau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z₀) (R := R / 2)
    (C := 1 / 4) (f := fun z => v z - 1) hR2pos hd hsph
  rw [deriv_sub_const] at hCau
  have hval : (1 / 4) / (R / 2) = 1 / (2 * R) := by
    rw [div_div]; ring
  linarith [hCau, hval.le, hval.ge]

theorem fatouDerivEstimate : MandelDim.FatouDerivEstimate := by
  obtain ⟨c, C, hc, hCpos, hkoebe⟩ := koebeTwoSided
  refine ⟨100, 200 * C, 200 * C, by norm_num, by positivity, by positivity, ?_⟩
  intro Φ v z₀ R hR hΦ hinj hv hv1 hAbel
  have hRpos : (0 : ℝ) < R := by linarith
  have hR16 : (16 : ℝ) ≤ R := by linarith
  have hR2inv_nn : (0 : ℝ) ≤ 1 / R ^ 2 := by positivity
  -- ### Step 0: elementary facts about `v z₀`.
  have hz₀mem : z₀ ∈ ball z₀ R := by rw [mem_ball, dist_self]; exact hRpos
  have hvz₀ : ‖v z₀ - 1‖ < 1 / 4 := hv1 z₀ hz₀mem
  have hw_lt : ‖v z₀‖ < 5 / 4 := by
    have h1 : ‖v z₀‖ ≤ ‖v z₀ - 1‖ + ‖(1 : ℂ)‖ := by
      calc ‖v z₀‖ = ‖(v z₀ - 1) + 1‖ := by ring_nf
        _ ≤ ‖v z₀ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [norm_one] at h1
    linarith
  have hw_gt : 3 / 4 < ‖v z₀‖ := by
    have h1 : (1 : ℝ) ≤ ‖v z₀‖ + ‖v z₀ - 1‖ := by
      have h := norm_sub_le (v z₀) (v z₀ - 1)
      have h2 : v z₀ - (v z₀ - 1) = (1 : ℂ) := by ring
      rw [h2, norm_one] at h
      exact h
    linarith
  have hw_nn : (0 : ℝ) < ‖v z₀‖ := by linarith
  have hzv_mem : z₀ + v z₀ ∈ ball z₀ R := by
    rw [mem_ball, dist_eq_norm]
    have h2 : z₀ + v z₀ - z₀ = v z₀ := by ring
    rw [h2]; linarith
  have hAbel_at : Φ (z₀ + v z₀) = Φ z₀ + 1 := hAbel z₀ hz₀mem hzv_mem
  -- ### Step 1: two-sided Koebe bound on a smaller ball.
  have hz₀_R2 : z₀ ∈ ball z₀ (R - 2) := by rw [mem_ball, dist_self]; linarith
  have hzv_R2 : z₀ + v z₀ ∈ ball z₀ (R - 2) := by
    rw [mem_ball, dist_eq_norm]
    have h2 : z₀ + v z₀ - z₀ = v z₀ := by ring
    rw [h2]; linarith
  have hKz : c ≤ ‖deriv Φ z₀‖ ∧ ‖deriv Φ z₀‖ ≤ C :=
    hkoebe Φ v z₀ R hΦ hinj hv hv1 hAbel z₀ hz₀_R2
  have hKzv : c ≤ ‖deriv Φ (z₀ + v z₀)‖ ∧ ‖deriv Φ (z₀ + v z₀)‖ ≤ C :=
    hkoebe Φ v z₀ R hΦ hinj hv hv1 hAbel (z₀ + v z₀) hzv_R2
  -- ### Step 2: differentiate the Abel relation at `z₀`.
  have hAbel' : deriv Φ (z₀ + v z₀) * (1 + deriv v z₀) = deriv Φ z₀ :=
    derivAbelEq Φ v z₀ R hΦ hv hAbel hz₀mem hzv_mem
  -- ### Step 3: Cauchy's estimate for `v'` and for `Φ'''`.
  have hderivv : ‖deriv v z₀‖ ≤ 1 / (2 * R) :=
    norm_deriv_le_of_bound_ball hRpos hv hv1
  have hderivv_nn : (0 : ℝ) ≤ ‖deriv v z₀‖ := norm_nonneg _
  set S : ℝ := 32 * C * (1 / R ^ 2) with hSdef
  have hSconv : 32 * C / R ^ 2 = S := by rw [hSdef]; ring
  have hS : ∀ ζ ∈ ball z₀ (5 / 4), ‖iteratedDeriv 3 Φ ζ‖ ≤ S := by
    intro ζ hζ
    have hζle : ‖ζ - z₀‖ ≤ 5 / 4 := by
      rw [mem_ball, dist_eq_norm] at hζ; linarith
    have h1 := cauchyIteratedDerivThree (z₀ := z₀) (R := R) (C := C) hR16 hΦ
      (fun z hz => (hkoebe Φ v z₀ R hΦ hinj hv hv1 hAbel z hz).2) (z := ζ) hζle
    rwa [hSconv] at h1
  -- ### Step 4: the mean slope `(Φ'(z₀+w) - Φ'(z₀))/w` vs `Φ''(z₀)`.
  have hA_bound :
      ‖(deriv Φ (z₀ + v z₀) - deriv Φ z₀) / v z₀‖ ≤ (4 / 3) * C * ‖deriv v z₀‖ := by
    have hnum : deriv Φ (z₀ + v z₀) - deriv Φ z₀
        = -(deriv Φ (z₀ + v z₀) * deriv v z₀) := by
      rw [← hAbel']; ring
    rw [hnum, norm_div, norm_neg, norm_mul]
    rw [div_le_iff₀ hw_nn]
    have hD : ‖deriv Φ (z₀ + v z₀)‖ ≤ C := hKzv.2
    have h2 : C ≤ (4 / 3) * C * ‖v z₀‖ := by
      have hw' : (1 : ℝ) ≤ (4 / 3) * ‖v z₀‖ := by linarith [hw_gt]
      calc C = C * 1 := by ring
        _ ≤ C * ((4 / 3) * ‖v z₀‖) := mul_le_mul_of_nonneg_left hw' hCpos.le
        _ = (4 / 3) * C * ‖v z₀‖ := by ring
    calc ‖deriv Φ (z₀ + v z₀)‖ * ‖deriv v z₀‖ ≤ C * ‖deriv v z₀‖ :=
          mul_le_mul_of_nonneg_right hD hderivv_nn
      _ ≤ ((4 / 3) * C * ‖v z₀‖) * ‖deriv v z₀‖ :=
          mul_le_mul_of_nonneg_right h2 hderivv_nn
      _ = (4 / 3) * C * ‖deriv v z₀‖ * ‖v z₀‖ := by ring
  have hPhi2 : ‖iteratedDeriv 2 Φ z₀‖ ≤ (4 / 3) * C * ‖deriv v z₀‖ + (25 / 12) * S := by
    have hmid := derivMiddleSubLe (f := Φ) (z₀ := z₀) (w := v z₀) (R := R) (S := S)
      (by linarith) hΦ hS hw_lt hw_gt.le
    calc ‖iteratedDeriv 2 Φ z₀‖
        = ‖(iteratedDeriv 2 Φ z₀ - (deriv Φ (z₀ + v z₀) - deriv Φ z₀) / v z₀)
            + (deriv Φ (z₀ + v z₀) - deriv Φ z₀) / v z₀‖ := by ring_nf
      _ ≤ ‖iteratedDeriv 2 Φ z₀ - (deriv Φ (z₀ + v z₀) - deriv Φ z₀) / v z₀‖
            + ‖(deriv Φ (z₀ + v z₀) - deriv Φ z₀) / v z₀‖ := norm_add_le _ _
      _ ≤ (25 / 12) * S + (4 / 3) * C * ‖deriv v z₀‖ := add_le_add hmid hA_bound
      _ = (4 / 3) * C * ‖deriv v z₀‖ + (25 / 12) * S := by ring
  -- ### Step 5: the second order Taylor remainder at `z₀`.
  have hnorm2 : ‖(v z₀ ^ 2 / 2) * iteratedDeriv 2 Φ z₀‖
      = (‖v z₀‖ ^ 2 / 2) * ‖iteratedDeriv 2 Φ z₀‖ := by
    rw [norm_mul, norm_div, norm_pow, Complex.norm_ofNat]
  have hPhi1 : ‖1 - v z₀ * deriv Φ z₀‖
      ≤ (125 / 64) * S + (25 / 32) * ‖iteratedDeriv 2 Φ z₀‖ := by
    have ht := taylor2MeanValue (f := Φ) (z₀ := z₀) (R := R) (S := S)
      (by linarith) hΦ hS hw_lt
    have hab : Φ (z₀ + v z₀) - Φ z₀ = 1 := by rw [hAbel_at]; ring
    rw [hab] at ht
    have hsplit : 1 - v z₀ * deriv Φ z₀
        = (1 - v z₀ * deriv Φ z₀ - (v z₀ ^ 2 / 2) * iteratedDeriv 2 Φ z₀)
          + (v z₀ ^ 2 / 2) * iteratedDeriv 2 Φ z₀ := by ring
    rw [hsplit]
    have h2 : ‖v z₀‖ ^ 2 / 2 ≤ 25 / 32 := by
      nlinarith [hw_lt, norm_nonneg (v z₀)]
    refine le_trans (norm_add_le _ _) (add_le_add ht ?_)
    rw [hnorm2]
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  -- ### Step 6: assemble.
  have hmain : ‖deriv Φ z₀ - 1 / v z₀‖ ≤ 200 * C * (1 / R ^ 2 + ‖deriv v z₀‖) := by
    have hv0 : v z₀ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hw_nn
      exact lt_irrefl 0 hw_nn
    have hfac : deriv Φ z₀ - 1 / v z₀ = -(1 - v z₀ * deriv Φ z₀) / v z₀ := by
      field_simp
      ring
    rw [hfac, norm_div, norm_neg]
    rw [div_le_iff₀ hw_nn]
    have hgoal : (125 / 64) * S + (25 / 32) * ((4 / 3) * C * ‖deriv v z₀‖ + (25 / 12) * S)
        ≤ 200 * C * (1 / R ^ 2 + ‖deriv v z₀‖) * (3 / 4) := by
      rw [hSdef]
      nlinarith [hCpos, hR2inv_nn, norm_nonneg (deriv v z₀)]
    have hcomb : ‖1 - v z₀ * deriv Φ z₀‖
        ≤ (125 / 64) * S + (25 / 32) * ((4 / 3) * C * ‖deriv v z₀‖ + (25 / 12) * S) := by
      have h2 := mul_le_mul_of_nonneg_left hPhi2 (by norm_num : (0 : ℝ) ≤ 25 / 32)
      linarith
    have hmono : 200 * C * (1 / R ^ 2 + ‖deriv v z₀‖) * (3 / 4)
        ≤ 200 * C * (1 / R ^ 2 + ‖deriv v z₀‖) * ‖v z₀‖ := by
      have hnn : 0 ≤ 200 * C * (1 / R ^ 2 + ‖deriv v z₀‖) := by positivity
      exact mul_le_mul_of_nonneg_left hw_gt.le hnn
    linarith [hcomb, hgoal, hmono]
  have hsec : ‖deriv Φ z₀ - 1 / v z₀‖ ≤ 200 * C / R := by
    have h2 : 1 / R ^ 2 + ‖deriv v z₀‖ ≤ 1 / R := by
      have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
      have hy : ‖deriv v z₀‖ * R ^ 2 ≤ R / 2 := by
        have h1 : ‖deriv v z₀‖ * R ^ 2 ≤ (1 / (2 * R)) * R ^ 2 :=
          mul_le_mul_of_nonneg_right hderivv (by positivity)
        have h2' : (1 / (2 * R)) * R ^ 2 = R / 2 := by
          have hne : R ≠ 0 := ne_of_gt hRpos
          field_simp
        linarith [h1, h2'.le, h2'.ge]
      rw [div_add' 1 ‖deriv v z₀‖ (R ^ 2) (ne_of_gt hR2pos), div_le_div_iff₀ hR2pos hRpos]
      nlinarith [hy, hRpos]
    calc ‖deriv Φ z₀ - 1 / v z₀‖ ≤ 200 * C * (1 / R ^ 2 + ‖deriv v z₀‖) := hmain
      _ ≤ 200 * C * (1 / R) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 200 * C / R := by ring
  exact ⟨hmain, hsec⟩

end

end Work.FatouCH
