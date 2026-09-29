import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.CRad.deps
import Submission.Work.C17.beukersUR_two_sided
import Submission.Work.C17.logP_defs
import Submission.Work.C17.beukersD_two_sided
import Submission.Work.C17.logP_bounds
import Submission.Work.C17.powseries_poly_geom
import Submission.Work.C17.Ffun_no_large_radius
import Submission.Work.C17.summable_poly_geom
import Submission.Work.C17.Pfun_eq_kap_Fsum_add_Ksum
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Submission.Commons.Analysis.InfiniteSum.summable_nat_pow_mul_geom

namespace Work.C17

open scoped BigOperators

/-- The two-sided bounds for the companion coefficients `dₙ(x) = vₙ(x) − η_x uₙ(x)`
(the conclusion of `Work.C17.beukersD_two_sided`), bundled. -/
def DBounds (x : ℝ) (c C : ℝ) : Prop :=
  0 < c ∧ ∀ n : ℕ,
    Submission.CDT.beukersD x n < 0 ∧
      c / (((n : ℝ) + 1) ^ 4 * (x + Real.sqrt (x ^ 2 - 1)) ^ n)
        ≤ |Submission.CDT.beukersD x n| ∧
      |Submission.CDT.beukersD x n| ≤ C * ((n : ℝ) + 1) ^ 2 / (x + Real.sqrt (x ^ 2 - 1)) ^ n

/-- Comparison test with a cubic polynomial factor (weakening of `summable_poly_geom`). -/
lemma summable_poly_geom3 (f : ℕ → ℝ) (C θ : ℝ) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hf : ∀ n : ℕ, |f n| ≤ C * ((n : ℝ) + 1) ^ 3 * θ ^ n) {r : ℝ} (hr : θ * |r| < 1) :
    Summable fun n : ℕ => f n * r ^ n := by
  refine summable_poly_geom f C θ hC hθ (fun n => ?_) hr
  have h2 : ((n : ℝ) + 1) ^ 3 ≤ ((n : ℝ) + 1) ^ 4 := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    calc ((n : ℝ) + 1) ^ 3 = ((n : ℝ) + 1) ^ 3 * 1 := (mul_one _).symm
      _ ≤ ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 by positivity)
      _ = ((n : ℝ) + 1) ^ 4 := by ring
  calc |f n| ≤ C * ((n : ℝ) + 1) ^ 3 * θ ^ n := hf n
    _ = C * (((n : ℝ) + 1) ^ 3 * θ ^ n) := by ring
    _ ≤ C * (((n : ℝ) + 1) ^ 4 * θ ^ n) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h2 (show (0 : ℝ) ≤ θ ^ n by positivity)) hC
    _ = C * ((n : ℝ) + 1) ^ 4 * θ ^ n := by ring

theorem logP_not_holomorphic_at_xs (a b : ℚ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a < b)
    (ra rb rab r0 : ℤ) (hrab : rab ≠ 0)
    (hrel : (ra : ℝ) * Submission.CDT.beukersEta (a : ℝ) + (rb : ℝ) * Submission.CDT.beukersEta (b : ℝ)
        + (rab : ℝ) * (Submission.CDT.beukersEta (a : ℝ) * Submission.CDT.beukersEta (b : ℝ)) = (r0 : ℝ))
    (heta : Irrational (Submission.CDT.beukersEta (b : ℝ)))
    (prings : ∀ (f : ℕ → ℝ), (∀ n, 0 ≤ f n) → ∀ (R : ℝ), 0 < R →
      (∀ r : ℝ, 0 ≤ r → r < R → Summable fun n => f n * r ^ n) →
      ∀ (g : ℂ → ℂ) (δ : ℝ), 0 < δ → DifferentiableOn ℂ g (Metric.ball (R : ℂ) δ) →
      (∀ z ∈ Metric.ball (R : ℂ) δ ∩ Metric.ball (0 : ℂ) R,
        HasSum (fun n => (f n : ℂ) * z ^ n) (g z)) →
      ∃ ρ : ℝ, R < ρ ∧ Summable fun n => f n * ρ ^ n)
    {δ : ℝ} (hδ : 0 < δ) (g : ℂ → ℂ) (hg : DifferentiableOn ℂ g (Metric.ball (xs a b : ℂ) δ)) :
    ¬ (∀ z ∈ Metric.ball (xs a b : ℂ) δ ∩ Metric.ball (0 : ℂ) (xs a b), g z = Pfun a b ra rb rab r0 z) := by
  intro hcont
  have hA3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hB3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hAB : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  -- ## 1. the two-sided Beukers input
  obtain ⟨cD, CD, hDa⟩ : ∃ c C : ℝ, DBounds (a : ℝ) c C := by
    simpa [DBounds] using beukersD_two_sided (a : ℝ) hA3
  obtain ⟨cE, CE, hDb⟩ : ∃ c C : ℝ, DBounds (b : ℝ) c C := by
    simpa [DBounds] using beukersD_two_sided (b : ℝ) hB3
  set Cmax : ℝ := max CD CE with hCmax
  obtain ⟨hxspos, hxssq, hFhi, hFlo, hKhi⟩ :=
    logP_bounds a b ha hb hab ra rb rab cD Cmax hDa.1
      (fun n => (hDa.2 n).2.1)
      (fun n => le_trans (hDa.2 n).2.2
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left CD CE) (by positivity))
          (by positivity)))
      (fun n => le_trans (hDb.2 n).2.2
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right CD CE) (by positivity))
          (by positivity)))
      (fun n => (beukersUR_two_sided (a : ℝ) hA3 n).2)
      (fun n => (beukersUR_two_sided (b : ℝ) hB3 n).1)
      (fun n => (beukersUR_two_sided (b : ℝ) hB3 n).2)
  obtain ⟨C₁, hC₁pos, hFb⟩ := hFhi
  obtain ⟨c₁, hc₁pos, hFlob⟩ := hFlo
  obtain ⟨C₂, hC₂pos, hKb⟩ := hKhi
  have hxs1 : xs a b < 1 := by nlinarith [hxspos, hxssq]
  -- ## 2. `κ ≠ 0` from the irrationality of `η_b`
  have hκ : kap a b ra rab ≠ 0 := by
    rw [kap]
    intro h
    have hrabR : (rab : ℝ) ≠ 0 := by exact_mod_cast hrab
    have hη : Submission.CDT.beukersEta (b : ℝ) = ((-ra : ℤ) : ℝ) / ((rab : ℤ) : ℝ) := by
      rw [eq_div_iff hrabR]
      push_cast
      linarith
    exact (irrational_iff_ne_rational (Submission.CDT.beukersEta (b : ℝ))).mp heta (-ra) rab hrab hη
  have hκC : (kap a b ra rab : ℂ) ≠ 0 := by
    exact_mod_cast hκ
  -- ## 3. the sign of the `F`-coefficients
  have hFneg : ∀ n : ℕ, Ffun a b n < 0 := by
    intro n
    have h1 : Submission.CDT.beukersD (a : ℝ) n < 0 := (hDa.2 n).1
    have h2 : 0 < Submission.CDT.beukersUR (b : ℝ) n :=
      Submission.CDT.beukersUR_pos (b : ℝ) (by linarith) n
    rw [Ffun]
    exact mul_neg_of_neg_of_pos h1 h2
  have hnn : ∀ n : ℕ, 0 ≤ -(Ffun a b n) := fun n => by linarith [hFneg n]
  -- ## 4. the disc on which the remainder series is analytic
  set RK : ℝ := 1 / xs a b with hRK
  have hRKgt : xs a b < RK := by
    rw [hRK, lt_div_iff₀ hxspos]
    linarith [hxssq]
  set R' : ℝ := (xs a b + RK) / 2 with hR'
  have hxR' : xs a b < R' := by rw [hR']; linarith
  have hR'RK : R' < RK := by rw [hR']; linarith
  have hθR' : xs a b * R' < 1 := by
    have h := (lt_div_iff₀ hxspos).mp (by rw [← hRK]; exact hR'RK)
    linarith [h]
  have hKnorm : ∀ n : ℕ, ‖(Kfun a b ra rb rab n : ℂ)‖ ≤ C₂ * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hKb n
  have hKdiff0 : DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ, (Kfun a b ra rb rab n : ℂ) * z ^ n)
      (Metric.ball (0 : ℂ) R') :=
    (powseries_poly_geom (fun n => (Kfun a b ra rb rab n : ℂ)) C₂ (xs a b) (le_of_lt hC₂pos)
      (le_of_lt hxspos) hKnorm).2 R' hθR'
  set δ₂ : ℝ := min δ (R' - xs a b) with hδ₂
  have hδ₂pos : 0 < δ₂ := by rw [hδ₂]; exact lt_min hδ (by linarith)
  have hδ₂δ : δ₂ ≤ δ := by rw [hδ₂]; exact min_le_left _ _
  have hδ₂R : δ₂ ≤ R' - xs a b := by rw [hδ₂]; exact min_le_right _ _
  have hballK : Metric.ball (xs a b : ℂ) (R' - xs a b) ⊆ Metric.ball (0 : ℂ) R' := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have hxsC : ‖((xs a b : ℝ) : ℂ)‖ = xs a b := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hxspos)]
    calc ‖z‖ = ‖z - (xs a b : ℂ) + (xs a b : ℂ)‖ := by congr 1; ring
      _ ≤ ‖z - (xs a b : ℂ)‖ + ‖((xs a b : ℝ) : ℂ)‖ := norm_add_le _ _
      _ < R' - xs a b + xs a b := by rw [hxsC]; linarith
      _ = R' := by ring
  set Khat : ℂ → ℂ := fun z => ∑' n : ℕ, (Kfun a b ra rb rab n : ℂ) * z ^ n with hKhat
  have hKdiff : DifferentiableOn ℂ Khat (Metric.ball (xs a b : ℂ) δ₂) := by
    rw [hKhat]
    exact hKdiff0.mono (Set.Subset.trans (Metric.ball_subset_ball hδ₂R) hballK)
  set G : ℂ → ℂ := fun z => (Khat z - g z) * (kap a b ra rab : ℂ)⁻¹ with hG
  have hGdiff : DifferentiableOn ℂ G (Metric.ball (xs a b : ℂ) δ₂) := by
    rw [hG]
    exact (hKdiff.sub (hg.mono (Metric.ball_subset_ball hδ₂δ))).mul_const _
  -- ## 5. summability of the `F`- and `K`-series
  have hFsumm_abs : ∀ z : ℂ, ‖z‖ < xs a b → Summable fun n : ℕ => |Ffun a b n| * ‖z‖ ^ n := by
    intro z hz
    refine summable_poly_geom3 (fun n : ℕ => |Ffun a b n|) C₁ (1 / xs a b) (le_of_lt hC₁pos)
      (by positivity) ?_ ?_
    · intro n
      rw [abs_abs]
      simpa only [div_eq_mul_inv, one_mul, inv_pow] using hFb n
    · rw [abs_of_nonneg (norm_nonneg z), one_div, inv_mul_eq_div, div_lt_one hxspos]
      exact hz
  have hFsumm : ∀ z : ℂ, ‖z‖ < xs a b → Summable fun n : ℕ => (Ffun a b n : ℂ) * z ^ n := by
    intro z hz
    refine Summable.of_norm_bounded (hFsumm_abs z hz) (fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  have hKsumm : ∀ z : ℂ, ‖z‖ < xs a b → Summable fun n : ℕ => (Kfun a b ra rb rab n : ℂ) * z ^ n := by
    intro z hz
    have habs : Summable fun n : ℕ => |Kfun a b ra rb rab n| * ‖z‖ ^ n := by
      refine summable_poly_geom (fun n : ℕ => |Kfun a b ra rb rab n|) C₂ (xs a b) (le_of_lt hC₂pos)
        (le_of_lt hxspos) ?_ ?_
      · intro n
        rw [abs_abs]
        exact hKb n
      · rw [abs_of_nonneg (norm_nonneg z)]
        have h1 : xs a b * ‖z‖ < xs a b * xs a b := mul_lt_mul_of_pos_left hz hxspos
        linarith [h1, hxssq]
    refine Summable.of_norm_bounded habs (fun n => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  -- ## 6. the `HasSum` identity: `G` extends the `-F`-series
  have hHasSum : ∀ z ∈ Metric.ball (xs a b : ℂ) δ₂ ∩ Metric.ball (0 : ℂ) (xs a b),
      HasSum (fun n : ℕ => ((-(Ffun a b n) : ℝ) : ℂ) * z ^ n) (G z) := by
    intro z hz
    obtain ⟨hzδ₂, hzx⟩ := hz
    have hzδ : z ∈ Metric.ball (xs a b : ℂ) δ := Metric.ball_subset_ball hδ₂δ hzδ₂
    have hgz : g z = Pfun a b ra rb rab r0 z := hcont z ⟨hzδ, hzx⟩
    have hzx' : ‖z‖ < xs a b := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hzx
      exact hzx
    have hFbC : ∀ n : ℕ, ‖(Ffun a b n : ℂ)‖ ≤ C₁ * ((n : ℝ) + 1) ^ 3 * (1 / (xs a b)) ^ n := by
      intro n
      rw [Complex.norm_real, Real.norm_eq_abs]
      simpa only [div_eq_mul_inv, one_mul, inv_pow] using hFb n
    have hKbC : ∀ n : ℕ, ‖(Kfun a b ra rb rab n : ℂ)‖ ≤ C₂ * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n :=
      hKnorm
    have hident := Pfun_eq_kap_Fsum_add_Ksum a b ra rb rab r0 hrel hxspos hxs1 C₁ C₂ hFbC hKbC hzx'
    have hKhatz : Khat z = ∑' n : ℕ, (Kfun a b ra rb rab n : ℂ) * z ^ n := by rw [hKhat]
    have hFsolve : (∑' n : ℕ, (Ffun a b n : ℂ) * z ^ n)
        = (g z - Khat z) * (kap a b ra rab : ℂ)⁻¹ := by
      have h2 : (kap a b ra rab : ℂ) * (∑' n : ℕ, (Ffun a b n : ℂ) * z ^ n) = g z - Khat z := by
        rw [hgz, hKhatz, hident]
        ring
      calc (∑' n : ℕ, (Ffun a b n : ℂ) * z ^ n)
          = (kap a b ra rab : ℂ)⁻¹ * ((kap a b ra rab : ℂ) * (∑' n : ℕ, (Ffun a b n : ℂ) * z ^ n)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hκC, one_mul]
        _ = (kap a b ra rab : ℂ)⁻¹ * (g z - Khat z) := by rw [h2]
        _ = (g z - Khat z) * (kap a b ra rab : ℂ)⁻¹ := by ring
    have hGval : G z = -(∑' n : ℕ, (Ffun a b n : ℂ) * z ^ n) := by
      rw [hG, hFsolve]
      ring
    have hFS := (hFsumm z hzx').hasSum.neg
    rw [← hGval] at hFS
    simpa only [Complex.ofReal_neg, neg_mul] using hFS
  -- ## 7. Vivanti-Pringsheim
  have hsumm_r : ∀ r : ℝ, 0 ≤ r → r < xs a b → Summable fun n : ℕ => -(Ffun a b n) * r ^ n := by
    intro r hr0 hr
    refine summable_poly_geom3 (fun n : ℕ => -(Ffun a b n)) C₁ (1 / xs a b) (le_of_lt hC₁pos)
      (by positivity) ?_ ?_
    · intro n
      rw [abs_neg]
      simpa only [div_eq_mul_inv, one_mul, inv_pow] using hFb n
    · rw [abs_of_nonneg hr0, one_div, inv_mul_eq_div, div_lt_one hxspos]
      exact hr
  obtain ⟨ρ, hρgt, hρsumm⟩ :=
    prings (fun n : ℕ => -(Ffun a b n)) hnn (xs a b) hxspos hsumm_r G δ₂ hδ₂pos hGdiff hHasSum
  have hFsummρ : Summable fun n : ℕ => Ffun a b n * ρ ^ n := by
    have h := hρsumm.neg
    simpa only [neg_mul, neg_neg] using h
  exact Ffun_no_large_radius a b ha hb hab c₁ hc₁pos hFlob hρgt hFsummρ

end Work.C17
