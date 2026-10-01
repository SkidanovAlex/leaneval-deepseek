import Mathlib
import Submission.Commons.NumberTheory.Linnik.partialFraction_conv
import Submission.Commons.NumberTheory.Linnik.goodRadius_pair
import Submission.Commons.Analysis.Complex.exterior_jensen_multiplicity

open Complex Metric Filter
open scoped Real BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

namespace Work.LinnikAreas

/-- A zero of a function all of whose zeros lie in the open critical strip, and whose imaginary
part is `< T` in absolute value with `T ≥ 0`, lies in the closed ball of radius `T + 1`. -/
lemma zeroNorm_le_of_im_lt_aux {f : ℂ → ℂ}
    (hstrip : ∀ u : ℂ, f u = 0 → 0 < u.re ∧ u.re < 1) {u : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hu : f u = 0) (him : |u.im| < T) : ‖u‖ ≤ T + 1 := by
  have hst := hstrip u hu
  have hre2 : u.re ^ 2 < 1 := by nlinarith [hst.1, hst.2]
  have him2 : u.im ^ 2 < T ^ 2 := by
    rw [sq_lt_sq]
    rwa [abs_of_nonneg hT]
  have hns : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hsu : ‖u‖ ^ 2 < (T + 1) ^ 2 := by
    rw [hns]; nlinarith
  have h1 : 0 ≤ ‖u‖ := norm_nonneg u
  have h2 : 0 ≤ T + 1 := by linarith
  exact le_of_lt ((sq_lt_sq₀ h1 h2).mp hsu)

/-- **General entire-function strip-sum convergence.**

If `f` is an entire function whose zeros all lie in the open critical strip `0 < Re < 1`, whose
zero count in the disk of radius `R` is `≪ R log R`, and `Φ` decays like `A/‖u‖²` on that strip,
then convergence of the ball-restricted divisor sums of `f` against `Φ` implies convergence of the
horizontal-strip (`|Im u| < T`) zero sums against `Φ` to the same limit.

This is the statement of `Commons.NumberTheory.Linnik.stripSum_tendsto_of_ballSum_tendsto`
(proved there for `f = completedLFunction χ`, `χ` non-principal primitive, with the zero count and
strip hypotheses discharged from the character theory); that proof adapts verbatim, replacing every
use of the specific `Λ = completedLFunction χ` by the hypotheses below. -/
theorem stripSum_tendsto_of_ballSum_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfne : f ≠ 0)
    (hstrip : ∀ u : ℂ, f u = 0 → 0 < u.re ∧ u.re < 1)
    {c : ℝ} (hc : 0 ≤ c)
    (hcount : ∀ R : ℝ, 2 ≤ R →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall 0 R)) u : ℤ) : ℝ))
        ≤ c * R * (Real.log (R + 2) + 2))
    {Φ : ℂ → ℂ} {A : ℝ} (hA : 0 < A)
    (hΦ : ∀ u : ℂ, 0 < u.re → u.re < 1 → 2 ≤ ‖u‖ → ‖Φ u‖ ≤ A / ‖u‖ ^ 2)
    {Z : ℂ}
    (hZ : Filter.Tendsto (fun R : ℝ => ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor f (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u)
        Filter.atTop (nhds Z)) :
    Filter.Tendsto (fun T : ℝ => ∑ᶠ u : ℂ,
        (if |u.im| < T then (((analyticOrderNatAt f u : ℕ) : ℂ) * Φ u) else 0))
      Filter.atTop (nhds Z) := by
  classical
  have hfan : ∀ U : Set ℂ, AnalyticOnNhd ℂ f U := fun U z _ => hf.analyticAt z
  let D : ℝ → Finset ℂ := fun R =>
    ((MeromorphicOn.divisor f (Metric.closedBall 0 R)).finiteSupport
      (isCompact_closedBall (0 : ℂ) R)).toFinset
  let g : ℂ → ℂ := fun u => ((analyticOrderNatAt f u : ℕ) : ℂ) * Φ u
  let B : ℝ → ℂ := fun R => ∑ᶠ u : ℂ,
      (((MeromorphicOn.divisor f (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u
  let W : ℝ → ℂ := fun T => ∑ᶠ u : ℂ,
      (if |u.im| < T then (((analyticOrderNatAt f u : ℕ) : ℂ) * Φ u) else 0)
  have hZ' : Filter.Tendsto B Filter.atTop (nhds Z) := by
    simpa [B] using hZ
  have hDmem : ∀ (R : ℝ) (u : ℂ),
      u ∈ D R ↔ MeromorphicOn.divisor f (Metric.closedBall 0 R) u ≠ 0 := by
    intro R u
    simp only [D]
    rw [Set.Finite.mem_toFinset, Function.mem_support]
  have hdivU : ∀ (R : ℝ) (u : ℂ), u ∈ D R →
      MeromorphicOn.divisor f (Metric.closedBall 0 R) u = (analyticOrderNatAt f u : ℤ) := by
    intro R u hu
    have hdu : MeromorphicOn.divisor f (Metric.closedBall 0 R) u ≠ 0 := (hDmem R u).mp hu
    have huB : u ∈ Metric.closedBall (0 : ℂ) R :=
      (MeromorphicOn.divisor f (Metric.closedBall 0 R)).supportWithinDomain hdu
    exact Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast (hfan _) huB
  have hBR : ∀ R : ℝ, B R = ∑ u ∈ D R, g u := by
    intro R
    have hsupp : Function.support (fun u : ℂ =>
        (((MeromorphicOn.divisor f (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u) ⊆ ↑(D R) := by
      intro u hu
      rw [Function.mem_support] at hu
      have hdu : MeromorphicOn.divisor f (Metric.closedBall 0 R) u ≠ 0 := by
        intro h0; exact hu (by simp [h0])
      exact (hDmem R u).mpr hdu
    calc B R = ∑ᶠ u : ℂ,
            (((MeromorphicOn.divisor f (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u := rfl
      _ = ∑ u ∈ D R, (((MeromorphicOn.divisor f (Metric.closedBall 0 R)) u : ℤ) : ℂ) * Φ u :=
            finsum_eq_sum_of_support_subset _ hsupp
      _ = ∑ u ∈ D R, g u := by
            apply Finset.sum_congr rfl
            intro u hu
            simp only [g]
            rw [hdivU R u hu, Int.cast_natCast]
  have hfinsumD : ∀ R : ℝ,
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor f (Metric.closedBall 0 R)) u : ℤ) : ℝ))
        = ∑ u ∈ D R, ((analyticOrderNatAt f u : ℕ) : ℝ) := by
    intro R
    have hsupp : Function.support (fun u : ℂ =>
        (((MeromorphicOn.divisor f (Metric.closedBall 0 R)) u : ℤ) : ℝ)) ⊆ ↑(D R) := by
      intro u hu
      rw [Function.mem_support] at hu
      have hdu : MeromorphicOn.divisor f (Metric.closedBall 0 R) u ≠ 0 := by
        intro h0; exact hu (by simp [h0])
      exact (hDmem R u).mpr hdu
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    apply Finset.sum_congr rfl
    intro u hu
    rw [hdivU R u hu, Int.cast_natCast]
  have hcountD : ∀ R : ℝ, 2 ≤ R →
      ∑ u ∈ D R, ((analyticOrderNatAt f u : ℕ) : ℝ) ≤ c * R * (Real.log (R + 2) + 2) := by
    intro R hR
    have h1 := hcount R hR
    rw [hfinsumD R] at h1
    exact h1
  have hW1 : ∀ T : ℝ, 0 ≤ T → W T = ∑ u ∈ (D (T + 1)).filter (fun u => |u.im| < T), g u := by
    intro T hT
    have hsupp : Function.support (fun u : ℂ =>
        (if |u.im| < T then (((analyticOrderNatAt f u : ℕ) : ℂ) * Φ u) else 0)) ⊆
        ↑((D (T + 1)).filter (fun u => |u.im| < T)) := by
      intro u hu
      rw [Function.mem_support] at hu
      rw [Finset.mem_coe, Finset.mem_filter]
      have hp : |u.im| < T := by
        by_contra h; rw [if_neg h] at hu; exact hu rfl
      refine ⟨?_, hp⟩
      rw [hDmem]
      have hmu : analyticOrderNatAt f u ≠ 0 := by
        intro h0
        apply hu
        rw [if_pos hp]
        simp [h0]
      have hfu : f u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hmu
      have hb : u ∈ Metric.closedBall (0 : ℂ) (T + 1) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact zeroNorm_le_of_im_lt_aux hstrip hT hfu hp
      exact Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero hf hfne hb hfu
    calc W T = ∑ᶠ u : ℂ,
            (if |u.im| < T then (((analyticOrderNatAt f u : ℕ) : ℂ) * Φ u) else 0) := rfl
      _ = ∑ u ∈ (D (T + 1)).filter (fun u => |u.im| < T),
            (if |u.im| < T then (((analyticOrderNatAt f u : ℕ) : ℂ) * Φ u) else 0) :=
            finsum_eq_sum_of_support_subset _ hsupp
      _ = ∑ u ∈ (D (T + 1)).filter (fun u => |u.im| < T), g u := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [if_pos (Finset.mem_filter.mp hu).2]
  have hstep : ∀ T : ℝ, 2 ≤ T → ‖W T - B (T + 1)‖
      ≤ c * A * (T + 1) * (Real.log (T + 1 + 2) + 2) / T ^ 2 := by
    intro T hT
    have hTpos : 0 < T := by linarith
    have hT0 : 0 ≤ T := le_of_lt hTpos
    have hpart := Finset.sum_filter_add_sum_filter_not (D (T + 1)) (fun u => |u.im| < T) g
    have hWB : W T - B (T + 1)
        = - ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)), g u := by
      rw [hBR (T + 1), hW1 T hT0, ← hpart]; ring
    have hAT2 : 0 ≤ A / T ^ 2 := le_of_lt (div_pos hA (by positivity))
    have hkey : ‖W T - B (T + 1)‖
        ≤ ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
            ((analyticOrderNatAt f u : ℕ) : ℝ) * (A / T ^ 2) := by
      rw [hWB, norm_neg]
      calc ‖∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)), g u‖
          ≤ ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)), ‖g u‖ := norm_sum_le _ _
        _ ≤ ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
              ((analyticOrderNatAt f u : ℕ) : ℝ) * (A / T ^ 2) := by
            apply Finset.sum_le_sum
            intro u hu
            have hmem := Finset.mem_filter.mp hu
            have huD : u ∈ D (T + 1) := hmem.1
            have hnp : ¬ (|u.im| < T) := hmem.2
            have hdu : MeromorphicOn.divisor f (Metric.closedBall 0 (T + 1)) u ≠ 0 :=
              (hDmem (T + 1) u).mp huD
            have hord : analyticOrderNatAt f u ≠ 0 := by
              intro h0
              exact hdu (by rw [hdivU (T + 1) u huD, h0]; simp)
            have hfu : f u = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
            have hst := hstrip u hfu
            have himT : T ≤ |u.im| := le_of_not_gt hnp
            have hu_norm : T ≤ ‖u‖ := le_trans himT (Complex.abs_im_le_norm u)
            have h2u : 2 ≤ ‖u‖ := le_trans hT hu_norm
            have hΦu : ‖Φ u‖ ≤ A / ‖u‖ ^ 2 := hΦ u hst.1 hst.2 h2u
            rw [norm_mul, Complex.norm_natCast]
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            refine le_trans hΦu ?_
            exact div_le_div_of_nonneg_left (le_of_lt hA) (by positivity)
              (pow_le_pow_left₀ hT0 hu_norm 2)
    have hsum_le : ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
          ((analyticOrderNatAt f u : ℕ) : ℝ) * (A / T ^ 2)
        ≤ (A / T ^ 2) * ∑ u ∈ D (T + 1), ((analyticOrderNatAt f u : ℕ) : ℝ) := by
      have hsub : (D (T + 1)).filter (fun u => ¬ (|u.im| < T)) ⊆ D (T + 1) :=
        Finset.filter_subset _ _
      calc ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
              ((analyticOrderNatAt f u : ℕ) : ℝ) * (A / T ^ 2)
          = (∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
              ((analyticOrderNatAt f u : ℕ) : ℝ)) * (A / T ^ 2) := (Finset.sum_mul _ _ _).symm
        _ = (A / T ^ 2) * (∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
              ((analyticOrderNatAt f u : ℕ) : ℝ)) := by ring
        _ ≤ (A / T ^ 2) * (∑ u ∈ D (T + 1), ((analyticOrderNatAt f u : ℕ) : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ hAT2
              exact Finset.sum_le_sum_of_subset_of_nonneg hsub
                (fun u _ _ => Nat.cast_nonneg _)
    have hfin : ∑ u ∈ D (T + 1), ((analyticOrderNatAt f u : ℕ) : ℝ)
        ≤ c * (T + 1) * (Real.log ((T + 1) + 2) + 2) := hcountD (T + 1) (by linarith)
    calc ‖W T - B (T + 1)‖
        ≤ ∑ u ∈ (D (T + 1)).filter (fun u => ¬ (|u.im| < T)),
            ((analyticOrderNatAt f u : ℕ) : ℝ) * (A / T ^ 2) := hkey
      _ ≤ (A / T ^ 2) * (∑ u ∈ D (T + 1), ((analyticOrderNatAt f u : ℕ) : ℝ)) := hsum_le
      _ ≤ (A / T ^ 2) * (c * (T + 1) * (Real.log ((T + 1) + 2) + 2)) :=
            mul_le_mul_of_nonneg_left hfin hAT2
      _ = c * A * (T + 1) * (Real.log (T + 1 + 2) + 2) / T ^ 2 := by ring
  have hEtend : Tendsto (fun T : ℝ => c * A * (T + 1) *
      (Real.log (T + 1 + 2) + 2) / T ^ 2) atTop (nhds 0) := by
    have hg : Tendsto (fun T : ℝ => 2 * (c * A) *
        ((Real.log (T + 2) + (2 + Real.log 2)) / T)) atTop (nhds 0) := by
      have h := Commons.NumberTheory.Linnik.log_add_two_add_const_div_self_tendsto_zero
        (2 + Real.log 2)
      have hc' : Tendsto (fun _ : ℝ => 2 * (c * A)) atTop (nhds (2 * (c * A))) :=
        tendsto_const_nhds
      simpa using hc'.mul h
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      have hlog : 0 ≤ Real.log (T + 1 + 2) := Real.log_nonneg (by linarith)
      have hnum : 0 ≤ c * A * (T + 1) * (Real.log (T + 1 + 2) + 2) := by
        have h1 : 0 ≤ c * A := mul_nonneg hc (le_of_lt hA)
        have h2 : 0 ≤ T + 1 := by linarith
        have h3 : 0 ≤ Real.log (T + 1 + 2) + 2 := by linarith
        positivity
      exact div_nonneg hnum (sq_nonneg T)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hTpos : 0 < T := by linarith
      have hlog_ge : 0 ≤ Real.log (T + 1 + 2) + 2 := by
        have h1 : 0 ≤ Real.log (T + 1 + 2) := Real.log_nonneg (by linarith)
        linarith
      have hlog_le : Real.log (T + 1 + 2) ≤ Real.log (T + 2) + Real.log 2 := by
        have hle : T + 1 + 2 ≤ 2 * (T + 2) := by linarith
        have h := Real.log_le_log (by linarith : 0 < T + 1 + 2) hle
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : (T + 2) ≠ 0)] at h
        linarith
      have hcore : (T + 1) * (Real.log (T + 1 + 2) + 2)
          ≤ 2 * T * (Real.log (T + 2) + (2 + Real.log 2)) := by
        have hT1 : T + 1 ≤ 2 * T := by linarith
        have hL : Real.log (T + 1 + 2) + 2 ≤ Real.log (T + 2) + (2 + Real.log 2) := by linarith
        calc (T + 1) * (Real.log (T + 1 + 2) + 2)
            ≤ (2 * T) * (Real.log (T + 1 + 2) + 2) :=
              mul_le_mul_of_nonneg_right hT1 hlog_ge
          _ ≤ (2 * T) * (Real.log (T + 2) + (2 + Real.log 2)) :=
              mul_le_mul_of_nonneg_left hL (by linarith)
      have hb : c * A * (T + 1) * (Real.log (T + 1 + 2) + 2) / T ^ 2
          ≤ 2 * (c * A) * ((Real.log (T + 2) + (2 + Real.log 2)) / T) := by
        rw [div_le_iff₀ (by positivity : 0 < T ^ 2)]
        have hcA : 0 ≤ c * A := mul_nonneg hc (le_of_lt hA)
        have hmul := mul_le_mul_of_nonneg_left hcore hcA
        have e1 : c * A * (T + 1) * (Real.log (T + 1 + 2) + 2)
            = c * A * ((T + 1) * (Real.log (T + 1 + 2) + 2)) := by ring
        have e2 : 2 * (c * A) * ((Real.log (T + 2) + (2 + Real.log 2)) / T) * T ^ 2
            = c * A * (2 * T * (Real.log (T + 2) + (2 + Real.log 2))) := by
          field_simp
        rw [e1, e2]
        exact hmul
      exact hb
  have hWtend : Tendsto W atTop (nhds Z) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → dist (B R) Z < ε / 2 := by
      obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hZ') (ε / 2) hε2)
      exact ⟨R₀, hR₀⟩
    obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T →
        c * A * (T + 1) * (Real.log (T + 1 + 2) + 2) / T ^ 2 < ε / 2 := by
      obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp ((tendsto_order.mp hEtend).2 (ε / 2) hε2)
      exact ⟨T₁, hT₁⟩
    refine ⟨max (max 2 T₁) (R₀ - 1), ?_⟩
    intro T hT
    have hT2 : 2 ≤ T :=
      le_trans (le_trans (le_max_left 2 T₁) (le_max_left (max 2 T₁) (R₀ - 1))) hT
    have hTT₁ : T₁ ≤ T :=
      le_trans (le_trans (le_max_right 2 T₁) (le_max_left (max 2 T₁) (R₀ - 1))) hT
    have hTR₀ : R₀ ≤ T + 1 := by
      have hle : R₀ - 1 ≤ T := le_trans (le_max_right (max 2 T₁) (R₀ - 1)) hT
      linarith
    rw [dist_eq_norm]
    have htri : ‖W T - Z‖ ≤ ‖W T - B (T + 1)‖ + ‖B (T + 1) - Z‖ := by
      calc ‖W T - Z‖ = ‖(W T - B (T + 1)) + (B (T + 1) - Z)‖ := by ring_nf
        _ ≤ ‖W T - B (T + 1)‖ + ‖B (T + 1) - Z‖ := norm_add_le _ _
    have hbad := hstep T hT2
    have hgood := hR₀ (T + 1) hTR₀
    rw [dist_eq_norm] at hgood
    have hbad' := hT₁ T hTT₁
    linarith
  simpa [W] using hWtend

end Work.LinnikAreas
