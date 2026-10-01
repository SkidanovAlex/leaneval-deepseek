import Mathlib
import Submission.Work.LinnikAreas.DhK.XiAux
import Submission.Work.ZeroFreeTables.P3.dyadicAnnulusKernel_le
import Submission.Work.LinnikAreas.FarRepel.XiAnnulusDefs
import Submission.Work.LinnikAreas.FarRepel.xiAnnulusMass_count_le
import Submission.Work.LinnikAreas.FarRepel.xiAnnulusDivisor_norm_sum_le

open scoped Classical BigOperators

namespace Work.LinnikAreas.FarRepel

/-- **Uniform annulus bound for the `k`-th partial-fraction sum of `Ξ`.** (module `Submission.Work.LinnikAreas.FarRepel.xiE_annulusBound`; declare in `namespace Work.LinnikAreas.FarRepel`; import `Submission.Work.LinnikAreas.DhK.XiAux`.)

For `k ≥ 1` there is `C ≥ 0` such that for all `R ≤ R'`, `2 ≤ R`, and `s` with `8‖s‖ ≤ R`, the
annulus `R < ‖u‖ ≤ R'` contribution to the divisor sum of `Ξ = 1/2 + (1/2)·s(s-1)·Λ₀(s)` is at most
`C * xiL R / R`, uniformly in `R'`, where `xiL R = log (R+2) + 2`.

PROOF ROUTE: mirror `Work.ZeroFreeTables.P3.annulusKDSum_le` with `Λ := DhK.Xi`; the generic
dyadic-annulus input is `Work.ZeroFreeTables.P3.dyadicAnnulusKernel_le` with the ball-count bound
`Work.LinnikAreas.DhK.Xi_zeroCount_L`, and the reduction uses `DhK.Xi_divisor_nonneg`,
`DhK.Xi_divisor_support_finite`, `DhK.Xi_divisor_ne_zero_is_zero`,
`Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le` and
`Commons.NumberTheory.Linnik.divisor_eq_zero_of_nmem` (family `Linnik.logDeriv_pf_identity`; do NOT
import `Commons.NumberTheory.Zeta.xiE_partialFraction_eq` or `...completedL_pf_identity_rect`, which
clash on `pfP`). -/
theorem xiE_annulusBound (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (R R' : ℝ), 2 ≤ R → R ≤ R' → 8 * ‖s‖ ≤ R →
      ‖∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 R') u -
            MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 R) u) : ℤ) : ℂ) *
          (1 / (s - u)) ^ (k + 1))‖ ≤ C * Work.LinnikAreas.DhK.xiL R / R := by
  classical
  obtain ⟨c₀, hc₀, hcnt⟩ := xiAnnulusMass_count_le
  obtain ⟨C₁, hC₁, hdyad⟩ :=
    Work.ZeroFreeTables.P3.dyadicAnnulusKernel_le (c := c₀) (L := 2) (n := k + 1)
      hc₀ (by norm_num) (by omega)
  refine ⟨(8/7 : ℝ) ^ (k + 1) * C₁ * (3/2), by positivity, ?_⟩
  intro s R R' hR2 hRR' hs
  have hkey : ‖∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
        (Metric.closedBall 0 R') u -
        MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 R) u) : ℤ) : ℂ) *
        (1 / (s - u)) ^ (k + 1))‖
      ≤ ∑ᶠ u : ℂ, xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ (k + 1) := by
    simpa only [xiAnnulusDivisor] using
      xiAnnulusDivisor_norm_sum_le (k + 1) s hRR'
  have hmono : (∑ᶠ u : ℂ, xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ (k + 1))
      ≤ (8/7 : ℝ) ^ (k + 1) *
        (∑ᶠ u : ℂ, (if R < ‖u‖ then xiAnnulusMass R R' u else 0)
          * (1 / ‖u‖) ^ (k + 1)) := by
    have hfin_inner : Function.HasFiniteSupport
        (fun u : ℂ => (if R < ‖u‖ then xiAnnulusMass R R' u else 0)
          * (1 / ‖u‖) ^ (k + 1)) := by
      refine (xiAnnulusMass_finiteSupport R R').subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hM
      apply hu
      rw [hM]
      by_cases h : R < ‖u‖ <;> simp [h]
    have hfin1 : Function.HasFiniteSupport
        (fun u : ℂ => xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ (k + 1)) := by
      refine (xiAnnulusMass_finiteSupport R R').subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hM
      exact hu (by rw [hM, zero_mul])
    have hfin2 : Function.HasFiniteSupport
        (fun u : ℂ => (8/7 : ℝ) ^ (k + 1) *
          ((if R < ‖u‖ then xiAnnulusMass R R' u else 0) * (1 / ‖u‖) ^ (k + 1))) := by
      refine (xiAnnulusMass_finiteSupport R R').subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hM
      apply hu
      rw [hM]
      by_cases h : R < ‖u‖ <;> simp [h]
    have hle : (fun u : ℂ => xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ (k + 1))
        ≤ (fun u : ℂ => (8/7 : ℝ) ^ (k + 1) *
          ((if R < ‖u‖ then xiAnnulusMass R R' u else 0) * (1 / ‖u‖) ^ (k + 1))) := by
      intro u
      show xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ (k + 1)
        ≤ (8/7 : ℝ) ^ (k + 1) *
          ((if R < ‖u‖ then xiAnnulusMass R R' u else 0) * (1 / ‖u‖) ^ (k + 1))
      by_cases h : R < ‖u‖
      · rw [if_pos h]
        have hM0 : 0 ≤ xiAnnulusMass R R' u := xiAnnulusMass_nonneg R R' u
        have hnorm : 7 * ‖u‖ / 8 ≤ ‖s - u‖ := by
          have h1 : ‖u‖ ≤ ‖s‖ + ‖s - u‖ := by
            have h2 := norm_add_le s (u - s)
            rw [add_sub_cancel] at h2
            rwa [norm_sub_rev u s] at h2
          have hs8 : ‖s‖ ≤ R / 8 := by linarith
          nlinarith [h, hs8, h1]
        have hrec : 1 / ‖s - u‖ ≤ (8/7) * (1 / ‖u‖) := by
          have hpos : 0 < 7 * ‖u‖ / 8 := by
            have hu0 : 0 < ‖u‖ := lt_of_le_of_lt (by linarith : (0:ℝ) ≤ R) h
            positivity
          calc 1 / ‖s - u‖ ≤ 1 / (7 * ‖u‖ / 8) := one_div_le_one_div_of_le hpos hnorm
            _ = (8/7) * (1 / ‖u‖) := by rw [one_div_div]; ring
        have hpu : (0:ℝ) ≤ 1 / ‖s - u‖ := by positivity
        have hpow := pow_le_pow_left₀ hpu hrec (k + 1)
        have hmul := mul_le_mul_of_nonneg_left hpow hM0
        calc xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ (k + 1)
            ≤ xiAnnulusMass R R' u * ((8/7) * (1 / ‖u‖)) ^ (k + 1) := hmul
          _ = (8/7 : ℝ) ^ (k + 1) * (xiAnnulusMass R R' u * (1 / ‖u‖) ^ (k + 1)) := by
              rw [mul_pow]; ring
      · rw [if_neg h]
        have hM0 : xiAnnulusMass R R' u = 0 := by
          unfold xiAnnulusMass
          exact if_neg h
        rw [hM0]
        simp
    calc (∑ᶠ u : ℂ, xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ (k + 1))
        ≤ ∑ᶠ u : ℂ, (8/7 : ℝ) ^ (k + 1) *
            ((if R < ‖u‖ then xiAnnulusMass R R' u else 0) * (1 / ‖u‖) ^ (k + 1)) :=
          finsum_le_finsum' hfin1 hfin2 hle
      _ = (8/7 : ℝ) ^ (k + 1) *
            (∑ᶠ u : ℂ, (if R < ‖u‖ then xiAnnulusMass R R' u else 0)
              * (1 / ‖u‖) ^ (k + 1)) := by
          rw [← mul_finsum' _ _ hfin_inner]
  have hcount : ∀ ρ : ℝ, 2 ≤ ρ →
      (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall (0 : ℂ) ρ) (xiAnnulusMass R R') u)
        ≤ c₀ * ρ * (Real.log (ρ + 2) + 2) := by
    intro ρ hρ
    simpa only [Work.LinnikAreas.DhK.xiL] using hcnt R R' hR2 hRR' ρ hρ
  have hdy := hdyad (xiAnnulusMass R R') (xiAnnulusMass_nonneg R R')
    (xiAnnulusMass_finiteSupport R R') hcount R hR2
  have hdy' : (∑ᶠ u : ℂ, (if R < ‖u‖ then xiAnnulusMass R R' u else 0)
        * (1 / ‖u‖) ^ (k + 1))
      ≤ C₁ * (Real.log (R + 2) + 2 + 1) / R := hdy
  have hX : Real.log (R + 2) + 2 + 1 ≤ (3/2) * (Real.log (R + 2) + 2) := by
    have hlog : 0 ≤ Real.log (R + 2) := Real.log_nonneg (by linarith)
    linarith
  calc ‖∑ᶠ u : ℂ, ((((MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi
          (Metric.closedBall 0 R') u -
          MeromorphicOn.divisor Work.LinnikAreas.DhK.Xi (Metric.closedBall 0 R) u) : ℤ) : ℂ) *
          (1 / (s - u)) ^ (k + 1))‖
      ≤ ∑ᶠ u : ℂ, xiAnnulusMass R R' u * (1 / ‖s - u‖) ^ (k + 1) := hkey
    _ ≤ (8/7 : ℝ) ^ (k + 1) *
        (∑ᶠ u : ℂ, (if R < ‖u‖ then xiAnnulusMass R R' u else 0)
          * (1 / ‖u‖) ^ (k + 1)) := hmono
    _ ≤ (8/7 : ℝ) ^ (k + 1) * (C₁ * (Real.log (R + 2) + 2 + 1) / R) :=
        mul_le_mul_of_nonneg_left hdy' (by positivity)
    _ ≤ (8/7 : ℝ) ^ (k + 1) * C₁ * (3/2) * Work.LinnikAreas.DhK.xiL R / R := by
        rw [Work.LinnikAreas.DhK.xiL]
        have hA : 0 ≤ (8/7 : ℝ) ^ (k + 1) * C₁ := by positivity
        have hRpos : 0 < R := by linarith
        have h1 : (8/7 : ℝ) ^ (k + 1) * C₁ * (Real.log (R + 2) + 2 + 1)
            ≤ (8/7 : ℝ) ^ (k + 1) * C₁ * ((3/2) * (Real.log (R + 2) + 2)) :=
          mul_le_mul_of_nonneg_left hX hA
        calc (8/7 : ℝ) ^ (k + 1) * (C₁ * (Real.log (R + 2) + 2 + 1) / R)
            = (8/7 : ℝ) ^ (k + 1) * C₁ * (Real.log (R + 2) + 2 + 1) / R := by ring
          _ ≤ (8/7 : ℝ) ^ (k + 1) * C₁ * ((3/2) * (Real.log (R + 2) + 2)) / R :=
              div_le_div_of_nonneg_right h1 (le_of_lt hRpos)
          _ = (8/7 : ℝ) ^ (k + 1) * C₁ * (3/2) * (Real.log (R + 2) + 2) / R := by ring

end Work.LinnikAreas.FarRepel
