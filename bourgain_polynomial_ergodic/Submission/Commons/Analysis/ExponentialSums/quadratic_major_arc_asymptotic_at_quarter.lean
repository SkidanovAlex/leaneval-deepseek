import Mathlib
import Submission.Commons.Analysis.ExponentialSums.quadratic_major_arc_asymptotic

namespace Commons.Analysis.ExponentialSums

open Finset MeasureTheory intervalIntegral Filter
open scoped BigOperators Real

set_option maxHeartbeats 1000000

/-- Major-arc asymptotic for the quadratic Weyl sum, specialized to the dyadic cutoff
`q ≤ N^{1/4}`: the normalized sum `(1/N) ∑_{n<N} e((a/q+b) n²)` is the product of the
residue factor `q⁻¹ ∑_{r<q} e(a r²/q)` and the oscillatory integral `∫_0^1 e(b N² s²) ds`,
up to `O(N^{-θ})`.

This is the specialization `δ = 1/4`, `θ = 1/8`, `C = 10^6` of the general
`Commons.Analysis.ExponentialSums.quadratic_major_arc_asymptotic`. -/
theorem quadratic_major_arc_asymptotic_at_quarter :
    ∃ θ : ℝ, 0 < θ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (a : ℤ) (q : ℕ) (b : ℝ), 1 ≤ N → 0 < q → (q : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) →
        Int.gcd a (q : ℤ) = 1 → |b| ≤ ((N : ℝ) ^ (1 + (1 : ℝ) / 4))⁻¹ →
        ‖(N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
            Complex.exp (2 * Real.pi * Complex.I *
              ((((a : ℝ) / (q : ℝ) + b) * (n : ℝ) ^ 2 : ℝ) : ℂ))
          - ((q : ℂ)⁻¹ * ∑ r ∈ Finset.range q,
              Complex.exp (2 * Real.pi * Complex.I * ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) : ℝ)))
            * (∫ s in (0 : ℝ)..1,
                Complex.exp (2 * Real.pi * Complex.I * ((b * (N : ℝ) ^ 2 * s ^ 2 : ℝ) : ℂ)))‖
        ≤ C * ((N : ℝ) ^ θ)⁻¹ := by
  refine ⟨1/8, by norm_num, 10^6, by norm_num, ?_⟩
  intro N a q b hN hq hqN hgcd hb
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqN' : (q:ℝ) ≤ (N:ℝ) := by
    calc (q:ℝ) ≤ (N:ℝ)^((1:ℝ)/4) := hqN
      _ ≤ (N:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = (N:ℝ) := Real.rpow_one _
  have hqN'' : q ≤ N := by exact_mod_cast hqN'
  -- exponent facts
  have hb5 : |b| ≤ (N:ℝ)^(-((5:ℝ)/4)) := by
    have h : (1:ℝ) + 1/4 = 5/4 := by norm_num
    rw [h] at hb
    have heq : (((N:ℝ)^((5:ℝ)/4))⁻¹) = (N:ℝ)^(-((5:ℝ)/4)) :=
      (Real.rpow_neg hNpos.le ((5:ℝ)/4)).symm
    rwa [heq] at hb
  have hbq : |b| * (q:ℝ) ≤ (N:ℝ)^(-(1:ℝ)) := by
    calc |b| * (q:ℝ) ≤ (N:ℝ)^(-((5:ℝ)/4)) * (N:ℝ)^((1:ℝ)/4) :=
          mul_le_mul hb5 hqN (by positivity) (by positivity)
      _ = (N:ℝ)^(-((5:ℝ)/4) + (1:ℝ)/4) := (Real.rpow_add hNpos _ _).symm
      _ = (N:ℝ)^(-(1:ℝ)) := by norm_num
  have hbs : |b| * Real.sqrt |b| ≤ (N:ℝ)^(-((15:ℝ)/8)) := by
    have hs : Real.sqrt |b| ≤ (N:ℝ)^(-((5:ℝ)/8)) := by
      calc Real.sqrt |b| ≤ Real.sqrt ((N:ℝ)^(-((5:ℝ)/4))) := Real.sqrt_le_sqrt hb5
        _ = ((N:ℝ)^(-((5:ℝ)/4)))^((1:ℝ)/2) := Real.sqrt_eq_rpow _
        _ = (N:ℝ)^(-((5:ℝ)/4) * ((1:ℝ)/2)) := (Real.rpow_mul hNpos.le _ _).symm
        _ = (N:ℝ)^(-((5:ℝ)/8)) := by norm_num
    calc |b| * Real.sqrt |b| ≤ (N:ℝ)^(-((5:ℝ)/4)) * (N:ℝ)^(-((5:ℝ)/8)) :=
          mul_le_mul hb5 hs (Real.sqrt_nonneg _) (by positivity)
      _ = (N:ℝ)^(-((5:ℝ)/4) + -((5:ℝ)/8)) := (Real.rpow_add hNpos _ _).symm
      _ = (N:ℝ)^(-((15:ℝ)/8)) := by norm_num
  -- main objects
  set S : ℂ := ∑ n ∈ Finset.range N, expTwoPiI (((a:ℝ)/(q:ℝ) + b) * (n:ℝ)^2) with hS
  set G : ℂ := ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) with hG
  set Iv : ℂ := ∫ t in (0:ℝ)..(N:ℝ), expTwoPiI (b * t^2) with hIv
  set v : ℂ := ∫ s in (0:ℝ)..1, expTwoPiI (b * (N:ℝ)^2 * s^2) with hvdef
  -- integral substitution
  have hv : v = (N:ℝ)⁻¹ * Iv := by
    have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNpos
    rw [hvdef, hIv]
    rw [show (∫ s in (0:ℝ)..1, expTwoPiI (b * (N:ℝ)^2 * s^2))
          = ∫ s in (0:ℝ)..1, (fun t : ℝ => expTwoPiI (b * t^2)) ((N:ℝ) * s) from by
        apply intervalIntegral.integral_congr
        intro s _
        simp only []
        rw [show b * (N:ℝ)^2 * s^2 = b * ((N:ℝ) * s)^2 by ring]]
    rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => expTwoPiI (b * t^2)) hNne]
    simp
  -- residue factorisation
  have hfac : S = ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
      ∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2) := by
    rw [hS]
    exact residue_factor_expTwoPiI N q hq a b
  -- change the goal into `S,G,Iv,v` form
  have hSform : (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * ((((a : ℝ) / (q : ℝ) + b) * (n : ℝ) ^ 2 : ℝ) : ℂ))) = S := by
    rw [hS]; simp only [expTwoPiI_def]
  have hGform : (∑ r ∈ Finset.range q,
        Complex.exp (2 * Real.pi * Complex.I * ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) : ℝ))) = G := by
    rw [hG]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    show expTwoPiI ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ)) = expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2)
    congr 1
    ring
  have hvform : (∫ s in (0 : ℝ)..1,
        Complex.exp (2 * Real.pi * Complex.I * ((b * (N : ℝ) ^ 2 * s ^ 2 : ℝ) : ℂ))) = v := by
    rw [hvdef]; simp only [expTwoPiI_def]
  rw [hSform, hGform, hvform, hv]
  -- per-residue block bound
  have hcont_f : Continuous (fun u : ℝ => expTwoPiI (b * u^2)) := by
    simp only [expTwoPiI_def]; fun_prop
  have hblock : ∀ r ∈ Finset.range q,
      ‖(N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q),
            expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
        - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv)‖
      ≤ (N:ℝ)⁻¹ * (22 + 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2) := by
    intro r hr
    have hrq : r < q := Finset.mem_range.mp hr
    have hr0 : (0:ℝ) ≤ (r:ℝ) := by positivity
    have hrq' : (r:ℝ) < (q:ℝ) := by exact_mod_cast hrq
    obtain ⟨hPr1, hPr2, hPr3⟩ := div_block_bounds hq hrq hqN''
    set Pr : ℕ := (N + q - 1 - r) / q with hPrdef
    -- key bounds on `q * Pr + r`
    have hPr2' : (q:ℝ) * (Pr:ℝ) + (r:ℝ) ≤ (N:ℝ) + (q:ℝ) := by
      have h1 : Pr * q ≤ N + q - 1 - r := by rw [hPrdef]; exact Nat.div_mul_le_self _ _
      have hcast : ((Pr * q : ℕ) : ℝ) ≤ ((N + q - 1 - r : ℕ) : ℝ) := by exact_mod_cast h1
      have h2 : ((N + q - 1 - r : ℕ) : ℝ) = (N:ℝ) + (q:ℝ) - 1 - (r:ℝ) := by
        have hle1 : 1 + r ≤ N + q := by omega
        rw [show N + q - 1 - r = (N + q) - (1 + r) by omega, Nat.cast_sub hle1]
        push_cast; ring
      rw [Nat.cast_mul, h2] at hcast
      linarith
    have hY : (q:ℝ) * (Pr:ℝ) + (r:ℝ) ≤ 3 * (N:ℝ) := by
      nlinarith [hPr2', hqN', hN1]
    have hYabs : |(q:ℝ) * (Pr:ℝ) + (r:ℝ) - (N:ℝ)| ≤ (q:ℝ) := by
      have hR : (N:ℝ) - (q:ℝ) ≤ (q:ℝ) * (Pr:ℝ) + (r:ℝ) := by linarith [hPr3, hr0]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hβ4 : |b| * (q:ℝ) * ((q:ℝ) * (Pr:ℝ) + (r:ℝ)) ≤ 4 := by
      have h1 : |b| * (q:ℝ) * ((q:ℝ) * (Pr:ℝ) + (r:ℝ)) ≤ (N:ℝ)^(-(1:ℝ)) * (3 * (N:ℝ)) :=
        mul_le_mul hbq hY (by positivity) (by positivity)
      have h2 : (N:ℝ)^(-(1:ℝ)) * (3 * (N:ℝ)) = 3 := by
        rw [show (N:ℝ)^(-(1:ℝ)) * (3 * (N:ℝ)) = 3 * ((N:ℝ)^(-(1:ℝ)) * (N:ℝ)^(1:ℝ)) from by
              rw [Real.rpow_one]; ring,
            ← Real.rpow_add hNpos, show (-(1:ℝ) + 1) = 0 by ring, Real.rpow_zero]
        ring
      linarith [h1, h2]
    -- the block bound
    have hC1 : ‖(∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
        - ∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2)‖
        ≤ 20 + 2000 * |b| * Real.sqrt |b| * (q:ℝ) * ((q:ℝ) * (Pr:ℝ) + (r:ℝ))^2 := by
      rw [show (∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
            = ∑ p ∈ Finset.range Pr, expTwoPiI (b * (q * (p:ℝ) + r)^2) from by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [show (((p*q+r:ℕ):ℝ)) = q * (p:ℝ) + r by push_cast; ring]]
      exact block_bound b hq0 hr0 Pr hPr1 hβ4
    -- the endpoint discrepancy
    have hC2 : ‖(∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2)) - (q:ℂ)⁻¹ * Iv‖ ≤ 2 := by
      have hsub : (∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2))
          = (q:ℂ)⁻¹ * (∫ u in (r:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2)) := by
        rw [show (∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2))
              = ∫ s in (0:ℝ)..(Pr:ℝ), (fun u : ℝ => expTwoPiI (b * u^2)) ((q:ℝ) * s + (r:ℝ)) from by
            apply intervalIntegral.integral_congr
            intro s _
            rfl]
        rw [intervalIntegral.integral_comp_mul_add (fun u : ℝ => expTwoPiI (b * u^2)) (ne_of_gt hq0) (r:ℝ)]
        rw [show ((q:ℝ) * 0 + (r:ℝ)) = (r:ℝ) by ring]
        rw [Complex.real_smul]
        rw [show (((q:ℝ)⁻¹ : ℝ) : ℂ) = (q:ℂ)⁻¹ from by
          rw [Complex.ofReal_inv, Complex.ofReal_natCast]]
      have hsub2 : (q:ℂ)⁻¹ * (∫ u in (r:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2)) - (q:ℂ)⁻¹ * Iv
          = (q:ℂ)⁻¹ * ((∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
              - (∫ u in (0:ℝ)..(N:ℝ), expTwoPiI (b * u^2))
              - (∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2))) := by
        rw [hIv]
        rw [show (∫ u in (r:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
              = (∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
                - (∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2)) from
          (intervalIntegral.integral_interval_sub_left
            (hcont_f.intervalIntegrable _ _) (hcont_f.intervalIntegrable _ _)).symm]
        ring
      rw [hsub, hsub2, norm_mul]
      rw [show ‖((q:ℂ))⁻¹‖ = (q:ℝ)⁻¹ from by
        have heq : (q:ℂ)⁻¹ = (((q:ℝ)⁻¹ : ℝ) : ℂ) := by
          rw [Complex.ofReal_inv, Complex.ofReal_natCast]
        rw [heq, show ‖(((q:ℝ)⁻¹ : ℝ) : ℂ)‖ = |(q:ℝ)⁻¹| from RCLike.norm_ofReal _,
            abs_of_nonneg (by positivity)]]
      have hlen1 : ‖(∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
            - (∫ u in (0:ℝ)..(N:ℝ), expTwoPiI (b * u^2))‖
          ≤ |(q:ℝ) * (Pr:ℝ) + (r:ℝ) - (N:ℝ)| := by
        rw [intervalIntegral.integral_interval_sub_left
              (hcont_f.intervalIntegrable _ _) (hcont_f.intervalIntegrable _ _)]
        calc ‖∫ u in (N:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2)‖
            ≤ 1 * |(q:ℝ) * (Pr:ℝ) + (r:ℝ) - (N:ℝ)| :=
              intervalIntegral.norm_integral_le_of_norm_le_const
                (fun u hu => by rw [norm_expTwoPiI])
          _ = |(q:ℝ) * (Pr:ℝ) + (r:ℝ) - (N:ℝ)| := by ring
      have hlen2 : ‖(∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2))‖ ≤ (r:ℝ) := by
        calc ‖∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2)‖
            ≤ 1 * |(r:ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const
              (fun u hu => by rw [norm_expTwoPiI])
          _ = (r:ℝ) := by rw [sub_zero, abs_of_nonneg hr0, one_mul]
      have hmain2 : ‖(∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
            - (∫ u in (0:ℝ)..(N:ℝ), expTwoPiI (b * u^2))
            - (∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2))‖ ≤ 2 * (q:ℝ) := by
        have h := norm_sub_le
          ((∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2)) - (∫ u in (0:ℝ)..(N:ℝ), expTwoPiI (b * u^2)))
          (∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2))
        linarith [h, hlen1, hlen2, hYabs]
      calc (q:ℝ)⁻¹ * ‖(∫ u in (0:ℝ)..((q:ℝ) * (Pr:ℝ) + (r:ℝ)), expTwoPiI (b * u^2))
              - (∫ u in (0:ℝ)..(N:ℝ), expTwoPiI (b * u^2))
              - (∫ u in (0:ℝ)..(r:ℝ), expTwoPiI (b * u^2))‖
          ≤ (q:ℝ)⁻¹ * (2 * (q:ℝ)) := mul_le_mul_of_nonneg_left hmain2 (by positivity)
        _ = 2 := by field_simp
    -- combine
    have hfac2 : (N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
        - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv)
        = (N:ℝ)⁻¹ * ((∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
            - (q:ℂ)⁻¹ * Iv) := by
      rw [hPrdef]; ring
    rw [hfac2, norm_mul]
    rw [show ‖(((N:ℝ)⁻¹ : ℝ) : ℂ)‖ = (N:ℝ)⁻¹ from by
      rw [show ‖(((N:ℝ)⁻¹ : ℝ) : ℂ)‖ = |(N:ℝ)⁻¹| from RCLike.norm_ofReal _,
          abs_of_nonneg (by positivity)]]
    have hmain3 : ‖(∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
        - (q:ℂ)⁻¹ * Iv‖ ≤ 22 + 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2 := by
      have hsplit : (∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2)) - (q:ℂ)⁻¹ * Iv
          = ((∑ p ∈ Finset.range Pr, expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
              - ∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2))
            + ((∫ s in (0:ℝ)..(Pr:ℝ), expTwoPiI (b * (q * s + r)^2)) - (q:ℂ)⁻¹ * Iv) := by
        ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      have hY2 : ((q:ℝ) * (Pr:ℝ) + (r:ℝ))^2 ≤ (3 * (N:ℝ))^2 := by
        have h1 : 0 ≤ (q:ℝ) * (Pr:ℝ) + (r:ℝ) := by positivity
        nlinarith [hY, h1]
      have hfin : 2000 * |b| * Real.sqrt |b| * (q:ℝ) * ((q:ℝ) * (Pr:ℝ) + (r:ℝ))^2
          ≤ 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2 := by
        have h0 : 0 ≤ |b| * Real.sqrt |b| * (q:ℝ) := by positivity
        nlinarith [hY2, h0]
      linarith [hC1, hC2, hfin]
    exact mul_le_mul_of_nonneg_left hmain3 (by positivity)
  -- rewrite the goal into the summed form
  have e1 : (N:ℝ)⁻¹ * S
      = ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
          ((N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))) := by
    rw [hfac, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    ring
  have e2 : (q:ℂ)⁻¹ * G * ((N:ℝ)⁻¹ * Iv)
      = ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
          ((q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv)) := by
    rw [hG, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    ring
  have hfac3 : (N:ℝ)⁻¹ * S - (q:ℂ)⁻¹ * G * ((N:ℝ)⁻¹ * Iv)
      = ∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
          ((N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
            - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv)) := by
    rw [e1, e2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    ring
  rw [hfac3]
  -- sum over residues
  have hsum : ‖∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
        ((N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
          - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv))‖
      ≤ 22 * (N:ℝ)^(-((3:ℝ)/4)) + 18000 * (N:ℝ)^(-((3:ℝ)/8)) := by
    calc ‖∑ r ∈ Finset.range q, expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
          ((N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
            - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv))‖
        ≤ ∑ r ∈ Finset.range q, ‖expTwoPiI ((a:ℝ)/(q:ℝ) * (r:ℝ)^2) *
          ((N:ℝ)⁻¹ * (∑ p ∈ Finset.range ((N + q - 1 - r) / q), expTwoPiI (b * (((p*q+r:ℕ):ℝ))^2))
            - (q:ℂ)⁻¹ * ((N:ℝ)⁻¹ * Iv))‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ Finset.range q, (N:ℝ)⁻¹ * (22 + 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2) := by
          refine Finset.sum_le_sum (fun r hr => ?_)
          rw [norm_mul, norm_expTwoPiI, one_mul]
          exact hblock r hr
      _ = (q:ℝ) * ((N:ℝ)⁻¹ * (22 + 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 22 * (N:ℝ)^(-((3:ℝ)/4)) + 18000 * (N:ℝ)^(-((3:ℝ)/8)) := by
          have h1 : (q:ℝ) * (N:ℝ)⁻¹ ≤ (N:ℝ)^(-((3:ℝ)/4)) := by
            calc (q:ℝ) * (N:ℝ)⁻¹ ≤ (N:ℝ)^((1:ℝ)/4) * (N:ℝ)⁻¹ :=
                  mul_le_mul_of_nonneg_right hqN (by positivity)
              _ = (N:ℝ)^((1:ℝ)/4) * (N:ℝ)^(-(1:ℝ)) := by rw [← Real.rpow_neg_one]
              _ = (N:ℝ)^((1:ℝ)/4 + -(1:ℝ)) := (Real.rpow_add hNpos _ _).symm
              _ = (N:ℝ)^(-((3:ℝ)/4)) := by norm_num
          have h2 : |b| * Real.sqrt |b| * (q:ℝ)^2 * (N:ℝ) ≤ (N:ℝ)^(-((3:ℝ)/8)) := by
            have hq2 : (q:ℝ)^2 ≤ (N:ℝ)^((1:ℝ)/2) := by
              have h := mul_self_le_mul_self hq0.le hqN
              have h2' : ((N:ℝ)^((1:ℝ)/4)) * ((N:ℝ)^((1:ℝ)/4)) = (N:ℝ)^((1:ℝ)/2) := by
                rw [← Real.rpow_add hNpos, show ((1:ℝ)/4 + (1:ℝ)/4) = (1:ℝ)/2 by norm_num]
              calc (q:ℝ)^2 = (q:ℝ) * (q:ℝ) := by ring
                _ ≤ ((N:ℝ)^((1:ℝ)/4)) * ((N:ℝ)^((1:ℝ)/4)) := h
                _ = (N:ℝ)^((1:ℝ)/2) := h2'
            have h3 : |b| * Real.sqrt |b| * (q:ℝ)^2 * (N:ℝ)
                ≤ (N:ℝ)^(-((15:ℝ)/8)) * ((N:ℝ)^((1:ℝ)/2) * (N:ℝ)^(1:ℝ)) := by
              have h0q : 0 ≤ (q:ℝ)^2 := sq_nonneg _
              have h0N : 0 ≤ (N:ℝ) := hNpos.le
              have hmul := mul_le_mul hbs hq2 h0q (by positivity : (0:ℝ) ≤ (N:ℝ)^(-((15:ℝ)/8)))
              have hmul2 : |b| * Real.sqrt |b| * (q:ℝ)^2 * (N:ℝ)
                  ≤ ((N:ℝ)^(-((15:ℝ)/8)) * (N:ℝ)^((1:ℝ)/2)) * (N:ℝ) :=
                mul_le_mul_of_nonneg_right hmul h0N
              have key : ((N:ℝ)^(-((15:ℝ)/8)) * (N:ℝ)^((1:ℝ)/2)) * (N:ℝ)
                  = (N:ℝ)^(-((15:ℝ)/8)) * ((N:ℝ)^((1:ℝ)/2) * (N:ℝ)^(1:ℝ)) := by
                rw [mul_assoc]
                congr 1
                congr 1
                exact (Real.rpow_one _).symm
              calc |b| * Real.sqrt |b| * (q:ℝ)^2 * (N:ℝ)
                  ≤ ((N:ℝ)^(-((15:ℝ)/8)) * (N:ℝ)^((1:ℝ)/2)) * (N:ℝ) := hmul2
                _ = (N:ℝ)^(-((15:ℝ)/8)) * ((N:ℝ)^((1:ℝ)/2) * (N:ℝ)^(1:ℝ)) := key
            have h4 : (N:ℝ)^(-((15:ℝ)/8)) * ((N:ℝ)^((1:ℝ)/2) * (N:ℝ)^(1:ℝ)) = (N:ℝ)^(-((3:ℝ)/8)) := by
              rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
              congr 1
              ring
            linarith [h3, h4]
          have e : (q:ℝ) * ((N:ℝ)⁻¹ * (22 + 18000 * |b| * Real.sqrt |b| * (q:ℝ) * (N:ℝ)^2))
              = 22 * ((q:ℝ) * (N:ℝ)⁻¹) + 18000 * (|b| * Real.sqrt |b| * (q:ℝ)^2 * (N:ℝ)) := by
            field_simp
          rw [e]
          linarith [h1, h2]
  -- final numeric bound
  refine le_trans hsum ?_
  rw [show 10^6 * ((N:ℝ)^((1:ℝ)/8))⁻¹ = 10^6 * (N:ℝ)^(-((1:ℝ)/8)) from by
    rw [(Real.rpow_neg hNpos.le ((1:ℝ)/8)).symm]]
  have hA : (N:ℝ)^(-((3:ℝ)/4)) = (N:ℝ)^(-((5:ℝ)/8)) * (N:ℝ)^(-((1:ℝ)/8)) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hB : (N:ℝ)^(-((3:ℝ)/8)) = (N:ℝ)^(-((1:ℝ)/4)) * (N:ℝ)^(-((1:ℝ)/8)) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hP : (N:ℝ)^(-((1:ℝ)/8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hQ : (N:ℝ)^(-((1:ℝ)/4)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hR : (N:ℝ)^(-((5:ℝ)/8)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hP0 : 0 < (N:ℝ)^(-((1:ℝ)/8)) := Real.rpow_pos_of_pos hNpos _
  rw [hA, hB]
  nlinarith [hP, hQ, hR, hP0]

end Commons.Analysis.ExponentialSums
