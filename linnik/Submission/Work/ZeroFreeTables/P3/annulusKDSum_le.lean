/-
# ZeroFreeTables/P3/annulusKDSum_le — the annulus bound on the `K_D` sum

HB's partial-fraction expansion of `Λ'/Λ` writes the `k`-th derivative of `Λ'/Λ` as a sum over
*all* the zeros of `Λ` (with multiplicity) of `(-1)^k k! (1/(s-u))^{k+1}`.  Splitting that sum by
the two balls `closedBall 0 R` and `closedBall 0 R'` leaves the *annulus* contribution

  `K_D(s, R, R') = Σ_{R < ‖u‖ ≤ R'} mult(u) · (1/(s-u))^{k+1}`,

and the present lemma is the bound on it, uniform in `R' ≥ R`, that the engine consumes:

  `‖K_D(s,R,R')‖ ≤ C · L_N(N,R) / R`   (`8‖s‖ ≤ R ≤ R'`, `2 ≤ R`, `k ≥ 1`).

The point is that although the annulus is unbounded in `R'`, the sum *converges* uniformly in
`R'`: the zeros of `Λ` have density `O(log)`, so a shell at radius `ρ` contributes
`O(log ρ / ρ^{k+1})`, and `∫_R^∞ log ρ ρ^{-k-1} dρ = O(log R / R^k)` for `k ≥ 1`.  Formally the
proof is a dyadic decomposition:

* `annulusDivisor_norm_sum_le` replaces the complex sum by the real weighted mass sum
  `Σ_u annulusMass u · (1/‖s-u‖)^{k+1}`;
* `‖s-u‖ ≥ (7/8)‖u‖` on the annulus turns the `s`-dependent kernel into
  `(8/7)^{k+1} Σ_u annulusMass u · (1/‖u‖)^{k+1}`;
* `annulusMass_count_le` provides the ball-count bound `≤ c ρ (log(ρ+2) + log N + 2)` that
  `dyadicAnnulusKernel_le` converts into `C(log(R+2) + log N + 3)/R`;
* `3 log`-bookkeeping with `L_N N R = log(R+2) + log N + 2` finishes.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.Imports
import Submission.Work.ZeroFreeTables.P3.AnnulusDiffDefs
import Submission.Work.ZeroFreeTables.P3.dyadicAnnulusKernel_le
import Submission.Work.ZeroFreeTables.P3.annulusMass_count_le
import Submission.Work.ZeroFreeTables.P3.annulusDivisor_norm_sum_le

open scoped Classical BigOperators

namespace Work.ZeroFreeTables.P3

theorem annulusKDSum_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℂ) (R R' : ℝ), 2 ≤ R → R ≤ R' → 8 * ‖s‖ ≤ R →
      ‖∑ᶠ u : ℂ, ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R') u -
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R) u) : ℤ) : ℂ) * (1 / (s - u)) ^ (k + 1))‖
        ≤ C * (Commons.NumberTheory.Linnik.L_N N R) / R := by
  classical
  obtain ⟨c₀, hc₀, hcnt⟩ := annulusMass_count_le χ hχ hχprim
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)))
  have hLnn : 0 ≤ Real.log (N : ℝ) + 2 := by linarith
  obtain ⟨C₁, hC₁, hdyad⟩ :=
    dyadicAnnulusKernel_le (c := c₀) (L := Real.log (N : ℝ) + 2) (n := k + 1) hc₀ hLnn (by omega)
  refine ⟨(8/7 : ℝ) ^ (k + 1) * C₁ * (3/2), by positivity, ?_⟩
  intro s R R' hR hRR' hs
  have hkey : ‖∑ᶠ u : ℂ, ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R') u -
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R) u) : ℤ) : ℂ) * (1 / (s - u)) ^ (k + 1))‖
      ≤ ∑ᶠ u : ℂ, annulusMass χ R R' u * (1 / ‖s - u‖) ^ (k + 1) := by
    simpa only [annulusDivisor] using annulusDivisor_norm_sum_le χ hχ (k+1) s hRR'
  have hmono : (∑ᶠ u : ℂ, annulusMass χ R R' u * (1 / ‖s - u‖) ^ (k + 1))
      ≤ (8/7 : ℝ) ^ (k + 1) *
        (∑ᶠ u : ℂ, (if R < ‖u‖ then annulusMass χ R R' u else 0) * (1 / ‖u‖) ^ (k + 1)) := by
    have hfin_inner : Function.HasFiniteSupport
        (fun u : ℂ => (if R < ‖u‖ then annulusMass χ R R' u else 0) * (1 / ‖u‖) ^ (k + 1)) := by
      refine (annulusMass_finiteSupport χ hχ R R').subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hM
      apply hu
      rw [hM]
      by_cases h : R < ‖u‖ <;> simp [h]
    have hfin1 : Function.HasFiniteSupport
        (fun u : ℂ => annulusMass χ R R' u * (1 / ‖s - u‖) ^ (k + 1)) := by
      refine (annulusMass_finiteSupport χ hχ R R').subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hM
      exact hu (by rw [hM, zero_mul])
    have hfin2 : Function.HasFiniteSupport
        (fun u : ℂ => (8/7 : ℝ) ^ (k + 1) *
          ((if R < ‖u‖ then annulusMass χ R R' u else 0) * (1 / ‖u‖) ^ (k + 1))) := by
      refine (annulusMass_finiteSupport χ hχ R R').subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro hM
      apply hu
      rw [hM]
      by_cases h : R < ‖u‖ <;> simp [h]
    have hle : (fun u : ℂ => annulusMass χ R R' u * (1 / ‖s - u‖) ^ (k + 1))
        ≤ (fun u : ℂ => (8/7 : ℝ) ^ (k + 1) *
          ((if R < ‖u‖ then annulusMass χ R R' u else 0) * (1 / ‖u‖) ^ (k + 1))) := by
      intro u
      show annulusMass χ R R' u * (1 / ‖s - u‖) ^ (k + 1)
        ≤ (8/7 : ℝ) ^ (k + 1) *
          ((if R < ‖u‖ then annulusMass χ R R' u else 0) * (1 / ‖u‖) ^ (k + 1))
      by_cases h : R < ‖u‖
      · rw [if_pos h]
        have hM0 : 0 ≤ annulusMass χ R R' u := annulusMass_nonneg χ hχ R R' u
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
        calc annulusMass χ R R' u * (1 / ‖s - u‖) ^ (k + 1)
            ≤ annulusMass χ R R' u * ((8/7) * (1 / ‖u‖)) ^ (k + 1) := hmul
          _ = (8/7 : ℝ) ^ (k + 1) * (annulusMass χ R R' u * (1 / ‖u‖) ^ (k + 1)) := by
              rw [mul_pow]; ring
      · rw [if_neg h]
        have hM0 : annulusMass χ R R' u = 0 := by
          unfold annulusMass
          exact if_neg h
        rw [hM0]
        simp
    calc (∑ᶠ u : ℂ, annulusMass χ R R' u * (1 / ‖s - u‖) ^ (k + 1))
        ≤ ∑ᶠ u : ℂ, (8/7 : ℝ) ^ (k + 1) *
            ((if R < ‖u‖ then annulusMass χ R R' u else 0) * (1 / ‖u‖) ^ (k + 1)) :=
          finsum_le_finsum' hfin1 hfin2 hle
      _ = (8/7 : ℝ) ^ (k + 1) *
            (∑ᶠ u : ℂ, (if R < ‖u‖ then annulusMass χ R R' u else 0) * (1 / ‖u‖) ^ (k + 1)) := by
          rw [← mul_finsum' _ _ hfin_inner]
  have hcount : ∀ ρ : ℝ, 2 ≤ ρ →
      (∑ᶠ u : ℂ, Set.indicator (Metric.closedBall (0 : ℂ) ρ) (annulusMass χ R R') u)
        ≤ c₀ * ρ * (Real.log (ρ + 2) + (Real.log (N : ℝ) + 2)) := by
    intro ρ hρ
    have h := hcnt R R' hR hRR' ρ hρ
    have he : Real.log (ρ + 2) + (Real.log (N : ℝ) + 2)
        = Real.log (ρ + 2) + Real.log (N : ℝ) + 2 := by ring
    rwa [he]
  have hdy := hdyad (annulusMass χ R R') (annulusMass_nonneg χ hχ R R')
    (annulusMass_finiteSupport χ hχ R R') hcount R hR
  have hdy' : (∑ᶠ u : ℂ, (if R < ‖u‖ then annulusMass χ R R' u else 0) * (1 / ‖u‖) ^ (k + 1))
      ≤ C₁ * (Real.log (R + 2) + Real.log (N : ℝ) + 3) / R := by
    have he : C₁ * (Real.log (R + 2) + (Real.log (N : ℝ) + 2) + 1) / R
        = C₁ * (Real.log (R + 2) + Real.log (N : ℝ) + 3) / R := by ring
    rwa [he] at hdy
  have hL2 : 2 ≤ Commons.NumberTheory.Linnik.L_N N R :=
    Commons.NumberTheory.Linnik.pf_L_ge_two (N := N) (A := R) (by linarith)
  have hLN : Commons.NumberTheory.Linnik.L_N N R
      = Real.log (R + 2) + Real.log (N : ℝ) + 2 := rfl
  have hX : Real.log (R + 2) + Real.log (N : ℝ) + 3
      ≤ (3/2) * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by
    rw [hLN] at hL2
    linarith
  calc ‖∑ᶠ u : ℂ, ((((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R') u -
            MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 R) u) : ℤ) : ℂ) * (1 / (s - u)) ^ (k + 1))‖
      ≤ ∑ᶠ u : ℂ, annulusMass χ R R' u * (1 / ‖s - u‖) ^ (k + 1) := hkey
    _ ≤ (8/7 : ℝ) ^ (k + 1) *
        (∑ᶠ u : ℂ, (if R < ‖u‖ then annulusMass χ R R' u else 0) * (1 / ‖u‖) ^ (k + 1)) := hmono
    _ ≤ (8/7 : ℝ) ^ (k + 1) * (C₁ * (Real.log (R + 2) + Real.log (N : ℝ) + 3) / R) :=
        mul_le_mul_of_nonneg_left hdy' (by positivity)
    _ ≤ (8/7 : ℝ) ^ (k + 1) * C₁ * (3/2) * Commons.NumberTheory.Linnik.L_N N R / R := by
        rw [hLN]
        have hstep : (8/7 : ℝ) ^ (k + 1) * (C₁ * (Real.log (R + 2) + Real.log (N : ℝ) + 3) / R)
            = (8/7 : ℝ) ^ (k + 1) * C₁ * (Real.log (R + 2) + Real.log (N : ℝ) + 3) / R := by
          ring
        rw [hstep]
        have hA : 0 ≤ (8/7 : ℝ) ^ (k + 1) * C₁ := by positivity
        have hRpos : 0 < R := by linarith
        have h1 : (8/7 : ℝ) ^ (k + 1) * C₁ * (Real.log (R + 2) + Real.log (N : ℝ) + 3)
            ≤ (8/7 : ℝ) ^ (k + 1) * C₁ *
              ((3/2) * (Real.log (R + 2) + Real.log (N : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hX hA
        calc (8/7 : ℝ) ^ (k + 1) * C₁ * (Real.log (R + 2) + Real.log (N : ℝ) + 3) / R
            ≤ (8/7 : ℝ) ^ (k + 1) * C₁ *
                ((3/2) * (Real.log (R + 2) + Real.log (N : ℝ) + 2)) / R :=
              div_le_div_of_nonneg_right h1 (le_of_lt hRpos)
          _ = (8/7 : ℝ) ^ (k + 1) * C₁ * (3/2) * (Real.log (R + 2) + Real.log (N : ℝ) + 2) / R := by
              ring

end Work.ZeroFreeTables.P3
