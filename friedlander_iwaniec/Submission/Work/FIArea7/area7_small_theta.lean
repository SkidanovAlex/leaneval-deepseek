import Mathlib
import Submission.Work.FIArea7.Bridge17Defs
import Submission.Work.FIArea7.UniCut6
import Submission.Work.FIArea7.area7_bound_polylog
import Submission.Work.FIArea7.isBetaCoeff6_mass_caps
import Submission.Work.FIArea7.smallTheta_tau_sum_bound
import Submission.Work.FIArea7.smallTheta_log_bound

namespace Work.FIArea7

open Finset
open scoped BigOperators

set_option autoImplicit false
attribute [local instance] Classical.propDecidable
noncomputable section

/-- The cutoff (4.11) is at least one: `log x ≥ log 3 ≥ 1` and `log x > 1` make the power
`(log x)^{A+124}` at least `(log x)^0 = 1`. -/
lemma one_le_tau (Pa : Work.FITop.Params) : 1 ≤ Pa.τ := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hl3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
    linarith [Real.exp_one_lt_three]
  have hl : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := le_trans hl3 (Real.log_le_log (by norm_num) hx3)
  have h0 : (0 : ℝ) ≤ Pa.A + 124 := by linarith [Pa.hA]
  calc (1 : ℝ) = (Real.log (Pa.x : ℝ)) ^ (0 : ℝ) := by rw [Real.rpow_zero]
    _ ≤ (Real.log (Pa.x : ℝ)) ^ (Pa.A + 124) := Real.rpow_le_rpow_of_exponent_le hl h0
    _ ≤ Pa.τ := Pa.hτ1

/-- `log x ≥ log 3 ≥ 1`. -/
lemma one_le_log_x (Pa : Work.FITop.Params) : (1 : ℝ) ≤ Real.log (Pa.x : ℝ) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hl3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
    linarith [Real.exp_one_lt_three]
  exact le_trans hl3 (Real.log_le_log (by norm_num) hx3)

/-- `θ = (log x)^{-A'} ≤ 1` (4.15). -/
lemma theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  have hl := one_le_log_x Pa
  have hA'0 : (0 : ℝ) ≤ Pa.A' := by
    have h20 : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ) := by norm_num
    linarith [Pa.hA, Pa.hA']
  calc Pa.θ = (Real.log (Pa.x : ℝ)) ^ (-Pa.A') := Pa.hθ
    _ = ((Real.log (Pa.x : ℝ)) ^ Pa.A')⁻¹ := Real.rpow_neg (by linarith) _
    _ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hl hA'0)

/-- Every value of a non-zero round-6 coefficient is of modulus at most `Pa.τ` (5.9) — the
`τ(n) ≤ Pa.τ` clause of the support together with the pointwise bound `‖β z‖ ≤ τ(|z|²)`. -/
lemma IsBetaCoeff6.norm_le_tau {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (z : GaussianInt) :
    ‖β z‖ ≤ Pa.τ := by
  by_cases hz : β z = 0
  · rw [hz, norm_zero]
    exact le_trans zero_le_one (one_le_tau Pa)
  · have hp := isBetaCoeff6_toIsPolarCoeff h
    exact (hp.2 z).trans (hp.tau_le hz)

/-- **The `ℓ¹`-mass of a round-6 coefficient.**  `Σ_{|z|² ≲ N}‖β z‖ ≤ Pa.τ·200(θ²N + θ√N + 1)`:
at most `200(θ²N+θ√N+1)` coefficients are non-zero, and each is of modulus at most `Pa.τ`. -/
lemma sum_norm_beta_le (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ)
    (h : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖
      ≤ Pa.τ * (200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)) := by
  have hp := isBetaCoeff6_toIsPolarCoeff h
  have hτ0 : (0 : ℝ) ≤ Pa.τ := le_trans zero_le_one (one_le_tau Pa)
  have hcard : (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter
      (fun z => β z ≠ 0)).card : ℝ)
      ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) :=
    IsPolarCoeff.card_support_le Pa φ β hp
  have hsum : ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖
      = ∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => β z ≠ 0), ‖β z‖ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases hz : β z = 0 <;> simp [hz]
  rw [hsum]
  calc ∑ z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => β z ≠ 0), ‖β z‖
      ≤ ∑ _z ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => β z ≠ 0), Pa.τ :=
        Finset.sum_le_sum (fun z _ => IsBetaCoeff6.norm_le_tau h z)
    _ = (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => β z ≠ 0)).card : ℝ) * Pa.τ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)) * Pa.τ :=
        mul_le_mul_of_nonneg_right hcard hτ0
    _ = Pa.τ * (200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)) := by ring

/-- **A1: the trivial regime** (`AREA7_ROUTE_LEAD.md` §2.2 (A1)) — needed only to know that
`modeLen` is polylogarithmic in every case where it is used, i.e. in the complement of the range of
this lemma.  (It is redundant if `Pa.θ` is also pinned to `thetaOf Pa.x Asave`, which the
composition supplies.)

Proof: (1) `|W+B| ≤ 2(X+1)log(16N)(Σ|β|)²`: at most `X` complementary divisors `e < X` contribute
(`Work.FIArea7.card_cut_le`), `φ(d)/d ≤ 1` and `|logFac6| ≤ log 16N`; (2) `Σ|β| ≤ Pa.τ·200(θ²N+θ√N+1)`
by the support cap `Work.FIArea7.isBetaCoeff6_mass_caps` together with `|γ| ≤ τ(n) ≤ Pa.τ`.  The two
side hypotheses give `τ ≤ N/X` and `τθ√N ≤ N/X²`, hence `Σ|β| ≤ 600N/X`. -/
theorem area7_small_theta : ∃ C : ℝ, 0 < C ∧
  ∀ {Pa : Work.FITop.Params} {X : ℕ} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
    Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X →
    Pa.θ ^ 2 * Pa.τ * X ≤ 1 → Pa.τ * (X:ℝ) ^ 2 ≤ Pa.N →
    ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖
      ≤ C * (X:ℝ)⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2) := by
  refine ⟨2880000, by norm_num, ?_⟩
  intro Pa X φ z0 β hβ hX hθ hτ
  have hτ0 : (0 : ℝ) ≤ Pa.τ := le_trans zero_le_one (one_le_tau Pa)
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le one_pos hXr
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  -- ## The three boundaries
  have hcut : Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β
      = Work.FITop4.Tcut (Work.FITop.radN Pa)
          (fun z1 z2 d => if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1:ℝ) else 0) β := by
    rw [Work.FITop4.Wcut, Work.FITop4.Bcut, Tcut6_add_cut]
    exact Tcut6_congr_cut _ _ _ _ (fun z1 z2 d => cutW_add_cutB (Work.FIPlan.absDelta z1 z2) X d)
  have hnorm := Tcut6_norm_le (Pa := Pa) (X := X) (φ := φ) (β := β)
    (fun z hz => hβ.support hz) hX
  -- ## `Σ ‖β‖ ≤ 600 N / X`
  have hS : ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ≤ 600 * Pa.N / (X : ℝ) := by
    have harith := smallTheta_tau_sum_bound (Pa := Pa) (X := X) hX hτ0 hθ hτ
    calc ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖
        ≤ Pa.τ * (200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)) :=
          sum_norm_beta_le Pa φ z0 β hβ
      _ = 200 * (Pa.τ * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)) := by ring
      _ ≤ 200 * (3 * Pa.N / (X : ℝ)) := mul_le_mul_of_nonneg_left harith (by norm_num)
      _ = 600 * Pa.N / (X : ℝ) := by ring
  -- ## `log(8(1+θ)N) ≤ 4 log(N+2)`
  have hL := smallTheta_log_bound (Pa := Pa) (theta_le_one Pa)
  -- ## The `log` factors are non-negative
  have hL0 : (0 : ℝ) ≤ Real.log (8 * (1 + Pa.θ) * Pa.N) :=
    Real.log_nonneg (by nlinarith [Pa.hθ0, hN1])
  have hlogN2 : (0 : ℝ) ≤ Real.log (Pa.N + 2) := Real.log_nonneg (by linarith)
  have hSnn : (0 : ℝ) ≤ ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ :=
    Finset.sum_nonneg (fun z _ => norm_nonneg _)
  have hSsq : (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖) ^ 2
      ≤ (600 * Pa.N / (X : ℝ)) ^ 2 := pow_le_pow_left₀ hSnn hS 2
  -- ## Assembly
  have hstep1 : (2 : ℝ) * (X : ℝ) * Real.log (8 * (1 + Pa.θ) * Pa.N)
        * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖) ^ 2
      ≤ 2 * (X : ℝ) * (4 * Real.log (Pa.N + 2)) * (600 * Pa.N / (X : ℝ)) ^ 2 := by
    have h2X0 : (0 : ℝ) ≤ 2 * (X : ℝ) := by linarith
    have h4log0 : (0 : ℝ) ≤ 4 * Real.log (Pa.N + 2) := by linarith
    have hfac : 2 * (X : ℝ) * Real.log (8 * (1 + Pa.θ) * Pa.N)
        ≤ 2 * (X : ℝ) * (4 * Real.log (Pa.N + 2)) :=
      mul_le_mul_of_nonneg_left hL h2X0
    exact mul_le_mul hfac hSsq (sq_nonneg _) (mul_nonneg h2X0 h4log0)
  have hstep2 : 2 * (X : ℝ) * (4 * Real.log (Pa.N + 2)) * (600 * Pa.N / (X : ℝ)) ^ 2
      = 2880000 * (X : ℝ)⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2) := by
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    field_simp
    ring
  calc ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β
        + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖
      = ‖Work.FITop4.Tcut (Work.FITop.radN Pa)
          (fun z1 z2 d => if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X
            then (1:ℝ) else 0) β‖ := by rw [hcut]
    _ ≤ 2 * (X : ℝ) * Real.log (8 * (1 + Pa.θ) * Pa.N)
          * (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖) ^ 2 := hnorm
    _ ≤ 2 * (X : ℝ) * (4 * Real.log (Pa.N + 2)) * (600 * Pa.N / (X : ℝ)) ^ 2 := hstep1
    _ = 2880000 * (X : ℝ)⁻¹ * Pa.N ^ 2 * Real.log (Pa.N + 2) := hstep2

end

end Work.FIArea7
