import Mathlib
import Submission.Work.Holonomy3.comp_defs
import Submission.Work.Holonomy3.cleared_defs
import Submission.Work.Holonomy3.coeff_subst_tsum
import Submission.Work.Holonomy3.psi_mul_norm_le
import Submission.Work.Holonomy3.psi_pow_eval_hasSum
import Submission.Work.Holonomy3.psi_pow_norm_bound
import Submission.Work.Holonomy3.finsupp_prod_hasSum
import Submission.Work.Holonomy3.subst_hasSum_eval
import Submission.Work.Holonomy3.cleared_series_decomp
import Submission.Work.Holonomy3.hasSum_polynomial_mul
import Submission.Work.Holonomy3.hasSum_prod_embedVarC
import Submission.Work.Holonomy3.hasSum_mul_ps
import Submission.Work.Holonomy3.tendsto_tsum_norm_mul_pow_zero

/-!
# The cleared Taylor expansion (STEP 3 of the fine holonomy bound)

This module proves `Work.Holonomy3.cleared_taylor`: the Taylor expansion of the cleared composite
`clearedFun Q ψ N P` is the explicit composition series
`uPoly P * diagComp Φ (auxSeriesC f Q)`.

The proof has two layers.

* **Univariate analytic layer** (`univariate_cleared_eval`).  Writing `f(ψ z) = N z / P z` as a germ
  at `0`, multiplying by a polynomial `R` and composing with the Taylor series `Φ` of `ψ`, one gets
  `HasSum (fun n => [X^n]((R:ℂ⟦X⟧) * (f ∘ Φ)) * z^n) (M z)` on the whole ball of radius `ρ`, where
  `M` is any function analytic on that ball agreeing with `z ↦ R(z)·N(z)/P(z)` near `0`.  The
  ingredient that differs from `0` inside the ball is the pole-clearing factor `R`: the composition
  series `f∘Φ` alone may diverge, but `R·(f∘Φ)` is the Taylor series of the analytic function `M`.
  The evaluation of the composition series near `0` is `subst_hasSum_eval`; the passage to the whole
  ball uses the Taylor theorem `Complex.hasSum_taylorSeries_on_ball` plus uniqueness of the power
  series development.

* **Multivariate assembly.**  `cleared_series_decomp` decomposes the series
  `uPoly P * diagComp Φ (auxSeriesC f Q)` into a finite sum of products over the variables of
  univariate series `(Φ s)^{k_s}·(∏_i P i s)·(f_{i_s}∘Φ_s)`; each factor is evaluated by the
  univariate layer, and `hasSum_prod_embedVarC` reassembles the multivariable `HasSum`.
-/

namespace Work.Holonomy3

open Submission.CDTPlan
open Filter Topology
open scoped BigOperators

noncomputable section

/-! ## Auxiliary lemmas -/

/-- `compPS Φ F = PowerSeries.subst Φ F` when `Φ` has vanishing constant coefficient (the two
coefficient formulas differ only by the terms `k > n`, which vanish by `coeff_pow_eq_zero_of_lt`). -/
lemma compPS_eq_subst {Φ F : PowerSeries ℂ} (h0 : PowerSeries.coeff 0 Φ = 0) :
    compPS Φ F = PowerSeries.subst Φ F := by
  have hsub : PowerSeries.HasSubst Φ :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      rwa [PowerSeries.coeff_zero_eq_constantCoeff] at h0)
  ext n
  rw [compPS_coeff, PowerSeries.coeff_subst' hsub]
  have hsupp : Function.support
      (fun d : ℕ => PowerSeries.coeff d F • PowerSeries.coeff n (Φ ^ d))
      ⊆ ↑(Finset.range (n + 1)) := by
    intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra hdn
    rw [not_lt] at hdn
    exact hd (by rw [coeff_pow_eq_zero_of_lt h0 hdn, smul_zero])
  rw [show (∑ᶠ d : ℕ, PowerSeries.coeff d F • PowerSeries.coeff n (Φ ^ d))
      = ∑ d ∈ Finset.range (n + 1),
          (PowerSeries.coeff d F • PowerSeries.coeff n (Φ ^ d))
      from finsum_eq_finsetSum_of_support_subset _ hsupp]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_eq_mul]

/-- `HasSum` of a finite sum of families. -/
lemma hasSum_finset_sum {ι β : Type*} [DecidableEq ι] :
    ∀ (s : Finset ι) (f : ι → β → ℂ) (a : ι → ℂ),
    (∀ i ∈ s, HasSum (f i) (a i)) → HasSum (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, a i) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro f a _
    simpa using (hasSum_zero (f := fun _ : β => (0 : ℂ)))
  | insert i s hi ih =>
    intro f a h
    have h1 := h i (Finset.mem_insert_self i s)
    have h2 := ih f a fun j hj => h j (Finset.mem_insert_of_mem hj)
    simpa only [Finset.sum_insert hi] using h1.add h2

/-- The coefficient of a nested finite sum of scalar multiples, multiplied by a constant. -/
lemma coeff_sum_sum_smul_mul {d m : ℕ} (c : (Fin d → Fin m) → (Fin d →₀ ℕ) → ℂ)
    (s : (Fin d → Fin m) → Finset (Fin d →₀ ℕ))
    (T : (Fin d → Fin m) → (Fin d →₀ ℕ) → MvPowerSeries (Fin d) ℂ)
    (n : Fin d →₀ ℕ) (P : ℂ) :
    MvPowerSeries.coeff n (∑ i, ∑ k ∈ s i, c i k • T i k) * P =
      ∑ i, ∑ k ∈ s i, c i k * (MvPowerSeries.coeff n (T i k) * P) := by
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

/-- `Polynomial.eval` of a finite product of polynomials. -/
lemma eval_finset_prod {m : ℕ} (s : Finset (Fin m)) (Q : Fin m → Polynomial ℂ) (w : ℂ) :
    Polynomial.eval w (∏ i ∈ s, Q i) = ∏ i ∈ s, Polynomial.eval w (Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, Polynomial.eval_mul, ih]

/-! ## The univariate analytic step -/

/-- **Univariate cleared Taylor expansion.**  Let `f ∈ ℚ⟦X⟧`, let `Φ` be the Taylor series of
`ψ` at `0` (with `ψ 0 = 0`), let `N` and `M` be functions with `M` analytic on the ball of radius
`ρ`, and suppose that near `0` the pullback of `f` along `ψ` equals `N z / P z` for a polynomial `P`
with `P 0 ≠ 0`, while `M z = R(z)·N(z)/P(z)` near `0` for a polynomial `R`.  Then for every
`‖z‖ < ρ` the series `R·(f ∘ Φ)` converges at `z` with sum `M z`. -/
theorem univariate_cleared_eval {f : PowerSeries ℚ} {Φ : PowerSeries ℂ} {ψ : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hψ0 : ψ 0 = 0)
    (hΦ : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun j : ℕ => PowerSeries.coeff j Φ * z ^ j) (ψ z))
    (N : ℂ → ℂ) (P R : Polynomial ℂ) (M : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M (Metric.ball 0 ρ))
    (hMPR : M =ᶠ[𝓝 (0 : ℂ)] fun z => R.eval z * (N z / P.eval z))
    (hpull : ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * ψ z ^ n) (N z / P.eval z)) :
    ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n : ℕ => PowerSeries.coeff n
        ((R : PowerSeries ℂ) * PowerSeries.subst Φ (PowerSeries.map (algebraMap ℚ ℂ) f))
          * z ^ n) (M z) := by
  set h : PowerSeries ℂ := PowerSeries.map (algebraMap ℚ ℂ) f with hh
  have hcf : ∀ n : ℕ, PowerSeries.coeff n h = ((PowerSeries.coeff n f : ℚ) : ℂ) := by
    intro n
    rw [hh, PowerSeries.coeff_map]
    rfl
  have hΦ0 : PowerSeries.coeff 0 Φ = 0 := by
    have h1 := hΦ 0 (by simpa using hρ)
    have hc : (fun j : ℕ => PowerSeries.coeff j Φ * (0 : ℂ) ^ j)
        = fun j : ℕ => if j = 0 then PowerSeries.coeff 0 Φ else 0 := by
      funext j
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp
      · rw [zero_pow (by omega : j ≠ 0), mul_zero]
        simp [show ¬ j = 0 by omega]
    rw [hc] at h1
    rw [(h1.unique (hasSum_ite_eq 0 (PowerSeries.coeff 0 Φ))).symm, hψ0]
  -- The eventual statement: the HasSum on a neighbourhood of `0`
  have hsmall : ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun k : ℕ => PowerSeries.coeff k
      ((R : PowerSeries ℂ) * PowerSeries.subst Φ h) * z ^ k) (M z) := by
    obtain ⟨δp, hδp, hpull₀⟩ := Metric.eventually_nhds_iff.mp hpull
    obtain ⟨δm, hδm, hMPR₀⟩ := Metric.eventually_nhds_iff.mp hMPR
    have hpull' : ∀ z : ℂ, ‖z‖ < δp → HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n f : ℚ) : ℂ) * ψ z ^ n) (N z / P.eval z) :=
      fun z hz => hpull₀ (by simpa [dist_zero_right] using hz)
    have hMPR' : ∀ z : ℂ, ‖z‖ < δm → M z = R.eval z * (N z / P.eval z) :=
      fun z hz => hMPR₀ (by simpa [dist_zero_right] using hz)
    -- Step 1: control of the weighted ℓ¹-norm of `Φ` by a convergence point of the pullback
    have hdom : ∃ δc > 0, ∀ z : ℂ, ‖z‖ < δc →
        Summable (fun p : ℕ => ‖PowerSeries.coeff p h‖ *
          (∑' j : ℕ, ‖PowerSeries.coeff j Φ‖ * ‖z‖ ^ j) ^ p) := by
      by_cases hΦz : Φ = 0
      · refine ⟨1, one_pos, fun z hz => ?_⟩
        have hA : (∑' j : ℕ, ‖PowerSeries.coeff j Φ‖ * ‖z‖ ^ j) = 0 := by
          rw [hΦz]
          simp
        rw [hA]
        refine summable_of_ne_finset_zero (s := {0}) fun p hp => ?_
        rw [Finset.mem_singleton] at hp
        rw [zero_pow hp, mul_zero]
      · -- `Φ ≠ 0`: find a point of the eventual set at which `ψ` does not vanish
        have hex : ∃ z₁ : ℂ, ‖z₁‖ < min δp (min 1 ρ) ∧ ψ z₁ ≠ 0 := by
          by_contra hcon
          push_neg at hcon
          have hbot : Φ = 0 := by
            have hzero : HasFPowerSeriesAt (fun _ : ℂ => (0 : ℂ))
                (FormalMultilinearSeries.ofScalars ℂ (fun j => PowerSeries.coeff j Φ)) 0 := by
              rw [hasFPowerSeriesAt_iff']
              refine Filter.eventually_of_mem
                (Metric.ball_mem_nhds 0 (lt_min hδp (lt_min one_pos hρ))) fun z hz => ?_
              have hz' : ‖z‖ < min δp (min 1 ρ) := by
                simpa [Metric.mem_ball, dist_zero_right] using hz
              have hzρ : ‖z‖ < ρ :=
                lt_of_lt_of_le hz' (le_trans (min_le_right _ _) (min_le_right _ _))
              have h1 := hΦ z hzρ
              rw [hcon z hz'] at h1
              refine h1.congr_fun fun n => ?_
              simp [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_comm]
            have hz2 := hzero.eq_zero
            ext n
            have h3 : (FormalMultilinearSeries.ofScalars ℂ
                  (fun j => PowerSeries.coeff j Φ)).coeff n
                = (0 : FormalMultilinearSeries ℂ ℂ ℂ).coeff n :=
              congrArg (fun (p : FormalMultilinearSeries ℂ ℂ ℂ) => p.coeff n) hz2
            rw [FormalMultilinearSeries.coeff_ofScalars] at h3
            have h4 : (0 : FormalMultilinearSeries ℂ ℂ ℂ).coeff n = 0 := by
              simp [FormalMultilinearSeries.coeff]
            rw [h4] at h3
            exact h3
          exact hΦz hbot
        obtain ⟨z₁, hz₁, hψz₁⟩ := hex
        have hz₁' : ‖z₁‖ < δp := lt_of_lt_of_le hz₁ (min_le_left _ _)
        have hw : 0 < ‖ψ z₁‖ := norm_pos_iff.mpr hψz₁
        have hsum₁ : Summable (fun n : ℕ => ‖PowerSeries.coeff n h‖ * ‖ψ z₁‖ ^ n) := by
          have h1 := (hpull' z₁ hz₁').summable.norm
          refine h1.congr fun n => ?_
          rw [hcf n, norm_mul, norm_pow]
        -- the weighted ℓ¹-norm of `Φ` on the radius `ρ/2`
        have hcpos : (0 : ℝ) < ρ / 2 := by linarith
        have hnormc : ‖((ρ / 2 : ℝ) : ℂ)‖ = ρ / 2 :=
          Complex.norm_of_nonneg (le_of_lt hcpos)
        have hsumΦ : Summable (fun j : ℕ => ‖PowerSeries.coeff j Φ‖ * (ρ / 2) ^ j) := by
          have h1 := (hΦ ((ρ / 2 : ℝ) : ℂ) (by rw [hnormc]; linarith)).summable.norm
          refine h1.congr fun j => ?_
          rw [norm_mul, norm_pow, hnormc]
        have htend := tendsto_tsum_norm_mul_pow_zero (Φ := Φ) (r := ρ / 2) hcpos hΦ0 hsumΦ
        have hev : ∀ᶠ t in 𝓝 (0 : ℝ),
            t ∈ Set.Ioi (0 : ℝ) → (∑' j : ℕ, ‖PowerSeries.coeff j Φ‖ * t ^ j) < ‖ψ z₁‖ :=
          eventually_nhdsWithin_iff.mp (htend.eventually (eventually_lt_nhds hw))
        obtain ⟨δA, hδApos, hδA₀⟩ := Metric.eventually_nhds_iff.mp hev
        have hδA'' : ∀ t : ℝ, 0 < t → t < δA →
            (∑' j : ℕ, ‖PowerSeries.coeff j Φ‖ * t ^ j) < ‖ψ z₁‖ :=
          fun t ht htA => hδA₀ (by rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact htA) ht
        refine ⟨min δA 1, lt_min hδApos one_pos, fun z hz => ?_⟩
        have hzc : ‖z‖ < min δA 1 := hz
        have hA_le : (∑' j : ℕ, ‖PowerSeries.coeff j Φ‖ * ‖z‖ ^ j) ≤ ‖ψ z₁‖ := by
          rcases eq_or_lt_of_le (norm_nonneg z) with h0z | hpos
          · rw [← h0z]
            rw [tsum_eq_single 0 (fun b hb => by rw [zero_pow hb, mul_zero])]
            simp [hΦ0]
          · exact le_of_lt (hδA'' ‖z‖ hpos (lt_of_lt_of_le hzc (min_le_left _ _)))
        refine Summable.of_nonneg_of_le
          (f := fun p : ℕ => ‖PowerSeries.coeff p h‖ * ‖ψ z₁‖ ^ p)
          (g := fun p : ℕ => ‖PowerSeries.coeff p h‖ *
            (∑' j : ℕ, ‖PowerSeries.coeff j Φ‖ * ‖z‖ ^ j) ^ p)
          (fun p => by positivity)
          (fun p => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (tsum_nonneg fun j => by positivity) hA_le p) (norm_nonneg _))
          hsum₁
    obtain ⟨δc, hδc, hdomc⟩ := hdom
    -- Step 2: the evaluation near `0`
    refine Metric.eventually_nhds_iff.mpr ⟨min (min δp δm) (min δc ρ), by positivity,
      fun z hz => ?_⟩
    simp only [dist_zero_right] at hz
    have hzp : ‖z‖ < δp := lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_left _ _))
    have hzm : ‖z‖ < δm := lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_right _ _))
    have hzc : ‖z‖ < δc := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _))
    have hzρ : ‖z‖ < ρ := lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _))
    have habsψ : Summable (fun j : ℕ => ‖PowerSeries.coeff j Φ‖ * ‖z‖ ^ j) := by
      have h1 := (hΦ z hzρ).summable.norm
      refine h1.congr fun j => ?_
      rw [norm_mul, norm_pow]
    have hpullz : HasSum (fun n : ℕ => PowerSeries.coeff n h * ψ z ^ n) (N z / P.eval z) :=
      (hpull' z hzp).congr_fun fun n => by rw [hcf n]
    have hcomp := subst_hasSum_eval (h := h) (ψ := Φ) hΦ0 (hΦ z hzρ) hpullz habsψ (hdomc z hzc)
    have hmul := hasSum_polynomial_mul (σ := PowerSeries.subst Φ h) R hcomp
    rw [← hMPR' z hzm] at hmul
    exact hmul
  -- Step 3: `M` has the power series `τ`
  have hPSt : HasFPowerSeriesAt M (FormalMultilinearSeries.ofScalars ℂ
      (fun n => PowerSeries.coeff n ((R : PowerSeries ℂ) * PowerSeries.subst Φ h))) 0 := by
    rw [hasFPowerSeriesAt_iff']
    filter_upwards [hsmall] with z hz
    refine hz.congr_fun fun n => ?_
    simp only [sub_zero, smul_eq_mul, FormalMultilinearSeries.coeff_ofScalars]
    ring
  have hTaylor : HasFPowerSeriesAt M (FormalMultilinearSeries.ofScalars ℂ
      (fun n => iteratedDeriv n M 0 / (n.factorial : ℂ))) 0 :=
    (hM 0 (by simpa using hρ)).hasFPowerSeriesAt
  have hcoeff : ∀ n : ℕ, PowerSeries.coeff n ((R : PowerSeries ℂ) * PowerSeries.subst Φ h)
      = iteratedDeriv n M 0 / (n.factorial : ℂ) := by
    intro n
    have h3 := congrArg (fun (p : FormalMultilinearSeries ℂ ℂ ℂ) => p.coeff n)
      (hPSt.eq_formalMultilinearSeries hTaylor)
    simpa [FormalMultilinearSeries.coeff_ofScalars] using h3
  -- Step 4: the Taylor theorem for `M` on the ball of radius `ρ`
  intro z hz
  have hdiff : DifferentiableOn ℂ M (Metric.ball 0 ρ) := hM.differentiableOn
  have htz := Complex.hasSum_taylorSeries_on_ball hdiff (by simpa [Metric.mem_ball] using hz)
  refine htz.congr_fun fun n => ?_
  rw [hcoeff n, smul_eq_mul, smul_eq_mul, div_eq_inv_mul]
  ring

/-! ## The multivariable assembly -/

/-- The value of `clearedFun` as a finite sum over the monomials of the templates `Q i`. -/
lemma clearedFun_eq_sum {d m : ℕ} (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℂ)
    (ψ : Fin d → ℂ → ℂ) (N : Fin m → Fin d → ℂ → ℂ) (P : Fin m → Fin d → Polynomial ℂ)
    (z : Fin d → ℂ) :
    clearedFun Q ψ N P z =
      ∑ i, ∑ k ∈ (Q i).support, (Q i).coeff k •
        ∏ s, (ψ s (z s) ^ (k s) *
          (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s))) := by
  rw [clearedFun]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.eval_eq']
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul]
  have h1 : (∏ s, (ψ s (z s) ^ (k s) *
        (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s))))
      = (∏ s, ψ s (z s) ^ (k s)) *
        ∏ s, (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s)) :=
    Finset.prod_mul_distrib
  rw [h1]
  ring

theorem cleared_taylor {d m : ℕ} (f : Fin m → PowerSeries ℚ)
    (Q : (Fin d → Fin m) → MvPolynomial (Fin d) ℚ)
    (ψ : Fin d → ℂ → ℂ) (Φ : Fin d → PowerSeries ℂ) (ρ : ℝ) (hρ : 1 < ρ)
    (hψ : ∀ s, AnalyticOnNhd ℂ (ψ s) (Metric.ball 0 ρ)) (hψ0 : ∀ s, ψ s 0 = 0)
    (hΦ : ∀ s z, ‖z‖ < ρ → HasSum (fun p => (Φ s).coeff p * z ^ p) (ψ s z))
    (N : Fin m → Fin d → ℂ → ℂ) (P : Fin m → Fin d → Polynomial ℂ)
    (hpull : ∀ i s, PullbackData (f i) (ψ s) ρ (N i s) (P i s)) :
    ClearedTaylorClaim f Q ψ Φ ρ N P := by
  intro z hz
  set F : Fin m → PowerSeries ℂ := fun i => PowerSeries.map (algebraMap ℚ ℂ) (f i) with hF
  set Q' : (Fin d → Fin m) → MvPolynomial (Fin d) ℂ :=
    fun i => MvPolynomial.map (algebraMap ℚ ℂ) (Q i) with hQ
  have hρpos : (0 : ℝ) < ρ := lt_trans one_pos hρ
  have hΦ0 : ∀ s : Fin d, PowerSeries.coeff 0 (Φ s) = 0 := by
    intro s
    have h1 := hΦ s 0 (by simpa using hρpos)
    have hc : (fun j : ℕ => PowerSeries.coeff j (Φ s) * (0 : ℂ) ^ j)
        = fun j : ℕ => if j = 0 then PowerSeries.coeff 0 (Φ s) else 0 := by
      funext j
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj; simp
      · rw [zero_pow (by omega : j ≠ 0), mul_zero]
        simp [show ¬ j = 0 by omega]
    rw [hc] at h1
    rw [(h1.unique (hasSum_ite_eq 0 (PowerSeries.coeff 0 (Φ s)))).symm, hψ0 s]
  -- unwind the pullback data
  have hp : ∀ i s, (P i s).eval 0 ≠ 0 ∧ AnalyticOnNhd ℂ (N i s) (Metric.ball 0 ρ) ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n (f i) : ℚ) : ℂ) * ψ s w ^ n) (N i s w / (P i s).eval w)) := by
    intro i s
    have h := hpull i s
    rw [PullbackData] at h
    exact h
  -- the weighted ℓ¹-norm of every `Φ s` at `z s`
  have habsΦ : ∀ s : Fin d, Summable (fun j : ℕ => ‖PowerSeries.coeff j (Φ s)‖ * ‖z s‖ ^ j) := by
    intro s
    have h1 := (hΦ s (z s) (hz s)).summable.norm
    refine h1.congr fun j => ?_
    rw [norm_mul, norm_pow]
  -- the univariate input
  have huni : ∀ (i : Fin d → Fin m) (s : Fin d) (w : ℂ), ‖w‖ < ρ → HasSum (fun n : ℕ =>
      PowerSeries.coeff n ((((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) *
        PowerSeries.subst (Φ s) (F (i s))) * w ^ n)
      (N (i s) s w * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval w) := by
    intro i s
    refine univariate_cleared_eval (f := f (i s)) (Φ := Φ s) (ψ := ψ s) (ρ := ρ) hρpos
      (hψ0 s) (hΦ s) (N (i s) s) (P (i s) s) (((∏ i', P i' s) : Polynomial ℂ))
      (fun w => N (i s) s w * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval w) ?_ ?_ ?_
    · refine AnalyticOnNhd.mul (hp (i s) s).2.1 ?_
      refine AnalyticOnNhd.congr (f := fun w : ℂ => Polynomial.eval w (∏ i' ∈ Finset.univ.erase (i s), P i' s)) Metric.isOpen_ball ?_ ?_
      · exact (AnalyticOnNhd.eval_polynomial (∏ i' ∈ Finset.univ.erase (i s), P i' s)).mono
          (Set.subset_univ _)
      · intro w _
        exact eval_finset_prod _ _ w
    · -- `M = R·(N/P)` near `0`
      have hP0 : (P (i s) s).eval 0 ≠ 0 := (hp (i s) s).1
      have hR : ((∏ i', P i' s) : Polynomial ℂ)
          = (P (i s) s) * ∏ i' ∈ Finset.univ.erase (i s), P i' s := by
        rw [← Finset.mul_prod_erase Finset.univ (fun i' => P i' s) (Finset.mem_univ (i s))]
      filter_upwards [((Polynomial.continuous (P (i s) s)).continuousAt).eventually_ne hP0]
        with w hw
      have hRw : Polynomial.eval w ((∏ i', P i' s) : Polynomial ℂ)
          = Polynomial.eval w (P (i s) s) *
            ∏ i' ∈ Finset.univ.erase (i s), Polynomial.eval w (P i' s) := by
        rw [hR, Polynomial.eval_mul, eval_finset_prod]
      rw [hRw]
      field_simp
    · exact (hp (i s) s).2.2
  -- the per-`(i,k)` multivariable HasSum
  have hprod : ∀ (i : Fin d → Fin m) (k : Fin d →₀ ℕ), k ∈ (Q' i).support →
      HasSum (fun n : Fin d →₀ ℕ =>
        (∏ s, embedVarC s ((Φ s) ^ (k s) *
          (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) * compPS (Φ s) (F (i s)))).coeff n
          * ∏ s, z s ^ (n s))
      (∏ s, (ψ s (z s) ^ (k s) *
        (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s)))) := by
    intro i k hk
    refine hasSum_prod_embedVarC
      (σ := fun s => (Φ s) ^ (k s) *
        ((((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ)) * compPS (Φ s) (F (i s)))
      (A := fun s => ψ s (z s) ^ (k s) *
        (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s))) z ?_
    intro s
    have hpow : HasSum (fun n : ℕ => PowerSeries.coeff n ((Φ s) ^ (k s)) * z s ^ n)
        (ψ s (z s) ^ (k s)) :=
      psi_pow_eval_hasSum (hΦ s (z s) (hz s)) (fun d => (psi_pow_norm_bound (habsΦ s) d).1) (k s)
    have hb := huni i s (z s) (hz s)
    have hbn : Summable (fun n : ℕ => ‖PowerSeries.coeff n
        ((((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) *
          PowerSeries.subst (Φ s) (F (i s))) * z s ^ n‖) := hb.summable.norm
    have hmul := hasSum_mul_ps hpow hb hbn
    have hbridge : PowerSeries.subst (Φ s) (F (i s)) = compPS (Φ s) (F (i s)) :=
      (compPS_eq_subst (Φ := Φ s) (F := F (i s)) (hΦ0 s)).symm
    simpa only [hbridge, mul_assoc] using hmul
  -- the finite sum over the monomials of the templates
  have hfin : HasSum (fun n : Fin d →₀ ℕ =>
      ∑ i, ∑ k ∈ (Q' i).support, ((Q' i).coeff k *
        ((∏ s, embedVarC s ((Φ s) ^ (k s) *
          (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) * compPS (Φ s) (F (i s)))).coeff n
          * ∏ s, z s ^ (n s))))
      (∑ i, ∑ k ∈ (Q' i).support, ((Q' i).coeff k *
        ∏ s, (ψ s (z s) ^ (k s) *
          (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s))))) := by
    refine hasSum_finset_sum Finset.univ
      (fun i (n : Fin d →₀ ℕ) => ∑ k ∈ (Q' i).support, ((Q' i).coeff k *
        ((∏ s, embedVarC s ((Φ s) ^ (k s) *
          (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) * compPS (Φ s) (F (i s)))).coeff n
          * ∏ s, z s ^ (n s))))
      (fun i => ∑ k ∈ (Q' i).support, ((Q' i).coeff k *
        ∏ s, (ψ s (z s) ^ (k s) *
          (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s)))))
      (fun i _ => ?_)
    exact hasSum_finset_sum (Q' i).support
      (fun k (n : Fin d →₀ ℕ) => (Q' i).coeff k *
        ((∏ s, embedVarC s ((Φ s) ^ (k s) *
          (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) * compPS (Φ s) (F (i s)))).coeff n
          * ∏ s, z s ^ (n s)))
      (fun k => (Q' i).coeff k *
        ∏ s, (ψ s (z s) ^ (k s) *
          (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s))))
      (fun k hk => (hprod i k hk).mul_left _)
  -- transfer to the coefficient of the decomposed series
  have htot : HasSum (fun n : Fin d →₀ ℕ =>
      (MvPowerSeries.coeff n (∑ i, ∑ k ∈ (Q' i).support, (Q' i).coeff k •
        ∏ s, embedVarC s ((Φ s) ^ (k s) *
          (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) * compPS (Φ s) (F (i s))))) *
        ∏ s, z s ^ (n s))
      (∑ i, ∑ k ∈ (Q' i).support, (Q' i).coeff k •
        ∏ s, (ψ s (z s) ^ (k s) *
          (N (i s) s (z s) * ∏ i' ∈ Finset.univ.erase (i s), (P i' s).eval (z s)))) := by
    refine hfin.congr_fun fun n => ?_
    exact coeff_sum_sum_smul_mul (c := fun i k => (Q' i).coeff k)
      (s := fun i => (Q' i).support)
      (T := fun i k => ∏ s, embedVarC s ((Φ s) ^ (k s) *
        (((∏ i', P i' s) : Polynomial ℂ) : PowerSeries ℂ) * compPS (Φ s) (F (i s))))
      n (∏ s, z s ^ (n s))
  -- conclusion
  rw [cleared_series_decomp P Q' Φ F hΦ0, clearedFun_eq_sum Q' ψ N P z]
  simp only [smul_eq_mul]
  exact htot

end

end Work.Holonomy3
