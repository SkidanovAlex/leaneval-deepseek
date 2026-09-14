/-
⚠ IMPORT-CLASH WORKAROUND (session 118) -- together with `Submission/GaussIsoperimetricBlowup.lean`.

The commons contains two modules that both declare `Commons.Analysis.GaussianMeasure.toLp_norm_sq`
(`bobkov_strong_nD` and `brascamp_lieb_truncated`); Lean refuses to load both in one environment,
and the theorem path needs `brascamp_lieb_truncated` (CFM04 (B)-conjecture).  The Ehrhard route to
the Gaussian isoperimetric inequality only used ONE lemma from `bobkov_strong_nD`, namely
`integrable_gauss_euclideanSpace`; here that single use is replaced by the (equivalent, standalone)
commons lemma `Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm`, and the import is dropped.

Content below is copied verbatim from the commons module except for that one line.
Proper fix: delete or rename the duplicate `toLp_norm_sq` in one of the two commons modules.
-/
import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.ehrhard_inequality_one_convex
import Submission.Commons.Analysis.GaussianMeasure.ball_mass_ge_cdf_sub
import Submission.Commons.Analysis.GaussianMeasure.gaussian_ball_quantile_asymptotic
import Submission.Commons.Analysis.GaussianMeasure.gaussian_cdf_strictMono
import Submission.Commons.Analysis.GaussianMeasure.gauss_cdf_tail_split
import Submission.Commons.Analysis.GaussianMeasure.gaussian_total_mass_one
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm

open MeasureTheory Set Real Filter Metric
open scoped Topology ENNReal

namespace Commons.Analysis.GaussianMeasure

noncomputable section

/-- The one-dimensional Gaussian cumulative distribution function
`t ↦ ∫_{x ≤ t} exp (-π x²)` (total mass `1`). -/
private def cdf (t : ℝ) : ℝ := ∫ x : ℝ in Set.Iic t, Real.exp (-Real.pi * x ^ 2)

/-- The standard Gaussian density `x ↦ exp (-π ‖x‖²)` on `ℝⁿ`. -/
private def dens {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ := Real.exp (-Real.pi * ‖x‖ ^ 2)

/-- The closed `ρ`-neighbourhood (blow-up) of a set. -/
private def nbhd {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (ρ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) := {x | ∃ u ∈ U, dist x u ≤ ρ}

private lemma dens_nonneg {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ dens x :=
  Real.exp_nonneg _

private lemma dens_integrable {n : ℕ} : Integrable (dens (n := n)) volume :=
  Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm Real.pi Real.pi_pos

private lemma nbhd_mono {n : ℕ} {U V : Set (EuclideanSpace ℝ (Fin n))} (h : U ⊆ V) (ρ : ℝ) :
    nbhd U ρ ⊆ nbhd V ρ := by
  intro x hx
  change ∃ u ∈ U, dist x u ≤ ρ at hx
  change ∃ u ∈ V, dist x u ≤ ρ
  exact ⟨hx.choose, h hx.choose_spec.1, hx.choose_spec.2⟩

private lemma cdf_eq_add (s : ℝ) :
    cdf s = cdf 0 + ∫ x in (0:ℝ)..s, Real.exp (-Real.pi * x ^ 2) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) :=
    integrable_exp_neg_mul_sq Real.pi_pos
  have h := intervalIntegral.integral_Iic_sub_Iic (a := (0:ℝ)) (b := s)
      (f := fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) (μ := volume)
      hg.integrableOn hg.integrableOn
  unfold cdf
  linarith

private lemma cdf_continuous : Continuous cdf := by
  have hg : Continuous (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) := by fun_prop
  have hfun : cdf = fun s : ℝ => cdf 0 + ∫ x in (0:ℝ)..s, Real.exp (-Real.pi * x ^ 2) :=
    funext cdf_eq_add
  rw [hfun]
  exact continuous_const.add
    (intervalIntegral.differentiable_integral_of_continuous (a := (0:ℝ)) hg).continuous

private lemma cdf_strictMono : StrictMono cdf :=
  gaussian_cdf_strictMono

/-! ### The bounded case -/

/-- The Gaussian isoperimetric (blow-up) inequality for a measurable set contained in a ball
of radius `M`. -/
private lemma bounded_case {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : MeasurableSet U)
    {M : ℝ} (hM : 0 ≤ M) (hUbd : ∀ u ∈ U, ‖u‖ ≤ M)
    {t ρ : ℝ} (hρ : 0 ≤ ρ) (hUγ : cdf t ≤ ∫ x in U, dens x) :
    cdf (t + ρ) ≤ ∫ x in nbhd U ρ, dens x := by
  set lam : ℕ → ℝ := fun k => ρ / (M + (k : ℝ) + 1) with hlam
  -- Eventually the `k`-ball carries at least the mass of the half-line up to `k - 1`.
  have hball : ∀ᶠ k : ℕ in atTop,
      cdf ((k : ℝ) - 1) ≤ ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ), dens x := by
    have h := ball_mass_ge_cdf_sub (n := n) 1 (by norm_num)
    exact tendsto_natCast_atTop_atTop.eventually h
  -- Eventually the denominator of `lam` exceeds `ρ`, so that `lam k ≤ 1`.
  have hbig : ∀ᶠ k : ℕ in atTop, ρ ≤ M + (k : ℝ) + 1 := by
    have hden : Tendsto (fun k : ℕ => M + (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1
        (tendsto_atTop_add_const_left atTop M tendsto_natCast_atTop_atTop)
    exact hden.eventually_ge_atTop ρ
  have hkey : ∀ᶠ k : ℕ in atTop,
      cdf ((1 - lam k) * t + lam k * ((k : ℝ) - 1)) ≤ ∫ x in nbhd U ρ, dens x := by
    filter_upwards [hball, hbig] with k hb hbigk
    have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hdenpos : (0:ℝ) < M + (k : ℝ) + 1 := by linarith
    have hlam0 : 0 ≤ lam k := by
      rw [hlam]; exact div_nonneg hρ hdenpos.le
    have hlam1 : lam k ≤ 1 := by
      rw [hlam, div_le_one hdenpos]
      exact hbigk
    -- The Minkowski combination of `U` and the `k`-ball lies in the `ρ`-neighbourhood.
    have hsub : {x : EuclideanSpace ℝ (Fin n) |
        ∃ a ∈ U, ∃ b ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ),
          x = (1 - lam k) • a + lam k • b} ⊆ nbhd U ρ := by
      intro x hx
      have hx' : ∃ a ∈ U, ∃ b ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ),
          x = (1 - lam k) • a + lam k • b := hx
      obtain ⟨a, ha, b, hb', rfl⟩ := hx'
      change ∃ u ∈ U, dist ((1 - lam k) • a + lam k • b) u ≤ ρ
      refine ⟨a, ha, ?_⟩
      have hbR : ‖b‖ ≤ (k : ℝ) := by
        have h := mem_closedBall.mp hb'
        rwa [dist_zero_right] at h
      have haM : ‖a‖ ≤ M := hUbd a ha
      have hnorm : dist ((1 - lam k) • a + lam k • b) a = lam k * ‖b - a‖ := by
        rw [dist_eq_norm]
        have h1 : (1 - lam k) • a + lam k • b - a = lam k • (b - a) := by
          rw [sub_smul, one_smul, smul_sub]
          abel
        rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0]
      rw [hnorm]
      calc lam k * ‖b - a‖ ≤ lam k * ((k : ℝ) + M) := by
            refine mul_le_mul_of_nonneg_left ?_ hlam0
            calc ‖b - a‖ ≤ ‖b‖ + ‖a‖ := norm_sub_le _ _
              _ ≤ (k : ℝ) + M := by linarith
        _ ≤ ρ := by
            rw [hlam, div_mul_eq_mul_div, div_le_iff₀ hdenpos]
            nlinarith [hρ, hk0, hM]
    have hehr := ehrhard_inequality_one_convex (A := U)
        (B := closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ))
        hU (convex_closedBall 0 (k : ℝ)) (isClosed_closedBall.measurableSet)
        (lam k) hlam0 hlam1 t ((k : ℝ) - 1) hUγ hb
    have hint_le : ∫ x in {x : EuclideanSpace ℝ (Fin n) |
          ∃ a ∈ U, ∃ b ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ),
            x = (1 - lam k) • a + lam k • b}, dens x ≤ ∫ x in nbhd U ρ, dens x :=
      setIntegral_mono_set (dens_integrable.integrableOn)
        (Eventually.of_forall (fun x => dens_nonneg x)) (Eventually.of_forall hsub)
    exact le_trans hehr hint_le
  -- The arguments of `cdf` in `hkey` converge to `t + ρ`.
  have hlim : Tendsto (fun k : ℕ => (1 - lam k) * t + lam k * ((k : ℝ) - 1))
      atTop (𝓝 (t + ρ)) := by
    have hden : Tendsto (fun k : ℕ => M + (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1
        (tendsto_atTop_add_const_left atTop M tendsto_natCast_atTop_atTop)
    have hone : Tendsto (fun k : ℕ => (M + 2 + t) / (M + (k : ℝ) + 1)) atTop (𝓝 0) :=
      hden.const_div_atTop (M + 2 + t)
    have hquot : Tendsto (fun k : ℕ => ((k : ℝ) - 1 - t) / (M + (k : ℝ) + 1))
        atTop (𝓝 1) := by
      have heq : (fun k : ℕ => ((k : ℝ) - 1 - t) / (M + (k : ℝ) + 1)) =
          fun k : ℕ => 1 - (M + 2 + t) / (M + (k : ℝ) + 1) := by
        funext k
        have hne : M + (k : ℝ) + 1 ≠ 0 := by
          have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        field_simp
        ring
      rw [heq]
      simpa using (tendsto_const_nhds.sub hone)
    have harg : (fun k : ℕ => (1 - lam k) * t + lam k * ((k : ℝ) - 1)) =
        fun k : ℕ => t + ρ * (((k : ℝ) - 1 - t) / (M + (k : ℝ) + 1)) := by
      funext k
      rw [hlam]
      have hne : M + (k : ℝ) + 1 ≠ 0 := by
        have hk0 : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      field_simp
      ring
    rw [harg]
    simpa using (tendsto_const_nhds.add (hquot.const_mul ρ))
  exact le_of_tendsto (cdf_continuous.continuousAt.tendsto.comp hlim) hkey

/-! ### The general case, by inner approximation with bounded sets -/

theorem gaussian_isoperimetric_via_ehrhard {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : MeasurableSet U) (t ρ : ℝ) (hρ : 0 ≤ ρ)
    (hUγ : (∫ x : ℝ in {x : ℝ | x ≤ t}, Real.exp (-Real.pi * x ^ 2)) ≤
            ∫ x in U, Real.exp (-Real.pi * ‖x‖ ^ 2)) :
    (∫ x : ℝ in {x : ℝ | x ≤ t + ρ}, Real.exp (-Real.pi * x ^ 2)) ≤
      ∫ x in {x : EuclideanSpace ℝ (Fin n) | ∃ u ∈ U, dist x u ≤ ρ},
        Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  have hmain : ∀ δ : ℝ, 0 < δ → cdf (t + ρ - δ) ≤ ∫ x in nbhd U ρ, dens x := by
    intro δ hδ
    have hsmono : Monotone (fun k : ℕ => U ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ)) :=
      fun a b hab =>
        inter_subset_inter_right U (closedBall_subset_closedBall (show (a:ℝ) ≤ (b:ℝ) by exact_mod_cast hab))
    have hiUnion : (⋃ k : ℕ, (U ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ))) = U := by
      ext x
      constructor
      · intro hx
        rw [Set.mem_iUnion] at hx
        obtain ⟨k, hk⟩ := hx
        exact hk.1
      · intro hx
        obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
        rw [Set.mem_iUnion]
        exact ⟨k, hx, by rw [mem_closedBall, dist_zero_right]; exact hk⟩
    have htrunc : Tendsto (fun k : ℕ =>
        ∫ x in U ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ), dens x)
        atTop (𝓝 (∫ x in U, dens x)) := by
      have h := tendsto_setIntegral_of_monotone
        (s := fun k : ℕ => U ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ))
        (f := dens) (μ := volume)
        (fun k => hU.inter isClosed_closedBall.measurableSet) hsmono
        (by rw [hiUnion]; exact dens_integrable.integrableOn)
      rwa [hiUnion] at h
    have hlt : cdf (t - δ) < ∫ x in U, dens x :=
      lt_of_lt_of_le (cdf_strictMono (by linarith)) hUγ
    obtain ⟨k, hk⟩ := (htrunc.eventually (Ioi_mem_nhds hlt)).exists
    have hbd : ∀ u ∈ U ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ), ‖u‖ ≤ (k : ℝ) := by
      intro u hu
      have h := mem_closedBall.mp hu.2
      rwa [dist_zero_right] at h
    have hbc := bounded_case (U := U ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (k : ℝ))
      (hU.inter isClosed_closedBall.measurableSet) (M := (k : ℝ)) (Nat.cast_nonneg k) hbd hρ hk.le
    rw [show t + ρ - δ = (t - δ) + ρ by ring]
    exact le_trans hbc (setIntegral_mono_set (dens_integrable.integrableOn)
      (Eventually.of_forall (fun x => dens_nonneg x))
      (Eventually.of_forall (nbhd_mono Set.inter_subset_left ρ)))
  have hfinal : Tendsto (fun k : ℕ => cdf (t + ρ - 1 / ((k : ℝ) + 1)))
      atTop (𝓝 (cdf (t + ρ))) := by
    refine cdf_continuous.continuousAt.tendsto.comp ?_
    have hk : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have hone : Tendsto (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      hk.const_div_atTop (1:ℝ)
    have hconst : Tendsto (fun _ : ℕ => (t + ρ)) atTop (𝓝 (t + ρ)) := tendsto_const_nhds
    have hsub : Tendsto (fun k : ℕ => (t + ρ) - 1 / ((k : ℝ) + 1)) atTop (𝓝 ((t + ρ) - 0)) :=
      hconst.sub hone
    simpa using hsub
  have hbound : ∀ᶠ k : ℕ in atTop,
      cdf (t + ρ - 1 / ((k : ℝ) + 1)) ≤ ∫ x in nbhd U ρ, dens x :=
    Eventually.of_forall fun k => hmain (1 / ((k : ℝ) + 1)) (by positivity)
  exact le_of_tendsto hfinal hbound

end

end Commons.Analysis.GaussianMeasure
