import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts
import Submission.Work.FIArea6Hecke.ZFRDefs
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_lower_bound_near_one
import Submission.Work.FIArea6Hecke.R.heckeArch_lower_bound_near_one
import Submission.Work.FIArea6Hecke.R.riemannZeta_lower_bound_near_one
import Submission.Work.FIArea6Hecke.R.axisBadPoly_lower_bound

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

noncomputable section

theorem noCompletion_aux (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (hd : 1 ≤ d)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hexc : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → Work.FIArea5.S16Hecke.IsUnitMod4d d z →
      Work.FIArea5.S16Hecke.psi chi m z = 1)
    (hA : ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      c ≤ ‖LSeries Work.FIArea6Hecke.R.axisChi4 (σ : ℂ)‖)
    (hB : ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      c ≤ ‖Work.FITop4.Bridge.heckeArch d m (σ : ℂ)‖)
    (hC : ∃ δ : ℝ, 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      1 / (2 * (σ - 1)) ≤ ‖riemannZeta (σ : ℂ)‖)
    (hD : ∃ c : ℝ, 0 < c ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      c ≤ ‖Work.FIArea6Hecke.R.axisBadPoly d (σ : ℂ)‖) :
    ¬ ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) := by
  classical
  -- ### Step 1: the Hecke coefficients only see the primary elements
  have hlam : Work.FIArea5.S16Hecke.heckeLam chi m
      = Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.principalStrict d) 0 := by
    funext n
    unfold Work.FIArea5.S16Hecke.heckeLam
    refine Finset.sum_congr rfl ?_
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨-, hprim, -⟩ := hz
    by_cases hu : Work.FIArea5.S16Hecke.IsUnitMod4d d z
    · rw [hexc z hprim hu]
      simp only [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one,
        Work.FIArea6Hecke.principalStrict_of_unit hu]
    · simp only [Work.FIArea5.S16Hecke.psi, hchi.2 z hu,
        Work.FIArea6Hecke.principalStrict_of_not_unit hu, zero_mul]
  have hLSeries : ∀ s : ℂ, Work.FIArea5.S16Hecke.heckeLSeries chi m s
      = Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea6Hecke.principalStrict d) 0 s :=
    fun s => LSeries_congr (fun {n} _ => congrFun hlam n) s
  -- ### Step 2: the model function and its analyticity
  set G : ℂ → ℂ := fun s => Work.FITop4.Bridge.heckeArch d m s *
      (riemannZeta s * LSeries Work.FIArea6Hecke.R.axisChi4 s
        * Work.FIArea6Hecke.R.axisBadPoly d s) with hG
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hbase : (((4 * (d : ℝ)) / Real.pi) : ℂ) ≠ 0 := by
    have hd0 : (0 : ℝ) < 4 * (d : ℝ) := by
      have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    exact_mod_cast (ne_of_gt (div_pos hd0 Real.pi_pos))
  have h1an : AnalyticOn ℂ (fun s : ℂ => Work.FITop4.Bridge.heckeArch d m s)
      {s : ℂ | 1 < s.re} := by
    refine DifferentiableOn.analyticOn ?_ hU
    intro s hs
    have hs' : 1 < s.re := hs
    have hne : ∀ n : ℕ, s + ((|(m : ℝ)| / 2 : ℝ) : ℂ) ≠ -(n : ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
      have hpos : (0 : ℝ) < s.re + |(m : ℝ)| / 2 := by
        have h2 : (0 : ℝ) < s.re := by linarith
        linarith [abs_nonneg (m : ℝ)]
      have hneg : -(n : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg n)
      linarith
    refine (DifferentiableAt.mul ?_ ?_).differentiableWithinAt
    · exact differentiableAt_id.const_cpow (Or.inl hbase)
    · have hf : DifferentiableAt ℂ (fun w : ℂ => w + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) s :=
        differentiableAt_id.add_const _
      have hg : DifferentiableAt ℂ Complex.Gamma (s + ((|(m : ℝ)| / 2 : ℝ) : ℂ)) :=
        Complex.differentiableAt_Gamma _ hne
      exact DifferentiableAt.comp (f := fun w : ℂ => w + ((|(m : ℝ)| / 2 : ℝ) : ℂ))
        (x := s) hg hf
  have h2an : AnalyticOn ℂ riemannZeta {s : ℂ | 1 < s.re} := by
    refine DifferentiableOn.analyticOn ?_ hU
    intro s hs
    have hs' : 1 < s.re := hs
    have hs1 : s ≠ 1 := by intro h; rw [h] at hs'; norm_num at hs'
    exact (differentiableAt_riemannZeta hs1).differentiableWithinAt
  have h3an : AnalyticOn ℂ (LSeries Work.FIArea6Hecke.R.axisChi4) {s : ℂ | 1 < s.re} := by
    refine DifferentiableOn.analyticOn ?_ hU
    intro s hs
    exact (Work.FIArea6Hecke.R.differentiableAt_LSeries_axisChi4
      (show 1 < s.re from hs)).differentiableWithinAt
  have h4an : AnalyticOn ℂ (fun s : ℂ => Work.FIArea6Hecke.R.axisBadPoly d s)
      {s : ℂ | 1 < s.re} := by
    have hfac : ∀ p ∈ (4 * d).primeFactors,
        AnalyticOn ℂ (fun s : ℂ => (1 - (p : ℂ) ^ (-s)) *
          (1 - Work.FIArea6Hecke.R.axisChi4 p * (p : ℂ) ^ (-s))) {s : ℂ | 1 < s.re} := by
      intro p hp
      have hp0 : (p : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      refine DifferentiableOn.analyticOn ?_ hU
      intro s hs
      have hcp : DifferentiableAt ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) s :=
        differentiableAt_id.neg.const_cpow (Or.inl hp0)
      have hA : DifferentiableAt ℂ (fun s : ℂ => 1 - (p : ℂ) ^ (-s)) s := hcp.const_sub 1
      have hB : DifferentiableAt ℂ (fun s : ℂ =>
          1 - Work.FIArea6Hecke.R.axisChi4 p * (p : ℂ) ^ (-s)) s :=
        (hcp.const_mul (Work.FIArea6Hecke.R.axisChi4 p)).const_sub 1
      exact (hA.mul hB).differentiableWithinAt
    have hpr := Finset.analyticOn_prod (𝕜 := ℂ) (E := ℂ) (A := ℂ) (s := {s : ℂ | 1 < s.re})
      (N := (4 * d).primeFactors)
      (f := fun p : ℕ => fun s : ℂ => (1 - (p : ℂ) ^ (-s)) *
        (1 - Work.FIArea6Hecke.R.axisChi4 p * (p : ℂ) ^ (-s))) hfac
    have hfe : (∏ p ∈ (4 * d).primeFactors, fun s : ℂ => (1 - (p : ℂ) ^ (-s)) *
        (1 - Work.FIArea6Hecke.R.axisChi4 p * (p : ℂ) ^ (-s)))
        = (fun s : ℂ => ∏ p ∈ (4 * d).primeFactors, (1 - (p : ℂ) ^ (-s)) *
        (1 - Work.FIArea6Hecke.R.axisChi4 p * (p : ℂ) ^ (-s))) := by
      funext s
      rw [Finset.prod_apply]
    rw [hfe] at hpr
    simpa only [Work.FIArea6Hecke.R.axisBadPoly] using hpr
  have hGan : AnalyticOn ℂ G {s : ℂ | 1 < s.re} := by
    have h234 : AnalyticOn ℂ (fun s : ℂ => riemannZeta s * LSeries Work.FIArea6Hecke.R.axisChi4 s
        * Work.FIArea6Hecke.R.axisBadPoly d s) {s : ℂ | 1 < s.re} :=
      (h2an.mul h3an).mul h4an
    have h12 : AnalyticOn ℂ (fun s : ℂ => Work.FITop4.Bridge.heckeArch d m s *
        (riemannZeta s * LSeries Work.FIArea6Hecke.R.axisChi4 s
          * Work.FIArea6Hecke.R.axisBadPoly d s)) {s : ℂ | 1 < s.re} := h1an.mul h234
    rwa [hG]
  -- ### Step 3: the agreement, propagated to the whole half-plane
  rintro ⟨Lam, hAnal, hagr⟩
  have hagrG : ∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re → Lam s = G s := by
    intro s hs
    have h1s : 1 < s.re := by linarith [abs_nonneg (m : ℝ)]
    rw [hagr s hs, hLSeries s,
      Work.FIArea6Hecke.R.heckeLSeries_principalStrict_eq d hd h1s, hG]
  have hEqOn : Set.EqOn Lam G {s : ℂ | 1 < s.re} := by
    have hAnNhd : AnalyticOnNhd ℂ Lam {s : ℂ | 1 < s.re} :=
      (analyticOn_univ.mp hAnal).mono (fun s _ => Set.mem_univ s)
    have hGNhd : AnalyticOnNhd ℂ G {s : ℂ | 1 < s.re} := hU.analyticOn_iff_analyticOnNhd.mp hGan
    have hpc : IsPreconnected {s : ℂ | 1 < s.re} := (convex_halfSpace_re_gt 1).isPreconnected
    have hmem : {s : ℂ | 1 + |(m : ℝ)| / 2 < s.re} ∈ 𝓝 (((2 + |(m : ℝ)| / 2 : ℝ)) : ℂ) := by
      refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
      simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
      linarith [abs_nonneg (m : ℝ)]
    have hev : Lam =ᶠ[𝓝 (((2 + |(m : ℝ)| / 2 : ℝ)) : ℂ)] G := by
      filter_upwards [hmem] with s hs
      exact hagrG s hs
    have hz0 : (((2 + |(m : ℝ)| / 2 : ℝ)) : ℂ) ∈ {s : ℂ | 1 < s.re} := by
      simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
      linarith [abs_nonneg (m : ℝ)]
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hAnNhd hGNhd hpc hz0 hev
  -- ### Step 4: the contradiction as `σ → 1⁺`
  obtain ⟨cA, δA, hcA, hδA, hA'⟩ := hA
  obtain ⟨cB, δB, hcB, hδB, hB'⟩ := hB
  obtain ⟨δC, hδC, hC'⟩ := hC
  obtain ⟨cD, hcD, hD'⟩ := hD
  have hcont : ContinuousAt (fun σ : ℝ => Lam (σ : ℂ)) 1 :=
    (hAnal.analyticAt (s := Set.univ) (by simp)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  obtain ⟨δE, hδE, hE⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ σ : ℝ, |σ - 1| < δ → ‖Lam (σ : ℂ) - Lam (1 : ℂ)‖ < 1 := by
    have hb : ∀ᶠ σ : ℝ in 𝓝 (1 : ℝ), ‖Lam (σ : ℂ) - Lam (1 : ℂ)‖ < 1 := by
      have h1 := hcont (Metric.ball_mem_nhds (Lam (1 : ℂ)) (by norm_num : (0 : ℝ) < 1))
      filter_upwards [h1] with σ hσ
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] using hσ
    rw [Metric.eventually_nhds_iff] at hb
    obtain ⟨δ, hδ, h⟩ := hb
    exact ⟨δ, hδ, fun σ hσ => h (y := σ) (by simpa only [Real.dist_eq] using hσ)⟩
  set δ₀ : ℝ := min (min (min δA δB) (min δC δE)) 1 with hδ₀
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀]
    exact lt_min (lt_min (lt_min hδA hδB) (lt_min hδC hδE)) one_pos
  have hδ₀A : δ₀ ≤ δA := by
    rw [hδ₀]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₀B : δ₀ ≤ δB := by
    rw [hδ₀]; exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₀C : δ₀ ≤ δC := by
    rw [hδ₀]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₀E : δ₀ ≤ δE := by
    rw [hδ₀]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ₀1 : δ₀ ≤ 1 := by rw [hδ₀]; exact min_le_right _ _
  have hPpos : 0 < cA * cB * cD := by positivity
  set B₀ : ℝ := ‖Lam (1 : ℂ)‖ + 1 with hB₀
  have hB₀pos : 0 < B₀ := by rw [hB₀]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / δ₀ + 1) (2 * B₀ / (cA * cB * cD) + 1))
  have hN1 : 1 / δ₀ + 1 < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 2 * B₀ / (cA * cB * cD) + 1 < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hδinv : (0 : ℝ) < 1 / δ₀ := one_div_pos.mpr hδ₀pos
    linarith [hN1, hδinv]
  have hinv : 1 / (N : ℝ) < δ₀ := by
    rw [div_lt_iff₀ hNpos]
    have h1 : (1 : ℝ) / δ₀ < (N : ℝ) := by linarith [hN1]
    calc (1 : ℝ) = δ₀ * (1 / δ₀) := by field_simp
      _ < δ₀ * (N : ℝ) := mul_lt_mul_of_pos_left h1 hδ₀pos
  have hNB : B₀ < (N : ℝ) * (cA * cB * cD) / 2 := by
    have h2 : 2 * B₀ / (cA * cB * cD) < (N : ℝ) := by linarith
    rw [div_lt_iff₀ hPpos] at h2
    linarith
  set σ : ℝ := 1 + 1 / (N : ℝ) with hσ
  have hσ1 : 1 < σ := by
    rw [hσ]
    have hpos : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  have hσsub : σ - 1 = 1 / (N : ℝ) := by rw [hσ]; ring
  have hσlt : σ - 1 < δ₀ := by rw [hσsub]; exact hinv
  have hσmem : (σ : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
    exact hσ1
  have hσA : σ < 1 + δA := by linarith [hσlt, hδ₀A]
  have hσB : σ < 1 + δB := by linarith [hσlt, hδ₀B]
  have hσC : σ < 1 + δC := by linarith [hσlt, hδ₀C]
  have hσ2 : σ ≤ 2 := by linarith [hσlt, hδ₀1]
  have hup : ‖Lam (σ : ℂ)‖ < B₀ := by
    have h := hE σ (by
      rw [abs_of_pos (by linarith : (0 : ℝ) < σ - 1)]
      exact lt_of_lt_of_le hσlt hδ₀E)
    calc ‖Lam (σ : ℂ)‖ = ‖Lam (1 : ℂ) + (Lam (σ : ℂ) - Lam (1 : ℂ))‖ := by ring_nf
      _ ≤ ‖Lam (1 : ℂ)‖ + ‖Lam (σ : ℂ) - Lam (1 : ℂ)‖ := norm_add_le _ _
      _ < ‖Lam (1 : ℂ)‖ + 1 := by linarith
      _ = B₀ := hB₀
  have hdown : B₀ < ‖Lam (σ : ℂ)‖ := by
    have hnorm : ‖G (σ : ℂ)‖ = ‖Work.FITop4.Bridge.heckeArch d m (σ : ℂ)‖ *
        (‖riemannZeta (σ : ℂ)‖ * ‖LSeries Work.FIArea6Hecke.R.axisChi4 (σ : ℂ)‖ *
          ‖Work.FIArea6Hecke.R.axisBadPoly d (σ : ℂ)‖) := by
      rw [hG]
      simp only [norm_mul]
    have h1 : cB ≤ ‖Work.FITop4.Bridge.heckeArch d m (σ : ℂ)‖ := hB' σ hσ1 hσB
    have h2 : (N : ℝ) / 2 ≤ ‖riemannZeta (σ : ℂ)‖ := by
      have h := hC' σ hσ1 hσC
      have he : 1 / (2 * (σ - 1)) = (N : ℝ) / 2 := by
        rw [hσsub]
        field_simp
      rwa [he] at h
    have h3 : cA ≤ ‖LSeries Work.FIArea6Hecke.R.axisChi4 (σ : ℂ)‖ := hA' σ hσ1 hσA
    have h4 : cD ≤ ‖Work.FIArea6Hecke.R.axisBadPoly d (σ : ℂ)‖ := hD' σ hσ1 hσ2
    have hprod : (cB * ((N : ℝ) / 2)) * (cA * cD) ≤ ‖G (σ : ℂ)‖ := by
      rw [hnorm]
      have t1 : cB * ((N : ℝ) / 2) ≤
          ‖Work.FITop4.Bridge.heckeArch d m (σ : ℂ)‖ * ‖riemannZeta (σ : ℂ)‖ :=
        mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
      have t2 : cA * cD ≤ ‖LSeries Work.FIArea6Hecke.R.axisChi4 (σ : ℂ)‖ *
          ‖Work.FIArea6Hecke.R.axisBadPoly d (σ : ℂ)‖ :=
        mul_le_mul h3 h4 (le_of_lt hcD) (norm_nonneg _)
      have t3 : (0 : ℝ) ≤ cA * cD := by positivity
      have t4 : (0 : ℝ) ≤ ‖Work.FITop4.Bridge.heckeArch d m (σ : ℂ)‖ *
          ‖riemannZeta (σ : ℂ)‖ := by positivity
      calc (cB * ((N : ℝ) / 2)) * (cA * cD) ≤
            (‖Work.FITop4.Bridge.heckeArch d m (σ : ℂ)‖ * ‖riemannZeta (σ : ℂ)‖) *
              (‖LSeries Work.FIArea6Hecke.R.axisChi4 (σ : ℂ)‖ *
                ‖Work.FIArea6Hecke.R.axisBadPoly d (σ : ℂ)‖) := mul_le_mul t1 t2 t3 t4
        _ = ‖Work.FITop4.Bridge.heckeArch d m (σ : ℂ)‖ *
            (‖riemannZeta (σ : ℂ)‖ * ‖LSeries Work.FIArea6Hecke.R.axisChi4 (σ : ℂ)‖ *
              ‖Work.FIArea6Hecke.R.axisBadPoly d (σ : ℂ)‖) := by ring
    have hmid : B₀ < (cB * ((N : ℝ) / 2)) * (cA * cD) := by
      have heq : (cB * ((N : ℝ) / 2)) * (cA * cD) = (N : ℝ) * (cA * cB * cD) / 2 := by ring
      rw [heq]
      exact hNB
    calc B₀ < (cB * ((N : ℝ) / 2)) * (cA * cD) := hmid
      _ ≤ ‖G (σ : ℂ)‖ := hprod
      _ = ‖Lam (σ : ℂ)‖ := by rw [hEqOn hσmem]
  linarith

/-- **The exceptional case of the Hecke completion: a character that is trivial on the primary
units has no entire completion**, i.e. there is no entire `Λ` with
`Λ s = heckeArch d m s · L(s, χ)` for `re s > 1 + |m|/2`.

The proof: on the primary elements `ψ_m` agrees with the principal strict character `χ_0`
(`ψ_m(z) = 1` on primary units by hypothesis, and `= 0` on primary non-units by strictness), so
`heckeLSeries χ m = heckeLSeries χ_0 0`; on `re s > 1` the latter is
`ζ(s)·L(s,χ₄)·G_d(s)`, and the Euler product makes each of the last three factors bounded below
near `s = 1` while `ζ` blows up; an identity-theorem step propagates the agreement of `Λ` with
the model function from `re s > 1 + |m|/2` down to `re s > 1`, where continuity of `Λ` at `1`
contradicts the blow-up. -/
theorem noCompletion_of_primaryTrivial (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (hd : 1 ≤ d)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hexc : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → Work.FIArea5.S16Hecke.IsUnitMod4d d z →
      Work.FIArea5.S16Hecke.psi chi m z = 1) :
    ¬ ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d m s *
          Work.FIArea5.S16Hecke.heckeLSeries chi m s) :=
  noCompletion_aux d chi m hd hchi hexc
    axisChi4_LSeries_lower_bound_near_one
    (heckeArch_lower_bound_near_one d m hd)
    riemannZeta_lower_bound_near_one
    (axisBadPoly_lower_bound d hd)

end

end Work.FIArea6Hecke.R
