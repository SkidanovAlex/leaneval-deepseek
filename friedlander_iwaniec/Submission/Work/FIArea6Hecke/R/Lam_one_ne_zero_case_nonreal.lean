import Mathlib
import Submission.Work.FIArea6Hecke.R.LamOneNeZeroDefs
import Submission.Work.FIArea6Hecke.R.hecke_three_four_one
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Hecke.R.riemannZeta_lower_bound_near_one
import Submission.Work.FIArea6Hecke.R.heckeLSeries_one_eq_zeta_mul_chi4
import Submission.Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology
open Filter

noncomputable section

set_option maxHeartbeats 1000000

/-- The square of a strict character is a strict character. -/
lemma isCharMod4dStrict_mul_self {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    Work.FIArea5.S16Hecke.IsCharMod4dStrict d (fun z => chi z * chi z) := by
  obtain ⟨⟨h1, hmul, hb, hper, hvanish⟩, hstrict⟩ := hchi
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show chi 1 * chi 1 = 1
    rw [h1]; norm_num
  · intro z w
    show chi (z * w) * chi (z * w) = chi z * chi z * (chi w * chi w)
    rw [hmul z w]; ring
  · intro z
    rw [norm_mul]
    exact mul_le_one₀ (hb z) (norm_nonneg _) (hb z)
  · intro z w hzw
    show chi z * chi z = chi w * chi w
    rw [hper z w hzw]
  · intro z hz
    show chi z * chi z = 0
    rw [hvanish z hz, zero_mul]
  · intro z hz
    show chi z * chi z = 0
    rw [hstrict z hz, zero_mul]

/-- `heckeArch d 0` does not vanish on the open right half-plane. -/
lemma heckeArch_zero_ne_zero_of_pos_re {d : ℕ} (hd : 1 ≤ d) {s : ℂ} (hs : 0 < s.re) :
    Work.FITop4.Bridge.heckeArch d 0 s ≠ 0 := by
  rw [heckeArch_zero_eq]
  refine mul_ne_zero ?_ ?_
  · rw [Complex.cpow_ne_zero_iff]; exact Or.inl (archBase_ne_zero hd)
  · exact Complex.Gamma_ne_zero_of_re_pos hs

/-- **The non-real case of `Lam_one_ne_zero`.**  If `χ` is not a quadratic character on the
primary units (`χ z * χ z ≠ 1` for some primary unit), then `ψ = χ` is not real, `L(s,ψ²)` has an
entire completion (`heckeCompletionImprimitive`), and the `(3,4,1)`-inequality
`hecke_three_four_one` applied on the real axis `σ → 1⁺` gives
`1 ≤ |L(σ,ψ)|⁴|L(σ,ψ²)||L(σ,1)|³ → 0`, contradicting an entire completion with `Lam 1 = 0`. -/
theorem Lam_one_ne_zero_case_nonreal {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hne2 : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z * chi z ≠ 1)
    {Lam : ℂ → ℂ} (hAn : AnalyticOn ℂ Lam Set.univ)
    (hagr : ∀ s : ℂ, 1 < s.re →
      Lam s = Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries chi 0 s)
    (hzero : Lam 1 = 0) : False := by
  set chi2 : GaussianInt → ℂ := fun z => chi z * chi z with hchi2def
  have hchi2 : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi2 := isCharMod4dStrict_mul_self hchi
  have hne2' : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ Work.FIArea5.S16Hecke.psi chi2 0 z ≠ 1 := by
    obtain ⟨z, hz1, hz2, hz3⟩ := hne2
    refine ⟨z, hz1, hz2, ?_⟩
    have hpsi : Work.FIArea5.S16Hecke.psi chi2 0 z = chi z * chi z := by
      rw [Work.FIArea5.S16Hecke.psi, zpow_zero, mul_one, hchi2def]
    rw [hpsi]
    exact hz3
  obtain ⟨Lam2, hAn2, hagr2⟩ :=
    Work.FIArea6Hecke.R.heckeCompletionImprimitive d chi2 0 hd hchi2 hne2'
  have hagr2' : ∀ s : ℂ, 1 < s.re →
      Lam2 s = Work.FITop4.Bridge.heckeArch d 0 s *
        Work.FIArea5.S16Hecke.heckeLSeries chi2 0 s := by
    intro s hs
    have := hagr2 s (by simpa using hs)
    simpa using this
  have hLam_diff : DifferentiableAt ℂ Lam 1 :=
    hAn.differentiableOn.differentiableAt (by simp)
  have hslope : Tendsto (fun z : ℂ => slope Lam 1 z) (𝓝[≠] (1 : ℂ)) (𝓝 (deriv Lam 1)) :=
    hLam_diff.hasDerivAt.tendsto_slope
  have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ), ‖slope Lam 1 z‖ ≤ ‖deriv Lam 1‖ + 1 :=
    hslope.norm.eventually (eventually_le_nhds (by linarith))
  rw [eventually_nhdsWithin_iff] at hev
  obtain ⟨δC, hδCpos, hδC⟩ := Metric.eventually_nhds_iff.mp hev
  have hLam_bound : ∀ z : ℂ, dist z 1 < δC → z ≠ 1 →
      ‖Lam z‖ ≤ (‖deriv Lam 1‖ + 1) * ‖z - 1‖ := by
    intro z hz hzne
    have h1 := hδC hz hzne
    have hsl : slope Lam 1 z = (z - 1)⁻¹ * Lam z := by
      rw [slope, smul_eq_mul]
      simp [hzero]
    have hz1 : Lam z = (z - 1) * slope Lam 1 z := by
      rw [hsl]
      field_simp
    rw [hz1, norm_mul, mul_comm (‖deriv Lam 1‖ + 1) ‖z - 1‖]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have hLam2cont : ContinuousAt Lam2 1 := hAn2.continuousOn.continuousAt (by simp)
  obtain ⟨δM, hδMpos, hδM⟩ := Metric.continuousAt_iff.mp hLam2cont (1 : ℝ) (by norm_num)
  have harch1ne : Work.FITop4.Bridge.heckeArch d 0 (((1 : ℝ)) : ℂ) ≠ 0 :=
    heckeArch_zero_one_ne_zero hd
  obtain ⟨δ1, hδ1pos, hδ1⟩ := Metric.continuousAt_iff.mp (heckeArch_zero_continuousAt_one hd)
    (‖Work.FITop4.Bridge.heckeArch d 0 (((1 : ℝ)) : ℂ)‖ / 2)
    (by have := norm_pos_iff.mpr harch1ne; linarith)
  have hL4cont : ContinuousAt (fun z : ℂ => Work.FIArea6Hecke.R.chi4C.LFunction z) 1 :=
    (DirichletCharacter.differentiable_LFunction Work.FIArea6Hecke.R.chi4C_ne_one).continuous.continuousAt
  obtain ⟨δA, hδApos, hδA⟩ := Metric.continuousAt_iff.mp hL4cont (1 : ℝ) (by norm_num)
  set C : ℝ := ‖deriv Lam 1‖ + 1 with hCdef
  set M : ℝ := ‖Lam2 1‖ + 1 with hMdef
  set c₁ : ℝ := ‖Work.FITop4.Bridge.heckeArch d 0 (((1 : ℝ)) : ℂ)‖ / 2 with hc₁def
  set A₄ : ℝ := ‖Work.FIArea6Hecke.R.chi4C.LFunction 1‖ + 1 with hA₄def
  have hCpos : 0 ≤ C := by rw [hCdef]; positivity
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hA₄pos : 0 ≤ A₄ := by rw [hA₄def]; positivity
  have harch1pos : 0 < ‖Work.FITop4.Bridge.heckeArch d 0 (((1 : ℝ)) : ℂ)‖ :=
    norm_pos_iff.mpr harch1ne
  have hc₁pos : 0 < c₁ := by rw [hc₁def]; linarith
  set K : ℝ := (C / c₁) ^ 4 * (M / c₁) * (4 * A₄) ^ 3 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set δ : ℝ := min (δC / 2) (min (δM / 2)
      (min (δ1 / 2) (min (δA / 2) (min (1 / 2) (1 / (4 * K)))))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    refine lt_min (by linarith) (lt_min (by linarith) (lt_min (by linarith)
      (lt_min (by linarith) (lt_min (by norm_num) (by positivity)))))
  have hδleC : δ ≤ δC / 2 := le_trans (min_le_left _ _) le_rfl
  have hδleM : δ ≤ δM / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) le_rfl)
  have hδle1 : δ ≤ δ1 / 2 :=
    le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) le_rfl))
  have hδleA : δ ≤ δA / 2 :=
    le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) le_rfl)))
  have hδlehalf : δ ≤ 1 / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hδleK : δ ≤ 1 / (4 * K) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  set σ : ℝ := 1 + δ / 2 with hσdef
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
  have hσdist : dist (((σ : ℝ)) : ℂ) (1 : ℂ) < δC := by
    rw [dist_eq_norm]
    have h1 : (((σ : ℝ)) : ℂ) - 1 = (((σ - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < σ - 1)]
    linarith [hδleC]
  have hσne : (((σ : ℝ)) : ℂ) ≠ 1 := by
    simp only [ne_eq, Complex.ofReal_eq_one]
    linarith
  have hA : ‖Lam (((σ : ℝ)) : ℂ)‖ ≤ C * (σ - 1) := by
    have h := hLam_bound (((σ : ℝ)) : ℂ) hσdist hσne
    have h2 : ‖(((σ : ℝ)) : ℂ) - 1‖ = σ - 1 := by
      rw [show (((σ : ℝ)) : ℂ) - 1 = (((σ - 1 : ℝ)) : ℂ) by push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < σ - 1)]
    rw [h2, hCdef] at h
    exact h
  have hB : ‖Lam2 (((σ : ℝ)) : ℂ)‖ ≤ M := by
    have hdist : dist (((σ : ℝ)) : ℂ) (1 : ℂ) < δM := by
      rw [dist_eq_norm]
      have h1 : (((σ : ℝ)) : ℂ) - 1 = (((σ - 1 : ℝ)) : ℂ) := by push_cast; ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < σ - 1)]
      linarith [hδleM]
    have h := hδM hdist
    rw [dist_eq_norm] at h
    have h2 : ‖Lam2 (((σ : ℝ)) : ℂ)‖ ≤ ‖Lam2 (((σ : ℝ)) : ℂ) - Lam2 1‖ + ‖Lam2 1‖ := by
      have := norm_add_le (Lam2 (((σ : ℝ)) : ℂ) - Lam2 1) (Lam2 1)
      simpa using this
    rw [hMdef]; linarith
  have hc1bound : c₁ ≤ ‖Work.FITop4.Bridge.heckeArch d 0 (((σ : ℝ)) : ℂ)‖ := by
    have hdist : dist ((σ : ℝ)) (1 : ℝ) < δ1 := by
      rw [Real.dist_eq, abs_of_pos (by linarith : (0:ℝ) < σ - 1)]
      linarith [hδle1]
    have h := hδ1 hdist
    have h2 : ‖Work.FITop4.Bridge.heckeArch d 0 (((1 : ℝ)) : ℂ)‖
        - ‖Work.FITop4.Bridge.heckeArch d 0 (((σ : ℝ)) : ℂ)‖
        ≤ dist (Work.FITop4.Bridge.heckeArch d 0 (((σ : ℝ)) : ℂ))
            (Work.FITop4.Bridge.heckeArch d 0 (((1 : ℝ)) : ℂ)) := by
      rw [dist_eq_norm, norm_sub_rev]
      exact norm_sub_norm_le _ _
    rw [hc₁def]; linarith
  have hA4bound : ‖LSeries Work.FIArea6Hecke.R.axisChi4 (((σ : ℝ)) : ℂ)‖ ≤ A₄ := by
    have hdist : dist (((σ : ℝ)) : ℂ) (1 : ℂ) < δA := by
      rw [dist_eq_norm]
      have h1 : (((σ : ℝ)) : ℂ) - 1 = (((σ - 1 : ℝ)) : ℂ) := by push_cast; ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < σ - 1)]
      linarith [hδleA]
    have h := hδA hdist
    rw [dist_eq_norm] at h
    have h2 : ‖Work.FIArea6Hecke.R.chi4C.LFunction (((σ : ℝ)) : ℂ)‖ ≤ A₄ := by
      have h3 : ‖Work.FIArea6Hecke.R.chi4C.LFunction (((σ : ℝ)) : ℂ)‖
          ≤ ‖Work.FIArea6Hecke.R.chi4C.LFunction (((σ : ℝ)) : ℂ)
              - Work.FIArea6Hecke.R.chi4C.LFunction 1‖
            + ‖Work.FIArea6Hecke.R.chi4C.LFunction 1‖ := by
        have := norm_add_le (Work.FIArea6Hecke.R.chi4C.LFunction (((σ : ℝ)) : ℂ)
          - Work.FIArea6Hecke.R.chi4C.LFunction 1) (Work.FIArea6Hecke.R.chi4C.LFunction 1)
        simpa using this
      rw [hA₄def]; linarith
    rw [LSeries_axisChi4_eq_LFunction (by simpa using hσ1)]
    exact h2
  have hσpos : (0 : ℝ) < σ := by linarith
  have hArchnz : Work.FITop4.Bridge.heckeArch d 0 (((σ : ℝ)) : ℂ) ≠ 0 :=
    heckeArch_zero_ne_zero_of_pos_re hd (by rw [Complex.ofReal_re]; exact hσpos)
  have hLval₁ : ‖Work.FIArea5.S16Hecke.heckeLSeries chi 0 (((σ : ℝ)) : ℂ)‖
      ≤ C * (σ - 1) / c₁ := by
    have h := hagr (((σ : ℝ)) : ℂ) (by simpa using hσ1)
    have hdiv : Work.FIArea5.S16Hecke.heckeLSeries chi 0 (((σ : ℝ)) : ℂ)
        = Lam (((σ : ℝ)) : ℂ) / Work.FITop4.Bridge.heckeArch d 0 (((σ : ℝ)) : ℂ) := by
      rw [h]; field_simp
    rw [hdiv, norm_div]
    exact div_le_div₀ (by positivity) hA hc₁pos hc1bound
  have hLval₂ : ‖Work.FIArea5.S16Hecke.heckeLSeries chi2 0 (((σ : ℝ)) : ℂ)‖ ≤ M / c₁ := by
    have h := hagr2' (((σ : ℝ)) : ℂ) (by simpa using hσ1)
    have hdiv : Work.FIArea5.S16Hecke.heckeLSeries chi2 0 (((σ : ℝ)) : ℂ)
        = Lam2 (((σ : ℝ)) : ℂ) / Work.FITop4.Bridge.heckeArch d 0 (((σ : ℝ)) : ℂ) := by
      rw [h]; field_simp
    rw [hdiv, norm_div]
    exact div_le_div₀ hMpos.le hB hc₁pos hc1bound
  have hLval₃ : ‖Work.FIArea5.S16Hecke.heckeLSeries (fun _ : GaussianInt => (1 : ℂ)) 0
      (((σ : ℝ)) : ℂ)‖ ≤ 4 * A₄ / (σ - 1) := by
    rw [Work.FIArea6Hecke.R.heckeLSeries_one_eq_zeta_mul_chi4 (by simpa using hσ1),
      norm_mul, norm_mul]
    have hζ : ‖riemannZeta (((σ : ℝ)) : ℂ)‖ ≤ 2 / (σ - 1) :=
      Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one hσ1 hσ2
    have h2s : ‖(1 : ℂ) - (2 : ℂ) ^ (-(((σ : ℝ)) : ℂ))‖ ≤ 2 := by
      have h1 : ‖(2 : ℂ) ^ (-(((σ : ℝ)) : ℂ))‖ ≤ (1 : ℝ) := by
        rw [show (2 : ℂ) = (((2 : ℝ)) : ℂ) from by norm_num,
          Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2)]
        simp only [Complex.neg_re, Complex.ofReal_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
      calc ‖(1 : ℂ) - (2 : ℂ) ^ (-(((σ : ℝ)) : ℂ))‖
          ≤ ‖(1 : ℂ)‖ + ‖(2 : ℂ) ^ (-(((σ : ℝ)) : ℂ))‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by rw [norm_one]; linarith
        _ = 2 := by norm_num
    calc ‖riemannZeta (((σ : ℝ)) : ℂ)‖ * ‖LSeries Work.FIArea6Hecke.R.axisChi4 (((σ : ℝ)) : ℂ)‖
          * ‖(1 : ℂ) - (2 : ℂ) ^ (-(((σ : ℝ)) : ℂ))‖
        ≤ (2 / (σ - 1)) * A₄ * 2 := by
          refine mul_le_mul (mul_le_mul hζ hA4bound (norm_nonneg _) (by positivity)) h2s
            (norm_nonneg _) (by positivity)
      _ = 4 * A₄ / (σ - 1) := by ring
  have h341 : 1 ≤ (C * (σ - 1) / c₁) ^ 4 * (M / c₁) * (4 * A₄ / (σ - 1)) ^ 3 := by
    have h := Work.FIArea6Hecke.R.hecke_three_four_one d hd chi hchi 0 (σ := σ) (t := 0) hσ1
    have h' : 1 ≤ ‖Work.FIArea5.S16Hecke.heckeLSeries chi 0 (((σ : ℝ)) : ℂ)‖ ^ 4
        * ‖Work.FIArea5.S16Hecke.heckeLSeries chi2 0 (((σ : ℝ)) : ℂ)‖
        * ‖Work.FIArea5.S16Hecke.heckeLSeries (fun _ : GaussianInt => (1 : ℂ)) 0
            (((σ : ℝ)) : ℂ)‖ ^ 3 := by
      simpa [hchi2def] using h
    refine le_trans h' ?_
    have h1 : ‖Work.FIArea5.S16Hecke.heckeLSeries chi 0 (((σ : ℝ)) : ℂ)‖ ^ 4
        ≤ (C * (σ - 1) / c₁) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hLval₁ 4
    have h3 : ‖Work.FIArea5.S16Hecke.heckeLSeries (fun _ : GaussianInt => (1 : ℂ)) 0
        (((σ : ℝ)) : ℂ)‖ ^ 3 ≤ (4 * A₄ / (σ - 1)) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _) hLval₃ 3
    refine mul_le_mul (mul_le_mul h1 hLval₂ (norm_nonneg _) (by positivity)) h3
      (by positivity) (by positivity)
  have hfinal : (C * (σ - 1) / c₁) ^ 4 * (M / c₁) * (4 * A₄ / (σ - 1)) ^ 3
      = K * (σ - 1) := by
    rw [hKdef]
    have hσm1 : σ - 1 ≠ 0 := by linarith
    field_simp
  have hsmall : K * (σ - 1) < 1 := by
    have h1 : σ - 1 = δ / 2 := by rw [hσdef]; ring
    rw [h1]
    have h2 : K * δ ≤ K * (1 / (4 * K)) := mul_le_mul_of_nonneg_left hδleK hKpos.le
    have h3 : K * (1 / (4 * K)) = 1 / 4 := by
      have hK0 : K ≠ 0 := hKpos.ne'
      field_simp
      try ring
    nlinarith [h2, h3, hKpos]
  rw [hfinal] at h341
  linarith

end

end Work.FIArea6Hecke.R
