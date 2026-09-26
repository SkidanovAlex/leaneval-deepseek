import Mathlib
import Submission.Work.Smooth.JordanSeparation.Unconditional
import Submission.Work.Smooth.JordanSeparation.LocalSides
import Submission.Work.Smooth.JordanSeparation.LocalTangency
import Submission.Work.Smooth.JordanSeparation.offset_notMem_trace

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

lemma collar_detV_locE_locN (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) :
    detV (locE c) (locN c) = 1 := by
  have h : (starRingEnd ℂ) (locE c) * (Complex.I * locE c)
      = ((Complex.normSq (locE c) : ℝ) : ℂ) * Complex.I := by
    calc (starRingEnd ℂ) (locE c) * (Complex.I * locE c)
        = ((starRingEnd ℂ) (locE c) * locE c) * Complex.I := by ring
      _ = ((Complex.normSq (locE c) : ℝ) : ℂ) * Complex.I := by
            rw [← Complex.normSq_eq_conj_mul_self]
  rw [detV_def, locN, h]
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero]
  rw [Complex.normSq_eq_norm_sq, norm_locE c hreg]
  norm_num

lemma collar_norm_locN (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) : ‖locN c‖ = 1 := by
  rw [locN, norm_mul, Complex.norm_I, one_mul]
  exact norm_locE c hreg

lemma collar_detV_decomp (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0) (w : ℂ) :
    w = (detV w (locN c) : ℂ) * locE c + (detV (locE c) w : ℂ) * locN c := by
  have hnorm : (locE c).re ^ 2 + (locE c).im ^ 2 = 1 := by
    have h := norm_locE c hreg
    have h2 : ‖locE c‖ ^ 2 = (1:ℝ) := by rw [h]; norm_num
    rw [Complex.sq_norm, Complex.normSq_apply] at h2
    nlinarith [h2]
  apply Complex.ext
  · simp only [detV_eq, locN, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    linear_combination (-w.re) * hnorm
  · simp only [detV_eq, locN, Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    linear_combination (-w.im) * hnorm

theorem collar_ray_side (c : SmoothPlaneCurve) (hreg : deriv c.γ 0 ≠ 0)
    (hs : c.toPlaneCurve.IsSimple) {κ : ℝ} (hκ : 0 < κ) :
    ∃ μ ε : ℝ, 0 < μ ∧ 0 < ε ∧
      (∀ t u : ℝ, t ∈ Ioo (-μ) μ → u ∈ Ioo (0:ℝ) ε → locPhi c (t, u) ∉ c.trace) ∧
      (∀ t u : ℝ, t ∈ Ioo (-μ) μ → u ∈ Ioo (-ε) (0:ℝ) → locPhi c (t, u) ∉ c.trace) ∧
      (∀ w : ℂ, κ * |detV w (locN c)| < detV (locE c) w →
        ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
          c.γ 0 + (lam : ℂ) * w ∈ locPhi c '' (Ioo (-μ) μ ×ˢ Ioo (0:ℝ) ε)) ∧
      (∀ w : ℂ, detV (locE c) w < -κ * |detV w (locN c)| →
        ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ lam : ℝ, 0 < lam → lam < lam0 →
          c.γ 0 + (lam : ℂ) * w ∈ locPhi c '' (Ioo (-μ) μ ×ˢ Ioo (-ε) (0:ℝ))) := by
  obtain ⟨r, hr, hmono⟩ := exists_locS_strictMono c hreg
  obtain ⟨η₀, hη₀, hRbound⟩ := exists_locR_le_mul_locS c hreg hκ
  set R : ℝ := min (min r η₀) (Real.pi / 4) with hRdef
  have hRpos : 0 < R := lt_min (lt_min hr hη₀) (by positivity)
  have hRr : R ≤ r := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRη : R ≤ η₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hRπ : R ≤ Real.pi / 4 := min_le_right _ _
  have hmonoR : StrictMonoOn (locS c) (Icc (-R) R) :=
    hmono.mono (fun x hx => ⟨by linarith [hRr, hx.1], by linarith [hRr, hx.2]⟩)
  have hbound : ∀ t : ℝ, |t| < R → |locR c t| ≤ κ * |locS c t| := by
    intro t ht
    rcases eq_or_lt_of_le (abs_nonneg t) with h0 | hpos
    · have ht0 : t = 0 := abs_eq_zero.mp h0.symm
      subst ht0; simp
    · exact hRbound t hpos (lt_of_lt_of_le ht hRη)
  set δ : ℝ := R / 4 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδR : δ < R := by rw [hδdef]; linarith
  have hδπ : δ + δ < 2 * Real.pi := by rw [hδdef]; nlinarith [hRπ, Real.pi_pos]
  obtain ⟨ε₁, hε₁pos, hnoReentry⟩ := exists_no_reentry c hs hδpos hδπ
  set ε : ℝ := ε₁ / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεlt : ε < ε₁ := by rw [hεdef]; linarith
  have hδmem : δ ∈ Icc (-R) R := ⟨by linarith [hRpos], le_of_lt hδR⟩
  have hδmem' : -δ ∈ Icc (-R) R := ⟨by linarith [hδR], by linarith [hδpos]⟩
  have h0mem : (0:ℝ) ∈ Icc (-R) R := ⟨by linarith [hRpos], by linarith [hRpos]⟩
  have hSδ : 0 < locS c δ := by
    have h := hmonoR h0mem hδmem (by linarith [hδpos])
    rwa [locS_zero] at h
  have hSneg : locS c (-δ) < 0 := by
    have h := hmonoR hδmem' h0mem (by linarith [hδpos])
    rwa [locS_zero] at h
  set ρ : ℝ := min (locS c δ) (-(locS c (-δ))) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min hSδ (by linarith)
  have hIVT : ∀ A : ℝ, |A| < ρ → ∃ t : ℝ, t ∈ Ioo (-δ) δ ∧ locS c t = A := by
    intro A hA
    have hAr : -ρ < A ∧ A < ρ := abs_lt.mp hA
    have hle1 : locS c (-δ) ≤ A := by
      have hh : ρ ≤ -(locS c (-δ)) := by rw [hρdef]; exact min_le_right _ _
      linarith
    have hle2 : A ≤ locS c δ := by
      have hh : ρ ≤ locS c δ := by rw [hρdef]; exact min_le_left _ _
      linarith
    obtain ⟨t, ht, htval⟩ := intermediate_value_Icc (show -δ ≤ δ by linarith [hδpos])
      (continuous_locS c).continuousOn (show A ∈ Icc (locS c (-δ)) (locS c δ) from ⟨hle1, hle2⟩)
    refine ⟨t, ⟨?_, ?_⟩, htval⟩
    · rcases eq_or_lt_of_le ht.1 with h | h
      · exfalso
        have hAeq : A = locS c (-δ) := by rw [← htval]; exact congrArg (locS c) h.symm
        have hh : ρ ≤ -(locS c (-δ)) := by rw [hρdef]; exact min_le_right _ _
        linarith
      · exact h
    · rcases eq_or_lt_of_le ht.2 with h | h
      · exfalso
        have hAeq : A = locS c δ := by rw [← htval]; exact congrArg (locS c) h
        have hh : ρ ≤ locS c δ := by rw [hρdef]; exact min_le_left _ _
        linarith
      · exact h
  refine ⟨δ, ε, hδpos, hεpos, ?_, ?_, ?_, ?_⟩
  · intro t u ht hu hmem
    obtain ⟨t₁, ht₁⟩ := (PlaneCurve.mem_trace_iff c.toPlaneCurve (locPhi c (t, u))).mpr hmem
    have htabs : |t| ≤ δ := le_of_lt (abs_lt.mpr ⟨ht.1, ht.2⟩)
    have hdist : ‖c.γ t₁ - c.γ t‖ < ε₁ := by
      have hsub : c.γ t₁ - c.γ t = (u : ℂ) * locN c := by rw [ht₁, locPhi]; ring
      rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, collar_norm_locN c hreg, mul_one,
        abs_of_pos hu.1]
      exact lt_of_lt_of_le hu.2 hεlt.le
    obtain ⟨k, hk⟩ : ∃ k : ℤ, |t₁ - t - (k : ℝ) * (2 * Real.pi)| < δ := by
      by_contra hcon
      have hfar : ∀ k : ℤ, δ ≤ |t₁ - t - (k : ℝ) * (2 * Real.pi)| :=
        fun k => not_lt.mp (fun hlt => hcon ⟨k, hlt⟩)
      have := hnoReentry t htabs t₁ hfar
      linarith
    set t₁' : ℝ := t₁ - (k : ℝ) * (2 * Real.pi) with ht₁'def
    have hper : c.γ t₁' = c.γ t₁ := by
      have h := PlaneCurve.apply_add_int_mul c.toPlaneCurve t₁' k
      rw [show t₁' + (k : ℝ) * (2 * Real.pi) = t₁ from by rw [ht₁'def]; ring] at h
      exact h.symm
    have ht₁'R : |t₁'| < R := by
      have h1 : t₁' = (t₁ - t - (k : ℝ) * (2 * Real.pi)) + t := by rw [ht₁'def]; ring
      calc |t₁'| = |(t₁ - t - (k:ℝ)*(2*Real.pi)) + t| := by rw [h1]
        _ ≤ |t₁ - t - (k:ℝ)*(2*Real.pi)| + |t| := abs_add_le _ _
        _ < δ + δ := by linarith [hk, htabs]
        _ ≤ R := by rw [hδdef]; linarith
    have ht₁'R' : -R < t₁' ∧ t₁' < R := abs_lt.mp ht₁'R
    have hphi : locPhi c (t₁', 0) = locPhi c (t, u) := by
      have hγ : c.γ t₁' = c.γ t + (u:ℂ) * locN c := by rw [hper, ht₁]; rfl
      show c.γ t₁' + ((0:ℝ):ℂ) * locN c = c.γ t + (u:ℂ) * locN c
      rw [hγ]; simp
    have hm1 : (t, u) ∈ Ioo (-R) R ×ˢ Ioo (-ε) ε :=
      ⟨⟨by linarith [ht.1, hδR], by linarith [ht.2, hδR]⟩,
        ⟨by linarith [hu.1, hεpos], hu.2⟩⟩
    have hm2 : (t₁', 0) ∈ Ioo (-R) R ×ˢ Ioo (-ε) ε :=
      ⟨⟨ht₁'R'.1, ht₁'R'.2⟩, ⟨by linarith [hεpos], hεpos⟩⟩
    have hzero : u = 0 := congrArg Prod.snd (locPhi_injOn c hreg hmonoR hm1 hm2 hphi.symm)
    exact absurd hzero (ne_of_gt hu.1)
  · intro t u ht hu hmem
    obtain ⟨t₁, ht₁⟩ := (PlaneCurve.mem_trace_iff c.toPlaneCurve (locPhi c (t, u))).mpr hmem
    have htabs : |t| ≤ δ := le_of_lt (abs_lt.mpr ⟨ht.1, ht.2⟩)
    have hdist : ‖c.γ t₁ - c.γ t‖ < ε₁ := by
      have hsub : c.γ t₁ - c.γ t = (u : ℂ) * locN c := by rw [ht₁, locPhi]; ring
      rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, collar_norm_locN c hreg, mul_one,
        abs_of_neg hu.2]
      linarith [hu.1, hεlt]
    obtain ⟨k, hk⟩ : ∃ k : ℤ, |t₁ - t - (k : ℝ) * (2 * Real.pi)| < δ := by
      by_contra hcon
      have hfar : ∀ k : ℤ, δ ≤ |t₁ - t - (k : ℝ) * (2 * Real.pi)| :=
        fun k => not_lt.mp (fun hlt => hcon ⟨k, hlt⟩)
      have := hnoReentry t htabs t₁ hfar
      linarith
    set t₁' : ℝ := t₁ - (k : ℝ) * (2 * Real.pi) with ht₁'def
    have hper : c.γ t₁' = c.γ t₁ := by
      have h := PlaneCurve.apply_add_int_mul c.toPlaneCurve t₁' k
      rw [show t₁' + (k : ℝ) * (2 * Real.pi) = t₁ from by rw [ht₁'def]; ring] at h
      exact h.symm
    have ht₁'R : |t₁'| < R := by
      have h1 : t₁' = (t₁ - t - (k : ℝ) * (2 * Real.pi)) + t := by rw [ht₁'def]; ring
      calc |t₁'| = |(t₁ - t - (k:ℝ)*(2*Real.pi)) + t| := by rw [h1]
        _ ≤ |t₁ - t - (k:ℝ)*(2*Real.pi)| + |t| := abs_add_le _ _
        _ < δ + δ := by linarith [hk, htabs]
        _ ≤ R := by rw [hδdef]; linarith
    have ht₁'R' : -R < t₁' ∧ t₁' < R := abs_lt.mp ht₁'R
    have hphi : locPhi c (t₁', 0) = locPhi c (t, u) := by
      have hγ : c.γ t₁' = c.γ t + (u:ℂ) * locN c := by rw [hper, ht₁]; rfl
      show c.γ t₁' + ((0:ℝ):ℂ) * locN c = c.γ t + (u:ℂ) * locN c
      rw [hγ]; simp
    have hm1 : (t, u) ∈ Ioo (-R) R ×ˢ Ioo (-ε) ε :=
      ⟨⟨by linarith [ht.1, hδR], by linarith [ht.2, hδR]⟩,
        ⟨hu.1, by linarith [hu.2, hεpos]⟩⟩
    have hm2 : (t₁', 0) ∈ Ioo (-R) R ×ˢ Ioo (-ε) ε :=
      ⟨⟨ht₁'R'.1, ht₁'R'.2⟩, ⟨by linarith [hεpos], hεpos⟩⟩
    have hzero : u = 0 := congrArg Prod.snd (locPhi_injOn c hreg hmonoR hm1 hm2 hphi.symm)
    exact absurd hzero (ne_of_lt hu.2)
  · intro w hcond
    set a : ℝ := detV w (locN c) with hadef
    set b : ℝ := detV (locE c) w with hbdef
    set D : ℝ := |a| + |b| + κ * |a| + 1 with hDdef
    have hDpos : 0 < D := by
      rw [hDdef]
      have h1 := mul_nonneg hκ.le (abs_nonneg a)
      linarith [h1, abs_nonneg a, abs_nonneg b]
    have hXpos : 0 < min (ρ/2) (ε/2) := lt_min (by linarith) (by linarith)
    refine ⟨min (ρ/2) (ε/2) / D, div_pos hXpos hDpos, ?_⟩
    intro lam lampos hlam
    have hx : lam * D < min (ρ/2) (ε/2) := by
      have h1 := mul_lt_mul_of_pos_right hlam hDpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h1
    have haD : |a| ≤ D := by
      rw [hDdef]
      have h1 := mul_nonneg hκ.le (abs_nonneg a)
      linarith [h1, abs_nonneg b]
    have hbD : |b| + κ * |a| ≤ D := by
      rw [hDdef]; linarith [abs_nonneg a]
    have hA : |lam * a| < ρ := by
      rw [abs_mul, abs_of_pos lampos]
      have h2 : lam * |a| ≤ lam * D := mul_le_mul_of_nonneg_left haD lampos.le
      have h3 : min (ρ/2) (ε/2) ≤ ρ/2 := min_le_left _ _
      linarith [h2, hx, h3]
    have hB : lam * (|b| + κ * |a|) < ε := by
      have h2 : lam * (|b| + κ * |a|) ≤ lam * D := mul_le_mul_of_nonneg_left hbD lampos.le
      have h3 : min (ρ/2) (ε/2) ≤ ε/2 := min_le_right _ _
      linarith [h2, hx, h3]
    obtain ⟨t, htIoo, htval⟩ := hIVT (lam * a) hA
    have htR : |t| < R := by
      have h := abs_lt.mpr htIoo
      linarith [hδR]
    have hRt : |locR c t| ≤ κ * (lam * |a|) := by
      calc |locR c t| ≤ κ * |locS c t| := hbound t htR
        _ = κ * (lam * |a|) := by rw [htval, abs_mul, abs_of_pos lampos]
    have hkl : κ * (lam * |a|) = lam * (κ * |a|) := by ring
    have hu1 : 0 < lam * b - locR c t := by
      have h3 : locR c t ≤ lam * (κ * |a|) := by
        have h := le_trans (le_abs_self (locR c t)) hRt
        linarith [h, hkl]
      have h4 : lam * (κ * |a|) < lam * b := mul_lt_mul_of_pos_left hcond lampos
      linarith [h3, h4]
    have hu2 : lam * b - locR c t < ε := by
      have h3 : -(lam * (κ * |a|)) ≤ locR c t := by
        have h4 := neg_abs_le (locR c t)
        linarith [hRt, h4, hkl]
      have h5 : lam * b ≤ lam * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) lampos.le
      have h6 : lam * b - locR c t ≤ lam * (|b| + κ * |a|) := by linarith [h3, h5]
      linarith [h6, hB, hεpos]
    have hdec := collar_detV_decomp c hreg w
    rw [← hadef, ← hbdef] at hdec
    refine ⟨(t, lam * b - locR c t), ⟨htIoo, ⟨hu1, hu2⟩⟩, ?_⟩
    have hγt : c.γ t = c.γ 0 + (locS c t : ℂ) * locE c + (locR c t : ℂ) * locN c := by
      have h := loc_reconstruction c hreg (c.γ t)
      simpa only [locS, locR] using h
    show locPhi c (t, lam * b - locR c t) = c.γ 0 + (lam : ℂ) * w
    rw [hdec]
    simp only [locPhi]
    rw [hγt, htval]
    push_cast
    ring
  · intro w hcond
    set a : ℝ := detV w (locN c) with hadef
    set b : ℝ := detV (locE c) w with hbdef
    set D : ℝ := |a| + |b| + κ * |a| + 1 with hDdef
    have hDpos : 0 < D := by
      rw [hDdef]
      have h1 := mul_nonneg hκ.le (abs_nonneg a)
      linarith [h1, abs_nonneg a, abs_nonneg b]
    have hXpos : 0 < min (ρ/2) (ε/2) := lt_min (by linarith) (by linarith)
    refine ⟨min (ρ/2) (ε/2) / D, div_pos hXpos hDpos, ?_⟩
    intro lam lampos hlam
    have hx : lam * D < min (ρ/2) (ε/2) := by
      have h1 := mul_lt_mul_of_pos_right hlam hDpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h1
    have haD : |a| ≤ D := by
      rw [hDdef]
      have h1 := mul_nonneg hκ.le (abs_nonneg a)
      linarith [h1, abs_nonneg b]
    have hbD : |b| + κ * |a| ≤ D := by
      rw [hDdef]; linarith [abs_nonneg a]
    have hA : |lam * a| < ρ := by
      rw [abs_mul, abs_of_pos lampos]
      have h2 : lam * |a| ≤ lam * D := mul_le_mul_of_nonneg_left haD lampos.le
      have h3 : min (ρ/2) (ε/2) ≤ ρ/2 := min_le_left _ _
      linarith [h2, hx, h3]
    have hB : lam * (|b| + κ * |a|) < ε := by
      have h2 : lam * (|b| + κ * |a|) ≤ lam * D := mul_le_mul_of_nonneg_left hbD lampos.le
      have h3 : min (ρ/2) (ε/2) ≤ ε/2 := min_le_right _ _
      linarith [h2, hx, h3]
    obtain ⟨t, htIoo, htval⟩ := hIVT (lam * a) hA
    have htR : |t| < R := by
      have h := abs_lt.mpr htIoo
      linarith [hδR]
    have hRt : |locR c t| ≤ κ * (lam * |a|) := by
      calc |locR c t| ≤ κ * |locS c t| := hbound t htR
        _ = κ * (lam * |a|) := by rw [htval, abs_mul, abs_of_pos lampos]
    have hkl : κ * (lam * |a|) = lam * (κ * |a|) := by ring
    have hu1 : lam * b - locR c t < 0 := by
      have h3 : -(lam * (κ * |a|)) ≤ locR c t := by
        have h4 := neg_abs_le (locR c t)
        linarith [hRt, h4, hkl]
      have h5 : lam * b + lam * (κ * |a|) < 0 := by
        have h6 : b + κ * |a| < 0 := by linarith [hcond]
        have h7 := mul_neg_of_pos_of_neg lampos h6
        have h8 : lam * (b + κ * |a|) = lam * b + lam * (κ * |a|) := by ring
        linarith [h7, h8]
      linarith [h3, h5]
    have hu2 : -ε < lam * b - locR c t := by
      have h3 : locR c t ≤ lam * (κ * |a|) := by
        have h := le_trans (le_abs_self (locR c t)) hRt
        linarith [h, hkl]
      have h4 : -(lam * |b|) ≤ lam * b := by
        have h5 := neg_abs_le b
        have h6 := mul_le_mul_of_nonneg_left h5 lampos.le
        linarith [h6]
      have h5 : -(lam * (|b| + κ * |a|)) ≤ lam * b - locR c t := by linarith [h3, h4]
      have h6 : lam * (|b| + κ * |a|) ≤ lam * D := mul_le_mul_of_nonneg_left hbD lampos.le
      have h7 : min (ρ/2) (ε/2) ≤ ε/2 := min_le_right _ _
      linarith [h5, h6, hx, h7, hεpos]
    have hdec := collar_detV_decomp c hreg w
    rw [← hadef, ← hbdef] at hdec
    refine ⟨(t, lam * b - locR c t), ⟨htIoo, ⟨hu2, hu1⟩⟩, ?_⟩
    have hγt : c.γ t = c.γ 0 + (locS c t : ℂ) * locE c + (locR c t : ℂ) * locN c := by
      have h := loc_reconstruction c hreg (c.γ t)
      simpa only [locS, locR] using h
    show locPhi c (t, lam * b - locR c t) = c.γ 0 + (lam : ℂ) * w
    rw [hdec]
    simp only [locPhi]
    rw [hγt, htval]
    push_cast
    ring



theorem collar_side (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (himm : Work.Smooth.Jordan.SmoothPlaneCurve.IsImmersion c)
    (hs : c.toPlaneCurve.IsSimple) {v : ℝ → ℂ} {κ L : ℝ} (hκ : 0 < κ) (hL : 0 < L)
    (hper : Function.Periodic v (2 * Real.pi))
    (htrans : Work.Smooth.JordanSeparation.IsTransverseUnitField c κ v)
    (hlip : Work.Smooth.JordanSeparation.IsLipschitzField L v)
    (hsgn : ∀ t : ℝ, 0 < Work.Smooth.JordanSeparation.detV (deriv c.γ t) (v t))
    (S : Work.Smooth.Jordan.PlaneSeparation c.toPlaneCurve) :
    ∃ δ : ℝ, 0 < δ ∧
      (((∀ t u : ℝ, 0 < u → u < δ →
          Work.Smooth.JordanSeparation.offset c v (t, u) ∈ S.V) ∧
        (∀ t u : ℝ, u < 0 → -δ < u →
          Work.Smooth.JordanSeparation.offset c v (t, u) ∈ S.U)) ∨
       ((∀ t u : ℝ, 0 < u → u < δ →
          Work.Smooth.JordanSeparation.offset c v (t, u) ∈ S.U) ∧
        (∀ t u : ℝ, u < 0 → -δ < u →
          Work.Smooth.JordanSeparation.offset c v (t, u) ∈ S.V))) := by
  have hreg : deriv c.γ 0 ≠ 0 := himm 0
  set a₀ : ℝ := detV (v 0) (locN c) with ha₀def
  set b₀ : ℝ := detV (locE c) (v 0) with hb₀def
  have hb₀pos : 0 < b₀ := by
    have h := hsgn 0
    rw [hb₀def]
    have hd : deriv c.γ 0 = ((‖deriv c.γ 0‖ : ℝ) : ℂ) * locE c := deriv_eq_norm_smul_locE c hreg
    rw [hd, detV_smul_left] at h
    exact pos_of_mul_pos_right h (le_of_lt (norm_pos_iff.mpr hreg))
  set κ' : ℝ := if a₀ = 0 then 1 else b₀ / (2 * |a₀|) with hκ'def
  have hκ'pos : 0 < κ' := by
    rw [hκ'def]; split
    · norm_num
    · exact div_pos hb₀pos (by positivity)
  have hκ'cond : κ' * |a₀| < b₀ := by
    rw [hκ'def]; split_ifs with ha
    · rw [ha]; simp only [abs_zero, mul_zero]; exact hb₀pos
    · have hne : (|a₀|) ≠ 0 := abs_ne_zero.mpr ha
      have h2 : (b₀ / (2 * |a₀|)) * |a₀| = b₀ / 2 := by
        rw [div_mul_eq_mul_div]
        field_simp
      rw [h2]; linarith [hb₀pos]
  obtain ⟨μ, ε, hμpos, hεpos, hPoff, hMoff, hrayP, hrayM⟩ := collar_ray_side c hreg hs hκ'pos
  set P : Set ℂ := locPhi c '' (Ioo (-μ) μ ×ˢ Ioo (0:ℝ) ε) with hPdef
  set M : Set ℂ := locPhi c '' (Ioo (-μ) μ ×ˢ Ioo (-ε) (0:ℝ)) with hMdef
  have hPpre : IsPreconnected P := by
    rw [hPdef]
    exact IsPreconnected.image (isPreconnected_Ioo.prod isPreconnected_Ioo) _
      (continuous_locPhi c).continuousOn
  have hMpre : IsPreconnected M := by
    rw [hMdef]
    exact IsPreconnected.image (isPreconnected_Ioo.prod isPreconnected_Ioo) _
      (continuous_locPhi c).continuousOn
  have hPsub : P ⊆ c.traceᶜ := by
    rintro z ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact hPoff p.1 p.2 hp1 hp2
  have hMsub : M ⊆ c.traceᶜ := by
    rintro z ⟨p, ⟨hp1, hp2⟩, rfl⟩
    exact hMoff p.1 p.2 hp1 hp2
  have hPside : P ⊆ S.U ∨ P ⊆ S.V :=
    hPpre.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV
      (fun z hz => by rw [S.union_eq]; exact hPsub hz)
  have hMside : M ⊆ S.U ∨ M ⊆ S.V :=
    hMpre.subset_or_subset S.isOpen_U S.isOpen_V S.disjoint_UV
      (fun z hz => by rw [S.union_eq]; exact hMsub hz)
  have hvcont : Continuous v := by
    rw [continuous_iff_continuousAt]
    intro t
    rw [Metric.continuousAt_iff]
    intro e he
    refine ⟨e / L, by positivity, fun t' ht' => ?_⟩
    have h := hlip t' t
    rw [dist_eq_norm] at ht' ⊢
    calc ‖v t' - v t‖ ≤ L * |t' - t| := h
      _ = L * dist t' t := by rw [Real.dist_eq]
      _ < L * (e / L) := mul_lt_mul_of_pos_left ht' hL
      _ = e := by field_simp
  obtain ⟨δ₁, hδ₁, hjump⟩ := ind_jump c himm hs
  have hNcond : κ' * |detV (locN c) (locN c)| < detV (locE c) (locN c) := by
    rw [detV_self, abs_zero, mul_zero, collar_detV_locE_locN c hreg]; norm_num
  have hNnegcond : detV (locE c) (-(locN c)) < -κ' * |detV (-(locN c)) (locN c)| := by
    have e1 : detV (locE c) (-(locN c)) = -1 := by
      rw [detV_neg_right, collar_detV_locE_locN c hreg]
    have e2 : detV (-(locN c)) (locN c) = 0 := by rw [detV_neg_left, detV_self, neg_zero]
    rw [e1, e2, abs_zero, mul_zero]
    norm_num
  obtain ⟨c1, hc1pos, hrayN⟩ := hrayP (locN c) hNcond
  obtain ⟨c2, hc2pos, hrayNneg⟩ := hrayM (-(locN c)) hNnegcond
  have hvcond : κ' * |detV (v 0) (locN c)| < detV (locE c) (v 0) := by
    rw [← ha₀def, ← hb₀def]; exact hκ'cond
  have hvnegcond : detV (locE c) (-(v 0)) < -κ' * |detV (-(v 0)) (locN c)| := by
    have e1 : detV (locE c) (-(v 0)) = -detV (locE c) (v 0) := detV_neg_right _ _
    have e2 : detV (-(v 0)) (locN c) = -detV (v 0) (locN c) := detV_neg_left _ _
    rw [e1, e2, abs_neg, ← hb₀def, ← ha₀def]
    linarith [hκ'cond]
  obtain ⟨c3, hc3pos, hrayv⟩ := hrayP (v 0) hvcond
  obtain ⟨c4, hc4pos, hrayvneg⟩ := hrayM (-(v 0)) hvnegcond
  set s : ℝ := min (min δ₁ c1) c2 / 2 with hsdef
  have hspos : 0 < s := by
    rw [hsdef]; exact div_pos (lt_min (lt_min hδ₁ hc1pos) hc2pos) (by norm_num)
  have hsδ₁ : s < δ₁ := by
    rw [hsdef]
    have h1 : min (min δ₁ c1) c2 ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith [h1, hδ₁]
  have hsc1 : s < c1 := by
    rw [hsdef]
    have h1 : min (min δ₁ c1) c2 ≤ c1 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith [h1, hc1pos]
  have hsc2 : s < c2 := by
    rw [hsdef]
    have h1 : min (min δ₁ c1) c2 ≤ c2 := min_le_right _ _
    linarith [h1, hc2pos]
  have hpP : c.γ 0 + s * normalField c 0 ∈ P := hrayN s hspos hsc1
  have hpM : c.γ 0 - s * normalField c 0 ∈ M := by
    have h := hrayNneg s hspos hsc2
    have he : c.γ 0 + (s:ℂ) * (-(locN c)) = c.γ 0 - s * normalField c 0 := by
      rw [mul_neg]; rfl
    rwa [he] at h
  obtain ⟨hpoff, hmoff, hjmp⟩ := hjump s hspos hsδ₁
  obtain ⟨δ_off, hδ_off_pos, hoff⟩ := offset_notMem_trace c himm hs hκ hL hper htrans hlip
  set δ : ℝ := min (min δ_off c3) c4 / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact div_pos (lt_min (lt_min hδ_off_pos hc3pos) hc4pos) (by norm_num)
  have hδlt : δ < δ_off := by
    rw [hδdef]
    have h1 : min (min δ_off c3) c4 ≤ δ_off := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith [h1, hδ_off_pos]
  have hδc3 : δ < c3 := by
    rw [hδdef]
    have h1 : min (min δ_off c3) c4 ≤ c3 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith [h1, hc3pos]
  have hδc4 : δ < c4 := by
    rw [hδdef]
    have h1 : min (min δ_off c3) c4 ≤ c4 := min_le_right _ _
    linarith [h1, hc4pos]
  have hposoff : posPart c v δ ⊆ c.traceᶜ := by
    rintro z ⟨p, ⟨-, hp⟩, rfl⟩
    exact hoff p.1 p.2 (by rw [abs_of_pos hp.1]; exact hp.1)
      (by rw [abs_of_pos hp.1]; exact lt_of_lt_of_le hp.2 hδlt.le)
  have hnegoff : negPart c v δ ⊆ c.traceᶜ := by
    rintro z ⟨p, ⟨-, hp⟩, rfl⟩
    exact hoff p.1 p.2 (by rw [abs_of_neg hp.2]; linarith [hp.2])
      (by rw [abs_of_neg hp.2]; linarith [hp.1, hδlt])
  have hqpos : offset c v (0, δ/2) ∈ posPart c v δ :=
    ⟨(0, δ/2), ⟨trivial, ⟨by linarith, by linarith⟩⟩, rfl⟩
  have hqneg : offset c v (0, -(δ/2)) ∈ negPart c v δ :=
    ⟨(0, -(δ/2)), ⟨trivial, ⟨by linarith, by linarith⟩⟩, rfl⟩
  have hqP : offset c v (0, δ/2) ∈ P := by
    have h := hrayv (δ/2) (by linarith) (by linarith [hδc3])
    simpa [offset] using h
  have hqM : offset c v (0, -(δ/2)) ∈ M := by
    have h := hrayvneg (δ/2) (by linarith) (by linarith [hδc4])
    simpa [offset, mul_neg] using h
  rcases hPside with hPU | hPV
  · rcases hMside with hMU | hMV
    · exfalso
      have h1 : ind c (c.γ 0 + s * normalField c 0) = 0 :=
        (mem_U_iff_ind_eq_zero_of_isSimple c hs (S := S) hpoff).mp (hPU hpP)
      have h2 : ind c (c.γ 0 - s * normalField c 0) = 0 :=
        (mem_U_iff_ind_eq_zero_of_isSimple c hs (S := S) hmoff).mp (hMU hpM)
      omega
    · refine ⟨δ, hδpos, Or.inr ⟨?_, ?_⟩⟩
      · intro t u hu huδ
        have hq : offset c v (t, u) ∈ posPart c v δ := ⟨(t, u), ⟨trivial, ⟨hu, huδ⟩⟩, rfl⟩
        rcases (posPart_isPreconnected c hvcont δ).subset_or_subset S.isOpen_U S.isOpen_V
          S.disjoint_UV (fun z hz => by rw [S.union_eq]; exact hposoff hz) with h | h
        · exact h hq
        · exfalso
          exact (Set.disjoint_left.mp S.disjoint_UV (hPU hqP)) (h hqpos)
      · intro t u hu huδ
        have hq : offset c v (t, u) ∈ negPart c v δ := ⟨(t, u), ⟨trivial, ⟨huδ, hu⟩⟩, rfl⟩
        rcases (negPart_isPreconnected c hvcont δ).subset_or_subset S.isOpen_U S.isOpen_V
          S.disjoint_UV (fun z hz => by rw [S.union_eq]; exact hnegoff hz) with h | h
        · exfalso
          exact (Set.disjoint_left.mp S.disjoint_UV (h hqneg)) (hMV hqM)
        · exact h hq
  · rcases hMside with hMU | hMV
    · refine ⟨δ, hδpos, Or.inl ⟨?_, ?_⟩⟩
      · intro t u hu huδ
        have hq : offset c v (t, u) ∈ posPart c v δ := ⟨(t, u), ⟨trivial, ⟨hu, huδ⟩⟩, rfl⟩
        rcases (posPart_isPreconnected c hvcont δ).subset_or_subset S.isOpen_U S.isOpen_V
          S.disjoint_UV (fun z hz => by rw [S.union_eq]; exact hposoff hz) with h | h
        · exfalso
          exact (Set.disjoint_left.mp S.disjoint_UV (h hqpos)) (hPV hqP)
        · exact h hq
      · intro t u hu huδ
        have hq : offset c v (t, u) ∈ negPart c v δ := ⟨(t, u), ⟨trivial, ⟨huδ, hu⟩⟩, rfl⟩
        rcases (negPart_isPreconnected c hvcont δ).subset_or_subset S.isOpen_U S.isOpen_V
          S.disjoint_UV (fun z hz => by rw [S.union_eq]; exact hnegoff hz) with h | h
        · exact h hq
        · exfalso
          exact (Set.disjoint_left.mp S.disjoint_UV (hMU hqM)) (h hqneg)
    · exfalso
      have h1 : |ind c (c.γ 0 + s * normalField c 0)| = 1 :=
        ind_abs_eq_one_of_mem_V_of_isSimple c hs (S := S) (hPV hpP)
      have h2 : |ind c (c.γ 0 - s * normalField c 0)| = 1 :=
        ind_abs_eq_one_of_mem_V_of_isSimple c hs (S := S) (hMV hpM)
      rcases ((abs_eq (show (0:ℤ) ≤ 1 by norm_num)).mp h2) with h | h
      · rw [hjmp, h] at h1; norm_num at h1
      · rw [hjmp, h] at h1; norm_num at h1

end

end Work.Smooth.JordanSeparation
