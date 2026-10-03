import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.multEps_sqWave_separation
import Submission.Work.FIArea7.sign_re_separation
import Submission.Work.FIArea7.multEpsHilbert
import Submission.Work.FIArea7.KStarDivs.PrimDefs
import Submission.Work.FIArea7.P231M.powSeriesConv
import Submission.Work.FIArea7.P231.normConvSummable_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7.P231

/-! Copy of `Work.FIArea7.P231.multEps_expansion` with the `sorry`-free Cauchy-product lemma
`Work.FIArea7.P231M.powSeriesConv` in place of the admitted `powSeriesConv`. -/

open scoped BigOperators

noncomputable section

theorem multEpsExpansion :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : GaussianInt) (R : ℕ), 2 ≤ R →
      Work.FIPlan.IsPrimary σ → IsCoprime σ.re σ.im → σ.im ≠ 0 →
      ∃ ĉ : ℤ → ℂ, (∀ s : Finset ℤ, ∑ k ∈ s, ‖ĉ k‖ ≤ C * (Real.log (2 * R)) ^ 4) ∧
      ∀ w z : GaussianInt, Work.FIPlan.IsPrimary w → Work.FIPlan.IsPrimary z →
        w ≠ 0 → z ≠ 0 →
        ‖σ.toComplex‖ * ‖(w * z).toComplex‖ ≤ (R : ℝ) * |(((σ * (w * z)).re : ℤ) : ℝ)| →
        ‖w.toComplex‖ * ‖z.toComplex‖ ≤ (R : ℝ) * |(((w * z).re : ℤ) : ℝ)| →
        HasSum (fun k : ℤ => ĉ k * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k
                                  * (z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k))
          (2 * (MultEps σ (w * z) : ℂ) * (HilbertInf σ.re σ.im : ℂ)) := by
  obtain ⟨C0, hC0pos, hCmain⟩ := Work.FIArea7.sign_re_separation
  refine ⟨(1 + C0) ^ 2, by positivity, ?_⟩
  intro σ R hR hσP hσc hσim
  obtain ⟨a, hafin, hasum⟩ := hCmain R hR
  -- basic real facts about the logarithm
  have hR2 : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have h2R4 : (4 : ℝ) ≤ 2 * (R : ℝ) := by linarith
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 4)]
    linarith [Real.exp_one_lt_three]
  have hlog1 : (1 : ℝ) ≤ Real.log (2 * (R : ℝ)) :=
    hlog4.trans (Real.log_le_log (by norm_num) h2R4)
  set L : ℝ := Real.log (2 * (R : ℝ)) with hLdef
  have hL1 : (1 : ℝ) ≤ L := by rw [hLdef]; exact hlog1
  have hL0 : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
  -- σ is a nonzero Gaussian integer, hence a nonzero complex number
  have hσne : σ ≠ 0 := by
    intro h
    have hz : σ.re = 0 := by rw [h]; rfl
    obtain ⟨k, hk⟩ := hσP.1
    rw [hz] at hk
    omega
  have hσc_ne : σ.toComplex ≠ 0 := fun h => hσne (GaussianInt.toComplex_eq_zero.mp h)
  -- the unit modulus part of a nonzero complex number
  have hunit : ∀ χ : ℂ, χ ≠ 0 → ‖χ / (‖χ‖ : ℂ)‖ = 1 := by
    intro χ hχ
    have hpos : 0 < ‖χ‖ := norm_pos_iff.mpr hχ
    rw [norm_div]
    have h1 : ‖((‖χ‖ : ℝ) : ℂ)‖ = ‖χ‖ := by
      rw [show ‖(((‖χ‖ : ℝ)) : ℂ)‖ = |‖χ‖| by simp, abs_of_nonneg hpos.le]
    rw [h1, div_self (ne_of_gt hpos)]
  set σ0 : ℂ := σ.toComplex / (‖σ.toComplex‖ : ℂ) with hσ0def
  have hσ0norm : ‖σ0‖ = 1 := by rw [hσ0def]; exact hunit σ.toComplex hσc_ne
  -- the modulator b_k = a_k σ0^k
  set b : ℤ → ℂ := fun k => a k * σ0 ^ k with hbdef
  have hbk : ∀ k : ℤ, ‖b k‖ = ‖a k‖ := by
    intro k
    simp only [hbdef, norm_mul, norm_zpow, hσ0norm, one_zpow, mul_one]
  have hbaeq : (fun k : ℤ => ‖b k‖) = (fun k : ℤ => ‖a k‖) := funext hbk
  have haSummable : Summable fun k : ℤ => ‖a k‖ :=
    summable_of_sum_le (fun k => norm_nonneg _) hafin
  have hafinL : ∀ s : Finset ℤ, ∑ k ∈ s, ‖a k‖ ≤ C0 * L := hafin
  have hbfinL : ∀ s : Finset ℤ, ∑ k ∈ s, ‖b k‖ ≤ C0 * L := fun s => by
    rw [show (fun k : ℤ => ‖b k‖) = (fun k : ℤ => ‖a k‖) from hbaeq]; exact hafinL s
  have hbSummable : Summable fun k : ℤ => ‖b k‖ := by rw [hbaeq]; exact haSummable
  have ha_tsum : ∑' k : ℤ, ‖a k‖ ≤ C0 * L :=
    Summable.tsum_le_of_sum_le haSummable hafin
  have hb_tsum : ∑' k : ℤ, ‖b k‖ ≤ C0 * L := by rw [hbaeq]; exact ha_tsum
  -- the convolution of the two coefficient families
  set conv : ℤ → ℂ := fun k => ∑' j : ℤ, a j * b (k - j) with hconvdef
  have hconvSumm : Summable fun n : ℤ => ‖conv n‖ := by
    have h := (normConvSummable_le haSummable hbSummable).1
    simpa only [hconvdef] using h
  have hconv_tsum : ∑' n : ℤ, ‖conv n‖ ≤ (C0 * L) * (C0 * L) := by
    have h := (normConvSummable_le haSummable hbSummable).2
    have h2 : ∑' n : ℤ, ‖conv n‖ ≤ (∑' k : ℤ, ‖a k‖) * (∑' k : ℤ, ‖b k‖) := by
      simpa only [hconvdef] using h
    have hX0 : (0 : ℝ) ≤ C0 * L := mul_nonneg hC0pos.le hL0
    have hA0 : (0 : ℝ) ≤ ∑' k : ℤ, ‖a k‖ := tsum_nonneg (fun k => norm_nonneg _)
    have hB0 : (0 : ℝ) ≤ ∑' k : ℤ, ‖b k‖ := tsum_nonneg (fun k => norm_nonneg _)
    calc ∑' n : ℤ, ‖conv n‖ ≤ (∑' k : ℤ, ‖a k‖) * (∑' k : ℤ, ‖b k‖) := h2
      _ ≤ (C0 * L) * (C0 * L) :=
            le_trans (mul_le_mul_of_nonneg_right ha_tsum hB0)
                     (mul_le_mul_of_nonneg_left hb_tsum hX0)
  -- the sign of σ.im as a complex number
  set sg : ℂ := ((Int.sign σ.im : ℤ) : ℂ) with hsgdef
  have hsgnorm : ‖sg‖ = 1 := by
    have hs : Int.sign σ.im = 1 ∨ Int.sign σ.im = -1 := by
      rcases lt_trichotomy σ.im 0 with h | h | h
      · exact Or.inr (Int.sign_eq_neg_one_of_neg h)
      · exact absurd h hσim
      · exact Or.inl (Int.sign_eq_one_of_pos h)
    rw [hsgdef]
    rcases hs with h | h <;> rw [h] <;> norm_num [Complex.norm_intCast]
  -- the assembled coefficient family
  set c : ℤ → ℂ := fun k => (if k = 0 then (1 : ℂ) else 0) + sg * a k + (-sg) * b k + conv k
    with hcdef
  refine ⟨c, ?_, ?_⟩
  · -- the ℓ¹ bound
    intro t
    have hδsum : ∑ k ∈ t, ‖(if k = 0 then (1 : ℂ) else 0)‖ ≤ 1 := by
      by_cases h0 : (0 : ℤ) ∈ t
      · rw [Finset.sum_eq_single (0 : ℤ) (fun bb _ hb => by rw [if_neg hb]; simp)
            (fun h => absurd h0 h)]
        simp
      · rw [Finset.sum_eq_zero (fun k hk => by
            have hk0 : k ≠ 0 := fun h => h0 (by rwa [h] at hk)
            rw [if_neg hk0]; simp)]
        norm_num
    have hsplit : (∑ k ∈ t, ‖(if k = 0 then (1 : ℂ) else 0)‖) + (∑ k ∈ t, ‖a k‖)
          + (∑ k ∈ t, ‖b k‖) + (∑ k ∈ t, ‖conv k‖)
        = ∑ k ∈ t, (‖(if k = 0 then (1 : ℂ) else 0)‖ + ‖a k‖ + ‖b k‖ + ‖conv k‖) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hconvfin : ∑ k ∈ t, ‖conv k‖ ≤ (C0 * L) * (C0 * L) :=
      le_trans (Summable.sum_le_tsum t (fun i _ => norm_nonneg _) hconvSumm) hconv_tsum
    have hsum_le : ∑ k ∈ t, ‖c k‖
        ≤ (∑ k ∈ t, ‖(if k = 0 then (1 : ℂ) else 0)‖) + (∑ k ∈ t, ‖a k‖)
          + (∑ k ∈ t, ‖b k‖) + (∑ k ∈ t, ‖conv k‖) := by
      rw [hsplit]
      apply Finset.sum_le_sum
      intro k _
      calc ‖c k‖ = ‖((if k = 0 then (1 : ℂ) else 0) + sg * a k + (-sg) * b k) + conv k‖ := by
              simp only [hcdef]
        _ ≤ ‖(if k = 0 then (1 : ℂ) else 0) + sg * a k + (-sg) * b k‖ + ‖conv k‖ :=
              norm_add_le _ _
        _ ≤ (‖(if k = 0 then (1 : ℂ) else 0) + sg * a k‖ + ‖(-sg) * b k‖) + ‖conv k‖ := by
              have h := norm_add_le ((if k = 0 then (1 : ℂ) else 0) + sg * a k) ((-sg) * b k)
              linarith
        _ ≤ ((‖(if k = 0 then (1 : ℂ) else 0)‖ + ‖sg * a k‖) + ‖(-sg) * b k‖)
              + ‖conv k‖ := by
              have h := norm_add_le ((if k = 0 then (1 : ℂ) else 0)) (sg * a k)
              linarith
        _ = ‖(if k = 0 then (1 : ℂ) else 0)‖ + ‖a k‖ + ‖b k‖ + ‖conv k‖ := by
              simp [hsgnorm]
    refine le_trans hsum_le ?_
    calc (∑ k ∈ t, ‖(if k = 0 then (1 : ℂ) else 0)‖) + (∑ k ∈ t, ‖a k‖)
          + (∑ k ∈ t, ‖b k‖) + (∑ k ∈ t, ‖conv k‖)
        ≤ 1 + C0 * L + C0 * L + (C0 * L) * (C0 * L) := by
          linarith [hδsum, hafinL t, hbfinL t, hconvfin]
      _ ≤ (1 + C0) ^ 2 * L ^ 4 := by
          have hstep1 : 1 + C0 * L ≤ (1 + C0) * L ^ 2 := by
            have hL2 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
            have hLe : L ≤ L ^ 2 := by nlinarith [hL1]
            have h1 : C0 * L ≤ C0 * L ^ 2 := mul_le_mul_of_nonneg_left hLe hC0pos.le
            linarith
          calc 1 + C0 * L + C0 * L + (C0 * L) * (C0 * L) = (1 + C0 * L) ^ 2 := by ring
            _ ≤ ((1 + C0) * L ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hstep1 2
            _ = (1 + C0) ^ 2 * L ^ 4 := by ring
  · -- the HasSum for each admissible pair (w,z)
    intro w z hwP hzP hwne hzne hroom1 hroom2
    have hwzP : Work.FIPlan.IsPrimary (w * z) := Work.FIArea7.KStarDivs.isPrimary_mul hwP hzP
    have hwne' : w.toComplex ≠ 0 := fun h => hwne (GaussianInt.toComplex_eq_zero.mp h)
    have hzne' : z.toComplex ≠ 0 := fun h => hzne (GaussianInt.toComplex_eq_zero.mp h)
    have hwz_ne : w * z ≠ 0 := mul_ne_zero hwne hzne
    have hwzc_ne : (w * z).toComplex ≠ 0 := fun h => hwz_ne (GaussianInt.toComplex_eq_zero.mp h)
    have hwzre : (w * z).re ≠ 0 := by
      intro h
      have hpos : 0 < ‖w.toComplex‖ * ‖z.toComplex‖ :=
        mul_pos (norm_pos_iff.mpr hwne') (norm_pos_iff.mpr hzne')
      rw [h] at hroom2
      simp at hroom2
      linarith
    have hσwzre : (σ * (w * z)).re ≠ 0 := by
      intro h
      have hpos : 0 < ‖σ.toComplex‖ * ‖(w * z).toComplex‖ :=
        mul_pos (norm_pos_iff.mpr hσc_ne) (norm_pos_iff.mpr hwzc_ne)
      rw [h] at hroom1
      simp at hroom1
      rw [GaussianInt.toComplex_mul, norm_mul] at hpos
      linarith
    set u : ℂ := (w.toComplex / (‖w.toComplex‖ : ℂ)) * (z.toComplex / (‖z.toComplex‖ : ℂ))
      with hu_def
    have hunorm : ‖u‖ = 1 := by
      rw [hu_def, norm_mul, hunit w.toComplex hwne', hunit z.toComplex hzne', one_mul]
    have hroom2' : ‖w.toComplex‖ * ‖z.toComplex‖ ≤ (R : ℝ) * |(w.toComplex * z.toComplex).re| := by
      rw [← GaussianInt.toComplex_mul, ← GaussianInt.intCast_re]; exact hroom2
    have hroom1' : ‖σ.toComplex‖ * ‖(w * z).toComplex‖
        ≤ (R : ℝ) * |(σ.toComplex * (w * z).toComplex).re| := by
      rw [← GaussianInt.toComplex_mul, ← GaussianInt.intCast_re]; exact hroom1
    have hvalA : (if 0 < (w.toComplex * z.toComplex).re then (1 : ℂ) else -1)
        = ((Int.sign ((w * z).re) : ℤ) : ℂ) := by
      rw [← GaussianInt.toComplex_mul, ← GaussianInt.intCast_re]
      exact (Work.FIArea7.int_sign_cast_eq_c hwzre).symm
    have hvalB : (if 0 < (σ.toComplex * (w * z).toComplex).re then (1 : ℂ) else -1)
        = ((Int.sign ((σ * (w * z)).re) : ℤ) : ℂ) := by
      rw [← GaussianInt.toComplex_mul, ← GaussianInt.intCast_re]
      exact (Work.FIArea7.int_sign_cast_eq_c hσwzre).symm
    have hsumA : HasSum (fun k : ℤ => a k * u ^ k) ((Int.sign ((w * z).re) : ℤ) : ℂ) := by
      have h := hasum w.toComplex z.toComplex hwne' hzne' hroom2'
      rw [hvalA] at h
      simpa only [hu_def, mul_zpow] using h
    have hsumB : HasSum (fun k : ℤ => b k * u ^ k) ((Int.sign ((σ * (w * z)).re) : ℤ) : ℂ) := by
      have h := hasum σ.toComplex (w * z).toComplex hσc_ne hwzc_ne hroom1'
      rw [hvalB] at h
      have huwz : ((w * z).toComplex / (‖(w * z).toComplex‖ : ℂ)) = u := by
        rw [hu_def, GaussianInt.toComplex_mul, norm_mul, Complex.ofReal_mul, div_mul_div_comm]
      have hfun : (fun k : ℤ => a k * ((σ.toComplex / (‖σ.toComplex‖ : ℂ)) ^ k
            * ((w * z).toComplex / (‖(w * z).toComplex‖ : ℂ)) ^ k)) = (fun k : ℤ => b k * u ^ k) := by
        funext k
        simp only [huwz, hbdef, hσ0def]
        ring
      rw [hfun] at h
      exact h
    have hconvHS : HasSum (fun k : ℤ => conv k * u ^ k)
        (((Int.sign ((w * z).re) : ℤ) : ℂ) * ((Int.sign ((σ * (w * z)).re) : ℤ) : ℂ)) := by
      have h := Work.FIArea7.P231M.powSeriesConv (u := u) hunorm hsumA hsumB haSummable hbSummable
      simpa only [hconvdef] using h
    have hdelta : HasSum (fun k : ℤ => (if k = 0 then (1 : ℂ) else 0) * u ^ k) 1 := by
      have h := hasSum_single (0 : ℤ)
        (f := fun k : ℤ => (if k = 0 then (1 : ℂ) else 0) * u ^ k)
        (fun b' hb' => by rw [if_neg hb', zero_mul])
      simpa using h
    have hsa' : HasSum (fun k : ℤ => (sg * a k) * u ^ k)
        (sg * ((Int.sign ((w * z).re) : ℤ) : ℂ)) := by
      have h := hsumA.mul_left sg
      simpa only [mul_assoc] using h
    have hsb' : HasSum (fun k : ℤ => ((-sg) * b k) * u ^ k)
        ((-sg) * ((Int.sign ((σ * (w * z)).re) : ℤ) : ℂ)) := by
      have h := hsumB.mul_left (-sg)
      simpa only [mul_assoc] using h
    have htot := ((hdelta.add hsa').add hsb').add hconvHS
    have hfun : (fun k : ℤ => ((((if k = 0 then (1 : ℂ) else 0) * u ^ k) + (sg * a k) * u ^ k)
            + ((-sg) * b k) * u ^ k) + conv k * u ^ k) = (fun k : ℤ => c k * u ^ k) := by
      funext k
      simp only [hcdef]
      ring
    rw [hfun] at htot
    have hcHS : HasSum (fun k : ℤ => c k * u ^ k)
        (1 + sg * ((Int.sign ((w * z).re) : ℤ) : ℂ)
          - sg * ((Int.sign ((σ * (w * z)).re) : ℤ) : ℂ)
          + ((Int.sign ((w * z).re) : ℤ) : ℂ) * ((Int.sign ((σ * (w * z)).re) : ℤ) : ℂ)) := by
      convert htot using 1; ring
    have hvalEq : 2 * (MultEps σ (w * z) : ℂ) * (HilbertInf σ.re σ.im : ℂ)
        = 1 + sg * ((Int.sign ((w * z).re) : ℤ) : ℂ)
          - sg * ((Int.sign ((σ * (w * z)).re) : ℤ) : ℂ)
          + ((Int.sign ((w * z).re) : ℤ) : ℂ) * ((Int.sign ((σ * (w * z)).re) : ℤ) : ℂ) := by
      have h := Work.FIArea7.multEpsHilbert hσP hσc hwzP
      rw [h, Int.sign_mul]
      push_cast
      rw [← hsgdef]
      ring
    have hmain : HasSum (fun k : ℤ => c k * u ^ k)
        (2 * (MultEps σ (w * z) : ℂ) * (HilbertInf σ.re σ.im : ℂ)) := by
      rw [hvalEq]
      exact hcHS
    simpa only [hu_def, mul_zpow] using hmain

end

end Work.FIArea7.P231
