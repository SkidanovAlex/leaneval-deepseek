import Mathlib
import Submission.Work.Asymptotics.BlLow.Defs
import Submission.Work.Asymptotics.BlLow.GrazeVanish
import Submission.Work.HFN.BlLow.Phi12
import Submission.Work.HFN.HalfFunnel.lowBad_Kaxis_bound_aux
import Submission.Work.Asymptotics.HalfFunnel.exists_bound_Kfun_off_coincidence
import Submission.Work.Asymptotics.KaxisMid.exists_bound_Kfun_of_coincidence
import Submission.Work.Asymptotics.arcT_jprime_dense
import Submission.Work.Asymptotics.Graze.Vanishing

set_option maxHeartbeats 2000000

noncomputable section

open UpperHalfPlane ModularGroup

namespace Work.HFN.BlLow
open Work.Asymptotics Work.Asymptotics.BlLow  -- ck-hfn-fix: fork moved out of Work.Asymptotics

open Work.Kernels
open Work.Asymptotics.HalfFunnel (tsign)

/-! ## 4. The contour point `i t` as a total function -/

/-- The point `i · max t (1/8)` of `ℍ`: a total continuous version of the contour point `i t`. -/
def axPt (t : ℝ) : ℍ := UpperHalfPlane.ofComplex (((max t (1 / 8) : ℝ) : ℂ) * Complex.I)

lemma axPt_coe (t : ℝ) : ((axPt t : ℍ) : ℂ) = ((max t (1 / 8) : ℝ) : ℂ) * Complex.I := by
  have hpos : 0 < ((((max t (1 / 8) : ℝ)) : ℂ) * Complex.I).im := by
    rw [Complex.mul_im]
    simpa using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 8) (le_max_right t (1 / 8))
  rw [axPt, UpperHalfPlane.ofComplex_apply_of_im_pos hpos]

lemma axPt_re (t : ℝ) : (axPt t).re = 0 := by
  rw [← UpperHalfPlane.coe_re, axPt_coe]
  simp [Complex.mul_re]

lemma axPt_im (t : ℝ) : (axPt t).im = max t (1 / 8) := by
  rw [← UpperHalfPlane.coe_im, axPt_coe]
  simp [Complex.mul_im]

lemma axPt_continuous : Continuous axPt := by
  rw [continuous_induced_rng (f := UpperHalfPlane.coe)]
  show Continuous fun t : ℝ => ((axPt t : ℍ) : ℂ)
  rw [show (fun t : ℝ => ((axPt t : ℍ) : ℂ))
      = fun t => ((max t (1 / 8) : ℝ) : ℂ) * Complex.I from funext fun t => axPt_coe t]
  exact (Complex.continuous_ofReal.comp
    (continuous_max.comp (continuous_id.prodMk continuous_const))).mul continuous_const

lemma axPt_eq_imagAxis {t : ℝ} (ht : 1 / 8 ≤ t) :
    axPt t = imagAxis t (lt_of_lt_of_le (by norm_num) ht) := by
  apply UpperHalfPlane.ext
  rw [axPt_coe, max_eq_left ht]
  rfl

/-- The contour segment `{i t : 1/8 ≤ t ≤ 3}`, as a compact subset of `ℍ`. -/
def contSeg : Set ℍ := axPt '' Set.Icc (1 / 8) 3

lemma isCompact_contSeg : IsCompact contSeg :=
  isCompact_Icc.image axPt_continuous

lemma axPt_mem_contSeg {t : ℝ} (h1 : 1 / 8 ≤ t) (h2 : t ≤ 3) : axPt t ∈ contSeg :=
  ⟨t, ⟨h1, h2⟩, rfl⟩

/-- Real part/im part of the `ℍ`-element as a complex number. -/
lemma coe_eq_re_add_im (τ : ℍ) :
    ((τ : ℍ) : ℂ) = ((τ.re : ℝ) : ℂ) + ((τ.im : ℝ) : ℂ) * Complex.I := by
  conv_lhs => rw [← Complex.re_add_im ((τ : ℍ) : ℂ)]
  simp [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]

/-! ## 5. The branch template -/

/-- `Kfun = KfunClear / growthPrefactor` off the coincidence divisor. -/
lemma Kfun_eq_div {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} (hd : d = 8 ∨ d = 24) {τ z : ℍ}
    (h : jInvariantFun τ ≠ jInvariantFun z) :
    Kfun ℓ d τ z = KfunClear ℓ d τ z / growthPrefactor d τ z := by
  have h1 := Work.Kernels.ClearLink.KPlusClear_eq_smul d hd τ z h
  have h2 := Work.Kernels.ClearLink.KMinusClear_eq_smul ℓ d hd τ z h
  have hg : growthPrefactor d τ z ≠ 0 := Work.Asymptotics.growthPrefactor_ne_zero d h
  rw [show Kfun ℓ d τ z = (KPlus d τ z + KMinus ℓ d τ z) / 2 from rfl,
    show KfunClear ℓ d τ z = (KPlusClear d τ z + KMinusClear ℓ d τ z) / 2 from rfl, h1, h2]
  field_simp

lemma scale_le_of_mem (z : ℍ) (h1 : ‖(z : ℂ)‖ ≤ 6) (h2 : (1 : ℝ) / 10 ≤ z.im) :
    Work.Kernels.scale z ≤ 17 := by
  have hinv : z.im⁻¹ ≤ 10 := by
    rw [inv_le_comm₀ z.im_pos (by norm_num)]
    linarith
  simp only [Work.Kernels.scale]
  linarith

/-- **The branch template.**  Let `Z` be a curve of "removable orbit points" — `KfunClear`
vanishes at every `(τ, Z τ)` and `j` is constant along `Z` — whose imaginary parts lie in an arc
`[a,b]` avoiding `1`.  Then, uniformly on a compact set `K` of parameters, the kernel is bounded
on the window `|t - Im (Z τ)| ≤ β` around the branch height, provided the branch point is within
`α` of the imaginary axis. -/
theorem branch_window (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {a b : ℝ} (ha : 1 / 5 < a) (hab : a ≤ b) (hb : b ≤ 16 / 5) (hne : b < 1 ∨ 1 < a)
    (Z : ℍ → ℍ)
    (hZclear : ∀ τ : ℍ, KfunClear ℓ d τ (Z τ) = 0)
    (hZj : ∀ τ : ℍ, jInvariantFun (Z τ) = jInvariantFun τ)
    {K : Set ℍ} (hK : IsCompact K)
    (him : ∀ τ ∈ K, a ≤ (Z τ).im ∧ (Z τ).im ≤ b) :
    ∃ C α β : ℝ, 0 ≤ C ∧ 0 < α ∧ 0 < β ∧ α + β < a / 4 ∧
      ∀ τ ∈ K, |(Z τ).re| ≤ α →
        ∀ t : ℝ, 0 < t → t ≤ 3 → |t - (Z τ).im| ≤ β →
          ‖Kaxis (Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨ρD, c₀, hρD, hc₀, hdq⟩ :=
    Work.HFN.HalfFunnel.exists_diffQuotient_lower_uniform a b (by linarith) hab hne
  set α : ℝ := min (ρD / 2) (1 / 40) with hα
  set β : ℝ := min (ρD / 2) (1 / 40) with hβ
  have hαpos : 0 < α := lt_min (by linarith) (by norm_num)
  have hβpos : 0 < β := lt_min (by linarith) (by norm_num)
  have hαρ : α < ρD := by rw [hα]; linarith [min_le_left (ρD / 2) (1 / 40)]
  have hβρ : β < ρD := by rw [hβ]; linarith [min_le_left (ρD / 2) (1 / 40)]
  have hα40 : α ≤ 1 / 40 := min_le_right _ _
  have hβ40 : β ≤ 1 / 40 := min_le_right _ _
  have hαβ : α + β < a / 4 := by linarith
  obtain ⟨R₁, hR₁, hb₁⟩ := Work.Asymptotics.KaxisMid.exists_scale_bound_of_isCompact hK
  obtain ⟨M, hM, hMb⟩ := Work.Asymptotics.KaxisMid.exists_bound_KfunClear_of_scale_bounds
    (S := K) (T := {w : ℍ | ‖(w : ℂ)‖ ≤ 6 ∧ (1 : ℝ) / 10 ≤ w.im}) ℓ d hd
    hR₁ (by norm_num : (0 : ℝ) < 17) hb₁
    (fun z hz => scale_le_of_mem z hz.1 hz.2)
  obtain ⟨δ₁, hδ₁, hbδ₁⟩ := Work.Asymptotics.KaxisMid.exists_lower_DeltaFun hK
  obtain ⟨δ₂, hδ₂, hbδ₂⟩ := Work.Asymptotics.KaxisMid.exists_lower_DeltaFun isCompact_contSeg
  obtain ⟨C₀, hC₀, hbC₀⟩ :=
    Work.Asymptotics.KaxisMid.exists_bound_Kfun_of_coincidence ℓ d hd hK isCompact_contSeg
  set Dh : ℝ := δ₁ * δ₂ ^ (if d = 8 then 1 else 2) * c₀ with hDh
  have hDhpos : 0 < Dh := mul_pos (mul_pos hδ₁ (pow_pos hδ₂ _)) hc₀
  refine ⟨max C₀ (4 * M / (a * Dh)), α, β, le_trans hC₀.le (le_max_left _ _), hαpos,
    hβpos, hαβ, ?_⟩
  intro τ hτ hre t ht ht3 hwin
  have himτ := him τ hτ
  have htim : (1 : ℝ) / 8 ≤ t := by
    have h1 : (1 : ℝ) / 5 < (Z τ).im := lt_of_lt_of_le ha himτ.1
    have h2 := abs_le.mp hwin
    linarith [h2.1, h2.2, hβ40]
  have hzcoe : ((axPt t : ℍ) : ℂ) = (t : ℂ) * Complex.I := by
    rw [axPt_coe, show max t (1 / 8) = t from max_eq_left htim]
  set D : ℝ := ‖((axPt t : ℍ) : ℂ) - ((Z τ : ℍ) : ℂ)‖ with hDdef
  have hZi : (0 : ℝ) < (Z τ).im := by linarith [himτ.1]
  have hZre : |(Z τ).re| ≤ α := hre
  have hnorm : D ≤ α + β := by
    have h1 : ((axPt t : ℍ) : ℂ) - ((Z τ : ℍ) : ℂ)
        = ((-(Z τ).re : ℝ) : ℂ) + (((t - (Z τ).im : ℝ)) : ℂ) * Complex.I := by
      have hsub : ((t - (Z τ).im : ℝ) : ℂ) = (t : ℂ) - ((Z τ).im : ℂ) := by
        push_cast
        ring
      have hneg : ((-(Z τ).re : ℝ) : ℂ) = -((Z τ).re : ℂ) := by
        push_cast
        ring
      rw [hzcoe, coe_eq_re_add_im (Z τ), hsub, hneg]
      ring
    rw [hDdef, h1]
    calc ‖((-((Z τ).re) : ℝ) : ℂ) + (((t - (Z τ).im : ℝ)) : ℂ) * Complex.I‖
        ≤ ‖((-((Z τ).re) : ℝ) : ℂ)‖ + ‖(((t - (Z τ).im : ℝ)) : ℂ) * Complex.I‖ :=
          norm_add_le _ _
      _ = |(Z τ).re| + |t - (Z τ).im| := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs]
      _ ≤ α + β := by linarith [hZre, hwin]
  have hZn : ‖((Z τ : ℍ) : ℂ)‖ ≤ 4 := by
    have hsq : ‖((Z τ : ℍ) : ℂ)‖ ^ 2 = (Z τ).re ^ 2 + (Z τ).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im]
      ring
    have h1 : (Z τ).re ^ 2 ≤ (1 / 40 : ℝ) ^ 2 := by
      have h := abs_le.mp (le_trans hZre hα40)
      nlinarith [h.1, h.2]
    have h2 : (Z τ).im ^ 2 ≤ (16 / 5 : ℝ) ^ 2 := by nlinarith [himτ.1, himτ.2, hZi]
    nlinarith [norm_nonneg ((Z τ : ℍ) : ℂ), hsq, h1, h2]
  by_cases hcoin : jInvariantFun τ = jInvariantFun (axPt t)
  · have hthis := hbC₀ τ (axPt t) hτ (axPt_mem_contSeg htim ht3) hcoin
    rw [Work.Kernels.Kaxis, dif_pos ht, ← axPt_eq_imagAxis htim]
    exact le_trans hthis (le_max_left _ _)
  · have hdiv := Kfun_eq_div (ℓ := ℓ) hd (τ := τ) (z := axPt t) hcoin
    have hr : 0 < (Z τ).im / 2 := by linarith
    have hbd : ∀ w : ℍ, ‖(w : ℂ) - ((Z τ : ℍ) : ℂ)‖ ≤ (Z τ).im / 2 →
        ‖KfunClear ℓ d τ w‖ ≤ M := by
      intro w hw
      refine hMb τ hτ w ⟨?_, ?_⟩
      · have h1 : ‖(w : ℂ)‖ ≤ ‖(w : ℂ) - ((Z τ : ℍ) : ℂ)‖ + ‖((Z τ : ℍ) : ℂ)‖ := by
          have h := norm_add_le ((w : ℂ) - ((Z τ : ℍ) : ℂ)) ((Z τ : ℍ) : ℂ)
          rwa [sub_add_cancel] at h
        linarith
      · have h1 : |(w : ℂ).im - ((Z τ : ℍ) : ℂ).im| ≤ ‖(w : ℂ) - ((Z τ : ℍ) : ℂ)‖ := by
          rw [show (w : ℂ).im - ((Z τ : ℍ) : ℂ).im = ((w : ℂ) - ((Z τ : ℍ) : ℂ)).im by simp]
          exact Complex.abs_im_le_norm _
        have h2 := (abs_le.mp (le_trans h1 hw)).1
        simp only [UpperHalfPlane.coe_im] at h2
        linarith
    have hone := Work.Asymptotics.KaxisMid.KbcAux2.one_zero_apply
      (f := fun w : ℍ => KfunClear ℓ d τ w)
      (Work.Asymptotics.KaxisMid.KbcAux2.mdifferentiable_KfunClear_snd ℓ d hd τ)
      hr (by linarith : (Z τ).im / 2 < (Z τ).im) hbd
      (w₀ := Z τ) (by rw [sub_self, norm_zero]; positivity) (hZclear τ)
    have hpoint : D < (Z τ).im / 4 := by
      have h4 : α + β < (Z τ).im / 4 := by linarith
      linarith
    have hone' : ‖KfunClear ℓ d τ (axPt t)‖ ≤ (2 * M / ((Z τ).im / 2)) * D := by
      refine hone (axPt t) ?_
      rw [← hDdef]
      linarith [hpoint]
    have hjc0 : c₀ * D ≤ ‖jInvariantFun τ - jInvariantFun (axPt t)‖ := by
      have hZcen : ‖((Z τ : ℍ) : ℂ) - Complex.I * ((Z τ).im : ℂ)‖ < ρD := by
        have h1 : ((Z τ : ℍ) : ℂ) - Complex.I * ((Z τ).im : ℂ) = (((Z τ).re : ℝ) : ℂ) := by
          rw [coe_eq_re_add_im (Z τ)]; ring
        rw [h1, Complex.norm_real, Real.norm_eq_abs]
        linarith
      have hzcen : ‖((axPt t : ℍ) : ℂ) - Complex.I * ((Z τ).im : ℂ)‖ < ρD := by
        have hsub : ((t - (Z τ).im : ℝ) : ℂ) = (t : ℂ) - ((Z τ).im : ℂ) := by
          push_cast
          ring
        have h1 : ((axPt t : ℍ) : ℂ) - Complex.I * ((Z τ).im : ℂ)
            = ((t - (Z τ).im : ℝ) : ℂ) * Complex.I := by
          rw [hzcoe, hsub]; ring
        rw [h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        linarith
      have hc := hdq (Z τ).im himτ.1 himτ.2 (Z τ) (axPt t) hZcen hzcen
      rw [hZj τ] at hc
      have h1 : D = ‖((Z τ : ℍ) : ℂ) - ((axPt t : ℍ) : ℂ)‖ := by
        rw [hDdef, norm_sub_rev]
      rw [← h1] at hc
      exact hc
    have hpos : 0 < D := by
      rw [hDdef]
      refine norm_pos_iff.mpr ?_
      intro h
      have h2 : axPt t = Z τ := UpperHalfPlane.ext (sub_eq_zero.mp h)
      exact hcoin (by rw [h2]; exact (hZj τ).symm)
    rw [Work.Kernels.Kaxis, dif_pos ht, ← axPt_eq_imagAxis htim, hdiv, norm_div]
    have hden : Dh * D ≤ ‖growthPrefactor d τ (axPt t)‖ := by
      rw [Work.Asymptotics.KaxisMid.norm_growthPrefactor]
      have hΔ : δ₁ ≤ ‖DeltaFun τ‖ := hbδ₁ τ hτ
      have hΔz : δ₂ ≤ ‖DeltaFun (axPt t)‖ := hbδ₂ (axPt t) (axPt_mem_contSeg htim ht3)
      have hpow : δ₂ ^ (if d = 8 then 1 else 2)
          ≤ ‖DeltaFun (axPt t)‖ ^ (if d = 8 then 1 else 2) := pow_le_pow_left₀ hδ₂.le hΔz _
      have h1 : δ₁ * δ₂ ^ (if d = 8 then 1 else 2)
          ≤ ‖DeltaFun τ‖ * ‖DeltaFun (axPt t)‖ ^ (if d = 8 then 1 else 2) :=
        mul_le_mul hΔ hpow (pow_nonneg hδ₂.le _) (norm_nonneg _)
      have hA : (0 : ℝ) ≤ ‖DeltaFun τ‖ * ‖DeltaFun (axPt t)‖ ^ (if d = 8 then 1 else 2) :=
        mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      have h1c : Dh
          ≤ (‖DeltaFun τ‖ * ‖DeltaFun (axPt t)‖ ^ (if d = 8 then 1 else 2)) * c₀ := by
        rw [hDh]
        exact mul_le_mul_of_nonneg_right h1 hc₀.le
      calc Dh * D
          ≤ ((‖DeltaFun τ‖ * ‖DeltaFun (axPt t)‖ ^ (if d = 8 then 1 else 2)) * c₀) * D :=
            mul_le_mul_of_nonneg_right h1c (norm_nonneg _)
        _ = (‖DeltaFun τ‖ * ‖DeltaFun (axPt t)‖ ^ (if d = 8 then 1 else 2)) * (c₀ * D) := by
            ring
        _ ≤ (‖DeltaFun τ‖ * ‖DeltaFun (axPt t)‖ ^ (if d = 8 then 1 else 2))
              * ‖jInvariantFun τ - jInvariantFun (axPt t)‖ :=
            mul_le_mul_of_nonneg_left hjc0 hA
    have hGPpos : 0 < ‖growthPrefactor d τ (axPt t)‖ :=
      lt_of_lt_of_le (mul_pos hDhpos hpos) hden
    have hN : ‖KfunClear ℓ d τ (axPt t)‖ ≤ (4 * M / (Z τ).im) * D := by
      refine le_trans hone' ?_
      have h2 : (2 * M / ((Z τ).im / 2)) = 4 * M / (Z τ).im := by
        field_simp
        ring
      rw [h2]
    have hmain : ‖KfunClear ℓ d τ (axPt t)‖ / ‖growthPrefactor d τ (axPt t)‖
        ≤ 4 * M / (a * Dh) := by
      rw [div_le_div_iff₀ hGPpos (by positivity)]
      calc ‖KfunClear ℓ d τ (axPt t)‖ * (a * Dh)
        ≤ ((4 * M / (Z τ).im) * D) * (a * Dh) :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = 4 * M * (a / (Z τ).im) * (Dh * D) := by field_simp
      _ ≤ 4 * M * 1 * (Dh * D) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (by rw [div_le_one hZi]; exact himτ.1) (by positivity)
      _ ≤ 4 * M * ‖growthPrefactor d τ (axPt t)‖ := by
          have := hden
          nlinarith [hM.le, this]
    exact le_trans hmain (le_max_right _ _)

/-! ## 6. The parameter regions and their geometry -/

/-- The contour point `i · max t ε` with an arbitrary positive cutoff. -/
def axPtE (ε : ℝ) (hε : 0 < ε) (t : ℝ) : ℍ :=
  ⟨(((max t ε : ℝ) : ℂ) * Complex.I), by
    have h : (((max t ε : ℝ) : ℂ) * Complex.I).im = max t ε := by simp [Complex.mul_im]
    rw [h]; exact lt_of_lt_of_le hε (le_max_right _ _)⟩

lemma axPtE_coe (ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    ((axPtE ε hε t : ℍ) : ℂ) = ((max t ε : ℝ) : ℂ) * Complex.I := rfl

lemma axPtE_eq_imagAxis (ε : ℝ) (hε : 0 < ε) {t : ℝ} (ht : ε ≤ t) :
    axPtE ε hε t = imagAxis t (lt_of_lt_of_le hε ht) := by
  apply UpperHalfPlane.ext
  rw [axPtE_coe, max_eq_left ht]
  rfl

/-- `blBox` is closed. -/
lemma isClosed_blBox : IsClosed blBox := by
  have h1 : IsClosed {τ : ℍ | (3 : ℝ) / 4 ≤ |τ.re|} :=
    isClosed_le continuous_const (continuous_abs.comp UpperHalfPlane.continuous_re)
  have h2 : IsClosed {τ : ℍ | |τ.re| ≤ (1 : ℝ)} :=
    isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const
  have h3 : IsClosed {τ : ℍ | (2 : ℝ) / 5 ≤ τ.im} :=
    isClosed_le continuous_const UpperHalfPlane.continuous_im
  have h4 : IsClosed {τ : ℍ | τ.im ≤ (1 : ℝ) / 2} :=
    isClosed_le UpperHalfPlane.continuous_im continuous_const
  have heq : blBox = {τ : ℍ | (3 : ℝ) / 4 ≤ |τ.re|} ∩ {τ : ℍ | |τ.re| ≤ (1 : ℝ)} ∩
      {τ : ℍ | (2 : ℝ) / 5 ≤ τ.im} ∩ {τ : ℍ | τ.im ≤ (1 : ℝ) / 2} := by
    ext τ; simp only [blBox, Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [heq]; exact ((h1.inter h2).inter h3).inter h4

lemma isCompact_blBox : IsCompact blBox :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_blBox, isBounded_blBox⟩

lemma closure_blLowSet_subset_blBox : closure blLowSet ⊆ blBox :=
  closure_minimal (fun τ h => mem_blBox h) isClosed_blBox

lemma isCompact_closure_blLowSet : IsCompact (closure blLowSet) :=
  isCompact_blBox.of_isClosed_subset isClosed_closure closure_blLowSet_subset_blBox

/-- Norm-square bounds on the closed box. -/
lemma normSq_bounds_of_blBox {τ : ℍ} (hτ : blBox τ) :
    289 / 400 ≤ ‖(τ : ℂ)‖ ^ 2 ∧ ‖(τ : ℂ)‖ ^ 2 ≤ 5 / 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := hτ
  have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  have hre1sq : ((3 : ℝ) / 4) ^ 2 ≤ τ.re ^ 2 := by
    have h : ((3 : ℝ) / 4) ^ 2 ≤ |τ.re| ^ 2 := by nlinarith [h1]
    rwa [sq_abs] at h
  have hhim1 : ((2 : ℝ) / 5) ^ 2 ≤ τ.im ^ 2 := by nlinarith [h3, h4, τ.im_pos]
  have hre2sq : τ.re ^ 2 ≤ 1 := by
    have h : |τ.re| ^ 2 ≤ 1 := by nlinarith [h2]
    rwa [sq_abs] at h
  have hhim2 : τ.im ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by nlinarith [h3, h4, τ.im_pos]
  constructor
  · rw [hsq]; nlinarith [hre1sq, hhim1]
  · rw [hsq]; nlinarith [hre2sq, hhim2]

/-- A point of `ℍ` with `blMargin > 0` and `|Re| < 1` lies in the fundamental domain `𝒟`. -/
lemma mem_DomainD_of_margin_pos {τ : ℍ} (hm : 0 < blMargin τ) (hre : |τ.re| < 1) :
    τ ∈ Work.Asymptotics.DomainD := by
  have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  rw [blMargin_eq, hsq] at hm
  obtain ⟨hr1, hr2⟩ := abs_lt.mp hre
  have h1 : ((1 : ℝ) / 2) ^ 2 < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
    have h : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    rw [h]
    rcases le_or_gt 0 τ.re with hre0 | hre0
    · nlinarith [hm, abs_of_nonneg hre0, sq_abs τ.re]
    · have hlt : τ.re < 0 := hre0
      nlinarith [hm, abs_of_neg hlt, sq_abs τ.re, sq_nonneg (τ.re - 1 / 2)]
  have h2 : ((1 : ℝ) / 2) ^ 2 < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by
    have h : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    rw [h]
    rcases le_or_gt 0 τ.re with hre0 | hre0
    · nlinarith [hm, abs_of_nonneg hre0, sq_abs τ.re, sq_nonneg (τ.re + 1 / 2)]
    · nlinarith [hm, abs_of_neg hre0, sq_abs τ.re]
  exact ⟨hr1, hr2, by nlinarith [norm_nonneg ((τ : ℂ) - (1 / 2 : ℂ))],
    by nlinarith [norm_nonneg ((τ : ℂ) + (1 / 2 : ℂ))]⟩

/-- For `τ ∈ 𝒟` with `Re τ ≠ 0` there is no coincidence of the contour with the orbit of `τ`. -/
lemma jInvariantFun_ne_axis_of_mem_DomainD {τ : ℍ} (hτ : τ ∈ Work.Asymptotics.DomainD)
    (hre : τ.re ≠ 0) {t : ℝ} (ht : 0 < t) :
    jInvariantFun τ ≠ jInvariantFun (imagAxis t ht) := by
  intro h
  have hzre : ((imagAxis t ht : ℍ) : ℂ).re = 0 := by
    show ((t : ℂ) * Complex.I).re = 0
    simp
  rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero hτ hzre h with h1 | h1
  · have h2 : ((imagAxis t ht : ℍ) : ℂ).re = τ.re := by rw [← h1]; rfl
    rw [hzre] at h2; exact hre h2.symm
  · have h2 : (ModularGroup.S • τ).re = 0 := by rw [← h1]; exact hzre
    rw [Work.HFN.HalfFunnel.sSre] at h2
    have h4 : ‖(τ : ℂ)‖ ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 ?_
      exact norm_ne_zero_iff.mpr (fun hh => hre (by rw [← UpperHalfPlane.coe_re, hh]; rfl))
    rcases div_eq_zero_iff.mp h2 with h5 | h5
    · exact hre (neg_eq_zero.mp h5)
    · exact absurd h5 h4

/-- The tangency margin is continuous. -/
lemma continuous_blMargin : Continuous blMargin := by
  have h2 : Continuous fun τ : ℍ => |τ.re| :=
    continuous_abs.comp UpperHalfPlane.continuous_re
  exact (UpperHalfPlane.continuous_im.pow 2).sub (h2.mul (continuous_const.sub h2))

/-- `blR` is continuous. -/
lemma continuous_blR : Continuous blR := by
  have h2 : Continuous fun τ : ℍ => |τ.re| :=
    continuous_abs.comp UpperHalfPlane.continuous_re
  exact continuous_const.sub h2

/-- The height of the first grazing branch. -/
noncomputable def hW (τ : ℍ) : ℝ := τ.im / ‖(τ : ℂ)‖ ^ 2

/-- `|Re|` of the first grazing branch, as a continuous function of `τ`. -/
noncomputable def gW (τ : ℍ) : ℝ := |blMargin τ| / ‖(τ : ℂ)‖ ^ 2

lemma hW_eq (τ : ℍ) : hW τ = (blW τ).im := by
  rw [hW, blW_im]

lemma gW_eq (τ : ℍ) : gW τ = |(blW τ).re| := by
  rw [gW, blW_re_abs]

lemma blW_norm_sq_eq (τ : ℍ) :
    ‖(blW τ : ℂ)‖ ^ 2 = (|blMargin τ| / ‖(τ : ℂ)‖ ^ 2) ^ 2 + (τ.im / ‖(τ : ℂ)‖ ^ 2) ^ 2 := by
  rw [blW_norm_sq, ← sq_abs ((blW τ).re), blW_re_abs, blW_im]

/-- The height of the second grazing branch. -/
noncomputable def hV (τ : ℍ) : ℝ :=
  (τ.im / ‖(τ : ℂ)‖ ^ 2) /
    ((|blMargin τ| / ‖(τ : ℂ)‖ ^ 2) ^ 2 + (τ.im / ‖(τ : ℂ)‖ ^ 2) ^ 2)

/-- `|Re|` of the second grazing branch. -/
noncomputable def gV (τ : ℍ) : ℝ :=
  |blMargin τ| / (‖(τ : ℂ)‖ ^ 2 *
    ((|blMargin τ| / ‖(τ : ℂ)‖ ^ 2) ^ 2 + (τ.im / ‖(τ : ℂ)‖ ^ 2) ^ 2))

lemma hV_eq (τ : ℍ) : hV τ = (blV τ).im := by
  rw [hV, blV_im, blW_im, blW_norm_sq_eq]

lemma gV_eq (τ : ℍ) : gV τ = |(blV τ).re| := by
  rw [gV, blV_re_abs, blW_norm_sq_eq]

lemma continuous_normSq_pos : ∀ τ : ℍ, ‖(τ : ℂ)‖ ^ 2 ≠ 0 := fun τ =>
  pow_ne_zero 2 (norm_ne_zero_iff.mpr τ.ne_zero)

lemma continuous_hW : Continuous hW :=
  UpperHalfPlane.continuous_im.div ((continuous_norm.comp UpperHalfPlane.continuous_coe).pow 2)
    continuous_normSq_pos

lemma continuous_gW : Continuous gW :=
  (continuous_abs.comp continuous_blMargin).div
    ((continuous_norm.comp UpperHalfPlane.continuous_coe).pow 2) continuous_normSq_pos

lemma continuous_hV : Continuous hV := (continuous_hW).div
  ((continuous_abs.comp continuous_blMargin).div
      ((continuous_norm.comp UpperHalfPlane.continuous_coe).pow 2) continuous_normSq_pos
    |>.pow 2 |>.add ((continuous_hW).pow 2))
  (fun τ => by
    have h1 : (0 : ℝ) < ‖(τ : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr τ.ne_zero) 2
    have h2 : (0 : ℝ) ≤ (|blMargin τ| / ‖(τ : ℂ)‖ ^ 2) ^ 2 := sq_nonneg _
    have h3 : (0 : ℝ) ≤ (τ.im / ‖(τ : ℂ)‖ ^ 2) ^ 2 := sq_nonneg _
    have h4 : τ.im / ‖(τ : ℂ)‖ ^ 2 ≠ 0 := by
      refine div_ne_zero (ne_of_gt τ.im_pos) (ne_of_gt h1)
    nlinarith [h2, h3, sq_pos_of_ne_zero h4])

lemma continuous_gV : Continuous gV :=
  (continuous_abs.comp continuous_blMargin).div
    (((continuous_norm.comp UpperHalfPlane.continuous_coe).pow 2).mul
      (((continuous_abs.comp continuous_blMargin).div
          ((continuous_norm.comp UpperHalfPlane.continuous_coe).pow 2) continuous_normSq_pos
        |>.pow 2 |>.add ((continuous_hW).pow 2))))
    (fun τ => mul_ne_zero (continuous_normSq_pos τ) (by
      have h1 : (0 : ℝ) < ‖(τ : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr τ.ne_zero) 2
      have h2 : (0 : ℝ) ≤ (|blMargin τ| / ‖(τ : ℂ)‖ ^ 2) ^ 2 := sq_nonneg _
      have h3 : (0 : ℝ) ≤ (τ.im / ‖(τ : ℂ)‖ ^ 2) ^ 2 := sq_nonneg _
      have h4 : τ.im / ‖(τ : ℂ)‖ ^ 2 ≠ 0 :=
        div_ne_zero (ne_of_gt τ.im_pos) (ne_of_gt h1)
      nlinarith [h2, h3, sq_pos_of_ne_zero h4]))


/-! ## 7. The four windows -/

/-- The contour points `i t` for `t ≥ δc`, as a compact subset of `ℍ`. -/
def contSegLo (δc : ℝ) (hδc : 0 < δc) : Set ℍ := axPtE δc hδc '' Set.Icc δc 3

lemma isCompact_contSegLo (δc : ℝ) (hδc : 0 < δc) : IsCompact (contSegLo δc hδc) :=
  isCompact_Icc.image (by
    rw [continuous_induced_rng (f := UpperHalfPlane.coe)]
    show Continuous fun t : ℝ => (((max t δc : ℝ) : ℂ) * Complex.I)
    exact (Complex.continuous_ofReal.comp
      (continuous_max.comp (continuous_id.prodMk continuous_const))).mul continuous_const)

lemma axPtE_mem_contSegLo (δc : ℝ) (hδc : 0 < δc) {t : ℝ} (h1 : δc ≤ t) (h2 : t ≤ 3) :
    axPtE δc hδc t ∈ contSegLo δc hδc := ⟨t, ⟨h1, h2⟩, rfl⟩

/-- The S-branch height for `Re τ > 0`. -/
noncomputable def hS (τ : ℍ) : ℝ := τ.im / ((τ.re - 1) ^ 2 + τ.im ^ 2)

/-- `|Re|` of the S-branch point for `Re τ > 0`. -/
noncomputable def gS (τ : ℍ) : ℝ := |τ.re - 1| / ((τ.re - 1) ^ 2 + τ.im ^ 2)

/-- The S-branch height for `Re τ < 0`. -/
noncomputable def hS' (τ : ℍ) : ℝ := τ.im / ((τ.re + 1) ^ 2 + τ.im ^ 2)

/-- `|Re|` of the S-branch point for `Re τ < 0`. -/
noncomputable def gS' (τ : ℍ) : ℝ := |τ.re + 1| / ((τ.re + 1) ^ 2 + τ.im ^ 2)

/-- The S-branch curve for `Re τ > 0`: `S • (τ - 1)`. -/
noncomputable def ZsP (τ : ℍ) : ℍ := ModularGroup.S • ((-1 : ℝ) +ᵥ τ)

/-- The S-branch curve for `Re τ < 0`: `S • (τ + 1)`. -/
noncomputable def ZsM (τ : ℍ) : ℍ := ModularGroup.S • ((1 : ℝ) +ᵥ τ)

lemma normSq_vadd_neg_one (τ : ℍ) :
    ‖(((-1 : ℝ) +ᵥ τ : ℍ) : ℂ)‖ ^ 2 = (τ.re - 1) ^ 2 + τ.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, UpperHalfPlane.vadd_re,
    UpperHalfPlane.vadd_im]
  ring

lemma normSq_vadd_one (τ : ℍ) :
    ‖(((1 : ℝ) +ᵥ τ : ℍ) : ℂ)‖ ^ 2 = (τ.re + 1) ^ 2 + τ.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, UpperHalfPlane.vadd_re,
    UpperHalfPlane.vadd_im]
  ring

lemma hS_eq (τ : ℍ) : hS τ = (ZsP τ).im := by
  rw [hS, ZsP, Work.Asymptotics.KaxisMid.KbcAux2.im_S, UpperHalfPlane.vadd_im,
    normSq_vadd_neg_one]

lemma gS_eq (τ : ℍ) : gS τ = |(ZsP τ).re| := by
  have hpos : 0 < (τ.re - 1) ^ 2 + τ.im ^ 2 := by nlinarith [sq_nonneg (τ.re - 1), τ.im_pos]
  have hre : (ZsP τ).re = -(τ.re - 1) / ((τ.re - 1) ^ 2 + τ.im ^ 2) := by
    rw [ZsP, Work.HFN.HalfFunnel.sSre, normSq_vadd_neg_one, UpperHalfPlane.vadd_re]
    ring
  rw [gS, hre, abs_div, abs_neg, abs_of_pos hpos]

lemma hS'_eq (τ : ℍ) : hS' τ = (ZsM τ).im := by
  rw [hS', ZsM, Work.Asymptotics.KaxisMid.KbcAux2.im_S, UpperHalfPlane.vadd_im,
    normSq_vadd_one]

lemma gS'_eq (τ : ℍ) : gS' τ = |(ZsM τ).re| := by
  have hpos : 0 < (τ.re + 1) ^ 2 + τ.im ^ 2 := by nlinarith [sq_nonneg (τ.re + 1), τ.im_pos]
  have hre : (ZsM τ).re = -(τ.re + 1) / ((τ.re + 1) ^ 2 + τ.im ^ 2) := by
    rw [ZsM, Work.HFN.HalfFunnel.sSre, normSq_vadd_one, UpperHalfPlane.vadd_re]
    ring
  rw [gS', hre, abs_div, abs_neg, abs_of_pos hpos]

lemma ZsP_clear (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) :
    KfunClear ℓ d τ (ZsP τ) = 0 := by
  have h := Work.Asymptotics.AfunFun_S_vadd_zero ℓ d hd 1 (Or.inl rfl) ((-1 : ℝ) +ᵥ τ)
  have hv : (((1 : ℤ) : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ)) = τ := by
    rw [show (((1 : ℤ) : ℝ)) = (1 : ℝ) by norm_num, ← vadd_assoc]; norm_num
  have h' : AfunFun ℓ d τ (ModularGroup.S • ((-1 : ℝ) +ᵥ τ)) = 0 := by
    rw [hv] at h; exact h
  rw [ZsP, Work.Asymptotics.KfunClear_eq_mul_AfunFun ℓ d τ
    (ModularGroup.S • ((-1 : ℝ) +ᵥ τ)), h', mul_zero]

lemma ZsM_clear (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : ℍ) :
    KfunClear ℓ d τ (ZsM τ) = 0 := by
  have h := Work.Asymptotics.AfunFun_S_vadd_zero ℓ d hd (-1) (Or.inr rfl) ((1 : ℝ) +ᵥ τ)
  have hv : (((-1 : ℤ) : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ)) = τ := by
    rw [show (((-1 : ℤ) : ℝ)) = (-1 : ℝ) by norm_num, ← vadd_assoc]; norm_num
  have h' : AfunFun ℓ d τ (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) = 0 := by
    rw [hv] at h; exact h
  rw [ZsM, Work.Asymptotics.KfunClear_eq_mul_AfunFun ℓ d τ
    (ModularGroup.S • ((1 : ℝ) +ᵥ τ)), h', mul_zero]

lemma ZsP_j (τ : ℍ) : jInvariantFun (ZsP τ) = jInvariantFun τ := by
  rw [ZsP, Work.Kernels.KernelFacts.jInvariantFun_S_smul, jInvariantFun_vadd_neg_one]

lemma ZsM_j (τ : ℍ) : jInvariantFun (ZsM τ) = jInvariantFun τ := by
  rw [ZsM, Work.Kernels.KernelFacts.jInvariantFun_S_smul,
    Work.Kernels.KernelFacts.jInvariantFun_vadd_one]

lemma continuous_hS : Continuous hS :=
  UpperHalfPlane.continuous_im.div
    (((UpperHalfPlane.continuous_re.sub continuous_const).pow 2).add
      (UpperHalfPlane.continuous_im.pow 2))
    (fun τ => by
      have hpos : 0 < (τ.re - 1) ^ 2 + τ.im ^ 2 := by
        nlinarith [sq_nonneg (τ.re - 1), τ.im_pos]
      exact ne_of_gt hpos)

lemma continuous_gS : Continuous gS :=
  (continuous_abs.comp (UpperHalfPlane.continuous_re.sub continuous_const)).div
    (((UpperHalfPlane.continuous_re.sub continuous_const).pow 2).add
      (UpperHalfPlane.continuous_im.pow 2))
    (fun τ => by
      have hpos : 0 < (τ.re - 1) ^ 2 + τ.im ^ 2 := by
        nlinarith [sq_nonneg (τ.re - 1), τ.im_pos]
      exact ne_of_gt hpos)

lemma continuous_hS' : Continuous hS' :=
  UpperHalfPlane.continuous_im.div
    (((UpperHalfPlane.continuous_re.add continuous_const).pow 2).add
      (UpperHalfPlane.continuous_im.pow 2))
    (fun τ => by
      have hpos : 0 < (τ.re + 1) ^ 2 + τ.im ^ 2 := by
        nlinarith [sq_nonneg (τ.re + 1), τ.im_pos]
      exact ne_of_gt hpos)

lemma continuous_gS' : Continuous gS' :=
  (continuous_abs.comp (UpperHalfPlane.continuous_re.add continuous_const)).div
    (((UpperHalfPlane.continuous_re.add continuous_const).pow 2).add
      (UpperHalfPlane.continuous_im.pow 2))
    (fun τ => by
      have hpos : 0 < (τ.re + 1) ^ 2 + τ.im ^ 2 := by
        nlinarith [sq_nonneg (τ.re + 1), τ.im_pos]
      exact ne_of_gt hpos)

/-- The height bounds of the two S-branches on the half-boxes. -/
lemma hS_bounds {τ : ℍ} (h1 : (3 : ℝ) / 4 ≤ τ.re) (h2 : |τ.re| ≤ 1)
    (h3 : (2 : ℝ) / 5 ≤ τ.im) (h4 : τ.im ≤ 1 / 2) :
    (5 : ℝ) / 4 ≤ hS τ ∧ hS τ ≤ 16 / 5 := by
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  have h5 : τ.re - 1 ≤ 0 := by linarith
  have h6 : (τ.re - 1) ^ 2 ≤ ((1 : ℝ) / 4) ^ 2 := by
    have h7 : -(1 : ℝ) / 4 ≤ τ.re - 1 := by linarith
    nlinarith
  have h7 : ((2 : ℝ) / 5) ^ 2 ≤ τ.im ^ 2 := by nlinarith [h3, h4, τ.im_pos]
  have h8 : τ.im ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by nlinarith [h3, h4, τ.im_pos]
  have hden1 : (4 : ℝ) / 25 ≤ (τ.re - 1) ^ 2 + τ.im ^ 2 := by nlinarith [h7]
  have hden2 : (τ.re - 1) ^ 2 + τ.im ^ 2 ≤ 5 / 16 := by nlinarith [h6, h8]
  have hdenp : 0 < (τ.re - 1) ^ 2 + τ.im ^ 2 := by nlinarith [h7]
  constructor
  · rw [hS, le_div_iff₀ hdenp]
    nlinarith [h3, hden2]
  · rw [hS, div_le_iff₀ hdenp]
    nlinarith [h4, hden1]

lemma hS'_bounds {τ : ℍ} (h1 : τ.re ≤ -(3 : ℝ) / 4) (h2 : |τ.re| ≤ 1)
    (h3 : (2 : ℝ) / 5 ≤ τ.im) (h4 : τ.im ≤ 1 / 2) :
    (5 : ℝ) / 4 ≤ hS' τ ∧ hS' τ ≤ 16 / 5 := by
  obtain ⟨h2a, h2b⟩ := abs_le.mp h2
  have h6 : (τ.re + 1) ^ 2 ≤ ((1 : ℝ) / 4) ^ 2 := by
    have h5 : τ.re + 1 ≤ (1 : ℝ) / 4 := by linarith
    have h7 : 0 ≤ τ.re + 1 := by linarith
    nlinarith
  have h7 : ((2 : ℝ) / 5) ^ 2 ≤ τ.im ^ 2 := by nlinarith [h3, h4, τ.im_pos]
  have h8 : τ.im ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by nlinarith [h3, h4, τ.im_pos]
  have hden1 : (4 : ℝ) / 25 ≤ (τ.re + 1) ^ 2 + τ.im ^ 2 := by nlinarith [h7]
  have hden2 : (τ.re + 1) ^ 2 + τ.im ^ 2 ≤ 5 / 16 := by nlinarith [h6, h8]
  have hdenp : 0 < (τ.re + 1) ^ 2 + τ.im ^ 2 := by nlinarith [h7]
  constructor
  · rw [hS', le_div_iff₀ hdenp]
    nlinarith [h3, hden2]
  · rw [hS', div_le_iff₀ hdenp]
    nlinarith [h4, hden1]

/-- The height bounds of the first grazing branch on the closed box. -/
lemma hW_bounds {τ : ℍ} (hτ : blBox τ) : (1 : ℝ) / 4 ≤ hW τ ∧ hW τ ≤ 3 / 4 := by
  obtain ⟨hn1, hn2⟩ := normSq_bounds_of_blBox hτ
  have hpos : 0 < ‖(τ : ℂ)‖ ^ 2 := by linarith
  have him1 : (2 : ℝ) / 5 ≤ τ.im := hτ.2.2.1
  have him2 : τ.im ≤ 1 / 2 := hτ.2.2.2
  rw [hW_eq, blW_im]
  constructor
  · rw [le_div_iff₀ hpos]; nlinarith [him1, hn2]
  · rw [div_le_iff₀ hpos]; nlinarith [him2, hn1]

/-- The height bounds of the second grazing branch when the tangency margin is small. -/
lemma hV_bounds {τ : ℍ} (hτ : blBox τ) (hm : |blMargin τ| ≤ 1 / 100) :
    (7 : ℝ) / 5 ≤ hV τ ∧ hV τ ≤ 16 / 5 := by
  obtain ⟨hn1, hn2⟩ := normSq_bounds_of_blBox hτ
  have hpos : 0 < ‖(τ : ℂ)‖ ^ 2 := by linarith
  have him1 : (2 : ℝ) / 5 ≤ τ.im := hτ.2.2.1
  have him2 : τ.im ≤ 1 / 2 := hτ.2.2.2
  set a : ℝ := τ.im / ‖(τ : ℂ)‖ ^ 2 with ha
  set b : ℝ := |blMargin τ| / ‖(τ : ℂ)‖ ^ 2 with hb
  have ha1 : (8 : ℝ) / 25 ≤ a := by
    rw [ha, le_div_iff₀ hpos]; nlinarith [him1, hn2]
  have ha2 : a ≤ 200 / 289 := by
    rw [ha, div_le_iff₀ hpos]; nlinarith [him2, hn1]
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hb2 : b ≤ 4 / 289 := by
    rw [hb]
    have h : (1 : ℝ) / 100 / (289 / 400) = 4 / 289 := by norm_num
    calc |blMargin τ| / ‖(τ : ℂ)‖ ^ 2 ≤ (1 / 100) / (289 / 400) :=
          div_le_div₀ (by norm_num) hm (by norm_num) hn1
      _ = 4 / 289 := h
  have hapos : 0 < a := by linarith
  have hdenp : 0 < a ^ 2 + b ^ 2 := by positivity
  have hVval : hV τ = a / (a ^ 2 + b ^ 2) := by
    rw [hV_eq, blV_im, blW_im, blW_norm_sq_eq, ← ha, ← hb, add_comm]
  rw [hVval]
  have hb2sq : b ^ 2 ≤ (4 / 289 : ℝ) ^ 2 := by nlinarith [hb0, hb2]
  have ha2sq : a ^ 2 ≤ (200 / 289 : ℝ) * a := by nlinarith [ha2, hapos]
  constructor
  · rw [le_div_iff₀ hdenp]
    have hkey : (7 : ℝ) / 5 * ((200 / 289 : ℝ) * a + (4 / 289 : ℝ) ^ 2) ≤ a := by
      nlinarith [ha1]
    nlinarith [hkey, ha2sq, hb2sq]
  · rw [div_le_iff₀ hdenp]
    have hasq : a ≤ (16 : ℝ) / 5 * a ^ 2 := by
      have h : (5 : ℝ) / 16 ≤ a := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h hapos.le, hapos]
    nlinarith [hasq, sq_nonneg b]

/-! ## 8. Auxiliary geometry for the assembly -/

lemma isCompact_of_subset_blBox {S : Set ℍ} (hS : S ⊆ blBox) (hcl : IsClosed S) :
    IsCompact S :=
  isCompact_blBox.of_isClosed_subset hcl hS

/-- The `ε`-contour point is continuous in the height. -/
lemma axPtE_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (axPtE ε hε) := by
  rw [continuous_induced_rng (f := UpperHalfPlane.coe)]
  show Continuous fun t : ℝ => ((axPtE ε hε t : ℍ) : ℂ)
  rw [show (fun t : ℝ => ((axPtE ε hε t : ℍ) : ℂ))
      = fun t => ((max t ε : ℝ) : ℂ) * Complex.I from funext fun t => axPtE_coe ε hε t]
  exact (Complex.continuous_ofReal.comp
    (continuous_max.comp (continuous_id.prodMk continuous_const))).mul continuous_const

/-- Points of `ℍ` with vanishing real part lie in the fundamental domain `𝒟`. -/
lemma mem_DomainD_of_re_eq_zero {z : ℍ} (hre : z.re = 0) : z ∈ Work.Asymptotics.DomainD := by
  have h1 : ((1 : ℝ) / 2) ^ 2 < ‖(z : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
    have hh : ‖(z : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (1 / 4 : ℝ) + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hre]
      ring
    rw [hh]; nlinarith [z.im_pos]
  have h2 : ((1 : ℝ) / 2) ^ 2 < ‖(z : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by
    have hh : ‖(z : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (1 / 4 : ℝ) + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hre]
      ring
    rw [hh]; nlinarith [z.im_pos]
  refine ⟨by rw [hre]; norm_num, by rw [hre]; norm_num, ?_, ?_⟩
  · nlinarith [norm_nonneg ((z : ℂ) - (1 / 2 : ℂ)), h1]
  · nlinarith [norm_nonneg ((z : ℂ) + (1 / 2 : ℂ)), h2]

/-- On the closure of `blLowSet` the tangency margin is nonnegative. -/
lemma blMargin_nonneg_of_closure {τ : ℍ} (hτ : τ ∈ closure blLowSet) : 0 ≤ blMargin τ :=
  closure_minimal (fun _ hσ => (blLowSet_margin_pos hσ).le)
    (isClosed_le continuous_const continuous_blMargin) hτ

/-- On the tangency arc the grazing branch `blW τ` is purely imaginary. -/
lemma blW_re_eq_zero_of_margin_eq_zero {τ : ℍ} (hm : blMargin τ = 0) : (blW τ).re = 0 := by
  have hsq : ‖(τ : ℂ)‖ ^ 2 = |τ.re| := by
    have h := blMargin_eq τ
    linarith
  have hpos : 0 < ‖(τ : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr τ.ne_zero) 2
  have hne : τ.re ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hsq
    rw [hsq] at hpos
    exact lt_irrefl 0 hpos
  rw [blW_re, hsq]
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 : tsign τ = -1 := by unfold tsign; rw [if_neg (not_lt.mpr h.le)]
    rw [h1, abs_of_neg h, div_neg, div_self hne]
    ring
  · have h1 : tsign τ = 1 := by unfold tsign; rw [if_pos h]
    rw [h1, abs_of_pos h, div_self hne]
    ring

/-- On the tangency arc, the grazing branch itself is a point of `𝒟`. -/
lemma blW_mem_DomainD_of_margin_eq_zero {τ : ℍ} (hm : blMargin τ = 0) :
    blW τ ∈ Work.Asymptotics.DomainD :=
  mem_DomainD_of_re_eq_zero (blW_re_eq_zero_of_margin_eq_zero hm)

/-- **The coincidence set of `blLowSet` on the imaginary axis.**  For `τ` in the closure of
`blLowSet` the only heights at which the contour `i t` meets the orbit of `τ` are the translate
height `Im τ` (excluded by `1/8 ≤ |t - Im τ|`) and the four branch heights `hS`, `hS'`, `hW`,
`hV`; the hypotheses `h1`--`h4` exclude those. -/
lemma offcoin_closure {τ : ℍ} {t : ℝ} (hτ : τ ∈ closure blLowSet) (ht : 0 < t)
    (hsep : (1 / 8 : ℝ) ≤ |t - τ.im|)
    {αs βs αs' βs' αW βW αV βV : ℝ}
    (hαs : 0 < αs) (hβs : 0 < βs) (hαs' : 0 < αs') (hβs' : 0 < βs')
    (hαW : 0 < αW) (hβW : 0 < βW) (hαV : 0 < αV) (hβV : 0 < βV)
    (h1 : αs ≤ gS τ ∨ τ.re ≤ 3 / 4 ∨ βs ≤ |t - hS τ|)
    (h2 : -3 / 4 ≤ τ.re ∨ αs' ≤ gS' τ ∨ βs' ≤ |t - hS' τ|)
    (h3 : αW ≤ gW τ ∨ βW ≤ |t - hW τ|)
    (h4 : αV ≤ gV τ ∨ 1 / 100 ≤ |blMargin τ| ∨ βV ≤ |t - hV τ|) :
    jInvariantFun τ ≠ jInvariantFun (imagAxis t ht) := by
  intro hcoin
  have hbox : blBox τ := closure_blLowSet_subset_blBox hτ
  have hzj : ((imagAxis t ht : ℍ) : ℂ).re = 0 := by
    show ((t : ℂ) * Complex.I).re = 0; simp
  have ht_im : (imagAxis t ht).im = t := by
    show ((t : ℂ) * Complex.I).im = t; simp
  rcases lt_or_eq_of_le hbox.2.1 with hlt | heq
  · rcases lt_or_eq_of_le (blMargin_nonneg_of_closure hτ) with hmpos | hm0'
    · have hre : τ.re ≠ 0 := by
        intro h0
        have h1 : (3 : ℝ) / 4 ≤ |τ.re| := hbox.1
        rw [h0, abs_zero] at h1
        norm_num at h1
      exact jInvariantFun_ne_axis_of_mem_DomainD (mem_DomainD_of_margin_pos hmpos hlt) hre ht hcoin
    · have hm0 : blMargin τ = 0 := hm0'.symm
      have hD : blW τ ∈ Work.Asymptotics.DomainD := blW_mem_DomainD_of_margin_eq_zero hm0
      have hσre : ((blW τ : ℍ) : ℂ).re = 0 := by
        rw [UpperHalfPlane.coe_re]; exact blW_re_eq_zero_of_margin_eq_zero hm0
      have hjeq : jInvariantFun (blW τ) = jInvariantFun (imagAxis t ht) := by
        rw [blW_jInvariantFun]; exact hcoin
      rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero hD hzj hjeq with h | h
      · have htW : t = hW τ := by
          have h' := congrArg UpperHalfPlane.im h
          rw [ht_im, ← hW_eq] at h'
          exact h'
        have hgW : gW τ = 0 := by simp [gW, hm0]
        rcases h3 with h3 | h3
        · rw [hgW] at h3; linarith
        · rw [htW, sub_self, abs_zero] at h3; linarith
      · have htV : t = hV τ := by
          have h' := congrArg UpperHalfPlane.im h
          rw [ht_im, show ModularGroup.S • blW τ = blV τ from rfl, ← hV_eq] at h'
          exact h'
        have hgV : gV τ = 0 := by simp [gV, hm0]
        rcases h4 with h4 | h4 | h4
        · rw [hgV] at h4; linarith
        · rw [hm0, abs_zero] at h4; linarith
        · rw [htV, sub_self, abs_zero] at h4; linarith
  · rcases abs_eq_abs.mp (by rw [heq]; norm_num : |τ.re| = |(1 : ℝ)|) with hre1 | hre1
    · have hD : ((-1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD :=
        mem_DomainD_of_re_eq_zero (by rw [UpperHalfPlane.vadd_re, hre1]; norm_num)
      have hjeq : jInvariantFun ((-1 : ℝ) +ᵥ τ) = jInvariantFun (imagAxis t ht) := by
        rw [jInvariantFun_vadd_neg_one]; exact hcoin
      rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero hD hzj hjeq with h | h
      · have htim : t = τ.im := by
          have h' := congrArg UpperHalfPlane.im h
          rw [ht_im, UpperHalfPlane.vadd_im] at h'
          exact h'
        rw [htim, sub_self, abs_zero] at hsep
        norm_num at hsep
      · have htS : t = hS τ := by
          have h' := congrArg UpperHalfPlane.im h
          rw [ht_im, show ModularGroup.S • ((-1 : ℝ) +ᵥ τ) = ZsP τ from rfl, ← hS_eq] at h'
          exact h'
        have hgS : gS τ = 0 := by simp [gS, hre1]
        rcases h1 with h1 | h1 | h1
        · rw [hgS] at h1; linarith
        · rw [hre1] at h1; norm_num at h1
        · rw [htS, sub_self, abs_zero] at h1; linarith
    · have hD : ((1 : ℝ) +ᵥ τ) ∈ Work.Asymptotics.DomainD :=
        mem_DomainD_of_re_eq_zero (by rw [UpperHalfPlane.vadd_re, hre1]; norm_num)
      have hjeq : jInvariantFun ((1 : ℝ) +ᵥ τ) = jInvariantFun (imagAxis t ht) := by
        rw [Work.Kernels.KernelFacts.jInvariantFun_vadd_one]; exact hcoin
      rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero hD hzj hjeq with h | h
      · have htim : t = τ.im := by
          have h' := congrArg UpperHalfPlane.im h
          rw [ht_im, UpperHalfPlane.vadd_im] at h'
          exact h'
        rw [htim, sub_self, abs_zero] at hsep
        norm_num at hsep
      · have htS : t = hS' τ := by
          have h' := congrArg UpperHalfPlane.im h
          rw [ht_im, show ModularGroup.S • ((1 : ℝ) +ᵥ τ) = ZsM τ from rfl, ← hS'_eq] at h'
          exact h'
        have hgS : gS' τ = 0 := by simp [gS', hre1]
        rcases h2 with h2 | h2 | h2
        · rw [hre1] at h2; norm_num at h2
        · rw [hgS] at h2; linarith
        · rw [htS, sub_self, abs_zero] at h2; linarith

/-! ## 9. The grazing branch vanishings (kernel-checked) -/

private lemma ST_mul_TinvS' : (ModularGroup.S * ModularGroup.T) *
    (ModularGroup.T⁻¹ * ModularGroup.S) = -1 := by decide

private lemma TST_mul_STS' : (ModularGroup.T * ModularGroup.S * ModularGroup.T) *
    (ModularGroup.S * (ModularGroup.T * ModularGroup.S)) = -1 := by decide

private lemma TSTinv_mul_STinvS' : (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹ *
    (ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.S)) = -1 := by decide

/-- The cleared kernel vanishes at the first grazing branch `blW τ` (kernel-checked proof). -/
theorem KfunClear_blW' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) : KfunClear ℓ d τ (blW τ) = 0 := by
  rcases lt_or_ge 0 τ.re with h | h
  · have h1 : blW τ = (1 : ℝ) +ᵥ (ModularGroup.S • τ) := by
      rw [blW, show tsign τ = 1 from by unfold tsign; rw [if_pos h]]
    rw [h1]
    exact KfunClear_vadd_S ℓ d hd τ
  · rw [blW_eq_smul' h]
    have hv := KfunClear_graze_eq_zero ℓ d hd (ModularGroup.S * ModularGroup.T)
      (Or.inr (Or.inr (Or.inl rfl))) ((ModularGroup.T⁻¹ * ModularGroup.S) • τ)
    rw [← mul_smul, ST_mul_TinvS', SL_neg_smul, one_smul] at hv
    exact hv

/-- The cleared kernel vanishes at the second grazing branch `blV τ` (kernel-checked proof). -/
theorem KfunClear_blV' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) : KfunClear ℓ d τ (blV τ) = 0 := by
  rcases lt_or_ge 0 τ.re with h | h
  · rw [blV_eq_smul h]
    have hv := KfunClear_graze_eq_zero ℓ d hd
      (ModularGroup.T * ModularGroup.S * ModularGroup.T)
      (Or.inl rfl) ((ModularGroup.S * (ModularGroup.T * ModularGroup.S)) • τ)
    rw [← mul_smul, TST_mul_STS', SL_neg_smul, one_smul] at hv
    exact hv
  · rw [blV_eq_smul' h]
    have hv := KfunClear_graze_eq_zero ℓ d hd
      (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹
      (Or.inr (Or.inr (Or.inr rfl)))
      ((ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.S)) • τ)
    rw [← mul_smul, TSTinv_mul_STinvS', SL_neg_smul, one_smul] at hv
    exact hv

/-! ## 9b. The assembly -/

/-- **Off-window bound of the CKMRV kernel on the low bad-line region.** For `τ` in
`blLowSet` (`{τ ∈ 𝒟 : 2/5 ≤ Im τ ≤ 1/2, |Re τ| > 3/4}`) and `0 < t ≤ lowT = 3` with
`1/8 ≤ |t - Im τ|`, the contour kernel `Kaxis (Kfun ℓ d) τ t` is bounded by a constant
independent of `τ` and `t`.

Low-height analogue of the proved `Work.Asymptotics.HalfFunnel.lowBad_Kaxis_bound`
(via `lowBad_Kaxis_bound_aux`).  Route: adapt `lowBad_Kaxis_bound_aux`, replacing `lowBadSet` by
`blLowSet`, the height bounds `1/2 ≤ τ.im ≤ 2` by `2/5 ≤ τ.im ≤ 1/2`, the arcs
`exists_diffQuotient_lower_uniform (1/2) (99/100)` / `(101/100) 2` by arcs covering
`[11/40, 5/8]` and `[2, 5/2]` (the latter for the S-branch heights `1/Im τ ∈ [2, 5/2]`), and
`translate_mem_DomainD` by the proof that the translate `τ ∓ 1` lies in `𝒟` because `τ ∈ 𝒟`.

The extra pole of this height range, the crossed translate `z = TS·τ = 1 - 1/τ` (height
`Im τ/|τ|² ∈ (0.32, 0.69)`, approaching the contour as `τ` tends to the tangency arc
`|τ - 1/2| = 1/2`, `Re τ > 0`), is *removable*: the proved
`Work.Asymptotics.BlLow.KfunClear_vadd_S` gives `KfunClear ℓ d τ (1 + S·τ) = 0`, and
`Kfun ℓ d τ ζ = KfunClear ℓ d τ ζ/(Δ τ Δ ζ^e (j τ - j ζ))` extends continuously across it
(numerator and denominator both vanish to order 1 there; `jprime` does not vanish at a point of
height `≈ 0.5`).  Note also that the far-case compactness step must use the cleared kernel,
since on the closed box `blBox` (which meets the tangency arc) coincidences do occur. -/
theorem offwindow_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      Work.Asymptotics.BlLow.blLowSet τ → 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT → (1 / 8 : ℝ) ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨δc, hδc, cc, hcc, hcusp⟩ := Work.HFN.BlLow.lowBad_flat ℓ d hd 0 le_rfl
  -- the compact half boxes carrying the two `S`-branches
  have hKsP : IsCompact {τ : ℍ | (3 : ℝ) / 4 ≤ τ.re ∧ |τ.re| ≤ 1 ∧ (2 : ℝ) / 5 ≤ τ.im ∧
      τ.im ≤ 1 / 2} := by
    refine isCompact_of_subset_blBox ?_ ?_
    · rintro τ ⟨h1, h2, h3, h4⟩
      exact ⟨le_trans h1 (le_abs_self _), h2, h3, h4⟩
    · have heq : {τ : ℍ | (3 : ℝ) / 4 ≤ τ.re ∧ |τ.re| ≤ 1 ∧ (2 : ℝ) / 5 ≤ τ.im ∧ τ.im ≤ 1 / 2} =
          {τ : ℍ | (3 : ℝ) / 4 ≤ τ.re} ∩ {τ : ℍ | |τ.re| ≤ 1} ∩ {τ : ℍ | (2 : ℝ) / 5 ≤ τ.im} ∩
            {τ : ℍ | τ.im ≤ 1 / 2} := by
        ext τ; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
      rw [heq]
      exact (((isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
        (isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const)).inter
        (isClosed_le continuous_const UpperHalfPlane.continuous_im)).inter
        (isClosed_le UpperHalfPlane.continuous_im continuous_const)
  have hKsM : IsCompact {τ : ℍ | τ.re ≤ -(3 : ℝ) / 4 ∧ |τ.re| ≤ 1 ∧ (2 : ℝ) / 5 ≤ τ.im ∧
      τ.im ≤ 1 / 2} := by
    refine isCompact_of_subset_blBox ?_ ?_
    · rintro τ ⟨h1, h2, h3, h4⟩
      exact ⟨le_trans (by linarith : (3 : ℝ) / 4 ≤ -τ.re) (neg_le_abs _), h2, h3, h4⟩
    · have heq : {τ : ℍ | τ.re ≤ -(3 : ℝ) / 4 ∧ |τ.re| ≤ 1 ∧ (2 : ℝ) / 5 ≤ τ.im ∧ τ.im ≤ 1 / 2} =
          {τ : ℍ | τ.re ≤ -(3 : ℝ) / 4} ∩ {τ : ℍ | |τ.re| ≤ 1} ∩ {τ : ℍ | (2 : ℝ) / 5 ≤ τ.im} ∩
            {τ : ℍ | τ.im ≤ 1 / 2} := by
        ext τ; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
      rw [heq]
      exact (((isClosed_le UpperHalfPlane.continuous_re continuous_const).inter
        (isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re) continuous_const)).inter
        (isClosed_le continuous_const UpperHalfPlane.continuous_im)).inter
        (isClosed_le UpperHalfPlane.continuous_im continuous_const)
  have hKarc : IsCompact {τ : ℍ | blBox τ ∧ |blMargin τ| ≤ 1 / 100} :=
    isCompact_of_subset_blBox (fun τ h => h.1)
      (isClosed_blBox.inter (isClosed_le (continuous_abs.comp continuous_blMargin) continuous_const))
  -- the four windows
  obtain ⟨Cs, αs, βs, hCs, hαs, hβs, hαβs, hbS⟩ := branch_window ℓ d hd
    (a := 5 / 4) (b := 16 / 5) (by norm_num) (by norm_num) (by norm_num) (Or.inr (by norm_num))
    ZsP (ZsP_clear ℓ d hd) ZsP_j
    (K := {τ : ℍ | (3 : ℝ) / 4 ≤ τ.re ∧ |τ.re| ≤ 1 ∧ (2 : ℝ) / 5 ≤ τ.im ∧ τ.im ≤ 1 / 2}) hKsP
    (fun τ hτ => by
      obtain ⟨h1, h2, h3, h4⟩ := hτ
      rw [← hS_eq]
      exact hS_bounds h1 h2 h3 h4)
  obtain ⟨Cs', αs', βs', hCs', hαs', hβs', hαβs', hbS'⟩ := branch_window ℓ d hd
    (a := 5 / 4) (b := 16 / 5) (by norm_num) (by norm_num) (by norm_num) (Or.inr (by norm_num))
    ZsM (ZsM_clear ℓ d hd) ZsM_j
    (K := {τ : ℍ | τ.re ≤ -(3 : ℝ) / 4 ∧ |τ.re| ≤ 1 ∧ (2 : ℝ) / 5 ≤ τ.im ∧ τ.im ≤ 1 / 2}) hKsM
    (fun τ hτ => by
      obtain ⟨h1, h2, h3, h4⟩ := hτ
      rw [← hS'_eq]
      exact hS'_bounds h1 h2 h3 h4)
  obtain ⟨CW, αW, βW, hCW, hαW, hβW, hαβW, hbW⟩ := branch_window ℓ d hd
    (a := 1 / 4) (b := 3 / 4) (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num))
    blW (KfunClear_blW' ℓ d hd) blW_jInvariantFun (K := blBox) isCompact_blBox
    (fun τ hτ => by rw [← hW_eq]; exact hW_bounds hτ)
  obtain ⟨CV, αV, βV, hCV, hαV, hβV, hαβV, hbV⟩ := branch_window ℓ d hd
    (a := 7 / 5) (b := 16 / 5) (by norm_num) (by norm_num) (by norm_num) (Or.inr (by norm_num))
    blV (KfunClear_blV' ℓ d hd) blV_jInvariantFun
    (K := {τ : ℍ | blBox τ ∧ |blMargin τ| ≤ 1 / 100}) hKarc
    (fun τ hτ => by rw [← hV_eq]; exact hV_bounds hτ.1 hτ.2)
  -- the exceptional compact set
  set E : Set (ℍ × ℝ) := {p : ℍ × ℝ |
    p.1 ∈ closure blLowSet ∧ δc ≤ p.2 ∧ p.2 ≤ 3 ∧ (1 / 8 : ℝ) ≤ |p.2 - p.1.im| ∧
    (αs ≤ gS p.1 ∨ p.1.re ≤ 3 / 4 ∨ βs ≤ |p.2 - hS p.1|) ∧
    (-3 / 4 ≤ p.1.re ∨ αs' ≤ gS' p.1 ∨ βs' ≤ |p.2 - hS' p.1|) ∧
    (αW ≤ gW p.1 ∨ βW ≤ |p.2 - hW p.1|) ∧
    (αV ≤ gV p.1 ∨ 1 / 100 ≤ |blMargin p.1| ∨ βV ≤ |p.2 - hV p.1|)} with hEdef
  have hEclosed : IsClosed E := by
    have hc1 : IsClosed {p : ℍ × ℝ | p.1 ∈ closure blLowSet} :=
      isClosed_closure.preimage continuous_fst
    have hc2 : IsClosed {p : ℍ × ℝ | δc ≤ p.2} := isClosed_le continuous_const continuous_snd
    have hc3 : IsClosed {p : ℍ × ℝ | p.2 ≤ 3} := isClosed_le continuous_snd continuous_const
    have hc4 : IsClosed {p : ℍ × ℝ | (1 / 8 : ℝ) ≤ |p.2 - p.1.im|} :=
      isClosed_le continuous_const (continuous_abs.comp (continuous_snd.sub
        (UpperHalfPlane.continuous_im.comp continuous_fst)))
    have hc5 : IsClosed ({p : ℍ × ℝ | αs ≤ gS p.1} ∪
        ({p : ℍ × ℝ | p.1.re ≤ 3 / 4} ∪ {p : ℍ × ℝ | βs ≤ |p.2 - hS p.1|})) :=
      (isClosed_le continuous_const (continuous_gS.comp continuous_fst)).union
        ((isClosed_le (UpperHalfPlane.continuous_re.comp continuous_fst) continuous_const).union
          (isClosed_le continuous_const (continuous_abs.comp (continuous_snd.sub
            (continuous_hS.comp continuous_fst)))))
    have hc6 : IsClosed ({p : ℍ × ℝ | -3 / 4 ≤ p.1.re} ∪
        ({p : ℍ × ℝ | αs' ≤ gS' p.1} ∪ {p : ℍ × ℝ | βs' ≤ |p.2 - hS' p.1|})) :=
      (isClosed_le continuous_const (UpperHalfPlane.continuous_re.comp continuous_fst)).union
        ((isClosed_le continuous_const (continuous_gS'.comp continuous_fst)).union
          (isClosed_le continuous_const (continuous_abs.comp (continuous_snd.sub
            (continuous_hS'.comp continuous_fst)))))
    have hc7 : IsClosed ({p : ℍ × ℝ | αW ≤ gW p.1} ∪ {p : ℍ × ℝ | βW ≤ |p.2 - hW p.1|}) :=
      (isClosed_le continuous_const (continuous_gW.comp continuous_fst)).union
        (isClosed_le continuous_const (continuous_abs.comp (continuous_snd.sub
          (continuous_hW.comp continuous_fst))))
    have hc8 : IsClosed ({p : ℍ × ℝ | αV ≤ gV p.1} ∪
        ({p : ℍ × ℝ | 1 / 100 ≤ |blMargin p.1|} ∪ {p : ℍ × ℝ | βV ≤ |p.2 - hV p.1|})) :=
      (isClosed_le continuous_const (continuous_gV.comp continuous_fst)).union
        ((isClosed_le continuous_const (continuous_abs.comp
          (continuous_blMargin.comp continuous_fst))).union
          (isClosed_le continuous_const (continuous_abs.comp (continuous_snd.sub
            (continuous_hV.comp continuous_fst)))))
    have heq : E = {p : ℍ × ℝ | p.1 ∈ closure blLowSet} ∩ {p : ℍ × ℝ | δc ≤ p.2} ∩
        {p : ℍ × ℝ | p.2 ≤ 3} ∩ {p : ℍ × ℝ | (1 / 8 : ℝ) ≤ |p.2 - p.1.im|} ∩
        ({p : ℍ × ℝ | αs ≤ gS p.1} ∪
          ({p : ℍ × ℝ | p.1.re ≤ 3 / 4} ∪ {p : ℍ × ℝ | βs ≤ |p.2 - hS p.1|})) ∩
        ({p : ℍ × ℝ | -3 / 4 ≤ p.1.re} ∪
          ({p : ℍ × ℝ | αs' ≤ gS' p.1} ∪ {p : ℍ × ℝ | βs' ≤ |p.2 - hS' p.1|})) ∩
        ({p : ℍ × ℝ | αW ≤ gW p.1} ∪ {p : ℍ × ℝ | βW ≤ |p.2 - hW p.1|}) ∩
        ({p : ℍ × ℝ | αV ≤ gV p.1} ∪
          ({p : ℍ × ℝ | 1 / 100 ≤ |blMargin p.1|} ∪ {p : ℍ × ℝ | βV ≤ |p.2 - hV p.1|})) := by
      rw [hEdef]
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union]
      tauto
    rw [heq]
    exact (((((((hc1.inter hc2).inter hc3).inter hc4).inter hc5).inter hc6).inter hc7).inter hc8)
  have hEsub : E ⊆ closure blLowSet ×ˢ Set.Icc δc 3 := by
    intro p hp
    rw [hEdef] at hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  have hEcomp : IsCompact E :=
    (isCompact_closure_blLowSet.prod isCompact_Icc).of_isClosed_subset hEclosed hEsub
  -- the `j`-difference is bounded below on `E`
  set G : ℍ × ℝ → ℝ := fun p =>
    ‖jInvariantFun p.1 - jInvariantFun (axPtE δc hδc p.2)‖ with hGdef
  have hGcont : Continuous G := by
    rw [hGdef]
    exact ((Work.Asymptotics.KaxisMid.continuous_jInvariantFun.comp continuous_fst).sub
      (Work.Asymptotics.KaxisMid.continuous_jInvariantFun.comp
        ((axPtE_continuous δc hδc).comp continuous_snd))).norm
  have hneq : ∀ p ∈ E, jInvariantFun p.1 ≠ jInvariantFun (axPtE δc hδc p.2) := by
    intro p hp
    rw [hEdef] at hp
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp
    rw [axPtE_eq_imagAxis δc hδc h2]
    exact offcoin_closure h1 (lt_of_lt_of_le hδc h2) h4 hαs hβs hαs' hβs' hαW hβW hαV hβV
      h5 h6 h7 h8
  have hmin : ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ p ∈ E, c₀ ≤ ‖jInvariantFun p.1 - jInvariantFun (axPtE δc hδc p.2)‖ := by
    rcases E.eq_empty_or_nonempty with hE0 | hEne
    · refine ⟨1, one_pos, fun p hp => ?_⟩
      rw [hE0] at hp
      exact absurd hp (Set.notMem_empty p)
    · obtain ⟨p₀, hp₀, hmin₀⟩ := hEcomp.exists_isMinOn hEne hGcont.continuousOn
      refine ⟨G p₀, ?_, fun p hp => hmin₀ hp⟩
      rw [hGdef]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (hneq p₀ hp₀))
  obtain ⟨c₀, hc₀pos, hc₀⟩ := hmin
  -- uniform bound for `AfunFun` on the boxes containing `closure blLowSet` and the contour arc
  obtain ⟨A, hApos, hbA⟩ := Work.HFN.HalfFunnel.exists_bound_AfunFun_prod ℓ d
    (Work.HFN.HalfFunnel.isCompact_box_im 4 (min δc (1 / 4)))
    (Work.HFN.HalfFunnel.isCompact_box_im 4 (min δc (1 / 4)))
    (fun z hz => lt_of_lt_of_le (lt_min hδc (by norm_num)) hz.2)
    (fun z hz => lt_of_lt_of_le (lt_min hδc (by norm_num)) hz.2)
  set C : ℝ := max (max (max (max cc Cs) (max Cs' CW)) CV) (A / c₀) with hCdef
  have hCcc : cc ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left cc Cs) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hCCs : Cs ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right cc Cs) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hCCs' : Cs' ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left Cs' CW) (le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hCCW : CW ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right Cs' CW) (le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hCCV : CV ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right _ CV) (le_max_left _ _)
  have hCA : A / c₀ ≤ C := by
    rw [hCdef]
    exact le_max_right _ _
  refine ⟨C, le_trans hcc.le hCcc, ?_⟩
  intro τ t hτ ht ht3 hsep
  have ht3' : t ≤ 3 := ht3
  have hτcl : τ ∈ closure blLowSet := subset_closure hτ
  have hbox : blBox τ := mem_blBox hτ
  have hrelo := blLowSet_re_abs_bounds hτ
  have himlo := blLowSet_im_bounds hτ
  by_cases htδc : t ≤ δc
  · have hcf := hcusp τ t hτ ht htδc
    rw [Real.rpow_zero, mul_one] at hcf
    exact le_trans hcf hCcc
  · push_neg at htδc
    have hδct : δc ≤ t := htδc.le
    by_cases hin : (τ, t) ∈ E
    · have hmem : (τ, t) ∈ E := hin
      have hcoord : jInvariantFun τ ≠ jInvariantFun (axPtE δc hδc t) := hneq (τ, t) hin
      rw [Work.Kernels.Kaxis, dif_pos ht, ← axPtE_eq_imagAxis δc hδc hδct]
      have hmul := Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd τ (axPtE δc hδc t) hcoord
      have hnorm : ‖Kfun ℓ d τ (axPtE δc hδc t)‖
          * ‖jInvariantFun τ - jInvariantFun (axPtE δc hδc t)‖
          = ‖AfunFun ℓ d τ (axPtE δc hδc t)‖ := by
        rw [← norm_mul, ← hmul]
      have hτbox : (τ : ℂ) ∈ {x : ℂ | ‖x‖ ≤ 4 ∧ min δc (1 / 4) ≤ x.im} := by
        obtain ⟨hn1, hn2⟩ := normSq_bounds_of_blBox hbox
        refine ⟨?_, ?_⟩
        · have h2 : ‖(τ : ℂ)‖ ≤ 2 := by nlinarith [norm_nonneg (τ : ℂ), hn2]
          linarith
        · rw [UpperHalfPlane.coe_im]
          exact le_trans (min_le_right δc (1 / 4))
            (le_trans (by norm_num : (1 : ℝ) / 4 ≤ 2 / 5) himlo.1)
      have hwbox : (axPtE δc hδc t : ℂ) ∈ {x : ℂ | ‖x‖ ≤ 4 ∧ min δc (1 / 4) ≤ x.im} := by
        rw [axPtE_coe]
        constructor
        · have hmax : max t δc ≤ 3 := max_le ht3' (le_trans hδct ht3')
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (lt_of_lt_of_le hδc (le_max_right t δc))]
          linarith
        · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
            mul_one, mul_zero, add_zero]
          exact le_trans (min_le_left δc (1 / 4)) (le_max_right t δc)
      have hAb : ‖AfunFun ℓ d τ (axPtE δc hδc t)‖ ≤ A := hbA τ (axPtE δc hδc t) hτbox hwbox
      have hJb : c₀ ≤ ‖jInvariantFun τ - jInvariantFun (axPtE δc hδc t)‖ := hc₀ (τ, t) hmem
      have hle : ‖Kfun ℓ d τ (axPtE δc hδc t)‖ ≤ A / c₀ := by
        rw [le_div_iff₀ hc₀pos]
        calc ‖Kfun ℓ d τ (axPtE δc hδc t)‖ * c₀
            ≤ ‖Kfun ℓ d τ (axPtE δc hδc t)‖
              * ‖jInvariantFun τ - jInvariantFun (axPtE δc hδc t)‖ :=
              mul_le_mul_of_nonneg_left hJb (norm_nonneg _)
          _ = ‖AfunFun ℓ d τ (axPtE δc hδc t)‖ := hnorm
          _ ≤ A := hAb
      exact le_trans hle hCA
    · rw [hEdef] at hin
      by_cases hW1 : gS τ ≤ αs ∧ (3 : ℝ) / 4 ≤ τ.re ∧ |t - hS τ| ≤ βs
      · exact le_trans (hbS τ ⟨hW1.2.1, hrelo.2.le, himlo.1, himlo.2⟩
          (by rw [← gS_eq]; exact hW1.1) t ht ht3' (by rw [← hS_eq]; exact hW1.2.2)) hCCs
      · by_cases hW2 : gS' τ ≤ αs' ∧ τ.re ≤ -(3 : ℝ) / 4 ∧ |t - hS' τ| ≤ βs'
        · exact le_trans (hbS' τ ⟨hW2.2.1, hrelo.2.le, himlo.1, himlo.2⟩
            (by rw [← gS'_eq]; exact hW2.1) t ht ht3' (by rw [← hS'_eq]; exact hW2.2.2)) hCCs'
        · by_cases hW3 : gW τ ≤ αW ∧ |t - hW τ| ≤ βW
          · exact le_trans (hbW τ hbox (by rw [← gW_eq]; exact hW3.1) t ht ht3'
              (by rw [← hW_eq]; exact hW3.2)) hCCW
          · by_cases hW4 : gV τ ≤ αV ∧ |blMargin τ| ≤ 1 / 100 ∧ |t - hV τ| ≤ βV
            · exact le_trans (hbV τ ⟨hbox, hW4.2.1⟩ (by rw [← gV_eq]; exact hW4.1) t ht ht3'
                (by rw [← hV_eq]; exact hW4.2.2)) hCCV
            · exfalso
              have hD1 : αs ≤ gS τ ∨ τ.re ≤ 3 / 4 ∨ βs ≤ |t - hS τ| := by
                by_contra hc
                push_neg at hc
                exact hW1 ⟨hc.1.le, hc.2.1.le, hc.2.2.le⟩
              have hD2 : -3 / 4 ≤ τ.re ∨ αs' ≤ gS' τ ∨ βs' ≤ |t - hS' τ| := by
                by_contra hc
                push_neg at hc
                exact hW2 ⟨hc.2.1.le, hc.1.le, hc.2.2.le⟩
              have hD3 : αW ≤ gW τ ∨ βW ≤ |t - hW τ| := by
                by_contra hc
                push_neg at hc
                exact hW3 ⟨hc.1.le, hc.2.le⟩
              have hD4 : αV ≤ gV τ ∨ 1 / 100 ≤ |blMargin τ| ∨ βV ≤ |t - hV τ| := by
                by_contra hc
                push_neg at hc
                exact hW4 ⟨hc.1.le, hc.2.1.le, hc.2.2.le⟩
              exact hin ⟨hτcl, hδct, ht3', hsep, hD1, hD2, hD3, hD4⟩

end Work.HFN.BlLow
