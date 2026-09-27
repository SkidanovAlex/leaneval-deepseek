import Mathlib
import Submission.Work.Drive.Neutral.StripDiskAux
import Submission.Work.Drive.Neutral.StripDiskValues
import Submission.Work.Drive.Neutral.stripTauChart
import Submission.Work.Drive.Neutral.exists_contMDiff_planeCross

/-!
# Plumbing for the strip disk presentation

The two linear bridges between `ℂ` and `EuclideanSpace ℝ (Fin 2)`, the radial cutoffs used to keep
the descended data globally positive / nonvanishing, and the elementary identities about `muX`,
`confProjVecOf` and the complex argument.
-/

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. The two linear bridges -/

/-- The linear isometry `ℂ → EuclideanSpace ℝ (Fin 2)`. -/
def sdEuc2 (z : ℂ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then z.re else z.im)

/-- The inverse of `sdEuc2`. -/
def sdCplxOf (a : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨a 0, a 1⟩

lemma sdCplxOf_eq (a : EuclideanSpace ℝ (Fin 2)) :
    sdCplxOf a = ((a 0 : ℝ) : ℂ) + (((a 1 : ℝ) : ℂ)) * Complex.I := by
  apply Complex.ext <;> simp [sdCplxOf, Complex.mul_I_re, Complex.mul_I_im]

lemma sdCplxOf_euc2 (z : ℂ) : sdCplxOf (sdEuc2 z) = z := by
  apply Complex.ext <;> simp [sdCplxOf, sdEuc2]

theorem sdContDiff_euc2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sdEuc2 := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => (fun i : Fin 2 => if i = 0 then z.re else z.im)) := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Complex.reCLM)
      exact Complex.reCLM.contDiff
    · change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Complex.imCLM)
      exact Complex.imCLM.contDiff
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm :
        (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2))) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm).toContinuousLinearEquiv.contDiff
  have h3 := h2.comp h1
  convert h3 using 2
  funext i
  simp [sdEuc2, PiLp.continuousLinearEquiv_symm_apply]

/-- The coordinate projection `EuclideanSpace ℝ (Fin 2) → ℝ`. -/
def sdProj (i : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] (Fin 2 → ℝ))

lemma sdProj_apply (i : Fin 2) (a : EuclideanSpace ℝ (Fin 2)) : sdProj i a = a i := by
  rw [sdProj]
  simp [PiLp.continuousLinearEquiv_apply]

theorem sdContDiff_cplxOf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sdCplxOf := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun a : EuclideanSpace ℝ (Fin 2) =>
        ((a 0 : ℝ) : ℂ) + ((((a 1 : ℝ) : ℂ)) * Complex.I)) := by
    have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun a : EuclideanSpace ℝ (Fin 2) => ((a 0 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (sdProj 0).contDiff
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun a : EuclideanSpace ℝ (Fin 2) => (((a 1 : ℝ) : ℂ) * Complex.I)) :=
      (Complex.ofRealCLM.contDiff.comp (sdProj 1).contDiff).mul contDiff_const
    exact h0.add h1
  rw [show sdCplxOf = fun a : EuclideanSpace ℝ (Fin 2) =>
      ((a 0 : ℝ) : ℂ) + ((((a 1 : ℝ) : ℂ)) * Complex.I) from funext sdCplxOf_eq]
  exact h

/-- `ContDiff` of the norm-square. -/
theorem sdContDiff_normSq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.normSq z) := by
  have hre : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  rw [show (fun z : ℂ => Complex.normSq z) = fun z : ℂ => z.re * z.re + z.im * z.im from
    funext (fun z => by rw [Complex.normSq_apply])]
  exact (hre.mul hre).add (him.mul him)

/-! ## 2. The radial cutoff in the disk variable -/

/-- A smooth radial cutoff: `1` for `‖x‖ ≤ 3` and `0` for `‖x‖ ≥ 4`. -/
def sdChi (x : ℂ) : ℝ := Real.smoothTransition ((16 - Complex.normSq x) / 7)

lemma sdContDiff_chi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) sdChi :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.sub sdContDiff_normSq).div_const 7)

lemma sdChi_nonneg (x : ℂ) : 0 ≤ sdChi x := Real.smoothTransition.nonneg _
lemma sdChi_le_one (x : ℂ) : sdChi x ≤ 1 := Real.smoothTransition.le_one _

lemma sdChi_eq_one {x : ℂ} (h : ‖x‖ ≤ 3) : sdChi x = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have h2 : Complex.normSq x ≤ 9 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg x]
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 7)]
  linarith

lemma sdChi_eq_zero {x : ℂ} (h : 4 ≤ ‖x‖) : sdChi x = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  have h2 : (16 : ℝ) ≤ Complex.normSq x := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg x]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

lemma sdChi_neg (x : ℂ) : sdChi (-x) = sdChi x := by simp [sdChi, Complex.normSq_neg]

lemma sdChi_ne_zero_norm {x : ℂ} (h : sdChi x ≠ 0) : ‖x‖ < 4 := by
  by_contra hcon
  exact h (sdChi_eq_zero (not_lt.mp hcon))

lemma norm_sdChi_smul_le (x : ℂ) : ‖sdChi x • x‖ ≤ 4 := by
  rcases eq_or_ne (sdChi x) 0 with h | h
  · rw [h, zero_smul, norm_zero]; norm_num
  · rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sdChi_nonneg x)]
    have h4 : ‖x‖ ≤ 4 := le_of_lt (sdChi_ne_zero_norm h)
    calc sdChi x * ‖x‖ ≤ 1 * 4 :=
          mul_le_mul (sdChi_le_one x) h4 (norm_nonneg x) (by norm_num)
      _ = 4 := by norm_num

/-! ## 3. The opening cutoff in the `τ` variable -/

/-- A smooth cutoff of the `τ` variable: `θ τ = τ` for `τ ≥ 0`, `θ τ = 0` for `τ ≤ -c`, and
`θ τ ≥ -c` always. -/
def sdTheta (c τ : ℝ) : ℝ := Real.smoothTransition ((τ + c) / c) * τ

lemma sdContDiff_theta (c : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sdTheta c) := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun τ : ℝ => Real.smoothTransition ((τ + c) / c)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const c)
  exact h.mul contDiff_id

lemma sdTheta_eq_self {c τ : ℝ} (hc : 0 < c) (hτ : 0 ≤ τ) : sdTheta c τ = τ := by
  rw [sdTheta, Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hc]; linarith), one_mul]

lemma sdTheta_ge {c : ℝ} (hc : 0 < c) (τ : ℝ) : -c ≤ sdTheta c τ := by
  have h0 : (0:ℝ) ≤ Real.smoothTransition ((τ + c) / c) := Real.smoothTransition.nonneg _
  have h1 : Real.smoothTransition ((τ + c) / c) ≤ 1 := Real.smoothTransition.le_one _
  by_cases hτ : 0 ≤ τ
  · have h := mul_nonneg h0 hτ
    rw [sdTheta]
    linarith
  · have hτ' : τ < 0 := not_le.mp hτ
    by_cases hc' : -c ≤ τ
    · have h := mul_le_mul_of_nonpos_right h1 hτ'.le
      rw [sdTheta, mul_comm]
      linarith
    · have hc'' : τ < -c := not_le.mp hc'
      have hz : Real.smoothTransition ((τ + c) / c) = 0 := by
        refine Real.smoothTransition.zero_of_nonpos ?_
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
      rw [sdTheta, hz, zero_mul]
      linarith

/-! ## 4. The blend `muX` -/

lemma sdContDiff_muX (k : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (muX k) :=
  Real.smoothTransition.contDiff.comp
    ((sdContDiff_normSq.sub contDiff_const).mul
      (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℂ => (4:ℝ) * (k:ℝ))))

lemma sdMuX_neg (k : ℕ) (x : ℂ) : muX k (-x) = muX k x := by
  simp [muX, Complex.normSq_neg]

lemma sdMuX_nonneg (k : ℕ) (x : ℂ) : 0 ≤ muX k x := Real.smoothTransition.nonneg _
lemma sdMuX_le_one (k : ℕ) (x : ℂ) : muX k x ≤ 1 := Real.smoothTransition.le_one _

lemma sdMuX_eq_zero {k : ℕ} {x : ℂ} (h : Complex.normSq x ≤ 1 / 4) : muX k x = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

lemma sdMuX_eq_one {k : ℕ} (hk₁ : 1 ≤ k) {x : ℂ}
    (h : 1 / 4 + 1 / (4 * k) ≤ Complex.normSq x) : muX k x = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have hk : (0:ℝ) < 4 * (k:ℝ) := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk₁
    linarith
  have h1 : 1 / (4 * (k:ℝ)) ≤ Complex.normSq x - 1 / 4 := by linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hk.le
  have h3 : (1 / (4 * (k:ℝ))) * (4 * (k:ℝ)) = 1 := by
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hk)]
  linarith [h3 ▸ h2]

lemma sdMuX_eq_one_of_norm_one {k : ℕ} (hk : 1 ≤ k) {x : ℂ} (h : ‖x‖ = 1) : muX k x = 1 := by
  refine sdMuX_eq_one hk ?_
  have hk4 : (4:ℝ) ≤ 4 * (k:ℝ) := by
    have : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    linarith
  have hle : 1 / (4 * (k:ℝ)) ≤ 1 / 4 :=
    one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 4) hk4
  have hns : Complex.normSq x = 1 := by rw [Complex.normSq_eq_norm_sq, h]; norm_num
  linarith

/-! ## 5. `sClamp` and the argument identity -/

lemma sdSClamp_ne_zero {s : ℝ} (hs : s ≠ 0) : sClamp s ≠ 0 := by
  intro h
  apply hs
  have hsq : (0:ℝ) < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hfac : sClamp s
      = s * (sKappa s + (Real.pi - 1) * (1 - sKappa s) / Real.sqrt (1 + s ^ 2)) := by
    rw [sClamp, sSig, div_eq_mul_inv]
    field_simp
  rw [hfac] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · have hk1 : sKappa s = 0 := by
      have h3 : 0 ≤ (Real.pi - 1) * (1 - sKappa s) / Real.sqrt (1 + s ^ 2) :=
        div_nonneg (mul_nonneg (by linarith [Real.pi_gt_three]) (by linarith [sKappa_le_one s]))
          hsq.le
      linarith [sKappa_nonneg s]
    have hk2 : 1 - sKappa s = 0 := by
      have h4 : (Real.pi - 1) * (1 - sKappa s) / Real.sqrt (1 + s ^ 2) = 0 := by linarith
      have h5 : (Real.pi - 1) * (1 - sKappa s) = 0 := by
        rcases div_eq_zero_iff.mp h4 with h6 | h6
        · exact h6
        · exact absurd h6 (ne_of_gt hsq)
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd h6 (by linarith [Real.pi_gt_three])
      · exact h6
    linarith [sKappa_le_one s]

/-- `exp (arg z · I) = z/‖z‖` for `z ≠ 0`. -/
theorem sdExp_arg (z : ℂ) (hz : z ≠ 0) :
    Complex.exp (((Complex.arg z : ℂ)) * Complex.I) = z / ((‖z‖ : ℝ) : ℂ) := by
  rw [eq_div_iff (by rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hz), mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I z

/-! ## 6. `confProjVecOf` is odd in its first argument -/

lemma sdC₁_neg (v : Eucl 3) : c₁ (-v) = -c₁ v := by
  simp only [c₁, PiLp.neg_apply]
  push_cast
  ring

lemma sdC₂_neg (v : Eucl 3) : c₂ (-v) = -c₂ v := by
  simp only [c₂, PiLp.neg_apply]
  push_cast
  ring

lemma sdConfProjVecOf_neg (u d : ℂ) : confProjVecOf (-u) d = -confProjVecOf u d := by
  rw [← ofComplex_c₁_c₂ (confProjVecOf (-u) d), ← ofComplex_c₁_c₂ (-confProjVecOf u d)]
  congr 1
  · rw [c₁_confProjVecOf, sdC₁_neg, c₁_confProjVecOf]; ring
  · rw [c₂_confProjVecOf, sdC₂_neg, c₂_confProjVecOf, star_neg]; ring

end

end Work.Drive.Neutral
