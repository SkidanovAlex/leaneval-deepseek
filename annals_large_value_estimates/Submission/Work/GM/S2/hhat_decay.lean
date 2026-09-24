import Mathlib
import Submission.Work.GM.S2.hhat_decay_defs
import Submission.Work.GM.S3.hhat_decay
import Submission.Work.GM.S2.ibp_phase_iterated
import Submission.Work.GM.S2.hhat_amp_deriv_bound
import Submission.Work.GM.S2.hhat_sum_tail

/-!
# GM Lemma 4.3 for `ĥ_t` (the `S₂` area): decay in `ξ`, decay in `t`, and the `m`-tail

`hhat t ξ = 𝓕 (h_t) ξ` with `h_t(u) = w(u)² u^{it}` (GM (4.4)).  This file proves

* **(1)** `‖ĥ_t(ξ)‖ ≤ C_j (1+|t|)^j / |ξ|^j` for `ξ ≠ 0` — GM Lemma 4.3(1), imported from
  the `S₃` area (`Work.GM.S3.hhat_decay`, itself the decay of a smooth compactly supported
  Fourier transform);
* **(2)** `‖ĥ_t(ξ)‖ ≤ C_j (1+|ξ|)^j / |t|^j` for `t ≠ 0` — GM Lemma 4.3(2): integrate by
  parts `j` times against the phase `u^{it}` (`Work.GM.S2.ibp_phase_iterated`), which costs a
  factor `∏_{k=1}^{j} (k + it)^{-1}` (of modulus `≤ |t|^{-j}`) and replaces the amplitude
  `g_ξ(u) = w(u)² e^{-2πiξu}` by its `j`-th derivative (bounded by `D_j (1+|ξ|)^j`);
* **(3)** `∑_{|m| > X} ‖ĥ_t(mN)‖ ≤ C_j (1+|t|)^j / (N^j X^{j-1})` for `j ≥ 2`, `X > 0`:
  (1) termwise plus the elementary tail bound `∑_{|m|>X} |m|^{-j} ≪ X^{1-j}`
  (`Work.GM.S2.hhat_sum_tail`).  This is the truncation estimate used in GM §§4–6 to discard
  the terms with `|m| ≫ (1+|t|)/N`.
-/

open MeasureTheory
open scoped Real BigOperators
set_option autoImplicit false

namespace Work.GM.S2

/-! ## Elementary calculus of the amplitude and the phase -/

/-- `h_t = (w²) · u^{it}` written with the phase `hhatPhase`. -/
theorem hfun_eq_amp_phase (t u : ℝ) :
    Submission.GM.hfun t u = ((Submission.LargeValues.bumpW u ^ 2 : ℝ) : ℂ) * hhatPhase t u := by
  rw [Submission.GM.hfun, hhatPhase]
  by_cases hu : u ≤ 0
  · have h1 : u ∉ Set.Icc (1 : ℝ) 2 := by
      simp only [Set.mem_Icc, not_and, not_le]; intro _; linarith
    rw [Submission.LargeValues.bumpW_eq_zero_of_notMem h1]; simp
  · push Not at hu
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hu), Complex.ofReal_log hu.le]
    push_cast
    ring_nf

/-- The kernel `e^{-2πiξu}` in the form produced by `Real.fourier_real_eq_integral_exp_smul`. -/
theorem hhatKernel_eq (ξ u : ℝ) :
    Complex.exp ((↑(-2 * Real.pi * u * ξ) : ℂ) * Complex.I) = hhatKernel ξ u := by
  rw [hhatKernel]
  congr 1
  push_cast
  ring

/-- `‖u^{it}‖ = 1` for every real `u`. -/
theorem norm_hhatPhase (t u : ℝ) : ‖hhatPhase t u‖ = 1 := by
  rw [hhatPhase, Complex.norm_exp]
  have : (Complex.I * (t : ℂ) * (Real.log u : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [this, Real.exp_zero]

/-- The amplitude vanishes off `[1,2]`. -/
theorem hhatAmp_zero_of_notMem (ξ u : ℝ) (hu : u ∉ Set.Icc (1 : ℝ) 2) : hhatAmp ξ u = 0 := by
  rw [hhatAmp, Submission.LargeValues.bumpW_eq_zero_of_notMem hu]
  simp

/-- All iterated derivatives of the amplitude vanish off `[1,2]`. -/
theorem iteratedDeriv_hhatAmp_eq_zero_of_notMem (ξ : ℝ) (k : ℕ) {u : ℝ}
    (hu : u ∉ Set.Icc (1 : ℝ) 2) : iteratedDeriv k (hhatAmp ξ) u = 0 := by
  have hEqOn : Set.EqOn (hhatAmp ξ) (fun _ : ℝ => (0 : ℂ)) (Set.Icc (1 : ℝ) 2)ᶜ :=
    fun y hy => hhatAmp_zero_of_notMem ξ y (by simpa using hy)
  have h := Set.EqOn.iteratedDeriv_of_isOpen hEqOn isClosed_Icc.isOpen_compl k
  simpa using h (by simpa using hu)

/-- The amplitude is `C^∞`. -/
theorem contDiff_hhatAmp (ξ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hhatAmp ξ) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : ℝ => ((Submission.LargeValues.bumpW u ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Submission.LargeValues.bumpW_contDiff.pow 2)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hhatKernel ξ) := by
    rw [show hhatKernel ξ = fun u : ℝ => Complex.exp ((↑(-2 * Real.pi * u * ξ) : ℂ) * Complex.I)
      from funext (fun u => (hhatKernel_eq ξ u).symm)]
    apply Complex.contDiff_exp.comp
    apply ContDiff.mul
    · exact (Complex.ofRealCLM.contDiff.comp (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => -2 * Real.pi * u * ξ)))
    · exact contDiff_const
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun u : ℝ => ((Submission.LargeValues.bumpW u ^ 2 : ℝ) : ℂ) * hhatKernel ξ u)
  exact h1.mul h2

/-! ## `ĥ_t(ξ)` as an integral of amplitude times phase -/

/-- `ĥ_t(ξ) = ∫_{1/2}^{5/2} g_ξ(u) u^{it} du`: the support of `h_t` is `[1,2] ⊂ [1/2,5/2]`. -/
theorem hhat_eq_integral_amp (t ξ : ℝ) :
    Submission.GM.hhat t ξ = ∫ u in (1 / 2)..(5 / 2), hhatAmp ξ u * hhatPhase t u := by
  rw [Submission.GM.hhat, Real.fourier_real_eq_integral_exp_smul]
  have hpt : ∀ v : ℝ,
      Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) • Submission.GM.hfun t v
        = hhatAmp ξ v * hhatPhase t v := by
    intro v
    rw [smul_eq_mul, hhatKernel_eq ξ v, hfun_eq_amp_phase t v, hhatAmp]
    ring
  rw [show (∫ v : ℝ, Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) •
        Submission.GM.hfun t v) = ∫ v : ℝ, hhatAmp ξ v * hhatPhase t v from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hvanish : ∀ v : ℝ, v ∉ Set.Icc (1 / 2 : ℝ) (5 / 2) → hhatAmp ξ v * hhatPhase t v = 0 := by
    intro v hv
    have hmem : v ∉ Set.Icc (1 : ℝ) 2 := by
      intro h
      exact hv (Set.Icc_subset_Icc (by norm_num) (by norm_num) h)
    rw [hhatAmp_zero_of_notMem ξ v hmem]; simp
  rw [show (∫ v : ℝ, hhatAmp ξ v * hhatPhase t v)
      = ∫ v in Set.Icc (1 / 2 : ℝ) (5 / 2), hhatAmp ξ v * hhatPhase t v from
    (setIntegral_eq_integral_of_forall_compl_eq_zero hvanish).symm]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 2)]

/-! ## GM Lemma 4.3(2): decay in `t` -/

/-- `|t| ≤ ‖(k+1) + it‖`, so the product `∏_{k<j} ((k+1)+it)` has modulus at least `|t|^j`. -/
theorem abs_le_norm_factor (t : ℝ) (k : ℕ) :
    (|t| : ℝ) ≤ ‖(((k : ℂ) + 1) + Complex.I * (t : ℂ))‖ := by
  have him : ((((k : ℂ) + 1) + Complex.I * (t : ℂ))).im = t := by simp
  calc (|t| : ℝ) = |((((k : ℂ) + 1) + Complex.I * (t : ℂ))).im| := by rw [him]
    _ ≤ ‖(((k : ℂ) + 1) + Complex.I * (t : ℂ))‖ := Complex.abs_im_le_norm _

theorem pow_abs_le_norm_prod (t : ℝ) (j : ℕ) :
    (|t| : ℝ) ^ j ≤ ‖∏ k ∈ Finset.range j, (((k : ℂ) + 1) + Complex.I * (t : ℂ))‖ := by
  rw [norm_prod]
  have h := Finset.prod_le_prod₀ (s := Finset.range j) (fun k _ => abs_nonneg t)
    (fun k _ => abs_le_norm_factor t k)
  rwa [Finset.prod_const, Finset.card_range] at h

/-- `j` integrations by parts against the phase, plus the bounds of the amplitude and of
`∏_{k<j} ((k+1)+it)` and the trivial bound for the remaining integral. -/
theorem hhat_decay_in_t_of (j : ℕ)
    (hAmp : ∀ k : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ (ξ u : ℝ),
      ‖iteratedDeriv k (hhatAmp ξ) u‖ ≤ D * (1 + |ξ|) ^ k)
    (hibp : ∀ (g : ℝ → ℂ) (t : ℝ) (j : ℕ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
      (∀ k ≤ j, iteratedDeriv k g (1 / 2) = 0) →
      (∀ k ≤ j, iteratedDeriv k g (5 / 2) = 0) →
      (∫ u in (1 / 2)..(5 / 2), g u * hhatPhase t u)
        = ((-1 : ℂ) ^ j / ∏ k ∈ Finset.range j, (((k : ℂ) + 1) + Complex.I * (t : ℂ))) *
          ∫ u in (1 / 2)..(5 / 2), iteratedDeriv j g u *
            ((u : ℂ) ^ j * hhatPhase t u)) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ξ : ℝ, t ≠ 0 →
      ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |ξ|) ^ j / |t| ^ j := by
  obtain ⟨D, _hD, hDb⟩ := hAmp j
  refine ⟨2 * (5 / 2) ^ j * D + 1, by positivity, ?_⟩
  intro t ξ ht
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hleft : ∀ k ≤ j, iteratedDeriv k (hhatAmp ξ) (1 / 2) = 0 :=
    fun k _ => iteratedDeriv_hhatAmp_eq_zero_of_notMem ξ k (by norm_num)
  have hright : ∀ k ≤ j, iteratedDeriv k (hhatAmp ξ) (5 / 2) = 0 :=
    fun k _ => iteratedDeriv_hhatAmp_eq_zero_of_notMem ξ k (by norm_num)
  rw [hhat_eq_integral_amp t ξ, hibp (hhatAmp ξ) t j (contDiff_hhatAmp ξ) hleft hright]
  set P : ℂ := ∏ k ∈ Finset.range j, (((k : ℂ) + 1) + Complex.I * (t : ℂ)) with hP
  have hPbound : (|t| : ℝ) ^ j ≤ ‖P‖ := by rw [hP]; exact pow_abs_le_norm_prod t j
  have hA : ‖((-1 : ℂ) ^ j / P)‖ ≤ 1 / |t| ^ j := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos htpos j) hPbound
  have hB : ‖∫ u in (1 / 2)..(5 / 2), iteratedDeriv j (hhatAmp ξ) u *
      ((u : ℂ) ^ j * hhatPhase t u)‖ ≤ 2 * (D * (1 + |ξ|) ^ j * (5 / 2) ^ j) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 / 2 : ℝ)) (b := (5 / 2 : ℝ))
      (f := fun u : ℝ => iteratedDeriv j (hhatAmp ξ) u * ((u : ℂ) ^ j * hhatPhase t u))
      (C := D * (1 + |ξ|) ^ j * (5 / 2) ^ j) (fun u hu => ?_)
    · have hb : |(5 / 2 : ℝ) - 1 / 2| = 2 := by norm_num
      rwa [hb, mul_comm] at h
    have hmax : max (1 / 2 : ℝ) (5 / 2) = 5 / 2 := by norm_num [max_def]
    have hmin : (0 : ℝ) < min (1 / 2 : ℝ) (5 / 2) := by norm_num [min_def]
    have hu0 : 0 < u := hmin.trans hu.1
    have hu1 : u ≤ 5 / 2 := hu.2.trans_eq hmax
    have hnorm : ‖(u : ℂ) ^ j‖ = u ^ j := by
      rw [norm_pow, show ‖(u : ℂ)‖ = |u| from RCLike.norm_ofReal u, abs_of_pos hu0]
    rw [norm_mul, norm_mul, norm_hhatPhase t u, mul_one, hnorm]
    have h1 : ‖iteratedDeriv j (hhatAmp ξ) u‖ ≤ D * (1 + |ξ|) ^ j := hDb ξ u
    have h2 : u ^ j ≤ (5 / 2 : ℝ) ^ j := pow_le_pow_left₀ (le_of_lt hu0) hu1 j
    have h0 : (0 : ℝ) ≤ D * (1 + |ξ|) ^ j := by positivity
    calc ‖iteratedDeriv j (hhatAmp ξ) u‖ * u ^ j
        ≤ (D * (1 + |ξ|) ^ j) * (5 / 2) ^ j := mul_le_mul h1 h2 (by positivity) h0
      _ = D * (1 + |ξ|) ^ j * (5 / 2) ^ j := by ring
  calc ‖((-1 : ℂ) ^ j / P) * ∫ u in (1 / 2)..(5 / 2), iteratedDeriv j (hhatAmp ξ) u *
        ((u : ℂ) ^ j * hhatPhase t u)‖
      = ‖((-1 : ℂ) ^ j / P)‖ * ‖∫ u in (1 / 2)..(5 / 2), iteratedDeriv j (hhatAmp ξ) u *
        ((u : ℂ) ^ j * hhatPhase t u)‖ := norm_mul _ _
    _ ≤ (1 / |t| ^ j) * (2 * (D * (1 + |ξ|) ^ j * (5 / 2) ^ j)) :=
        mul_le_mul hA hB (norm_nonneg _) (by positivity)
    _ = (2 * (5 / 2) ^ j * D) * ((1 + |ξ|) ^ j / |t| ^ j) := by
        rw [div_eq_mul_inv]; ring
    _ ≤ (2 * (5 / 2) ^ j * D + 1) * ((1 + |ξ|) ^ j / |t| ^ j) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ = (2 * (5 / 2) ^ j * D + 1) * (1 + |ξ|) ^ j / |t| ^ j := by
        rw [div_eq_mul_inv]; ring

/-! ## The three statements -/

theorem hhat_decay :
    ((∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ξ : ℝ, ξ ≠ 0 →
        ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j) ∧
     (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ξ : ℝ, t ≠ 0 →
        ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |ξ|) ^ j / |t| ^ j)) ∧
    (∀ j : ℕ, 2 ≤ j → ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ t X : ℝ, 0 < X →
        ∑' (m : {m : ℤ // X < |(m : ℝ)|}), ‖Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖
          ≤ C * (1 + |t|) ^ j / ((N : ℝ) ^ j * X ^ (j - 1))) := by
  have hpart1 : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ξ : ℝ, ξ ≠ 0 →
      ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j :=
    fun j => Work.GM.S3.hhat_decay j
  refine ⟨⟨hpart1, ?_⟩, ?_⟩
  · intro j
    exact hhat_decay_in_t_of j (fun k => hhat_amp_deriv_bound k)
      (fun g t j hg hl hr => ibp_phase_iterated g t j hg hl hr)
  · intro j hj
    exact hhat_sum_tail hpart1 j hj

end Work.GM.S2
