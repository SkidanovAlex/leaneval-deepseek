/-
# The `T`-ladder of the CKMRV layer `layer (Gcusp ℓ d)`

The CKMRV layer `F₂ = Work.Asymptotics.layer (Gcusp ℓ d) ℓ d` satisfies the "second difference"
identity `layer ℓ d (1 +ᵥ u) r = 2 * layer ℓ d u r - layer ℓ d (-1 +ᵥ u) r`, i.e.
`(T-I)² layer = 0` along the translation `T : τ ↦ τ + 1`.  This is the layer-level counterpart of
the `T`-ladder of the naive contour transform
(`Work.Asymptotics.kernelTransform_vadd_of_integrable`).

The proof decomposes `layer` (for `r ≠ 0`) as `layerLow + layerTrunc + highPart`:

* `layerLow` and `layerTrunc` are integrals of integrands that are *pointwise* ladders
  (`Work.Asymptotics.Kaxis_T2_Kfun` for the kernel, `Gcusp_vadd_ladder` for the cusp
  coefficients); the integrals inherit the ladder from linearity of the Bochner integral once
  the three integrands are known to be *integrable*;
* `highPart` is an explicit linear combination of the four coefficient functions `Gcusp ℓ d i j`
  with `τ`-independent coefficients, so it inherits the ladder entrywise.

The integrability is the only analytic input.  Under the hypotheses `u.re ∉ ℤ` and `1/2 < u.im`
the contour `z = i t` (`t > 0`) never meets a pole of `z ↦ K^{(d)}(u,z)`
(`Work.Asymptotics.NonCoincidence.jInvariantFun_ne_imagAxis_of_re_notInt_im_gt_half`), so
`Kaxis (Kfun ℓ d) u` is bounded on compact `t`-segments (`Kaxis_le_on_segment` below); near
`t = 0` this is `Work.Asymptotics.Kaxis_cusp_of_bounded`, and as `t → ∞` the cusp expansion
`Work.Asymptotics.kernel_axis_bound` gives exponential decay of `Kaxis - Aexp`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.cuspTile_seminorm
import Submission.Work.Asymptotics.PGFar.Reduction
import Submission.Work.Asymptotics.Divisor
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.paperLayer_agreement
import Submission.Work.Asymptotics.cuspExpansionKernel
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.MiddleRange.Main
import Submission.Work.Asymptotics.NonCoincidence.jInvariantFun_ne_imagAxis_of_re_notInt_im_gt_half
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Kernels.KernelFacts.psi4_T2
import Submission.Work.Kernels.PhiAnnihilation
import Submission.Work.Kernels.Theorem31

namespace Work.Asymptotics

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 800000

/-! ## The contour point `i t` as a total function

Following `Work.Asymptotics.HalfFunnel.ctFun`, we record `i t` through
`UpperHalfPlane.ofComplex` so that `t ↦ i t` is a total function and images of intervals are
compact. -/

/-- The contour point `i t` (its value off `t > 0` is irrelevant). -/
def ctPointL (t : ℝ) : ℍ := UpperHalfPlane.ofComplex (Complex.I * (t : ℂ))

lemma ctPointL_coe {t : ℝ} (ht : 0 < t) : ((ctPointL t : ℍ) : ℂ) = Complex.I * (t : ℂ) := by
  rw [ctPointL, UpperHalfPlane.ofComplex_apply_of_im_pos (z := Complex.I * (t : ℂ))
    (by simpa [Complex.mul_im] using ht)]

lemma ctPointL_eq_imagAxis {t : ℝ} (ht : 0 < t) :
    ctPointL t = Work.Kernels.imagAxis t ht := by
  apply UpperHalfPlane.ext
  rw [ctPointL_coe ht]
  change Complex.I * (t : ℂ) = (t : ℂ) * Complex.I
  exact mul_comm _ _

lemma ctPointL_im {t : ℝ} (ht : 0 < t) : (ctPointL t).im = t := by
  rw [← UpperHalfPlane.coe_im, ctPointL_coe ht]
  simp

lemma ctPointL_re {t : ℝ} (ht : 0 < t) : (ctPointL t).re = 0 := by
  rw [← UpperHalfPlane.coe_re, ctPointL_coe ht]
  simp [Complex.mul_re]

lemma continuousOn_ctPointL : ContinuousOn ctPointL (Set.Ioi 0) :=
  UpperHalfPlane.continuousOn_ofComplex_I_mul

/-- The contour segment `{i t : δ ≤ t ≤ B}` as a subset of `ℍ`. -/
def csegL (δ B : ℝ) : Set ℍ := ctPointL '' Set.Icc δ B

lemma isCompact_csegL {δ B : ℝ} (hδ : 0 < δ) : IsCompact (csegL δ B) :=
  isCompact_Icc.image_of_continuousOn
    (continuousOn_ctPointL.mono fun t ht => lt_of_lt_of_le hδ (Set.mem_Icc.mp ht).1)

lemma ctPointL_mem_csegL {δ B t : ℝ} (ht : t ∈ Set.Icc δ B) : ctPointL t ∈ csegL δ B :=
  ⟨t, ht, rfl⟩

lemma mem_csegL {δ B : ℝ} {z : ℍ} : z ∈ csegL δ B ↔ ∃ t ∈ Set.Icc δ B, ctPointL t = z := Iff.rfl

lemma csegL_im {δ B : ℝ} (hδ : 0 < δ) {z : ℍ} (hz : z ∈ csegL δ B) :
    δ ≤ z.im ∧ z.im ≤ B := by
  obtain ⟨t, ht, rfl⟩ := hz
  have ht0 : 0 < t := lt_of_lt_of_le hδ (Set.mem_Icc.mp ht).1
  rw [ctPointL_im ht0]
  exact ⟨(Set.mem_Icc.mp ht).1, (Set.mem_Icc.mp ht).2⟩

/-! ## A uniform lower bound for a continuous function on a compact set away from its zeros -/

lemma exists_lower_norm_of_isCompact_ne {S : Set ℍ} (hS : IsCompact S) {f : ℍ → ℂ}
    (hf : Continuous f) (hne : ∀ z ∈ S, f z ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ S, c ≤ ‖f z‖ := by
  rcases S.eq_empty_or_nonempty with rfl | hne'
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨z₀, hz₀, hmin⟩ := hS.exists_isMinOn hne' (hf.norm.continuousOn)
    exact ⟨‖f z₀‖, norm_pos_iff.mpr (hne z₀ hz₀), fun z hz => (isMinOn_iff.mp hmin) z hz⟩

/-! ## `Kaxis` is bounded on compact contour segments away from the coincidences -/

/-- **Boundedness of the kernel on a contour segment avoiding the coincidences.**  If
`j u ≠ j (i t)` for `t ∈ [δ,B]`, then `‖K^{(d)}(u, i t)‖` is bounded on that segment. -/
theorem Kaxis_le_on_segment (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : UpperHalfPlane) {δ B : ℝ} (hδ : 0 < δ)
    (hclean : ∀ (t : ℝ) (ht : 0 < t), δ ≤ t → t ≤ B →
      Work.Kernels.jInvariantFun u ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ M : ℝ, 0 < M ∧ ∀ (t : ℝ) (ht : 0 < t), δ ≤ t → t ≤ B →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t‖ ≤ M := by
  obtain ⟨M, hMpos, hM⟩ := Work.Asymptotics.HalfFunnel.exists_bound_Kfun_off_coincidence
    ℓ d hd isCompact_singleton (isCompact_csegL hδ) (fun τ hτ z hz => by
      rw [Set.mem_singleton_iff] at hτ
      obtain ⟨t, ht, htz⟩ := hz
      have ht0 : 0 < t := lt_of_lt_of_le hδ (Set.mem_Icc.mp ht).1
      subst htz
      rw [hτ, ctPointL_eq_imagAxis ht0]
      exact hclean t ht0 (Set.mem_Icc.mp ht).1 (Set.mem_Icc.mp ht).2)
  refine ⟨M, hMpos, fun t ht htδ htB => ?_⟩
  rw [Work.Kernels.Kaxis, dif_pos ht]
  exact hM u rfl (Work.Kernels.imagAxis t ht) (by
    rw [← ctPointL_eq_imagAxis ht]
    exact ctPointL_mem_csegL (Set.mem_Icc.mpr ⟨htδ, htB⟩))

/-! ## Integrability of the two contour integrands -/

lemma norm_exp_contourL (r t : ℝ) :
    ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ = Real.exp (-(Real.pi * r ^ 2 * t)) := by
  rw [Complex.norm_exp]
  congr 1
  have hr2 : ((r : ℂ) ^ 2).re = r ^ 2 := by
    have h : ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow r 2).symm
    rw [h, Complex.ofReal_re]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  rw [hr2]
  ring

lemma measurable_AexpL (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (u : UpperHalfPlane) :
    Measurable (fun t : ℝ => Work.Asymptotics.Aexp G u t) := by
  rw [show (fun t : ℝ => Work.Asymptotics.Aexp G u t) = fun t : ℝ =>
      G 0 0 u + ((t : ℂ) * Complex.I) * G 0 1 u
        + Complex.exp (2 * Real.pi * t) * (G 1 0 u + ((t : ℂ) * Complex.I) * G 1 1 u) from by
    funext t; rw [Work.Asymptotics.Aexp]]
  fun_prop

lemma norm_Aexp_le (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (u : UpperHalfPlane) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖Work.Asymptotics.Aexp G u t‖
      ≤ ‖G 0 0 u‖ + t * ‖G 0 1 u‖
        + Real.exp (2 * Real.pi * t) * (‖G 1 0 u‖ + t * ‖G 1 1 u‖) := by
  have hti : ‖((t : ℂ) * Complex.I)‖ = t := by
    rw [norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_nonneg ht]
  have hexp : ‖Complex.exp (2 * Real.pi * t)‖ = Real.exp (2 * Real.pi * t) := by
    rw [Complex.norm_exp]; congr 1; simp
  rw [Work.Asymptotics.Aexp]
  refine le_trans (norm_add_le _ _) (add_le_add (le_trans (norm_add_le _ _) ?_) ?_)
  · rw [norm_mul, hti]
  · rw [norm_mul, hexp]
    refine mul_le_mul_of_nonneg_left (le_trans (norm_add_le _ _) (add_le_add le_rfl ?_))
      (Real.exp_nonneg _)
    rw [norm_mul, hti]

/-- **Integrability of the contour integrand over `(0,1]`.** -/
theorem integrableOn_contour_low (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (u : UpperHalfPlane)
    (hclean : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun u ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioc 0 1) := by
  obtain ⟨δ₀, hδ₀pos, hcusp⟩ := Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
    ℓ d hd (K := ({u} : Set UpperHalfPlane)) (isCompact_singleton.isBounded)
  obtain ⟨c, hcpos, hc⟩ := hcusp 0 le_rfl
  obtain ⟨M, hMpos, hM⟩ := Kaxis_le_on_segment ℓ d hd u (δ := min δ₀ 1) (B := 1)
    (lt_min hδ₀pos one_pos) (fun t ht _ _ => hclean t ht)
  refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ (max c M) ?_
  · exact ((measurable_Kaxis_Kfun ℓ d hd u).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hexp : ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ 1 := by
      rw [norm_exp_contourL, Real.exp_le_one_iff]
      have hpos : 0 ≤ Real.pi * r ^ 2 * t :=
        mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht0.le
      linarith
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_right (norm_nonneg _) hexp) ?_
    by_cases hle : t ≤ min δ₀ 1
    · have h := hc u t (by rfl) ht0 (le_trans hle (min_le_left _ _))
      rw [Real.rpow_zero, mul_one] at h
      exact le_trans h (le_max_left _ _)
    · have h := hM t ht0 (le_of_lt (not_le.mp hle)) ht1
      exact le_trans h (le_max_right _ _)

/-- **Integrability of the truncated contour integrand over `(1,∞)`.** -/
theorem integrableOn_contour_trunc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (u : UpperHalfPlane)
    (hclean : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun u ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1) := by
  obtain ⟨C, Mn, T, hCpos, hMn, hTpos, hdec⟩ :=
    Work.Asymptotics.kernel_axis_bound ℓ d hd (K := ({u} : Set UpperHalfPlane))
      isCompact_singleton
  set T' : ℝ := max T 1 with hT'
  have hT'1 : (1 : ℝ) ≤ T' := le_max_right _ _
  have hT'T : T ≤ T' := le_max_left _ _
  obtain ⟨M, hMpos, hM⟩ := Kaxis_le_on_segment ℓ d hd u (δ := 1) (B := T') one_pos
    (fun t ht _ _ => hclean t ht)
  set Ae : ℝ := ‖Work.Asymptotics.Gcusp ℓ d 0 0 u‖ + T' * ‖Work.Asymptotics.Gcusp ℓ d 0 1 u‖
      + Real.exp (2 * Real.pi * T')
        * (‖Work.Asymptotics.Gcusp ℓ d 1 0 u‖ + T' * ‖Work.Asymptotics.Gcusp ℓ d 1 1 u‖)
    with hAe
  have hAexp : ∀ t ∈ Set.Icc (1 : ℝ) T',
      ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t‖ ≤ Ae := by
    intro t ht
    have htT : t ≤ T' := ht.2
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hexp1 : Real.exp (2 * Real.pi * t) ≤ Real.exp (2 * Real.pi * T') :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have h1 : t * ‖Work.Asymptotics.Gcusp ℓ d 0 1 u‖
        ≤ T' * ‖Work.Asymptotics.Gcusp ℓ d 0 1 u‖ :=
      mul_le_mul_of_nonneg_right htT (norm_nonneg _)
    have h2 : t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 u‖
        ≤ T' * ‖Work.Asymptotics.Gcusp ℓ d 1 1 u‖ :=
      mul_le_mul_of_nonneg_right htT (norm_nonneg _)
    have h3 : Real.exp (2 * Real.pi * t) * (‖Work.Asymptotics.Gcusp ℓ d 1 0 u‖
          + t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 u‖)
        ≤ Real.exp (2 * Real.pi * T') * (‖Work.Asymptotics.Gcusp ℓ d 1 0 u‖
          + T' * ‖Work.Asymptotics.Gcusp ℓ d 1 1 u‖) :=
      mul_le_mul hexp1 (add_le_add le_rfl h2) (by positivity) (Real.exp_nonneg _)
    have hgen := norm_Aexp_le (Work.Asymptotics.Gcusp ℓ d) u ht0
    rw [hAe]
    linarith
  -- the compact piece
  have hfin : MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Icc 1 T') := by
    refine IntegrableOn.of_bound isCompact_Icc.measure_lt_top ?_ (max (M + Ae) 1) ?_
    · exact (((measurable_Kaxis_Kfun ℓ d hd u).sub (measurable_AexpL _ u)).mul
        (by fun_prop)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
      have hexp : ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ 1 := by
        rw [norm_exp_contourL, Real.exp_le_one_iff]
        have hpos : 0 ≤ Real.pi * r ^ 2 * t :=
          mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht0.le
        linarith
      rw [norm_mul]
      refine le_trans (mul_le_of_le_one_right (norm_nonneg _) hexp) ?_
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t‖
          ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t‖
            + ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t‖ := norm_sub_le _ _
        _ ≤ M + Ae := add_le_add (hM t ht0 ht.1 ht.2) (hAexp t ht)
        _ ≤ max (M + Ae) 1 := le_max_left _ _
  -- the tail
  have htail : MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi T') := by
    have hg : MeasureTheory.Integrable
        (fun t : ℝ => (C * 2 ^ Mn) * (t ^ Mn * Real.exp (-(Real.pi * t))))
        (MeasureTheory.volume.restrict (Set.Ioi T')) :=
      ((Work.Asymptotics.integrableOn_rpow_mul_exp_neg_mul_Ioi Mn Real.pi Real.pi_pos).mono_set
        (Set.Ioi_subset_Ioi hT'1)).const_mul (C * 2 ^ Mn)
    refine MeasureTheory.Integrable.mono' hg ?_ ?_
    · exact (((measurable_Kaxis_Kfun ℓ d hd u).sub (measurable_AexpL _ u)).mul
        (by fun_prop)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htT : T ≤ t := le_trans hT'T (le_of_lt ht)
      have ht1 : (1 : ℝ) ≤ t := le_trans hT'1 (le_of_lt ht)
      have hbd := hdec u rfl t htT
      have hexp : ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ ≤ 1 := by
        rw [norm_exp_contourL, Real.exp_le_one_iff]
        have hpos : 0 ≤ Real.pi * r ^ 2 * t :=
          mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) (by linarith)
        linarith
      have h1t : (1 + t) ^ Mn ≤ 2 ^ Mn * t ^ Mn := by
        have h : (1 + t) ^ Mn ≤ (2 * t) ^ Mn :=
          Real.rpow_le_rpow (by linarith) (by linarith) hMn
        rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith : (0:ℝ) ≤ t)] at h
      rw [norm_mul]
      refine le_trans (mul_le_of_le_one_right (norm_nonneg _) hexp) ?_
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t‖
          ≤ C * (1 + t) ^ Mn * Real.exp (-(Real.pi * t)) := hbd
        _ ≤ C * (2 ^ Mn * t ^ Mn) * Real.exp (-(Real.pi * t)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1t hCpos.le)
              (Real.exp_nonneg _)
        _ = (C * 2 ^ Mn) * (t ^ Mn * Real.exp (-(Real.pi * t))) := by ring
  have hunion := IntegrableOn.union hfin htail
  have hset : Set.Icc (1 : ℝ) T' ∪ Set.Ioi T' = Set.Ici 1 := by
    ext t
    constructor
    · rintro (⟨h1, _⟩ | h2)
      · exact h1
      · exact le_of_lt (lt_of_le_of_lt hT'1 h2)
    · intro h1
      by_cases h2 : t ≤ T'
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (lt_of_not_ge h2)
  rwa [hset] at hunion


/-! ## The `T`-ladder of the cusp coefficients `Gcusp ℓ d i j`

`Gcusp ℓ d i j` is a linear combination of products `(T2op-killed factor) · (T-invariant
factor)`, so it is annihilated by `(T-I)²`, i.e. it satisfies the ladder
`G(τ+1) = 2G(τ) - G(τ-1)`.  We prove this entrywise. -/

/-- The "second difference" form of `(T-I)² F = 0`. -/
lemma vadd_ladder_of_T2op {F : ℍ → ℂ} (h : Work.Kernels.T2op F = 0) (u : ℍ) :
    F ((1 : ℝ) +ᵥ u) = 2 * F u - F ((-1 : ℝ) +ᵥ u) := by
  have h1 := congr_fun h ((-1 : ℝ) +ᵥ u)
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h1
  have h2 : (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u) = (1 : ℝ) +ᵥ u := by
    rw [← add_vadd]; norm_num
  have h3 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u) = u := by
    rw [← add_vadd]; norm_num
  rw [h2, h3] at h1
  linear_combination h1

private lemma T2op_congr_L {F G : ℍ → ℂ} (h : F = G) (hG : Work.Kernels.T2op G = 0) :
    Work.Kernels.T2op F = 0 := by rw [h]; exact hG

private lemma T2op_periodic_L {F : ℍ → ℂ} (h : ∀ τ, F ((1 : ℝ) +ᵥ τ) = F τ) :
    Work.Kernels.T2op F = 0 := by
  ext τ
  have h2 : F ((2 : ℝ) +ᵥ τ) = F τ := by
    rw [show (2 : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ ((1 : ℝ) +ᵥ τ) from by rw [← add_vadd]; norm_num, h, h]
  simp only [Work.Kernels.T2op, Pi.zero_apply]
  rw [h2, h]
  ring

private lemma T2op_const_mul_L (c : ℂ) {F : ℍ → ℂ} (h : Work.Kernels.T2op F = 0) :
    Work.Kernels.T2op (fun τ => c * F τ) = 0 := by
  ext τ
  have h1 := congr_fun h τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h1 ⊢
  linear_combination c * h1

private lemma T2op_sub_L {F G : ℍ → ℂ} (hF : Work.Kernels.T2op F = 0)
    (hG : Work.Kernels.T2op G = 0) :
    Work.Kernels.T2op (fun τ => F τ - G τ) = 0 := by
  ext τ
  have h1 := congr_fun hF τ
  have h2 := congr_fun hG τ
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h1 h2 ⊢
  linear_combination h1 - h2

private lemma T2op_div_const_L (c : ℂ) {F : ℍ → ℂ} (h : Work.Kernels.T2op F = 0) :
    Work.Kernels.T2op (fun τ => F τ / c) = 0 := by
  refine T2op_congr_L (G := fun τ => c⁻¹ * F τ) ?_ (T2op_const_mul_L c⁻¹ h)
  funext τ; rw [div_eq_mul_inv, mul_comm]

private lemma per_E4_L : ∀ τ : ℍ, Work.Kernels.E4Fun ((1 : ℝ) +ᵥ τ) = Work.Kernels.E4Fun τ :=
  fun τ => Work.Kernels.KernelFacts.E4Fun_vadd_one τ

private lemma per_E6_L : ∀ τ : ℍ, Work.Kernels.E6Fun ((1 : ℝ) +ᵥ τ) = Work.Kernels.E6Fun τ :=
  fun τ => Work.Kernels.KernelFacts.E6Fun_vadd_one τ

private lemma per_Delta_L : ∀ τ : ℍ, Work.Kernels.DeltaFun ((1 : ℝ) +ᵥ τ) = Work.Kernels.DeltaFun τ :=
  fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ

private lemma per_E4sq_L : ∀ τ : ℍ,
    (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 2) ((1 : ℝ) +ᵥ τ)
      = (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 2) τ := by
  intro τ
  show Work.Kernels.E4Fun ((1 : ℝ) +ᵥ τ) ^ 2 = Work.Kernels.E4Fun τ ^ 2
  rw [Work.Kernels.KernelFacts.E4Fun_vadd_one]

private lemma per_E4cube_L : ∀ τ : ℍ,
    (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 3) ((1 : ℝ) +ᵥ τ)
      = (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 3) τ := by
  intro τ
  show Work.Kernels.E4Fun ((1 : ℝ) +ᵥ τ) ^ 3 = Work.Kernels.E4Fun τ ^ 3
  rw [Work.Kernels.KernelFacts.E4Fun_vadd_one]

private lemma per_E4E6_L : ∀ τ : ℍ,
    (fun σ : ℍ => Work.Kernels.E4Fun σ * Work.Kernels.E6Fun σ) ((1 : ℝ) +ᵥ τ)
      = (fun σ : ℍ => Work.Kernels.E4Fun σ * Work.Kernels.E6Fun σ) τ := by
  intro τ
  show Work.Kernels.E4Fun ((1 : ℝ) +ᵥ τ) * Work.Kernels.E6Fun ((1 : ℝ) +ᵥ τ) = Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ
  rw [Work.Kernels.KernelFacts.E4Fun_vadd_one, Work.Kernels.KernelFacts.E6Fun_vadd_one]

private lemma per_E4sqE6_L : ∀ τ : ℍ,
    (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 2 * Work.Kernels.E6Fun σ) ((1 : ℝ) +ᵥ τ)
      = (fun σ : ℍ => Work.Kernels.E4Fun σ ^ 2 * Work.Kernels.E6Fun σ) τ := by
  intro τ
  show Work.Kernels.E4Fun ((1 : ℝ) +ᵥ τ) ^ 2 * Work.Kernels.E6Fun ((1 : ℝ) +ᵥ τ)
      = Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ
  rw [Work.Kernels.KernelFacts.E4Fun_vadd_one, Work.Kernels.KernelFacts.E6Fun_vadd_one]

private lemma T2op_phiVec0_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phiVec τ 0) = 0 := by
  refine T2op_congr_L (G := Work.Kernels.phiNeg2) ?_ Work.Kernels.phiNeg2_T2
  funext τ; simp [Work.Kernels.phiVec]

private lemma T2op_phiVec1_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phiVec τ 1) = 0 := by
  refine T2op_congr_L (G := Work.Kernels.phi0) ?_ Work.Kernels.phi0_T2
  funext τ; simp [Work.Kernels.phiVec]

private lemma T2op_phiVec2_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.phiVec τ 2) = 0 := by
  refine T2op_congr_L (G := Work.Kernels.phi2) ?_ Work.Kernels.phi2_T2
  funext τ; simp [Work.Kernels.phiVec]

private lemma T2op_psi2_L (ℓ : Work.Kernels.LogLambdaData) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.psi2 ℓ τ) = 0 :=
  Work.Kernels.KernelFacts.psi2_T2 ℓ

private lemma T2op_psi4_L (ℓ : Work.Kernels.LogLambdaData) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.psi4 ℓ τ) = 0 :=
  Work.Kernels.KernelFacts.psi4_T2 ℓ

private lemma T2op_E4_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E4Fun τ) = 0 :=
  T2op_periodic_L per_E4_L

private lemma T2op_E6_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E6Fun τ) = 0 :=
  T2op_periodic_L per_E6_L

private lemma T2op_Delta_L : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.DeltaFun τ) = 0 :=
  T2op_periodic_L per_Delta_L

private lemma E4Fun_vadd_neg_one_L (τ : ℍ) :
    Work.Kernels.E4Fun ((-1 : ℝ) +ᵥ τ) = Work.Kernels.E4Fun τ := by
  have h := Work.Kernels.KernelFacts.E4Fun_vadd_one ((-1 : ℝ) +ᵥ τ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ from by rw [← add_vadd]; norm_num] at h
  exact h.symm

private lemma E6Fun_vadd_neg_one_L (τ : ℍ) :
    Work.Kernels.E6Fun ((-1 : ℝ) +ᵥ τ) = Work.Kernels.E6Fun τ := by
  have h := Work.Kernels.KernelFacts.E6Fun_vadd_one ((-1 : ℝ) +ᵥ τ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ from by rw [← add_vadd]; norm_num] at h
  exact h.symm

private lemma DeltaFun_vadd_neg_one_L (τ : ℍ) :
    Work.Kernels.DeltaFun ((-1 : ℝ) +ᵥ τ) = Work.Kernels.DeltaFun τ := by
  have h := Work.Kernels.KernelFacts.DeltaFun_vadd_one ((-1 : ℝ) +ᵥ τ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ from by rw [← add_vadd]; norm_num] at h
  exact h.symm

/-- The `T`-ladder of the three components of `phiVec`. -/
lemma phiVec_vadd_ladder_L (k : Fin 3) (τ : ℍ) :
    Work.Kernels.phiVec ((1 : ℝ) +ᵥ τ) k
      = 2 * Work.Kernels.phiVec τ k - Work.Kernels.phiVec ((-1 : ℝ) +ᵥ τ) k := by
  fin_cases k
  · exact vadd_ladder_of_T2op T2op_phiVec0_L τ
  · exact vadd_ladder_of_T2op T2op_phiVec1_L τ
  · exact vadd_ladder_of_T2op T2op_phiVec2_L τ

private lemma psi2_vadd_ladder_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.psi2 ℓ ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Kernels.psi2 ℓ τ - Work.Kernels.psi2 ℓ ((-1 : ℝ) +ᵥ τ) :=
  vadd_ladder_of_T2op (T2op_psi2_L ℓ) τ

private lemma psi4_vadd_ladder_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.psi4 ℓ ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Kernels.psi4 ℓ τ - Work.Kernels.psi4 ℓ ((-1 : ℝ) +ᵥ τ) :=
  vadd_ladder_of_T2op (T2op_psi4_L ℓ) τ

private lemma Gcusp8_00_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp8 ℓ 0 0 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp8 ℓ 0 0 τ
        - Work.Asymptotics.Gcusp8 ℓ 0 0 ((-1 : ℝ) +ᵥ τ) := by
  have hbase : Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp8 ℓ 0 0 τ) = 0 := by
    have hA : Work.Kernels.T2op (fun τ : ℍ =>
        (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ) * (-Complex.I)) = 0 :=
      Work.Kernels.T2op_mul_of (Work.Kernels.T2op_mul_of T2op_phiVec0_L per_E6_L)
        (fun _ => rfl)
    have hB : Work.Kernels.T2op (fun τ : ℍ =>
        Work.Kernels.E4Fun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)) = 0 :=
      T2op_div_const_L _ (Work.Kernels.T2op_mul_of T2op_E4_L (fun _ => rfl))
    have hC : Work.Kernels.T2op (fun τ : ℍ =>
        Work.Kernels.psi4 ℓ τ / (2 * (Real.pi : ℂ))) = 0 :=
      T2op_div_const_L _ (T2op_psi4_L ℓ)
    have hsum : Work.Kernels.T2op (fun τ : ℍ =>
        ((Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ) * (-Complex.I)
          + Work.Kernels.E4Fun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - Work.Kernels.psi4 ℓ τ / (2 * (Real.pi : ℂ))) / 2) = 0 :=
      T2op_div_const_L 2 (T2op_sub_L (Work.Kernels.T2op_add hA hB) hC)
    refine T2op_congr_L (G := fun τ : ℍ =>
        ((Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ) * (-Complex.I)
          + Work.Kernels.E4Fun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - Work.Kernels.psi4 ℓ τ / (2 * (Real.pi : ℂ))) / 2) ?_ hsum
    funext τ
    rw [Work.Asymptotics.Gcusp8, if_neg (by decide : ¬ ((0 : Fin 2) = 1)),
      if_pos (by decide : ((0 : Fin 2) = 0))]
  exact vadd_ladder_of_T2op hbase τ

private lemma Gcusp8_01_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp8 ℓ 0 1 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp8 ℓ 0 1 τ
        - Work.Asymptotics.Gcusp8 ℓ 0 1 ((-1 : ℝ) +ᵥ τ) := by
  have hbase : Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp8 ℓ 0 1 τ) = 0 := by
    have hA : Work.Kernels.T2op (fun τ : ℍ =>
        (Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
          - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)) = 0 :=
      T2op_const_mul_L _ (T2op_sub_L
        (Work.Kernels.T2op_mul_of T2op_phiVec0_L per_E6_L)
        (Work.Kernels.T2op_mul_of T2op_phiVec1_L per_E4_L))
    have hB : Work.Kernels.T2op (fun τ : ℍ => Complex.I * Work.Kernels.E4Fun τ) = 0 :=
      T2op_const_mul_L _ T2op_E4_L
    have hsum : Work.Kernels.T2op (fun τ : ℍ =>
        ((Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
            - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)
          + Complex.I * Work.Kernels.E4Fun τ) / 2) = 0 :=
      T2op_div_const_L 2 (Work.Kernels.T2op_add hA hB)
    refine T2op_congr_L (G := fun τ : ℍ =>
        ((Real.pi : ℂ) / 3 * (Work.Kernels.phiVec τ 0 * Work.Kernels.E6Fun τ
            - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ)
          + Complex.I * Work.Kernels.E4Fun τ) / 2) ?_ hsum
    funext τ
    rw [Work.Asymptotics.Gcusp8, if_neg (by decide : ¬ ((0 : Fin 2) = 1)),
      if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
  exact vadd_ladder_of_T2op hbase τ

private lemma Gcusp8_10_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp8 ℓ 1 0 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp8 ℓ 1 0 τ
        - Work.Asymptotics.Gcusp8 ℓ 1 0 ((-1 : ℝ) +ᵥ τ) := by
  have h : ∀ σ : ℍ, Work.Asymptotics.Gcusp8 ℓ 1 0 σ = 0 := by
    intro σ
    rw [Work.Asymptotics.Gcusp8, if_pos (by decide : ((1 : Fin 2) = 1))]
  rw [h ((1 : ℝ) +ᵥ τ), h τ, h ((-1 : ℝ) +ᵥ τ)]
  ring

private lemma Gcusp8_11_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp8 ℓ 1 1 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp8 ℓ 1 1 τ
        - Work.Asymptotics.Gcusp8 ℓ 1 1 ((-1 : ℝ) +ᵥ τ) := by
  have h : ∀ σ : ℍ, Work.Asymptotics.Gcusp8 ℓ 1 1 σ = 0 := by
    intro σ
    rw [Work.Asymptotics.Gcusp8, if_pos (by decide : ((1 : Fin 2) = 1))]
  rw [h ((1 : ℝ) +ᵥ τ), h τ, h ((-1 : ℝ) +ᵥ τ)]
  ring

private lemma Gcusp24_00_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp24 ℓ 0 0 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp24 ℓ 0 0 τ
        - Work.Asymptotics.Gcusp24 ℓ 0 0 ((-1 : ℝ) +ᵥ τ) := by
  have hbase : Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ 0 0 τ) = 0 := by
    have h1 : Work.Kernels.T2op (fun τ : ℍ => -(13 * Complex.I / 12)
        * (Work.Kernels.phiVec τ 0
          * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))) = 0 :=
      T2op_const_mul_L _ (Work.Kernels.T2op_mul_of T2op_phiVec0_L per_E4sqE6_L)
    have h2 : Work.Kernels.T2op (fun τ : ℍ => Complex.I / 6
        * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) = 0 :=
      T2op_const_mul_L _ (Work.Kernels.T2op_mul_of T2op_phiVec1_L per_E4cube_L)
    have h3 : Work.Kernels.T2op (fun τ : ℍ => 168 * Complex.I
        * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)) = 0 :=
      T2op_const_mul_L _ (Work.Kernels.T2op_mul_of T2op_phiVec1_L per_Delta_L)
    have h4 : Work.Kernels.T2op (fun τ : ℍ => Complex.I / 12
        * (Work.Kernels.phiVec τ 2
          * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))) = 0 :=
      T2op_const_mul_L _ (Work.Kernels.T2op_mul_of T2op_phiVec2_L per_E4E6_L)
    have h5 : Work.Kernels.T2op (fun τ : ℍ => 720 * Work.Kernels.DeltaFun τ
        * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)) = 0 :=
      T2op_div_const_L _ (Work.Kernels.T2op_mul_of
        (T2op_const_mul_L 720 T2op_Delta_L) (fun _ => rfl))
    have h6 : Work.Kernels.T2op (fun τ : ℍ => 36 * Work.Kernels.DeltaFun τ
        / (Real.pi : ℂ)) = 0 :=
      T2op_div_const_L _ (T2op_const_mul_L 36 T2op_Delta_L)
    have h7 : Work.Kernels.T2op (fun τ : ℍ => Work.Kernels.E4Fun τ ^ 3
        * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)) = 0 :=
      T2op_div_const_L _ (Work.Kernels.T2op_mul_of
        (T2op_periodic_L per_E4cube_L) (fun _ => rfl))
    have h8 : Work.Kernels.T2op (fun τ : ℍ => 7 * (Work.Kernels.psi2 ℓ τ
        * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)) / (24 * (Real.pi : ℂ))) = 0 :=
      T2op_div_const_L _ (T2op_const_mul_L 7
        (Work.Kernels.T2op_mul_of (T2op_psi2_L ℓ) per_E4E6_L))
    have h9 : Work.Kernels.T2op (fun τ : ℍ => 5 * (Work.Kernels.psi4 ℓ τ
        * Work.Kernels.E4Fun τ ^ 2) / (24 * (Real.pi : ℂ))) = 0 :=
      T2op_div_const_L _ (T2op_const_mul_L 5
        (Work.Kernels.T2op_mul_of (T2op_psi4_L ℓ) per_E4sq_L))
    have hsum : Work.Kernels.T2op (fun τ : ℍ =>
        (-(13 * Complex.I / 12) * (Work.Kernels.phiVec τ 0
            * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))
          + Complex.I / 6 * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
          - 168 * Complex.I * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
          - Complex.I / 12 * (Work.Kernels.phiVec τ 2
              * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
          - 720 * Work.Kernels.DeltaFun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - 36 * Work.Kernels.DeltaFun τ / (Real.pi : ℂ)
          + Work.Kernels.E4Fun τ ^ 3 * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - 7 * (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
              / (24 * (Real.pi : ℂ))
          - 5 * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2)
              / (24 * (Real.pi : ℂ))) / 2) = 0 :=
      T2op_div_const_L 2 (T2op_sub_L (T2op_sub_L (Work.Kernels.T2op_add
        (T2op_sub_L (T2op_sub_L (T2op_sub_L (T2op_sub_L
          (Work.Kernels.T2op_add h1 h2) h3) h4) h5) h6) h7) h8) h9)
    refine T2op_congr_L (G := fun τ : ℍ =>
        (-(13 * Complex.I / 12) * (Work.Kernels.phiVec τ 0
            * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ))
          + Complex.I / 6 * (Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
          - 168 * Complex.I * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
          - Complex.I / 12 * (Work.Kernels.phiVec τ 2
              * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
          - 720 * Work.Kernels.DeltaFun τ * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - 36 * Work.Kernels.DeltaFun τ / (Real.pi : ℂ)
          + Work.Kernels.E4Fun τ ^ 3 * Work.Asymptotics.cuspL ℓ / (Real.pi : ℂ)
          - 7 * (Work.Kernels.psi2 ℓ τ * (Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ))
              / (24 * (Real.pi : ℂ))
          - 5 * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E4Fun τ ^ 2)
              / (24 * (Real.pi : ℂ))) / 2) ?_ hsum
    funext τ
    dsimp only [Work.Asymptotics.Gcusp24]
    rw [if_pos (by decide : ((0 : Fin 2) = 0 ∧ (0 : Fin 2) = 0))]
  exact vadd_ladder_of_T2op hbase τ

private lemma Gcusp24_01_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp24 ℓ 0 1 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp24 ℓ 0 1 τ
        - Work.Asymptotics.Gcusp24 ℓ 0 1 ((-1 : ℝ) +ᵥ τ) := by
  have hbase : Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp24 ℓ 0 1 τ) = 0 := by
    have hA : Work.Kernels.T2op (fun τ : ℍ => (Real.pi : ℂ) / 3
        * (Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
          + 720 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
          - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)) = 0 :=
      T2op_const_mul_L _ (T2op_sub_L (Work.Kernels.T2op_add
        (Work.Kernels.T2op_mul_of T2op_phiVec0_L per_E4sqE6_L)
        (T2op_const_mul_L 720 (Work.Kernels.T2op_mul_of T2op_phiVec1_L per_Delta_L)))
        (Work.Kernels.T2op_mul_of T2op_phiVec1_L per_E4cube_L))
    have hB : Work.Kernels.T2op (fun τ : ℍ => Complex.I * (720 * Work.Kernels.DeltaFun τ
        - Work.Kernels.E4Fun τ ^ 3)) = 0 :=
      T2op_const_mul_L _ (T2op_sub_L (T2op_const_mul_L 720 T2op_Delta_L)
        (T2op_periodic_L per_E4cube_L))
    have hsum : Work.Kernels.T2op (fun τ : ℍ =>
        ((Real.pi : ℂ) / 3
            * (Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
              + 720 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
              - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
          - Complex.I * (720 * Work.Kernels.DeltaFun τ
              - Work.Kernels.E4Fun τ ^ 3)) / 2) = 0 :=
      T2op_div_const_L 2 (T2op_sub_L hA hB)
    refine T2op_congr_L (G := fun τ : ℍ =>
        ((Real.pi : ℂ) / 3
            * (Work.Kernels.phiVec τ 0 * (Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ)
              + 720 * (Work.Kernels.phiVec τ 1 * Work.Kernels.DeltaFun τ)
              - Work.Kernels.phiVec τ 1 * Work.Kernels.E4Fun τ ^ 3)
          - Complex.I * (720 * Work.Kernels.DeltaFun τ
              - Work.Kernels.E4Fun τ ^ 3)) / 2) ?_ hsum
    funext τ
    dsimp only [Work.Asymptotics.Gcusp24]
    rw [if_neg (by decide : ¬ ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 0)),
      if_pos (by decide : ((0 : Fin 2) = 0 ∧ (1 : Fin 2) = 1))]
  exact vadd_ladder_of_T2op hbase τ

private lemma Gcusp24_10_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp24 ℓ 1 0 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp24 ℓ 1 0 τ
        - Work.Asymptotics.Gcusp24 ℓ 1 0 ((-1 : ℝ) +ᵥ τ) := by
  have h := Work.Asymptotics.Gcusp10_vadd_int ℓ (-1) τ
  have h1 : Work.Asymptotics.Gcusp24 ℓ 1 0 ((-1 : ℝ) +ᵥ τ)
      = Work.Asymptotics.Gcusp24 ℓ 1 0 τ
        + (-1 : ℂ) * (Work.Asymptotics.Gcusp24 ℓ 1 0 ((1 : ℝ) +ᵥ τ)
          - Work.Asymptotics.Gcusp24 ℓ 1 0 τ) := by
    have h2 : ((↑(-1 : ℤ) : ℝ)) = (-1 : ℝ) := by norm_num
    rw [h2] at h
    simpa [Work.Asymptotics.Gcusp] using h
  rw [h1]; ring

private lemma Gcusp24_11_L (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Asymptotics.Gcusp24 ℓ 1 1 ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp24 ℓ 1 1 τ
        - Work.Asymptotics.Gcusp24 ℓ 1 1 ((-1 : ℝ) +ᵥ τ) := by
  have h := Work.Asymptotics.Gcusp11_vadd_int ℓ (-1) τ
  have h1 : Work.Asymptotics.Gcusp24 ℓ 1 1 ((-1 : ℝ) +ᵥ τ)
      = Work.Asymptotics.Gcusp24 ℓ 1 1 τ
        + Complex.I / 3456 * (2 * (Real.pi : ℂ) * Complex.I) * Work.Asymptotics.A24 τ := by
    have h2 : ((↑(-1 : ℤ) : ℝ)) = (-1 : ℝ) := by norm_num
    rw [h2] at h
    simpa [Work.Asymptotics.Gcusp] using h
  have h3 : Work.Asymptotics.Gcusp24 ℓ 1 1 ((1 : ℝ) +ᵥ τ)
      = Work.Asymptotics.Gcusp24 ℓ 1 1 τ
        - Complex.I / 3456 * (2 * (Real.pi : ℂ) * Complex.I) * Work.Asymptotics.A24 τ := by
    simpa [Work.Asymptotics.Gcusp] using Work.Asymptotics.Gcusp11_vadd_int ℓ 1 τ
  rw [h1, h3]; ring

/-- **The `T`-ladder of the cusp coefficients.**  Every entry of `Gcusp ℓ d` (`d = 8` or `24`)
is annihilated by `(T-I)²`: `G(τ+1) = 2G(τ) - G(τ-1)`. -/
theorem Gcusp_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (i j : Fin 2) (τ : ℍ) :
    Work.Asymptotics.Gcusp ℓ d i j ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp ℓ d i j τ
        - Work.Asymptotics.Gcusp ℓ d i j ((-1 : ℝ) +ᵥ τ) := by
  rcases hd with h8 | h24
  · subst h8
    fin_cases i <;> fin_cases j
    · simpa [Work.Asymptotics.Gcusp] using Gcusp8_00_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp8_01_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp8_10_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp8_11_L ℓ τ
  · subst h24
    fin_cases i <;> fin_cases j
    · simpa [Work.Asymptotics.Gcusp] using Gcusp24_00_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp24_01_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp24_10_L ℓ τ
    · simpa [Work.Asymptotics.Gcusp] using Gcusp24_11_L ℓ τ

/-- **The `T`-ladder of the cusp model `Aexp`.** -/
theorem Aexp_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (t : ℝ) :
    Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ τ) t
      = 2 * Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ τ) t := by
  simp only [Work.Asymptotics.Aexp]
  rw [Gcusp_vadd_ladder ℓ d hd 0 0 τ, Gcusp_vadd_ladder ℓ d hd 0 1 τ,
    Gcusp_vadd_ladder ℓ d hd 1 0 τ, Gcusp_vadd_ladder ℓ d hd 1 1 τ]
  ring


/-! ## The ladder of the three pieces of the layer -/

lemma jInvariantFun_vadd_one_L (τ : ℍ) :
    Work.Kernels.jInvariantFun ((1 : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  simp only [Work.Kernels.jInvariantFun, Work.Kernels.KernelFacts.E4Fun_vadd_one,
    Work.Kernels.KernelFacts.DeltaFun_vadd_one]

lemma jInvariantFun_vadd_neg_one_L (τ : ℍ) :
    Work.Kernels.jInvariantFun ((-1 : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  simp only [Work.Kernels.jInvariantFun, E4Fun_vadd_neg_one_L, DeltaFun_vadd_neg_one_L]

/-- **The ladder of the `low` piece.** -/
theorem layerLow_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ)
    (hclean : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (r : ℝ) :
    Work.Asymptotics.layerLow ℓ d ((1 : ℝ) +ᵥ τ) r
      = 2 * Work.Asymptotics.layerLow ℓ d τ r
        - Work.Asymptotics.layerLow ℓ d ((-1 : ℝ) +ᵥ τ) r := by
  have hclean1 : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun ((1 : ℝ) +ᵥ τ)
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht
    rw [jInvariantFun_vadd_one_L]
    exact hclean t ht
  have hcleanm : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun ((-1 : ℝ) +ᵥ τ)
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht
    rw [jInvariantFun_vadd_neg_one_L]
    exact hclean t ht
  have hint1 := integrableOn_contour_low ℓ d hd ((1 : ℝ) +ᵥ τ) hclean1 r
  have hint0 := integrableOn_contour_low ℓ d hd τ hclean r
  have hintm := integrableOn_contour_low ℓ d hd ((-1 : ℝ) +ᵥ τ) hcleanm r
  have hpoint : ∀ t : ℝ,
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        = 2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
          - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ τ) t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    intro t
    have h := Work.Asymptotics.Kaxis_T2_Kfun ℓ d hd ((-1 : ℝ) +ᵥ τ) t
    have h2 : (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = (1 : ℝ) +ᵥ τ := by rw [← add_vadd]; norm_num
    have h3 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by rw [← add_vadd]; norm_num
    rw [h2, h3] at h
    linear_combination Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) * h
  have hkey : (∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = 2 * (∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        - ∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ τ) t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hsub : MeasureTheory.IntegrableOn (fun t : ℝ =>
        2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))) (Set.Ioc 0 1) :=
      hint0.const_mul 2
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => hpoint t),
      MeasureTheory.integral_sub hsub hintm, MeasureTheory.integral_const_mul]
  simp only [Work.Asymptotics.layerLow]
  rw [hkey]
  ring

/-- **The ladder of the `trunc` piece.** -/
theorem layerTrunc_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ)
    (hclean : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))
    (r : ℝ) :
    Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ τ) r
      = 2 * Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
        - Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ τ) r := by
  have hclean1 : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun ((1 : ℝ) +ᵥ τ)
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht
    rw [jInvariantFun_vadd_one_L]
    exact hclean t ht
  have hcleanm : ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun ((-1 : ℝ) +ᵥ τ)
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro t ht
    rw [jInvariantFun_vadd_neg_one_L]
    exact hclean t ht
  have hint1 := integrableOn_contour_trunc ℓ d hd ((1 : ℝ) +ᵥ τ) hclean1 r
  have hint0 := integrableOn_contour_trunc ℓ d hd τ hclean r
  have hintm := integrableOn_contour_trunc ℓ d hd ((-1 : ℝ) +ᵥ τ) hcleanm r
  have hpoint : ∀ t : ℝ,
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ τ) t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
      = 2 * ((Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ τ) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ τ) t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    intro t
    have h := Work.Asymptotics.Kaxis_T2_Kfun ℓ d hd ((-1 : ℝ) +ᵥ τ) t
    have h2 : (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = (1 : ℝ) +ᵥ τ := by rw [← add_vadd]; norm_num
    have h3 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by rw [← add_vadd]; norm_num
    rw [h2, h3] at h
    have ha := Aexp_vadd_ladder ℓ d hd τ t
    linear_combination (Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) * h
      - (Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) * ha
  have hkey : (∫ t in Set.Ici (1 : ℝ),
        (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ τ) t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = 2 * (∫ t in Set.Ici (1 : ℝ),
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        - ∫ t in Set.Ici (1 : ℝ),
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ τ) t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ τ) t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    have hsub : MeasureTheory.IntegrableOn (fun t : ℝ =>
        2 * ((Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))) (Set.Ici 1) :=
      hint0.const_mul 2
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun t _ => hpoint t),
      MeasureTheory.integral_sub hsub hintm, MeasureTheory.integral_const_mul]
  simp only [Work.Asymptotics.layerTrunc]
  rw [hkey]
  ring

/-- **The ladder of the `high` piece.** -/
theorem highPart_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (r : ℝ) :
    Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ τ) r
      = 2 * Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r
        - Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ τ) r := by
  simp only [Work.Asymptotics.highPart]
  rw [Gcusp_vadd_ladder ℓ d hd 0 0 τ, Gcusp_vadd_ladder ℓ d hd 0 1 τ,
    Gcusp_vadd_ladder ℓ d hd 1 0 τ, Gcusp_vadd_ladder ℓ d hd 1 1 τ]
  ring


/-! ## The ladder of the layer -/

/-- **The `T`-ladder of the CKMRV layer.**  For `u` with non-integral real part and imaginary
part `> 1/2` (so that the contour `z = i t` avoids the poles of `z ↦ K^{(d)}(u,z)`) the layer
satisfies `layer(u+1) = 2 layer(u) - layer(u-1)` for every `r`. -/
theorem layer_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : UpperHalfPlane) (hre : u.re ∉ Set.range (fun n : ℤ => (n : ℝ)))
    (him : (1 / 2 : ℝ) < u.im) :
    ∀ r : ℝ,
      Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) r
        = 2 * Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d u r
          - Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) r := by
  intro r
  by_cases hr : r = 0
  · subst hr
    simp [Work.Asymptotics.layer]
  · have hclean : ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun u ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) :=
      fun t ht => NonCoincidence.jInvariantFun_ne_imagAxis_of_re_notInt_im_gt_half u hre him ht
    have hL := layerLow_vadd_ladder ℓ d hd u hclean r
    have hT := layerTrunc_vadd_ladder ℓ d hd u hclean r
    have hH := highPart_vadd_ladder ℓ d hd u r
    have h1 : Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) r
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) r := by
      rw [Work.Asymptotics.layer, if_neg hr]
    have hu : Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d u r
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u r := by
      rw [Work.Asymptotics.layer, if_neg hr]
    have hm : Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) r
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) r := by
      rw [Work.Asymptotics.layer, if_neg hr]
    rw [h1, hu, hm]
    simp only [Work.Asymptotics.paperLayer]
    rw [hL, hT, hH]
    ring


end

end Work.Asymptotics
