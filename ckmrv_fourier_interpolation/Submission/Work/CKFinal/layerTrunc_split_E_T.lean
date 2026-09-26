/-
# Splitting the `trunc` part of the CKMRV layer at the cusp threshold `E_T w`

CKMRV's layer `F₂` decomposes (5.2)--(5.3) as `low + trunc + high`.  On the cusp-`0` tile
`E = KEpsilon` the `trunc` piece is split at the height `E_T w = Im (S • w) + 1` of the cusp
expansion of the kernel instead of at `t = 1`:

* `E_WinT ℓ d w r` — the window `[1, E_T w]` against the full kernel `Kaxis (Kfun ℓ d) w`;
* `E_DevT ℓ d w r` — the tail `[E_T w, ∞)` against the *deviation* `Kaxis - Aexp (Gcusp ℓ d)`;
* the explicit integral of the cusp model `Aexp (Gcusp ℓ d)` over the window, which is what the
  closed form `E_TailClosed (Gcusp ℓ d) (E_T w)` completes to `highPart`.

The identity proved here is the pure bookkeeping step of that split: the `trunc` integral over
`[1,∞)` of the deviation equals the window integral of the *kernel*, plus the tail integral of
the deviation, minus the window integral of the *model*.

The only analytic input is the integrability of the deviation against the Gaussian weight on
`[1,∞)` (`devTail_integrable` below): on the window `[1, E_T w]` the kernel is bounded by
`Work.Asymptotics.EpolyWindowE_clean_far` and the model by its four explicit coefficients, while
on `(E_T w, ∞)` the sharp deviation `Work.Asymptotics.E_deviation_sharp` gives the decay
`e^{-π(t - Im (S • w))}`.
-/
import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.SKEC.Defs
import Submission.Work.Asymptotics.SKEC.FarWindowClean
import Submission.Work.Asymptotics.E_deviation_sharp
import Submission.Work.Asymptotics.TailIntegral
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.CKFinal.setIntegral_Ici_eq_Ioi_of_eq_zero_below

namespace Work.CKFinal

open MeasureTheory UpperHalfPlane

/-- Norm bound for the cusp model on `t ≥ 0`. -/
private lemma Aexp_norm_le (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (w : ℍ) {t : ℝ} (ht : 0 ≤ t) :
    ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
      ≤ ‖Work.Asymptotics.Gcusp ℓ d 0 0 w‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 0 1 w‖
        + Real.exp (2 * Real.pi * t)
          * (‖Work.Asymptotics.Gcusp ℓ d 1 0 w‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 w‖) := by
  have h01 : ‖((t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 0 1 w)‖
      = t * ‖Work.Asymptotics.Gcusp ℓ d 0 1 w‖ := by
    rw [mul_assoc, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_of_nonneg ht]
  have h11 : ‖((t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 1 1 w)‖
      = t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 w‖ := by
    rw [mul_assoc, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_of_nonneg ht]
  have hexpn : ‖Complex.exp (2 * Real.pi * t)‖ = Real.exp (2 * Real.pi * t) := by
    rw [Complex.norm_exp]; simp
  rw [Work.Asymptotics.Aexp]
  calc ‖Work.Asymptotics.Gcusp ℓ d 0 0 w
          + (t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 0 1 w
          + Complex.exp (2 * Real.pi * t)
            * (Work.Asymptotics.Gcusp ℓ d 1 0 w
              + (t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 1 1 w)‖
      ≤ ‖Work.Asymptotics.Gcusp ℓ d 0 0 w
            + (t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 0 1 w‖
          + ‖Complex.exp (2 * Real.pi * t)
            * (Work.Asymptotics.Gcusp ℓ d 1 0 w
              + (t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 1 1 w)‖ := norm_add_le _ _
    _ ≤ (‖Work.Asymptotics.Gcusp ℓ d 0 0 w‖
            + ‖(t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 0 1 w‖)
          + Real.exp (2 * Real.pi * t)
            * (‖Work.Asymptotics.Gcusp ℓ d 1 0 w‖
              + ‖(t : ℂ) * Complex.I * Work.Asymptotics.Gcusp ℓ d 1 1 w‖) := by
        refine add_le_add (norm_add_le _ _) ?_
        rw [norm_mul, hexpn]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_nonneg _)
    _ = ‖Work.Asymptotics.Gcusp ℓ d 0 0 w‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 0 1 w‖
          + Real.exp (2 * Real.pi * t)
            * (‖Work.Asymptotics.Gcusp ℓ d 1 0 w‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 w‖) := by
        rw [h01, h11]

/-- Integrability of the truncated-deviation integrand on `[1,∞)`. -/
private lemma devTail_integrable (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {w : UpperHalfPlane} (hw : w ∈ Work.Asymptotics.KEpsilon) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici (1 : ℝ)) := by
  obtain ⟨C, N, M, hC, hN, hM, hwin⟩ := Work.Asymptotics.EpolyWindowE_clean_far ℓ d hd
  obtain ⟨Cd, Nd, Md, hCd, hNd, hMd, hdev⟩ := Work.Asymptotics.E_deviation_sharp ℓ d hd
  set T : ℝ := Work.Asymptotics.E_T w with hT
  have hTim : T = (ModularGroup.S • w).im + 1 := by rw [hT]; rfl
  have hT1 : (1 : ℝ) ≤ T := by rw [hTim]; exact Work.Asymptotics.one_le_E_T hw
  have hTs : T ≤ Work.Kernels.scale w := by rw [hT]; exact Work.Asymptotics.E_T_le_scale hw
  have hmeasK : Measurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t) :=
    Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd w
  have hmeasA : Measurable (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t) := by
    unfold Work.Asymptotics.Aexp; fun_prop
  have hmeasE : Measurable (fun t : ℝ => Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    fun_prop
  have hnormE : ∀ t : ℝ, ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
      = Real.exp (-(Real.pi * r ^ 2 * t)) := by
    intro t
    rw [Complex.norm_exp]
    congr 1
    have h : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, Complex.ofReal_re]
  -- the window `[1,T]`
  have hwint : IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Icc (1 : ℝ) T) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun t : ℝ => C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
        + (‖Work.Asymptotics.Gcusp ℓ d 0 0 w‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 0 1 w‖
          + Real.exp (2 * Real.pi * t)
            * (‖Work.Asymptotics.Gcusp ℓ d 1 0 w‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 w‖))) ?_ ?_ ?_
    · have hcont : Continuous (fun t : ℝ =>
          C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
            + (‖Work.Asymptotics.Gcusp ℓ d 0 0 w‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 0 1 w‖
              + Real.exp (2 * Real.pi * t)
                * (‖Work.Asymptotics.Gcusp ℓ d 1 0 w‖
                  + t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 w‖))) := by
        refine Continuous.add ?_ ?_
        · exact continuous_const.mul ((Real.continuous_rpow_const hM).comp (by fun_prop))
        · fun_prop
      exact hcont.continuousOn.integrableOn_compact isCompact_Icc
    · exact ((hmeasK.sub hmeasA).mul hmeasE).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      obtain ⟨ht1, htT⟩ := ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
      have hb := hwin w t hw ht0 (le_trans htT hTs)
      have hA := Aexp_norm_le ℓ d w (le_of_lt ht0)
      have he1 : Real.exp (-(Real.pi * r ^ 2 * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht0.le)
      calc ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
          = ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
            * Real.exp (-(Real.pi * r ^ 2 * t)) := by rw [norm_mul, hnormE]
        _ ≤ (‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
              + ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖) * 1 := by
            refine mul_le_mul (norm_sub_le _ _) he1 (Real.exp_nonneg _) (by positivity)
        _ = ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
              + ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖ := mul_one _
        _ ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
              + (‖Work.Asymptotics.Gcusp ℓ d 0 0 w‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 0 1 w‖
                + Real.exp (2 * Real.pi * t)
                  * (‖Work.Asymptotics.Gcusp ℓ d 1 0 w‖
                    + t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 w‖)) := add_le_add hb hA
  -- the tail `(T,∞)`
  have htint : IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi T) := by
    have hpos : 0 < Real.pi * (1 + r ^ 2) := by positivity
    refine MeasureTheory.Integrable.mono'
      (g := fun t : ℝ => (Cd * (Work.Kernels.scale w) ^ Nd * 2 ^ Md
            * Real.exp (Real.pi * (ModularGroup.S • w).im))
          * (t ^ Md * Real.exp (-(Real.pi * (1 + r ^ 2) * t)))) ?_ ?_ ?_
    · refine ((Work.Asymptotics.integrableOn_rpow_mul_exp_neg Md (Real.pi * (1 + r ^ 2))
        hMd hpos).mono_set ?_).const_mul _
      intro t ht
      exact le_trans hT1 (le_of_lt ht)
    · exact ((hmeasK.sub hmeasA).mul hmeasE).aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have htT : T ≤ t := le_of_lt ht
      have ht1 : (1 : ℝ) ≤ t := le_trans hT1 htT
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
      have hb := hdev w t hw (by rw [← hTim]; exact htT)
      have hpow : (1 + t) ^ Md ≤ 2 ^ Md * t ^ Md := by
        have h2 : 1 + t ≤ 2 * t := by linarith
        have h3 : (1 + t) ^ Md ≤ (2 * t) ^ Md := Real.rpow_le_rpow (by linarith) h2 hMd
        rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt ht0)] at h3
      have hexp : Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
            * Real.exp (-(Real.pi * r ^ 2 * t))
          = Real.exp (Real.pi * (ModularGroup.S • w).im)
            * Real.exp (-(Real.pi * (1 + r ^ 2) * t)) := by
        calc Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
              * Real.exp (-(Real.pi * r ^ 2 * t))
            = Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)) + -(Real.pi * r ^ 2 * t)) :=
              (Real.exp_add _ _).symm
          _ = Real.exp (Real.pi * (ModularGroup.S • w).im + -(Real.pi * (1 + r ^ 2) * t)) := by
              congr 1; ring
          _ = Real.exp (Real.pi * (ModularGroup.S • w).im)
              * Real.exp (-(Real.pi * (1 + r ^ 2) * t)) := Real.exp_add _ _
      calc ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖
          = ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
            * Real.exp (-(Real.pi * r ^ 2 * t)) := by rw [norm_mul, hnormE]
        _ ≤ (Cd * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
              * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))))
            * Real.exp (-(Real.pi * r ^ 2 * t)) :=
            mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
        _ ≤ (Cd * (Work.Kernels.scale w) ^ Nd * (2 ^ Md * t ^ Md)
              * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))))
            * Real.exp (-(Real.pi * r ^ 2 * t)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
            exact mul_le_mul_of_nonneg_left hpow
              (mul_nonneg hCd.le (Real.rpow_nonneg (Work.Kernels.scale_pos w).le Nd))
        _ = (Cd * (Work.Kernels.scale w) ^ Nd * 2 ^ Md * t ^ Md)
              * (Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
                * Real.exp (-(Real.pi * r ^ 2 * t))) := by ring
        _ = (Cd * (Work.Kernels.scale w) ^ Nd * 2 ^ Md * t ^ Md)
              * (Real.exp (Real.pi * (ModularGroup.S • w).im)
                * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) := by rw [hexp]
        _ = (Cd * (Work.Kernels.scale w) ^ Nd * 2 ^ Md
              * Real.exp (Real.pi * (ModularGroup.S • w).im))
            * (t ^ Md * Real.exp (-(Real.pi * (1 + r ^ 2) * t))) := by ring
  have hunion := hwint.union htint
  rwa [Set.Icc_union_Ioi_eq_Ici hT1] at hunion
/-- **`E_DevT` as a tail integral over `(E_T w, ∞)`.**  `E_DevT` is by definition
`sinSq r · ∫_{t ≥ 1} g t` with `g t = 0` for `t < E_T w` and `g t = (Kaxis - Aexp) t · e^{-πr²t}`
for `t ≥ E_T w`; since `E_T w ≥ 1` this is the same as the integral over `(E_T w, ∞)` of the
deviation alone (`setIntegral_Ici_eq_Ioi_of_eq_zero_below`). -/
lemma E_DevT_eq_integral_Ioi (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) {w : ℍ}
    (hw : w ∈ Work.Asymptotics.KEpsilon) (r : ℝ) :
    Work.Asymptotics.E_DevT ℓ d w r
      = Work.Asymptotics.sinSq r * ∫ t in Set.Ioi (Work.Asymptotics.E_T w),
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
              * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  rw [Work.Asymptotics.E_DevT, Work.Asymptotics.tailIntegral]
  congr 1
  refine setIntegral_Ici_eq_Ioi_of_eq_zero_below (B := Work.Asymptotics.E_T w)
    (f := fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
    (Work.Asymptotics.one_le_E_T hw) ?_ ?_
  · intro t ht
    rw [if_pos ht, zero_mul]
  · intro t ht
    rw [if_neg (not_lt.mpr ht)]
    congr 1
    rw [show -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_exp]

/-- **The `trunc` piece splits at the cusp threshold `E_T w`.**  With `T := E_T w ≥ 1`,
`∫_{[1,∞)} (Kaxis - Aexp)e^{-πr²t} = ∫_{[1,T]} Kaxis e^{-πr²t} + ∫_{(T,∞)} (Kaxis - Aexp)e^{-πr²t}
- ∫_{[1,T]} Aexp e^{-πr²t}`, which after multiplication by the regularising factor `sinSq r` is
exactly the asserted decomposition of `layerTrunc (Gcusp ℓ d)`. -/
theorem layerTrunc_split_E_T (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
      Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d w r
        = Work.Asymptotics.E_WinT ℓ d w r + Work.Asymptotics.E_DevT ℓ d w r
          - Work.Asymptotics.sinSq r * ∫ t in (1 : ℝ)..(Work.Asymptotics.E_T w),
              Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t
                * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  intro w hw r
  have hT1 : (1 : ℝ) ≤ Work.Asymptotics.E_T w := Work.Asymptotics.one_le_E_T hw
  rw [Work.Asymptotics.layerTrunc, Work.Asymptotics.E_WinT,
    E_DevT_eq_integral_Ioi ℓ d hw r]
  -- abbreviations for the three integrands of the window/tail integral
  set F : ℝ → ℂ := fun t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hF
  set Kf : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hKf
  set Af : ℝ → ℂ := fun t => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hAf
  -- the deviation is integrable on `[1,∞)`
  have hFint : IntegrableOn F (Set.Ici (1 : ℝ)) := devTail_integrable ℓ d hd hw r
  -- the cusp model is continuous, hence integrable on the compact window
  have hAint : IntegrableOn Af (Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w)) := by
    have hcont : Continuous Af := by rw [hAf]; unfold Work.Asymptotics.Aexp; fun_prop
    exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hKfint : IntegrableOn Kf (Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w)) := by
    refine IntegrableOn.congr_fun ((hFint.mono_set (fun t ht => ht.1.le)).add hAint)
      (fun t _ => ?_) measurableSet_Ioc
    simp only [Pi.add_apply]
    rw [hF, hKf, hAf]; ring
  -- splitting `∫_{[1,∞)} F = ∫_{[1,T]} F + ∫_{(T,∞)} F`
  have hsplit : ∫ t in Set.Ici (1 : ℝ), F t
      = (∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), F t)
        + ∫ t in Set.Ioi (Work.Asymptotics.E_T w), F t := by
    have h1 : ∫ t in Set.Ici (1 : ℝ), F t = ∫ t in Set.Ioi (1 : ℝ), F t :=
      setIntegral_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici' (by simp : volume ({(1 : ℝ)} : Set ℝ) = 0)).symm
    rw [h1, ← Set.Ioc_union_Ioi_eq_Ioi hT1]
    exact setIntegral_union
      (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2)))
      measurableSet_Ioi (hFint.mono_set (fun t ht => ht.1.le))
      (hFint.mono_set (fun t ht => le_trans hT1 ht.le))
  -- on the window, `F = Kf - Af`
  have hsub : ∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), F t
      = (∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), Kf t)
        - ∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), Af t := by
    rw [← integral_sub hKfint hAint]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [hF, hKf, hAf]; ring
  have hKfIoc : ∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), Kf t
      = ∫ t in (1 : ℝ)..(Work.Asymptotics.E_T w), Kf t :=
    (intervalIntegral.integral_of_le hT1).symm
  have hAfIoc : ∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), Af t
      = ∫ t in (1 : ℝ)..(Work.Asymptotics.E_T w), Af t :=
    (intervalIntegral.integral_of_le hT1).symm
  have hL : ∫ t in Set.Ici (1 : ℝ), F t
      = (∫ t in (1 : ℝ)..(Work.Asymptotics.E_T w), Kf t)
        + (∫ t in Set.Ioi (Work.Asymptotics.E_T w), F t)
        - (∫ t in (1 : ℝ)..(Work.Asymptotics.E_T w), Af t) := by
    rw [hsplit, hsub, hKfIoc, hAfIoc]
    ring
  rw [hL]
  ring

end Work.CKFinal
