import Mathlib
import Submission.Work.CKFinal.LineDecay.ContourPoint
import Submission.Work.Asymptotics.Khat_funnel_tail_sharp
import Submission.Work.CKFinal.S_smul_line_mem_DomainD

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-- `Gplus d τ` is continuous as a function of the second variable. -/
lemma continuous_Gplus (d : ℕ) (τ : UpperHalfPlane) :
    Continuous (fun z : UpperHalfPlane => Work.Asymptotics.Compact.Gplus d τ z) := by
  unfold Work.Asymptotics.Compact.Gplus
  split_ifs with hd8
  · unfold Work.Asymptotics.Compact.Gplus8 Work.Asymptotics.Compact.phi1
    fun_prop
  · have hpow : Continuous
        (fun z : UpperHalfPlane => Complex.exp ((Real.pi : ℂ) * Complex.I * (z : ℂ)) ^ (-2 : ℤ)) := by
      have h : Continuous
          (fun z : UpperHalfPlane => Complex.exp ((Real.pi : ℂ) * Complex.I * (z : ℂ))) := by
        fun_prop
      exact h.zpow₀ (-2) (fun z => Or.inl (Complex.exp_ne_zero _))
    unfold Work.Asymptotics.Compact.Gplus24 Work.Asymptotics.Compact.phi1
      Work.Asymptotics.Compact.phi2t
    fun_prop

/-- `Gminus d ℓ τ` is continuous as a function of the second variable. -/
lemma continuous_Gminus (d : ℕ) (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    Continuous (fun z : UpperHalfPlane => Work.Asymptotics.Compact.Gminus d ℓ τ z) := by
  unfold Work.Asymptotics.Compact.Gminus
  split_ifs with hd8
  · unfold Work.Asymptotics.Compact.Gminus8
    fun_prop
  · have hpow : Continuous
        (fun z : UpperHalfPlane => Complex.exp ((Real.pi : ℂ) * Complex.I * (z : ℂ)) ^ (-2 : ℤ)) := by
      have h : Continuous
          (fun z : UpperHalfPlane => Complex.exp ((Real.pi : ℂ) * Complex.I * (z : ℂ))) := by
        fun_prop
      exact h.zpow₀ (-2) (fun z => Or.inl (Complex.exp_ne_zero _))
    unfold Work.Asymptotics.Compact.Gminus24
    fun_prop

/-- **The cusp-`i∞` deviation of `K̂` along the imaginary axis, for fixed `τ`.**

Let `τ` lie on one of the lines `Re τ = ±1/2` with `Im τ ≥ 12` (so `Funnel τ` holds, in the sense
of `Work.Asymptotics.Funnel`), let `zcb t = ofComplex (t * I)` (the contour point, see
`Submission.Work.CKFinal.LineDecay.ContourPoint`), and suppose `t ↦ K̂^{(d)}(τ, i t)` is continuous
on `(0,∞)` (hypothesis `hcont`, available from the pole-free-ness of the imaginary axis).  Then
for `t ≥ 1` the hatted kernel differs from the `S`-transported cusp model
`(𝒢₊^{(d)}(τ, i t) - 𝒢₋^{(d)}(τ, i t))/2` by at most `C (1+t)^N e^{-π t}`.

Route: for `t ≥ Im τ + 1` this is `Work.Asymptotics.Khat_funnel_tail_sharp ℓ d hd` (module
`Submission.Work.Asymptotics.Khat_funnel_tail_sharp`), applied with `z = zcb t` (whose coercion is
`t * I`); for `t ∈ [1, Im τ + 1]` the difference is continuous on a compact interval (`hcont`
together with the fact that `Gplus`/`Gminus` are polynomials in `z` and `(Ept z)^{-2}`, hence
continuous), so it is bounded there.  Combine the two constants (up to `max` with the value at
`t = 1`) and set `N := max M 0`. -/
theorem khat_tail_deviation (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im)
    (hcont : ContinuousOn (fun t : ℝ => Work.Kernels.Khat ℓ d τ (zcb t)) (Set.Ioi 0)) :
    ∃ C N : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ici (1 : ℝ),
      ‖Work.Kernels.Khat ℓ d τ (zcb t)
          - (Work.Asymptotics.Compact.Gplus d τ (zcb t)
              - Work.Asymptotics.Compact.Gminus d ℓ τ (zcb t)) / 2‖
        ≤ C * (1 + t) ^ N * Real.exp (-(Real.pi * t)) := by
  -- `τ` lies on the funnel
  have hF : Work.Asymptotics.Funnel τ :=
    ⟨(Work.CKFinal.S_smul_line_mem_DomainD τ hre (by linarith)).1, by linarith⟩
  -- the sharp funnel tail estimate
  obtain ⟨C0, N0, M0, hC0, hN0, hM0, hb⟩ := Work.Asymptotics.Khat_funnel_tail_sharp ℓ d hd
  -- the compact interval `[1, Im τ + 1]`
  have hsub : Set.Icc (1 : ℝ) (τ.im + 1) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le one_pos ht.1
  have hzcb : ContinuousOn zcb (Set.Icc (1 : ℝ) (τ.im + 1)) := continuousOn_zcb.mono hsub
  have hdev : ContinuousOn
      (fun t : ℝ => Work.Kernels.Khat ℓ d τ (zcb t)
        - (Work.Asymptotics.Compact.Gplus d τ (zcb t)
            - Work.Asymptotics.Compact.Gminus d ℓ τ (zcb t)) / 2)
      (Set.Icc (1 : ℝ) (τ.im + 1)) :=
    (hcont.mono hsub).sub
      ((((continuous_Gplus d τ).comp_continuousOn hzcb).sub
        ((continuous_Gminus d ℓ τ).comp_continuousOn hzcb)).div_const 2)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hdev
  have h1mem : (1 : ℝ) ∈ Set.Icc (1 : ℝ) (τ.im + 1) := ⟨le_refl 1, by linarith⟩
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 1 h1mem)
  -- the combined constant and exponent
  set C : ℝ := max (C0 * (Work.Kernels.scale τ) ^ N0)
      (B * Real.exp (Real.pi * (τ.im + 1))) with hCdef
  have hscale : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hC1 : C0 * (Work.Kernels.scale τ) ^ N0 ≤ C := le_max_left _ _
  have hC2 : B * Real.exp (Real.pi * (τ.im + 1)) ≤ C := le_max_right _ _
  have hCnn : 0 ≤ C :=
    le_trans (mul_nonneg hC0.le (Real.rpow_nonneg hscale.le N0)) (le_max_left _ _)
  refine ⟨C, M0, hCnn, ?_⟩
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := ht
  rcases le_or_gt t (τ.im + 1) with hle | hgt
  · -- compact regime
    have hmem : t ∈ Set.Icc (1 : ℝ) (τ.im + 1) := ⟨ht1, hle⟩
    have hexp_ge : Real.exp (-(Real.pi * (τ.im + 1))) ≤ Real.exp (-(Real.pi * t)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    have hpow_ge : (1 : ℝ) ≤ (1 + t) ^ M0 := Real.one_le_rpow (by linarith) hM0
    have hpow_nn : (0 : ℝ) ≤ (1 + t) ^ M0 := Real.rpow_nonneg (by linarith) M0
    have hsplit : B * Real.exp (Real.pi * (τ.im + 1)) * Real.exp (-(Real.pi * (τ.im + 1))) = B := by
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    calc ‖Work.Kernels.Khat ℓ d τ (zcb t)
            - (Work.Asymptotics.Compact.Gplus d τ (zcb t)
                - Work.Asymptotics.Compact.Gminus d ℓ τ (zcb t)) / 2‖
        ≤ B := hB t hmem
      _ = B * Real.exp (Real.pi * (τ.im + 1)) * Real.exp (-(Real.pi * (τ.im + 1))) := hsplit.symm
      _ ≤ C * Real.exp (-(Real.pi * (τ.im + 1))) :=
          mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le
      _ ≤ C * ((1 + t) ^ M0 * Real.exp (-(Real.pi * t))) := by
          apply mul_le_mul_of_nonneg_left _ hCnn
          calc Real.exp (-(Real.pi * (τ.im + 1)))
              ≤ 1 * Real.exp (-(Real.pi * t)) := by rw [one_mul]; exact hexp_ge
            _ ≤ (1 + t) ^ M0 * Real.exp (-(Real.pi * t)) :=
                mul_le_mul_of_nonneg_right hpow_ge (Real.exp_pos _).le
      _ = C * (1 + t) ^ M0 * Real.exp (-(Real.pi * t)) := by rw [mul_assoc]
  · -- funnel tail regime
    have hge : τ.im + 1 ≤ t := le_of_lt hgt
    have htpos : 0 < t := by linarith
    have hzt : ((zcb t : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := zcb_coe htpos
    have htail := hb τ (zcb t) t hF hge hzt
    calc ‖Work.Kernels.Khat ℓ d τ (zcb t)
            - (Work.Asymptotics.Compact.Gplus d τ (zcb t)
                - Work.Asymptotics.Compact.Gminus d ℓ τ (zcb t)) / 2‖
        ≤ C0 * (Work.Kernels.scale τ) ^ N0 * (1 + t) ^ M0 * Real.exp (-(Real.pi * t)) := htail
      _ ≤ C * (1 + t) ^ M0 * Real.exp (-(Real.pi * t)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg (by linarith) M0)

end Work.CKFinal.LineDecay
