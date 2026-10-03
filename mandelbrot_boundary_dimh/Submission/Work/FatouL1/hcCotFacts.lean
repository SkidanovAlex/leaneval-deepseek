import Mathlib
import Submission.Work.FatouL1.cothKernel
import Submission.Work.FatouL1.cotPiNegHalf
import Submission.Work.FatouL1.cotPiPosHalf
import Submission.Work.FatouL1.cotDecayHalfPlane
import Submission.Work.FatouL1.dslopeSin_ne_zero
import Submission.Work.FatouL1.cot_sub_inv_eq_deriv_dslope

/-!
# The cotangent facts of Shishikura's Fatou-coordinate chapter

The elementary analytic facts about `Complex.cot (π ·)` used when the Fatou-coordinate kernel is
moved through the strip `|Re| < 1`:

* the two boundary lines `π(±1/2 + i y)` are mapped to `-i tanh (π y)`;
* the decay of `cot (π τ) ± i` in the half-planes `Im τ ≥ 1/2` resp. `Im τ ≤ -1/2`;
* the logarithmic-derivative identity
  `cot (π τ) - 1/(π τ) = (dslope sin 0)'(πτ) / (dslope sin 0)(πτ)` on `|Re τ| < 1`, the
  non-vanishing of `dslope sin 0` on `|Re| < π`, and differentiability of the left hand side.

The only non-trivial point is the value `deriv (dslope sin 0) 0 = 0` at the origin (needed both for
`τ = 0` in the identity above and for the removable singularity of `cot (π w) - 1/(π w)` at `0`).
Writing `g = dslope sin 0` one has the doubling identity `g (2z) = g z * cos z` for all `z` (from
`sin (2z) = 2 sin z cos z` and `w * g w = sin w`), so differentiating at `0` gives
`(deriv g 0) * 2 = deriv g 0`, whence `deriv g 0 = 0`.  Since then `g w - cos w = o(w)` at `0` and
`w * g w = sin w`, the function `w ↦ cot (π w) - 1/(π w) = -(g(πw) - cos(πw)) / (π w g(π w))` has
limit `0` at `0`, which by the removable-singularity theorem makes it complex differentiable there.
-/

namespace Work.FatouL1

open Filter
open scoped Topology

noncomputable section

private abbrev hcSlopeSin : ℂ → ℂ := dslope Complex.sin 0

private lemma hcSlopeSin_zero : dslope Complex.sin 0 0 = 1 := by
  simp [hcSlopeSin, dslope_same]

private lemma hcSlopeSin_diff : DifferentiableAt ℂ (dslope Complex.sin 0) 0 := by
  have h := (Complex.differentiableOn_dslope (f := Complex.sin) (s := Set.univ) (c := 0)
    (by simp : (Set.univ : Set ℂ) ∈ 𝓝 (0:ℂ))).mpr Complex.differentiable_sin.differentiableOn
  exact (h 0 (Set.mem_univ 0)).differentiableAt (by simp)

private lemma hcSlopeSin_doubling (h : ℂ) : hcSlopeSin (2*h) = hcSlopeSin h * Complex.cos h := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · have h1 : (2*h) * hcSlopeSin (2*h) = Complex.sin (2*h) := by
      have := sub_smul_dslope Complex.sin (0:ℂ) (2*h)
      simpa using this
    have h2 : h * hcSlopeSin h = Complex.sin h := by
      have := sub_smul_dslope Complex.sin (0:ℂ) h
      simpa using this
    have h3 : (2 * h) * hcSlopeSin (2 * h) = (2 * h) * (hcSlopeSin h * Complex.cos h) := by
      rw [h1, Complex.sin_two_mul, ← h2]
      ring
    exact mul_left_cancel₀ (mul_ne_zero two_ne_zero hh) h3

private lemma hcSlopeSin_deriv_zero : deriv (dslope Complex.sin 0) 0 = 0 := by
  have hd : HasDerivAt hcSlopeSin (deriv hcSlopeSin 0) 0 := hcSlopeSin_diff.hasDerivAt
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) (2:ℂ) 0 := hasDerivAt_const_mul (2:ℂ)
  have h2 : HasDerivAt (fun w => hcSlopeSin (2*w)) (deriv hcSlopeSin 0 * 2) 0 :=
    hd.comp_of_eq (x := 0) (h := fun w : ℂ => 2*w) hlin (by ring)
  have h3 : HasDerivAt (fun w => hcSlopeSin w * Complex.cos w)
      (deriv hcSlopeSin 0 * Complex.cos 0 + hcSlopeSin 0 * (-Complex.sin 0)) 0 :=
    hd.mul (Complex.hasDerivAt_cos 0)
  have hfun : (fun w : ℂ => hcSlopeSin (2*w)) = fun w => hcSlopeSin w * Complex.cos w := by
    funext w; exact hcSlopeSin_doubling w
  have h4 : HasDerivAt (fun w => hcSlopeSin (2*w))
      (deriv hcSlopeSin 0 * Complex.cos 0 + hcSlopeSin 0 * (-Complex.sin 0)) 0 := by
    rw [hfun]; exact h3
  have key : deriv hcSlopeSin 0 * 2 = deriv hcSlopeSin 0 * Complex.cos 0 + hcSlopeSin 0 * (-Complex.sin 0) := h2.unique h4
  have key' : deriv hcSlopeSin 0 * 2 = deriv hcSlopeSin 0 := by simpa [hcSlopeSin_zero] using key
  have h1 : deriv hcSlopeSin 0 * (2 - 1) = 0 := by
    rw [mul_sub, mul_one, key', sub_self]
  have h2' : (2:ℂ) - 1 = 1 := by norm_num
  rw [h2', mul_one] at h1
  exact h1

private lemma sin_pi_mul_ne_zero (τ : ℂ) (hτ : τ ≠ 0) (hre : |τ.re| < 1) :
    Complex.sin (Real.pi * τ) ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h0
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hk' : Real.pi * τ = Real.pi * (k : ℂ) := by rw [hk]; ring
  have hτk : τ = (k : ℂ) := mul_left_cancel₀ hpi hk'
  have hklt : |(k : ℝ)| < 1 := by
    rw [hτk] at hre
    simpa using hre
  rw [← Int.cast_abs] at hklt
  have hk0 : |k| < 1 := by exact_mod_cast hklt
  have : k = 0 := Int.abs_lt_one_iff.mp hk0
  rw [this] at hτk
  exact hτ (by simpa using hτk)

private lemma tendsto_Fw : Tendsto (fun w : ℂ => Complex.cot (Real.pi*w) - 1/(Real.pi*w)) (𝓝[≠] 0) (𝓝 0) := by
  have hlin : HasDerivAt (fun w : ℂ => Real.pi * w) (Real.pi : ℂ) 0 := hasDerivAt_const_mul (Real.pi : ℂ)
  have hg' : HasDerivAt (fun w : ℂ => hcSlopeSin (Real.pi*w)) (deriv hcSlopeSin 0 * Real.pi) 0 :=
    hcSlopeSin_diff.hasDerivAt.comp_of_eq (x := 0) (h := fun w : ℂ => Real.pi * w) hlin (by ring)
  have hc' : HasDerivAt (fun w : ℂ => Complex.cos (Real.pi*w)) ((-Complex.sin 0) * Real.pi) 0 :=
    (Complex.hasDerivAt_cos 0).comp_of_eq (x := 0) (h := fun w : ℂ => Real.pi*w) hlin (by ring)
  have hH : HasDerivAt (fun w : ℂ => hcSlopeSin (Real.pi*w) - Complex.cos (Real.pi*w))
      (deriv hcSlopeSin 0 * Real.pi - (-Complex.sin 0) * Real.pi) 0 := hg'.sub hc'
  have hH0 : deriv hcSlopeSin 0 * Real.pi - (-Complex.sin 0) * Real.pi = 0 := by simp [hcSlopeSin_deriv_zero]
  have hHlim : Tendsto (fun w : ℂ => (hcSlopeSin (Real.pi*w) - Complex.cos (Real.pi*w)) / w) (𝓝[≠] 0) (𝓝 0) := by
    have h := hH.tendsto_slope
    rw [hH0] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [slope, sub_zero, vsub_eq_sub, hcSlopeSin_zero, mul_zero, Complex.cos_zero, sub_self,
      smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hcontg : ContinuousAt (fun w : ℂ => Real.pi * hcSlopeSin (Real.pi*w)) 0 := by
    have h2 : ContinuousAt hcSlopeSin (Real.pi * 0) := by
      have := (continuousAt_dslope_same (f := Complex.sin) (a := (0:ℂ))).mpr
        Complex.differentiable_sin.differentiableAt
      simpa using this
    have h1 : ContinuousAt (fun w : ℂ => Real.pi * w) 0 := by fun_prop
    have h3 : ContinuousAt (fun w : ℂ => hcSlopeSin (Real.pi * w)) 0 :=
      ContinuousAt.comp (x := (0:ℂ)) (f := fun w : ℂ => Real.pi * w) (g := hcSlopeSin) h2 h1
    exact h3.const_mul (Real.pi : ℂ)
  have hden : Tendsto (fun w : ℂ => Real.pi * hcSlopeSin (Real.pi*w)) (𝓝[≠] 0) (𝓝 (Real.pi : ℂ)) := by
    have h := hcontg.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
    simpa [hcSlopeSin_zero] using h
  have hquot : Tendsto ((fun x : ℂ => -((hcSlopeSin (Real.pi*x) - Complex.cos (Real.pi*x)) / x)) /
      fun w : ℂ => Real.pi * hcSlopeSin (Real.pi*w)) (𝓝[≠] 0) (𝓝 0) := by
    have := hHlim.neg.div hden (by simp [Real.pi_ne_zero])
    simpa using this
  refine hquot.congr' ?_
  have hwball : ∀ᶠ w in 𝓝[≠] (0:ℂ), w ∈ Metric.ball (0:ℂ) 1 :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 zero_lt_one)
  filter_upwards [self_mem_nhdsWithin, hwball] with w hw hb
  have hre : |w.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm w)
    (by simpa [Metric.mem_ball, dist_eq_norm] using hb)
  have hS : Complex.sin (Real.pi*w) = (Real.pi*w) * hcSlopeSin (Real.pi*w) := by
    have := sub_smul_dslope Complex.sin (0:ℂ) (Real.pi*w); simpa using this.symm
  have hsinne : Complex.sin (Real.pi*w) ≠ 0 := sin_pi_mul_ne_zero w hw hre
  have hPne : Real.pi * w ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hw
  have hGne : hcSlopeSin (Real.pi*w) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hS; exact hsinne hS
  have hPG : (Real.pi*w) * hcSlopeSin (Real.pi*w) ≠ 0 := mul_ne_zero hPne hGne
  show -((hcSlopeSin (Real.pi*w) - Complex.cos (Real.pi*w)) / w) / (Real.pi * hcSlopeSin (Real.pi*w)) =
    Complex.cot (Real.pi*w) - 1/(Real.pi*w)
  rw [Complex.cot_eq_cos_div_sin, hS]
  field_simp
  ring

private lemma continuousAt_Fw :
    ContinuousAt (fun w : ℂ => Complex.cot (Real.pi*w) - 1/(Real.pi*w)) 0 := by
  have hlim : Tendsto (fun w : ℂ => Complex.cot (Real.pi*w) - 1/(Real.pi*w)) (𝓝 0)
      (𝓝 ((fun w : ℂ => Complex.cot (Real.pi*w) - 1/(Real.pi*w)) 0)) := by
    rw [← nhdsNE_sup_pure (0:ℂ), Filter.tendsto_sup]
    refine ⟨?_, ?_⟩
    · simpa [Complex.cot] using tendsto_Fw
    · exact tendsto_pure_nhds (fun w : ℂ => Complex.cot (Real.pi*w) - 1/(Real.pi*w)) (0:ℂ)
  exact hlim

private lemma diffAt_Fw (τ : ℂ) (hτ : τ ≠ 0) (hre : |τ.re| < 1) :
    DifferentiableAt ℂ (fun w : ℂ => Complex.cot (Real.pi*w) - 1/(Real.pi*w)) τ := by
  have hsin : Complex.sin (Real.pi * τ) ≠ 0 := sin_pi_mul_ne_zero τ hτ hre
  have hPτ : Real.pi * τ ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hτ
  have hlin : DifferentiableAt ℂ (fun w : ℂ => Real.pi * w) τ :=
    (differentiableAt_id (𝕜 := ℂ)).const_mul (Real.pi : ℂ)
  have hcos : DifferentiableAt ℂ (fun w : ℂ => Complex.cos (Real.pi * w)) τ :=
    DifferentiableAt.comp τ (Complex.differentiableAt_cos (x := Real.pi * τ)) hlin
  have hsinf : DifferentiableAt ℂ (fun w : ℂ => Complex.sin (Real.pi * w)) τ :=
    DifferentiableAt.comp τ (Complex.differentiableAt_sin (x := Real.pi * τ)) hlin
  have hcot : DifferentiableAt ℂ (fun w : ℂ => Complex.cot (Real.pi * w)) τ := by
    have h := hcos.div hsinf hsin
    have h' : ((fun w : ℂ => Complex.cos (Real.pi * w)) / fun w : ℂ => Complex.sin (Real.pi * w))
        = fun w : ℂ => Complex.cot (Real.pi*w) := by
      funext w
      rw [Pi.div_apply, Complex.cot_eq_cos_div_sin]
    rwa [h'] at h
  exact hcot.sub ((differentiableAt_const (1:ℂ)).div hlin hPτ)

private theorem diffAt_Fw_all (τ : ℂ) (hre : |τ.re| < 1) :
    DifferentiableAt ℂ (fun w : ℂ => Complex.cot (Real.pi*w) - 1/(Real.pi*w)) τ := by
  by_cases hτ : τ = 0
  · subst hτ
    have hball : Metric.ball (0:ℂ) 1 ∈ 𝓝 (0:ℂ) := Metric.ball_mem_nhds 0 zero_lt_one
    have h1 : DifferentiableOn ℂ (fun w : ℂ => Complex.cot (Real.pi*w) - 1/(Real.pi*w))
        (Metric.ball 0 1 \ {0}) := by
      intro x hx
      have hxre : |x.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm x)
        (by simpa [Metric.mem_ball, dist_eq_norm] using hx.1)
      exact (diffAt_Fw x hx.2 hxre).differentiableWithinAt
    have h3 : DifferentiableOn ℂ (fun w : ℂ => Complex.cot (Real.pi*w) - 1/(Real.pi*w))
        (Metric.ball 0 1) :=
      (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
        (f := fun w : ℂ => Complex.cot (Real.pi*w) - 1/(Real.pi*w))
        (s := Metric.ball 0 1) (c := 0) hball).mp ⟨h1, continuousAt_Fw⟩
    exact (h3 0 (Metric.mem_ball_self zero_lt_one)).differentiableAt hball
  · exact diffAt_Fw τ hτ hre


theorem hcCotFacts :
    (∀ y : ℝ, Complex.cot (Real.pi * ((1 / 2 : ℂ) + (y : ℂ) * Complex.I)) =
      -Complex.I * (Real.tanh (Real.pi * y) : ℂ)) ∧
    (∀ y : ℝ, Complex.cot (Real.pi * ((-1 / 2 : ℂ) + (y : ℂ) * Complex.I)) =
      -Complex.I * (Real.tanh (Real.pi * y) : ℂ)) ∧
    (∀ τ : ℂ, 1 / 2 ≤ τ.im →
      ‖Complex.cot (Real.pi * τ) + Complex.I‖ ≤ 4 * Real.exp (-2 * Real.pi * τ.im)) ∧
    (∀ τ : ℂ, τ.im ≤ -(1 / 2) →
      ‖Complex.cot (Real.pi * τ) - Complex.I‖ ≤ 4 * Real.exp (2 * Real.pi * τ.im)) ∧
    (∀ τ : ℂ, |τ.re| < 1 → Complex.cot (Real.pi * τ) - 1 / (Real.pi * τ) =
      deriv (dslope Complex.sin 0) (Real.pi * τ) / (dslope Complex.sin 0 (Real.pi * τ))) ∧
    (∀ v : ℂ, |v.re| < Real.pi → dslope Complex.sin 0 v ≠ 0) ∧
    (∀ τ : ℂ, |τ.re| < 1 →
      DifferentiableAt ℂ (fun w => Complex.cot (Real.pi * w) - 1 / (Real.pi * w)) τ) := by
  refine ⟨cotPiPosHalf, cotPiNegHalf, cotDecayHalfPlane.1, cotDecayHalfPlane.2, ?_,
    dslopeSin_ne_zero, diffAt_Fw_all⟩
  intro τ hτ
  rcases eq_or_ne τ 0 with rfl | hne
  · simp [Complex.cot, hcSlopeSin_zero, hcSlopeSin_deriv_zero]
  · exact cot_sub_inv_eq_deriv_dslope τ hne hτ

end

end Work.FatouL1
