import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs
import Submission.Work.Smooth.JordanSeparation.deriv_global_norm_bounds
import Submission.Work.Smooth.JordanSeparation.deriv_uniform_continuous
import Submission.Work.Smooth.JordanSeparation.detV_I_mul
import Submission.Work.Smooth.JordanSeparation.exists_lipschitz_of_periodic_contDiff


/-!
# A transverse Lipschitz unit field along an immersed closed plane curve

Given a `C¹` `2π`-periodic curve `c : ℝ → ℂ` whose derivative never vanishes (an *immersion*),
this file produces a `C¹` `2π`-periodic field `v : ℝ → ℂ` of *unit* vectors which is

* uniformly **transverse** to the curve (`IsTransverseUnitField c κ v`, with an explicit modulus
  `κ > 0`), and
* globally **Lipschitz** (`IsLipschitzField L v`, with an explicit constant `L > 0`).

The natural candidate — the normal field `t ↦ I·γ'(t)/‖γ'(t)‖` — already satisfies the
transversality condition *identically* (`detV (γ' t) (I·γ' t/‖γ' t‖) = ‖γ' t‖`), but it is only
as regular as `γ'`, which for a merely `C¹` curve need not be `C¹`.  The construction used here
instead *regularises the tangent direction by a chord*: for a sufficiently small shift `δ > 0`,
the chord field

`sec t = γ (t + δ) - γ t`

is `C¹` (it is a difference of `C¹` functions), `2π`-periodic, and — because `sec t ≈ δ·γ'(t)`
uniformly in `t` — nowhere vanishing, so the rotated normalised chord

`v t = I · sec t / ‖sec t‖`

is a `C¹` `2π`-periodic unit field.  Writing `m = inf ‖γ'‖ > 0` (the immersion is needed here),
`M = sup ‖γ'‖`, and choosing `δ` so that `‖γ' (t+δ) - γ' t‖ ≤ m²/(2M)` for all `t`, the mean
value inequality gives `‖sec t - δ·γ' t‖ ≤ ε·δ` with `ε = m²/(2M)`, whence
`⟪sec t, γ' t⟫ ≥ δ·m²/2` and hence

`detV (γ' t) (v t) = ⟪sec t, γ' t⟫ / ‖sec t‖ ≥ m²/(2M) ≥ (m²/(2M²))·‖γ' t‖`.

So `κ = m²/(2M²)` is a valid transversality modulus.  Global Lipschitz regularity is then a
consequence of `v` being `C¹` and periodic (the derivative of a periodic `C¹` function is bounded
by its maximum on one period).

The analytic inputs are isolated in the sibling files
`deriv_global_norm_bounds`, `deriv_uniform_continuous`, `detV_I_mul` and
`exists_lipschitz_of_periodic_contDiff`.
-/

namespace Work.Smooth.JordanSeparation

open Set Real

noncomputable section

lemma inner_div_ofReal_norm (a w : ℂ) :
    inner ℝ a (w / ((‖w‖ : ℝ) : ℂ)) = inner ℝ a w / ‖w‖ := by
  have h : w / ((‖w‖ : ℝ) : ℂ) = (‖w‖⁻¹ : ℝ) • w := by
    rw [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.real_smul, mul_comm]
  rw [h, inner_smul_right, div_eq_mul_inv, mul_comm]

theorem exists_transverse_lipschitz_field (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (h : Work.Smooth.Jordan.SmoothPlaneCurve.IsImmersion c) :
    ∃ (v : ℝ → ℂ) (κ L : ℝ), 0 < κ ∧ 0 < L ∧ Function.Periodic v (2 * Real.pi) ∧
      ContDiff ℝ 1 v ∧ Work.Smooth.JordanSeparation.IsTransverseUnitField c κ v ∧
      Work.Smooth.JordanSeparation.IsLipschitzField L v := by
  obtain ⟨m, M, hm_pos, hM_pos, hm_le, hM_le⟩ := deriv_global_norm_bounds c h
  have hmM : m ≤ M := le_trans (hm_le 0) (hM_le 0)
  set ε : ℝ := m ^ 2 / (2 * M) with hεdef
  have hε_pos : 0 < ε := by rw [hεdef]; positivity
  have hε_le : ε ≤ m / 2 := by
    rw [hεdef, div_le_iff₀ (by positivity)]
    nlinarith [hmM, hm_pos, hM_pos]
  obtain ⟨δ, hδ_pos, hδ⟩ := deriv_uniform_continuous c ε hε_pos
  set sec : ℝ → ℂ := fun t => c.γ (t + δ) - c.γ t with hsec
  have hsec_cd : ContDiff ℝ 1 sec := by
    rw [hsec]
    exact (c.contDiff.comp (by fun_prop)).sub c.contDiff
  have hsec_per : Function.Periodic sec (2 * Real.pi) := by
    intro t
    simp only [hsec]
    have h1 : c.γ (t + 2 * Real.pi + δ) = c.γ (t + δ) := by
      have ht : t + 2 * Real.pi + δ = (t + δ) + 2 * Real.pi := by ring
      rw [ht, c.periodic_apply]
    rw [h1, c.periodic_apply]
  have hMVT_shift : ∀ t : ℝ, ‖sec t - (δ : ℂ) * deriv c.γ t‖ ≤ ε * δ := by
    intro t
    have hGderiv : ∀ s : ℝ,
        HasDerivAt (fun s : ℝ => c.γ (t + s) - (s : ℂ) * deriv c.γ t)
          (deriv c.γ (t + s) - deriv c.γ t) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => c.γ (t + s)) (deriv c.γ (t + s)) s := by
        have hbase : HasDerivAt (fun y : ℝ => c.γ y) (deriv c.γ (t + s)) (t + s) :=
          (c.differentiable (t + s)).hasDerivAt
        have hinner : HasDerivAt (fun s : ℝ => t + s) 1 s := by
          simpa [add_comm] using (hasDerivAt_id s).const_add t
        have hcomp := HasDerivAt.scomp (x := s) (h := fun s : ℝ => t + s)
          (g₁ := fun y : ℝ => c.γ y) hbase hinner
        convert hcomp using 2
        all_goals first | rfl | rw [one_smul]
      have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * deriv c.γ t) (deriv c.γ t) s := by
        have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) s := by
          simpa using (hasDerivAt_id s).ofReal_comp
        simpa using hid.mul_const (deriv c.γ t)
      exact h1.sub h2
    have hbound : ∀ x ∈ Set.Ico (0:ℝ) δ,
        ‖deriv c.γ (t + x) - deriv c.γ t‖ ≤ ε := by
      intro x hx
      have hxle : |t - (t + x)| ≤ δ := by
        rw [show t - (t + x) = -x by ring, abs_neg, abs_of_nonneg hx.1]
        exact le_of_lt hx.2
      have hh := hδ t (t + x) hxle
      simpa [norm_sub_rev] using hh
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
        (f := fun s : ℝ => c.γ (t + s) - (s : ℂ) * deriv c.γ t)
        (a := 0) (b := δ) (f' := fun x : ℝ => deriv c.γ (t + x) - deriv c.γ t) (C := ε)
        (fun x _ => (hGderiv x).hasDerivWithinAt) hbound
    have hδmem : δ ∈ Set.Icc (0:ℝ) δ := ⟨le_of_lt hδ_pos, le_rfl⟩
    have hthis := hmvt δ hδmem
    have hGG : (fun s : ℝ => c.γ (t + s) - (s : ℂ) * deriv c.γ t) δ
          - (fun s : ℝ => c.γ (t + s) - (s : ℂ) * deriv c.γ t) 0
        = sec t - (δ : ℂ) * deriv c.γ t := by
      simp only [hsec, Complex.ofReal_zero, add_zero]
      ring
    rw [hGG] at hthis
    simpa using hthis
  have hMVT_up : ∀ t : ℝ, ‖sec t‖ ≤ M * δ := by
    intro t
    have hb := norm_image_sub_le_of_norm_deriv_le_segment'
        (f := c.γ) (a := t) (b := t + δ) (f' := deriv c.γ) (C := M)
        (fun x _ => (c.differentiable x).hasDerivAt.hasDerivWithinAt)
        (fun x _ => hM_le x)
    have hmem : t + δ ∈ Set.Icc t (t + δ) := ⟨by linarith [hδ_pos], le_rfl⟩
    have hthis := hb (t + δ) hmem
    have h2 : ‖c.γ (t + δ) - c.γ t‖ ≤ M * δ := by
      simpa using hthis
    simpa only [hsec] using h2
  have hInner : ∀ t : ℝ, (m^2/2) * δ ≤ inner ℝ (sec t) (deriv c.γ t) := by
    intro t
    have hshift := hMVT_shift t
    have hb1 : -(‖sec t - (δ:ℂ)*deriv c.γ t‖ * ‖deriv c.γ t‖)
        ≤ inner ℝ (sec t - (δ:ℂ)*deriv c.γ t) (deriv c.γ t) := by
      have h := abs_real_inner_le_norm (sec t - (δ:ℂ)*deriv c.γ t) (deriv c.γ t)
      have h2 := neg_abs_le (inner ℝ (sec t - (δ:ℂ)*deriv c.γ t) (deriv c.γ t))
      linarith
    have hb2 : ‖sec t - (δ:ℂ)*deriv c.γ t‖ * ‖deriv c.γ t‖ ≤ (ε*δ) * M :=
      mul_le_mul hshift (hM_le t) (norm_nonneg _) (le_of_lt (by positivity : 0 < ε*δ))
    have hsplit : inner ℝ (sec t) (deriv c.γ t)
        = inner ℝ (sec t - (δ:ℂ)*deriv c.γ t) (deriv c.γ t)
          + inner ℝ ((δ:ℂ)*deriv c.γ t) (deriv c.γ t) := by
      conv_lhs => rw [← sub_add_cancel (sec t) ((δ:ℂ)*deriv c.γ t)]
      rw [inner_add_left]
    have h2 : inner ℝ ((δ:ℂ)*deriv c.γ t) (deriv c.γ t) = δ * ‖deriv c.γ t‖^2 := by
      rw [← Complex.real_smul, inner_smul_left, real_inner_self_eq_norm_sq]
      simp
    rw [hsplit, h2]
    have h3 : δ * m^2 ≤ δ * ‖deriv c.γ t‖^2 := by
      have hsq : m^2 ≤ ‖deriv c.γ t‖^2 := by
        nlinarith [hm_le t, hm_pos, norm_nonneg (deriv c.γ t)]
      nlinarith [hδ_pos]
    have hεδM : (ε*δ) * M = δ * (m^2/2) := by
      rw [hεdef]; field_simp; try ring
    linarith [hb1, hb2, h3, hεδM]
  have hsec_nz : ∀ t : ℝ, sec t ≠ 0 := by
    intro t hzero
    have hh := hInner t
    rw [hzero, inner_zero_left] at hh
    have : 0 < (m^2/2) * δ := by positivity
    linarith
  set v : ℝ → ℂ := fun t => Complex.I * (sec t / ((‖sec t‖ : ℝ) : ℂ)) with hv
  have hv_per : Function.Periodic v (2 * Real.pi) := by
    intro t
    simp only [hv]
    rw [hsec_per t]
  have hv_cd : ContDiff ℝ 1 v := by
    rw [hv]
    have hnorm : ContDiff ℝ 1 (fun t => ‖sec t‖) :=
      hsec_cd.norm ℝ (fun t => hsec_nz t)
    have hcast : ContDiff ℝ 1 (fun t => ((‖sec t‖ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hnorm
    have hne : ∀ t, ((‖sec t‖ : ℝ) : ℂ) ≠ 0 := by
      intro t
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact norm_ne_zero_iff.mpr (hsec_nz t)
    have hinv : ContDiff ℝ 1 (fun t => (((‖sec t‖ : ℝ) : ℂ))⁻¹) := hcast.inv hne
    have hmain : ContDiff ℝ 1
        (fun t => Complex.I * (sec t * (((‖sec t‖ : ℝ) : ℂ))⁻¹)) :=
      (contDiff_const (c := Complex.I)).mul (hsec_cd.mul hinv)
    simpa only [div_eq_mul_inv] using hmain
  have hv_unit : ∀ t : ℝ, ‖v t‖ = 1 := by
    intro t
    simp only [hv]
    rw [norm_mul, Complex.norm_I, one_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr (hsec_nz t))
  have hInner_div : ∀ t : ℝ, m^2/(2*M) ≤ inner ℝ (sec t) (deriv c.γ t) / ‖sec t‖ := by
    intro t
    have hnpos : 0 < ‖sec t‖ := norm_pos_iff.mpr (hsec_nz t)
    rw [le_div_iff₀ hnpos]
    have h1 : m^2/(2*M) * ‖sec t‖ ≤ m^2/(2*M) * (M*δ) :=
      mul_le_mul_of_nonneg_left (hMVT_up t) (by positivity)
    have h2 : m^2/(2*M) * (M*δ) = (m^2/2)*δ := by
      field_simp
      try ring
    linarith [hInner t]
  have hv_trans : ∀ t : ℝ, (m^2/(2*M^2)) * ‖deriv c.γ t‖
      ≤ |detV (deriv c.γ t) (v t)| := by
    intro t
    have hdet : detV (deriv c.γ t) (v t) = inner ℝ (sec t) (deriv c.γ t) / ‖sec t‖ := by
      rw [hv, detV_I_mul, inner_div_ofReal_norm, real_inner_comm]
    have hpos : 0 < inner ℝ (sec t) (deriv c.γ t) / ‖sec t‖ := by
      have h1 := hInner_div t
      have h3 : 0 < m^2/(2*M) := by positivity
      linarith
    rw [hdet, abs_of_pos hpos]
    have h1 : (m^2/(2*M^2)) * ‖deriv c.γ t‖ ≤ m^2/(2*M) := by
      have hle := hM_le t
      have hid : m^2/(2*M^2) * M = m^2/(2*M) := by field_simp; try ring
      have hc : 0 ≤ m^2/(2*M^2) := by positivity
      nlinarith [hle, hid, hc]
    linarith [hInner_div t]
  obtain ⟨L, hL_pos, hL_lip⟩ := exists_lipschitz_of_periodic_contDiff hv_per hv_cd
  exact ⟨v, m^2/(2*M^2), L, by positivity, hL_pos, hv_per, hv_cd,
    ⟨hv_unit, hv_trans⟩, hL_lip⟩

end

end Work.Smooth.JordanSeparation
