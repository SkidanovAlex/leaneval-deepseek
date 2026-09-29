import Mathlib
import Submission.Work.CNum.C2_clockwise
import Submission.Work.CNum.C2_mem
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.ArcsinChord
import Submission.Work.CNum.C2PsiRangeClosed
import Submission.Work.CNum.PsiChordGeom
import Submission.Work.CPsi.psiC_continuous

/-!
# `Work.CNum.PsiChord`

The chord bound for `ψ_C` on the large arc `C₂` of the unit circle: for
`alpR ≤ θ₁ ≤ θ₂ ≤ 2π - alpR` one has

`Ψ(θ₁/2) - Ψ(θ₂/2) ≤ (143/115)c + ((143/115)c)³/12 + ((143/115)c)⁵/160`,  `Ψ = C2Psi`,

where `c = ‖ψ_C(e^{iθ₂}) - ψ_C(e^{iθ₁})‖`.  This is the `C₂`-arc counterpart of the
`C₁`-arc bound `Work.CNum.PhiChord`.

With `u = |Ψ(θ₁/2) - Ψ(θ₂/2)|/2` the geometry of the circle `C₂` (centre `cenC2`, radius
`√rho2sq = 115/143`, argument `Ψ(θ/2)`) gives the exact chord `c = (230/143)·sin u`, and
`|Ψ| ≤ alpR/2` on the whole closed arc gives `u ≤ alpR/2`, hence `sin u ≤ 429/629`.  The
elementary bound `2u ≤ 2 sin u + (2/3) sin³u + (1/5) sin⁵u` for such `u` (proved below by
monotonicity of `Fp u = 2 sin u + (2/3)sin³u + (1/5)sin⁵u - 2u`, whose derivative
`Fp' u = cos u (2 + 2 sin²u + sin⁴u) - 2` is non-negative there) then converts the chord
bound into the statement: `sin u = (143/230)c` turns `2 sin u + (2/3)sin³u + (1/5)sin⁵u`
into `(143/115)c + ((143/115)c)³/12 + ((143/115)c)⁵/160` exactly.
-/

namespace Work.CNum

set_option autoImplicit false

open Complex

/-! ## 1. The closed-arc polar form of `Vof` -/

/-- `ψ_C = (3/4)·Wfun` (the definitional identity `√ = (·)^{1/2}`). -/
private lemma psiC_eq_smul_Wfun' (z : ℂ) :
    Submission.CDTPlan.psiC z = (3 / 4 : ℂ) * Wfun z := by
  unfold Submission.CDTPlan.psiC Submission.CDTPlan.lune Wfun Ra AR BR dR cR
  rw [Complex.sqrt]
  push_cast
  ring_nf

/-- `Vof` in terms of `ψ_C`: `Vof θ = (ψ_C (e^{iθ}) - cenC2)/√rho2sq`. -/
private lemma Vof_eq_psiC (θ : ℝ) :
    Vof θ = (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) - (cenC2 : ℂ)) /
      ((Real.sqrt rho2sq : ℝ) : ℂ) := by
  rw [Vof, psiC_eq_smul_Wfun']

/-- The polar form `Vof θ = -exp (I · Ψ(θ/2))` on the **closed** arc `[alpR, 2π - alpR]`:
both sides are continuous there and agree on the dense open arc (`C2_Vof_explicit`,
`C2_ratio_eq`). -/
private lemma Vof_eq_exp_closed {θ : ℝ} (h1 : alpR ≤ θ) (h2 : θ ≤ 2 * Real.pi - alpR) :
    Vof θ = -Complex.exp (Complex.I * (C2Psi (θ / 2) : ℂ)) := by
  have hsub : Set.Ioo alpR (2 * Real.pi - alpR) ⊆ Set.Icc alpR (2 * Real.pi - alpR) :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hne : alpR ≠ 2 * Real.pi - alpR := by
    intro h
    have := alpR_lt_pi
    linarith
  have hclosure : Set.Icc alpR (2 * Real.pi - alpR) ⊆
      closure (Set.Ioo alpR (2 * Real.pi - alpR)) := by
    rw [closure_Ioo hne]
  have hEq : Set.EqOn (fun θ : ℝ => Vof θ)
      (fun θ : ℝ => -Complex.exp (Complex.I * (C2Psi (θ / 2) : ℂ)))
      (Set.Ioo alpR (2 * Real.pi - alpR)) := by
    intro θ hθ
    change Vof θ = -Complex.exp (Complex.I * (C2Psi (θ / 2) : ℂ))
    rw [C2_Vof_explicit hθ, C2_ratio_eq hθ]
  have hcont₁ : ContinuousOn (fun θ : ℝ => Vof θ) (Set.Icc alpR (2 * Real.pi - alpR)) := by
    rw [show (fun θ : ℝ => Vof θ) = (fun θ : ℝ =>
        (Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ : ℂ))) - (cenC2 : ℂ)) /
          ((Real.sqrt rho2sq : ℝ) : ℂ)) from funext Vof_eq_psiC]
    refine ContinuousOn.div_const ?_ _
    refine ContinuousOn.sub ?_ continuousOn_const
    refine Work.CPsi.psiC_continuous.comp ?_ ?_
    · fun_prop
    · intro θ _
      simp [Metric.mem_closedBall, Complex.norm_exp_I_mul_ofReal]
  have hcont₂ : ContinuousOn (fun θ : ℝ => -Complex.exp (Complex.I * (C2Psi (θ / 2) : ℂ)))
      (Set.Icc alpR (2 * Real.pi - alpR)) := by
    apply Continuous.continuousOn
    unfold C2Psi
    fun_prop
  exact Set.EqOn.of_subset_closure hEq hcont₁ hcont₂ hsub hclosure ⟨h1, h2⟩

/-! ## 2. The elementary bound `2u ≤ 2 sin u + (2/3) sin³u + (1/5) sin⁵u` on `[0, alpR/2]` -/

/-- `Fp u = 2 sin u + (2/3) sin³u + (1/5) sin⁵u - 2u`. -/
private noncomputable def Fp (u : ℝ) : ℝ :=
  2 * Real.sin u + (2 / 3) * Real.sin u ^ 3 + Real.sin u ^ 5 / 5 - 2 * u

/-- `Fp' u = cos u (2 + 2 sin²u + sin⁴u) - 2`. -/
private lemma hasDerivAt_Fp (u : ℝ) :
    HasDerivAt Fp (Real.cos u * (2 + 2 * Real.sin u ^ 2 + Real.sin u ^ 4) - 2) u := by
  change HasDerivAt (fun y : ℝ => 2 * Real.sin y + (2 / 3) * Real.sin y ^ 3
    + Real.sin y ^ 5 / 5 - 2 * y)
    (Real.cos u * (2 + 2 * Real.sin u ^ 2 + Real.sin u ^ 4) - 2) u
  have ha : HasDerivAt (fun y : ℝ => 2 * Real.sin y) (2 * Real.cos u) u := by
    simpa using (Real.hasDerivAt_sin u).const_mul 2
  have hb : HasDerivAt (fun y : ℝ => (2 / 3) * Real.sin y ^ 3)
      (2 * Real.sin u ^ 2 * Real.cos u) u := by
    have h : HasDerivAt (fun y : ℝ => (2 / 3) * Real.sin y ^ 3)
        (2 / 3 * (((3 : ℕ) : ℝ) * Real.sin u ^ (3 - 1) * Real.cos u)) u := by
      simpa using ((Real.hasDerivAt_sin u).pow 3).const_mul (2 / 3)
    have hv : 2 / 3 * (((3 : ℕ) : ℝ) * Real.sin u ^ (3 - 1) * Real.cos u)
        = 2 * Real.sin u ^ 2 * Real.cos u := by ring_nf
    rw [hv] at h
    exact h
  have hc : HasDerivAt (fun y : ℝ => Real.sin y ^ 5 / 5)
      (Real.sin u ^ 4 * Real.cos u) u := by
    have h : HasDerivAt (fun y : ℝ => Real.sin y ^ 5 / 5)
        ((((5 : ℕ) : ℝ) * Real.sin u ^ (5 - 1) * Real.cos u) / 5) u := by
      simpa using ((Real.hasDerivAt_sin u).pow 5).div_const 5
    have hv : ((((5 : ℕ) : ℝ) * Real.sin u ^ (5 - 1) * Real.cos u) / 5)
        = Real.sin u ^ 4 * Real.cos u := by ring_nf
    rw [hv] at h
    exact h
  have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 u := by
    simpa using (hasDerivAt_id u).const_mul 2
  have hsum : HasDerivAt (fun y : ℝ => 2 * Real.sin y + (2 / 3) * Real.sin y ^ 3
      + Real.sin y ^ 5 / 5) (2 * Real.cos u + 2 * Real.sin u ^ 2 * Real.cos u
      + Real.sin u ^ 4 * Real.cos u) u := (ha.add hb).add hc
  have htot := hsum.sub h2
  rw [show 2 * Real.cos u + 2 * Real.sin u ^ 2 * Real.cos u + Real.sin u ^ 4 * Real.cos u - 2
      = Real.cos u * (2 + 2 * Real.sin u ^ 2 + Real.sin u ^ 4) - 2 by ring] at htot
  exact htot

/-- The derivative of `Fp` is non-negative on `[0, alpR/2]`: with `s = sin²u ≤ (429/629)²`,
`(cos u (2 + 2s + s²))² = (1-s)(2+2s+s²)² = 4 + s(4 - 4s² - 3s³ - s⁴) ≥ 4`. -/
private lemma deriv_Fp_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ alpR / 2) :
    0 ≤ Real.cos u * (2 + 2 * Real.sin u ^ 2 + Real.sin u ^ 4) - 2 := by
  have hα2 : alpR / 2 ≤ Real.pi / 2 := by linarith [alpR_lt_pi]
  have hmemα : alpR / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [alpR_pos], hα2⟩
  have hmemu : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [h1, hα2]⟩
  have hsin_le : Real.sin u ≤ 429 / 629 := by
    have h := Real.strictMonoOn_sin.monotoneOn hmemu hmemα h1
    rw [sin_half_alpR] at h
    have hC : C2σ = 429 / 629 := rfl
    rwa [hC] at h
  have hsin0 : 0 ≤ Real.sin u :=
    Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [h1, hα2, alpR_lt_pi, Real.pi_pos]⟩
  have hcos0 : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc hmemu
  set s : ℝ := Real.sin u ^ 2 with hs
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hsle : s ≤ (429 / 629) ^ 2 := by
    rw [hs]
    exact pow_le_pow_left₀ hsin0 hsin_le 2
  have hs1 : s ≤ 1 / 2 := by
    have hc : ((429 : ℝ) / 629) ^ 2 ≤ 1 / 2 := by norm_num
    linarith
  have hs2 : s ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ hs0 hs1 2
    norm_num at h
    linarith
  have h3 : s ^ 3 ≤ s ^ 2 := pow_le_pow_of_le_one hs0 (by linarith) (by norm_num : 2 ≤ 3)
  have h4 : s ^ 4 ≤ s ^ 2 := pow_le_pow_of_le_one hs0 (by linarith) (by norm_num : 2 ≤ 4)
  have hbd : 4 * s ^ 2 + 3 * s ^ 3 + s ^ 4 ≤ 4 := by linarith
  have hkey : 4 ≤ (1 - s) * (2 + 2 * s + s ^ 2) ^ 2 := by
    have hident : (1 - s) * (2 + 2 * s + s ^ 2) ^ 2 - 4
        = s * (4 - 4 * s ^ 2 - 3 * s ^ 3 - s ^ 4) := by ring
    have hnn : 0 ≤ s * (4 - 4 * s ^ 2 - 3 * s ^ 3 - s ^ 4) :=
      mul_nonneg hs0 (by linarith)
    linarith
  have hcos2 : Real.cos u ^ 2 = 1 - s := by
    rw [hs]; linarith [Real.sin_sq_add_cos_sq u]
  have hprod : 4 ≤ (Real.cos u * (2 + 2 * s + s ^ 2)) ^ 2 := by
    rw [mul_pow, hcos2]
    exact hkey
  have hfin : 0 ≤ Real.cos u * (2 + 2 * s + s ^ 2) - 2 := by
    have hfac : 0 ≤ (Real.cos u * (2 + 2 * s + s ^ 2) - 2) *
        (Real.cos u * (2 + 2 * s + s ^ 2) + 2) := by nlinarith [hprod]
    have hpos : 0 < Real.cos u * (2 + 2 * s + s ^ 2) + 2 := by
      have hA : (0 : ℝ) ≤ 2 + 2 * s + s ^ 2 := by positivity
      have hB := mul_nonneg hcos0 hA
      linarith
    exact nonneg_of_mul_nonneg_left hfac hpos
  have hgoal : Real.cos u * (2 + 2 * Real.sin u ^ 2 + Real.sin u ^ 4) - 2
      = Real.cos u * (2 + 2 * s + s ^ 2) - 2 := by rw [hs]; ring
  rw [hgoal]
  exact hfin

/-- `2u ≤ 2 sin u + (2/3) sin³u + (1/5) sin⁵u` for `0 ≤ u ≤ alpR/2`. -/
private lemma sin_chord {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ alpR / 2) :
    2 * u ≤ 2 * Real.sin u + (2 / 3) * Real.sin u ^ 3 + Real.sin u ^ 5 / 5 := by
  have hmono : MonotoneOn Fp (Set.Icc (0 : ℝ) (alpR / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · apply Continuous.continuousOn
      unfold Fp
      fun_prop
    · intro v hv
      rw [interior_Icc] at hv
      exact (hasDerivAt_Fp v).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Icc] at hv
      rw [(hasDerivAt_Fp v).deriv]
      exact deriv_Fp_nonneg (le_of_lt hv.1) (le_of_lt hv.2)
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (alpR / 2) := ⟨le_refl _, by linarith [alpR_pos]⟩
  have hmemu : u ∈ Set.Icc (0 : ℝ) (alpR / 2) := ⟨h0, h1⟩
  have hm : Fp 0 ≤ Fp u := hmono hmem0 hmemu h0
  have hF0 : Fp 0 = 0 := by simp [Fp]
  rw [hF0] at hm
  have : 0 ≤ Fp u := hm
  unfold Fp at this
  linarith

/-! ## 3. The analytic core and the theorem -/

/-- The analytic core, in the variables `Ψ₁, Ψ₂` (the two values of `C2Psi`) and `c` (the
chord): from the chord formula `c = (230/143)|sin((Ψ₁ - Ψ₂)/2)|` and the range
`|Ψᵢ| ≤ alpR/2` deduce the bound. -/
private lemma main_ineq {Ψ₁ Ψ₂ c : ℝ}
    (habs : c = (230 / 143) * |Real.sin ((Ψ₁ - Ψ₂) / 2)|)
    (hr₁ : -(alpR / 2) ≤ Ψ₁) (hr₁' : Ψ₁ ≤ alpR / 2)
    (hr₂ : -(alpR / 2) ≤ Ψ₂) (hr₂' : Ψ₂ ≤ alpR / 2) :
    Ψ₁ - Ψ₂ ≤ (143 / 115) * c + ((143 / 115) * c) ^ 3 / 12 + ((143 / 115) * c) ^ 5 / 160 := by
  set u : ℝ := (|Ψ₁ - Ψ₂| : ℝ) / 2 with hu
  have hu0 : 0 ≤ u := by rw [hu]; exact div_nonneg (abs_nonneg _) (by norm_num)
  have hd : |Ψ₁ - Ψ₂| ≤ alpR := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have hu_le : u ≤ alpR / 2 := by rw [hu]; linarith
  have habs2 : |(Ψ₁ - Ψ₂) / 2| = |Ψ₁ - Ψ₂| / 2 := by simp [abs_div]
  have hu_lt_pi : |(Ψ₁ - Ψ₂) / 2| ≤ Real.pi := by rw [habs2, ← hu]; linarith [hu_le, alpR_lt_pi]
  have hsin_abs : |Real.sin ((Ψ₁ - Ψ₂) / 2)| = Real.sin u := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hu_lt_pi, habs2, hu]
  have hc' : c = (230 / 143) * Real.sin u := by rw [habs, hsin_abs]
  have hsinu : Real.sin u = (143 / 230) * c := by rw [hc']; ring
  have harc := sin_chord hu0 hu_le
  have hle : Ψ₁ - Ψ₂ ≤ 2 * u := by
    rw [hu]
    have h2 : 2 * (|Ψ₁ - Ψ₂| / 2) = |Ψ₁ - Ψ₂| := by ring
    rw [h2]
    exact le_abs_self _
  have hconv : 2 * Real.sin u + (2 / 3) * Real.sin u ^ 3 + Real.sin u ^ 5 / 5
      = (143 / 115) * c + ((143 / 115) * c) ^ 3 / 12 + ((143 / 115) * c) ^ 5 / 160 := by
    rw [hsinu]; ring
  exact le_trans (le_trans hle harc) (le_of_eq hconv)

theorem PsiChord {θ₁ θ₂ : ℝ} (h1 : Work.CNum.alpR ≤ θ₁) (h2 : θ₂ ≤ 2 * Real.pi - Work.CNum.alpR) (h12 : θ₁ ≤ θ₂) : Work.CNum.C2Psi (θ₁ / 2) - Work.CNum.C2Psi (θ₂ / 2) ≤ (143 / 115) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ))) - Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖ + ((143 / 115) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ))) - Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖) ^ 3 / 12 + ((143 / 115) * ‖Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₂ : ℂ))) - Submission.CDTPlan.psiC (Complex.exp (Complex.I * (θ₁ : ℂ)))‖) ^ 5 / 160 := by
  have hchord := PsiChordGeom (θ₁ := θ₁) (θ₂ := θ₂)
    (fun θ a b => Vof_eq_exp_closed a b) h1 h2 h12
  have hr₁ := C2PsiRangeClosed h1 (le_trans h12 h2)
  have hr₂ := C2PsiRangeClosed (le_trans h1 h12) h2
  exact main_ineq hchord hr₁.1 hr₁.2 hr₂.1 hr₂.2

end Work.CNum
