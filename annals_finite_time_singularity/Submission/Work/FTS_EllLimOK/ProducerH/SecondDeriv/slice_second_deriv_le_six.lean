import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.SliceBound.slice_second_deriv_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.SecondDeriv

open Set Real Filter
open scoped Real Topology

open Work.FTS_EllLimOK.ProducerH.SliceBound

local notation "sliceI" => Set.Ioo 0 (π / 2)

/-!
# The angular slice second-derivative bound with the sharp constant `6`

We specialise the argument of `Work.FTS_EllLimOK.ProducerH.SliceBound.slice_second_deriv_le`
(the `∃ K` version) to the explicit constant `K = 6`.

With `f := sin(2θ)/2 · S' + S` and `V := f - 2 S cos²θ`, the ODE

  `S'' = tan θ · S' + cos(θ)⁻² · S - 6 S - G`

is equivalent to `V' = tan θ (V - G cos²θ)`.  The monotone barriers
`Z = 3 V cos θ - M cos³θ` and `Zt = 3 V cos θ + M cos³θ` then force
`|V| ≤ (M/3) cos²θ`, and since `S'' = V / cos²θ - 4 S - G` we get
`|S''| ≤ M/3 + 4 M + M ≤ 6 M`.
-/

theorem slice_second_deriv_le_six {S G : ℝ → ℝ}
    (hS : ContDiffOn ℝ 2 S (Set.Ioo 0 (Real.pi / 2)))
    (heq : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (deriv S) θ
        = Real.tan θ * deriv S θ + ((Real.cos θ) ^ 2)⁻¹ * S θ - 6 * S θ - G θ)
    {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |Real.sin (2 * θ) / 2 * deriv S θ + S θ| ≤ M)
    (hSb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |S θ| ≤ M)
    (hGb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |G θ| ≤ M) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv (deriv S) θ| ≤ 6 * M := by
  have hIopen : IsOpen sliceI := isOpen_Ioo
  have hIconv : Convex ℝ sliceI := convex_Ioo 0 (π / 2)
  have hIint : interior sliceI = sliceI := hIopen.interior_eq
  have hS1 : ContDiffOn ℝ 1 (deriv S) sliceI := hS.deriv_of_isOpen hIopen (by norm_num)
  have hSd : ∀ θ ∈ sliceI, HasDerivAt S (deriv S θ) θ := fun θ hθ =>
    ((hS.contDiffAt (hIopen.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
  have hSd2 : ∀ θ ∈ sliceI, HasDerivAt (deriv S) (deriv (deriv S) θ) θ := fun θ hθ =>
    ((hS1.contDiffAt (hIopen.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
  have hcospos : ∀ θ ∈ sliceI, 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by have := hθ.1; linarith [Real.pi_pos], hθ.2⟩
  have hcosne : ∀ θ ∈ sliceI, Real.cos θ ≠ 0 := fun θ hθ => ne_of_gt (hcospos θ hθ)
  -- derivative of `sliceV S`
  have hVd : ∀ θ ∈ sliceI,
      HasDerivAt (sliceV S) (Real.tan θ * (sliceV S θ - G θ * (Real.cos θ) ^ 2)) θ := by
    intro θ hθ
    have h1 : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) / 2) (Real.cos (2 * θ)) θ := by
      have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      have h : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ)) (Real.cos (2 * θ) * 2) θ :=
        (Real.hasDerivAt_sin (2 * θ)).comp θ h2
      convert h.div_const 2 using 1
      ring
    have hF : HasDerivAt (fun θ : ℝ => Real.sin (2 * θ) / 2 * deriv S θ + S θ)
        (Real.cos (2 * θ) * deriv S θ + Real.sin (2 * θ) / 2 * deriv (deriv S) θ
          + deriv S θ) θ :=
      ((h1.mul (hSd2 θ hθ)).add (hSd θ hθ)).congr_deriv (by ring)
    have hc2 : HasDerivAt (fun θ : ℝ => (Real.cos θ) ^ 2) (2 * Real.cos θ * (-Real.sin θ)) θ :=
      ((Real.hasDerivAt_cos θ).pow 2).congr_deriv (by norm_num)
    have hG2 : HasDerivAt (fun θ : ℝ => 2 * S θ * (Real.cos θ) ^ 2)
        (2 * deriv S θ * (Real.cos θ) ^ 2 + 2 * S θ * (2 * Real.cos θ * (-Real.sin θ))) θ :=
      (((hSd θ hθ).const_mul 2).mul hc2).congr_deriv (by ring)
    have hraw := hF.sub hG2
    have hfun : ((fun θ : ℝ => Real.sin (2 * θ) / 2 * deriv S θ + S θ)
        - (fun θ : ℝ => 2 * S θ * (Real.cos θ) ^ 2)) = sliceV S := by
      funext x
      simp only [Pi.sub_apply, sliceV, sliceF]
    rw [hfun] at hraw
    refine hraw.congr_deriv ?_
    simp only [sliceV, sliceF]
    rw [heq θ hθ, Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
    field_simp [hcosne θ hθ]
    ring
  -- derivative of `sliceZ S M`
  have hZd : ∀ θ ∈ sliceI,
      HasDerivAt (sliceZ S M) (3 * Real.sin θ * (Real.cos θ) ^ 2 * (M - G θ)) θ := by
    intro θ hθ
    have h3V : HasDerivAt (fun θ : ℝ => 3 * sliceV S θ)
        (3 * (Real.tan θ * (sliceV S θ - G θ * (Real.cos θ) ^ 2))) θ :=
      (hVd θ hθ).const_mul 3
    have hprod : HasDerivAt (fun θ : ℝ => 3 * sliceV S θ * Real.cos θ)
        (3 * (Real.tan θ * (sliceV S θ - G θ * (Real.cos θ) ^ 2)) * Real.cos θ
          + 3 * sliceV S θ * (-Real.sin θ)) θ :=
      ((h3V.mul (Real.hasDerivAt_cos θ)).congr_deriv (by ring))
    have hc3 : HasDerivAt (fun θ : ℝ => (Real.cos θ) ^ 3)
        (3 * (Real.cos θ) ^ 2 * (-Real.sin θ)) θ :=
      ((Real.hasDerivAt_cos θ).pow 3).congr_deriv (by ring)
    have hMc : HasDerivAt (fun θ : ℝ => M * (Real.cos θ) ^ 3)
        (M * (3 * (Real.cos θ) ^ 2 * (-Real.sin θ))) θ := hc3.const_mul M
    have hraw := hprod.sub hMc
    have hfun : ((fun θ : ℝ => 3 * sliceV S θ * Real.cos θ)
        - (fun θ : ℝ => M * (Real.cos θ) ^ 3)) = sliceZ S M := by
      funext x
      simp only [Pi.sub_apply, sliceZ]
    rw [hfun] at hraw
    refine hraw.congr_deriv ?_
    simp only [sliceV, sliceF]
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp [hcosne θ hθ]
    ring
  -- derivative of `sliceZt S M`
  have hZtd : ∀ θ ∈ sliceI,
      HasDerivAt (sliceZt S M) (-(3 * Real.sin θ * (Real.cos θ) ^ 2 * (G θ + M))) θ := by
    intro θ hθ
    have h3V : HasDerivAt (fun θ : ℝ => 3 * sliceV S θ)
        (3 * (Real.tan θ * (sliceV S θ - G θ * (Real.cos θ) ^ 2))) θ :=
      (hVd θ hθ).const_mul 3
    have hprod : HasDerivAt (fun θ : ℝ => 3 * sliceV S θ * Real.cos θ)
        (3 * (Real.tan θ * (sliceV S θ - G θ * (Real.cos θ) ^ 2)) * Real.cos θ
          + 3 * sliceV S θ * (-Real.sin θ)) θ :=
      ((h3V.mul (Real.hasDerivAt_cos θ)).congr_deriv (by ring))
    have hc3 : HasDerivAt (fun θ : ℝ => (Real.cos θ) ^ 3)
        (3 * (Real.cos θ) ^ 2 * (-Real.sin θ)) θ :=
      ((Real.hasDerivAt_cos θ).pow 3).congr_deriv (by ring)
    have hMc : HasDerivAt (fun θ : ℝ => M * (Real.cos θ) ^ 3)
        (M * (3 * (Real.cos θ) ^ 2 * (-Real.sin θ))) θ := hc3.const_mul M
    have hraw := hprod.add hMc
    have hfun : ((fun θ : ℝ => 3 * sliceV S θ * Real.cos θ)
        + (fun θ : ℝ => M * (Real.cos θ) ^ 3)) = sliceZt S M := by
      funext x
      simp only [Pi.add_apply, sliceZt]
    rw [hfun] at hraw
    refine hraw.congr_deriv ?_
    simp only [sliceV, sliceF]
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp [hcosne θ hθ]
    ring
  have hZcont : ContinuousOn (sliceZ S M) sliceI :=
    DifferentiableOn.continuousOn (fun θ hθ => (hZd θ hθ).differentiableAt.differentiableWithinAt)
  have hZmono : MonotoneOn (sliceZ S M) sliceI := by
    refine monotoneOn_of_deriv_nonneg hIconv hZcont ?_ ?_
    · intro x hx
      rw [hIint] at hx
      exact (hZd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [hIint] at hx
      rw [(hZd x hx).deriv]
      have hsinx : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
      have hGle : G x ≤ M := (abs_le.mp (hGb x hx)).2
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsinx) (sq_nonneg _))
        (by linarith)
  have hZtcont : ContinuousOn (sliceZt S M) sliceI :=
    DifferentiableOn.continuousOn (fun θ hθ => (hZtd θ hθ).differentiableAt.differentiableWithinAt)
  have hZtanti : AntitoneOn (sliceZt S M) sliceI := by
    refine antitoneOn_of_deriv_nonpos hIconv hZtcont ?_ ?_
    · intro x hx
      rw [hIint] at hx
      exact (hZtd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [hIint] at hx
      rw [(hZtd x hx).deriv]
      have hsinx : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hx.1, by linarith [hx.2, Real.pi_pos]⟩
      have hGle : -M ≤ G x := (abs_le.mp (hGb x hx)).1
      have hnonneg : 0 ≤ 3 * Real.sin x * (Real.cos x) ^ 2 * (G x + M) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hsinx) (sq_nonneg _)) (by linarith)
      linarith
  -- upper bound on `sliceV`
  have hVupper : ∀ θ ∈ sliceI, sliceV S θ ≤ M / 3 * (Real.cos θ) ^ 2 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨θ₀, hθ₀, hgt⟩ := hcon
    refine mode_contradiction_up (V := sliceV S) (Z₀ := sliceZ S M θ₀) (θ₀ := θ₀) hM hθ₀ ?_ ?_ ?_
    · have hcp : 0 < Real.cos θ₀ := hcospos θ₀ hθ₀
      have h3 : 0 < 3 * sliceV S θ₀ - M * (Real.cos θ₀) ^ 2 := by nlinarith [hgt]
      have hthis : 0 < (3 * sliceV S θ₀ - M * (Real.cos θ₀) ^ 2) * Real.cos θ₀ :=
        mul_pos h3 hcp
      have hZeq : (3 * sliceV S θ₀ - M * (Real.cos θ₀) ^ 2) * Real.cos θ₀
          = sliceZ S M θ₀ := by simp only [sliceZ]; ring
      rwa [hZeq] at hthis
    · intro θ hθ hle
      exact hZmono hθ₀ hθ hle
    · intro θ hθ
      have hfm : sliceF S θ ≤ M := (abs_le.mp (hf θ hθ)).2
      have hSm : -M ≤ S θ := (abs_le.mp (hSb θ hθ)).1
      have hVeq : sliceV S θ = sliceF S θ - 2 * S θ * (Real.cos θ) ^ 2 := rfl
      rw [hVeq]
      have hstep : -2 * S θ * (Real.cos θ) ^ 2 ≤ 2 * M * (Real.cos θ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hSm (by positivity : (0:ℝ) ≤ 2 * (Real.cos θ) ^ 2)
        linarith
      linarith
  -- lower bound on `sliceV`
  have hVlower : ∀ θ ∈ sliceI, -(M / 3) * (Real.cos θ) ^ 2 ≤ sliceV S θ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨θ₀, hθ₀, hlt⟩ := hcon
    refine mode_contradiction_down (V := sliceV S) (Z₀ := sliceZt S M θ₀) (θ₀ := θ₀) hM hθ₀ ?_ ?_ ?_
    · have hcp : 0 < Real.cos θ₀ := hcospos θ₀ hθ₀
      have h3 : 3 * sliceV S θ₀ + M * (Real.cos θ₀) ^ 2 < 0 := by nlinarith [hlt]
      have hthis : (3 * sliceV S θ₀ + M * (Real.cos θ₀) ^ 2) * Real.cos θ₀ < 0 :=
        mul_neg_of_neg_of_pos h3 hcp
      have hZeq : (3 * sliceV S θ₀ + M * (Real.cos θ₀) ^ 2) * Real.cos θ₀
          = sliceZt S M θ₀ := by simp only [sliceZt]; ring
      rwa [hZeq] at hthis
    · intro θ hθ hle
      exact hZtanti hθ₀ hθ hle
    · intro θ hθ
      have hfm : -M ≤ sliceF S θ := (abs_le.mp (hf θ hθ)).1
      have hSm : S θ ≤ M := (abs_le.mp (hSb θ hθ)).2
      have hVeq : sliceV S θ = sliceF S θ - 2 * S θ * (Real.cos θ) ^ 2 := rfl
      rw [hVeq]
      have hstep : -2 * M * (Real.cos θ) ^ 2 ≤ -2 * S θ * (Real.cos θ) ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hSm (by positivity : (0:ℝ) ≤ 2 * (Real.cos θ) ^ 2)
        linarith
      linarith
  -- final assembly
  intro θ hθ
  have hW : deriv (deriv S) θ = sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ - G θ := by
    rw [heq θ hθ, sliceV, sliceF, Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp [hcosne θ hθ]
    ring
  rw [hW]
  have hc2pos : 0 < (Real.cos θ) ^ 2 := pow_pos (hcospos θ hθ) 2
  have hc2inv : (Real.cos θ) ^ 2 * ((Real.cos θ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hc2pos)
  have hW1 : sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ ≤ M / 3 := by
    have h := mul_le_mul_of_nonneg_right (hVupper θ hθ) (inv_nonneg.mpr hc2pos.le)
    rwa [mul_assoc, hc2inv, mul_one] at h
  have hW2 : -(M / 3) ≤ sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ := by
    have h := mul_le_mul_of_nonneg_right (hVlower θ hθ) (inv_nonneg.mpr hc2pos.le)
    rwa [mul_assoc, hc2inv, mul_one] at h
  have hWabs : |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹| ≤ M / 3 := by
    rw [abs_le]
    exact ⟨hW2, hW1⟩
  have h4S : |4 * S θ| ≤ 4 * M := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    linarith [hSb θ hθ]
  calc |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ - G θ|
      ≤ |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹| + |4 * S θ| + |G θ| := by
        have h2 : |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ|
            ≤ |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹| + |4 * S θ| := by
          have := abs_sub_le (sliceV S θ * ((Real.cos θ) ^ 2)⁻¹) (0 : ℝ) (4 * S θ)
          simpa using this
        have h1 : |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ - G θ|
            ≤ |sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ| + |G θ| := by
          have := abs_sub_le (sliceV S θ * ((Real.cos θ) ^ 2)⁻¹ - 4 * S θ) (0 : ℝ) (G θ)
          simpa using this
        linarith
    _ ≤ M / 3 + 4 * M + M := by linarith [hWabs, h4S, hGb θ hθ]
    _ ≤ 6 * M := by linarith [hM]

end Work.FTS_EllLimOK.ProducerH.SecondDeriv
