import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs
import Submission.Work.BourgainPlan.Maximal.mst_freeze_lift_pointwise
import Submission.Work.BourgainPlan.Maximal.mst_freeze_fubini

/-!
# The Fourier coefficients of the single-arc error term, frozen at the arc

This module puts the rewriting steps of the freezing estimate together and computes the `m`-th
Fourier coefficient of MST's single-arc error term `mstFreezeFn P J d χ η s k β` (eq. (99) of
Mirek–Stein–Trojan §4.4):

`fourierCoeff (mstFreezeFn …) m = fourier (−m) (iwRep β) · c⁻¹ ∫_0^1 mstHat Ξ ((m + P(2^k σ))/c) dσ`,

where `c = mstScale d χ s` and `Ξ = mstFreezeXi P J β c η` (`w ↦ mstTht … (w/c) · η w`).

Route.
* `fourierCoeff_eq_intervalIntegral` with `a = iwRep β − 1/2` puts the coefficient on the
  fundamental interval centred at the arc `β`;
* `mst_freeze_lift_pointwise` rewrites the integrand there (the profile becomes the average of the
  character `e^{−2πi (x−iwRep β) P(2^k σ)}`, and `fourier (−m)` splits into
  `e^{−2πi m iwRep β} · e^{−2πi m (x−iwRep β)}`);
* the translation `x = iwRep β + u` moves the integral to `(−1/2, 1/2)`;
* `mst_freeze_fubini` swaps the `u`- and `σ`-integrals;
* finally the dilation `w = c u` (`mstHat_dilate_char`) turns the inner integral into
  `c⁻¹ mstHat Ξ ((m + P(2^k σ))/c)`.
-/

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- The character is multiplicative in its second argument. -/
theorem mstFreezeChar_mul (a b t : ℝ) :
    mstFreezeChar a t * mstFreezeChar b t = mstFreezeChar (a + b) t := by
  rw [mstFreezeChar, mstFreezeChar, mstFreezeChar, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `mstHat` written with the character `mstFreezeChar`. -/
theorem mstHat_eq_char (Λ : ℝ → ℂ) (t : ℝ) :
    mstHat Λ t = ∫ u in (-(1 / 2))..(1 / 2), Λ u * mstFreezeChar u t := by
  rw [mstHat_apply]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  refine congrArg (fun z => Λ u * Complex.exp z) ?_
  push_cast
  ring

/-- **The dilation dictionary of the freezing estimate**, in the `mstFreezeChar` normalization. -/
theorem mstHat_dilate_char (Λ : ℝ → ℂ) (c t : ℝ) (hc : 1 ≤ c)
    (hΛ : ∀ w : ℝ, 1 / 2 < |w| → Λ w = 0) :
    mstHat Λ (t / c) = c * ∫ u in (-(1 / 2))..(1 / 2), Λ (c * u) * mstFreezeChar u t := by
  have hcpos : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc
  have hcne : c ≠ 0 := hcpos.ne'
  -- extend the domain of integration of `mstHat Λ (t/c)` to `(-c/2, c/2)`
  have htrunc : (∫ w in (-(c / 2))..(c / 2), Λ w * mstFreezeChar w (t / c))
      = ∫ w in (-(1 / 2))..(1 / 2), Λ w * mstFreezeChar w (t / c) := by
    refine intervalIntegral_eq_of_support (r := 1 / 2) (R := c / 2) (by norm_num) (by linarith) ?_
    intro x hx
    rw [hΛ x hx, zero_mul]
  -- substitute `w = c u`
  have hcomp : (∫ u in (-(1 / 2))..(1 / 2), Λ (c * u) * mstFreezeChar u t)
      = c⁻¹ • ∫ w in (-(c / 2))..(c / 2), Λ w * mstFreezeChar w (t / c) := by
    have h := intervalIntegral.integral_comp_mul_left (a := (-(1 / 2) : ℝ)) (b := (1 / 2 : ℝ))
      (c := c) (f := fun w : ℝ => Λ w * mstFreezeChar w (t / c)) hcne
    rw [show c * (-(1 / 2) : ℝ) = -(c / 2) by ring,
        show c * (1 / 2 : ℝ) = c / 2 by ring] at h
    rw [← h]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    refine congrArg (fun z => Λ (c * u) * Complex.exp z) ?_
    rw [show (2 * Real.pi * ((c * u) * (t / c)) : ℝ) = 2 * Real.pi * (u * t) by
      field_simp]
  rw [hcomp, htrunc, ← mstHat_eq_char]
  have h1 : ((c : ℝ) : ℂ) * (c⁻¹ • mstHat Λ (t / c)) = mstHat Λ (t / c) := by
    rw [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc,
      mul_inv_cancel₀ (by
        intro h
        exact hcne (Complex.ofReal_inj.mp (by simpa using h))), one_mul]
  rw [h1]

/-- **The Fourier coefficient of the single-arc error term.** -/
theorem mstFreezeFn_fourierCoeff (P : Polynomial ℤ) (J d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hηc : ContDiff ℝ 2 η) (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (s k : ℕ) (hc1 : 1 ≤ mstScale d χ s) (β : Circ) (m : ℤ) :
    fourierCoeff (mstFreezeFn P J d χ η s k β) m
      = (fourier (-m)) (((iwRep β) : ℝ) : Circ) *
        ((((mstScale d χ s : ℝ) : ℂ))⁻¹ *
          ∫ σ in (0 : ℝ)..1, mstHat (mstFreezeXi P J β (mstScale d χ s) η)
            (((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ)) / mstScale d χ s)) := by
  have hcpos : 0 < mstScale d χ s := mstScale_pos d χ s
  have hcne : mstScale d χ s ≠ 0 := hcpos.ne'
  have hcne' : ((mstScale d χ s : ℝ) : ℂ) ≠ 0 := by
    intro h
    exact hcne (Complex.ofReal_inj.mp (by simpa using h))
  have hΛ0 : ∀ w : ℝ, 1 / 2 < |w| → mstFreezeXi P J β (mstScale d χ s) η w = 0 := by
    intro w hw
    rw [mstFreezeXi_apply, hη0 w hw, mul_zero]
  -- Step 1 : the coefficient as an integral over the interval centred at the arc
  have h1 : fourierCoeff (mstFreezeFn P J d χ η s k β) m
      = ∫ x in (iwRep β - 1 / 2)..(iwRep β + 1 / 2),
          (fourier (-m)) ((x : ℝ) : Circ) * mstFreezeFn P J d χ η s k β ((x : ℝ) : Circ) := by
    rw [fourierCoeff_eq_intervalIntegral (T := 1) _ m (iwRep β - 1 / 2)]
    rw [show iwRep β - 1 / 2 + 1 = iwRep β + 1 / 2 by ring,
      show ((1 : ℝ) / 1) = 1 by norm_num, one_smul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [smul_eq_mul]
  -- Step 2 : the integrand read on the fundamental interval
  set G : ℝ → ℂ := fun x => mstFreezeChar (iwRep β) (m : ℝ) *
      (mstFreezeChar (x - iwRep β) (m : ℝ) *
        (mstTht P J β (iwRep β) (x - iwRep β) *
          ((∫ σ in (0 : ℝ)..1, mstFreezeChar (x - iwRep β)
              ((toRealPoly P).eval ((2 ^ k : ℝ) * σ))) *
            η (mstScale d χ s * (x - iwRep β))))) with hG
  have hstep1 : (∫ x in (iwRep β - 1 / 2)..(iwRep β + 1 / 2),
        (fourier (-m)) ((x : ℝ) : Circ) * mstFreezeFn P J d χ η s k β ((x : ℝ) : Circ))
      = ∫ x in (iwRep β - 1 / 2)..(iwRep β + 1 / 2), G x := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    have hmem : x ∈ Set.Ioc (iwRep β - 1 / 2) (iwRep β + 1 / 2) := by
      rwa [Set.uIoc_of_le (by linarith : iwRep β - 1 / 2 ≤ iwRep β + 1 / 2)] at hx
    rw [hG]
    simp only
    rw [mst_freeze_lift_pointwise P J d χ η s k β x hmem, fourier_neg_coe_eq]
    rw [show mstFreezeChar x (m : ℝ)
        = mstFreezeChar (iwRep β) (m : ℝ) * mstFreezeChar (x - iwRep β) (m : ℝ) by
      rw [mstFreezeChar_mul, show iwRep β + (x - iwRep β) = x by ring]]
    simp only [mstFreezeChar]
    ring
  -- Step 3 : the translation `x = iwRep β + u`
  have hstep2 : (∫ x in (iwRep β - 1 / 2)..(iwRep β + 1 / 2), G x)
      = ∫ u in (-(1 / 2))..(1 / 2), G (u + iwRep β) := by
    have h := intervalIntegral.integral_comp_add_right (a := (-(1 / 2) : ℝ)) (b := (1 / 2 : ℝ))
      (f := G) (d := iwRep β)
    rw [show (-(1 / 2) : ℝ) + iwRep β = iwRep β - 1 / 2 by ring,
      show (1 / 2 : ℝ) + iwRep β = iwRep β + 1 / 2 by ring] at h
    exact h.symm
  -- Step 4 : the integrand in the offset variable
  set H : ℝ → ℂ := fun u => mstTht P J β (iwRep β) u * η (mstScale d χ s * u) *
      (∫ σ in (0 : ℝ)..1, mstFreezeChar u ((toRealPoly P).eval ((2 ^ k : ℝ) * σ))) *
      mstFreezeChar u (m : ℝ) with hH
  have hstep3 : (∫ u in (-(1 / 2))..(1 / 2), G (u + iwRep β))
      = mstFreezeChar (iwRep β) (m : ℝ) * ∫ u in (-(1 / 2))..(1 / 2), H u := by
    rw [hG, hH]
    simp only [add_sub_cancel_right]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    ring
  -- Step 5 : Fubini
  have hstep4 : (∫ u in (-(1 / 2))..(1 / 2), H u)
      = ∫ σ in (0 : ℝ)..1, ∫ u in (-(1 / 2))..(1 / 2), mstTht P J β (iwRep β) u *
          η (mstScale d χ s * u) *
          mstFreezeChar u ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)) := by
    rw [hH]
    have hf := mst_freeze_fubini P J β η hηc (mstScale d χ s) k m
    simpa only [mstFreezeChar] using hf
  -- Step 6 : the dilation, one `σ` at a time
  have hstep5 : (∫ σ in (0 : ℝ)..1, ∫ u in (-(1 / 2))..(1 / 2), mstTht P J β (iwRep β) u *
          η (mstScale d χ s * u) *
          mstFreezeChar u ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)))
      = ((mstScale d χ s : ℝ) : ℂ)⁻¹ *
        ∫ σ in (0 : ℝ)..1, mstHat (mstFreezeXi P J β (mstScale d χ s) η)
          (((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ)) / mstScale d χ s) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun σ _ => ?_)
    rw [show ((m : ℝ) + (toRealPoly P).eval ((2 ^ k : ℝ) * σ))
        = ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)) by ring]
    have hd := mstHat_dilate_char (mstFreezeXi P J β (mstScale d χ s) η) (mstScale d χ s)
      ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)) hc1 hΛ0
    have hid : (∫ u in (-(1 / 2))..(1 / 2), mstFreezeXi P J β (mstScale d χ s) η
          (mstScale d χ s * u) * mstFreezeChar u
            ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)))
        = ∫ u in (-(1 / 2))..(1 / 2), mstTht P J β (iwRep β) u * η (mstScale d χ s * u) *
            mstFreezeChar u ((toRealPoly P).eval ((2 ^ k : ℝ) * σ) + (m : ℝ)) := by
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      rw [mstFreezeXi_apply,
        show (mstScale d χ s * u) / mstScale d χ s = u by field_simp]
    rw [hd, hid, inv_mul_cancel_left₀ hcne']
  rw [h1, hstep1, hstep2, hstep3, hstep4, hstep5]
  rw [fourier_neg_coe_eq]

end

end Work.BourgainPlan.Maximal
