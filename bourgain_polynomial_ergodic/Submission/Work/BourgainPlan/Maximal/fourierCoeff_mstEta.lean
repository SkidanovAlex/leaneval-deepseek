import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs

/-!
# The Fourier coefficients of the MST level bump `η_n`

`Work.BourgainPlan.Maximal.mstEta d χ η n` is the level bump `ξ ↦ η (c_n · iwRep ξ)` on the circle,
where `c_n = mstScale d χ n = 2^{n (d − χ)} ≥ 1` and `iwRep` is the canonical lift
`𝕋 → Ioc (-1/2) (1/2]`.

This file proves the dilation dictionary advertised in `mst_err1_bump_defs`:

`fourierCoeff (mstEta d χ η n) m = c_n⁻¹ · mstHat η (m / c_n)`,

where `mstHat` is the `ℝ`-Fourier transform of `η` in the period-`1` convention.  On the
fundamental interval `Ioc (-1/2) (1/2]` the lift is the identity, so the Haar integral defining the
coefficient becomes `∫_{−1/2}^{1/2} η (c_n x) e^{−2π i m x} dx`; the substitution `x = u/c_n`
turns it into `c_n⁻¹ ∫_{−c_n/2}^{c_n/2} η u e^{−2π i (m/c_n) u} du`, and the support hypothesis
`η u = 0` for `1/2 < |u|` (together with `c_n ≥ 1`) truncates the latter back to the fundamental
interval `[−1/2, 1/2]`.

The support truncation is performed on the *closed* intervals, so that no boundary point is lost:
if `h` vanishes outside `Icc (-r) r` with `0 ≤ r ≤ R`, then the interval integrals over `(-R, R)`
and over `(-r, r)` agree.  (Stating the support on the half-open interval would leave the endpoint
`-r` uncontrolled; comparing the closed intervals first, whose difference from the half-open ones
is a null set, removes the problem entirely.)
-/

open MeasureTheory Set
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Work.BourgainPlan.IonescuWainger

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-- **Truncation to the support.**  If `h` vanishes off the closed interval `Icc (-r) r` and
`0 ≤ r ≤ R`, then the interval integral of `h` over `(-R, R)` equals its interval integral over
`(-r, r)`. -/
private lemma intervalIntegral_eq_of_support {h : ℝ → ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R)
    (hsupp : ∀ x : ℝ, r < |x| → h x = 0) :
    ∫ x in -R..R, h x = ∫ x in -r..r, h x := by
  have hIcc : (Set.Icc (-R) R).indicator h = (Set.Icc (-r) r).indicator h := by
    funext x
    by_cases hx : x ∈ Set.Icc (-r) r
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem (Set.Icc_subset_Icc (by linarith) (by linarith) hx)]
    · by_cases hx2 : x ∈ Set.Icc (-R) R
      · have hx' : r < |x| := by
          rw [Set.mem_Icc] at hx2
          have hc : x < -r ∨ r < x := by
            by_contra hcon
            push Not at hcon
            exact hx ⟨hcon.1, hcon.2⟩
          rcases hc with hc | hc
          · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
          · exact lt_of_lt_of_le hc (le_abs_self x)
        rw [Set.indicator_of_notMem hx, Set.indicator_of_mem hx2, hsupp x hx']
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx2]
  calc ∫ x in -R..R, h x
      = ∫ x in Set.Ioc (-R) R, h x := intervalIntegral.integral_of_le (by linarith)
    _ = ∫ x in Set.Icc (-R) R, h x := (integral_Icc_eq_integral_Ioc).symm
    _ = ∫ x, (Set.Icc (-R) R).indicator h x := (integral_indicator measurableSet_Icc).symm
    _ = ∫ x, (Set.Icc (-r) r).indicator h x := by rw [hIcc]
    _ = ∫ x in Set.Icc (-r) r, h x := integral_indicator measurableSet_Icc
    _ = ∫ x in Set.Ioc (-r) r, h x := integral_Icc_eq_integral_Ioc
    _ = ∫ x in -r..r, h x := (intervalIntegral.integral_of_le (by linarith)).symm

/-- **The change of variable `x ↦ c * x`** on the symmetric interval `[-1/(2c), 1/(2c)]`, which
scales the fundamental interval `[-1/2, 1/2]` by `c`. -/
private lemma intervalIntegral_comp_mul_scale (G : ℝ → ℂ) {c : ℝ} (hc : c ≠ 0) :
    ∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), G (c * x)
      = c⁻¹ • ∫ u in (-(1 / 2) : ℝ)..(1 / 2), G u := by
  have hcomp := intervalIntegral.integral_comp_mul_left
    (a := -(1 / (2 * c))) (b := 1 / (2 * c)) (c := c) G hc
  rw [hcomp]
  have e1 : c * (-(1 / (2 * c))) = -(1 / 2) := by field_simp
  have e2 : c * (1 / (2 * c)) = (1 / 2) := by field_simp
  rw [e1, e2]

/-- The character `fourier (-m)` at a real point, in the exponential form used by `mstHat`. -/
private lemma fourier_neg_coe (m : ℤ) (x : ℝ) :
    fourier (-m) ((x : ℝ) : Circ)
      = Complex.exp ((((-(2 * Real.pi * (m : ℝ) * x)) : ℝ) : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem fourierCoeff_mstEta {d : ℕ} {χ : ℝ} (hχ : χ + 1 ≤ (d : ℝ)) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (n : ℕ) (m : ℤ) :
    fourierCoeff (mstEta d χ η n) m
      = ((mstScale d χ n : ℝ) : ℂ)⁻¹ * mstHat η ((m : ℝ) / mstScale d χ n) := by
  set c : ℝ := mstScale d χ n with hcdef
  have hc1 : 1 ≤ c := by rw [hcdef]; exact one_le_mstScale hχ n
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcne : c ≠ 0 := hcpos.ne'
  -- Step 1: the coefficient as an integral over the fundamental interval, with the bump read
  -- through the canonical lift `iwRep` (which is the identity there).
  have hA : fourierCoeff (T := 1) (mstEta d χ η n) m
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          η (c * x) * Complex.exp ((((-(2 * Real.pi * (m : ℝ) * x)) : ℝ) : ℂ) * Complex.I) := by
    rw [fourierCoeff_eq_intervalIntegral (T := 1) (mstEta d χ η n) m (-(1 / 2))]
    rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]
    rw [show ((1 : ℝ) / 1) = 1 by norm_num]
    rw [one_smul]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [Set.uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hx
    have hx' : x ∈ Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
      rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]; exact hx
    have hrep : iwRep ((x : ℝ) : Circ) = x := by
      have h : AddCircle.liftIoc (1 : ℝ) (-(1 / 2)) (fun y : ℝ => y) ((x : ℝ) : Circ) = x :=
        AddCircle.liftIoc_coe_apply hx'
      simpa only [iwRep, AddCircle.liftIoc, Function.comp_apply, Set.domRestrict_apply] using h
    have hmst : mstEta d χ η n ((x : ℝ) : Circ) = η (c * x) := by
      rw [mstEta_apply, hrep, hcdef, mstScale_apply]
    rw [hmst, fourier_neg_coe, smul_eq_mul]
    ring
  -- Step 2: change of variables `x = u/c` together with the truncation to the support of `η`.
  have hB : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          η (c * x) * Complex.exp ((((-(2 * Real.pi * (m : ℝ) * x)) : ℝ) : ℂ) * Complex.I))
      = c⁻¹ • ∫ u in (-(1 / 2) : ℝ)..(1 / 2),
          η u * Complex.exp ((((-(2 * Real.pi * ((m : ℝ) / c) * u)) : ℝ) : ℂ) * Complex.I) := by
    set G : ℝ → ℂ := fun u =>
      η u * Complex.exp ((((-(2 * Real.pi * ((m : ℝ) / c) * u)) : ℝ) : ℂ) * Complex.I) with hG
    set H : ℝ → ℂ := fun x =>
      η (c * x) * Complex.exp ((((-(2 * Real.pi * (m : ℝ) * x)) : ℝ) : ℂ) * Complex.I) with hH
    -- `G (c * x)` has the same exponential factor as `H x`, because `(m/c) * c = m`
    have harg : ∀ x : ℝ,
        (((-(2 * Real.pi * ((m : ℝ) / c) * (c * x))) : ℝ) : ℂ) * Complex.I
          = (((-(2 * Real.pi * (m : ℝ) * x)) : ℝ) : ℂ) * Complex.I := by
      intro x
      have hr : 2 * Real.pi * ((m : ℝ) / c) * (c * x) = 2 * Real.pi * (m : ℝ) * x := by
        field_simp
      rw [hr]
    have htrunc : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), H x)
        = ∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), H x := by
      refine intervalIntegral_eq_of_support (by positivity) ?_ ?_
      · have h2c : (0 : ℝ) < 2 * c := by linarith
        rw [div_le_iff₀ h2c]
        linarith
      · intro x hx
        have hx' : (1 : ℝ) / 2 < |c * x| := by
          have h := mul_lt_mul_of_pos_left hx hcpos
          rw [show c * (1 / (2 * c)) = 1 / 2 by field_simp] at h
          rwa [abs_mul, abs_of_pos hcpos]
        simp only [hH]
        rw [hη2 (c * x) hx', zero_mul]
    have hscale : (∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), H x)
        = c⁻¹ • ∫ u in (-(1 / 2) : ℝ)..(1 / 2), G u := by
      rw [show (∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), H x)
            = ∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), G (c * x) from
          intervalIntegral.integral_congr (fun x _ => by
            simp only [hH, hG]
            rw [harg x])]
      exact intervalIntegral_comp_mul_scale G hcne
    change (∫ x in (-(1 / 2) : ℝ)..(1 / 2), H x)
        = c⁻¹ • ∫ u in (-(1 / 2) : ℝ)..(1 / 2), G u
    rw [htrunc, hscale]
  rw [hA, hB]
  rw [mstHat_apply]
  rw [← Complex.ofReal_inv c, Complex.real_smul]

end

end Work.BourgainPlan.Maximal
