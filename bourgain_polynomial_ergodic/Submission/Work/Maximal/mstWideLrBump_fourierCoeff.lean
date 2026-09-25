import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs
import Submission.Work.BourgainPlan.Maximal.fourierCoeff_mstEta

/-!
# The Fourier coefficients of a general dilated bump `ξ ↦ η (c · iwRep ξ)`

`Work.BourgainPlan.Maximal.fourierCoeff_mstEta` computes the Fourier coefficients of the level bump
`mstEta d χ η n`, whose dilation factor is the particular scale `c_n = 2^{n(d−χ)}`.  The large-scale
half of the level estimate (`Work.Maximal.mst_level_lr_large`) uses instead the *wide* bump
`mstWideBump P χ η s : ξ ↦ η (mstWideC P s · iwRep ξ)`, whose scale `mstWideC P s = Q_s^{3d}` is
not of the form `2^{n(d−χ)}`.  This file therefore proves the identity for an **arbitrary**
dilation `c ≥ 1`:

`∫_𝕋 η (c · iwRep ξ) · conj (fourier m ξ) dξ = c⁻¹ · mstHat η (m / c)`,

which is precisely the hypothesis `hid` of `Work.Maximal.mstWideLrBump_coeff_l1`.  The proof is the
dictionary of `fourierCoeff_mstEta`, with `mstEta` replaced by the general bump and the level scale
by the general `c`:

* the Haar integral is the Fourier coefficient of `ξ ↦ η (c · iwRep ξ)` (`fourierCoeff`, using
  `fourier_neg`);
* `fourierCoeff_eq_intervalIntegral` (at `T = 1`, `a = −1/2`) turns it into the interval integral
  `∫_{−1/2}^{1/2} η (c x) e^{−2πi m x} dx` (on the fundamental interval `iwRep` is the identity);
* the substitution `x = u/c` gives `c⁻¹ ∫_{−c/2}^{c/2} η u e^{−2πi (m/c) u} du`, and the support
  hypothesis `η u = 0` for `1/2 < |u|` (together with `c ≥ 1`) truncates the latter back to the
  fundamental interval `[−1/2, 1/2]`, which is exactly `mstHat η (m/c)`.

The truncation is performed on the *closed* intervals (see
`mstWideLrBump_supp_intervalIntegral`), so that the endpoint `±1/2`, where `η` need not vanish,
is not lost.
-/

open MeasureTheory Set
open scoped BigOperators

set_option autoImplicit false

namespace Work.Maximal

open Work.BourgainPlan.IonescuWainger
open Work.BourgainPlan.Maximal

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-- **Truncation to the support.**  If `h` vanishes off the closed interval `Icc (-r) r` and
`0 ≤ r ≤ R`, then the interval integral of `h` over `(-R, R)` equals its interval integral over
`(-r, r)`. -/
private lemma mstWideLrBump_supp_intervalIntegral {h : ℝ → ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R)
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
private lemma mstWideLrBump_comp_mul_scale (G : ℝ → ℂ) {c : ℝ} (hc : c ≠ 0) :
    ∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), G (c * x)
      = c⁻¹ • ∫ u in (-(1 / 2) : ℝ)..(1 / 2), G u := by
  have hcomp := intervalIntegral.integral_comp_mul_left
    (a := -(1 / (2 * c))) (b := 1 / (2 * c)) (c := c) G hc
  rw [hcomp]
  have e1 : c * (-(1 / (2 * c))) = -(1 / 2) := by field_simp
  have e2 : c * (1 / (2 * c)) = (1 / 2) := by field_simp
  rw [e1, e2]

/-- The character `fourier (-m)` at a real point, in the exponential form used by `mstHat`. -/
private lemma mstWideLrBump_fourier_neg_coe (m : ℤ) (x : ℝ) :
    fourier (-m) ((x : ℝ) : Circ)
      = Complex.exp ((((-(2 * Real.pi * (m : ℝ) * x)) : ℝ) : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- **The Fourier-coefficient dictionary for a general dilated bump.**  For any dilation
`c ≥ 1`, the `m`-th Fourier coefficient of the circle function `ξ ↦ η (c · iwRep ξ)` is
`c⁻¹ · mstHat η (m / c)`, where `mstHat` is the `ℝ`-Fourier transform of `η` in the period-`1`
convention.  Only the support hypothesis `η u = 0` for `1/2 < |u|` is needed. -/
theorem mstWideLrBump_fourierCoeff {c : ℝ} (hc1 : 1 ≤ c) {η : ℝ → ℂ}
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (m : ℤ) :
    (∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
        η (c * Work.BourgainPlan.Maximal.iwRep ξ) * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1)))
      = ((c : ℂ))⁻¹ * Work.BourgainPlan.Maximal.mstHat η ((m : ℝ) / c) := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcne : c ≠ 0 := hcpos.ne'
  set F : Circ → ℂ := fun ξ => η (c * iwRep ξ) with hFdef
  -- Step 0: the Haar integral is the Fourier coefficient of the dilated bump.
  have h0 : (∫ ξ : Circ, F ξ * star (fourier m ξ) ∂(AddCircle.haarAddCircle (T := 1)))
      = fourierCoeff (T := 1) F m := by
    rw [fourierCoeff]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)).symm
    rw [fourier_neg, smul_eq_mul, Complex.star_def]
    ring
  -- Step 1: the coefficient as an integral over the fundamental interval, with the bump read
  -- through the canonical lift `iwRep` (which is the identity there).
  have hA : fourierCoeff (T := 1) F m
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          η (c * x) * Complex.exp ((((-(2 * Real.pi * (m : ℝ) * x)) : ℝ) : ℂ) * Complex.I) := by
    rw [fourierCoeff_eq_intervalIntegral (T := 1) F m (-(1 / 2))]
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
    have hFval : F ((x : ℝ) : Circ) = η (c * x) := by
      show η (c * iwRep ((x : ℝ) : Circ)) = η (c * x)
      rw [hrep]
    rw [hFval, mstWideLrBump_fourier_neg_coe, smul_eq_mul]
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
      refine mstWideLrBump_supp_intervalIntegral (by positivity) ?_ ?_
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
      exact mstWideLrBump_comp_mul_scale G hcne
    change (∫ x in (-(1 / 2) : ℝ)..(1 / 2), H x)
        = c⁻¹ • ∫ u in (-(1 / 2) : ℝ)..(1 / 2), G u
    rw [htrunc, hscale]
  rw [h0, hA, hB]
  rw [mstHat_apply]
  rw [← Complex.ofReal_inv c, Complex.real_smul]

end

end Work.Maximal
