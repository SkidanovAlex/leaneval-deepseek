import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation
import Submission.Work.BourgainPlan.Maximal.fourierCoeff_mstEta
import Submission.Work.BourgainPlan.Maximal.mstKernel_helpers

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haar" => (AddCircle.haarAddCircle (T := 1))
local notation "circleLift" => Work.BourgainPlan.Thm52.circleLift

noncomputable section

/-! ## Copied helpers (verbatim from `fourierCoeff_mstEta.lean`) -/

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

/-- The conjugate character `fourier (-m)` at a real point, written with the character `polyE`. -/
private lemma fourier_neg_coe_polyE (m : ℤ) (x : ℝ) :
    fourier (-m) ((x : ℝ) : Circ) = polyE (-((m : ℝ) * x)) := by
  rw [fourier_coe_apply]
  unfold polyE
  congr 1
  push_cast
  ring

/-- The scaled bump `x ↦ η (c * x)` is a.e. strongly measurable on `ℝ` (its only possible
discontinuities are the two endpoints `±1/(2c)`). -/
private lemma scaled_eta_aestronglyMeasurable {d : ℕ} {χ : ℝ} {η : ℝ → ℂ} {c : ℝ}
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hηcont : Continuous (circleLift (mstEta d χ η 0))) (hc : 0 < c) :
    AEStronglyMeasurable (fun x : ℝ => η (c * x)) (volume : Measure ℝ) := by
  have hcont' : Continuous (fun x : ℝ => circleLift (mstEta d χ η 0) (-(c * x))) :=
    hηcont.comp ((continuous_const.mul continuous_id).neg)
  exact hcont'.aestronglyMeasurable.congr
    (eta_scaled_ae_eq_circleLift d χ η hη2 hc).symm

/-- **The elementary inner integral**: for a bump supported in `[-1/2,1/2]` and `c ≥ 1`, the
integral of `η (c x) e(-xS)` over the fundamental interval is `c⁻¹ mstHat η (S/c)`. -/
private lemma coeff_inner_eq {c : ℝ} (hcpos : 0 < c) (hc1 : 1 ≤ c) (η : ℝ → ℂ)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (S : ℝ) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2), η (c * x) * polyE (-(x * S)))
      = c⁻¹ • mstHat η (S / c) := by
  have hcne : c ≠ 0 := hcpos.ne'
  have htrunc : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), η (c * x) * polyE (-(x * S)))
      = ∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), η (c * x) * polyE (-(x * S)) := by
    refine intervalIntegral_eq_of_support (h := fun x : ℝ => η (c * x) * polyE (-(x * S)))
      ?_ ?_ ?_
    · positivity
    · have h2c : (0 : ℝ) < 2 * c := by linarith
      rw [div_le_iff₀ h2c]
      linarith
    · intro x hx
      have hx' : (1 : ℝ) / 2 < |c * x| := by
        have h := mul_lt_mul_of_pos_left hx hcpos
        rw [show c * (1 / (2 * c)) = 1 / 2 by field_simp] at h
        rwa [abs_mul, abs_of_pos hcpos]
      rw [hη2 (c * x) hx', zero_mul]
  have hscale : (∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), η (c * x) * polyE (-(x * S)))
      = c⁻¹ • ∫ u in (-(1 / 2) : ℝ)..(1 / 2), η u * polyE (-((u / c) * S)) := by
    rw [show (∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), η (c * x) * polyE (-(x * S)))
          = ∫ x in (-(1 / (2 * c)))..(1 / (2 * c)),
              (fun u : ℝ => η u * polyE (-((u / c) * S))) (c * x) from
        intervalIntegral.integral_congr (fun x _ => by
          show η (c * x) * polyE (-(x * S)) = η (c * x) * polyE (-(((c * x) / c) * S))
          rw [mul_div_cancel_left₀ x hcne])]
    exact intervalIntegral_comp_mul_scale (fun u : ℝ => η u * polyE (-((u / c) * S))) hcne
  rw [htrunc, hscale]
  congr 1
  rw [mstHat_apply]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  congr 1
  unfold polyE
  congr 1
  push_cast
  ring

/-! ## The main identity -/

/-- **The Fourier coefficients of `star (mstProf P N ·) * mstEta d χ η s` as a one-dimensional
average of the bump transform `mstHat`.**

For a bump `η` bounded by `M`, supported in `|x| ≤ 1/2` and with continuous fundamental-domain lift
`circleLift (mstEta d χ η 0)`, and with the level scale `c = mstScale d χ s ≥ 1` (from
`χ + 1 ≤ d`),

`∫ ξ, (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ) ∂haar
    = ∫_0^1 c⁻¹ · mstHat η ((m + P(N t))/c) dt`.

This is the *non-diagonal* coefficient identity of the MST §4.2 kernel estimate: the profile scale
`N` and the bump level `s` are independent.  The diagonal case `N = 2^n` is
`Work.BourgainPlan.Maximal.profCoeff_eq` (`profCoeff_eq.lean`, being proved concurrently with the
same route), and the bump-alone case is the already-proved
`Work.BourgainPlan.Maximal.fourierCoeff_mstEta` (`fourierCoeff_mstEta.lean`), from which the two
private helper lemmas `intervalIntegral_eq_of_support` (truncation of an interval integral to the
support of the integrand, performed on the *closed* intervals so that no endpoint is lost) and
`intervalIntegral_comp_mul_scale` (the change of variable `x ↦ c * x` on `[−1/(2c), 1/(2c)]`) should
be copied verbatim.

Route.

1. `fourierCoeff_eq_intervalIntegral` (`T = 1`, `a = −1/2`) and `fourier_coe_apply` turn the Haar
   integral into `∫ x in (−1/2)..(1/2), star (mstProf P N (x:Circle)) * mstEta d χ η s (x:Circle) *
   e(−m x) dx`; on the fundamental domain `iwRep (x : Circle) = x`
   (`AddCircle.liftIoc_coe_apply`, or `mstKernel_helpers.iwRep_coe_of_mem`), so
   `star (mstProf P N (x:Circle)) = star (polyProfile P N x)` and
   `mstEta d χ η s (x:Circle) = η (c x)`.

2. `star_polyProfile` writes the first factor as `∫ t in 0..1, polyE (−(x · P(N t))) dt`
   (`polyE s = e(s) = exp(2πi s)` from
   `Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation`).

3. Fubini for two interval integrals,
   `MeasureTheory.intervalIntegral_intervalIntegral_swap` applied with
   `IntegrableOn F.uncurry (uIoc (−1/2) (1/2) ×ˢ uIoc 0 1)`: the joint integrand
   `(t, x) ↦ polyE (−(x · P(N t))) · η (c x) · polyE (−(m x))` is bounded by `M` (from `hηbd` and
   `‖polyE‖ = 1`) and a.e. strongly measurable — the latter needs `AEStronglyMeasurable η volume`,
   which follows from `hηcont` and `hη2` because `η =ᵐ circleLift (mstEta d χ η 0) ∘ (−·)` (the only
   exceptions are `±1/2`); `mstKernel_helpers.aestronglyMeasurable_eta` (or
   `eta_ae_eq_circleLift_neg`) is exactly this.  This yields
   `∫_0^1 ∫ x in (−1/2)..(1/2), e(−x · P(N t)) · η (c x) · e(−m x) dx dt`.

4. `polyE_add`/`polyE_mul_neg` combine the two phases into `e(−x (P(N t) + m))`, and the inner
   integral is then computed exactly as in `fourierCoeff_mstEta`: substitute `u = c x`
   (`intervalIntegral_comp_mul_scale`, giving `c⁻¹ ∫_{(−c/2, c/2)} η u · e(−(u/c)(P(N t)+m)) du`)
   and truncate `(−c/2, c/2)` back to `(−1/2, 1/2)` using `hη2` and `c ≥ 1`
   (`intervalIntegral_eq_of_support`), which is `c⁻¹ · mstHat η ((m + P(N t))/c)`. -/
theorem mstProfBumpS_coeff_identity (P : Polynomial ℤ) {d : ℕ} {χ : ℝ} {η : ℝ → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hχ : χ + 1 ≤ (d : ℝ)) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hηcont : Continuous (Work.BourgainPlan.Thm52.circleLift (mstEta d χ η 0)))
    (N s : ℕ) (m : ℤ) :
    (∫ ξ : Work.BourgainPlan.IonescuWainger.Circle,
        (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1)))
      = ∫ t in (0 : ℝ)..1, ((mstScale d χ s : ℝ) : ℂ)⁻¹ *
          mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * t)) / mstScale d χ s) := by
  have _hM := hM
  set c : ℝ := mstScale d χ s with hcdef
  have hc1 : 1 ≤ c := by rw [hcdef]; exact one_le_mstScale hχ s
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hstar_prof (x : ℝ) : star (polyProfile P N x)
      = ∫ t in (0 : ℝ)..1, polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t))) := by
    simpa using star_polyProfile P N x
  -- ### Step 1: the Haar integral is the `m`-th Fourier coefficient of the product
  have hI0 : (∫ ξ : Circ, (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ) ∂haar)
      = fourierCoeff (fun ξ : Circ => star (mstProf P N ξ) * mstEta d χ η s ξ) m := by
    rw [fourierCoeff]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ => ?_))
    change (star (mstProf P N ξ) * mstEta d χ η s ξ) * star (fourier m ξ)
      = fourier (-m) ξ • (star (mstProf P N ξ) * mstEta d χ η s ξ)
    rw [fourier_neg, starRingEnd_apply, smul_eq_mul]
    ring
  -- ### Step 2: evaluation on the fundamental domain
  have hI1 : fourierCoeff (fun ξ : Circ => star (mstProf P N ξ) * mstEta d χ η s ξ) m
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          star (polyProfile P N x) * η (c * x) * polyE (-((m : ℝ) * x)) := by
    rw [fourierCoeff_eq_intervalIntegral (T := 1)
      (fun ξ : Circ => star (mstProf P N ξ) * mstEta d χ η s ξ) m (-(1 / 2))]
    rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]
    rw [show ((1 : ℝ) / 1) = 1 by norm_num]
    rw [one_smul]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    change fourier (-m) ((x : ℝ) : Circ)
        • (star (mstProf P N ((x : ℝ) : Circ)) * mstEta d χ η s ((x : ℝ) : Circ))
      = star (polyProfile P N x) * η (c * x) * polyE (-((m : ℝ) * x))
    rw [Set.uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hx
    have hrep : iwRep ((x : ℝ) : Circ) = x := iwRep_coe_of_mem hx
    have hprof : mstProf P N ((x : ℝ) : Circ) = polyProfile P N x := by
      rw [mstProf_apply, hrep]
    have heta : mstEta d χ η s ((x : ℝ) : Circ) = η (c * x) := by
      rw [mstEta_apply, hrep, hcdef, mstScale_apply]
    rw [fourier_neg_coe_polyE, smul_eq_mul, hprof, heta]
    ring
  -- ### Step 3: `star_polyProfile` inserts the `t`-average
  have hI2 : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          star (polyProfile P N x) * η (c * x) * polyE (-((m : ℝ) * x)))
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          (∫ t in (0 : ℝ)..1, polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t))))
            * (η (c * x) * polyE (-((m : ℝ) * x))) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [hstar_prof x]
    ring
  -- ### Step 4: Fubini
  have hFub : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          (∫ t in (0 : ℝ)..1, polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t))))
            * (η (c * x) * polyE (-((m : ℝ) * x))))
      = ∫ t in (0 : ℝ)..1, ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t)))
            * (η (c * x) * polyE (-((m : ℝ) * x))) := by
    have hint : IntegrableOn
        (Function.uncurry (fun x t : ℝ =>
          polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t)))
            * (η (c * x) * polyE (-((m : ℝ) * x)))))
        (Set.uIoc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.uIoc (0 : ℝ) 1) volume := by
      have hfin : (volume : Measure (ℝ × ℝ))
          (Set.uIoc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.uIoc (0 : ℝ) 1) < ⊤ := by
        rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod]
        exact ENNReal.mul_lt_top (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top)
          (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top)
      refine IntegrableOn.of_bound hfin ?_ M ?_
      · have hAB : Function.uncurry (fun x t : ℝ =>
            polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t)))
              * (η (c * x) * polyE (-((m : ℝ) * x))))
            = (fun z : ℝ × ℝ => polyE (-(z.1 * (toRealPoly P).eval ((N : ℝ) * z.2))))
              * (fun z : ℝ × ℝ => η (c * z.1) * polyE (-((m : ℝ) * z.1))) := rfl
        rw [hAB]
        have hA : AEStronglyMeasurable (fun z : ℝ × ℝ =>
            polyE (-(z.1 * (toRealPoly P).eval ((N : ℝ) * z.2)))) (volume : Measure (ℝ × ℝ)) :=
          (continuous_polyE.comp ((continuous_fst.mul
            ((Polynomial.continuous (toRealPoly P)).comp
              (continuous_const.mul continuous_snd))).neg)).aestronglyMeasurable
        have hB : AEStronglyMeasurable (fun z : ℝ × ℝ => η (c * z.1))
            (volume : Measure (ℝ × ℝ)) :=
          (scaled_eta_aestronglyMeasurable hη2 hηcont hcpos).comp_fst
        have hC : AEStronglyMeasurable (fun z : ℝ × ℝ => polyE (-((m : ℝ) * z.1)))
            (volume : Measure (ℝ × ℝ)) :=
          (continuous_polyE.comp ((continuous_const.mul continuous_fst).neg)).aestronglyMeasurable
        exact (hA.mul (hB.mul hC)).mono_measure Measure.restrict_le_self
      · refine Filter.Eventually.of_forall (fun z => ?_)
        change ‖polyE (-(z.1 * (toRealPoly P).eval ((N : ℝ) * z.2)))
            * (η (c * z.1) * polyE (-((m : ℝ) * z.1)))‖ ≤ M
        simpa using hηbd (c * z.1)
    have hswap := intervalIntegral_intervalIntegral_swap (F := fun x t : ℝ =>
        polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t)))
          * (η (c * x) * polyE (-((m : ℝ) * x)))) hint
    have h1 : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          (∫ t in (0 : ℝ)..1, polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t))))
            * (η (c * x) * polyE (-((m : ℝ) * x))))
        = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), ∫ t in (0 : ℝ)..1,
            polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t)))
              * (η (c * x) * polyE (-((m : ℝ) * x))) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      exact (intervalIntegral.integral_mul_const (a := (0 : ℝ)) (b := 1)
        (η (c * x) * polyE (-((m : ℝ) * x)))
        (fun t : ℝ => polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t))))).symm
    rw [h1]
    exact hswap
  -- ### Step 5: the inner integral, for each `t`
  have hInner : (∫ t in (0 : ℝ)..1, ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t)))
            * (η (c * x) * polyE (-((m : ℝ) * x))))
      = ∫ t in (0 : ℝ)..1, (c⁻¹ : ℝ) • mstHat η
          (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * t)) / c) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have hpt : ∀ x : ℝ, polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t)))
          * (η (c * x) * polyE (-((m : ℝ) * x)))
        = η (c * x) * polyE (-(x * ((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * t)))) := by
      intro x
      have h1 : polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t)))
            * (η (c * x) * polyE (-((m : ℝ) * x)))
          = η (c * x) * (polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t)))
              * polyE (-((m : ℝ) * x))) := by ring
      rw [h1, polyE_add]
      congr 1
      ring_nf
    change (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t)))
            * (η (c * x) * polyE (-((m : ℝ) * x))))
        = (c⁻¹ : ℝ) • mstHat η (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * t)) / c)
    rw [show (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
            polyE (-(x * (toRealPoly P).eval ((N : ℝ) * t)))
              * (η (c * x) * polyE (-((m : ℝ) * x))))
          = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
              η (c * x) * polyE (-(x * ((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * t)))) from
        intervalIntegral.integral_congr (fun x _ => hpt x)]
    exact coeff_inner_eq hcpos hc1 η hη2 (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * t)))
  -- ### Step 6: the real scalar `c⁻¹` is the complex factor `((c : ℂ))⁻¹`
  have hScal : (∫ t in (0 : ℝ)..1, (c⁻¹ : ℝ) • mstHat η
          (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * t)) / c))
      = ∫ t in (0 : ℝ)..1, ((c : ℝ) : ℂ)⁻¹ * mstHat η
          (((m : ℝ) + (toRealPoly P).eval ((N : ℝ) * t)) / c) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [Complex.real_smul, Complex.ofReal_inv]
  exact hI0.trans (hI1.trans (hI2.trans (hFub.trans (hInner.trans hScal))))

end

end Work.BourgainPlan.Maximal
