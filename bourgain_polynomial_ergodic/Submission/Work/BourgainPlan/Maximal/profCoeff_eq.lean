import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_prof_err1_defs
import Submission.Work.BourgainPlan.Maximal.mst_err1_bump_defs
import Submission.Work.BourgainPlan.Maximal.fourierCoeff_mstEta

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal BigOperators

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

/-- The character `fourier (-m)` at a real point, in the exponential form of `polyE`. -/
private lemma fourier_neg_coe (m : ℤ) (x : ℝ) :
    fourier (-m) ((x : ℝ) : Circ) = polyE (-((m : ℝ) * x)) := by
  rw [fourier_coe_apply]
  simp only [Complex.ofReal_one, div_one]
  unfold polyE
  congr 1
  push_cast
  ring

/-- **Truncation to the support.**  If `h` vanishes off the closed interval `Icc (-r) r` and
`0 ≤ r ≤ R`, then the interval integral of `h` over `(-R, R)` equals its interval integral over
`(-r, r)`.  (Copied from `Work.BourgainPlan.Maximal.fourierCoeff_mstEta`, where it is private.) -/
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
scales the fundamental interval `[-1/2, 1/2]` by `c`.  (Copied from
`Work.BourgainPlan.Maximal.fourierCoeff_mstEta`, where it is private.) -/
private lemma intervalIntegral_comp_mul_scale (G : ℝ → ℂ) {c : ℝ} (hc : c ≠ 0) :
    ∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), G (c * x)
      = c⁻¹ • ∫ u in (-(1 / 2) : ℝ)..(1 / 2), G u := by
  have hcomp := intervalIntegral.integral_comp_mul_left
    (a := -(1 / (2 * c))) (b := 1 / (2 * c)) (c := c) G hc
  rw [hcomp]
  have e1 : c * (-(1 / (2 * c))) = -(1 / 2) := by field_simp
  have e2 : c * (1 / (2 * c)) = (1 / 2) := by field_simp
  rw [e1, e2]

/-- **The inner integral.**  For `c ≥ 1` and a bump `η` supported in `[-1/2, 1/2]`,

`∫_{-1/2}^{1/2} η (c x) · e(−x T) dx = c⁻¹ · mstHat η (T / c)`.

This is the level-`n` dilation dictionary of `fourierCoeff_mstEta`, with the character written as
`polyE` and a general frequency `T`. -/
private lemma inner_integral_of (c : ℝ) (hc1 : 1 ≤ c) {η : ℝ → ℂ}
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) (T : ℝ) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2), η (c * x) * polyE (-(x * T)))
      = (c : ℂ)⁻¹ * mstHat η (T / c) := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcne : c ≠ 0 := hcpos.ne'
  set G : ℝ → ℂ := fun u => η u * polyE (-(u * (T / c))) with hG
  set H : ℝ → ℂ := fun x => η (c * x) * polyE (-(x * T)) with hH
  have harg : ∀ x : ℝ, -((c * x) * (T / c)) = -(x * T) := by
    intro x; field_simp
  have hcomp : ∀ x : ℝ, H x = G (c * x) := by
    intro x
    simp only [hH, hG]
    rw [harg x]
  have htrunc : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), H x)
      = ∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), H x := by
    refine intervalIntegral_eq_of_support (r := 1 / (2 * c)) (R := (1 : ℝ) / 2)
      (by positivity) ?_ ?_
    · have h2c : (0 : ℝ) < 2 * c := by linarith
      rw [div_le_iff₀ h2c]
      linarith
    · intro x hx
      have hx' : (1 : ℝ) / 2 < |c * x| := by
        have hh : c * (1 / (2 * c)) = 1 / 2 := by field_simp
        rw [abs_mul, abs_of_pos hcpos, ← hh]
        exact mul_lt_mul_of_pos_left hx hcpos
      simp only [hH, hη2 (c * x) hx', zero_mul]
  have hscale : (∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), H x)
      = c⁻¹ • ∫ u in (-(1 / 2) : ℝ)..(1 / 2), G u := by
    rw [show (∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), H x)
          = ∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), G (c * x) from
        intervalIntegral.integral_congr (fun x _ => hcomp x)]
    exact intervalIntegral_comp_mul_scale G hcne
  have hGmst : (∫ u in (-(1 / 2) : ℝ)..(1 / 2), G u) = mstHat η (T / c) := by
    rw [mstHat_apply]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    simp only [hG, polyE]
    congr 1
    push_cast
    ring_nf
  calc (∫ x in (-(1 / 2) : ℝ)..(1 / 2), η (c * x) * polyE (-(x * T)))
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), H x := rfl
    _ = ∫ x in (-(1 / (2 * c)))..(1 / (2 * c)), H x := htrunc
    _ = c⁻¹ • ∫ u in (-(1 / 2) : ℝ)..(1 / 2), G u := hscale
    _ = c⁻¹ • mstHat η (T / c) := by rw [hGmst]
    _ = (c : ℂ)⁻¹ * mstHat η (T / c) := by
        rw [Complex.real_smul, Complex.ofReal_inv]

/-- **The double integral.**  For a bump `η` bounded by `M` and supported in `[-1/2, 1/2]`, a
scale `c ≥ 1` and a continuous frequency `Pa`,

`∫_{−1/2}^{1/2} (∫_0^1 e(−x Pa(s)) ds) · η (c x) · e(−m x) dx
   = ∫_0^1 c⁻¹ · mstHat η ((Pa(s) + m)/c) ds`.

Fubini on the rectangle `uIoc (−1/2) (1/2) ×ˢ uIoc 0 1` (legitimate because the joint integrand is
bounded by `M` and a.e. strongly measurable — the latter coming from the a.e. strong measurability
of `η`), followed by the inner evaluation `inner_integral_of` for each `s`. -/
private lemma double_integral_eval {η : ℝ → ℂ} {M : ℝ} (_hM : 0 ≤ M)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hηm : AEStronglyMeasurable η (volume : Measure ℝ))
    {c : ℝ} (hc1 : 1 ≤ c) {Pa : ℝ → ℝ} (hPac : Continuous Pa) (m : ℤ) :
    (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
        ((∫ s in (0 : ℝ)..1, polyE (-(x * Pa s))) * η (c * x)) * polyE (-((m : ℝ) * x)))
      = ∫ s in (0 : ℝ)..1, (c : ℂ)⁻¹ * mstHat η ((Pa s + (m : ℝ)) / c) := by
  have hcpos : 0 < c := lt_of_lt_of_le one_pos hc1
  have hcne : c ≠ 0 := hcpos.ne'
  have hηc : AEStronglyMeasurable (fun x : ℝ => η (c * x)) (volume : Measure ℝ) := by
    refine hηm.comp_quasiMeasurePreserving ⟨measurable_const_mul c, ?_⟩
    rw [Real.map_volume_mul_left hcne]
    intro t ht
    rw [Measure.smul_apply, ht, smul_zero]
  have hInt : IntegrableOn (Function.uncurry (fun x s : ℝ =>
      polyE (-(x * Pa s)) * (η (c * x) * polyE (-((m : ℝ) * x)))))
      (Set.uIoc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Set.uIoc (0 : ℝ) 1) volume := by
    refine IntegrableOn.of_bound ?_ ?_ M ?_
    · rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl]
      rw [Measure.prod_prod, Real.volume_uIoc, Real.volume_uIoc]
      norm_num
    · rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
        ← Measure.prod_restrict]
      have h1 : AEStronglyMeasurable (fun z : ℝ × ℝ => polyE (-(z.1 * Pa z.2)))
          ((volume.restrict (Set.uIoc (-(1 / 2) : ℝ) (1 / 2))).prod
            (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
        (continuous_polyE.comp ((continuous_fst.mul (hPac.comp continuous_snd)).neg)).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun z : ℝ × ℝ => η (c * z.1))
          ((volume.restrict (Set.uIoc (-(1 / 2) : ℝ) (1 / 2))).prod
            (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
        (hηc.mono_measure (Measure.restrict_le_self (s := Set.uIoc (-(1 / 2) : ℝ) (1 / 2)))).comp_fst
      have h3 : AEStronglyMeasurable (fun z : ℝ × ℝ => polyE (-((m : ℝ) * z.1)))
          ((volume.restrict (Set.uIoc (-(1 / 2) : ℝ) (1 / 2))).prod
            (volume.restrict (Set.uIoc (0 : ℝ) 1))) :=
        (continuous_polyE.comp ((continuous_const.mul continuous_fst).neg)).aestronglyMeasurable
      exact h1.mul (h2.mul h3)
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry]
      have hb : ‖polyE (-(z.1 * Pa z.2)) * (η (c * z.1) * polyE (-((m : ℝ) * z.1)))‖
          = ‖η (c * z.1)‖ := by
        rw [norm_mul, norm_mul, norm_polyE, norm_polyE, one_mul, mul_one]
      rw [hb]
      exact hηbd _
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := fun x s : ℝ => polyE (-(x * Pa s)) * (η (c * x) * polyE (-((m : ℝ) * x))))
    (a := -(1 / 2)) (b := 1 / 2) (c := 0) (d := 1) hInt
  have hstep1 : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
        ((∫ s in (0 : ℝ)..1, polyE (-(x * Pa s))) * η (c * x)) * polyE (-((m : ℝ) * x)))
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          ∫ s in (0 : ℝ)..1, polyE (-(x * Pa s)) * (η (c * x) * polyE (-((m : ℝ) * x))) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    rw [show ((∫ s in (0 : ℝ)..1, polyE (-(x * Pa s))) * η (c * x)) * polyE (-((m : ℝ) * x))
          = (∫ s in (0 : ℝ)..1, polyE (-(x * Pa s)))
              * (η (c * x) * polyE (-((m : ℝ) * x))) by ring]
    rw [intervalIntegral.integral_mul_const]
  have hstep3 : (∫ s in (0 : ℝ)..1, ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
        polyE (-(x * Pa s)) * (η (c * x) * polyE (-((m : ℝ) * x))))
      = ∫ s in (0 : ℝ)..1, (c : ℂ)⁻¹ * mstHat η ((Pa s + (m : ℝ)) / c) := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    have hinner : (∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          polyE (-(x * Pa s)) * (η (c * x) * polyE (-((m : ℝ) * x))))
        = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), η (c * x) * polyE (-(x * (Pa s + (m : ℝ)))) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [show polyE (-(x * Pa s)) * (η (c * x) * polyE (-((m : ℝ) * x)))
            = η (c * x) * (polyE (-(x * Pa s)) * polyE (-((m : ℝ) * x))) by ring]
      rw [polyE_add]
      congr 1
      ring_nf
    rw [hinner, inner_integral_of c hc1 hη2 (Pa s + (m : ℝ))]
  rw [hstep1, hswap, hstep3]

/-- **The Fourier coefficient of the profile-times-bump is a one-dimensional average of `mstHat`.**

With `c = mstScale d χ n = 2^{n(d−χ)} ≥ 1` (hypothesis `χ + 1 ≤ d`),

`fourierCoeff (fun ξ => star (mstProf P (2^n) ξ) * mstEta d χ η n ξ) m
   = ∫_0^1 c⁻¹ · mstHat η ((P(2^n s) + m)/c) ds`.

The proof is a two-line extension of `Work.BourgainPlan.Maximal.fourierCoeff_mstEta`
(`Submission/Work/BourgainPlan/Maximal/fourierCoeff_mstEta.lean`), whose *private* helper lemmas
`intervalIntegral_eq_of_support` (truncation to the support on *closed* intervals, avoiding the loss
of the endpoint) and `intervalIntegral_comp_mul_scale` (the change of variable `x ↦ c x` on
`[−1/(2c), 1/(2c)]`) should simply be copied into your file.

Route.
1. `fourierCoeff f m = ∫_{x ∈ (−1/2,1/2)} e(−m x) · f (x : Circle) dx`
   (`fourierCoeff_eq_intervalIntegral` at `T = 1, a = −1/2`, `fourier_coe_apply`); on the
   fundamental domain `iwRep (x : Circle) = x` (`AddCircle.liftIoc_coe_apply`), so
   `f (x : Circle) = star (polyProfile P (2^n) x) · η (c x)`.
2. `star_polyProfile` writes the first factor as `∫_0^1 e(−x · P(2^n s)) ds`
   (`polyE t = e(t)`; note `(2^n : ℝ) = (2:ℝ)^n`).
3. Fubini for the two interval integrals
   (`MeasureTheory.intervalIntegral_intervalIntegral_swap`, over `uIoc (−1/2) (1/2) ×ˢ uIoc 0 1`;
   integrability of the joint integrand follows from the uniform bound `hηbd` and a.e. strong
   measurability of `η`, the latter being needed because the integrand is bounded but not obviously
   measurable) turns the coefficient into
   `∫_0^1 ∫_{x ∈ (−1/2,1/2)} e(−x (P(2^n s) + m)) · η (c x) dx ds`.
4. For each fixed `s` the inner integral is computed exactly as in `fourierCoeff_mstEta`:
   substitute `u = c x` (`intervalIntegral_comp_mul_scale`, giving
   `c⁻¹ ∫_{(−c/2,c/2)} η u · e(−(u/c)(P(2^n s)+m)) du`) and truncate `(−c/2, c/2)` back to
   `(−1/2, 1/2)` using `hη2` and `c ≥ 1` (`intervalIntegral_eq_of_support`), which is
   `c⁻¹ · mstHat η ((P(2^n s) + m)/c)`. -/
theorem profCoeff_eq (P : Polynomial ℤ) {d : ℕ} {χ : ℝ} (hχ : χ + 1 ≤ (d : ℝ)) {η : ℝ → ℂ}
    {M : ℝ} (hM : 0 ≤ M) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hηm : AEStronglyMeasurable η (volume : Measure ℝ)) (n : ℕ) (m : ℤ) :
    fourierCoeff (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
        star (mstProf P (2 ^ n) ξ) * mstEta d χ η n ξ) m
      = ∫ s in (0 : ℝ)..1,
          ((mstScale d χ n : ℝ) : ℂ)⁻¹ * mstHat η
            (((toRealPoly P).eval (((2 : ℝ) ^ n) * s) + (m : ℝ)) / mstScale d χ n) := by
  have hc1 : 1 ≤ mstScale d χ n := one_le_mstScale hχ n
  have hPac : Continuous (fun s : ℝ => (toRealPoly P).eval (((2 : ℝ) ^ n) * s)) :=
    (Polynomial.continuous (toRealPoly P)).comp (continuous_const.mul continuous_id)
  set F : Circ → ℂ := fun ξ => star (mstProf P (2 ^ n) ξ) * mstEta d χ η n ξ with hF
  have hA : fourierCoeff F m
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2), F (x : Circ) * polyE (-((m : ℝ) * x)) := by
    rw [fourierCoeff_eq_intervalIntegral (T := 1) F m (-(1 / 2))]
    rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]
    rw [show ((1 : ℝ) / 1) = 1 by norm_num]
    rw [one_smul]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x _ => ?_))
    rw [smul_eq_mul, fourier_neg_coe, mul_comm]
  have hB : (∫ x in (-(1 / 2) : ℝ)..(1 / 2), F (x : Circ) * polyE (-((m : ℝ) * x)))
      = ∫ x in (-(1 / 2) : ℝ)..(1 / 2),
          ((∫ s in (0 : ℝ)..1,
              polyE (-(x * ((toRealPoly P).eval (((2 : ℝ) ^ n) * s)))))
            * η (mstScale d χ n * x)) * polyE (-((m : ℝ) * x)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x hx => ?_))
    rw [Set.uIoc_of_le (by norm_num : (-(1 / 2) : ℝ) ≤ 1 / 2)] at hx
    have hx' : x ∈ Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
      rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num]; exact hx
    have hrep : iwRep ((x : ℝ) : Circ) = x := by
      have h : AddCircle.liftIoc (1 : ℝ) (-(1 / 2)) (fun y : ℝ => y) ((x : ℝ) : Circ) = x :=
        AddCircle.liftIoc_coe_apply hx'
      simpa only [iwRep, AddCircle.liftIoc, Function.comp_apply, Set.domRestrict_apply] using h
    have hmst : mstEta d χ η n ((x : ℝ) : Circ) = η (mstScale d χ n * x) := by
      rw [mstEta_apply, hrep, mstScale_apply]
    have hmprof : mstProf P (2 ^ n) ((x : ℝ) : Circ) = polyProfile P (2 ^ n) x := by
      rw [mstProf_apply, hrep]
    have hstar : star (polyProfile P (2 ^ n) x)
        = ∫ s in (0 : ℝ)..1, polyE (-(x * ((toRealPoly P).eval (((2 : ℝ) ^ n) * s)))) := by
      rw [← starRingEnd_apply (R := ℂ), star_polyProfile]
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [Nat.cast_pow, Nat.cast_ofNat]
    simp only [hF, hmprof, hmst, hstar]
  rw [hA, hB]
  exact double_integral_eval (Pa := fun s : ℝ => (toRealPoly P).eval (((2 : ℝ) ^ n) * s))
    (c := mstScale d χ n) hM hηbd hη2 hηm hc1 hPac m

end

end Work.BourgainPlan.Maximal
