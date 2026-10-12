import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Star.Real
import Submission.RadialIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.radialDecay4`

For `L ≥ 0` the tail integral of the radial weight `((1+‖p‖)^4 ‖p‖^2)^{-1}` is bounded by
`4π/(1+L)^3`, and the (truncated) integrand is integrable:

    `∫_{‖p‖ ≥ L} ((1+‖p‖)^4 ‖p‖^2)^{-1} dp ≤ 4π/(1+L)^3`.

The integrand is radial with profile `r ↦ ((1+r)^4 r^2)^{-1}`, so the polar-coordinate
identities of `Submission.RadialIntegral` (`integral_fun_norm_r3`, and `integrable_radial_r3`
for integrability) reduce everything to the one-dimensional statement

    `∫_L^∞ (1+r)^{-4} dr = 1/(3(1+L)^3)`,

which is the fundamental theorem of calculus for the antiderivative `r ↦ -(1/3)(1+r)^{-3}`
on `(L,∞)` (`integral_Ioi_of_hasDerivAt_of_tendsto'`), the derivative being computed with
`HasDerivAt.rpow_const`.  Since `1/(3(1+L)^3) ≤ 1/(1+L)^3`, the stated constant follows.

The sharp value of the left-hand side is `4π/(3(1+L)^3)`; only the (weaker) displayed
bound is needed downstream.
-/

noncomputable section

open MeasureTheory Filter
open scoped Real Topology

namespace Work.BoseRowsFS.LatRiemann

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `((1+r)^n)⁻¹ = (1+r)^(-n)` for `1 + r ≥ 0` (natural powers against real powers). -/
private lemma inv_one_add_pow_eq_rpow_neg (n : ℕ) (r : ℝ) (hr : 0 ≤ 1 + r) :
    ((1 + r) ^ n)⁻¹ = (1 + r) ^ (-(n : ℝ)) := by
  have h4 : (1 + r) ^ ((n : ℝ)) = (1 + r) ^ n := Real.rpow_natCast (1 + r) n
  rw [← h4, ← Real.rpow_neg hr (n : ℝ)]

/-- `r ↦ ((1+r)^4)⁻¹` is integrable on `(c,∞)` for `c > -1`. -/
private lemma integrableOn_Ioi_inv_one_add_pow_four (c : ℝ) (hc : -1 < c) :
    IntegrableOn (fun r : ℝ => ((1 + r) ^ 4)⁻¹) (Set.Ioi c) := by
  have h1 : IntegrableOn (fun r : ℝ => (1 + r) ^ (-4 : ℝ)) (Set.Ioi c) := by
    have := integrableOn_add_rpow_Ioi_of_lt (a := (-4 : ℝ)) (c := c) (m := (1 : ℝ))
      (by norm_num) (by linarith)
    simpa [add_comm] using this
  refine h1.congr_fun ?_ measurableSet_Ioi
  intro r hr
  exact (inv_one_add_pow_eq_rpow_neg 4 r (by have := Set.mem_Ioi.mp hr; linarith)).symm

/-- `∫_c^∞ (1+r)^{-4} dr = 1/(3(1+c)^3)` for `c ≥ 0`. -/
private lemma integral_Ioi_inv_one_add_pow_four (c : ℝ) (hc : 0 ≤ c) :
    (∫ r in Set.Ioi c, ((1 + r) ^ 4)⁻¹) = 1 / (3 * (1 + c) ^ 3) := by
  have hderiv : ∀ x ∈ Set.Ici c,
      HasDerivAt (fun r : ℝ => -(1 / 3) * (1 + r) ^ (-3 : ℝ)) ((1 + x) ^ (-4 : ℝ)) x := by
    intro x hx
    have hx0 : 1 + x ≠ 0 := by have := Set.mem_Ici.mp hx; linarith
    have hbase : HasDerivAt (fun r : ℝ => (1 + r)) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have h1 : HasDerivAt (fun r : ℝ => (1 + r) ^ (-3 : ℝ))
        ((-3 : ℝ) * (1 + x) ^ (-4 : ℝ)) x := by
      have hh := hbase.rpow_const (p := (-3 : ℝ)) (Or.inl hx0)
      simpa [show (-3 : ℝ) - 1 = (-4 : ℝ) by norm_num, one_mul] using hh
    have h3 := h1.const_mul (-(1 / 3))
    have key : (-(1 / 3) : ℝ) * ((-3 : ℝ) * (1 + x) ^ (-4 : ℝ)) = (1 + x) ^ (-4 : ℝ) := by
      ring
    rw [key] at h3
    exact h3
  have hint : IntegrableOn (fun r : ℝ => (1 + r) ^ (-4 : ℝ)) (Set.Ioi c) := by
    have := integrableOn_add_rpow_Ioi_of_lt (a := (-4 : ℝ)) (c := c) (m := (1 : ℝ))
      (by norm_num) (by linarith)
    simpa [add_comm] using this
  have htend : Tendsto (fun r : ℝ => (1 + r) ^ (-3 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := (3 : ℝ)) (by norm_num)).comp
      (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
  have hf : Tendsto (fun r : ℝ => -(1 / 3) * (1 + r) ^ (-3 : ℝ)) atTop (𝓝 0) := by
    have h := htend.const_mul (-(1 / 3))
    rw [mul_zero] at h
    exact h
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' (a := c) hderiv hint hf
  have hconv : (∫ r in Set.Ioi c, (1 + r) ^ (-4 : ℝ)) = ∫ r in Set.Ioi c, ((1 + r) ^ 4)⁻¹ := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro r hr
    exact (inv_one_add_pow_eq_rpow_neg 4 r (by have := Set.mem_Ioi.mp hr; linarith)).symm
  rw [← hconv, hftc]
  have h3 : (1 + c) ^ (-3 : ℝ) = ((1 + c) ^ 3)⁻¹ := by
    rw [Real.rpow_neg (by linarith)]
    simp
  rw [h3]
  rw [show (0 : ℝ) - -(1 / 3) * ((1 + c) ^ 3)⁻¹ = 1 / (3 * (1 + c) ^ 3) by
    have hc3 : (1 + c) ^ 3 ≠ 0 := by positivity
    field_simp
    ring]

/-- The truncated integral over the full half-line: for `c ≥ 0`,
`∫_0^∞ 1_{c ≤ r} (1+r)^{-4} dr = 1/(3(1+c)^3)`. -/
private lemma setIntegral_Ioi_zero_indicator_Ici (c : ℝ) (hc : 0 ≤ c) :
    (∫ r in Set.Ioi (0 : ℝ), (Set.Ici c).indicator (fun r : ℝ => ((1 + r) ^ 4)⁻¹) r)
      = 1 / (3 * (1 + c) ^ 3) := by
  rw [setIntegral_indicator measurableSet_Ici]
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · rw [← hc0]
    have hset : Set.Ioi (0 : ℝ) ∩ Set.Ici 0 = Set.Ioi 0 := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, le_of_lt h⟩
    rw [hset]
    exact integral_Ioi_inv_one_add_pow_four 0 le_rfl
  · have hset : Set.Ioi (0 : ℝ) ∩ Set.Ici c = Set.Ici c := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨lt_of_lt_of_le hcpos h, h⟩
    rw [hset, setIntegral_congr_set Ioi_ae_eq_Ici.symm]
    exact integral_Ioi_inv_one_add_pow_four c hc

theorem radialDecay4 (L : ℝ) (hL : 0 ≤ L) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        if L ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) else 0)
      ∧ (∫ p : EuclideanSpace ℝ (Fin 3),
          (if L ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) else 0))
          ≤ 4 * Real.pi / (1 + L) ^ 3 := by
  -- the radial profile of the integrand
  set g : ℝ → ℝ := fun r => if L ≤ r then (r ^ 2)⁻¹ * ((1 + r) ^ 4)⁻¹ else 0 with hg
  have hgval : ∀ r : ℝ, g r = if L ≤ r then (r ^ 2)⁻¹ * ((1 + r) ^ 4)⁻¹ else 0 := by
    intro r; rw [hg]
  -- pointwise identification of the integrand with `g ‖p‖`
  have hpoint : ∀ p : ℝ³,
      (if L ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) else 0) = g ‖p‖ := by
    intro p
    rw [hgval]
    by_cases h : L ≤ ‖p‖
    · rw [if_pos h, if_pos h, one_div, mul_inv, mul_comm]
    · rw [if_neg h, if_neg h]
  have hfun : (fun p : ℝ³ =>
        (if L ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) else 0)) = (fun p : ℝ³ => g ‖p‖) :=
    funext hpoint
  -- integrability of the (untruncated) radial majorant
  have hmaj : Integrable (fun p : ℝ³ => (‖p‖ ^ 2)⁻¹ * ((1 + ‖p‖) ^ 4)⁻¹) := by
    refine (Submission.BoseGases.integrable_radial_r3 (f := fun r : ℝ =>
      (r ^ 2)⁻¹ * ((1 + r) ^ 4)⁻¹)).mpr ?_
    refine (integrableOn_Ioi_inv_one_add_pow_four 0 (by norm_num)).congr_fun ?_ measurableSet_Ioi
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hr)
    show ((1 + r) ^ 4)⁻¹ = r ^ 2 * ((r ^ 2)⁻¹ * ((1 + r) ^ 4)⁻¹)
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr0), one_mul]
  -- integrability of the truncated integrand, by domination
  have htrunc : Integrable (fun p : ℝ³ =>
      (if L ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) else 0)) := by
    rw [hfun]
    refine Integrable.mono' hmaj ?_ ?_
    · have hgm : Measurable g := by
        rw [hg]
        exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const
      exact (hgm.comp measurable_norm).aestronglyMeasurable
    · filter_upwards with p
      rw [hgval]
      by_cases h : L ≤ ‖p‖
      · rw [if_pos h, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
            (inv_nonneg.mpr (pow_nonneg (by positivity) 4)))]
      · rw [if_neg h]
        have hp : (0 : ℝ) ≤ (‖p‖ ^ 2)⁻¹ * ((1 + ‖p‖) ^ 4)⁻¹ := by positivity
        simpa using hp
  refine ⟨htrunc, ?_⟩
  -- the exact value of the integral
  have hstep : (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
      = ∫ r in Set.Ioi (0 : ℝ), (if L ≤ r then ((1 + r) ^ 4)⁻¹ else 0) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hr)
    show r ^ 2 * g r = (if L ≤ r then ((1 + r) ^ 4)⁻¹ else 0)
    rw [hgval]
    by_cases h : L ≤ r
    · rw [if_pos h, if_pos h, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hr0), one_mul]
    · rw [if_neg h, if_neg h, mul_zero]
  have hiv : (∫ r in Set.Ioi (0 : ℝ), (if L ≤ r then ((1 + r) ^ 4)⁻¹ else 0))
      = 1 / (3 * (1 + L) ^ 3) := by
    have hfe : (fun r : ℝ => (if L ≤ r then ((1 + r) ^ 4)⁻¹ else 0))
        = (Set.Ici L).indicator (fun r : ℝ => ((1 + r) ^ 4)⁻¹) := by
      funext r
      by_cases h : L ≤ r <;> simp [h]
    rw [hfe]
    exact setIntegral_Ioi_zero_indicator_Ici L hL
  have hval : (∫ p : ℝ³, (if L ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) else 0))
      = 4 * Real.pi * (1 / (3 * (1 + L) ^ 3)) := by
    calc (∫ p : ℝ³, (if L ≤ ‖p‖ then 1 / ((1 + ‖p‖) ^ 4 * ‖p‖ ^ 2) else 0))
        = ∫ p : ℝ³, g ‖p‖ := integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = 4 * Real.pi * (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r) :=
            Submission.BoseGases.integral_fun_norm_r3 (g := g)
      _ = 4 * Real.pi * (∫ r in Set.Ioi (0 : ℝ), (if L ≤ r then ((1 + r) ^ 4)⁻¹ else 0)) := by
            rw [hstep]
      _ = 4 * Real.pi * (1 / (3 * (1 + L) ^ 3)) := by rw [hiv]
  rw [hval]
  have hle : 1 / (3 * (1 + L) ^ 3) ≤ 1 / (1 + L) ^ 3 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith [pow_pos (by linarith : (0 : ℝ) < 1 + L) 3]
  calc 4 * Real.pi * (1 / (3 * (1 + L) ^ 3))
      ≤ 4 * Real.pi * (1 / (1 + L) ^ 3) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 4 * Real.pi / (1 + L) ^ 3 := by rw [mul_one_div]

end Work.BoseRowsFS.LatRiemann
