/-
Copyright: work module for the Elgindi finite-time singularity project.

# Local integrability of the angular moment `F_*(D_z^j F)`

This module proves `Work.FTS.EllipticEst.GbarSin.Fstar_local_integrableOn`: for a source `F`
which is `C^∞` on the open quadrant `Q0 = (0,∞) × (0,π/2)`
(`Work.FTS.EllipticEst.SmoothOpen`) and which lies in the weighted space `ℋ^k`
(`Work.Spaces.HkMem`), and for every `j ≤ k`, the angular moment

  `U_j(r) = F_*(D_z^j F)(r) = ∫_θ D_z^j F(r,θ) · sinθcos²θ dθ`

is locally integrable on `(0,∞)`, both against `dr/r` and against the weight `s^{5/α-1} ds`
appearing in the Hardy operator `HarOp (5/α)` of `Work.Elliptic.Gbar`.  These are the two
integrability side conditions needed by the integration by parts of §'Elliptic Regularity
Estimates' (Elgindi, Annals of Math. **194** (2021)).

## Proof

The single analytic input is the Cauchy–Schwarz bound `FstarDzIter_sq_mul_w_le_open`

  `U_j(r)² · w(r)² ≤ (π/2) · ∫_θ (D_z^j F(r,θ)·w(r)/sin(2θ)^{η/2})² dθ`,   `r > 0`,

combined with the fact that the `j`-th summand of the `H^k`-integrand is dominated by the
whole integrand (`Work.Spaces.sq_le_HkIntegrand_z`), so that the right-hand side is at most
`(π/2)·G(r)` with `G(r) = ∫_θ HkIntegrand α k F r θ`, an integrable function of `r` by
`HkMem`.  Since `w(r) = (1+r)²/r²` and hence `r·w(r) = (1+r)²/r ≥ 1`, the bound gives
`|U_j(r)|/r ≤ √((π/2)·G(r))`, and the AM–GM inequality `√X ≤ (X+1)/2` turns this into the
`L¹` bound `|U_j(r)|/r ≤ ((π/2)·G(r) + 1)/2`.  Integrating over `(0,z)` gives the first
claim.  For the second, `s^{5/α-1}·U_j(s)` is dominated on `(0,z]` by
`z^{5/α}·((π/2)·G(s) + 1)/2` — here `α ≤ 1` is used only to make the exponent `5/α - 1`
nonnegative, so that `s^{5/α-1} ≤ z^{5/α-1}` — and the same `L¹` bound applies.

All the measurability inputs come from continuity on the open quadrant
(`aestronglyMeasurable_integral_Itheta_Q0`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.GbarSin

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary estimates -/

/-- AM–GM in the form used below: `√X ≤ (X + 1)/2` for `X ≥ 0`. -/
theorem sqrt_le_add_one_div_two {X : ℝ} (hX : 0 ≤ X) : Real.sqrt X ≤ (X + 1) / 2 := by
  rw [Real.sqrt_le_iff]
  exact ⟨by positivity, by nlinarith [sq_nonneg (1 - X)]⟩

/-- The `j`-th summand of the `H^k`-integrand of the source, integrated over the angle, is
dominated by the full angular slice of the `H^k`-integrand. -/
theorem slice_le_HkIntegrand (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {r : ℝ} (hr : r ∈ Work.Spaces.Iz) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter j F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ :=
  integral_mono_of_nonneg
    (Eventually.of_forall fun θ =>
      sq_nonneg (Work.Spaces.DzIter j F r θ
        * (Work.Spaces.w r / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))
    (hmem.1 r hr)
    (Eventually.of_forall fun θ => Work.Spaces.sq_le_HkIntegrand_z α k F r θ j hj)

/-! ## The pointwise Cauchy–Schwarz bound for the angular moment -/

/-- **The `L¹` bound for the angular moment.**  For `r > 0`,
`|F_*(D_z^j F)(r)|/r ≤ ((π/2)·∫_θ HkIntegrand α k F r θ + 1)/2`, the right-hand side being an
integrable function of `r` on every bounded interval of `(0,∞)`. -/
theorem Fstar_div_le_majorant (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ)
    (hj : j ≤ k) {r : ℝ} (hr : 0 < r) :
    |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r| / r
      ≤ ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) + 1) / 2 := by
  have hrI : r ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hr
  have hGnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ :=
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F r θ
  set X : ℝ := (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ)
    with hX
  have hXnn : 0 ≤ X := by rw [hX]; exact mul_nonneg (by positivity) hGnn
  -- Cauchy–Schwarz for the angular moment, with the slice dominated by the full integrand
  have hsq : (Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r) ^ 2 * (Work.Spaces.w r) ^ 2
      ≤ X := by
    rw [hX]
    exact le_trans (FstarDzIter_sq_mul_w_le_open α k F hF hmem j hj hr)
      (mul_le_mul_of_nonneg_left (slice_le_HkIntegrand α k F hmem j hj hrI) (by positivity))
  have hmul : (Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r * Work.Spaces.w r) ^ 2 ≤ X := by
    rw [mul_pow]; exact hsq
  -- `r · w(r) = (1+r)²/r ≥ 1`, so that `1/r ≤ w(r)`
  have hweight : 1 ≤ Work.Spaces.w r * r := by
    rw [Work.Spaces.w]
    field_simp
    nlinarith [hr, sq_nonneg r, pow_pos hr 3]
  have hw_pos : 0 < Work.Spaces.w r := by rw [Work.Spaces.w]; positivity
  have h1r : r⁻¹ ≤ Work.Spaces.w r := by
    have h : 1 / r ≤ Work.Spaces.w r := (div_le_iff₀ hr).mpr hweight
    simpa only [one_div] using h
  calc |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r| / r
      = |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r| * r⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r| * Work.Spaces.w r :=
        mul_le_mul_of_nonneg_left h1r (abs_nonneg _)
    _ = |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r * Work.Spaces.w r| := by
        rw [abs_mul, abs_of_nonneg hw_pos.le]
    _ = Real.sqrt ((Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r * Work.Spaces.w r) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt X := Real.sqrt_le_sqrt hmul
    _ ≤ (X + 1) / 2 := sqrt_le_add_one_div_two hXnn
    _ = ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ) + 1) / 2 := by
        rw [hX]

/-! ## Measurability of the angular moment -/

/-- The angular moment `r ↦ F_*(D_z^j F)(r)` is a.e. strongly measurable on `(0,∞)`: it is the
integral over `θ` of a function continuous on the open quadrant. -/
theorem Fstar_aesm (F : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen F) (j : ℕ) :
    AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r)
      (volume.restrict (Set.Ioi 0)) := by
  have hcont : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ := by
    show ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ
    exact ((Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn).mono
      (Set.subset_univ _)
  have h := aestronglyMeasurable_integral_Itheta_Q0 (Work.Spaces.DzIter j F)
    ((hF.DzIter j).continuousOn) Work.Elliptic.sinCos2 hcont
  change AEStronglyMeasurable (fun r : ℝ => ∫ θ in Work.Spaces.Iθ,
    Work.Spaces.DzIter j F r θ * Work.Elliptic.sinCos2 θ) (volume.restrict (Set.Ioi 0))
  exact h

/-- `r ↦ F_*(D_z^j F)(r)/r` is a.e. strongly measurable on any `(0,z)`. -/
theorem Fstar_div_aesm (F : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen F) (j : ℕ)
    {z : ℝ} :
    AEStronglyMeasurable (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r)
      (volume.restrict (Set.Ioo 0 z)) := by
  have hmom : AEStronglyMeasurable
      (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r)
      (volume.restrict (Set.Ioo 0 z)) :=
    (Fstar_aesm F hF j).mono_measure (Measure.restrict_mono (fun r hr => hr.1) le_rfl)
  have hinv : AEStronglyMeasurable (fun r : ℝ => r⁻¹) (volume.restrict (Set.Ioo 0 z)) :=
    (continuousOn_id.inv₀ (fun _ hr => ne_of_gt hr.1)).aestronglyMeasurable measurableSet_Ioo
  exact hmom.mul hinv

/-- `s ↦ F_*(D_z^j F)(s)` is a.e. strongly measurable on any `(0,z]`. -/
theorem Fstar_aesm_Ioc (F : ℝ → ℝ → ℝ) (hF : Work.FTS.EllipticEst.SmoothOpen F) (j : ℕ)
    {z : ℝ} :
    AEStronglyMeasurable (fun s : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s)
      (volume.restrict (Set.Ioc 0 z)) :=
  (Fstar_aesm F hF j).mono_measure (Measure.restrict_mono (fun _ hr => hr.1) le_rfl)

/-! ## Integrability of the majorant -/

/-- **The majorant is integrable** on every measurable subset of `[0,∞)` of finite measure:
this is just `HkMem` together with the finiteness of `∫_θ HkIntegrand α k F r θ`. -/
theorem majorant_integrableOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k F) {s : Set ℝ} (hs : s ⊆ Work.Spaces.Iz)
    (hvol : volume s ≠ ⊤) :
    IntegrableOn (fun r : ℝ => ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F r θ) + 1) / 2) s := by
  have hG : IntegrableOn (fun r : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F r θ) s := hmem.2.mono_set hs
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) s :=
    integrableOn_const (s := s) (C := (1 : ℝ)) hvol
  exact ((hG.const_mul (Real.pi / 2)).add h1).div_const 2

/-- **Interval integrability of `s^p · f`** from a linear bound on `f` by an integrable
dominating function: for `p ≥ 0`, `z > 0`, `A ≥ 0` integrable on `(0,z]` and
`|f r| ≤ r·A r` there, the product `s^p · f s` is interval integrable on `[0,z]`. -/
theorem intervalIntegrable_rpow_mul_of_abs_le_mul {p z : ℝ} (hp : 0 ≤ p) (hz : 0 < z)
    {f A : ℝ → ℝ} (hA : IntegrableOn A (Set.Ioc 0 z))
    (hA0 : ∀ r ∈ Set.Ioc (0 : ℝ) z, 0 ≤ A r)
    (hAe : AEStronglyMeasurable f (volume.restrict (Set.Ioc 0 z)))
    (hbd : ∀ r ∈ Set.Ioc (0 : ℝ) z, |f r| ≤ r * A r) :
    IntervalIntegrable (fun s : ℝ => s ^ p * f s) volume 0 z := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hz.le]
  have hcont : ContinuousOn (fun s : ℝ => s ^ p) (Set.Ioc 0 z) :=
    (Real.continuous_rpow_const hp).continuousOn
  have haesm : AEStronglyMeasurable (fun s : ℝ => s ^ p * f s)
      (volume.restrict (Set.Ioc 0 z)) :=
    (hcont.aestronglyMeasurable measurableSet_Ioc).mul hAe
  refine (hA.const_mul (z ^ (p + 1))).mono' haesm ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun s hs => ?_
  have hs0 : 0 < s := hs.1
  have hsp : 0 ≤ s ^ p := Real.rpow_nonneg hs0.le p
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsp]
  calc s ^ p * |f s| ≤ s ^ p * (s * A s) := mul_le_mul_of_nonneg_left (hbd s hs) hsp
    _ = s ^ (p + 1) * A s := by
        rw [Real.rpow_add hs0 p 1, Real.rpow_one]; ring
    _ ≤ z ^ (p + 1) * A s :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hs0.le hs.2 (by linarith)) (hA0 s hs)

/-! ## The theorem -/

theorem Fstar_local_integrableOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    (∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r)
        (Set.Ioo 0 z)) ∧
    (∀ z : ℝ, 0 < z →
      IntervalIntegrable (fun s : ℝ => s ^ (5 / α - 1)
        * Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s) MeasureTheory.volume 0 z) := by
  constructor
  · intro z hz
    have hH : IntegrableOn (fun r : ℝ => ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F r θ) + 1) / 2) (Set.Ioo 0 z) :=
      majorant_integrableOn α k F hmem (fun r hr => by rw [Work.Spaces.Iz]; exact le_of_lt hr.1)
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    refine hH.mono' (Fstar_div_aesm F hF j) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun r hr => ?_
    have hr0 : 0 < r := hr.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]
    exact Fstar_div_le_majorant α k F hF hmem j hj hr0
  · intro z hz
    have hp : 0 ≤ (5 : ℝ) / α - 1 := by
      have h5 : (1 : ℝ) ≤ 5 / α := (le_div_iff₀ hα).mpr (by linarith)
      linarith
    have hH : IntegrableOn (fun r : ℝ => ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F r θ) + 1) / 2) (Set.Ioc 0 z) :=
      majorant_integrableOn α k F hmem (fun r hr => by rw [Work.Spaces.Iz]; exact le_of_lt hr.1)
        (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hA0 : ∀ r ∈ Set.Ioc (0 : ℝ) z, 0 ≤ ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F r θ) + 1) / 2 := by
      intro r _
      have hGnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F r θ :=
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F r θ
      have hπ : (0 : ℝ) ≤ Real.pi / 2 := by positivity
      exact div_nonneg (by linarith [mul_nonneg hπ hGnn]) (by norm_num)
    have hbd : ∀ r ∈ Set.Ioc (0 : ℝ) z,
        |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r|
          ≤ r * (((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k F r θ) + 1) / 2) := by
      intro r hr
      have hr0 : 0 < r := hr.1
      calc |Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r|
          ≤ (((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k F r θ) + 1) / 2) * r :=
            (div_le_iff₀ hr0).mp (Fstar_div_le_majorant α k F hF hmem j hj hr0)
        _ = r * (((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k F r θ) + 1) / 2) := by ring
    exact intervalIntegrable_rpow_mul_of_abs_le_mul (p := 5 / α - 1) (z := z)
      (f := fun s : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s)
      (A := fun s : ℝ => ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F s θ) + 1) / 2) hp hz hH hA0 (Fstar_aesm_Ioc F hF j) hbd

end Work.FTS.EllipticEst.GbarSin
