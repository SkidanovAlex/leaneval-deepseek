/-
# `Work.FTS.EllSol.EllPkgAux.mollHdom` — local integrability of the slice functional

The uncurried integrand of the double mollification is `Hxyc G t s = Qext G (e^t) s`, the
doubly-odd extension of the angular slice of `G` at the logarithmic radial variable `t`.  The
slice functional

  `F t = ∫_{Iθ} |Hxyc G t s| ds`

is the object whose local integrability is needed by the Fubini-type manipulations in the
Fatou step of the open-quadrant interpolation estimate.

The proof is a *domination* argument:

* on the open angular interval the doubly-odd extension is the slice itself,
  `|Qext G w s| = |G w s|`, so the hypothesis `hsl` gives `|Qext G w s| ≤ C · MGf G w`;
* hence `F t ≤ C · (π/2) · MGf G (e^t)`, and it suffices to see that
  `t ↦ MGf G (e^t)` is locally integrable;
* since `MGf G` is integrable on compact subintervals of `(0, ∞)` (`hint`) and `t ↦ e^t` is a
  diffeomorphism `ℝ ≃ (0, ∞)` whose Jacobian `e^t` is bounded below on each bounded interval,
  the substitution rule `intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg` gives
  the claim;
* the actual kernel of the argument is the *Fubini* step: on a compact interval `K ∋ x` the
  function `(t, s) ↦ |G (e^t) s|` (extended by zero off the strip `s ∈ (0, π/2)`) is jointly
  a.e. strongly measurable and dominated by the integrable function
  `p ↦ C · MGf G (e^{p.1})`, hence integrable on `K × Iθ`; Tonelli/Fubini
  (`Integrable.integral_prod_left`) then yields the integrability of the slice functional on
  `K`.  This is the one-dimensional counterpart of
  `Work.FTS.EllSol.EllPkgAux.MollSmooth.Hxy_quad_locallyIntegrable`.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-! ## The zero-extended angular slice -/

/-- The angular slice of `G` at the logarithmic radial variable `t`, extended by zero off the
open angular interval `(0, π/2)`.  This is the integrand of the slice functional. -/
def sliceAbs (G : ℝ → ℝ → ℝ) (t s : ℝ) : ℝ :=
  if s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) then |G (Real.exp t) s| else 0

theorem sliceAbs_of_mem (G : ℝ → ℝ → ℝ) {t s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    sliceAbs G t s = |G (Real.exp t) s| := by
  rw [sliceAbs, ite_eq_left hs]

theorem sliceAbs_of_notMem (G : ℝ → ℝ → ℝ) {t s : ℝ}
    (hs : s ∉ Set.Ioo (0 : ℝ) (Real.pi / 2)) : sliceAbs G t s = 0 := by
  rw [sliceAbs, ite_eq_right hs]

/-- The closed and the open angular interval give the same restricted measure. -/
theorem restrict_Iθ_eq_restrict_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  rw [Work.Spaces.Iθ]
  exact (Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))).symm

/-! ## The main theorem -/

theorem mollHdom (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) (C : ℝ) (hC : 0 < C) (hsl : ∀ w : ℝ, 0 < w → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |G w θ| ≤ C * Work.FTS.EllSol.EllPkgAux.MGf G w) (hint : ∀ a b : ℝ, 0 < a → a ≤ b → MeasureTheory.IntegrableOn (Work.FTS.EllSol.EllPkgAux.MGf G) (Set.Icc a b)) : MeasureTheory.LocallyIntegrable (fun t : ℝ => ∫ s in Work.Spaces.Iθ, |Work.FTS.EllSol.EllPkgAux.Hxyc G t s|) MeasureTheory.volume := by
  -- `MGf G` is nonnegative.
  have hMGnn : ∀ w : ℝ, 0 ≤ MGf G w := by
    intro w
    have h2 : (0 : ℝ) ≤ |G w (Real.pi / 4)| := abs_nonneg _
    have h3 : (0 : ℝ) ≤ |Work.Spaces.pth G w (Real.pi / 4)| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ Real.sqrt (E2s G w) := Real.sqrt_nonneg _
    simp only [MGf]
    linarith
  -- The angular interval has finite measure.
  have hFinθ : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) :=
    ⟨by rw [Measure.restrict_apply_univ, Work.Spaces.Iθ, Real.volume_Icc, sub_zero]
        exact ENNReal.ofReal_lt_top⟩
  -- `t ↦ MGf G (e^t)` is integrable on every bounded interval (substitution, `e^t` bounded
  -- below by `e^a > 0` on `(a,b)`).
  have hExp : ∀ a b : ℝ, a < b →
      IntegrableOn (fun t : ℝ => MGf G (Real.exp t)) (Set.Ioo a b) := by
    intro a b hab
    have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := Real.exp) (f' := fun x => Real.exp x) (g := MGf G) (a := a) (b := b)
      (by fun_prop) (fun x _ => Real.hasDerivAt_exp x) (fun x _ => (Real.exp_pos x).le)
    have hR : IntervalIntegrable (MGf G) volume (Real.exp a) (Real.exp b) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (le_of_lt (Real.exp_lt_exp.mpr hab))).mpr
        ((hint (Real.exp a) (Real.exp b) (Real.exp_pos a)
          (le_of_lt (Real.exp_lt_exp.mpr hab))).mono_set Set.Ioo_subset_Icc_self)
    have hL : IntegrableOn (fun t : ℝ => MGf G (Real.exp t) * Real.exp t) (Set.Ioo a b) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (le_of_lt hab)).mp (hiff.mpr hR)
    rw [IntegrableOn] at hL ⊢
    have h2 : Integrable (fun t : ℝ => (Real.exp a)⁻¹ * (MGf G (Real.exp t) * Real.exp t))
        (volume.restrict (Set.Ioo a b)) := hL.const_mul _
    refine h2.mono' ?_ ?_
    · have hcont : Continuous (fun t : ℝ => Real.exp a * (Real.exp t)⁻¹) :=
        continuous_const.mul (Real.continuous_exp.inv₀ (fun t => Real.exp_ne_zero t))
      refine (hcont.aestronglyMeasurable.mul h2.aestronglyMeasurable).congr ?_
      filter_upwards with t
      have ha : Real.exp a ≠ 0 := Real.exp_ne_zero a
      have ht : Real.exp t ≠ 0 := Real.exp_ne_zero t
      calc Real.exp a * (Real.exp t)⁻¹ * ((Real.exp a)⁻¹ * (MGf G (Real.exp t) * Real.exp t))
          = (Real.exp t)⁻¹ * Real.exp t * (Real.exp a * (Real.exp a)⁻¹)
              * MGf G (Real.exp t) := by ring
        _ = MGf G (Real.exp t) := by rw [inv_mul_cancel₀ ht, mul_inv_cancel₀ ha]; ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hpa : 0 < Real.exp a := Real.exp_pos a
      have hlt : Real.exp a < Real.exp t := Real.exp_lt_exp.mpr ht.1
      have hge : 1 ≤ Real.exp t / Real.exp a := (one_le_div hpa).mpr hlt.le
      rw [Real.norm_of_nonneg (hMGnn _)]
      calc MGf G (Real.exp t) = MGf G (Real.exp t) * 1 := by ring
        _ ≤ MGf G (Real.exp t) * (Real.exp t / Real.exp a) :=
            mul_le_mul_of_nonneg_left hge (hMGnn _)
        _ = (Real.exp a)⁻¹ * (MGf G (Real.exp t) * Real.exp t) := by ring
  -- Main argument: on a compact interval `K` the slice functional is integrable.
  intro x
  refine ⟨Set.Ioo (x - 1) (x + 1), IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩, ?_⟩
  -- measurability of the joint integrand
  have hmeasS : MeasurableSet {p : ℝ × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} :=
    (isOpen_Ioo.preimage continuous_snd).measurableSet
  have hcontS : ContinuousOn (fun p : ℝ × ℝ => |G (Real.exp p.1) p.2|)
      {p : ℝ × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} := by
    have hmp : MapsTo (fun p : ℝ × ℝ => (Real.exp p.1, p.2))
        {p : ℝ × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} Work.FTS.EllipticEst.Q0 := by
      intro p hp
      rw [Work.FTS.EllipticEst.mem_Q0]
      exact ⟨Real.exp_pos p.1, hp.1, hp.2⟩
    exact (hS.continuousOn.comp (by fun_prop) hmp).abs
  have hmeasF : AEStronglyMeasurable (Function.uncurry (sliceAbs G))
      ((volume.restrict (Set.Ioo (x - 1) (x + 1))).prod (volume.restrict Work.Spaces.Iθ)) := by
    have h1 : AEStronglyMeasurable
        (Set.indicator {p : ℝ × ℝ | p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)}
          (fun p : ℝ × ℝ => |G (Real.exp p.1) p.2|))
        ((volume.restrict (Set.Ioo (x - 1) (x + 1))).prod (volume.restrict Work.Spaces.Iθ)) :=
      (aestronglyMeasurable_indicator_iff hmeasS).mpr (hcontS.aestronglyMeasurable hmeasS)
    refine h1.congr ?_
    filter_upwards with p
    by_cases hp : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · rw [Set.indicator_of_mem
        (show p ∈ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} from hp)]
      show |G (Real.exp p.1) p.2| = sliceAbs G p.1 p.2
      rw [sliceAbs_of_mem G hp]
    · rw [Set.indicator_of_notMem
        (show p ∉ {q : ℝ × ℝ | q.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} from hp)]
      show (0 : ℝ) = sliceAbs G p.1 p.2
      rw [sliceAbs_of_notMem G hp]
  -- integrability of the dominating function on the product
  have hDomInt : Integrable (fun p : ℝ × ℝ => C * MGf G (Real.exp p.1))
      ((volume.restrict (Set.Ioo (x - 1) (x + 1))).prod (volume.restrict Work.Spaces.Iθ)) :=
    ((hExp (x - 1) (x + 1) (by linarith)).comp_fst
      (volume.restrict Work.Spaces.Iθ)).const_mul C
  -- the joint integrand is integrable
  have hFInt : Integrable (Function.uncurry (sliceAbs G))
      ((volume.restrict (Set.Ioo (x - 1) (x + 1))).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine hDomInt.mono' hmeasF (Eventually.of_forall (fun p => ?_))
    by_cases hp : p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · have hval : ‖Function.uncurry (sliceAbs G) p‖ = |G (Real.exp p.1) p.2| := by
        show ‖sliceAbs G p.1 p.2‖ = |G (Real.exp p.1) p.2|
        rw [sliceAbs_of_mem G hp, Real.norm_eq_abs, abs_abs]
      rw [hval]
      exact hsl (Real.exp p.1) (Real.exp_pos p.1) p.2 hp.1 hp.2
    · have hval : ‖Function.uncurry (sliceAbs G) p‖ = 0 := by
        show ‖sliceAbs G p.1 p.2‖ = 0
        rw [sliceAbs_of_notMem G hp, norm_zero]
      rw [hval]
      exact mul_nonneg (le_of_lt hC) (hMGnn _)
  -- Fubini
  have hFub := hFInt.integral_prod_left
  refine hFub.congr (Eventually.of_forall (fun t => ?_))
  rw [restrict_Iθ_eq_restrict_Ioo]
  refine setIntegral_congr_ae measurableSet_Ioo (Eventually.of_forall (fun s hs => ?_))
  show sliceAbs G t s = |Hxyc G t s|
  rw [sliceAbs_of_mem G hs, Hxyc,
    Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G (Real.exp t) s (Set.Ioo_subset_Icc_self hs)]

end Work.FTS.EllSol.EllPkgAux
