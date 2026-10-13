/-
# `xProdIntLe` — the mixed-slot `ℋ⁶` integral bound of the coefficient row

The level-six coefficient row `row_N_pair` prices its coefficient slot with the two angular
averages appearing in `xSliceAgmon5`:

`z ↦ w(z)² · ( (4/π) ∫_θ (D_z^5 A)² + (200/(γ-1)) ∫_θ sin(2θ)^{-γ} (D_z^5D_θ A)² )`.

`xSliceAgmon5` shows that the first term bounds `(D_z^5 A z θ)²` pointwise, and this file
shows that *integrated in `z`* the whole expression is dominated by the `ℋ⁶`-square, with the
same two coefficients — i.e. `HkSq α 6 A` already contains both angular averages, so the
pricing is Cauchy–Schwarz-optimal and loses only the (fixed) factor `4/π + 200/(γ-1)`.

## The mathematics

`HkIntegrand α 6 A` is a sum of nonnegative slots, and near every interior angle
`sin(2θ) ≤ 1` so `sin(2θ)^{-η} ≥ 1`.  Hence, pointwise for `z ∈ Iz` and a.e. `θ`,

* `w(z)² (D_z^5A)² ≤ (D_z^5A · w(z)/sin(2θ)^{η/2})² ≤ HkIntegrand`  (the `i = 5` pure slot);
* `w(z)² sin(2θ)^{-γ} (D_z^5D_θA)² = (D_z^5D_θA · Wt)² ≤ HkIntegrand`     (the `(i,j) = (1,5)`
  mixed slot).

Integrating over `θ` and using `∫_θ c · f = c ∫_θ f` gives, for every `z ∈ Iz`,

`w(z)² · ( (4/π)F₁(z) + (200/(γ-1))F₂(z) ) ≤ (4/π + 200/(γ-1)) ∫_θ HkIntegrand α 6 A z θ`,

and integrating over `z ∈ Iz` against `volume` (monotone comparison against the integrable
`z ↦ ∫_θ HkIntegrand`, supplied by `HkMem α 6 A`) gives the stated inequality.  Integrability of
the left-hand side follows from the same pointwise domination plus the a.e. strong measurability
of the two angular averages, which are integrals of functions continuous on the open quadrant.

The development is complete and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.HkProdOpen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

/-- The open interval `(0,π/2)` is conull in `Iθ = [0,π/2]`: it differs from `Iθ` only at the
two endpoints. -/
private theorem xProdIntLe_ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  show ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))), θ ∈ Set.Ioo 0 (π / 2)
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)

/-- **The pure `D_z`-slot comparison.**  For an interior angle (`sin 2θ > 0`) the weighted
square `w(z)²(D_z^iA)²` is dominated by the `ℋ⁶`-integrand, because `sin(2θ)^{-η} ≥ 1` there
and the weighted square `(D_z^iA · w/sin(2θ)^{η/2})²` is one of the summands of `HkIntegrand`. -/
private theorem xProdIntLe_w_sq_dzIter_sq_le (α : ℝ) (A : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hsin : 0 < Real.sin (2 * θ)) (i : ℕ) (hi : i ≤ 6) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter i A z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 A z θ := by
  have h1 := Work.Spaces.sq_le_HkIntegrand_z α 6 A z θ i hi
  have hid : (Work.Spaces.DzIter i A z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter i A z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    Work.Spaces.sq_mul_div_rpow (Work.Spaces.DzIter i A z θ) (Work.Spaces.w z)
      (Real.sin (2 * θ)) Work.Spaces.eta (le_of_lt hsin) (by norm_num [Work.Spaces.eta])
  rw [hid] at h1
  have hone : 1 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hsin (Real.sin_le_one (2 * θ))
      (show -(Work.Spaces.eta) ≤ 0 by norm_num [Work.Spaces.eta])
    simpa using h
  calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter i A z θ) ^ 2
      = (Work.Spaces.DzIter i A z θ) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
    _ ≤ (Work.Spaces.DzIter i A z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
        le_mul_of_one_le_right (by positivity) hone
    _ ≤ Work.Spaces.HkIntegrand α 6 A z θ := h1

/-- **The mixed-slot comparison.**  The weighted square `w(z)² sin(2θ)^{-γ}(D_z^5D_θA)²` is
exactly the square of the `(i,j) = (1,5)` summand of `HkIntegrand` (all angles, the boundary
values being `0` on both sides), hence is dominated by the whole integrand. -/
private theorem xProdIntLe_w_sq_mixed_sq_le (α : ℝ) (A : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hsin : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 5 1 A z θ) ^ 2)
      ≤ Work.Spaces.HkIntegrand α 6 A z θ := by
  have h1 := Work.Spaces.sq_le_HkIntegrand_mixed α 6 A z θ 1 5 (le_refl 1) (by norm_num)
  have hs2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [sq, ← Real.rpow_add hsin,
      show -(Work.Spaces.gam α / 2) + -(Work.Spaces.gam α / 2) = -(Work.Spaces.gam α) by ring]
  have hid : (Work.Spaces.mixed 5 1 A z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 5 1 A z θ) ^ 2) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, hs2]
    ring
  rwa [hid] at h1

/-- **The pointwise-in-`z` comparison**: for `z ∈ Iz` the `θ`-integrated combination of the two
angular averages is dominated by the `θ`-integral of the whole `ℋ⁶`-integrand, with the same
coefficients `4/π` and `200/(γ-1)`. -/
private theorem xProdIntLe_key (α : ℝ) (A : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hmem : Work.Spaces.HkMem α 6 A) :
    ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2
        * ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2))
      ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ) := by
  have hgam : Work.Spaces.gam α - 1 = α / 10 := by rw [Work.Spaces.gam]; ring
  have h200 : 0 ≤ 200 / (Work.Spaces.gam α - 1) := by rw [hgam]; positivity
  have h4pi : 0 ≤ 4 / Real.pi := by positivity
  have hIoo := xProdIntLe_ae_mem_Ioo_Iθ
  intro z hz
  have hstep1 : (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hmem.1 z hz) ?_
    filter_upwards [hIoo] with θ hθ
    exact xProdIntLe_w_sq_dzIter_sq_le α A
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
      5 (by norm_num)
  have hstep2 : (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 5 1 A z θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z hz) ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => ?_
      exact mul_nonneg (sq_nonneg _) (mul_nonneg
        (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos])) _) (sq_nonneg _))
    · filter_upwards [hIoo] with θ hθ
      exact xProdIntLe_w_sq_mixed_sq_le α A
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  calc (Work.Spaces.w z) ^ 2
        * ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2))
      = (4 / Real.pi) * ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2))
        + (200 / (Work.Spaces.gam α - 1)) * ((Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2)) := by ring
    _ ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ)
        + (200 / (Work.Spaces.gam α - 1))
          * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ) :=
        add_le_add (mul_le_mul_of_nonneg_left hstep1 h4pi)
          (mul_le_mul_of_nonneg_left hstep2 h200)
    _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ) := by ring

/-- The two angular averages are a.e. strongly measurable functions of `z` on `Iz`: each is the
`θ`-integral of a function continuous on the open quadrant `(0,∞) × (0,π/2)`, and that quadrant
is conull inside `Iz × Iθ`. -/
private theorem xProdIntLe_aesm_averages (α : ℝ) (A : ℝ → ℝ → ℝ)
    (hso : Work.FTS.EllipticEst.SmoothOpen A) :
    AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) ∧
      AEStronglyMeasurable
        (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed 5 1 A z θ) ^ 2)
        (volume.restrict Work.Spaces.Iz) := by
  have hsin : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) : Set (ℝ × ℝ)),
      0 < Real.sin (2 * p.2) := by
    intro p hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])
  refine ⟨?_, ?_⟩
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter 5 A p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := ((hso.DzIter 5).forall 0).continuousOn.pow 2
    exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  · have hcont : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 5 1 A p.1 p.2) ^ 2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      (((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsin p hp)))).mul
        (((hso.mixed 5 1).forall 0).continuousOn.pow 2)
    exact (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'

/-- The radial weight `w(z)²` is measurable (division by `z²` is measurable on `ℝ`); it is the
only `z`-dependent factor besides the two angular averages. -/
private theorem xProdIntLe_aesm_w_sq :
    AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
  have hmeas : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
    rw [show (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 from by funext z; rfl]
    fun_prop
  exact hmeas.aestronglyMeasurable

theorem xProdIntLe : ∀ (α : ℝ) (A : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 6 A →
    MeasureTheory.Integrable (fun z : ℝ => (Work.Spaces.w z) ^ 2
        * ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) ∧
    (∫ z, (Work.Spaces.w z) ^ 2
        * ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
          + (200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                * (Work.Spaces.mixed 5 1 A z θ) ^ 2))
      ∂(MeasureTheory.volume.restrict Work.Spaces.Iz))
      ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 6 A := by
  intro α A hα hα1 hso hmem
  have hgam : Work.Spaces.gam α - 1 = α / 10 := by rw [Work.Spaces.gam]; ring
  have h200 : 0 ≤ 200 / (Work.Spaces.gam α - 1) := by rw [hgam]; positivity
  have h4pi : 0 ≤ 4 / Real.pi := by positivity
  have hkey := xProdIntLe_key α A hα hmem
  have hsinNN : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  -- nonnegativity of the integrand
  have hGnn : ∀ z : ℝ, 0 ≤ (Work.Spaces.w z) ^ 2
      * ((4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter 5 A z θ) ^ 2)
        + (200 / (Work.Spaces.gam α - 1))
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed 5 1 A z θ) ^ 2)) := by
    intro z
    refine mul_nonneg (sq_nonneg _) (add_nonneg (mul_nonneg h4pi ?_) (mul_nonneg h200 ?_))
    · exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
    · exact MeasureTheory.integral_nonneg_of_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
          mul_nonneg (Real.rpow_nonneg (hsinNN θ hθ) _) (sq_nonneg _))
  -- the dominating integrable function
  have hdom : MeasureTheory.Integrable (fun z : ℝ =>
      (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6 A z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
  obtain ⟨haesm1, haesm2⟩ := xProdIntLe_aesm_averages α A hso
  have haesmW := xProdIntLe_aesm_w_sq
  constructor
  · refine MeasureTheory.Integrable.mono' hdom (haesmW.mul ?_) ?_
    · exact (haesm1.const_mul (4 / Real.pi)).add
        (haesm2.const_mul (200 / (Work.Spaces.gam α - 1)))
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => ?_
      rw [Real.norm_of_nonneg (hGnn z)]
      exact hkey z hz
  · have hmono := MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall hGnn) hdom
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hkey)
    rw [MeasureTheory.integral_const_mul] at hmono
    rw [Work.Spaces.HkSq]
    exact hmono

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
