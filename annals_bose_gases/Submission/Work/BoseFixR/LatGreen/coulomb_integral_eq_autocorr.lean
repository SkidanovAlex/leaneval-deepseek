import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.LatGreen.aemeasurable_shear_mul_div
import Submission.Work.BoseFixR.LatGreen.coulomb_fourier_side
import Submission.Work.BoseFixR.LatGreen.coulomb_iterated_lintegral_ne_top
import Submission.Work.BoseFixR.LatGreen.latGreen_le_inv_fourpi_infDist
import Submission.Work.BoseRowsFS.CoulShift.integral_integral_eq_toReal_lintegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.LatGreen.coulomb_integral_eq_autocorr`

**The Coulomb/Newtonian-energy identity in the autocorrelation form**

  `4 (2π)^{-3} ∫ q, Ŵ(q)²/(2‖q‖²) = (2π)^{-1} ∫ u, (∫ x, V x · V(x+u)) / ‖u‖`,

for an integrable, pointwise nonnegative, even `V : ℝ³ → ℝ` with
`tsupport V ⊆ B(0,1)` and finite momentum-space Coulomb energy
(`hint`), where `Ŵ = Work.BoseFixR.chat V` is the `p`-convention Fourier transform of `V`.

## Mathematics

The classical Newtonian-energy (Coulomb) identity relates the momentum-space energy of `V`
to the position-space pair energy.  Writing
`D := ∫ p : ℝ³ × ℝ³, V p.1 · V p.2 / ‖p.1 − p.2‖` (the pair energy) and
`I := ∫ q, Ŵ(q)²/(2‖q‖²)`, the corpus lemma
`Work.BoseB7AK.C3Q.chat_sq_div_eq_coulomb_toReal` (packaged as
`Work.BoseFixR.Rb5Lin.chat_sq_div_integral_eq_coulomb`) gives

  `(2π)^{-3} I = (8π)^{-1} D`,

which, multiplied by `4`, is `(2π)^{-1} D = 2·(2π)^{-3} ∫ Ŵ²/‖q‖²`.  The remaining step is
the *position-space* identification of `D` with the autocorrelation form appearing in the
target.  Substituting `y = x + u` in the inner integral and using Fubini,

  `D = ∫ x, ∫ y, V x V y/‖x−y‖ = ∫ u, (∫ x, V x V(x+u)) / ‖u‖`.

## Route of the position-space identity

`coulomb_pair_eq_autocorr_integral` performs the substitution `y = x + u` inside the
*inner* `∫⁻` for each `x` (`MeasureTheory.lintegral_add_left_eq_self`, no measurability
assumption needed), swaps the two `∫⁻` (`MeasureTheory.lintegral_lintegral_swap`, via the
delegated a.e.-measurability lemma `aemeasurable_shear_mul_div` for the sheared integrand
`(u,x) ↦ V x · V(x+u)/‖u‖`), and converts the iterated Bochner integral into the
`.toReal` of the iterated `∫⁻` with the corpus tool
`Work.BoseRowsFS.CoulShift.integral_integral_eq_toReal_lintegral`; finiteness of the
position-space double `∫⁻` comes from the momentum bound `hint` via
`Work.BoseRowsFS.coulomb_pair_integrable` (packaged as `coulomb_iterated_lintegral_ne_top`).

The two halves are then combined in `coulomb_integral_eq_autocorr` by rewriting the
autocorrelation integral and applying the momentum identity
`coulomb_fourier_side`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixR.LatGreen

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The inner substitution `y = x + u` in the iterated `∫⁻` -/

/-- **Substitution `y = x + u` in the inner lower integral.**  For every fixed `x`,

  `∫⁻ u, ofReal (V x * V (x+u)/‖u‖) = ∫⁻ y, ofReal (V x * V y/‖x−y‖)`,

which is translation invariance of Lebesgue measure applied to the `y`-integral
(`MeasureTheory.lintegral_add_left_eq_self`) together with `‖x − (x+u)‖ = ‖u‖`. -/
theorem lintegral_shear_eq_lintegral_separated {V : E3 → ℝ} (x : E3) :
    (∫⁻ u : E3, ENNReal.ofReal (V x * V (x + u) / ‖u‖))
      = ∫⁻ y : E3, ENNReal.ofReal (V x * V y / ‖x - y‖) := by
  rw [← MeasureTheory.lintegral_add_left_eq_self
    (fun y : E3 => ENNReal.ofReal (V x * V y / ‖x - y‖)) x]
  refine MeasureTheory.lintegral_congr (fun u => ?_)
  congr 2
  rw [show x - (x + u) = -u by abel, norm_neg]

/-- **The iterated lower integrals agree**: the sheared one (outer variable `u`) equals the
separated one.  This is `lintegral_shear_eq_lintegral_separated` integrated over `x`. -/
theorem lintegral_lintegral_shear_eq_separated {V : E3 → ℝ} :
    (∫⁻ x : E3, ∫⁻ u : E3, ENNReal.ofReal (V x * V (x + u) / ‖u‖))
      = (∫⁻ x : E3, ∫⁻ y : E3, ENNReal.ofReal (V x * V y / ‖x - y‖)) :=
  MeasureTheory.lintegral_congr (fun x => lintegral_shear_eq_lintegral_separated x)

/-! ### The position-space identity -/

/-- **The pair (Coulomb) energy is the `‖·‖⁻¹`-integral of the autocorrelation.**

For an integrable, pointwise nonnegative, even `V` with finite momentum-space Coulomb
energy (`hint`),

  `∫ p : ℝ³ × ℝ³, V p.1 V p.2/‖p.1 − p.2‖ = ∫ u, (∫ x, V x V(x+u))/‖u‖`.

Only the momentum hypothesis `hint` (through the finiteness of the position-space double
`∫⁻`, `coulomb_iterated_lintegral_ne_top`) and evenness are used besides integrability and
nonnegativity. -/
theorem coulomb_pair_eq_autocorr_integral {V : E3 → ℝ}
    (hV1 : MeasureTheory.Integrable V)
    (hVnn : ∀ x, 0 ≤ V x) (hVev : ∀ x, V (-x) = V x)
    (hint : MeasureTheory.Integrable
      (fun q : E3 => (Work.BoseFixR.chat V q) ^ 2 / (2 * ‖q‖ ^ 2))) :
    (∫ p : E3 × E3, V p.1 * V p.2 / ‖p.1 - p.2‖)
      = ∫ u : E3, (∫ x : E3, V x * V (x + u)) / ‖u‖ := by
  -- the product-measure pair integral is the `.toReal` of the iterated position `∫⁻`
  have hD : (∫ p : E3 × E3, V p.1 * V p.2 / ‖p.1 - p.2‖)
      = (∫⁻ x : E3, ∫⁻ y : E3, ENNReal.ofReal (V x * V y / ‖x - y‖)).toReal :=
    Work.BoseFixR.Rb5Lin.integral_coulomb_eq_toReal_lintegral hV1
      (Filter.Eventually.of_forall hVnn)
  -- finiteness of the position-space double `∫⁻`, from `hint`
  have hfin : (∫⁻ x : E3, ∫⁻ y : E3, ENNReal.ofReal (V x * V y / ‖x - y‖)) ≠ ⊤ :=
    coulomb_iterated_lintegral_ne_top hV1 hVnn hVev hint
  -- the swap of the two iterated `∫⁻`, using a.e.-measurability of the sheared integrand
  have hswap : (∫⁻ u : E3, ∫⁻ x : E3, ENNReal.ofReal (V x * V (x + u) / ‖u‖))
      = (∫⁻ x : E3, ∫⁻ u : E3, ENNReal.ofReal (V x * V (x + u) / ‖u‖)) :=
    MeasureTheory.lintegral_lintegral_swap
      (f := fun u x : E3 => ENNReal.ofReal (V x * V (x + u) / ‖u‖))
      (by
        change AEMeasurable (fun z : E3 × E3 =>
          ENNReal.ofReal (V z.2 * V (z.2 + z.1) / ‖z.1‖))
          (MeasureTheory.volume.prod MeasureTheory.volume)
        exact (aemeasurable_shear_mul_div hV1.aestronglyMeasurable.aemeasurable).ennreal_ofReal)
  -- the iterated Bochner integral as the `.toReal` of the iterated `∫⁻`
  have hstep2 : (∫ u : E3, ∫ x : E3, V x * V (x + u) / ‖u‖)
      = (∫⁻ u : E3, ∫⁻ x : E3, ENNReal.ofReal (V x * V (x + u) / ‖u‖)).toReal :=
    Work.BoseRowsFS.CoulShift.integral_integral_eq_toReal_lintegral
      (g := fun u x : E3 => V x * V (x + u) / ‖u‖)
      (fun u x => div_nonneg (mul_nonneg (hVnn x) (hVnn (x + u))) (norm_nonneg _))
      (by
        change AEMeasurable (fun z : E3 × E3 => V z.2 * V (z.2 + z.1) / ‖z.1‖)
          (MeasureTheory.volume.prod MeasureTheory.volume)
        exact aemeasurable_shear_mul_div hV1.aestronglyMeasurable.aemeasurable)
      (by rw [hswap, lintegral_lintegral_shear_eq_separated]; exact hfin)
  -- pull the constant `‖u‖⁻¹` out of the inner integral
  have hstep1 : (∫ u : E3, (∫ x : E3, V x * V (x + u)) / ‖u‖)
      = ∫ u : E3, ∫ x : E3, V x * V (x + u) / ‖u‖ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    exact (MeasureTheory.integral_div (μ := MeasureTheory.volume) (‖u‖)
      (fun x => V x * V (x + u))).symm
  rw [hstep1, hstep2, hswap, lintegral_lintegral_shear_eq_separated]
  exact hD

/-! ### The target identity -/

theorem coulomb_integral_eq_autocorr {V : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hV1 : MeasureTheory.Integrable V)
    (hV2 : MeasureTheory.MemLp V 2 MeasureTheory.volume)
    (hVnn : ∀ x, 0 ≤ V x) (hVev : ∀ x, V (-x) = V x)
    (hVsupp : tsupport V ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hint : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) => (Work.BoseFixR.chat V q) ^ 2 / (2 * ‖q‖ ^ 2))) :
    4 * ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ q : EuclideanSpace ℝ (Fin 3), (Work.BoseFixR.chat V q) ^ 2 / (2 * ‖q‖ ^ 2)
      = (2 * Real.pi)⁻¹ * ∫ u : EuclideanSpace ℝ (Fin 3),
          (∫ x : EuclideanSpace ℝ (Fin 3), V x * V (x + u)) / ‖u‖ := by
  rw [← coulomb_pair_eq_autocorr_integral hV1 hVnn hVev hint]
  exact coulomb_fourier_side hV1 hVnn hVev hint

end Work.BoseFixR.LatGreen
