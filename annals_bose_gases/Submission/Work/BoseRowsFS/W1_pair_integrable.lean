import ChallengeDeps
import Submission.Work.BoseRowsFS.W1_g0_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.W1_pair_integrable`

Bochner-integrability, on the product measure `volume × volume`, of the Coulomb (Newtonian)
pair kernel of the renormalised one-body kernel `W₁ = wScaled ℓ (g₀ v h) = W1fun v h ℓ`:

  `(p : ℝ³ × ℝ³) ↦ W₁ p.1 · W₁ p.2 / ‖p.1 − p.2‖`.

This is the position-space hypothesis `hcd`/`hfin` consumed by the Newtonian-energy rows of the
FS §11 far-leg chain (`Work.BoseRowsFS.small_s_bound`, `Work.BoseRowsFS.free_eq_coulomb`,
`SmallBoxD1Assembly`), and it is one of the two sides of the classical identity
`(2π)⁻³∫ Ŵ₁(p)²/(2‖p‖²) = (1/8π)∬ W₁(x)W₁(y)/‖x − y‖`.

## Route

`Work.BoseRowsFS.W1_g0_finite` (the Newtonian self-energy of `W₁`, obtained there from the
closed-form `W₁⊗g₀` energy and the comparison `W₁⊗W₁ ≤ 2·W₁⊗g₀`) supplies the finiteness of the
*iterated* `∫⁻`

  `∫⁻ x, ∫⁻ y, ofReal (W₁ x · W₁ y / ‖x − y‖) ≠ ⊤`.

Three measure-theoretic steps turn that into Bochner integrability of the pair kernel:

* `W₁` is `L¹` and nonnegative a.e. (`wScaled_g0_integrable`, `wScaled_g0_nonneg_ae` in the dilute
  regime `R ≤ ℓ·chiR0`), hence a.e. strongly measurable;
* a.e. strong measurability of the pair kernel, and Tonelli (`MeasureTheory.lintegral_prod`)
  identify the product-measure `∫⁻` with the iterated one (both coordinates are nonnegative a.e.,
  so the `∫⁻` is the `∫⁻` of the absolute value);
* `MeasureTheory.lintegral_ofReal_ne_top_iff_integrable` concludes `Integrable`.

Note that the *evenness* and a.e.-nonnegativity of `W₁` are all that is used about it beyond
integrability — no `MemLp v 1`, no regularity of `v` beyond what `ScatSol v` gives.
-/

namespace Work.BoseRowsFS

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem W1_pair_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {R ℓ : ℝ}
    (hR : 0 < R) (hℓ : 0 < ℓ) (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixR.W1fun v h ℓ p.1 * Work.BoseFixR.W1fun v h ℓ p.2 / ‖p.1 - p.2‖) := by
  set W : E3 → ℝ := Work.BoseFixR.W1fun v h ℓ with hWdef
  -- ### `W₁` is `L¹` and nonnegative a.e.
  have hWint : MeasureTheory.Integrable W := by
    rw [hWdef]
    simpa only [Work.BoseFixR.W1fun] using
      Submission.BoseGases.wScaled_g0_integrable (v := v) (R := R) (ℓ := ℓ)
        hR hv_supp h hℓ hRℓ
  have hW0 : ∀ᵐ x : E3, 0 ≤ W x := by
    rw [hWdef]
    simpa only [Work.BoseFixR.W1fun] using
      Submission.BoseGases.wScaled_g0_nonneg_ae (v := v) (R := R) (ℓ := ℓ)
        hR hv_nonneg hvrad hv_supp h
  -- ### finiteness of the iterated `∫⁻` of the pair kernel
  have hiter : (∫⁻ x : E3, ∫⁻ y : E3, ENNReal.ofReal (W x * W y / ‖x - y‖)) ≠ ⊤ := by
    rw [hWdef]
    exact (W1_g0_finite hR hℓ hv_nonneg hvrad hv_supp h hRℓ).1
  -- ### a.e. strong measurability of the pair kernel
  have hAEW : AEMeasurable W (MeasureTheory.volume : MeasureTheory.Measure E3) :=
    hWint.aestronglyMeasurable.aemeasurable
  have hAEF : AEMeasurable (fun p : E3 × E3 => W p.1 * W p.2 / ‖p.1 - p.2‖)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    ((hAEW.comp_fst).mul (hAEW.comp_snd)).div
      ((measurable_fst.sub measurable_snd).norm.aemeasurable)
  -- ### the pair kernel is nonnegative a.e. on the product
  have hF0 : 0 ≤ᵐ[(MeasureTheory.volume.prod MeasureTheory.volume : MeasureTheory.Measure (E3 × E3))]
      (fun p : E3 × E3 => W p.1 * W p.2 / ‖p.1 - p.2‖) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hW0,
      Measure.quasiMeasurePreserving_snd.ae hW0] with p h1 h2
    exact div_nonneg (mul_nonneg h1 h2) (norm_nonneg _)
  -- ### Tonelli: the product-measure `∫⁻` equals the iterated one
  have hprod : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2 / ‖p.1 - p.2‖)
        ∂(MeasureTheory.volume.prod MeasureTheory.volume))
      = (∫⁻ x : E3, ∫⁻ y : E3, ENNReal.ofReal (W x * W y / ‖x - y‖)) :=
    MeasureTheory.lintegral_prod _ hAEF.ennreal_ofReal
  have hne : (∫⁻ p : E3 × E3, ENNReal.ofReal (W p.1 * W p.2 / ‖p.1 - p.2‖)
      ∂(MeasureTheory.volume.prod MeasureTheory.volume)) ≠ ⊤ := by
    rw [hprod]
    exact hiter
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hAEF.aestronglyMeasurable hF0).mp hne

end Work.BoseRowsFS
