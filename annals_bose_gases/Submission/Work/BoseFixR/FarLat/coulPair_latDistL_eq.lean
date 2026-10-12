import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixR.FarLatDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FarLat.coulPair_latDistL_eq`

The double integral of a pair kernel depending only on the *difference* `q.1 - q.2` is, by the
substitution `(q₁, q₂) ↦ (q₁ + q₂, q₂)` in the product measure, the iterated integral of the
"convolution in the difference variable":

    ∫∫ W q₁ W q₂ / latDistL (q₁ - q₂) = ∫ z (∫ x W x W (x + z)) / latDistL z .

The transformation `(x, z) ↦ (x + z, z)` is the additive shear: it is a measurable equivalence of
`ℝ³ × ℝ³` with measurable inverse `(u, v) ↦ (u - v, v)`, and it preserves the Lebesgue product
measure (`MeasureTheory.measurePreserving_add_prod`).  It maps the integrand
`W q₁ W q₂ / latDistL (q₁ - q₂)` exactly to `W (x + z) W z / latDistL x`, i.e. into the shape in
which Fubini (`MeasureTheory.integral_prod`) applies and the `x`-dependent weight
`(latDistL x)⁻¹` can be pulled out of the inner integral (`MeasureTheory.integral_mul_const`).

The hypothesis `hfin` (finiteness of the `lintegral` of the pointwise value — the integrand is
nonnegative a.e. because `W ≥ 0` a.e. and `latDistL ≥ 0`) is exactly what makes the Bochner
integral finite, so that the Fubini step is legitimate: it is converted into
`MeasureTheory.Integrable` of the integrand on the product measure via
`MeasureTheory.lintegral_ofReal_ne_top_iff_integrable`, and then transported across the shear by
`MeasureTheory.MeasurePreserving.integrable_comp`.

The a.e. nonnegativity of `W` on the product is obtained from `hWnn` through the
quasi-measure-preserving projections `Prod.fst`, `Prod.snd`
(`MeasureTheory.Measure.quasiMeasurePreserving_fst`, `..._snd`), and the measurability of
`latDistL` from the fact that it is `1`-Lipschitz (`Metric.infDist_le_infDist_add_dist`).
-/

noncomputable section

open scoped Real
open MeasureTheory Filter

namespace Work.BoseFixR.FarLat

/-- The additive shear `(x, z) ↦ (x + z, z)` as a measurable equivalence of `ℝ³ × ℝ³`; its
inverse is `(u, v) ↦ (u - v, v)`.  It preserves the Lebesgue product measure (this is
`MeasureTheory.measurePreserving_add_prod`). -/
noncomputable def shearFstCoulPair :
    (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ≃ᵐ
      (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) where
  toEquiv :=
    { toFun := fun p => (p.1 + p.2, p.2)
      invFun := fun p => (p.1 - p.2, p.2)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  measurable_toFun := by measurability
  measurable_invFun := by measurability

-- imports used below: Submission.Work.BoseFixR.FarLatDefs
theorem coulPair_latDistL_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : MeasureTheory.Integrable W) (hWnn : 0 ≤ᵐ[MeasureTheory.volume] W)
    (hfin : (∫⁻ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        ENNReal.ofReal (W q.1 * W q.2 * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹)) < ⊤) :
    (∫ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        W q.1 * W q.2 * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹)
      = ∫ z : EuclideanSpace ℝ (Fin 3),
          (∫ x : EuclideanSpace ℝ (Fin 3), W x * W (x + z))
            * (Work.BoseFixR.latDistL ℓ z)⁻¹ := by
  have _hℓ := hℓ
  -- `latDistL` is `1`-Lipschitz, hence continuous and measurable
  have hlat_lip : LipschitzWith 1 (Work.BoseFixR.latDistL ℓ) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, NNReal.coe_one, one_mul]
      simp only [Work.BoseFixR.latDistL]
      refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
      · have h := Metric.infDist_le_infDist_add_dist (x := x) (y := y)
          (s := Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n))
        linarith
      · have h := Metric.infDist_le_infDist_add_dist (x := y) (y := x)
          (s := Set.range (fun n : Fin 3 → ℤ => Work.BoseFixR.lat ℓ n))
        rw [dist_comm]
        linarith
  have hlat_meas : Measurable (Work.BoseFixR.latDistL ℓ) := hlat_lip.continuous.measurable
  -- `W ≥ 0` a.e. on each factor of the product
  have h1 : 0 ≤ᵐ[volume.prod volume]
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => W q.1) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).tendsto_ae
      |>.eventually hWnn
  have h2 : 0 ≤ᵐ[volume.prod volume]
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => W q.2) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).tendsto_ae
      |>.eventually hWnn
  -- the integrand is nonnegative a.e.
  have hFnn : 0 ≤ᵐ[volume.prod volume]
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        W q.1 * W q.2 * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹) := by
    filter_upwards [h1, h2] with q hq1 hq2
    exact mul_nonneg (mul_nonneg hq1 hq2) (inv_nonneg.mpr (Work.BoseFixR.latDistL_nonneg ℓ _))
  -- the integrand is a.e. strongly measurable
  have hFaesm : AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        W q.1 * W q.2 * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹)
      (volume.prod volume) := by
    have hA : AEMeasurable
        (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => W q.1)
        (volume.prod volume) := hW.aemeasurable.comp_fst
    have hB : AEMeasurable
        (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => W q.2)
        (volume.prod volume) := hW.aemeasurable.comp_snd
    have hC : AEMeasurable
        (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹)
        (volume.prod volume) :=
      (hlat_meas.comp (measurable_fst.sub measurable_snd)).aemeasurable.inv
    exact ((hA.mul hB).mul hC).aestronglyMeasurable
  -- hence the integrand is integrable
  have hIntF : Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        W q.1 * W q.2 * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹)
      (volume.prod volume) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hFaesm hFnn).mp (ne_top_of_lt hfin)
  -- the shear `(x, z) ↦ (x + z, z)` preserves the product measure
  have hMP : MeasurePreserving (⇑shearFstCoulPair) (volume.prod volume) (volume.prod volume) :=
    measurePreserving_add_prod volume volume
  -- integrability of the sheared integrand
  have hIntK : Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        W (p.1 + p.2) * W p.2 * (Work.BoseFixR.latDistL ℓ p.1)⁻¹)
      (volume.prod volume) := by
    have h := (hMP.integrable_comp hFaesm).mpr hIntF
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply]
    simp [show shearFstCoulPair p = (p.1 + p.2, p.2) from rfl]
  have hshear := hMP.integral_comp'
    (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      W q.1 * W q.2 * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹)
  -- step 1: the substitution `q = (x + z, z)`
  have hstep1 : (∫ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        W q.1 * W q.2 * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹)
      = ∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          W (p.1 + p.2) * W p.2 * (Work.BoseFixR.latDistL ℓ p.1)⁻¹ := by
    have h1' : (∫ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          W q.1 * W q.2 * (Work.BoseFixR.latDistL ℓ (q.1 - q.2))⁻¹)
        = ∫ x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
            W (shearFstCoulPair x).1 * W (shearFstCoulPair x).2
              * (Work.BoseFixR.latDistL ℓ
                  ((shearFstCoulPair x).1 - (shearFstCoulPair x).2))⁻¹ := hshear.symm
    rw [h1']
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp [show shearFstCoulPair p = (p.1 + p.2, p.2) from rfl]
  -- step 2: Fubini
  have hstep2 : (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        W (p.1 + p.2) * W p.2 * (Work.BoseFixR.latDistL ℓ p.1)⁻¹)
      = ∫ x : EuclideanSpace ℝ (Fin 3), ∫ z : EuclideanSpace ℝ (Fin 3),
          W (x + z) * W z * (Work.BoseFixR.latDistL ℓ x)⁻¹ :=
    MeasureTheory.integral_prod _ hIntK
  -- step 3: pull the `x`-dependent weight out of the inner integral
  have hstep3 : (∫ x : EuclideanSpace ℝ (Fin 3), ∫ z : EuclideanSpace ℝ (Fin 3),
        W (x + z) * W z * (Work.BoseFixR.latDistL ℓ x)⁻¹)
      = ∫ x : EuclideanSpace ℝ (Fin 3),
          (∫ z : EuclideanSpace ℝ (Fin 3), W (x + z) * W z)
            * (Work.BoseFixR.latDistL ℓ x)⁻¹ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    exact MeasureTheory.integral_mul_const ((Work.BoseFixR.latDistL ℓ x)⁻¹)
      (fun z => W (x + z) * W z)
  -- step 4: commute the product and rename the integration variables
  have hstep4 : (∫ x : EuclideanSpace ℝ (Fin 3),
        (∫ z : EuclideanSpace ℝ (Fin 3), W (x + z) * W z)
          * (Work.BoseFixR.latDistL ℓ x)⁻¹)
      = ∫ z : EuclideanSpace ℝ (Fin 3),
          (∫ x : EuclideanSpace ℝ (Fin 3), W x * W (x + z))
            * (Work.BoseFixR.latDistL ℓ z)⁻¹ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have hinner : (∫ t : EuclideanSpace ℝ (Fin 3), W (z + t) * W t)
        = ∫ x : EuclideanSpace ℝ (Fin 3), W x * W (x + z) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun t => by
        simp only []
        rw [add_comm z t, mul_comm]))
    simp only [] at hinner ⊢
    rw [hinner]
  exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))

end Work.BoseFixR.FarLat
