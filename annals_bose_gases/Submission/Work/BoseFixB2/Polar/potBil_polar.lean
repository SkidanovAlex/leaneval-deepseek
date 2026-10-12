import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Polar.potBil_polar`

The polarisation identity for the **potential part** of the box word
`Work.BoseFixB2.potBil` (see `Submission/Work/BoseFixB2/Defs.lean`):

`((∫_{abox} (Φ+Ψ)²·W) − (∫_{abox} (Φ−Ψ)²·W)) / 4 = ∫_{abox} Φ·Ψ·W`,

where `W = potWordU n v g ℓ μ 0` is FS's multiplicative potential profile
(`Work.BoseKinLoc.potWordU`, independent of the state) and `abox n ℓ` is the centred
`n`-particle box.

The mathematics is the pointwise algebraic identity

`(Φ x + Ψ x)²·W x − (Φ x − Ψ x)²·W x = 4·(Φ x · Ψ x · W x)`

combined with additivity/homogeneity of the Bochner integral over the box: this is
exactly the statement that the potential part is the *diagonal of a symmetric bilinear form*
— the missing half, together with `boxFormB_parallelogram` and `boxFormB_smul`
(2-homogeneity), of `lem:LocMatrices`' claim that `polB` is symmetric bilinear.

The only analytic input is integrability of the three integrands on `abox n ℓ`:

* `W` is integrable by hypothesis (`hw`);
* the weights `(Φ±Ψ)²` and `Φ·Ψ` are continuous (the states are `ContDiff`) on the compact
  box `abox n ℓ` (`BoseGases.abox_compact`), so
  `IntegrableOn.continuousOn_mul` produces each product from `hw`.

No integrability of `Φ•Ψ•W` is assumed: it is *derived*, which is what makes the integral
manipulations (`integral_sub`, `integral_const_mul`) legitimate rather than formal.
-/

open MeasureTheory

namespace Work.BoseFixB2.Polar

theorem potBil_polar {n : ℕ} {v g : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) {Φ Ψ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v g ℓ μ 0 x) (Submission.BoseGases.abox n ℓ)) : ((∫ x in Submission.BoseGases.abox n ℓ, (Φ x + Ψ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x) - (∫ x in Submission.BoseGases.abox n ℓ, (Φ x - Ψ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)) / 4 = ∫ x in Submission.BoseGases.abox n ℓ, Φ x * Ψ x * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x := by
  have hK : IsCompact (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_compact n hℓ
  have hms : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => Φ x + Ψ x) :=
    hΦ.add hΨ
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => Φ x - Ψ x) :=
    hΦ.sub hΨ
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun x : Submission.BoseGases.X n => Φ x * Ψ x) :=
    hΦ.mul hΨ
  -- Integrability of the three integrands on the box.
  have hA : IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Φ x + Ψ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      (Submission.BoseGases.abox n ℓ) :=
    MeasureTheory.IntegrableOn.continuousOn_mul
      (g := fun x : Submission.BoseGases.X n => (Φ x + Ψ x) ^ 2)
      (g' := fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      (hsum.continuous.continuousOn.pow 2) hw hK
  have hB : IntegrableOn (fun x : Submission.BoseGases.X n =>
      (Φ x - Ψ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      (Submission.BoseGases.abox n ℓ) :=
    MeasureTheory.IntegrableOn.continuousOn_mul
      (g := fun x : Submission.BoseGases.X n => (Φ x - Ψ x) ^ 2)
      (g' := fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      (hsub.continuous.continuousOn.pow 2) hw hK
  -- The pointwise `(f+g)² − (f−g)² = 4fg` under the integral sign.
  have hcongr : (∫ x in Submission.BoseGases.abox n ℓ,
        ((Φ x + Ψ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x
          - (Φ x - Ψ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (4 * (Φ x * Ψ x * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)) := by
    apply MeasureTheory.setIntegral_congr_fun hms
    intro x _
    ring
  -- Subtract the two integrals and pull out the factor `4`.
  have hkey : (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x + Ψ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      - (∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x - Ψ x) ^ 2 * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x)
      = 4 * (∫ x in Submission.BoseGases.abox n ℓ,
        Φ x * Ψ x * Work.BoseKinLoc.potWordU n v g ℓ μ 0 x) := by
    rw [← MeasureTheory.integral_sub hA hB]
    rw [hcongr, MeasureTheory.integral_const_mul]
  rw [hkey]
  ring

end Work.BoseFixB2.Polar
