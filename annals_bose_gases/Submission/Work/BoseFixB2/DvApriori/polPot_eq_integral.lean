import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.BandDefs
import Submission.Work.BoseFixB2.Polar.potBil_polar
import Submission.Work.BoseFixB2.Pot.potWordU_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.polPot_eq_integral` — the polarisation of the potential band

`polPot v h μ n Φ Ψ` is the polarisation `(potPart (Φ+Ψ) − potPart (Φ−Ψ))/4` of the
multiplicative part `potPart Ξ = ∫_{abox n ℓ} (Ξ x)² · W x` of the box word, where
`W = potWordU n v (g₀ v h) ℓ μ 0` and `ℓ = fsSide v μ`.  The statement identifies it with the
associated bilinear form `∫_{abox n ℓ} Φ x · Ψ x · W x`.

The mathematics is the pointwise identity `(a+b)² − (a−b)² = 4ab` under the integral sign
together with additivity of the Bochner integral, i.e. exactly
`Work.BoseFixB2.Polar.potBil_polar`.  The analytic input that lemma needs is integrability of
`W` on `abox n ℓ` — supplied here by `Work.BoseFixB2.Pot.potWordU_integrable`, which holds for
*every* box side (it does not require the dilution condition `R ≤ ℓ·chiR0`).

The dilution hypothesis `hRℓ : R ≤ fsSide v μ · chiR0` of the statement is used only to make
the box side `ℓ = fsSide v μ` **positive** (`chiR0 > 0`), which is the form in which
`potBil_polar` consumes it.
-/

namespace Work.BoseFixB2.DvApriori

theorem polPot_eq_integral {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n : ℕ} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hv1 : MeasureTheory.MemLp v 1)
    (hRℓ : R ≤ Work.BoseFixB2.fsSide v μ * Submission.BoseGases.chiR0)
    {Φ Ψ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    polPot v h μ n Φ Ψ
      = ∫ x in Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ),
          Φ x * Ψ x * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h)
            (Work.BoseFixB2.fsSide v μ) μ 0 x := by
  -- ## the box side is positive: `0 < R ≤ fsSide v μ · chiR0` and `chiR0 > 0`
  have hℓ : 0 < Work.BoseFixB2.fsSide v μ := by
    have hχ : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
    have hpos : 0 < Work.BoseFixB2.fsSide v μ * Submission.BoseGases.chiR0 :=
      lt_of_lt_of_le hR hRℓ
    exact pos_of_mul_pos_left hpos hχ.le
  -- ## integrability of the potential profile on the box
  have hw : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h)
          (Work.BoseFixB2.fsSide v μ) μ 0 x)
      (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ)) :=
    Work.BoseFixB2.Pot.potWordU_integrable (v := v) (h := h) (R := R) hR hv_supp hv1
      (μ := μ) (n := n) (Work.BoseFixB2.fsSide v μ)
  -- ## the polarisation identity for the multiplicative part
  exact Work.BoseFixB2.Polar.potBil_polar (n := n) (v := v)
    (g := Submission.BoseGases.g0 v h) (ℓ := Work.BoseFixB2.fsSide v μ) (μ := μ)
    hℓ hΦ hΨ hw

end Work.BoseFixB2.DvApriori
