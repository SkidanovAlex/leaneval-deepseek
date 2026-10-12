import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.acubePVFacts
import Submission.Work.BoseBoxFock.cIPn_sum_aPC_re
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- **The insertion map pulls null sets back to null sets of the product measure.**

For a measurable set `D` of `N`-particle configurations of vanishing Lebesgue measure, the set
of pairs `(x, y)` with `x[i ↦ y] ∈ D` is null for the product of the two Lebesgue measures.

This is the general-`N` form of `Work.BoseBoxFock.prod_update_preimage_null` (which is stated for
`Fin (n+1)`, the shape in which it is used by the box-relative arguments); the two types agree
definitionally, so the `n+1` statement is the whole content. -/
theorem prod_update_preimage_null' {N : ℕ} (i : Fin N)
    {D : Set (Fin N → EuclideanSpace ℝ (Fin 3))} (hDm : MeasurableSet D)
    (hD0 : (volume : Measure (Fin N → EuclideanSpace ℝ (Fin 3))) D = 0) :
    ((volume : Measure (Fin N → EuclideanSpace ℝ (Fin 3))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      {p : (Fin N → EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) |
        Function.update p.1 i p.2 ∈ D} = 0 := by
  cases N with
  | zero => exact i.elim0
  | succ n => exact prod_update_preimage_null (n := n) i hDm hD0

/-- **Null modifications of the state do not change the slot mean.**

If `f = g` almost everywhere (for the *global* Lebesgue measure on configuration space), then
their slot means `aPC ℓ i f` and `aPC ℓ i g` agree almost everywhere.

The proof mirrors `Work.BoseBoxFock.ae_aPC_congr`, the box-relative companion: replacing the bad
set by a measurable null superset `M`, the insertion map `(x,y) ↦ x[i ↦ y]` pulls `M` back to a
null set of the product measure (`prod_update_preimage_null'`); Tonelli
(`Measure.ae_prod_iff_ae_ae`) then says that for almost every `x` the fibre
`y ↦ x[i ↦ y]` meets `M` only on a null set of `y`s, so the two fibres agree a.e. in `y` and
their Bochner integrals coincide (`integral_congr_ae`, which needs no integrability hypothesis,
the integral of a non-integrable function being the junk value `0`). -/
theorem aPC_congr_ae {N : ℕ} {ℓ : ℝ} (i : Fin N)
    {f g : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (h : f =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
      (Fin N → EuclideanSpace ℝ (Fin 3)))] g) :
    Work.BoseBoxFock.aPC ℓ i f =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
      (Fin N → EuclideanSpace ℝ (Fin 3)))] Work.BoseBoxFock.aPC ℓ i g := by
  have hD : (volume : Measure (Fin N → EuclideanSpace ℝ (Fin 3))) {x | ¬ (f x = g x)} = 0 :=
    MeasureTheory.ae_iff.mp h
  obtain ⟨M, hsub, hMm, hM0⟩ := exists_measurable_superset_of_null hD
  have hprod : ((volume : Measure (Fin N → EuclideanSpace ℝ (Fin 3))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      {p : (Fin N → EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) |
        Function.update p.1 i p.2 ∈ M} = 0 :=
    prod_update_preimage_null' i hMm hM0
  have hae : ∀ᵐ p ∂((volume : Measure (Fin N → EuclideanSpace ℝ (Fin 3))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))),
      ¬ (Function.update p.1 i p.2 ∈ M) := by
    rw [MeasureTheory.ae_iff]
    simpa using hprod
  have hmeas : MeasurableSet {p : (Fin N → EuclideanSpace ℝ (Fin 3)) ×
        EuclideanSpace ℝ (Fin 3) | ¬ (Function.update p.1 i p.2 ∈ M)} :=
    (hMm.preimage (by fun_prop)).compl
  have hle : ((volume : Measure (Fin N → EuclideanSpace ℝ (Fin 3))).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)))
      ≤ ((volume : Measure (Fin N → EuclideanSpace ℝ (Fin 3))).prod
        (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hae2 : ∀ᵐ p ∂((volume : Measure (Fin N → EuclideanSpace ℝ (Fin 3))).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ))),
      ¬ (Function.update p.1 i p.2 ∈ M) := ae_mono hle hae
  have hiter : ∀ᵐ x ∂(volume : Measure (Fin N → EuclideanSpace ℝ (Fin 3))),
      ∀ᵐ y ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)),
      ¬ (Function.update x i y ∈ M) :=
    (Measure.ae_prod_iff_ae_ae hmeas).mp hae2
  filter_upwards [hiter] with x hx
  unfold Work.BoseBoxFock.aPC
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hx] with y hy
  by_contra hcon
  exact hy (hsub hcon)

end Work.BoseBoxFock
