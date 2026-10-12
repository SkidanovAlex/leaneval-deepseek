import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.amgmSlotSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.fSqMul_le`

The slot bound: for a continuous `g` on the `N`-particle box, an
`L¹`-measurable cube-bounded `f` with `|f| ≤ B`,

`∫_{abox N ℓ} g² · f(xᵢ) ≤ B · ∫_{abox N ℓ} g²`.

Both integrands are integrable on the box by the corpus lemma
`Submission.BoseGases.integrableOn_slot_fibre` (continuity of the slot `g²`,
`L¹`-measurability of `f` on the cube, and the cube bound), so this is the
pointwise inequality `g²·f(xᵢ) ≤ g²·B` integrated a.e.
-/

namespace Work.BoseFixB1

theorem fSqMul_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : Submission.BoseGases.X N → ℝ} (hgc : Continuous g)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hfm : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    (hfb : ∀ z, |f z| ≤ B) (i : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ, (g x) ^ 2 * f (x i))
      ≤ B * (∫ x in Submission.BoseGases.abox N ℓ, (g x) ^ 2) := by
  -- the global bound is in particular a cube bound
  have hfB : ∀ z ∈ Submission.BoseGases.acube ℓ, |f z| ≤ B := fun z _ => hfb z
  -- integrability of the slot integrand
  have hIf : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => (g x) ^ 2 * f (x i))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    Submission.BoseGases.integrableOn_slot_fibre hℓ i hfm hfB (hgc.pow 2)
  -- integrability of the majorant (the slot lemma applied to the constant fibre `B`)
  have hIB : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N => (g x) ^ 2 * B)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    Submission.BoseGases.integrableOn_slot_fibre (N := N) (ℓ := ℓ) hℓ i
      (F := fun _ : EuclideanSpace ℝ (Fin 3) => B) (C := B)
      MeasureTheory.aestronglyMeasurable_const (fun _ _ => by rw [abs_of_nonneg hB0])
      (hgc.pow 2)
  -- the pointwise (hence a.e.) comparison
  have hae : (fun x : Submission.BoseGases.X N => (g x) ^ 2 * f (x i))
      ≤ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
      (fun x : Submission.BoseGases.X N => (g x) ^ 2 * B) :=
    Filter.Eventually.of_forall fun x => by
      have h1 : f (x i) ≤ B := (abs_le.mp (hfb (x i))).2
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg (g x))
  have key := MeasureTheory.integral_mono_ae hIf hIB hae
  rw [MeasureTheory.integral_mul_const] at key
  calc (∫ x in Submission.BoseGases.abox N ℓ, (g x) ^ 2 * f (x i))
      ≤ (∫ x in Submission.BoseGases.abox N ℓ, (g x) ^ 2) * B := key
    _ = B * (∫ x in Submission.BoseGases.abox N ℓ, (g x) ^ 2) := by rw [mul_comm]

end Work.BoseFixB1
