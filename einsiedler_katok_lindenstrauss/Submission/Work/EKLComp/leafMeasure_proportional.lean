import Mathlib
import Submission.Work.EKLComp.MaxLeafDefs

/-!
# Proportionality of leafwise measures along a leaf

The system of leafwise measures `ν` of the contract (`Work.EKLContract.IsLeafwise`) comes
with an equivariance property: for `x ∈ X'` and `u ∈ U`,
`ν x = c • (ν (u • x)).map (· * u)` for some `0 < c < ⊤`.  Pushing this identity to the leaf
via `g ↦ g • x` (which converts `(g * u) • x` into `g • (u • x) = g • y`) shows that on a
single `U_ij`-leaf the pushed measures are proportional.  This is the statement proved here:
for `y ∈ leaf i j hij x`, `leafMeasure ν y = c • leafMeasure ν x` for some `0 < c < ⊤`.

This is exactly the geometric input used in the maximal inequality for leafwise measures
(`Work.EKLComp.PlaqueAlgebraExists` consumption): two points of the same leaf carry
proportional leafwise measures.
-/

namespace Work.EKLComp

open MeasureTheory
open scoped ENNReal

theorem leafMeasure_proportional (i j : Fin 3) (hij : i ≠ j)
    (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (X' : Set Work.EKLContract.X3)
    (hν : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) ν X')
    {x y : Work.EKLContract.X3} (hx : x ∈ X') (hy : y ∈ X')
    (hxy : y ∈ Work.EKLComp.leaf i j hij x) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ Work.EKLComp.leafMeasure ν y = c • Work.EKLComp.leafMeasure ν x := by
  -- `y` lies in the `U_ij`-leaf of `x`, so `y = u • x` for some `u ∈ U_ij`.
  obtain ⟨u, hu, hux⟩ := hxy
  have hux' : u • x = y := hux
  have huy : u • x ∈ X' := by rw [hux']; exact hy
  -- Equivariance of the leafwise measures at the point `x`, in the direction `x → u • x = y`.
  obtain ⟨c, hc0, hct, hceq⟩ := hν.equivariant x hx u hu huy
  refine ⟨c⁻¹, ENNReal.inv_ne_zero.mpr hct, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  -- Push the identity to the leaf: `leafMeasure ν x = c • leafMeasure ν y`.
  have hmap : leafMeasure ν x = c • leafMeasure ν y := by
    simp only [leafMeasure]
    rw [hceq, Measure.map_smul, hux'] <;> try fun_prop
    rw [Measure.map_map]
    · have hcomp : ((fun g : Work.EKLContract.SL3 => g • x) ∘
            (fun g : Work.EKLContract.SL3 => g * u)) =
          (fun g : Work.EKLContract.SL3 => g • y) := by
        funext g
        simp only [Function.comp_apply]
        rw [mul_smul, hux']
      rw [hcomp]
    · exact (continuous_smul.comp (continuous_id.prodMk continuous_const)).measurable
    · exact (continuous_mul_const u).measurable
  -- Invert the proportionality.
  have : c⁻¹ • leafMeasure ν x = leafMeasure ν y := by
    rw [hmap, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
  exact this.symm

end Work.EKLComp
