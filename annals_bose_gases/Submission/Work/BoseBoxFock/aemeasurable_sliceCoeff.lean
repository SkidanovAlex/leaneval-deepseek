import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.slotSum_sectorPointwise
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-!
# `Work.BoseBoxFock.aemeasurable_sliceCoeff` — measurability of the slice coefficient

The monomial coefficient of the slice of a sector,

    `y ↦ ∫ u, conj (M_α u) · sliceF e S Φ y u`,

is a.e. measurable on the complement configuration space.  No analytic input is needed: the
integrand is *jointly* strongly measurable in `(u, y)`, because

* `M_α = modeProd e S.card α` is continuous (`e` is continuous),
* `(u, y) ↦ sliceF e S Φ y u = slotExact e S Φ (pairCoord S (u ∘ S.equivFin) y)` is the
  composition of the *measurable* `(u, y) ↦ pairCoord S (u ∘ S.equivFin) y` (each coordinate is a
  projection) with the *measurable* `slotExact e S Φ` of
  `Work.BoseBoxFock.slotExact_measurable_bounded_compactSupport` (`Φ` continuous, compactly
  supported),

and `StronglyMeasurable.integral_prod_left'` (which needs no integrability hypothesis: the
Bochner integral is defined for every function) makes the `u`-integral strongly measurable in `y`.
-/

theorem aemeasurable_sliceCoeff {m n : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hcont : ∀ l, Continuous (e l)) (hcomp : ∀ l, HasCompactSupport (e l))
    (α : Fin m →₀ ℕ) (S : Finset (Fin n))
    {Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    AEMeasurable
      (fun y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3) =>
        ∫ u : Fin S.card → EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
            * Work.BoseBoxFock.sliceF e S Φ y u)
      (MeasureTheory.volume :
        MeasureTheory.Measure ({i // i ∉ S} → EuclideanSpace ℝ (Fin 3))) := by
  classical
  -- the mode product is continuous, hence jointly strongly measurable in the `u`-variable
  have hcont_mode : Continuous (fun u : Fin S.card → EuclideanSpace ℝ (Fin 3) =>
      Work.BoseDict.modeProd e S.card α u) := by
    simp only [Work.BoseDict.modeProd]
    refine continuous_finsetSum _ (fun σ _ => ?_)
    refine Continuous.mul continuous_const ?_
    exact continuous_finsetProd _ (fun i _ => (hcont (σ i)).comp (continuous_apply i))
  -- the reassembling map `(u, y) ↦ pairCoord S (u ∘ S.equivFin) y` is measurable
  have hpair : Measurable (fun p : (Fin S.card → EuclideanSpace ℝ (Fin 3)) ×
      ({i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) =>
      pairCoord S (fun i : {i // i ∈ S} => p.1 (S.equivFin i)) p.2) := by
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j ∈ S
    · simp only [pairCoord, dif_pos hj]
      exact (measurable_pi_apply (S.equivFin ⟨j, hj⟩)).comp measurable_fst
    · simp only [pairCoord, dif_neg hj]
      exact (measurable_pi_apply (⟨j, hj⟩ : {i // i ∉ S})).comp measurable_snd
  -- the slice of the sector, as a function of `(u, y)`, is strongly measurable
  have hslice : StronglyMeasurable (fun p : (Fin S.card → EuclideanSpace ℝ (Fin 3)) ×
      ({i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) => sliceF e S Φ p.2 p.1) := by
    have hsm := (slotExact_measurable_bounded_compactSupport e hcont hcomp S Φ hΦ hΦc).1
    have h2 : Measurable (fun p : (Fin S.card → EuclideanSpace ℝ (Fin 3)) ×
        ({i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) =>
        slotExact e S Φ (pairCoord S (fun i => p.1 (S.equivFin i)) p.2)) := hsm.comp hpair
    simpa only [sliceF, sectorSlice] using h2.stronglyMeasurable
  -- hence the integrand is jointly strongly measurable
  have hG : StronglyMeasurable (fun p : (Fin S.card → EuclideanSpace ℝ (Fin 3)) ×
      ({i // i ∉ S} → EuclideanSpace ℝ (Fin 3)) =>
      (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α p.1)
        * sliceF e S Φ p.2 p.1) :=
    ((Complex.continuous_conj.comp (hcont_mode.comp continuous_fst)).stronglyMeasurable).mul hslice
  -- and its `u`-integral is strongly measurable in `y`
  have hint : StronglyMeasurable (fun y : {i // i ∉ S} → EuclideanSpace ℝ (Fin 3) =>
      ∫ u : Fin S.card → EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseDict.modeProd e S.card α u)
          * sliceF e S Φ y u) :=
    MeasureTheory.StronglyMeasurable.integral_prod_left'
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Fin S.card → EuclideanSpace ℝ (Fin 3))))
      hG
  exact hint.aemeasurable

end Work.BoseBoxFock
