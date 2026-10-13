/-
Copyright: work module for the Elgindi finite-time singularity project.

# a.e. strong measurability of a pointwise limit taken on the open quadrant

The elliptic estimates of §'Elliptic Regularity Estimates' of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021)

are proved for data `u` which is a pointwise limit of smooth (`C^∞` on the *open* quadrant
`Q0 = (0,∞) × (0,π/2)`) functions `un`, the convergence being available only on `Q0`.  The
measure that all the statements of the chapter use is `ν = dz dθ = (dz|_{Iz}) × (dθ|_{Iθ})`
on the *closed* rectangle `Iz × Iθ`, and it is supported (modulo a null set) on the open
quadrant `Q0`.  This module records the elementary but indispensable consequence: the
limit is a.e. strongly measurable for `ν`, even though nothing at all is known about `u`
on the boundary `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}`.

## Route

* `ν` is the restriction of the planar Lebesgue measure `volume.prod volume` to
  `Iz × Iθ = [0,∞) × [0,π/2]` (`Measure.prod_restrict`), whose complement in `Iz × Iθ`
  is contained in `{0} × univ ∪ univ × {0} ∪ univ × {π/2}`, a null set
  (`Measure.prod_prod` + `Real.volume_singleton`).  Hence `Q0` is conull for `ν`
  (`MeasureTheory.ae_iff`).
* The function `G p = if p ∈ Q0 then u p.1 p.2 else 0` is Borel measurable: on the open
  set `Q0` it is the pointwise limit of the (continuous, hence measurable) functions
  `Q0.domRestrict (Function.uncurry (un n))` — here `measurable_of_tendsto_metrizable`
  applies on the subtype `↥Q0` — and off `Q0` it vanishes
  (`measurable_of_restrict_of_restrict_compl`).
* `G` agrees with `Function.uncurry u` `ν`-a.e., and `AEMeasurable.congr` finishes.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

open MeasureTheory Set Filter

open scoped Topology

/-- **A pointwise limit on the open quadrant is a.e. strongly measurable** for the measure
`(dz|_{Iz}) × (dθ|_{Iθ})` of the elliptic estimates: continuity of the approximants is only
assumed on the open quadrant `(0,∞) × (0,π/2)` and the convergence only there, but the
boundary of the quadrant is null for the measure, so the (otherwise completely arbitrary)
boundary values of the limit are irrelevant. -/
theorem aemeasurable_uncurry_of_tendsto_Q0 {un : ℕ → ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hcont : ∀ n : ℕ, ContinuousOn (Function.uncurry (un n)) Work.FTS.EllipticEst.Q0)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n => un n z θ) Filter.atTop (nhds (u z θ))) :
    AEMeasurable (Function.uncurry u)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  classical
  set ν := (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hν
  have hQmeas : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  -- The limit, restricted to the open quadrant, is the pointwise limit of the continuous
  -- functions `un`, hence Borel measurable there.
  have hlim : Measurable (Work.FTS.EllipticEst.Q0.domRestrict (Function.uncurry u)) := by
    refine measurable_of_tendsto_metrizable
      (f := fun n => Work.FTS.EllipticEst.Q0.domRestrict (Function.uncurry (un n)))
      (fun n => ?_) ?_
    · exact (hcont n).domRestrict.measurable
    · exact tendsto_pi_nhds.mpr (fun p => hconv p.1.1 p.1.2 p.2)
  -- Extend by zero off the quadrant.
  have hG : Measurable (fun p : ℝ × ℝ =>
      if p ∈ Work.FTS.EllipticEst.Q0 then u p.1 p.2 else 0) := by
    refine measurable_of_restrict_of_restrict_compl hQmeas ?_ ?_
    · have heq : (Work.FTS.EllipticEst.Q0.domRestrict
          (fun p : ℝ × ℝ => if p ∈ Work.FTS.EllipticEst.Q0 then u p.1 p.2 else 0))
          = Work.FTS.EllipticEst.Q0.domRestrict (Function.uncurry u) := by
        funext p
        simp only [Set.domRestrict, Function.uncurry]
        exact ite_eq_left p.2
      rw [heq]; exact hlim
    · have heq : (((Work.FTS.EllipticEst.Q0)ᶜ).domRestrict
          (fun p : ℝ × ℝ => if p ∈ Work.FTS.EllipticEst.Q0 then u p.1 p.2 else 0))
          = fun _ => (0 : ℝ) := by
        funext p
        simp only [Set.domRestrict]
        exact ite_eq_right p.2
      rw [heq]; exact measurable_const
  -- `ν` is the planar Lebesgue measure restricted to `Iz × Iθ`.
  have hνeq : ν = (MeasureTheory.volume.prod MeasureTheory.volume).restrict
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [hν]
    exact Measure.prod_restrict _ _
  -- The complement of the open quadrant inside `Iz × Iθ` is null.
  have hνcompl : ν (Work.FTS.EllipticEst.Q0)ᶜ = 0 := by
    rw [hνeq, Measure.restrict_apply'
      (show MeasurableSet (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) from
        measurableSet_Ici.prod measurableSet_Icc)]
    refine measure_mono_null (t := (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
      ∪ ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ))
      ∪ ((Set.univ : Set ℝ) ×ˢ ({(Real.pi / 2)} : Set ℝ))) ?_ ?_
    · rintro p ⟨hpQ, hpz, hpθ⟩
      have hz : 0 ≤ p.1 := hpz
      have hθ0 : 0 ≤ p.2 := hpθ.1
      have hθ1 : p.2 ≤ Real.pi / 2 := hpθ.2
      have hnQ : ¬ (0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2) := by
        intro h
        exact hpQ ((Work.FTS.EllipticEst.mem_Q0).mpr h)
      rcases eq_or_lt_of_le hz with hz0 | hzpos
      · exact Or.inl (Or.inl ⟨hz0.symm, trivial⟩)
      · by_cases h2 : p.2 = 0
        · exact Or.inl (Or.inr ⟨trivial, h2⟩)
        · have hθpos : 0 < p.2 := lt_of_le_of_ne hθ0 (Ne.symm h2)
          have hθ2 : p.2 = Real.pi / 2 := by
            rcases eq_or_lt_of_le hθ1 with h | h
            · exact h
            · exact absurd ⟨hzpos, hθpos, h⟩ hnQ
          exact Or.inr ⟨trivial, hθ2⟩
    · have h1 : (MeasureTheory.volume.prod MeasureTheory.volume)
          (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
        rw [Measure.prod_prod, Real.volume_singleton, zero_mul]
      have h2 : (MeasureTheory.volume.prod MeasureTheory.volume)
          ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) = 0 := by
        rw [Measure.prod_prod, Real.volume_singleton, mul_zero]
      have h3 : (MeasureTheory.volume.prod MeasureTheory.volume)
          ((Set.univ : Set ℝ) ×ˢ ({(Real.pi / 2)} : Set ℝ)) = 0 := by
        rw [Measure.prod_prod, Real.volume_singleton, mul_zero]
      refine le_antisymm ?_ (by simp)
      calc (MeasureTheory.volume.prod MeasureTheory.volume)
            ((({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ))
              ∪ ((Set.univ : Set ℝ) ×ˢ ({(Real.pi / 2)} : Set ℝ)))
          ≤ (MeasureTheory.volume.prod MeasureTheory.volume)
              ((({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
                ∪ ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)))
            + (MeasureTheory.volume.prod MeasureTheory.volume)
              ((Set.univ : Set ℝ) ×ˢ ({(Real.pi / 2)} : Set ℝ)) := measure_union_le _ _
        _ ≤ ((MeasureTheory.volume.prod MeasureTheory.volume)
              (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ))
            + (MeasureTheory.volume.prod MeasureTheory.volume)
              ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)))
            + (MeasureTheory.volume.prod MeasureTheory.volume)
              ((Set.univ : Set ℝ) ×ˢ ({(Real.pi / 2)} : Set ℝ)) :=
              add_le_add (measure_union_le _ _) le_rfl
        _ = 0 := by rw [h1, h2, h3]; simp
  have hQae : ∀ᵐ p ∂ν, p ∈ Work.FTS.EllipticEst.Q0 := by
    rw [MeasureTheory.ae_iff, show {p : ℝ × ℝ | ¬ p ∈ Work.FTS.EllipticEst.Q0}
      = (Work.FTS.EllipticEst.Q0)ᶜ from rfl]
    exact hνcompl
  refine AEMeasurable.congr hG.aemeasurable ?_
  filter_upwards [hQae] with p hp
  show (if p ∈ Work.FTS.EllipticEst.Q0 then u p.1 p.2 else 0) = u p.1 p.2
  exact ite_eq_left hp

end Work.FTS_EllLimOK
