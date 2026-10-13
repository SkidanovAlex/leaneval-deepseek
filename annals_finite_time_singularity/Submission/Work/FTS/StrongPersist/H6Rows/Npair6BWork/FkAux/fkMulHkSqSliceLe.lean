import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.radialMatchedMajorant
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.contDiffOn6_FK
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.Spaces.Slots.lintegral_DzIter_le_HkSq_smooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `fkMulHkSqSliceLe` — the level-six integrand of `(FK f) · f`, integrated over `θ`

The radial factor `z ↦ FK f z` multiplies the datum `f`, and the level-six weighted integrand of
the product is dominated at each *point* `(z,θ)` of the open quadrant by the matched radial sum
`∑_{b ≤ 6} (D_z^b (FK f)(z))² · HkIntegrand α (6-b) f z θ` (`radialMatchedMajorant`, proved in
this directory).  Here the pointwise domination is *integrated* over `θ ∈ Iθ`, the finite sum is
interchanged with the `θ`-integral, and the result is turned into an a.e.-in-`z` statement in the
shape in which the consumers (`fkPsi6TermBound`, `fkMulHkSqLe`) use it.

The three ingredients are all available in the tree:

* `radialMatchedMajorant` — the pointwise matched majorant (constant valid for every `α`);
* the two Leibniz rules `leibniz_rad_Dz_cd6`, `leibniz_rad_mixed_cd6`, whose hypotheses are
  `ContDiffOn ℝ 6` of the uncurried radial factor (`contDiffOn6_FK`, from `DatData` and the
  `ℋ⁷`-honesty of the datum) and of the datum (`SmoothOpen.forall`);
* `HkMem_of_le` (`T5bPrep`) to descend the `ℋ⁶`-honesty of the datum to the matched levels
  `6 - b`, giving the `θ`-integrability of every summand.

The passage from "for every `z > 0`" to "for a.e. `z ∈ Iz`" costs the single point `z = 0`, which
is a null set for `volume.restrict Iz`.
-/

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

/-- **The `θ`-integrated matched majorant of `(FK f) · f`.**

There is a universal constant `C > 0` so that for every `α ∈ (0,1]`, every datum
`DatData α f M` and almost every `z ∈ Iz` (in fact for every `z > 0`), the `θ`-integral of the
level-six weighted integrand of the product `(FK f) · f` is bounded by `C` times the matched
radial sum `∑_{b ≤ 6} (D_z^b(FK f)(z))² · ∫_θ HkIntegrand α (6-b) f z θ`. -/
theorem fkMulHkSqSliceLe : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 6
            (fun z θ => Work.Construction.FK f z * f z θ) z θ)
          ≤ C * ∑ b ∈ Finset.range 7,
              (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
                * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
  obtain ⟨C, hCpos, hC⟩ := radialMatchedMajorant
  refine ⟨C, hCpos, ?_⟩
  intro α hα f M hD
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  have hcd6 : ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hsm.forall 6
  have hcdR : ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 := contDiffOn6_FK α hα f M hD
  have hmem6 : Work.Spaces.HkMem α 6 f := hD.h6
  -- the only non-positive `z` in `Iz` is `z = 0`, which is null
  have haepos : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), (0 : ℝ) < z := by
    rw [MeasureTheory.ae_iff]
    have hmeas : MeasurableSet {z : ℝ | ¬ (0 : ℝ) < z} := by
      have h : {z : ℝ | ¬ (0 : ℝ) < z} = Set.Iic (0 : ℝ) := by ext z; simp [not_lt]
      rw [h]; exact measurableSet_Iic
    rw [MeasureTheory.Measure.restrict_apply hmeas]
    have hsub : {z : ℝ | ¬ (0 : ℝ) < z} ∩ Work.Spaces.Iz ⊆ ({0} : Set ℝ) := by
      intro z hz
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hz
      simp only [Set.mem_singleton_iff]
      exact le_antisymm (not_lt.mp hz.1) hz.2
    exact MeasureTheory.measure_mono_null hsub (by simp)
  filter_upwards [haepos] with z hz
  -- the pointwise (in `θ`) matched majorant of `radialMatchedMajorant`, on the open interval
  have hpt : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.HkIntegrand α 6 (fun z θ => Work.Construction.FK f z * f z θ) z θ
        ≤ C * ∑ b ∈ Finset.range 7,
            (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
              * Work.Spaces.HkIntegrand α (6 - b) f z θ := by
    refine Work.Spaces.Slots.ae_restrict_Iθ_of_Ioo ?_
    intro θ hθ0 hθ1
    have h := hC (α := α) (r := fun z => Work.Construction.FK f z) (g := f)
      (fun z θ hz' hθ0' hθ1' j hj =>
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
          hcdR hcd6 hj z θ hz' hθ0' hθ1')
      (fun z θ hz' hθ0' hθ1' j i hi hij =>
        Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
          hcdR hcd6 hi hij z θ hz' hθ0' hθ1')
      hz hθ0 hθ1
    -- the radial iterates `DzdIter` of the one-variable factor are the `D_z`-iterates of the
    -- two-variable function `(z,θ) ↦ FK f z`
    have hsum : (∑ b ∈ Finset.range 7,
          Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z ^ 2
            * Work.Spaces.HkIntegrand α (6 - b) f z θ)
        = ∑ b ∈ Finset.range 7,
            (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
              * Work.Spaces.HkIntegrand α (6 - b) f z θ := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← Work.Elliptic.DzIter_rad (fun z => Work.Construction.FK f z) b z 0]
    rw [hsum] at h
    simpa using h
  -- `θ`-integrability of every summand of the majorant, from `HkMem α (6-b) f`
  have hintb : ∀ b ∈ Finset.range 7, MeasureTheory.Integrable (fun θ : ℝ =>
      (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro b hb
    have hb6 : 6 - b ≤ 6 := by
      have := Finset.mem_range.mp hb; omega
    exact MeasureTheory.Integrable.const_mul
      ((Work.FTS.StrongPersist.H6Pair6Aux.HkMem_of_le (k := 6 - b) (k' := 6) hb6
        hsm hmem6).1 z (show z ∈ Work.Spaces.Iz from le_of_lt hz)) _
  have hint : MeasureTheory.Integrable (fun θ : ℝ => C * ∑ b ∈ Finset.range 7,
      (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
        * Work.Spaces.HkIntegrand α (6 - b) f z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.integrable_finsetSum (Finset.range 7) (fun b hb => hintb b hb)).const_mul C
  -- integrate the pointwise bound in `θ`
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 6 _ z θ) hint hpt
  -- the `θ`-integral of the majorant is the matched sum of `θ`-integrals
  have hval : (∫ θ in Work.Spaces.Iθ, C * ∑ b ∈ Finset.range 7,
        (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
          * Work.Spaces.HkIntegrand α (6 - b) f z θ)
      = C * ∑ b ∈ Finset.range 7,
          (Work.Spaces.DzIter b (fun z _ => Work.Construction.FK f z) z 0) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (6 - b) f z θ) := by
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finsetSum (Finset.range 7) (fun b hb => hintb b hb)]
    rw [Finset.sum_congr rfl (fun b _ => MeasureTheory.integral_const_mul _ _)]
  exact hmono.trans (le_of_eq hval)

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
