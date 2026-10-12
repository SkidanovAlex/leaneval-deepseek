import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FibreProjDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

namespace Work.BoseBoxFock.SecAux

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- **Linearity of `slotProj e T` in its state argument**: on bounded measurable states the slot
projection commutes with finite `ℂ`-linear combinations.

`slotProj e T Φ x` is the Bochner integral over the slots of `T` of the fixed kernel
`z ↦ ∏ i : ↑T, PV e (x i.1) (z i)` against the state `Φ` at the configuration in which the slots of
`T` are replaced by `z` (`slotProj_eq_slotInt_fun` writes this as `slotInt`).  The kernel is
continuous and compactly supported (`continuous_finsetProd`, `hasCompactSupport_prod_PV`) and each
`Ψ U` is measurable and bounded, so every piece of the integrand is integrable
(`integrable_mul_of_continuous_hasCompactSupport_of_bounded`), and the Bochner integral is additive
and `ℂ`-homogeneous on integrable functions. -/
theorem slotProj_finset_sum {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (T : Finset (Fin n)) (s : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℂ)
    (Ψ : Finset (Fin n) → (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΨm : ∀ U, Measurable (Ψ U)) (hΨb : ∀ U, ∃ C, ∀ x, ‖Ψ U x‖ ≤ C) :
    slotProj e T (fun x => ∑ U ∈ s, c U • Ψ U x) =
      fun x => ∑ U ∈ s, c U • slotProj e T (Ψ U) x := by
  classical
  -- It suffices to prove the identity pointwise, and to rewrite `slotProj` as `slotInt`.
  funext x
  simp only [slotProj_eq_slotInt_fun]
  -- Each summand of the integrand — the fixed compactly supported continuous kernel
  -- `z ↦ ∏ i : ↑T, PV e (x i.1) (z i)` times the (measurable, bounded) state
  -- `z ↦ Ψ U (updateFinset x T z)` — is integrable.
  have hInt : ∀ U ∈ s, Integrable (fun z : ↑T → Ω =>
      (∏ i : ↑T, PV e (x i.1) (z i)) * Ψ U (Function.updateFinset x T z)) volume := by
    intro U _
    have hKcont : Continuous (fun z : ↑T → Ω => ∏ i : ↑T, PV e (x i.1) (z i)) :=
      continuous_finsetProd _ (fun i _ => (continuous_PV_snd e he (x i.1)).comp (continuous_apply i))
    have hKcs : HasCompactSupport (fun z : ↑T → Ω => ∏ i : ↑T, PV e (x i.1) (z i)) :=
      hasCompactSupport_prod_PV e hec T x
    have hupd : Measurable (fun z : ↑T → Ω => Function.updateFinset x T z) :=
      (measurable_updateFinset_pair T).comp (measurable_const.prodMk measurable_id)
    obtain ⟨C, hC⟩ := hΨb U
    exact integrable_mul_of_continuous_hasCompactSupport_of_bounded (μ := volume)
      (f := fun z : ↑T → Ω => Ψ U (Function.updateFinset x T z))
      hKcont hKcs (((hΨm U).comp hupd).aestronglyMeasurable)
      ⟨C, fun z => hC (Function.updateFinset x T z)⟩
  -- Pointwise, the kernel factors out of the finite linear combination.
  have hpt : ∀ z : ↑T → Ω, (∏ i : ↑T, PV e (x i.1) (z i)) *
      (∑ U ∈ s, c U • Ψ U (Function.updateFinset x T z))
      = ∑ U ∈ s, c U • ((∏ i : ↑T, PV e (x i.1) (z i)) *
          Ψ U (Function.updateFinset x T z)) := by
    intro z
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [smul_eq_mul, smul_eq_mul]
    ring
  -- **Linearity**: the integral of the fixed kernel times a finite linear combination of states
  -- is the linear combination of the integrals.
  calc slotInt e T (fun y => ∑ U ∈ s, c U • Ψ U y) x
      = ∫ z : ↑T → Ω, (∏ i : ↑T, PV e (x i.1) (z i)) *
          (∑ U ∈ s, c U • Ψ U (Function.updateFinset x T z)) := rfl
    _ = ∫ z : ↑T → Ω, ∑ U ∈ s, c U • ((∏ i : ↑T, PV e (x i.1) (z i)) *
          Ψ U (Function.updateFinset x T z)) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ U ∈ s, ∫ z : ↑T → Ω, c U • ((∏ i : ↑T, PV e (x i.1) (z i)) *
          Ψ U (Function.updateFinset x T z)) :=
        integral_finsetSum _ (fun U hU => by
          simpa only [smul_eq_mul] using (hInt U hU).const_mul (c U))
    _ = ∑ U ∈ s, c U • ∫ z : ↑T → Ω, (∏ i : ↑T, PV e (x i.1) (z i)) *
          Ψ U (Function.updateFinset x T z) := by
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [integral_smul]
    _ = ∑ U ∈ s, c U • slotInt e T (Ψ U) x := Finset.sum_congr rfl fun U _ => rfl

end Work.BoseBoxFock.SecAux
