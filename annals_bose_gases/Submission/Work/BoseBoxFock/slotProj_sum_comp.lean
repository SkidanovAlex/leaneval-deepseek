import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotProj_idem_and_comm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

-- Linearity of `slotProj e T` in its state argument together with the composition law, applied to
-- a finite linear combination of slot projections: the integrand of `slotProj` is the fixed kernel
-- times the state, so `slotProj e T` is additive and `ℂ`-homogeneous on bounded measurable states
-- (integrability of each piece follows from the compactly supported continuous kernel times a
-- bounded measurable state, `integrable_mul_of_continuous_hasCompactSupport_of_bounded`), and
-- `slotInt_comp` of `slotProj_idem_and_comm` gives `slotProj e T (slotProj e U Φ) =
-- slotProj e (T ∪ U) Φ` since `slotProj e U Φ` is measurable and bounded
-- (`slotInt_measurable_bounded`).
theorem slotProj_sum_comp {m n : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', ∫ z, star (e l z) * e l' z = (if l = l' then (1 : ℂ) else 0))
    (T : Finset (Fin n)) (s : Finset (Finset (Fin n))) (c : Finset (Fin n) → ℂ)
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    slotProj e T (fun x => ∑ U ∈ s, c U • slotProj e U Φ x) =
      fun x => ∑ U ∈ s, c U • slotProj e (T ∪ U) Φ x := by
  -- It suffices to prove the identity pointwise, and to rewrite `slotProj` as `slotInt`
  -- (`slotProj_eq_slotInt_fun`), which is the form in which the integral can be handled.
  funext x
  simp only [slotProj_eq_slotInt_fun]
  -- `slotProj e U Φ` is measurable and bounded for every `U` (`slotInt_measurable_bounded`).
  have hmb : ∀ U : Finset (Fin n),
      Measurable (slotInt e U Φ) ∧ ∃ C, ∀ y : Fin n → Ω, ‖slotInt e U Φ y‖ ≤ C :=
    fun U => slotInt_measurable_bounded e he hec U Φ hΦm hΦb
  -- Each summand of the integrand — the fixed compactly supported continuous kernel
  -- `z ↦ ∏ i : ↑T, PV e (x i.1) (z i)` times the (measurable, bounded) state
  -- `z ↦ slotProj e U Φ (updateFinset x T z)` — is integrable.
  have hInt : ∀ U ∈ s, Integrable (fun z : ↑T → Ω =>
      (∏ i : ↑T, PV e (x i.1) (z i)) * slotInt e U Φ (Function.updateFinset x T z)) volume := by
    intro U _
    have hKcont : Continuous (fun z : ↑T → Ω => ∏ i : ↑T, PV e (x i.1) (z i)) :=
      continuous_finsetProd _ (fun i _ => (continuous_PV_snd e he (x i.1)).comp (continuous_apply i))
    have hKcs : HasCompactSupport (fun z : ↑T → Ω => ∏ i : ↑T, PV e (x i.1) (z i)) :=
      hasCompactSupport_prod_PV e hec T x
    have hupd : Measurable (fun z : ↑T → Ω => Function.updateFinset x T z) :=
      (measurable_updateFinset_pair T).comp (measurable_const.prodMk measurable_id)
    obtain ⟨C, hC⟩ := (hmb U).2
    exact integrable_mul_of_continuous_hasCompactSupport_of_bounded (μ := volume)
      (f := fun z : ↑T → Ω => slotInt e U Φ (Function.updateFinset x T z))
      hKcont hKcs (((hmb U).1.comp hupd).aestronglyMeasurable)
      ⟨C, fun z => hC (Function.updateFinset x T z)⟩
  -- **Linearity**: the integral of the fixed kernel times a finite linear combination of states
  -- is the linear combination of the integrals.
  have key : slotInt e T (fun y => ∑ U ∈ s, c U • slotInt e U Φ y) x
      = ∑ U ∈ s, c U • slotInt e T (slotInt e U Φ) x := by
    have hpt : ∀ z : ↑T → Ω, (∏ i : ↑T, PV e (x i.1) (z i)) *
        (∑ U ∈ s, c U • slotInt e U Φ (Function.updateFinset x T z))
        = ∑ U ∈ s, c U • ((∏ i : ↑T, PV e (x i.1) (z i)) *
            slotInt e U Φ (Function.updateFinset x T z)) := by
      intro z
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun U _ => ?_
      rw [smul_eq_mul, smul_eq_mul]
      ring
    calc slotInt e T (fun y => ∑ U ∈ s, c U • slotInt e U Φ y) x
        = ∫ z : ↑T → Ω, (∏ i : ↑T, PV e (x i.1) (z i)) *
            (∑ U ∈ s, c U • slotInt e U Φ (Function.updateFinset x T z)) := rfl
      _ = ∫ z : ↑T → Ω, ∑ U ∈ s, c U • ((∏ i : ↑T, PV e (x i.1) (z i)) *
            slotInt e U Φ (Function.updateFinset x T z)) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∑ U ∈ s, ∫ z : ↑T → Ω, c U • ((∏ i : ↑T, PV e (x i.1) (z i)) *
            slotInt e U Φ (Function.updateFinset x T z)) :=
          integral_finsetSum _ (fun U hU => by
            simpa only [smul_eq_mul] using (hInt U hU).const_mul (c U))
      _ = ∑ U ∈ s, c U • ∫ z : ↑T → Ω, (∏ i : ↑T, PV e (x i.1) (z i)) *
            slotInt e U Φ (Function.updateFinset x T z) := by
          refine Finset.sum_congr rfl fun U _ => ?_
          rw [integral_smul]
      _ = ∑ U ∈ s, c U • slotInt e T (slotInt e U Φ) x :=
          Finset.sum_congr rfl fun U _ => rfl
  rw [key]
  -- **Composition law**: `slotInt e T (slotInt e U Φ) = slotInt e (T ∪ U) Φ`.
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [slotInt_comp e he hec horth Φ hΦm hΦb T U]

end Work.BoseBoxFock
