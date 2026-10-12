import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.SlotProjAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

-- namespace `Work.BoseBoxFock`; imports `Submission.Work.BoseBoxFock.SlotProjAux`.
/-- PEEL LEMMA, measurable/bounded form.  With `Ω = EuclideanSpace ℝ (Fin 3)`,
`slotInt e S Φ x = ∫ z : (↑S → Ω), (∏ i : ↑S, PV e (x i.1) (z i)) * Φ (updateFinset x S z)` and
`slotProj1 e i Ψ x = ∫ w : Ω, PV e (x i) w * Ψ (update x i w)`; projecting the slots of `S ∪ {i}`
(`i ∉ S`) equals projecting the slot `i` after projecting the slots of `S`.  No orthonormality is
needed; the state is assumed only measurable and bounded (NOT continuous, NOT compactly supported).

Route: change variables along `Eeq hi` (`Eeq_measurePreserving`, `MeasurePreserving.integral_comp`),
rewrite with `prod_Eeq`/`updateFinset_Eeq`, then `MeasureTheory.integral_prod_symm` — the needed
`Integrable` follows from `integrable_mul_of_continuous_hasCompactSupport_of_bounded` in
`SlotProjAux` applied to the continuous compactly supported kernel
`(z',w) ↦ (∏ i : ↑S, PV e (x i.1) (z' i)) * PV e (x i) w` and the bounded measurable state
`(z',w) ↦ Ψ (update (updateFinset x S z') i w)` — and `integral_const_mul` together with
`Function.update_of_ne` (`u.1 ≠ i` for `u : ↑S`). -/
theorem slotInt_peelMB {m : ℕ} (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ)
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    {ι : Type*} [DecidableEq ι] {S : Finset ι} {i : ι} (hi : i ∉ S)
    (Φ : (ι → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΦm : Measurable Φ)
    (hΦb : ∃ C, ∀ y, ‖Φ y‖ ≤ C) :
    slotInt e (S ∪ {i}) Φ = slotProj1 e i (slotInt e S Φ) := by
  classical
  funext x
  -- the common integrand, written as a function of the `S`-slots and of the extra slot `i`
  let G : (↑S → Ω) → Ω → ℂ :=
    fun z' w => (∏ u : ↑S, PV e (x u.1) (z' u)) *
      (PV e (x i) w * Φ (Function.update (Function.updateFinset x S z') i w))
  -- the integrand of `slotInt e (S ∪ {i}) Φ x`, viewed on the `S ∪ {i}`-configuration space
  let g : (↑(S ∪ {i}) → Ω) → ℂ :=
    fun z => (∏ u : ↑(S ∪ {i}), PV e (x u.1) (z u)) * Φ (Function.updateFinset x (S ∪ {i}) z)
  have hmp : MeasurePreserving (Eeq hi) (volume : Measure ((↑S → Ω) × Ω))
      (volume : Measure (↑(S ∪ {i}) → Ω)) := Eeq_measurePreserving hi
  have hemb : MeasurableEmbedding (Eeq hi) := (Eeq hi).measurableEmbedding
  -- the two faces of the integrand agree along the splitting equivalence
  have hcomp : ∀ p : (↑S → Ω) × Ω, g (Eeq hi p) = G p.1 p.2 := by
    rintro ⟨z', w⟩
    simp only [g, G]
    rw [prod_Eeq e hi x z' w, updateFinset_Eeq hi x z' w]
    ring
  -- the first factor of `g` is a continuous compactly supported kernel
  have hcont : Continuous (fun z : ↑(S ∪ {i}) → Ω => ∏ u : ↑(S ∪ {i}), PV e (x u.1) (z u)) :=
    continuous_finsetProd _ (fun u _ =>
      (continuous_PV_snd e he (x u.1)).comp (continuous_apply u))
  have hcs : HasCompactSupport (fun z : ↑(S ∪ {i}) → Ω =>
      ∏ u : ↑(S ∪ {i}), PV e (x u.1) (z u)) := hasCompactSupport_prod_PV e hec (S ∪ {i}) x
  -- the second factor is a bounded measurable state
  have hmeas : Measurable (fun z : ↑(S ∪ {i}) → Ω => Function.updateFinset x (S ∪ {i}) z) := by
    refine Measurable.of_eval (fun j => ?_)
    simp only [Function.updateFinset_def]
    split_ifs with hj
    · exact measurable_pi_apply _
    · exact measurable_const
  have hbdd : ∃ C, ∀ z : ↑(S ∪ {i}) → Ω,
      ‖Φ (Function.updateFinset x (S ∪ {i}) z)‖ ≤ C := by
    obtain ⟨C, hC⟩ := hΦb
    exact ⟨C, fun z => hC _⟩
  have hg : Integrable g volume :=
    integrable_mul_of_continuous_hasCompactSupport_of_bounded hcont hcs
      ((hΦm.comp hmeas).aestronglyMeasurable) hbdd
  have hInt : Integrable (fun q : (↑S → Ω) × Ω => G q.1 q.2) (volume.prod volume) :=
    ((hmp.integrable_comp_emb hemb).mpr hg).congr
      (Filter.Eventually.of_forall hcomp)
  -- left-hand side: change of variables along `Eeq`
  have hL : slotInt e (S ∪ {i}) Φ x = ∫ q : (↑S → Ω) × Ω, G q.1 q.2 := by
    have h1 : slotInt e (S ∪ {i}) Φ x = ∫ z : ↑(S ∪ {i}) → Ω, g z := rfl
    rw [h1, ← hmp.integral_comp hemb g]
    exact integral_congr_ae (Filter.Eventually.of_forall hcomp)
  -- right-hand side: expand the inner `slotInt` and pull out the factor of the slot `i`
  have hR : slotProj1 e i (slotInt e S Φ) x =
      ∫ w : Ω, ∫ z' : ↑S → Ω, G z' w := by
    rw [slotProj1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [slotInt]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z' => ?_)
    simp only [G]
    have hprod : (∏ u : ↑S, PV e (Function.update x i w u.1) (z' u))
        = ∏ u : ↑S, PV e (x u.1) (z' u) :=
      Finset.prod_congr rfl (fun u _ => by
        rw [Function.update_of_ne (show u.1 ≠ i from by rintro rfl; exact hi u.2)])
    have hcfg : Function.updateFinset (Function.update x i w) S z' =
        Function.update (Function.updateFinset x S z') i w := by
      funext j
      by_cases hj : j ∈ S
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simp [Function.updateFinset, Function.update_of_ne hji, hj]
      · by_cases hji : j = i
        · subst hji
          simp [Function.updateFinset, hj]
        · simp [Function.updateFinset, Function.update_of_ne hji, hj]
    rw [hprod, hcfg]
    ring
  -- Fubini: the product integral of `G` as the iterated integral over the last slot first
  rw [hL, hR]
  exact integral_prod_symm (fun q : (↑S → Ω) × Ω => G q.1 q.2) hInt

end Work.BoseBoxFock
