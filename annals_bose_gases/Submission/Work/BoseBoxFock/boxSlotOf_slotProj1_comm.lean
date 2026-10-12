import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.fibre_decomposition
import Submission.Work.BoseDict.Defs3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxSlotOf_slotProj1_comm` — the slot-`j` operator commutes with the
single-slot projection at a *different* slot `i`

`Work.BoseDict.boxSlotOf e (evec l) (evec l') j` acts on the slot `j` only (it multiplies by
`e l (x j)` and integrates the slot-`j` variable against `star (e l' ·)`), while
`Work.BoseBoxFock.slotProj1 e i` integrates the slot-`i` variable against the projection kernel
`PV e (x i) ·`.  For `i ≠ j` the two operators act on different slots and therefore commute.

The proof is a Fubini exchange: after unfolding both operators (`boxSlotOf_evec_apply`), the two
nested integrals are over the two slots `z` (slot `j`) and `w` (slot `i`), the nested
`Function.update`s commute by `Function.update_comm`, and the exchange
`∫ z ∫ w = ∫ w ∫ z` is `MeasureTheory.integral_integral_swap` applied to the jointly integrable
integrand `star (e l' z) · (PV e (x i) w · Θ …)`, whose integrability comes from
`Integrable.mul_prod` (`star (e l' ·)` and `PV e (x i) ·` are continuous with compact support) and
`Integrable.mul_bdd` (with `Θ` measurable and bounded).  Orthonormality `horth` and the
integrability `hint` of the mode overlaps are *not* needed here; they are hypotheses of the
ambient interface.
-/

namespace Work.BoseBoxFock

set_option linter.unusedVariables false

/-- `η_{evec l} = e l`: the superposition `η_w` at the coordinate vector `w = evec l`
(`= Pi.single l 1`) is the mode `e l`. -/
private lemma etaOf_evec_eq {m : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ) (l : Fin m)
    (z : Work.BoseDict.Sp) : Work.BoseDict.etaOf e (Work.BoseB4.evec m l) z = e l z := by
  simp only [Work.BoseDict.etaOf, Work.BoseB4.evec, Pi.single_apply]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb; simp [if_neg hb]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- The slot-`j` operator of the dictionary at the coordinate vectors `evec l`, `evec l'`, in
the form in which the slot computations are carried out:
`(boxSlotOf e (evec l) (evec l') j Θ)(x) = e l (x j) · ∫ z, star (e l' z) · Θ (x[j ↦ z])`. -/
private lemma boxSlotOf_evec_apply {m d : ℕ} (e : Fin m → Work.BoseDict.Sp → ℂ)
    (l l' : Fin m) (j : Fin d) (Θ : (Fin d → Work.BoseDict.Sp) → ℂ)
    (x : Fin d → Work.BoseDict.Sp) :
    Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x
      = e l (x j) * ∫ z, star (e l' z) * Θ (Function.update x j z) := by
  simp only [Work.BoseDict.boxSlotOf, etaOf_evec_eq]
  rfl

theorem boxSlotOf_slotProj1_comm {m d : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ) (l l' : Fin m) (i j : Fin d) (hij : i ≠ j)
    (he : ∀ k, Continuous (e k)) (hec : ∀ k, HasCompactSupport (e k))
    (horth : ∀ k k', ∫ z, star (e k z) * e k' z = (if k = k' then (1 : ℂ) else 0))
    (hint : ∀ k k', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e k z) * e k' z))
    (Θ : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
        (Work.BoseBoxFock.slotProj1 e i Θ)
      = Work.BoseBoxFock.slotProj1 e i
        (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ) := by
  classical
  funext x
  -- `PV e (x i) ·` is continuous with compact support.
  have hPVcs : HasCompactSupport (fun w : EuclideanSpace ℝ (Fin 3) => PV e (x i) w) := by
    refine HasCompactSupport.intro (isCompact_iUnion (fun l : Fin m => (hec l).isCompact)) ?_
    intro w hw
    exact PV_eq_zero_of_factors e
      (fun l => image_eq_zero_of_notMem_tsupport (fun h => hw (Set.mem_iUnion.mpr ⟨l, h⟩)))
  have hf1 : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => star (e l' z)) :=
    (continuous_star.comp (he l')).integrable_of_hasCompactSupport
      ((hec l').comp_left (g := star) (by simp))
  have hf2 : MeasureTheory.Integrable (fun w : EuclideanSpace ℝ (Fin 3) => PV e (x i) w) :=
    (continuous_PV_snd e he (x i)).integrable_of_hasCompactSupport hPVcs
  have hf : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        star (e l' p.1) * PV e (x i) p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := hf1.mul_prod hf2
  -- the joint integrand of the two slot integrals is integrable on the product
  have hφ : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Function.update (Function.update x i p.2) j p.1) :=
    ((continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin 3) ×
        EuclideanSpace ℝ (Fin 3) => x)).update i continuous_snd).update j continuous_fst
  have hg : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Θ (Function.update (Function.update x i p.2) j p.1))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (hΘm.comp hφ.measurable).aestronglyMeasurable
  obtain ⟨C, hC⟩ := hΘb
  have hbdd : Filter.Eventually
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ‖Θ (Function.update (Function.update x i p.2) j p.1)‖ ≤ C)
      (MeasureTheory.ae (MeasureTheory.volume.prod MeasureTheory.volume)) :=
    Filter.Eventually.of_forall (fun p => hC _)
  have hInt : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        star (e l' p.1) * (PV e (x i) p.2 *
          Θ (Function.update (Function.update x i p.2) j p.1)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have h := hf.mul_bdd hg hbdd
    simpa only [mul_assoc] using h
  -- Fubini: the two slot integrals commute
  have hswap : (∫ z, ∫ w, star (e l' z) * (PV e (x i) w *
        Θ (Function.update (Function.update x i w) j z)))
      = ∫ w, ∫ z, star (e l' z) * (PV e (x i) w *
        Θ (Function.update (Function.update x i w) j z)) :=
    MeasureTheory.integral_integral_swap hInt
  -- left-hand side, reduced to the `z`-outer double integral
  have hL : (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
        (Work.BoseBoxFock.slotProj1 e i Θ)) x
      = e l (x j) * ∫ z, ∫ w, star (e l' z) * (PV e (x i) w *
          Θ (Function.update (Function.update x i w) j z)) := by
    rw [boxSlotOf_evec_apply]
    have h2 : (fun z : EuclideanSpace ℝ (Fin 3) =>
          star (e l' z) * slotProj1 e i Θ (Function.update x j z))
        = fun z : EuclideanSpace ℝ (Fin 3) =>
          ∫ w, star (e l' z) * (PV e (x i) w *
            Θ (Function.update (Function.update x i w) j z)) := by
      funext z
      rw [slotProj1]
      simp only [Function.update_of_ne hij, Function.update_comm (Ne.symm hij)]
      rw [← MeasureTheory.integral_const_mul]
    rw [h2]
  -- right-hand side, reduced to the `w`-outer double integral
  have hR : (slotProj1 e i
        (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)) x
      = e l (x j) * ∫ w, ∫ z, star (e l' z) * (PV e (x i) w *
          Θ (Function.update (Function.update x i w) j z)) := by
    rw [slotProj1]
    have h2 : (fun w : EuclideanSpace ℝ (Fin 3) => PV e (x i) w *
          (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
            (Function.update x i w))
        = fun w : EuclideanSpace ℝ (Fin 3) => e l (x j) * (PV e (x i) w *
            ∫ z, star (e l' z) * Θ (Function.update (Function.update x i w) j z)) := by
      funext w
      simp only [boxSlotOf_evec_apply, Function.update_of_ne (Ne.symm hij)]
      ring
    rw [h2, MeasureTheory.integral_const_mul]
    have h3 : (∫ w, PV e (x i) w * ∫ z, star (e l' z) *
          Θ (Function.update (Function.update x i w) j z))
        = ∫ w, ∫ z, star (e l' z) * (PV e (x i) w *
            Θ (Function.update (Function.update x i w) j z)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      ring
    rw [h3]
  have hmid : e l (x j) * (∫ z, ∫ w, star (e l' z) * (PV e (x i) w *
          Θ (Function.update (Function.update x i w) j z)))
      = e l (x j) * (∫ w, ∫ z, star (e l' z) * (PV e (x i) w *
          Θ (Function.update (Function.update x i w) j z))) := by
    rw [hswap]
  exact hL.trans (hmid.trans hR.symm)

end Work.BoseBoxFock
