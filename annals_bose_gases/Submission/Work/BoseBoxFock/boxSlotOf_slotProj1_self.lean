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
# `Work.BoseBoxFock.boxSlotOf_slotProj1_self` — the slot-`j` rank-one operator absorbs the
`j`-th slot projection

The one-body operator `|η_w⟩⟨η_v|` of `Work.BoseDict.Defs2` acts on the `j`-th slot by
`boxSlotOf e w v j`.  When `w = evec m l`, `v = evec m l'` the superposition `η_w` is the mode
`e l` itself, and both modes lie in the span of the `e k`; hence the rank-one operator
`|e l⟩⟨e l'|` is not affected by projecting the `j`-th slot of the state onto that span, i.e.

    boxSlotOf e (evec m l) (evec m l') j (slotProj1 e j Θ)
      = boxSlotOf e (evec m l) (evec m l') j Θ .

This is the "absorption" identity behind the box-side fibre decomposition (`BF3C_PLAN.md` §1):
the projection `slotProj1 e j` is the identity on the `V`-slots of the model's rows.

The proof is a two-variable Fubini: expanding both the fibre integral (over `w`) and the slot
projection (over `z`) and using the resolution form of `PV` plus orthonormality `horth`
(the identity `∫ z, star (e l' z) * PV e z w = star (e l' w)`) collapses the double integral
back onto the single one.
-/

namespace Work.BoseBoxFock

open MeasureTheory

set_option autoImplicit false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- `etaOf` of a basis vector `evec m l` is the mode `e l` itself. -/
theorem etaOf_evec_self {m : ℕ} (e : Fin m → Ω → ℂ) (l : Fin m) :
    Work.BoseDict.etaOf e (Work.BoseB4.evec m l) = e l := by
  funext z
  simp only [Work.BoseDict.etaOf, Work.BoseB4.evec, Pi.single_apply]
  rw [show (∑ x : Fin m, (↑(if x = l then (1 : ℝ) else 0) : ℂ) * e x z)
      = ∑ x : Fin m, (if x = l then e x z else 0) from
    Finset.sum_congr rfl (fun x _ => by split_ifs <;> simp)]
  rw [Finset.sum_ite_eq']
  simp

/-- The two-variable integrand of the absorption computation is integrable: it is the
continuous compactly supported kernel `(z, w) ↦ star (e l' z) * PV e z w` times the bounded
measurable state `(z, w) ↦ Θ (Function.update x j w)`. -/
theorem integrable_uncurry_slotProj1_self {m d : ℕ} (e : Fin m → Ω → ℂ) (l' : Fin m) (j : Fin d)
    (he : ∀ k, Continuous (e k)) (hec : ∀ k, HasCompactSupport (e k))
    (Θ : (Fin d → Ω) → ℂ) (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    (x : Fin d → Ω) :
    Integrable (Function.uncurry (fun z w : Ω =>
      star (e l' z) * (PV e z w * Θ (Function.update x j w)))) (volume.prod volume) := by
  refine (integrable_uncurry_of_cont_cs (g := fun p : Ω × Ω => star (e l' p.1) * PV e p.1 p.2)
    (h := fun p : Ω × Ω => Θ (Function.update x j p.2))
    ?_ ?_ ?_ ?_).congr ?_
  · exact ((continuous_star.comp (he l')).comp continuous_fst).mul (continuous_PV_uncurry e he)
  · refine HasCompactSupport.intro
      (((hec l').comp_left (g := star) (by simp : star (0 : ℂ) = 0)).isCompact.prod
        (isCompact_iUnion (fun k : Fin m => (hec k).isCompact))) ?_
    rintro ⟨z, w⟩ hzw
    by_cases hz : z ∈ tsupport (fun y : Ω => star (e l' y))
    · have hw : w ∉ ⋃ k : Fin m, tsupport (e k) := fun hw => hzw ⟨hz, hw⟩
      simp [PV_eq_zero_of_notMem_iUnion e hw]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  · exact hΘm.comp (measurable_update_snd x j)
  · obtain ⟨C, hC⟩ := hΘb; exact ⟨C, fun p => hC _⟩
  · filter_upwards with p
    simp only [Function.uncurry]
    ring

/-- The `j`-th slot of the rank-one operator `|e l⟩⟨e l'|` is unaffected by the `j`-th slot
projection onto `span{e k}`. -/
theorem boxSlotOf_slotProj1_self {m d : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ) (l l' : Fin m) (j : Fin d)
    (he : ∀ k, Continuous (e k)) (hec : ∀ k, HasCompactSupport (e k))
    (horth : ∀ k k', ∫ z, star (e k z) * e k' z = (if k = k' then (1 : ℂ) else 0))
    (hint : ∀ k k', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e k z) * e k' z))
    (Θ : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j
        (Work.BoseBoxFock.slotProj1 e j Θ)
      = Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ := by
  -- the resolution form of `PV`: `∫ z, star (e l' z) * PV e z w = star (e l' w)`
  have hval : ∀ w : Ω, (∫ z, star (e l' z) * PV e z w) = star (e l' w) := by
    intro w
    have hpt : (fun z : Ω => star (e l' z) * PV e z w)
        = (fun z : Ω => ∑ k : Fin m, star (e k w) * (star (e l' z) * e k z)) := by
      funext z
      simp only [PV, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring
    rw [hpt, MeasureTheory.integral_finsetSum]
    swap
    · intro k _
      exact (hint l' k).const_mul _
    have hsum : (∑ k : Fin m, ∫ z, star (e k w) * (star (e l' z) * e k z))
        = ∑ k : Fin m, star (e k w) * (if l' = k then (1 : ℂ) else 0) :=
      Finset.sum_congr rfl (fun k _ => by rw [integral_const_mul, horth l' k])
    rw [hsum]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  funext x
  simp only [Work.BoseDict.boxSlotOf]
  rw [etaOf_evec_self e l, etaOf_evec_self e l']
  have hstep : ∀ z : Ω, (slotProj1 e j Θ) (Function.update x j z)
      = ∫ w, PV e z w * Θ (Function.update x j w) := by
    intro z
    rw [slotProj1]
    apply integral_congr_ae
    filter_upwards with w
    rw [Function.update_self, Function.update_idem]
  have hmain : (∫ z, star (e l' z) * (slotProj1 e j Θ) (Function.update x j z))
      = ∫ z, star (e l' z) * Θ (Function.update x j z) := by
    calc ∫ z, star (e l' z) * (slotProj1 e j Θ) (Function.update x j z)
        = ∫ z, star (e l' z) * (∫ w, PV e z w * Θ (Function.update x j w)) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [hstep z]
      _ = ∫ z, ∫ w, star (e l' z) * (PV e z w * Θ (Function.update x j w)) := by
          apply integral_congr_ae
          filter_upwards with z
          rw [integral_const_mul]
      _ = ∫ w, ∫ z, star (e l' z) * (PV e z w * Θ (Function.update x j w)) :=
          integral_integral_swap
            (integrable_uncurry_slotProj1_self e l' j he hec Θ hΘm hΘb x)
      _ = ∫ w, (∫ z, star (e l' z) * PV e z w) * Θ (Function.update x j w) := by
          apply integral_congr_ae
          filter_upwards with w
          rw [show (fun z : Ω => star (e l' z) * (PV e z w * Θ (Function.update x j w)))
              = (fun z : Ω => (star (e l' z) * PV e z w) * Θ (Function.update x j w))
              from funext fun z => by ring]
          rw [integral_mul_const]
      _ = ∫ w, star (e l' w) * Θ (Function.update x j w) := by
          apply integral_congr_ae
          filter_upwards with w
          rw [hval w]
  exact congrArg (fun t => e l (x j) * t) hmain

end Work.BoseBoxFock
