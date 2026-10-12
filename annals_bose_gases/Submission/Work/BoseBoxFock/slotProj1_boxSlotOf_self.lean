import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.fibre_decomposition
import Submission.Work.BoseDict.Defs3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotProj1_boxSlotOf_self` — the box slot operators are already in the modes

The box ↔ model dictionary writes every one-body row of the box Hamiltonian through the
first-quantised slot operators

`(boxSlotOf e w v j Θ)(x) = η_w(x_j) · ∫_z conj(η_v z) · Θ(x[j ↦ z])`

(`Work.BoseDict.Defs2`), where `η_w = Σ_l w_l e_l` and `x[j ↦ z] = Function.update x j z`.
For the *coordinate* vectors `w = evec m l`, `v = evec m l'` the slot operator is exactly the
rank-one slot `|e_l⟩⟨e_{l'}|` acting in the slot `j`, so its `j`-th slot is *already* in the
span of the modes and the single-slot projection `slotProj1 e j` leaves it unchanged:

    slotProj1 e j (boxSlotOf e (evec l) (evec l') j Θ) = boxSlotOf e (evec l) (evec l') j Θ .

The whole content is the one-dimensional kernel computation

    ∫_w PV e (x j) w · e_l w = e_l (x j),

which is `integral_PV_mul_eq_sum` (`PV_algebra`) followed by orthonormality (`horth`):
`∫_w (Σ_k e_k(x_j) conj(e_k w)) e_l w = Σ_k e_k(x_j) δ_{kl} = e_l(x_j)`.
(The `w`-integral contributes nothing that depends on `w` in the second factor, because
`Function.update (Function.update x j w) j z = Function.update x j z`.)

Neither regularity hypothesis on `Θ` (`hΘm`, `hΘb`) nor continuity/compact support of the modes
(`he`, `hec`) is needed: the identity is purely algebraic once the `w`-integral is evaluated.
-/

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- `η_{evec l} = e l`: the superposition of the modes with the coordinate vector `evec m l`
is the single mode `e l`. -/
private lemma etaOf_evec_eq {m : ℕ} (e : Fin m → Ω → ℂ) (l : Fin m) (z : Ω) :
    Work.BoseDict.etaOf e (Work.BoseB4.evec m l) z = e l z := by
  rw [Work.BoseDict.etaOf, Work.BoseB4.evec]
  rw [Finset.sum_eq_single l]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ l) h

theorem slotProj1_boxSlotOf_self {m d : ℕ}
    (e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ) (l l' : Fin m) (j : Fin d)
    (he : ∀ k, Continuous (e k)) (hec : ∀ k, HasCompactSupport (e k))
    (horth : ∀ k k', ∫ z, star (e k z) * e k' z = (if k = k' then (1 : ℂ) else 0))
    (hint : ∀ k k', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e k z) * e k' z))
    (Θ : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    Work.BoseBoxFock.slotProj1 e j
        (Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ)
      = Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ := by
  funext x
  -- the one-dimensional kernel computation `∫_w PV e (x j) w · e_l w = e_l (x j)`
  have hPV : ∫ w : Ω, PV e (x j) w * e l w = e l (x j) := by
    rw [integral_PV_mul_eq_sum e (fun y : Ω => e l y) (fun k => hint k l) (x j)]
    rw [Finset.sum_eq_single l]
    · rw [horth l l, if_pos rfl, mul_one]
    · intro k _ hk
      rw [horth k l, if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ l) h
  -- the slot operator in the slot `j` is constant in the integration variable `w`
  have hpt : (fun w : Ω =>
        PV e (x j) w *
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ
            (Function.update x j w))
      = (fun w : Ω => (PV e (x j) w * e l w) *
          (∫ z : Ω, star (e l' z) * Θ (Function.update x j z))) := by
    funext w
    rw [Work.BoseDict.boxSlotOf]
    simp only [Function.update_self, Function.update_idem]
    simp only [etaOf_evec_eq, starRingEnd_apply]
    ring
  rw [slotProj1, hpt, MeasureTheory.integral_mul_const, hPV]
  rw [Work.BoseDict.boxSlotOf]
  simp only [etaOf_evec_eq, starRingEnd_apply]

end Work.BoseBoxFock
