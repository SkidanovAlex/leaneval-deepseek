import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0SlotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.n0ProjOpOrthAux.n0Iter_fix`

If every slot `i` of the list `l` leaves the state `Ψ` *fixed on the box* — i.e. `P_{B,i}Ψ = Ψ`
there when `b i = true`, and `P_{B,i}Ψ = 0` there when `b i = false` — then the whole slot
iteration `n0Iter volA A b l` leaves `Ψ` fixed on the box.

## The mathematical point

`P_{B,i}Φ(x)` for `x ∈ abox N ℓ` is `volA⁻¹ ∫_{z∈A} Φ(x|i↦z) dz · 1_A(x_i)`, and `A ⊆ acube ℓ`
puts every `x|i↦z` (`z ∈ A`) back in the box whenever `x` is in the box.  Hence, *on the box*,
`P_{B,i}` only reads the values of its argument on the box
(`Work.BoseFixB1S.agreeBox_boxPInd`).

Consequently the slot iteration can be peeled from the left: putting `Φ' = n0Slot volA A b i Φ`,
the hypothesis at the head slot `i` says exactly that `Φ'` agrees with `Φ` on the box
(`P_iΦ = Φ` in the `true` case, `Φ − P_iΦ = Φ − 0 = Φ` in the `false` case), so for every other
slot `j` the value `P_jΦ'` on the box equals `P_jΦ` on the box, and the hypothesis transfers to
`Φ'`.  No commutation of the projections (and no idempotence) is needed: only the box locality of
`P_j` and the single-slot hypothesis at the head.
-/

noncomputable section

open MeasureTheory

namespace Work.n0ProjOpOrthAux

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The single-slot fixing condition.**  Slot `i` fixes `Ψ` when, on the analysis box,
`P_{B,i}Ψ = Ψ` if `b i = true` and `P_{B,i}Ψ = 0` if `b i = false`.  The two alternatives are the
two ways in which `n0Slot volA A b i Ψ = Ψ` can hold on the box (see
`Work.BoseFixB1S.n0Slot_eq_true` / `n0Slot_eq_false`). -/
def SlotFixes {N : ℕ} (ℓ volA : ℝ) (A : Set E3) (b : Fin N → Bool) (i : Fin N)
    (Ψ : X N → ℝ) : Prop :=
  (b i = true → ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxPInd volA A i Ψ x = Ψ x) ∧
  (b i = false → ∀ x ∈ abox N ℓ, Work.UBBInputs8.boxPInd volA A i Ψ x = 0)

/-- **The iteration fixing lemma (box form).**  If every slot of `l` fixes `Φ` on the box, then
`n0Iter volA A b l Φ = Φ` on the box.  Proved by peeling the head slot: the head hypothesis makes
`n0Slot volA A b i Φ` agree with `Φ` on the box, and `P_j` only reads box values. -/
theorem n0Iter_fix_aux {N : ℕ} {ℓ volA : ℝ} {A : Set E3} (hA : MeasurableSet A)
    (hAc : A ⊆ acube ℓ) (b : Fin N → Bool) :
    ∀ (l : List (Fin N)) (Φ : X N → ℝ),
      (∀ i ∈ l, SlotFixes ℓ volA A b i Φ) →
      ∀ x ∈ abox N ℓ, Work.BoseFixB1S.n0Iter volA A b l Φ x = Φ x := by
  intro l
  induction l with
  | nil => intro Φ _ x _; rfl
  | cons i l ih =>
    intro Φ hfix x hx
    rw [Work.BoseFixB1S.n0Iter_cons]
    -- The head slot is applied first; call the resulting state `Φ'`.
    have hfixi : SlotFixes ℓ volA A b i Φ := hfix i List.mem_cons_self
    -- `Φ'` agrees with `Φ` on the box.
    have hΦ'box : ∀ y ∈ abox N ℓ, Work.BoseFixB1S.n0Slot volA A b i Φ y = Φ y := by
      intro y hy
      by_cases hbi : b i = true
      · rw [Work.BoseFixB1S.n0Slot_eq_true volA A b i Φ hbi]
        exact hfixi.1 hbi y hy
      · have hbf : b i = false := by cases hb : b i <;> simp_all
        rw [Work.BoseFixB1S.n0Slot_eq_false volA A b i Φ hbf]
        show Φ y - Work.UBBInputs8.boxPInd volA A i Φ y = Φ y
        rw [hfixi.2 hbf y hy, sub_zero]
    -- hence the hypothesis transfers to `Φ'`.
    have h' : ∀ j ∈ l, SlotFixes ℓ volA A b j (Work.BoseFixB1S.n0Slot volA A b i Φ) := by
      intro j hj
      have hfixj : SlotFixes ℓ volA A b j Φ :=
        hfix j (List.mem_cons_of_mem i hj)
      have hagree : ∀ y ∈ abox N ℓ,
          Work.UBBInputs8.boxPInd volA A j (Work.BoseFixB1S.n0Slot volA A b i Φ) y
            = Work.UBBInputs8.boxPInd volA A j Φ y :=
        Work.BoseFixB1S.agreeBox_boxPInd hA hAc j hΦ'box
      refine ⟨?_, ?_⟩
      · intro hbj y hy
        rw [hagree y hy, hfixj.1 hbj y hy, hΦ'box y hy]
      · intro hbj y hy
        rw [hagree y hy, hfixj.2 hbj y hy]
    rw [ih (Work.BoseFixB1S.n0Slot volA A b i Φ) h' x hx, hΦ'box x hx]

theorem n0Iter_fix {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (b : Fin N → Bool) (l : List (Fin N)) {Ψ : Submission.BoseGases.X N → ℝ}
    (hfix : ∀ i ∈ l, ∀ x ∈ Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.n0Slot volA A b i Ψ x = Ψ x) :
    ∀ x ∈ Submission.BoseGases.abox N ℓ,
      Work.BoseFixB1S.n0Iter volA A b l Ψ x = Ψ x := by
  intro x hx
  refine n0Iter_fix_aux hA hAc b l Ψ ?_ x hx
  intro i hi
  refine ⟨?_, ?_⟩
  · intro hbi y hy
    have h := hfix i hi y hy
    rwa [Work.BoseFixB1S.n0Slot_eq_true volA A b i Ψ hbi] at h
  · intro hbi y hy
    have h := hfix i hi y hy
    rw [Work.BoseFixB1S.n0Slot_eq_false volA A b i Ψ hbi] at h
    simp only [Pi.sub_apply] at h
    linarith

end Work.n0ProjOpOrthAux
