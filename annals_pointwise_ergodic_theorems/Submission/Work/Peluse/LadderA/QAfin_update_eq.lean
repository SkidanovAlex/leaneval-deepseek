import Mathlib
import Submission.Work.Peluse.ladderA_defs

namespace Work.Peluse.LadderA

theorem QAfin_update_eq {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Work.Peluse.UControl.Slot ι k → ℤ)
    (s₀ : Work.Peluse.UControl.Slot ι k) (a₀ : ℤ) :
    ∀ i : Fin (Fintype.card (Work.Peluse.LadderA.AIdx k kω s₀)),
      Work.Peluse.LadderA.QAfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀ i =
        Work.Peluse.arithIcc (p s₀.1 a * a₀ +
          ∑ s ∈ (((Fintype.equivFin (Work.Peluse.LadderA.AIdx k kω s₀)).symm i).1.1.1.erase s₀),
            p s.1 a * a'' s) M₁ := by
  -- **Updating the peeled parameter.**  For the `A`-indices `j = ⟨⟨ω, h⟩, r⟩` of the ladder, over
  -- the slot set `ω ∋ s₀` the sum `∑_{s ∈ ω} p s.1 a · a' s` of `pDir` splits into the `s₀`-term
  -- (whose value is the updated entry `a₀`, with coefficient `p s₀.1 a`) and the remaining sum over
  -- `ω.erase s₀`, where the update is invisible.
  intro i
  -- `j` is the `A`-index of `i`; its slot set contains `s₀` by definition of `AIdx`.
  set j := (Fintype.equivFin (Work.Peluse.LadderA.AIdx k kω s₀)).symm i with hj
  have hmem : s₀ ∈ j.1.1.1 := j.1.2
  simp only [Work.Peluse.LadderA.QAfin, Work.Peluse.LadderA.qA, Work.Peluse.UControl.pDir]
  congr 1
  -- Split the sum over `j.1.1.1 ∋ s₀` into the `s₀`-term and the sum over the erased set.
  rw [← Finset.sum_erase_add j.1.1.1
    (fun s => p s.1 a * Function.update a'' s₀ a₀ s) hmem]
  simp only [Function.update_self]
  rw [add_comm]
  congr 1
  -- On the erased set `s ≠ s₀`, so the update does nothing.
  exact Finset.sum_congr rfl (fun s hs => by
    rw [Function.update_of_ne (Finset.mem_erase.mp hs).1])

end Work.Peluse.LadderA
