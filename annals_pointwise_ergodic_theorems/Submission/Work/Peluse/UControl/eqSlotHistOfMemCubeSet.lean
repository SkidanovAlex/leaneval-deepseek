import Mathlib
import Submission.Work.Peluse.UControl.slotHist_natAdd

namespace Work.Peluse.UControl

/-- `slotHist h₀ r w` is the concatenation of `h₀` with `w`, in Mathlib's sense of `Fin.append`:
the two evaluation lemmas `slotHist_castAdd` (on the old coordinates) and `slotHist_natAdd` (on the
new ones) determine it. -/
lemma append_eq_slotHist {L r : ℕ} (h₀ : Fin L → Bool) (w : Fin r → Bool) :
    Fin.append h₀ w = slotHist h₀ r w := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) i
  · rw [Fin.append_left, slotHist_castAdd]
  · rw [Fin.append_right, slotHist_natAdd]

/-- The sub-cube of `Fin (L + r) → Bool` of functions agreeing with `slotHist h₀ r 0` on the first
`L` coordinates is exactly the set of `slotHist h₀ r w`, with a unique `w`.  (`slotHist` appends the
`r` Boolean coordinates `w` to `h₀ : Fin L → Bool`; `slotHist_natAdd` evaluates it at the new
coordinates: `slotHist h₀ r w (Fin.natAdd L j) = w j`.)

Proof route: existence with `w j := h (Fin.natAdd L j)`, by induction on `r` — split `h` as
`Fin.snoc (Fin.init h) (h (Fin.last …))` (`Fin.snoc_init_self`), apply the induction hypothesis to
`Fin.init h` and identify the last coordinate with `Fin.natAdd L (Fin.last …)` (`Fin.natAdd_last`);
uniqueness follows from `slotHist_natAdd` by evaluating at `Fin.natAdd L j`. -/
theorem eqSlotHistOfMemCubeSet {L r : ℕ} {h₀ : Fin L → Bool} {h : Fin (L + r) → Bool}
    (hh : h ∈ cubeSet (L + r) (Finset.univ.filter (fun i : Fin (L + r) => L ≤ i.1))
      (slotHist h₀ r 0)) :
    ∃! w : Fin r → Bool, h = slotHist h₀ r w := by
  -- the coordinates `Fin.castAdd r i` are the "old" ones, off which `h` agrees with `h₀`
  have hmem : ∀ i : Fin L,
      Fin.castAdd r i ∉ Finset.univ.filter (fun i : Fin (L + r) => L ≤ i.1) := by
    intro i
    have hval : (Fin.castAdd r i).1 = i.1 := rfl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hval]
    omega
  have hleft : (fun i : Fin L => h (Fin.castAdd r i)) = h₀ := by
    funext i
    rw [(Finset.mem_filter.mp hh).2 _ (hmem i), slotHist_castAdd]
  refine ⟨(fun j : Fin r => h (Fin.natAdd L j)), ?_, ?_⟩
  · -- `h` is recovered from the two halves `h ∘ castAdd = h₀` and `h ∘ natAdd`
    have hsplit : h = Fin.append (fun i : Fin L => h (Fin.castAdd r i))
        (fun j : Fin r => h (Fin.natAdd L j)) :=
      (Fin.append_castAdd_natAdd (m := L) (n := r) (f := h)).symm
    have hzero : Fin.append (fun i : Fin L => h (Fin.castAdd r i))
        (fun j : Fin r => h (Fin.natAdd L j))
        = Fin.append h₀ (fun j : Fin r => h (Fin.natAdd L j)) := by
      rw [hleft]
    exact hsplit.trans (hzero.trans (append_eq_slotHist h₀ _))
  · intro w hw
    funext j
    have h1 := congrFun hw (Fin.natAdd L j)
    rw [slotHist_natAdd] at h1
    exact h1.symm

end Work.Peluse.UControl
