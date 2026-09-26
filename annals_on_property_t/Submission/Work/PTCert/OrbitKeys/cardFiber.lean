import Mathlib
import Submission.Work.PTCert.OrbitKeysDefs

/-!
# `Work.PTCert.OrbitKeys.cardFiber` — the fibre sizes of the row/group labels

The index type `EI` of the certificate is the subtype of `ℕ` cut out by the codes of `B₂`
(`EI = {z // z ∈ eS}`, `eS = eAll.toFinset`). Counting in `EI` therefore is counting inside the
duplicate-free list `eAll`:

* `card_fiber_univ`: `#{y : EI | p y.1} = (eAll.filter p).length` (using `ESem`);
* `sum_univ_eq_sum_eAll`: the same statement for sums instead of cardinalities.

The two counting `Prop`s of the shared data are of the list form: `RowSem` gives the number of
elements of the row `r` (`#{z ∈ eAll | labE 0 z = r} = cntL[r]`) and `GroupSem` gives the number of
elements of row `r` in group `g` (`#{z ∈ eAll | labE r z = g} = sizeE r g`, for `1 ≤ r`). Transported
back to `EI` these are `rowFiber_card` and `cardFiber` (for the row `0` the groups are the rows,
`ngE 0 = 18`, so `sizeE 0 g = cntL[g]` and the `RowSem` count applies).
-/

open scoped BigOperators

set_option autoImplicit false

namespace Work.PTCert.OrbitKeys

/-- Counting over the index type `EI` is counting inside the list `eAll`: for any predicate `p` on
codes, `#{y : EI | p y.1} = (eAll.filter p).length`. (`eAll` is duplicate-free by `ESem`.) -/
theorem card_fiber_univ (hE : Submission.PTCert.G.ESem) (p : ℕ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun y : Submission.PTCert.G.EI => p y.1)).card
      = (Submission.PTCert.D.eAll.filter p).length := by
  rw [← List.toFinset_card_of_nodup (hE.2.1.filter p)]
  refine Finset.card_bij (fun (y : Submission.PTCert.G.EI)
    (_ : y ∈ Finset.univ.filter (fun y : Submission.PTCert.G.EI => p y.1)) => y.1) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [List.mem_toFinset, List.mem_filter, decide_eq_true_iff]
    exact ⟨(mem_eS_iff y.1).mp y.2, hy⟩
  · intro y₁ _ y₂ _ h
    exact Subtype.ext h
  · intro b hb
    rw [List.mem_toFinset, List.mem_filter, decide_eq_true_iff] at hb
    exact ⟨⟨b, mem_eS_of_mem b hb.1⟩, by simp [Finset.mem_filter, hb.2], rfl⟩

/-- Summing over the index type `EI` is summing over the list `eAll`: `Σ y : EI, F y.1 = Σ eAll, F`
(again using that `eAll` is duplicate-free). -/
theorem sum_univ_eq_sum_eAll {M : Type*} [AddCommMonoid M] (hE : Submission.PTCert.G.ESem)
    (F : ℕ → M) :
    (∑ y : Submission.PTCert.G.EI, F y.1) = (Submission.PTCert.D.eAll.map F).sum := by
  rw [show (Finset.univ : Finset Submission.PTCert.G.EI) = Submission.PTCert.G.eS.attach from rfl]
  rw [Finset.sum_attach]
  rw [← List.sum_toFinset F hE.2.1]
  rfl

/-- The number of elements of the row `r` (the `RowSem` count, transported to `EI`). -/
theorem rowFiber_card (hE : Submission.PTCert.G.ESem) (hR : Submission.PTCert.G.RowSem)
    {r : ℕ} (hr : r < 18) :
    (Finset.univ.filter (fun y : Submission.PTCert.G.EI => Submission.PTCert.G.labE 0 y.1 = r)).card
      = Submission.PTCert.D.cntL.getD r 0 := by
  rw [card_fiber_univ hE (fun z => Submission.PTCert.G.labE 0 z = r)]
  exact hR.2.2.2.2.2.1 r hr

theorem cardFiber (hE : Submission.PTCert.G.ESem) (hR : Submission.PTCert.G.RowSem) (hG : Submission.PTCert.G.GroupSem) {r g : ℕ} (hr : r < 18) (hg : g < Submission.PTCert.G.ngE r) : (Finset.univ.filter (fun y : Submission.PTCert.G.EI => Submission.PTCert.G.labE r y.1 = g)).card = Submission.PTCert.G.sizeE r g := by
  rw [card_fiber_univ hE (fun z => Submission.PTCert.G.labE r z = g)]
  by_cases hr0 : r = 0
  · subst hr0
    have h18 : g < 18 := by rw [hG.1] at hg; exact hg
    rw [show Submission.PTCert.G.sizeE 0 g = Submission.PTCert.D.cntL.getD g 0 from rfl]
    exact hR.2.2.2.2.2.1 g h18
  · have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
    exact (hG.2.2 r hr hr1).2.2.2.1 g hg

end Work.PTCert.OrbitKeys
