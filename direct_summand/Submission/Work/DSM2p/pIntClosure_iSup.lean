import Mathlib
import Submission.Work.DSM2p.Basic

/-!
# `pIntClosure` commutes with directed suprema

The `p`-integral closure `pIntClosure p R` (CS §p-int-cl, see `Submission/Work/DSM2p/Basic.lean`)
is the smallest `p`-integrally closed subring containing `R`.  Here we record that it commutes
with suprema of *monotone* families of subrings indexed by a semilattice.

The inclusion `⨆ i, pIntClosure p (R i) ≤ pIntClosure p (⨆ i, R i)` is purity of `pIntClosure`
in `R`.  For the converse it suffices, by minimality of `pIntClosure`, to see that
`C = ⨆ i, pIntClosure p (R i)` is itself `p`-integrally closed; this uses that the family
`i ↦ pIntClosure p (R i)` is directed (because `R` is monotone and `ι` is a semilattice), so
that membership in the supremum is membership in one of the members.
-/

open scoped Classical

namespace Work.DSM2p

universe u

variable {S : Type u} [CommRing S]

/-- `pIntClosure` is monotone in its argument. -/
theorem pIntClosure_mono (p : ℕ) {R R' : Subring S} (h : R ≤ R') :
    pIntClosure p R ≤ pIntClosure p R' :=
  pIntClosure_le (h.trans (le_pIntClosure p R')) (pIntClosure_isPIntegrallyClosed p R')

theorem pIntClosure_iSup (p : ℕ) {S : Type u} [CommRing S] {ι : Type*} [Nonempty ι] [SemilatticeSup ι] (R : ι → Subring S) (hR : Monotone R) : pIntClosure p (⨆ i, R i) = ⨆ i, pIntClosure p (R i) := by
  have hmono : Monotone fun i => pIntClosure p (R i) := fun _ _ hij => pIntClosure_mono p (hR hij)
  have hdir : Directed (· ≤ ·) fun i => pIntClosure p (R i) :=
    fun i j => ⟨i ⊔ j, hmono le_sup_left, hmono le_sup_right⟩
  refine le_antisymm ?_ ?_
  · refine pIntClosure_le (iSup_le fun i => ?_) ?_
    · exact (le_pIntClosure p (R i)).trans (le_iSup (fun i => pIntClosure p (R i)) i)
    · intro x hx
      obtain ⟨i, hi⟩ := (Subring.mem_iSup_of_directed hdir).1 hx
      exact le_iSup (fun i => pIntClosure p (R i)) i
        (pIntClosure_isPIntegrallyClosed p (R i) x hi)
  · exact iSup_le fun i => pIntClosure_mono p (le_iSup R i)

end Work.DSM2p
