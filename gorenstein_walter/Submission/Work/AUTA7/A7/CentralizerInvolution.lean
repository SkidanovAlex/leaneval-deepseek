import Mathlib
import Submission.Work.A7.Defs
import Submission.Work.AUTA7.A7.EvenInvolutionCycleType
import Submission.Work.AUTA7.A7.OddElementInCentralizerInvolution
import Submission.Work.AUTA7.A7.CardInfMulTwoOfIndexTwo
import Submission.Work.AUTA7.A7.NatCardCentralizerSubtypeA7

namespace Work.AUTA7.A7

/-!
# The centralizer of an involution of `A₇` has order `24`

`|A₇| = 2520 = 8 · 315`.  We show that for every non-identity involution `z` of `A₇` the
centralizer `C_{A₇}(z)` has order `24`.

The argument is the one sketched in the original request:

* viewing `z` as a permutation of `Fin 7`, an even non-identity involution has cycle type `{2, 2}`
  (all its cycles have length dividing `2`, and the parity of the number of its `2`-cycles is its
  sign), so Mathlib's `Equiv.Perm.nat_card_centralizer` gives
  `|C_{S₇}(z)| = (7 - 4)! · (2 · 2) · 2! = 48`;
* `C_{S₇}(z)` contains an odd permutation, namely a transposition `Equiv.swap a (z a)` for any `a`
  moved by `z`, so `C_{S₇}(z) ⊓ A₇` has index `2` in `C_{S₇}(z)`, whence `|C_{S₇}(z) ⊓ A₇| = 24`;
* the centralizer of `z` inside `A₇` is (carries the same elements as) `C_{S₇}(z) ⊓ A₇`.
-/

open Equiv

/-- `Equiv.Perm.nat_card_centralizer` at cycle type `{2,2}`: the centralizer in `S₇` of a double
transposition has order `(7 - 4)! * (2 * 2) * 2! = 48`. -/
theorem nat_card_centralizer_doubleTransposition {Z : Equiv.Perm (Fin 7)}
    (hct : Z.cycleType = ({2, 2} : Multiset ℕ)) :
    Nat.card ↥(Subgroup.centralizer ({Z} : Set (Equiv.Perm (Fin 7)))) = 48 := by
  rw [Equiv.Perm.nat_card_centralizer, hct]
  norm_num

/-- **The centralizer of an involution of `A₇` has order `24`.** -/
theorem CentralizerInvolution {z : alternatingGroup (Fin 7)} (hz : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card (Subgroup.centralizer ({z} : Set (alternatingGroup (Fin 7)))) = 24 := by
  have hZZ : (z : Equiv.Perm (Fin 7)) * (z : Equiv.Perm (Fin 7)) = 1 := by
    have h := congrArg (fun x : alternatingGroup (Fin 7) => (x : Equiv.Perm (Fin 7))) hz
    simpa using h
  have hZ1 : (z : Equiv.Perm (Fin 7)) ≠ 1 := fun h => hz1 (Subtype.coe_injective h)
  have hsign : Equiv.Perm.sign (z : Equiv.Perm (Fin 7)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp z.2
  have hct : (z : Equiv.Perm (Fin 7)).cycleType = ({2, 2} : Multiset ℕ) :=
    EvenInvolutionCycleType hZZ hZ1 hsign
  have h48 : Nat.card ↥(Subgroup.centralizer
      ({(z : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) = 48 :=
    nat_card_centralizer_doubleTransposition hct
  obtain ⟨c, hc, hcsign⟩ := OddElementInCentralizerInvolution hZZ hZ1
  have hnotle : ¬ Subgroup.centralizer ({(z : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))
      ≤ alternatingGroup (Fin 7) := by
    intro hle
    have hmem : c ∈ alternatingGroup (Fin 7) := hle hc
    have h1 : Equiv.Perm.sign c = 1 := Equiv.Perm.mem_alternatingGroup.mp hmem
    rw [hcsign] at h1
    exact absurd h1 (by decide)
  have hkey : Nat.card ↥(Subgroup.centralizer
        ({(z : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))
        ⊓ alternatingGroup (Fin 7)) * 2 = 48 := by
    rw [CardInfMulTwoOfIndexTwo (alternatingGroup (Fin 7))
      (Subgroup.centralizer ({(z : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7))))
      (alternatingGroup.index_eq_two (α := Fin 7)) hnotle, h48]
  rw [NatCardCentralizerSubtypeA7 z]
  omega

end Work.AUTA7.A7
