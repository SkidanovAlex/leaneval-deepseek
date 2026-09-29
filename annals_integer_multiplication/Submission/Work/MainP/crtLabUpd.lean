import Mathlib
import Submission.Work.MainP.crtLabDefs
import Submission.Work.MainP.crtTab_one_le
import Submission.Work.MainP.entryUpd_entry

/-!
# `crtLabUpd`: one step of the CRT label odometer

`canon ss i` is the state of the CRT label table at time `i`: entry `j` is the triple
`((i % sⱼ)·Pⱼ, Pⱼ, sⱼ·Pⱼ)` where `(sⱼ, Pⱼ) = (crtTab ss)ⱼ`.  The main loop of `crtLabWord` advances the
state by mapping every entry through `entryUpd`: `c ↦ c + P`, with a wrap to `0` when `c + P` reaches
the stored modulus `Q = sⱼ·Pⱼ`.  The loop also rebuilds the entry list by prepending, so the runtime
state `Est ss i` is `canon ss i` when `i` is even and `(canon ss i).reverse` when `i` is odd.

This file proves the two identities describing one step:
* `canon_succ`  : `canon ss (i+1) = (canon ss i).map entryUpd`;
* `Est_succ`    : `Est ss (i+1) = ((Est ss i).map entryUpd).reverse`;

and packages them as `crtLabUpd`.  The entrywise arithmetic (`entryUpd_entry`) and the positivity of the
table (`crtTab_one_le`, needed because `(r+1)·P = s·P` must force `r+1 = s`) are the two delegated
ingredients; everything below is the assembly.
-/

set_option autoImplicit false

namespace Work.MainP

/-- One odometer step, entrywise: the `j`-th entry of `canon ss i` updates to the `j`-th entry of
`canon ss (i+1)`. -/
theorem canon_succ (ss : List ℕ) (hpos : ∀ s ∈ ss, 1 ≤ s) (i : ℕ) :
    canon ss (i + 1) = (canon ss i).map entryUpd := by
  have hstep : ∀ sp ∈ crtTab ss,
      entryUpd (triple (((i % sp.1) * sp.2 : ℕ) : ℤ) (sp.2 : ℤ) ((sp.1 * sp.2 : ℕ) : ℤ))
        = triple ((((i + 1) % sp.1) * sp.2 : ℕ) : ℤ) (sp.2 : ℤ) ((sp.1 * sp.2 : ℕ) : ℤ) := by
    intro sp hsp
    obtain ⟨h1, h2⟩ := crtTab_one_le ss hpos sp hsp
    exact entryUpd_entry sp.1 sp.2 i h1 h2
  unfold canon
  rw [List.map_map]
  apply List.map_congr_left
  intro sp hsp
  exact (hstep sp hsp).symm

/-- The runtime state also advances by one `entryUpd` pass, followed by a reversal: at even times the
update pass leaves the list reversed, at odd times it restores it. -/
theorem Est_succ (ss : List ℕ) (hc : ∀ i, canon ss (i + 1) = (canon ss i).map entryUpd) (i : ℕ) :
    Est ss (i + 1) = ((Est ss i).map entryUpd).reverse := by
  by_cases hi : Even i
  · have hni : ¬ Even (i + 1) := fun h => (Nat.even_add_one.mp h) hi
    unfold Est
    rw [if_neg hni, if_pos hi, hc i]
  · have hni : Even (i + 1) := Nat.even_add_one.mpr hi
    unfold Est
    rw [if_pos hni, if_neg hi, hc i, List.map_reverse, List.reverse_reverse]

theorem crtLabUpd (ss : List ℕ) (hpos : ∀ s ∈ ss, 1 ≤ s) :
    (∀ i : ℕ, Work.MainP.canon ss (i + 1) = (Work.MainP.canon ss i).map Work.MainP.entryUpd) ∧
    (∀ i : ℕ, Work.MainP.Est ss (i + 1) = ((Work.MainP.Est ss i).map Work.MainP.entryUpd).reverse) :=
  ⟨fun i => canon_succ ss hpos i,
   fun i => Est_succ ss (fun j => canon_succ ss hpos j) i⟩

end Work.MainP
