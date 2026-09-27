import Mathlib
import Submission.Work.Drive.Surf.Model
import Submission.Work.Surf.chordMeetAll_parity
import Submission.Work.Surf.chord_parity

/-!
# `(SURF)` in the form the chain route uses: the pairing with an essential loop

`Submission/Work/Surf/chordMeetAll_parity` gives the *family* form of the mod-2 intersection number of
two systems of chords: if every pair `(A i, B j)` crosses oddly then
`Odd (chordMeetAll A B).ncard ↔ Odd (#ι * #κ)`.  Here we record the form of `(SURF)` actually used by
Hugelmeyer's Lemmas 3–4 on a capped plane `P ≅ ℝP²`: with `γ` an **essential** loop of `P` (in the
disk model, a system of an *odd* number of chords — the loop is essential exactly when it crosses the
projective line `L` oddly, `Model.lean`), the intersection number of two 1-chains is the product of
their two pairings with `γ`:

`#(A ⋔ B)` is odd exactly when both `#(A ⋔ γ)` and `#(B ⋔ γ)` are odd, i.e.
`#(A ⋔ B) ≡ #(A ⋔ γ) · #(B ⋔ γ)  (mod 2)`.

This is a corollary of the family form applied to the three families `A, B`, `A, γ` and `B, γ`: the
pairing with `γ` is odd exactly when the number of chords of the family is odd (because `#γ` is odd),
and the parities of the three totals reflect the products of the chord numbers.

The hypothesis `hodd` (oddness of every pair) is the base case `chord_crossing_parity` of the
chapter, which is *proved* in `Submission/Work/Surf/chord_crossing_parity.lean`; the consumer that
discharges it can import `Submission.Work.Drive.Surf.ChainFormChords`, which repeats the statement in
unconditional form.  The conditional form is kept here, in a module whose import closure contains
neither `Submission.Work.Drive.winding_eq_crossing_sum` nor `Submission.Work.Drive.even_winding`
(the three duplicate declarations of `Work.Drive.toC` make the three import closures mutually
incompatible: see `TO_C_CLASH.md`).
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- **`(SURF)` with an essential loop.**  For finite systems of chords `A`, `B` and an essential loop
`γ` given by a system of an *odd* number of chords, all pairs of which cross oddly, the intersection
number of `A` and `B` is the product of the two pairings with `γ`. -/
theorem surf_intersection_form {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (γ : ν → ℝ → EuclideanSpace ℝ (Fin 2))
    (hAB : ∀ i j, Odd (chordMeet (A i) (B j)).ncard)
    (hAγ : ∀ i l, Odd (chordMeet (A i) (γ l)).ncard)
    (hBγ : ∀ j l, Odd (chordMeet (B j) (γ l)).ncard)
    (hγ : Odd (Fintype.card ν)) :
    Odd (chordMeetAll A B).ncard ↔
      (Odd (chordMeetAll A γ).ncard ∧ Odd (chordMeetAll B γ).ncard) := by
  rw [Work.Surf.chordMeetAll_parity A B hAB, Work.Surf.chordMeetAll_parity A γ hAγ,
    Work.Surf.chordMeetAll_parity B γ hBγ, Nat.odd_mul, Nat.odd_mul, Nat.odd_mul]
  constructor
  · rintro ⟨hι, hκ⟩
    exact ⟨⟨hι, hγ⟩, hκ, hγ⟩
  · rintro ⟨⟨hι, -⟩, hκ, -⟩
    exact ⟨hι, hκ⟩


/-- **`(SURF)` with the *cut line* as the essential loop.**  For two finite systems of chords `A`, `B`
all of whose pairs cross oddly (`Work.Surf.chordMeetAll_parity`), the intersection number of `A` and `B`
is the product of the two **pairings with the projective line `L`** — and the pairing with `L` is the
*number of arcs*, i.e. the number of chords, by `Work.Drive.ncard_chainMeetsLine`:

`#(A ⋔ B)` is odd exactly when both `#(A ⋔ L)` and `#(B ⋔ L)` are odd.

This is the form in which the chain route consumes `(SURF)`: the cut of the capped plane `P ≅ ℝP²` is
the essential loop `C_0` (a projective line), and the "side" function of Hugelmeyer's order is
`b v = #(C_0 ⋔ A_v) = ⟨A_v, L⟩ = ` the number of arcs of `A_v` (mod `2`) — see
`SWEEP_TRANSPORT_NOTES.md` §3. -/
theorem surf_intersection_form_line {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l)
    (hAB : ∀ i j, Odd (chordMeet (A i) (B j)).ncard) :
    Odd (chordMeetAll A B).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) := by
  rw [Work.Surf.chordMeetAll_parity A B hAB, Nat.odd_mul,
    ncard_chainMeetsLine A hA, ncard_chainMeetsLine B hB]


/-! ## The unconditional form from `Work.Surf.chord_parity`

`Work.Surf.chord_parity` is the base case of the chapter under the *family-transversality* hypothesis
(the straightening family of the first chord against the second is transverse at every stage), which is
exactly the hypothesis the box-parity engine consumes and which the generically built chains of the
chain route satisfy.  Unlike `Work.Surf.chord_crossing_parity` its import closure is compatible with
`CappingSpace` (see `TO_C_CLASH.md`), so it is the base case the assembly should use. -/

/-- **The position of a pair of chords in which the base case applies.**  Both are chords
(`Work.Drive.IsChord`), both are `C^∞`, every crossing is strictly inside the disk, and the
straightening family `τ ↦ (1-τ) • a + τ • (cos (π ·) • a 0)` of `a` is transverse to `b` at every
stage (this is the hypothesis of `Work.Surf.chord_parity`). -/
def ChordPair (a b : ℝ → EuclideanSpace ℝ (Fin 2)) : Prop :=
  IsChord a ∧ IsChord b ∧ ContDiff ℝ Ctop a ∧ ContDiff ℝ Ctop b ∧
    (∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0 : ℝ) 1 ∧ t ∈ Set.Ioo (0 : ℝ) 1) ∧
    (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ s t : ℝ, s ∈ Set.Ioo (0 : ℝ) 1 → t ∈ Set.Ioo (0 : ℝ) 1 →
      (1 - τ) • a s + τ • (Real.cos (Real.pi * s) • a 0) = b t →
      det2 ((1 - τ) • deriv a s - τ • ((Real.pi * Real.sin (Real.pi * s)) • a 0))
        (deriv b t) ≠ 0)

/-- **Two chords in general position cross an odd number of times** (`Work.Surf.chord_parity`). -/
theorem odd_ncard_chordMeet_of_pair {a b : ℝ → EuclideanSpace ℝ (Fin 2)} (h : ChordPair a b) :
    Odd (chordMeet a b).ncard :=
  Work.Surf.chord_parity a b h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

/-- **`(SURF)` with the cut line, in unconditional form, from the family-transversality base case.**
For two finite systems of chords `A`, `B` whose pairs are all in the position `Work.Drive.ChordPair`
and whose endpoints are pairwise distinct modulo the antipodal map, the intersection number of `A` and
`B` is the product of the two pairings with the projective line:
`Odd #(A ⋔ B) ↔ Odd #(A ⋔ L) ∧ Odd #(B ⋔ L)`. -/
theorem surf_intersection_form_line_family {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → ℝ → EuclideanSpace ℝ (Fin 2)) (B : κ → ℝ → EuclideanSpace ℝ (Fin 2))
    (hpair : ∀ i j, ChordPair (A i) (B j))
    (hA : ∀ i k : ι, A i 0 = A k 0 ∨ A i 0 = antipode (A k 0) → i = k)
    (hB : ∀ j l : κ, B j 0 = B l 0 ∨ B j 0 = antipode (B l 0) → j = l) :
    Odd (chordMeetAll A B).ncard ↔
      (Odd (chainMeetsLine A).ncard ∧ Odd (chainMeetsLine B).ncard) :=
  surf_intersection_form_line A B hA hB fun i j => odd_ncard_chordMeet_of_pair (hpair i j)

end

end Work.Drive
