/-
# Localising the lattice translates of a function supported in a small ball

Given `f : (Fin n → ℝ) → ℝ` whose support is contained in the ball of radius `R ≤ 1/2`, the
periodisation `z ↦ ∑' m : Fin n → ℤ, f (z + m)` is, in a neighbourhood of any point `z`, a sum of
only `2^n` translates of `f` (`Work.Diff.STE.B3.perRbox z`): if `z' ∈ ball z (1/2)` and
`f (z' + m) ≠ 0`, then each coordinate of `m` is one of the two integers determined by the floor of
the corresponding coordinate of `z`.

This file contains the definitions and the two elementary lemmas used by the proof of
`Work.Diff.STE.B3.perR_jet_bound`; the localisation lemma itself is
`Work.Diff.STE.B3.perRbox_local`.
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- The point of the integer lattice `ℤⁿ` inside `ℝⁿ`. -/
def perRlattice {n : ℕ} (m : Fin n → ℤ) : Fin n → ℝ := fun i => (m i : ℝ)

/-- The (finite) set of lattice points that can contribute to the periodisation of a function
supported in the ball of radius `1/2`, in a neighbourhood of the point `z`. -/
noncomputable def perRbox {n : ℕ} (z : Fin n → ℝ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun i => Finset.Icc (-Int.floor (z i) - 1) (-Int.floor (z i))

/-- The localisation box has `2^n` elements. -/
lemma perRbox_card {n : ℕ} (z : Fin n → ℝ) : (perRbox z).card = 2 ^ n := by
  rw [perRbox, Fintype.card_piFinset]
  simp [Int.card_Icc]

/-- Membership in the localisation box, coordinatewise. -/
lemma perRbox_mem {n : ℕ} {z : Fin n → ℝ} {m : Fin n → ℤ} :
    m ∈ perRbox z ↔ ∀ i, -Int.floor (z i) - 1 ≤ m i ∧ m i ≤ -Int.floor (z i) := by
  rw [perRbox, Fintype.mem_piFinset]
  constructor
  · intro h i
    have h' := h i
    rw [Finset.mem_Icc] at h'
    omega
  · intro h i
    have h' := h i
    rw [Finset.mem_Icc]
    omega

end Work.Diff.STE.B3
