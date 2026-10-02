import Mathlib
import Submission.Work.RatHurewicz.Excision

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Homotopy excision: the vocabulary of the Puppe argument

This module fixes the vocabulary in which the proof of `Work.RatHurewicz.HomotopyExcision`
(`Submission/Work/RatHurewicz/Excision.lean`) is carried out: the *comparison map* of the triad
`(X; B, C)` and the *compression property* of a pair, which is the form of the classical
synonym for the vanishing of the relative homotopy groups (tom Dieck, *Algebraic Topology*,
Proposition 6.7.5: the four equivalent definitions of `n`-connectedness of a pair).

## The classical route (Puppe's elementary proof, tom Dieck §6.9)

For `X = B ∪ C` with `B, C` open and `x₀ ∈ B ∩ C`, write `F_B = {(a,γ) : a ∈ B∩C, γ ⊆ B}` and
`F = {(a,γ) : a ∈ C, γ ⊆ X}` (the homotopy fibres of `B∩C ↪ B` and of `C ↪ X`), so that the map
`excisionComparison B C x₀ : F_B → F` of this file induces the excision map on homotopy groups.

* Step 1 (compression of the pieces).  The hypothesis `π_k(F_B) = 0` for `k ≤ p` is, by
  Proposition 6.7.5, equivalent to the *compression property* `CompressRel ↥B (↥(B∩C)) d` for all
  `d ≤ p+1`: every map of pairs `(Iᵈ, ∂Iᵈ) → (B, B∩C)` is homotopic relative to the boundary into
  `B∩C`.  (Same for `C` and `q`.)
* Step 2 (Puppe's preparation theorem, tom Dieck 6.9.2).  Subdivide `Iⁿ` by the Lebesgue lemma
  into small cubes each mapped into `B` or `C`; pushing the boxes one at a time in increasing
  dimension (using the compression properties for boxes of dimension `≤ p+1`, resp. `≤ q+1`, and
  the "K/G" trick of Lemma 6.9.1 for the higher-dimensional ones) puts the map into a normal form.
* Step 3 (the dimension count, tom Dieck 6.9.3).  In the normal form the two "bad" sets have
  `≥ p+1` respectively `≥ q+1` distinguished coordinates, so they are disjoint in `Iⁿ` as soon as
  `n ≤ p+q`; a Urysohn function then produces a homotopy of the map into `B`, i.e. the compression
  of the pair `(F, F_B)` at all levels `≤ p+q+1`.
* Step 4.  By Proposition 6.7.5 again, the compression of `(F, F_B)` at levels `≤ p+q+1` is the
  vanishing of the relative groups `π_m(F, F_B)` for `m ≤ p+q+1`, and the long exact sequence of
  the pair (`Work.RatHurewicz.pair_les` applied to `excisionComparison B C x₀`) gives that the
  comparison map is an isomorphism on `π_k` for `k ≤ p+q`.
-/

set_option linter.unusedVariables false

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- The standard `n`-cube, `Iⁿ = (Fin n → [0,1])`. -/
abbrev ICube (n : ℕ) : Type := Fin n → unitInterval

/-- **The compression property of the pair `(Y, A)` in dimension `d`**: every map of pairs
`(Iᵈ, ∂Iᵈ) → (Y, A)` is homotopic to a map into `A`, relative to the boundary.

By tom Dieck, *Algebraic Topology*, Proposition 6.7.5, this is equivalent to the vanishing of the
relative homotopy groups `π_q(Y,A,·)` for `q ≤ d` and to the connectivity statements for the
inclusion `A ↪ Y`. -/
def CompressRel (Y : Type) [TopologicalSpace Y] (A : Set Y) (d : ℕ) : Prop :=
  ∀ f : C(ICube d, Y), (∀ x, x ∈ Cube.boundary (Fin d) → f x ∈ A) →
    ∃ G : C(ICube d × I, Y),
      (∀ x, G (x, 0) = f x) ∧
      (∀ x (hx : x ∈ Cube.boundary (Fin d)) t, G (x, t) = f x) ∧
      (∀ x, G (x, 1) ∈ A)

/-- **The comparison map of the triad `(X; B, C)`**: the canonical map of homotopy fibres
`F_B → F` induced by the square of inclusions `(B∩C ↪ B)` and `(C ↪ X)`.  It is the map whose
effect on homotopy groups is `Work.RatHurewicz.excisionMap`. -/
noncomputable def excisionComparison {X : Type} [TopologicalSpace X] (B C : Set X)
    (x₀ : ↥(B ∩ C)) :
    C(homotopyFibre (interInclLeft B C) x₀, homotopyFibre (setIncl C) ⟨x₀.1, x₀.2.2⟩) :=
  homotopyFibreMap (interInclLeft B C) (setIncl C) (setIncl B) (interInclRight B C)
    (excision_square B C) x₀

end

end Work.RatHurewicz
