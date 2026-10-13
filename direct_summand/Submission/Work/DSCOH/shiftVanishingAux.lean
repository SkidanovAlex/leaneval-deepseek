/-
Area DSCOH — exactness of the chart Čech complex of the shifted free module `S(-d)`.

This file contains the assembly of the vanishing theorem `Work.DSCOH.chartCech_shift_vanishing`
from the pieces proved in parallel elsewhere:

* `Work.DSCOH.locAt_monomial_basis`: the chart localizations have an explicit monomial `A`-basis,
  the structure maps `resAt` act as the identity on exponents, and the degree-zero parts
  `degZero (shift d) S` consist of the exponents of total degree `-d`;
* `Work.DSCOH.simplex_cech_lift_Z`: the simplex acyclicity, giving for every Laurent exponent `β`
  a linear way of solving the piece of the Čech complex attached to `β`;
* `Work.DSCOH.cycle_piece_conditions`: the cycle conditions of a Čech cocycle, read in the
  monomial coordinates of every piece;
* `Work.DSCOH.exists_boundary_of_coeffs`: a finitely supported family of chart coordinates is
  realised by an element of the Čech term, with the coordinates of its differential;
* `Work.DSCOH.chartCech_exact_isZero_homology`: exactness of the complex in one degree gives the
  vanishing of the homology there.

The main statement here is the exactness `range (cechDiff q) = ker (cechDiff (q+1))` of the chart
Čech complex of `S(-d)` in the middle degrees — Serre's/Bott's vanishing for the free case.
-/
import Mathlib
import Submission.Work.DSCOH.coordToolkit
import Submission.Work.DSCOH.Cech
import Submission.Work.DSCOH.Chart
import Submission.Work.DSCOH.shift_gradedSMul

open Module MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ} {d : ℕ}

/-- The charts on which the `β`-piece of a Čech cochain at level `q + 1` lives: the charts of
cardinality `q + 2` containing `Z(β)`. -/
abbrev pieceChart (β : Fin n → ℤ) (q : ℕ) :=
  {U : Finset (Fin n) // Zset β ⊆ U ∧ U.card = q + 2}

/-- The solution indices of the `β`-piece: the charts of the boundary at level `q`, i.e. the
charts `U` of cardinality `q + 1` containing `Z(β)`. -/
abbrev pieceSol (β : Fin n → ℤ) (q : ℕ) :=
  {U : Finset (Fin n) // Zset β ⊆ U ∧ U.card + 1 = q + 2}

variable (B : (S : Finset (Fin n)) →
    Module.Basis {β : Fin n → ℤ // ∀ i, i ∉ S → 0 ≤ β i} A (locAt (A := A) (M := Poly A n) S))

/-- The coordinate family of the `β`-piece of a Čech cochain at chart level `q`: the
`β`-coordinates of the components of `a` at the charts of cardinality `q` containing `Z(β)`. -/
noncomputable def pieceData {q : ℕ}
    (a : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q)
    (β : Fin n → ℤ) : {S : Finset (Fin n) // Zset β ⊆ S ∧ S.card = q + 1} → A :=
  fun S => ((B S.1).repr (cechCoeff a S.1 S.2.2))
    ⟨β, (Zset_subset_iff S.1 β).mp S.2.1⟩

/-- The finite set of Laurent exponents that can occur in the coordinates of a fixed Čech
cochain: the union of the supports of its chart coordinates. -/
noncomputable def pieceSupport {q : ℕ}
    (a : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q) :
    Finset (Fin n → ℤ) :=
  Finset.univ.biUnion fun S : {S : Finset (Fin n) // S.card = q + 1} =>
    (((B S.1).repr (cechCoeff a S.1 S.2)).support.image
      (fun b => b.1))

lemma mem_pieceSupport {q : ℕ}
    (a : CechTerm (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d) q)
    {β : Fin n → ℤ} :
    β ∈ pieceSupport B a ↔
      ∃ (S : {S : Finset (Fin n) // S.card = q + 1})
        (hβ : ∀ i, i ∉ S.1 → 0 ≤ β i),
        ((B S.1).repr (cechCoeff a S.1 S.2)) ⟨β, hβ⟩ ≠ 0 := by
  classical
  simp only [pieceSupport, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨S, b, hb, hbeq⟩
    refine ⟨S, fun i hi => ?_, ?_⟩
    · rw [← hbeq]
      exact b.2 i hi
    · rw [show (⟨β, fun i hi => by rw [← hbeq]; exact b.2 i hi⟩ :
          {β : Fin n → ℤ // ∀ i, i ∉ S.1 → 0 ≤ β i}) = b from
        Subtype.ext hbeq.symm]
      exact Finsupp.mem_support_iff.mp hb
  · rintro ⟨S, hβ, hne⟩
    exact ⟨S, ⟨β, hβ⟩, Finsupp.mem_support_iff.mpr hne, rfl⟩

end Work.DSCOH
