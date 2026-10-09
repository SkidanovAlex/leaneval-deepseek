import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_mul_of_shortExact
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_eq_hOne_of_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Herbrand's lemma: invariance under a finite quotient

Milne, *Class Field Theory*, II.3.9: if `0 → A → B → C → 0` is a short exact sequence of
`ℤ[G]`-modules over a finite cyclic group `G` and `C` is finite, then the Herbrand quotients
of `A` and `B` agree, `h(A) = h(B)`.

In the multiplicative form used in `NK.GlobalCFTdeep` (`hZero M = |Ĥ⁰(G,M)|`,
`hOne M = |Ĥ¹(G,M)|`, `HerbrandEq M m` meaning `hZero M = m * hOne M`) this is the statement
that `HerbrandEq S.X₁ m ↔ HerbrandEq S.X₂ m`.

The proof combines the six-term exact hexagon
`natCard_tateCohomology_mul_of_shortExact`,

`|Ĥ⁰(X₂)| · |Ĥ¹(X₁)| · |Ĥ¹(X₃)| = |Ĥ⁰(X₁)| · |Ĥ⁰(X₃)| · |Ĥ¹(X₂)|`,

with Herbrand's lemma `hZero_eq_hOne_of_finite` for the finite module `X₃`,
`|Ĥ⁰(X₃)| = |Ĥ¹(X₃)|`, which lets the `X₃` terms cancel and reduces the hexagon to the
cross relation `|Ĥ⁰(X₂)| · |Ĥ¹(X₁)| = |Ĥ⁰(X₁)| · |Ĥ¹(X₂)|`.  Cancelling the (nonzero, both
groups being finite) factors `|Ĥ¹(X₁)|`, `|Ĥ¹(X₂)|` then converts this into the required
equivalence.
-/

namespace NK.GlobalCFTdeep.Herbrand

/-- Elementary arithmetic behind the cancellation.  If `b * a = c * d` with `a, d ≠ 0`, then
`c = m * a` and `b = m * d` are equivalent. -/
private lemma eq_mul_iff_eq_mul_of_mul_eq_mul {a b c d m : ℕ} (ha : 0 < a) (hd : 0 < d)
    (h : b * a = c * d) : c = m * a ↔ b = m * d := by
  constructor
  · intro hc
    apply Nat.mul_right_cancel ha
    rw [h, hc]
    ring
  · intro hb
    apply Nat.mul_right_cancel hd
    rw [← h, hb]
    ring

theorem herbrandEq_iff_of_finite_quotient {G : Type} [CommGroup G] [Fintype G] [IsCyclic G]
    (S : CategoryTheory.ShortComplex (Rep ℤ G)) (hS : S.ShortExact) [Finite S.X₃]
    [Finite ↥(tateCohomology S.X₁ 0)] [Finite ↥(tateCohomology S.X₁ 1)]
    [Finite ↥(tateCohomology S.X₂ 0)] [Finite ↥(tateCohomology S.X₂ 1)]
    [Finite ↥(tateCohomology S.X₃ 0)] [Finite ↥(tateCohomology S.X₃ 1)] (m : ℕ) :
    HerbrandEq S.X₁ m ↔ HerbrandEq S.X₂ m := by
  -- the six-term exact hexagon
  have hhex := natCard_tateCohomology_mul_of_shortExact S hS
  -- Herbrand's lemma for the finite module `X₃`
  have h3 : Nat.card ↥(tateCohomology S.X₃ 0) = Nat.card ↥(tateCohomology S.X₃ 1) :=
    hZero_eq_hOne_of_finite S.X₃
  have h31 : 0 < Nat.card ↥(tateCohomology S.X₃ 1) :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  -- cancel the `X₃` terms and reduce to the cross relation
  have hkey : Nat.card ↥(tateCohomology S.X₂ 0) * Nat.card ↥(tateCohomology S.X₁ 1)
      = Nat.card ↥(tateCohomology S.X₁ 0) * Nat.card ↥(tateCohomology S.X₂ 1) := by
    apply Nat.mul_right_cancel h31
    rw [hhex, h3]
    ring
  have h11 : 0 < Nat.card ↥(tateCohomology S.X₁ 1) :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  have h21 : 0 < Nat.card ↥(tateCohomology S.X₂ 1) :=
    Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
  simp only [HerbrandEq, hZero, hOne]
  exact eq_mul_iff_eq_mul_of_mul_eq_mul h11 h21 hkey

end NK.GlobalCFTdeep.Herbrand
