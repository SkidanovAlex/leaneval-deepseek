import Mathlib.RepresentationTheory.Invariants

/-!
# Descending an `S`-invariant function to the quotient

Let `S ◁ G` be a normal subgroup of a group `G` and `A` a `k`-linear representation of `G`.
Suppose `z : G × G → A` is
* invariant under right multiplication by `S` in the first argument (`h1`),
* invariant under right multiplication by `S` in the second argument (`h2`), and
* takes values in the `S`-invariants of `A` (`h3`).

Then `z` factors through the quotient `G ⧸ S` as a function `(G ⧸ S) × (G ⧸ S) → A^S`.

This is the standard well-definedness/descent step used when comparing cocycles on `G` with
cocycles on `G ⧸ S` with values in the invariants `A^S` (cf. the inflation–restriction
five-term sequence and CoNF XII, proof of (12.2.1)).
-/

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory Representation

variable {k : Type} [CommRing k] {G : Type} [Group G]

lemma descent_to_quotient_of_invariant (S : Subgroup G) [S.Normal] (A : Rep k G) (z : G × G → A)
    (h1 : ∀ (g h : G) (s : S), z (g * s.1, h) = z (g, h))
    (h2 : ∀ (g h : G) (s : S), z (g, h * s.1) = z (g, h))
    (h3 : ∀ (g h : G) (s : S), A.ρ s.1 (z (g, h)) = z (g, h)) :
    ∃ Z : (G ⧸ S) × (G ⧸ S) → (Rep.res S.subtype A).ρ.invariants,
      ∀ g h : G, (Z (QuotientGroup.mk' S g, QuotientGroup.mk' S h) : A) = z (g, h) := by
  -- The `S`-invariant lift of `z` to the invariants of `A`.
  let F : G → G → (Rep.res S.subtype A).ρ.invariants :=
    fun g h => ⟨z (g, h), fun s => h3 g h s⟩
  -- `F` is compatible with the left-coset relation in both arguments.
  have hF : ∀ (a₁ a₂ b₁ b₂ : G), (QuotientGroup.leftRel S) a₁ b₁ → (QuotientGroup.leftRel S) a₂ b₂ →
      F a₁ a₂ = F b₁ b₂ := by
    intro a₁ a₂ b₁ b₂ hb₁ hb₂
    rw [QuotientGroup.leftRel_apply] at hb₁ hb₂
    have key : z (a₁ * (a₁⁻¹ * b₁), a₂ * (a₂⁻¹ * b₂)) = z (a₁, a₂) := by
      rw [h1 a₁ (a₂ * (a₂⁻¹ * b₂)) ⟨a₁⁻¹ * b₁, hb₁⟩, h2 a₁ a₂ ⟨a₂⁻¹ * b₂, hb₂⟩]
    refine Subtype.ext ?_
    show z (a₁, a₂) = z (b₁, b₂)
    have e₁ : b₁ = a₁ * (a₁⁻¹ * b₁) := by group
    have e₂ : b₂ = a₂ * (a₂⁻¹ * b₂) := by group
    rw [e₁, e₂]
    exact key.symm
  refine ⟨fun p => Quotient.lift₂ F hF p.1 p.2, ?_⟩
  intro g h
  exact congrArg (fun x : (Rep.res S.subtype A).ρ.invariants => (x : A))
    (Quotient.lift₂_mk F hF g h)

end Commons.RepresentationTheory.GroupCohomology