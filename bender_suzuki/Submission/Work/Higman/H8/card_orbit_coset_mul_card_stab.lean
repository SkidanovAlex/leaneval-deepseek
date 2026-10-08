import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.H8

set_option linter.style.haveILetI false

/-- For an automorphism `f` of `P` that preserves a normal subgroup `A` (i.e. `A.map f = A`),
the induced homomorphism `P ⧸ A →* P ⧸ A` sending the coset of `y` to the coset of `f y`.
It is `QuotientGroup.lift A ((QuotientGroup.mk' A).comp f.toMonoidHom)` in the notation of the
statement below, packaged with `QuotientGroup.map`. -/
private noncomputable def quotientGroupMapOfInvariant {P : Type} [Group P] {A : Subgroup P}
    [A.Normal] (f : MulAut P) (hf : A.map (f : MulAut P).toMonoidHom = A) : P ⧸ A →* P ⧸ A :=
  QuotientGroup.map A A (f : MulAut P).toMonoidHom (Subgroup.map_le_iff_le_comap.mp hf.le)

private lemma quotientGroupMapOfInvariant_mk {P : Type} [Group P] {A : Subgroup P} [A.Normal]
    (f : MulAut P) (hf : A.map (f : MulAut P).toMonoidHom = A) (y : P) :
    quotientGroupMapOfInvariant f hf (QuotientGroup.mk y : P ⧸ A) = QuotientGroup.mk (f y) :=
  QuotientGroup.map_mk A A (f : MulAut P).toMonoidHom _ y

/-- **Orbit–stabiliser for the action of a subgroup `S ≤ MulAut P` on the coset space `P ⧸ A`.**

Let `P` be a finite group, `A ⊴ P` a normal subgroup, and `S ≤ MulAut P` a subgroup of
automorphisms each of which *preserves* `A` (`A.map g.toMonoidHom = A`).  Such automorphisms
descend to automorphisms of the quotient `P ⧸ A`, so `S` acts on `P ⧸ A` by
`g • (yA) = (g y)A`; consequently the orbit of the coset `xA` has `|S| / |Stab|` elements.

Proof route: use `QuotientGroup.lift A ((QuotientGroup.mk' A).comp (g : MulAut P).toMonoidHom)`
(well defined because `g` maps `A` into `A`) to get a monoid hom `P ⧸ A →* P ⧸ A` for each
`g : S`, assemble these into a `MulAction S (P ⧸ A)` instance with `g • mk y = mk (g y)`
(the two axioms are checked by `Quotient.inductionOn`), then apply
`Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S (QuotientGroup.mk x))` together with
`Nat.card_prod`.  Finally identify the two subtypes in the statement with the orbit and the
stabiliser: `w` lies in the orbit of `mk x` iff `w = mk (g x)` for some `g : S`, and
`g • mk x = mk x ↔ (g x) * x⁻¹ ∈ A` (using that `A` is normal, to move between
`(g x)⁻¹ * x ∈ A` and `(g x) * x⁻¹ ∈ A`). -/
theorem card_orbit_coset_mul_card_stab {P : Type} [Group P] [Finite P]
    {A : Subgroup P} [A.Normal] (S : Subgroup (MulAut P))
    (hS : ∀ g ∈ S, A.map (g : MulAut P).toMonoidHom = A) (x : P) :
    Nat.card {w : P ⧸ A // ∃ g : S, w = QuotientGroup.mk ((g : MulAut P) x)} *
      Nat.card {g : S // ((g : MulAut P) x) * x⁻¹ ∈ A} = Nat.card ↥S := by
  classical
  -- Each `g : S` acts on `P ⧸ A` by `g • mk y = mk (g y)`; assemble the `MulAction`.
  letI : MulAction S (P ⧸ A) :=
  { smul := fun g q => quotientGroupMapOfInvariant (g : MulAut P) (hS g g.2) q
    one_smul := fun q => by
      show quotientGroupMapOfInvariant ((1 : S) : MulAut P) (hS 1 (1 : S).2) q = q
      refine QuotientGroup.induction_on q fun y => ?_
      simp only [quotientGroupMapOfInvariant_mk]
      simp
    mul_smul := fun g h q => by
      show quotientGroupMapOfInvariant ((g * h : S) : MulAut P) (hS (g * h) (g * h).2) q =
        quotientGroupMapOfInvariant (g : MulAut P) (hS g g.2)
          (quotientGroupMapOfInvariant (h : MulAut P) (hS h h.2) q)
      refine QuotientGroup.induction_on q fun y => ?_
      simp only [quotientGroupMapOfInvariant_mk, Subgroup.coe_mul, MulAut.mul_apply] }
  have hsmul : ∀ (g : S) (y : P),
      g • (QuotientGroup.mk y : P ⧸ A) = QuotientGroup.mk ((g : MulAut P) y) := by
    intro g y
    show quotientGroupMapOfInvariant (g : MulAut P) (hS g g.2) (QuotientGroup.mk y) = _
    rw [quotientGroupMapOfInvariant_mk]
  -- The orbit of `mk x` is exactly the image set appearing in the statement.
  have horbit : ∀ w : P ⧸ A, w ∈ MulAction.orbit S (QuotientGroup.mk x : P ⧸ A) ↔
      ∃ g : S, w = QuotientGroup.mk ((g : MulAut P) x) := by
    intro w
    rw [MulAction.mem_orbit_iff]
    exact ⟨fun ⟨g, hg⟩ => ⟨g, hg.symm⟩, fun ⟨g, hg⟩ => ⟨g, by rw [hg, hsmul g x]⟩⟩
  -- The stabiliser of `mk x` is exactly the subtype appearing in the statement: the condition
  -- `mk (g x) = mk x` is `((g x) * x⁻¹) ∈ A` for the normal subgroup `A`.
  have hstab : ∀ g : S, g ∈ MulAction.stabilizer S (QuotientGroup.mk x : P ⧸ A) ↔
      ((g : MulAut P) x) * x⁻¹ ∈ A := by
    intro g
    rw [MulAction.mem_stabilizer_iff]
    rw [hsmul g x, QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
  have hcard_orbit : Nat.card {w : P ⧸ A // ∃ g : S, w = QuotientGroup.mk ((g : MulAut P) x)}
      = Nat.card ↥(MulAction.orbit S (QuotientGroup.mk x : P ⧸ A)) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun w => (horbit w).symm))
  have hcard_stab : Nat.card ↥(MulAction.stabilizer S (QuotientGroup.mk x : P ⧸ A))
      = Nat.card {g : S // ((g : MulAut P) x) * x⁻¹ ∈ A} :=
    Nat.card_congr (Equiv.subtypeEquivRight hstab)
  -- Orbit–stabiliser.
  have hos : Nat.card ↥(MulAction.orbit S (QuotientGroup.mk x : P ⧸ A)) *
      Nat.card ↥(MulAction.stabilizer S (QuotientGroup.mk x : P ⧸ A)) = Nat.card ↥S := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S (QuotientGroup.mk x : P ⧸ A))
  rw [hcard_orbit, ← hcard_stab]
  exact hos

end Work.Higman.H8
