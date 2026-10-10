import Mathlib.FieldTheory.Galois.Basic
import Submission.NK.LocalReciprocityLubinTate.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm-subgroup correspondence (Hasse's *Normensatz* / Umkehrsatz)

This file isolates the **norm-subgroup correspondence** of local class field theory as a named
`Prop`, in the exact form in which the rest of the chapter consumes it.  It is the classical
theorem that the order-reversing map

`L ↦ N_{L/F} Lˣ`   (finite abelian extensions `L/F` inside `F^{ab}` ↦ subgroups of `Fˣ`)

is a *bijection onto its image*, i.e. that a norm group remembers its field:

> if `N_{L₁/F} L₁ˣ ≤ N_{L₂/F} L₂ˣ`, then `L₂ ≤ L₁`.

(Equivalently — with the always-valid converse `L₂ ≤ L₁ ⟹ N_{L₁} ≤ N_{L₂}`, which is transitivity
of the norm — the map `L ↦ N_{L/F} Lˣ` is an order-reversing *embedding* of the finite abelian
levels of `F^{ab}` into the subgroups of `Fˣ`.)

## Status and role of this statement

`NormCorrespondence F F'` is **not** the target of the chapter (`NK.LocalCFT.ArtinReciprocity`),
and it does not mention any Artin map: it is a statement about norm groups only.  It is a
*consequence* of the local reciprocity law — given `ArtinReciprocity`, it is proved in
`Submission/Work/LocalCFT/NormGroup/normGroup_le_iff.lean` as
`NK.LocalCFT.NormGroup.normGroup_le_iff` (and `NK.LocalArtin.normGroup_le_iff` re-exports it) —
and it is classically *equivalent* to the reciprocity law in the presence of the norm index theorem
and the existence theorem (both of which are **proved** in this chapter for `F = 𝔭.adicCompletion K`:
`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion` and
`NK.LocalReciprocityLubinTate.existenceTheorem_adicCompletion`).

It is the residue in terms of which the chapter's remaining classical content is organised, because
it is the single hypothesis under which the *canonical Artin map on the Lubin–Tate tower* extends
from the tower levels to *all* finite abelian levels (see
`NK.LocalReciprocityLubinTate.Unramified.cofinality_of_normCorrespondence` and
`NK.LocalReciprocityLubinTate.Unramified.TowerSymbol`): in Milne, *Class Field Theory*, §I.1.15
(the proof of the local Kronecker–Weber theorem) this is exactly the step "`Nm(Lˣ) ⊇ U_{n,m}`
implies `L ⊆ K_{n,m}`", and it is also Neukirch, *Algebraic Number Theory*, V.1.7/V.5.5 ("Der
Normensatz", Hasse's Umkehrsatz).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter V, §1 (the norm-subgroup correspondence) and
  §5 (the Lubin–Tate reciprocity law);
* J-P. Serre, *Local Fields*, Chapter XI §2 and Chapter XIII §3 (the axioms of a class formation,
  the second of which is this statement) and Chapter XV §5;
* J. S. Milne, *Class Field Theory*, §I.1 (Thm. 1.1, the reciprocity law) and §I.1.15.
-/

namespace NK.LocalReciprocityLubinTate

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The norm-subgroup correspondence** (Hasse's *Normensatz* / Umkehrsatz) for the Galois
extension `F' / F`: for finite abelian Galois levels `L₁, L₂ ≤ F^{ab}`, a containment of norm
groups forces the reverse containment of fields.

The commutative Galois group hypotheses `∀ σ τ, σ * τ = τ * σ` are carried explicitly (rather than
as type-class arguments) exactly as in `NK.LocalArtin.KernelCondition` and
`NK.LocalCFT.ReciprocityLaw`, so that the statement can be consumed by the same code. -/
def NormCorrespondence (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] : Prop :=
  ∀ (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L₁] [Normal F L₁] [FiniteDimensional F L₂] [Normal F L₂]
    (_ : ∀ σ τ : ↥L₁ ≃ₐ[F] ↥L₁, σ * τ = τ * σ)
    (_ : ∀ σ τ : ↥L₂ ≃ₐ[F] ↥L₂, σ * τ = τ * σ),
    NK.LocalReciprocity.normGroup F ↥L₁ ≤ NK.LocalReciprocity.normGroup F ↥L₂ → L₂ ≤ L₁

/-- The *unconditional* half of the correspondence: the norm group of a bigger field is smaller
(transitivity of the norm, `NK.LocalReciprocity.normGroup_le_of_tower`).  Recorded here so that
the two halves of `NormCorrespondence` live in one file. -/
theorem normGroup_le_of_level_le {L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F')}
    (h : L₂ ≤ L₁) :
    NK.LocalReciprocity.normGroup F ↥L₁ ≤ NK.LocalReciprocity.normGroup F ↥L₂ :=
  NK.LocalCFT.normGroup_le_of_le h

/-- **The correspondence from the reciprocity datum.**  The target of the chapter
(`NK.LocalCFT.ArtinReciprocity`) implies `NormCorrespondence`; this is the precise sense in which
`NormCorrespondence` is *weaker* than the target.  (It is
`NK.LocalCFT.NormGroup.normGroup_le_iff`, re-exported.) -/
theorem normCorrespondence_of_artinReciprocity
    (D : NK.LocalCFT.ArtinReciprocity F F') : NormCorrespondence F F' := by
  intro L₁ L₂ _ _ _ _ h₁ h₂ h
  exact (NK.LocalCFT.NormGroup.normGroup_le_iff D L₁ L₂ h₁ h₂).mp h

end NK.LocalReciprocityLubinTate
