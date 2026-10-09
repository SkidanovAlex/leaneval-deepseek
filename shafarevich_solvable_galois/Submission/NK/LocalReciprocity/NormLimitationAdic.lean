import Mathlib
import Submission.NK.LocalReciprocity.NormIndexAbelianization
import Submission.NK.LocalReciprocity.NormGroup
import Submission.NK.LocalReciprocity.MaxAbelianSetup
import Submission.NK.LocalReciprocity.commutator_gal_maxAbelianSubext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm limitation theorem for a Galois extension of a local field

Let `K` be a number field, `Q` a finite place of `K`, `F = Q.adicCompletion K` the corresponding
local field, `B / F` a finite extension and `E / B` a finite Galois extension.  Write
`A = B^{ab} = NK.LocalReciprocity.maxAbelianSubext B E` for the maximal abelian subextension
of `E / B` (the fixed field of the commutator subgroup of `Gal(E/B)`).

**The norm limitation theorem** (Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
(5.1.4) / the local norm limitation theorem of class field theory) says that the norm group of
`E / B` coincides with the norm group of its maximal abelian subextension:

  `N_{E/B} Eˣ = N_{B^{ab}/B} (B^{ab})ˣ`.

Both inclusions *are* content:

* `≤` is the transitivity of norms (the first class-formation axiom,
  `NK.LocalReciprocity.normGroup_le_of_tower`): `B^{ab} ⊆ E` so norms from `E` are norms from
  `B^{ab}`.
* `≥` is the arithmetic half: it is equivalent to the statement that the norm index
  `[Bˣ : N_{E/B} Eˣ]` equals `|Gal(E/B)^{ab}|`, i.e. to the *norm index theorem* in the
  non-abelian case.

The proof here is the standard index comparison.  The norm index theorem for a finite Galois
extension of a local field is `NK.LocalReciprocity.NormIndexAbelianization`

  `[Bˣ : N_{E/B} Eˣ] = |Abelianization (Gal(E/B))|`,

proved in the workspace from Tate's theorem, Hilbert 90 and the local fundamental class.  Applying
it both to `E/B` and to the *abelian* extension `B^{ab}/B` gives

  `[Bˣ : N_{E/B} Eˣ] = |Ab (Gal(E/B))|`,   `[Bˣ : N_{B^{ab}/B}(B^{ab})ˣ] = |Ab (Gal(B^{ab}/B))|`,

and the two right hand sides agree because

* `Gal(B^{ab}/B)` is abelian, so its abelianisation is itself
  (`NK.LocalReciprocity.commutator_gal_maxAbelianSubext`);
* restriction `Gal(E/B) → Gal(B^{ab}/B)` is surjective with kernel the commutator subgroup, so
  `Gal(B^{ab}/B) ≅ Gal(E/B)^{ab}` (`IsGalois.normalAutEquivQuotient`).

Two subgroups of a group, one contained in the other, with the same (finite) index are equal,
which gives the theorem.
-/

set_option linter.style.haveILetI false

namespace NK.LocalReciprocity

/-- **A subgroup of finite index that has the same index as a supergroup is that supergroup.**

(The finite-index hypothesis is supplied in the form `A.index ≠ 0`: with Mathlib's convention,
`Subgroup.index = 0` means *infinite* index.) -/
theorem eq_of_le_of_index_eq_of_index_ne_zero {G : Type*} [Group G] {A B : Subgroup G}
    (h : A ≤ B) (hne : A.index ≠ 0) (hidx : B.index = A.index) : A = B := by
  haveI : A.FiniteIndex := Subgroup.finiteIndex_iff.mpr hne
  by_contra hAB
  have hlt : B.index < A.index := Subgroup.index_strictAnti (lt_of_le_of_ne h hAB)
  rw [hidx] at hlt
  exact lt_irrefl _ hlt

theorem NormLimitationAdic
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type*} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E] :
    NK.LocalReciprocity.normGroup B E =
      NK.LocalReciprocity.normGroup B ↥(NK.LocalReciprocity.maxAbelianSubext B E) := by
  -- the abelianisation of `Gal(E/B)` is finite, `Gal(E/B)` being a finite group
  have hfiniteAbG : Finite (Abelianization (E ≃ₐ[B] E)) :=
    Finite.of_surjective Abelianization.of fun y => QuotientGroup.mk_surjective y
  -- the two abelianisations in play have the same cardinality:
  -- `Ab (Gal(B^{ab}/B)) = Gal(B^{ab}/B)` (the extension is abelian) and
  -- `Gal(B^{ab}/B) ≅ Gal(E/B) ⧸ commutator = Ab (Gal(E/B))` (restriction).
  have hcardA : Nat.card (Abelianization (↥(NK.LocalReciprocity.maxAbelianSubext B E) ≃ₐ[B]
        ↥(NK.LocalReciprocity.maxAbelianSubext B E)))
      = Nat.card (Abelianization (E ≃ₐ[B] E)) := by
    have hc : commutator (↥(NK.LocalReciprocity.maxAbelianSubext B E) ≃ₐ[B]
        ↥(NK.LocalReciprocity.maxAbelianSubext B E)) = ⊥ :=
      NK.LocalReciprocity.commutator_gal_maxAbelianSubext
    have h1 : Nat.card (Abelianization (↥(NK.LocalReciprocity.maxAbelianSubext B E) ≃ₐ[B]
        ↥(NK.LocalReciprocity.maxAbelianSubext B E)))
        = Nat.card (↥(NK.LocalReciprocity.maxAbelianSubext B E) ≃ₐ[B]
            ↥(NK.LocalReciprocity.maxAbelianSubext B E)) := by
      rw [Abelianization, hc]
      exact Nat.card_congr (QuotientGroup.quotientBot (G :=
        ↥(NK.LocalReciprocity.maxAbelianSubext B E) ≃ₐ[B]
          ↥(NK.LocalReciprocity.maxAbelianSubext B E))).toEquiv
    have h2 : Nat.card (↥(NK.LocalReciprocity.maxAbelianSubext B E) ≃ₐ[B]
        ↥(NK.LocalReciprocity.maxAbelianSubext B E))
        = Nat.card (Abelianization (E ≃ₐ[B] E)) :=
      (Nat.card_congr (IsGalois.normalAutEquivQuotient (K := B) (L := E)
        (H := commutator (E ≃ₐ[B] E))).toEquiv).symm
    exact h1.trans h2
  -- the norm index theorem at `E/B` and at `B^{ab}/B`
  have hE := NK.LocalReciprocity.NormIndexAbelianization (K := K) Q (B := B) (E := E)
  have hA := NK.LocalReciprocity.NormIndexAbelianization (K := K) Q (B := B)
      (E := ↥(NK.LocalReciprocity.maxAbelianSubext B E))
  -- the inclusion of norm groups, from the transitivity of norms
  have hle : NK.LocalReciprocity.normGroup B E ≤
      NK.LocalReciprocity.normGroup B ↥(NK.LocalReciprocity.maxAbelianSubext B E) :=
    NK.LocalReciprocity.normGroup_le_of_tower
  -- the equality of the two indices
  have hidx : (NK.LocalReciprocity.normGroup B
        ↥(NK.LocalReciprocity.maxAbelianSubext B E)).index
      = (NK.LocalReciprocity.normGroup B E).index := by
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    change Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B :
        ↥(NK.LocalReciprocity.maxAbelianSubext B E) →* B)))
      = Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B)))
    rw [hA, hE, hcardA]
  -- the index of the norm group of `E/B` is finite and non-zero
  have hne : (NK.LocalReciprocity.normGroup B E).index ≠ 0 := by
    rw [Subgroup.index_eq_card]
    change Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) ≠ 0
    rw [hE]
    exact Nat.card_ne_zero.mpr ⟨⟨Abelianization.of 1⟩, hfiniteAbG⟩
  exact eq_of_le_of_index_eq_of_index_ne_zero hle hne hidx

end NK.LocalReciprocity
