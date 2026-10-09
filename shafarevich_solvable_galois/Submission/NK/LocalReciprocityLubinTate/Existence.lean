import Submission.NK.LocalReciprocityLubinTate.Target
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Lubin–Tate existence theorem, bundled, and the resulting boundary theorems

The boundary theorem `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` takes the
Lubin–Tate tower together with the two properties of its unit filtration as explicit hypotheses.
This file bundles them into the single named classical statement

`NK.LocalReciprocityLubinTate.LubinTateExistence F F'`:

there is a uniformiser `π` and a decreasing, cofinal filtration `U` of `Fˣ` for which the
Lubin–Tate tower exists, i.e. the levels `E_{m,n} = F^{ur}_{m+1} · F(π_{n+1})` are finite abelian
extensions of `F` with norm groups `N_{E_{m,n}/F}E_{m,n}ˣ = ⟨π^{m+1}⟩ · U^{n+1}`.  (The local
Kronecker–Weber theorem — that these levels *exhaust* `F^{ab}` — is **not** part of this statement any
more: it was the field `exhaust` of `LubinTateTower` up to §16.2, and no theorem of the chapter
consumes it.  See `README.md` §16.2.  For `F = 𝔭.adicCompletion K` this whole structure is a
*theorem* from Honda's reciprocity law alone,
`NK.LocalReciprocityLubinTate.Unramified.nonempty_lubinTateTower_adicCompletion`.)

This is *one* classical theorem — Serre, *Local Fields*, Ch. XV §3–§5 (equivalently Milne, *Class
Field Theory*, §I.1–I.4: the existence of the Lubin–Tate formal group, the description of its
division points, the explicit reciprocity law and the local Kronecker–Weber theorem), for the
filtration `U^n = 1 + 𝔪^n` of the higher principal units.  It is strictly weaker than the target
`NK.LocalCFT.ArtinReciprocity F F'`: it says nothing about the Artin map.

The consequences are then proved in this chapter:

* `NK.LocalCFT.ExistenceTheorem F F'` (`existenceTheorem_of_lubinTateExistence`);
* `Nonempty (NK.LocalCFT.ArtinReciprocity F F')` from the norm residue symbol with the correct
  kernels and the norm index theorem (`nonempty_artinReciprocity_of_lubinTateExistence`), and — for
  `F = 𝔭.adicCompletion K` — with the norm index theorem *discharged*
  (`nonempty_artinReciprocity_adicCompletion`).

## Main definitions and results

* `NK.LocalReciprocityLubinTate.LubinTateExistence`;
* `NK.LocalReciprocityLubinTate.existenceTheorem_of_lubinTateExistence`;
* `NK.LocalReciprocityLubinTate.nonempty_artinReciprocity_of_lubinTateExistence`;
* `NK.LocalReciprocityLubinTate.nonempty_artinReciprocity_adicCompletion`.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u v

noncomputable section

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The Lubin–Tate existence theorem** (Serre, *Local Fields*, Ch. XV §3–§5; Milne, *Class Field
Theory*, §I.1–I.4), in the form consumed by this chapter: there is a uniformiser `π` of `F`, a
decreasing filtration `U` of `Fˣ` which is cofinal among its finite-index subgroups, and a
Lubin–Tate tower with norm groups `⟨π^{m+1}⟩ · U^{n+1}` exhausting `F^{ab}`.

For `F` a `p`-adic field one takes `U^n = 1 + 𝔪[F]^n` (the higher principal units, for a complete
discretely valued `F`), `q = #𝓀[F]`, and `π` any uniformiser. -/
def LubinTateExistence (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] : Prop :=
  ∃ (π : Fˣ) (U : ℕ → Subgroup Fˣ) (q : ℕ),
    Nonempty (LubinTateTower F F' π U q) ∧ Antitone U ∧
      (∀ M : Subgroup Fˣ, M.FiniteIndex → ∃ n, U n ≤ M)

/-- **The existence theorem of local class field theory from the Lubin–Tate existence theorem.** -/
theorem existenceTheorem_of_lubinTateExistence (h : LubinTateExistence F F') :
    NK.LocalCFT.ExistenceTheorem F F' := by
  obtain ⟨π, U, q, ⟨T⟩, hUanti, hU⟩ := h
  exact existenceTheorem_of_tower T hUanti hU

/-- **The Artin reciprocity datum from the Lubin–Tate existence theorem.**  Together with the norm
residue symbol with the correct kernels (`NK.LocalArtin.KernelCondition`) and the norm index
theorem, the Lubin–Tate existence theorem gives `Nonempty (NK.LocalCFT.ArtinReciprocity F F')`.
The norm index theorem is discharged for `F = 𝔭.adicCompletion K` by
`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`. -/
theorem nonempty_artinReciprocity_of_lubinTateExistence (h : LubinTateExistence F F')
    (hK : NK.LocalArtin.KernelCondition F F') (hN : NK.LocalArtin.NormIndex F F') :
    Nonempty (NK.LocalCFT.ArtinReciprocity F F') := by
  obtain ⟨π, U, q, ⟨T⟩, hUanti, hU⟩ := h
  exact nonempty_artinReciprocity_of_lubinTate T hUanti hU hK hN

/-- **The boundary theorem for a `p`-adic field, in the bundled form**: for a number field `K` and a
finite prime `𝔭`, the Lubin–Tate existence theorem for `F = 𝔭.adicCompletion K` together with the
norm residue symbol with the correct kernels gives the canonical local Artin reciprocity datum.  The
norm index theorem is *proved* here
(`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`), so it is no longer a
hypothesis. -/
theorem nonempty_artinReciprocity_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : LubinTateExistence (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K)))
    (hK : NK.LocalArtin.KernelCondition (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) :
    Nonempty (NK.LocalCFT.ArtinReciprocity (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) :=
  nonempty_artinReciprocity_of_lubinTateExistence h hK (NormIndex.normIndex_adicCompletion Q)

/-- **The infinite-level reciprocity isomorphism from the Lubin–Tate existence theorem**:
`Fˣ^{∧} ≃* Gal(F^{ab}/F)`, the form in which the downstream developments consume local class field
theory.  This is `NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion` composed with the datum
produced by `nonempty_artinReciprocity_of_lubinTateExistence`. -/
theorem exists_mulEquiv_completionUnits_of_lubinTateExistence (h : LubinTateExistence F F')
    (hK : NK.LocalArtin.KernelCondition F F') (hN : NK.LocalArtin.NormIndex F F') :
    Nonempty (NK.LocalReciprocity.completionUnits F ≃* NK.LocalCFT.AbGal F F') :=
  (nonempty_artinReciprocity_of_lubinTateExistence h hK hN).map
    fun D => Classical.choice (NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion D)

end

end NK.LocalReciprocityLubinTate
