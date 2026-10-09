import Submission.NK.LocalReciprocityLubinTate.Reciprocity
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_lubinTateTower_adicCompletion
import Submission.NK.LocalReciprocityLubinTate.Unramified.hondaReciprocity
import Submission.NK.LocalReciprocityLubinTate.Unramified.exists_isUniformizer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local reciprocity datum for a `p`-adic field: the boundary theorem

This file states the theorem that the consumer (`Submission/Work/LocalCFT/Basic.lean`, and through it
the Neukirch–Uchida development) imports:

```
NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion
  : Nonempty (NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) (SeparableClosure (𝔭.adicCompletion K)))
```

for every number field `K` and every finite prime `𝔭`, given **two named classical theorems**:

* `NK.LocalReciprocityLubinTate.HondaReciprocity F π (higherUnits F) (residueCard F)` — Honda's
  explicit reciprocity law `N_{F(Λ_n)/F} F(Λ_n)ˣ = ⟨π⟩ · U^n` for the Lubin–Tate levels
  (Serre, *Local Fields*, Ch. XV §5.2; Neukirch, *Algebraic Number Theory*, V.5.5);
* `NK.LocalArtin.KernelCondition F F'` — the existence of the norm residue symbol
  `Fˣ →* Gal(F^{ab}/F)` with the correct finite-level kernels (the fundamental class of the local
  class formation `(G_F, F̄ˣ)`).

Everything else is **proved** in this chapter and its siblings:

* the *Lubin–Tate tower itself* — `NK.LocalReciprocityLubinTate.Unramified.nonempty_lubinTateTower_adicCompletion`
  constructs `LubinTateTower F F' π (higherUnits F) (residueCard F)` from Honda's reciprocity law
  alone, by taking the levels `E_{m,n} = F^{ur}_{m+1} · F(Λ_{n+1})` and computing their norm groups
  by transitivity of the norm and an index squeeze;
* the *existence theorem* `NK.LocalCFT.ExistenceTheorem F F'`
  (`NK.LocalReciprocityLubinTate.existenceTheorem_of_tower`) follows from the tower together with
  the cofinality of the higher unit filtration
  (`NK.LocalReciprocityLubinTate.Units.higherUnits_cofinal`);
* the *norm index theorem* `NK.LocalArtin.NormIndex F F'` is a theorem of this chapter for
  `F = 𝔭.adicCompletion K` (`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`);
* the surjectivity of the Artin map at every finite abelian level is a theorem
  (`NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap`), as is the packaging of the level
  isomorphisms into the datum (`NK.LocalArtin.ReciprocityMap.toArtinReciprocity`);
* so is the whole polynomial/geometric layer of Lubin–Tate theory: the Lubin–Tate formal group and
  its `𝒪[F]`-module structure (`LubinTate/`), the division points `Λ_n` with `#Λ_n = q^n`, the
  degrees `[F(Λ_n) : F] = (q-1)q^{n-1}`, and the Galois structure
  `Gal(F(Λ_n)/F) ≅ (𝒪[F]/π^n)^×` (`Eval/`, `LubinTate/`).

## Main results

* `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` — the boundary theorem
  (the two classical residues above, for `K` a number field and `𝔭` a finite prime);
* `NK.LocalReciprocityLubinTate.artinReciprocity_of_lubinTate_higherUnits` — the same for a general
  nonarchimedean local field, with `NormIndex` as an extra hypothesis (the classical
  Herbrand-quotient computation, not available unconditionally for a general `F` in this workspace);
* `NK.LocalReciprocityLubinTate.artinReciprocity_of_lubinTate` — the general-`F`, general-`U` form.

## Universes

The boundary theorem is stated for `K : Type` (universe `0`): the unramified levels of the tower
come from `NK.Unramified.exists_unramified_level_adicCompletion`, which is universe-`0` because
the shared commons lemma `Commons.NumberTheory.NumberField.Completion.exists_galois_unramified_tower_with_subfield`
is.  Everything *else* in the chapter is `Type u`-polymorphic, including the registered instances
`ValuativeRel`, `IsNonarchimedeanLocalField`, `CharZero` on `Q.adicCompletion K`, the norm index
theorem `NormIndex.normIndex_adicCompletion`, and the tower assembly
`Unramified.nonempty_lubinTateTower_adicCompletion`.  See `README.md` §16.7.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u v

noncomputable section

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The local reciprocity datum for a `p`-adic field** (the boundary theorem of the chapter).

For a number field `K` and a finite prime `𝔭`, given

* a uniformiser `π` of `F = 𝔭.adicCompletion K` (which always exists, and is *not* a hypothesis:
  `NK.LocalReciprocityLubinTate.exists_isUniformizer_adicCompletion` produces one),
* Honda's explicit reciprocity law for `π` and the higher unit filtration
  `U^n = 1 + 𝔪[F]^n` (`NK.LocalReciprocityLubinTate.Unramified.hondaReciprocity`, a *theorem*),
* the norm residue symbol with the correct level kernels (the fundamental class of the local class
  formation),

the canonical local Artin reciprocity datum for `F ⊆ SeparableClosure F` exists.  Everything except
`KernelCondition` is *proved* here — the Lubin–Tate tower (which uses Honda), the existence
theorem, the norm index theorem and the surjectivity of the level Artin maps; see the module
docstring. -/
theorem artinReciprocity_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hK : NK.LocalArtin.KernelCondition (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) :
    Nonempty (NK.LocalCFT.ArtinReciprocity (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_adicCompletion Q
  obtain ⟨T⟩ := Unramified.nonempty_lubinTateTower_adicCompletion Q hπ
    (Unramified.hondaReciprocity (Q.adicCompletion K) π hπ)
  exact nonempty_artinReciprocity_of_lubinTate_higherUnits (Q.adicCompletion K)
    (SeparableClosure (Q.adicCompletion K)) T
    (fun M hM => Units.higherUnits_cofinal (Q.adicCompletion K) M hM) hK
    (NormIndex.normIndex_adicCompletion Q)

/-- **The residue of the boundary theorem, bundled.**  After Honda's explicit reciprocity law and
the construction of the Lubin–Tate tower, the *single* remaining classical statement is the norm
residue symbol with the correct level kernels (`NK.LocalArtin.KernelCondition`) — the existence of
the fundamental class of the local class formation `(G_F, F̄ˣ)`, i.e. Serre, *Local Fields*, Ch. XIII
§4, Thm. 6 / Ch. XIV §3, together with Ch. XV §5.2 (Neukirch, *Algebraic Number Theory*, V.5.5).

Note that `KernelCondition` does *not* contain the existence theorem (that is
`NK.LocalCFT.ExistenceTheorem`, proved here unconditionally for `𝔭.adicCompletion K`), nor the
norm index theorem (proved here for `𝔭.adicCompletion K`), nor the surjectivity of the level Artin
maps (proved from the norm index theorem by `NK.LocalArtin.Reduction`). -/
def LocalResidual (F : Type u) (F' : Type v) [Field F] [Field F'] [Algebra F F']
    [IsGalois F F'] : Prop :=
  Nonempty (NK.LocalArtin.KernelCondition F F')

/-- **The existence theorem of local class field theory for a `p`-adic field, from Honda's
reciprocity law alone.**

Every finite-index subgroup `M ≤ Fˣ` contains the norm group of a finite abelian extension of `F`.
This is item 3 of the chapter's specification (`cofinal`), and it is *proved*, not assumed: from
Honda's reciprocity law one gets the Lubin–Tate tower
(`Unramified.nonempty_lubinTateTower_adicCompletion`), whose levels `E_{m,n}` have norm groups
`⟨π^{m+1}⟩ · U^{n+1}`; a finite-index `M` contains `π^k` for some `k ≥ 1` and `U^n` for some `n`
(`Units.higherUnits_cofinal`), hence contains `N_{E_{k-1,n-1}/F}`. -/
theorem existenceTheorem_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    NK.LocalCFT.ExistenceTheorem (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K)) := by
  obtain ⟨π, hπ⟩ := exists_isUniformizer_adicCompletion Q
  obtain ⟨T⟩ := Unramified.nonempty_lubinTateTower_adicCompletion Q hπ
    (Unramified.hondaReciprocity (Q.adicCompletion K) π hπ)
  exact existenceTheorem_of_tower T (higherUnits_antitone (Q.adicCompletion K))
    (fun M hM => Units.higherUnits_cofinal (Q.adicCompletion K) M hM)

/-- **The boundary theorem, `p`-adic form, with the two classical residues bundled** as
`NK.LocalReciprocityLubinTate.LocalResidual`. -/
theorem artinReciprocity_adicCompletion_of_residual {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (h : LocalResidual (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K))) :
    Nonempty (NK.LocalCFT.ArtinReciprocity (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) :=
  artinReciprocity_adicCompletion Q h.some

/-- The general-field form of the boundary theorem: over any field `F` with Galois extension `F'`,
the Lubin–Tate tower, the cofinality of the unit filtration, the norm residue symbol with the correct
kernels, and the norm index theorem give the local reciprocity datum.  (For `F` a nonarchimedean
local field that the workspace can reach by a number-field argument, the norm index theorem is
supplied unconditionally by
`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`; for a general nonarchimedean
local field it is the classical Herbrand-quotient computation.) -/
theorem artinReciprocity_of_lubinTate {π : Fˣ} {U : ℕ → Subgroup Fˣ} {q : ℕ}
    (T : LubinTateTower F F' π U q) (hUanti : Antitone U)
    (hU : ∀ M : Subgroup Fˣ, M.FiniteIndex → ∃ n, U n ≤ M)
    (hK : NK.LocalArtin.KernelCondition F F') (hN : NK.LocalArtin.NormIndex F F') :
    Nonempty (NK.LocalCFT.ArtinReciprocity F F') :=
  nonempty_artinReciprocity_of_lubinTate T hUanti hU hK hN

/-- The boundary theorem with the unit filtration instantiated at the higher unit groups
`U^n = 1 + 𝔪^n` of a nonarchimedean local field, i.e. in the classical form in which the norm groups
of the Lubin–Tate levels are `N_{F(π_n)/F} F(π_n)ˣ = ⟨π⟩ · U^n`.  This is the general-field form of
`artinReciprocity_adicCompletion`, with the *tower* still a hypothesis (for
`F = 𝔭.adicCompletion K` the tower is a theorem,
`NK.LocalReciprocityLubinTate.Unramified.nonempty_lubinTateTower_adicCompletion`). -/
theorem artinReciprocity_of_lubinTate_higherUnits (F : Type u) (F' : Type v) [Field F]
    [Field F'] [Algebra F F'] [IsGalois F F'] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {π : Fˣ} {q : ℕ}
    (T : LubinTateTower F F' π (higherUnits F) q)
    (hU : ∀ M : Subgroup Fˣ, M.FiniteIndex → ∃ n, higherUnits F n ≤ M)
    (hK : NK.LocalArtin.KernelCondition F F') (hN : NK.LocalArtin.NormIndex F F') :
    Nonempty (NK.LocalCFT.ArtinReciprocity F F') :=
  nonempty_artinReciprocity_of_lubinTate_higherUnits F F' T hU hK hN

end

end NK.LocalReciprocityLubinTate
