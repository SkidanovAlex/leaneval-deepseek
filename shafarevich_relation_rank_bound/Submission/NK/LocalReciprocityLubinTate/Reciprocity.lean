import Submission.NK.LocalReciprocityLubinTate.Tower
import Submission.NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap

/-!
# The reciprocity datum from the Lubin–Tate tower

This file assembles the target of the chapter:

```
Lubin–Tate tower  +  the norm residue symbol with the correct kernels
      ⟹  Nonempty (NK.LocalCFT.ArtinReciprocity F F')
```

The two remaining classical inputs are

* `NK.LocalReciprocityLubinTate.LubinTateTower F F' π U q` (with `U` decreasing and cofinal among
  the finite-index subgroups) — the Lubin–Tate construction itself: the levels `F(π_n)` exist, their
  norm groups are `⟨π⟩ · U^n`, and `F^{ab}` is exhausted by the composita of an unramified and a
  Lubin–Tate level;
* `NK.LocalArtin.KernelCondition F F'` — the existence of the norm residue symbol with the correct
  kernels (Honda's explicit reciprocity law, equivalently the fundamental class of the local class
  formation `(G_F, F̄ˣ)`).

Everything else is proved here or in the sibling chapters:

* the *existence theorem* `NK.LocalCFT.ExistenceTheorem F F'` is a theorem of this chapter
  (`existenceTheorem_of_tower`, from the tower alone);
* the *norm index theorem* `NK.LocalArtin.NormIndex F F'` is a theorem for the local fields that
  the workspace can reach unconditionally (`Submission/Work/LocalReciprocityLubinTate/NormIndex/`);
* the surjectivity of the Artin map at every finite abelian level is a theorem of
  `NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap`;
* the packaging of the level isomorphisms into the datum is
  `NK.LocalArtin.ReciprocityMap.toArtinReciprocity` and
  `NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw`.

## Main results

* `NK.LocalReciprocityLubinTate.nonempty_artinReciprocity_of_lubinTate`;
* `NK.LocalReciprocityLubinTate.nonempty_artinReciprocity_of_lubinTate_higherUnits`.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u v

noncomputable section

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The Artin reciprocity datum from the Lubin–Tate tower.**

Given a Lubin–Tate tower for `(F, π)` whose norm groups are `⟨π^{m+1}⟩ · U^{n+1}` and which
exhausts `F^{ab}`, with `U` decreasing and cofinal among the finite-index subgroups of `Fˣ`, the
norm index theorem, and the norm residue symbol with the correct level kernels, the full
`ArtinReciprocity` datum exists. -/
theorem nonempty_artinReciprocity_of_lubinTate {π : Fˣ} {U : ℕ → Subgroup Fˣ} {q : ℕ}
    (T : LubinTateTower F F' π U q) (hUanti : Antitone U)
    (hU : ∀ M : Subgroup Fˣ, M.FiniteIndex → ∃ n, U n ≤ M)
    (hK : NK.LocalArtin.KernelCondition F F') (hN : NK.LocalArtin.NormIndex F F') :
    Nonempty (NK.LocalCFT.ArtinReciprocity F F') := by
  have hex : NK.LocalCFT.ExistenceTheorem F F' := existenceTheorem_of_tower T hUanti hU
  obtain ⟨R⟩ := NK.LocalArtin.Reduction.kernelCondition_toReciprocityMap hK hN
  exact ⟨R.toArtinReciprocity hex⟩

/-- **The Artin reciprocity datum in the Lubin–Tate form of item 3 of the chapter's specification**:
with the unit filtration instantiated at the higher unit groups `U^n = 1 + 𝔪[F]^n` of a
nonarchimedean local field, the norm groups of the tower levels are the classical
`N_{F(π_n)/F} F(π_n)ˣ = ⟨π⟩ · U^n`. -/
theorem nonempty_artinReciprocity_of_lubinTate_higherUnits (F : Type u) (F' : Type v) [Field F]
    [Field F'] [Algebra F F'] [IsGalois F F'] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {π : Fˣ} {q : ℕ}
    (T : LubinTateTower F F' π (higherUnits F) q)
    (hU : ∀ M : Subgroup Fˣ, M.FiniteIndex → ∃ n, higherUnits F n ≤ M)
    (hK : NK.LocalArtin.KernelCondition F F') (hN : NK.LocalArtin.NormIndex F F') :
    Nonempty (NK.LocalCFT.ArtinReciprocity F F') :=
  nonempty_artinReciprocity_of_lubinTate T (higherUnits_antitone F) hU hK hN

/-- **The chapter's second classical input is implied by the target.**  An
`ArtinReciprocity F F'` (the target of the sibling chapter `NK.LocalCFT`) gives the norm residue
symbol with the correct kernels, so `KernelCondition F F'` is strictly weaker than the target — it is
the target with surjectivity of the level maps, canonicity of the level isomorphisms and the
existence theorem removed. -/
def kernelCondition_of_artinReciprocity (D : NK.LocalCFT.ArtinReciprocity F F') :
    NK.LocalArtin.KernelCondition F F' :=
  D.toReciprocityMap.toKernelCondition

/-- **The norm index theorem is implied by the target** (and is in fact *proved* in this chapter for
`F = 𝔭.adicCompletion K`, see `NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`). -/
theorem normIndex_of_artinReciprocity (D : NK.LocalCFT.ArtinReciprocity F F') :
    NK.LocalArtin.NormIndex F F' :=
  D.toReciprocityMap.normIndex

end

end NK.LocalReciprocityLubinTate
