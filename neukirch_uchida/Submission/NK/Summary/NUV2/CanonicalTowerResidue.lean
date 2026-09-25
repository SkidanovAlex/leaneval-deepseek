import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Target
import Submission.NK.LocalReciprocityLubinTate.Unramified.adicResidual
import Submission.NK.LocalReciprocityLubinTate.Unramified.artinReciprocity_adicCompletion_of_towerCover
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_kernelCondition_of_reciprocityLaw
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion
import Submission.NK.LocalArtin.Basic

/-!
# The well-posed residual of the local reciprocity law at a completion

The requested datum `NK.LocalArtin.KernelCondition (Q.adicCompletion K) (SeparableClosure …)` — a
single Artin map `Fˣ →* Gal(F^{ab}/F)` with the norm groups as its level kernels — is the **local
reciprocity law** for the `p`-adic field `F = Q.adicCompletion K` (Serre, *Local Fields*, Ch. XI §2
and Ch. XV §5.2), and it is the workspace's named classical residual
(`NK.LocalReciprocityLubinTate.LocalResidual`, `NK.NUV2.KCAll`).

This file isolates the residual in the form in which the workspace's Lubin–Tate construction can
attack it, and proves that the residual *is* the missing ingredient (nothing else is missing):

`kernelCondition_of_canonicalTower` shows

```
CanonicalTowerResidue K Q  ⟹  Nonempty (KernelCondition (Q.adicCompletion K) (SeparableClosure …)),
```

and the proof uses only theorems: the assembly of a compatible family of level isomorphisms into one
Artin map (`nonempty_reciprocityLaw_of_symbolTower_noNormCorrespondence`), the norm index theorem at
`Q.adicCompletion K` (`NormIndex.normIndex_adicCompletion`) and the passage from the reciprocity law
to the kernel condition (`nonempty_kernelCondition_of_reciprocityLaw`).

## Why not simply state it about the canonical tower `adicSymbolTower`?

`NK.LocalReciprocityLubinTate.adicSymbolTower` is `Classical.choice` of a `Nonempty`; `Nonempty`
has no specification lemma, and the tower axioms are closed under twists
`symbol m n ↦ β m n ∘ symbol m n` (for a compatible family `β`) for which the norm-kernel property
fails.  A property of the chosen tower is therefore a property of *every* tower satisfying the
axioms, and `NormInKernel` is not such a property.  The existential form below avoids this trap:
the construction of the Lubin–Tate tower produces a *specific* tower, and the properties have to be
verified for it.

## The remaining mathematics

`NormInKernel T` is "the canonical Artin symbol kills norms", and the covering half is the
`Normensatz` restricted to the tower levels (equivalently local Kronecker–Weber,
`F^{ab} = F^{ur} · ⋃_n F(Λ_{π^{n+1}})`).  The workspace's `README.md` for
`Submission/Work/LocalReciprocityLubinTate/` records (§21.8, §21.12, §21.13) that the remaining
content of both is the **canonicity of the Lubin–Tate symbol** (Iwasawa, *Local Class Field Theory*,
Thm. 6.9), equivalently the `Res`-compatibility of the local fundamental classes, i.e. the invariant
map `Br(F) ≅ ℚ/ℤ`; neither the explicit reciprocity law (trace/different) nor cup products are
formalised in this workspace.
-/

namespace NK.Summary.NUV2

open IsDedekindDomain

/-- **The well-posed residual of the local reciprocity law at a completion.**

There is a uniformiser `π` of `F = Q.adicCompletion K` and a Lubin–Tate symbol tower `T` of `π` with
unramified degrees `a m = (m+1)!`, unit filtration `U^{n+1}` and residue cardinality `#𝓀[F]`, such
that

* `NormInKernel T` — the canonical symbols of `T` kill the norms of every finite abelian subfield of
  every level ("the Artin symbol of a norm is trivial", Serre XV §5.2 / Iwasawa Thm. 6.9), and
* the levels of `T` cover the maximal abelian extension of `F` (the `Normensatz` restricted to the
  tower levels, equivalently local Kronecker–Weber). -/
def CanonicalTowerResidue (K : Type) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Prop :=
  ∃ (π : (Q.adicCompletion K)ˣ)
    (_ : NK.LocalReciprocityLubinTate.IsUniformizer (Q.adicCompletion K) (π : Q.adicCompletion K)),
    ∃ T : NK.LocalReciprocityLubinTate.LubinTateSymbolTower (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K)) π (fun m : ℕ => Nat.factorial (m + 1))
        (NK.LocalReciprocityLubinTate.higherUnits (Q.adicCompletion K))
        (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K)),
      NK.LocalReciprocityLubinTate.NormInKernel (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K)) π (fun m : ℕ => Nat.factorial (m + 1))
        (NK.LocalReciprocityLubinTate.residueCard (Q.adicCompletion K)) T ∧
      (∀ (L : IntermediateField (Q.adicCompletion K)
          (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
            (SeparableClosure (Q.adicCompletion K))))
        [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L],
        (∀ σ τ : ↥L ≃ₐ[Q.adicCompletion K] ↥L, σ * τ = τ * σ) →
          ∃ m n : ℕ, L ≤ T.level m n)

/-- **The kernel condition from the well-posed tower residual.**

A canonical symbol tower whose symbols kill norms and whose levels cover `F^{ab}` gives the
compatible family of level isomorphisms, hence the reciprocity law, hence the kernel condition.
Everything except the residual is a theorem of this workspace. -/
theorem kernelCondition_of_canonicalTower (K : Type) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hres : CanonicalTowerResidue K Q) :
    Nonempty (NK.LocalArtin.KernelCondition (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) := by
  obtain ⟨π, _hπ, T, hNK, hcov⟩ := hres
  obtain ⟨hlaw⟩ :=
    NK.LocalReciprocityLubinTate.Unramified.nonempty_reciprocityLaw_of_symbolTower_noNormCorrespondence
      (F := Q.adicCompletion K) (F' := SeparableClosure (Q.adicCompletion K))
      (π := π) (a := fun m : ℕ => Nat.factorial (m + 1)) T
      (NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q) hNK hcov
  exact NK.LocalReciprocityLubinTate.Unramified.nonempty_kernelCondition_of_reciprocityLaw hlaw

end NK.Summary.NUV2
