import Mathlib
import Submission.NK.RankTheoryDeep.RankTop
import Submission.NK.RankTheoryDeep.CharModule
import Submission.NK.RankTheoryDeep.IdeleFinal
import Submission.NK.Reconstruct.GammaObject
import Submission.NK.Reconstruct.galToGamma
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.GlobalCFTdeep.Existence

/-!
# Towers of `(ℤ/2^n)^r`-quotients: levelwise isomorphisms can be made compatible

This file isolates the *group-theoretic crux* behind the reduction recorded in
`Submission/Work/NUV2/TowerRank/NOTES.md`: for two towers of finite groups whose levels are
`(ℤ/2^n)^r`, any levelwise family of isomorphisms can be corrected to a *compatible* family.

```
NK.NUV2.TowerRank.TowerCompatible r :
  ∀ (G H : ℕ → Type) [..], (qG : ∀ n, G (n+1) →* G n) → (qH : ∀ n, H (n+1) →* H n) →
  (∀ n, Surjective (qG n)) → (∀ n, Surjective (qH n)) →
  (∀ n, G n ≃* Multiplicative (Fin r → ZMod (2^n))) →
  (∀ n, H n ≃* Multiplicative (Fin r → ZMod (2^n))) →
  (∀ n, G n ≃* H n) →
  ∃ φ : ∀ n, G n ≃* H n, ∀ n, (φ n).toMonoidHom.comp (qG n) = (qH n).comp (φ (n+1)).toMonoidHom
```

**Why this is the right statement.**  `NK.RankTheoryDeep.ArtinDualBridge` asks for the equality of
the `ℤ_ℓ`-ranks of `Hom_cts(Γ_K, ℤ_ℓ)` and `Hom_cts(C_K, ℤ_ℓ)`.  A `ℤ_ℓ`-quotient of a compact
abelian group is the same thing as a `ℤ_ℓ^r`-**tower**, i.e. a maximal chain of open subgroups with
levels `(ℤ/ℓ^n)^r` (NOT the whole lattice of open subgroups): see §1 of the NOTES.  Along a chain,
the compatibility of the levelwise Artin isomorphisms can be arranged *without any canonicity*, by

* **descending**: given an isomorphism at level `N`, push it down the chain by the *uniqueness* of
  the map induced by `qH_n ∘ φ_{n+1}` — its kernel is the `2`-torsion (which is *computed*, not
  chosen), so it is well defined and an isomorphism;
* **an ultrafilter limit**: the descending construction produces a compatible system up to any
  finite level, and an ultrafilter limit of finite sets extracts a global compatible system.

This is exactly where the "canonicity of the Artin map" of `../ArtinBridge/NOTES.md` §3–§5 is *not*
needed: the global coherent system at *all* levels (equivalently `LevelPairIso` / a topological
isomorphism `C_K ⧸ C_K⁰ ≅ G_K^ab`) is genuinely harder, but the rank only sees chains.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.NUV2.TowerRank

/-- **Compatibility of levelwise isomorphisms of a `(ℤ/2^n)^r`-tower**: the group-theoretic crux of
the rank form of ℓ-adic Artin reciprocity.  See the module docstring and §2 of the NOTES. -/
def TowerCompatible (r : ℕ) : Prop :=
  ∀ (G H : ℕ → Type) [∀ n, Group (G n)] [∀ n, Group (H n)]
    [∀ n, Fintype (G n)] [∀ n, Fintype (H n)]
    (qG : ∀ n, G (n+1) →* G n) (qH : ∀ n, H (n+1) →* H n),
    (∀ n, Function.Surjective (qG n)) → (∀ n, Function.Surjective (qH n)) →
    (∀ n, G n ≃* Multiplicative (Fin r → ZMod (2^n))) →
    (∀ n, H n ≃* Multiplicative (Fin r → ZMod (2^n))) →
    (∀ n, G n ≃* H n) →
    ∃ φ : ∀ n, G n ≃* H n, ∀ n, (φ n).toMonoidHom.comp (qG n)
      = (qH n).comp (φ (n+1)).toMonoidHom

/-! ### Where the crux is proved

`TowerCompatible r` is **a theorem** for every `r`: see
`NK.NUV2.TowerRank.towerCompatible` in `Submission/Work/NUV2/TowerRank/towerCompatible.lean`
(descending construction along the tower + ultrafilter limit; §2 of the NOTES).  The proof lives in
that module rather than here so that this module (which only *states* the crux) stays free of
imports of the proof.  Consumers who need the crux should

```
import Submission.NK.NUV2.TowerRank.towerCompatible
```

and use `NK.NUV2.TowerRank.towerCompatible r : TowerCompatible r`. -/

end NK.NUV2.TowerRank
