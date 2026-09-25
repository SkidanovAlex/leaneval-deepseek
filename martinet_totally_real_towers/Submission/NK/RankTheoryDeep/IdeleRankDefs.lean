import Submission.NK.RankTheoryDeep.CharModule
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.Reconstruct.GammaObject

/-!
# The idèle-side rank theory: vocabulary

This file fixes the vocabulary of the idèle-class-group computation of `r_ℓ(K)` (CoNF Ch. X
§10.3, CoNF (10.3.20)), the half of the Shimizu rank input that does **not** need class field
theory:

* `NK.RankTheoryDeep.dualRank` — the `ℤ_ℓ`-rank of the continuous character module
  `Dual G ℓ = Hom_cts(G, ℤ_ℓ)` of a topological commutative group;
* `NK.RankTheoryDeep.LocalUnitDualRankInput ℓ` — the **local unit structure** at the places
  `v | ℓ` (`𝒪_vˣ ≅ μ_{q-1} × (1+𝔪)`, `1+𝔪 ≅ ℤ_ℓ^{[K_v:ℚ_ℓ]}`), in the form in which the assembly
  consumes it: at a place of residue characteristic `ℓ` (equivalently `v | ℓ`) the `ℤ_ℓ`-rank of
  the character module of the local units is at most `e_v·f_v = [K_v : ℚ_ℓ]`;
* `NK.RankTheoryDeep.IdeleDualRankBound ℓ` — the idèle-side rank bound
  `rank_{ℤ_ℓ} Hom_cts(C_K, ℤ_ℓ) ≤ [K : ℚ]`, i.e. `r_ℓ(K) ≤ [K : ℚ]`;
* `NK.RankTheoryDeep.ArtinDualBridge Ω ℓ` — ℓ-adic Artin reciprocity in the form needed to
  pass from the idèle class group to `Γ_K`: `Dual (Γ_K) ℓ ≅ Dual (C_K) ℓ`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField

namespace NK.RankTheoryDeep

universe u

/-- The `ℤ_ℓ`-rank of the continuous character module of a topological commutative group.  For
`G` a compact `ℓ`-adic analytic group this is the quantity `r_ℓ` of Shimizu §4. -/
noncomputable def dualRank (G : Type u) [CommGroup G] [TopologicalSpace G]
    (ℓ : ℕ) [Fact ℓ.Prime] : Cardinal :=
  Module.rank (PadicInt ℓ) (NK.Reconstruct.Dual G ℓ)

/-- **The local unit structure at `v | ℓ`** (CoNF Ch. X §10.3, the standard local computation
`𝒪_vˣ ≅ μ_{q-1} × (1 + 𝔪)` with `1 + 𝔪 ≅ ℤ_ℓ^{[K_v : ℚ_ℓ]}`), in the form consumed by the
assembly: for a finite place `q` of the number field `K` lying over `ℓ`, the `ℤ_ℓ`-rank of the
continuous character module of the local units `𝒪_qˣ` is at most the local degree
`e_q · f_q = [K_q : ℚ_ℓ]`.

(`q.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)})` says that the residual characteristic of `q` is `ℓ`,
i.e. `q | ℓ`; see `NK.RankTheoryDeep.charP_quotient_iff_liesOver_span`.) -/
def LocalUnitDualRankInput (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K]
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
    q.asIdeal.LiesOver (Ideal.span {(ℓ : ℤ)}) →
      dualRank (↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q))) ℓ
        ≤ (q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ : Cardinal)

/-- **The idèle-side rank bound** (CoNF (10.3.20), the half that needs no class field theory): the
`ℤ_ℓ`-rank of the continuous character module of the idèle class group `C_K = 𝕀 K ⧸ Kˣ` is at most
the degree `[K : ℚ]`.  Classically it is *equal* to `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K)`. -/
def IdeleDualRankBound (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K],
    dualRank (NK.GlobalCFT.IdeleClassGroup K) ℓ ≤ (Module.finrank ℚ K : Cardinal)

/-- **ℓ-adic Artin reciprocity, in dual form — stated at the separable closure.**

For every number field `K` *with a `K`-algebra structure on `Ω`* (equivalently, `K` a subfield of
`Ω`) the continuous character module of `Γ_K = lim_L ℓ-part(Gal(L/K)^{ab})` is that of the idèle
class group `C_K`: `Hom_cts(Γ_K, ℤ_ℓ) ≅ Hom_cts(C_K, ℤ_ℓ)`, i.e. `r_ℓ(K) = rank_{ℤ_ℓ} Hom(C_K, ℤ_ℓ)`.

**Why the quantification is restricted to `K' = Ω`, and not made over an arbitrary Galois
`K'/K`.**  The level was too generous, exactly as with `NK.Reconstruct.RankFormulaInput` at
`K' = K`: at `K' = K` the only level of `K/K` is `K` itself, so `Γ_{K/K}` is the trivial group and
its continuous dual has `ℤ_ℓ`-rank `0`, while `Dual (C_K) ℓ` has rank `r_ℓ(K) ≥ 1`; an equality for
all `K'` would therefore be false at `K' = K`.  The mathematics of Artin reciprocity lives at
`K' = Ω` (all the finite levels being present), and that is the form stated here; the small-`K'`
statements are weaker, and are obtained from this one by descent whenever `K'` is a level of
`Ω/K` (the restriction `Γ_K^{Ω} ↠ Γ_K^{K'}` is then surjective, so `Dual (Γ_K^{K'}) ℓ ↪
Dual (Γ_K^{Ω}) ℓ`).

This is the limit form of the finite-level reciprocity isomorphism
`C_K ⧸ N_{L/K} C_L ≅ Gal(L/K)ᵃᵇ` of `NK.GlobalCFT.GaloisReciprocity`
(`Submission/Work/GlobalCFT/Reciprocity.lean`). -/
def ArtinDualBridge (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [Algebra K Ω] [IsGalois K Ω],
    dualRank (NK.Reconstruct.Gamma K Ω ℓ) ℓ
      = dualRank (NK.GlobalCFT.IdeleClassGroup K) ℓ

end NK.RankTheoryDeep
