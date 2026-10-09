import Submission.NK.Reconstruct.fourf5Gen
import Submission.NK.Reconstruct.fourf5Rank
import Submission.NK.Reconstruct.torsionFreeGamma
import Submission.NK.Reconstruct.hausPi
import Submission.NK.Reconstruct.gammaSmul
import Submission.NK.Reconstruct.NumFieldIn
import Submission.NK.Reconstruct.NumFieldInSup
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/ShimizuRank/` — the Iwasawa-theoretic rank inputs of Shimizu's proof

Shimizu's proof of the Neukirch–Uchida theorem (arXiv:2009.10431, §4; CoNF Ch. XII §12.2) runs the
*abelianised* reconstruction: the map `ϕ : G_{K₁} ≃ G_{K₂}` induces an isomorphism
`σ̄ : Γ_{K₁} ≃ Γ_{K₂}` of the torsion-free ℓ-adic abelianisations, and Proposition 4f.5 pins down the
base fields by comparing the ℤ_ℓ-*ranks* `r_ℓ(K) = rank_{ℤ_ℓ} Γ_K`.

The live route of `Submission/Work/Reconstruct/` (the endgame
`NK.Reconstruct.exists_sigma_of_localCorrespondence`) consumes exactly three named rank inputs,
all of them stated for `Ω` a separable closure of `ℚ` and `ℓ` a prime:

* `NK.Reconstruct.HausRankInput Ω ℓ` — `rank_{ℤ_ℓ} (Γ_K ⧸ invisible) = r_ℓ(K)`;
* `NK.Reconstruct.RankStrictMonoLevelInputGen Ω ℓ` — Shimizu's Lemma 4f.2;
* `NK.Reconstruct.ResRankInputGen Ω ℓ` — the rank computation of Proposition 4f.5.

This directory is the chapter that *discharges* them (as far as the workspace reaches) and, where
they are irreducible, replaces each of them by **strictly sharper named residuals**, with the
reduction proved, sorry-free and axiom-clean.

## Contents

| module | content |
|---|---|
| `Basic.lean` | the residual predicates (`LeopoldtDefectMono`, `InvisibleSubgroupTorsion`, `GammaTFRankFinite`, `RankUpperBound`, `ResKernelRankInput`) and the elementary rank algebra of `Γ_K`; |
| `ComplexPlace.lean` | the number-field theory of `rComplex` (count of complex places): monotonicity, and the strict increase `r_ℂ(M) < r_ℂ(N)` for a nontrivial extension with a complex prime; |
| `StrictMono.lean` | `RankStrictMonoLevelInputGen` from `LeopoldtDefectMono` and `ComplexPlace.lean`; |
| `HausRank.lean` | `HausRankInput` from `InvisibleSubgroupTorsion` + `GammaTFRankFinite`; |
| `ResRank.lean` | `ResRankInputGen` from `HausRankInput` + `ResKernelRankInput`; |
| `Package.lean` | the packaged corollary `rankInputs`, and the consumer-facing `rankStrictMono_of_complex`; |
| `All.lean` | umbrella. |

## The mathematical content of the three inputs, and what is left

The classical evaluation of `r_ℓ(K)` is CoNF (10.3.20):

  `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K) ≤ [K : ℚ]`,

where `r_ℂ(K)` is the number of complex places and `δ_ℓ(K) ≥ 0` the **Leopoldt defect**
(`δ_ℓ(K) = rank_{ℤ_ℓ} 𝒪_K^{×,∧} - (r₁ + r₂ - 1)`, not formalised here, and *not* assumed to
vanish: Leopoldt's conjecture is not presupposed anywhere in this directory).

Shimizu's Lemma 4f.2 is proved from that formula together with `r_ℂ(M) < r_ℂ(N)` (which is
elementary, `ComplexPlace.lean`) and the **monotonicity of the defect** `δ_ℓ(M) ≤ δ_ℓ(N)`
(CoNF (10.3.7) Corollary and the proof of (10.3.11) Corollary).  Since `δ_ℓ` is not part of this
development, the only hypothesis one has to carry is the *difference estimate*
`r_ℓ(M) - r_ℂ(M) ≤ r_ℓ(N) - r_ℂ(N)`, which is exactly what `LeopoldtDefectMono` records — with the
subtractions avoided by clearing denominators (a statement in `ℕ`).

For `HausRankInput` and `ResRankInputGen` the content is the ℓ-adic group theory of the pro-ℓ
completion of `G_K^{ab}` and the transfer/duality of Lemma 4f.1; the residuals
`InvisibleSubgroupTorsion`, `GammaTFRankFinite` and `ResKernelRankInput` below isolate precisely
the parts that the formal development cannot reach (see the module docstrings of `HausRank.lean`
and `ResRank.lean` for the audit of each).

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. I §1.6, Ch. X §10.3,
Ch. XII §12.1–12.2;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.ShimizuRank

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-! ## The complex places of a number field

`NK.Reconstruct.rComplex K` is defined as `Nat.card {v : InfinitePlace K // IsComplex v}`; this
section records its two elementary estimates: it is Mathlib's `nrComplexPlaces`, and it is bounded by
half the degree (the `r_ℂ`-half of the bound `r_ℓ(K) ≤ [K : ℚ]` of CoNF (10.3.20)). -/

/-- `r_ℂ(K)`, Shimizu's count of complex primes, is Mathlib's `nrComplexPlaces`. -/
theorem rComplex_eq_nrComplexPlaces (K : Type*) [Field K] [NumberField K] :
    rComplex K = NumberField.InfinitePlace.nrComplexPlaces K := by
  classical
  rw [rComplex, NumberField.InfinitePlace.nrComplexPlaces, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- **The number of complex places is at most half the degree**: `2 r_ℂ(K) ≤ [K : ℚ]`.

This is the `r_ℂ`-half of the bound `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K) ≤ [K : ℚ]` of CoNF (10.3.20)
(with `r_ℂ(K) + 1 ≤ [K:ℚ]` for `K ≠ ℚ`). -/
theorem two_mul_rComplex_le_finrank (K : Type*) [Field K] [NumberField K] :
    2 * rComplex K ≤ Module.finrank ℚ K := by
  classical
  rw [rComplex_eq_nrComplexPlaces, ← NumberField.InfinitePlace.card_complex_embeddings,
    ← NumberField.Embeddings.card K ℂ]
  exact Fintype.card_subtype_le _

/-! ## Monotonicity of the Leopoldt defect (CoNF (10.3.7), (10.3.11)) -/

/-- **Monotonicity of the Leopoldt defect** (CoNF (10.3.7) Corollary, and the proof of
(10.3.11) Corollary), in the subtraction-free form used by Shimizu's Lemma 4f.2.

Shimizu (arXiv:2009.10431, Lemma 4f.2) proves `r_ℓ(K) < r_ℓ(L)` for a nontrivial finite extension
`L/K` with a complex prime from the two facts

* `r_ℂ(K) < r_ℂ(L)` (a theorem, `NK.ShimizuRank.ComplexPlace.rComplex_lt_of_lt`), and
* `δ_ℓ(K) ≤ δ_ℓ(L)` (NSW (10.3.7) Corollary) — the monotonicity of the Leopoldt defect,

together with (10.3.20) `r_ℓ = r_ℂ + 1 + δ`.  Since `δ_ℓ` itself is not formalised in this
development, this predicate records the conclusion of those two facts *after substituting the
formula*: the difference estimate `r_ℓ(M) - r_ℂ(M) ≤ r_ℓ(N) - r_ℂ(N)` becomes, after clearing the
negative signs,

  `r_ℓ(M) + r_ℂ(N) ≤ r_ℓ(N) + r_ℂ(M)`.

By the displayed formula this is *equivalent* to `δ_ℓ(N) - δ_ℓ(M) ≥ 0` (with `δ_ℓ = r_ℓ - r_ℂ - 1`
the defect), so it is exactly the classical statement — it is stated in `ℕ` only to avoid the
truncated subtraction.

*Satisfiability.*  `LeopoldtDefectMono Ω ℓ` is a theorem of the literature (CoNF (10.3.7)
Corollary); it holds for every `Ω`, `ℓ`, and it is implied by the full rank formula of
(10.3.20) together with the defect's monotonicity.  It is not implied by any other residual of
this directory, and it is *not* vacuous: it is a nontrivial inequality between the ranks of two
different fields.  Nothing in this development assumes `δ_ℓ = 0`. -/
def LeopoldtDefectMono (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (M N : NumFieldIn ℚ Ω) [IsSepClosure ↥M.L Ω] [IsSepClosure ↥N.L Ω],
    M.L ≤ N.L →
      rankGamma ↥M.L Ω ℓ + rComplex ↥N.L ≤ rankGamma ↥N.L Ω ℓ + rComplex ↥M.L

/-- **`LeopoldtDefectMono` from the rank formula of CoNF (10.3.20).**

If the rank formula `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K)` is available with a defect function `δ` and `δ`
is monotone along finite extensions, then the difference estimate `LeopoldtDefectMono` follows
immediately.  This records that the residual `LeopoldtDefectMono` is exactly "the rank formula plus
the monotonicity of the defect", i.e. CoNF (10.3.7) Corollary and the proof of (10.3.11) Corollary,
and no more. -/
theorem leopoldtDefectMono_of_rankFormula {ℓ : ℕ} [Fact ℓ.Prime] (δ : NumFieldIn ℚ Ω → ℕ)
    (hformula : ∀ (K : NumFieldIn ℚ Ω) [IsSepClosure ↥K.L Ω],
      RankFormulaInput ↥K.L Ω ℓ (δ K))
    (hmono : ∀ (M N : NumFieldIn ℚ Ω) [IsSepClosure ↥M.L Ω] [IsSepClosure ↥N.L Ω],
      M.L ≤ N.L → δ M ≤ δ N) :
    LeopoldtDefectMono Ω ℓ := by
  intro M N _ _ hMN
  rw [(hformula M).formula, (hformula N).formula]
  have hd := hmono M N hMN
  omega

/-! ## The rank bound of CoNF (10.3.20) -/

/-- **The upper bound of CoNF (10.3.20)**: `r_ℓ(K) ≤ [K : ℚ]`.

This is the second half of Shimizu's displayed formula `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K) ≤ [K:ℚ]`.
It is *not* needed by the endgame of `Submission/Work/Reconstruct/` (Prop. 4f.5 uses only the
strict monotonicity of `r_ℓ`, i.e. Lemma 4f.2), and it is recorded here for completeness and
use by later work; it is implied by the full rank formula, and hence implied by the input list of
nothing else in this directory.

*Satisfiability.*  CoNF (10.3.20) is a theorem for every `Ω`, `ℓ`; the bound is a genuine
statement (it also implies `rankGamma ℚ Ω ℓ ≤ 1`). -/
def RankUpperBound (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : NumFieldIn ℚ Ω) [IsSepClosure ↥K.L Ω], rankGamma ↥K.L Ω ℓ ≤ Module.finrank ℚ ↥K.L

/-! ## The two halves of `HausRankInput` -/

/-- **The invisible subgroup of `Γ_K` is a torsion group.**

`NK.Reconstruct.HausQuot K K' ℓ = Γ_K ⧸ invisibleSubmodule` is the quotient of the ℓ-adic
abelianisation of `G_K` by the subgroup invisible to every continuous character
`Γ_K → ℤ_ℓ`; `NK.Reconstruct.rankGamma K K' ℓ` is the ℤ_ℓ-rank of `Γ_K ⧸ torsion`.  The
predicate says that the invisible subgroup *is* the torsion subgroup, i.e. that the Hausdorff
quotient and the torsion-free quotient are the same group up to finite index.

This is the exact group-theoretic content of the identification of the two models of `Γ_K` used by
Shimizu (see `NK.Reconstruct.HausRankInput`): it is the statement that the ℓ-adic completion of
`G_K^{ab}` has the shape `ℤ_ℓ^{r} ⊕ T` with `T` a torsion group such that *every* continuous
character kills `T`.

It is *not* a formal consequence of the definitions: what is provable unconditionally (and proved
here) is only the *containment* `torsion ⊆ invisible`
(`NK.ShimizuRank.gammaTorsion_le_invisibleSubmodule`) and the torsion-freeness of `HausQuot`
(`NK.ShimizuRank.hausQuot_torsionFree`).  The predicate is exactly the statement that `Γ_K` is an
extension of a free `ℤ_ℓ`-module by a group killed by every continuous character.  Classically it
follows from `G_K^{ab,(ℓ)} ≅ (C_K)^{(ℓ)}` (Artin
reciprocity) together with the structure theory of the idèle class group of a number field
(`C_K ≅ ℝ_{>0}^{r₁} × Ẑ × 𝒪_K^{×,∧} × Cl(K)`, NSW Ch. X §10.3), i.e. from CoNF (10.3.20). -/
def InvisibleSubgroupTorsion (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K'] [Algebra K K']
    [IsGalois K K'],
    Module.IsTorsion (PadicInt ℓ) ↥(invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ))

/-- **The torsion-free ℓ-adic abelianisation `Γ_K^{tf}` has finite ℤ_ℓ-rank.**

`NK.Reconstruct.rankGamma K K' ℓ` is `Module.finrank (PadicInt ℓ) (GammaTF K K' ℓ)`, and
`Module.finrank` is `Cardinal.toNat` of `Module.rank`; the two agree *only* when the rank is
finite.  Hence the identification of `rankGamma` with the honest `Module.rank` — which is what
`NK.Reconstruct.HausRankInput` asserts on the `HausQuot` side — needs the finiteness of the
rank, i.e. the first half of CoNF (10.3.20): `Γ_K` is a finitely generated `ℤ_ℓ`-module
(this is `NK.Reconstruct.RankFormulaInput.finite`, restated for the level-`∞` form
`GammaTF`).

*Satisfiability.*  A theorem of CoNF (10.3.20): `Γ_K ≅ ℤ_ℓ^{r_ℓ(K)} ⊕ (finite)`, so the rank is
`r_ℓ(K) < ℵ₀`.  It is *strictly weaker* than `HausRankInput` (which implies it) and is not implied
by any other residual here. -/
def GammaTFRankFinite (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K'] [Algebra K K']
    [IsGalois K K'],
    Module.rank (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) < Cardinal.aleph0

/-! ## The residual of `ResRankInputGen`: the kernel-rank computation

The rank computation of Shimizu's Proposition 4f.5 has a *proved* half and an *unproved* half.

**Proved** (in `Submission/Work/Reconstruct/`), with `K ⊆ L` finite levels of `Ω/ℚ`:

* the cokernel of the base change `π^{tf}_{L/K} : Γ_L^{tf} → Γ_K^{tf}` is finite
  (`NK.Reconstruct.finite_coker_hausPi`);
* hence `r_ℓ(K) = rank_{ℤ_ℓ}(Γ_L^{tf} ⧸ ker π^{tf}_{L/K})`
  (`NK.Reconstruct.rank_hausQuot_eq_rank_quot_ker`), and for `K ⊆ M ⊆ L` the functoriality
  `π^{tf}_{L/K} = π^{tf}_{M/K} ∘ π^{tf}_{L/M}` (`NK.Reconstruct.hausPi_comp`) gives
  `ker π^{tf}_{L/M} ⊇ ker π^{tf}_{L/K}`, whence the monotonicity
  `r_ℓ(K) ≤ r_ℓ(M)` (`NK.Reconstruct.rank_hausQuot_le_of_le`);
* if `K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}` then `ker π^{tf}_{L/K₁} = ker π^{tf}_{L/K₂}`
  (`NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq`).

**Unproved.**  With `M = K₁ ∩ K₂`, the proof of Prop. 4f.5 needs the *reverse* inequality
`r_ℓ(K₁) ≤ r_ℓ(M)`.  Since `ker π^{tf}_{L/M} ⊇ ker π^{tf}_{L/K₁}`, the general rank calculus gives
the opposite inequality, so this is genuine extra content: it is Shimizu's duality argument, whose
two ingredients are Lemma 4f.1 (the restriction `res = π^*` has finite cokernel, NSW (1.6.7)) and
the fact that `im(res^{K₁}) ∩ im(res^{K₂})` is contained in the `G(L/K₁∩K₂)`-invariants of
`Hom(Γ_L, ℤ_ℓ)`.  `ResKernelRankInput` below isolates exactly the inequality. -/

/-- **The kernel-rank computation of Shimizu's Proposition 4f.5.**

With `M = K₁ ∩ K₂` and a finite level `L ⊇ K₁, K₂` such that `K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}`: the
rank of `Γ_L^{tf}` modulo the (larger) kernel of `π^{tf}_{L/M}` is at least the rank modulo the
(smaller) kernel of `π^{tf}_{L/K₁}`.

Rewritten with `NK.Reconstruct.rank_hausQuot_eq_rank_quot_ker` this is exactly the statement
`r_ℓ(M) ≥ r_ℓ(K₁)`, i.e. the inequality `NK.Reconstruct.ResRankInputGen` asks for; it is
recorded in kernel form because that is where the mathematics sits (the two kernels differ by the
Galois group of `LK₁^{(∞)} / LM^{(∞)}`, and the claim is that this difference does not contribute
to the rank — the "finite index" statement of Shimizu's proof of Prop. 4f.5).

*Satisfiability.*  A theorem of Shimizu (it is the rank step of the proof of Prop. 4f.5, and hence
holds whenever `K₁ = K₂`, in particular in the situation where Prop. 4f.5 applies).  It is
*not* a formal consequence of the base-change calculus (the latter gives the reverse inequality)
and it is not implied by `HausRankInput`; the reduction
`NK.ShimizuRank.resRankInputGen_of_residual` shows that `ResRankInputGen` follows from it
together with `HausRankInput`. -/
def ResKernelRankInput (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K₁ K₂ M : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K₁.L Ω]
    [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω],
    M.L = (K₁.L ⊓ K₂.L) → (h₁ : K₁.L ≤ L.L) → (h₂ : K₂.L ≤ L.L) →
    (hM : M.L ≤ L.L) →
    (levelInfinityOf K₁ ℓ ⊔ L.L = L.L ⊔ levelInfinityOf K₂ ℓ) →
      Module.rank (PadicInt ℓ)
          (HausQuot ↥L.L Ω ℓ ⧸ LinearMap.ker (hausPi M L hM ℓ))
        ≥ Module.rank (PadicInt ℓ)
          (HausQuot ↥L.L Ω ℓ ⧸ LinearMap.ker (hausPi K₁ L h₁ ℓ))

end NK.ShimizuRank
