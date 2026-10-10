import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.NK.Reconstruct.GammaModule
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The torsion-free `Γ_K` of Shimizu's §4 (item (1) of the reconstruction deliverable)

Shimizu (arXiv:2009.10431, §4; CoNF Ch. X §10.3) sets

  `Γ_K = Γ_{K,ℓ} := G_K^{ab,(ℓ),/\tor}`,

the **torsion-free quotient** of the ℓ-part `G_K^{ab,(ℓ)}` (the maximal pro-ℓ quotient of the
abelianisation of `G_K`), a finitely generated `ℤ_ℓ`-module of rank `r_ℓ(K)`.  Everything in
Shimizu's §4 is a statement about this object and its rank.

`NK.Reconstruct.Gamma K K' ℓ` (`GammaObject.lean`) is the projective limit of the finite ℓ-parts
`Γ_{L,ℓ} = ℓ-Sylow(Gal(L/K)^{ab})` over the finite Galois levels `L/K` of `K'`, i.e. exactly
`G_K^{ab,(ℓ)}`.  This file adjoins the missing step of item (1) of the deliverable: the quotient by
the `ℤ_ℓ`-torsion, and with it the *correct* rank invariant `r_ℓ(K)`.

## Why the quotient is needed, and what is *not* true of the limit

The projective system of *full* ℓ-parts is a system of **finite** groups, and its limit
`G_K^{ab,(ℓ)}` has *infinite* torsion in general: for `K = ℚ`, `ℓ = 2`, the multiquadratic levels
`ℚ(√2, …, √p_k)` have `Gal(L/ℚ) = (ℤ/2)^k`, so `Γ_K` admits `(ℤ/2)^k` as a quotient for every `k`,
and `G_ℚ^{ab,(2)}` is `ℤ_2^× × (ℤ/2)^{∞}` up to the identification of the maximal pro-2 quotient of
`Ẑ^× = ∏_p ℤ_p^×`, whose torsion-free quotient is `ℤ_2`.  In particular:

* the limit is **not** a finitely generated `ℤ_ℓ`-module;
* the ℓ-ranks `ellRank(Gal(L/K)^{ab})` of the finite levels are **unbounded**;
* only the *torsion-free quotient* `Γ_K = (G_K^{ab,(ℓ)})/tor` is finitely generated, and it is the
  object `r_ℓ(K)` refers to.

Consequently the earlier invariant `NK.Reconstruct.levelRankSup` (the supremum of the level
ℓ-ranks) is **not** `r_ℓ(K)`; see the warning in `Gamma.lean`.  `rankGamma` below is the correct
invariant, and `RankFormulaInput` below is the corrected (and satisfiable) form of CoNF (10.3.20).

## What is proved here

* `GammaTorsion` — the `ℤ_ℓ`-torsion submodule of `G_K^{ab,(ℓ)}`;
* `GammaTF` — the torsion-free quotient `Γ_K`;
* `mem_gammaTorsion_iff`, `instIsTorsionFreeGammaTF`, `eq_zero_of_smul_eq_zero_gammaTF`,
  `eq_one_of_pow_eq_one_gammaTF` — the basic API of the quotient;
* `gammaTFMk`, `gammaTFMk_surjective` — the quotient map;
* `moduleFinite_gammaTF` — `Γ_K` is a finitely generated `ℤ_ℓ`-module, **given** the
  class-field-theory finiteness input (a field of `RankFormulaInput`);
* `moduleFree_gammaTF` — a finitely generated torsion-free module over the PID `ℤ_ℓ` is *free*;
  hence `Γ_K` is a finite free `ℤ_ℓ`-module;
* `rankGamma` — Shimizu's `r_ℓ(K) = rank_{ℤ_ℓ} Γ_K = finrank_{ℤ_ℓ} Γ_K`;
* `rankGammaLevel` — the same invariant for a finite extension `L ⊆ K'` of `K`;
* `RankFormulaInput` — **(10.3.20) of CoNF**: `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K) ≤ [K : ℚ]` together
  with the finiteness of `Γ_K`; the named class-field-theory input of the reconstruction;
* `RankStrictMonoInput` — **CoNF (10.3.7) / Shimizu Lemma 4f.2**: `r_ℓ(K) < r_ℓ(L)` for a nontrivial
  finite extension `L/K` with a complex prime;
* `eq_bot_of_rankGamma_eq` — Shimizu's Prop. 4f.5 rank step.

## References

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Ch. X §10.3, Ch. XII §12.1–2;
S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

open scoped Pointwise

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]

/-! ## The torsion submodule and the torsion-free quotient -/

/-- **The `ℤ_ℓ`-torsion submodule of the ℓ-adic abelianisation** `G_K^{ab,(ℓ)}` — Shimizu's
`(G_K^{ab,(ℓ)})_{\tor}`.  That it is closed under the `ℤ_ℓ`-action is the statement that a
`ℤ_ℓ`-multiple of a torsion element is torsion; `Submodule.torsion` provides it. -/
noncomputable abbrev GammaTorsion (ℓ : ℕ) [Fact ℓ.Prime] :
    Submodule (PadicInt ℓ) (Additive (Gamma K K' ℓ)) :=
  Submodule.torsion (PadicInt ℓ) (Additive (Gamma K K' ℓ))

/-- **Shimizu's `Γ_K = G_K^{ab,(ℓ),/\tor}`**: the torsion-free quotient of the ℓ-adic
abelianisation, as a `ℤ_ℓ`-module. -/
noncomputable abbrev GammaTF (ℓ : ℕ) [Fact ℓ.Prime] : Type _ :=
  Additive (Gamma K K' ℓ) ⧸ GammaTorsion (K := K) (K' := K') ℓ

/-- Membership in the torsion submodule, unfolded: an element of the ℓ-adic abelianisation is
torsion iff it is annihilated by a non-zero-divisor of `ℤ_ℓ`. -/
theorem mem_gammaTorsion_iff (x : Additive (Gamma K K' ℓ)) :
    x ∈ GammaTorsion (K := K) (K' := K') ℓ ↔
      ∃ a : nonZeroDivisors (PadicInt ℓ), a • x = 0 :=
  Submodule.mem_torsion_iff x

/-- **A power of `ℓ` kills a torsion element**: for `ℤ_ℓ` the non-zero-divisors are precisely the
elements of the form `unit * ℓ ^ n`, so every torsion element is annihilated by some `ℓ ^ n`.  (This
is the direction of the description of the torsion that is used in practice; the converse is
`Submodule.mem_torsion_iff`.) -/
theorem mem_gammaTorsion_of_pow_smul_eq_zero {n : ℕ} {x : Additive (Gamma K K' ℓ)}
    (h : (ℓ : PadicInt ℓ) ^ n • x = 0) : x ∈ GammaTorsion (K := K) (K' := K') ℓ :=
  (Submodule.mem_torsion_iff x).mpr
    ⟨⟨(ℓ : PadicInt ℓ) ^ n,
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (pow_ne_zero n (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero))⟩, h⟩

/-- **`Γ_K` is torsion-free.** -/
instance instIsTorsionFreeGammaTF :
    Module.IsTorsionFree (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) :=
  inferInstance

/-- The quotient map `G_K^{ab,(ℓ)} → Γ_K`. -/
noncomputable def gammaTFMk : Additive (Gamma K K' ℓ) →ₗ[PadicInt ℓ]
    GammaTF (K := K) (K' := K') ℓ :=
  (GammaTorsion (K := K) (K' := K') ℓ).mkQ

@[simp] theorem gammaTFMk_apply (x : Additive (Gamma K K' ℓ)) :
    gammaTFMk (K := K) (K' := K') (ℓ := ℓ) x = (GammaTorsion (K := K) (K' := K') ℓ).mkQ x := rfl

/-- The quotient map is surjective. -/
theorem gammaTFMk_surjective :
    Function.Surjective (gammaTFMk (K := K) (K' := K') (ℓ := ℓ)) :=
  (GammaTorsion (K := K) (K' := K') ℓ).mkQ_surjective

/-- The `ℤ_ℓ`-action on `Γ_K` is injective: `Γ_K` is torsion-free. -/
theorem eq_zero_of_smul_eq_zero_gammaTF {a : PadicInt ℓ} (ha : a ≠ 0)
    {x : GammaTF (K := K) (K' := K') ℓ} (h : a • x = 0) : x = 0 :=
  (smul_eq_zero.mp h).resolve_left ha

/-- Torsion-freeness in multiplicative form: a non-trivial natural power of an element of `Γ_K`
can only be trivial if the element is. -/
theorem eq_one_of_pow_eq_one_gammaTF {n : ℕ} (hn : n ≠ 0)
    {x : GammaTF (K := K) (K' := K') ℓ} (h : n • x = 0) : x = 0 := by
  have hn' : (n : PadicInt ℓ) ≠ 0 := by
    exact_mod_cast hn
  rw [← Nat.cast_smul_eq_nsmul (PadicInt ℓ) n x] at h
  exact eq_zero_of_smul_eq_zero_gammaTF hn' h

/-! ## Finite generation and freeness -/

/-- **`Γ_K` is a finitely generated `ℤ_ℓ`-module**: the class-field-theory input of the
reconstruction (see `RankFormulaInput`). -/
theorem moduleFinite_gammaTF (h : Module.Finite (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ)) :
    Module.Finite (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) := h

/-- **`Γ_K` is a free `ℤ_ℓ`-module of finite rank.**  A finitely generated torsion-free module over
a principal ideal domain is free (`Module.free_of_finite_type_torsion_free`), and `ℤ_ℓ` is a
discrete valuation ring, hence a PID. -/
theorem moduleFree_gammaTF (h : Module.Finite (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ)) :
    Module.Free (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := PadicInt ℓ)
    (M := GammaTF (K := K) (K' := K') ℓ)
  exact Module.free_of_finite_type_torsion_free hs

/-- **`Γ_K` is a finite free `ℤ_ℓ`-module**, in the bundled form: `Module.Finite` and
`Module.Free` together, which is the statement of item (1) of the deliverable. -/
theorem moduleFinite_moduleFree_gammaTF
    (h : Module.Finite (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ)) :
    Module.Finite (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) ∧
      Module.Free (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) :=
  ⟨h, moduleFree_gammaTF h⟩

/-! ## Shimizu's rank `r_ℓ(K)` -/

/-- **Shimizu's `r_ℓ(K)`**: the `ℤ_ℓ`-rank of `Γ_K = G_K^{ab,(ℓ),/\tor}`, i.e. the rank of the
torsion-free quotient of the ℓ-adic abelianisation of `G_K`.  Equivalently
`rank_{ℤ_ℓ} Hom_{cts}(Γ_K, ℤ_ℓ)`.

Because `Γ_K` is a *free* `ℤ_ℓ`-module of finite rank (`moduleFree_gammaTF`), `Module.finrank`
computes exactly this rank. -/
noncomputable def rankGamma (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] : ℕ :=
  Module.finrank (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ)

/-- **`r_ℓ(L)` for a finite extension `L ⊆ K'` of `K`**: the rank of the torsion-free quotient of
the ℓ-adic abelianisation of `Gal(K'/L)`, computed in the same separable closure `K'`. -/
noncomputable def rankGammaLevel (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] (L : IntermediateField K K')
    [NumberField ↥L] [IsGalois ↥L K'] : ℕ :=
  rankGamma ↥L K' ℓ

/-- `rankGammaLevel` restricted to a finite Galois number-field level is `rankGamma` of that
field. -/
theorem rankGammaLevel_eq_rankGamma (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] (L : IntermediateField K K')
    [NumberField ↥L] [IsGalois ↥L K'] :
    rankGammaLevel K K' ℓ L = rankGamma ↥L K' ℓ := rfl

/-! ## The named inputs of the abelianised route: CoNF (10.3.20) and Lemma 4f.2 -/

/-- **(10.3.20) of CoNF** — the rank formula for the torsion-free ℓ-adic abelianisation,
*assumed as an input* (this is the class-field-theory input of the whole argument).

Shimizu (arXiv:2009.10431, §4) writes it as `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K) ≤ [K : ℚ]`, where
`δ_ℓ(K) ≥ 0` is the Leopoldt defect; `δ` is a parameter here because the defect itself is not
formalised in this development.  The first field records that `Γ_K` is a finitely generated
`ℤ_ℓ`-module (CoNF Ch. X §10.3: `Γ_K` is `ℤ_ℓ`-free of rank `r_ℓ(K)`) — this is what makes the
rank finite in the first place, and it is here rather than as a separate hypothesis so that
`rankGamma` is *the* rank rather than an a priori possibly-degenerate number. -/
structure RankFormulaInput (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ δ : ℕ) [Fact ℓ.Prime] : Prop where
  /-- `Γ_K` is a finitely generated `ℤ_ℓ`-module -/
  finite : Module.Finite (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ)
  /-- `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K)` -/
  formula : rankGamma K K' ℓ = rComplex K + 1 + δ
  /-- `r_ℓ(K) ≤ [K : ℚ]` -/
  bound : rankGamma K K' ℓ ≤ Module.finrank ℚ K

/-- The finiteness of `Γ_K` extracted from `RankFormulaInput`. -/
theorem RankFormulaInput.moduleFinite {δ : ℕ} (h : RankFormulaInput K K' ℓ δ) :
    Module.Finite (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) := h.finite

/-- `Γ_K` is a finite free `ℤ_ℓ`-module of rank `r_ℓ(K)`, from `RankFormulaInput`. -/
theorem RankFormulaInput.moduleFree {δ : ℕ} (h : RankFormulaInput K K' ℓ δ) :
    Module.Free (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) :=
  moduleFree_gammaTF h.finite

/-- **CoNF (10.3.7), Shimizu's Lemma 4f.2** — *assumed as an input*.

If `L/K` is a nontrivial finite extension of number fields and `L` has a complex prime, then
`r_ℓ(K) < r_ℓ(L)`.  Shimizu proves it from `r_ℂ(K) < r_ℂ(L)` and the monotonicity of the Leopoldt
defect (CoNF (10.3.7)). -/
def RankStrictMonoInput (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    [IsGalois ↥L K'],
    L ≠ ⊥ → (∃ v : NumberField.InfinitePlace ↥L, NumberField.InfinitePlace.IsComplex v) →
      rankGamma K K' ℓ < rankGammaLevel K K' ℓ L

/-- **The ranks distinguish fields** (Shimizu's Prop. 4f.5, from Lemma 4f.2): if `L / K` is a finite
extension of number fields with a complex prime and the ℓ-ranks of `K` and `L` agree, then `L = K`.
This is the form in which the rank computation of Prop. 4f.5 is consumed. -/
theorem eq_bot_of_rankGamma_eq (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime]
    (h : RankStrictMonoInput K K' ℓ)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    [IsGalois ↥L K']
    (hc : ∃ v : NumberField.InfinitePlace ↥L, NumberField.InfinitePlace.IsComplex v)
    (hL : rankGammaLevel K K' ℓ L = rankGamma K K' ℓ) : L = ⊥ := by
  by_contra hne
  exact absurd hL (ne_of_gt (h L hne hc))

end NK.Reconstruct
