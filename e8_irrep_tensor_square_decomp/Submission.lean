import ChallengeDeps
import Submission.Helpers
import Submission.Enveloping
import Submission.EnvelopingModule
import Submission.E8Weights
import Submission.WordSpan
import Submission.WeightIndependence
import Submission.TriangularSpan
import Submission.E8RootSystem
import Submission.E8Numerics
import Submission.E8Engine
import Submission.IsotypicCount
import Submission.Sl2Span
import Submission.StarModule
import Submission.StarDerivation
import Submission.StarQuotient
import Submission.E8Casimir
import Submission.HWTTensor
import Submission.E8Character
import Submission.E8Orbit
import Submission.E8Enum
import Submission.E8Support
import Submission.E8Integrable
import Submission.E8PBW
import Submission.E8NullVector
import Submission.E8LocallyNilpotent
import Submission.E8WeightSpaces
import Submission.E8WInvariance
import Submission.E8Freudenthal
import Submission.E8Multiplicity
import Submission.E8Finrank
import Submission.E8Tensor
import Submission.E8TensorBound
import Submission.E8FreudenthalGen
import Submission.VermaNonzero
import Submission.VermaModel
import Submission.VermaWeight
import Submission.WeylWeights
import Submission.WeylRoots
import Submission.WeylReflect
import Submission.WeylBall
import Submission.WeylChamber
import Submission.E8TensorChar
import Submission.E8NoKernel
import Submission.E8KostantConv
import Submission.E8WCFC
import Submission.E8WCFD
import Submission.E8WCFE
import Submission.E8MtabUnitri
import Submission.E8WCFW
import Submission.E8WCFM
import Submission.E8Klimyk
import Submission.E8Trunc
import Submission.E8Num40
import Submission.E8Ncard
import Submission.E8SuppBound
import Submission.E8PRV

open LeanEval.RepresentationTheory
open scoped TensorProduct

namespace Submission

/-!
# SESSION 10: the Freudenthal uniqueness theorem is PROVED; the missing input is now isolated

**New file `Submission/E8Character.lean` (sorry-free, imported here).**  Everything combinatorial
that the character theory of `e₈` needs, and the uniqueness theorem itself:

* `coords γ = A⁻¹γ` (integral, since `det E₈ = 1`), `posCon γ` (`γ ∈ ℕΦ⁺`, decided by the
  non-negativity of `coords`), `htOf γ = ∑ (A⁻¹γ)ᵢ = ⟪γ, ρ⟫`, with additivity, positivity on the
  cone, the characterisation `posCon γ ↔ ∃ n : ℕ⁸, γ = A·n`, and `alpha i` with
  `posCon_alpha`, `htOf_alpha`;
* **`dc`**, the dominant conjugate: the "reflect at the first negative coordinate until dominant"
  algorithm (`dcList`, `dcListAux`, `dc`), with the facts that matter --
  `dc_dominant`, `dc_mem_WConj` (with the *explicit list* of simple reflections),
  **`dc_sub_posCon : posCon (dc v - v)`** (each step adds a positive multiple of a simple root --
  this is what replaces the whole Weyl-group/dominant-chamber theory), `dc_idem`,
  `dc_eq_self_of_dominant`, `htOf_dc_le`, `htOf_dc_eq_iff`;
* `Bint ν = ⟪ν+ρ, ν+ρ⟫` (integral), `brk μ j = ⟪μ, pR j⟫`, `posCon_pR`, `htOf_pR`;
* **`no_dominant_singular_weight'`**: the Key Lemma, restated in the integral form
  (`Bint ν ≠ Bint λ`), derived from the committed commons lemma
  `Commons.Algebra.Lie.SerreConstruction.no_dominant_singular_weight` by casting through
  `E8q_inv`;
* **`eq_of_freudenthal`** -- **the uniqueness theorem**:

  > if `m, m' : (Fin 8 → ℤ) → ℚ` satisfy (a) `m lam = m' lam = 1`, (b) the support bound
  > `lam - v = 0 ∨ posCon (lam - v)` whenever `m v ≠ 0` (resp. `m' v ≠ 0`), (c) invariance under
  > the dominant conjugate `m (dc v) = m v` (resp. `m'`), and (d) Freudenthal's recursion
  > `(Bint lam - Bint ν) * m ν = 2 * ∑_{α>0} ∑_{k ≥ 1} ⟪ν+kα, α∨⟫ * m (ν + kα)` on the dominant
  > weights `ν ≠ lam` of the support cone (truncated at `k = (htOf (lam - ν)).toNat`, where the
  > summands vanish), then `m = m'`.

  Proof: strong induction on `htOf (lam - ν)` over dominant weights.  At a dominant `ν` in the
  support cone, either `ν = lam` (both values are `1`) or the Key Lemma makes the recursion's
  coefficient non-zero and the recursion expresses `m ν` through the values at `ν + kα ≻ ν`; those
  are handled by (c) (`δ η = δ (dc η)`) plus the support bound (`dc_sub_posCon` gives the strict
  height drop, and `lam - dc η ∉ ℕΦ⁺ ∪ {0}` forces both functions to vanish).  Arbitrary weights
  reduce to dominant ones by (c).

**This closes the *combinatorial* half of the character theory**: the uniqueness theorem no longer
needs the Weyl group to be generated, `W`-sums, or the "saturated set" theory.  Only three
hypotheses have to be supplied for the concrete multiplicities.

## The precise remaining gap (important!)

For `L(λ)` with `λ = ω₁ + ω₈` we must supply:

1. **(a)+(b)**: easy -- the `λ`-weight space of the Verma model is one-dimensional
   (`Submission.VermaWeight.Wm_zero_eq`) and every weight of a highest weight module is
   `λ - ∑ nᵢαᵢ`.
2. **(d) Freudenthal's recursion**: the trace argument of the roadmap §2 above.  Note it needs
   *no* finiteness of the module, only finite-dimensional weight spaces, `Ω` acting by the scalar
   `(λ,λ+2ρ)_κ`, and the support bound -- all available for `L(λ)` (whose weight spaces are
   quotients of the Verma weight spaces).  So a proof of `hd` for `L(λ)` is *independent* of the
   gap below.
3. **(c) `W`-invariance of the multiplicities** -- the one genuinely missing input.  The elementary
   route, worked out this session:
   * *integrability*: `fᵢ^{λᵢ+1}` acts by `0` on `L(λ)`.  Indeed `uᵢ := fᵢ^{λᵢ+1} v` is killed by
     every `SerreE j` (`j ≠ i`: `[e_j, f_i] = 0`; `j = i`: the `𝔰𝔩₂` identity
     `e f^{λ_i+1} v = 0`), so it is a primitive vector; the submodule `U(g)uᵢ` is therefore a
     highest weight module of highest weight `μᵢ = λ - (λᵢ+1) αᵢ`, whose weights are `⪯ μᵢ`, so it
     misses `v` (of weight `λ ≻ μᵢ`); hence it is proper, hence contained in the unique maximal
     submodule `N`, hence `fᵢ^{λᵢ+1} • vbar = 0`, and by commutativity (`L(λ)` is generated by `v`)
     `fᵢ^{λᵢ+1} = 0` on all of `L(λ)`.  This is exactly "integrability".
   * then every weight vector spans a *finite-dimensional* `𝔰𝓵₂⁽ⁱ⁾`-module (`eᵢ` is locally
     nilpotent by the cone bound, `fᵢ^{λᵢ+1} = 0`), so `Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm`
     applied to the (finite, once the support is known) `αᵢ`-string gives
     `dim L(λ)_ν = dim L(λ)_{sᵢν}`; the same argument at the level of *sets* (using only `eᵢ`
     locally nilpotent, `fᵢ^{λᵢ+1}=0`) shows `sᵢν` is a weight whenever `ν` is, hence the support is
     contained in `W·{dominant ≤ λ}` -- **finite**, so `L(λ)` is finite-dimensional.
   * the only slightly non-elementary ingredient is "a cyclic module generated by a primitive vector
     is a highest weight module" (`U(g) = U(n⁻)U(b)` by PBW, `U(b)u = ℂu`), needed in the first
     bullet.

So the remaining work is: (i) formalise the integrability argument above in the concrete
`⋆`-model `V = A/J`, (ii) the trace argument for (d), (iii) the two certification computations
(7 dominant multiplicities for `L(ω₁+ω₈)`, 40 characters for the tensor square), (iv) the tensor
square assembly.

**Weyl's complete reducibility is now DONE**, in both the forms the tensor-square step needs:
`Commons.Algebra.Lie.CompleteReducibility.isCompl_of_isKilling` (every Lie submodule of a
finite-dimensional module over a Lie algebra with non-degenerate Killing form has a Lie-submodule
complement) and `Commons.Algebra.Lie.CompleteReducibility.isSemisimpleModule_enveloping`
(`IsSemisimpleModule (UniversalEnvelopingAlgebra K L) M` for the canonical transported module
structure).  Both were proved and committed during this session; the latter file also contains the
`ofEnveloping`/`toEnveloping`/`lieModuleSubmoduleEquiv` dictionary between `e₈`-submodules and
`U(e₈)`-submodules that the final assembly will use.

The `Submodule`-level form of this theorem gives back `isCompl` for the *Lie* submodules of
`V ⊗ V`; combined with the classical bijection between `U(e₈)`-submodules and `e₈`-submodules and
`Commons.RingTheory.SimpleModule.isotypicComponents_eq_range_of_iSupIndep_isIsotypicOfType_of_isSemisimpleModule`
it turns the tensor square into a direct sum of isotypic components.


-/

/-!
# SESSION 7: THE GATE IS `IsKilling ℂ e₈`, AND THE CHARACTER THEORY IS NOW FULLY WORKED OUT

## 1. The single most important discovery: Mathlib's `IsKilling` chapter does the heavy lifting

Mathlib already contains a complete theory of **Lie algebras with non-degenerate Killing form**,
which is precisely the "missing chapter" we were going to have to build:

* `LieAlgebra.IsKilling R L` (`Mathlib.Algebra.Lie.Killing`) — the typeclass "the Killing form is
  non-singular".  `IsKilling.killingForm_nondegenerate`, `IsKilling.instSemisimple`,
  `IsKilling.ker_killingForm_eq_bot`, `LieIdeal.isCompl_killingCompl`, …;
* `Mathlib.Algebra.Lie.CartanCriterion`: **`LieAlgebra.HasTrivialRadical.instIsKilling`** — Cartan's
  criterion, `HasTrivialRadical R L → IsKilling R L` (and `HasTrivialRadical ↔ IsKilling` over a
  field of characteristic zero, plus `IsSemisimple → HasTrivialRadical` in `Semisimple/Basic`).
  So `IsSimple → IsSemisimple → HasTrivialRadical → IsKilling` is a *pipeline*.
* `Mathlib.Algebra.Lie.Weights.Killing` (`LieAlgebra.IsKilling` namespace): the restriction of the
  Killing form to a Cartan subalgebra is non-degenerate (`traceForm_cartan_nondegenerate`),
  **`cartanEquivDual`** (`𝔥 ≃ₗ 𝔥*`), **`coroot α`**, `root_apply_coroot` (`α (coroot α) = 2`),
  `isCompl_ker_weight_span_coroot`, **`lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg`**
  (`⁅e,f⁆ = κ(e,f) • (cartanEquivDual H).symm α` — *the coroot identity*, with no normalisation
  choice!), **`exists_isSl2Triple_of_weight_isNonZero`** (an `sl₂`-triple in every root space),
  **`finrank_rootSpace_eq_one`**, `span_weight_eq_top`, `iInf_ker_weight_eq_bot`,
  `sl2SubalgebraOfRoot`, `IsSl2Triple.h_eq_coroot`,
  `lieIdeal_eq_inf_cartan_sup_biSup_rootSpace`;
* `Mathlib.Algebra.Lie.Weights.RootSystem`: `chainTopCoeff`, `chainBotCoeff`, `chainLength`,
  `rootSpace_zsmul_add_ne_bot_iff`, **`exists_mem_rootSpace_lie_ne_zero`**, the abstract root
  system `H.root`, `IsCrystallographic`, `IsReduced`, `chainTopCoeff_add_chainBotCoeff`;
* `Mathlib.Algebra.Lie.Weights.Chain` (`chainTopCoeff`, `chainBotCoeff` for a general Lie module),
  `Mathlib.Algebra.Lie.Weights.IsSimple`, `Mathlib.Algebra.Lie.Sl2`
  (`IsSl2Triple`, `HasPrimitiveVectorWith`, `exists_nat`, `exists_hasPrimitiveVectorWith`).

**Consequence.**  The critical path was a *single* e₈-specific theorem,

> `e8_isKilling : LieAlgebra.IsKilling ℂ (LieAlgebra.e₈ ℂ)` —

**and it is now PROVED and committed**: `Commons.Algebra.Lie.SerreConstruction.e8_isKilling`
(`Submission/Commons/Algebra/Lie/SerreConstruction/e8_isKilling.lean`, sorry-free, builds).  The
same file also registers the instance `e8_moduleFinite : Module.Finite ℂ (e₈ ℂ)` and provides
`exists_e8W_inf_ne_bot`, `e8W_zero_eq_span_SerreH` (the zero weight space is spanned by the
`SerreH i`), `reflAutList`, `reflAutList_maps_W`, `reflAutList_e8W` and `W_alpha_eq_span`.
Together with `Commons.Algebra.Lie.SerreConstruction.weight_norm_two` (every nonzero weight of the
adjoint representation of `e₈` is a root), **the entire structural half of the project is done**:
`haveI := e8_isKilling` gives `LieAlgebra.IsSemisimple ℂ (e₈ ℂ)`,
`LieAlgebra.HasTrivialRadical ℂ (e₈ ℂ)`, `IsKilling.killingForm_nondegenerate`,
`IsKilling.traceForm_cartan_nondegenerate`, `IsKilling.cartanEquivDual`, `IsKilling.coroot`,
`IsKilling.exists_isSl2Triple_of_weight_isNonZero` (an `sl₂`-triple in every root space),
`IsKilling.finrank_rootSpace_eq_one`, `IsKilling.lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg`
(the coroot identity), `IsKilling.span_weight_eq_top`, `IsKilling.iInf_ker_weight_eq_bot`,
`IsKilling.lieIdeal_eq_inf_cartan_sup_biSup_rootSpace` (a Lie ideal is its Cartan part plus root
spaces — i.e. `e₈` is *simple*), and the `𝔰𝔩₂`-chain theory of
`Mathlib.Algebra.Lie.Weights.{Chain,RootSystem}`.

**So, going forward, every structural ingredient of the representation theory is a Mathlib
theorem.**  The remaining work is purely representation-theoretic:

(i) package `𝔥 := e8W 0 = span{SerreH i}` as a `LieSubalgebra` with `H.IsCartanSubalgebra` and
`IsTriangularizable ℂ H (e₈ ℂ)`, so that the `IsKilling` API applies;
(ii) the Casimir `Ω ∈ U(e₈)` of the (now non-degenerate) Killing form — the centrality half is
already in the commons as `Commons.Algebra.Lie.Casimir.lie_commute` — and `Ω · v = (λ,λ+2ρ) v` on a
highest weight vector;
(iii) Freudenthal's formula (§2) and its uniqueness theorem (§3, now complete);
(iv) `W`-invariance of weight multiplicities (`Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm`
plus `IsKilling.exists_isSl2Triple_of_weight_isNonZero`);
(v) the certified computation of §4.

Once it is available, every structural ingredient of the representation theory
(Casimir/coroots/`sl₂`-triples/Weyl-group invariance) is a *Mathlib* theorem, and the remaining
work is representation-theoretic rather than structural.  The suggested proof route (routed to the
fleet together with the statement) is:

1. weights of the adjoint representation of `e₈` are `{0} ∪ Φ` with `dim g_0 = 8`
   (`e8_zero_weightSpace_finrank`), `dim g_α = 1` for `α ≠ 0`
   (`e8_root_weightSpace_finrank_eq_one`), `{SerreH i}` independent (`e8_H_linearIndependent`);
2. a nonzero weight reflects (via `e8_weightSpace_ascent`, iterated) to a dominant weight, which is
   `θ` (`e8_dominant_weight_eq_zero_or_theta`), the form `μ ↦ μᵀA⁻¹μ` being reflection-invariant
   (`qform_reflect`), so the weights are the 240 roots (`exists_finset_e8_roots`);
3. hence `killingForm (SerreH i) (SerreH j) = ∑_{α ∈ Φ} α_i α_j = 60 · E8 i j`, an invertible
   matrix, so `κ|_𝔥` is non-degenerate;
4. `[g_α, g_{-α}] ≠ 0` for every root, reducing to simple roots by conjugating with the reflection
   automorphism `reflAut i` (`e8_weightSpace_reflect_finrank.lean`: `reflAut_H`, `maps_W`);
5. `κ` is block diagonal, its `𝔥`-block and each `g_α ⊕ g_{-α}`-block are non-degenerate, so `κ`
   is non-degenerate — i.e. `IsKilling`.

## 2. THE FREUDENTHAL FORMULA — complete derivation (verified numerically), ready to formalise

Let `L` be a Lie algebra over a field of characteristic `0` with an invariant non-degenerate
symmetric form `κ`, `{b_i}` a basis and `{b'_i}` the `κ`-dual basis
(`κ b_i b'_j = δ_ij`, `κ b'_i b_j = δ_ij`), and let
`Ω = ∑_i b_i b'_i ∈ U(L)` be the **Casimir element**; `Ω` is central
(the commons lemma `Commons.Algebra.Lie.Casimir.lie_commute`, requested this session; the proof
uses `y = ∑_i κ y (b'_i) • b_i` and `y = ∑_i κ y (b_i) • b'_i` and then a `TensorProduct` argument).

Let `V` be a module with a weight decomposition for a Cartan `𝔥 ⊆ L` with **finite-dimensional
weight spaces** `V_ν`, on which `Ω` acts by the scalar `c_λ ∈ K` (true for a highest weight module
of highest weight `λ`, where `c_λ = (λ, λ + 2ρ)_κ`).

Write `y_α` for the element of `g_{-α}` with `κ (x_α) (y_α) = 1`.  Then:

* **(coroot identity)** `[x_α, y_α] = h_α` where `h_α` is the `κ`-dual of the weight `α`
  (this holds for *any* invariant form and *any* choice of `x_α`, with NO normalisation); proof:
  for `h_μ` the dual of `μ`, `κ ([x_α,y_α], h_μ) = -κ (y_α, [x_α,h_μ]) = α(h_μ) κ (x_α,y_α) = (α,μ)_κ`
  and also `= κ (c_α h_α, h_μ) = c_α (α,μ)_κ`, whence `c_α = 1`;
* **(the trace identity)** `tr_{V_ν}(Ω) = c_λ · dim V_ν`, and expanding `Ω` in the root
  decomposition gives
  `tr_{V_ν}(Ω) = (ν,ν)_κ dim V_ν + ∑_{α>0} (2 · tr_{V_ν}(y_α x_α) + ν(h_α) dim V_ν)`;
* **(the string recursion)** `D^{(α)}_ν := tr_{V_ν}(y_α x_α)` satisfies
  `D^{(α)}_ν - D^{(α)}_{ν+α} = (ν+α, α)_κ · dim V_{ν+α}` (because
  `x_α y_α = y_α x_α + h_α`), hence `D^{(α)}_ν = ∑_{k≥1} (ν+kα, α)_κ dim V_{ν+kα}`
  (a *finite* sum for a highest weight module, since the weights are `≤ λ`).

Adding the pieces gives **Freudenthal's formula**
```
((λ+ρ, λ+ρ)_κ - (ν+ρ, ν+ρ)_κ) · dim V_ν = 2 ∑_{α>0} ∑_{k ≥ 1} (ν+kα, α)_κ · dim V_{ν+kα}.
```
Note that this needs **no finiteness of `V`**, only finite-dimensional weight spaces, the scalar
action of `Ω` and the bound `supp ⊆ λ - ℕΦ⁺` (which makes the sums finite).  It therefore applies
directly to `L(ω₁+ω₈)`.

## 3. THE UNIQUENESS THEOREM — complete proof, ready to formalise

Let `λ ∈ Λ⁺` (dominant integral), and let `m : Λ → ℤ` satisfy
(a) `m λ = 1`;  (b) `m ν ≠ 0 ⟹ λ - ν ∈ ℕΦ⁺`;  (c) `W`-invariance `m (s_i ν) = m ν`;
(d) Freudenthal's identity of §2.  Then `m` is **unique**, hence (since the multiplicities of
`L(λ)` satisfy (a)–(d), by §2 plus `W`-invariance) `m` *is* the multiplicity function of `L(λ)`.

**Proof** (descending induction on `ht(λ-ν)`; suppose `d = m - m'` and `d` vanishes strictly
above `ν`).  The linearised Freudenthal identity reads
`((λ+ρ,λ+ρ) - (ν+ρ,ν+ρ)) d ν = 2 ∑_{α>0} ∑_{k≥1} (ν+kα,α) d (ν+kα)`.
* If the coefficient is non-zero, `d ν = 0`.
* If the coefficient vanishes (`ν` on the "Casimir sphere") and `ν ≠ λ`: then `ν + ρ = w(λ+ρ)` for
  some `w ≠ e` (both are strictly dominant up to the `W`-action), and the **key identity**
  `w^{-1} ν = λ + ∑_{α>0, wα<0} α` (from the standard formula `ρ - wρ = ∑_{α>0,w^{-1}α<0} α`) shows
  `λ - w^{-1}ν = -∑_{α>0,wα<0}α ∉ ℕΦ⁺`; by (b), `m(w^{-1}ν) = 0`, and by (c) `d ν = 0`.
  (This sidesteps the *false* "leading term" uniqueness argument recorded below: no `W`-summation
  over the 696729600 elements of `W` is ever needed, and only the eight simple reflections are used.)

**`W`-invariance of the multiplicities of `L(λ)`** (ingredient (c)): for a simpleroot `α_i`, the
`α_i`-string through a weight `ν` of `L(λ)` is *finite* (weights lie in `λ - ℕΦ⁺`, and the
`α_i`-coordinate of `λ - ν` cannot decrease past `-⟨λ,α_i∨⟩`), so the `𝔰𝔩₂(α_i)`-module it spans is
a direct sum of finite-dimensional irreducibles; the multiplicity of the eigenvalue `e` of `h_{α_i}`
is `∑_{j ≥ |e|, j ≡ e (2)} d_j`, symmetric in `e ↔ -e`, whence `dim V_ν = dim V_{s_iν}`.
In Lean: `Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm` (requested this session) plus the
`IsSl2Triple` / `exists_isSl2Triple_of_weight_isNonZero` of Mathlib.


### 3bis. The "singular weight" gap in §3 is CLOSED (key lemma proved this session)

The induction in §3 needs one extra input at a *singular* weight `ν`
(one with `(ν+ρ,ν+ρ) = (λ+ρ,λ+ρ)`, `ν ≠ λ`).  It is supplied by:

> **Key Lemma.**  Let `λ` be dominant integral and `ν` dominant with `λ - ν ∈ ℕΦ⁺ \ {0}`.
> Then `(ν+ρ,ν+ρ) ≠ (λ+ρ,λ+ρ)`.

*Proof.*  Write `μ := λ - ν = ∑ nᵢ αᵢ` with `nᵢ ≥ 0`, `μ ≠ 0`.  Because `ν` is dominant,
`νᵢ = λᵢ - ⟨μ, αᵢ∨⟩ ≥ 0`, so `⟨μ, αᵢ∨⟩ ≤ λᵢ`.  Hence
`(μ,μ) = ∑ᵢ nᵢ ⟨μ, αᵢ∨⟩ ≤ ∑ᵢ nᵢ λᵢ`.  On the other hand `(μ,ρ) = ∑ᵢ nᵢ` (as `⟨ρ,αᵢ∨⟩ = 1`,
`(αᵢ,αᵢ) = 2`) and `(μ,λ) = ∑ᵢ nᵢ λᵢ` (`A` symmetric), so `(μ, λ+ρ) = ∑ᵢ nᵢ(λᵢ+1)`; the
singularity `(ν+ρ,ν+ρ) = (λ+ρ,λ+ρ)` is equivalent to `2(μ, λ+ρ) = (μ,μ)`, whence
`(μ,μ) = 2∑ᵢ nᵢ(λᵢ+1) ≥ 2∑ᵢ nᵢ λᵢ + 2`.  Combining the two estimates gives
`∑ᵢ nᵢ λᵢ + 2 ≤ 0`, contradicting `λᵢ ≥ 0`, `nᵢ ≥ 0`, `∑ nᵢ ≥ 1`.  ∎

(Verified computationally too: for `λ = ω₁+ω₈` in `E₈` and all `286524` singular weights with
coefficients `≤ 7`, **none** is dominant, and for every singular weight the *dominant* conjugate
`ν⁺` satisfies `λ - ν⁺ ∉ ℕΦ⁺`; same check for `A₂`, `A₃` and several other `λ`.)

**Consequence — §3 is complete.**  Let `d = m - m'` and induct on `ht(λ-ν)`.  At a singular `ν ≠ λ`
with `λ - ν ∈ ℕΦ⁺`, let `ν⁺ = wν` be the dominant conjugate, so `ht(λ-ν⁺) ≤ ht(λ-ν)`.  Then either
* `λ - ν⁺ ∉ ℕΦ⁺`: then `d(ν) = d(ν⁺) = 0` by (b) and (c); or
* `λ - ν⁺ ∈ ℕΦ⁺`: then either `ν⁺ = λ` and `d(ν) = d(λ) = 0`, or (the Key Lemma) the recursion at
  `ν⁺` has a **non-zero** coefficient and involves only weights of strictly smaller `λ`-height,
  whence `d(ν⁺) = 0` by the induction hypothesis, and `d(ν) = 0` by (c).

So the only inputs are (a) `m λ = 1`, (b) `supp m ⊆ λ - ℕΦ⁺`, (c) `W`-invariance of `m`, and
(d) Freudenthal's identity — no boundedness or finiteness of the support is needed.

### 3quater. Status of the (non-Lean) character computation used to plan the certification

For `λ = ω₁+ω₈` the sub-dominant dominant weights were enumerated (solving `A n ≤ λ`, `n ≥ 0`,
which forces `n₃ ≤ 16` and hence is a tiny polytope): there are exactly **7** dominant weights `≤ λ`,
namely `λ`, `ω₂`, `2ω₈`, `ω₇`, `ω₁`, `ω₈`, `0`.  So the character of `L(ω₁+ω₈)` has at most seven
distinct non-zero dominant multiplicities, which is excellent news for the certification plan of
§4: the whole character is encoded by seven natural numbers together with `W`-invariance.

A python implementation of the §3 recurrence on the dominant weights (using `W`-invariance to
replace `m(ν+kα)` by `m((ν+kα)⁺)`, and `λ - (ν+kα) ∉ ℕΦ⁺ ⟹ m(ν+kα) = 0` as the stopping rule)
reproduces the known answers `dim L(θ) = 8`, `dim L(2ω₁) = 6` for `A₂` and `dim L(ω₁+ω₂+ω₃) = 64`
for `A₃`, so the algorithm itself is correct; but run naively for `E₈` it returns non-integral
multiplicities (`1/4`, `1/9`, …) for `λ = ω₁+ω₈`.  **There is therefore a bug (most likely in the
"reflect into the dominant chamber" routine, or in the handling of terms whose dominant conjugate
is not comparable with `λ`) to be found before the numbers can be trusted** — this is a pure
computation and does not affect the mathematics of §2/§3.  Once fixed, the expected output is
`dim L(ω₁+ω₈) = 779247` and (via §4) `40` constituents for the tensor square.

### 3ter. Commons lemmas that landed this session (all proved, verified)

* `Commons.Algebra.Lie.Casimir.lie_commute` — **the Casimir element `∑ᵢ bᵢ b'ᵢ` of a Lie algebra
  with a symmetric invariant bilinear form commutes with every element of the Lie algebra**
  (`Submission/Commons/Algebra/Lie/Casimir/lie_commute.lean`).  This is the `Omega` of §2.
* `Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm` — for endomorphisms `h e f` of a vector
  space over a field of characteristic `0` satisfying the `𝔰𝔩₂` relations, with `e` and `f` locally
  nilpotent, the `h`-eigenspaces at `μ` and `-μ` have the same dimension
  (`Submission/Commons/LinearAlgebra/End/sl2_eigenspace_finrank_symm.lean`).
  This is ingredient (c) of §3: applied to the `𝔰𝔩₂`-triples `exists_isSl2Triple_of_weight_isNonZero`
  of Mathlib it gives `W`-invariance of the weight multiplicities of `L(λ)`.

## 3quinquies. Immediate next steps (the structural half is DONE)

The gateway `e8_isKilling` is proved, so the concrete next steps -- in order -- are:

1. **Cartan subalgebra.**  `𝔥 := e8W 0` as a `LieSubalgebra` with `H.IsCartanSubalgebra`
   (requested: `Commons.Algebra.Lie.SerreConstruction.e8W_zero_isCartan`; `e8W_zero_eq_span_SerreH`
   already identifies it with `span{SerreH i}`) and the `IsTriangularizable ℂ H (e₈ ℂ)` instance, so
   that `LieAlgebra.IsKilling.{cartanEquivDual, coroot, lie_eq_smul_of_mem_rootSpace, ...}` apply.
2. **Casimir.**  Take the Killing form (`killingForm ℂ (e₈ ℂ)`, non-degenerate by `e8_isKilling`),
   a basis `b` of `e₈` and the dual basis `b'`; the centrality of `Ω = ∑ bᵢ b'ᵢ` is already the
   commons lemma `Commons.Algebra.Lie.Casimir.lie_commute`.  Then compute `Ω · v` on a highest weight
   vector using the root decomposition (`IsKilling` gives one-dimensional root spaces and the root
   vectors) and the coroot identity, obtaining `Ω · v = (λ, λ+2ρ) · v`; since `Ω` is central and the
   module is generated by `v`, `Ω` acts by that scalar everywhere.
3. **Freudenthal.**  Formalise §2 (per-weight trace of `Ω` on `V_ν`, the string recursion for
   `D^{(α)}_ν = tr_{V_ν}(y_α x_α)`), giving Freudenthal's identity for `L(λ)` (note: no
   finite-dimensionality of `L(λ)` is needed, only finite-dimensional weight spaces and the support
   bound `supp ⊆ λ - ℕΦ⁺`).
4. **`W`-invariance.**  `Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm` applied to the
   `𝟙sl₂`-triples `IsKilling.exists_isSl2Triple_of_weight_isNonZero` gives
   `dim V_ν = dim V_{sᵢν}`.
5. **Uniqueness + certification.**  §3 + §3bis give uniqueness; the character of `L(ω₁+ω₈)` is then
   determined by the seven dominant multiplicities of §3quater, so the certification computation is
   *small*: it suffices to enter the seven numbers (well, the whole character is `m(ν⁺)` for the
   dominant conjugate `ν⁺`) and verify (a)-(d).
6. **Tensor square.**  §4.

## 4. THE TENSOR SQUARE — plan for `(isotypicComponents U (L ⊗ L)).ncard = 40`

Let `χ_λ` be the (now certified) formal character of `L(λ)`, a function `Λ → ℕ` of finite support.
1. `χ_{L⊗L}(ν) = ∑_{ν₁+ν₂=ν} χ_λ(ν₁) χ_λ(ν₂)` (finite computation).
2. For each dominant `μ`, the multiplicity of `L(μ)` in `L ⊗ L` is
   `c_μ = ∑_{w ∈ W} (-1)^{l(w)} χ_{L⊗L}(μ + ρ - wρ)`
   (Brauer/Klimyk — a consequence of `χ_μ · A_ρ = A_{μ+ρ}` and the triangularity of the character
   matrix, i.e. of `c_μ = [χ_{L⊗L} · A_ρ : e^{μ+ρ}]`).
   Only the finitely many `w` with `μ + ρ - wρ ∈ supp χ_{L⊗L}` contribute; `w ↦ wρ` is injective,
   and `(-1)^{l(w)} = (-1)^{negCount(wρ)}` where `negCount` is the length function already
   implemented in `Submission.WeylReflect`.  So the whole computation is finite and elementary.
3. `V ⊗ V` is completely reducible (`IsSemisimpleModule`), so
   `Commons.RingTheory.SimpleModule.isotypicComponents_eq_range_of_iSupIndep_isIsotypicOfType_of_isSemisimpleModule`
   turns the decomposition into `ncard = #{μ : c_μ ≠ 0} = 40`.
   Complete reducibility comes from the Casimir: the kernel of the Casimir operator on a module with
   a non-degenerate invariant form gives an invariant complement.

**Certification.**  The character `χ_λ` itself will be entered as literal data and *certified* by
verifying (i) `m λ = 1`, (ii) the support condition, (iii) `W`-invariance, and (iv) Freudenthal's
identity — all as finite `decide`/`native_decide` computations — and then invoking §3's uniqueness.
(The size of the support is the main engineering risk of the whole project; splitting the
verification into per-weight lemmas and/or using `Array`-based `native_decide` computations is the
way to manage it.)
-/

/-!
# SESSION 6: the Weyl group of `E₈` (the road to `dim L(ω₁+ω₈) = 779247`)

Two new sorry-free files (both imported here), completing the *Weyl group* half of Stage 4:

**`Submission/WeylRoots.lean`** (`namespace Submission.WeylRoots`).  A weight `v : Fin 8 → ℤ` is a
vector in the `ω`-basis (`v j = ⟨v, α_j∨⟩`, cf. `Submission.WeylWeights`); a *root* is stored by its
**`d`-coordinates** `d j = ⟨ω_j, α∨⟩`, which makes the Cartan pairing integral and computable:
`⟨v, α∨⟩ = ∑ j, v j * d j` (`pair`), and `α > 0 ↔ 0 < ∑ j, d j`.  The reflection acts on the
`d`-coordinates by `rref i d = d - (∑ k, A i k * d k) • eᵢ` where `eᵢ = Pi.single i 1` is the
`d`-coordinate vector of `αᵢ`.  Contents: the literal lists `rootsD` (240 roots) and `posRootsD`
(120 positive roots), `rootsD_nodup`, `posRootsD_nodup`, `RD_card = 240`, `PD_card = 120`.
(These literal lists are the image of `Submission.E8RootSystem.rootsAll/posRootList` under
`(r, αⱼ) ↦ ⟨r, αⱼ∨⟩`, computed from `dotInt r (simpleRoot j) / 4` followed by the inverse Cartan
matrix; the data was generated deterministically and verified in Python.)

**`Submission/WeylReflect.lean`** (`namespace Submission.WeylReflect`).  The Weyl group action:
* `pair_sub_right`, `pair_smul_e`, `pair_neg`, `pair_e`, `pair_rref`, and
  **`pair_sref`**: `⟨sᵢ v, α∨⟩ = ⟨v, (sᵢα)∨⟩` (the Cartan pairing is `W`-invariant);
* `cval i d = (A · d) i`, `cval_rref` (`cval i (rref i d) = -cval i d`),
  **`rref_involutive`** (`rref i` is an involution of the root lattice);
* `e_mem_PD` (`αᵢ ∈ Φ⁺`), `neg_e_notMem_PD` (`-αᵢ ∉ Φ⁺`),
  `rref_mem_rootsD` (`rref i` permutes the 240 roots, proved by 8 separate `decide` lemmas — a
  single `fin_cases i <;> decide` exhausts memory),
  **`PD_image_rref`**: `PD.image (rref i) = insert (-(e i)) (PD.erase (e i))` — *a simple reflection
  permutes the positive roots, moving `αᵢ` to `-αᵢ`*;
* `negCount v = #{α ∈ Φ⁺ : ⟨v, α∨⟩ < 0}` (the length of the Weyl group element taking `v` to the
  dominant chamber) and **`negCount_sref`**: if `v i < 0` then
  `negCount (sref i v) = negCount v - 1` (the termination measure of the reflection algorithm);
* `Dominant v := ∀ i, 0 ≤ v i`, `dominant_of_negCount_zero`,
  `WConj v v' := ∃ L : List (Fin 8), L.foldl (fun w i => sref i w) v = v'` (reachability by simple
  reflections), `WConj_refl`, `WConj.step`, and
  **`exists_dominant_WConj`**: every weight can be reflected into the dominant chamber.  (The Weyl
  group has 696 729 600 elements, so this is proved by the length function `negCount` and the group
  is *never* enumerated; this is the key trick for the whole Weyl theory.)

**Commons published this session** (all proved by fleet children):
`Commons.Data.Finset.card_filter_comp_image`, `Commons.Data.Finset.image_eq_insert_erase_of_involutive`,
`Commons.LinearAlgebra.Matrix.Cartan.{reflectD_involutive, pairing_reflect, cval_reflect}`,
`Commons.Data.Finset.card_filter_reflect`.

### BUILD WARNING (for the next session)
`Submission/WeylRoots.lean` takes ~8 min and `Submission/WeylReflect.lean` ~12 min to compile from
scratch (the literal 240/120-element `decide` checks dominate; memory blows up if several of them are
in one `fin_cases <;> decide`).  They are cached, so ordinary incremental builds are fast, but a cold
`lake build Submission` is ~25 min.  **If this becomes a problem, replace the `decide` membership
checks by explicit permutation witnesses**: for each `i`, produce (in Python) the permutation
`σ i : Fin 240 → Fin 240` with `rref i (rootsD.get j) = rootsD.get (σ i j)` and prove it by 240 cheap
`decide`s (single vectors, not 240² membership tests).

### THE ROAD FROM HERE (updated)
1. ~~Stage 1–3~~: done (Lie-module/`U`-module dictionary; Serre presentation; ⋆-action and all six
   Serre families; word spanning; `M(λ) ≠ 0`; `L(ω₁+ω₈)` exists and is irreducible).
2. ~~Weyl root data and the reflection algorithm~~: done (this session).
3. **Weyl group combinatorics, second half** (next): the length function `l(w)` and the sign
   character `(-1)^l`; the *fundamental chamber* (a dominant weight is uniquely determined inside
   its `W`-orbit); the "simple roots span the root lattice" lemma (`ν ∈ ℕΦ⁺ ⟹ ⟨ν, ·⟩` is not
   everything) — needed for the alternating-element uniqueness below.
4. **The Weyl denominator / alternating elements** (`Submission/WeylCharacter.lean`): work in the
   group ring `AddMonoidAlgebra ℤ (Fin 8 → ℤ)` of the weight lattice.  Define
   `AForm := ∏_{α ∈ Φ⁺} (e^{α/2} - e^{-α/2})` (a *finite* product, hence computable) and the notion
   of an *alternating* element (`sᵢ · f = - f` for the eight generators — note that the Weyl group is
   never summed over!).  Key lemma: **if `ν` is strictly dominant then the alternating elements with
   support in `ν - ℕΦ⁺` are determined by their coefficient at `e^ν`** (proof: take a maximal
   exponent `ν'` of the support; if `ν' < ν` then some simple root has positive coefficient in
   `ν - ν'`, whence `⟨ν', αᵢ∨⟩ < 0`, so `sᵢν' > ν'` is again in the support — contradiction; uses
   `E8_posDef` and positivity of the Cartan pairing on `Φ⁺ × {simple roots}`).
   This is the substitute for `Σ_{w∈W} (-1)^{l(w)} e^{wρ}` — the Weyl group is far too large to sum
   over, and this reformulation makes the Weyl character formula a *finite* statement.
5. **Structure theory of `LieAlgebra.e₈ ℂ`** (the real mountain): `Matrix.ToLieAlgebra ℂ E8` has no
   structure theory in Mathlib.  Needed: the Cartan subalgebra (image of the `hᵢ`), the root space
   decomposition, the Chevalley basis and `dim e₈ = 248`, the invariant form and the **Casimir
   element** `Ω` (its action on a highest-weight module is the scalar `(λ, λ+2ρ)`), Weyl's complete
   reducibility.  Route: build `𝔤_c` = the Chevalley Lie algebra on `{hᵢ} ∪ {x_α}` with the
   structure constants of the `α`-strings, or (the currently favoured route) prove PBW for the Serre
   presentation via the *module* `V = FA ⧸ J` of `Submission.StarQuotient` (which already carries a
   faithful enough `e₈`-action).
6. **Freudenthal's formula** (the route to the dimension that avoids `W`): for a highest weight
   module `V` of highest weight `λ` with finite-dimensional weight spaces,
   `(‖λ+ρ‖² - ‖μ+ρ‖²) dim V_μ = 2 Σ_{α>0} Σ_{k≥1} dim V_{μ+kα} ⟨μ+kα, α∨⟩`.
   Derivation: trace of the Casimir on the `α`-string through `μ` (uses the `sl₂`-triple
   `{x_α, x_{-α}, h_α}` and the invariant form).  Together with `W`-invariance (8 conditions!) and
   the support bound `supp ⊆ λ - ℕΦ⁺` this *determines* the character; then the explicit candidate
   multiplicities (computed in Python, certified digit-by-digit in ℕ) give
   `dim L(ω₁+ω₈) = 779247`.  The numerical identity `∏_{α>0}⟨λ+ρ,α∨⟩/⟨ρ,α∨⟩ = 779247` is already
   certified in `Submission.E8RootSystem.weyl_dim_e8`; the limit argument
   (`e^{α} ↦ e^{tα}`, `t → 0`, L'Hôpital) turns the character formula into the dimension formula.
7. **Tensor square**: from the certified character of `L(ω₁+ω₈)` compute
   `χ_λ · χ_λ = Σ_μ m_μ χ_μ` (a finite computation once the χ_μ are available as certified
   functions) and count the distinct `μ` — the answer is 40.  Then convert complete reducibility
   into `(isotypicComponents U (L ⊗ L)).ncard = 40` with
   `Commons.RingTheory.SimpleModule.isotypicComponents_eq_range_of_iSupIndep_isIsotypicOfType_of_isSemisimpleModule`
   and `..._ncard_of_linearEquiv` (the `IsSemisimpleModule` hypothesis is essential).

### A DEAD END FOUND THIS SESSION (do not retry it)
The tempting idea "an alternating element of `ℤ[Λ]` with support in `ν - ℕΦ⁺` and leading
coefficient `1` at `e^ν` is unique" is **FALSE**, so the Weyl character formula cannot be obtained
from it by a leading-term argument.  Counterexample: type `A₁` with `ν = 3ω` (`= λ + ρ` for
`λ = 2ω`); the alternating elements supported in `ν - ℕΦ⁺ = {3ω, ω, -ω, -3ω}` form a **2**-dimensional
space (spanned by `e^{3ω}-e^{-3ω}` and `e^{ω}-e^{-ω}`), and the `3ω`-coefficient does not determine
the element.  Equivalently, the "Weyl alternants" `A_{μ+ρ}` with `μ` dominant are a ℤ-basis of the
alternating part, and several of them can have support below a given `ν`.  *The Weyl character
formula is genuinely a division, not a leading-term determination*: one really needs the
representation theory (Casimir/Freudenthal/complete reducibility) to know that the numerator is
divisible with a "positive" quotient.

### KEY STRUCTURAL INSIGHT (recorded this session)
`V = FA (Fin 8) ⧸ J` of `Submission.StarQuotient` is, by construction, the universal enveloping
algebra of the *Serre-presented* `𝔫⁻`: `𝔫⁻ = FL(f₁,…,f₈)/(⁅f_p,f_q⁆ (A_{pq}=0),
⁅f_p,⁅f_p,f_q⁆⁆ (A_{pq}=-1))` and `U(𝔫⁻) = FA/(two-sided ideal generated by those same elements)`,
which is *exactly* `J`.  Hence `V ≅ U(𝔫⁻)` (granting the standard Serre presentation of `𝔫⁻`) and the
⋆-action makes it the Verma module `M(λ)`: the map `M(λ) = U(e₈)⧸J(λ) ↠ V`, `u ↦ ρ(u)(1+J)`, is
surjective by `Submission.VermaNonzero.cyclic_V`.  **So the ⋆-action model is a concrete realization
of the Verma module, and the missing ingredient for the character of `M(λ)`
(= `e^λ ∏_{α>0}(1-e^{-α})^{-1}`) is exactly the PBW/independence statement for `𝔫⁻`.**

### FREUDENTHAL PLAN, with the two caveats to resolve
`(‖λ+ρ‖²-‖μ+ρ‖²) m(μ) = 2 Σ_{α>0} Σ_{k≥1} m(μ+kα)⟨μ+kα,α∨⟩`.  Since the recursion at a weight `μ`
only involves *higher* weights `μ+kα` (with `ν = λ-μ` dropping to `ν - kα` in `ℕΦ⁺`), it determines
`m` by ascending induction on `ν ∈ ℕΦ⁺` (well-founded, because `Σνᵢ` drops).  Caveats:
* **Vanishing coefficient**: `‖λ+ρ‖² = ‖μ+ρ‖²` happens exactly for `μ` on the "Casimir sphere";
  e.g. `μ = λ - αᵢ` with `⟨λ, αᵢ∨⟩ = 0` (for `λ = ω₁+ω₈` and `i ∉ {1,8}`).  There the recursion is a
  consistency condition, not a definition, and `m(μ)` must be recovered from **`W`-invariance**:
  `sᵢμ = λ + αᵢ ≰ λ` gives `m(μ) = m(λ+αᵢ) = 0`.  A lemma "every weight on the Casimir sphere
  below `λ` has a `W`-translate above `λ`" is needed (only finitely many such `μ`; for these a
  finite check is acceptable).
* **Support/finiteness**: the induction needs the support to be bounded below.  Since `L(λ)` is a
  quotient of `M(λ)`, `supp ⊆ λ - ℕΦ⁺`, which is *not* bounded below, so finiteness of `L(λ)`
  (Weyl's theorem) is genuinely needed.

### 🎉 BREAKTHROUGH (end of this session): THE STRUCTURE THEORY OF `e₈` NOW EXISTS IN THE COMMONS

A fleet agent proved `Commons.Algebra.Lie.e8_finrank : Module.finrank ℂ (LieAlgebra.e₈ ℂ) = 248`
(`Submission/Commons/Algebra/Lie/e8_finrank.lean`, sorry-free) — the **existence of `e₈`**, which was
the "missing chapter" of the whole project.  It is accompanied by a full new commons chapter
`Submission/Commons/Algebra/Lie/SerreConstruction/` (~9000 lines, all sorry-free) containing:

* `e8_finrank` — `finrank ℂ e₈ = 248`;
* `e8_zero_weightSpace_finrank` — the Cartan subalgebra `span{Hᵢ}` has dimension 8;
* `e8_root_weightSpace_finrank_eq_one` — **every nonzero weight space is 1-dimensional**;
* `e8_W_eq_bot_of_not_cone`, `e8_weightSpace_eq_bot_of_not_positiveCone`, `e8_weightSpace_ascent`,
  `e8_weightSpace_descent`, `e8_weightSpace_reflect_finrank` — the weight-space/positivity structure
  (this is where the `γ = ½∑nᵢαᵢ`, `(γ,γ)=2` classification of the occurring weights is proved);
* `e8_W_le_Psub`, `e8_W_le_Msub`, `e8_eq_sup_cartan_positive_negative` — the **triangular
  decomposition** `e₈ = 𝔫⁻ ⊕ 𝔥 ⊕ 𝔫⁺`;
* `e8_weightSpace_iSup_eq_top` — the weight-space decomposition `e₈ = ⨁_μ e8W μ`;
* `e8_iota_injective`, `e8_serreE_ne_zero`, `e8_simple_root_weightSpace_finrank`,
  `e8_rootVector_card`, `exists_finset_e8_roots`, `e8_dominant_weight_eq_zero_or_theta`;
* `Commons.LinearAlgebra.Submodule.rank_iSup_eq_sum_of_iSupIndep`,
  `Commons.LinearAlgebra.Eigenspace.iSupIndep_eigenspace_of_commute_of_torsionfree` (new general
  linear-algebra lemmas used by the above).

**What this unlocks (the new plan to the target theorem).**  With the root space decomposition and
`dim e₈ = 248` available, the classical route becomes available *without* the ad-hoc Serre-quotient
arguments:
1. Build the **explicit Chevalley-type basis** of `e₈` (the 8 `Hᵢ` plus one vector in each of the 240
   root spaces, cf. `e8_rootVector_card`/`exists_finset_e8_roots`) and feed it to
   `Commons.Algebra.Lie.PBW.standardMonomial_basis` to get **PBW for `e₈`**; then
   `U(e₈) ≅ U(𝔫⁻) ⊗ U(𝔥) ⊗ U(𝔫⁺)` and the Verma module character
   `ch M(λ) = e^λ ∏_{α>0}(1 - e^{-α})^{-1}` together with the Kostant partition function.
2. The **invariant form** (Killing form `LieAlgebra.killingForm`, or the root-datum form) and the
   **Casimir element** `Ω`: on a highest weight module `Ω` acts by `(λ, λ+2ρ)`.
3. **Freudenthal's formula** `(‖λ+ρ‖²-‖μ+ρ‖²) m(μ) = 2 Σ_{α>0} Σ_{k≥1} m(μ+kα)⟨μ+kα,α∨⟩`
   (trace of the Casimir over the `α`-string; Mathlib's `Weights/Chain.lean` has the `sl₂`-chain
   theory).  Plus finiteness of `L(λ)` for dominant integral `λ` (Weyl's theorem).
4. Certificate + uniqueness ⟹ `dim L(ω₁+ω₈) = 779247`; tensor-square decomposition ⟹ `ncard = 40`.
Also: the Weyl group machinery of `Submission/WeylRoots.lean`/`WeylReflect.lean`/`WeylChamber.lean`
(240 roots, reflections, the length function `negCount`, the dominant chamber) is already in place,
and `Submission/WeylRoots.posRootsD`/`rootsD` can now be *identified with* `exists_finset_e8_roots`
(same 240 roots), removing the need for the brute-force `decide` proofs.

### THE NEXT CONCRETE THEOREM: `M(λ) ≅ V` (the ⋆-action model IS the Verma module)

**Progress (this session):** `Submission/VermaModel.lean` (sorry-free) already contains the first
half: the algebra map `iotaA : ℂ⟨f₁,…,f₈⟩ →ₐ[ℂ] U(e₈)` (`fᵢ ↦ Fᵢ`),
`iotaA_serreGen`, `iotaA_serreGen2` (`iotaA` sends the free-algebra Serre elements to
`ι(⁅F_p,F_q⁆)` resp. `ι(⁅F_p,⁅F_p,F_q⁆⁆)`), the **vanishing** `iotaA_serreGen_eq_zero`,
`iotaA_serreGen2_eq_zero`, `iotaA_gen` and `iotaA_mem_J` (**`J ⊆ Ann_A(v(λ))` for every `λ`** —
this is what makes `α` well defined), plus `iotaA_wordElt_list` and `rho_v0_eq_mk`
(`rho lam (iotaA x) v0 = mk x`, the `A`-linearity of `ρ ∘ ι'` on the cyclic vector).
**Still to do:** define `alpha := Submodule.liftQ (J E8) (x ↦ iotaA x • v lam)` and
`beta := Submodule.liftQ (spanIdeal e h (weightInU lam)) (u ↦ rho lam u v0)` (the well-definedness
of `beta` is verbatim the `hJ` computation inside `Submission.VermaNonzero.M_nontrivial`), then
`beta ∘ alpha = id_V` (from `rho_v0_eq_mk` and `A`-linearity on the generator `v0`), and `alpha`
surjective — the latter via `Submission.TriangularSpan.span_triMon_eq_top`: `U(e₈)` is spanned by
`Fw·Hw·Ew`, and `Hw ∈ ι'(A) + spanIdeal(e, h - w)`, `Ew ∈ spanIdeal(e, h - w)`, so
`U(e₈) = ι'(A) + spanIdeal e h (weightInU lam)` and hence `M(λ) = ι'(A)·v(λ) = α(V)`.  Then
`alpha` is a bijection with inverse `beta`.

**This is the highest-value next step** — it is concrete, provable with the existing machinery, and
it turns the ⋆-action model (`Submission.StarQuotient.V E8`) into a fully usable description of the
Verma module `M(λ) = Submission.E8Weights.M lam`.  Let `A = FA (Fin 8) = ℂ⟨f₁,…,f₈⟩` (the free
associative algebra), `J ⊆ A` the `ℂ`-span of `{wordElt u * s * wordElt v : s ∈ Gen}`
(`Submission.StarQuotient`), `V = A ⧸ J`, and let `v₀ = 1 + J`.  Let `ι' : A →ₐ[ℂ] U(e₈)` be the
algebra map `f_i ↦ f i` (exists by the universal property of the free algebra; in Lean:
`MonoidAlgebra.lift`/`liftNC` with the monoid hom `FreeMonoid (Fin 8) →* U` sending `of i ↦ f i`).

* **The F-side Serre elements vanish in `U(e₈)`.**  For `s ∈ Gen`, `ι' s = 0` in `U(e₈)`: for
  `s = serreGen p q = f_pf_q - f_qf_p` we get `ι' s = ι(⁅SerreF p, SerreF q⁆)` which is `0` when
  `A_{pq} = 0` (`Submission.E8Weights.serreLie_*` / `ι_lie`), and similarly `ι' (serreGen2 p q) = 0`.
  Hence `x ∈ J ⟹ ι' x = 0`, so `J ⊆ Ann_A(v(λ))` for *every* `λ`.
* **`α : V → M(λ)`**, `mk x ↦ ι'(x) • v(λ)`: well defined by the previous bullet
  (`Submodule.liftQ`, or `Submodule.mapQ` from the linear map `x ↦ ι'(x) • v(λ)`).
  It is `A`-linear and **surjective**, because `M(λ) = ι'(A) · v(λ)`
  (`ι'(A) ⊆ U(e₈)` is the subalgebra generated by the `f_i`, i.e. `U(𝔫⁻)`, and
  `M(λ) = U(e₈)v(λ) = U(𝔫⁻)v(λ)` since the `e_i` kill `v(λ)` and the `h_i` act by scalars).
* **`β : M(λ) → V`**, the `U(e₈)`-module map with `v(λ) ↦ v₀`: exists because
  `spanIdeal e h (weightInU λ) ⊆ ker(u ↦ ρ(u) v₀)`; this is exactly the argument already used in
  `Submission.VermaNonzero.M_nontrivial` (`ψ (u * y) = ρ u (ψ y)` with
  `Submission.VermaNonzero.highest_weight_annihilate`/`highest_weight_diagonal`).
* **`β ∘ α = id_V`**: both are `A`-linear, `V` is generated by `v₀` as an `A`-module, and
  `β (α v₀) = β (v(λ)) = v₀`.  (`ρ ∘ ι'` is the given `A`-action on `V`, cf.
  `Submission.VermaNonzero.rho_fword`.)
* **`α ∘ β = id_{M(λ)}`**: `α` is a bijection by the previous two bullets (injectivity from
  `β ∘ α = id`, surjectivity as above), so `β = α⁻¹`.

Consequences worth recording in the roadmap afterwards: `M(λ) ≅ A ⧸ J` **for every** `λ` (the
`λ`-dependence sits in the `e₈`-action only), `V` *is* the free rank-1 module over `A ⧸ J`, and the
`f`-side Serre relations are *the only* relations among the `f_i` acting on a highest weight vector.

### ADDED AFTER THE ROADMAP (this session)
`Submission/WeylChamber.lean` (`namespace Submission.WeylChamber`):
* **`exists_pos_cval`**: if `m : Fin 8 → ℤ` is nonzero and nonnegative then some
  `cval i m = ∑ k, A i k * m k` is positive (from `Commons...E8_posDef`: `m ⬝ A m > 0` while a
  nonpositive `cval` would force `m ⬝ A m ≤ 0`).  This is the positivity input for the chamber /
  uniqueness arguments.
* **`eq_zero_of_forall_cval_nonpos`**: a nonnegative `m` with all `cval i m ≤ 0` is zero.
-/

/-!
# Roadmap for `e8_irrep_tensor_square_decomp`

Goal: exhibit a 779247-dimensional irreducible `LieAlgebra.e₈ ℂ`-module `V` whose tensor square
has 40 isotypic components as a module over `U(e₈) = UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ)`.

## What is in place (sorry-free; `lake build Submission` is green)

* `Submission.Enveloping`, the Lie-module ↔ `U(𝔩)`-module dictionary (the reusable parts are
  published in the commons as `Commons.RepresentationTheory.LieEnveloping.*`):
  `ι_smul_eq_lie`, `mul_smul_eq_smul_smul`, `algebraMap_smul_eq_smul`,
  `enveloping_smul_mem_of_lieSubmodule` (every Lie submodule is `U(𝔩)`-stable),
  `toEnveloping`/`ofEnveloping` with the order isomorphism `lieModuleSubmoduleEquiv` between
  Lie submodules and `U(𝔩)`-submodules, and `isIrreducible_iff_isSimpleModule`
  (`LieModule.IsIrreducible` ⟺ `IsSimpleModule U(𝔩)`).
* `Submission.EnvelopingModule`: the reverse dictionary (`instLieRingModuleE8`, `instLieModuleE8`):
  every `U(e₈)`-module is a Lie module of `e₈` by `x • m = (ι ℂ x) • m`.
* `Submission.EnvelopingModuleCheck` / `Submission.EnvelopingRoundtrip`: the intended witness
  `Mω = U(e₈)/J(ω₁+ω₈)` carries all five structure classes of the existential statement, and its
  two module structures agree; the annihilation law survives the change of semantics.
* `Submission.E8Weights`: the cyclic highest-weight module `M(λ) = U(e₈)/J(λ)`, its highest-weight
  vector `v(λ)`, the annihilation `Eᵢ • v = 0`, the diagonal action `Hᵢ • v = λᵢ • v`, cyclicity,
  the complete Serre presentation in `e₈` and in `U(e₈)`, the weight-shift lemmas
  (`h_smul_wordVec`-style bookkeeping), the joint weight spaces of `Mω` and their separation for
  distinct weights (`weightSpace_ne_of_ne`).
* `Submission.WordSpan`: the word-spanning floor of this session.
  - `eq_top_of_generators`: any Lie subalgebra of `e₈` containing the images of the Serre
    generators is everything (published in the commons as
    `Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators`).
  - `smul_mem_wordSpan`: **word spanning** — if `v` is annihilated by every `Eᵢ` and is a joint
    eigenvector of the `Hᵢ` (eigenvalues `λ`), then every element of the `U(e₈)`-submodule
    generated by `v` lies in the `ℂ`-span of the word vectors `F_{i₁}⋯F_{i_k} • v`
    (`wordVec`, `wordSpan`).  This is the half of the triangular decomposition of a
    highest-weight module that does *not* need PBW.
  - `wordSpan_vω_eq_top`, `iSup_jointWeightSpace_eq_top`: `M(ω₁+ω₈)` is spanned by its joint
    weight spaces, equivalently by the vectors `F_{i₁}⋯F_{i_k} • vω`.
* `Submission.WeightIndependence`: the weight-space structure of `Mω`.
  - `wtVec m` (the weight attached to a vector `m` of letter multiplicities) with
    `wtVec_injective` (the E₈ Cartan matrix is invertible over `ℂ`);
  - `eq_zero_of_sum_eq_zero`: **vectors of pairwise distinct joint weights are linearly
    independent** (the interpolation argument with the commuting family `H₁,…,H₈`);
  - `jointWeightSpace_eq_span_wordVec` / `jointWeightSpace_le_span_wordVec`: the `wtVec m`-weight
    space is *exactly* the span of the word vectors whose letters have multiplicities `m`;
  - `jointWeightSpace_le_span_finite`: each weight space of `Mω` is spanned by finitely many
    weight vectors (there are only finitely many words with prescribed letter multiplicities,
    `Commons.Data.List.finite_setOf_count_eq`).

* `Submission.TriangularSpan`: the spanning half of the triangular decomposition of `U(e₈)`.
  Writing `Fw w = ∏ f i`, `Hw v = ∏ h j`, `Ew u = ∏ e k` and
  `triMon w v u = Fw w * Hw v * Ew u`, it is proved that
  `Submodule.span ℂ (Set.range (fun p => triMon p.1 p.2.1 p.2.2)) = ⊤`
  (`T_eq_top`, `span_triMon_eq_top`): **every element of `U(e₈)` is a finite ℂ-linear combination of
  triangular monomials.**  The moving lemmas are `Ew_mul_h` (`Ew u * h i = h i * Ew u - c • Ew u`),
  `Hw_mul_f` (`Hw v * f i = f i * R` with `R` in the span of the `H`-words), `Ew_mul_f`
  (`Ew u * f i = f i * Ew u + R` with `R` in the span of the `(H-word)*(E-word)` products), and the
  closure lemmas `T_mul_e`, `T_mul_h`, `T_mul_f`.  The final step is the "subalgebra" argument
  (`TRight`, `iota_mem_TRight`): the subalgebra of elements preserving `T` on the right contains
  `ι(e₈)`, hence is everything; applying it to `1 ∈ T` gives `T = ⊤`.

* `Submission.StarModule`: **the "⋆-action" on the free algebra and the Serre relations** — the
  mathematical core of the non-vanishing of the Verma module.  Let `F = ℂ⟨f_1,…,f_8⟩` be the free
  associative algebra on the generators `f_i` (realised as `MonoidAlgebra ℂ (FreeMonoid ι)`), and
  for a Cartan matrix `A` and a weight `lam` define the operators
  * `Lop i` — left multiplication by `f_i`,
  * `Hop i` — the diagonal operator `w ↦ (λ_i - ρ_i(w))·w` (`ρ_i(w) = ∑_{t∈w} A_{i,t}`),
  * `Eop i` — the "delete an occurrence of `i`" operator, recursively
    `Eop i (f_a · x) = Lop a (Eop i x) + (if a = i then Hop i x else 0)`,
    equivalently `Eop i w = ∑_{w = x i y} (λ_i - ρ_i(y)) xy` (note the *suffix*, which is what makes
    the relation `[E_i,F_j] = δ_{ij}H_i` hold while keeping `F_i` a left multiplication).
  Main results (`Submission.StarModule.*`, all sorry-free):
  * `Eop_Lop` (relation 4: `[E_i, F_j] = δ_{ij}H_i`), `Hop_Lop` (relation 3),
    `Hop_Eop` (relation 2: `[H_i, E_j] = A_{ij}E_j`), `Hop_Hop` (relation 1);
  * `Eop_Eop_lie_eq_zero`: **`[E_i,E_j] = 0` when `A i j = 0`** (Serre relation `ad(E_i)^1(E_j)`);
  * `serre_adE_two`: **`(ad E_i)^2(E_j) = 0` when `A i i = 2` and `A i j = -1`** (Serre relation
    `ad(E_i)^{2}(E_j)`).
  The technique for the last two is `eq_zero_of_comm_L` (generalised in the commons as
  `Commons.Algebra.MonoidAlgebra.eq_zero_of_comm_mulLeft`): a linear endomorphism of the free
  algebra which commutes with all the left multiplications by generators and kills `1` is zero.
  Hence it suffices to compute `[S, L_a]` for the Serre element `S`, by Jacobi plus the relations
  above — e.g. `[⁅E_i,⁅E_i,E_j⁆⁆, L_a] = δ_{ai}(A_{ii} + 2A_{ij})⁅E_i,E_j⁆ = 0` when `A_{ii} = 2`,
  `A_{ij} = -1`.
  **What remains for `M(λ) ≠ 0`** is the "F-side" of the triangular decomposition: `F/J` (the
  two-sided ideal generated by `⁅f_i,f_j⁆` and `⁅f_i,⁅f_i,f_j⁆⁆`) carries the e₈-action induced by
  the ⋆-action, is nonzero (it is contained in the augmentation ideal), and `1` in `F/J` is a
  highest-weight vector of weight `λ`.  The needed intermediate inputs — that `wdelta i`
  (`x ↦ ρ_i(x)x`) is a derivation, that `Hop i = λ_i·id - wdelta i`, that `Dop i` and `Eop i` kill
  the Serre elements — are the next step.

* `Submission.StarDerivation`: the "weight derivation" `wdelta i` (`x ↦ ρᵢ(x)·x` on words) and the
  Serre relation elements `serreGen i j = ⁅f_i, f_j⁆`, `serreGen2 i j = ⁅f_i, ⁅f_i, f_j⁆⁆` of the
  free algebra, together with:
  * `wdelta_deriv`: `wdelta i` is a derivation (`wdelta i (xy) = wdelta i x · y + x · wdelta i y`);
  * `Hop_eq`: `Hop i = λ_i·id - wdelta i`;
  * `wdelta_serreGen`, `wdelta_serreGen2`: the Serre elements are eigenvectors of `wdelta i` (their
    letters form a multiset, so `ρᵢ` is constant on the words they are supported on).  In
    particular `wdelta i s ∈ serreIdeal` for every `s ∈ serreSet`, which is the key input for
    showing that the ideal `serreIdeal` (generated by the "f-side" Serre elements) is stable under
    the ⋆-action and hence that `F/J` is an e₈-module.

* `Submission.E8RootSystem`: the root system of E₈ in its standard realization, in *doubled
  integer coordinates* (an entry `x : List ℤ` stands for `½ ∑ xᵢ εᵢ`), with `dotInt x y = ∑ xᵢ yᵢ`
  equal to `4 · (x,y)` for the standard form `(·,·)`.  Contents:
  - `rootsAll`: the 240 roots; they are the union (`rootsAll_toFinset`) of
    `pairRootsList` (the 112 roots `±2εᵢ ± 2εⱼ`, `pairRootsList_length`) and `spinorRootsList`
    (the 128 roots `(±1,…,±1)` with an even number of minus signs, `spinorRootsList_length`);
    `rootsAll_length`, `rootsAll_nodup`, `rootsAll_neg` (stability under negation).
  - `simpleRoot`: the eight Bourbaki simple roots; `simpleRoot_cartan` proves that their Cartan
    matrix is `4 · CartanMatrix.E₈` (so this realization carries the root datum of the
    Serre-presented `LieAlgebra.e₈ = Matrix.ToLieAlgebra ℂ CartanMatrix.E₈`).
  - `rho = (0,2,4,6,8,10,12,46)` is the Weyl vector (`rho_duality`: `(ρ,αᵢ) = 1` for all `i`), and
    `posRootList_eq_filter` shows that the positive roots (in the sense of `ρ`) are exactly the
    120 entries of `posRootList`, each of which is a genuine root (`posRootList_facts`).
  - `omega1PlusOmega8` is the weight `ω₁+ω₈` (`omega1PlusOmega8_duality`), `lamPlusRho_eq` records
    `ω₁+ω₈+ρ = lamPlusRho`.
  - **`weyl_dim_e8` / `weyl_dim_e8_full`**: the Weyl dimension formula at the highest weight
    `ω₁+ω₈`,
    `∏_{α>0} ⟨ω₁+ω₈+ρ, α∨⟩ / ⟨ρ, α∨⟩ = 779247`,
    the dimension of `V(ω₁ + ω₈)`.  This is where the number `779247` of the challenge statement
    comes from (given the highest-weight theory and the Weyl character formula).

## What is missing (the road to the theorem)

1. **Triangular decomposition of `U(e₈)` — the spanning half is DONE**
   (`Submission.TriangularSpan`, generalised in the commons as
   `Commons.Algebra.Lie.TriangularSpan.span_triMon_eq_top`): `U(e₈)` is *spanned* by the products
   (F-word)·(H-word)·(E-word).
2. **The independence half — the fundamental blocker.**  What is missing is that this spanning
   family is linearly independent, equivalently that the Verma module `M(λ) = U(e₈)/J(λ)` is
   nonzero (`1 ∉ J(λ)`), equivalently PBW for the Serre presentation.  Routes analysed so far:
   * The classical "⋆-action" model (`V` = the free associative algebra on the `Fᵢ`, `Fᵢ` acting by
     left multiplication, `Hᵢ` diagonally, `Eᵢ` by the "delete an occurrence" formula) satisfies all
     Serre relations *except* the `ad(Fᵢ)`-nilpotency: there the operator is left multiplication by
     the non-zero associator `fᵢ²fⱼ − 2fᵢfⱼfᵢ + fⱼfᵢ²`.  The fix (using `U(𝔫⁻)` rather than the
     free algebra) is exactly `M(λ) ≠ 0`, i.e. circular.
   * The concrete `e₈` (Chevalley basis over the explicit root system, which is now available in
     `Submission.E8RootSystem`) would give the triangular decomposition at once from
     `Commons.Algebra.Lie.PBW.standardMonomial_basis` — but it requires the Jacobi identity for the
     Chevalley structure constants, i.e. the classical (non-trivial) Chevalley commutator-formula
     verification.
   * A way *around* Jacobi: define `𝔤_c` as the quotient of the **free** Lie algebra on the symbols
     `{hᵢ} ∪ {x_α : α ∈ Φ}` by the Chevalley ("root system") relations
     `[hᵢ,hⱼ] = 0`, `[hᵢ,x_α] = ⟨α,αᵢ∨⟩x_α`, `[x_α,x_β] = N_{αβ}x_{α+β}`, `[x_α,x_{-α}] = h_α`.
     This is a Lie algebra *by construction* (a quotient of a free Lie algebra), and the six Serre
     relations in `𝔤_c` (hence, by `Commons.Algebra.Lie.SerreConstruction.liftOfSerrePresentation`,
     a surjection `e₈ ↠ 𝔤_c`) are a finite verification on the root data.  Any `𝔤_c`-module is then
     an `e₈`-module.  What is still missing is the structure theory of `𝔤_c` (that the 248 spanning
     roots are linearly independent, i.e. `dim 𝔤_c = 248`), which is exactly the classical
     "existence of the Chevalley basis" theorem — but the triangular *spanning*
     `𝔤_c = 𝔫⁻ + 𝔥 + 𝔫⁺` is available from the weight grading, so this may be the most promising
     concrete route.
3. **Structure theory of the Serre-constructed `e₈`:** the root spaces of the adjoint action of
   the Cartan `span{Hᵢ}`, the Chevalley basis and `dim e₈ = 248`; the invariant form and the
   Casimir element.  Available: `commutator_HH` (the `Hᵢ` commute) and
   `Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators`.
4. **Weyl theory.**  With the weight lattice `ℤ⁸`, the Cartan pairing `⟨λ, μ⟩ = λᵀ A⁻¹ μ`
   (`CartanMatrix.E₈_det`: the Cartan matrix is invertible over `ℚ`) and the reflections
   `(sᵢ λ)_j = λ_j - λ_i A_{ij}` (an involution on weights:
   `Commons.LinearAlgebra.Matrix.Cartan.reflect_involutive`), one needs: the Weyl group and its
   action on weights, the Weyl vector `ρ` (`ρ(Hᵢ) = 1`, available concretely in
   `Submission.E8RootSystem.rho`), Weyl's denominator identity, and then the character formula, or
   alternatively the Freudenthal recursion, to obtain `dim L(ω₁+ω₈) = 779247` for the simple
   quotient `L(λ) = M(λ)/rad`.  The *numerical value* of the Weyl dimension formula is already
   verified in `Submission.E8RootSystem.weyl_dim_e8`; what is missing is the representation theory
   that identifies it with `dim L(ω₁+ω₈)`.  The tools for the module theory side are in place:
   `Submission.WeightIndependence` gives the linear independence of vectors of distinct weights
   (`eq_zero_of_sum_eq_zero`, generalised to the commons as
   `Commons.LinearAlgebra.Eigenvector.linearIndependent_of_separating_eigenvalues_of_ne_zero`), the
   description of the weight spaces as spans of word vectors, and their finite generation.
5. **Tensor square.**  `L(ω₁+ω₈) ⊗ L(ω₁+ω₈)` is completely reducible with 40 distinct simple
   constituents (155 summands counted with multiplicity).  The general module theory for turning a
   decomposition into simple summands into the number of isotypic components is available in the
   commons: `Commons.RingTheory.SimpleModule.isotypicComponents_eq_range_of_iSupIndep_isIsotypicOfType_of_isSemisimpleModule`
   (note the essential `IsSemisimpleModule` hypothesis) and
   `Commons.RingTheory.SimpleModule.isotypicComponents_ncard_of_linearEquiv`.

## SESSION 4: THE BLOCKER IS RESOLVED -- `M(λ) ≠ 0` is proved

New files `Submission/StarQuotient.lean` and `Submission/VermaNonzero.lean` (both sorry-free)
break the "independence half" of the triangular decomposition:

* `Submission.StarQuotient` (namespace `Submission.StarQuotient`, general `A : Matrix ι ι ℤ`):
  - `Gen` (the "f-side" Serre elements: `⁅f_p,f_q⁆` when `A p q = A q p = 0`, and
    `(ad f_p)^2 f_q` when `A p p = 2`, `A p q = -1`) and `J`, the `ℂ`-span of the products
    `wordElt u * s * wordElt v` (`s ∈ Gen`) -- the two-sided ideal cutting out `U(𝔫⁻)`.
  - `V A := FA ι ⧸ J A` and the descended operators `Lbar`, `Hbar`, `Ebar`
    (`Submodule.mapQ`), with the `mk`-evaluation lemmas `Lbar_mk`, `Hbar_mk`, `Ebar_mk`.
  - the right-multiplication formulas `Hop_mul_single`, `Dop_mul_single`, `Eop_mul_single`,
    the word recursions `Dword_append_single`, `Eword_append_single`, the derivation property
    `Dop_deriv`, and the "delete operator kills the generators" computations
    `Eop_serreGen`, `Eop_serreGen2` (crucially `Eop i s ∈ J` for `s ∈ Gen`).
  - the **stability of `J`** under the whole ⋆-action: `wdelta_mem_J`, `Hop_mem_J`,
    `Dop_mem_J`, `Eop_mem_J` (the last one via the left/right expansions
    `Eop_wordElt_mul_mem`, `Eop_Dop_right_mem`).
  - the **six Serre relations on `V`**: `lie_Hbar_Hbar`, `lie_Hbar_Ebar`, `lie_Hbar_Lbar`,
    `lie_Ebar_Lbar`, `lie_Ebar_Ebar_zero`, `serre_adE_two_V`, `lie_Lbar_Lbar_zero`,
    `serre_adF_two_V`, packaged with the nilpotency bookkeeping as `adE_zero`/`adF_zero`.
* `Submission.VermaNonzero` (namespace `Submission.VermaNonzero`, `E8 = CartanMatrix.E₈`):
  - `act : e₈ →ₗ⁅ℂ⁆ Module.End ℂ V` from `liftOfSerrePresentation`, hence a `LieRingModule` and a
    `LieModule` structure on `V` (`lieRingModule`, `lieModule`);
  - `mk_one_ne_zero` / `Nontrivial (V E8)` (via the augmentation `aug`, whose existence is in the
    commons as `Commons.Algebra.MonoidAlgebra.freeAlgebra_counit`);
  - `highest_weight_annihilate`, `highest_weight_diagonal` (`Eᵢ • v = 0`, `Hᵢ • v = lam i • v`);
  - `verma_exists : ∃ V ... , ∃ v ≠ 0, (∀ i, ⁅Eᵢ,v⁆ = 0) ∧ (∀ i, ⁅Hᵢ,v⁆ = lam i • v)`;
  - **`M_nontrivial : Nontrivial (Submission.E8Weights.M lam)`** -- the Verma module
    `U(e₈)/J(λ)` is nonzero for EVERY weight `λ`: the former "fundamental blocker" is gone.

## SESSION 5: STAGE 3 DONE -- `L(ω₁+ω₈)` EXISTS (nonzero, irreducible)

New file `Submission/VermaWeight.lean` (namespace `Submission.VermaWeight`, ~500 lines,
sorry-free, imported by `Submission.lean`).  It proves that the Verma module
`V = FA (Fin 8) ⧸ J` with its `e₈`-action (`Submission.VermaNonzero.act`) has a **unique maximal
submodule**, hence a **nonzero simple quotient `L(ω₁+ω₈)`**.  Contents:

* `Wm m` (the span of the word vectors `mk (wordElt w)` whose letters have multiplicity vector
  `m`), `mk_wordElt_mem_Wm`, and the eigen-action **`Hbar_apply_mem_Wm`**:
  `Hbar i` acts on `Wm m` by the scalar `wt m i` (`wt = Submission.WeightIndependence.wtVec`).
* `span_mk_wordElt_eq_top` (the word vectors span `V`), `iSup_Wm_eq_top`, and
  **`exists_decomp`**: every `x : V` is a finite sum `∑ m ∈ s, y m` with `y m ∈ Wm m`.
* `Wm_zero_eq`: the `λ`-weight space `Wm 0` is exactly `ℂ ∙ v`, `v = 1 + J` (`v_ne_zero`).
* the **killer projector**: for `m₀ ∈ s` and coordinates `j m` with `wt m (j m) ≠ wt m₀ (j m)`,
  the *list* product (`List.prod`, because `Finset.prod` needs a commutative monoid and
  `Module.End` is not commutative!) of the operators
  `killer m₀ m j = (wt m₀ j - wt m j)⁻¹ • (Hbar j - wt m j • 1)` satisfies
  `prod_killer_apply` (it acts on every `Wm n` by a product of scalars),
  `prod_killer_mem` (it preserves every `Hbar`-stable subspace) and
  **`prod_killer_apply_sum`**: `(∏ m ∈ s \ {m₀}, killer m₀ m (j m)) (∑ m ∈ s, y m) = y m₀`.
  Consequently **`exists_decomp_mem` / `exists_decomp_mem'`**: the weight components of an element
  of an `Hbar`-stable subspace (in particular of a `U(e₈)`-submodule) lie in the subspace.
* the enveloping-module structure on `V` (`instModuleU`, `instIsScalarTower`,
  `instModuleUQuot`, `instIsScalarTowerQuot`), `hbar_mem`, `eq_top_of_mem`
  (a `U(e₈)`-submodule containing `v` is everything, by cyclicity),
  **`sup_ne_top`** (the sum of two proper `U(e₈)`-submodules is proper -- the one-dimensionality
  of the `λ`-weight space),
  **`exists_max_submodule`** (via `Commons.Algebra.Module.exists_max_submodule_notMem`),
  **`quotient_isSimpleModule`** (via `isSimpleModule_iff_isCoatom`) and
  **`exists_irreducible_highest_weight`**:
  `∃ L, Nontrivial L ∧ LieModule.IsIrreducible ℂ (LieAlgebra.e₈ ℂ) L`.
* `vbar`/`vbar_ne_zero`: the image of the highest weight vector in the quotient.

### WARNING for the next session: instance ambiguity on the quotient `V ⧸ N`

`Module U (V ⧸ N)` has two candidate instances: the quotient instance
`Submodule.Quotient.module N` and the one produced by `lieModuleToEnvelopingModule`
(`ChallengeDeps`).  `Submission.VermaWeight.instModuleUQuot` (declared with **priority 2000**)
pins the quotient instance, and `instIsScalarTowerQuot` supplies `IsScalarTower ℂ U (V ⧸ N)`;
with these, `Submodule U V ⧸ ·` quotients behave well and `lieModuleToEnvelopingModule` /
`Submission.Enveloping.instLieModuleE8` synthesize the Lie module structure on `V ⧸ N`.
**But**: statements such as `u • (mk m : V ⧸ N) = mk (u • m)` or
`⁅x, (mk m : V ⧸ N)⁆ = (ι ℂ x) • mk m` are *not* `rfl` when elaborated inside
`Submission/VermaWeight.lean`, although the same statements ARE `rfl` in a separate file that only
imports it (the `SMul U (V ⧸ N)` chosen by typeclass search differs).  Consequence: the
highest-weight-vector facts *of the quotient* (`⁅Hᵢ, vbar⁆ = λᵢ • vbar`, `⁅Eᵢ, vbar⁆ = 0`,
`U`-cyclicity of `vbar`) are **not yet formalised**; they were dropped from the file for that
reason.  Whoever needs them should first make the instances unambiguous (e.g. state the lemmas
with explicit instance arguments, or define the quotient as a new type with hand-written
instances), and only then re-approach the character theory of `L(λ)`.

### SESSION 5, second half: `Submission/WeylWeights.lean` (start of the Weyl theory)

New sorry-free file `Submission/WeylWeights.lean` (namespace `Submission.WeylWeights`).  Weights are
written in the **`ω`-basis** of the weight lattice (`v i = ⟨v, αᵢ∨⟩`, type `Fin 8 → ℤ` or
`Fin 8 → ℚ`).  In these coordinates:

* the highest weight of the target is `lam = e₀ + e₇` (`lam_apply_of_ne`), the Weyl vector is the
  constant vector `1` (`rho`, `rho_apply`), the fundamental chamber is `IsDominant`;
* the simple reflection is `sref i v = fun j => v j - v i * A i j` (`sref_apply`), an involution
  (`sref_involutive` from `Commons...reflect_involutive`) with `(sᵢv)ᵢ = -vᵢ`
  (`sref_apply_self`); for `vᵢ < 0` all other coordinates weakly **decrease** (`sref_coord_le`) and
  the `i`-th becomes positive (`sref_apply_pos`);
* the Weyl-invariant form `⟪v,w⟫ = v ⬝ A⁻¹ w` (`form`), symmetric (`form_symm`), and **`sref i` is
  an isometry** for it (`sref_isometry`, from the new commons lemma
  `Commons.LinearAlgebra.Matrix.Cartan.reflect_dotProduct_inv`), together with
  `E8q_det_ne_zero`.

**Important correction of an earlier idea:** the "reflect into the dominant chamber" algorithm
cannot use the number of negative *coordinates* as termination measure (a reflected coordinate can
create a new negative coordinate at a neighbouring node).  The correct measure is
`#{α ∈ Φ⁺ : ⟨v, α∨⟩ < 0}`, which drops by exactly one at each step because a simple reflection
permutes `Φ⁺ \ {αᵢ}`.  What is needed for this is the list of the **120 positive roots in
`ω`-coordinates** (obtainable from the explicit root system of `Submission.E8RootSystem` by
applying the Cartan matrix: the `ω`-coordinates of a root `r` are `⟨r, αⱼ∨⟩ = dotInt r (simpleRoot j)/4`),
together with the finite check that `sref i` permutes them.

## What is missing now (updated road to the theorem)

1. ~~Highest-weight structure of `V`; existence of a simple quotient `L(λ) ≠ 0`.~~  DONE
   (`Submission.VermaWeight`).  The remaining cosmetic gap is the listing of the quotient's
   highest-weight vector properties (see the warning above).
2. **Finite-dimensionality of `L(λ)` for dominant integral `λ` and `dim L(ω₁+ω₈) = 779247`.**
   This is the remaining mountain.  The numerical value is already certified in
   `Submission.E8RootSystem.weyl_dim_e8` (`∏_{α>0} ⟨λ+ρ,α∨⟩/⟨ρ,α∨⟩ = 779247`); what is missing is
   the representation theory identifying it with `dim L(ω₁+ω₈)`.
   **Weyl theory plan (see also the session-1/2 notes).**
   * `Submission.E8RootSystem` already contains the 240 roots in doubled integer coordinates, the
     eight Bourbaki simple roots (`simpleRoot`), the Weyl vector `rho = (0,2,4,6,8,10,12,46)`
     (`rho_duality`), the 120 positive roots (`posRootList_eq_filter`) and `omega1PlusOmega8`.
   * The simple reflection on weights in the `ω`-coordinates is
     `(sᵢv)ⱼ = vⱼ - vᵢ Aᵢⱼ` (`Commons.LinearAlgebra.Matrix.Cartan.reflect_involutive`); the
     Weyl-invariant form is `⟪v,w⟫ = v ⬝ (A⁻¹ · w)` and `sᵢ` is an isometry for it
     (`Commons.LinearAlgebra.Matrix.Cartan.reflect_dotProduct_inv`).
   * **The Weyl group of `E₈` has order 696 729 600, so it can never be enumerated.**  The Weyl
     character formula / Kostant formula must therefore be proved *structurally* (Weyl denominator
     identity `∏_{α>0}(e^{α/2}-e^{-α/2}) = Σ_{w∈W} (-1)^{l(w)} e^{wρ}` from the chamber structure
     of the reflection group on the weight lattice), not by summing over explicit elements.
   * Alternative route to the *dimension only*: Freudenthal's recursion
     `(‖λ+ρ‖²-‖μ+ρ‖²) m(μ) = 2 Σ_{α>0} Σ_{k≥1} m(μ+kα)(μ+kα,α)` determines the character of
     `L(λ)` from its support; the support is the Weyl-saturation of `λ` (so this too needs the
     Weyl group, i.e. at least the "reflect into the dominant chamber" algorithm and the strict
     monotonicity of the Casimir eigenvalue on dominant weights).
   * In either case one needs: the weight lattice `= ` the `ω`-coordinates `Fin 8 → ℤ`, `ρ`, the
     dominance order, the reflection algorithm, the sign/length function of `W`, the `sl₂`-string
     / complete-reducibility input (`IsSemisimpleModule` for finite-dimensional `e₈`-modules).
3. **The tensor square.** `L(ω₁+ω₈) ⊗ L(ω₁+ω₈)` has 40 isotypic components; the general module
   theory for turning a complete decomposition into `isotypicComponents ... .ncard = 40` is
   already in the commons
   (`Commons.RingTheory.SimpleModule.isotypicComponents_eq_range_of_iSupIndep_isIsotypicOfType_of_isSemisimpleModule`,
   `..._ncard_of_linearEquiv`).  Note that the *count* 40 needs the explicit decomposition of
   `V ⊗ V` into simple summands, i.e. the character theory of the previous item.

## Commons contributions made in this session (all sorry-free)

`Commons.RepresentationTheory.LieEnveloping.{adjoin_range_iota, smul_mem_of_lieSubmodule,
isIrreducible_iff_isSimpleModule, iota_leibniz}`,
`Commons.Algebra.CyclicModule.{quotient_positive_annihilates, quotient_diagonal_acts}`,
`Commons.Algebra.Lie.FreeLieAlgebra.lieSpan_range_of`,
`Commons.Algebra.Lie.SerreConstruction.{lieSpan_range_generators,
eq_top_of_lieSubalgebra_of_generators, liftOfSerrePresentation}`,
`Commons.Algebra.Lie.Module.quotient_lift`,
`Commons.Data.List.finite_setOf_count_eq`,
`Commons.LinearAlgebra.Matrix.Cartan.reflect_involutive`,
`Commons.LinearAlgebra.Eigenvector.linearIndependent_of_separating_eigenvalues_of_ne_zero`.
## SESSION 9: the Casimir element of `e₈` is built, and the build is united again

**Landmine removed.**  `Submission/StarModule.lean`, `Submission/StarDerivation.lean` and
`Submission/StarQuotient.lean` were verbatim duplicates of the first 1154 lines of the commons file
`Commons.Algebra.Lie.SerreConstruction.e8_zero_weightSpace_finrank`; importing both chains made the
environment clash.  They are now thin `import` stubs of that commons module (every name is
unchanged), and `Submission.lean` imports `Submission.E8Casimir` too.  `lake build Submission` is
green with the whole e₈-structure chain and the Verma-module chain in one environment.

**New sorry-free file `Submission/E8Casimir.lean`** (namespace `Submission.E8Casimir`, ~820 lines,
`import`ed by `Submission.lean`).  Contents, in order:

* `K = killingForm ℂ (e₈ ℂ)`; `killingForm_lieInvariant`, `killingForm_nondegenerate`,
  `killingForm_eq_zero_of_add_ne_zero` (`x ∈ e8W μ`, `y ∈ e8W ν`, `μ + ν ≠ 0`) — the two-line
  orthogonality lemma that replaces every trace argument; `exists_decomp_weight`,
  `linearMap_eq_zero_of_weight`, `killingForm_eq_zero_of_orthogonal_cartan`.
* The Cartan `H = e8W 0` with `hBasis`, the restricted form `KH` and `KH_nondegenerate`, and the
  `κ`-dual family `hdual` (`K_SerreH_hdual`).
* `posR : List (Fin 8 → ℤ)` — the 120 positive roots in `ω`-coordinates — with `pR`,
  `pR_injective`, `pR_ne_zero`, `pR_qZ`, **`pR_sum` (`∑_{α>0} α = 2ρ`)**, `pR_add_ne_zero`,
  `pR_neg_add_ne_zero`; `e8W_pR_ne_bot`; `eRoot k ∈ e8W (pR k)`, `fRoot k ∈ e8W (-(pR k))` with
  `K_eRoot_fRoot = 1`, and all the orthogonality cases `K_eRoot_eRoot`, `K_fRoot_fRoot`,
  `K_eRoot_fRoot'`, `K_fRoot_eRoot`, `K_SerreH_eRoot`, …, `K_hdual_fRoot`.
* `Idx = Fin 8 ⊕ (Fin 120 ⊕ Fin 120)`, `bFam = {SerreH, eRoot, fRoot}`, `bDual = {hdual, fRoot,
  eRoot}`, the duality `K_bFam_bDual`/`K_bDual_bFam`, linear independence, the `κ`-orthonormal
  basis `bIdx` (248 elements), and `bIdx_repr`.
* **`Omega`**, the Casimir element; **`Omega_central`** (centrality, from
  `Commons.Algebra.Lie.Casimir.lie_commute`) and **`Omega_mul_comm`** (`Omega * u = u * Omega` for
  *all* `u ∈ U(e₈)`).
* `wdual μ` (the Cartan element with `K (SerreH i) (wdual μ) = μ i`), `rootFun`,
  `lie_mem_e8W`, `lie_eRoot_of_mem_cartan`, and **`eRoot_comm_fRoot :
  ⁅eRoot k, fRoot k⁆ = wdual (pR k)`** (the coroot identity).
* **`Omega_smul_highest_weight`**: for any `U(e₈)`-module `M` with `(ι x) • m = ⁅x, m⁆`, and any
  `v : M` with `⁅SerreH i, v⁆ = lam i • v` and `⁅eRoot k, v⁆ = 0`,
  `Omega • v = (K (wdual lam) (wdual (lam + 2ρ))) • v` — i.e. the Casimir eigenvalue
  `(λ, λ + 2ρ)_κ`.  `Omega_smul_of_cyclic` then spreads it over any cyclic module.

**Commons published this session** (`request_lemma`): `Commons.Algebra.Lie.SerreConstruction.killingForm_SerreH`
(`κ (SerreH i) (SerreH j) = 60 Aᵢⱼ`), `Commons.LinearAlgebra.BilinForm.linearIndependent_of_dual`,
`Commons.LinearAlgebra.BilinForm.sum_dual_basis_pairing`, and (from the previous session, delivered
now) `Commons.Algebra.Lie.SerreConstruction.e8W_ne_bot_of_normTwo`.


## SESSION 11: a kernel-evaluable dominant conjugate, and the performance architecture of the numerics

**`Submission/E8Orbit.lean` (sorry-free, imported here)** provides `dcX`, a dominant-conjugate
algorithm built only from `List` operations and `Int` comparisons, together with the proof
`dcX_eq_dc : dcX v = dc v` (so every lemma about the abstract `dc` applies), and the inherited
structural facts `dcX_dominant`, `dcX_sub_posCon`, `dcX_idem`, `dcX_eq_self_of_dominant`,
`WConj_dcX`.

Why this matters: `Submission.E8Character.dc` reduces through `Finset.min'`/`Finset.filter`, and
the kernel *cannot* evaluate it (`decide` gets stuck or blows the memory cap).  `dcX` can be
evaluated, which makes the numerical certification of the character feasible in principle.

**Measured costs** (recorded in `Submission/Work/pydata`/session notes):

* one `dcX` evaluation costs ≈ 5000 elaboration heartbeats;
* `decide` on a 75-term Freudenthal sum costs ≈ 55 s / 4·10^5 heartbeats;
* `ℚ` is *not* decidable in the kernel (`instDecidableEqRat` gets stuck) — all `decide`
  computations must be stated over `ℤ`;
* a `DecidableEq (Fin 8 → ℤ)` function equality inside the candidate multiplicity function is
  ~10× more expensive than a `List ℤ` key comparison — use the key.

**The pruning trick.** Every weight of `L(λ)` is conjugate to one of the seven dominant weights
`≤ λ`, hence has norm `⟪η,η⟫ ∈ {0,2,4,6,8,10}`.  In the Freudenthal recursion at the dominant `ν`
the term `η = ν+kα_j` can contribute only when `⟪η,η⟫` lies in that set (this uses only
`⟪dcX η, dcX η⟫ = ⟪η,η⟫`).  Counting the surviving `(j,k)` pairs gives

| dominant ν | all terms | surviving |
|---|---|---|
| ω₁+ω₈ | 1785 | 0 |
| ω₂ | 1614 | 28 |
| ω₇ | 1354 | 91 |
| ω₁ | 1077 | 120 |
| 2ω₈ | 1370 | 63 |
| ω₈ | 653 | 180 |
| 0 | 0 | 0 |
| **total** | **7853** | **482** |

So the certification of `dim L(ω₁+ω₈) = 779247` needs only 482 dominant-conjugate evaluations
(≈ 15 min of elaboration) instead of 7853.  The remaining 7371 terms are killed by a *hand-written*
quadratic form `normQ` with the literal `E8inv` entries (do **not** go through the matrix: the
kernel lookup is the dominant cost).

For the tensor square the same pruning applies with the norm set of the 40 constituents, but the
recursion has to be run for every pair `ν' ⪯ ν` of dominant weights below `2λ` (~800 recursion
checks, ~10^6 terms before pruning) — that is the next scaling problem.

Delegated (in flight at session end): `Commons.Algebra.Lie.Sl2.pow_pow_eq_zero` (local finiteness
of the `U(𝔰𝔩₂)`-span of a vector, for the integrability/finiteness theory) and
`Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_unique` (uniqueness of the dominant element of a
Weyl orbit — needed to identify `dc^{-1}(ν)` with the orbit `Wν` and hence to compute
`dim L(λ) = Σ_ν m(ν)·|Wν|`).

## SESSION 12: the enumeration of the dominant weights below `λ` and `2λ`, and the candidate character

**`Submission/E8Enum.lean`** (sorry-free, imported here) delivers the *enumeration* of the dominant
weights in the cones below `λ` and `2λ`, which is needed both for the support condition of the
character and for the upper bound `≤ 40` on the isotypic components of `V ⊗ V`:

* `levelL k` (resp. `candL k`) lists all `v : Fin 8 → ℤ` with non-negative entries and
  `∑ v i = k` (resp. `≤ k`), with the *completeness* lemma `mem_levelL`/`mem_candL`;
* the **bound**: if `ν` is dominant and `posCon (lam - ν)` then `∑ i, ν i ≤ 2`
  (`sum_le_two_lam`), because `(A⁻¹(λ-ν))₇ = 4 - ∑ j (A⁻¹)₇ⱼνⱼ ≤ 4 - 2∑ν`; likewise `≤ 4` for
  `2λ` (`sum_le_four_lam`);
* `verify7` / `verify40`, `decide`-computations over the (short) lists `candL 2 = 73` and
  `candL 4 = 4681` elements, and hence `mem_the7 : dominant ∧ posCon (lam - ν) → ν ∈ the7`,
  `mem_the40 : dominant ∧ posCon (2•lam - ν) → ν ∈ the40`, plus `the7_nodup`, `the40_nodup`
  (so the second one says **exactly 40** dominant weights lie below `2λ` — the upper bound for the
  tensor square), and `mem_the7_cases` (the case split over the seven).

**`Submission/E8Numerics.lean`** (sorry-free, imported here) is the *candidate character*:
`qq = qZ`, `normTable`, `normOk` (`⟪v,v⟫ ∈ {0,2,4,6,8,10}`), the table `tab`, and
`mfun v = if normOk v then tab (dcX v) else 0` (with `mfunAux` so that the norm test is evaluated
once and `dcX` only for the ~500 surviving weights).  Proven there: `mfun_support`
(`mfun v ≠ 0 → lam - v = 0 ∨ posCon (lam - v)`) and `mfun_dcX` (`mfun (dcX v) = mfun v`),
i.e. hypotheses (b) and (c) of `eq_of_freudenthal` for the candidate.

**The six Freudenthal recursion checks (hypothesis (d)) are NOT yet in the repository.**  They are
pure `decide`-computations but *expensive*; measured facts (this session):

* the whole environment is needed (~20 s baseline); a `decide` over 120 iterations of a trivial
  function costs ~25 s, i.e. a `Finset.sum` over `Fin n` costs ≈ 0.02 s *per element* (the
  `Finset.univ` machinery dominates), and one `pR j` lookup (`posR.get`, a 120-element list of
  `![…]` vectors) costs ≈ 0.04 s;
* consequently the recursion check at `ν = ω₂` (840 terms (j,k), of which only 28 need `dcX`)
  costs **2m17s** of elaboration; the six checks together have 23040 terms, so the naive total is
  ≈ 1 hour — a large fraction of the comparator's budget;
* the fix is to replace the `Fin 8`/`Fin 120` `Finset.sum`s and the `pR`/`coords` lookups by
  *hand-written coordinate arithmetic* (as in the deleted `normQ`: 8 explicit products beat the
  `Finset` version by ~10×), i.e. to define
  `dot, cR : Fin 120 → Fin 8 → ℤ` (the `coords (pR j)`, as literal data), `brkR`, and to bridge
  with `List.all`-style `decide`-checks (`coords (pR j) = cR j`, `brk μ j = dot μ (cR j)`), and to
  use `Fin.sum_univ_eq_sum_range` (or a literal list sum over `pR`/`posR`) so that the kernel walks
  a literal list instead of `Finset.univ`.

**`Submission/IsotypicCount.lean`** (sorry-free, imported here): `ncard_isotypicComponents_eq_card`
— if a semisimple module `M` is the supremum of a finite family `N i` of pairwise non-isomorphic
simple submodules, then `M` has exactly `Fintype.card ι` isotypic components.  This is the
combinatorial half of the target count: one only has to exhibit forty pairwise non-isomorphic
simple summands spanning `V ⊗ V` (and then use `mem_the40` for the upper bound).

**`Submission/Sl2Span.lean`** (sorry-free, imported here): the local-finiteness input for
integrability — `pow_apply_eq_zero` (`f ^ (n+1) v = 0 → f ^ k v = 0` for `k ≥ n+1`), `span_pow_eq`
(the `f`-span of `v` is the span of the finite string `{v, f v, …, f^n v}`), `finite_span_pow`
(hence finite dimensional), `f_mem_span_pow`, and `e_mem_span_pow` (the span is `e`-stable when
`e v = 0` and `e (f w) = f (e w) + h • w`).

The other measured facts of this session: `dom7_eq : dom7 = {the 7}` etc. work with `decide` on
*`List`* membership but **not** on `Finset` equality (`Finset.decidableEq` gets stuck on the
`Quot`/`Multiset` representation), and typeclass synthesis of `Decidable (Dominant v)` fails
because `Dominant`/`posCon` are `def`s: use `Bool`-valued predicates (`allNonneg`, `posB`) instead.

## SESSION 13: the kernel-fast arithmetic engine, and the six Freudenthal recursion checks

**`Submission/E8Engine.lean` (sorry-free, imported here)** replaces the accessory definitions that
dominate kernel evaluation by hand-written ones, with the extensional guarantees proved by
`simp`/`decide`:

* `e8e (i j) = CartanMatrix.E₈ i j`, `srefE = sref`, `dcXE = dcX` (the dominant conjugate with a
  hand-coded Cartan matrix instead of the `!![...]` matrix literal);
* `mvn = E8inv *ᵥ ·`, `md` (an explicit 8-term dot product, `md_eq`), `htO = htOf`, `qE = qq`,
  `BintE = Bint`, `brkE = brk`;
* a hand-coded **balanced decision tree** `pRn` for the 120 positive roots, with `pRn = pR`
  (via `posR_eq_ofFn`), hence `brkF = brk`;
* `smulE`, `Gfun`, `GfunR`, `brkR`, `freudJ`, `freudS`;
* the bilinear form `bq` with `bq_add_left`, `bq_add_right`, `bq_smul_left`, `bq_smul_right`, the
  **quadratic formula for the norm**
  `qE_add_smul : qE (x + k • z) = qE x + k * (bq x z + bq z x) + k^2 * qE z`
  and `quad ν j k := qE ν + k*(bq ν (pRn j) + bq (pRn j) ν) + 2k^2` with `quad_eq_qE`.

**`Submission/E8Checks.lean` (sorry-free, NOT imported here — importing it costs ≈ 340 s of kernel
time)** supplies hypothesis `(d)` of `eq_of_freudenthal` for `mfun`:

* `sum_Icc_eq_of_gt` (pruning a sum over `Icc 1 N`), the height bound
  `Kb ν j = (htO (λ-ν)).toNat / (htOf αⱼ)`, the vanishing lemma `mfun_eq_zero_of_height`, and
  `freudGp_eq_freudG`: the loose sum of `(d)` equals its pruned form (**23040 terms → 4392**);
* `freudGq` (the same sum with the norm test replaced by the quadratic formula `quad`) and
  `freudGq_eq_freudGp`;
* the six `decide` checks `check_1 … check_6` at `ω₂, 2ω₈, ω₇, ω₁, ω₈, 0`, and
  **`freudenthal_mfun`**: Freudenthal's recursion for `mfun` at *every* dominant `ν ≠ λ` of the cone.

**Measured costs (the key engineering datum of this session).** The six checks cost ≈ 340 s of
kernel time in total (`ω₂` ≈ 25 s, `ω₈` ≈ 176 s, `0` ≈ 290 s); the marginal cost is ≈ 0.16 s per
term.  The `Finset` machinery is *not* the bottleneck (≈ 4 ms per summand, measured with a
constant summand), and neither is the norm test (`quad`, ≈ 4 ms per term): it is the evaluation of
`dcXE` on the ≈ 240 terms of the `ν = 0` check that survive the norm test (≈ 1.1 s each).  The
reason is structural: `srefE i v = fun j => v j - v i * e8e i j` is a **lambda**, so a weight
needing `d` reflections is represented by a term in which the original weight occurs `2^d` times —
kernel evaluation is *exponential* in the number of reflections.  Measured: `dcXE (pRn j)` for a
single **root** costs ≈ 1.9 s (a root needs ≈ 20 reflections; `2^20 ≈ 10^6`); the kernel does not
share `let` values (a `let`-bound `η` inside the summand made the `ν = 0` check *slower*: 158 s vs
147 s), and `k • pRn j` (`nsmul`) re-evaluates `pRn j` at every step (replacing it by a
coordinatewise `smulE` changed nothing, 297 s vs 303 s).

**Tested fixes (all measured this session, in `/tmp` scratch files):**

* a `List ℤ`-valued reflection with `List.zipWith` does *not* help (the entries stay thunks; ≈ 0.23 s
  per reflection step);
* an 8-field **structure** `W` with `srefW`/`pickNegW`/`dclW` (projections force the constructor, so
  the term stops doubling) *is* polynomial: 30/45/60 reflection steps cost ≈ 1.5/3/6 s, i.e.
  ≈ 0.05 s per step — but that is still ≈ 1 s per dominant conjugate, i.e. **no better** than the
  current engine for the roots that occur in the checks.

**Strategic consequence.**  Even with a value representation, kernel evaluation of the reflection
algorithm costs ≈ 0.05 s per step.  Certifying one character costs ≈ 5 min (measured: the six checks
of `E8Checks` together are 300–340 s); certifying the **40 characters of the constituents of
`V ⊗ V`** (≈ 10^5 reflected weights) is therefore ≈ 10^4 s of kernel time — *out of reach*.  The
decomposition of `V ⊗ V` thus needs a **mathematical** proof (Weyl character formula / Kostant
multiplicity formula, or PRV-type results), not a numerical certification.  The numerical
certification route remains viable only for the single character of `V` (done here).

**Commons published this session:** `Commons.Combinatorics.Finset.sum_Icc_eq_of_gt`
(`import Submission.Commons.Combinatorics.Finset.sum_Icc_eq_of_gt`) — pruning a sum over `Icc 1 N`
when the summand vanishes above `K` (the general form of the lemma used by `E8Checks`).

**Also learned:** `ℚ` is not kernel-decidable (`instDecidableEqRat` gets stuck), so every `decide`
computation must be stated over `ℤ` and upgraded to `ℚ` with `exact_mod_cast` (which does handle
`Finset.sum`); `Finset.Icc 1 (computed bound)` recomputed per `j` is cheap once the bound is
computed with the fast `htO`; `decide` on a `∀`-statement over `Fin 120` with a *free* variable is
impossible, so all `decide`-lemmas must be fully closed statements.

-/

/-!
# SESSION 14: the count `ncard = 40` and the three routes; the antisymmetric tensor-square lemma

**New file `Submission/HWTTensor.lean`** (imported here, sorry-free).  The first *elementary* half
of the PRV statement:

* `lie_antisym_tmul`: if `⁅e,f⁆ = h`, `⁅e,v⁆ = 0` and `⁅h,v⁆ = c • v`, then
  `(f·v) ⊗ v - v ⊗ (f·v)` is killed by `e` in `M ⊗ M`;
* `lie_h_antisym_tmul`: additionally `h · ((f·v)⊗v - v⊗(f·v)) = (2c - d) • ((f·v)⊗v - v⊗(f·v))`
  when `⁅h,f⁆ = -d • f`;
* `e8_antisym_lieE`, `e8_antisym_lieH`, `e8_hwt_antisym`: in `e₈`, if `v` is a highest weight
  vector of weight `ψ` then `Zt i v := (fᵢ·v) ⊗ v - v ⊗ (fᵢ·v)` is a highest weight vector of
  weight `2ψ - αᵢ`.  Hence `L(2λ - αᵢ) ⊆ V ⊗ V` whenever `2λ - αᵢ` is dominant (for
  `λ = ω₁+ω₈`: `i = 0` and `i = 7`).

Also in the file: `linearIndependent_of_weight_ne` (two nonzero eigenvectors of `h` with different
eigenvalues are linearly independent), `e8_Zt_ne_zero` (`Zt i v ≠ 0` when `v ≠ 0` and `fᵢ·v ≠ 0`),
and `e8_hwt_tmul` / `e8_hwt_tmul_weight` (`u₁ ⊗ u₂` of two vectors killed by all `eᵢ` is killed by
all `eᵢ`, with weight the sum).  The last two give, for free, the constituents `L(μ₁+μ₂)` for
μ₁, μ₂ ∈ {λ, ω₂, ω₇, ω₁, 2ω₈, ω₈, 0} — these 25 dominant weights are exactly the sums of two of the
seven dominant weights of `V` (Python: 25 of the 40 `∈ the40`); together with the two
`2λ - αᵢ`-constituents this accounts for 27 of the forty.

The construction does **not** iterate: with `D_i := f_i⁽¹⁾ - f_i⁽²⁾`, `D_j z` is a highest weight
vector iff `z` is balanced (`h⁽¹⁾z = h⁽²⁾z`), and `D_i (v⊗v)` is not balanced.

**Numerical findings of this session** (details in `Submission/Work/pydata/SESSION14_NOTES.md`):

* every one of the 40 dominant weights `ν ≤ 2λ` is a sum `wλ + w'λ` of two `W`-conjugates of `λ`
  (40/40, `probe3.py`); `ν - λ` is a weight of `V` for all 40 (`probe4.py`);
* the **Racah–Speiser/Klimyk formula** `c_ν = Σ_{w∈W} (-1)^{ℓ(w)} m(ν + ρ - w(λ+ρ))` reproduces all
  forty multiplicities of `SUMMARY.txt` exactly, with only 1–94 nonzero terms per `ν`
  (`probe5.py`); the completeness of that list of terms is the obstruction: the a-priori candidate
  set `{w : Λ - wΛ ⪯ 2λ - ν}` has up to `10⁶` elements (`probe7.py`).

**Consequence for the plan.**  The upper bound `ncard ≤ 40` is free (constituents' highest weights
are weights of `V ⊗ V`, hence `⪯ 2λ`, hence among `the40`).  The lower bound needs either

* **PRV** (`L(wλ + w'λ) ⊆ L(λ)⊗L(λ)` for `wλ+w'λ` dominant) — a deep theorem, or
* the **Weyl character formula** (giving the Racah–Speiser formula) **plus** the character of `V`
  (`m = mfun`, i.e. the Freudenthal trace argument + integrability) **plus** a completeness
  argument for the finite list of contributing weights.

The dimension `dim V = 779247` needs the **Weyl dimension formula** (⟸ WCF) or the orbit sizes
`30240, 17280, 6720, 2160, 240, 240, 1` (⟸ `|W(E₈)| = 696729600` and the parabolic stabilisers
`W(D₆), W(A₇), W(E₆)×W(A₁), W(D₇), W(E₇)`).  Both remaining pieces are classical theorems Mathlib
does not have; the Weyl character formula is the common bottleneck.  Useful existing Weyl-group
infrastructure lives in the commons
(`Commons.LinearAlgebra.Matrix.Cartan.{sref,wact,wact_memP,image_wact_P,wact_sum_P,posRoot_finite,
P,E8_weyl_posRoots_fixes_rho,E8_dominant_unique}`).
-/

/-!
# SESSION 15: the character of `V` is **norm-determined**; a route to the count that avoids PRV

This session was mainly reconnaissance and the discovery of two structural facts that change the
plan.  No new Lean file was added by it (two lemmas were sent to the fleet:
`Commons.Algebra.Lie.Sl2.uea_mul_pow`, the `sl₂` power identity
`ιe * (ιf)^n = (ιf)^n * ιe + n • ((ιf)^(n-1) * (ιh - (n-1)))`, and
`Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_sum_le_two`).

## 1. The support of `mfun` and its `norm`-determination (the key new fact)

All the following are cheap *mathematical* facts (no `dcX` evaluation involved):

* **(a)** every entry of `E8inv` is `≥ 2` (`decide` on the `8 × 8` integer matrix).
* **(b)** for a *dominant* `ν` (all `νᵢ ≥ 0`): `qZ ν = ∑ᵢⱼ E8invᵢⱼ νᵢνⱼ ≥ 2 (∑ᵢ νᵢ)²`, hence
  `qZ ν ≤ 10 ⟹ ∑ᵢ νᵢ ≤ 2`.  Consequently the dominant weights of norm `≤ 10` are among
  `0, ωᵢ, 2ωᵢ, ωᵢ+ωⱼ` — a handful of cases, and a `decide` check gives:
  **the dominant `ν` with `qZ ν ≤ 10` are exactly `the7`** (their norms are `10, 8, 6, 8, 4, 2, 0`).
* **(c)** For *any* `ν` with `qZ ν ≤ 10`, its dominant conjugate `dcX ν` is dominant of the same norm
  `qZ (dcX ν) = qZ ν` (`qZ_dcX`), hence lies in `the7`; conversely `mfun ν ≠ 0` iff
  `dcX ν ∈ the7` and `normOk ν`.  By (b): **`mfun ν ≠ 0 ↔ qZ ν ≤ 10`**, i.e.
  `supp (mfun) = {ν : qZ ν ≤ 10}`, and the number of such `ν` is `56881 = Σ_{q} N_q` with
  `N_q = 240 σ₃(q/2) = 1, 240, 2160, 6720, 17520, 30240`.
* **(d)** The two elements of `the7` of norm `8` are `ω₂ = e₁` and `2ω₈ = 2e₇` and **`tab` takes the
  same value `7` on both**; on the other norm classes `the7` has a single element.  Hence
  **`mfun ν` depends only on `qZ ν`**: `mfun ν = m_{qZ ν}` where `m_0 = 1407, m_2 = 455, m_4 = 133,
  m_6 = 34, m_8 = 7, m_10 = 1`.
* **(e)** `dim V = Σ_ν mfun ν = Σ_{q ∈ {0,2,4,6,8,10}} m_q · N_q = 1407·1 + 455·240 + 133·2160 +
  34·6720 + 7·17520 + 1·30240 = 779247` ✓.

The `N_q` are computable in the kernel by a *pruned* nested-loop enumeration: for `qZ ν ≤ 10` every
coordinate satisfies `|νᵢ| ≤ 4` (Cauchy–Schwarz for the form `⟪x,y⟫ = xᵀA⁻¹y`:
`νᵢ = ⟪ν,αᵢ⟫`, `⟪αᵢ,αᵢ⟫ = 2`, so `νᵢ² ≤ 2·qZ ν ≤ 20`), and since **all** entries of `E8inv` are
`≥ 0` the *partial* quadratic forms on the first `k` coordinates are `≤ qZ ν`, so an enumeration
that prunes at every level visits only `O(10⁵)` nodes (the last level has `56881`), each costing a
few integer operations — feasible for the comparator, unlike the `dcX`-based computations.

## 2. A route to `ncard = 40` that avoids PRV: Klimyk + word certificates

Take the **Klimyk formula** for the tensor square, a consequence of the Weyl character formula for
`V(λ)` (`λ = ω₁+ω₈`, `Λ = λ+ρ`):

  `c_ν = [V⊗V : L(ν)] = Σ_{w∈W} ε(w) · m_V(ν + ρ - w Λ)`   (`m_V = mfun`).

By §1, `mfun` is *norm-determined*, so **evaluating the summand needs no `dcX` at all** — this was
the obstruction that killed the numerical route in SESSION 13.  Rewriting the sum over the weights
`η := ν + ρ - wΛ` gives

  `c_ν = Σ_{η ∈ supp mfun} mfun(η) · #{w : wΛ = ν+ρ-η} · ε(w)`,

a sum over at most `56881` weights `η` (enumerable, §1(e)), of which the only ones that can
contribute are those satisfying the *cheap* necessary condition `qZ (ν+ρ-η) = qZ Λ`; in practice
`≤ 100` per `ν`.  For each of those candidates a **certificate** decides the term:

* a *membership* certificate is an explicit word `L` with `wact L (ν+ρ-η) = Λ`; then
  `ν+ρ-η ∈ WΛ` and `ε(w) = (-1)^{|L|}` (parity is well defined because it equals `det`);
* an *exclusion* certificate is an explicit word `L` with `wact L (ν+ρ-η) =` a **dominant** weight
  `≠ Λ`; by `E8_dominant_unique` the dominant conjugate is then `≠ Λ`, so `ν+ρ-η ∉ WΛ` and the term
  is `0`.

Both certificates are cheap to *verify* in the kernel (a word of length `≤ ~120` folded on a vector);
they are cheap to *find* outside Lean (the `dominant`/`dc` algorithm of `Submission/Work/pydata`
produces exactly the required word, and `E8Orbit.dcX`/`E8Character.dcList` is its formal version).
The upper bound `ncard ≤ 40` is free (`mem_the40` + the support bound); the lower bound reduces to
`c_ν ≥ 1` for the forty `ν ∈ the40`, each of which is a finite sum of the above shape.

**So: PRV is not needed for the count** — the Weyl character formula (or rather its Klimyk
corollary) plus cheap certificates suffice.  This is the main strategic finding of the session.

## 3. The (revised) critical path

1. **Integrability**: `fᵢ^(λᵢ+1) = 0` on `L(λ)` for `λ` dominant integral.  Pieces:
   (i) the `sl₂` power identity (fleet: `Commons.Algebra.Lie.Sl2.uea_mul_pow`);
   (ii) `eᵢ · (fᵢ^(λᵢ+1) v) = 0` and `eⱼ · (fᵢ^n v) = 0` for `j ≠ i` (from `⁅eⱼ,fᵢ⁆ = 0`):
       both are immediate in the ⋆-model once (i) is available;
   (iii) the submodule `U(e₈)·(fᵢ^(λᵢ+1) v)` is **proper** — it is a highest weight module with
       highest weight `μ = λ - (λᵢ+1)αᵢ` whose weights are all `⪯ μ`, and `λ ⋠ μ`; the standard
       route in the ⋆-model is the universal property of `V E8` as the Verma module
       (`Submission/VermaModel.lean`), or `U(e₈) = U(n⁻)U(b)` + `U(b)z = ℂz` for a primitive `z`;
   (iv) from (iii): `fᵢ^(λᵢ+1) v ∈ N` (the unique maximal submodule), and then
       `{m : fᵢ^N m = 0 for N ≫ 0}` is a `U(e₈)`-submodule containing `v`, hence everything
       (needs `ad fᵢ` locally nilpotent on `U(e₈)`, cf. `Commons.Algebra.Lie.ad_locallyNilpotent_of_generators`).
2. **W-invariance** of the character of `L(λ)`: from integrability, via the `𝔰𝔩₂`-string argument
   (`Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm`, `Commons.Algebra.Lie.Sl2.string_of_locallyNilpotent`).
3. **The Freudenthal trace argument** for the actual character of `L(λ)` (no finiteness of the module
   needed: only finite-dimensional weight spaces, `Ω` acting by the scalar `(λ,λ+2ρ)_κ` — available
   as `E8Casimir.Omega_smul_of_cyclic` —, the coroot identity `E8Casimir.eRoot_comm_fRoot` and
   `LinearMap.trace_comp_comm'`).
4. `eq_of_freudenthal` then gives `char(L(λ)) = mfun`, hence **`dim V = 779247`** by §1(e), and the
   set of weights of `L(λ)` is `∪_{ν ∈ the7} W·ν`.
5. **Weyl character formula** in the form needed: define `χ := A_{Λ}/A_ρ` formally.  Prove that
   `χ` and the character of `L(λ)` both satisfy (a)–(d) of `eq_of_freudenthal` — for `χ` this is a
   formal alternation computation (the Weyl denominator identity `A_ρ = e^ρ Π_{α>0}(1-e^{-α})` is
   the only extra input); for the character it is steps 2–3 — hence `χ = char(L(λ))` and the
   **Klimyk formula** follows.  This needs the Weyl group as a group with `ε = det` and the
   denominator identity (the existing commons gives the reflection action, the dominant chamber as
   a fundamental domain and the height bounds).
6. **The count**: §2 (enumeration of `supp (mfun)`, certificates, `c_ν ≥ 1` for the 40).

Steps 1–4 give the dimension; steps 5–6 give the count.  Neither needs PRV.

## 4. New files of this session (both sorry-free and imported here)

* **`Submission/E8Support.lean`** — the support/norm structure of §1:
  `E8inv_ge_two`, `two_sum_sq_le_qZ`, `dominant_sum_le_two`, `mem_the7_of_norm_le` (a `decide`
  check over `candL 2`), and the capstones **`mfun_eq_mnorm`** (`mfun v = mnorm (qq v)`) and
  **`mfun_ne_zero_iff`** (`mfun v ≠ 0 ↔ qq v ∈ {0,2,4,6,8,10}`).  Build cost ≈ 36 s.
* **`Submission/E8Integrable.lean`** — the first step of the integrability argument of §3(1):
  `kI`, `lam_eq_kI`, `Ebar_v`, `Hbar_v`, `Ebar_Lbar_comm`, `Ebar_Lbar_pow_comm`, and the capstone
  **`Ebar_Lbar_pow_v (i j) : Ebar E8 lam j (((Lbar E8 i) ^ (kI i + 1)) v) = 0`**: the null vector
  `fᵢ^(λᵢ+1) v` of `M(ω₁+ω₈)` is killed by every raising operator, i.e. it is a primitive (highest
  weight) vector of weight `λ - (λᵢ+1)αᵢ`.  The proof uses the fleet lemma
  `Commons.Algebra.Lie.Sl2.uea_mul_pow_aux` and the `U(e₈)`-level Serre relations
  `E8Weights.commutator_E_F`, `E8Weights.commutator_H_F` (deliberately avoiding the `⁅·,·⁆`-instance
  diamond on `e₈ ℂ`, which is a real hazard here: `serreLie_*` lemmas do not rewrite inside
  `VermaWeight`-flavoured goals because a shadowing `LieRingModule` instance is in scope).
  Build cost ≈ 12 s.

## 5. What the next session should do (in order)

1. `Submission/E8Integrable.lean`: finish integrability — prove `U(e₈)·(fᵢ^(λᵢ+1) v) ≠ V`
   (properness: exhibit the universal property of `V E8` as the Verma module `M(μ)` of weight
   `μ = λ - (λᵢ+1)αᵢ`, so all weights of the image are `⪯ μ`; `λ ⋠ μ` because `λ - μ = (λᵢ+1)αᵢ`),
   then the "locally `f`-nilpotent vectors" argument to get `fᵢ^(λᵢ+1) = 0` on `L(λ) = V/N`.
2. The `𝔰𝔩₂`-string argument for the `W`-invariance of the character (step 2 of §3).
3. The Freudenthal trace argument (step 3), then `eq_of_freudenthal` and `dim V = 779247`
   (either via `∑_ν mfun ν = ∑_q m_q N_q` of §1, or via the Weyl dimension formula of §3(5) once the
   WCF is available — note `E8RootSystem.weyl_dim_e8` already evaluates the product to `779247`).
4. The Weyl character formula and the Klimyk corollary (§3(5)), then the count (§2).


# SESSION 16: the PBW triangular decomposition, and **integrability's first half is PROVED**

This session closed the "properness" gap of SESSION 15 and built the spanning theory it needed.
Three new files, all sorry-free and imported above.

## 1. `Submission/E8PBW.lean` — the triangular-decomposition spanning of `U(e₈)`

`U = U(e₈)` is spanned by the *sorted monomials* `f^{a} h^{b} e^{c}` (a negative monomial, then a
Cartan monomial, then a positive monomial, in that order).  Only the three Serre commutation
relations `E8Weights.commutator_E_F` / `commutator_H_E` / `commutator_H_F` are used — no PBW basis.

* `fmono`, `hmono`, `emono` and their `append`/`cons` calculus;
* `h_mul_fmono` (`hᵢ f^{a} = f^{a} hᵢ - (∑ Aᵢⱼ) f^{a}`), `e_mul_hmono` (`eᵢ h^{b} ∈ span{h^{b'} eᵢ}`),
  `e_mul_fmono` (`eᵢ f^{a} ∈ S`), and the closure of `S = span{f^{a} h^{b} e^{c}}` under left
  multiplication by `fᵢ`, `hᵢ`, `eᵢ`;
* **`S_eq_top : S = ⊤`** (via the subalgebra `T = {u | ∀ v ∈ S, u * v ∈ S}` and
  `Commons.RepresentationTheory.LieEnveloping.adjoin_range_iota` +
  `Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators`);
* **`smul_mem_fspan`**: if `x` is killed by all `eᵢ` and `hᵢ • x = μᵢ • x`, then for every `u ∈ U`,
  `u • x ∈ fspan x := span{f^{a} • x}`.  **Consequence: the submodule generated by a primitive vector
  has all its weights below the weight of the vector** — this is the missing "highest weight module"
  statement.

## 2. `Submission/E8NullVector.lean` — the null vector lies in the maximal submodule

* `eps : V →ₗ[ℂ] ℂ`, the descended augmentation (coefficient of the highest weight vector), with
  `eps (mk (wordElt w)) = if w = [] then 1 else 0` and `eps v = 1`;
* `Z m = span{mk (wordElt w) : m ≤ content w}` (`Z_le_ker_eps`, **`v_notMem_Z`**: for `m ≠ 0`, a
  word of content `≥ m` is nonempty, so `ε` kills `Z m` but not `v`);
* `m0 i c = c·eᵢ`, `Lbar_mem_Wm`, `Lbar_pow_mem_Wm`, `fmono_smul_mem_Wm`, `Wm_le_Z`;
* **`nullvector_mem_of_max`**: for *every* submodule `N` with `v ∉ N`, the null vector
  `(Lbar i)^(kI i + 1) v` lies in `N` (proof: `U·x ⊆ fspan x ⊆ Z (m0 i (kI i+1)) ∌ v`, and a
  submodule not containing `v` is contained in the maximal one);
* **`f_pow_smul_vbar`**: in `L = V ⧸ N`, `(fᵢ)^(kI i + 1) • vbar = 0`.

**This is the first half of integrability** (SESSION 15's step (iii)+(iv) for the *null vector*).

## 3. `Submission/E8LocallyNilpotent.lean` — local nilpotence of `fᵢ` on `L`

* `Commons.Algebra.Lie.UeaNilpotent.ad_locallyNilpotent_uea` (fleet, **PROVED**): if `ad f` is
  locally nilpotent on `L` then the commutator operator `u ↦ ι f * u - u * ι f` is locally
  nilpotent on `U(L)`.
* `Commons.Algebra.Lie.UeaNilpotent.smul_eq_zero_of_ad_local` (fleet, **PROVED**): consequently, in
  any module, `f` is locally nilpotent on `u • m` whenever it is locally nilpotent at `m`.
* `toEnd_pow_eq`, `quot_hι` (the quotient's `U`-action is the Lie action), and the capstone
  **`f_locallyNilpotent`**: `fᵢ` is locally nilpotent on `L = V ⧸ N` (using
  `SerreConstruction.hloc_F`, the local nilpotence of `ad (SerreF i)` on `e₈`).
* **`e_locallyNilpotent`**: `eᵢ` is locally nilpotent on `L = V ⧸ N`, from the word-length
  filtration `elen K = span{mk (wordElt w) : |w| ≤ K}` (`Eword_mem_short`, `Ebar_mem_elen`,
  `Ebar_mem_elen_zero`): `Ebar i` deletes one letter, so `(Ebar i)^(K+2)` kills `elen K`.

So **both `eᵢ` and `fᵢ` are locally nilpotent on `L`**, which is exactly the hypothesis of
`Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm`.

## 4. What is left for `W`-invariance of the character

`Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm` gives the symmetry of `h`-eigenspace
dimensions for an `𝔰𝔩₂`-triple with both `e` and `f` locally nilpotent.  Applied to
`(Hbar i, Ebar i, Lbar i)` on the **`αᵢ`-string module** `W := ⊕_{ν' : ν'ⱼ = νⱼ (j ≠ i)} L_{ν'}` it
gives `dim L_ν = dim L_{sᵢν}`.  Still missing:

1. ~~`eᵢ` is locally nilpotent on `L`~~ — **done this session** (`e_locallyNilpotent`);
2. the weight-space structure of `L = V ⧸ N` — suggested: `Lw m := (Wm m).map (N.mkQ)`, so that
   `L = ⨆_m Lw m`, `Lw m` is finite-dimensional, `Hbar i` acts on `Lw m` by the scalar `wt m i`,
   and the `αᵢ`-string of the weight `wt m` is `⨆_{k : ℤ} Lw (m + k • eᵢ)`, whose `Hbar i`-eigenspaces
   are exactly the individual `Lw (m + k • eᵢ)` (this identification in the other Cartan directions
   is what upgrades the *summed* identity of `sl2_eigenspace_finrank_symm` to the individual
   `dim L_ν = dim L_{sᵢν}`);
3. finiteness of the `αᵢ`-string: the weights of `L` lie in `λ - ℕΦ⁺` (bounded above in the `αᵢ`-
   coordinate) and `eᵢ`, `fᵢ` are locally nilpotent (bounded below); then apply
   `Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm` to the (finite-dimensional, `𝔰𝔩₂`-stable)
   string module `W`, whose `𝔰𝔩₂`-relations are inherited from `е₈`.

After that `eq_of_freudenthal` (SESSION 10) with (a),(b),(c),(d) gives `char(L(ω₁+ω₈)) = mfun`,
hence `dim L(ω₁+ω₈) = 779247` (SESSION 15 §1(e)), and the remaining work is only the count
`ncard = 40` (Weyl character formula / Klimyk, SESSION 15 §2).

## 5. Session 16 bookkeeping

* Kernel time: `Submission/E8PBW.lean` ≈ 60 s, `E8NullVector` ≈ 25 s, `E8LocallyNilpotent` ≈ 15 s.
* `E8Checks.lean` is still deliberately **not** imported (≈ 340 s).
* Lean pitfalls met (all worked around): a `let`-bound submodule in a goal makes `rw` fail with a
  "stuck typeclass instance" — use a top-level `def` (this is why `fspan` is a `def`);
  `Submodule.span_induction` in this Mathlib takes its membership proof **last**, so the
  `induction … using … with` form must not be used on terms (only on hypotheses).

# SESSION 17: the weight-space decomposition of `L(ω₁+ω₈)` is BUILT, and the plan for the rest

**New file `Submission/E8WeightSpaces.lean`** (namespace `Submission.E8WeightSpaces`, imported
here, sorry-free).  It provides the *weight-space structure* of the simple quotient
`L = V ⧸ N` of the Verma module (SESSION 16 built `V`, its maximal submodule `N`, the local
nilpotence of `eᵢ` and `fᵢ`, and the PBW triangular decomposition).  Contents:

* `Wm_finite` : the word space `Wm m` (spanned by the words of letter-multiplicity vector `m`) is
  finite-dimensional, using the commons lemma
  `Commons.Data.List.finite_setOf_count_eq` (finitely many words with prescribed content);
* `Lw N m := (Wm m).map (mkQc N)` — the image of `Wm m` in `L`, with `mk_mem_Lw`,
  `iSup_Lw_eq_top` (the `Lw N m` span `L`), `toLw`/`toLw_surjective` and **`Lw_finite`**
  (`Module.Finite ℂ ↥(Lw N m)`);
* `endU N u` : the ℂ-linear endomorphism `x ↦ u • x` of `L` attached to `u : U(e₈)` (built from
  `Submission.Enveloping.module_smul_comm_scalar`), with `endU_apply`, `endU_mul/add/sub`;
* **`endU_h_apply_mem_Lw`** : `Hᵢ` acts on `Lw N m` by the scalar `wt m i`;
* the *killer* projection `killerL N m₀ m j` (the descended `Hbar`-killer of `VermaWeight`), with
  `killerL_apply_mem_Lw`, `killerL_mem_Lw`, `prod_killerL_apply`, and the **uniqueness of the
  weight decomposition** `eq_zero_of_sum_eq_zero` (a finite sum of elements of distinct weight
  spaces vanishes iff all terms do);
* `exists_decomp_Lw` : every element of `L` is a finite sum of weight components;
* `wtZ m` : the *integral* weight of the multiplicity vector `m` (`wtZ m = λ - ∑ mᵢ αᵢ`, with
  `wt_eq_cast : wt m i = ((wtZ m i : ℤ) : ℂ)`, `wtZ_injective`);
* **`Lwt N μ := ⨅ i, eigenspace (endU N (Hᵢ)) (μ i)`** — the joint Cartan eigenspace, indexed by
  *integral* weights, with `mem_Lwt_iff`, `Lw_le_Lwt`, and the **identification**
  `Lw_eq_Lwt : Lw N m = Lwt N (wtZ m)` (proved with the killer projection: on a joint eigenvector
  the killers act by non-zero scalars, which inverts the decomposition).  Hence
  `Lwt_finite`, `iSup_Lwt_eq_top`;
* the **weight shifts** `endU_e_apply_mem_Lwt` (`eⱼ` shifts the weight by the `j`-th root:
  `μ ↦ μ + Aᵢⱼ`), `endU_f_apply_mem_Lwt` (`μ ↦ μ - Aᵢⱼ`), from the commutators
  `commutator_H_E`/`commutator_H_F` of `Submission.E8Weights`;
* **the support bound** `exists_wtZ_of_mem_Lwt` : every non-zero weight vector has a weight of the
  form `wtZ m`, i.e. the support of `L` is contained in `λ - ℕΦ⁺` (this is hypothesis (b) of
  `E8Character.eq_of_freudenthal`), together with
  `eq_of_mem_Lwt_of_mem_Lwt` (a non-zero vector cannot have two different weights).

### `W`-invariance is PROVED: `Submission/E8WInvariance.lean`

`Submission/E8WInvariance.lean` (namespace `Submission.E8WInvariance`, imported here, sorry-free)
proves the infinitesimal form of `W`-invariance of the character of `L = V ⧸ N`:

* `shift i ν c = ν + c·αᵢ` (with `shift_zero`, `shift_succ`, `shift_pred`, `shift_apply_eigen`,
  `shift_neg : shift i ν (-νᵢ) = sref i ν`);
* `Str i ν = ⨆ c : ℤ, Lwt (ν + cαᵢ)` — the `αᵢ`-string through `ν`, which is stable under `eᵢ`,
  `fᵢ` and `Hᵢ` (`endU_e_maps_Str`/`endU_e_mem_Str` and the analogues for `f` and `h`);
* the eigenspace identification **`Str_inf_eigenspace`**
  `Str i ν ⊓ eigenspace (Hᵢ) (νᵢ) = Lwt ν` (and `Str_inf_eigenspace_neg` with `-νᵢ` and `sref i ν`)
  — this is the commons lemma `Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq` applied to the
  independent family of `Lwt`-spaces (the eigenvalues `νᵢ + 2c` are pairwise distinct);
* the restricted operators `StrH`, `StrE`, `StrF` on the string with the `𝔰𝔩₂`-relations
  (`Str_sl2_1`, `Str_sl2_2`, `Str_sl2_3`) and their local nilpotence
  (`StrE_localNilpotent`, `StrF_localNilpotent`, the latter using the maximality of `N`);
* the eigenspace linear equivalence `eigenspaceEquiv` and
**`finrank_Lwt_sref`** :
  `Module.finrank ℂ ↥(Lwt N ν) = Module.finrank ℂ ↥(Lwt N (sref i ν))` for every integral weight
  `ν` and every simple reflection `sᵢ`.

This is hypothesis **(c)** of `E8Character.eq_of_freudenthal` (modulo iterating the simple
reflections along the explicit list produced by `dcX`, which is a finite bookkeeping step).

Two lemmas were commissioned from the fleet this session:
`Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_count` (the enumeration of the `56881` lattice
points of squared length `≤ 10`, with the norm distribution `1, 240, 2160, 6720, 17520, 30240` —
this is what turns `∑_ν mfun ν = 779247` into a finite computation) and
`Commons.LinearAlgebra.End.sl2_span_finite_stable` (the `𝔰𝔩₂`-span of a finite-dimensional
subspace is finite-dimensional and stable — the technical core of `W`-invariance).

### The precise remaining plan

1. **`W`-invariance** (hypothesis (c)): for `x ∈ Lwt N (wtZ m)` and `i : Fin 8`, let
   `M := span{fᵢ^a eᵢ^b x' : x' ∈ Lwt N (wtZ m), a b ∈ ℕ}`.  By
   `Commons.LinearAlgebra.End.sl2_span_finite_stable`, `M` is finite-dimensional and stable under
   `hᵢ = endU N (Hᵢ)`, `eᵢ = endU N (Eᵢ)`, `fᵢ = endU N (Fᵢ)`; by the weight shifts, the weights of
   `M` lie in the `αᵢ`-string through `wtZ m`, so the `hᵢ`-eigenspace of `M` at the eigenvalue
   `(wtZ m)ᵢ` is exactly `M ⊓ Lwt N (wtZ m)` and the one at `-(wtZ m)ᵢ` is
   `M ⊓ Lwt N (sᵢ (wtZ m))`.  Applying `Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm`
   gives `dim (M ⊓ L_ν) = dim (M ⊓ L_{sᵢν})`, whence
   `dim L_ν ≤ dim L_{sᵢν}`, and symmetrically `dim L_{sᵢν} ≤ dim L_ν`; hence
   **`finrank L_ν = finrank L_{sᵢν}`** for every weight `ν` and every simple reflection `sᵢ`.
   Iterating gives invariance under the dominant conjugate `dcX` — hypothesis (c).
2. **The Freudenthal trace argument** (hypothesis (d)): on the finite-dimensional weight space
   `L_ν`, take the trace of the Casimir `Ω` (`E8Casimir.Omega`), which acts by the scalar
   `K (wdual λ) (wdual (λ+2ρ))` because `L` is generated by the highest weight vector
   (`E8Casimir.Omega_smul_of_cyclic`).  Decomposing `Ω` along the κ-orthonormal basis `bIdx` and
   using `E8Casimir.eRoot_comm_fRoot` (the coroot identity), `LinearMap.trace_comp_comm'`
   (`tr (f∘e|L_ν) = tr (e∘f|L_{ν+α})`) and the Cartan trace
   `tr (Hᵢ H'ᵢ|L_ν) = (K (wdual ν) Hᵢ) (K (wdual ν) H'ᵢ) dim L_ν` gives
   `(Bint λ - Bint ν) · dim L_ν = 2 ∑_{j} ∑_{k ≥ 1} braek (ν+k·pR j, j) · dim L_{ν+k·pR j}`.
3. With (a), (b), (c), (d) supplied, `Submission.E8Character.eq_of_freudenthal` gives
   `char L = mfun` on all integral weights, so `dim L = ∑_ν mfun ν = 779247` by
   `E8Support.mfun_eq_mnorm` plus the lattice count of step 1 (or `E8Checks` + `mem_the7`).
4. **The count `ncard = 40`**: the upper bound is free (every constituent's highest weight is a
   dominant weight `⪯ 2λ`, and there are exactly `40` of those — `mem_the40`); the lower bound
   needs `c_ν ≥ 1` for the forty `ν`, i.e. the Weyl character formula (its Klimyk corollary
   `c_ν = ∑_w ε(w)·mfun(ν+ρ-w(λ+ρ))`) together with word certificates for the `W`-orbit
   membership of the ≤ 100 candidate weights per `ν` (SESSION 15 §2).

## 6. The shape of the remaining `W`-invariance argument (analysis, SESSION 16)

The Freudenthal recursion for the actual character of `L(λ)` (SESSION 15 §3(3), the trace argument)
reads, at **every** weight `ν ∈ λ - ℕΦ⁺`,

  `(⟪λ+ρ,λ+ρ⟫ - ⟪ν+ρ,ν+ρ⟫) · m_ν = 2 Σ_{j,k≥1} ⟪ν+kα_j, α_j⟫ · m_{ν+kα_j}`.

Since `htOf(λ - (ν+kα_j)) = htOf(λ-ν) - k·htOf(α_j)`, this determines `m_ν` from weights of smaller
`htOf(λ-·)` whenever the coefficient is non-zero.  By the Key Lemma
(`no_dominant_singular_weight'`, SESSION 10) the singular weights (`⟪ν+ρ,ν+ρ⟫ = ⟪λ+ρ,λ+ρ⟫`) inside
the cone `λ - ℕΦ⁺` are exactly the `W`-conjugates of `λ` (a singular `ν` has a dominant conjugate
`μ ⪯ λ` with the same norm, hence `μ = λ` by the Key Lemma).  So:

* at every **non-singular** weight the recursion determines `m_ν` — and the resulting values are
  automatically `W`-invariant at the non-singular part provided the values at the smaller heights
  are (the difference of the recursion at `ν` and at `sᵢν` has vanishing left-hand side *only*
  through the coefficient, so one must compare at the level of the *shifted* sums; this is the
  one place where the naive comparison fails: `⟪sᵢν+ρ,sᵢν+ρ⟫ = ⟪ν+ρ,ν+ρ⟫ - 2νᵢ`, because `sᵢρ = ρ-αᵢ`,
  so the two coefficients differ);
* the **singular** weights `ν = wλ` are the genuinely missing input, and this is what the
  `𝔰𝔩₂`-string argument (items 2–3 above) provides `m_{wλ} = m_λ = 1`.

**The string argument does *not* need the `αᵢ`-string of a weight to be connected** — here is the
argument as designed at the end of SESSION 16 (it avoids that subtlety entirely, and also avoids
any a-priori finiteness of `L`):

For a weight `ν` of `L`, let `L_ν` be its weight space and let
`M := span{fᵢ^a eᵢ^b x : a b ∈ ℕ, x ∈ L_ν}` be the `U(𝔰𝔩₂)`-span of `L_ν`.
* `M` is `𝔰𝔩₂`-stable: `eᵢ fᵢ^a eᵢ^b x = fᵢ^a eᵢ^{b+1} x + a(νᵢ+2b-a+1) fᵢ^{a-1}eᵢ^b x`
  (`Commons.Algebra.Lie.Sl2.uea_mul_pow`), `fᵢ` and `hᵢ` act by transport of the weight.
* `M` is finite-dimensional: `L_ν` is finite-dimensional, so local nilpotence of `eᵢ`, `fᵢ` on `L`
  gives **uniform** bounds `eᵢ^N(L_ν) = 0`, `fᵢ^{M_b}(eᵢ^b L_ν) = 0`, and `M` is therefore contained
  in the (finite) sum of the finitely many weight spaces `L_{ν+(b-a)αᵢ}` with `b < N`, `a < M_b`.
* The weights of `M` are contained in `ν + ℤαᵢ`, so the `hᵢ`-eigenspace of `M` at `νᵢ` is exactly
  `L_ν` and the one at `-νᵢ` is `M ∩ L_{sᵢν}`.
* `Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm` applied to `M` therefore gives
  `dim L_ν = dim (M ∩ L_{sᵢν}) ≤ dim L_{sᵢν}`, and the symmetric argument with the module generated
  by `L_{sᵢν}` gives the reverse inequality, hence **`dim L_ν = dim L_{sᵢν}`**.

What still has to be built for this: the weight spaces `L_ν` of `L = V ⧸ N` — concretely
`Lw m := (Wm m).map (N.mkQ)` with (i) `L = ⨆_m Lw m`, (ii) each `Lw m` finite-dimensional,
(iii) `Hbar i` acts on `Lw m` by `wt m i`, and (iv) the independence of the `Lw m` (distinct
`wt m`, i.e. the generalised-eigenspace argument, using the "killer" products of
`Submission.VermaWeight`); then each `Lw m` *is* the joint weight space and the identification in
the third bullet holds.  The same `Lw m` are needed anyway for the Freudenthal trace argument
(SESSION 15 §3(3)), so this is on the critical path twice.

## SESSION 18: THE FREUDENTHAL RECURSION IS PROVED — `char L(ω₁+ω₈) = mfun`

The single missing input of the whole character-theoretic half is now in place, together with the
identification of the character with the numerically defined `mfun`.

### 1. `Submission/E8Freudenthal.lean` (sorry-free, ~900 lines, imported here)

Namespace `Submission.E8Freudenthal`.  **`freudenthal_mul`**:

```
theorem freudenthal_mul (N : Submodule U V) (ν : Fin 8 → ℤ) (hcon : posCon (lamZ - ν)) :
    ((Bint lamZ - Bint ν : ℤ) : ℚ) * mul N ν
      = 2 * ∑ j : Fin 120, ∑ k ∈ Finset.Icc 1 (htOf (lamZ - ν)).toNat,
          ((brk (ν + k • pR j) j : ℤ) : ℚ) * mul N (ν + k • pR j)
```

where `mul N ν = (finrank ℂ ↥(Lwt N ν) : ℚ)`.  This is hypothesis **(d)** of
`Submission.E8Character.eq_of_freudenthal` — *and it is proved for every weight ν* (not only the
dominant ones; no dominance or non-singularity hypothesis is needed).

The proof is the classical trace argument, formalised directly (all lemmas below are in
`Submission.E8Freudenthal`):

* **The `U(e₈)`-level Casimir.**  `Omega_smul_vbar` (Ω acts on the highest weight vector `vbar` of
  `V ⧸ N` by `cas = K (wdual lamZ) (wdual (lamZ + twoRho))`) and `Omega_smul_eq` (`Ω · x = cas • x`
  for *all* `x : V ⧸ N`, via `Omega_smul_of_cyclic` and `cyclic_vbar`).  The needed
  `ι (eRoot k) • vbar = 0` is `eRoot_smul_vbar` (a raising root vector kills the highest weight
  vector; proved by the support bound `exists_wtZ_of_mem_Lwt` and the height argument, *not* by
  invoking the `n⁺`-spanning).
* **The trace decomposition** (`restOmega_eq`, `traceOmega_eq_sum`): since `Ω` acts by the scalar
  `cas`, `cas * dim L_ν = Σ_i trace(HᵢHⁱ|L_ν) + Σ_k trace(e_k f_k|L_ν) + Σ_k trace(f_k e_k|L_ν)`
  (all traces on the finite-dimensional weight space `Lwt N ν`); the Cartan part is
  `K(wdual ν)(wdual ν) * dim L_ν` (`sum_cartan`, `HHmap_apply`).
* **The restricted operators** `Eop`, `Fop`, `EFmap`, `FEmap` and the three relations
  (a) `EFmap - FEmap = K(wdual ν)(wdual (pR k)) • 1` (`EFmap_sub_FEmap`, the coroot identity),
  (b) `trace(FEmap|ν) = trace(EFmap|ν+pR k)` (`Str_eq_Ttr`, `LinearMap.trace_comp_comm'`),
  (c) `Str_step` : `Str k ν = Str k (ν+pR k) + K(wdual (ν+pR k))(wdual (pR k)) * dmul N (ν+pR k)`.
* **The master identity** `two_sum_Str` : `2 Σ_k Str k ν = (cas - c_ν) * dim L_ν`.
* **Unfolding** (`sh`, `Str_eq_sum`, `Str_last_zero`, `Str_eq_zero_of_htOf_neg`): iterating (c) `M`
  times gives `Str k ν = Σ_{s ∈ Icc 1 M} K(wdual (ν+s·pR k))(wdual (pR k)) * dim L_{ν+s·pR k}`
  plus the tail; the tail vanishes at `M = (htOf (lamZ - ν)).toNat` (all weights there have
  `htOf (lamZ - ·) < 0`, hence a trivial weight space, `lwt_bot_of_htOf_neg`).
* **The Weyl normalisation** of the Killing form: `bil μ ν = ∑ᵢⱼ μᵢ (A⁻¹)ᵢⱼ νⱼ`,
  `brk_eq_bil`, `bil_twoRho` (`bil μ (μ+2ρ) = Bint μ - Bint 0`, using `E8invM_symm`),
  `cas_eq`, `cnu_eq`, `K_wdual_pR`, `cas_sub_cnu`, `sixty_Str_eq`, `sixty_cas_sub_cnu`
  (all from the commons lemma
  `Commons.Algebra.Lie.SerreConstruction.killingForm_cartanDual`, proved this session by a fleet
  agent: `κ y z = (1/60) ∑ᵢⱼ μᵢ (A⁻¹)ᵢⱼ νⱼ` for `y, z ∈ e8W 0` with the prescribed pairings).
* `omega`-instances: the file opens with `attribute [local instance 100] LieRing.ofAssociativeRing`
  and `attribute [-instance] Submission.Enveloping.instLieRingModuleE8 / instLieModuleE8`
  (otherwise `⁅·,·⁆` on `L8` resolves to the `U`-action bracket and the `E8Casimir` lemmas do not
  match syntactically).  **All four new "weight-space finite-dimensional" instances** are in the
  file: `instFiniteLwt` (`Module.Finite ℂ ↥(Lwt N ν)`, by `Lw_eq_Lwt` + `exists_wtZ_of_mem_Lwt`).

### 2. `Submission/E8Multiplicity.lean` (sorry-free, imported here)

Namespace `Submission.E8Multiplicity`.  The three remaining hypotheses of
`Submission.E8Checks.mfun_unique` for `mul N`:

* `mul_lam : mul N lamZ = 1` (`finrank_Lwt_lam`: `Lwt N lamZ = Lw N 0` has dimension `1`);
* `mul_support : mul N w ≠ 0 → lamZ - w = 0 ∨ posCon (lamZ - w)`;
* `mul_dc : mul N (dc w) = mul N w` (`finrank_Lwt_foldl` + `finrank_Lwt_sref`).

Together with `freudenthal_mul` this gives the capstone

```
theorem mfun_eq_mul (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) :
    ∀ w : Fin 8 → ℤ, (Submission.E8Numerics.mfun w : ℚ) = mul N w
```

so **the character of `L(ω₁+ω₈) = V ⧸ N` is `mfun`**: the multiplicity of the weight `w` is
`mfun w = mnorm (qq w)`, i.e. the seven dominant multiplicities
`λ ↦ 1, ω₂ ↦ 7, ω₇ ↦ 34, ω₁ ↦ 133, 2ω₈ ↦ 7, ω₈ ↦ 455, 0 ↦ 1407`.
(Note `Submission.E8Checks` must therefore be imported — it carries `mfun_unique`, whose proof is
the `decide`-certified recursion for `mfun`; importing it costs ≈ 340 s of kernel time.)

### 3. What remains (the precise state)

* **`dim L = 779247`.**  From `mfun_eq_mul` one gets `dmul N ν = (mfun ν).toNat` for every ν.  Two
  steps remain:
  1. **the finrank decomposition** `finrank ℂ (V ⧸ N) = ∑_{ν ∈ S} dmul N ν` for a finite set `S`
     containing the support.  The support is contained in `{ν : qq ν ≤ 10}` (from
     `E8Support.mfun_ne_zero_iff`), whose elements are enumerated by the commons lemma
     `Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_count`; the independence of the family
     `{Lwt N ν}` is proved by the *killer* argument (for `ν ≠ ν'` pick `j` with `ν j ≠ ν' j`, then
     `((ν j - ν' j)⁻¹)(H_j - ν'_j)` kills `Lwt N ν'` and fixes `Lwt N ν`) — the same product trick as
     `Submission.E8WeightSpaces.eq_zero_of_sum_eq_zero`.  A fleet agent is proving the general
     `Commons.LinearAlgebra.Dimension.finrank_eq_sum_of_iSupIndep`
     (`iSupIndep p → ⨆ p = ⊤ → finrank = Σ finrank`) for this.
  2. **the arithmetic** `∑_{ν ∈ L} mnorm (qZ ν) = 779247` (`1·1407 + 240·455 + 2160·133 +
     6720·34 + 17520·7 + 30240·1`), delegated to the fleet as
     `Commons.LinearAlgebra.Matrix.Cartan.e8_lattice_mnorm_sum`.
* **`ncard = 40`** — unchanged from SESSION 15: the upper bound is free (`mem_the40`), the lower
  bound needs the 40 constituents.  With the character now known, the *numerical* certification of
  the forty characters is still out of reach (SESSION 13 §3), so this remains the hard step.
### 4. `dim L(ω₁+ω₈) = 779247` — PROVED (SESSION 18, later in the session)

`Submission/E8Finrank.lean` (sorry-free, imported here) now contains

```
theorem finrank_eq (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) :
    Module.finrank ℂ (V ⧸ N) = 779247
```

The ingredients:

* **the killer operators** `killerW N w₀ w j = (w₀ j - w j)⁻¹ (H_j - w_j)`: for `x ∈ Lwt N w` it acts
  by the scalar `(w₀ j - w j)⁻¹ (w j - w j) = 0` (`killerW_kills`) and for `x ∈ Lwt N w₀` by
  `(w₀ j - w j)⁻¹ (w₀ j - w j) = 1` when `w j ≠ w₀ j` (`killerW_fixes`); `killerW_mem` records that
  it preserves every weight space;
* `exists_killer`: a **product of killers** `P` (built by Finset induction, deliberately *not* with
  `Finset.prod` — `Module.End ℂ X` is not commutative, so `Finset.prod` does not apply) which
  preserves all weight spaces, fixes `Lwt N w₀` and kills `Lwt N w` for every `w ∈ s`;
* `disjoint_Lwt`: therefore `Disjoint (Lwt N w₀) ((S.erase w₀).sup fun w => Lwt N w)`;
* `finrank_sup_Lwt` (Finset induction with
  `Submodule.finrank_sup_add_finrank_inf_eq`) and `finrank_eq_sum_dmul`:
  `finrank ℂ (V ⧸ N) = ∑_{w ∈ S} dmul N w` for any finite `S` containing the support;
* the support is `{w : qq w ∈ {0,2,4,6,8,10}}` (from `mfun_ne_zero_iff` and `mfun_eq_mul`), hence
  contained in the lattice list `L` of `Commons.…e8_lattice_count`, and
  `∑_{w ∈ L} (mnorm (qq w)).toNat = 779247` by the fleet lemmas
  `Commons.…e8_lattice_toNat_sum` (the six norm counts `1,240,2160,6720,17520,30240` against the
  multiplicities `1407,455,133,34,7,1`) — no `L.length` hypothesis is needed since the summand
  vanishes off the six norm classes.

**All numerical content of the target theorem is therefore now formally verified except the count
`ncard = 40`.**

⚠️ A warning for the fleet: the general lemma
`finrank R M = ∑ i, finrank R ↥(p i)` for `iSupIndep p`, `⨆ p = ⊤` was requested for an arbitrary
ring with `StrongRankCondition` and **refuted** by a child agent (`R = ZMod 4 × ZMod 2` with the two
coordinate ideals: `iSupIndep` and spanning hold, both ideals have `finrank 0`, but `finrank R R =
1`).  The corrected version `Commons.LinearAlgebra.Dimension.finrank_eq_sum_of_iSupIndep_of_isDomain`
is committed; the proof *used here* (`finrank_sup_Lwt`) is a direct Finset induction over `ℂ`, where
additivity of `finrank` over `⊔` holds by `Submodule.finrank_sup_add_finrank_inf_eq`.**
-/



/-!
# SESSION 19: the tensor square `V ⊗ V` is set up; the count `ncard = 40` and its two halves

**New file `Submission/E8Tensor.lean` (sorry-free, imported here).**  Namespace
`Submission.E8Tensor`.  It builds the tensor square `T N = (V ⧸ N) ⊗[ℂ] (V ⧸ N)` of the
irreducible quotient `L(ω₁+ω₈) = V ⧸ N` and its weight structure:

* `deriv x : Module.End ℂ (T N)` — the tensor-product (derivation) action
  `x·(a⊗b) = x·a ⊗ b + a ⊗ x·b` of a Lie algebra element (`deriv_tmul`);
* `TLwt N ν` — the `ν`-weight space of `T N`, spanned by the pure tensors `a ⊗ b` with
  `a ∈ Lwt N ν₁`, `b ∈ Lwt N ν₂`, `ν₁ + ν₂ = ν` (`tmul_mem_TLwt`);
* `deriv_h_eq_of_mem_TLwt` — the Cartan `H_j` acts on `TLwt N ν` by the scalar `ν_j`
  (so `TLwt` is a genuine weight decomposition);
* `iSup_TLwt_eq_top` — the weight spaces span: `T N = ⨆_ν TLwt N ν`;
* `posCon_lam_sub_wtZ` (`λ - wtZ m ∈ ℕΦ⁺`) and `posCon_two_lam_of_tmul` — **the support bound**:
  a non-zero pure tensor of weights `ν₁`, `ν₂` has weight `ν₁+ν₂` with `2λ - (ν₁+ν₂) ∈ ℕΦ⁺`;
* `finite_quot` — for `N` the maximal submodule, `V ⧸ N` is **finite-dimensional** (the support is
  contained in the lattice list `L` of `e8_lattice_count`, and `V ⧸ N = ⨆_{w ∈ L} Lwt N w` is a
  finite supremum of finite-dimensional spaces), and `finite_tensor` — `T N` is
  finite-dimensional.  (Consequently Weyl's theorem, i.e.
  `Commons.Algebra.Lie.CompleteReducibility.isSemisimpleModule_enveloping`, makes `T N`
  semisimple over `U(e₈)` — this must be applied to the *derivation* instance, see below.)

## ⚠️ CRITICAL: instance resolution on `V ⊗ V`

The `Module (U(e₈)) (V ⊗ V)` instance that typeclass search picks **depends on the context**:

* in the abstract context of `Challenge.lean` / `Solution.lean` (where `V` is the `∃`-bound
  variable and its only `Module (U(e₈))` structure comes from
  `LeanEval.RepresentationTheory.lieModuleToEnvelopingModule`), the tensor square gets the
  **correct derivation action** (verified: `(ι x) • (a⊗b) = (ι x)•a ⊗ b + a ⊗ (ι x)•b`);
* but in a concrete context where a *concrete* `Module (U(e₈)) (V ⧸ N)` instance is in scope
  (e.g. `Submission.VermaWeight.instModuleUQuot`), the instance

  ```lean
  TensorProduct.leftModule : Module R (M ⊗[R] N)
  ```

  wins, giving the **wrong** structure `u • (a⊗b) = (u•a) ⊗ b` (for which `V ⊗ V ≅ V^{⊕ dim V}`
  has a *single* isotypic component, so the theorem would be false).

Since `∃`-elaboration *fixes* the predicate, the instance used in the final statement is the one
resolved while `V` is still abstract, i.e. the derivation action.  All the lemmas above are
therefore stated for the *explicit* derivation action `deriv` (not for an inferred `•`), so that
they apply in the final statement.  When assembling the final proof one must **not** let a
concrete `Module U (V ⊗ V)` instance leak into the statement.

## The precise remaining work for `ncard = 40`

### (A) The upper bound `ncard ≤ 40`

Every simple submodule `S ⊆ T N` (finite-dimensional, semisimple: Weyl's theorem) has a highest
weight vector `x ≠ 0` killed by all `eᵢ`, of a **dominant** weight `ν` which is a weight of `T N`,
hence (support bound) `ν ⪯ 2λ`, i.e. `ν ∈ Submission.E8Enum.the40` (`mem_the40`).  Since the map
`{simple submodules} → the40`, `S ↦ ν(S)`, is constant on isomorphism classes, and two simple
modules with the same `ν` are isomorphic, `ncard ≤ 40`.

**In flight (fleet)**: `Commons.Algebra.Lie.SerreConstruction.exists_dominant_primitive_of_ne_bot`
— every non-zero finite-dimensional `LieSubmodule` of an `e₈`-module contains a non-zero vector
`x` which is a simultaneous `SerreH i`-eigenvector of a *dominant* weight `ν` and is killed by all
`SerreE i` — i.e. exactly the primitive vector needed for (A) (module
`Submission.Commons.Algebra.Lie.SerreConstruction.exists_dominant_primitive_of_ne_bot`).

* (i) **DONE (fleet)**: `Commons.Algebra.Lie.SerreConstruction.exists_dominant_primitive_of_ne_bot`
  — a non-zero finite-dimensional `LieSubmodule` contains a non-zero vector `x` which is a
  simultaneous `SerreH i`-eigenvector of a **dominant** weight `ν` killed by all `SerreE i`.
  (Proof: take a weight vector of a maximal weight in the submodule, and use the 𝔰𝔩₂-string
  `fᵢx ≠ 0` whenever `νᵢ < 0`.)

* (ii) **DONE (fleet)**: `Commons.Algebra.Lie.SerreConstruction.lieEquiv_of_same_primitive_weight`
  — two finite-dimensional simple (irreducible) `e₈`-modules having non-zero primitive vectors of
  the same weight `ν` are isomorphic.  The proof (recorded below, in case a variant is needed)
  avoids the general Verma module `M(ν)` entirely:  let `S, S'` be finite-dimensional
  simple `e₈`-modules with primitive vectors `x`, `x'` of the same dominant weight `ν`; put
  `z := (x, x') ∈ S ⊕ S'` and `N := U(e₈)·z ⊆ S ⊕ S'`.  Two facts about `N`:

  1. **`N_ν = ℂ·z`.**  `N = U(n⁻)U(𝔥)U(n⁺)z = U(n⁻)·ℂz`, and the `ν`-weight part of `U(n⁻)`
     acting on `z` is `U(n⁻)_0 z = ℂz` (`U(n⁻)_0 = ℂ·1`, since every non-trivial monomial in the
     `fᵢ` has a strictly negative weight in the root lattice).  This uses exactly the triangular
     spanning `Submission.E8PBW.S_eq_top` plus the commutator lemmas
     `Submission.E8Weights.commutator_H_F` / `commutator_H_E`.
  2. Hence `K_ν = 0` for every *proper* submodule `K ⊆ N` (if `K_ν ∋ w ≠ 0` then `w = cz`,
     `z ∈ K`, `K = N`).  Therefore `(K + K')_ν = K_ν + K'_ν = 0` for proper `K, K'` while
     `N_ν ≠ 0`, so **the sum of two proper submodules is proper** and `N` has a *unique* maximal
     submodule, hence a *unique* simple quotient `Q`.

  Both `S` and `S'` are simple quotients of `N` (the projections `N → S`, `N → S'` are onto), so
  `S ≅ Q ≅ S'`.  ∎

  (The same argument gives that `M(ν)` — the Verma module — has a unique maximal submodule, by
  `N = M(ν)`; here we only need it inside the finite-dimensional `S ⊕ S'`.)

  The ingredient of step 1 that is *specific to our development* is the triangular spanning
  `Submission.E8PBW.S_eq_top` with the weight bookkeeping of
  `Submission.E8Weights.commutator_H_E` / `commutator_H_F`; the fleet agent formalised an
  equivalent statement in the commons directly from `Commons.Algebra.Lie.SerreConstruction`.

**With (i) and (ii) the upper bound `ncard ≤ 40` is now a pure assembly problem**:  map every
isotypic component `c ≠ ⊥` of `T N` (equivalently every non-zero `LieSubmodule`) to the dominant
weight `ν` of a primitive vector in a simple submodule of `c`
(`exists_dominant_primitive_of_ne_bot`), use `Independent`-style uniqueness
(`Submission.E8Tensor.eq_of_mem_TLwt_of_mem_TLwt`) to see that two isotypic components with the
same `ν` coincide (`lieEquiv_of_same_primitive_weight`), and note that `ν` is a weight of `T N`
hence (support bound) `posCon (2λ - ν)`, so `ν ∈ Submission.E8Enum.the40` (`mem_the40`) and
`ncard ≤ 40`.  The remaining technical gap for this assembly is the **support bound for an
arbitrary weight vector of `T N`** (not just a pure tensor): from `iSup_TLwt_eq_top` write
`x = Σ_{i ∈ s} x_i` with `x_i ∈ TLwt N ν_i` (this needs the finite-decomposition lemma
`Submodule.mem_iSup_iff_exists_finset` plus the killer-product projection, exactly as
`Submission.E8WeightSpaces.eq_zero_of_sum_eq_zero` does for `L = V ⧸ N`), then apply
`Submission.E8Tensor.posCon_two_lam_of_tmul` to a non-zero summand.

### (B) The lower bound `ncard ≥ 40`

For each `ν ∈ the40` one must show `c_ν := [V ⊗ V : L(ν)] ≥ 1`.  The planned route is the
**Klimyk/Brauer formula**

`c_ν = Σ_{w ∈ W} ε(w) · mfun(ν + ρ - w(λ+ρ))`,

a corollary of the Weyl character formula for `V` (`A_ρ · ch V = A_{λ+ρ}`).  Two facts make the
sum finite and *small* (all verified numerically, Python scripts in `Submission/Work/pydata`):

* the summand `mfun(η)` vanishes unless `η ∈ L = {qq ≤ 10}` (the `56881` lattice points of
  `e8_lattice_count`), so only the `10914` pairs `(ν, η)` with `qq(ν + ρ - η) = qq(λ+ρ) = 780`
  survive the norm test;
* writing `γ = w(λ+ρ)`, `δ = λ+ρ-γ ∈ ℕΦ⁺`, the condition `ν+ρ-γ ∈ L` forces
  `htOf δ ≤ 5` — **so only the finitely many `δ = Σ_{α>0} d_α α` with `Σ d_α ≤ 5` need to be
  examined** (a few dozen), and for each the membership `λ+ρ-δ ∈ W(λ+ρ)` is decided by the
  dominant-conjugate algorithm (`dcX`, ≤ 4 reflection steps in every case that occurs!) with
  sign `(-1)^{#steps}`.  Explicitly:

  `c_ν = Σ_{δ : htOf δ ≤ 5} [dcX(λ+ρ-δ) = λ+ρ] · (-1)^{steps} · mfun(ν-λ+δ)`.

  The numerical evaluation reproduces all forty multiplicities of
  `Submission/Work/pydata/SUMMARY.txt` (in particular all are `≥ 1`).

Needed: **the Weyl character formula for `V`** (`A_ρ · mfun = A_{λ+ρ}`, equivalently
`Σ_w ε(w) mfun(ξ - wρ) = δ_{ξ,λ+ρ}` on dominant `ξ`), then the small finite computation above.

### (C) Assembly

`ncard = 40` from (A)+(B); `Submission.E8Enum.the40_length` and `the40_nodup` give the count.

## SESSION 20: **THE UPPER BOUND `ncard ≤ 40` IS PROVED**

**New file `Submission/E8TensorBound.lean` (sorry-free, imported here).**  It completes step (A)
of the plan above and connects to the target statement.

### 1. The weight structure of the tensor square, sharpened

* `exists_decomp_TLwt` — every element of `T N` is a finite sum of weight components (from
  `iSup_TLwt_eq_top` + `Submodule.mem_iSup_iff_exists_finset` +
  `Submodule.mem_iSup_finset_iff_exists_sum`);
* **`posCon_of_mem_TLwt`** — **the support bound for an ARBITRARY non-zero weight vector of the
  tensor square**: `x ∈ TLwt N ν`, `x ≠ 0` ⟹ `2λ - ν ∈ ℕΦ⁺`.  (The proof is a
  `Submodule.span_induction` over the pure tensors defining `TLwt`, using
  `posCon_two_lam_of_tmul`; the only ingredient beyond `E8Tensor` is
  `a ⊗ b ≠ 0 → a ≠ 0 ∧ b ≠ 0`, obtained from `TensorProduct.tmul_zero`/`zero_tmul`.)
* the **killer operators** `killerT ν μ j = (ν j - μ j)⁻¹ (H_j - μ_j)` on `T N` (`killerT_apply`,
  `killerT_kills`, `killerT_fixes`, `killerT_eigen`), the killer product `exists_killerT` (mirroring
  `Submission.E8Finrank.exists_killer`, with the extra property that the product fixes every vector
  on which the Cartan acts by `ν`), and **`mem_TLwt_of_deriv_h_eq`**: a vector `x` with
  `deriv (SerreH j) x = ν_j • x` for all `j` lies in `TLwt N ν`.

### 2. The tensor square is semisimple, and the weight map is injective

* `isSemisimple_tensor` — Weyl's theorem (`Commons.…isSemisimpleModule_enveloping`) applied to
  `T N` (needs `Commons.…e8_isKilling` and `finite_tensor`).
* On the way, several **instance-resolution traps** had to be disarmed (the same phenomenon as in
  §"CRITICAL" of SESSION 19): the tensor square carries *several* competing `Module U (T N)` /
  `SMul U (T N)` / `IsScalarTower ℂ U (T N)` structures, and `T N`'s `LieRingModule` could be the
  derivation or the left-action one.  The fix, at the top of `Submission/E8TensorBound.lean`:
  * declare the derivation structures explicitly as (high-priority) instances
    (`instLieRingT`, `instLieT`, `instModT` defined as
    `{ Module.compHom (T N) (uEnd N).toRingHom with smul := fun u m => uEnd N u m }`, where
    `uEnd N = UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ e₈ (T N))`);
  * declare **high-priority** versions of the scalar actions that must win
    (`instSMulT : SMul U (T N) := (instModT N).toSMul`,
    `instModuleUSub : Module U ↥S := Submodule.module S`), so that `IsScalarTower ℂ U (T N)`
    (`instISTTensor`) and the induced structures on a `U`-submodule (`instModuleSubC` via
    `Submodule.restrictScalars`, `instISTSub`) become synthesizable and
    `IsSimpleModule`/`LieModule.IsIrreducible` agree.  (An earlier version of the file used
    `attribute [-instance] TensorProduct.leftHasSMul …`; the high-priority-instance formulation is
    preferred because it has no effect on other files.)
    The key identity making `IsScalarTower ℂ U (T N)` provable is
    `(uEnd N (c • u)) m = c • ((uEnd N u) m)`, from `map_smul` for the algebra homomorphism
    `uEnd N : U →ₐ[ℂ] Module.End ℂ (T N)`.
  * `instModT` is *definitionally equal* to the framework instance
    `LeanEval.RepresentationTheory.lieModuleToEnvelopingModule ℂ (e₈ ℂ) (T N)` — this is exactly
    the instance that the `∃`-statement of the target theorem uses (verified in a probe), so the
    results below apply to the goal **verbatim**.
* `submoduleLinearEquivOfLieEquiv`: a **Lie isomorphism of `U`-submodules of `T N` is an
  isomorphism over `U(e₈)`** (U-linearity by `Algebra.adjoin_induction` on the `ι`-images).
  `sub_bracket` identifies the Lie action on a `U`-submodule with `deriv`.
* `exists_prim_of_simple`: a simple `U`-submodule of `T N` has a non-zero primitive vector of a
  dominant weight belonging to `the40` (`exists_dominant_primitive_of_ne_bot` +
  `mem_TLwt_of_deriv_h_eq` + `posCon_of_mem_TLwt` + `mem_the40`);
* `CompData`/`compData`: the chosen data `(S, x, ν)` for each isotypic component `c`, with
  `c = isotypicComponent U (T N) S`;
* **`compData_inj`/`compData_inj_aux`**: the map `c ↦ ν_c` is **injective** — two isotypic
  components with the same `ν` give simple submodules with primitives of the same weight, which are
  isomorphic by `Commons.…lieEquiv_of_same_primitive_weight` and then — via
  `submoduleLinearEquivOfLieEquiv` — isomorphic over `U`, so their isotypic components coincide
  (`LinearEquiv.isotypicComponent_eq`).

### 3. The upper bound

**`ncard_tensor_le_forty`**:
```
theorem ncard_tensor_le_forty (N : Submodule U V) (hvN : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) :
    (isotypicComponents U (T N)).ncard ≤ 40
```
by `Set.ncard_le_ncard_of_injOn` with `c ↦ ν_c` into `the40.toFinset`
(`the40_length`/`the40_nodup` give the cardinality `40`).

**Connection to the target** (verified in a probe file): with the witness `V ⧸ N` and the
`inferInstance`s supplied by `exists_max_submodule`,
```
exact Submission.E8TensorBound.ncard_tensor_le_forty N hv hmax
```
proves the third conjunct of `e8_irrep_tensor_square_decomp` (with `≤ 40`), so the upper bound is
done **at the level of the target statement**.

### 4. What remains: the lower bound `ncard ≥ 40` (unchanged plan)

`ncard = |A|` where `A ⊆ the40` is the set of weights realized by an isotypic component; the upper
bound gives `≤`.  For `≥ 40` one must show `c_ν ≥ 1` for all forty `ν`, i.e. the multiplicity
`[T N : L(ν)] = c_ν > 0`.  The planned route is the **Klimyk/Brauer formula**
`c_ν = Σ_{w ∈ W} ε(w)·mfun(ν + ρ - w(λ+ρ))`, a corollary of the Weyl character formula
`A_ρ · ch TN = A_{λ+ρ} · ch V` — but extracting `c_ν` is equivalent to
`[e^{ν+ρ}](A_ρ · ch L(μ)) = δ_{μν}` for the constituents, i.e. the **Weyl character formula for
every constituent**, which is the genuinely missing input.  Two known reformulations worth
recording:
* `A_ρ = e^ρ · D` with `D = ∏_{α>0}(1 - e^{-α})` (Weyl denominator formula) makes `A_ρ` (hence
  `[e^ν](D · ch TN)`) *computable without the Weyl group*; the missing piece is the character
  formula for the constituents, equivalently `D · ch L(μ) = Σ_w ε(w)e^{w(μ+ρ)-ρ}`.
* The identity `A_ρ · mfun² = A_{λ+ρ} · mfun` *is* a W-free, finite statement about the explicit
  `mfun`; together with the invertibility of `mfun` in the ring of formal characters it would give
  the Weyl character formula for `V` — it does not by itself give the multiplicities.

**A failed idea, recorded so it is not repeated.**  A purely linear-algebraic lower bound: the space
of primitive vectors of weight `ν` in `T N` is `P_ν = ker(e : (T N)_ν → ∏_j (T N)_{ν+α_j})`, so
`dim P_ν = c_ν` and rank–nullity gives `c_ν ≥ dim (T N)_ν - Σ_j dim (T N)_{ν+α_j}`.  Both sides are
computable from `mfun` (`dim (T N)_ξ = Σ_{ξ₁+ξ₂=ξ} mfun ξ₁ · mfun ξ₂`), but the bound is *negative*
for 36 of the forty weights (only `2λ`, `ω₃+2ω₈`, `2ω₁+ω₇` and `ω₁+ω₂+ω₈` give `≥ 1`; e.g. `ν = 0`
gives `98530929 - 408744000 < 0`), so the crude estimate overcounts the image massively.

A second, structural route (recorded for a future session): the multiplicities `c_ν` satisfy the
triangular recursion `c_{λ'} = F(λ') - Σ_{μ ≻ λ'} c_μ m_μ(λ')` in the dominant weights, where `F`
is the (known) character of `T N`.  This needs the weight multiplicities `m_μ` of the constituents,
which would follow from the **general Freudenthal theorem** ("the character of a cyclic module
generated by a primitive vector of dominant weight `μ` satisfies the axioms (a)–(d) of
`Submission.E8Character.eq_of_freudenthal`"); the existing `freudenthal_mul` proves this only for
`V ⧸ N`, and generalising it (or building the constituent characters as explicit `M_μ`) is a
self-contained sub-project.

**A note for whoever starts that sub-project:** the general weight spaces
`Wt ν = ⨅ i, eigenspace (H_i) (ν i)` of a module `W` with `[Module U(e₈) W] [IsScalarTower ℂ U(e₈) W]`
(`endU u = (u • ·)`, `module_smul_comm_scalar` for ℂ-linearity, `⁅H_i, E_j⁆ = A_{ij}E_j` for the
weight shifts) are the right starting point (mirroring `endU`/`Lwt` in `E8WeightSpaces`), but the
same instance-resolution traps as above reappear: an unattempted sketch of such a file
(`Submission/E8FreudenthalGen.lean`) was abandoned because the typeclass search for
`IsScalarTower ℂ U(e₈) ?` stayed stuck with metavariables under `variable` declarations; passing all
instances explicitly (or restating the framework with `@`-explicit instances, as in
`E8TensorBound.lean`) is recommended.  Specific pitfall found: inside a `where`-structure literal
for `Module.End ℂ P` with `P` a *variable*, the elaborator cannot synthesize the
`IsScalarTower ℂ U(e₈) P` / `Module U(e₈) P` instances (it leaves a metavariable for the module),
which blocks `Submission.Enveloping.module_smul_comm_scalar` there; the same identity can instead be
proved from `IsScalarTower.smul_assoc` + `Algebra.smul_def`, and `LinearMap`-level goals over such
a variable are best handled with explicit instance arguments.

## SESSION 21: the lower bound `ncard ≥ 40` — the route is FOUND and validated numerically

**Nothing in the *proof* changed this session** (the target still has its single `sorry`), but the
lower bound is now a well-posed, finite, and quantitatively *sized* problem.  Everything below was
checked numerically with the scratch scripts in `.tmp_s20/` (`e8lib2.py` = the library:
`E8inv`, `sref`, `dom` = dominant conjugate, `qq` = squared length, the 7 dominant weights of
`V = L(ω₁+ω₈)` with their multiplicities `1,7,7,34,133,455,1407`, `WtV` = the 56881 weights of `V`).

### 1. ⭐ THE 40 WEIGHTS ARE THE PRV WEIGHTS

`the40 = { π(λ + wλ) : w ∈ W }` (verified: the 30240-element orbit `W·λ` gives exactly 40 distinct
dominant conjugates, and they are precisely `Submission.E8Enum.the40`).  So the lower bound is
"the PRV theorem for `V ⊗ V`, `V = L(ω₁+ω₈)`".
Also: **`WtT` (the weights of `T`) = the `W`-saturation of `the40`** (8355121 weights), and
`ξ ∈ WtT ⟺ π(ξ) ∈ the40` — a *cheap* complete test (one dominant-conjugate call).

### 2. ⭐ THE TRIANGULAR SYSTEM REPRODUCES THE PUBLISHED MULTIPLICITIES EXACTLY

Let `M_ν` (`ν ∈ the40`) be the Freudenthal-normalised function (the recursion
`(Bint ν - Bint μ) m(μ) = 2 ∑_{j:s} (brk (μ+s·α_j) j) m(μ+s·α_j)`, with the sum over
`s ∈ Icc 1 (htOf (ν-μ))`, plus `m(ν) = 1`, `m(μ) = 0` unless `posCon (ν-μ)`).  Computed
*independently in Python* for all `ν ∈ the40` (only the 40 dominant weights ⪯ ν are needed, using
`m(ξ) = m(π(ξ))`), and then the triangular system

  `c_ν := mfun²(ν) - ∑_{μ ∈ the40, μ ≻ ν} c_μ · M_μ(ν)`   (`mfun²(ξ) = ∑_{ξ₁+ξ₂=ξ} mfun ξ₁ mfun ξ₂`)

gives **exactly** the forty multiplicities of `Work/pydata/SUMMARY.txt`
(`1,1,1,1,2,1,1,2,1,2,1,2,1,4,4,3,5,4,7,1,3,3,6,7,6,7,10,10,4,7,2,8,8,9,5,4,5,3,2,1`), all ≥ 1.
**So `ch T = mfun² = ∑_{ν∈the40} c_ν M_ν` with all `c_ν ≥ 1` is the whole lower bound.**

### 2bis. ⭐⭐ THE ONE REMAINING INTERFACE IS OPEN — the constituents' characters are FREE

Recall `ncard_tensor_le_forty` supplies, for every isotypic component `Z` of `T`, a simple
submodule `S ≤ Z`, a vector `0 ≠ z ∈ S`, a dominant weight `ν ∈ the40` with `S` generated by `z`,
`SerreH i z = ν i • z`, `SerreE i z = 0`.  Since `S` is simple, `S = U(e₈)·z`; since `Ω` is central
and `Ω z = casOf ν • z`, the Casimir acts on `S` by the *scalar* `casOf ν`; and
`Commons…weight_support_of_primitive` (this session) gives `posCon (ν - τ)` for every weight `τ` of
`S`.  Hence **`freudenthal_recursion` applies verbatim with `Λ = ν` to `S`**, so
`ch S` satisfies the Freudenthal recursion, and by the *uniqueness* encoded in
`Submission.E8Character.eq_of_freudenthal` (or directly by homogeneity) **`ch S = M_ν`**.
Therefore, with `A ⊆ the40` the set of realised weights (`ncard_tensor_le_forty`) and `c_ν` the
multiplicity of `L(ν)`,
```
        mfun² = ch T = ∑_{ν ∈ A} c_ν * M_ν        (c_ν ≥ 1 on A, c_ν := 0 off A)
```
*with no Casimir-projection, no Weyl character formula, no `W`-sum* — this is now a direct
consequence of the three ingredients 1-3 below.  Comparing coefficients on the dominant weights
gives the **unitriangular system** `mfun²(μ) = ∑_{ν ⪰ μ} c_ν M_ν(μ)`, which determines `(c_ν)`
uniquely (`M_ν(ν) = 1`, `M_ν(μ) = 0` unless `posCon (ν-μ)`), so the lower bound `ncard ≥ 40` is
**exactly** the numerical statement "the triangular system's solution has `c_ν ≥ 1` for all forty
`ν`".  [The SESSION 21 computation of `M.pkl` shows this is true.]

A CAVEAT FOUND THIS SESSION, and why it is harmless: the Casimir eigenvalues `casOf ν` are **not**
pairwise distinct on `the40` — the four collisions (computed: `884: {ω₃+ω₈, 4ω₈}`, `920: {ω₄, 3ω₁+ω₈}`,
`940: {ω₁+ω₂+ω₈, ω₆+2ω₈}`, `956: {ω₃+2ω₈, 2ω₁+ω₇}`) mean a polynomial in `Ω` **cannot** isolate a
single isotypic component (the projection idea of the earlier plan is therefore abandoned).  It is
harmless here because (a) the argument above needs no projection, and (b) all four colliding pairs
are *incomparable* in the dominance order (verified: `posCon (ν-ν')` and `posCon (ν'-ν)` both false),
so the unitriangular system is unaffected by them.

### 3. (superseded by §2bis) The Casimir-projection route

Write `Z_ν` for the `ν`-isotypic component of `T` (so `ch T = ∑_{ν∈the40} ch Z_ν`, all isotypic
components of `T` being of type `L(ν)` with `ν ∈ the40` — this is what `ncard_tensor_le_forty`
gives).  `Z_ν` is *characterised* as the image of the projection `Q_ν(Ω) ▸ T`, where
`Q_ν(x) = ∏_{ν' ∈ the40, ν' ≠ ν} (x - c(ν'))/(c(ν) - c(ν'))`, because **the Casimir eigenvalues
`c(ν) = ⟪ν+ρ,ν+ρ⟫` are pairwise distinct on `the40`** (`ν+ρ` is strictly dominant, and a strictly
dominant weight is determined by its `W`-orbit).  On `Z_ν` the Casimir `Ω` therefore acts as the
**scalar** `c(ν)`, and the *trace argument* of `Submission/E8Freudenthal.lean` — whose only input
beyond the module structure is "`Ω` acts as a scalar" (its cyclicity/Casimir-eigenvalue input is
used only to *get* the scalar) — applies verbatim to `Z_ν` and yields

  `(Bint ν - Bint μ) · m_{Z_ν}(μ) = 2 ∑_{j,k} (brk (μ+k·α_j) j) · m_{Z_ν}(μ+k·α_j)`,

i.e. **the Freudenthal recursion holds for every non-zero isotypic component of `T`**, hence
`m_{Z_ν} = c_ν · M_ν` (the recursion is homogeneous and determines `m` from `m(ν) = c_ν`), hence
`ch T = ∑_{ν ∈ the40} c_ν M_ν`.  **No Weyl character formula, no Kostant formula, no `W`-sum is
needed for this step** — only the generalisation of the existing trace argument from `V ⧸ N` to an
arbitrary finite-dimensional `e₈`-module on which the Casimir is a scalar.

### 4. Six ingredients, with the *measured* size of the only big one

1. the trace recursion for a module with scalar Casimir (item §3) — **the one piece of real work**;
   **DONE — `Submission/E8FreudenthalGen.lean`** (sorry-free, imported here): the *generic* file
   now compiles and already contains the whole `N`-free half of `E8Freudenthal`'s trace argument for
   an arbitrary `M` with `[Module ℂ M] [Module U M] [IsScalarTower ℂ U M] [Module.Finite ℂ M]` and
   `endM Omega = c • 1`: `endM`(the action endomorphism), `Wt`/`mem_Wt_iff`, the weight shift
   `endM_iota_mem_Wt`, the Cartan action `endM_iota_cartan_apply`/`endM_iota_wdual_pR_apply`,
   `restOmegaM`/`traceOmegaM`/`traceOmegaM_eq`, the restricted root operators
   `EopM/FopM/FEmapM/EFmapM` with `FEmapM_eq`/`EFmapM_eq`/`EFmapM_sub_FEmapM`, the traces
   `StrM`/`TtrM` with `StrM_eq_TtrM` and the **step relation** `StrM_step`, the Casimir
   decomposition `HHmapM`/`restOmegaM_eq`/`traceOmegaM_eq_sum`, `TtrM_eq`/`sum_cartanM`/
   `sum_TtrM_eq` and the **master trace identity**
   `two_sum_StrM : 2 * ∑_k StrM k ν = (c - K (wdual ν) (wdual (ν+2ρ))) * dim Wt_ν`,
   followed by the string unfolding `shM`/`StrM_eq_sum`/`StrM_eq_zero_of_htOf_neg`/
   `StrM_last_zero` (the last three parametrised by a bound `Λ` through the hypothesis
   `∀ τ, Wt τ = ⊥ ∨ 0 ≤ htOf (Λ - τ)`).
   and finally, after `StrM_eq_bil`/`sixty_StrM_eq`/`sixty_cas_sub` (all proved),

   **`freudenthal_recursion`** (the file's main theorem, sorry-free):
   ```
   theorem freudenthal_recursion {M} [AddCommGroup M] [Module ℂ M] [Module U M]
       [IsScalarTower ℂ U M] [Module.Finite ℂ M]
       (Λ : Fin 8 → ℤ) (hc : endM Omega = casOf Λ • 1)
       (hsupp : ∀ τ, Wt τ = ⊥ ∨ 0 ≤ htOf (Λ - τ))
       (ν : Fin 8 → ℤ) (hcon : 0 ≤ htOf (Λ - ν)) :
       ((Bint Λ - Bint ν : ℤ) : ℚ) * (finrank ℂ (Wt ν) : ℚ)
         = 2 * ∑ j : Fin 120, ∑ k ∈ Icc 1 (htOf (Λ-ν)).toNat,
             ((brk (ν + k • pR j) j : ℤ) : ℚ) * (finrank ℂ (Wt (ν + k • pR j)) : ℚ)
   ```
   with `casOf Λ := K (wdual Λ) (wdual (Λ + twoRho))` (the Casimir eigenvalue, `cnu_eq_gen`),
   i.e. **the Freudenthal recursion for any finite-dimensional `e₈`-module on which the Casimir is
   a scalar** — the missing general theorem announced in SESSION 20.  The remaining step is the
   *instantiation*: apply it with `Λ = ν` to the isotypic component `Z_ν ⊆ T = (V⧸N)⊗(V⧸N)` (whose
   Casimir eigenvalue is `casOf ν` by construction of the projection `Q_ν(Ω)`, whose weights obey
   `posCon (ν - τ)`, and which is finite-dimensional with `[Module U ↥Z_ν]` from
   `Submodule.module`), then `m_{Z_ν} = c_ν · M_ν` by homogeneity of the recursion.
2. the support bound `posCon (ν - μ)` for weights of `Z_ν` (PBW: `Z_ν` is spanned by the lowering
   operators applied to a primitive vector of weight `ν`) — **DONE, in the commons**:
   `Commons.Algebra.Lie.SerreConstruction.weight_support_of_primitive`
   (`import Submission.Commons.Algebra.Lie.SerreConstruction.weight_support_of_primitive`),
   proved this session by a fleet agent: a `U(e₈)`-module generated by a vector killed by all
   `SerreE i` and of Cartan weight `ν` has all its weights `μ` with `0 ≤ coords (ν-μ) i`;
3. `W`-invariance of the weight multiplicities (`m(ξ) = m(π(ξ))`) so that the recursion can be run
   on the 40 dominant weights only — **DONE for a single simple reflection, in the commons**:
   `Commons.Algebra.Lie.SerreConstruction.weight_mult_reflect`
   (`import Submission.Commons.Algebra.Lie.SerreConstruction.weight_mult_reflect`), also proved this
   session by a fleet agent: for a finite-dimensional `e₈`-module, `finrank` of the `μ`-weight
   space and of the `sref i μ`-weight space agree; composing over the word `L` gives the full
   `W`-invariance `m(ξ) = m(π(ξ))`, whence the *dominant-chamber* recursion
   `(Bint ν - Bint μ)m(μ) = 2∑_{j}∑_{s}(brk (μ+s α_j) j)·m(π(μ+s α_j))`;
4. the definition of the explicit function `M_ν` (a computable function of `(ν, μ)`; needed only on
   the 40 × 40 pairs `μ ⪯ ν`);
5. **the computation of the `M_ν(μ)` table** — sized this session: the raw dominant-chamber
   recursion has 3 526 440 `(ν,μ,α,k)` terms, but the *cheap* filter
   `posCon (2λ - (μ+kα)) ∧ qq(μ+kα) ∈ {qq(δ) : δ ∈ the40}` (pure integer arithmetic, no
   dominant conjugate) leaves **201 094** terms, and the full test
   `π(μ+kα) ∈ the40` leaves **188 709** terms supported on only **5686 distinct vectors `η`**.
   So the kernel should only need ≈ 2·10⁵ dominant-conjugate calls *on 5686 distinct inputs* —
   a precomputed `η ↦ π(η)` table of 5686 entries verified by one `decide` is the recommended
   shape (≈ 10-30 min of kernel time), after which the 1600 recursion identities are *integer
   arithmetic only*;
6. the triangular system (§2) — trivial arithmetic once (5) is done.

### 5. The alternative route (Klimyk / Weyl character formula) and why it is *worse* here

If one has WCF for the constituents, `c_ν = ∑_{w∈W} ε(w)·mfun²(ν+ρ-wρ)`; and
`A_ρ·ch T = ∑_ν k_ν A_{ν+ρ}`, `k_ν := [e^{ν+ρ}](A_ρ ch T)`, follows from the purely numerical
vanishing of `[e^δ](A_ρ ch T)` for regular dominant `δ ∉ {ν+ρ : ν ∈ the40}`.  Obstructions found:
(a) `|W| = 696729600` and the *relevant* `w` (those with `ν+ρ-wρ ∈ WtT`) are not cheaply
enumerable; the "leading-exponent induction" that would convert `A_ρ ch T = ∑ k_ν A_{ν+ρ}` into
`c_ν = k_ν` **fails** because subtracting the top term needs `A_ρ ch L(ν) = A_{ν+ρ}` (WCF) and
without it the off-diagonal coefficients `[e^{ν+ρ}](A_ρ ch L(ν'))` are the unknown constituent
multiplicities; (b) replacing the `W`-sum by the Weyl denominator
`A_ρ = e^ρ ∏_{α>0}(1-e^{-α})` needs the *signed* partition function, whose relevant region is
large.  Also tried and dead: the rank-nullity lower bound (SESSION 20), a pure dimension count
(`∑_{ν∈the40} dim L(ν) = dim T - ∑(c_ν-1)dim L(ν) < dim T`), and the "maximal weight" lemma
(`ν ∈ the40` with `mfun²(ν+α_i) = 0 ∀i`: true only for `ν = 2λ`; note `α_i` *is* a weight of `T`,
so the lemma cannot give `L(0)`).

### 6. Scratch data usable next session

`.tmp_s20/e8lib2.py` (library), `.tmp_s20/e8lib2.py` + `WtV.pkl` (the 56881 weights of `V`),
`.tmp_s20/freud.py` + `M.pkl` (the 1600-entry `M_ν(μ)` table, computed in a few minutes),
`.tmp_s20/tri.py` (the triangular system, reproduces SUMMARY), `.tmp_s20/count3.py` (the term
counts of §4.5), `.tmp_s20/orbsize.py` (`|WtT| = 8355121`, orbit sizes).
WARNING: the box is heavily loaded — always `python3 -u ... > file` and avoid the old
`.tmp_me/e8lib.py` (it eagerly enumerates 8·10⁸ roots).

## SESSION 23: THE CRUX IS PINPOINTED = the Weyl character formula; the numerics are *sized* and
## the M-table route is ruled out by measurement

**Nothing in the *proof* changed this session** (the target keeps its single `sorry`), but the two
candidate routes are now *measured* and the remaining gap is a single classical theorem.  All
numbers below were recomputed this session (`.tmp_s22/termsize.py`, `.tmp_s22/margins.py`,
`.tmp_s22/dform2.py`).

### 0. KERNEL SPEED (measured, `.bench1.lean`)

`by decide` over `(List.range n).foldl (fun a b => a + b*b*b) 0` (with `maxRecDepth` raised):
`n = 1000` ≈ 3.8 s wall, `n = 4000` ≈ 5.2 s wall (incl. ≈ 2 s Lean startup).  So the kernel does
only ≈ **10³ list steps per second**; a "term" of our recursions (a `Fin 8 → ℤ` vector operation
plus a `qq`/dot-product, ≈ 100 elementary steps) costs ≈ **0.05–0.1 s of kernel time**.
**Consequence: the whole certified computation must be ≤ ≈ 10⁴ "term evaluations"**, i.e.
≈ 10⁶ elementary steps ≈ a few minutes.  (Because `declare_proven` replays the proof through the
nanoda kernel *and* `lake build` pays the same reduction again, budget for 2–3× that.)

### 1. ROUTE A (M-table + triangular system) IS RULED OUT — measured

The triangular system `c_ν = mfun²(ν) - Σ_{μ ≻ ν} c_μ M_μ(ν)` is *correct* and, re-verified this
session, reproduces the published multiplicities exactly.  But it needs **two** certified
computations, both infeasible:

* the **M-table** `M_μ(ν)` for the 700 pairs `ν ≻ μ` in `the40`: the dominant-chamber Freudenthal
  recursion has **3 526 440 raw terms** `(ν,μ,j,k)` (`k ≤ htOf(ν-μ)`), of which **225 083**
  survive the *provable* support filter `posCon(ν-μ-kα_j)` (i.e. `π(μ+kα_j) ⪯ ν`), supported on
  **11 552 distinct η = μ+kα_j**.  At ≈ 0.05–0.1 s per term (each needs the conjugate `π(η)` and
  two table lookups) this is **3–6 hours of kernel time** ⟹ infeasible.
* the **40 values `mfun²(ν)` = dim (T N)_ν** (the convolution `Σ_{ξ₁+ξ₂=ν} dmul ξ₁ · dmul ξ₂`),
  with **184 189 pairs** in total; certifying the *completeness* of the pair list needs a
  2.3·10⁶-element scan of the 56 881 lattice points ⟹ **10⁸ kernel steps** ⟹ infeasible.

**Ruled out, do not retry**: a cheap *sufficient* inequality (bounding `c_μ` by something explicit)
— computed this session: `mfun²(ν) - Σ_{μ≻ν} mfun²(μ) M_μ(ν)` is *wildly negative* for all 37
non-top ν (down to `-5.75·10¹⁰` at ν = 0), so no crude bound on the `c_μ` can work; the exact
M-table (or WCF) is genuinely needed.  [Data: `.tmp_s22/margins.py` output.]

### 2. ROUTE B (Weyl character formula) — the crux, in two equivalent forms

We have `ch V = mfun` (SESSION 18) and `ch T = ch V · ch V = mfun²` (multiplicativity of
characters, needs the tensor-product weight-space lemma, *not yet formalised*).  The classical
requirement is the **Weyl character formula**

  (WCF)  `A_ρ · ch L(μ) = A_{μ+ρ}`  for every finite-dimensional **irreducible** `L(μ)` with a
         primitive generator of dominant weight `μ`, where `A_ξ = Σ_{w∈W} ε(w) e^{wξ}`.

Two equivalent reformulations, both statable **without the Weyl group** (only `Φ⁺`, the 120 roots
`pR`, whose height is `1` for each — that fact is what makes the reformulations work):

  (Kostant/Racah–Speiser form)  for dominant `ν, μ`:
     `Σ_{T ⊆ Φ⁺} (-1)^{|T|} · dim (L(μ))_{ν - Σ_{α∈T} α}  =  δ_{νμ}`
     (equivalently: `D · ch L(μ)` has dominant coefficients `δ`, where `D = e^{-ρ}A_ρ = Π_{α>0}(1-e^{-α})`;
      note `e^ρ` here is the shift `ν ↦ ν + ρ`.)

  (off-diagonal vanishing)  for dominant `ν ≺ μ`:  `[e^{ν+ρ}](A_ρ·ch L(μ)) = Σ_{w}ε(w)·dim(L(μ))_{ν+ht(w)} = 0`,
     where `ht(w) := ρ - wρ = Σ_{α ∈ N(w)}α` and `N(w) = {α > 0 : wα < 0}`.

Both are *true* and both need the same input.  **The cheapest route to them is the Weyl
denominator formula** `Σ_w ε(w)e^{-ht(w)} = D = Π_{α∈Φ⁺}(1-e^{-α})`:  once `A_ρ = e^ρ D` is known,
`A_ρ·M_μ = e^ρ D M_μ` and the identity `D·ch L(μ) = Σ_wε(w)e^{w(μ+ρ)-ρ}` (WCF) follows from the
*uniqueness* of the "alternant with support in `μ+ρ-Q⁺`", **provided** one has that uniqueness;
and the α-component of that argument (the diagonal) is *already proved in this session's analysis*:
`[e^{ν+ρ}](A_ρ M_ν) = dim(L(ν))_ν = 1` because all `w ≠ 1` terms have weight `ν+ht(w)` *above* `ν`
with `ht(w) ∈ Q⁺∖{0}` ⟹ outside the support of `M_ν` by `weight_support_of_primitive`.
So **the single genuinely missing theorem is the Weyl denominator formula.**

### 3. ✱ The numerics of Route B: the W-sum reduces *provably* to the ball of radius 4

For `ν ∈ the40` the sum `Φ(ν) := Σ_w ε(w) mfun(ν+ρ-w(λ+ρ))` has *only finitely many* non-zero
terms: a term is non-zero only if `η := ν+ρ-w(λ+ρ)` satisfies `mfun η ≠ 0`, i.e.
`η ∈ L ∪ {0}` = the 56 881 lattice points of norm ≤ 10 (this is `mfun_eq_mnorm` +
`tab_ne_zero`: `mfun η ≠ 0` ⟹ `dcX η ∈ the7`).  SESSION 22 found numerically that all contributing
`w` have `ℓ(w) ≤ 4` (**94 terms per ν, 1162 in total**, `.tmp_s22/klimyk_table.pkl`).
**A proof of a length bound is *not yet* available.**  ⚠️ CORRECTION (found by a fleet agent this
session, with a machine-checked counterexample): `620 - htOf(wρ) = htOf(ρ - wρ)` is the **sum of
the *heights* of the positive roots sent negative** by `w`, i.e. `Σ_{α ∈ N(w)} htOf(α)`, and it is
**not** `ℓ(w) = #N(w)`: they differ already at `L₀ = [3,4,4,7,6,0,7,3,6]`, where
`wact L₀ rhoZ = ![-1,1,2,1,1,2,1,-2]` has `620 - ht = 4` while `wact L₀ = wact [0,6,7]` has `ℓ = 3`
(so the "length" of that element is odd, and no word of length `4` can represent it).  All that is
available is `620 - htOf(wρ) ≥ ℓ(w)` (`Commons…E8_weyl_height_bound` gives `htOf(wρ) ≤ 620`, and
`htOf(α) ≥ 1` for every positive root).  ❗**The true length `ℓ(w) = #N(w)` therefore needs `Φ⁺`
as a finite object — see §5ter.  In particular the earlier plan of bounding `ℓ(w)` by
`htOf(η) - htOf(ν) + htOf(wλ)` does *not* work.**  Two ways out:
  (a) **enumerate** `η ∈ L` with the *cheap* necessary test `qq(ν+ρ-η) = 780 = qq(λ+ρ)`
      (a dot product, ≈ 16 steps): `|L| × 40 = 2.3·10⁶` tests ≈ **10⁷ kernel steps ≈ 1 h** —
      feasible but slow; the surviving 10 914 candidates then need `π(ν+ρ-η) = λ+ρ` and the sign.
  (b) find the *proof* of the length bound (open).
**Either way the numerical part is ≈ 10⁴–10⁶ kernel steps — three orders of magnitude cheaper than
Route A.**  So: **prove WCF, then compute.**

### 4. Crucial small fact proved this session (in the analysis, ready to formalise)

`[e^{ν+ρ}](A_ρ·M_ν) = 1` for every dominant `ν` and every finite-dim `L(ν)` *with support
condition* (only the support bound `weights of L(ν) ⊆ ν - Q⁺` is used, `weight_support_of_primitive`).
This is the whole "diagonal" of the extraction; **the off-diagonal vanishing is exactly WCF.**

### 5. Plan from here (in order)

1. **the tensor-product weight-space lemma** (`ch T = mfun²`): for a finite-dim `e₈`-module `M`,
   `dim (M ⊗ M)_{ν} = Σ_{ξ₁+ξ₂=ν} dim M_{ξ₁} · dim M_{ξ₂}` — tensor products of the `ξ`-weight
   spaces for different `ξ` are *independent* (separate them by the killer operators of
   `E8Finrank.exists_killer` applied to the first, then the second factor).  Delegate-able.
2. **the Weyl denominator formula for `E₈`** — the crux (see §2).  Statable without the Weyl group
   as: for every `γ ∈ Q`, `Σ_{T ⊆ Φ⁺, Σ_Tα = γ} (-1)^{|T|} = Σ_{w : ρ-wρ = γ} ε(w)`; the RHS can
   be replaced by a "signed count over the ball" using §3, once `Φ⁺` is a finite commons object
   (§5ter).  **Note the sign is safe**: `ε(w)` is the parity of *any* word representing `w`
   (`det (sref i) = -1`), so no reducedness theory is needed for the signs — only for the
   *enumeration* of the ball (an element of length `k` is representable by a word of length `k`,
   but the enumeration by "all words of length ≤ K" also meets larger elements, whose
   distinguishing requires `ℓ(w) = #N(w)`).
3. **WCF** from `1 + 2` (via `e^ρ D` and the uniqueness of the alternant), then
   `c_ν = Φ(ν) = Σ_w ε(w) mfun(ν+ρ-w(λ+ρ))` via the derivation in §2 (uses WCF for `V` and for the
   constituents).
4. **the numerical extraction** of §3(a)/(b) — the 40 values `Φ(ν)` must come out `≥ 1`
   (they are `1,1,1,1,2,1,1,2,1,2,1,2,1,4,4,3,5,4,7,1,3,3,6,7,6,7,10,10,4,7,2,8,8,9,5,4,5,3,2,1`).
5. **assembly**: `ncard = 40` from `ncard ≤ 40` + all `c_ν ≥ 1`, then the target theorem.

### 5bis. ADDENDUM (later in the same session): what was actually built

* **NEW COMMONS LEMMA (proved by a fleet child, `import Submission.Commons.Algebra.Lie.SerreConstruction.weight_tensor_finrank`)**:
  `Commons.Algebra.Lie.SerreConstruction.weight_tensor_finrank` —
  for finite-dimensional `e₈`-modules `M`, `N` over `ℂ` and any weight `ν`,
  `dim (M ⊗ N)_ν = Σ_{ξ ∈ s} dim M_ξ · dim N_{ν-ξ}` for any finset `s` of weights containing all
  the weights `ξ` of `M`.  (The child's file also contains `Mwt_iSupIndep` (independence of weight
  spaces), `Mwt_iSup_eq_top`, and the integrality of the `Hᵢ`-eigenvalues.)  **This is `ch T =
  mfun²` at the level of weight multiplicities** — the first step of BOTH routes; the remaining
  work is only to *instantiate* it for `M = N = V ⧸ N` (bridging `Mwt ↔ Lwt` and our explicit
  `deriv`/`endU` actions with the framework's `LieModule.toEnd`, the same instance traps recorded
  in SESSION 19/20) and to use `E8Multiplicity.mfun_eq_mul`.
* **NEW COMMONS LEMMA (requested, still running)**: `Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_reduced_word` —
  every Weyl group element (a word `L`) is represented by a *reduced* word of length
  `(620 - ht(wρ)).toNat`; this gives the *canonical enumeration* of the ball needed for the
  W-sum, without needing the "sign of a word is well defined" theory.
* **NEW COMMONS LEMMAS (proved by fleet children — all committed):**
  * `Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset` — `∃ s : Finset (Fin 8 → ℤ)`,
    `v ∈ s ↔ v ≠ 0 ∧ qZ v = 2 ∧ ∀ i, 0 ≤ coords v i`, and `s.card = 120`: **the 120 positive
    roots of `E₈` as a finite object** (the prerequisite for *stating* the denominator formula).
  * `Commons.LinearAlgebra.Matrix.Cartan.E8_wact_sign` — if two words give the same endomorphism
    of the weight lattice then `(-1)^{L₁.length} = (-1)^{L₂.length}`: **the sign `ε(w)` is the
    parity of ANY word representing `w`** (via `det (wact L) = (-1)^{L.length}`).
  * (requested, still running) `Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_denom` — **the crux
    itself** (the coefficient form of the Weyl denominator formula), stated in §5ter.
* **A `declared FALSE` report that saved a wrong turn** (fleet agent L139): my first version of
  `E8_weyl_reduced_word` claimed `ℓ(w) = 620 - ht(wρ)`; the agent produced a machine-checked
  counterexample (`L₀ = [3,4,4,7,6,0,7,3,6]`: `ht`-defect `4`, but `wact L₀ = wact [0,6,7]` has
  `ℓ = 3`).  The correct identity is `620 - ht(wρ) = Σ_{α ∈ N(w)} ht(α) ≥ ℓ(w)` (see §3).
* **NEW FILE `Submission/WeylBall.lean`** (sorry-free, imported here): the combinatorial side of
  any sum over `W(E₈)`: `rhoZ` (`htOf rhoZ = 620`), `wact` (word action, with `wact_append`),
  `wlen x = 620 - htOf x`, `wsign k = (-1)^k`, `wordsUpTo K` (all words of length ≤ K),
  `ballList K`/`ballSet K` (the elements of length ≤ K as the vectors `wρ` — injective since `ρ` is
  regular) and `ballSum K f = Σ_{ℓ(w) ≤ K} ε(w) f(wρ)`; and, built on the commons lemma
  `E8_posRoots_finset`, the **true length** `wlenOf L = #N(w) = #{α ∈ Φ⁺ : wα < 0}`
  (noncomputable, via `Classical.choose`; make it computable before using it in numerics) and the
  sign `wsignOf L = (-1)^{ℓ(w)}`.  **`ballSum 4` is the object to evaluate** once the vanishing of
  the terms with `ℓ(w) ≥ 5` is known.  *(To do: `wsignOf L = (-1)^L.length`, from `E8_wact_sign`.)*

### 5ter. The delegation chain for the Weyl denominator formula (for the next sessions)

The denominator formula is *statable* with only `Φ⁺` and the words, but it needs `Φ⁺` as a *finite
object* in the commons first.  Recommended chain of fleet requests (each statable from Mathlib + the
commons):
1. `exists_positiveRoots` : `∃ s : Finset (Fin 8 → ℤ), (∀ v, v ∈ s ↔ v ≠ 0 ∧ qZ v = 2 ∧ ∀ i, 0 ≤ coords v i) ∧ s.card = 120`
   — the 120 positive roots as a finite set.  (The proof is a finite enumeration; the coordinates of
   a norm-2 vector are bounded by `2`, so a `decide` over the box `{-2,…,2}⁸` (390 625 vectors)
   works but costs ≈ `4·10⁷` kernel steps ≈ 1–3 h: *budget it deliberately*.)
2. `weyl_denom_coeff` : for every word `L` and every finset `s` with the property of (1),
   `∑ T ∈ s.powerset, (if ∑ α ∈ T, α = rhoZ - wact L rhoZ then (-1 : ℤ) ^ T.card else 0) = (-1 : ℤ) ^ L.length`
   — the coefficient form of `Σ_w ε(w)e^{-ht(w)} = ∏_{α>0}(1-e^{-α})`.  This is the *crux*.
3. `E8_wact_sign` (requested): the sign is well defined on elements — if two words give the same
   endomorphism of the weight lattice then they have the same length parity (`det (wact L) =
   (-1)^{L.length}`).  This is what makes `ε(w)` computable from *any* word representing `w`
   (no reducedness needed for the signs).
4. `kostant_racah_speiser` (WCF in the root-only form): for a finite-dimensional simple
   `e₈`-module with a primitive generator of dominant weight `μ` and dominant `ν`:
   `∑ T ∈ s.powerset, (-1)^{|T|} · dim (weight space of L(μ) at ν - ∑_{α∈T}α) = if ν = μ then 1 else 0`.
   (Equivalently `D · ch L(μ) = Σ_w ε(w) e^{w(μ+ρ)-ρ}`.)  Then `A_ρ ch L(μ) = A_{μ+ρ}`.

### 6. Scratch data created this session

`.tmp_s22/termsize.py` (the 700 pairs / 3.5M raw / 225 083 surviving / 11 552 distinct η),
`.tmp_s22/margins.py` (the `mfun²` values and the crude-bound failure), `.tmp_s22/dform2.py`
(the D-form: `Σ_{γ}σ(γ)mfun(ν-λ-γ)` — **WRONG**, since `A_{λ+ρ} ≠ e^{λ+ρ}D`; recorded so it is not
retried), `.bench1.lean` (kernel speed), plus SESSION 22's `.tmp_s22/klimyk_table.pkl`.
## SESSION 24: ⭐ THE FULL WEYL DENOMINATOR FORMULA IS PROVABLE (clean induction found);
## kernel-budget measured; the W-sum sized exactly; the remaining crux isolated

**Nothing in the proof changed this session** (the target keeps its single `sorry`), but the SESSION
23 "crux" is now *proved on paper* and the whole route is re-sized.  Read this section; it supersedes
SESSION 23 §2/§5.

### 1. ⭐⭐ THE FULL WEYL DENOMINATOR FORMULA — a clean proof, found this session

Let `P` be the 120 positive roots (the commons lemma `E8_posRoots_finset`), and

  `C(γ) := Σ_{T ⊆ P, Σ_{α∈T}α = γ} (-1)^{|T|}`   (supported on `Q⁺`, `C(0) = 1`).

`E8_weyl_denom` (commons, PROVED) gives only the *values* `C(ρ - wρ) = ε(w)`.  The missing half —
vanishing off `{ρ-wρ}` — is what makes the denominator formula usable.  **Theorem:**
`C(γ) = ε(w)` if `γ = ρ-wρ` (unique `w`, since `ρ` is regular), and `C(γ) = 0` otherwise.

**PROOF** (strong induction on `htOf γ`; everything is elementary):
1. If `γ ∉ Q⁺` then no `T` has `Σ_Tα = γ`, so `C(γ) = 0`.  (So assume `posCon γ`.)
2. **Reflection identity.** `C(α_i + s_iδ) = -C(δ)` for all `δ, i` (this is the *only* nontrivial
   combinatorial input; it is proved inside the commons file `E8_weyl_denom` as the private lemma
   `C_sref`, via the fixed-point-free sign-reversing involution `T ↦ s_i(T∖{α_i})` of `P.powerset`).
   Substituting `δ = s_iμ` gives `C(s_iμ) = -C(μ+α_i)`, i.e. **`C(γ) = -C(s_iγ + α_i)`** for all γ.
3. Write `γ_i := ⟨γ, α_i∨⟩` (the ω-coordinate of γ, i.e. `γ i` as a coordinate).  Then
   `htOf(s_iγ + α_i) = htOf(γ) - γ_i + 1` (because `htOf(s_iv) = htOf(v) - ⟨v,α_i∨⟩` and
   `htOf(α_i) = 1`; ω-coordinates of `α_i` are the entries of the Cartan matrix and `A_ii = 2`).
4. **Case `γ_i = 1`** for some `i`: then `s_iγ + α_i = γ`, so step 2 gives `C(γ) = -C(γ)`, hence
   `C(γ) = 0`.  (Consistent: `(ρ-wρ)_i = 1 - (wρ)_i` and `(wρ)_i ≠ 0` for every `w`, since
   `Stab_W(ρ) = {1}`, so `ρ-wρ` never has an ω-coordinate equal to `1`.)
5. **Case `γ_i ≥ 2`** for some `i`: then `htOf(s_iγ+α_i) < htOf γ` and step 2 gives
   `C(γ) = -C(γ')` with `γ' := s_iγ+α_i`.  If `γ' ∉ Q⁺` then `C(γ') = 0` hence `C(γ) = 0`.
   If `γ' ∈ Q⁺`, the induction hypothesis applies to `γ'`: either `C(γ') = 0` (so `C(γ) = 0`, and
   then `γ` is also not of the form `ρ-wρ`, because `γ = ρ-wρ` would force
   `γ' = ρ - (s_iw)ρ ∈ Q⁺` with `C(γ') = ε(s_iw) ≠ 0` — contradiction), or `γ' = ρ - w'ρ` with
   `C(γ') = ε(w')`, and then `γ = s_iγ' + α_i = ρ - (s_i w')ρ` and `C(γ) = -ε(w') = ε(s_iw')`.
6. **Case `γ_i ≤ 0` for all i**: then `⟨γ, α_i⟩ ≤ 0` for all simple roots, so
   `⟨γ, γ⟩ = Σ_j coords_j(γ)·⟨γ, α_j⟩ ≤ 0` (as `posCon γ`, i.e. `coords_j(γ) ≥ 0`), whence
   `γ = 0`; and `0 = ρ - 1·ρ` with `C(0) = 1 = ε(1)`. ∎
   (Every nonzero `γ ∈ Q⁺` has *some* ω-coordinate `γ_i ≥ 1`, so cases 4–6 exhaust everything.)

**Consequences** (all now unconditionally provable):
* `Σ_γ C(γ) e^{γ} = Σ_{w} ε(w) e^{-(ρ-wρ)}`, i.e. `Π_{α>0}(1-e^{-α}) = Σ_w ε(w)e^{-(ρ-wρ)}`;
* `A_ρ := Σ_w ε(w) e^{wρ}` satisfies **`A_ρ = e^{ρ}·Π_{α>0}(1-e^{-α})`**, i.e. (as functions on the
  weight lattice) `A_ρ(τ) = C(ρ-τ)` for all `τ`.  *(Only this second form is needed downstream.)*
* ⚠️ **`A_ξ = e^ξ D` is FALSE for general ξ** (verified numerically: it fails at `ξ = 2ρ` because
  `C(2α_i) = 0` while `A_{2ρ}(2s_iρ) = -1`).  So the earlier `dform2.py` heuristic stays dead; only
  `ξ = ρ` is available, which is exactly what WCF below uses.

### 2. Kernel budget — MEASURED this session (replaces the earlier estimates)

* `by decide` over an **explicit integer polynomial** (the quadratic form
  `qq8 a b c d e f g h` with the 64 literal coefficients `E8inv i j` written out, no matrix lookup)
  costs ≈ **2.5 ms per evaluation** (20000 evaluations ≈ 51 s of kernel time; baseline import ≈ 17 s).
  The same `qZ` written through the matrix `E8inv` costs ≈ 12 ms (list lookups dominate).
* Nanoda is **forced on** by `WorkspaceTest.lean` regardless of `config.json`, so the comparator pays
  the kernel cost ≈2–3×.  **Budget for the whole numerics: ≈ 10⁴–10⁵ "quadratic-form evaluations"
  (a few minutes).** Design every certified computation to use ≤ 10⁴ such evaluations.
* `Fin 8 → ℤ` vector *comparisons/equalities* are much cheaper than `qq` but still ~0.1 ms.

### 3. The W-sum: exactly 1162 nonzero terms; the height bound

Numerically (`.tmp_s24/w1.py`; word enumeration up to length 6, no lattice scan needed):

* `Σ_w ε(w) mfun(ν + ρ - w(λ+ρ))` has **exactly 1162 nonzero terms** over the 40 `ν` — confirmed
  (this is the SESSION 22 count, now independently reproduced).
* `ℓ(w) ≤ B_ν := ⟨ν, λ⟩ - qq(ν)/2` for every contributing `w`, where `⟨ν,λ⟩ = ν ⧝ coords(λ)` and
  `coords(λ) = [6,8,11,16,13,10,7,4]`; PROOF: `qq(ν+ρ-w(λ+ρ)) ≤ 10` gives
  `⟨β, ν+ρ⟩ ≤ ⟨ν,λ⟩ - qq(ν)/2` for `β := λ+ρ-w(λ+ρ) ∈ Q⁺`, and
  `ℓ(w) ≤ htOf(ρ-wρ) = htOf(β) - htOf(λ-wλ) ≤ htOf(β) ≤ ⟨β,ν+ρ⟩`.
  `max_ν B_ν = 5` (attained at `ν = λ`); for `ν = 0` and `ν = 2λ` one gets `B_ν = 0` (only `w=1`).
* ⚠️ `B_ν` alone does **not** give a small enumeration: `wordsUpTo 5` has 37449 words and the
  *deduplication* (`ballPairs`, currently `O(n²)`) is far beyond budget.  The deduplication is the
  only obstacle to using `ballPairs K` directly; a cheap canonical form / a certified literal list of
  the ball is the open practical question.

### 4. WCF — the route, and the single remaining step

Needed: `A_ρ·ch L(ν) = A_{ν+ρ}` for finite-dim simple `L(ν)` with a primitive generator, and in
particular for `V = L(λ)`.  Equivalently `D·ch L(ν) = e^{-ρ}A_{ν+ρ} =: Ψ_ν`.
**Route via `eq_of_freudenthal`** (`Submission.E8Character.eq_of_freudenthal`): with the denominator
formula in hand, define `m' := D^{-1}·Ψ_λ` (well defined: `D` has constant term `1` and lives in the
ring of series supported on `Q⁺`, so `D^{-1}` is supported on `Q⁺`).  Then:
* **(b) support** `m'(v) ≠ 0 ⇒ λ - v ∈ Q⁺`: immediate from `supp(D^{-1}) ⊆ Q⁺`, `supp(Ψ_λ) ⊆ λ-Q⁺`.
* **(c) W-invariance**: from `w·D = ε(w)e^{ρ-w^{-1}ρ}D` and `w·Ψ_λ = ε(w)e^{ρ-w^{-1}ρ}Ψ_λ`
  (both checked) it follows that `w·(D^{-1}Ψ_λ) = D^{-1}Ψ_λ` — *pure equivariance, no content*.
* **(a)** `m'(λ) = 1`: `Ψ_λ(λ-δ) ≠ 0 ⇒ λ-δ = w(λ+ρ)-ρ ⇒ -δ = (wλ-λ) + (wρ-ρ) ∈ Q⁺`, and this is
  nonzero for `w ≠ 1` (since `wρ ≠ ρ`), so `D^{-1}(δ) = 0`; hence `m'(λ) = D^{-1}(0)Ψ_λ(λ) = 1`.
* **(d) the Freudenthal recursion** at the dominant weights `ν ≺ λ` — **THE ONE REMAINING STEP**.
  (Note `λ = ω₁+ω₈` has `qq(λ) = 10`, so there are only **six** dominant `ν` with `posCon(λ-ν)`:
  `the7 ∖ {λ}`.)  Classical statement: the WCF-candidate satisfies Freudenthal's recursion (the
  "Freudenthal's formula from the Weyl character formula" direction).  Nothing in the commons does
  this; the classical proofs are (i) the algebraic/manipulation proof with the Kostant partition
  function, or (ii) the anti-invariant structure theorem `ℤ[P]^{-W} = A_ρ·ℤ[P]^W` plus positivity.

### 5. What is *not* needed (simplifications found this session)

* The **full** denominator formula is needed only to produce `D` (or `A_ρ(τ) = C(ρ-τ)`); the
  derivations `c_ν = [e^{ν+ρ}](A_ρ·chT)` and `A_ρ chT = A_{λ+ρ}·chV` use only the *definition*
  `A_ρ = Σ_w ε(w)δ_{wρ}` plus WCF.  So WCF (not the denominator formula) is the mathematical crux.
* `[e^{ν+ρ}](A_ρ·ch L(ν')) = δ_{νν'}` (needed to *extract* `c_ν`) is triangular:
  `[e^{ν+ρ}](A_ρ ch L(ν')) = 0` unless `ν ⪯ ν'` (support of `ch L(ν')`), and `= 1` on the diagonal
  (the easy half, using only `weight_support_of_primitive`).

### 6. Scratch files this session

`.tmp_s24/lib.py` (Cartan matrix, `sref`, `dc`, `the40` parsed from `E8Enum`, Cholesky),
`.tmp_s24/w1.py` (the 1162-term word enumeration + `B_ν`), `.tmp_s24/n4.py` (lattice enumeration,
**buggy**: the DFS constraint is wrong), `ProbeS24*.lean` (kernel timing; deleted).


## SESSION 24 (cont.): ⭐⭐ WCF FOR `V = L(ω₁+ω₈)` IS PROVABLE — reduced to 6 finite identities

This is the sharpest progress of the session and it *supersedes* the pessimistic §4 above.

**Setting.** `A_ρ := Σ_w ε(w) e^{wρ}` (functions on the weight lattice), `mfun = ch V` (proved in
SESSION 18: `mfun ξ = mnorm (qq ξ)`, `mfun ξ ≠ 0 ↔ qq ξ ≤ 10`).  WCF for `V` is
`A_ρ·mfun = A_{λ+ρ}`; since both sides are *anti-invariant* (`X(wμ) = ε(w)X(μ)`) it suffices to
check the identity at the **dominant** weights `μ`.

**The key computation (no machine input).** Let `μ` be dominant and suppose `w` contributes to
`(A_ρ mfun)(μ) = Σ_w ε(w) mfun(μ - wρ)`.  Then `qq(μ-wρ) ≤ 10`, while
`qq(μ-wρ) = qq(μ) + qq(ρ) - 2⟨μ,wρ⟩ = qq μ + 620 - 2⟨μ,wρ⟩` and `⟨μ,wρ⟩ ≤ ⟨μ,ρ⟩ = htOf(μ)`
(μ dominant, `wρ ⪯ ρ`).  So `10 ≥ qqμ + 620 - 2 htOf(μ)`, i.e. `htOf(μ) ≥ (qq μ + 610)/2`.
Writing `ν := μ - ρ` (`htOf(μ) = htOf(ν)+620`, `qq μ = qq ν + 2htOf(ν) + 620`) this becomes
`5 ≥ qq(ν)/2`, i.e. **`qq(ν) ≤ 10`**.

**Consequence.** If `qq(μ-ρ) > 10` then `(A_ρ mfun)(μ) = 0`, *with no computation*.  Hence the only
dominant `μ` at which `A_ρ mfun` can differ from `A_{λ+ρ}` are `μ = ρ + ν` with
`ν ∈ {dominant, qq ν ≤ 10} = the7`, i.e. **seven** weights.  For `ν = λ`: only `w = 1` survives
(`qq(λ+ρ-wρ) > 10` for `w ≠ 1`, because `ρ-wρ ∈ Q⁺∖{0}` and λ is dominant), so
`(A_ρmfun)(ρ+λ) = mfun(λ) = 1 = A_{λ+ρ}(ρ+λ)`.  For the other six `ν ∈ the7 ∖ {λ}` the identity
`(A_ρmfun)(ρ+ν) = 0` is a *finite* sum, verified numerically this session (`Σ_w ε(w)mfun(μ+ρ-wρ)`
= 1 at μ = λ and = 0 at the other six, by word enumeration up to length 6, `.tmp_s24/w2.py`).

**Length bound for these six sums — and why the ball of radius 4 suffices.** For such a term,
`htOf(ρ-wρ) = 620 - htOf(wρ) ≤ 5 - qq(ν)/2 ≤ 5`.  If `ℓ(w) = 5` then `N(w)` has 5 elements; if
all of them were simple they would be 5 pairwise non-adjacent nodes of the E8 diagram, which is
impossible (the independence number of the E8 Dynkin diagram is 4 — and if `α_i, α_j ∈ N(w)` are
adjacent then `α_i+α_j ∈ N(w)` is not simple).  So some `α ∈ N(w)` is non-simple, giving
`htOf(ρ-wρ) ≥ 4·1 + 2 = 6 > 5`, a contradiction.  Hence **`ℓ(w) ≤ 4`** for every contributing
term.  ∎

**So WCF for `V` needs only:** (i) the anti-invariance (formal), (ii) the estimate above, (iii) the
six finite sums over the **450 elements of the ball of radius 4** — certified as in §3/§7 below.
The same `ℓ ≤ 4` bound governs the main computation (§3).

### 7. What is still open: WCF for the *constituents* (Racah–Speiser)

To *extract* `c_ν = [T : L(ν)]` one needs `[e^{ν+ρ}](A_ρ ch L(ν')) = δ_{νν'}` for the constituents
`ν' ∈ the40`, i.e. the Racah–Speiser identity `Σ_w ε(w) M_{ν'}(ν+ρ-wρ) = δ_{νν'}`.  The `τ`-candidate
argument above generalises *partially*: for dominant `τ = ρ+η` and the module `L(ν')`, a term
requires `qq(η) ≤ qq(ν')`, and the length bound becomes
`ℓ(w) ≤ (qq(ν')-qq(η))/2` (and `≤ htOf(ν')-htOf(η)`), which is **only usable when the norm gap is
≤ 8** — for large gaps (e.g. `η = 0`, `ν' = 2λ`) it gives nothing.  So the constituents need a
genuine proof.  Classical options: the anti-invariant structure theorem
`ℤ[P]^{-W} = A_ρ·ℤ[P]^W` (with `A_ρ = e^ρD` and the divisibility by each `(1-e^{-α})`), or the
Kostant multiplicity formula (equivalently the BGG resolution / the Freudenthal recursion for the
candidate `D^{-1}Ψ_μ`).

**Fallback if the Racah–Speiser route stalls:** the triangular route needs the M-table
(`225 083` surviving Freudenthal terms) **and** `dim T_ν = Σ_{ξ₁+ξ₂=ν} mfun ξ₁ mfun ξ₂` for the 40
dominant `ν` (184189 pairs, whose *complete enumeration* needs a scan of the 56881 lattice points).
NOTE: `declare_proven` itself has **no time limit**, so a ~1 h kernel computation is *possible*;
but `lake build` and the shared machine make it costly.  Prefer the proof.

### 8. The ball-of-radius-4 certificate (design; needed by BOTH §3 and §6)

`ball4` = the 450 elements `wρ` of `W` with `ℓ(w) ≤ 4` (numerically: `ℓ`-distribution
`1, 8, 35, 112, 294`).  Certificate:
1. `ball : List (Fin 8 → ℤ)` — 450 literal vectors, **sorted** lexicographically (w.r.t.
   `Pi.instLinearOrder`); `List.Sorted (·<·) ball` by `decide` (449 comparisons, cheap) gives
   `ball.Nodup`, so each element is counted once;
2. `wic : List (List (Fin 8))` — for each `i`, a literal word of length ≤ 4 with
   `wact (wic i) rhoZ = ball i` (checked pointwise by list recursion, 450 × ~4 reflections);
   this gives `ball ⊆` image(`wordsUpTo 4`);
3. `nxt : Fin 450 → Fin 8 → Fin 450` — a literal transition table with
   `ball (nxt i j) = sref j (ball i)` (3600 checks, each one `sref` + one list lookup + a vector
   comparison); together with `rhoZ ∈ ball` this gives closure of `ball` under `sref`, hence
   (by induction over `wordsUpTo`) `ball ⊇` image(`wordsUpTo 4`), i.e. **completeness**.
   Because `image(wordsUpTo 4)` = the elements of length ≤ 4 and `ball` is nodup, `ball` *is* the
   ball, each element once.
Then any relevant sum is `Σ_{i : Fin 450} (-1)^{(wic i).length} · F (wact (wic i) (λ+ρ))` — 450
`qq`-evaluations per ν (~1 s each at 2.5 ms), i.e. 40·450 ≈ 18000 evaluations ≈ 45 s for the main
computation and 7·450 for §6.  ⚠️ The naive `Submission.WeylBall.ballPairs 4` **must not** be used:
`by decide` on `(ballPairs 4).length = 450` was killed by the 12 GB memory cap (the kernel's nested
`List.any` closures explode), so the deduplication has to be done *offline* and certified by
sortedness + closure as above.


## SESSION 24 (cont.2): the Klimyk sum is numerically CONFIRMED; the constituent blocker isolated

* **⭐ `f_ν = c_ν` for all forty `ν`** (`.tmp_s24/f1.py`): with
  `f_ν := Σ_w ε(w) mfun(ν + ρ - w(λ+ρ))` summed over the **450 elements of the ball of radius 4**
  (deduplicated by `w(λ+ρ)`), one gets exactly the published multiplicities
  `1,1,1,1,2,1,1,2,1,2,1,2,1,4,4,3,5,4,7,1,3,3,6,7,6,7,10,10,4,7,2,8,8,9,5,4,5,3,2,1`
  (sum `155`).  Together with the `ℓ ≤ 4` bound of §6 this pins the *whole* main computation as a
  sum of 40 × 450 `qq`-evaluations ≈ 45 s of kernel time — **once** the extraction `c_ν = f_ν` is
  available.
* **The extraction is exactly WCF for the constituents** (Racah–Speiser).  The triangular form is
  `f_ν = Σ_{ν'⪰ν} c_{ν'} B_{ν'ν}` with `B_{ν'ν} := Σ_w ε(w) M_{ν'}(ν+ρ-wρ)`; `B_{νν} = 1`
  (easy), and `c_ν = f_ν` for all `ν` is *equivalent* to `B_{ν'ν} = 0` for `ν ≺ ν'`.
  Numerically (`.tmp_s24/b1.py`, using the SESSION 20 `M.pkl` table and a BFS over `[0,10]`-balls)
  `B_{ν'ν}` = 0 for the tested pairs, and **the truncated sum over `ℓ(w) ≤ 4` already equals `δ`**
  for them — but the *provable* length bound for the constituents is only
  `ℓ(w) ≤ min(htOf(ν')-htOf(ν), (qq(ν')-qq(ν))/2)`, which is *not* ≤ 4 for large norm gaps
  (and indeed for e.g. `(ν,ν') = (0,2λ)` the weight `2λ = ρ-wρ` *is* a weight of `L(2λ)`, so terms
  with large `ℓ` do exist and must cancel).  So the constituents genuinely need a **proof** of
  Racah–Speiser / WCF, not a computation.
* ⚠️ Consequence for the fallback: a proof of `B_{ν'ν} ≤ 0` for `ν ≺ ν'` would not suffice on its
  own (it must be established, and `B = 0` is the truth); but `B ≤ 0` *together with* `f ≥ 1` would
  give `c ≥ f ≥ 1` directly, so a cheap *proof* of the sign (if it exists) is worth looking for.
* The commons now contains (all PROVED, this session):
  `E8_weyl_denom_refl` (the reflection identity, public), `E8_weyl_denom_support` (the *support*
  half of the Weyl denominator formula — combined with the pre-existing `E8_weyl_denom` this is the
  full denominator formula `Π_{α>0}(1-e^{-α}) = Σ_w ε(w)e^{-(ρ-wρ)}`, equivalently
  `A_ρ(τ) = C(ρ-τ)`), and (in flight) `E8_weyl_ball4`.


## SESSION 24 (cont.3): `ch T = mfun²` PROVED (new file `Submission/E8TensorChar.lean`)

**NEW FILE `Submission/E8TensorChar.lean`** (sorry-free, imported by `Submission.lean`), namespace
`Submission.E8TensorChar`.  It instantiates the commons theorem
`Commons.Algebra.Lie.SerreConstruction.weight_tensor_finrank` for `M = N = V ⧸ N`:

* `toEnd_quot`, `Mwt_quot`: the framework's weight space `Mwt (M := V ⧸ N) μ` coincides with our
  `Lwt N μ` (the `U(e₈)`-action transported by `Submission.Enveloping.instLieModuleE8` is the
  `endU`-action);
* `toEnd_tensor`, `Mwt_tensor`: `Mwt (M := T N) ν = TLwt N ν` (the tensor Lie action is the
  `deriv` derivation action; the two inclusions use `deriv_h_tmul` and `mem_TLwt_of_deriv_h_eq`);
* **`finrank_TLwt_eq_sum`**: `dim (T N)_ν = ∑_{ξ ∈ E8Iso.L.toFinset} dmul N ξ * dmul N (ν-ξ)`,
  where `E8Iso.L` is the commons list of all lattice points of squared length `≤ 10` (it contains
  every weight of `V ⧸ N` via `mfun_ne_zero_iff` + `mfun_eq_mul`);
* **`finrank_TLwt_eq`**: the same in terms of the candidate character,
  `(dim (T N)_ν : ℤ) = ∑_{ξ ∈ E8Iso.L.toFinset} mfun ξ * mfun (ν-ξ)`.

This is the `ch T = ch V · ch V` input of every route; it is now unconditional.


### Addendum: a provable vanishing criterion for the constituent sums

For a dominant evaluation point `τ` and a finite-dimensional simple `L(μ')` with a primitive
generator, a term of `(A_ρ M_{μ'})(τ) = Σ_u ε(u) M_{μ'}(τ-uρ)` is non-zero only if `τ-uρ` is a
weight of `L(μ')`, so `qq(τ-uρ) ≤ qq(μ')` (`ξ ⪯ μ'` dominant ⟹ `qq ξ ≤ qq μ'`), while
`qq(τ-uρ) = qq τ + qq(ρ) - 2⟨τ,uρ⟩ = qq(τ-ρ) + 2⟨τ-ρ, ρ-uρ⟩ + qq(uρ) - qq(ρ)`, and
`⟨τ,uρ⟩ ≤ ⟨τ,ρ⟩ = htOf τ` for `τ` dominant (since `uρ ⪯ ρ`).  Hence

  `qq(τ-uρ) ≥ 1240 - qq(τ-ρ)`  **and more sharply** `qq(τ-uρ) ≥ qq(τ-ρ)`,

the second because `qq(uρ) = qq(ρ) = 620` and `⟨τ-ρ,ρ⟩ = htOf(τ-ρ)`.  Therefore

  **(V)** `(A_ρ M_{μ'})(τ) = 0` for dominant `τ` with `qq(τ-ρ) > qq(μ')`.

For the triangular system this gives, for `ν, ν' ∈ the40`, `B_{ν'ν} = 0` **whenever
`qq(ν) > qq(ν')`** — a provable chunk of the Racah–Speiser vanishing.  The remaining pairs have
`qq(ν) ≤ qq(ν')`, where the length bound `ℓ(u) ≤ (qq(ν')-qq(ν))/2` of §7 applies: pairs with norm
gap `≤ 8` are decided by the ball-of-radius-4 computation, larger gaps need the general proof.

*(For `μ' = λ` the criterion (V) says the only dominant `τ` with a possibly non-zero value are those
with `qq(τ-ρ) ≤ 10`, i.e. `τ = ρ+ν` with `ν ∈ the7` — exactly the content of §6.)*


## SESSION 24 (cont.4): the ball of radius 4 is available, and WCF for `V` is *computed*

**New commons lemma (proved by a fleet child this session):**
`Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_ball4` — the elements of `W(E₈)` of length `≤ 4`, as a
certified `∃ ballp : List ((Fin 8 → ℤ) × List (Fin 8))` with `length = 450`, each carrying a word of
length `≤ 4`, nodup values, and the characterisation
`v ∈ ballp.map Prod.fst ↔ ∃ L, L.length ≤ 4 ∧ wact L rhoZ = v`.

**NEW FILE `Submission/E8Ball.lean`** (sorry-free).  The commons certificate is an *existential*, so
it cannot be *computed* with; this file is a verbatim copy of that file with the namespace renamed
(`Submission.E8Ball`), the `private`s dropped and the final theorem renamed `E8_weyl_ball4_data`.
It exposes the literal `e8ball : List ((Fin 8 → ℤ) × List (Fin 8))` (**450 entries**), the
transition table `e8nxt` and the certification lemmas `e8ball_prop`, `e8ball_nodup`, so that the
ball is available both as a *computation* and as a *proof object*.

**NEW FILE `Submission/E8CharCompute.lean`** (sorry-free).  `ballSum f = Σ_{p ∈ e8ball} (-1)^{|p.2|} f p.1`
and `ballSumL f` (the same with `f` at `w(λ+ρ)`), plus `mfun_eq : mfun v = mnorm (qZ v)` and
`ballSum_congr_mfun`.  It *proves by `decide`*:

  `ballSum (fun x => mnorm (qZ (μ + ρ - x))) = if μ = λ then 1 else 0`

for all **seven** dominant weights `μ ⪯ λ` (i.e. `the7`), using only the ball of radius 4 (legitimate
because a contributing `w` has `htOf(ρ-wρ) ≤ 5 - qq(μ-ρ)/2 ≤ 5`, hence `ℓ(w) ≤ 4`).  This is the
**numerical input of WCF for `V`** of §6, now machine-checked.

⚠️ COST: the seven `decide`s cost ≈ 3 min of kernel time (≈ 30 s per sum of 450 terms; the kernel
unfolds `qZ`'s `E8inv` matrix literal).  Optimisation is *not yet* done: a cheap explicit integer
polynomial  is *not yet* wired up (the obvious `qq8 … = qZ` "ring_nf" lemma does not close by
`ring`/`ring_nf`; the literal 64-term polynomial itself evaluates at ≈ 2.5 ms vs ≈ 12 ms for `qZ`,
a 4–5× speedup waiting to be had).  Because of that the **forty** Klimyk evaluations `f_ν` are *not*
yet in the build: they would cost ≈ 20 min of kernel time each build.  Do that only once the
extraction is ready, or after the speedup.

### Remaining, precisely

1. `mfun`-sum ↔ ball-sum: a finite version of `A_ρ` (the alternant) whose sum over `W` is *provably*
   supported on `ℓ(w) ≤ 4` (§6), so that WCF for `V` becomes a theorem rather than a computation.
2. The **extraction** `c_ν = f_ν` (WCF for the constituents / Racah–Speiser) — still the one real
   mathematical gap (§7 and the addendum, which give the provable partial result
   `B_{ν'ν} = 0` whenever `qq(ν) > qq(ν')`).
3. The forty Klimyk evaluations (§ this section) once (1)/(2) are in place.

## SESSION 26: the Weyl-character-formula route is pinned down; the Weyl group is now a finite object

**Nothing in the proof changed** (the target keeps its single `sorry`), but the *analysis* of the
remaining gap is now complete, and the first pieces of the WCF infrastructure are in the commons and
in `Submission/WCFSetup.lean`.

### 0. Two decisive *negative* findings (so they are not retried)

* **The D-form of the Klimyk sum is NOT computable.**  The value `f_ν = [e^{ν+ρ}](A_ρ·ch T)` has the
  D-form `Σ_{γ ∈ Weyl heights} C(γ)·dim T_{ν+γ}`, which needs **no** WCF for `V`, but its surviving
  terms are NOT confined to the ball of radius 4: measured by BFS over the orbit of `ρ`, the number
  of surviving `(ν, w)` pairs is `44, 156, 450, 1122, 2508, 5148, …` for radii `2..7` at the
  maximal `ν` (it keeps growing).  The *mfun*-form
  `Σ_w ε(w)·mfun(ν+ρ-w(λ+ρ))` *is* confined to the ball (exactly `1162` surviving terms, `94` per
  `ν`, stable from radius 4 on), **but its legitimacy relies on WCF for `V`** (`A_ρ·mfun = A_{λ+ρ}`).
  ⟹ **WCF is unavoidable, even for the numerics.**
* **The `ℓ(w) ≤ 4` bound used by the notes' §6 argument is NOT proved by the `qq` estimate alone.**
  From `mfun(ν+ρ-w(λ+ρ)) ≠ 0` one gets `qq(ν+ρ-w(λ+ρ)) ≤ 10`, and `qq(μ+δ) = qq μ + qq δ + 2⟪μ,δ⟫`
  only gives `qq δ ≤ 10`; Cauchy–Schwarz (`ht(δ)² ≤ qq δ · 620`) then yields `ht(ρ-wρ) ≤ 78`,
  not `≤ 5`.  The true reason `ℓ(w) ≤ 4` must be **arithmetic** (a case check on the Weyl heights),
  not a soft inequality.  *Delegated*: `Commons…E8_wact_small_height_length`
  (`615 ≤ e8ht(wρ) ⟹ ∃` a word of length `≤ 4` with the same action).

### 1. The Weyl group is now a FINITE SET OF MATRICES (commons)

`Commons.LinearAlgebra.Matrix.Cartan.E8_wactMat_finite` — `Set.range wactMat` is finite — was proved
this session by a fleet agent (the entries of `wactMat L` are bounded because the columns are
vectors of squared length `≤ 4`).  Together with the pre-existing
`E8_wact_sign` and the new `E8_wact_sign_rho` (the parity of a word is a function of `wρ`), this
makes the Weyl sum `Σ_{w ∈ W} ε(w) f(x - wρ)` a **statable, computable object**.

New commons lemmas of this session (all PROVED):
* `E8_wact_sign_rho` — the sign `ε` is well defined on the orbit of `ρ`;
* `E8_wactMat_finite` — the Weyl group is finite;
* `E8_wact_fixes_strict_dominant` — a strictly dominant weight has trivial stabiliser;
* `E8_dom_sub_wact_mem_cone` — `x - w x ∈ ℕΦ⁺` for `x` dominant (the "height decrease");
* `E8_weyl_C_wact` — the *public* sign-equivariance of the Weyl denominator coefficients,
  `C(wact L γ + (ρ - wact L ρ)) = (-1)^{|L|}·C γ`;
* (in flight) `E8_wact_small_height_length` — the `ℓ ≤ 4` bound above.

### 2. `Submission/WCFSetup.lean` (sorry-free, NOT yet imported by `Submission.lean`)

* `WG : Finset (Matrix (Fin 8) (Fin 8) ℤ)` — the Weyl group as a finite set of matrices;
* `WG_one`, `WG_mul`, `WG_inv`, `wactMat_append`, `wactMat_mul_reverse`, `wactMat_reverse_mul`;
* `wactMat_mulVec` — the matrix acts as `wact L`;
* `ap` — the action on weights, with `ap_add`, `ap_mul`, `ap_one`;
* `WSum f x = Σ_{w ∈ WG} det(w)·f(x - ap w ρ)` — the Weyl sum (with `rhoV = ρ`);
* **`WSum_reindex`** — `WSum f (w x) = det(w)·WSum f x` for `W`-invariant `f` (the reindexing of the
  finite sum by the group structure);
* **`WSum_anti`** — `WSum f (wact L x) = ε(L)·WSum f x`: *the Weyl sum of a `W`-invariant function is
  anti-invariant*.

### 2bis. The support estimate for the ball, SOLVED (analysis)

The vanishing hypothesis needed to replace the Weyl sum by the certified ball sum is
`∀ M ∈ W, M ∉ ball ⟹ mfun(μ+ρ-Mρ) = 0` (for dominant `μ ⪯ λ`).  The key is the **identity**

  `qq (ρ - wρ) = 2 · e8ht (ρ - wρ)`  for every `w`,

which holds because `qq (ρ - wρ) = qq ρ + qq (wρ) - 2⟪ρ, wρ⟫ = 1240 - 2 e8ht(wρ)` (using the
`W`-invariance `qq (wρ) = qq ρ = 620` and the symmetry `⟪ρ, wρ⟫ = e8ht (wρ)`) while
`e8ht (ρ - wρ) = 620 - e8ht (wρ)`.  Hence, writing `δ = ρ - wρ` and using `qq (μ + δ) ≥ qq δ`
(`μ` dominant, `δ ∈ ℚ⁺`, so `⟪μ,δ⟫ ≥ 0`):

  `mfun (μ + ρ - wρ) ≠ 0 ⟹ qq (μ + δ) ≤ 10 ⟹ 2 e8ht(δ) ≤ 10 ⟹ e8ht(wρ) ≥ 615`

and then `E8_wact_small_height_length` gives a word of length `≤ 4` for `w`.  Contrapositively:
**every Weyl group element with no word of length `≤ 4` contributes `0`** — exactly the
element-based vanishing hypothesis of `WSum_eq_ballSum'` below.  (Numerically verified: the minimal
`qq δ` over the Weyl heights of height `h` is exactly `2h`, for all `h`.)

### 2ter. `Submission/WCFSetup.lean` continued: the ball comparison (all sorry-free)

* `Ball.ballMat`, `Ball.ballMat_mem`, `Ball.ballMat_injOn` (two ball entries with the same matrix
  are equal), `Ball.ballSet` (the 450 matrices of the ball), `Ball.ballSet_sub`;
* **`WSum_eq_sum_ballSet`** (word-based hypothesis) and **`WSum_eq_sum_ballSet'`** (element-based
  hypothesis, the one used for `mfun`);
* **`sum_ballSet_eq_ballSum`**: the sum over the ball matrices is `∑_{p ∈ e8ball} (-1)^{|p.2|} f (x - p.1)`,
  i.e. exactly the `ballSum` of `Submission.E8CharCompute`;
* **`WSum_eq_ballSum` / `WSum_eq_ballSum'`**: the Weyl sum equals the certified ball sum.

So **WCF for `V` is now reduced to** (i) the support estimate above (pure lattice arithmetic), and
(ii) the seven `decide` computations already present in `Submission/E8CharCompute.lean`.

### 3. The plan from here (the only remaining mathematical content)

* **(A) WCF for `V`** (`A_ρ·mfun = A_{λ+ρ}`), whose dominant-values form is
  `WSum mfun (μ+ρ) = δ_{μλ}` for the seven dominant `μ ⪯ λ`:
  - `WSum_anti` reduces it to the dominant weights;
  - the "only the seven" reduction: `mfun ≠ 0 ⟹ qq ≤ 10` shows only `μ = ρ+ν`, `ν ∈ the7`, can
    contribute;
  - the seven values are `E8CharCompute`'s `decide` results, transported to `WSum` by identifying
    the ball sum with the Weyl sum (needs the `ℓ ≤ 4` bound and the certified ball `e8ball`).
* **(B) The extraction (Racah–Speiser)**: `mult_ν(T) = WSum (ch T)(ν+ρ)` for the forty dominant `ν`.
  This is the **one real gap**, and the only route found is the classical one:
  *Verma modules + the BGG candidate* `K_ν = Σ_w ε(w)·ch M(w·ν)`: `K_ν` satisfies the Freudenthal
  recursion (sum of the Verma recursions, each of which follows from the *general*
  `freudenthal_recursion` once the Verma weight spaces are known to be finite-dimensional), has
  support in `ν - ℚ⁺`, the right value at `ν`, and is `dc`-invariant; hence `K_ν = ch S` for a
  simple `S` with a primitive generator of weight `ν`, by `eq_of_freudenthal` (which is already
  stated for an *arbitrary* dominant `Λ`), and then `A_ρ·ch S = Σ_w ε(w)e^{w(ν+ρ)} = A_{ν+ρ}`.
  The missing formalisation is the **Verma module for an arbitrary weight** (the existing
  `⋆`-model `Submission.VermaWeight` is specialised to `ω₁+ω₈`) together with its finite-dimensional
  weight spaces.
* **(C) The forty Klimyk evaluations** `f_ν = WSum mfun²`-type sums over the certified ball
  (`E8CharCompute` already does the seven for `V`; the forty cost ≈ 17 min of kernel time).

-/


/-!

## SESSION 27: ⭐⭐ THE EXTRACTION IS *VALIDATED* — the c-table route, and it is kernel-affordable

**The single remaining gap (the extraction / "WCF for the constituents") is now solved *in
principle*, with a fully explicit and computationally cheap normal form.  Nothing in the proof of
the target changed this session (the `sorry` is still there), but the hard step is now a finite
computation whose whole content is arithmetic on explicit literals.**

### 1. THE IDEA: the c-table turns the Freudenthal recursion into 40-term sums

For a dominant weight `mu` and a weight `nu`, the recursion (in the *dominant-chamber* form used by
`freudenthal_recursion_of_cyclic` together with `W`-invariance of the multiplicity function) reads

  `(Bint ν - Bint μ) F(μ) = 2 · ∑_{j<120} ∑_{k≥1} brk(μ+k·pR_j, j) · F(π(μ+k·pR_j))`.

**The `k`-range is bounded by 4**: if `π(η) ⪯ ν ∈ the40` then `qq η = qq (π η) ≤ qq ν ≤ 40`, while
`qq(μ+kα) = qq μ + 2k⟪μ,α⟫ + 2k² ≥ qq μ + 2k²` (μ dominant, α a positive root); hence `k ≥ 5`
gives `qq η ≥ 50 > 40` and the term vanishes.  (Verified numerically: no `(ν,μ,α,k)` with `k ≥ 5`
has `π(μ+kα) ∈ the40`.)

Therefore, *for every* `ν ∈ the40` simultaneously,

  `(Bint ν - Bint μ) M_ν(μ) = 2 · ∑_d c(d,μ) · M_ν(d)`      (★)

where the **c-table** is the `ν`-independent data

  `c(d,μ) := ∑_{j<120, 1≤k≤4, π(μ+k·pR_j)=d} brk(μ+k·pR_j, j)`    (`d ∈ the40`).

There are only `40·480 = 19200` root-shifts `(μ,j,k)` in total, of which **7187** have
`π(μ+kα) ∈ the40` (measured: `.tmp_s27/measure_pruned.py`); the c-table is a `40×40` integer
matrix.  So the recursion becomes a **40-term linear identity** for each of the `40·39/2+40 = 740`
pairs `(ν,μ)` — no `W`-sum, no partition function, no `dc` computation in the arithmetic.

### 2. THE WHOLE COMPUTATION IS VALIDATED (Python, `.tmp_s27/gen_data.py` → `final.pkl`)

* the c-table `c[i][d]` (40×40, literals), computed with the DOMINANT CONJUGATES ONLY;
* the M-table `M[ν][μ]` (the Freudenthal-normalised multiplicities of `L(ν)`), obtained by solving
  the *unitriangular* system (★) in the topological order of `the40` — it reproduces the
  independently computed `M.pkl` of SESSION 21 **exactly** (0 mismatches on all 1600 pairs);
* `mf2[ν] = [e^{ν}](ch T) = ∑_{a+b=ν} mfun a · mfun b` for the 40 dominant `ν`;
* the solution `cc` of the unitriangular system `mf2(ν) = ∑_{μ ⪰ ν} cc(μ)·M_μ(ν)` is

  `[1,1,1,1,2,1,1,2,1,2,1,2,1,4,4,3,5,4,7,1,3,3,6,7,6,7,10,10,4,7,2,8,8,9,5,4,5,3,2,1]`

  **all ≥ 1, sum 155 — exactly the forty multiplicities of `Submission/Work/pydata/SUMMARY.txt`**
  (and `∑ cc(μ)·dim L(μ) = (dim V)²`).  ⟹ the lower bound `ncard ≥ 40` follows from the
  triangular system + (★) + nothing else.

Data and generator: `.tmp_s27/{gen_data.py,final.pkl,README.md}` (order, c-table, M-table, the
19200 reflection-word certificates `cert[i][(j,k)] = (d-index, word)`, `mf2`, `cc`).

### 3. WHAT MUST BE FORMALISED (the plan; all pieces are cheap now)

Let `ord40 : List (Fin 8 → ℤ)` be the 40 weights in the *topological* order of the data
(decreasing `htOf`), so that `M` is upper triangular with `M_ν(ν) = 1`.

1. (`Submission/E8Extract.lean`, generated) the literal data: `ord40`, the c-table `ctab : Fin 40 →
   Fin 40 → ℤ`, the M-table `Mtab : Fin 40 → Fin 40 → ℤ`, `mf2 : Fin 40 → ℤ`, `cc : Fin 40 → ℤ`,
   and the certificate table `didx : Fin 40 → Fin 120 → Fin 4 → Fin 40` (index of the verified
   dominant conjugate of `ord40 i + (k+1)·pR j`, or `0`/`none` for "not in `the40`"), each entry
   *certified by an explicit word of simple reflections* (the words are in `final.pkl`).
   The certificates are checked by ONE `decide` over the table (19200 entries, each an
   application of a short word: `applyWord w η = ord40.get ⟨didx, _⟩`).
2. The candidate characters `Mν : Fin 40 → (Fin 8 → ℤ) → ℚ`, `Mν i η := Mtab i (domIdx η)`,
   where `domIdx η` is the index of `dc η` in `the40` (0 off `the40`).  Prove the four hypotheses
   of `eq_of_freudenthal`:
   * `Mν i (ord40 i) = 1`;
   * support: `Mν i η ≠ 0 → ord40 i - η = 0 ∨ posCon (ord40 i - η)`
     (uses `dc_sub_posCon` and `Mtab i d ≠ 0 → d ⪯ ord40 i`, provable by `decide` on the table);
   * `dc`-invariance: `Mν i (dc η) = Mν i η` (`dc ∘ dc = dc`);
   * **the recursion `(d)`** — use the certificate table: for each `(i,j,k≤4)`,
     `Mν i (ord40 i' + (k+1)·pR j) = Mtab i (didx i j k)` by the general lemma
     "if `w·η = d` and `d` is dominant then `dc η = d`" (two dominant `W`-conjugate weights are
     equal), and the `k ≥ 5` vanishing; then (★) is the verified 40-term identity (2).
3. `eq_of_freudenthal` with an *arbitrary* dominant top weight (currently it is stated only for
   `lam`, but the proof is general) ⟹ **`Mν i` is the character of the simple constituent of
   highest weight `ord40 i`** (instantiate with the `CompData` primitive vector of any isotypic
   component of type `ν`, using `freudenthal_recursion_of_cyclic`).
4. The character of `T = (V⧸N)⊗(V⧸N)` is `mfun²` (`Submission.E8TensorChar`), so evaluating the
   isotypic decomposition `ch T = ∑_{c} ch(c.val)` at the 40 dominant weights gives
   `mf2(ν) = ∑_{μ} cc^true(μ)·M_μ(ν)`, the same unitriangular system as in (2), whence
   `cc^true = cc` — **each of the 40 weights is realised, `ncard ≥ 40`**; with
   `ncard_tensor_le_forty` this gives `ncard = 40`.
5. Assembly: `Submission.E8Tensor`'s `V ⧸ N` with `N` the maximal submodule, `dim = 779247`
   (`E8Finrank`), irreducibility (`E8Tensor`/`E8NullVector`), then the target theorem.

**Kernel budget — MEASURED this session.**  `Submission/E8Extract.lean` (generated by
`.tmp_s27/gen_lean.py`) already contains the literal tables `ord40`, `Mtab` (740 nonzero entries),
`ctab` (308 nonzero), `mf2v`, `ccv` and proves, by two `decide`s,
* `ccv_pos : ∀ i, 1 ≤ ccv i` and `ccv_sum : ∑ ccv = 155`,
* `ccv_system` — the 40 unitriangular equations `mf2v i = ∑_d ccv d · Mtab d i`,
* **`freud_star`** — all 740 identities `(Bint (ord40 i) - Bint (ord40 d)) · Mtab i d
  = 2 ∑_e ctab d e · Mtab i e` (with the table lookups in a balanced decision tree, so each is
  cheap).
It **builds in 190 s** (`lake build Submission.E8Extract`, 3 minutes of elaboration + kernel, no
`sorry`).  The earlier "the M-table route is infeasible (1 h+ of kernel)" measurement was about the
*unpruned* enumeration (3.5 M terms); the `k ≤ 4` bound plus the c-table make it a 3-minute
computation.  **This was the last "hard" obstacle: the extraction is no longer speculation.**

### 5. WHAT EXACTLY REMAINS (in order; all of it ordinary work)

1. **Part B — the c-table certificates** (`.tmp_s27/final.pkl` has them: for each `(μ,j,k≤4)`,
   `cert[t][(j,k)] = (d, word)` with `wact word (ord40 d) = μ + k·pR_j`; `d = -1` when the dominant
   conjugate is outside `the40`).  Add to `E8Extract.lean`: the two tables `didx`, `dwrd` (as
   balanced decision trees) and the single `decide`-check
   `cert_ok : ∀ t j k, didx t j k < 40 → wact (dwrd t j k) (ord40get ⟨didx t j k, _⟩) = ord40get t + (k+1) • pR j`
   (when `didx ≥ 40` the check is vacuous; the *value* used is then `0`).  Then prove
   `ctab_eq : ∀ t d, ctab t d = ∑_{j,k} brk(ord40get t + (k+1)•pR_j, j) · [didx t j k = d]`
   (grouping the 19200 terms by their certified `d`; a `decide` on the tables).
2. **The reduction recursion ⟹ (★)** (`Submission/E8Extract.lean`): from
   `freudenthal_recursion_of_cyclic`, `weight_mult_wact` (W-invariance of the multiplicities) and
   * the `k ≥ 5` vanishing: `qq(μ+kα) ≥ qq μ + 2k² ≥ 50 > 40 ≥ qq ν` (commons
   `E8_qZ_add_nsmul_posRoot_ge` + `E8_qZ_le_of_cone`), so `M_ν(π(μ+kα)) = 0` for `k ≥ 5`;
   * the certified dominant conjugates (step 1) and `E8_dominant_conj_unique` (two dominant
     W-conjugate weights are equal) so that `M_ν(η) = Mtab ν (didx …)` for every term,
   derive `(★)` `(Bint ν - Bint μ)·M_ν(μ) = 2 ∑_d ctab d μ · M_ν(d)` — i.e. exactly
   `freud_star` with `Mtab`/`ctab` in place of the lookups.
3. **The candidate characters**: `Mν i η := Mtab i (didx-of-`dc η`)` (0 if `dc η ∉ the40`), with
   (a) `Mν i (ord40 i) = 1`, (b) support (`dc_sub_posCon` + a `decide` that `Mtab i d ≠ 0 → d ⪯ i`),
   (c) `dc`-invariance (`dc ∘ dc = dc`), (d) the recursion = `freud_star` + step 2.
   `eq_of_freudenthal` (E8Character, **already general in the top weight**) then gives: `Mν i` is the
   character of the simple constituent of highest weight `ord40 i` (instantiate with the primitive
   vector from `E8TensorBound.exists_prim_of_simple`).
4. **The system and the conclusion**: `ch T = mfun²` (`E8TensorChar.finrank_TLwt_eq_sum`), the
   isotypic decomposition evaluated at the forty dominant weights, step 3 ⟹ the actual multiplicities
   satisfy the same unitriangular system as `ccv` ⟹ they *are* `ccv` ⟹ all `≥ 1` ⟹ every one of the
   forty weights is realised ⟹ `ncard ≥ 40` (`E8TensorBound`, using `exists_prim_of_simple` for each
   realised weight) ⟹ with `ncard_tensor_le_forty`: `ncard = 40` ⟹ the target.
5. **Assembly**: `V := V ⧸ N` (`N` the maximal submodule), `dim = 779247` (`E8Finrank`),
   `IsIrreducible` (`E8Tensor`/`E8NullVector`), then
   `exact ⟨V ⧸ N, inferInstance, …, hdim, hirr, hncard⟩`.
   *Warning*: keep the `∃`-statement first in `Submission.lean` so that typeclass search picks the
   derivation action on `V ⊗ V` (see the SESSION 19 warning).

### 4. ALSO DONE THIS SESSION
* `Commons…E8_qZ_rho_sub_wact` (in flight last session) landed: `qZ (ρ - wρ) = 2·e8ht (ρ - wρ)`.
* the support estimate of SESSION 26 for `WCF for V` was re-derived: `mfun(μ+ρ-wρ) ≠ 0 ⟹ qq(ρ-wρ)
  = 2 e8ht(ρ-wρ) ≤ 10 ⟹ e8ht(wρ) ≥ 615` ⟹ `ℓ(w) ≤ 4` (`E8_wact_small_height_length`), which
  together with the seven `decide`s of `Submission/E8CharCompute` gives `WCF for V`.  (Not needed
  for the route above, which uses no Weyl sum at all — it is kept as an independent cross-check of
  `mf2` and of the `d_ν`.)


/-!

## SESSION 28: ⭐⭐ THE c-TABLE CERTIFICATE IS PROVED, AND `Mnu` SATISFIES 3 OF THE 4 HYPOTHESES

**The single most delicate computational piece of the extraction — the dominant conjugates of all
`19200` c-table terms — is now proved in Lean, sorry-free, and assembled into usable lemmas.**
Everything below is on disk; `lake build Submission.E8CertAll`, `Submission.E8Star`,
`Submission.E8Regroup`, `Submission.DcFast` are green, and `lake build Submission` is unchanged
(green, the target still has its single `sorry`).

### 1. ⭐ THE KERNEL BOTTLENECK OF `dcX` — found and fixed (`Submission/DcFast.lean`)

`dcX`/`dcXE` represent a weight as a *function* `Fin 8 → ℤ`; each reflection builds a fresh closure
`fun j => v j - v i * …`.  After `k` reflections the evaluation of one coordinate walks a chain of
`k` closures, so the cost is **quadratic** in `ℓ(w)` — measured `≈ 30 ms` per reflection for the
weights of the c-table (which need up to `28` reflections).

`Submission/DcFast.lean` carries the weight as an explicit `8`-tuple `W8` with the sparse
reflections `srefW` (each node of the `E₈` diagram has `≤ 3` neighbours, so one reflection updates
`2..4` of the eight fields).  It proves

* `fun'_srefW : fun' (srefW i w) = srefE i (fun' w)`, `srefW_mk'`, `dclW_mk'`, and
* **`dcWE_eq : dcWE v = dcX v = dc v`** (`Submission.DcFast.dcWE_eq_dcXE`, `dcWE_eq`).

This is a **linear-time** dominant conjugate: measured `0.14 s` per conjugation for the c-table
weights (vs `0.57 s`), and it is what makes the certificate affordable.

### 2. THE MEMORY WALL — measured, and worked around by chunking

* `import Mathlib` alone costs **6.8 GB** RSS; the box kills any process above **12 GB**.
* A `decide` accumulates roughly **MB per instance**, so a single `decide` over all `19200` terms
  is killed (as is one over the `40` separate statements in one file).
* Consequence: the certificate lives in **40 separate modules** `Submission/Cert/D0..D39.lean`
  (one per `d : Fin 40`, each `≈ 3..6 min`, peak `≈ 10 GB`), assembled in
  `Submission/E8CertAll.lean` (**28 s**, `6.9 GB`).
* `Submission/E8Regroup.lean` (`sum_regroup`, `sum_Icc_one_four`) is the purely combinatorial
  regrouping step; it is independent of the certificate and builds in seconds.

### 3. WHAT IS IN THE COMMONS-LIKE WORKSPACE NOW (all sorry-free)

* **`Submission/DcFast.lean`** — `W8`, `fun'`, `mk'`, `srefW`, `pickNegW`, `dclW`, `dcWE` and the
  bridges to `srefE`/`dclE`/`dcXE`/`dcX`.
* **`Submission/E8Cert.lean`** — the c-table data and the *definitions* of the extraction:
  * `sidA / sidTab d j k` — the index in `ord40` of the dominant conjugate of the term
    `eta = ord40 d + (k+1) * pR j`, or `40` when `qZ eta > 40`;
  * `brkA / brkTab d j k` — `brk eta j`;
  * `eqv`, `ord40v` (+`ord40v_eq`), `clOrd`, `findD` (+`findD_sound`), `classify`
    (+`classify_sound`), `term`, **`domIdx`** (+**`domIdx_sound`**:
    `domIdx v = some e → ord40get e = dcX v`), **`Mnu i v = (domIdx v).elim 0 (Mtab i)`**;
  * the *grouping* of the terms is now **definitional**: `stList d e` is
    `pairList.filter (fun p => sidTab d p.1 p.2 == e.1)`, so `st_sid`, `st_nodup`, `st_mem` are
    proved by `List.mem_filter`/`List.Nodup.filter` — **no computation at all**;
  * `ctabN d e = (stList d e).toFinset.sum (fun p => brkTab d p.1 p.2)` (the grouped c-table).
* **`Submission/Cert/D<d>.lean`** (40 files) — `cert_sid_d`, `brk_eq_d`, `ctab_eq_d`.
* **`Submission/E8CertAll.lean`** — **`cert_sid`**, **`brk_eq`**, **`ctab_eq`** assembled.
* **`Submission/E8Regroup.lean`** — `sum_Icc_one_four` (`∑_{k∈Icc 1 4} f k = ∑_{k:Fin 4} f (k+1)`)
  and **`sum_regroup`** (the ungroupped sum over the terms equals `∑_e ctab d e * X e`).
* **`Submission/E8Star.lean`** — `posF`/`posF_true` (`posCon` through the fast `mvn`),
  `domIdx_dom`, `Mnu_dom`, **`Mnu_top`**, **`Mnu_dc`**, `Mtab_support`, **`Mnu_support`** — the
  hypotheses (a), (c) and the support bound (b) of `eq_of_freudenthal` for `Mnu i`.

### 4. WHAT REMAINS, IN ORDER

1. **(d) the Freudenthal recursion for `Mnu i`** — ✅ **DONE** (`Submission/E8Rec.lean`,
   sorry-free).  The four hypotheses of `eq_of_freudenthal` for the candidate characters are now
   all proved: `Mnu_top` (a), `Mnu_support` (b) and `Mnu_dc` (c) in `Submission/E8Star.lean`, and
   **`Mnu_freud`** (d) in `Submission/E8Rec.lean`.  The supporting lemmas are
   `sum_Icc_eq_four` (the `k`-range reduction), `Mnu_eq_zero_of_five_le` (the `k ≥ 5` vanishing,
   from the commons `E8_qZ_add_nsmul_posRoot_dominant` and `pR_memP`),
   `Mnu_eq_zero_of_height` (the height vanishing), `Mnu_sum_eq` (the term rewriting via
   `cert_sid`/`brk_eq`/`term_eq_smul`), `Mnu_sum_core` (the regrouping, `Finset`-manipulation
   only) and `E8Extract.freud_star` (the tabulated recursion).  ⭐ **The extraction — the single
   "real gap" of SESSION 23–27 — is therefore closed at the level of the candidate functions.**
   The historical route, for the record:  For
   `ν = ord40get d ⪯ ord40get i`:
   * `Mnu i ν = Mtab i d` (`Mnu_dom`);
   * extend `∑_{k ∈ Icc 1 N}` (`N = (htOf (lam - ν)).toNat`) to `Icc 1 4` — terms with `k ≥ 5`
     have `qZ ≥ qZ ν + 2k² ≥ 50 > 40` so `domIdx = none` (commons
     `E8_qZ_add_nsmul_posRoot_dominant`), and terms with `N < k ≤ 4` have
     `htOf (ν + k•pR j) > htOf (ord40get i)`, impossible for a non-zero value
     (`domIdx_sound` + `domIdx`'s definition + `Mtab_support`);
   * `sum_Icc_one_four` turns this into `∑_{j : Fin 120} ∑_{k : Fin 4} brkTab d j k * V` where
     `V = if sidTab d j k < 40 then Mtab i ⟨sidTab d j k⟩ else 0` — via **`cert_sid`** and
     **`brk_eq`**;
   * **`sum_regroup`** + **`ctab_eq`** turn this into `∑_e ctab d e * Mtab i e`;
   * **`E8Extract.freud_star`** finishes: `(Bint ν - Bint μ) Mtab i d = 2 ∑_e ctab d e Mtab i e`.
2. **`eq_of_freudenthal` for the *actual* constituents** of `T = (V⧸N) ⊗ (V⧸N)`.  For a simple
   submodule `S ≤ T` with a primitive generator of dominant weight `ord40 i` (`exists_prim_of_simple`
   in `Submission.E8TensorBound`), the character `v ↦ finrank ℂ (S ∩ TLwt v)` satisfies
   (a) (`Mnu_top`-style), (b) (support — `posCon_of_mem_TLwt`), (d)
   (`freudenthal_recursion_of_cyclic`) and (c) **W-invariance of the weight multiplicities**.
   ⚠ The latter is available for `V ⧸ N` (`Submission.E8WInvariance.finrank_Lwt_sref`) but **not
   yet for `TLwt` of the tensor square** — the `𝔰𝔩₂`-string argument has to be repeated for `T N`
   (or one argues that `S ∩ TLwt` is the `Str`-module of `Submission.E8WInvariance` transported
   along the Lie isomorphism `submoduleLinearEquivOfLieEquiv`).  **This is the next real gap.**
3. **The isotypic system**: `T` is semisimple (`isSemisimple_tensor`), so
   `dim T_ν = ∑_c m_c · dim (S_c)_ν`; with step 2 this is `mf2v i = ∑_d cc^true_d * Mtab d i`,
   the same unitriangular system as `ccv_system`, so `cc^true = ccv` — and `ccv_pos` gives
   `ncard ≥ 40`.  With `ncard_tensor_le_forty`, `ncard = 40`.
4. **Assembly**: `V := V ⧸ N`, `dim = 779247` (`E8Finrank.finrank_eq`), `IsIrreducible`
   (`E8Tensor`/`E8NullVector`), `ncard = 40`, then the target theorem.

**Kernel budget for the future**: `lake build` of the 40 chunks takes `≈ 2 h` in total (they are
already built and cached); do **not** put a `decide` over more than `≈ 1000` instances of a
`Fin 8 → ℤ` computation into a single file.

-/


/-!

## SESSION 29: the `W`-invariance of the tensor square — the string machinery, and one instance obstacle

**Nothing in the proof of the target changed** (the `sorry` is still the only one; `lake build
Submission` is green).  The work this session is `Submission/E8WInvarianceT.lean`, the mirror of
`Submission/E8WInvariance.lean` for the tensor square `T N = (V ⧸ N) ⊗ (V ⧸ N)` — the step that
unblocks applying `eq_of_freudenthal` to the *actual* constituents rather than just to the
candidate characters `Mnu i`.

### What is proved (all sorry-free, `lake build Submission.E8WInvarianceT` green)

Let `shift i ν c = ν + c·αᵢ` (re-used from `Submission.E8WInvariance`) and

  `StrT N i ν = ⨆ c : ℤ, TLwt N (shift i ν c)`

the `αᵢ`-string through `ν` in the tensor square.  Then

* **`deriv_e_apply_mem_TLwt`, `deriv_f_apply_mem_TLwt`** — the derivation action of `Eᵢ` /`Fᵢ`
  raises/lowers the weight by `αᵢ` (`TLwt μ → TLwt (μ ± αᵢ)`), the tensor-square analogue of
  `endU_e_apply_mem_Lwt`/`endU_f_apply_mem_Lwt` of `Submission.E8WeightSpaces`;
* **`deriv_h_maps_StrT`, `deriv_e_maps_StrT`, `deriv_f_maps_StrT`** — the string is stable under
  `Hᵢ`, `Eᵢ`, `Fᵢ`;
* **`StrT_inf_eigenspace_shift`, `StrT_inf_eigenspace`, `StrT_inf_eigenspace_neg`** — the
  `Hᵢ`-eigenspaces inside the string are the single weight spaces
  `StrT ⊓ eigenspace (deriv Hᵢ) μ = TLwt …`, via the commons
  `Commons.LinearAlgebra.End.iSup_inf_eigenspace_eq`.

So the *whole* `𝔰𝔩₂`-string input of `E8WInvariance` has been reconstructed for `T N`.

### ⚠ The remaining obstacle (isolated exactly, with a minimal counterexample)

The next step is to form the *restricted* operators
`StrTH, StrTE, StrTF : Module.End ℂ ↥(StrT N i ν)`, check the `𝔰𝔩₂` commutators and local
nilpotence, and apply `Commons.LinearAlgebra.End.sl2_eigenspace_finrank_symm`.  This fails at
typeclass search, and **the obstruction is purely about the tensor square**:

```lean
example (N) (i) (ν) : AddCommGroup ↥(StrT N i ν) := inferInstance                -- ✔
example (N) (i) (ν) : Module ℂ ↥(StrT N i ν) := inferInstance                    -- ✔
example (N) (i) (ν) : AddCommMonoid (Module.End ℂ ↥(StrT N i ν)) := inferInstance -- ✔
example (N) (i) (ν) : Mul (Module.End ℂ ↥(StrT N i ν)) := inferInstance           -- ✔
example (N) (i) (ν) : One (Module.End ℂ ↥(StrT N i ν)) := inferInstance           -- ✔
example (N) (i) (ν) : Module ℂ (Module.End ℂ ↥(StrT N i ν)) := inferInstance      -- ✔
example (N) (i) (ν) : AddCommGroup (Module.End ℂ ↥(StrT N i ν)) := inferInstance  -- ✘ FAILS
example (N) : AddCommGroup (Module.End ℂ (T N)) := inferInstance                  -- ✔
```

so the `AddCommGroup` on `Module.End ℂ ↥(StrT N i ν)` is what is lost (an instance diamond
caused by the project's high-priority instances on `T N`), and `StrTH * StrTE - StrTE * StrTH`
does not even elaborate (`failed to synthesize HSub (Module.End ℂ ↥(StrT N i ν)) …`).
**Tried and did not help**: `letI : Module ℂ ↥(StrT N i ν) := Submodule.module _`, and
`attribute [local instance 10000] Submodule.module`.  The same code is *verbatim* in `E8WInvariance.lean`,
where it works for `↥(Str N i ν)` with `Str N i ν : Submodule ℂ (V ⧸ N)`.  The only structural
difference is that `T N` carries the extra high-priority instances `instModT`, `instSMulT`,
`instISTTensor` of `Submission.E8TensorBound`, so the `ℂ`-structure on `↥(StrT N i ν)` is
apparently not recognised when `Module.End` asks for its `Ring`.

**Suggested fixes for the next session**:
1. avoid the subtype's `Module.End` altogether — the most promising route: run the `𝔰𝔩₂`
   argument on `StrT N i ν` via `Submodule.subtype`/`Submodule.comap` and `LinearMap.ker` of the
   *ambient* operator `deriv Hᵢ - μ • 1`, where only `Module.End ℂ (T N)` (whose `AddCommGroup`
   and `Ring` instances do exist) is used, and where the string's stability is exactly
   `deriv_*_maps_StrT` (proved);
2. define the restricted operators with explicit instance ascriptions, e.g.
   `(StrTH N i ν : @Module.End ℂ ↥(StrT N i ν) _ _ _)`, and prove the commutators by `ext` with
   the instances pinned in the goal;
3. make `StrT N i ν` a plain `Submodule` built with `Submodule.mk` (rather than `⨆`), or restate
   the string as `LinearMap.range` of an explicit map, so that `Submodule.module` is the only
   `Module ℂ` candidate for the subtype.

The remaining content after that is routine: `deriv_lie`
(`deriv ⁅x,y⁆ = deriv x * deriv y - deriv y * deriv x`, a direct consequence of the
`LieRingModule` axiom for the tensor-product action), local nilpotence of `deriv Eᵢ`/`deriv Fᵢ`
on `T N` (from `Submission.E8LocallyNilpotent.e_locallyNilpotent`/`f_locallyNilpotent` through the
filtration `span {u^p a ⊗ u^q b : p + q = n}`), and the finrank transfer.

-/


/-!

## SESSION 30: ⭐⭐ THE `W`-INVARIANCE OF THE TENSOR SQUARE IS PROVED — the SESSION-29 gap is CLOSED

**Nothing in the proof of the target changed** (the target keeps its single `sorry`;
`lake build Submission` is green).  The flagged "next real gap" — the `W`-invariance of the weight
multiplicities of the tensor square, the input that lets `eq_of_freudenthal` be applied to the
*actual* constituents of `T = (V ⧸ N) ⊗ (V ⧸ N)` rather than only to the candidate characters
`Mnu i` — is now **proved**, in `Submission/E8WinTensor.lean` (sorry-free):

* **`finrank_TLwt_sref`** — `finrank ℂ ↥(TLwt N ν) = finrank ℂ ↥(TLwt N (sᵢν))` for every weight
  `ν` and every simple reflection;
* **`finrank_TLwt_dcl`**, **`finrank_TLwt_dc`** — the same for the iterated dominant-conjugate
  algorithm `dcl` and for `dc` (the form hypothesis (c) of `eq_of_freudenthal` asks for).

### The proof: a two-line convolution argument (no `𝔰𝔩₂` theory at all)

The weight multiplicities of the tensor square are the **convolution** of those of `V ⧸ N`:

  `dim (T N)_ν = ∑_{ξ ∈ L} d(ξ)·d(ν - ξ)`,   `d(ξ) = dim (V ⧸ N)_ξ`

(`Submission.E8TensorChar.finrank_TLwt_eq_sum`, already proved).  Now:

1. `d` is `W`-invariant: `d(sᵢξ) = d(ξ)` (`Submission.E8WInvariance.finrank_Lwt_sref`, PROVED);
2. the simple reflection `sᵢ` is additive and involutive on the weight lattice
   (`sref_sub`, `sref_involutive`), and `sᵢν - sᵢξ = sᵢ(ν - ξ)`;
3. `sᵢ` preserves the finite set `L = E8Iso.L` of lattice points of squared length `≤ 10`
   (which contains the support of `d`), because `qZ (sᵢv) = qZ v` (`qZ_sref`), so the substitution
   `ξ ↦ sᵢξ` is a bijection of `L` onto itself (`Finset.sum_bij`).

Hence `∑_ξ d(ξ)d(sᵢν - ξ) = ∑_ξ d(sᵢξ)d(sᵢν - sᵢξ) = ∑_ξ d(ξ)d(ν - ξ)`, which is exactly
`finrank_TLwt_sref`.

### ⚠ `Submission/E8WInvarianceT.lean` is therefore *not needed* (but is kept)

That file is the mirror of `E8WInvariance`'s `𝔰𝔩₂`-string argument for the tensor square.  Its
string machinery is fully proved there (`StrT`, the weight shifts `deriv_e/f_apply_mem_TLwt`, the
stability `deriv_*_maps_StrT`, the eigenspace identification `StrT_inf_eigenspace*`); the remaining
step (the restricted operators on `↥(StrT N i ν)`) is blocked by an instance diamond caused by the
project's high-priority `instModT`/`instSMulT`/`instISTTensor` on `T N`
(`AddCommGroup (Module.End ℂ ↥(StrT N i ν))` does not synthesise although all its ingredients do),
and is now **superseded**: the convolution route above proves the same statement without any
`𝔰𝔩₂` theory.  `E8WinTensor.lean` is the file to build on.

### What is left for step 2 (`eq_of_freudenthal` for the actual constituents), now much smaller

For a simple `U`-submodule `S ≤ T N` with a primitive generator of dominant weight `ord40 i`
(`exists_prim_of_simple`), the function `v ↦ finrank ℂ ↥(S ⊓ TLwt N v)` satisfies

* (a) value `1` at the top weight (the top weight space of a cyclic module with a primitive
  generator is one-dimensional);
* (b) the support bound (`posCon_of_mem_TLwt` + the highest-weight structure);
* **(c) `W`-invariance — NOW PROVED** (`finrank_TLwt_dc`, transported along the inclusion);
* (d) the Freudenthal recursion (`freudenthal_recursion_of_cyclic`, transported along
  `submoduleLinearEquivOfLieEquiv`).

Then `eq_of_freudenthal` gives `Mnu i = ` the character of `S`, i.e. step 3 of the SESSION-28
roadmap (the isotypic system `mf2v i = ∑_d cc_d · Mtab d i` ⟹ `cc = ccv` ⟹ `ncard ≥ 40`), and then
the assembly.

-/

-/

/-!

## SESSION 32: ⭐ `E8ConstChar` IS PROVED — AND THE FINAL GAP IS NOW A SINGLE CLASSICAL THEOREM

**The target still has its single `sorry`** (`lake build Submission` green, 8839 jobs).  Two things
were done this session: (I) the *characters of the actual simple constituents* are now known
(`Submission/E8ConstChar.lean`, sorry-free, builds in ≈ 28 s, **not yet imported by
`Submission.lean`**), and (II) the last remaining gap has been *identified and reduced* to a single
classical theorem, with a complete proof strategy for everything around it.

### 1. ⭐⭐ `Submission/E8ConstChar.lean` — DONE, sorry-free, builds

For a simple `U`-submodule `S ≤ T N` with a primitive generator `x` of dominant weight
`Λ = ord40get i` (`hxS`, `hx0`, `hprim : ∀ j, deriv (SerreE j) x = 0`,
`hwt : ∀ j, deriv (SerreH j) x = ((Λ j : ℤ) : ℂ) • x`, `[IsSimpleModule U ↥S]`) the function

  `chFun N S μ := (finrank ℂ ↥(restr S ⊓ TLwt N μ) : ℚ)`   (`restr S := S.restrictScalars ℂ`)

satisfies the four hypotheses of `eq_of_freudenthal` with top weight `Λ`:

* **the bridge `Wt ↔ TLwt`**: `wtEquiv`, `mem_Wt_of_mem_TLwt`, `mem_TLwt_of_mem_Wt`,
  `chFun_eq_Wt`; the key technical lemma is **`coe_smul_C`** (the `ℂ`-scalar action on `↥S`
  commutes with the coercion — it is *not* `Submodule.coe_smul`, since the `ℂ`-action goes through
  `instModuleSubC`/`restrictScalars`; the proof routes through
  `Submission.Enveloping.algebraMap_smul_eq` twice);
* **(a)** `chFun_top_ne_zero` (`0 < finrank` because the top weight space contains `x ≠ 0`);
* **(b)** `chFun_support` — from the commons
  `Commons.Algebra.Lie.SerreConstruction.weight_support_of_primitive` at `M := ↥S`, with
  `exists_smul_eq_of_simple` (`IsSimpleModule` ⟹ `span U {z} = ⊤` ⟹ every `m` is `u • z`);
* **(c)** `chFun_dc` — one line from `E8WInvSub.finrank_inf_TLwt_dc`;
* **(d)** `chFun_freudenthal` — `E8FreudenthalGen.freudenthal_recursion_of_cyclic` at `M := ↥S`,
  transported along `chFun_eq_Wt`;
* **CAPSTONE** `chFun_eq_Mnu` : **`∀ μ, chFun N S μ = chFun N S Λ * Mnu i μ`**, by
  `E8Character.eq_of_freudenthal` applied to `m := MnuQ i := (Mnu i · : ℤ → ℚ)` and
  `m' := chFun N S · / chFun N S Λ` (so hypothesis (a) for `m'` is `c/c = 1`; the normalisation by
  `c := chFun N S Λ ≠ 0` is what *bypasses* having to prove `chFun S Λ = 1`).
  Auxiliary: `MnuQ_top/_support/_dc/_freud` (the four hypotheses for the rational-valued table), and
  `freud_div` (the Freudenthal recursion is stable under division by a non-zero constant).

  ⚠ Note `Mnu : Fin 40 → (Fin 8 → ℤ) → ℤ`, so *all* the `Mnu`-hypotheses must be transported to `ℚ`
  by `MnuQ`.

⚠ Two hazards found while writing this file (do not rediscover):
* `S.restrictScalars ℂ` in a *statement* is ambiguous: dot notation may bind `S` as the **ring**
  argument of `Submodule.restrictScalars`, producing a `Submodule ℂ ↥S`.  Use the `abbrev restr`.
* the section variable `S` must not shadow the *ring* variable `S` of
  `Submodule.restrictScalars_mem`: write `Submodule.restrictScalars_mem ℂ S x`.

### 2. ⭐ THE REMAINING GAP, EXACTLY

Everything else is in place.  Writing `T := T N`, `λ := ω₁+ω₈`, `U := U(e₈)`, the isotypic
decomposition gives (Mathlib `IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp`, or the
`IsIsotypic` API)

  `T ≅ ⨁_{i : Fin n} S_i`,  each `S_i` simple,

so, with `d_i : Fin 40` the top weight of `S_i` (`exists_prim_of_simple`) and
`c_i := chFun S_i (ord40get d_i) ≥ 1`,

  **`dim T_μ = Σ_i chFun S_i μ = Σ_i c_i · Mnu (d_i) μ`**   (by `chFun_eq_Mnu`),

hence, at the 40 dominant weights and with `G_e := Σ_{i : d_i = e} c_i ≥ 0`,

  (★) **`dim T_{ord40 d} = Σ_e G_e · Mtab (e,d)`**   for all `d : Fin 40`.

`E8Extract.ccv_system` states `mf2v d = Σ_e ccv_e Mtab(e,d)` (proved by `decide`), and the system is
unitriangular (`Mtab_support` + `Mtab d d = 1`), so `dim T_d = mf2v d` for all `d` implies
**`G = ccv`**, hence **`G_e = ccv_e ≥ 1` for all `e`** (`E8Extract.ccv_pos`); with
`compData_inj` + `ncard_tensor_le_forty` this gives `ncard = 40`.

**Therefore the whole target is reduced to the single identity**

  **(★★)  `dim T_{ord40 d} = mf2v d`  for all `d : Fin 40`.**

(`dim T_ν = finrank ℂ ↥(TLwt N ν)` is the pair count `Σ_ξ mfun ξ · mfun (ν-ξ)`, by
`E8TensorChar.finrank_TLwt_eq`.)

### 3. ⚠ WHY (★★) CANNOT BE PROVED BY DIRECT COMPUTATION (measured)

* `dim T_ν = Σ_{ξ ∈ E8Iso.L} dmul ξ · dmul (ν-ξ)` has `56881` terms per `ν` (the support =
  `{qq ≤ 10}`), i.e. `40 · 56881 = 2.3·10⁶` `qq`-evaluations.  **Measured** this session: a `decide`
  over 2000 terms of this shape does not finish in 30 minutes (≈ 0.9 s per `qq`, because `qZ` is a
  64-term `∑ᵢⱼ` with a `Matrix`-lookup), i.e. ≈ 600 h.  Even a hand-unrolled symmetric form is
  ≈ 0.09 s/term ⟹ ≈ 60 h.  **Infeasible.**
* The *total* number of non-zero terms over all 40 `ν` is only **184 188** (measured,
  `.tmp_s28/pairs.py`), and the pair counts are `1,2,2,4,14,10,20,40,14,28,57,84,34,88,164,170,
  294,316,500,127,254,597,828,794,1248,1210,1878,2748,2999,3938,2398,3948,5586,7834,10800,11655,
  15058,21078,30488,56881` — but *completeness* of such a list needs a scan of the 56881-point
  support for each `ν`, so this does not help.
* `E8Iso.L` is **non-computable** (`Set.Finite.toFinset.toList`), so no `decide` over it is possible;
  a computable replacement would need `43·10⁶ = 9⁸` candidates.

### 4. ⭐ THE PATH THAT DOES WORK: KLIMA, AND THE ONE MISSING CLASSICAL THEOREM

The classical route needs no lattice computation at all, and **every step except the last is
either already done, already in the commons, or a small computation**:

1. **`A_ρ · ch V = A_{λ+ρ}`  (WCF for `V`)** — the SESSION-24/26 plan, and it *is* computationally
   certifiable: for `μ = ρ + ν`, `ν ∈ the7`, every term `mfun(μ-wρ)` needs
   `qq(μ-wρ) ≤ 10`, hence (as `ρ-wρ ∈ ℕΦ⁺`, `ν` dominant) `htOf(ρ-wρ) ≤ 5`, hence
   `e8ht(wρ) ≥ 615`, hence **`ℓ(w) ≤ 4`** (`Commons.LinearAlgebra.Matrix.Cartan.E8_wact_small_height_length`).
   The ball of radius 4 has **450** elements and is certified (`Submission/E8Ball.lean`,
   `E8_weyl_ball4`), the `WSum = ballSum` bridge is `Submission/WCFSetup.lean`
   (`WSum_eq_ballSum'`), and the seven values are the `decide`s of `Submission/E8CharCompute.lean`.
   ⟹ **this step is within reach.**
2. **`A_ρ ch T = A_{λ+ρ} ch V`** — pure associativity of the group algebra:
   `A_ρ·(chV·chV) = (A_ρchV)·chV` with `ch T = chV · chV` (the *convolution*, proved as
   `E8TensorChar.finrank_TLwt_eq`).
3. **`c_x := [e^{x+ρ}](A_{λ+ρ}chV) = Σ_{w} ε(w)·mfun(x+ρ-w(λ+ρ))` is COMPUTABLE**: the terms vanish
   unless `qq(x+ρ-w(λ+ρ)) ≤ 10`; the SESSION-25 ℓ-bound (`ℓ(w) ≤ B_x := ⟪x,λ⟫ - qq(x)/2 ≤ 5`, and
   `≤ 4` by the Dynkin-diagram argument) confines the sum to the 450-element ball.  **Verified
   numerically** (SESSION 25): the 40 values are exactly the multiplicities
   `[1,1,1,1,2,1,1,2,1,2,1,2,1,4,4,3,5,4,7,1,3,3,6,7,6,7,10,10,4,7,2,8,8,9,5,4,5,3,2,1]`.
   Also needed: **`c_x = 0` for dominant `x ∉ the40`** — provable, because
   `qq(x+ρ-w(λ+ρ)) ≥ qq(x-λ) > 20` for those `x`, i.e. `c_x ≠ 0` forces `qq(x-λ) ≤ 20` (a *finite*
   check on dominant `x`).
4. **`A_{λ+ρ}chV = Σ_{x∈the40} c_x A_{x+ρ}`** — because both sides are anti-invariant and their
   coefficients at *dominant* weights agree (step 3), and an anti-invariant function is determined
   by its dominant coefficients.  Hence with (2): **`A_ρ(ch T - Σ_{x∈the40}c_x S_x) = 0`** where
   `S_x := A_{x+ρ}/A_ρ`.
5. **THE NO-KERNEL LEMMA** (easy, and the key to step 6): if `f` is a W-invariant formal series with
   support bounded above (in `ν - Q⁺`) and `A_ρ f = 0`, then `f = 0`.  Proof: `A_ρ = e^ρ D` with
   `D = ∏_{α>0}(1-e^{-α}) = 1 - Σ_α e^{-α} + …`; at the *top* weight `ν` of the support,
   `[e^ν](Df) = f_ν ≠ 0`.
   ⟹ **`ch T = Σ_{x∈the40} c_x S_x`** (step 4 + 5).  ⭐ *This is a genuine theorem, and it already
   says that all forty candidate characters `S_x` occur with a positive coefficient.*
6. **THE ONE REMAINING CLASSICAL THEOREM — the Weyl character formula for the constituents**:
   `S_x = ch L(x)`, i.e. `A_ρ ch L(x) = A_{x+ρ}` for dominant `x`.
   Equivalently (the *Kostant multiplicity formula*): the coefficients of `S_x` are the weight
   multiplicities `dim L(x)_μ`.

   **Why everything else fails but this one suffices.**  We have `ch T = Σ_{x∈the40}c_x S_x` (step 5)
   and, by `chFun_eq_Mnu` + the isotypic decomposition, `ch T = Σ_{e∈the40}G_e ch L(e)`.  Once
   `S_x = chL(x)`, we get `G = c` — and `c_x ≥ 1` (step 3) gives `ncard = 40` directly, with **no
   computation of `dim T_ν` at all**.  More generally: the W-invariant series with support in
   `ν - Q⁺` are spanned by the `ch L(μ)` (a *descending induction on the cone order* — pick the
   maximal dominant weight `η` of the support and subtract `f(η)·chL(η)`; well-founded since
   `htOf` strictly decreases), so `S_x = chL(x) + Σ_{μ≺x}a_{xμ}chL(μ)` with `a_{xx} = 1`
   (provable: `[e^x](A_ρS_x) = Σ_w ε(w)m_x(x+ρ-wρ)` and all `w ≠ 1` terms vanish by the support
   bound; also `a_{xμ} = 0` for `μ ⋠ x`).  Hence `G_e = Σ_{x⪰e}c_x a_{xe}`, and `G_e ≥ 1`
   follows from `a_{xμ} ≥ 0` — which *is* the WCF/Kostant statement.

   ⚠ **Numerical warning (do not retry)**: one cannot verify `Σ_w ε(w)Mtab(x, y-wρ) = δ_{xy}`
   computationally over a small ball — that sum does **not** truncate (it converges only at radius
   ≈ 20-25 in `W`, i.e. ~10⁵–10⁶ elements; `.tmp_s28/conv2.py`, `extract2.py`: with the ball of
   radius 10 there are still 2 non-converged pairs of 1600).  The identity must be *proved*, not
   computed.  (It *does* converge fast for the specific examples `(x,y) = (λ,λ)`, `(λ,0)`, which is
   why the first test was misleading.)
   ⚠ The "alternant uniqueness" (`F` anti-invariant with support in `X - Q⁺` and `F(X) = 1` ⟹
   `F = A_X`) is **FALSE** in general (`A_X + A_{X-α}` can be a counterexample), so the classical
   proof must go through the Freudenthal/Kostant or the BGG route.

### 5. NEXT STEPS (in order)

1. **`Submission/E8Isotypic.lean`** — formalise §2: for the decomposition `T ≅ ⨁ S_i`, prove
   `finrank ℂ ↥(Wt (M := T N) μ) = Σ_i finrank ℂ ↥(Wt (M := ↥S_i) μ)` (the `Wt` of a direct sum /
   product is the direct sum / product of the `Wt`s), conclude (★), and get `E8ConstChar` +
   `ccv_system` + `Mtab_support` ⟹ `G = ccv` ⟹ `ncard ≥ 40` — *conditional on* (★★).
   ⚠ **Instance hazard**: `Module U (∀ i, W i)` resolves to the framework instance
   `LeanEval.RepresentationTheory.lieModuleToEnvelopingModule`, *not* to `Pi.module`, and the
   `IsScalarTower ℂ U (∀ i, W i)` search then diverges — so **avoid the `Pi`-type route**; use the
   *internal* direct sum of the submodules `↥Z_c ≤ T N` with the projections
   `π_c := (DirectSum.component …).comp (DirectSum.IsInternal.chooseDecomposition …).symm`.
2. **WCF for `V`** (step 4.1 above) — concrete, small computation.
3. **The no-kernel lemma** (step 4.5) — formal series (`ℂ[P]`), the Weyl denominator formula
   (`E8_weyl_denom`, already in the commons), and the top-coefficient argument.
4. **Step 4.3-4.4** — the 40 values `c_x` (ball of radius 4, `E8Ball`) + the `qq(x-λ) ≤ 20` finite
   check + the anti-invariance argument.
5. ⭐⭐⭐ **THE LAST THEOREM — AND IT IS *PROVABLE*: SESSION 32's KEY DISCOVERY**

   We need `m_x(μ) = Mtab (x, domIdx μ)` for all `x ∈ the40` (`m_x =` the coefficient function of
   `S_x = A_{x+ρ}/A_ρ`; this is exactly the **Kostant multiplicity formula / WCF for the
   constituents**).  By `E8Character.eq_of_freudenthal` it suffices that `m_x` satisfies (a)–(d)
   with top weight `x`:
   (a) `m_x(x) = 1` — provable: `[e^{x+ρ}](A_ρS_x) = [e^{x+ρ}]A_{x+ρ} = 1` and every `w ≠ 1` term
       vanishes because `x+ρ-wρ ≻ x` is outside the support `x - Q⁺` of `S_x`;
   (b) support ⊆ `x - Q⁺` — by construction;
   (c) W-invariance — `S_x` is a quotient of two anti-invariant series;
   (d) **the Freudenthal recursion — and this IS provable, by the following argument:**
       the classical Freudenthal derivation (as formalised in `Submission/E8FreudenthalGen.lean` for
       a module on which `Ω` acts by the scalar `cas(x)`) uses only:

         * `Ω = Σ_i h_i h^i + 2Σ_{α>0} e_α f_α` (the `sl₂`-string decomposition), and
         * `tr(Ω|M_μ) = cas(x)·dim M_μ` on every weight space, and
         * for every positive root `α`, the finite-`α`-string identity
           `tr(e_αf_α|M_μ) = Σ_{k≥1} ⟪μ+kα,α∨⟫ dim M_{μ+kα}`.
           (`e_α` is locally nilpotent, so the `α`-string through `μ` is finite.)

       All three are *linear* in the module, and `S_x` is the **Euler characteristic of Verma
       modules**:
         `S_x = A_{x+ρ}/A_ρ = Σ_w ε(w) e^{w(x+ρ)}/A_ρ = Σ_w ε(w)·chM(w·x)`,
       where `M(ν)` is the Verma module, `chM(ν) = e^ν/∏_{α>0}(1-e^{-α})` and
       `w·x := w(x+ρ)-ρ` is the dot action.  The three inputs therefore hold *verbatim* for the
       virtual object `S_x`, because they hold for each `chM(w·x)`.  The decisive point is the third
       condition:

         **⭐ `cas(w·x) = cas(x)` for every `w ∈ W`**  —  because, with `cas(ν) = ⟪ν,ν+2ρ⟫`,
           `⟪w(x+ρ)-ρ, w(x+ρ)+ρ⟫ = ⟪w(x+ρ),w(x+ρ)⟫ - ⟪ρ,ρ⟫ = qq(x+ρ) - qq(ρ)`,
           which is *independent of `w`* (the `ρ`-cross terms cancel, and `qq` is `W`-invariant).
       ⟹ `Ω(S_x) = Σ_w ε(w)·cas(w·x)·chM(w·x) = cas(x)·S_x`, i.e. `Ω` acts on `S_x` by the scalar
       `cas(x)` on every weight space;
       ⟹ **the Freudenthal recursion holds for `m_x`** (run the `E8FreudenthalGen` derivation with
       `tr` replaced by the coefficient functional, all inputs being linear over the `chM(w·x)`).

   **Consequence (the plan is now complete, with no gaps):**
   `eq_of_freudenthal (lam := x)` applied to `m_x` and `MnuQ x` gives **`m_x μ = Mtab (x, domIdx μ)`
   for every `μ`**; hence from step 5, for every `μ`,

     `dim T_μ = Σ_{x∈the40} c_x · Mtab (x, domIdx μ)`,   and at `μ = ord40get d`:
     **`mf2v d = Σ_{x∈the40} c_x · Mtab (x,d)`**   (a finite `decide`-able identity!),

   and `E8Extract.ccv_system` + the unitriangularity (`Mtab_support`, `Mtab x x = 1`) give
   **`c = ccv`**, hence `c_x = ccv_x ≥ 1`.  Finally, the isotypic decomposition
   `ch T = Σ_{e∈the40} G_e · ch L(e)` with `G_e = Σ_{i : d_i = e} c_i = m_e·c'_e`
   (`c'_e := chFun S_e(ord40 e) = dim L(e)_e > 0`) and `ch L(e) = c'_e·Mtab (e,·)` (E8ConstChar)
   gives `Σ_e G_e Mtab(e,domIdx μ) = Σ_x c_x Mtab(x,domIdx μ)` for all `μ`, hence (again by
   uniqueness) **`G = c = ccv`**, so `m_e = c_e / c'_e > 0` for every `e ∈ the40`:
   **every one of the forty weights is the top weight of a constituent**, and `compData_inj` +
   `ncard_tensor_le_forty` give **`ncard = 40`** ✓.

   ⚠ We never need `c'_e = 1` (the one-dimensionality of the top weight space): only `c'_e > 0`,
   which is `E8ConstChar.chFun_top_ne_zero`.  And we never need the pair-count character
   `E8TensorChar.finrank_TLwt_eq` of the tensor square: the `dim T_μ` identity above replaces it.

### 6. THE ISOTYPIC SYSTEM: WHAT IS NOW AVAILABLE

* **NEW COMMONS LEMMA (proved by a fleet child, after a `declare_false` on the first version)**:
  `Commons.LinearAlgebra.Pi.finrank_iInf_ker_pi_of_field` —
  for a finite family of **finite-dimensional** modules `W i` over a **field** `R` and pointwise
  linear operators `g j i`, the simultaneous kernel of the pointwise operators on `Π i, W i` has
  `finrank` equal to the sum of the `finrank`s of the simultaneous kernels.  (The version without
  `[Field R]`/`[Module.Finite R (W i)]` is **false**: `Module.finrank` is `Cardinal.toNat ∘ rank`,
  which is not additive in general; the child produced a machine-checked counterexample with
  `W false = ℚ`, `W true = ℚ[X]`.)  With this, applied to `Z_c ≅ (Fin n_c → S_c)` from
  `IsIsotypicOfType.linearEquiv_fun`, the isotypic decomposition of `T N` gives
  `finrank ℂ ↥(Wt (M := ↥Z_c) μ) = n_c · finrank ℂ ↥(Wt (M := ↥S_c) μ)`.
  ⚠ **Instance hazard** (measured this session): `Module U (∀ i, W i)` synthesises to the
  *framework* instance `LeanEval.RepresentationTheory.lieModuleToEnvelopingModule`, not to
  `Pi.module`, and the subsequent `IsScalarTower ℂ U (∀ i, W i)` search then diverges;
  `attribute [-instance] LeanEval.RepresentationTheory.lieModuleToEnvelopingModule` fixes synthesis
  but must be scoped carefully.  The direct-sum route through `LinearEquiv.finrank_eq` avoids it.

### 7. NEW THIS SESSION: `Submission/E8WCFV.lean` (sorry-free, builds in 15 s, NOT imported)

The infrastructure of the Weyl character formula for `V`, as far as it needs no numerical ball
evaluation:

* `mfun_wact`, `mfun_ap` — `ch V = mfun` is `W`-invariant (`mfun = mnorm ∘ qZ`, `qZ` is
  `W`-invariant: `Commons…qZ_wact`; the `wact` in `WCFSetup` is the commons one, **not**
  `Submission.WeylBall.wact` — the latter's namespace is not even imported by `WCFSetup`);
* `WSum_mfun_anti` — the Weyl sum of `mfun` is anti-invariant;
* `altLP` (the alternant `∑_M det(M)·[M(λ+ρ) = x]`), `altLP_ap`, `altLP_wact` — anti-invariance of
  the target, by a `Finset.sum_bij` reindexing `M ↦ M₀ * N` (the `if`-rewriting needs `by_cases`,
  not `rw`);
* `hqq_le` — **the support estimate** `qZ δ ≤ qZ (ν + δ)` for `ν` dominant and `δ` in the cone
  (from `Commons…E8_qZ_add_mem_cone_dominant` and `qZ ν ≥ 0` via `diag_le_qZ`);
* `mfun_eq_zero_of_ten_lt` — `mfun` vanishes off `qq ≤ 10`.

Remaining for the full `WCF_V` theorem (see §5.1 above): the reduction to dominant `x`
(`exists_dominant_WConj` gives the word, and `WConj`'s `foldl` is definitionally the commons `wact`
— verified), the wall case (both sides vanish by anti-invariance along a reflection fixing `x`),
the `qq (x-ρ) > 10` case, and the seven `decide`-checked ball values of
`Submission/E8CharCompute.lean` (restate the `example`s there as named theorems; the ℓ-bound is
`hqq_le` + `E8_qZ_rho_sub_wact` + `E8_wact_small_height_length`).

### 7bis. ⭐⭐ SESSION 32 (cont.): **THE WEYL CHARACTER FORMULA FOR `V` IS PROVED**

`Submission/E8WCFV.lean` (sorry-free, builds in 31 s; imports `Submission.WCFSetup`) now contains

  **`WCF_V (x : Fin 8 → ℤ) : WSum (fun v => (mfun v : ℚ)) x = altLP x`**

i.e. **`A_ρ · ch V = A_{λ+ρ}`** for `V = L(ω₁+ω₈)`, where
`WSum f x = ∑_{M ∈ WG} det(M)·f(x - Mρ)` and `altLP x = ∑_{M ∈ WG} det(M)·[M(λ+ρ) = x]`.

Proof (all of it; the numerical ball values live in the new file `Submission/E8WCFBall.lean`):

* `mfun_wact`/`mfun_ap` (`mfun` is `W`-invariant) ⟹ `WSum_mfun_anti`; `altLP_ap`/`altLP_wact`
  (the target is anti-invariant, by a `Finset.sum_bij` reindexing);
* hence it suffices to check **dominant** `x` (`exists_dominant_WConj` gives a word `L` with
  `wact L x` dominant; `WConj`'s `foldl` is definitionally the commons `wact`), and the identity
  for `x` follows from the identity for `wact L x` by multiplying both sides by `ε(L)`;
* three cases for the dominant `x`:
  - **wall** (`x i = 0`): both sides vanish, by anti-invariance along the reflection `sᵢ` fixing `x`
    (`WSum_mfun_eq_zero_of_wall`, `altLP_eq_zero_of_wall`);
  - **`qq (x-ρ) > 10`**: every term of the Weyl sum vanishes, because
    `qq (x - wρ) ≥ qq (x-ρ) > 10` (`qq_le_add` from `E8_qZ_le_of_dominant`, using that `x - ρ` is
    dominant in the strictly-dominant case) and `mfun` is supported on `qq ≤ 10`
    (`mfun_eq_zero_of_ten_lt`); the target vanishes by `altLP_eq_zero_of_ne`;
  - **`qq (x-ρ) ≤ 10`** (`WSum_mfun_eq_of_le`): then `ν := x - ρ` is dominant of norm `≤ 10`, so
    `ν ∈ the7` (`mem_the7_of_norm_le`), and the ℓ-bound argument shows that a term with
    `ℓ(w) > 4` vanishes: `mfun (x - wρ) ≠ 0` ⟹ `qq (x-wρ) ≤ 10` ⟹
    `qq (ρ-wρ) ≤ qq (x-wρ) ≤ 10` (`E8_qZ_rho_sub_wact` and `hqq_le`) ⟹
    `e8ht (ρ-wρ) ≤ 5` ⟹ `615 ≤ e8ht (wρ)` ⟹ `E8_wact_small_height_length` ⟹ `M ∈ ballSet`;
    hence `WSum = ballSum` (`WSum_eq_ballSum'`) and the value is one of the **seven `decide`-checked
    identities** of `Submission/E8WCFBall.lean`
    (`ballSum_lam = 1`, `ballSum_e1 = ballSum_2e7 = ballSum_e6 = ballSum_e0 = ballSum_e7 =
    ballSum_zero = 0`, combined in `ballSum_the7`).

⚠ **Memory hazard (measured, and it cost two failed builds)**: `all_goals decide` over the seven
450-term ball sums **exceeds the 12 GB cap**; splitting them into seven separate theorems fixed it
(`Submission/E8WCFBall.lean` builds in 433 s).  A single `by decide` over 450 terms is fine.

### 7ter. ⭐⭐ SESSION 32 (cont. 2): THE REMAINING GAP IS NOW `VermaWeight`-SHAPED

`Submission/E8Kostant.lean` (NEW, sorry-free, builds in 34 s) contains the two inputs that make the
last theorem (d) of §5 *mechanical*:

* **`casOf_eq_bil : casOf ν = (1/60)·(qq (ν+ρ) - qq ρ)`** — via `Bint_eq_qq : Bint ν = qq (ν+ρ)`
  and `cnu_eq_gen`;
* ⭐ **`casOf_dotact : casOf (dotact L x) = casOf x`** where `dotact L x = wact L (x+ρ) - ρ` — the
  Casimir eigenvalue of the Verma module `M(w·x)` does not depend on `w`.  (This is the `w`-independence
  of `⟪w(x+ρ)-ρ, w(x+ρ)+ρ⟫ = qq(w(x+ρ)) - qq(ρ)`.)
* **`eq_of_MnuQ`** — the packaged uniqueness: any `m` satisfying (a)–(d) at top weight `ord40get i`
  is `Mnu i` (the four hypotheses for `Mnu` being `Mnu_top/_support/_dc/_freud`);
* **`KostantP`** — the Kostant partition function (`= #{f : Fin 120 → ℕ | Σ f_j pR_j = γ}`),
  with `KostantP_zero = 1`, `KostantP_eq_height` (the total height of a decomposition is `htOf γ`)
  and `KostantP_eq_zero_of_not_posCon` (the support is the cone).

**The refined plan for (d) — no new theory is needed, only the Verma module:**

1. For every weight `ν`, construct the Verma module `M(ν)` as a `U(e₈)`-module with
   `endM Omega = casOf ν • 1` and `Module.finrank ℂ ↥(Wt (M := M(ν)) μ) = KostantP (μ - ν)`.
   (`Submission/E8FreudenthalGen.freudenthal_recursion` is stated for an **arbitrary** module with
   scalar Casimir, so this one construction is all that is missing — the same construction
   `Submission/VermaWeight.lean` carries out for the single weight `ω₁+ω₈`.)
2. Apply `freudenthal_recursion` to each `M(w·x)`: for dominant `ν` with `x - ν ∈ Q⁺`,
   `(Bint (w·x) - Bint ν)·dim M(w·x)_ν = 2·Σ_{j,k} brk(ν+kα_j,α_j)·dim M(w·x)_{ν+kα_j}`.
3. Multiply by `ε(w)` and sum over `w ∈ W`: the **left** side is `(Bint x - Bint ν)·m_x(ν)`
   because `Bint (w·x) = Bint x` (`casOf_dotact` + `casOf_eq_bil`), and the **right** side is
   `2·Σ_{j,k} brk(ν+kα_j,α_j)·m_x(ν+kα_j)` because the sum over `W` is finite at each weight
   (the same truncation as in `freudenthal_recursion`).  That is **exactly (d) for `m_x`**.
4. `eq_of_MnuQ` then gives `m_x = Mtab (x, ·)`, hence `ch T = Σ_{x∈the40} c_x·ch L(x)` by §5's
   no-kernel lemma, and the ball/Klimyk values give `c_x = ccv_x` and `ncard = 40`.

So the last gap is *not* the Weyl character formula any more: it is "instantiate the existing
`freudenthal_recursion` at the Verma module of an arbitrary weight".

### 8. FILES TOUCHED

* `Submission/E8ConstChar.lean` — **NEW**, sorry-free, builds (28 s).  NOT yet imported by
  `Submission.lean`.
* `Submission/E8WCFV.lean` — **NEW**, sorry-free, builds (31 s), contains `WCF_V`.  NOT yet imported.
* `Submission/E8WCFBall.lean` — **NEW**, sorry-free, builds (433 s): the seven `decide`-checked ball
  values (split into seven theorems to stay under the memory cap).  NOT yet imported.
* `Submission/E8Kostant.lean` — **NEW**, sorry-free, builds (34 s): `casOf_dotact`, `eq_of_MnuQ`,
  the Kostant partition function.  NOT yet imported.
* `Submission.lean` — this roadmap only; the target keeps its single `sorry`.
* commons: `Commons.LinearAlgebra.Pi.finrank_iInf_ker_pi_of_field` (+ helpers `finrank_pi_submodule`,
  and the counterexample lemmas `mem_span_range_single_sub`, `pi_split_at`).
* Scratch: `.tmp_s28/{weylball.py,extract.py,extract2.py,conv.py,conv2.py,pairs.py}` (numerics).

-/



/-!
### 7quater. ⚠️⚠️ SESSION 33: A DECISIVE NEGATIVE RESULT — AND THE CORRECTED PLAN

#### 1. `T N` is **NOT** cyclic, so the Freudenthal recursion with top weight `2λ` is FALSE

SESSION 32 §7ter proposed to prove `dim T_{ord40 i} = mf2v i` by
`eq_of_freudenthal (lam := 2λ)` comparing the table `mf2` with the *actual* weight-multiplicity
function `chT` of the tensor square.  **This is impossible.**  The point is that
`Ω` does **not** act on `T N = L(λ) ⊗ L(λ)` by the scalar `casOf (2λ)`:

* the `2λ`-weight space of `T N` is one-dimensional, spanned by `v̄ ⊗ v̄` (the only constituent
  with top weight `2λ` contributes there), and `v̄ ⊗ v̄ ∈ L(2λ)`; as `L(2λ)` is irreducible and
  `U·(v̄⊗v̄)` is a submodule of the *completely reducible* module `T N` whose top weight is `2λ`,
  the submodule generated by `v̄ ⊗ v̄` is exactly `L(2λ)` — **not** all of `T N`;
* a module generated by one vector on which `Ω` acts by `casOf (2λ)` would have `Ω = casOf(2λ)·1`
  everywhere (`Omega_smul_of_cyclic`), hence every constituent would have the *same* Casimir
  eigenvalue, hence (dominant top weights) be equal to `2λ`: `T N` would be isotypic, i.e.
  `ncard = 1`.  Numerically `ncard = 40`.

**Numerical confirmation** (`Submission/Work/Scratch_zk5.lean`, `#eval`, 50 min) of the identity
`(Bint 2λ - Bint ν)·MF2 ν = 2·Σ_{j,k} brk(ν+k·pR j, j)·MF2(ν+k·pR j)` (`MF2 v := mf2v (domIdx v)`)
at the forty dominant `ν`: it holds **only at `i = 0` (`ν = 2λ`)**; the left side is strictly larger
for every other `i` (e.g. `i=1`: 8 vs 4, `i=3`: 32 vs 16, `i=4`: 520 vs 392, `i=34`:
1265620608 vs 1127372064, `i=39`: 33500515860 vs 30917927040).

⟹ everything in §7ter that used `freudenthal_recursion` at `M := T N` (and the "compare `mf2`
with `chT` by `eq_of_freudenthal`" step of §5) must be discarded.  The recursion is *only* valid
for modules with a **single** Casimir eigenvalue, i.e. for one constituent at a time (that is
exactly what `E8Extract.freud_star` and `E8Rec.Mnu_freud` do).

#### 2. What is nevertheless available (all sorry-free)

* `E8TensorChar.finrank_TLwt_eq_sum` — `dim (T N)_ν = Σ_{ξ ∈ E8Iso.L} mfun ξ · mfun (ν-ξ)`,
  i.e. `ch T = (ch L(λ))²` in exact form;
* `E8ConstChar.chFun_eq_Mnu` — for an **actual** constituent `S` of `T N` with top weight
  `ord40 i`, `chFun S = chFun S (ord40 i) · Mnu i`, i.e. *the constituents' characters are known*
  (`Mtab i (domIdx ·)`), with the top multiplicity `c'_i ≥ 1`;
* `E8Star` + `E8Rec` (`Mnu_top/_support/_dc/_freud`) + `E8Kostant.eq_of_MnuQ`: `Mtab i (domIdx ·)`
  is the **unique** function with the four hypotheses (a)–(d) at top weight `ord40 i`;
* `E8Extract.ccv_system` (a `decide`): `mf2v i = Σ_d ccv d · Mtab d i` with `ccv_pos : 1 ≤ ccv i`;
* `E8Enum.mem_the40` (**completeness of the list!**): a dominant `ν` with `2λ - ν ∈ ℕΦ⁺` is one of
  the forty — this is what makes the *finite* Freudenthal computations legitimate;
* ⭐ **NEW `Submission/E8NoKernel.lean`** (this session, sorry-free, builds in seconds):
  * `ht_rho_sub_ap_pos` — `0 < htOf (ρ - wρ)` for `w ≠ 1` (via `E8_rho_sub_wact_rho_eq_sum`
    + `one_le_e8ht_of_mem_P`);
  * `WSum_eq_zero_of_bounded` — **the no-kernel lemma**: if `f` is supported on a set of
    `htOf`-bounded weights and `WSum f ≡ 0`, then `f = 0`;
  * `eq_of_WSum_eq` — hence `A_ρ` is **injective** on bounded-height functions:
    `WSum f = WSum g ⟹ f = g`.
  These are the *uniqueness half of the Weyl character formula*: they convert an identity of Weyl
  sums into an identity of the functions, and are exactly what turns
  "`A_ρ m = A_{μ+ρ}` + support condition" into "`m` is the character" (the `A_ρ`-argument of §3).

#### 3. The corrected route to `ncard = 40` (no circularity left)

Recall the needed extraction: with `b_e := Σ_{c : λ_c = e} m_c · c'_e` (isotypic multiplicity
`m_c ≥ 1`, top multiplicity `c'_e ≥ 1`), the isotypic decomposition plus `chFun_eq_Mnu` give
`ch T = Σ_{e ∈ the40} b_e · Mtab(e, domIdx ·)`, and `ccv_system` identifies `b_determines = ccv`
**provided** the forty numbers `dim T_{ord40 i}` are known to equal `mf2v i`
(token: `Mtab` is unitriangular with `Mtab i i = 1` and `Mtab i e ≠ 0 ⟹ e ⪯ i` in the `ord40`
order; `ccv e ≥ 1` then yields `b_e = ccv e ≥ 1`, so *every* one of the forty weights is realised,
and `compData_inj` + `ncard_tensor_le_forty` give `ncard = 40`).

The forty values `dim T_{ord40 i}` are available **cheaply** from the **Klimyk formula**, and the
only missing input is:

> **(WCF-c)** `A_ρ Mtab(e, ·) = A_{e+ρ}` for every `e ∈ the40`, i.e. `WSum (Mnu e) = altLP_{e+ρ}`,
> equivalently `ch L(e) = A_{e+ρ}/A_ρ`.

Given (WCF-c), `A_ρ ch T = A_ρ mfun² = (A_ρ mfun)·mfun = A_{λ+ρ}·mfun` (WCF for `V` is
`Submission.E8WCFV.WCF_V`, proved) becomes
`Σ_e b_e A_{e+ρ} = A_{λ+ρ}·mfun`; taking the coefficient of `e^{ν+ρ}` (for `ν` dominant, where
`ν+ρ` is *strictly* dominant, so only `w = 1` contributes to the left side) gives the **Klimyk
formula**

  `b_ν = Σ_{M ∈ WG} det(M) · mfun(ν + ρ - M(λ+ρ))`   for `ν ∈ the40`,

whose summands are supported on `qq ≤ 10` and therefore truncate to the certified ball of radius
`4` (Session 25: 94 terms per `ν`); this is an entirely finite, `decide`-able computation, and its
values are the `ccv` of `E8Extract` (Session 27 validated this numerically, sum `155`).

Route to (WCF-c): the **Verma Euler characteristic**
`m_e' := Σ_{M ∈ WG} det(M)·chFun(V_{M·e})`, where `V_ν` is the Verma module `M(ν) = U(e₈)/J(ν)`
— already available as `Submission.E8Weights.M (fun i => ν i)` for an **arbitrary** weight, with
`act`, `lieRingModule`, `lieModule`, `rho`, `positive_annihilates`, `diagonal_acts`, `cyclic`
all proved generically in `lam` (`Submission/VermaNonzero.lean`) and `M_nontrivial`
(`v ≠ 0`), `endM_Omega_of_cyclic` (`Ω = casOf ν·1`, no finiteness needed).  Then

1. **(a),(b)** (top value, support) — from the support bound of a cyclic primitive module and
   `htOf (M·e - e) ≥ 0`; **(d)** the Freudenthal recursion — the *sum* of the individual Verma
   recursions, whose left coefficients agree by `E8Kostant.casOf_dotact`
   (`casOf (w·x) = casOf x`) — this needs `freudenthal_recursion` for a module with
   **finite-dimensional weight spaces** (the Verma module is infinite-dimensional); the honest
   proof is via `Submission/E8PBW.lean`, which spans `U(e₈)` by sorted monomials
   `f^a h^b e^c`, hence `Wt (M := M ν) μ` is spanned by the **finitely many** word vectors
   `f_a·v` of weight `μ`, and the top weight space is `ℂ v`.  (Mechanical generalisation of the
   `[Module.Finite ℂ M]` variable of `E8FreudenthalGen` to a per-weight hypothesis.)
2. **(c)** `W`-invariance of `m_e'`.  Two ways:
   * via `A_ρ m_e' = A_{e+ρ}`: applying `w ∈ W` to `A_ρ·chFun V_ν = e^{ν+ρ}` gives
     `A_ρ·(w·chFun V_ν) = ε(w)·w(e^{ν+ρ})` so for the invariant combination `m_e'` one gets
     `A_ρ(m_e' ∘ w) = A_ρ m_e'` for all `w`, and then **`E8NoKernel.eq_of_WSum_eq`** gives
     `m_e' ∘ w = m_e'`;
   * both ways need the **Verma character identity**
       **(VC)** `A_ρ chFun V_ν = e^{ν+ρ}`   (`⟺ Σ_{M∈WG} det(M)·chFun V_ν(η - Mρ) = [η = ν+ρ]`),
     which in turn is equivalent to the classical **Kostant identification**
     `chFun V_ν(μ) = KostantP(ν-μ)` together with the **combinatorial identity**
       **(K⁻¹)** `Σ_{s ⊆ Φ⁺} (-1)^{|s|}·KostantP(γ - Σ_{α∈s}α) = [γ = 0]`
     ("the Kostant series is the inverse of the Weyl denominator").  **(K⁻¹) has a clean
     telescoping proof**: over the list `α₁,…,α₁₂₀` of positive roots, `K_n(γ) := #{multisets
     from α₁..α_n summing to γ}` satisfies `K_{n+1}(γ) - K_{n+1}(γ-α_{n+1}) = K_n(γ)`
     (split off the last root), i.e. `(1 - e^{-α_{n+1}})·K_{n+1} = K_n`, and the product of the
     `(1-e^{-α})` telescopes to `1`.  (VC) also follows from `dim M(ν)_μ = dim U(n⁻)_{μ-ν}`
     plus the classical `dim U(n⁻)_γ = KostantP γ` — the PBW basis of `n⁻` indexed by multisets
     of positive roots, which is NOT in Mathlib.

#### 4. The alternative (no new mathematics, but a big computation)

`dim T_{ord40 i} = Σ_{ξ ∈ E8Iso.L} mfun ξ · mfun(ord40 i - ξ)`
(`E8TensorChar.finrank_TLwt_eq_sum`), with `mfun = mnorm ∘ qq` (`E8Support.mfun_eq_mnorm`) and
`E8Iso.L = {v : qq v ≤ 10}` (`E8WinTensor`), `56881` points.  This is `40 × 56881 ≈ 2.3·10⁶`
terms; measured costs (Session 32): `decide` over the unfolded `qq` ≈ 0.9 s/term, hand-unrolled
≈ 0.09 s/term ⟹ **≈ 57 h of kernel**: infeasible in the present form.  It becomes feasible only
with (i) a literal, *certified-complete* list of the `56881` points (the `56881 = 1+240+2160+6720
+17520+30240` norm distribution and the orbit structure `W·the7` are already known in the
commons: `e8_lattice_count`), and (ii) a reorganisation of the sum that avoids recomputing `qq`
per term.  Route §3 is the mathematical one and is preferred.

#### 5. What exactly remains

1. `freudenthal_recursion` for per-weight-finite modules; the Verma module `M(ν)` instances +
   weight-space finiteness + top weight space + support (mechanical, via `E8PBW`).
2. (VC) / (K⁻¹) — the missing combinatorial chapter (the telescoping proof of (K⁻¹) is elementary;
   the Kostant identification needs PBW with an ordered basis of `n⁻`).
3. `A_ρ Mtab(e,·) = A_{e+ρ}` for the forty `e`, then the Klimyk extraction `b_ν = ccv_ν`.
4. The isotypic plumbing `ch T = Σ_e b_e Mtab(e, domIdx ·)` (Mathlib `IsSemisimpleModule` +
   `IsIsotypicOfType` + `E8ConstChar`) and the unitriangularity argument.
5. Assembly (unchanged): `V := V ⧸ N` maximal, `finrank = 779247`, irreducible, `ncard = 40`.


#### 6. ⭐ ASSETS DISCOVERED IN THE SHARED COMMONS (checked this session) — the missing chapters mostly EXIST

The commons is far ahead of what `Submission.lean` imports.  In particular:

* **Poincaré–Birkhoff–Witt is PROVED for an arbitrary Lie algebra over a field of characteristic
  zero with an ordered basis**: `Commons.Algebra.Lie.PBW.standardMonomial_basis` (file
  `Submission/Commons/Algebra/Lie/PBW/standardMonomial_basis.lean`; spanning:
  `standardMonomial_spanning`, independence: `standardMonomial_linearIndependent`, plus
  `filtration_eq_span_sorted` for the length filtration).  ⟹ for `n⁻ ⊂ e₈` with an ordered basis
  consisting of **root vectors** (the commons has `e8_rootVector_card`,
  `e8_root_weightSpace_finrank_eq_one` — the root spaces are one-dimensional — and
  `exists_finset_e8_roots`), the PBW monomials of weight `γ` are in bijection with the *multisets*
  of positive roots summing to `γ`, so `dim U(n⁻)_γ = KostantP γ` is in reach **without new
  theory**.
* **The triangular decomposition** `e₈ = h ⊕ n⁺ ⊕ n⁻`: `Commons.Algebra.Lie.SerreConstruction.
  e8_eq_sup_cartan_positive_negative` (+ `e8_W_le_Psub`, `e8_W_le_Msub`, `borel_side_span_top`,
  `e8_weightSpace_iSup_eq_top`), together with `e8W_zero_eq_span_SerreH` (the Cartan is spanned by
  the `Hᵢ`) — these give `U(e₈) = U(n⁻) ⊕ (U n⁺ + U h)`-type statements and hence
  `M(ν) ≅ U(n⁻)` as weight-graded vector spaces (the identification needed for
  `chFun V_ν(μ) = KostantP(ν-μ)`).
* the Weyl denominator formula in coefficient form: `E8_weyl_denom` (`C (ρ-wρ) = ε(w)`) and
  `E8_weyl_denom_support` (`C γ ≠ 0 ⟹ ∃ L, wact L rhoZ = rhoZ - γ`), `C` being the coefficient
  functional of `∏_{α>0}(1-e^{-α})`.
  ⟹ the two remaining gaps of §3 (the Kostant identification and (K⁻¹)) are *library-assembly*
  work rather than new mathematics.

**Delegated this session** (child agent, in flight): the commons lemma
`Commons.LinearAlgebra.Matrix.Cartan.E8_denom_mul_Kostant`, i.e. the coefficient form of
`(∏_{α>0}(1-e^{-α}))·(∏_{α>0}(1-e^{-α})^{-1}) = 1` (statement + the telescoping proof recipe in
the request).  This is (K⁻¹) of §3.

#### 7. Refinements to `Submission/E8NoKernel.lean` (this session, final form)

* `WSum_eq_zero_of_bounded (f) (N) (hsupp : f ν ≠ 0 → htOf ν ≤ N) (h0 : WSum f ≡ 0) : f = 0`
  (the proof only needs an **upper** bound on `htOf` over the support — the set of heights in the
  support is a nonempty subset of `ℤ` bounded above, hence has a maximum; this is what makes it
  applicable to supports contained in a *cone-translate* `{ν : ν ⪯ x}`, where `htOf ν ≤ htOf x`).
* `eq_of_WSum_eq (Nf Ng) (hf) (hg) (h : WSum f = WSum g) : f = g`.
* `ht_rho_sub_ap_pos` — `0 < htOf (ρ - w ρ)` for `w ≠ 1`.
* **Remark for the next session (the W-invariance criterion).**  To deduce *`W`-invariance* of `f`
  from `WSum f = altLP_{μ}` one argues `WSum (f ∘ w) = ε(w)·(WSum f) ∘ w = ε(w)·ε(w)·altLP_μ`
  (the second factor by the anti-invariance of the alternant), hence `WSum (f ∘ w) = WSum f` and
  `f ∘ w = f` by `eq_of_WSum_eq`.  Two technical points must be respected:
  1. the support bound of `f ∘ w` is *not* the same as that of `f` in the height formulation:
     `htOf (w ν) = htOf ν + htOf (wν - ν)`, and `wν - ν` can be a *negative* combination
     (e.g. `ν = ρ`, `w = sᵢ`: `sᵢρ - ρ = -αᵢ`).  The right hypothesis is therefore the
     *cone-translate* one (`supp f ⊆ {ν : ν ⪯ x}`), which is `W`-stable in the sense that
     `supp (f ∘ w) ⊆ {ν : ν ⪯ w^{-1} x}` — this is exactly the shape of the supports occurring in
     the WCF argument (`supp chFun V_ν ⊆ ν - Q⁺`);
  2. the identity `WSum (f ∘ w) x = ε(w)·WSum f (w x)` is a `Finset.sum_bij` along
     `M ↦ wactMat L * M`, using `wact L (x - ap M ρ) = wact L x - ap (wactMat L * M) ρ`
     (`Commons...wact_sub'`, `ap_mul`, `wactMat_ap`), `Matrix.det_mul` and `wactMat_det`.

#### 8. ⭐ SESSION 33 (cont.): THE KOSTANT IDENTIFICATION — the one step, begun and delegated

The single mathematical input separating `E8NoKernel` from (WCF-c) of §3 is the **Kostant
identification**

  `chFun V_ν(μ) = KostantP(ν - μ)`   for the Verma module `V_ν = M(ν) = U(e₈)/J(ν)`,

which splits into exactly two library pieces:

* **(B) the negative part of the enveloping algebra** (delegated this session, commons path
  `Algebra/Lie/E8_Msub_weight_finrank`, statement bank in
  `Submission/Work/E8KostantId.lean`): for `γ : Fin 8 → ℤ`,
  `finrank ℂ ↥(wtPartM γ) = KcountP γ`, where
  - `wtPartM γ` is the span of the elements of the subalgebra of `U(e₈)` generated by the
    negative part `Commons.Algebra.Lie.SerreConstruction.Msub` whose `ad (SerreH i)`-weight is `-γ`
    (i.e. `ι (SerreH i) * u - u * ι (SerreH i) = -γᵢ • u`), and
  - `KcountP γ = Nat.card {k : ↥E8posRoots.P → ℕ // ∑ α, k α • α = γ}` is the Kostant partition
    function (multisets of positive roots; the `Nat.card` form avoids any height bound).
  Proof plan (in the request): (1) `Msub = ⨆_{α ∈ P} e8W (-α)` with one-dimensional summands
  (`e8_root_weightSpace_finrank_eq_one`, `e8_W_le_Msub`); (2) PBW
  (`Commons.Algebra.Lie.PBW.standardMonomial_basis`) for `Msub` with a basis indexed by `P` and
  injectivity of `U(Msub) → U(e₈)`; (3) the weight of a PBW monomial is minus the sum of its
  roots, so the weight-`(-γ)` part is spanned by the multiset monomials summing to `γ`, and PBW
  makes them independent — giving the count `KcountP γ`.
* **(C) the Weyl denominator × Kostant convolution** (delegated earlier this session, commons path
  `LinearAlgebra/Matrix/Cartan/E8_denom_mul_Kostant`): the coefficient form of
  `(∏_{α>0}(1-e^{-α})) · (∏_{α>0}(1-e^{-α})^{-1}) = 1`, i.e. `Σ_{T ⊆ Φ⁺} (-1)^{|T|} K(γ - Σ_Tα) =
  [γ = 0]`, with the telescoping proof recipe.

Assembly of (B) and (C) into the Verma character identity:
`M(ν) ≅ U(n⁻)` as weight-graded vector spaces (from the triangular decomposition
`e8_eq_sup_cartan_positive_negative` plus the PBW basis of `U(e₈)` in a weight-compatible order:
the `f`-monomials of `U(n⁻)` inject into `U(e₈)`, and `U(e₈) = U(n⁻) ⊕ (n⁺U + hU)`), so (B)
gives `chFun V_ν(μ) = KostantP(ν-μ)`; then, in the group algebra of the weight lattice,
`A_ρ · chFun V_ν = e^{ν+ρ} · (∏(1-e^{-α}))(Σ_γ K(γ)e^{-γ}) = e^{ν+ρ}` by (C) and the Weyl
denominator formula `E8_weyl_denom` (`C(ρ-wρ) = ε(w)`), giving **(VC)** of §3.  With **(VC)**,
the `A_ρ`-argument (now backed by `Submission/E8NoKernel.eq_of_WSum_eq`) gives the `W`-invariance
(c) of the Verma Euler characteristic `m_e' = Σ_M det(M)·chFun V_{M·e}`, hence `m_e' = Mtab(e,·)`
by `E8Kostant.eq_of_MnuQ`, hence **(WCF-c)** `A_ρ Mtab(e,·) = A_{e+ρ}`, and finally the Klimyk
extraction `b_ν = Σ_{M ∈ WG} det(M)·mfun(ν+ρ-M(λ+ρ))` (a `decide` over the certified ball of radius
`4`, = `ccv_ν ≥ 1`), hence `ncard = 40`.

⚠️ Note on the commons: importing *both* `SerreConstruction/e8_zero_weightSpace_finrank` and
`SerreConstruction/e8_simple_root_weightSpace_finrank` in one file fails ("environment already
contains `L8`") — the two files duplicate the Serre data.  Requests must avoid that pair.

#### 9. ⭐ SESSION 33 (cont. 2): (C) HAS LANDED — the routing's first link is closed

**PROVED and committed to the commons** (child `L175`):

> `Commons.LinearAlgebra.Matrix.Cartan.E8_denom_mul_Kostant`
> (`Submission/Commons/LinearAlgebra/Matrix/Cartan/E8_denom_mul_Kostant.lean`,
> module `Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_denom_mul_Kostant`):
> ```
> theorem E8_denom_mul_Kostant (γ : Fin 8 → ℤ) :
>     (∑ T ∈ E8posRoots.P.powerset, (-1 : ℤ) ^ T.card *
>       ((Fintype.piFinset (fun _ : ↥E8posRoots.P =>
>           Finset.range ((E8NormTwo.e8ht γ).toNat + 1))).filter
>         (fun f => ∑ α : ↥E8posRoots.P, f α • (α : Fin 8 → ℤ) = γ - ∑ α ∈ T, α)).card)
>       = if γ = 0 then 1 else 0
>   ```
> — exactly (C) of §8 (the coefficient form of `(∏_{α>0}(1-e^{-α}))·(∏_{α>0}(1-e^{-α})^{-1}) = 1`;
> `import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_denom_mul_Kostant`).

The child's proof is *stronger* than the telescoping recipe I supplied, and is worth knowing about:
it proves the more general `E8Kostant.Srep_main` for an **arbitrary finite family of vectors whose
heights are `≥ 1`** (any `M`, additive height `ht : M →+ ℤ`), by turning the double sum into the
count of pairs `(T, f)` with `Σ_i f_i v_i + Σ_{α∈T} α = γ`, substituting `g = f + 1_T` and
evaluating the Möbius sums `Σ_{Z ⊆ T ⊆ Z ∪ S} (-1)^{|T|}` (which vanish unless the "free" set
`S = ∅`); the height bound then kills the leftover terms.  Useful general-purpose machinery:
`E8Kostant.Srep_finset` (the finset form), `E8Kostant.KK`, `e8htHom : (Fin 8 → ℤ) →+ ℤ` (the
height as an *additive* homomorphism — reusable).

**Next link of the routing (the W-sum form).**  Combining (C) with the Weyl denominator formula —
`E8_weyl_denom` (`Σ_{T ⊆ s} (if Σ_{α∈T}α = ρ - wact L ρ then (-1)^{|T|} else 0) = (-1)^{L.length}`,
for any `s` satisfying the positive-root characterisation, in particular `E8posRoots.P`) and
`E8_weyl_denom_support` — gives, by regrouping the `T`-sum by the value of `Σ_{α∈T}α`,

  **(K-inv)**  `∀ η, Σ_{M ∈ WG} det(M) · KostantP (ap M ρ - η) = if η = ρ then 1 else 0`,

i.e. "the Kostant series `Σ_δ K(δ)e^{-δ}` is the inverse of `A_ρ`".  This is the form actually
consumed by the Verma character identity (VC): with (B) giving `chFun V_ν(μ) = KostantP(ν-μ)`, the
identity `Σ_M det(M)·chM(ν)(η - Mρ) = [η = ν+ρ]` is exactly (K-inv) at `η = ν+ρ`.

⚠️ **Where to prove (K-inv)**: `WG`/`ap`/`rhoV` are objects of `Submission/WCFSetup.lean`, *not* of
the commons, so (K-inv) must be proved **in `Submission/`** (e.g. a new
`Submission/E8KostantConv.lean`), not delegated to the commons.  Its proof is a
fiber-regrouping of the (C) sum: group `T ⊆ E8posRoots.P` by `Σ_{α∈T}α`, note that the fibers with
`Σα ∉ {ρ - wρ}` contribute `0` (their total coefficient is `0` by `E8_weyl_denom_support`) and that
the fiber at `ρ - wρ` contributes `(-1)^{|L|} = det(wactMat L)` (by `E8_weyl_denom`), then
re-index over `WG` (`mem_WG`, `wactMat_ap`, `ap`).  Elementary but index-heavy; it needs no new
mathematics.
-/

/-!
#### 10. ⭐ SESSION 34: (K-inv) PROVED, and the Weyl character formula for the constituents REDUCED to ONE combinatorial identity

**PROVED this session** (both files are imported by `Submission.lean`, sorry-free):

* **`Submission/E8KostantConv.lean`** — **(K-inv)**, the "Kostant series inverts the Weyl
  denominator" identity in W-sum form:
  ```
  theorem E8_weyl_kostant_K (η : Fin 8 → ℤ) :
      (∑ M ∈ WG, (M.det : ℤ) * (KP (ap M rhoV - η) : ℤ)) = if η = rhoV then 1 else 0
  ```
  where `KP δ = Commons.Algebra.Lie.E8KostantId.KcountP δ` is the Kostant partition function
  (`Nat.card` of the multiset-counting subtype of `↥E8posRoots.P`).  Proof: regroup the
  commons (C)-identity `E8_denom_mul_Kostant` by the value of the root-sum `Σ_{α∈T} α`
  (`Finset.sum_fiberwise_of_maps_to`), use `E8_weyl_denom_support` + `E8_weyl_denom` to evaluate
  the fiber sums (`fiber_C`, `D_filter_eq`, `D_sum_eq`), and reindex over `WG` via `mem_WG`,
  `wactMat_ap` and `inj_delta`.  Also here: `Kbr`, `Kbr_eq_KP` (the truncated count equals the
  honest one), `denom_mul_KP`, `denom_regroup`, `C`, `fiber_C`, `C_rho_sub_wact`, `posCon` facts.

* **`Submission/E8WCFC.lean`** — the `A_ρ`-setup for the Weyl character formula:
  `chV ν μ = KP (ν - μ)` (Verma character), `dot M ν = ap M (ν + ρ) - ρ`, `alt μ x`,
  `euler Λ μ = ∑_{N ∈ WG} det N · chV (dot N Λ) μ` (Euler characteristic of the Verma modules on
  the dot-orbit), and
  * **`WSum_chV`**: `A_ρ · chV ν = δ_{ν+ρ}` (immediate from (K-inv)),
  * **`WSum_euler`**: **`A_ρ · euler Λ = alt (Λ + ρ)`** — i.e. `∑_M det M euler Λ (x - Mρ) =
    ∑_M det M [M(Λ+ρ) = x]`,
  * `alt_ap` (anti-invariance of the alternant), `euler_ht` (support bound: `euler Λ μ ≠ 0 ⟹
    htOf μ ≤ htOf Λ` for `Λ` dominant), `htOf_rhoV`, `htOf_dot`, `KP_posCon`, plus the bridge
    `coords_eq'` (commons `coords` = `E8Character.coords`) and `posCon_dom_sub_wact`.

**The plan is now: identify `Mnu i` with `euler (ord40get i)`** for each of the forty dominant
weights.  Both are functions `(Fin 8 → ℤ) → ℚ`; `Mnu i` (the certified table character) satisfies
hypotheses (a)–(d) of `Submission.E8Character.eq_of_freudenthal` **already proved**
(`MnuQ_top`, `MnuQ_support`, `MnuQ_dc`, `MnuQ_freud`), and for `euler Λ`:

* (a) `euler Λ Λ = 1` — easy (all terms with `N ≠ 1` have `dot N Λ - Λ = ap N (Λ+ρ) - (Λ+ρ)`,
  which is `≠ 0` and not in the cone, so `KP = 0`, using `E8_wact_fixes_strict_dominant` and
  `wactMat_eq_of_rho_eq`);
* (b) `W`-invariance of `euler Λ`, i.e. `euler Λ (ap M μ) = euler Λ μ`.  This follows from
  `WSum_euler` (the difference `euler Λ ∘ ap M - euler Λ` has vanishing Weyl sum) **provided one
  can run the maximality/cone argument**: the support of the difference is contained in
  `{μ : htOf μ ≤ htOf Λ} ∪ {μ : htOf (ap M μ) ≤ htOf Λ}`; in the *cone* order the `N = 1` term of
  `WSum (euler Λ ∘ ap M - euler Λ) (ν + ρ)` is `euler Λ ∘ ap M (ν) - euler Λ (ν)` and all other
  terms sit at `ν + (ρ - Nρ) ⪰ ν`, so a *cone*-maximal point of the support gives a contradiction.
  The clean alternative is the *formal* one (group algebra of the weight lattice, in which
  `euler Λ = A_{Λ+ρ}/A_ρ`, a quotient of two anti-invariant elements), which needs a localization
  of the monoid algebra `P → ℚ`.  **This is one of the two remaining inputs.**
* (b') the **support bound**: for *dominant* `ν` with `euler Λ ν ≠ 0` one has
  `Λ - ν ∈ ℕΦ⁺ ∪ {0}`.  The proof (recorded here) uses (b) and `WSum_euler`:
  `A_ρ euler Λ (ν + ρ) = [ν = Λ]`, and a height-maximal *bad* dominant `ν` would need every
  `euler Λ (ν + ρ - Nρ)` (`N ≠ 1`) to vanish, because `ν + (ρ-Nρ) ⪰ ν` with strictly larger height
  and (by (b)) its `dc`-closure is dominant; but then the `N = 1` term gives `euler Λ ν = 0`, a
  contradiction.  (This argument is elementary and does not need the full Freudenthal theory.)
* (d) the **Freudenthal recursion** for `euler Λ`, which is *linear* in the function: it suffices
  that each `chV ν` satisfies it, i.e. the **combinatorial identity**
  ```
  (qZ (ν+ρ) - qZ (μ+ρ)) · K (ν-μ) = 2 ∑_{α>0} ∑_{k≥1} (brk(μ,α) + 2k) · K (ν-μ-kα)
  ```
  for the Kostant partition function `K` (`brk(μ,α) = Σᵢ μᵢ (A⁻¹α)ᵢ`).  **This is exactly the
  Freudenthal formula for the `E₈` Verma module**; it is `ℚ`-affine in `μ`, and its `μ`-independent
  part is `(2 htOf γ + qZ γ) K γ = 4 ∑_{α>0} ∑_{k≥1} k · K (γ - kα)` (verified numerically for all
  `γ` with `htOf γ ≤ 12`), which is equivalent to the root-system identity
  `∑_{α≠β} ⟪α,β⟫ u_α u_β = 2 ∑_{α>0} (1 - htOf α) u_α` for `u_α = e^{-α}/(1-e^{-α})`.
  **Delegated this session as the commons lemma
  `Commons.LinearAlgebra.Matrix.Cartan.E8_Kostant_freudenthal`
  (`LinearAlgebra/Matrix/Cartan/E8_Kostant_freudenthal`) — this is the single remaining piece of
  new mathematics.**

Note that `chV ν` is by *definition* the weight-multiplicity function of the Verma module
`M(ν)` (`dim M(ν)_μ = KP(ν-μ)` is the commons theorem
`Commons.Algebra.Lie.E8_Msub_weight_finrank` combined with the Kostant identification); the
alternative route to (d) is the per-weight-finiteness generalisation of
`Submission.E8FreudenthalGen.freudenthal_recursion` (whose `StrM`/`TtrM` already carry
`[Module.Finite ℂ ↥(Wt ν)]` as *per-weight* instance arguments) applied to the Verma module.

**Also needed** (mechanical): the variant of `Submission.E8Character.eq_of_freudenthal` in which the
support hypothesis `hb` is required only for *dominant* weights
(`∀ v, Dominant v → m v ≠ 0 → lam - v = 0 ∨ posCon (lam - v)`); its proof is the existing one with
the two uses of `hb` (both at the dominant conjugate `dc v`) adapted — the definition of `dc`,
`dc_dominant` and `dc_sub_posCon` are all that those uses need.  Then (a)–(d) for `euler Λ`
together with (a)–(d) for `Mnu i` give `euler (ord40get i) = MnuQ i`, hence
**`A_ρ · Mnu i = A_{ord40get i + ρ}` ((WCF-c))**.

#### 11. SESSION 34 (cont.): the Freudenthal recursion for the *Verma characters* is PROVED

* **`Commons.LinearAlgebra.Matrix.Cartan.E8_Kostant_freudenthal`** (PROVED, delegated child `L180`):
  ```
  theorem E8_Kostant_freudenthal (ν μ : Fin 8 → ℤ) :
      (qZ (ν+ρ) - qZ (μ+ρ)) * (Kbd (ν-μ) : ℤ)
        = 2 * ∑ α ∈ P, ∑ k ∈ Icc 1 (e8ht (ν-μ)).toNat,
            ((∑ i, μ i * (E8inv.mulVec α) i) + 2 * (k:ℤ)) * (Kbd (ν-μ-k•α) : ℤ)
  ```
  with `Kbd` the height-bounded Kostant count (`Kbd_eq_KcountP`: `Kbd = KcostantId.KcountP = KP`).
  Its proof (see the file docstring) rests on three pieces: the *marking identity*, the *second-order
  identity*, and the `μ`-independent *Casimir-null* part `(⟪δ,δ⟫+2htδ)Kδ = 4∑nK(δ-nβ)`, which the
  child derived from `E8_weyl_denom_support` + the root-system identity
  `Commons.…E8_root_pairing_summation` convolved with `K` (`Commons.Algebra.Lie.E8_Kostant_crux_convolved`).

* **`Submission/E8WCFD.lean`** (sorry-free, imported): converts it to the form used by
  `eq_of_freudenthal`, and proves
  * `brkP` (`= ⟪·,·⟫`), `brk_eq_brkP` (`brk x j = brkP x (pR j)`), `brkP_add_nsmul`,
  * `card_P`, `pR_mem`, `sum_pR_eq_sum_P` (the `Fin 120` / `↥P` sum conversion),
  * `KP_eq_Kbd`, `Bint_eq_qZ` (`Bint ν = qZ (ν+ρ)`), `Bint_dot'`,
  * **`chV_freudenthal`**: `(Bint ν - Bint μ) * chV ν μ = 2 ∑_j ∑_k brk(μ+kα_j,j) chV ν (μ+kα_j)`
    — **the Freudenthal recursion for the Verma character** (the classical `dim M(ν)_μ = K(ν-μ)`).

**Still to do for (d) for `euler Λ`** (routine, but the `k`-range needs care): `euler Λ = Σ_N ε(N) chV(N·Λ)`,
and `Bint (N·Λ) = Bint Λ` (`Bint_dot'`), so the recursion is inherited; the only subtlety is that the
`k`-range `Icc 1 (htOf (N·Λ - ν)).toNat` of `chV (N·Λ)` differs from the target
`Icc 1 (htOf (Λ - ν)).toNat`.  Since `htOf (N·Λ) ≤ htOf Λ` for `Λ` dominant (`htOf_dot_le`), and
`chV (N·Λ) (ν + kα) = 0` as soon as `htOf (N·Λ - ν) < k·htOf α`, the extra terms vanish and the two
ranges give the same sum (`sum_Icc_eq_of_zero`).

### What remains after SESSION 34 (in order)

1. `euler_freudenthal` (the `k`-range comparison above);
2. `W`-invariance of `euler Λ` ((b), see above — formal route or cone-maximality);
3. `euler Λ Λ = 1` (PROVED: `Submission.E8WCFC.euler_top`) and the dominant-weight-only
   Freudenthal-uniqueness variant;
4. `euler (ord40get i) = MnuQ i` ⟹ **(WCF-c)** `WSum (MnuQ i) x = alt (ord40get i + rhoV) x`;
5. the isotypic plumbing `ch T = ∑_e b_e c_e Mnu e` (from `Submission.E8ConstChar.chFun_eq_Mnu`
   applied to a constituent of each occurring type, plus `IsSemisimpleModule` for `T N`);
6. the **Klimyk extraction** `b_ν = ∑_{M∈WG} det M · mfun (ν + ρ - M(λ+ρ))` — a `decide` over the
   certified ball of radius 4 (`Submission.E8Ball`, `Submission.E8CharCompute`);
7. `b_ν = ccv_ν ≥ 1` (`Submission.E8Extract.ccv_pos`) ⟹ `ncard = 40` with
   `Submission.E8TensorBound.ncard_tensor_le_forty`; then the assembly (unchanged).
## SESSION 36: the support bound for `euler Λ` is PROVED; the extraction reduced to a triangular
## system; and two decisive measurement/negative results

### 1. ⭐ `euler_support` — the support bound — PROVED (`Submission/E8WCFE.lean`)

For a **dominant** `Λ = ord40get i`:

  `euler_support : euler Λ μ ≠ 0 → posCon (Λ - μ)`   (i.e. `μ ⪯ Λ`).

This is the analogue of "the weights of `L(Λ)` lie in `Λ - ℕΦ⁺`" and it is proved **without any
`W`-invariance**: a *single* non-zero summand `chV (N·Λ) μ = K(N(Λ+ρ)-ρ-μ)` already forces
`N(Λ+ρ)-ρ-μ ∈ ℕΦ⁺` (`KP_posCon`), and then

  `Λ - μ = (N(Λ+ρ)-ρ-μ) + (Λ+ρ - N(Λ+ρ))`

is a sum of two cone elements, because `Λ+ρ` is *strictly* dominant so `N(Λ+ρ) ⪯ Λ+ρ`
(`posCon_dom_sub_wact`).  Also proved in the same file:

* `KP_eq_zero_of_htOf_neg`, `chV_eq_zero_of_htOf_neg` — vanishing off the cone;
* `htOf_dot_le`, `Bint_dot_eq` — `htOf (N·Λ) ≤ htOf Λ` and `Bint (N·Λ) = Bint Λ`;
* **`euler_freudenthal`** — the *unreduced* Freudenthal recursion for `euler Λ`, valid at **every**
  weight `ν` (not only at the dominant ones):
  `(Bint Λ - Bint ν)·euler Λ ν = 2 ∑_j ∑_k brk(ν+kα_j,j)·euler Λ (ν+kα_j)`, the sum of the
  Verma recursions `chV_freudenthal (N·Λ) ν` (whose Casimir coefficients agree); the `k`-ranges
  are compared with `chV_dot_range` + `htOf_dot_le` + `chV_eq_zero_of_htOf_neg`.

### 2. ⭐ `Submission/E8MtabUnitri.lean` — the triangular system is solved abstractly

* `Mtab_diag : Mtab i i = 1` (from `Mnu_top`/`Mnu_dom`);
* `Mtab_unitri : Mtab i e ≠ 0 → posCon (Λ i - Λ e)` (the support bound `Mtab_support`);
* `ord40get_inj`, `ord40_ht_nonincreasing` (both `decide`): `ord40` is **non-increasing in
  height** (with the two ties `(1,2)` at 149 and `(21,22)` at 114);
* `ht_lt_of_Mtab_ne`; `system_sum_split`; and
* **`eq_ccv_of_system`**: any `b : Fin 40 → ℤ` satisfying the *same* system as `ccv`
  (`System b`) has `b = ccv`; hence **`pos_of_system : 1 ≤ b i`** for every `i`.

So: **if the weight multiplicities of the tensor square at the forty dominant weights are the
table `mf2v` (i.e. `dim T_{Λ i} = mf2v i`), then every one of the forty types occurs.**

### 3. ⚠️ MEASUREMENT: the direct computation over the ball of radius 10 is INFEASIBLE

* `dimT_ν = ∑_{ξ : qZ ξ ≤ 10} mfun ξ · mfun (ν-ξ) = mf2v` — **verified numerically for all 40 `ν`**
  (`.tmp_lb/e8.py`) with the certified ball (56881 points, the union of the 7 orbits
  `1+240+2160+6720+(240+17280)+30240`, norm distribution confirmed by `e8_lattice_count`).
* Kernel cost of `decide` over a *literal list* (measured): `List ℤ` ≈ **3 ms/element**;
  `List (Fin 8 → ℤ)` with `v 0` ≈ **0.25 s/element**; nested-`ℤ`-tuples ≈ **0.7 s/element**.
  ⟹ the 2.3·10^6-term direct sum (`Fin 8 → ℤ`) costs **≈160 h of kernel**: infeasible.
  A `List ℤ`-reformulation (≈2 h) would require *certifying* the precomputed summands, i.e.
  evaluating `qZ` on 56881 vectors ≈ 4 h, plus a completeness proof for the literal list
  (`List.Nodup` of 56881 `Fin 8 → ℤ` is itself ≈ 10^9 comparisons): **not attempted**.
* The **orbit decomposition** `dimT_ν = Σ_{O} mnorm(qZ_O)·∑_{ξ∈O}mfun(ν-ξ)` together with the
  ball-of-radius-4 truncation of `∑_{w∈W}mfun(ν-wη_O)` is **WRONG for large `η_O` and small `ν`**
  (measured: e.g. `η_O = λ`, `d = 9`: full sum `1451520` vs ball-4 sum `33468`).  The truncation is
  valid only when `ν ⪰ η_O` (then `qZ(η_O - wη_O) ≤ 10` bounds `htOf (ρ-wρ) ≤ 5`, and
  `E8_wact_small_height_length` gives a word of length ≤ 4).

### 4. ⚠️ The `W`-invariance of `euler Λ` — remaining gap, with everything now in place

`euler Λ` satisfies (a) `euler_top`, (b) `euler_support` ✓ NEW, (ii) `euler_ht`, (d)
`euler_freudenthal` ✓ NEW, and the unreduced recursion at *all* weights.  Writing
`h = euler Λ ∘ s_i - euler Λ`, we have `supp h ⊆ (Λ-ℚ⁺) ∪ s_i(Λ-ℚ⁺)` (two cone translates),
`h(s_i x) = -h(x)`, and `WSum h = 0` (i.e. `S * h = 0`, `S = ∏_{α>0}(1-e^{-α})`).  To conclude
`h = 0` it suffices that `supp h` be *bounded above in height* (`E8NoKernel.WSum_eq_zero_of_bounded`),
which is not known because `s_i supp (euler Λ)` is unbounded above (it is only bounded in the
*s_i*-direction).  Two other facts now available: for a dominant `ν`, the *maximum-height* point
of `supp (euler Λ)` is `Λ` itself; and the "singular" points `Bint ν = Bint Λ` are the only ones
where the (unreduced) recursion is vacuous — so the *unreduced-recursion uniqueness* for `euler Λ`
vs `MnuQ` holds at every non-singular weight, leaving exactly the Casimir sphere.

### 4bis. ⭐ NEW (numerical): an explicit pair decomposition and the PRV cover

For **every** one of the forty weights there is an *exact* decomposition

  `Λ d = η d + ζ d` with `η d` a weight of `V` (i.e. `qZ η d ≤ 10`, `η d ∈ ball`) and `ζ d` a
  **dominant** weight of `V` (i.e. `ζ d ∈ the7`).

Explicit witnesses (`.tmp_lb`): `d=0`: `λ+λ`; `d=1`: `(λ-ω₁)+λ`; `d=4`: `ω₂+λ`; `d=8`:
`(2ω₁-ω₈)+λ`; `d=17`: `ω₁+λ`; `d=19`: `(2ω₈-ω₈)+2ω₈ = (-1,0,0,0,0,0,0,3)+ω₁+ω₈`; `d=22`:
`ω₁+ω₂`; `d=33`: `0+λ`; `d=37`: `0+ω₁`; `d=39`: `(-λ)+λ`; etc.  (The full list is in the
scratch script.)

Consequently: if `v_η` is a weight vector of `V` of weight `η d` and `v_ζ` a weight vector of `V`
of weight `ζ d`, then `v_η ⊗ v_ζ ∈ (V⊗V)_{Λ d}` is non-zero, so `(V⊗V)_{Λ d} ≠ 0`; and the *top
weight of the cyclic submodule* it generates is a dominant weight `ν ⪰ Λ d` of the forty.

**The PRV theorem** (`L(ζ + wλ) ⊆ V ⊗ L(ζ)` for `ζ` dominant and `ζ+wλ` dominant) would give,
for `ζ ∈ the7`, `w = 1`: `L(ζ + λ) ⊆ V ⊗ L(ζ)` — but `L(ζ)` is *not* a submodule of the
irreducible `V`, so one must use `V ⊗ V` directly: the classical PRV statement
`L(λ + wλ) ⊆ V ⊗ V` only yields the seven weights `λ + wλ` with `λ+wλ` dominant.
Numerically, the set of *dominant* elements of `{ζ + wλ : ζ ∈ the7, w ∈ W}` (the “PRV cover”)
contains **28 of the forty** weights; the twelve missing ones are

  `ω₁, ω₂, ω₃, ω₄, ω₅, ω₆, ω₇, ω₈, 2ω₇, 2ω₈, ω₂+ω₈, ω₇+ω₈`

(all of `qZ ≤ 30`, i.e. the “low” ones; note `λ` and `0` *are* in the PRV cover).
So the remaining twelve need a different argument (e.g. `Sym² V` / `Λ² V` components, or the
`𝔰𝔩₂`-string structure), or one uses the exact computation `dim T_{Λ d} = mf2v d`.

### 4ter. The exact remaining gap, stated precisely

`Submission.E8Multiplicity.mfun_eq_mul` (pre-existing) gives `dim (Lwt N ξ) = mfun ξ` for every
weight, and `Submission.E8TensorChar.finrank_TLwt_eq_sum` gives

  `dim (T N)_ν = ∑_{ξ : qZ ξ ≤ 10} mfun ξ · mfun (ν-ξ)`   (`T N = (V⧸N) ⊗ (V⧸N)`).

Together with `Submission.E8TensorBound.compData` (an isotypic component `c` of `T N` is detected
by the dominant top weight `ν_c ∈ the40` of any of its constituents, and `compData_inj` says
`c ↦ ν_c` is injective) and `Submission.E8ConstChar.chFun_eq_Mnu` (a constituent with top weight
`Λ e` has character `c · MnuQ e`), the *only* missing input for `ncard = 40` is:

  **(GAP)** `dim (T N)_{Λ d} = mf2v d` for all `d : Fin 40`, i.e. the table `mf2v` of
  `Submission.E8Extract` (verified in Python to equal the ball sum above for all forty `d`).

Given (GAP), the isotypic decomposition `ch T = ∑_e b_e MnuQ e` with `b_e = ∑_{c : ν_c = Λ e} m_c c_c`
gives the `System` of `Submission/E8MtabUnitri.lean`, whose unique solution is `ccv` with
`ccv e ≥ 1`: hence every `b_e ≥ 1`, every one of the forty types occurs, and
`ncard = 40` follows from `ncard_tensor_le_forty`.

*Proved* is the triangle: `pos_of_system : (System b → 1 ≤ b i)`.

### 4quater. The supp-bound: reduced, and the crux it exposes

`Submission/E8SuppBound.lean` (sorry-free, imported) proves the *reduction*:

* `htOf_sref : htOf (sᵢ v) = htOf v - v i`;
* **`supp_smul_s_i_bounded`**: if the *string bound* `∀ μ ∈ supp (euler Λ), -C ≤ μ i` holds, then
  `supp (euler Λ ∘ sᵢ) ⊆ {htOf ≤ htOf Λ + C}`;
* **`supp_sub_bounded`**: the same for `euler Λ ∘ sᵢ - euler Λ`.

⚠️ But the string bound is itself the crux, and here is why it is *not* an independent step:

* `supp (euler Λ) ⊆ Λ - ℕΦ⁺` (`euler_support`) is a *cone translate*, hence unbounded below; the
  only missing half of a *bounded* support is exactly the `αᵢ`-coordinate bound.
* For the *true* character `ch L(Λ)` the string bound `μ i ≥ -Λ i` is the standard statement that
  the `αᵢ`-string through a weight of `L(Λ)` has length `≤ Λ i + 1`; its proof uses that the
  `𝔰𝔩₂`-module generated by `v_μ` is finite-dimensional, which is exactly the
  finite-dimensionality of `L(Λ)` — i.e. it is *equivalent* to `euler Λ` being a genuine (finite
  support) character.
* Formally: any height bound from below for `supp (euler Λ)` would give the `αᵢ`-bound, and
  conversely `supp (euler Λ)` bounded above *and* below is equivalent to `euler Λ = ch L(Λ)`
  (`A_ρ euler Λ = A_{Λ+ρ}` + injectivity of `A_ρ` on bounded supports = `E8NoKernel`).

So the `W`-invariance route and the "supp-bound first" route are the *same* gap.  What is still
true and useful: `WSum (euler Λ ∘ sᵢ) = WSum (euler Λ)`; `h := euler Λ ∘ sᵢ - euler Λ` is
`sᵢ`-anti-invariant with `supp h ⊆ (Λ-ℚ⁺) ∪ sᵢ(Λ-ℚ⁺)`; and `S * h = 0` with
`S = ∏_{α>0}(1-e^{-α})`, i.e. `h` is a sum of `↓α`-periodic functions.

### 4quinquies. The PRV route, opened (`Submission/E8PRV.lean`)

Proved (sorry-free, imported):

* `eRoot_smul_vbar'` — the highest weight vector `vbar` of `V ⧸ N` is killed by every positive root
  vector (`eRoot_smul_vbar`);
* **`deriv_tmul_vbar`** — hence `x ↦ x ⊗ vbar` is `𝔫⁺`-equivariant:
  `deriv (eRoot k) (a ⊗ vbar) = (ι (eRoot k) • a) ⊗ vbar`;
* `tmul_vbar_mem_TLwt` — `a ∈ Lwt N η → a ⊗ vbar ∈ TLwt N (η + λ)`;
* `tmul_vbar_ne_zero` — `a ≠ 0 → a ⊗ vbar ≠ 0` (from the new commons lemma
  `Commons.LinearAlgebra.TensorProduct.tmul_ne_zero`);
* **`exists_primitive_in_cyclic`** — for every non-zero `a ∈ Lwt N η`, the `U`-cyclic submodule
  generated by `a ⊗ vbar` contains a non-zero primitive vector whose weight `ν` lies in `the40`.

**The remaining PRV content** (not proved): that this weight `ν` equals the dominant conjugate
`dc (η + λ)`.  Everything else in the PRV package is now in place.  Note the obstructing
structural facts: the only primitive vector of `V ⧸ N` is `vbar` itself (because `V⧸N` is
irreducible with top weight `λ`), so `a ⊗ vbar` is primitive only for `a = vbar` (giving `d = 0`);
and `weight_support_of_primitive` cannot be applied with the generator `a ⊗ vbar` (it is not
primitive).  What *is* provable unconditionally is the existence of a primitive of some weight in
`the40` inside the cyclic submodule, which is what `exists_primitive_in_cyclic` records.

For the extraction one needs the *map* `d ↦ ν d` to be surjective onto `the40`; the numerical
witness `Λ d = η d + λ` with `η d ∈ ball` for all forty `d` (recorded in §4bis) shows that the
*expected* primitive has weight exactly `Λ d`, and its cyclicity statement is precisely the PRV
content that is still missing.

### 4sexies. The `2λ`-family and the exact shape of the remaining PRV step

`Submission/E8PRV.lean` additionally proves the `2λ`-family, which is the model case:

* `deriv_eRoot_tmul_vbar_vbar` — **`vbar ⊗ vbar` is primitive** (both factors are killed by the
  raising operators, so `deriv (eRoot k) (vbar ⊗ vbar) = 0`);
* `deriv_h_tmul_vbar_vbar` — `vbar ⊗ vbar` has weight `2λ`;
* `tmul_vbar_vbar_mem_TLwt` — `vbar ⊗ vbar ∈ TLwt N (2 • λ)`.

Why this case works and the general one does not: for `η = λ` the generator `x = vbar` is itself
primitive, so `weight_support_of_primitive` applies *with the generator* `vbar ⊗ vbar` and gives
`ν ⪰ 2λ` directly, together with `2λ ⪰ ν` from `posCon (2•λ - ν)` (`posCon_of_mem_TLwt`), hence
`ν = 2λ`.  For `η ≠ λ` the generator `a ⊗ vbar` is **not** primitive (indeed `(ι (SerreE i))·(a⊗vbar)
= ((ι (SerreE i))·a) ⊗ vbar ≠ 0` unless `a = vbar`, by `deriv_tmul_vbar` and injectivity), so:

1. `weight_support_of_primitive` **cannot** be applied to it — this is the formal obstruction to
   reading off `ν ⪰ η + λ`;
2. the only primitive vector of `V ⧸ N` is `vbar` (irreducibility), so no choice of generator fixes
   this;
3. what survives is only `exists_primitive_in_cyclic`, which gives *some* `ν ∈ the40` for the
   cyclic submodule, not the identification `ν = dc (η + λ)`.

The standard proof of PRV (which is what remains) uses a **splitting argument through the dual
module**: the composition
`L(μ) → L(λ)^* ⊗ L(λ) ⊗ L(μ) → L(λ)^* ⊗ L(wλ+μ)`
is `U`-linear out of the irreducible `L(μ)`, hence injective, and is non-zero by an explicit
matrix-coefficient computation.  Formalising that needs (a) the dual of `V ⧸ N` as a `U`-module,
(b) `U`-linearity of that composition, and (c) the non-vanishing of the matrix coefficient
`⟨v^*_{wλ}, u v_λ⟩` for a suitable `u`.  (a)–(c) are the concrete sub-goals.

### 5. Files touched this session
* NEW `Submission/E8WCFE.lean` (sorry-free, imported) — support bound + Freudenthal recursion.
* NEW `Submission/E8MtabUnitri.lean` (sorry-free, imported) — the triangular system.
* `Submission.lean`: imports + this roadmap section.
* Scratch: `.tmp_lb/{e8.py,cnt.py,lb.py,ball4.py,gen*.py}` (numerics).


-/

/-!
## SESSION 39: ⭐⭐ THE `chT`-RECURSION AND THE FINITE SET `Dset` — the extraction reduced to a
## FINITE, EXPLICIT, PROVABLE linear system (validated numerically end-to-end)

**The target still has its single `sorry`; `lake build Submission` is GREEN (8937 jobs).**
Everything below is analysis + numerics + generated data; new Lean files are NOT yet written.

### 1. ⭐ THE KEY IDENTITY

From `Submission.E8TensorChar.finrank_TLwt_eq_sum` (`chT = mfun * mfun`) together with
`Submission.E8WCFV.WCF_V` (`WSum mfun = altLP(λ+ρ)`, i.e. `A_ρ · mfun = A_{λ+ρ}`) one gets, for
**every** `x`,

  **(TRACE-D)**  `Σ_{M ∈ WG} det(M) · chT(x - Mρ)  =  Σ_{M ∈ WG} det(M) · mfun(x - M(λ+ρ))`.

Indeed `chT(x-Mρ) = Σ_{ξ ∈ E8Iso.L} mfun ξ · mfun(x-Mρ-ξ)`, and (WCF-V)
`Σ_M det M mfun(y - Mρ) = altLP(λ+ρ)(y) = Σ_M det M [M(λ+ρ) = y]`; swapping the finite sums gives
the right-hand side.  **This identity is provable with the existing assets** (it is the
associativity of the convolution `A_ρ * (mfun * mfun) = (A_ρ * mfun) * mfun`).

At `x = Λ i + ρ = ord40get i + ρ` the term `M = 1` of the left-hand side is exactly `C_i := chT(Λ i)`
and the right-hand side is a **computable** number `K_i`, so

  `C_i  =  K_i  −  Σ_{M ∈ WG, M ≠ 1} det(M) · chT(Λ i + ρ - Mρ)`       (★)

### 2. ⭐ THE TRUNCATION: `Mρ = ρ - γ` with `D := coords γ = coords(ρ - Mρ) ∈ Dset`

`chT(μ) ≠ 0` forces `μ ∈ L + L` (`L = {qZ ≤ 10}`), hence `qZ μ ≤ 40`.  With `Mρ = ρ - γ`,
`γ = ρ - Mρ ∈ ℚ⁺`, `D := coords γ ∈ ℕ⁸`, we have `qZ(ρ - γ) = 620` (because `Mρ ∈ Wρ`), which is
equivalent to the **light-like condition**

  `qZ D  =  2 · Σ D_i`   (because `qZ(ρ-γ) = 620 − 2 htOf γ + qZ γ` and `htOf γ = Σ D_i`),

and `qZ D ≤ qZ(Λ i + γ) ≤ 40`, hence `Σ D_i ≤ 20`.  Therefore every `M ≠ 1` that contributes to (★)
satisfies `D = coords(ρ-Mρ) ∈ Dset`, where

  **`Dset  :=  { D ∈ ℕ⁸  :  Σ D_i ≤ 20,  qZ D = 2 Σ D_i,  dc(ρ - γ_D) = ρ } ,  γ_D = E8 · D`
  (i.e. `coords γ_D = D`)**

and `dc(ρ - γ_D) = ρ` is equivalent to `ρ - γ_D ∈ Wρ`, i.e. to the existence of `M ∈ WG` with
`Mρ = ρ - γ_D` (whose sign `det M` equals `(-1)^{k}` where `k` is the number of reflections used by
the `dc`-algorithm).  **`|Dset| = 10574`** (the intermediate set `{ΣD ≤ 20, qZ D = 2ΣD}` has 35024
elements), and `D = 0` corresponds to `M = 1`.  The `htOf`-distribution of `Dset` is
`0:1, 1:8, 2:21, 3:35, 4:70, 5:98, 6:130, 7:174, 8:247, 9:271, 10:377, 11:428, 12:541, 13:592,
14:734, 15:760, 16:982, 17:1038, 18:1209, 19:1288, 20:1570`.

So (★) becomes the **finite explicit system**

  `C_i  =  K_i  −  Σ_{D ∈ Dset, D ≠ 0} ε(D) · chT(Λ i + γ_D)`        (★★)

with `ε(D) = det M_D ∈ {±1}` precomputable.  Writing `chT(Λ i + γ_D) = Σ_j C_j·[dc(Λ i + γ_D) = Λ j]`
this is a linear system in `C`; the coefficient table
`Dc[i][j] := Σ_{D: dc(Λ i + γ_D) = Λ j} ε(D)` was computed (`.tmp_lb/ball_data/coeff.json`) and is
**strictly triangular** (`Dc[i][j] ≠ 0 ⟹ j < i`, since `htOf(Λ j) ≥ htOf(Λ i + γ_D) > htOf(Λ i)`).

### 3. ⭐ NUMERICAL VALIDATION (exact, `.tmp_lb/ball_data/rec6.py`, `.tmp_lb/ball_data/Dset.py`)

* `K_i` computed over the **certified ball of radius 4** (`Submission.E8Ball.e8ball`, 450 entries):
  `mfun(Λ i + ρ - M(λ+ρ)) = 0` unless `ℓ(M) ≤ 4`, because `mfun(γ) ≠ 0 ⟹ htOf γ ≤ 2` and
  `htOf(Λ i + ρ - M(λ+ρ)) = htOf Λ i + 622 - htOf(M(λ+ρ))`, while
  `htOf((λ+ρ) - M(λ+ρ)) ≥ ℓ(M)`.  (This is the only place where the ball of radius 4 is used, and it
  is the *same* reduction as `E8WCFV.WCF_V`.)
* With `C = mf2v` (`Submission.E8Extract.mf2v`), the equation (★) was verified **exactly for all
  forty `i`** (0 mismatches) using `Dset` and the ball-4 `K_i`.
* `chT(μ)` in that computation was evaluated as `mf2v j` where `Λ j = dc(μ)`, else `0`.
* The forty values `mf2v` also satisfy `mf2v i = Σ_d ccv d · Mtab d i` (`E8Extract.ccv_system`)
  with `ccv d ≥ 1`, so the triangular system (★★) + `pos_of_system` give `C_i = mf2v i`.

### 4. THE PROOF PLAN (4 steps, all finite)

1. **(TRACE-D)** as a Lean identity, plus the ball-4 truncation of the `mfun`-side giving `K_i` as
   an explicit 450-term sum.
2. The truncation of the `chT`-side to `Dset`: for `M ∈ WG` with
   `Σ coords(ρ-Mρ)_i ≤ 20` the associate `D` lies in `Dset`; for `Σ D_i > 20` the term vanishes
   because `qZ(Λ i + γ_D) ≥ qZ γ_D = 2ΣD_i > 40` while `chT(μ) ≠ 0 ⟹ qZ μ ≤ 40`.
   (Careful: `chT(μ) ≠ 0 ⟹ μ ∈ L+L ⟹ qZ μ ≤ 40` is the *only* usable condition here; the
   *cone* condition `posCon(2λ - μ)` alone gives no truncation at all — see §6.)
3. The identification `chT(Λ i + γ_D) = Σ_j C_j [dc(Λ i + γ_D) = Λ j]` using
   `Submission.E8WinTensor` (`chT` is `W`-invariant) and `E8TensorBound.posCon_of_mem_TLwt`
   (`chT(μ) ≠ 0 ⟹ posCon(2λ-μ) ⟹ dc μ ∈ the40`).
   ⚠ **Simplification attempted and REFUTED numerically** (`.`tmp_lb/cheap.py``): replacing the
   `dc`-computation by the cheap test `qZ μ = qZ(Λ j) ⟹ dc μ = Λ j`.  Two obstructions:
   (i) the argument would need `dc μ ⪯ 2λ` from `μ ⪯ 2λ`, which is **false in general** — only
   `dc v ⪰ v` is available (`E8Character.dc_sub_posCon`), and `dc(2λ-3α₁) = 2λ+α₁ ≻ 2λ`;
   (ii) **the forty weights `ord40` do NOT have distinct `qZ`** (e.g. `qZ = 36` and `qZ = 40` each
   occur twice), so the cheap test is ambiguous and gives 49366 mismatches.
   **Cheap filters that do work**: the *cone* test `posCon(2λ - μ)` (i.e. `D ≤ coords(2λ-Λ i)`,
   valid because `chT(μ) ≠ 0 ⟹ μ ∈ L+L ⟹ qZ μ ≤ 40` and… the cone bound gives vanishing), and the
   *necessary* test `qZ μ ∈ {qZ(Λ j)}`.  After both, the candidate pairs `(i, D)` number **58974**
   (of which 42838 are non-zero); the per-`i` counts are
   `[0,1,1,3,22,11,31,68,22,85,91,172,36,116,221,201,329,303,463,89,298,472,687,650,1070,802,1124,
   1533,1681,2175,1146,1861,2678,3022,4337,3820,4860,6291,7525,10573]`.
4. The numerical verification that `mf2v` satisfies (★★) and triangularity
   (`Dc[i][j] ≠ 0 ⟹ j < i`) to conclude `C = mf2v`, then `pos_of_system` ⟹ `ncard = 40`, plus the
   isotypic plumbing `ch T = Σ_e b_e MnuQ e` (`E8ConstChar.chFun_eq_Mnu` + semisimplicity) and the
   final assembly (unchanged).

### 5. COST MEASUREMENTS AND ENVIRONMENT (important for the next session)

* The machine is **heavily oversubscribed** (`load average ≈ 29`); a `lake build` of a file whose
  extra content is a single 10574-term `decide` did **not** finish within 41 minutes of wall time.
  Prefer *small* targets; expect everything big to be slow.
* **Kernel arithmetic is slow, and `Nat`/`Int` literals are reduced unarily**: `decide` on
  `(List.range 20000).foldl (fun a b => a+b) 0 = 199990000` takes ≈ 5 s of CPU, i.e. ≈ 4·10³
  kernel steps per second in this environment.  Any `decide` needing more than ≈10⁶ steps is
  impractical; 10⁷ is borderline (≈1 h).  **Therefore the `dc`-classification of the 58974
  candidate pairs (≈ 6·10⁴ × ≈3·10³ steps ≈ 2·10⁸ steps) is NOT feasible by kernel computation**,
  and neither is a `decide` that evaluates a 10574-term sum whose per-term cost is a `dc` call.
* `decide` needs `set_option maxRecDepth 100000` whenever long lists are involved ("maximum
  recursion depth has been reached" otherwise).
* ⚠ **`native_decide` is NOT allowed**: `#print axioms` on a `native_decide` proof reports
  `…_native.native_decide.ax_1_1`, i.e. an extra axiom ⟹ the comparator would reject it.
  (Confirmed experimentally, `Submission/Work/Cal3.lean` was deleted afterwards.)
* Elaborating literal data: a `List (Fin 8 → ℤ)` with 30240 entries (726 KB) **times out** at 4·10⁶
  heartbeats; a flat `List ℤ` with 241920 entries likewise; a `List Nat` with 10574 entries
  (mixed-radix encoding) elaborates in ≈1 min (needs `set_option maxRecDepth 100000`, otherwise
  "maximum recursion depth has been reached").
  ⟹ **Encode the ball/`Dset` data as `List Nat` (base-32 mixed radix), not as vectors.**
* `Submission.E8Iso.L` (the commons certified list of `{qZ ≤ 10}`) is **noncomputable**
  (`Set.Finite.toFinset.toList`), so `decide` cannot unfold it at all; the computational route needs
  a *literal* (computable) replacement.
* The certified 450-element ball of radius 4 is available as `Submission.E8Ball.e8ball`
  (imported via `Submission.WCFSetup`).

### 6. NEGATIVE RESULTS OF THIS SESSION (do not retry)

* **The "cone-truncation" set `G := {M ∈ WG : ρ - Mρ ⪯ 2λ}` is huge** (saturation from `1` by the
  moves `M ↦ s_iM` for `(Mρ)_i > 0`, which are exactly the `G`-preserving ones, already has
  ≥ 1.45·10⁶ elements after 20 rounds and keeps growing).  Hence `posCon(2λ - μ)` alone gives **no**
  truncation.
* **The `htOf`-filtered set `F := {M ∈ WG : htOf(ρ - Mρ) ≤ 10}` (1432 elements) is WRONG**: the
  `htOf`-bound for `supp chT` is `htOf ≤ htOf(2λ) = 150` (not 10!), and there are genuine
  contributors with `htOf(ρ - Mρ) = 11` at length 5,6,7.  (The ball of radius 11 — 51116 elements —
  gives the same answer as `Dset`, but its *justification* via a height bound is invalid.)
* **The `D`-box `{D ∈ ℕ⁸ : qZ D ≤ 40}` has 2.4·10⁶ elements** — too big to enumerate; the
  light-like condition `qZ D = 2ΣD` (10574 after the `dc` test, 35024 before) is what makes it
  finite and small.
* `E8Iso.L` is noncomputable (see §5).

### 6bis. ⭐ FEASIBILITY RECIPE FOR THE NEXT SESSION (measured)

Kernel costs measured in this environment (`load ≈ 29`):
* `decide` on 20000 small `Nat` additions: ≈5 s  ⟹ ≈4·10³ kernel steps/s.
* `domIdx` (which runs `dcWE`, the 130-iteration reflection fold): ≈50 ms per call
  (`Submission/Work/Cal4.lean`, deleted afterwards: 100 calls ≈ 5 s of `decide` time).
* A 10574-term `decide` whose summand re-computes `qE (ord40get j)` for all 40 `j`
  (≈2600 steps per term) did **not** finish in 41 min.  ⟹ **precompute the 40 `qE`-values as a
  literal table**; the per-term cost then drops to ≈100 steps.
* A `List Nat` literal of 10574 entries (base-32 encoding) elaborates in ≈1 min with
  `set_option maxRecDepth 100000`; a `List (Fin 8 → ℤ)` of 30240 entries does **not** elaborate.

**Concrete recipe** (the candidate data is already generated in
`.tmp_lb/ball_data/cands.json`: for each `i : Fin 40` a list of triples
`(base-32 encoding of D, sign ε(D), j)` with `j = -1` meaning `chT = 0`, 58870 entries in total,
42838 non-zero):

1. `Submission/E8Cands.lean`: `def cand : Fin 40 → List (Nat × Int × Int) := …` (literal, ≈1 min to
   elaborate), plus `def qtab : List Nat := …` (the forty `qE (ord40get j)`), plus the base-32 decoder
   `dec n i = (n >>> (5*i)) &&& 31` and `gam n i = Σ_j E8 i j * dec n j`.
   The candidate list was built with the **provable** necessary conditions
   `qZ(Λ i + γ_D) ∈ {qZ(Λ j)}` and `posCon(2λ - (Λ i + γ_D))`; any `D` failing either has
   `chT(Λ i + γ_D) = 0` (support of `chT`: `chT(μ) ≠ 0 ⟹ μ ∈ L+L ⟹ qZ μ ≤ 40`, plus
   `posCon(2λ-μ)` from `E8TensorBound.posCon_of_mem_TLwt`).
2. One `decide` verifying the third component of every triple, i.e. that
   `(domIdx (Λ i + γ_D)).elim (-1) (fun j => j)` agrees with the table — ≈58870 × 50 ms ≈ **50 min**.
3. One `decide` verifying the recursion
   `mf2v i = K_i − Σ_{p ∈ cand i} p.2.1 * (if p.2.2 < 0 then 0 else mf2v p.2.2)` for all `i`, where
   `K_i := Σ_{p ∈ e8ball} (-1)^{p.2.length} * mfun (Λ i + ρ - wact p.2 (λ+ρ))` (450 terms per `i`) —
   ≈ 10 min.  (`domIdx` must be replaced by the *table* from step 2 to keep this cheap.)
4. Then the theory: (TRACE-D), the `Dset`-truncation (`D ∈ Dset` for every contributor; the
   completeness follows from `Σ coords(ρ-Mρ)_i ≤ 20`, `qZ D = 2ΣD` and `dc(ρ-γ_D) = ρ`, all of which
   hold for `D = coords(ρ-Mρ)`), the identification `chT(Λ i+γ_D) = Σ_j C_j[domIdx(Λ i+γ_D) = j]`,
   and triangularity (`htOf(Λ i+γ_D) > htOf(Λ i)`).

### 7. DATA LEFT ON DISK (in `.tmp_lb/ball_data/`)

`Dset.json` (the 10574 `(D, k)` pairs, `D ∈ ℕ⁸`, `k` the reflection count of `dc(ρ-γ_D)`),
`coeff.json` (the triangular coefficient table `Dc[i][j]`), `orb0..6.txt` (the seven literal orbits
of `{qZ ≤ 10}`, sizes 30240, 17280, 240, 6720, 2160, 240, 1 = 56881, with the norms 10,8,8,6,4,2,0),
`cands.json` (the 58870 candidate triples described in §6bis) and the scripts `e8.py`,
`genorbs.py`, `Dset.py`, `rec6.py`, `box3.py`, `cheap.py`, `gen_cands.py`, `gen_F.py`, `rec3.py`.
-/

/-!
## SESSION 42: ⭐⭐⭐ THE `W`-INVARIANCE OF `euler Λ` — THE LONGSTANDING GAP `(c)` — IS CLOSED

**This closes the single remaining structural gap of the extraction.**  New files
`Submission/E8WCFW.lean` and `Submission/E8WCFM.lean` (both sorry-free, both imported here) contain

* `Submission.E8WCFW.WSum_comp_ap` / `WSum_euler_ap` — `A_ρ` does not distinguish `euler Λ` from its
  `W`-conjugates: `WSum (euler Λ ∘ w) = WSum (euler Λ)`;
* `Submission.E8WCFW.euler_sref` — **`euler Λ (sᵢ μ) = euler Λ μ`** for every simple reflection;
* `Submission.E8WCFW.euler_wact_of_simple` / `euler_ap` — hence `euler Λ (w μ) = euler Λ μ` for
  every `w ∈ W` (`W` is generated by the `sᵢ`, and `srefMat i = wactMat [i]`);
* `Submission.E8WCFW.euler_dc` — invariance under the dominant conjugate;
* `Submission.E8WCFM.euler_eq_MnuQ` — **`euler (Λ i) = Mnu i`** (all four hypotheses of
  `E8Character.eq_of_freudenthal`: value, support, `dc`-invariance, Freudenthal recursion — the
  last three were already available in `E8WCFE`);
* `Submission.E8WCFM.WCF_constituent` — **THE WEYL CHARACTER FORMULA FOR THE CONSTITUENTS**:
  `WSum (MnuQ i) x = alt (Λ i + ρ) x`, i.e. `A_ρ · ch L(Λ i) = A_{Λ i + ρ}`;
* `Submission.E8WCFM.alt_dominant` — `alt (Λ i + ρ) (Λ j + ρ) = [Λ i = Λ j]`.

### How `euler_sref` is proved (this is the trick that was missing for eight sessions)

Let `H = euler Λ ∘ sᵢ - euler Λ` and suppose `H ≠ 0`.  The key functional is

  `ψ ν := htOf ν - (coords ν)ᵢ`,  so that `ψ(α_k) = 1 - δ_{ik} ≥ 0` and `ψ(sᵢ ν) = ψ(ν)`.

* `ψ` is bounded above by `ψ Λ` on `supp H` (because `euler Λ μ ≠ 0 ⟹ μ ⪯ Λ`, and
  `euler Λ (sᵢ μ) ≠ 0 ⟹ sᵢ μ ⪯ Λ`, while `ψ(sᵢβ) = ψ(β)`).
* Let `m` be the maximum of `ψ` on `supp H` (`Finset.max'` over `Icc (ψ ν₁) (ψ Λ)`).
* For `ν` with `ψ ν = m` and `H ν ≠ 0`, `WSum H (ν+ρ) = 0` and every term with `ψ(ρ - Mρ) > 0`
  vanishes by maximality.  The remaining ones satisfy `ψ(ρ - Mρ) = 0`, i.e. `ρ - Mρ = c·αᵢ`
  (`ker ψ ∩ ℚ⁺ = ℕαᵢ`); then `htOf(ρ - cαᵢ) = 620 - c = htOf(wρ) ≤ 620` forces `c = 1`, so
  `Mρ = sᵢρ` and `M = srefMat i` (`ρ` is regular).  Hence **`H(ν + αᵢ) = H ν`**
  (`gamma_eq_srefMat` is exactly the classification `M = sᵢ`).
* iterating: `H(ν ± k αᵢ) = H ν` for all `k ≥ 0` (the closure under both `ν ↦ ν ± αᵢ` follows by
  applying the previous bullet to `sᵢν` as well), while `H(sᵢν) = -H ν`.
* but if `νᵢ = 0` then `sᵢν = ν` gives `Hν = -Hν`; if `νᵢ = -1` then `sᵢν = ν+αᵢ` gives
  `Hν = -H(ν+αᵢ) = -Hν`; in both cases `Hν = 0`, a contradiction.  Since `(ν ± kαᵢ)ᵢ = νᵢ ± 2k`,
  a suitable `k` always reaches `{0, -1}` — contradiction.  Hence `H = 0`.

(⚠ Do **not** try the "no-kernel" argument `E8NoKernel.WSum_eq_zero_of_bounded`: the support of
`H` is contained in the union of the two cone translates `Λ - ℚ⁺` and `sᵢ(Λ - ℚ⁺)`, which is not
height-bounded.  The functional `ψ` above is the correct substitute; it is *the* linear functional
that is nonnegative on both `ℚ⁺` and `sᵢℚ⁺`, and the one direction it misses (`αᵢ`) is exactly
what forces the iteration and the parity contradiction.)

## WHAT REMAINS (route now completely charted)

With `WCF_constituent` the Klimyk extraction is available.  For `Λ` dominant, `alt (Λ+ρ)` is the
alternant, and for the tensor square `T = T N = (V ⧸ N) ⊗ (V ⧸ N)` (semisimple,
`E8TensorBound.isSemisimple_tensor`) one has

  `(A_ρ chT)(Λ i + ρ) = Σ_e b'_e · alt (Λ e + ρ)(Λ i + ρ) = b'_i`   (`alt_dominant`),

where `chT ν = (finrank (TLwt N ν) : ℚ)` and `b'_e` is the multiplicity of `L(Λ e)` in `T`
(uses the character decomposition `chT = Σ_e b'_e ch L(Λ e)` and `WCF_constituent`).  The route is

1. **(TRACE-D)** — `∀ x, WSum chT x = Σ_{M ∈ WG} det M · mfun (x - ap M (λ + ρ))`.  This is the
   associativity of convolution: `WSum chT = A_ρ * (mfun * mfun) = (A_ρ * mfun) * mfun
   = alt (λ+ρ) * mfun`, using `E8TensorChar.finrank_TLwt_eq` and `E8WCFV.WCF_V`.
2. **the ball-4 truncation of `K_i := Σ_{M ∈ WG} det M · mfun (Λ i + ρ - M(λ+ρ))`**: a non-zero
   term has `mfun (Λ i - λ + ((λ+ρ) - M(λ+ρ))) ≠ 0`, so (`mfun γ ≠ 0 ⟹ htOf γ ≤ 2`, because
   `mfun γ ≠ 0` forces `γ = w r` with `r` one of `the7` dominant, and `htOf (w r) ≤ htOf r ≤ 2`)
   `htOf ((λ+ρ) - M(λ+ρ)) ≤ 2 - htOf (Λ i - λ) ≤ 4 - htOf (Λ i) ≤ 4`.  Since
   `htOf ((λ+ρ) - M(λ+ρ)) = ℓ(M)`, only the elements of the certified ball of radius `4`
   (`Submission.E8Ball.e8ball`, 450 entries) contribute.  Hence
   `b'_i = K_i = Σ_{p ∈ e8ball} (-1)^{p.2.length} · mfun (Λ i + ρ - wact p.2 (λ+ρ))`.
3. **`decide`**: `b'_i = ccv i ≥ 1` for the forty `i` (`Submission.E8Extract.ccv`, `ccv_pos`) —
   `40 × 450` evaluations of `mfun ∘ qq`; measured budget ≈ 1 min (compare `E8Checks`, 4392 terms
   in ≈ 11 s).
4. Then `ncard ≥ 40`: every one of the forty constituents occurs; combined with
   `ncard_tensor_le_forty` gives `ncard = 40`.

-/

/-!
## SESSION 42 (cont.): (TRACE-D) IS PROVED — `Submission/E8Klimyk.lean`

```
Submission.E8Klimyk.WSum_chT (N) (hvN) (hmax) (x) :
    WSum (fun ν => (Module.finrank ℂ ↥(TLwt N ν) : ℚ)) x
      = ∑ M ∈ WG, (M.det : ℚ) * mfun (x - ap M (λ + ρ))
```
i.e. `A_ρ · ch T = A_{λ+ρ} · ch V`, the associativity of the convolution
`A_ρ * (mfun * mfun) = (A_ρ * mfun) * mfun` written out with `Finset.sum_comm`.
Auxiliary: `mfun_eq_zero_of_not_mem` (support of `mfun` inside `E8Iso.L`),
`sum_mfun_ite` / `sum_mfun_ite_sub` (the delta collapses), `WSum_mfun_eq_sum_delta` (= `WCF_V`).

### The ball-4 truncation of `K_i` (next step, ingredients all in place)

For `x = Λ i + ρ` the terms of (TRACE-D) are `mfun (Λ i + ρ - M(λ+ρ))`, and a non-zero one has
`qZ (Λ i + ρ - M(λ+ρ)) ≤ 10` (`E8Support.mfun_ne_zero_iff`).  ⚠ The *height* form of the support
bound (`htOf γ ≤ 2` for `mfun γ ≠ 0`) is **FALSE** — `mfun ≠ 0` only gives `qZ γ ≤ 10`, and e.g.
`htOf λ = 75`.  The correct computation uses the quadratic form.  Write `γ = (Λ i - Mλ) + (ρ - Mρ)`;
then

  `qZ γ = qZ (Λ i - Mλ) + qZ (ρ - Mρ) + 2·⟪Λ i - Mλ, ρ - Mρ⟫`,
  `qZ (ρ - Mρ) = 2·e8ht (ρ - Mρ) = 2·ℓ(M)`  (`E8_qZ_rho_sub_wact` + `ρ - wρ` as a sum of roots),
  `⟪Λ i, ρ - Mρ⟫ ≥ 0`  (`Λ i` dominant, `ρ - Mρ ∈ ℚ⁺`),
  `⟪Mλ, ρ - Mρ⟫ = ⟪λ, M⁻¹ρ - ρ⟫ ≤ 0`  (`λ` dominant, `M⁻¹ρ - ρ ∈ -ℚ⁺`),
  `qZ (Λ i - Mλ) ≥ 0`  (positive definite).

⚠ **Formalisation warning (SESSION 42).**  The three algebraic inputs (`qZ (u+v) = qZ u + qZ v +
2⟪u,v⟫`, `⟪wact L u, wact L v⟫ = ⟪u,v⟫`, `⟪ρ - Mρ, Λ⟫ ≥ 0` and `⟪ρ - Mρ, Mλ⟫ ≤ 0`) are easy
mathematics but were **not** formalisable in `Submission/` without care: writing them in a file that
`open`s several namespaces at once makes `E8inv : Matrix (Fin 8) (Fin 8) ℤ` (an `abbrev` for
`Fin 8 → Fin 8 → ℤ`) trip the unifier inside `rw`/`simp` ("function expected `E8inv i`").  Do them in
a **separate file** `Submission/E8Pair.lean` with `import Submission.E8NoKernel` (which brings in
`Commons.LinearAlgebra.Matrix.Cartan.qz_wact' : qZ (wact L v) = qZ v`) and the pairing
`⟪u,v⟫ = ∑ᵢ uᵢ (coords v)ᵢ`, then use them elsewhere.  Also note `wact`/`sref` exist in *two*
commons namespaces (`Commons.LinearAlgebra.Matrix.Cartan` and `….E8posRoots`) — only one is visible
per file.

Hence `2·ℓ(M) ≤ qZ γ ≤ 10`, i.e. `htOf (ρ - Mρ) ≤ 5`, and the independence-number argument
(`E8_Nroot_card_le_four`, cf. `E8_wact_small_height_length`) gives `ℓ(M) ≤ 4`: `M` has a word of
length `≤ 4`, and `Submission.E8Ball.wact_mem` puts it into the certified 450-element ball `e8ball`
(`ballSet`, `WSum_eq_sum_ballSet'`).  Therefore

  `b'_i = K_i = ((e8ball.map (fun p => (-1)^p.2.length * mnorm (qZ (Λ i + ρ - wact p.2 (λ+ρ)))).sum : ℤ) : ℚ)`

and `decide` gives `b'_i = ccv i ≥ 1` (`E8Extract.ccv_pos`), `40 × 450` terms (`mfun ∘ qQ`) — about a
minute of kernel time (cf. `E8Checks`: 4392 terms in ≈ 11 s).

### The last structural item: the character decomposition

`b'_i = (A_ρ chT)(Λ i + ρ)` used above is the identity `b'_i = Σ_{S simple ≤ T} (A_ρ chFun S)(Λ i+ρ)`
with `chFun S = c_S · Mnu e(S)` (`E8ConstChar.chFun_eq_Mnu`) and
`(A_ρ Mnu e)(Λ i + ρ) = δ_{e,i}` (`E8WCFM.WCF_constituent` + `alt_dominant`).  What is still needed is
the *weight-multiplicity additivity of a direct sum*:

  `chT ν = Σ_{S ∈ family of simple constituents} chFun S ν`

which follows by strong induction on `finrank ℂ P` for a semisimple `P ≤ T N`:  pick a simple
`S ≤ P` (exists as `P ≠ 0`), semisimplicity gives `IsCompl S S'` with `P = S ⊔ S'`, whence
`finrank (P ⊓ TLwt ν) = finrank (S ⊓ TLwt ν) + finrank (S' ⊓ TLwt ν)`
(`Submodule.finrank_sup_add_finrank_inf_eq`), and recurse on `S'` (smaller dimension).
Also needed: `IsSimpleModule U ↥S` implies `S` is made of one `Mnu e` (this is
`E8ConstChar.chFun_eq_Mnu`, already available).

-/

/-!
## SESSION 42 — SUMMARY OF THE REMAINING WORK (for the next session)

**Done this session (all sorry-free, all imported):**

* `Submission.E8WCFW.euler_sref` / `euler_ap` / `euler_dc` — `euler Λ` is `W`-invariant
  (**this was the gap `(c)` open since SESSION 26**);
* `Submission.E8WCFM.euler_eq_MnuQ` — `euler (Λ i) = Mnu i`;
* `Submission.E8WCFM.WCF_constituent` — `A_ρ · Mnu i = A_{Λ i + ρ}` (WCF for the constituents, (Z));
* `Submission.E8WCFM.alt_dominant` — `alt (Λ i + ρ) (Λ j + ρ) = [Λ i = Λ j]`;
* `Submission.E8Klimyk.WSum_chT` — (TRACE-D) `A_ρ · chT = alt (λ+ρ) * mfun`.

**Remaining work, in dependency order.**

1. **The character decomposition.**  `chT ν = Σ_{S} chFun S ν` over the simple constituents `S` of
   `T N`.  Route: strong induction on `finrank ℂ P` for a `U`-submodule `P ≤ T N`; if `P ≠ 0` pick a
   simple `S ≤ P` (`IsSemisimpleModule.eq_bot_or_exists_simple_le`), semisimplicity gives a
   complement `S'` with `IsCompl S S'` and `P = S ⊔ S'`; then for every `ν`
   `finrank (P ⊓ TLwt ν) = finrank (S ⊓ TLwt ν) + finrank (S' ⊓ TLwt ν)` because
   `S ⊓ S' = ⊥` makes the two submodules of `TLwt ν` disjoint
   (`Submodule.finrank_sup_add_finrank_inf_eq`; note `P ⊓ TLwt ν = (S⊓TLwt ν) ⊔ (S'⊓TLwt ν)`).
   Recurse on `S'`.  (No isotypic-component machinery is needed.)
   Then, for a simple `S ≤ T N` with primitive generator of weight `Λ e`,
   `chFun S = c_S · Mnu e` with `c_S = chFun S (Λ e) ≥ 1` (**already proved**:
   `E8ConstChar.chFun_eq_Mnu`), and `(A_ρ chFun S)(Λ i + ρ) = c_S · δ_{e,i}` by `WCF_constituent`
   plus `alt_dominant`.

2. **The Klimyk value.**  `(A_ρ chT)(Λ i + ρ) = K_i` by (TRACE-D), and by 1. this equals
   `b'_i := Σ_{S ≅ L(Λ i)} c_S ≥ 1`.  For the computation of `K_i`:
   `K_i = Σ_{M ∈ WG} (M.det : ℚ) · mfun (Λ i + ρ - M(λ+ρ))`, and only `M` in the certified ball of
   radius `4` (`E8Ball.e8ball`, 450 entries, `WSum_eq_sum_ballSet'` + `sum_ballSet_eq_ballSum`)
   contribute — see the truncation argument above (`Submission/E8Pair.lean`, to be written).

3. **The `decide`.**  `K_i = ccv i` for the forty `i` (`E8Extract.ccv`, `E8Extract.ccv_pos`):
   `40 × 450` evaluations of `mfun ∘ qZ` — measured budget ≈ 1 minute.

4. **Assembly.**  `b'_i ≥ 1` for all forty `i` gives `ncard ≥ 40`; with
   `E8TensorBound.ncard_tensor_le_forty` this is `ncard = 40`, and the final assembly
   (`V := VermaWeight.V ⧸ N`, `E8Finrank.finrank_eq`, `E8Tensor`/`E8NullVector` irreducibility)
   is unchanged from the older sessions' roadmap.

-/

theorem e8_irrep_tensor_square_decomp :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : LieRingModule (LieAlgebra.e₈ ℂ) V) (_ : LieModule ℂ (LieAlgebra.e₈ ℂ) V),
      Module.finrank ℂ V = 779247 ∧
      LieModule.IsIrreducible ℂ (LieAlgebra.e₈ ℂ) V ∧
      (isotypicComponents (UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ))
        (V ⊗[ℂ] V)).ncard = 40 :=
  Submission.E8Ncard.main_assembly Submission.E8Num40.KbZ_ccv

end Submission
