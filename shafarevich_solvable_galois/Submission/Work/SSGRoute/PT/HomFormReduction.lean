import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.LTDDefs.H2locEquivH2
import Submission.Work.SSGRoute.LTDDefs.DecompAction
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
import Submission.Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local Tate duality in degrees `0` and `2` for a decomposition group

## What the target says

`Work.SSGRoute.PT.localTatePairing_deg02` is the *first conjunct* of the arithmetic input `(02)` of
the local-Tate-duality node `Work.SSGRoute.local_tate_duality` (see
`Submission/Work/SSGRoute/LTD_DESIGN.md`, §Inputs): for a number field `k`, an algebraic closure
`Ω`, a finite Galois `K/k` containing a primitive `p`-th root of unity `ζ`
(`T = μ_p^∨` the cyclotomic dual, `hT`), and every finite `𝔽_p[Gal(K/k)]`-module `M`, at every
finite place `A` of `Ω` over `k`,

  `dim H²(D_A, M) = dim H⁰(D_A, M^∨(1))`,   `M^∨(1) = DualMod p (M ⊗ T) ≅ Hom(M, μ_p)`,
  `D_A = decomp k A`.

This is **Milne, *Arithmetic Duality Theorems*, Cor. I.2.3 at `r = 0`**, for the local field `k_v`
obtained by completing `k` at the place below `A`.  Because `M` has exponent `p`, `M^D :=
Hom(M, k̄_v^×) = Hom(M, μ_p)`, and the corollary reads `H⁰(D_A, M^D)^∨ ≅ H²(D_A, M)`.  So the
target — and only this — is the degree-`0`/`2` case of local Tate duality.  It is **true**.

## Status update (class-formation route; read before attacking the target)

The target is Milne, *ADT*, Cor. I.2.3 at `r = 0` (with Theorem 2.1), i.e. for a finite module `M`
of exponent `p` over `G = D_A ≅ G_{k_v}`,

  `dim H²(G, M) = dim H⁰(G, Hom(M, μ_p))`   (`μ_p` with its *cyclotomic* action).

Its proof needs Milne's class-formation theorem (Theorem 1.8) for the class formation
`(G_{k_v}, \bar k_v^×)`, whose two axioms are

* **1.1a** `H¹(U, \bar k^×) = 0` for every open `U` — **provable and proved** in this workspace:
  `Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup`
  (`Submission/Work/SSGRoute/PT/KrullCorrespondence.lean`), together with the Krull correspondence
  `fixingSubgroup_fixedField_of_isOpen`, the finiteness `finiteDimensional_fixedField_of_isOpen`
  and the homeomorphism `isHomeomorph_fixingSubgroupEquiv` used in the transfer;
* **1.1b** a compatible family `H²(U, \bar k^×) ≅ ℚ/ℤ` — the local invariant map; in the workspace
  this is available at finite levels (`Commons.NumberTheory.NumberField.Completion.*`, the
  fundamental class `H²(Gal(L/K), L^×) ≅ ℤ/[L:K]`), and must be transported to the full group
  `D_A` (via the colimit description / Milne's Lemma 1.9 argument).

Together with the extra hypothesis of Theorem 1.8(c) — `α⁰(U, ℤ/m)` bijective for all open `U`
and all `m` (Kummer: `H²(U, ℤ/m) ≅ μ_m(U)^∨`) — Theorem 1.8 gives the target.  Two further
foundational pieces are on this route and are/were built here:

* `h1Transfer` (done, `PT/H1Transfer.lean`) and the requested `Work.SSGRoute.PT.H2Transfer`
  (degree-2 transfer along a homeomorphic group isomorphism), which transport cohomology along
  `D_A ≅ G_{k_v}` (`Commons.NumberTheory.NumberField.Completion.*LocalGalois*`) and along
  algebraic-closure isomorphisms;
* the coefficient long exact sequence for `Work.AbsoluteKummer.H1/H2`
  (`Submission/Work/AbsoluteKummer/SES*.lean`), which is what the Kummer sequence
  `1 → μ_p → \bar k^× → \bar k^× → 1` is fed into.

**Two warnings for whoever continues.**

1. *Do not* use the naive "colimit over finite levels" formula without care: the transition maps
   are the *inflations*, which are frequently **zero** (e.g. `inf : H²(ℤ/p^n, 𝔽_p) → H²(ℤ/p^{n+1},
   𝔽_p)` is zero for trivial coefficients, by the Hochschild–Serre sequence, since the transgression
   kills the whole group).  This is why `dim H²(G_{k_v}, 𝔽_p)` is `0` for `k_v = ℚ_p`, `p` odd
   (`= [μ_p ⊆ k_v] + f(e-1)` in general), and *not* the dimension of the individual terms.
   In particular `dim H²(G_{k_v}, 𝔽_p)` is **not** the relation rank of the maximal pro-`p`
   quotient.
2. **The archimedean question is settled (in favour of the statement), by
   `isFinPlace_iff_ne_top` below**: for `Ω` algebraic over `k` (here `IsAlgClosure k Ω`),
   `IsFinPlace k A` is *equivalent* to `A ≠ ⊤`.  A `ValuationSubring Ω` is the unit ball of an
   ultrametric valuation `Ω → Γ₀` (Mathlib's `ValuationSubring` is defined by
   `∀ x, x ∈ A ∨ x⁻¹ ∈ A`, which forces `v(x + y) ≤ max (v x) (v y)` for `v x = x·A^×`), so
   *archimedean* places are not represented by `ValuationSubring`s at all; and the trivial
   valuation ring `⊤` (whose restriction to `k` is again `⊤`) is the *only* `A` with
   `A.comap (algebraMap k Ω) = ⊤`, because a valuation subring containing a field algebraic over
   which the ambient field is algebraic is everything
   (`Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top`).
   Consequently every `A` in the quantifier lies over a *non-archimedean* place of `k`, and Milne,
   *ADT*, §I.2 applies; the finite-group counterexamples at complex/real places (which *are* real:
   e.g. `G = ℤ/2`, `M = 𝔽_2[ℤ/2]`, where `H²(ℤ/2,M) = 0` by Shapiro while
   `Hom_{ℤ/2}(M, μ_2) = 𝔽_2`) cannot occur, and real places are handled in this workspace as
   involutions of `G_k` (`Work.SSGRoute.local_tate_duality_archimedean`), not as
   `ValuationSubring`s.

## Status of the assembly, and the exact remaining obligations (roadmap)

**Verified in this file** (sorry-free):

* `isFinPlace_iff_ne_top` — `IsFinPlace k A ↔ A ≠ ⊤` for `IsAlgClosure k Ω`; this settles the
  archimedean question (see above): the quantifier of the target is exactly the set of
  *non-archimedean* places of `k`, so Milne, *ADT*, §I.2 applies to every `A` it mentions;
* `finrank_eq_of_addEquiv` — the `𝔽_p`-dimension is an invariant of the underlying additive group
  among finite `𝔽_p`-vector spaces (so `finrank` transfers along the `≃+` bridges);
* `instModuleH2` — the `𝔽_p`-module structure on the workspace's `Work.AbsoluteKummer.H2`, and
  `card_H2loc_eq_card_H2` — the two models of `H²(D_A, M)` (`H2loc` of `LTDDefs/Basic` and
  `Work.AbsoluteKummer.H2`) have the same cardinality;
* `H2locEquivH2_decomp` — the model bridge at `D_A = decomp k A`;
* `curryMT`, `HomH`, `h0loc_dualMod_tensor` — the right-hand side of the target is
  `Hom_{D_A}(M, T^∨) = Hom_{D_A}(M, μ_p)`;
* `localTatePairing_deg02_of_hom_form` — **the target is *equivalent* to the `Hom`-form**
  `dim H²(D_A, M) = dim Hom_{D_A}(M, μ_p)` for every finite `𝔽_p[Gal(K/k)]`-module `M`.

Adjacent plumbing that is already verified in the workspace and that the eventual assembly of
the target will use: `Work.SSGRoute.PT.dualMod_smul_zeta_pow`
(`Submission/Work/SSGRoute/PT/dualMod_smul_zeta_pow.lean`) — the action of `Gal(K/k)` on the line
`DualMod p T` is the cyclotomic character, i.e. `σ • ψ = c • ψ` when `σ ζ = ζ^c`; this is the
comparison between the abstract coefficient module `DualMod p T` and the concrete `μ_p(Ω)`
(`Work.SSGRoute.selfdual`, `Work.SSGRoute.zmod_roots_of_unity`, `Work.SSGRoute.dualUnits_linearEquiv`
supply the `𝔽_p`-linear side of that comparison).

**The one remaining obligation is therefore Milne, ADT, I.1.8 at `r = 0`**, i.e. the `Ext`/`Hom`
duality for the local class formation `(G_{k_v}, \bar k_v^×)`, together with the two class-formation
axioms and the extra hypothesis of I.1.8(c).  Concretely, in this workspace:

**UPDATE (the `α²`-form: the target is the `r = 2` case, so `I.1.8(c)` is *not* needed).**  Apply
I.1.8(a) not to `M` but to the finite module `N = M^∨(1) = DualMod p (M ⊗ T)`: it gives
`Ext²_G(N, C) ≅ H⁰(G,N)^∨`.  Since `Hom_ℤ(N, \bar k_v^×) ≅ M` — the twist cancellation
`Hom_ℤ(E^∨(1), Ωˣ) ≅ E` proved in this workspace as
`Work.SSGRoute.hom_dualMod_local_units` (`Submission/Work/SSGRoute/hom_dualMod_local_units.lean`)
and `hom_dualMod_units_equiv` — the source of that isomorphism *is* `H²(G, M)`, and the dimension
of `H⁰(G,N)^∨` is that of `H⁰(G,N) = H⁰(D_A, DualMod p (M⊗T))`, i.e. exactly the right-hand side of
the target.  Hence the target is *the `r = 2` case of Milne's Theorem I.1.8(a)*, which is proved
**without** hypothesis I.1.8(c) (Kummer duality `α⁰(U, ℤ/m)`); the arithmetic inputs that the
proof of (a) does use are the class-formation axioms (1.1a) — *already proved here* — and (1.1b)
(the invariant map), together with Lemma 1.9 and the trivial-action cases of (1.7).

The coefficient-level pairing `α²` that carries the statement is built, inside this workspace's
continuous-cochain model, in `Submission/Work/SSGRoute/PT/AlphaPairing.lean`
(`Work.SSGRoute.PT.alphaTwo`), together with `α⁰` (`Work.SSGRoute.PT.alphaZero`) and the coefficient
module `Work.SSGRoute.PT.ConjHom` `= Hom_ℤ(N,C)` with its **conjugation** action
`(g • f)(n) = g • f (g⁻¹ • n)`.  The next steps of the assembly are the naturality of `α²` in `N`
(`Work.SSGRoute.PT.alphaTwo_naturality`) and with respect to the evaluation maps
(`Work.SSGRoute.PT.alphaTwo_evalHom`), the short exact sequence of coefficient modules
`0 → Hom_ℤ(N'',C) → Hom_ℤ(N,C) → Hom_ℤ(N',C) → 0` (exactness of `Hom_ℤ(-,C)` — `C` divisible:
`Work.SSGRoute.PT.exists_addHom_extend_addUnits`), and the five-lemma dévissage of I.1.8(a).

1. **(1.1a) `H¹(U, \bar k_v^×) = 0`** for every open `U ≤ D_A` — *proved*
   (`Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup`), using the Krull correspondence
   `fixingSubgroup_fixedField_of_isOpen`, its finiteness, and `h1Transfer`.
2. **(1.1b) the invariant map** `inv_U : H²(U, \bar k_v^×) ≅ ℚ/ℤ`, *compatible* along `V ≤ U`
   (`inv_V ∘ Res_{V,U} = ×(U:V) ∘ inv_U`).  At finite levels this is the fundamental class of
   `Commons.NumberTheory.NumberField.Completion`
   (`…addEquiv_tateCohomology_of_fundamental_class`, `…exists_addOrderOf_eq_finrank_groupCohomology_two_units`);
   the passage to open `U ≤ D_A` is Milne's Lemma 1.9 argument (the *modified* direct system with
   transition maps `(U:V)·Inf`, whose limit vanishes because `|U|` is divisible by every integer —
   **not** the naive `Inf`-system, whose transition maps are frequently zero).  The bridges to
   `D_A` are `Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois*`
   and `Work.SSGRoute.PT.H2Transfer`; `Work.SSGRoute.PT/*LocalizationAt*` and `H2locEquivH2sub`
   are the level-restriction infrastructure.
3. **I.1.8(c)** `α⁰(U, ℤ/m)` bijective for all open `U` and all `m` — the Kummer/Brauer base case
   `H²(U, ℤ/m) ≅ μ_m(U)^∨` (equivalently `H²(U, μ_p) ≅ ℤ/p`–type statements).  This is *not*
   implied by the axioms; it must be proved (or assumed) separately.
4. **Theorem I.1.8 itself**: the Yoneda/`Ext` map `α^r(G, M) : Ext^r_G(M, C) → H^{2-r}(G, M)^∨` is
   an isomorphism for finite `M` (at `r = 0` the target).  Its proof needs `Ext` in the category of
   discrete `G`-modules, the cup-product/`Ext` compatibilities (`(0.14)`, `(1.7)`, Lemma 1.9's
   vanishing `Ext^r_G(M,C) = 0` for `r ≥ 3`, `M` torsion-free), and the dévissage along
   `0 → M → ℤ[G/U] ⊗ M → M₁ → 0`.

Because `M` has exponent `p` here, `Hom_{G_{k_v}}(M, \bar k_v^×) = Hom_{G_{k_v}}(M, μ_p)` (every
`G`-homomorphism into the divisible `\bar k_v^×` lands in its `p`-torsion `μ_p`), which is what
turns I.1.8 at `r = 0` into the target's right-hand side.

## Reduction

`H2locEquivH2_decomp` below identifies `H2loc p k Ω K M (decomp k A)` with the workspace's
continuous-cohomology model `Work.AbsoluteKummer.H2 ↥(decomp k A) M` of the *profinite* group
`D_A ≅ G_{k_v}`, and `H0loc p k Ω K N (decomp k A) = N^{D_A}`.  So the target is exactly local
Tate duality for the profinite local class formation `(G_{k_v}, k̄_v^×)`.

The classical proof is Milne, *ADT*, **Theorem I.1.8** (Tate–Nakayama for a class formation): for a
class formation `(G, C)` with fundamental class `u ∈ H²(G, C)`, the Yoneda/cup-product map

  `˛^r(G, M) : Ext^r_G(M, C) → H^{2-r}(G, M)^∨`

is an isomorphism for all finitely generated `M`.  For `C = k̄_v^×` (divisible) one has
`Ext^r_G(M, C) ≅ H^r(G, Hom(M, C))`, so at `r = 0`

  `H⁰(G, Hom(M, μ_p))^∨ ≅ H²(G, M)`,

which is the target (the finiteness of the two groups comes with the isomorphism).

## The genuine missing input, and a warning about the naive statement

The workspace proves exactly the **`M = ℤ` case** of Theorem I.1.8
(`Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class`,
`Commons.NumberTheory.NumberField.Completion.addEquiv_tateCohomology_of_fundamental_class`) and
the class-formation axioms for completions of number fields.  It does **not** have I.1.8 for
general coefficients, and that is the whole gap.

*Do not* try to substitute the naive "`Tor₁`-free" form of Tate–Nakayama
(`Ĥ^r(G, M) ≅ Ĥ^{r+2}(G, M ⊗_ℤ C)`): that statement is **false** without the hypothesis
`Tor^ℤ₁(M, C) = 0`.  (Milne, *ADT*, Theorem 0.2 carries this hypothesis; a concrete counterexample
is `F = ℚ₃`, `L = ℚ₃(i)` unramified of degree `2`, `C = L^×`, `M = ℤ/2` trivial: then
`M ⊗ C = L^×/L^{×2} ≅ (ℤ/2)²` carries the *trivial* `G`-action, so `|Ĥ⁰(G, M⊗C)| = 4` while
`|Ĥ^{-2}(G, M)| = 2`.)  The correct route is the `Ext`/`Hom`-duality above, which is why the
class module must be the *divisible* `k̄_v^×` rather than `L^×`.

## The level-wise `Ext` form of local duality is FALSE (do not rebuild it)

Two attempts to state the local Tate pairing at the *finite levels* `L ⊇ K`, `w' ∣ w` in the
`DESIGN_EXT` style (as companions of node E7b `Work.SSGRoute.local_duality_ext`) were refuted by
review, with two independent counterexamples.  The correct statement of local Tate duality is
over the **full** profinite group `G_{k_v}` — which is exactly what this file's target is:

* **Archimedean places.**  `NK.GlobalCFT.Place K` includes archimedean places; at a *complex*
  `w` every `D_{w'} = Gal(ℂ/ℂ) = 1`, so `H²(D_{w'}, M) = 0` at every level and the pairing is
  identically `0` — but `Ext⁰_{D_w}(M, K_wˣ) = Hom_{D_w}(M, ℂˣ) ≠ 0` for nontrivial finite `M`
  (`k = K = ℚ(i)`, `p = 2`, `M = 𝔽₂`, `w` complex).  So "no left kernel" fails, and it must be
  restricted to `w.IsFinite`.
* **The realisation clause is not uniform in `L`.**  `Ext⁰_{D_w}(M, K_wˣ)` is computed at the
  *fixed* level `K`, while `H²(D_{w'}, M)` grows with `L`.  E.g. `k = K = ℚ`, `p = 2`, `M = 𝔽₂`,
  `w` the place over `2`, `L = ℚ(ζ₈)`: `Ext⁰` has `𝔽₂`-dimension `1`, but
  `D_{w'} = Gal(ℚ(ζ₈)/ℚ) = (ℤ/2)²`, `2 ∣ 4`, and `H²((ℤ/2)², 𝔽₂)` has dimension `3`, so most
  `2`-torsion functionals are realised by no `x`.

The two failures cancel in the *direct limit* over `L`: `H²(G_{k_v}, M) = colim_L H²(D_{w'}, M)`
with `Hom_{D_w}(M, K_wˣ) = H⁰(G_{k_v}, Hom(M, μ_p))`, and *that* pairing is Milne's (Cor. I.2.3 at
`r = 0`) — the target below.  **Consequence for the fleet:** node E7b
(`Work.SSGRoute.local_duality_ext`, degree `1`) carries the same unbounded-`L` clause and should be
re-examined against these two counterexamples before it is relied on.  The positive, usable
fragments are `Work.SSGRoute.PT.local_duality_ext_deg02`'s replacements: the pairing calculus
`Work.SSGRoute.PT.levelPair_functoriality` (`levelPair` additive/zero, `Ext⁰ = Hom`), and the two
targets `Work.SSGRoute.PT.localTatePairing_deg02` (full group) and
`Work.SSGRoute.PT.finite_H2loc`.

## Roadmap: what is proved here, and the one missing input

Proved, sorry-free, in this file:

* `finrank_eq_of_nondegenerate_pairing`, `finite_H0loc`, `moduleFinite_H0loc`,
  `isClosed_decomp` — the linear algebra and model facts;
* `H2locEquivH2_decomp` — `H2loc p k Ω K M (decomp k A) ≃+ Work.AbsoluteKummer.H2 ↥(decomp k A) M`
  (the bridge to the workspace's continuous cohomology of the profinite group `D_A`);
* `curryMT`, `HomH`, `h0locToHomH`, `h0loc_dualMod_tensor` — **the two sides of the target are
  identified**: for every subgroup `H ≤ G_k`,
  `H0loc p k Ω K (DualMod p (M ⊗ T)) H ≃ₗ[𝔽_p] Hom_H(M, T^∨)`
  (with `T^∨ = DualMod p T = μ_p` under `IsCyclotomicDual`);
* `localTatePairing_deg02_of_hom_form` — **the target reduced to its `Hom`-form**:
  `(∀ A hA M, dim H²(D_A,M) = dim Hom_{D_A}(M, DualMod p T))` implies the target.

The single missing input is therefore the `Hom`-form of local Tate duality over the *full*
profinite group `D_A ≅ G_{k_v}`:

  `dim H²(D_A, M) = dim Hom_{D_A}(M, μ_p)`   for every finite `𝔽_p[Gal(K/k)]`-module `M`.

This is Milne, *ADT*, I.2.1 (= Cor. I.2.3 at `r = 0`), and it is **not** reachable from the
finite-level Tate theorem alone: the finite-level statement `Ĥ²(Gal(L/k_v), M) ≅
Ĥ⁰(Gal(L/k_v), Hom(M, μ_p))^∨` is **false** for `M` of exponent `p` (take `k_v = ℚ_2`, `L` with
`Gal(L/ℚ_2) = (ℤ/2)²`, `M = 𝔽_2`: `|H²((ℤ/2)², 𝔽_2)| = 8 ≠ 2 = |Ĥ⁰((ℤ/2)², μ_2)|`); the correct
finite-level theorem uses the `⊗`-form `Ĥ^r(G, M) ≅ Ĥ^{r+2}(G, M ⊗ L^×)` for `ℤ`-free `M`, which
degenerates for torsion `M` since `ar k_v^×` is divisible.  The genuine route is Milne's
*class-formation* theorem (ADT I.1.8): for a class formation `(G, C)` with `C` divisible and
fundamental class `u`, the Yoneda/cup-product map

  `Ext^r_G(M, C) → H^{2-r}(G, M)^∨`

is an isomorphism for all finite `M`; at `r = 0` and `G = G_{k_v}`, `C = ar k_v^×` it reads
`Hom_{G_{k_v}}(M, μ_p) ≅ H²(G_{k_v}, M)^∨`, which is the missing input.

### Smaller pieces still needed (independently useful)

* `finite_H2loc` — `Finite (H2loc p k Ω K M (decomp k A))`.  **Caution: this is *not* an
  independent piece.**  The `2`-cocycle group is *infinite*: `d¹` of the (infinite) locally
  constant `1`-cochains is already infinite — e.g. for `H = ℤ_p`, `M = ℤ/p` trivial,
  `B² ⊇ d¹{f : f factors through ℤ/pⁿ}`, an infinite increasing union — while `H²(H,M) = ℤ/p`
  is finite.  So finiteness of the *quotient* `Z²/B²` needs the same local theory as the target
  (`dim H²(D_A,M) = dim Hom_{D_A}(M,μ_p)` gives finiteness and the dimension at once).  The
  finite-`U`-invariance argument only bounds `Z²/B²` *relative to a level*; it does not by itself
  bound the colimit.  Do not attack `finite_H2loc` in isolation.
* the `M = 𝔽_p` base case (`SSGRoute/PT/localTatePairing_deg02_triv`), i.e.
  `dim H²(D_A, 𝔽_p) = dim μ_p(k_v)` — the Kummer/Brauer computation;
* the Shapiro/dévissage step reducing the general finite `M` to the base cases.

### The next delegation: the abstract class-formation Tate duality

Write in `Submission/Work/SSGRoute/PT/<name>.lean`.  **Design constraints established by two
review rounds (do not lose these):**

* The statement must be made in the **continuous-cohomology** vocabulary — `Work.AbsoluteKummer.H1`
  / `H2` (locally constant cochains on a topological group) — *not* `SSGRoute.PTExt.extH`
  (`Abelian.Ext` in `Rep Coeff G`), which is *abstract* group cohomology.  For the intended
  `G = D_A`, `C = \bar k_v^×` the abstract `H¹(H,C)` is `Hom_abs(H,C) ≠ 0` for trivial-action
  finite-index `H`, so `h1` (Hilbert 90) would **fail**; and Milne's 1.8 rests on colimits over
  open normal subgroups, which is the continuous theory.
* Milne's Theorem 1.8(c) (`_mywork/adt.txt`, lines 1352–1419) has an **extra hypothesis** beyond
  the class-formation axioms 1.1a/b: `α⁰(U, ℤ/mℤ)` must be *bijective for all open `U` and all
  `m`*, where `α^r(U,N) : Ext^r_U(N,C) → H^{2-r}(U,N)^∨`.  This hypothesis is **not** implied by
  the axioms + divisibility of `C` (for `M = ℤ/m` it *is* the conclusion), so it must appear in
  the statement.  Its local verification is exactly the Kummer/Brauer base case
  `H²(L, ℤ/m) ≅ μ_m(L)^∨` — i.e. the `M`-trivial case of the target.
* The class-formation axioms 1.1a/b are: `H¹(U,C) = 0` for all open `U`, together with a
  **compatible family** of isomorphisms `inv_U : H²(U,C) ≅ ℚ/ℤ` (index `U`, `V ⊆ U`:
  `inv_V ∘ Res = ×(U:V) ∘ inv_U`).  The compatibility is used and should be data, not `Nonempty`.
* Milne's Example 1.6(a) (`G = Ẑ`, `C = ℤ`) is **not** a counterexample to the axioms (one has
  `H²(Ẑ,ℤ/2) = 0 = Hom_Ẑ(ℤ/2,ℤ)`; see Milne Example 1.10), so divisibility of `C` is not
  motivated by it.

The shape to aim at (to be instantiated at `G = ↥(SSGRoute.decomp k A)`, `C = ` the units of `Ω`
at `A`, `M` a finite `𝔽_p[Gal(K/k)]`-module):

* (A) abstract: class formation (continuous cohomology, compatible `inv` family) `+`
  `α⁰(U,ℤ/mℤ)`-bijectivity for all open `U` and all `m`  ⟹  `H²(G,M) ≅ H⁰(G, Hom(M,C))^∨`
  for all finite `M`;
* (B) arithmetic: the class-formation axioms for `(D_A, \bar Ω^×)` (Hilbert 90 for `h1`, the local
  invariant map `Br(L) ≅ ℚ/ℤ` for `h2` with the compatibility) **and** the base case
  `α⁰(U, ℤ/mℤ)`-bijectivity (Kummer/Brauer: `H²(L, ℤ/m) ≅ μ_m(L)^∨`, i.e. the `M`-trivial case of
  the target, `SSGRoute/PT/localTatePairing_deg02_triv`).

Then the instantiation below finishes it.

* `G := ↥(SSGRoute.decomp k A)` (a plain group; `H.FiniteIndex ↔ IsOpen` for profinite `G`);
* `C := ` the units of `Ω` at `A`, i.e. `Additive ↥(Ω)ˣ ≅ ` `NK.HassePrinciple.localUnitsRep`
  (`SSGRoute.PTExt.localUnitsK (w := A)`) — the class module whose `H¹` vanishes by Hilbert 90
  (`Submission.hilbert90_H1_eq_zero`) and whose `H²` is `ℚ/ℤ` by the local invariant map;
* identify `SSGRoute.PTExt.extH M 2 = Ext²_{D_A}(ℤ,M)` with `Work.SSGRoute.H2loc p k Ω K M
  (decomp k A)` via `PT/pt_ext_cohomology.lean` (`coHomAddEquivExt`) and
  `H2locEquivH2_decomp` (this file);
* identify `Hom_{D_A}(M, C)` with `Hom_{D_A}(M, μ_p) = HomH p k Ω K M T (decomp k A)`
  (`h0loc_dualMod_tensor`, this file) — legitimate because `M` has exponent `p`, so every
  homomorphism into the divisible `C` lands in `μ_p = C[p]`;
* conclude with `localTatePairing_deg02_of_hom_form` (this file).

### A remark on the vocabulary of the missing input

The left-hand side of the target is *already* the continuous cohomology of the profinite group
`D_A`: `H2loc` is defined through locally constant cochains on `G_k = Ω ≃ₐ[k] Ω` and
`H2locEquivH2_decomp` identifies it with `Work.AbsoluteKummer.H2 ↥(decomp k A) M`.  The delegated
statement may therefore be phrased with `H2loc`/`H0loc`/`HomH` directly (as in
`localTatePairing_deg02_of_hom_form`); what must **not** be used is `SSGRoute.PTExt.extH`
(`Abelian.Ext` in `Rep Coeff G`), which is *abstract* group cohomology: for the intended infinite
`D_A` its `H¹` is `Hom_abs(D_A, C) ≠ 0`, so Hilbert 90 fails there.

### The first piece of (B): Hilbert 90 at an open subgroup — what is missing

Target of the piece: for `U ≤ Ω ≃ₐ[k] Ω` **open** (`Ω` with `IsAlgClosure k Ω`),
`Subsingleton (Work.AbsoluteKummer.H1 ↥U (Additive ↥Ωˣ))` — Milne's class-formation axiom 1.1a for
`C = \bar Ω^×`.  Two things are missing and both are infrastructure, not mathematics:

1. **`H¹`-transfer along a *group* isomorphism — DONE.**  See
   `Submission/Work/SSGRoute/PT/H1Transfer.lean` (sorry-free):
   * `Work.SSGRoute.PT.cochainTransfer`, `.cochainTransfer_isLocallyConstant` (uses
     `IsHomeomorph.isOpenMap` to get `Continuous Φ.symm`, then
     `Work.AbsoluteKummer.IsLocallyConstant.comp`),
   * `.cochainTransfer_isCrossedHom`, `.cochainTransfer_d0`, `.z1Transfer`,
   * `.h1TransferAddHom`, `.h1TransferAddHom_mk`,
   * `.h1Transfer` — the headline: for `Φ : G' ≃* G` with `IsHomeomorph Φ`
     (`hΦ`) and `Ψ : M' ≃+ M` with `Ψ (g' • m') = Φ g' • Ψ m'` (`hΨ`),
     `H1 G' M' ≃+ H1 G M`.
   Note the hypothesis must be `IsHomeomorph Φ`, **not** `IsLocallyConstant Φ` (false for an
   injective homomorphism of profinite groups: trivial kernel would force `1` open).

2. **Hilbert 90 over an arbitrary `IsAlgClosure` field — DONE.**  See
   `Submission/Work/SSGRoute/PT/Hilbert90IsAlgClosure.lean` (sorry-free):
   * `Work.SSGRoute.PT.algEquivUnitsMapOfField` (+ `_coe` / `_mul` / `_one`),
   * `Work.SSGRoute.PT.instDistribMulActionAddUnitsOfField` — the general action of `Gal(E/F)`
     on `Additive (Units E)`, at **priority 100** so that the workspace's specialised instance
     `Work.AbsoluteKummer.instDistribMulActionAddUnits` still wins for `E = AlgebraicClosure k`,
   * `Work.SSGRoute.PT.algEquivUnitsMapOfField_comm` — `e.symm (σ u) = (e.autCongr⁻¹ σ) (e.symm u)`,
   * **`Work.SSGRoute.PT.hilbert90_H1_eq_zero_of_isAlgClosure`** — for `F Ω` with `IsGalois F Ω`,
     `IsAlgClosure F Ω`, `CharZero F`: `Subsingleton (H1 (Ω ≃ₐ[F] Ω) (Additive (Units Ω)))`, i.e.
     Milne's class-formation axiom 1.1a in the generality the target needs, obtained by
     `h1Transfer` along `(AlgEquiv.autCongr e)⁻¹` (`e := IsAlgClosure.equiv F (AlgebraicClosure F) Ω`,
     a homeomorphism by `NK.Mine.isHomeomorph_autCongr` / `isHomeomorph_symm`) from
     `Submission.hilbert90_H1_eq_zero`.
   * Two pieces of *generic* infrastructure were needed and are now also permanent:
     `H1Transfer.lean`'s universe-polymorphic `Work.SSGRoute.PT.cochainTransfer` chain (the
     workspace's groups had to be made `Type*`), and
     `Work.SSGRoute.PT.isLocallyConstant_comp_continuous` — the workspace's
     `Work.AbsoluteKummer.IsLocallyConstant.comp` forces both domains into the *same* universe,
     which blocks the transfer between `Gal(Ω/F)` and `Gal(\bar F/F)`; the restated version is
     universe-polymorphic.

3. **Hilbert 90 at an *open* subgroup — the last step (NEXT).**  With item 2 in hand the target
   statement is
   `Subsingleton (H1 ↥U (Additive (Units Ω)))` for `U ≤ Ω ≃ₐ[k] Ω` **open** (`IsGalois k Ω`,
   `IsAlgClosure k Ω`, `CharZero k` — all satisfied in the application).  Two sub-steps:
   * **(3a) the Krull correspondence — DONE** (`Submission/Work/SSGRoute/PT/KrullCorrespondence.lean`):
     `Work.SSGRoute.PT.fixingSubgroup_fixedField_of_isOpen` and its easy half
     `Work.SSGRoute.PT.le_fixingSubgroup_fixedField`.  The one missing ingredient was the
     `Normal k ↥M` instance for `M := normalClosure k ↥E Ω`: it needs the ambient to be *Galois*
     (`[IsGalois k Ω]`, present in the statement — compare
     `Submission/NeukirchUchida/Local/PlaceFromValuation.lean:387`), and then `inferInstance`
     works.  Proof: Krull basis → finite `E` with `E.fixingSubgroup ⊆ U`; `M := normalClosure`,
     `ρ := AlgEquiv.restrictNormalHom (K₁ := Ω) ↥M`, `H := U.map ρ`,
     `fixedField H = (fixedField U).comap _` (via `restrictNormalHom_apply`), `ρ σ ∈ H` via the
     finite-level `fixingSubgroup_fixedField H`, then `Subgroup.mem_map` and
     `ker ρ = M.fixingSubgroup ⊆ U`.
   * **(3b) Hilbert 90 at an open subgroup (NEXT)**: stated as
     `Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup` in the same file.  What is settled:
     `InferInstance` supplies `IsGalois ↥L Ω` and `CharZero ↥L` from `[IsGalois k Ω]`/`[CharZero k]`
     (verified), and Mathlib has the group isomorphism
     `IntermediateField.fixingSubgroupEquiv L : ↥L.fixingSubgroup ≃* Gal(Ω/L)` (verified).  What
     remains is its `IsHomeomorph`, i.e. the agreement of the subspace topology on
     `L.fixingSubgroup ⊆ Gal(Ω/k)` with `krullTopology L Ω`; Mathlib has *no*
     `isHomeomorph_fixingSubgroupEquiv`, and no `IntermediateField.finrank_fixedField` /
     `finrank_fixingSubgroup` either, so the auxiliary fact that `L = fixedField U` is finite over
     `k` for open `U` (needed to turn `fixingSubgroup M`, `M/L` finite, into a neighbourhood of
     `1` in `U`) must be proved locally — e.g. from `U.FiniteIndex` (`IsOpen` gives finite index)
     plus the Galois correspondence for `[fixedField U : k]`, or by choosing the basic open
     `fixingSubgroup E ⊆ U` (`E/k` finite) and working with `E` rather than `L`.

     **UPDATE (after review):** the homeomorphism lemma *already exists*, sorry-free, in the
     workspace: `Work.SSGRoute.isHomeomorph_fixingSubgroupEquiv`
     (`Submission/Work/SSGRoute/finite_openKernel_homs_decomp_kernel.lean:122`), with exactly the
     hypotheses `[FiniteDimensional k K] [IsAlgClosure k Ω]` and the statement
     `IsHomeomorph (IntermediateField.fixingSubgroupEquiv K : ↥(K.fixingSubgroup) → (Ω ≃ₐ[↥K] Ω))`
     — i.e. `IsAlgClosure k Ω` (in the target) plus `FiniteDimensional k ↥L` for `L := fixedField U`.
     A companion `continuous_fixingSubgroupEquiv` (no finiteness hypothesis) and
     `IntermediateField.fixingSubgroup_isOpen` are in the same file.  **Do not re-request**: a
     standalone version without `[FiniteDimensional F L]` is *false* (reviewers' counterexample:
     `F = ℚ`, `E = ℚ(X)`, `L = ℚ(X²)`: `↥L.fixingSubgroup` carries the indiscrete subspace topology
     while `Gal(E/↥L)` is discrete, so the map is not continuous).
     
     So the **single remaining gap for 3b** is `FiniteDimensional k ↥(fixedField U)` for open `U`
     (equivalently `Module.finrank k ↥(fixedField U) = U.index`): Mathlib has only the
     finite-extension case (`IntermediateField.finrank_fixedField_eq_card`, used by
     `Submission/Work/SSGRoute/phi1_mono_sylow_in.lean:50`), not the infinite Galois correspondence
     `[fixedField U : k] = [Gal(Ω/k) : U]`.  Requested as
     `SSGRoute/PT/finiteDimensional_fixedField_of_isOpen`.  Once it is in,
     `hilbert90_H1_eq_zero_of_isAlgClosure ↥L Ω` (item 2) transported along
     `Work.SSGRoute.isHomeomorph_fixingSubgroupEquiv` finishes 3b exactly as in the recipe above.
   * **(3a, superseded) original note:**  File
     `Submission/Work/SSGRoute/PT/KrullCorrespondence.lean`: the statement
     `Work.SSGRoute.PT.fixingSubgroup_fixedField_of_isOpen` is down, the easy direction
     (`Work.SSGRoute.PT.le_fixingSubgroup_fixedField`, from the Galois connection
     `IntermediateField.le_iff_le`) is proved, and the first step of the hard direction
     (the Krull basis `obtain ⟨E, hEfin, hEU⟩` from `krullTopology_mem_nhds_one_iff`) already
     elaborates.  **Remaining**: the normal-closure step — `M := IntermediateField.normalClosure k
     ↥E Ω` satisfies `E ≤ M` (`IntermediateField.le_normalClosure`) and
     `FiniteDimensional k ↥M` (`normalClosure.is_finiteDimensional`, found by `#synth`), but
     `Normal k ↥M` is **not** found by `#synth`; `exact?` *does* close that goal, so a proof term
     exists — recover its name (candidates that failed: `normalClosure_normal`,
     `normalClosure_normal_iff`, `isNormal_normalClosure`, `normalClosure_le_iff`) or prove it
     from the universal property `AlgHom.fieldRange_le_normalClosure` (used in
     `Submission/NeukirchUchida/Local/PlaceFromValuation.lean`).  Then the recipe in the file's
     docstring (restriction map `AlgEquiv.restrictNormalHom`, `H := U.map ρ`, and
     `IntermediateField.fixingSubgroup_fixedField H` for the finite level) applies verbatim.  Mathlib's `IntermediateField.fixingSubgroup_fixedField` requires
     `[FiniteDimensional F E]`, which fails for `E = Ω`, so it must be proved from the Krull basis:
     `krullTopology_mem_nhds_one_iff` (used by `NK.Mine.continuous_autCongr`) gives a finite
     extension `E/k` with `fixingSubgroup E ⊆ U`; replacing `E` by its normal closure gives
     `V := fixingSubgroup M ⊆ U` with `M/k` finite **Galois** (normal, and `V ⊴ Gal(Ω/k)`).
     Then `M^U = fixedField U =: L`, `U/V` is the image of `U` in the *finite* group `Gal(M/k)`,
     and `IntermediateField.fixingSubgroup_fixedField` applied to `M/k` and the subgroup `U/V`
     (using `M^{U/V} = L`) gives `Gal(M/L) = U/V`; hence `fixingSubgroup L = U`.
   * **(3b) transfer along the resulting group isomorphism** `↥U ≃* Gal(Ω/L)` (an
     `AddEquiv` on `H1`, via `h1Transfer` once `IsHomeomorph` of the inclusion-induced iso is in
     hand — it is the identity map on a *closed* subgroup with the subspace topology, so
     `IsHomeomorph` follows from `U` being open hence closed), composed with item 2 at `L`
     (`Ω` is an algebraic closure of `L` ✓, `IsGalois L Ω` ✓).

### A remark on the vocabulary of the missing input

The left-hand side of the target is *already* the continuous cohomology of the profinite group
`D_A`: `H2loc` is defined through locally constant cochains on `G_k = Ω ≃ₐ[k] Ω` and
`H2locEquivH2_decomp` identifies it with `Work.AbsoluteKummer.H2 ↥(decomp k A) M`.  The delegated
statement may therefore be phrased with `H2loc`/`H0loc`/`HomH` directly (as in
`localTatePairing_deg02_of_hom_form`); what must **not** be used is `SSGRoute.PTExt.extH`
(`Abelian.Ext` in `Rep Coeff G`), which is *abstract* group cohomology: for the intended infinite
`D_A` its `H¹` is `Hom_abs(D_A, C) ≠ 0`, so Hilbert 90 fails there.

### The first piece of (B): Hilbert 90 at an open subgroup — what is missing

Target of the piece: for `U ≤ Ω ≃ₐ[k] Ω` **open** (`Ω` with `IsAlgClosure k Ω`),
`Subsingleton (Work.AbsoluteKummer.H1 ↥U (Additive ↥Ωˣ))` — Milne's class-formation axiom 1.1a for
`C = \bar Ω^×`.  Two things are missing and both are infrastructure, not mathematics:

1. **`H¹`-transfer along a *group* isomorphism — DONE.**  See
   `Submission/Work/SSGRoute/PT/H1Transfer.lean` (sorry-free):
   * `Work.SSGRoute.PT.cochainTransfer`, `.cochainTransfer_isLocallyConstant` (uses
     `IsHomeomorph.isOpenMap` to get `Continuous Φ.symm`, then
     `Work.AbsoluteKummer.IsLocallyConstant.comp`),
   * `.cochainTransfer_isCrossedHom`, `.cochainTransfer_d0`, `.z1Transfer`,
   * `.h1TransferAddHom`, `.h1TransferAddHom_mk`,
   * `.h1Transfer` — the headline: for `Φ : G' ≃* G` with `IsHomeomorph Φ`
     (`hΦ`) and `Ψ : M' ≃+ M` with `Ψ (g' • m') = Φ g' • Ψ m'` (`hΨ`),
     `H1 G' M' ≃+ H1 G M`.
   Note the hypothesis must be `IsHomeomorph Φ`, **not** `IsLocallyConstant Φ` (false for an
   injective homomorphism of profinite groups: trivial kernel would force `1` open).

2. **Hilbert 90 over an arbitrary `IsAlgClosure` field — DONE.**  See
   `Submission/Work/SSGRoute/PT/Hilbert90IsAlgClosure.lean` (sorry-free):
   * `Work.SSGRoute.PT.algEquivUnitsMapOfField` (+ `_coe` / `_mul` / `_one`),
   * `Work.SSGRoute.PT.instDistribMulActionAddUnitsOfField` — the general action of `Gal(E/F)`
     on `Additive (Units E)`, at **priority 100** so that the workspace's specialised instance
     `Work.AbsoluteKummer.instDistribMulActionAddUnits` still wins for `E = AlgebraicClosure k`,
   * `Work.SSGRoute.PT.algEquivUnitsMapOfField_comm` — `e.symm (σ u) = (e.autCongr⁻¹ σ) (e.symm u)`,
   * **`Work.SSGRoute.PT.hilbert90_H1_eq_zero_of_isAlgClosure`** — for `F Ω` with `IsGalois F Ω`,
     `IsAlgClosure F Ω`, `CharZero F`: `Subsingleton (H1 (Ω ≃ₐ[F] Ω) (Additive (Units Ω)))`, i.e.
     Milne's class-formation axiom 1.1a in the generality the target needs, obtained by
     `h1Transfer` along `(AlgEquiv.autCongr e)⁻¹` (`e := IsAlgClosure.equiv F (AlgebraicClosure F) Ω`,
     a homeomorphism by `NK.Mine.isHomeomorph_autCongr` / `isHomeomorph_symm`) from
     `Submission.hilbert90_H1_eq_zero`.
   * Two pieces of *generic* infrastructure were needed and are now also permanent:
     `H1Transfer.lean`'s universe-polymorphic `Work.SSGRoute.PT.cochainTransfer` chain (the
     workspace's groups had to be made `Type*`), and
     `Work.SSGRoute.PT.isLocallyConstant_comp_continuous` — the workspace's
     `Work.AbsoluteKummer.IsLocallyConstant.comp` forces both domains into the *same* universe,
     which blocks the transfer between `Gal(Ω/F)` and `Gal(\bar F/F)`; the restated version is
     universe-polymorphic.

3. Finally, `U = fixingSubgroup (fixedField U)` for open `U`: `IntermediateField.fixingSubgroup_fixedField`
   requires `[FiniteDimensional F E]`, which fails for `E = Ω`, so the general Galois
   correspondence is not available; it must be proved from the Krull basis: pick an open normal
   `V = fixingSubgroup M ⊆ U` with `M/k` finite Galois, and use the *finite* correspondence for
   `M/L`, `L = fixedField U`.

## Footer

`finrank_eq_of_nondegenerate_pairing` below is the (elementary, proved) linear-algebra step that
turns a non-degenerate pairing between two finite-dimensional `𝔽_p`-spaces into the equality of
their dimensions; it is the last step of the eventual proof, and is independent of the arithmetic.
-/

set_option linter.style.haveILetI false

open Classical
open scoped TensorProduct

namespace Work.SSGRoute.PT

noncomputable section

/-- A non-degenerate `𝔽_p`-bilinear pairing between two finite-dimensional spaces forces equal
dimensions: the two "kernels trivial" conditions make `V ↪ W^∨` and `W ↪ V^∨` injective. -/
theorem finrank_eq_of_nondegenerate_pairing {F : Type*} [Field F] {V W : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [Module.Finite F V] [Module.Finite F W]
    (Φ : V →ₗ[F] W →ₗ[F] F)
    (h1 : ∀ x, (∀ y, Φ x y = 0) → x = 0)
    (h2 : ∀ y, (∀ x, Φ x y = 0) → y = 0) :
    Module.finrank F V = Module.finrank F W := by
  have hinj1 : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    exact h1 x (fun y => by
      have := LinearMap.mem_ker.mp hx
      simp [this])
  have hle1 : Module.finrank F V ≤ Module.finrank F W := by
    have := LinearMap.finrank_le_finrank_of_injective hinj1
    rwa [Subspace.dual_finrank_eq] at this
  let Ψ : W →ₗ[F] Module.Dual F V :=
    LinearMap.mk₂ F (fun y x => Φ x y) (by intro y1 y2 x; simp)
      (by intro a y x; simp) (by intro y x1 x2; simp) (by intro a y x; simp)
  have hinj2 : Function.Injective Ψ := by
    intro y1 y2 hy
    have : ∀ x, Φ x (y1 - y2) = 0 := by
      intro x
      have h := congrArg (fun (g : Module.Dual F V) => g x) hy
      simp only [Ψ, LinearMap.mk₂_apply] at h
      have hsub : Φ x (y1 - y2) = Φ x y1 - Φ x y2 := by rw [map_sub]
      rw [hsub, h]
      simp
    have := h2 (y1 - y2) this
    rwa [sub_eq_zero] at this
  have hle2 : Module.finrank F W ≤ Module.finrank F V := by
    have := LinearMap.finrank_le_finrank_of_injective hinj2
    rwa [Subspace.dual_finrank_eq] at this
  exact le_antisymm hle1 hle2

/-- `H0loc` of a finite coefficient module is finite (it is a submodule).  In particular the right
hand side of `localTatePairing_deg02` is a finite `𝔽_p`-vector space, so
`finrank_eq_of_nondegenerate_pairing` applies to it. -/
theorem finite_H0loc (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N]
    [DistribMulAction (K ≃ₐ[k] K) N] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N] [Finite N]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Finite (Work.SSGRoute.H0loc p k Ω K N H) :=
  Finite.of_injective (Subtype.val) Subtype.val_injective

/-- `H0loc` of a finite coefficient module is a finite-dimensional `𝔽_p`-vector space. -/
theorem moduleFinite_H0loc (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N]
    [DistribMulAction (K ≃ₐ[k] K) N] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) N] [Finite N]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Module.Finite (ZMod p) (Work.SSGRoute.H0loc p k Ω K N H) :=
  Module.Finite.of_finite

section Closed

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- The decomposition group of a place of `Ω` over `k` is closed in the Krull topology (so that
the continuous-cohomology model bridge of `LTDDefs/H2locEquivH2.lean` applies to it). -/
theorem isClosed_decomp (A : ValuationSubring Ω) :
    IsClosed (SSGRoute.decomp k A : Set (Ω ≃ₐ[k] Ω)) := by
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  exact Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring (K := k) (K' := Ω) A

end Closed

section Bridge

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- **The `H²` model bridge at a decomposition group.**  The local `H²` of `LTDDefs/Basic.lean` of
`D_A = decomp k A` is the workspace's continuous-cohomology `H²` of the profinite group `D_A`
(`= G_{k_v}`, `k_v` the completion of `k` at the place below `A`), for the canonical `D_A`-action
through `res k K`. -/
def H2locEquivH2_decomp (A : ValuationSubring Ω) :
    letI : SMul ↥(SSGRoute.decomp k A) M := (SSGRoute.decompDistribMulAction K M A).toSMul
    letI : DistribMulAction ↥(SSGRoute.decomp k A) M := SSGRoute.decompDistribMulAction K M A
    Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A) ≃+
      Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) M :=
  letI : SMul ↥(SSGRoute.decomp k A) M := (SSGRoute.decompDistribMulAction K M A).toSMul
  letI : DistribMulAction ↥(SSGRoute.decomp k A) M := SSGRoute.decompDistribMulAction K M A
  Work.SSGRoute.LTDDefs.H2locAddEquivH2 p k Ω K M (SSGRoute.decomp k A)
    (isClosed_decomp k Ω A) (fun h m => SSGRoute.decomp_smul_eq_res K M A h m)

end Bridge

end


section H0locBridge

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M T : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]

/-- Currying `(M ⊗ T)^∨ ≃ₗ (M → T^∨)` over `𝔽_p`. -/
noncomputable def curryMT :
    DualMod p (M ⊗[ZMod p] T) ≃ₗ[ZMod p] (M →ₗ[ZMod p] DualMod p T) :=
  (TensorProduct.lift.equiv (RingHom.id (ZMod p)) M T (ZMod p)).symm

@[simp] theorem curryMT_apply (ψ : DualMod p (M ⊗[ZMod p] T)) (m : M) (t : T) :
    curryMT p M T ψ m t = ψ (m ⊗ₜ[ZMod p] t) := rfl

/-- The `H`-equivariant `𝔽_p`-linear maps `M → T^∨` (the fixed points of the `H`-action on `M^∨`). -/
noncomputable def HomH (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Submodule (ZMod p) (M →ₗ[ZMod p] DualMod p T) where
  carrier := {φ | ∀ (g : Ω ≃ₐ[k] Ω), g ∈ H → ∀ m : M,
      φ (SSGRoute.res k K g • m) = SSGRoute.res k K g • (φ m)}
  zero_mem' := by
    intro g _ m
    simp
  add_mem' := by
    intro φ ψ hφ hψ g hg m
    rw [LinearMap.add_apply, hφ g hg m, hψ g hg m, LinearMap.add_apply, smul_add]
  smul_mem' := by
    intro c φ hφ g hg m
    rw [LinearMap.smul_apply, hφ g hg m, LinearMap.smul_apply,
      ← smul_comm (SSGRoute.res k K g) c (φ m)]


/-- The forward linear map `H⁰(H, (M ⊗ T)^∨) → Hom_H(M, T^∨)`: currying. -/
noncomputable def h0locToHomH (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    H0loc p k Ω K (DualMod p (M ⊗[ZMod p] T)) H →ₗ[ZMod p] HomH p k Ω K M T H where
  toFun ψ := ⟨curryMT p M T ψ.1, by
    intro g hg m
    ext t
    rw [curryMT_apply, DualMod.dualSMul_apply, curryMT_apply]
    have hfix : SSGRoute.res k K g • ψ.1 = ψ.1 := ψ.2 g hg
    have h1 := congrArg (fun (f : DualMod p (M ⊗[ZMod p] T)) =>
      f ((SSGRoute.res k K g • m) ⊗ₜ[ZMod p] t)) hfix
    simp only [DualMod.dualSMul_apply] at h1
    rw [← h1]
    congr 1
    simp⟩
  map_add' ψ χ := Subtype.ext (map_add (curryMT p M T) ψ.1 χ.1)
  map_smul' c ψ := Subtype.ext (map_smul (curryMT p M T) c ψ.1)

/-- **The right-hand side of the degree-`0`/`2` local Tate duality is a `Hom`-module.**  For every
subgroup `H ≤ G_k = Ω ≃ₐ[k] Ω`, the `H`-fixed points of the dual `(M ⊗ T)^∨` are the
`H`-equivariant `𝔽_p`-linear maps `M → T^∨`:

  `H⁰(H, (M ⊗ T)^∨) ≃ₗ[𝔽_p] (M →ₗ[𝔽_p] T^∨)^H`.

With `T` the cyclotomic dual of `μ_p` and `D_A = decomp k A`, this turns the right-hand side of
`localTatePairing_deg02` into the standard `Hom_{D_A}(M, μ_p)`. -/
noncomputable def h0loc_dualMod_tensor (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    H0loc p k Ω K (DualMod p (M ⊗[ZMod p] T)) H ≃ₗ[ZMod p] HomH p k Ω K M T H := by
  refine LinearEquiv.ofBijective (h0locToHomH p k Ω K M T H) ⟨?_, ?_⟩
  · intro ψ χ h
    have h1 : curryMT p M T ψ.1 = curryMT p M T χ.1 := Subtype.ext_iff.mp h
    exact Subtype.ext ((curryMT p M T).injective h1)
  · intro φ
    refine ⟨⟨(curryMT p M T).symm φ.1, ?_⟩, ?_⟩
    · intro g hg
      apply LinearMap.ext
      intro x
      have hψ : ∀ (m' : M) (t' : T),
          (curryMT p M T).symm φ.1 (m' ⊗ₜ[ZMod p] t') = φ.1 m' t' := by
        intro m' t'
        rw [← curryMT_apply, LinearEquiv.apply_symm_apply]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, smul_add, ha, hb]
      | tmul m t =>
        rw [DualMod.dualSMul_apply,
          show (SSGRoute.res k K g)⁻¹ • (m ⊗ₜ[ZMod p] t)
            = ((SSGRoute.res k K g)⁻¹ • m) ⊗ₜ[ZMod p] ((SSGRoute.res k K g)⁻¹ • t) from by simp,
          hψ, hψ]
        have hφ := φ.2 g⁻¹ (H.inv_mem hg) m
        rw [show SSGRoute.res k K g⁻¹ = (SSGRoute.res k K g)⁻¹ from map_inv _ _] at hφ
        rw [hφ, DualMod.dualSMul_apply]
        simp
    · exact Subtype.ext (LinearEquiv.apply_symm_apply (curryMT p M T) φ.1)

end H0locBridge



/-! ## Auxiliary lemmas on the two sides of the target

The lemmas in this section are used by the assembly of `localTatePairing_deg02` (and by the rest of
the `PT` lane).  They are independent of the arithmetic input, which is the `Hom`-form of local
Tate duality recorded in `localTatePairing_deg02_of_hom_form`. -/

section Aux

/-- **The places quantified over by `localTatePairing_deg02` are the nontrivial valuation subrings
of `Ω`** — i.e. the places of `Ω` over a *finite* (non-archimedean) prime of `k`.

If the restriction `A.comap (algebraMap k Ω)` of `A` to `k` is the trivial valuation subring then,
`Ω/k` being algebraic (`IsAlgClosure k Ω`), `A` itself is the trivial valuation subring
(`Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top`: a valuation
subring containing a field is everything if the ambient field is algebraic over that field).

In particular `IsFinPlace k A` does **not** range over archimedean places: a `ValuationSubring` of
`Ω` is by definition (Mathlib) the unit ball of an ultrametric valuation `Ω → Γ₀`, so archimedean
places are not represented by `ValuationSubring`s at all, and the only `A` with
`A.comap (algebraMap k Ω) = ⊤` is `A = ⊤`.  (This is the point left open in the design note; it is
what makes Milne, *Arithmetic Duality Theorems*, §I.2 applicable to every `A` in the quantifier.) -/
theorem isFinPlace_iff_ne_top (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) : SSGRoute.IsFinPlace k A ↔ A ≠ ⊤ := by
  refine ⟨fun h hA => h ?_, fun h hcomap => h ?_⟩
  · rw [hA]
    ext x
    simp [ValuationSubring.coe_comap]
  · exact Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top A
      (inferInstance : Algebra.IsAlgebraic k Ω) hcomap

/-- **`𝔽_p`-dimension is an invariant of the underlying additive group among finite `𝔽_p`-vector
spaces.**  Used to transfer `finrank` across the additive equivalences of the models (e.g.
`H2locEquivH2_decomp`, which is only `≃+`). -/
theorem finrank_eq_of_addEquiv (p : ℕ) [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    [Finite V] [Finite W] (e : V ≃+ W) :
    Module.finrank (ZMod p) V = Module.finrank (ZMod p) W := by
  haveI := Fintype.ofFinite V
  haveI := Fintype.ofFinite W
  have hV := Module.card_eq_pow_finrank (K := ZMod p) (V := V)
  have hW := Module.card_eq_pow_finrank (K := ZMod p) (V := W)
  rw [ZMod.card] at hV hW
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e.toEquiv
  have hpow : p ^ Module.finrank (ZMod p) V = p ^ Module.finrank (ZMod p) W := by
    rw [← hV, ← hW, hcard]
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hpow

/-- **The `𝔽_p`-module structure on the continuous cohomology `H²(G, M)`** of an `𝔽_p`-module `M`
of exponent `p`: `H²` is a quotient of an additive subgroup of the `𝔽_p`-module of `2`-cochains,
so it has exponent `p` and `𝔽_p`-module structures on such a group are unique.  (The underlying
type of `Work.AbsoluteKummer.H2` is only an `AddSubgroup` quotient, so the structure has to be
installed by hand.) -/
noncomputable instance instModuleH2 (p : ℕ) {G : Type*} [Group G] [TopologicalSpace G]
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] :
    Module (ZMod p) (Work.AbsoluteKummer.H2 G M) :=
  QuotientAddGroup.zmodModule (n := p) (G := ↥(Work.AbsoluteKummer.Z2 G M))
    (H := (Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype)
    (fun x => by
      have hx : (p : ℕ) • x = 0 := by
        refine Subtype.ext ?_
        change (p : ℕ) • (x : G × G → M) = (0 : G × G → M)
        rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) p (x : G × G → M), ZMod.natCast_self,
          zero_smul]
      rw [hx]
      exact (Work.AbsoluteKummer.B2 G M).zero_mem)

end Aux

section LeftHandSideBridge

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- **The right-hand side of the target at `M = DualMod p T` (`≅ μ_p`) is one-dimensional.**

For a cyclotomic dual `T` (`hT : IsCyclotomicDual p T (res k K) ζ`), the module
`M = DualMod p T` is a line, and *every* `𝔽_p`-linear endomorphism of a line on which
`Gal(K/k)` acts is automatically equivariant (a linear action on a line is by scalars, and scalars
commute with linear maps).  Hence

  `Hom_{D_A}(DualMod p T, T^∨) = End_{𝔽_p}(DualMod p T) = 𝔽_p`,

and by `h0loc_dualMod_tensor` the same holds for the right-hand side of the target's instance
`M = DualMod p T`, namely `H⁰(D_A, DualMod p (DualMod p T ⊗ T))`, whose `𝔽_p`-dimension is `1`.

This is the "easy half" of the `M = μ_p` base case of the target; the hard half is
`dim H²(D_A, μ_p) = 1`, i.e. `Br(k_v)[p] = ℤ/p` (the invariant map of local class field theory). -/
theorem finrank_H0loc_dual_self
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) :
    Module.finrank (ZMod p)
      (H0loc p k Ω K (DualMod p (DualMod p T ⊗[ZMod p] T)) (SSGRoute.decomp k A)) = 1 := by
  have hD : Module.finrank (ZMod p) (DualMod p T) = 1 := by rw [finrank_dualMod, hT.1]
  haveI : Finite T := finite_of_finrank_eq_one (p := p) T hT.1
  haveI : Finite (DualMod p T) := finite_dualMod (p := p) T
  haveI : Module.Finite (ZMod p) (DualMod p T) := Module.Finite.of_finite
  have htop : HomH p k Ω K (DualMod p T) T (SSGRoute.decomp k A) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro φ g _ m
    haveI : Module.Free (ZMod p) (DualMod p T) := Module.Free.of_divisionRing (ZMod p) _
    obtain ⟨b⟩ := (finrank_eq_one_iff (K := ZMod p) (V := DualMod p T) Unit).mp hD
    have hspan : ∀ w : DualMod p T, ∃ d : ZMod p, d • b () = w := by
      intro w
      exact ⟨b.repr w (), by rw [← b.sum_repr w]; simp⟩
    obtain ⟨c, hc⟩ := hspan (SSGRoute.res k K g • b ())
    have hscalar : ∀ w : DualMod p T, SSGRoute.res k K g • w = c • w := by
      intro w
      obtain ⟨d, hd⟩ := hspan w
      rw [← hd, smul_comm (SSGRoute.res k K g) d (b ()), ← hc, smul_comm c d (b ())]
    rw [hscalar m, map_smul, hscalar (φ m)]
  rw [(h0loc_dualMod_tensor p k Ω K (DualMod p T) T (SSGRoute.decomp k A)).finrank_eq, htop,
    finrank_top, Module.finrank_linearMap, hD, mul_one]

/-- **The left-hand side of the target may be computed in either model of the continuous
cohomology of `D_A`**: the locally constant cochain model `H2loc` of `LTDDefs/Basic` and the
workspace's `Work.AbsoluteKummer.H2` have the same cardinality (and, when finite, the same
`𝔽_p`-dimension, by `finrank_eq_of_addEquiv`). -/
theorem card_H2loc_eq_card_H2 (A : ValuationSubring Ω) :
    letI : SMul ↥(SSGRoute.decomp k A) M := (SSGRoute.decompDistribMulAction K M A).toSMul
    letI : DistribMulAction ↥(SSGRoute.decomp k A) M := SSGRoute.decompDistribMulAction K M A
    Nat.card (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
      Nat.card (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) M) := by
  letI : SMul ↥(SSGRoute.decomp k A) M := (SSGRoute.decompDistribMulAction K M A).toSMul
  letI : DistribMulAction ↥(SSGRoute.decomp k A) M := SSGRoute.decompDistribMulAction K M A
  exact Nat.card_congr (H2locEquivH2_decomp p k Ω K M A).toEquiv

end LeftHandSideBridge

/-- **The target, reduced to its `Hom`-form.**  By `h0loc_dualMod_tensor` the right-hand side of
`localTatePairing_deg02` is canonically `Hom_{D_A}(M, T^∨)` (`T^∨ = μ_p` under `IsCyclotomicDual`),
so the target is *equivalent* to the standard `Hom`-form of local Tate duality:

  `dim H²(D_A, M) = dim Hom_{D_A}(M, DualMod p T)`   for every finite `M`.

This lemma records that reduction: it is the last formal step of the assembly, and identifies
exactly the arithmetic input still missing. -/
theorem localTatePairing_deg02_of_hom_form
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (h : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (HomH p k Ω K M T (SSGRoute.decomp k A))) :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) := by
  intro A hA M _ _ _ _ _
  rw [h A hA M]
  exact (h0loc_dualMod_tensor p k Ω K M T (SSGRoute.decomp k A)).symm.finrank_eq


/-- **The right-hand side of the target is a finite-dimensional `𝔽_p`-space** (so that
`finrank_eq_of_nondegenerate_pairing` applies to it once the Tate pairing is available). -/
theorem moduleFinite_H0loc_dualMod_tensor
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M T : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      [AddCommGroup T] [Module (ZMod p) T]
      [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Module.Finite (ZMod p)
      (Work.SSGRoute.H0loc p k Ω K (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) H) := by
  haveI : Finite (M ⊗[ZMod p] T) := finite_tensor (p := p) M T
  haveI : Finite (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    finite_dualMod (p := p) (M ⊗[ZMod p] T)
  exact moduleFinite_H0loc p k Ω K (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) H

end Work.SSGRoute.PT
