import Submission.NK.NUV2.LCLeaves
import Submission.NK.BrauerTwist.Hasse
import Submission.NK.HasseTwist.Localisation
import Submission.NK.BrauerTwist.Main
import Submission.NK.LocalCFT.Brauer.Basic

/-!
# The Albert–Brauer–Hasse–Noether input of the place correspondence, for odd `p`

This file isolates — as an *exact statement* — the local–global arithmetic input that Neukirch's
containment argument (leaf `NK.NUV2.DecompContainment` of `NK.NUV2.LCAll0`) consumes.  It is
stated in the `μ_p`-twisted vocabulary of `Submission/Work/BrauerTwist/` (the coefficient-correct
one: `H2Twist p U` is the profinite colimit `H²(U, μ_p)` and `H2Twist.loc p U` the localisation
`H²(U, μ_p) → ∏_A H²(U ⊓ D_A, μ_p)`), and it has two halves:

* **injectivity** (`ABHNInjectivity`) — *the Hasse principle in the limit*: for a closed subgroup
  `U ≤ G_K` of the absolute Galois group of a number field `K` which is topologically isomorphic to
  the absolute Galois group of a `p`-adic field `κ` containing `μ_p` (a completion of a number
  field), every class of `H²(U, μ_p)` whose local component vanishes at *every* place of `K'` over
  a finite prime of `K` is zero.  Classically this is Albert–Brauer–Hasse–Noether (Hasse 1933,
  Satz 24) for the (possibly infinite) fixed field of `U`, in the `κ`-labelled form.  The
  `κ`-labelling is **not** cosmetic: without it the statement fails, because
  `Br(F)[p] → ∏_v Br(F_v)[p]` sees only the *finite* places while a class can be ramified only at
  the archimedean ones (the quaternion class `(-1,-1)` over `ℚ(√2)` at `p = 2`) — this is the
  counterexample of `Submission/Work/HassePrinciple/README.md` §13.1.  Restricting `U` to a group
  isomorphic to a local absolute Galois group excludes it.  For odd `p` the archimedean defect is
  absent (`Br(ℝ)[p] = 0`), which is why the prime is assumed odd.

* **surjectivity** (`ABHNSurjectivity`) — Neukirch's *modified surjectivity* (Neukirch,
  Invent. Math. **6** (1969), Theorem 1; Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
  (9.2.1)), in the guarded form `NK.HasseTwist.NeukirchH2modifiedsurjAt` already present in the
  workspace: at a prime `𝔭` carrying a non-zero local component the localisation to the product over
  the places over `𝔭` is surjective.  Its classical proof is the `Σ_v inv_v = 0` exactness of global
  class field theory together with the freedom to adjust the local component at a place that is not
  in the index set (Ivanov, arXiv:1309.2801, proof of Proposition 3.5: *"the sequence
  `H²(U, μ_{p^∞}) → ⊕_{q ∈ T} H²(D_q, μ_{p^∞}) → 0` is exact by [NSW] 9.2.1 … since there are still
  non-archimedean primes which do not enter the index set of the direct sum"*).

Both halves follow from the global fundamental class `NK.GlobalCFTdeep.FundamentalClassElement`
(`hFC`): injectivity from `H¹(G, C_L) = 0` (`NK.GlobalCFTdeep.H1All`) together with Shapiro's
lemma and the idèle class group exact sequence; surjectivity from the fundamental class, i.e. from
the identification of the cokernel of the localisation with `H²(Γ, C_L) ≅ ℤ/[L:K]` ("`Σ inv = 0`
is the only relation").

## The statements

* `NK.NUV2.ABHNInjectivity`, `NK.NUV2.ABHNSurjectivity` — the two halves;
* `NK.NUV2.ABHN` — the bundle;
* `NK.NUV2.abhn_injectivity`, `NK.NUV2.abhn_surjectivity`, `NK.NUV2.abhn` — the producers
  from `hFC`.

Everything is in `Type 0`, matching `NK.NUV2.LCAll0`.
-/

namespace NK.NUV2

open IsDedekindDomain
open NK.BrauerTwist

/-- **Injectivity half of ABHN for odd `p`** (the Hasse principle in the limit).

Let `K` be a number field with separable closure `K'`, `L` a number field with a finite prime `𝔮`,
`κ = 𝔮.adicCompletion L` a `p`-adic field containing `μ_p`, and `p` an odd prime.  Let `U ≤ G_K` be
a closed subgroup topologically isomorphic to `Gal(κ̄/κ)`.  Then a class of `H²(U, μ_p)` all of whose
local components (at the places of `K'` over the finite primes of `K`) vanish is zero. -/
def ABHNInjectivity : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (K' : Type) [Field K'] [Algebra K K']
    [IsSepClosure K K'] (L : Type) [Field L] [NumberField L]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L)) {p : ℕ},
    p.Prime → p ≠ 2 →
    (∃ ζ : 𝔮.adicCompletion L, IsPrimitiveRoot ζ p) →
    ∀ (U : Subgroup Gal(K'/K)), IsClosed (U : Set Gal(K'/K)) →
      Nonempty (↥U ≃ₜ* Gal(SeparableClosure (𝔮.adicCompletion L) / 𝔮.adicCompletion L)) →
      ∀ x : H2Twist (K := K) (K' := K') p U,
        (∀ A : OverFinitePrime K K', H2Twist.loc p U x A = 0) → x = 0

/-- **Surjectivity half of ABHN for odd `p`**: Neukirch's modified surjectivity (NSW (9.2.1)).

For a number field `K` with separable closure `K'` and a `p`-adic field `κ = 𝔮.adicCompletion L`
containing `μ_p` (`p` odd), the localisation of `H²(U, μ_p)` onto the product of the local groups over
a prime is surjective, at any prime carrying a non-zero local component (the guarded form
`NK.HasseTwist.NeukirchH2modifiedsurjAt`). -/
def ABHNSurjectivity : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (K' : Type) [Field K'] [Algebra K K']
    [IsSepClosure K K'] (L : Type) [Field L] [NumberField L]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L)) {p : ℕ},
    p.Prime → p ≠ 2 →
    (∃ ζ : 𝔮.adicCompletion L, IsPrimitiveRoot ζ p) →
    NK.HasseTwist.NeukirchH2modifiedsurjAt p K K'
      (𝔮.adicCompletion L) (SeparableClosure (𝔮.adicCompletion L))

/-- **The local Brauer non-vanishing at a `p`-adic field containing `μ_p`** (trivial `ℤ/p`
coefficients): `H²(G_κ, ℤ/p) ≠ 0`.

For `κ = 𝔮.adicCompletion L` a `p`-adic field containing `μ_p`, the coefficient modules `ℤ/p` and
`μ_p` coincide, so this is the Kummer/Brauer computation `H²(G_κ, μ_p) = Br(κ)[p] ≅ ℤ/p`
(Serre, *Local Fields* XII–XIV; NSW (7.1.7)): it follows from local class field theory, which the
hypothesis `hKC` supplies at the completion (`NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion`).
This is the local input that supplies the non-zero class of `decompContainment`. -/
def LocalBrauerOdd : Prop :=
  ∀ (L : Type) [Field L] [NumberField L]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L)) {p : ℕ},
    p.Prime → (∃ ζ : 𝔮.adicCompletion L, IsPrimitiveRoot ζ p) →
    NK.LocalCFT.LocalH2Nonvanishing p (𝔮.adicCompletion L)
      (SeparableClosure (𝔮.adicCompletion L))

/-- **The local Brauer computation in the `μ_p`-twisted form**: `H²(G_κ, μ_p) ≅ ℤ/p` for a
`p`-adic field `κ` containing `μ_p` (`NK.BrauerTwist.LocalFieldBrauerCyclic`), i.e.
`Br(κ)[p] ≅ ℤ/p`.  Both halves (the equivalence with `ZMod p` and the existence of a non-zero
class) are included. -/
def LocalBrauerCyclicOdd : Prop :=
  ∀ (L : Type) [Field L] [NumberField L]
    (𝔮 : HeightOneSpectrum (NumberField.RingOfIntegers L)) {p : ℕ},
    p.Prime → (∃ ζ : 𝔮.adicCompletion L, IsPrimitiveRoot ζ p) →
    NK.BrauerTwist.LocalFieldBrauerCyclic p (𝔮.adicCompletion L)
      (SeparableClosure (𝔮.adicCompletion L))

/-- **The local–global arithmetic input (ABHN) of the place correspondence, for odd `p`.**

The two *local* halves and the *injectivity* half are the ones for which producers exist or are
being built here; the *surjectivity* half `ABHNSurjectivity` (Neukirch's modified surjectivity,
NSW (9.2.1)) is stated above and is the separate -- and harder -- producer
`NK.NUV2.LC.SurjTwo` in the `p = 2`, trivial-coefficient form consumed by
`NK.NUV2.DecompContainment`; it is deliberately *not* a field of this bundle so that the bundle
records exactly the part that is assemble-able from the producers of this directory. -/
structure ABHN : Prop where
  /-- the Hasse principle in the limit -/
  injective : ABHNInjectivity
  /-- the local Brauer non-vanishing `H²(G_κ, ℤ/p) ≅ ℤ/p` -/
  localBrauer : LocalBrauerOdd
  /-- the local Brauer computation in the `μ_p`-twisted form -/
  localBrauerCyclic : LocalBrauerCyclicOdd

end NK.NUV2

/-!
## Proof notes for the two halves (for the prover of `abhn_injectivity` / `abhn_surjectivity`)

Both halves are consequences of the *finite-level* exactness of the idèle class group, which the
workspace already has in the form of
`NK.GlobalCFTdeep.H1All.subsingleton_groupCohomology_one_ideleClassGroup` together with the
fundamental class `hFC`.  Concretely, for a finite Galois extension `L/K` of number fields with
`Γ = Gal(L/K)` the exact sequence `1 → Lˣ → 𝕀_L → C_L → 1` of `Γ`-modules gives (Shapiro for
`𝕀_L`, `H¹(Γ, C_L) = 0`)

  `H²(Γ, Lˣ) ↪ ⊕_w H²(Γ_w, L_wˣ)`     (injectivity: `H¹(C_L) = 0` + Shapiro),

and the cokernel of this localisation is `H²(Γ, C_L) ≅ ℤ/[L:K]` (Hasse's fundamental class,
`hFC`/Tate), the local fundamental classes composing to the global one, so that

  `image(⊕_w H²(Γ_w, L_wˣ) ← H²(Γ, Lˣ)) = ker(⊕_w H²(Γ_w, L_wˣ) → ℤ/[L:K])`
  = "`Σ_w inv_w = 0`",   and in particular the image lies in the **direct sum** (finite support).

### Injectivity

Let `x : H2Twist p U` be represented at a finite Galois level `L/K` by `x_L` (`H2Twist.ofLevel`).
For each place `A` of `K'` over a finite prime of `K`, `H2Twist.loc p U x A = 0` says (by
`NK.HasseTwist.loc_ofLevel_eq_zero_iff`) that the image of `x_L` in the local colimit dies after
inflation to some larger level `L_A`.  Two inputs finish the proof:

1. **finite support**: the localisation of the level class `x_L` is non-zero at only finitely many
   places `A` — because the level localisation lands in the *direct sum* over the places of `L`
   (the "`Σ inv = 0`" exactness above; equivalently: a class of `Br(L/(L ⊓ K'^U))` is ramified at
   only finitely many places).  Hence only finitely many `A` occur in the set `{L_A}`;
2. **level-wise injectivity**: at a single level `L''` containing `L` and all the finitely many
   `L_A`, the level class `levelMap x_L` has *all* its localisations zero, so it is zero by the
   level-wise form of the Hasse principle — which at a finite level is the `μ_p`-coefficient
   statement `H²(Γ, μ_p(L)) → ∏_w H²(Γ_w, μ_p(L))` injective.  The latter follows from the `Lˣ`
   statement above together with the detection of its Kummer correction
   (`1 → μ_p(L) → Lˣ → Lˣ^p → 1`, `H¹(Γ_w, L_wˣ) = 0` makes the local connecting maps injective,
   and `H¹(Γ, Lˣ^p) ≅ (Mˣ/Mˣ^p)/μ_p(M)`, `M = L^Γ`, is the group of degree-`p` extensions `N/M`
   with `N ⊆ L`; "every place of `M` splits completely in `N`" is detected locally, and an abelian
   extension all of whose places split completely is trivial, by the *surjectivity of the Artin
   map* — which `hFC` supplies).

### Surjectivity

`NeukirchH2modifiedsurjAt` at a prime `𝔭` carrying a non-zero local component: the classical proof
is the same `Σ inv = 0` exactness — a tuple of local classes over a *finite* set of places `S` can
be adjusted at one further place (which exists, since the index set is a proper subset of the
places over `𝔭`) to have `Σ inv = 0`, hence lies in the image of the global localisation; the
"further place" is exactly what makes the *guarded* form (the one stated here) the correct one
(NSW (9.2.1); Ivanov, arXiv:1309.2801, proof of Proposition 3.5).
-/

/-!
## Audit note (orchestrator-visible): the surjectivity half needs the correct NSW form

A prover of `ABHNSurjectivity` returned the following finding, which is worth recording because it
identifies the exact missing piece.

`NeukirchH2modifiedsurjAt` (the guarded *product* form over all places over a prime) is, given the
local Brauer computation and the disjointness of decomposition groups of distinct places
(`NK.LocalDecomposition.stabSubgroup_inf_eq_bot_of_ne`), **equivalent to Neukirch's
indecomposedness conclusion** `H ≤ D_A` — i.e. it is a reformulation of the containment itself, not
an intermediate input.  The classical *input* (NSW (9.2.1), Ivanov `eq:NeukirchH2modifiedsurj`) is
instead a statement about the localisation onto the **direct sum over a finite set of places over a
fixed rational prime that misses at least one place**, and its proof needs the global invariant
machinery:

* the canonical local invariant maps `inv_v : Br(K_v) → ℚ/ℤ` with their normalisations, and
* Hilbert's reciprocity law `Σ_v inv_v = 0`, i.e. the fundamental exactness
  `0 → Br(K) → ⊕_v Br(K_v) → ℚ/ℤ → 0` (Milne, *CFT*, VIII.4.2),

neither of which is formalised anywhere in the workspace (`GlobalCFTdeep/README.md` §16.3/§17
records the same).  `hFC` is only the *existential* fundamental-class statement; it yields the
reciprocity isomorphism `C_K ⧸ N C_L ≃* Gal(L/K)^{ab}` and Tate's theorem, hence
`H²(Γ, C_L) ≅ ℤ/[L:K]`, but not the invariant maps themselves.

**The formulation that is both provable from `hFC` and sufficient for the rank count** is the
finite-level one: for a finite Galois extension `L/K` of number fields with `Γ = Gal(L/K)`, the
localisation `H²(Γ, Lˣ) → ∏_w H²(Γ_w, L_wˣ)` has image of cardinality
`|∏_w H²(Γ_w, L_wˣ)| ⧸ [L:K]`: the cokernel is `H²(Γ, C_L) ≅ ℤ/[L:K]` (`hFC` + Shapiro), because
`H³(Γ, Lˣ) = 0` (Tate) makes the connecting map `H²(Γ, 𝕀_L) → H²(Γ, C_L)` surjective.  At a finite
level the "sum of invariants" map is, concretely, the natural map `⊕_w ℤ/n_w → ℤ/n` induced by the
identifications `H²(Γ_w, L_wˣ) ≅ ℤ/n_w`, `H²(Γ, C_L) ≅ ℤ/n` (`n = [L:K]`, `n_w = [L_w:K_𝔭]`), so
that this form needs no abstract invariant map.
-/

/-!
## Audit note (orchestrator-visible): what does *not* give the rank count

Two devices were tried for Neukirch's rank count ("at most one non-trivial local group over `𝔭`")
and both fail/have a defect; recording them prevents a wasted subproject.

1. **The product form is the goal.**  Given `CardGlobalTwo` (`|H²(H, Z/2)| = 2` for the labelled
   `H`) and the disjointness of the decomposition groups of distinct places, the statement that the
   localisation `H²(H, Z/2) → ∏_{A | 𝔭} H²(H ⊓ D_A, Z/2)` is surjective *is equivalent* to `H ≤ D_A`
   for some `A | 𝔭`: the product is the whole index set `localGroupSubgroupsOver H 𝔭` (infinite),
   the source has two elements, and if `H ⊓ D_A ≠ ⊥` then `H²(H ⊓ D_A, Z/2) = Z/2`, so two distinct
   non-trivial factors already make the target have `≥ 4` elements (and the conclusion gives the
   converse).  Hence `NK.NUV2.LC.SurjTwo` (and the sibling `NK.NUV2.ABHNSurjectivity`) cannot be
   an *intermediate* input; only the classical *finite-support* form (NSW (9.2.1), the localisation
   onto the direct sum over a finite set of places **missing at least one place**, with the
   invariant-sum `Σ_v inv_v = 0` relation) is, and that requires the invariant maps
   `inv_v : Br(K_v) → ℚ/ℤ` and Hilbert reciprocity, formalised nowhere here.

2. **The transfer argument is not sufficient.**  For a non-zero local component at `A` one might
   hope to use `cor ∘ res = ·[H : H ⊓ D_A]` on `H²(H, Z/2) = Z/2` to force the index to be odd and
   then derive a contradiction from two such places (their intersection would have odd index, hence
   be non-trivial, contradicting disjointness).  This does not go through: for `V = H ⊓ D_A` the
   transfer formula only says that **odd index implies `res ≠ 0`**; it gives no constraint in the
   direction needed (`res ≠ 0` does not force the index to be odd or finite, and the restriction can
   be non-zero for `V` of infinite index in `H`, e.g. for `V` the inertia subgroup inside the
   labelled local group).  Hence the rank count genuinely requires the classical surjectivity input
   of item 1 and cannot be replaced by the transfer.
-/

/-!
## RULE (project lead, 2026-09-24) and the route for the two ABHN producers

**RULE: there are NO licensed inputs and NO designated residuals.**  Every named `Prop` in this
workspace that is TRUE must be *proved*, by building the missing mathematics.  `declare_false` is
ONLY for a statement that is actually false, with a counterexample; "true but not derivable from
what is on disk" means BUILD IT, never `declare_false`.

### The finite-level localisation exactness (the "`Σ_v inv_v = 0`" statement, without invariant maps)

Let `L/K` be a finite Galois extension of number fields, `Γ = Gal(L/K)`.  From the exact sequence of
`Γ`-modules `1 → Lˣ → 𝕀_L → C_L → 1` one gets, using Shapiro for the idèles
(`H²(Γ, 𝕀_L) ≅ ∏_w H²(Γ_w, L_wˣ)`, the workspace's `NK.HassePrinciple.ideleLoc`) the **exact**
sequence

  `H²(Γ, Lˣ) → H²(Γ, 𝕀_L) → H²(Γ, C_L) → H³(Γ, Lˣ)`.

`H³(Γ, Lˣ) = 0` is Tate's theorem for the extension `L/K` (it follows from the fundamental class
`hFC` through `NK.GlobalCFTdeep.cohomologicalFieldAxiom_of_fundamentalClassElement`), so the
connecting map `H²(Γ, 𝕀_L) → H²(Γ, C_L)` is **surjective**, and therefore

  `[∏_w H²(Γ_w, L_wˣ) : image of the localisation] = |H²(Γ, C_L)| = [L : K]`.

This is the rank input ("`Σ_v inv_v = 0` is the only relation") in a form that needs **no** abstract
invariant map: the "sum of invariants" *is* the connecting map.  Note that
`NK.GlobalCFTdeep.hbnUnits` already supplies the *injectivity* half of this localisation for every
finite Galois extension (unconditionally).

### From the finite levels to the labelled subgroup `H ≅ Gal(κ'/κ)`

`H2Profinite 2 H` is the filtered colimit of the level cohomologies over the finite Galois levels
`L/K`; a class has a representative `x_L` at some level.  Two facts finish:

* **finite support**: the localisation of `x_L` is non-zero at only finitely many places (its image
  lies in the *direct sum* over the places of `L`, which is what the exactness above gives at the
  level, together with the vanishing of the invariants outside the ramified places);
* **level-wise completeness**: at a single level `L''` containing `L` and the finitely many levels
  at which the individual localisations die, `levelMap x_L` has *all* localisations zero, so it is
  zero by the level-wise form (for `Z/2` coefficients: the Kummer correction is detected locally,
  because a non-zero Kummer class is a degree-`2` extension `N/M` with `N ⊆ L`, and an abelian
  extension all of whose places split completely is trivial by the *surjectivity of the Artin map* —
  which `hFC` supplies).
-/

/-!
## STATE (2026-09-24)

Proved in this directory:

* `NK.NUV2.ABHN.local_brauer_cyclic` (`local_brauer_cyclic.lean`) —
  `NK.NUV2.LocalBrauerCyclicOdd`: `H²(G_κ, μ_p) ≅ ℤ/p` (`Br(κ)[p] ≅ ℤ/p`) for
  `κ = 𝔮.adicCompletion L ⊇ μ_p`, in the `μ_p`-twisted form.  (Proved from the local fundamental
  class, Hilbert 90 and the Kummer comparison; `hKC` is not consumed.)
* `NK.NUV2.ABHN.local_brauer_trivial` (`local_brauer_trivial.lean`) — `NK.NUV2.LocalBrauerOdd`:
  the trivial-`ℤ/p` form `NK.LocalCFT.LocalH2Nonvanishing`.
* `NK.NUV2.ABHN.transport_homeomorph` (`transport_homeomorph.lean`) — the transport of the local
  Brauer non-vanishing along a *continuous* isomorphism `↥H ≃ₜ* Gal(κ'/κ)` of profinite groups,
  with the openness hypotheses of `NK.LocalCFT.Brauer.exists_ne_zero_H2Profinite_of_mulEquiv`
  *derived* from continuity (no Nikolov–Segal).
* `NK.NUV2.abhn_of` (`Assembly.lean`) — the bundle `NK.NUV2.ABHN` from its three producers.

Pending (delegated, in progress): `NK.NUV2.ABHN.abhn_injectivity` (the Hasse principle in the
limit, odd `p`, `μ_p`-twisted) and, for the containment, the two `p = 2`, trivial-coefficient
producers `NK.NUV2.LC.hasse_two_of_fc` (injectivity) and `NK.NUV2.LC.surjTwo_of_fc`
(surjectivity, i.e. NSW (9.2.1) in the guarded product form consumed by
`NK.NUV2.LC.decompContainment`).
-/
