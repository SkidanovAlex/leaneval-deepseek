import Mathlib
import Submission.Work.SSGRoute.ZConstruction.AuxInterface
import Submission.Work.SSGRoute.ZDataMup.isLocalTateSystem_of_family
import Submission.Work.SSGRoute.ZSplit.levelK_unramifiedSubgroup
import Submission.Work.SSGRoute.ZConstruction.bilinForm_vanishing_submodule
import Submission.Work.SSGRoute.LTDRefs.levelK_finite
import Submission.Work.SSGRoute.ZConstruction.bilinForm_alternating_of_even_finrank
import Submission.Work.SSGRoute.ZConstruction.unramifiedSubgroup_isCyclic
import Submission.Work.SSGRoute.ZConstruction.even_finrank_H1loc_levelK
import Submission.Work.SSGRoute.ZSplit.levelK_bridge
import Submission.Work.SSGRoute.ZConstruction.levelK_reciprocity_lkPair
import Submission.Work.SSGRoute.ZConstruction.unramifiedOrthogonal_lkPairTransport
import Submission.Work.SSGRoute.ZDataMup.mupOddPairLin
import Submission.Work.SSGRoute.ZDataMup.mupOddForm
import Submission.Work.SSGRoute.ZDataMup.mupOddRecipAux
import Submission.Work.SSGRoute.ZDataMup.mupOddLevel
import Submission.Work.SSGRoute.ZDataMup.OddForm.oPairForm_sum_attach_eq_zero_of_outside
import Submission.Work.SSGRoute.ZDataMup.OddForm.oPair_toClass_eq_oPairGlob
import Submission.Work.SSGRoute.ZDataMup.OddForm.oTheta_eq_one_of_ne_oddPrime
import Submission.Work.SSGRoute.ZDataMup.exists_levelFamily_of_placeFamily
import Submission.Work.SSGRoute.ZConstruction.auxPairingGate_odd_aux
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.LocalFactor
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.SupStructure
import Submission.Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxHeartbeats 400000

/-!
# Gate (P): state of the analysis

The target `Work.SSGRoute.ZConstruction.levelK_pairing_productFormula` asks for a single family
`pair` of local pairings at the *level-`K` local groups* `decomp k A ⊓ K.fixingSubgroup` carrying
the three conjuncts of `Work.SSGRoute.AuxPairingGate K`:

* (i) `ZDataMup.IsLocalTateSystem` -- the local axioms (bi-additivity on locally constant
  cocycles, vanishing on a coboundary in either argument, left non-degeneracy on cocycles);
* (ii) `ZDataMup.IsProductFormula` -- the Hilbert-symbol product formula (the sum of the local
  pairings over one place per prime of `K` of two *global* cocycles which are unramified outside
  that place set vanishes);
* (iii) `Work.SSGRoute.IsUnramifiedOrthogonal` -- the pairing of two level-`K` local classes which
  are both trivial on the inertia vanishes.

## The statement is true, and here is what it is

Every group occurring in (i)--(iii) is contained in `K.fixingSubgroup = G_K`, on which the
restriction `res k K` is trivial; consequently `IsCocycleOn (res k K) H ·` is *additivity* and a
coboundary on such an `H` is the *zero* function.  The axioms (i) therefore say precisely that the
pairing descends to the level-`K` local `H¹`'s
`H1loc p k Ω K (ZMod p) H = H¹_cont(H, 𝔽_p)` and induces there a bilinear form which is
non-degenerate in its first variable (`Work.SSGRoute.ZDataMup.isLocalTateSystem_of_family`, the
linear-algebra half of the gate), while (iii) says that the unramified subgroup
`unramifiedSubgroup p k Ω K A H`
(`Submission/Work/SSGRoute/ZSplit/levelK_unramifiedSubgroup.lean`) is totally isotropic.

With `K ∋ ζ_p` the coefficient module `ZMod p` is its own Tate dual, and the *canonical* family is
the local Tate pairing at the prime `𝔭 | A` of `K` -- the cup product with the local invariant,
equivalently the `p`-th power Hilbert symbol.  For `p ≠ 2` it is alternating, so the level-`K`
unramified subgroups are isotropic (the odd-`p` content of (iii)); and its product formula (ii) is
*Hilbert reciprocity* in the `μ_p` form: for global classes `a`, `b` with Kummer elements
`α`, `β ∈ K^×`, the sum `∑_𝔭 (α,β)_𝔭` of the local invariants vanishes.  The `p = 2` sibling
carries the archimedean corrections, which is why the target assumes `p ≠ 2`.

The product formula is *not* a consequence of the local axioms, and it is not satisfiable by a
"dimension count" choice of the forms: (ii) is equivalent to the reciprocity law, and it is what
pins the pairing down (cf. the workspace's `ZDataMup/localTateSystem_productFormula.lean`,
`ZDataMup/isMupZData_odd.lean`, `ZSplit/LEVELK_STATUS.md`, and the warning at
`coker_obstruction.lean:206`).

## The status of the two arithmetic-free conjuncts (i) and (iii) -- state after the reviews

The target's conjuncts (i) (`IsLocalTateSystem`) and (iii) (`IsUnramifiedOrthogonal`) are both
about the *level-`K` local `H¹`* `V_A := H1loc p k Ω K (ZMod p) (D_A ⊓ G_K)` and reduce to:

* **(i)** `pair H a b = F H (toClass a) (toClass b)` with `F H` bilinear and non-degenerate in its
  first variable at every level-`K` local group;
* **(iii)** at every finite place `A`, `F (D_A ⊓ G_K)` vanishes on `U_A × U_A`, where `U_A` is the
  level-`K` unramified subgroup `ZSplit.unramifiedSubgroup p k Ω K A (D_A ⊓ G_K)`.

**A bookkeeping fact asserted in an earlier session is FALSE.**  The unramified subgroup `U_A` is
*not* independent of the place `A` among the places with the same level-`K` local group
`D_A ⊓ G_K`: for `K = k` and a finite Galois level with a ramified prime of type `(e,f,g) = (2,2,3)`
(e.g. `Gal = A₄`) the three primes above it have the same decomposition group but *distinct* inertia
subgroups, so `D_{A'} = D_A` while `I_{A'} ≠ I_A`, and the two unramified subgroups differ.  Since
`pair`'s first argument is the subgroup `D_A ⊓ G_K` only, the same form `F H` has to kill *every*
`U_A` with `H = D_A ⊓ G_K`.

This is why the correct linear-algebra input is an **alternating** form: if `F H` is alternating
(`F H x x = 0`) then it vanishes on the diagonal, and since each `U_A` is *cyclic*
(`U_A = 𝔽_p ∙ u_A`, the image of `H¹(Ẑ, 𝔽_p) = 𝔽_p`; the pro-cyclicity of `H/(H ⊓ I_A)`), the
bilinearity gives `F H(c u_A)(c' u_A) = c c' F H u_A u_A = 0` for every place `A` at once.  The
existence of an alternating left-non-degenerate form on `V_A` is, over the field `ZMod p` with
`p ≠ 2`, equivalent to `V_A` being finite-dimensional of *even* dimension.

## What is proved here

`exists_pair_localAxioms_and_unramifiedOrthogonal_of_family` below: **given** a family `F` of
bilinear forms on the level-`K` local `H¹`-groups which is left non-degenerate and vanishes on the
unramified subgroups, the descended pairing `pair H a b := F H [a] [b]` satisfies both (i) and
(iii) -- the two arithmetic-free conjuncts.  The remaining content of the gate is therefore exactly

* (ii) `IsProductFormula`, and
* an *alternating* family `F` as in `exists_pair_localAxioms_and_unramifiedOrthogonal_of_alternating`
  below, whose existence is the arithmetic `FiniteDimensional (ZMod p) V_A` (proved here as
  `finiteDimensional_H1loc_localGroup`, from `Work.SSGRoute.LTDRefs.levelK_finite`) together with
  `Even (finrank (ZMod p) V_A)`.  The parity is the local count
  `dim V_A = [κ : ℚ_ℓ] + 2` (or `2` when `ℓ ≠ p`): for `p | κ` the inclusion `ℚ_p(ζ_p) ⊆ κ`
  (`ζ_p ∈ K ⊆ κ`) makes `[κ : ℚ_p]` even, and for `ℓ ≠ p` the reduction of `ζ_p` is a nontrivial
  `p`-th root of unity in the residue field, so both cases are even.

## The status of the local half (updates)

`Work.SSGRoute.ZConstruction.bilinForm_vanishing_submodule` (proved, separate module) supplies the
linear algebra: on a finite-dimensional `𝔽_p`-vector space `V` a submodule `U` with
`2 * dim U ≤ dim V` is totally isotropic for some form non-degenerate in the first variable.  So
the local half of the gate is assembled from three bookkeeping facts about the level-`K` local
groups `H = decomp k A ⊓ K.fixingSubgroup` and their unramified subgroups `U_A`:

* `FiniteDimensional (ZMod p) (H1loc p k Ω K (ZMod p) H)`,
* `2 * finrank U_A ≤ finrank (H1loc p k Ω K (ZMod p) H)`, and
* `U_A = U_{A'}` for two places with `decomp k A ⊓ K.fixingSubgroup = decomp k A' ⊓ K.fixingSubgroup`
  (which holds because the two places are `G_K`-conjugate, so their inertia subgroups are equal in
  that local group).

Together with `exists_pair_localAxioms_and_unramifiedOrthogonal_of_family` and the child lemma,
these give conjuncts (i) and (iii) of the gate.

## The remaining obligations, precisely

* **(i)+(iii)**: the hypotheses of `exists_pair_localAxioms_and_unramifiedOrthogonal_of_even` are

  - `hcyc`: `ZSplit.unramifiedSubgroup p k Ω K A (D_A ⊓ G_K)` is cyclic (the image of
    `H¹(Ẑ, 𝔽_p) = 𝔽_p`, using the Frobenius/inertia decomposition
    `D_A ⊓ G_K = (D_A ⊓ G_K ⊓ I_A) ⋊ closure (zpowers σ)` of
    `Work.SSGRoute.inertiaSub_frobenius_complement_inf`); delegated as
    `Work.SSGRoute.ZConstruction.unramifiedSubgroup_isCyclic`;
  - `heven`: `Even (finrank (ZMod p) (H1loc p k Ω K (ZMod p) (D_A ⊓ G_K)))`.  Its finiteness is
    proved here (`finiteDimensional_H1loc_localGroup`, from
    `Work.SSGRoute.LTDRefs.levelK_finite`).  For the parity there are three routes on disk / in
    flight:
    1. `Work.SSGRoute.ZConstruction.natCard_homs_sq` (delegated): the *cardinality* of the
       continuous homs `D_A ⊓ G_K →* 𝔽_p` is `p ^ (2 * m)` — this is the local count
       `dim = 2` for residue characteristic `≠ p` and `dim = [κ : ℚ_p] + 2` for `= p`, with
       `(p-1) | [κ : ℚ_p]` because `ζ_p ∈ K ⊆ κ`.  Combined with the model isomorphism
       `H1loc ≅ Hom_cont` (`Work.SSGRoute.LTDDefs.H1loc_iso_H1cont`) and
       `Nat.card = p ^ finrank`, this gives `heven`.
    2. `Work.SSGRoute.ZConstruction.even_finrank_H1loc_dualMod` (delegated): the same parity for
       the cyclotomic-dual coefficients `DualMod p T`, then transported to `ZMod p` by
       `Work.SSGRoute.ZConstruction.even_finrank_H1loc_of_dualMod` (delegated), using the
       finrank formula `finrank H1loc(M) = finrank M · finrank H1loc(𝔽_p)`
       (`LTDRefs.H1locLinear.h1loc_finrank_trivialAction`) and `finrank (DualMod p T) = 1`.
    3. `Work.SSGRoute.ZConstruction.even_finrank_H1loc_levelK` (delegated).

* **(ii)**: `ZDataMup.IsProductFormula` is untouched.  It is the Hilbert-symbol product formula
  (`∑_𝔭 (α,β)_𝔭 = 0` for `α,β ∈ K^×`), i.e. the *reciprocity law*, and it is what pins the local
  pairing down; it is *not* a consequence of (i)+(iii) (nor of the existing one-place Hilbert
  reciprocity `NK.CFTLib.hilbertReciprocity_onePlace_aux`, whose formal consequence
  `Work.HilbertSymbolGeneral.hilbertReciprocityTwo` works only for `p = 2`).  The route is the
  local Artin map (`NK.LocalArtin.KernelCondition` / its local-global compatibility), see the
  module `ZDataMup/localTateSystem_productFormula`.

  Two remarks on the route, so that they are not re-explored:

  * The identity `∑_{A ∈ T'} pair_A(a,b) = 0` is *not* implied by the per-place conditions and the
    alternation: the pairing at a place `A` is a form on the local `H¹`, and the sum runs over one
    place per prime of `K`, so the family of forms is genuinely coupled.  The canonical (Hilbert
    symbol) family is a solution; that it is essentially the only one is the content of the
    `coker_obstruction` discussion in the workspace.
  * The proved one-place Hilbert reciprocity `NK.CFTLib.hilbertReciprocity_onePlace_aux` does give,
    for free, the *product formula for the symbols normalised by the global class group*, i.e. for
    the maps `ζ_A : K_A^× → Q ≅ ℤ/p`, `x ↦ [onePlace_A x]`, `Q = 𝕀_K ⧸ (𝕀^N L · K^×)` (here the
    class of `P(x)` is `0` because `K^× ⊆ K^× · 𝕀^N`).  What is *not* free is the comparison of
    these `ζ_A` with the local norm-residue symbols `λ_A`: both are onto `ℤ/p` with the same kernel,
    so they differ by a scalar `c_A ∈ (ℤ/p)^×` at each place, and the product formula is equivalent
    to `c_A = 1` for all `A`.  That identity is exactly the reciprocity law (equivalently, that the
    glued Artin map of `NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists` kills `K^×`), so the
    one-place input alone does not suffice for odd `p` (for `p = 2` it does, because then the local
    norm groups have index `2` and the two normalisations are forced, which is why the workspace's
    `Work.HilbertSymbolGeneral.hilbertReciprocityTwo` succeeds).

## What is missing

(ii) `IsProductFormula` for the canonical family is the "P1/P3 rung" of the workspace: it needs the
local Artin map (`NK.LocalArtin.ReciprocityMap`, whose existence is the *residual*
`NK.LocalReciprocityLubinTate.LocalResidual` = `NK.LocalArtin.KernelCondition`, i.e. the norm
residue symbol of the local class formation -- an input, not a theorem, in
`Submission/NK/LocalReciprocityLubinTate/Target.lean`), its local-global compatibility
(`NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists`), and the Kummer dictionary between level-`K`
local cocycles and `K_𝔭^×/K_𝔭^{×p}` (`Work.SSGRoute.local_kummer_dictionary` supplies the global
side).  With the local Artin map, the product formula follows from its triviality on principal
idèles -- the classical proof of Hilbert reciprocity.  **CORRECTION (session 4): the local CFT at the completions IS axiom-clean now.**  The
paragraph above is out of date.  The following inputs are `#print axioms`-clean
(`[propext, Classical.choice, Quot.sound]`) and available:

* `NK.NUV2.kernelCondition_all` -- the local reciprocity law in kernel form at *every* completion
  `𝔭.adicCompletion K` of *every* number field (module `Submission/NK/NUV2/kernelCondition_all.lean`);
* `NK.LocalReciprocityLubinTate.existenceTheorem_adicCompletion` and
  `NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`;
  hence (via `NK.LocalArtin.nonempty_artinReciprocity_of_reciprocal...`/`of_residual`)
  `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` gives the full local class field
  theory datum `NK.LocalCFT.ArtinReciprocity (𝔭.adicCompletion K) (SeparableClosure _)`:
  `artin : (𝔭.adicCompletion K)ˣ →* AbGal`, with `isLevelIso` (surjective, kernel the norm group at
  every finite abelian level) and cofinality.  **This is the local Artin map at every level-`K`
  local group**, since `decomp k A ⊓ K.fixingSubgroup ≅ Gal(κ̄/κ)` for `κ = (A ⊓ K).adicCompletion`
  (topological isomorphism: `decompEquiv_fok` + `NK.Mine.localGaloisEquiv`, packaged in the proof of
  `Work.SSGRoute.finite_openKernel_homs_decomp_kernel`).
* the level-`K` local Kummer dictionary `Work.SSGRoute.local_kummer_dictionary` (the Kummer
  character of `β ∈ Kˣ` vanishes on `decomp` iff `β` is a local `p`-th power) and
  `Work.SSGRoute.kummerIdx_mul` / `kummerIdx_eq_zero_of_mem_pow` (the character is *multiplicative*
  and kills `p`-th powers).
* GLOBAL, clean: `NK.CFTLib.artinReciprocityIdeal_proved` (ideal-theoretic reciprocity at a modulus
  `m` with weak ramification support), `NK.CFTLib.Arl.exists_monoidHom_ideleArtin` (an idèlic Artin
  map killing the *principal* idèles and the idèlic norms, surjective, Frobenius-normalised at every
  prime `∤ (m)`), `NK.CFTLib.Existence.ker_artinMapCK_eq_normClassSubgroup` (its kernel is
  `normImage ⊔ principalSubgroup`, i.e. the main theorem of CFT), `NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists`
  (the *glued local* Artin map `Φ₁ = ∏_v λ_v`: kills the norms, surjective, one-place faithful,
  Frobenius-normalised at *every* unramified prime), `NK.CFTLib.IdeleHasse.localFaithful_onePlace`,
  `NK.CFTLib.hilbertReciprocity_cyclic` (the one-place form: the bad set is never a singleton),
  `NK.CFTLib.IdeleHasse.localFactor...`/`Work.SSGRoute.ZSplit.localFactor_kernel_reciprocity` and
  `Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one` (the `R`-product formula for *any* idèlic Artin
  map killing the principal idèles and the norms).

**TAINTED (`sorryAx`) -- do not use**: `Work.SSGRoute.ZDataMup.ideleArtin_frob_unramified_abelian`,
`Work.SSGRoute.ZDataMup.localGlobalArtinMap_killing_principalIdele` (its *statement* is exactly the
"crux + product formula" package), `Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified`,
`Work.SSGRoute.ZSplit.localFactor_productFormula_cyclic` (also does not compile: two API drifts --
`NK.CFTLib.IdeleClassGroup.unifUnit` and `Idele.normIdeleHom` apply-lemma), and the whole
`local_tate_duality*` / `hasPerfectLocalPairing` / `exists_perfect_pairing` lane.

## The exact remaining gap, and a Chebotarev comparison that does *not* close it

The two clean global maps differ in exactly one property: `Φ₁ = ∏_v λ_v` (the glued local Artin
maps) does **not** obviously kill the principal idèles, while the idèlic map `art` of
`exists_monoidHom_ideleArtin` does (**its** local factors are the local Artin maps only at the primes
`∤ (m)`).  The product formula (ii) for the canonical local pairings is *equivalent* to
"`Φ₁` kills `Kˣ`" (equivalently `ker Φ₁ = normImage ⊔ principalSubgroup`, since both have index
`[L:K]` in `𝕀_K` and `Φ₁` is surjective).  This is the documented crux (the conductor drop /
local–global compatibility of the Artin map).

A tempting shortcut, and why it fails: at an unramified prime `Q ∤ (m)` both `Φ₁(onePlace_Q ·)` and
`art(onePlace_Q ·)` are maps `κ_Qˣ → D_Q` with kernel the local norm group and value `Frob_Q` at a
uniformiser, and `κ_Qˣ/N_Q` is cyclic generated by that uniformiser, so they *agree* there.  One is
then tempted to conclude `art = χ ∘ Φ₁` for an endomorphism `χ` of the cyclic group `Gal(L/K)`
(which would follow from `ker art ⊇ ker Φ₁`) and to pin `χ` down by Chebotarev (pick `Q ∤ (m)` whose
`Frob_Q` generates, so `χ = id` and `art = Φ₁`).  The step `ker art ⊇ ker Φ₁` is *exactly* the crux
in disguise (`ker Φ₁ ⊆ normImage ⊔ principalSubgroup` is equivalent to `Φ₁` killing `Kˣ`), so the
argument is circular; the honest content of the computation is only that the local factors of `art`
at the unramified primes `∤ (m)` are the local Artin maps (`art = Φ₁` on the one-place idèles there).

## The route to (ii), as it stands

1. build the level-`K` local Kummer isomorphism `κ_A : K_𝔭ˣ/(K_𝔭ˣ)^p ≅ H1loc p k Ω K (ZMod p) H_A`
   (multiplicativity: proved, `Work.SSGRoute.ZConstruction.kummerCharZMod_fixingSubgroup_mul_pow`;
   kernel: `Work.SSGRoute.local_kummer_dictionary` (proved) via the class map `toClass` and
   `Work.SSGRoute.ZDataMup.isCoboundaryOn_iff_eqOn_zero`; surjectivity: weak approximation + the
   cardinality inputs below).
   **Cardinality inputs already clean on disk**: `Work.SSGRoute.ZSplit.levelK_localKummer`
   (`|H1loc p k Ω K (DualMod p T) H_A| = |KummerGroup p (K ⊔ decompField k Ω A)|`) and, at the
   completion, `Work.SSGRoute.PTembedding.lcHoms_localUnits`
   (`|lcHoms p G_κ| = |κˣ ⧸ (κˣ)^p|`), which is built on the *clean* `NK.NUV2.kernelCondition_all`
   and `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` -- i.e. the local Kummer
   count at the level-`K` local group is reachable now, whereas the `E7` file
   `PTembedding/localKummer_base.lean` (`kummerBaseDim`, one `sorry`) still blocks the
   dimension-form only.
   **Instance caveat (do not lose time on it)**: stating the class-form dictionary with the base
   field `↥K` and the trivial extension `⊥` (where the domain of `kummerCharZMod` matches `G_k`
   directly) fails instance synthesis inside `toClass`; either supply the missing
   `FiniteDimensional`/`IsGalois`/`DistribMulAction` instances for `⊥` explicitly, or work at the
   base `k` with the character extended by zero outside `K.fixingSubgroup`.
2. define the local form by `F(x, y) := y(Art_κ(κ_A^{-1} x))` (`y ∈ V_A = Hom_cont(H_A, 𝔽_p)`
   extended to `H_A^ab`, `Art_κ` the local Artin map of step 1 above): bilinearity is then formal,
   left non-degeneracy follows from the surjectivity of `Art_κ` plus Pontryagin duality of the finite
   `𝔽_p`-space `H1loc`, and the unramified orthogonality (iii) from `Art_κ(units) ⊆ I_κ`;
3. the product formula (ii) is then Hilbert reciprocity in the `μ_p` form, i.e. the crux above:
   `∏_A λ_A(x_A) = 1` for `x ∈ Kˣ` and the cyclic Kummer extension `L = K(x^{1/p})`, which is
   `Work.SSGRoute.ZDataMup.cprod_localFactor_eq_one` *once* one has an idèlic Artin map whose local
   factors are the `λ_A` (the tainted `localGlobalArtinMap_killing_principalIdele` is exactly that
   statement).  Step 3 is *not* obtainable from the clean material on disk at the time of writing.

## Sharpening of the gap (session 5)

Writing `Θ` for the glued local-global Artin map `Φ = ∏_v λ_v` of
`NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists` (which is *clean*, and whose local factors have
kernel the local norm subgroups and are Frobenius-normalised at *every* unramified prime), and `art`
for the idelic Artin map of `NK.CFTLib.Arl.exists_monoidHom_ideleArtin` (clean; kills `Kˣ` and the
norms; Frobenius-normalised only at `v ∤ m`, where `m` is the modulus of a reciprocity datum), the
conjunct (ii) reduces to a single arithmetic statement:

  **(LOCAL–GLOBAL COMPATIBILITY, Milne CFT VII.8.1(a))**: `Φ` kills the principal idèles `Kˣ`.

Equivalently `Φ = art`, equivalently `ker Φ = Kˣ · N_{L/K}𝕀_L`, equivalently the *conductor drop*
(`art` is Frobenius-normalised at every unramified prime), equivalently **Hilbert reciprocity in
the `μ_p` form** `∏_v λ_v(x) = 1` for the honest local Artin maps `λ_v`.

Two clean ingredients on disk make this the *only* gap:

* `Work.SSGRoute.ZSplit.localFactor_kernel_reciprocity` — the family `θ_v := art ∘ onePlace_v` has
  `ker θ_v = N_v` **and** the product formula `∏_v θ_v(x_v) = 1` for `x ∈ Kˣ` (trivially, since
  `art` kills `Kˣ`), but is *not* intrinsic: `θ_v = φ_v ∘ λ_v` with `φ_v ∈ Aut(C_v)`, and only
  `φ_v = 1` for `v ∤ m` is known.
* `NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists` — the family `λ_v := Φ ∘ onePlace_v` is
  intrinsic (it is built from the local Artin maps), has `ker λ_v = N_v` **and** is
  Frobenius-normalised at every unramified prime, but `∏_v λ_v(x_v) = 1` is *not* known.

So each of the two clean families has two of the three needed properties (`ker = N_v`, Frobenius
normalisation, product formula) and misses exactly the third; the missing third is the same
statement in both cases, and it is (LOCAL–GLOBAL COMPATIBILITY).  Writing `φ_v = (·)^{c_v}` on
`C_v = Gal(L_v/K_v)` (`|C_v| ≤ p`), the statement is `c_v = 1` for every place `v`, and the
`θ`-product formula is equivalent to the single linear relation `∏_{v ∈ bad(x)} λ_v(x)^{c_v} = 1`
on the "bad set" of `x`; since the bad set is never a singleton (one-place Hilbert reciprocity,
`NK.CFTLib.hilbertReciprocity_onePlace_aux`, clean) this pins `c_v` down *only up to a common
scalar*, and killing the scalar requires the conductor drop itself.

**New (session 5), and the sharpest form of the gap**: `c_v = 1` for every `v ∤ m` (this is
`hgood` of `exists_monoidHom_ideleArtin` together with `unifUnit ↦ Frob` and
`O_v^× ⊆ N_v` for unramified `v`).  Hence the vector `e := (c_v − 1)_v` is *finitely supported*,
contained in the set `supp(m)` of primes dividing the modulus — a *finite* set of conditions, not
a global one.  Moreover the `θ`-product formula reads `Φ(P(x)) = ∏_v λ_v(x)^{c_v} = 1`, i.e.

  `∏_{Q | m} λ_Q(x)^{e_Q} = ∏_{Q ∤ m} λ_Q(x)^{-1}`  (`= Φ(P(x))^{-1}`),

so the gap is: *the family `(e_Q)_{Q | m} ∈ 𝔽_p^{supp(m)}` is orthogonal to the image of
`x ↦ (λ_Q(x))_{Q | m}`*.  By Grunwald–Wang for odd `p` (and `hp : p ≠ 2` in the target) that
image is *all* of `∏_{Q | m} C_Q` for the honest local Artin maps — which is why the local
constraints cannot be satisfied by a dimension count — so the gap is exactly `e = 0`, i.e. the
"local-honestness at the primes of `supp(m)`".  Concretely, the single
`sorry` of the whole lane is `Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified`
(the "pole case": `art (ideleOfPrime 𝔭) = Frob_𝔭` for the *unramified* `𝔭 | (m)`), and
`Work.SSGRoute.ZDataMup.conductorDrop_ramifiedCongr{,_Lane}`, `mup_localArtin_productFormula`,
`productFormula_cyclic_primePowerCase` all remain tainted by it (`#print axioms` admits `sorryAx`).
-/


/-!
## Session L6: the crux measured, and the exact shape of the remaining input

This session measured the axiom footprint of the whole `ZDataMup` / `ArtinReciprocity` lane with
`#print axioms` (all files present, all building).  Result:

* CLEAN (`[propext, Classical.choice, Quot.sound]`):
  `NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists` (the glued map `Φ = ∏_v λ_v`: surjective,
  kills the idelic norms, one-place faithful, Frobenius-normalised at *every* unramified prime),
  `Work.SSGRoute.ZDataMup.artinKillsPrincipal_of_isAdmissible`,
  `Work.SSGRoute.ZDataMup.isAdmissible_of_artinKillsPrincipal` (the two directions of
  ``the modulus is admissible `` ⇔ ``the Artin symbol kills the congruence-principal ideals ``,
  given `hram`), `Work.SSGRoute.ZDataMup.abelian_of_cyclicCase`,
  `Work.SSGRoute.ZSplit.localFactor_kernel_reciprocity` (`θ_v := art ∘ onePlace_v` has kernel `N_v`
  and satisfies the product formula `∏_v θ_v(x_v) = 1` for `x ∈ Kˣ`).
* TAINTED (`sorryAx`), *circularly*: `conductorDrop_ramifiedCongrLane` ←
  `cyclicCaseStatement_lane` ← `artinSym_eq_one_of_isAdmissible_cyclic` ←
  `localGlobalArtinMap_killing_principalIdele` ← `ideleArtin_ideleOfPrime_of_unramified`
  (the single literal `sorry` of the lane; there is no clean exit from the cycle).  The same taint
  reaches `productFormula_cyclic_canonical` and `mup_localArtin_productFormula`.

So the whole lane is equivalent to one arithmetic statement, and the loop above is not a defect of
the formalisation but the genuine equivalence of the two classical forms of the reciprocity law:

  **(★)**  the glued map `Φ = ∏_v λ_v` of `localGlobalArtinMap_exists` kills the principal ideles
  `Kˣ`  —  Milne, *CFT*, VII.8.1(a);  equivalently `art = Φ` for the ideal-theoretic idelic Artin
  map `art`;  equivalently the conductor drop "`artinSym((b)) = 1` for `b ≡ 1 mod m` at the
  *ramified* primes only" (Neukirch V.6.1).

Three sharpened forms of the gap, all verified this session:

1. **Local-factor form.**  Write `θ_v := art ∘ onePlace_v` and `λ_v := Φ ∘ onePlace_v`.  Both have
   kernel the local norm subgroup `N_v` and both send a uniformiser at an unramified `v` to `Frob_v`;
   hence `θ_v = φ_v ∘ λ_v` with `φ_v ∈ Aut(Gal(L_v/K_v))`, `φ_v = 1` for every `v ∤ m`, and
   `φ_v = 1` for every unramified `v` with `p(v) ∉ P`, where `P` is the set of rational primes
   carrying a ramified prime of `L/K` (there one takes a modulus `m'` whose support is the
   saturated set `{𝔮 : p(𝔮) ∈ P}` and concludes from the Frobenius normalisation at `𝔮 ∤ (m')`).
   **(★) is exactly `φ_v = 1` for the unramified `v` with `p(v) ∈ P`**, i.e. it is needed only at
   the finitely many *unramified* primes above the rational primes that also carry a ramified prime
   — precisely the primes the notes call the "gap" `R̂ ∖ R`.
2. **Why `ℕ`-moduli cannot express the input.**  For a natural-number modulus, `𝔭 ∣ (m)` implies
   `𝔮 ∣ (m)` for every `𝔮 | p(𝔭)`; so `supp (m)` is always *saturated above the rational primes*,
   and no `ℕ`-modulus has support exactly the ramified set unless that set is already saturated
   (which holds e.g. when `K/ℚ` is Galois, but not in general).  The conductor drop needs the
   congruence condition at `R` only, so it needs an **ideal** modulus
   `𝔪 = ∏_{𝔭 ∈ R, 𝔭 | (m)} 𝔭^{v_𝔭(m)}`; `IsAdmissible` transfers to `𝔪` (its conditions at
   unramified primes are automatic: congruence units are local units, and local units are norms at
   unramified primes), and what is missing is exactly the Lang transfer / index inequality for
   ideal moduli (the vocabulary is under construction in `ZDataMup/idealModulusDefs.lean`).
3. **Equivalence of the two clean families, again.**  `art` is intrinsic and kills `Kˣ` but is
   Frobenius-normalised only at `Q ∤ (m)`; `Φ` is intrinsic and Frobenius-normalised everywhere but
   does not obviously kill `Kˣ`.  All the on-disk comparisons of the two already reduce to (★):
   e.g. `cprod_localFactor_eq_one` needs `Φ(principalIdele b) = 1` (i.e. (★) for `b`), and
   `ideleArtin_frobAtPrime_unramifiedLane` needs `conductorDrop_ramifiedCongrLane`.

The delegation `Work.SSGRoute.ZDataMup.gluedMap_kills_principalIdele` (this session) requests (★)
at a fresh path, stated so that a clean proof is *forced* by `declare_proven`'s axiom check (the
on-disk carriers are all `sorryAx`-tainted).
-/

/-!
## Live status of the crux (mid-session L6, measured; the fleet is moving fast)

Two independent routes to the conductor drop / (★) are being closed in parallel; both are
*sorry-free in their bricks* and both bypass the circular chain recorded above.

**Route A - decomposition fields (the "inertia" argument).**  Files (all `#print axioms` clean):
`ZDataMup/restrict_ideleArtin_ideleOfPrime_of_admissible.lean` (descent step: the restriction of
`ideleArtin^{L/K}_𝔪(ideleOfPrime Q)` to an intermediate `M/K` is `frobAtPrime^{M/K} Q`, provided an
admissible modulus for `M/K` coprime to `Q` exists),
`ZDataMup/ideleArtin_prime_eq_frob_of_admissible_coprime.lean`,
`ZDataMup/unramified_of_decompositionSubgroup_le_fixingSubgroup.lean` (if every decomposition
subgroup at `L` above `q` lies in `Gal(L/M)`, then `q` splits completely in `M/K`),
`ZDataMup/exists_admissible_modulus_avoiding_unramified.lean` (a `p`-free admissible modulus via
`mRam`; proved and clean, 12:16).  Remaining: kill the unramified prime `𝔮 | p` modulo
`L^D`, `D := ⟨decompositionSubgroup Q : Q | p⟩`, and then the `I_ram` residue.

**Route B - ideal moduli.**  `ZDataMup/idealModulusDefs.lean` (vocabulary) plus the four adapters
`ArtinReciprocity/IdealModulus/*.lean` (surjectivity of the ideal Artin symbol, the translation
`artinSymbol_span_eq_artinSym_spanSingleton_of_ideal`, `FracCoprimeId` closure, and
`CongrOneId_of_mem_sub_one`) are all proved; the assembly `artinSymbolKillsPrincipal_ideal`
(ideal-modulus analogue of `artinKillsPrincipal_of_isAdmissible`) is then a mechanical copy of
`artinSymbolKillsPrincipal_of_kernelLe_of_relIndex_fixed`.  With it,
`IsAdmissibleIdeal(𝔪) + hram ⟹ hprinc(𝔪)` for `𝔪 := ∏_{𝔭 ram, 𝔭 | (m)} 𝔭^{v_𝔭(m)}` gives the
conductor drop, hence (★), hence the lane's product formula - see `ZDataMup/mRam_ramifiedSupport.lean`
and `ZDataMup/mRam_hprinc.lean` (`mRam` = the optimal ℕ-modulus supported on the ramified primes,
admissible, with `hprinc`).

So `AuxPairingGate`'s conjunct (ii) is expected to become available from *either* route; the
remaining work for the target is then the level-`K` Kummer wiring recorded above.
**Update (same session, later).**  Route B has landed: `NK.CFTLib.ArtinReciprocityIdeal
.artinSymbolKillsPrincipal_ideal` (`ZDataMup/ArtinReciprocity/IdealModulus/artinSymbolKillsPrincipal
_ideal.lean`, sorry-free) is the ideal-modulus assembly: from the ideal-modulus Lang transfer
`hkerK`, the containment `hPNI` and the index inequality `hIdx` at an ideal modulus `𝔪` it gives
`artinSymbol (span {a}) = 1` for `a - 1 ∈ 𝔪` and `a` totally positive.  Applied at
`𝔪 := ∏_{𝔭 ram, 𝔭 | (m)} 𝔭^{v_𝔭(m)}` (whose admissibility is inherited from that of `m`, since
`IsAdmissible` only constrains the ramified primes) this is the conductor drop, hence (★).  Route A
is packaged up to its decomposition-field construction in
`Submission/Work/SSGRoute/ZConstruction/badPrime_mod_decompField.lean` (this session, clean): given
`M ≤ L` with `M/K` cyclic in which every prime above a rational prime `p` is unramified, a prime
`Q | p` of `K` has `restrictNormalM (ideleArtin^{L/K}(ideleOfPrime Q)) = frobAtPrime^{M/K} Q`, i.e.
`ε_Q ∈ Gal(L/M)`.

**THE CRUX IS PROVED (this session).**  `Work.SSGRoute.ZDataMup.gluedMap_kills_principalIdele`
(`Submission/Work/SSGRoute/ZDataMup/gluedMap_kills_principalIdele.lean`, 206 lines, axioms
`[propext, Classical.choice, Quot.sound]`) is Milne CFT VII.8.1(a): for finite cyclic `L/K` there
is `Φ : 𝕀_K →* Gal(L/K)` killing `Kˣ` and the idelic norms, surjective, one-place faithful and
Frobenius-normalised at every unramified prime.  It was obtained by delegating the statement at a
fresh path (so that `declare_proven`'s axiom check forces a clean proof); the prover routed it
through `Work.SSGRoute.ZDataMup.ArtinReciprocity.productFormula_cyclic` (the fleet's ideal-modulus
conductor machinery) rather than through the circular chain recorded above.  Consequently the whole
`conductorDrop` / `localGlobalArtinMap_killing_principalIdele` chain can now be re-proved cleanly by
re-pointing, and the remaining obstruction of this node is *only* the wiring: from `Φ` (or from the
local factors `θ_Q := Φ ∘ onePlace_Q`, whose product formula is
`Work.SSGRoute.ZDataMup.mup_localArtin_productFormula`) to the level-`K` local pairings, via the
level-`K` Kummer dictionary (`ZDataMup/levelK_localKummer.lean`, `ZSplit/levelK_localTateSystem_exists
.lean`, `ZSplit/levelK_pairing_of_tateSystem.lean`).  A clean re-statement of that rung is requested
at `Submission/Work/SSGRoute/ZConstruction/mup_localArtin_productFormula_clean.lean`.

Also contributed this session:
`Submission/Work/SSGRoute/ZConstruction/badPrime_mod_decompField.lean` (clean): the composition of
the fleet's decomposition-field bricks - if every prime above a rational prime `p` is unramified in
a cyclic intermediate `M/K`, then for `Q | p` the restriction of `ideleArtin^{L/K}(ideleOfPrime Q)`
to `M` is `frobAtPrime^{M/K} Q` (step 5 of the second, independent route to (★)).

## Session L7: the exact gap, measured again -- (★) is the *idele*-Artin-map form, not the honest form

This session re-examined the claim "(★) = `Φ` kills `Kˣ` is Hilbert reciprocity, hence conjunct
(ii)".  The measurement below shows that (★) does **not** by itself give conjunct (ii), and it
isolates the missing statement.

**1. What conjunct (ii) is.**  In `IsProductFormula` the two arguments `a`, `b` are global
locally constant `1`-cocycles on `G_K`; since every group occurring lies in `K.fixingSubgroup`,
`a` (resp. `b`) is nothing but a continuous additive map `G_K → ZMod p`, i.e. an element of
`H¹(G_K, ZMod p) = Hom_cont(G_K, ZMod p)`.  With `ζ_p ∈ K` this is `Kˣ/(Kˣ)^p` (Kummer), and the
canonical local Tate pairing at a place `A` is the `p`-power Hilbert symbol, so (ii) reads

  `∑_A (α_A, β_A)_A = 0`  for  `α, β ∈ Kˣ`,

which is Hilbert reciprocity for the odd prime `p`.  So (ii) is a *statement about the honest
local Artin maps of the completions*, and the question is whether the workspace can prove it.

**2. What (★) actually gives.**  `Work.SSGRoute.ZDataMup.gluedMap_kills_principalIdele` produces,
for a finite cyclic `L/K`, a homomorphism `Φ : 𝕀_K →* Gal(L/K)` with

  (1) `Φ` kills `Kˣ`;  (2) `Φ` kills `N_{L/K} 𝕀_L`;  (3) `Φ` is surjective;
  (4) `Φ (onePlace v a) = 1 ↔ a ∈ N_v` (one-place faithful);
  (5) `Φ (ideleOfPrime K Q) = Frob_Q` for every unramified `Q`.

`Φ` is built from the ideal-modulus Artin symbol `artinSym = ∏_𝔮 (frobAtPrime 𝔮)^{v_𝔮}`
(`NK.CFTLib.Arl.artinSym`), i.e. from the *chosen* Frobenius elements
`NK.Chebotarev.frobAtPrime`.  For an unramified `𝔮` that choice is canonical (the unique
Frobenius), but for a **ramified** `𝔮` it is `Classical.choose` of "`∃ σ, IsFrobAtPrime 𝔮 σ`", an
*arbitrary* element of the Frobenius coset `I_𝔮 · Frob` of `D_𝔮` — no canonical value exists.
Consequently the *local factor* `θ_v^Φ := Φ ∘ onePlace_v : K_vˣ → Gal(L/K)` is, at a ramified `v`,
only determined by `ker = N_v`; compared with the honest local Artin map `λ_v^{can}` it satisfies
`θ_v^Φ = λ_v^{can} · c_v` for an unknown scalar `c_v ∈ (ZMod p)ˣ`, and `c_v = 1` is known
*only* at the unramified places (there clause (5) pins it).  The workspace states this ambiguity
explicitly: `Work.SSGRoute.ZDataMup.ArtinReciprocity.frobAtPrime_eq_ideleArtin_of_index_le_two`
compares `art` with the glued map `∏_v λ_v` and says in its docstring that the index hypothesis
`≤ 2` "is *not* redundant: it is used exactly to rule out the possibility that the two local maps
differ by multiplication by an element of order `> 2`" — i.e. for `p > 2` the local factors at the
ramified primes genuinely differ by a non-trivial scalar.

**3. Why that is exactly the difference between (★) and (ii).**  Writing
`ζ := Φ / Φ_can` (the pointwise ratio with the canonical gluing `Φ_can := ∏_v λ_v^{can}`, a
homomorphism because `Gal(L/K)` is abelian), one computes `ζ (onePlace v x) = λ_v^{can}(x)^{e_v}`
with `e_v = c_v - 1` *supported on the ramified primes*.  So (★) — `Φ (principalIdele α) = 1` —
reads

  `Φ_can (principalIdele α) · ∏_v λ_v^{can}(α)^{e_v} = 1`,   equivalently
  `∑_{v ramified} e_v · (the local symbol of α at v) = ∑_v (the local symbol of α at v)`,

and conjunct (ii) is the assertion `∑_v λ_v^{can}(α) = 0`, i.e. `e = 0`.  Thus

  **(ii)  ⟺  `e_v = 0` for every ramified `v`  ⟺  `Φ = Φ_can`  (the ideal-modulus Artin map and
  the canonical gluing coincide) ⟺ the local factors of `artinSym` at the ramified primes are the
  canonical local Artin maps.**

None of these follows from (★): (★) is a statement about *one* map with the properties (1)-(5),
and (1)-(5) do not determine `Φ` among the maps with those properties (if `Ψ` has (1)-(5) then so
does `χ ∘ Ψ` for any `χ ∈ Aut(Gal(L/K))`, and these differ at the ramified primes).  The
workspace's own reduction analysis (`ZDataMup/glueMap_kills_principalIdele_cyclic.lean`, module
docstring) is *correct* in identifying the crux with the conductor drop, but the conductor drop is
the Frobenius normalisation at the **unramified** primes `Q | (m)` only; the canonically-normalised
local factors at the **ramified** primes are a strictly stronger input, and they are not on disk.

**4. Two consequences worth recording.**

* *The target reduces to the level-`⊤` instance.*  By the on-disk base-change dictionary
  (`ZSplit/levelK_reciprocity_baseChange.lean`,
  `ZSplit/levelK_bridge.isLevelKLocalTateSystem_iff_isLocalTateSystem`), conjuncts (i)+(ii) for the
  level-`K` local groups are exactly the generic statements, at the base field `↥K` with the
  *trivial* extension `⊥` (where `G_{↥K} = ⊤`, so the two unramifiedness conditions coincide).  So
  the target is a transport of the level-`⊤` gate `∃ pair, IsLocalTateSystem p ↥K Ω ⊥ pair ∧
  IsProductFormula p ↥K Ω ⊥ pair ∧ IsUnramifiedOrthogonal (⊥) pair`, and the workspace already
  uses exactly this pattern in `ZSplit/levelK_counting_of_baseChange.lean` (`hbase`).

* *The arithmetic core is Hilbert reciprocity for the odd prime `p`.*  At the base field, (ii) is
  `∑_v (α, β)_v = 0` for `α, β ∈ Kˣ` — the sum of local invariants of a global class, i.e.
  Milne, *CFT*, VII.8.1(a).  The classical proofs use the Hasse principle for `Br(K)` plus the
  reduction to the cyclotomic/Kummer cases; the workspace has the Hasse principle
  (`NK.GlobalCFTdeep.hbnUnits`) and the *cyclotomic* case of the crux
  (`ZDataMup/glueMap_kills_principalIdele_cyclotomic.lean`, proved), but not the passage from the
  cyclotomic case to the honest local factors at the ramified primes.

**5. What this session added, verified.**  The target is now *reduced* to the base-field instance,
with the reduction proved:

* `Work.SSGRoute.ZConstruction.levelK_reciprocity_lkPair` (new file, proved): the witness-exposed
  form of `ZSplit.levelK_reciprocity_baseChange` — the level-`K` local Tate axioms and the level-`K`
  product formula hold for the *specific* transported pairing `ZSplit.lkPair p k Ω K pair'`;
* `Work.SSGRoute.ZConstruction.unramifiedOrthogonal_lkPairTransport` (new file, proved): the
  unramified orthogonality transports along the same dictionary;
* `hasLevelKReciprocity_imp_isProductFormula` (below, proved): the level-`K` product formula implies
  the `ZDataMup` spelling (the latter has the stronger unramifiedness hypothesis);
* `auxPairingGate_of_baseGate` (below, proved): **the whole gate at level `K` follows from the gate
  at the base field `↥K` with the trivial extension `⊥`**, i.e. from a single base pairing `pair'`
  with the local Tate axioms, the product formula and the unramified orthogonality on `G_{↥K}`.

So the target is *equivalent* to the level-`⊤` instance (the reverse implication is what (i)+(iii)
at level `K` for the transported pairing cannot give without the arithmetic), and that instance is
Hilbert reciprocity for the odd prime `p`.  The residual is **not** the conductor drop of §2-3 but
the canonically-normalised local factors at the *ramified* primes.

**6. The executable route to `e_v = 0` (planned, with what is already on disk).**

The statement to prove is: for every cyclic extension `L/K` of degree `p` (odd) and every place `v`,
the scalar `c_v(L) := θ_v^Φ / λ_v^{can}` is `1`, where `Φ` is any map with (1),(2),(4),(5) and
`λ_v^{can}` the canonical local Artin map of the completion.  Two steps:

* **(a) `c_v(L)` is independent of `L`.**  For cyclic `L`, `M` of degree `p` over `K` the composite
  `LM/K` is abelian of exponent `p`, and the tower functoriality of the idelic Artin map gives
  `proj_L ∘ Φ_{LM} = Φ_L`, `proj_M ∘ Φ_{LM} = Φ_M`; on the local factors this reads
  `c_v(L) = c_v(LM) = c_v(M)`.  The *ideal-theoretic* half of the functoriality is **already on
  disk**: `NK.CFTLib.ArtinReciprocityIdeal.artinSymFrac_restrictNormalHom`
  (`ArtinReciprocityIdeal/kernelLe_of_auxField.lean`) and
  `Work.SSGRoute.ZDataMup.artinSym_restrictNormalHom_of_unramifiedSupport`
  (`ZDataMup/abelian_of_cyclicCase.lean`), both sorry-free — the restriction of `artinSym` along
  `↥M ⊆ L` is `artinSym` for the smaller extension, at ideals coprime to the ramified primes.
  **Update (this stretch): Milne 8.4(a) itself is on disk.**
  `Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom`
  (`ZDataMup/ideleArtin_restrictNormalHom.lean`, sorry-free) is exactly the adjuster comparison: for
  a congruence datum `(m, U, hadj)` on `K` and a normal intermediate field `↥M ⊆ L` (with
  `Gal(↥M/K)` commutative) the idelic Artin map of `L/K` restricted to `M` *with the same datum* is
  the idelic Artin map of `↥M/K`.  The local-factor shape consumed here is
  `Work.SSGRoute.ZDataMup.ideleArtin_onePlace_restrictNormalHom`
  (`ZDataMup/localFactor_towerCompat.lean`, sorry-free, added this stretch).
  What still has to be added for (a) is the *local* identification: writing
  `θ_A^{L} := Φ_L ∘ onePlace_A`, if `L` and `M` have the same local extension at `A` then
  `θ_A^{L} = θ_A^{M}` as maps into the common local group `Gal(L_A/K_A)`.  Two elementary inputs
  suffice: (i) `θ_A^{L}` lands in the decomposition subgroup of `A` (so that `Gal(L_A/K_A)` may be
  identified with a subgroup of `Gal(L/K)`), and (ii) `proj_L` is injective on `Gal((LM)_A/K_A)`,
  which holds because `(LM)_A = L_A M_A = L_A` when `L_A = M_A`.
* **(b) one of the two extensions can be taken unramified at `v`.**  By Grunwald–Wang for the odd
  prime `p` there is a cyclic extension `M/K` of degree `p` ramified only away from `v`; there
  `c_v(M) = 1` because the unramified places pin the local factor (clause (5)).  Combined with (a),
  `c_v(L) = 1` for every `L`.

With `e_v = 0` the ideal-modulus Artin map `Φ` equals the canonical gluing `Φ_can`, hence
`Φ_can` kills `Kˣ`; as `Φ_can` is the product of the canonical local Artin maps, the honest local
Tate pairing then satisfies the product formula (`∑_v (α,β)_v = 0`), which is the base gate of §5
and hence the target.

Ingredient already on disk for (b) and for the local bookkeeping: for a prime `𝔭` dividing the
modulus `m` of the ideal-theoretic reciprocity law, a congruence unit `x ≡ 1 mod 𝔭^{v_𝔭(m)}` lies in
the local norm subgroup `N_𝔭` — this is
`Work.SSGRoute.ZDataMup.localFactor_ramified_eq_one`
(`ZDataMup/localFactor_ramified_eq_one.lean`, sorry-free) together with one-place faithfulness
(clause (4)) of the countepart map, and it is what identifies `Φ_can` on the congruence subgroup
`P(c)` with `artinSym` on the principal ideals of `P(c)` — i.e. with the reciprocity law
`NK.CFTLib.artinReciprocityIdeal_proved`.

## The canonical family, built (this session), and the exact remaining obligations

The gate is now reduced (`auxPairingGate_of_reciprocityFamily` below) to the existence of a *single*
family of bilinear forms on the level-`K` local `H¹`-groups carrying (1) first-variable
non-degeneracy, (2) the reciprocity sum and (3) the unramified orthogonality.  The canonical such
family is *constructed* in `Submission/Work/SSGRoute/ZConstruction/levelK_canonicalPairing.lean`
(module `Submission.Work.SSGRoute.ZConstruction.levelK_canonicalPairing`, sorry-free):
`levelKCanonPairingAt A x y = χ_x^A (rec_A (β_y))`, the character of `x` at the completion
evaluated at the honest local Artin map `rec_A = mupRec` of the Kummer class `β_y` of `y`.  It is
packaged as a family of `ZMod p`-linear maps in
`.../levelK_canonicalBilinear.lean` (`levelKCanonFormA`, `levelKCanonFamily`), where the following
is **proved**:

* bilinearity (`levelKCanonPairing_add_left/right`, via the multiplicativity of the model
  identification, of the local Galois transport, of the abelianisation and of the Kummer
  dictionary);
* **(1)** `levelKCanonPairing_nondegenerate` — first-variable non-degeneracy, from the *density* of
  the local Artin image (`Work.SSGRoute.LT_abGal_kills_of_artin`) plus the bijectivity of the model
  identification and of the Kummer dictionary.

The remaining obligations of the gate, exactly:

* **(2)** the reciprocity sum for the canonical family — Hilbert reciprocity in the `μ_p` form, i.e.
  the statement that the glued local-global Artin map kills `Kˣ`
  (`Work.SSGRoute.ZDataMup.gluedMap_kills_principalIdele`, clean) together with the local-global
  compatibility of the Artin map at the ramified primes.  Statement (reviewed, `hp : p ≠ 2` added
  after review): `Work.SSGRoute.ZConstruction.levelK_canonical_rec`.
* **(3)** the unramified orthogonality of the canonical pairing — the local input
  `Br(κ_A^{un}/κ_A) = 0`, i.e. "an unramified Kummer class is the class of a unit" plus
  "`rec_A` sends units into the inertia".  Statement (reviewed):
  `Work.SSGRoute.ZConstruction.levelK_canonical_unramified`.
* **the transport** (bookkeeping, for the family packaging): two places `A`, `A'` with the same
  level-`K` local group must give the same form on it.  Its *premise* is that `decomp (↥K) A` and
  `decomp (↥K) A'` then agree (the canonical identification `G_K ≃* Gal(Ω/↥K)` carries
  `H_A = decomp k A ⊓ G_K` to `decomp (↥K) A`); what remains is the compatibility of the two chosen
  transports (the model identification `mupH1locLcHoms`, the local Galois transport and the Kummer
  dictionary), which is what would let the family be defined without a `Classical.choose` on the
  place.

-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute
open Work.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The local half of gate (P), conditionally on a family of forms.**

Given, for every subgroup `H` of `G_k`, a bilinear form `F H` on the level-`K` local `H¹`-group
`H1loc p k Ω K (ZMod p) H` which

* is non-degenerate in its first variable at every level-`K` local group
  `H = decomp k A ⊓ K.fixingSubgroup`, and
* vanishes on the level-`K` unramified subgroup
  `unramifiedSubgroup p k Ω K A H` in both variables (at every finite place `A`),

the descended pairing `pair H a b := F H (toClass a) (toClass b)` satisfies the local axioms
`IsLocalTateSystem` and the unramified orthogonality `IsUnramifiedOrthogonal`.

The axioms are the *cochain-level* form of "`F H` descends to the local `H¹`'s": the restriction
action is trivial on `H ≤ G_K`, so cocycles on such an `H` are additive, a coboundary on such an
`H` is the zero function, and `toClass` is exactly the projection onto `H¹`. -/
theorem exists_pair_localAxioms_and_unramifiedOrthogonal_of_family
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (F : ∀ H : Subgroup (Ω ≃ₐ[k] Ω),
      Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p]
        (Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p] ZMod p))
    (hF : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
        H = SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
      ∀ x, (∀ y, F H x y = 0) → x = 0)
    (hU : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ∀ x ∈ Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      ∀ y ∈ Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        F (SSGRoute.decomp k A ⊓ K.fixingSubgroup) x y = 0) :
    ∃ pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p,
      ZDataMup.IsLocalTateSystem p k Ω K pair ∧ IsUnramifiedOrthogonal (p := p) K pair := by
  classical
  refine ⟨fun H a b => F H (toClass p k Ω K (ZMod p) H a) (toClass p k Ω K (ZMod p) H b),
    ZDataMup.isLocalTateSystem_of_family p k Ω K ζ hζ hζK F hF, ?_⟩
  intro A hA a b ha hb hia hib
  have hle : SSGRoute.decomp k A ⊓ K.fixingSubgroup ≤ K.fixingSubgroup := inf_le_right
  have hmA : toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a ∈
      Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
    rw [Work.SSGRoute.ZSplit.toClass_mem_unramifiedSubgroup_iff p k Ω K A _ hle ha]
    intro σ hσ hi
    exact hia σ hσ.2 hi
  have hmB : toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b ∈
      Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
    rw [Work.SSGRoute.ZSplit.toClass_mem_unramifiedSubgroup_iff p k Ω K A _ hle hb]
    intro σ hσ hi
    exact hib σ hσ.2 hi
  exact hU A hA _ hmA _ hmB


/-- Finiteness of the level-`K` local `H¹` at a level-`K` local group, for the coefficient module
`ZMod p` carrying the action of the statement.  This is `Work.SSGRoute.LTDRefs.levelK_finite`
(the arithmetic input `Work.SSGRoute.finite_openKernel_homs_decomp_kernel`, i.e.
`D_A ⊓ G_K ≅ Gal(κ̄/κ)` for the completion `κ = K_𝔭` and finiteness of the continuous homs of a
local Galois group into a finite module). -/
theorem finite_H1loc_localGroup (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Finite (Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :=
  Work.SSGRoute.LTDRefs.levelK_finite p k Ω K A hA (ZMod p)

/-- The level-`K` local `H¹` at a level-`K` local group is finite-dimensional. -/
theorem finiteDimensional_H1loc_localGroup (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    FiniteDimensional (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) := by
  haveI := finite_H1loc_localGroup p k Ω K A hA
  exact Module.Finite.of_finite

/-- **The two arithmetic-free conjuncts of gate (P), from an alternating family and cyclic
unramified subgroups.**

Given, for every subgroup `H` of `G_k`, a bilinear form `F H` on the level-`K` local `H¹`-group
`H¹_loc(H, 𝔽_p)` which is

* non-degenerate in its first variable at every level-`K` local group, and
* *alternating* there (`F H x x = 0`),

and given that the level-`K` unramified subgroup `unramifiedSubgroup p k Ω K A (D_A ⊓ G_K)` at every
finite place is *cyclic* (`= 𝔽_p ∙ u` for some `u`), the descended pairing
`pair H a b := F H (toClass a) (toClass b)` satisfies the local axioms `IsLocalTateSystem` and the
unramified orthogonality `IsUnramifiedOrthogonal`.

The point of the alternating hypothesis is the orthogonality: at a finite place `A` with local group
`H = D_A ⊓ G_K`, a locally constant cocycle on `H` vanishing on `H ⊓ I_A` represents a *member of
the cyclic* subgroup `unramifiedSubgroup p k Ω K A H` (`ZSplit.toClass_mem_unramifiedSubgroup_iff`),
so both arguments of the pairing are multiples of the single generator `u`, and bilinearity together
with `F H u u = 0` (alternation) gives the vanishing.  (This care is needed because
`unramifiedSubgroup p k Ω K A H` is *not* independent of the chosen place `A` over a fixed prime of
`K` — see the counterexample in the review of `unramifiedSubgroup_eq_of_localGroup_eq` — so `F H`
must kill every generator occurring, not just the one for a fixed representative; alternation does
this for free.) -/
theorem exists_pair_localAxioms_and_unramifiedOrthogonal_of_alternating
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (F : ∀ H : Subgroup (Ω ≃ₐ[k] Ω),
      Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p]
        (Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p] ZMod p))
    (hF : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
        H = SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
      ∀ x, (∀ y, F H x y = 0) → x = 0)
    (halt : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
        H = SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
      ∀ x, F H x x = 0)
    (hcyc : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ∃ u : Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) = Submodule.span (ZMod p) {u}) :
    ∃ pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p,
      ZDataMup.IsLocalTateSystem p k Ω K pair ∧ IsUnramifiedOrthogonal (p := p) K pair := by
  refine exists_pair_localAxioms_and_unramifiedOrthogonal_of_family p k Ω K ζ hζ hζK F hF ?_
  intro A hA x hx y hy
  obtain ⟨u, hu⟩ := hcyc A hA
  rw [hu] at hx hy
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hy
  have huu : (F (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) u u = 0 := halt _ ⟨A, hA, rfl⟩ u
  rw [← hc, ← hd]
  simp only [map_smul, LinearMap.smul_apply, huu, smul_zero]


/-- **The two arithmetic-free conjuncts of gate (P), from the parity of the level-`K` local `H¹`.**

Given that the level-`K` local `H¹` at every finite place is finite-dimensional of *even* dimension
(then `bilinForm_alternating_of_even_finrank` produces an alternating, left-non-degenerate form on
it, and `h1loc_finrank_trivialAction` shows that this dimension is independent of the coefficient
module used), and given that the level-`K` unramified subgroup is cyclic, the local axioms and the
unramified orthogonality of gate (P) hold.

The two hypotheses are the arithmetic content of (i)+(iii); (ii) (`IsProductFormula`) is *not*
touched by this theorem -- it is the Hilbert-symbol product formula, i.e. the reciprocity law, and
is the remaining obligation of the gate. -/
theorem exists_pair_localAxioms_and_unramifiedOrthogonal_of_even
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (heven : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A),
      Even (Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup))))
    (hcyc : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ∃ u : Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) = Submodule.span (ZMod p) {u}) :
    ∃ pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p,
      ZDataMup.IsLocalTateSystem p k Ω K pair ∧ IsUnramifiedOrthogonal (p := p) K pair := by
  classical
  -- the alternating family: at a level-`K` local group `H`, take the form produced by the parity
  let F : ∀ H : Subgroup (Ω ≃ₐ[k] Ω),
      Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p]
        (Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p] ZMod p) := fun H =>
    if h : ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
        H = SSGRoute.decomp k A ⊓ K.fixingSubgroup then
      haveI : FiniteDimensional (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) :=
        h.choose_spec.2.symm ▸ finiteDimensional_H1loc_localGroup p k Ω K h.choose h.choose_spec.1
      Classical.choose (bilinForm_alternating_of_even_finrank p hp
        (h.choose_spec.2.symm ▸ heven h.choose h.choose_spec.1))
    else 0
  have hF : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
        H = SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
      ∀ x, (∀ y, F H x y = 0) → x = 0 := by
    intro H hH x hx
    haveI : FiniteDimensional (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) :=
      hH.choose_spec.2.symm ▸ finiteDimensional_H1loc_localGroup p k Ω K hH.choose hH.choose_spec.1
    have h1 : F H = Classical.choose (bilinForm_alternating_of_even_finrank p hp
        (hH.choose_spec.2.symm ▸ heven hH.choose hH.choose_spec.1)) := by
      simp only [F, dif_pos hH]
    rw [h1] at hx
    exact (Classical.choose_spec (bilinForm_alternating_of_even_finrank p hp
      (hH.choose_spec.2.symm ▸ heven hH.choose hH.choose_spec.1))).1 x hx
  have halt : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
        H = SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
      ∀ x, F H x x = 0 := by
    intro H hH x
    haveI : FiniteDimensional (ZMod p) (Work.SSGRoute.H1loc p k Ω K (ZMod p) H) :=
      hH.choose_spec.2.symm ▸ finiteDimensional_H1loc_localGroup p k Ω K hH.choose hH.choose_spec.1
    have h1 : F H = Classical.choose (bilinForm_alternating_of_even_finrank p hp
        (hH.choose_spec.2.symm ▸ heven hH.choose hH.choose_spec.1)) := by
      simp only [F, dif_pos hH]
    rw [h1]
    exact (Classical.choose_spec (bilinForm_alternating_of_even_finrank p hp
      (hH.choose_spec.2.symm ▸ heven hH.choose hH.choose_spec.1))).2 x
  exact exists_pair_localAxioms_and_unramifiedOrthogonal_of_alternating p hp k Ω K ζ hζ hζK
    F hF halt hcyc


/-- **(i) and (iii) of gate (P), unconditionally.**

There is a single family of local pairings at the level-`K` local groups satisfying the local Tate
axioms `ZDataMup.IsLocalTateSystem` and the unramified orthogonality
`Work.SSGRoute.IsUnramifiedOrthogonal`: take, at each level-`K` local group, a *non-degenerate
alternating* form on the level-`K` local `H¹` (`exists_pair_localAxioms_and_unramifiedOrthogonal_of_even`,
using the parity `even_finrank_H1loc_levelK` and the linear algebra
`bilinForm_alternating_of_even_finrank`), and pair two cocycles by the classes they represent.

The unramified orthogonality is where the alternation is used: the level-`K` unramified subgroup is
*cyclic* (`unramifiedSubgroup_isCyclic`), so both arguments lie in a single line `𝔽_p ∙ u` and the
bilinearity together with `F u u = 0` gives the vanishing.  (The unramified subgroup is *not*
constant in the place among places with the same level-`K` local group, so this is genuinely
needed; see the module docstring.)

The remaining, genuinely arithmetic conjunct of the gate is (ii) `IsProductFormula` — the
Hilbert-symbol product formula, i.e. the reciprocity law. -/
theorem exists_pair_localAxioms_and_unramifiedOrthogonal
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    ∃ pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p,
      ZDataMup.IsLocalTateSystem p k Ω K pair ∧ IsUnramifiedOrthogonal (p := p) K pair :=
  exists_pair_localAxioms_and_unramifiedOrthogonal_of_even p hp k Ω K ζ hζ hζK
    (fun A hA => even_finrank_H1loc_levelK p hp k Ω K ζ hζ hζK A hA)
    (fun A hA => unramifiedSubgroup_isCyclic p k Ω K A hA)

/-- **The master reduction: gate (P) of the node, from a single family of forms carrying the three
properties.**

This is the exact remaining obligation of the node, in the `H1loc`-form on which the arithmetic
acts.  A family

`F H : H1loc p k Ω K (ZMod p) H →ₗ (H1loc p k Ω K (ZMod p) H →ₗ ZMod p)`

with

* (1) `F H` non-degenerate in its first variable at every level-`K` local group
  `H = decomp k A ⊓ K.fixingSubgroup`,
* (3) `F (decomp k A ⊓ K.fixingSubgroup)` vanishing on the level-`K` unramified subgroup
  `unramifiedSubgroup p k Ω K A (decomp k A ⊓ K.fixingSubgroup)` in both variables, and
* (2) the reciprocity sum `∑_{A ∈ T'} F (decomp k A ⊓ K.fixingSubgroup) [a] [b] = 0` for global
  cocycles `a`, `b` unramified outside a one-sided place set `T'`

produces the gate: `pair H a b := F H [a] [b]` satisfies (i) (`IsLocalTateSystem`, by
`ZDataMup.isLocalTateSystem_of_family`), (ii) (`IsProductFormula`, clause (2)) and (iii)
(`IsUnramifiedOrthogonal`, clause (3)).

The three clauses are not interchangeable: (1) and (3) are free (an *alternating* left-non-degenerate
form always works, `exists_pair_localAxioms_and_unramifiedOrthogonal`), while (2) is the
Hilbert-symbol product formula and pins `F` down (see the module docstring, and the warning of
`coker_obstruction.lean`).  So the whole content of the node is the existence of an `F` with all
three clauses; this theorem is the wrapper that turns such an `F` into the gate. -/
theorem auxPairingGate_of_reciprocityFamily
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (F : ∀ H : Subgroup (Ω ≃ₐ[k] Ω),
      Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p]
        (Work.SSGRoute.H1loc p k Ω K (ZMod p) H →ₗ[ZMod p] ZMod p))
    (hF : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
        H = SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
      ∀ x, (∀ y, F H x y = 0) → x = 0)
    (hU : ∀ (A : ValuationSubring Ω), SSGRoute.IsFinPlace k A →
      ∀ x ∈ Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      ∀ y ∈ Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        F (SSGRoute.decomp k A ⊓ K.fixingSubgroup) x y = 0)
    (hrec : ∀ (a b : (Ω ≃ₐ[k] Ω) → ZMod p),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup a →
      SSGRoute.IsLocConstOn K.fixingSubgroup a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b →
      SSGRoute.IsLocConstOn K.fixingSubgroup b →
      ∀ (T' : Finset (ValuationSubring Ω)), (∀ A ∈ T', SSGRoute.IsFinPlace k A) →
      (∀ A ∈ T', ∀ B ∈ T',
        (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T', ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
      ∑ A ∈ T', F (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)
        (Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b) = 0) :
    AuxPairingGate (p := p) K := by
  classical
  refine ⟨fun H a b => F H (Work.SSGRoute.toClass p k Ω K (ZMod p) H a)
    (Work.SSGRoute.toClass p k Ω K (ZMod p) H b), ?_, ?_, ?_⟩
  · exact ZDataMup.isLocalTateSystem_of_family p k Ω K ζ hζ hζK F hF
  · intro a b ha hla hb hlb T' hTfin hTdisj hunram
    exact hrec a b ha hla hb hlb T' hTfin hTdisj hunram
  · intro A hA a b ha hb hia hib
    have hle : SSGRoute.decomp k A ⊓ K.fixingSubgroup ≤ K.fixingSubgroup := inf_le_right
    have hmA : Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a ∈
        Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
      rw [Work.SSGRoute.ZSplit.toClass_mem_unramifiedSubgroup_iff p k Ω K A _ hle ha]
      intro σ hσ hi
      exact hia σ hσ.2 hi
    have hmB : Work.SSGRoute.toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b ∈
        Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
      rw [Work.SSGRoute.ZSplit.toClass_mem_unramifiedSubgroup_iff p k Ω K A _ hle hb]
      intro σ hσ hi
      exact hib σ hσ.2 hi
    exact hU A hA _ hmA _ hmB

/-- The three conjuncts of `AuxPairingGate`, named: this exhibits the gate as `(i) + (ii) + (iii)`
with no hidden content. -/
theorem auxPairingGate_of_conjuncts (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hlocal : ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hprod : ZDataMup.IsProductFormula p k Ω K pair)
    (hunram : IsUnramifiedOrthogonal (p := p) K pair) :
    AuxPairingGate (p := p) K :=
  ⟨pair, hlocal, hprod, hunram⟩

/-- **The level-`K` product formula implies the `ZDataMup` product formula.**  `IsProductFormula`
asks the two global cocycles to vanish on the whole inertia at the places outside `T'` — for *all*
`σ : Ω ≃ₐ[k] Ω` — whereas `HasLevelKReciprocity` asks this only for `σ ∈ G_K`; so the former has
the stronger hypothesis and is implied by the latter.  The two spellings of level-`K` conjugacy
agree by `Work.SSGRoute.ZSplit.exists_forall_mem_iff_smul_eq`. -/
theorem hasLevelKReciprocity_imp_isProductFormula
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) →
      ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (h : Work.SSGRoute.ZSplit.HasLevelKReciprocity p k Ω K pair) :
    ZDataMup.IsProductFormula p k Ω K pair := by
  intro a b ha hla hb hlb T' hTfin hTdisj hTunram
  refine h a b ha hla hb hlb T' hTfin ?_ ?_
  · intro A hA B hB hc
    exact hTdisj A hA B hB
      ((Work.SSGRoute.ZSplit.exists_forall_mem_iff_smul_eq K A B).mpr hc)
  · intro B hB hnot σ hσK hσI
    exact hTunram B hB
      (fun A hA hc => hnot A hA ((Work.SSGRoute.ZSplit.exists_forall_mem_iff_smul_eq K A B).mp hc))
      σ hσI

/-- **Gate (P) at level `K` from the gate at the base field `↥K` (trivial extension `⊥`).**

This is the `K`-free form of the target: `Work.SSGRoute.ZSplit.levelK_reciprocity_baseChange` shows
that the level-`K` local Tate system and the level-`K` product formula are the *generic* statements
instantiated at the base field `↥K` with the trivial extension `⊥` (where
`(⊥ : IntermediateField ↥K Ω).fixingSubgroup = ⊤`), transported along the isomorphism
`K.fixingSubgroup ≃* (Ω ≃ₐ[↥K] Ω)`.  The witness-exposed version of that transport is
`Work.SSGRoute.ZConstruction.levelK_reciprocity_lkPair`, and the unramified orthogonality transports
as `Work.SSGRoute.ZConstruction.unramifiedOrthogonal_lkPairTransport`.

So the whole arithmetic of gate (P) is concentrated in the *base* instance: a pairing `pair'` on
the cocycles of `G_{↥K}` with the local Tate axioms, the product formula (Hilbert reciprocity for the
odd prime `p`, i.e. `∑_v (α, β)_v = 0` on global classes) and the unramified orthogonality. -/
theorem auxPairingGate_of_baseGate
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair' : Subgroup (Ω ≃ₐ[↥K] Ω) → ((Ω ≃ₐ[↥K] Ω) → ZMod p) →
      ((Ω ≃ₐ[↥K] Ω) → ZMod p) → ZMod p)
    (hloc : ZDataMup.IsLocalTateSystem p ↥K Ω (⊥ : IntermediateField ↥K Ω) pair')
    (hprod : ZDataMup.IsProductFormula p ↥K Ω (⊥ : IntermediateField ↥K Ω) pair')
    (hunr : IsUnramifiedOrthogonal (p := p) (K := (⊥ : IntermediateField ↥K Ω)) pair') :
    AuxPairingGate (p := p) K := by
  obtain ⟨hTate, hrec⟩ :=
    levelK_reciprocity_lkPair p k Ω K pair' hloc hprod
  refine ⟨Work.SSGRoute.ZSplit.lkPair p k Ω K pair', ?_, ?_, ?_⟩
  · exact (Work.SSGRoute.ZSplit.isLevelKLocalTateSystem_iff_isLocalTateSystem
      p k Ω K _).mp hTate
  · exact hasLevelKReciprocity_imp_isProductFormula p k Ω K _ hrec
  · exact unramifiedOrthogonal_lkPairTransport p k Ω K pair' hunr

section OddAlternating

open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup.OddForm

set_option maxHeartbeats 1000000 in
/-- **The odd-`p` local pairing `oPairForm` is *alternating*** (`oPairForm x x = 0`).

Mathematically this is the identity `(α, α)_𝔭 = (α, -1)_𝔭 = 1` of the `p`-th power Hilbert symbol
for odd `p`: for odd `p` the element `-1 = (-1)^p` is a `p`-th power, so the Hilbert symbol is
alternating.  In the `hLevel`/`oPair` vocabulary of the odd-`p` lane the proof is:

* `oPair x x = (oChar x (oFactor x α)).toAdd` with `α = hLift ζ hζ A hA x`
  (`Work.SSGRoute.ZDataMup.LTRecFamHonest.hLift`, the coherent lift of the class `x`) and
  `hLevel α = oLevel x`;
* if `α ∈ (↥Kˣ)^p` the Kummer level is `⊥` (degenerate), so `localPowClass α = 1` and
  `oFactor x α = 1` (`oddLocalFactor_eq_one_of_localPowClass_eq_one`);
* otherwise `α = N_{hLevel α / ↥K}(-α^{1/p+…})` is a global — hence local — norm
  (`Work.SSGRoute.ZConstruction.aux_norm_kummerSqrt_gen`), so
  `localImageAt_𝔭 α ∈ localNormSubgroup`
  (`Work.SSGRoute.ZConstruction.aux_localImageAt_mem_localNormSubgroup_hLevel_of_notMem`) and the
  local factor of the Artin map kills it
  (`Work.SSGRoute.ZDataMup.LTRecFamHonest.hLocalFactor_eq_one_of_mem_localNormSubgroup`, the Artin
  map killing the idèlic norms): `oFactor x α = 1`;
* `oChar x` is a monoid homomorphism, so `oChar x 1 = 1` and `.toAdd 1 = 0`.

The alternation is the arithmetic input of the *unramified orthogonality* (iii) of the gate: the
level-`K` unramified subgroup is cyclic (`Work.SSGRoute.ZConstruction.unramifiedSubgroup_isCyclic`),
so `F (c • u) (d • u) = cd · F u u = 0` for a generator `u`, which is exactly
`IsUnramifiedOrthogonal` for the descended pairing. -/
theorem oPairForm_self_eq_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {A : ValuationSubring Ω} (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (hA : SSGRoute.IsFinPlace k A)
    (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x x = 0 := by
  have hfac : oFactor ζ hζ hA x (hLift ζ hζ A hA x) = 1 := by
    by_cases hα : hLift ζ hζ A hA x ∈ NK.LocalAnabelian.powSubgroup p ↥K
    · obtain ⟨c, hc⟩ := hα
      simp only [NK.LocalAnabelian.powSubgroup, MonoidHom.mem_range, powMonoidHom_apply] at hc
      refine oddLocalFactor_eq_one_of_localPowClass_eq_one ζ hζ hA x _ ?_
      rw [← hc]
      haveI : IsMulCommutative (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥K) (oddPrime (K := K) A hA))ˣ :=
        ⟨⟨fun a b => Units.ext (by rw [Units.val_mul, Units.val_mul]; exact mul_comm _ _)⟩⟩
      haveI : (NK.UchidaKummer.ellPowSubgroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion (↥K) (oddPrime (K := K) A hA)) p).Normal :=
        Subgroup.normal_of_comm _
      show QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup
          ((oddPrime A hA).adicCompletion ↥K) p)
          (Units.map (algebraMap ↥K ((oddPrime A hA).adicCompletion ↥K)).toMonoidHom (c ^ p)) = 1
      rw [map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨Units.map (algebraMap ↥K ((oddPrime A hA).adicCompletion ↥K)).toMonoidHom c,
        by rw [powMonoidHom_apply]⟩
    · have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ :=
        Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA
      haveI hfdL : FiniteDimensional ↥K
          ↥(hLevel (K := K) (Ω := Ω) (p := p) (hLift ζ hζ A hA x)) :=
        hLevel_finiteDimensional ζ hζ _
      haveI hgalL : IsGalois ↥K
          ↥(hLevel (K := K) (Ω := Ω) (p := p) (hLift ζ hζ A hA x)) :=
        hLevel_isGalois ζ hζ _
      haveI hnfL : NumberField
          ↥(hLevel (K := K) (Ω := Ω) (p := p) (hLift ζ hζ A hA x)) :=
        hLevel_numberField ζ hζ _
      have hcomm := hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) ζ hζ (hLift ζ hζ A hA x)
      have hmem := Work.SSGRoute.ZConstruction.aux_localImageAt_mem_localNormSubgroup_hLevel_of_notMem
        ζ hζ hp A hA hAK (hLift ζ hζ A hA x) hα
      have hΦ : ∀ y ∈ NK.GlobalCFT.Idele.normImage ↥K
          ↥(hLevel (K := K) (Ω := Ω) (p := p) (hLift ζ hζ A hA x)),
          Work.SSGRoute.ZDataMup.oddArtin (K := K)
            (hLevel (K := K) (Ω := Ω) (p := p) (hLift ζ hζ A hA x)) hcomm y = 1 := by
        intro y hy
        rw [NK.GlobalCFT.Idele.normImage_eq_range, MonoidHom.mem_range] at hy
        obtain ⟨z, rfl⟩ := hy
        exact Work.SSGRoute.ZDataMup.oddArtin_norm (K := K)
          (hLevel (K := K) (Ω := Ω) (p := p) (hLift ζ hζ A hA x)) hcomm z
      rw [show oFactor ζ hζ hA x (hLift ζ hζ A hA x) =
          hLocalFactor A hA (hLevel (K := K) (Ω := Ω) (p := p) (hLift ζ hζ A hA x))
            (Work.SSGRoute.ZDataMup.oddArtin (K := K)
              (hLevel (K := K) (Ω := Ω) (p := p) (hLift ζ hζ A hA x)) hcomm)
            (hLift ζ hζ A hA x) from rfl]
      exact hLocalFactor_eq_one_of_mem_localNormSubgroup (K := K) hA _
        (Work.SSGRoute.ZDataMup.oddArtin (K := K)
          (hLevel (K := K) (Ω := Ω) (p := p) (hLift ζ hζ A hA x)) hcomm) hΦ _ hmem
  rw [oPairForm_apply]
  show (oChar ζ hζ hA x (oFactor ζ hζ hA x (hLift ζ hζ A hA x))).toAdd = 0
  rw [hfac, map_one, toAdd_one]

end OddAlternating

/-- Gate (P) of the node `Work.SSGRoute.shafarevich_z_construction`: the *canonical* level-`K`
local Tate pairing on the trivial module `ZMod p` (`K ∋ ζ_p`), with (i) the local axioms at every
level-`K` local group `decomp k A ⊓ K.fixingSubgroup` (bilinearity on cocycles, vanishing on a
coboundary, non-degeneracy), (ii) the Hilbert-symbol product formula for global cocycles on `G_K`
unramified outside a finite place set, and (iii) the *unramified orthogonality*
(`Work.SSGRoute.IsUnramifiedOrthogonal`): the pairing of two classes that are both trivial on the
inertia vanishes (this is `Br(K_𝔭^{un}/K_𝔭) = 0`, the local input of the p. 18 chase).

The pairing is *not* an arbitrary dimension-count form: the product formula is what pins it down
(the workspace's `coker_obstruction.lean:206` warns that dimension-count pairings cannot be used).
This is the odd-`p` case; the `p = 2` sibling carries the archimedean corrections. -/
theorem levelK_pairing_productFormula (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    Work.SSGRoute.AuxPairingGate (p := p) K := by
  classical
  haveI hNFK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  haveI hSepK : IsSepClosure ↥K Ω := by
    have : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
    exact IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  haveI hSepk : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  haveI hAlgC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  -- the primitive root of unity, read in `↥K`
  obtain ⟨ζK, hζKdef⟩ : ∃ ζ' : ↥K, (ζ' : Ω) = ζ := ⟨⟨ζ, hζK⟩, rfl⟩
  have hζK' : IsPrimitiveRoot ζK p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω)
      (show IsPrimitiveRoot ((ζK : Ω)) p from hζKdef ▸ hζ)
      (algebraMap ↥K Ω).injective
  -- the place-indexed family of bilinear forms: the odd-`p` (Hilbert symbol) pairing
  obtain ⟨F, hFcomp⟩ := Work.SSGRoute.ZDataMup.exists_levelFamily_of_placeFamily
    (p := p) (k := k) (Ω := Ω) K
    (fun A hA => Work.SSGRoute.ZDataMup.OddForm.oPairForm (K := K) (p := p) (k := k) (Ω := Ω)
      ζK hζK' hA)
  refine ⟨fun H a b => F H (toClass p k Ω K (ZMod p) H a) (toClass p k Ω K (ZMod p) H b),
    ?_, ?_, ?_⟩
  · -- (i) the local axioms
    refine ZDataMup.isLocalTateSystem_of_family p k Ω K ζ hζ hζK F ?_
    intro H hH x hx
    obtain ⟨A, hA, rfl⟩ := hH
    refine Work.SSGRoute.ZDataMup.OddForm.oPairForm_nondegenerate (K := K) (p := p) (k := k)
      (Ω := Ω) ζK hζK' hA x ?_
    intro y
    rw [← hFcomp A hA x y]
    exact hx y
  · -- (ii) the Hilbert-symbol product formula
    intro a b ha hla hb hlb T' hTfin hTdisj hunr
    show ∑ A ∈ T', F (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      (toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)
      (toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b) = 0
    -- on `G_K = K.fixingSubgroup` the restriction `res k K` is trivial, so `a` and `b` are additive
    have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
      IntermediateField.restrictNormalHom_ker K
    have hz : ∀ (z : (Ω ≃ₐ[k] Ω) → ZMod p),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z →
        ∀ g ∈ K.fixingSubgroup, ∀ h' ∈ K.fixingSubgroup, z (g * h') = z g + z h' := by
      intro z hz g hg h' hh'
      have hg1 : SSGRoute.res k K g = 1 := by
        have hg' : g ∈ (SSGRoute.res k K).ker := by rw [hker]; exact hg
        simpa using hg'
      rw [hz g hg h' hh', hg1, one_smul]
    -- the global Kummer elements of `a` and `b`
    obtain ⟨α, hα⟩ := Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
      p k Ω K ζK hζK' a (hz a ha) hla
    obtain ⟨β, hβ⟩ := Work.SSGRoute.ZDataMup.KummerSurjectivity.kummerCharZMod_surjective_levelK
      p k Ω K ζK hζK' b (hz b hb) hlb
    -- rewrite the sum over the level family as the sum of the odd-`p` pairings over `T'`
    have hsum : (∑ A ∈ T', F (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)
        (toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b)) =
        ∑ A ∈ T'.attach, Work.SSGRoute.ZDataMup.OddForm.oPairForm (K := K) (p := p) (k := k)
          (Ω := Ω) ζK hζK' (hTfin A.1 A.2)
          (toClass p k Ω K (ZMod p) (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) a)
          (toClass p k Ω K (ZMod p) (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) b) := by
      rw [← Finset.sum_attach T' (fun A => F (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)
        (toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b))]
      exact Finset.sum_congr rfl fun A _ => hFcomp A.1 (hTfin A.1 A.2) _ _
    rw [hsum]
    -- the reciprocity sum at the Kummer level of `α`: the local factors outside `T'` are trivial
    exact Work.SSGRoute.ZDataMup.OddForm.oPairForm_sum_attach_eq_zero_of_outside
      (K := K) (p := p) (k := k) (Ω := Ω) ζK hζK' a b α β ha hla hb hlb hα hβ T' hTfin hTdisj
      (fun v hv => Work.SSGRoute.ZDataMup.OddForm.oTheta_eq_one_of_ne_oddPrime hp ζK hζK'
        a b α β hα hβ T' hTfin hunr v hv)
  · -- (iii) the unramified orthogonality, from the alternation and the cyclicity of `U_A`
    intro A hA a b ha hb hia hib
    show F (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      (toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)
      (toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b) = 0
    obtain ⟨u, hu⟩ := unramifiedSubgroup_isCyclic p k Ω K A hA
    have hle : SSGRoute.decomp k A ⊓ K.fixingSubgroup ≤ K.fixingSubgroup := inf_le_right
    have hmA : toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a ∈
        Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
      rw [Work.SSGRoute.ZSplit.toClass_mem_unramifiedSubgroup_iff p k Ω K A _ hle ha]
      intro σ hσ hi
      exact hia σ hσ.2 hi
    have hmB : toClass p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b ∈
        Work.SSGRoute.ZSplit.unramifiedSubgroup p k Ω K A
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
      rw [Work.SSGRoute.ZSplit.toClass_mem_unramifiedSubgroup_iff p k Ω K A _ hle hb]
      intro σ hσ hi
      exact hib σ hσ.2 hi
    rw [hu] at hmA hmB
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmA
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hmB
    have huu : F (SSGRoute.decomp k A ⊓ K.fixingSubgroup) u u = 0 := by
      rw [hFcomp A hA u u]
      exact oPairForm_self_eq_zero (K := K) (p := p) (k := k) (Ω := Ω) (A := A) hp ζK hζK' hA u
    rw [← hc, ← hd]
    simp only [map_smul, LinearMap.smul_apply, huu, smul_zero]

end Work.SSGRoute.ZConstruction
