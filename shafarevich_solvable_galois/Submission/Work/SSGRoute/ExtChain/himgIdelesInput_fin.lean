import Mathlib
import Submission.Work.SSGRoute.PTdualControl.extExact
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.SSGStage.e1aLandingFinCompat
import Submission.Work.SSGRoute.ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp
import Submission.Work.SSGRoute.extToIdeles_eq_zero_iff_extLoc
import Submission.Work.SSGRoute.PT.pt_pairing_ext
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
import Submission.Work.SSGRoute.ExtChain.deltaH2_restrictSES_e1aSES_injective
import Submission.Work.SSGRoute.ExtChain.shift_symm_extToIdeles_eq_zero_gen
import Submission.Work.SSGRoute.ExtChain.subsingleton_ext_dualMod_regular_rankOne
import Submission.Work.SSGRoute.ExtChain.himgLeafCore
import Submission.Work.SSGRoute.ExtChain.resH1_e1cMap_eq_zero_of_invariant_lift
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
import Submission.Work.SSGRoute.PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf
import Submission.Work.SSGRoute.ExtChain.himgIdelesInput_fin_leaf
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

-- the `Additive Ωˣ` / `Ωˣ` action instances are only equal up to unfolding the transport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## Roadmap for the gluing step, and a measured warning (item 1)

The target is now reduced (see the two reduction lemmas below) to

    for every `G`-equivariant `w : R.V → C_K`,   `resH1_{D_A} (e1cMap R (extDelta w)) = 0`,

and the two identification lemmas above supply the *invariant coefficient module*
`Hom_ℤ(R.V, Ω^{D_A ⊓ G_K}) = Hom_ℤ(R.V, (K·Ω^{D_A})ˣ)` (fixed points = values in the fixed field,
plus the compositum identification `Ω^{H ⊓ G_K} = Ω^H · K`).

**Warning (measured 2026-10-02, on the way to item 1).**  The five-term-sequence step at `D_A`
must be carried out in the **continuous** model.  The workspace's Hilbert-90 vanishing
`ExtChain.subsingletonH1_homCoind_of_le_ker` is a statement about `Work.AbsoluteKummer.H1`, that is
`Z¹_c ⧸ B¹_c` (`Submission/Work/AbsoluteKummer/Defs.lean:249`), whereas
`Work.GroupCohomology.infH1_bijective_of_subsingleton` (the abstract inflation–restriction
isomorphism) is stated for `Work.GroupCohomology.H1 = Z¹ ⧸ B¹`
(`Submission/Work/GroupCohomology/Basic.lean:217`).  The forgetful map `akToGCH1` between the two is
*only injective* (`Submission/Work/SSGRoute/Sha2Lib/akToGCH1.lean:72`), so the *abstract*
`Subsingleton (GroupCohomology.H1 ↥H M)` is **not** implied by the continuous vanishing — and is
false in general for a non-discrete `H` with infinite discrete coefficients (the abstract `H¹` is
`Z¹/B¹` on *all* cocycles).  Hence an inflation–restriction statement phrased with the abstract
`infH1` is not a consequence of the library, and must not be requested.

**The brick to build** is therefore the continuous counterpart: the inflation map
`infH1_c : H¹_c(D_A ⧸ H, M^H) → H¹_c(D_A, M)` for the continuous cochains (`AbsoluteKummer.H1`),
its injectivity and its exactness at `H¹_c(D_A, M)` (kernel = image) under
`Subsingleton (H¹_c(H, M))`, together with the invariance of the locally-constant condition under
inflation.  With that brick, the identification lemmas above, and the group isomorphism
`D_A ⧸ (D_A ⊓ G_K) ≅ decomp_K(A|_K)`, the target's sharp form
`resH1_{D_A}(e1cMap R z) = 0 ⟺ cc_{K·Ω^{D_A}}(res_{D_q} z) = 0` becomes derivable.

## Session record (2026-10-02b): why the target is global, and what is *not* a proof

Let `G = Gal(K/k)` (finite), `D_A ≤ Γ = Gal(Ω/k)` the decomposition group of the finite place `A`,
`H = D_A ∩ G_K ◁ D_A` (normal, `G_K ◁ Γ`), `D_q = D_A/H ≤ G` and `L = K·Ω^{D_A} = Ω^H` (the
algebraic "decomposition compositum", `fixedField_inf_fixingSubgroup` below).  `L/Z` with
`Z = Ω^{D_A}` is finite Galois of group `D_q`, and `L ⊆ K_q` for the completion `K_q` of `K` at the
place below `A` (the completion of `Z` is the *base* local field `k_p`).

1. **The one-place formal route is refuted.**  `𝕀_K → K_qˣ` (the `q`-component) is `D_q`-equivariant
   and restricts to the diagonal on `Kˣ`, so a commutative square of short exact sequences
   `(Kˣ → 𝕀_K → C_K) → (Kˣ → K_qˣ → K_qˣ/Kˣ)` exists; the naturality of connecting maps then gives
   `cc_{K_q}(res_{D_q} z) ∈ im(δ)` and hence only the *completion* condition `z_q = 0` — which is
   exactly the refuted per-place form (session 11, quaternion class `(-1,-1)` over `ℚ(i)` at `3`).
   Any proof must therefore use the vanishing at *all* places, i.e. the fact
   `ker(extToIdeles) = im(extDelta)` (both the exactness of the class formation and the *injectivity*
   of the idèle localisation `extIdele_localisation_injective_of_finite` are on disk).

2. **The map-of-short-exact-sequences route: a genuine sufficient condition, *not* excluded by the
   counterexample.**  If there is a `D_q`-equivariant retraction `α : 𝕀_K → Lˣ` of the diagonal
   embedding `Kˣ ↪ 𝕀_K` (equivalently: a `D_q`-equivariant `β : C_K → Lˣ/Kˣ` making
   `(Kˣ → 𝕀_K → C_K)` the pullback of `(Kˣ → Lˣ → Lˣ/Kˣ)` along `β`), then the naturality of
   connecting maps gives `δ₁ = δ₂ ∘ β_*`, whence `δ₁(v) ∈ im(δ₂) = ker(cc_L)` for *every*
   `v ∈ Ext⁰_{D_q}(R.V,C_K)`, and in particular `cc_L(res_{D_q} z) = 0` for `z ∈ im(extDelta)`.
   The statement this proves,
   `(P₂)   ker (Ext¹_{D_q}(R.V,Kˣ) --cc_{𝕀_K}--> Ext¹_{D_q}(R.V,𝕀_K)) ⊆ ker (cc_L)`,
   is *strictly weaker* than the refuted per-place statement
   `(P₁)   ker (cc_{K_q}) ⊆ ker (cc_L)`:
   indeed `cc_{K_q}` factors through `cc_{𝕀_K}` (the `q`-component is `D_q`-equivariant), so
   `ker cc_{𝕀_K} ⊆ ker cc_{K_q}`, and the refuting quaternion class is ramified over `2`, i.e. it is
   *not* in `ker cc_{𝕀_K}` (that would contradict Hasse's theorem `Br(K) ↪ ⊕_v Br(K_v)`).  So the
   session-11 counterexample does **not** refute this route: `α` is a legitimate *candidate*
   intermediate statement.  What makes it hard is that `𝕀_K` is a restricted product and `Lˣ` a
   subfield of the completion, so no canonical `α` is visible; and `P₂` with the *specific* `R.V`
   (a syzygy of a `p`-torsion module) is weaker than `P₂` for all `R.V`.

3. **The honest remaining input** is the global localisation statement
   `cc_L(res_{D_q} z) = 0` for `z ∈ ker(extToIdeles)` (equivalently: for every
   `x ∈ Ext¹_G(e1aN0 …, C_K)`, the composite
   `resH1_{D_A} ∘ e1cMap ∘ (e1aSyzShift)⁻¹ ∘ extDelta` vanishes at `x`).  Two routes are recorded
   in the workspace: the Tate–Poitou workshop (`SSGRoute/tatePoitouEmbedding`, still
   `sorryAx`-dependent) and the **dévissage in the coefficient `E`** (`NOTE_devissage_E.md`): the
   base case `E = 𝔽_p[G]` is *vacuous* — `N_E ≅ 𝔽_p[G] ⊗ T^∨` has a two-term resolution by free
   `ℤ[G]`-modules, so `Ext^{≥2}_G(N_E,Kˣ) = 0` and every `z` in question is already `0` (the engine
   of that argument is `himgIdelesInput_fin_of_subsingleton_ext2` below, and the `Ext`-vanishing is
   the delegated `ExtChain.subsingleton_ext_dualMod_regular`) — and the inductive step is the snake
   lemma for the localisation kernels of `0 → E₁ → F → E → 0` together with the *degree-one*
   local–global statement `Work.SSGRoute.hassePrinciple_h1_cocycles` (Chebotarev), which is on disk.

## Session record (2026-10-02c): the continuous five-term step, and the target as an `H²`-statement

New in this stretch (all sorry-free, axioms ⊆ `propext, Classical.choice, Quot.sound`):

* `exists_quotientCocycle_descend`, `H1pi_infCocycle1_c_eq_of_value`,
  `range_infH1_c_eq_ker_resH1` and the unconditional `infH1_c_bijective`: the **continuous
  counterpart of the inflation–restriction exactness**
  `im(infH1_c) = ker(resH1)` for `N ◁ G` open, together with the five-term step
  `H¹_c(G ⧸ N, A^N) ≅ H¹_c(G, A)` when `H¹_c(N, A) = 0`.  This completes the "brick to build"
  announced in the module docstring above; the only genuinely continuous ingredient is that the
  descended primitive is locally constant, which is automatic because `N` open forces `G ⧸ N` to be
  discrete (`QuotientGroup.discreteTopology`).  Compare `Work.GroupCohomology.range_infH1_eq_ker_resH1`
  (the abstract statement, proved the same way without the local-constancy check).
  *(Beware the naming: the workspace also carries delegations `exists_quotientCocycle_descend`,
  `H1pi_infCocycle1_c_eq_of_value`, `range_infH1_c_eq_ker_resH1` under a distinct path, with the
  same content and the same statements; the versions here are the ones this file uses and are
  suffixed `_inline` to avoid a duplicate-declaration clash on assembly.)*

* `resH2_e1aChainH_eq_zero_of_resH1_e1cMap_eq_zero` and
  `resH1_e1cMap_eq_zero_iff_resH2_e1aChainH_eq_zero`: the **converse of the bridge**, hence the
  equivalence

      resH1_D (e1cMap R z) = 0   ⟺   resH2_D (e1aChainH N (e1aSyzShift N z)) = 0

  for `D` closed.  So the finite-place target is *literally* the `H²`/`Sha`-side statement in which
  the dévissage in the coefficient `E` is designed to run; a prover may work on either side.

* **PROVED** (this stretch, by the fleet):
  `SSGRoute/ExtChain/subsingleton_ext_dualMod_regular_rankOne` — the dévissage **base case in
  abstract-group form**: for `finrank_𝔽_p T = 1`,
  `Ext^{≥2}_G(DualMod p (𝔽_p[G] ⊗ T), A) = 0`.  The delivered proof builds the explicit
  `G`-isomorphism `Ψ f = Σ_σ (α σ * f (e_σ ⊗ t₀)) • e_σ` (`α` the character of the line `T`), then
  applies `ext_iso_subsingleton` and `subsingleton_ext_fpRegular`.  This subsumes the stale
  `ExtChain.subsingleton_ext_dualMod_regular` (whose file still carries a `sorry`).

* Delivered (this stretch): `SSGRoute/ExtChain/shift_symm_extToIdeles_eq_zero_gen` — **the connecting
  map of a presentation preserves the localisation kernel** (`δ = (e1aShiftEquiv S hS unitsK 1 _)⁻¹`
  maps `ker (extToIdeles)` into itself), together with its general engine
  `e1aShiftEquiv_natural_coeff` (coefficient naturality of the syzygy shift = associativity of
  `Abelian.Ext.comp`).  This is the connecting half of the snake step of the dévissage in `E`.

* Consequently (new, sorry-free, in this file): `extToIdeles_e1aSyzShift_eq_zero_iff` —

      extToIdeles (e1aSyzShift N z) = 0  ⟺  extToIdeles z = 0

  for `z ∈ Ext¹_G(R_N, Kˣ)`.  Both directions are now *elementary*: `⟸` is the coefficient
  naturality of the shift (`e1aShiftEquiv_natural_coeff`), `⟹` is the delivered connecting brick.
  So the idèle localisation kernel is *shift-invariant* — the `Ш²`-image does not depend on the
  chosen canonical presentation — and the hypothesis `hz` of the target may be replaced by
  `extToIdeles z = 0` (which is how the dévissage consumes it).  This supersedes the heavier route
  through the idèle Shapiro injectivity used in `extToIdeles_e1aSyzShift_eq_zero_imp` above (which
  is kept, as its statement is part of the file's API).

* Also in this file (all sorry-free, axiom-clean):
  * `extToIdeles_extDelta_eq_zero` — the **reverse inclusion** of the exactness of the class
    formation: `extToIdeles (extDelta x) = 0` for every `x ∈ Ext^r_G(M, C_K)`.  This is the
    "formal consequence `extDelta ≫ extToIdeles = 0`" announced (but not stated) in
    `ExtChain/extExact.lean`; with `PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero` it
    makes `im (extDelta) = ker (extToIdeles)` at the `Ext`-level.
  * `e1aSyzShift_extDelta_comm` — the two connecting maps commute: the syzygy shift in the first
    variable `e1aSyzShift N` and the class-formation `extDelta` in the second variable agree up to
    the degree-`0` connecting map of the canonical presentation
    (`(freeCoverSES N).extClass ∘ w`); pure `Ext`-associativity
    (`comp_assoc_of_second_deg_zero`).
  * `exists_extDelta_eq_iff_extToIdeles_e1aSyzShift_eq_zero` — consequently the **two forms of the
    hypothesis are equivalent**:

        z ∈ im (extDelta : Ext⁰_G(R_N,C_K) → Ext¹_G(R_N,Kˣ))  ⟺  extToIdeles (e1aSyzShift N z) = 0.

    So the hypothesis-form target of this file and the unconditional `extDelta`-form used by
    `ExtChain/himgExtDeltaInput_fin.lean` (and by `himg_of_extDelta_input`) carry exactly the same
    content, as `NOTE_himgIdelesInput_inf_reduction.md` §9.1 asserts.
  * `subsingleton_ext_dualMod_e1aN0` — **the dévissage base case in the number-field form**: for
    `T` a `p`-cyclotomic dual (hence a line, `hT.1`) and `E = 𝔽_p[Gal(K/k)]` the regular
    coefficient, `Ext^{≥2}_{Gal(K/k)}(e1aN0 p k Ω K T E, A) = 0`.  This is precisely the statement
    requested by `ExtChain/NOTE_devissage_E.md` §1 (`ExtChain.subsingleton_ext_dualMod_regular`,
    whose file still carries a `sorry`), derived here from the abstract-group rank-one version
    `ExtChain.subsingleton_ext_dualMod_regular_rankOne` (delivered this stretch, 368 lines: it
    builds the explicit `G`-iso `DualMod p (𝔽_p[G] ⊗ T) ≅ 𝔽_p[G]` via `Ψ f = Σ_σ (α σ * f (e_σ ⊗ t₀)) • e_σ`
    with `α` the character of the line `T`).
  * `himgIdelesInput_fin_regular` — **the dévissage base case at the level of the target itself**:
    the finite-place input holds when the coefficient is the regular module
    `E = 𝔽_p[Gal(K/k)]` (instantiation of `himgIdelesInput_fin_of_subsingleton_ext2` at the
    vanishing above).  This is the exact statement a dévissage in `E` would start from.
  * `subsingleton_ext_biprod` — `Subsingleton (Ext^r(X,A)) → Subsingleton (Ext^r(Y,A)) →
    Subsingleton (Ext^r(X ⊞ Y,A))` (transfer along Mathlib's `Ext.biprodAddEquiv`), the step that
    would lift the base case to free coefficients of any rank.
  * Child brick landed independently: `ExtChain/dualMod_tensor_regular_iso`, the `Rep`-isomorphism
    `DualMod p (𝔽_p[G] ⊗ T) ≅ 𝔽_p[G]` for `finrank_𝔽_p T = 1` (the module-theoretic content of the
    base case; now also inside `subsingleton_ext_dualMod_regular_rankOne`).

Nothing of the above touches the arithmetic content: the target remains equivalent to the global
localisation statement of item 3 above, which is blocked on the Poitou–Tate chapter
(`tatePoitouEmbedding` is `sorryAx`-dependent) shared with the Grünwald–Wang lane — see
`NOTE_himgIdelesInput_inf_reduction.md` §9.2 for the precise list of missing chapters.  In
particular the *missing square* that would connect this file's finite-place target to a `G`-level
statement on which the dévissage can run is the level-change square for `e1cMap` along an
*infinite* level extension `K → L = K·Ω^{D_A}` (`NOTE_himg_status_session11.md` §2(b)); the
workspace's `E1aClean.BaseChangeSquare.e1cMap_levelChange_square` covers only *sub*levels `L ⊆ K`.

## Session record (2026-10-02d): the target IS an extension problem, and where the gap really is

**The target is *equivalent* to an explicit extension problem, and both directions of the equivalence
are on disk.**  Write `z = PhiE R y` (`y ∈ Ext⁰_G(R₁,Kˣ)`, `R₁ = ker (freeCover R)`) — this is
available because `PhiE` is surjective.  Then

    resH1_D (e1cMap R (PhiE R y)) = 0   ⟺   ∃ Φ ∈ H⁰(D, Hom_ℤ((E1cF R).V, Ωˣ))  with  Φ ∘ κ_R = ΨE(y),

where `Φ ∘ κ_R = ΨE(y)` is the statement that `Φ` *extends* the `Kˣ`-valued coefficient data `y`
along the syzygy inclusion `κ_R : R₁.V → (E1cF R).V`:
* `⟸` is `ExtChain.resH1_e1cMap_eq_zero_of_extension`
  (`extToIdeles_eq_zero_imp_chainC_locallyTrivial.lean`, proved, sorry-free);
* `⟹` is `E1aClean.exists_invariant_extension_of_resH1_e1cMap_eq_zero`
  (`E1aClean/finLocalCriterion.lean`, proved, sorry-free — exactness of the dualised canonical
  resolution).

So the *whole* content of the finite-place input is an **extension problem**, and the honest
statement of the remaining gap is:

* **hypothesis** (`hz`): `extToIdeles z = 0`, i.e. (`δ_{𝕀_K}(y) = 0`) `y` extends to a
  `G`-equivariant `(E1cF R).V → 𝕀_K` (idèle-valued);
* **conclusion**: `y` extends to a `D_A`-equivariant `(E1cF R).V → Ωˣ` (algebraic-field-valued).

The gap is therefore **not** "per place vs. all places" (that was sessions 11/13) but the passage
`𝕀_K ↝ Ωˣ`: an idèle-valued invariant extension must produce an algebraic-field-valued one.  This is
the same class-formation/Hasse content as before, now in its sharpest form.

**New sorry-free bricks of this session** (in this file):

* `isOpen_subgroupOf_ker_decomp` — `H₀ := (res k K).ker.subgroupOf (decomp k A) = D_A ⊓ Gal(Ω/K)`
  is open in `D_A` (`Gal(Ω/K)` is open in `Γ` and `H₀` is its preimage under `D_A ↪ Γ`);
* `infH1_c_decomp_inf_ker_bijective` — the five-term (inflation–restriction) step at the finite
  place: `infH1_c : H¹_c(D_A ⧸ H₀, Hom(R.V,Ωˣ)^{H₀}) → H¹_c(D_A, Hom(R.V,Ωˣ))` is bijective once
  `H¹_c(H₀, Hom(R.V,Ωˣ)) = 0` (Hilbert 90 at the closed subgroup `H₀ ≤ Gal(Ω/K)`);
* `resH1_e1cMap_eq_zero_of_invariant_extension` — the target's conclusion from the extension
  obligation, in the vocabulary of the target: for any `z` that is `PhiE R y` with `y` admitting a
  `D`-invariant lift `Φ : (E1cF R).V →+ Ωˣ` along `kappa R`, `resH1_D (e1cMap R z) = 0`.

**Delegated (this session)**: `ExtChain.subsingleton_h1_homCoind_decomp_inf_ker` (the Hilbert-90
vanishing at `H₀`) and `ExtChain.homCoind_invariants_decomp_inf_ker_equiv` (the invariant module
`Hom(R.V,Ωˣ)^{H₀} = Hom_ℤ(R.V,(Ω^{H₀})ˣ)`, `Ω^{H₀} = K·Ω^{D_A}`).  Together with the two lemmas
here they give the five-term identification
`H¹(D_A, Hom(R.V,Ωˣ)) ≅ H¹(D_q, Hom_ℤ(R.V,(K·Ω^{D_A})ˣ))`, `D_q = res(D_A)`.  **Both children came
back PROVED**, and the assembled statement —
`ExtChain.finPlaceFiveTerm.infH1_c_decomp_inf_ker_bijective_unconditional` plus
`ExtChain.finPlaceFiveTerm.invariants_decomp_inf_ker_nonempty_equiv`, in
`Submission/Work/SSGRoute/ExtChain/finPlaceFiveTerm.lean` — is sorry-free.  (That file imports this
one and both children; this file must *not* import them, or the dependency cycle is detected.)

**Why the "exponent trick" does not close the gap (analysis, this session).**  One might hope to
combine the `q`-components `Y_q : F.V → K_qˣ` of the G-equivariant idèle extension `Y` with natural
systems of local homs `ψ_q : K_qˣ → Ωˣ`, taking the product over a G-orbit `O` of places.  The
product is automatically `G`-equivariant (hence `D_A`-equivariant), so the extension criterion
applies; but on `κ(R₁.V)` every term of the product acts as the *same* exponent (naturality forces
`ψ_{gq} = g ψ_q g^{-1}`, and `y(R₁.V) ⊆ Kˣ` is `G`-fixed), giving `Φ ∘ κ = y^{|O|}` and hence only
`|O| · resH1_{D_A}(e1cMap R z) = 0`.  A norm argument gives the same shape (`y ^{[K_q:L]}` is also
unavailable: `K_q/L` is an *infinite* extension, so there is no norm).  The remaining freedom
(choosing exponents `a_O` with `Σ |O|a_O = 1`) requires `gcd{|O|} = 1`, which fails e.g. for the
Hilbert class field of a field with class group `(ℤ/2)²`.  Producing `ψ_q` with prescribed values on
`y(R₁.V)` is itself an equivariant extension problem, i.e. it *is* the target.  So the exponent trick
reduces the target to itself; no CFT-free proof comes out of it, consistent with §2 of
`NOTE_himgIdelesInput_inf_reduction.md`.

**A measured warning about the recorded sharp form (★).**  `NOTE_himg_extDelta_session13.md` §2
records the sharp per-place form

    (★)  resH1_{D_A}(e1cMap R z) = 0  ⟺  cc_{K·Ω^{D_A}}(res_{D_q} z) = 0 .

By the criterion above, the left-hand side is `⟺` "`y` extends into `Ωˣ`", while the right-hand
side is `⟺` "`y` extends into `Lˣ`, `L := K·Ω^{D_A}`" (exactness of the LES for the presentation,
as `Lˣ ⊆ Ωˣ`).  Hence (★) is equivalent to the injectivity of

    H¹(D_A, Hom_ℤ(R.V,Lˣ))  ⟶  H¹(D_A, Hom_ℤ(R.V,Ωˣ)) .

That map is injective on the nose in the case of *trivial* action of `D_A` on `R.V` — indeed
`H⁰(D_A, Ωˣ/Lˣ) = 0` because `H⁰(D_A,Ωˣ/Lˣ) ⊆ (Ω^{D_A})ˣLˣ/Lˣ = Lˣ/Lˣ = 0` (`H¹(D_A,Lˣ) = 0` by
Hilbert 90 for the *finite* Galois extension `L/K` with group `D_q`) — but for a twisted coefficient
`(Ωˣ/Lˣ)(χ)`, `χ ≠ 1`, the group `H⁰(D_q,(Ωˣ/Lˣ)(χ))` has the shape
`{m : δm = χ(δ)m}` and is *not* obviously trivial (its vanishing is equivalent to the surjectivity
of `H⁰(D_q,Ωˣ(χ)) → H⁰(D_q,(Ωˣ/Lˣ)(χ))`, i.e. to `H¹(D_q,Lˣ(χ^{-1})) = 0`, which is *false* for
twisted Hilbert 90).  **So (★) with `Lˣ` is not established, and the criterion proved on disk is
the `Ωˣ`-form.**  Any future proof must either prove the injectivity for the *specific* carrier
`R.V` (a syzygy of a `p`-torsion dualised module) or work directly with the `Ωˣ`-criterion above.

## Session record (2026-10-03): the criterion is now an equivalence at the syzygy, and the
"coefficient-field mismatch" is *not* an obstruction

**Two new sorry-free modules/bricks.**

* `Submission/Work/SSGRoute/ExtChain/resH1_e1cMap_eq_zero_of_invariant_lift.lean`:
  * `d0_subgroup_apply`, `resZ1_subgroup_mem_B1` — the `D`-general forms of the `⟨σ⟩`-lemmas of
    `ExtChain/resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero.lean`;
  * `resH1_e1cMap_eq_zero_of_invariant_lift` — the extension criterion
    `resH1_D (e1cMap R (PhiE R w)) = 0` from a `D`-invariant lift, **with only
    `[Module.Finite ℤ R.V]`**: `ExtChain.resH1_e1cMap_eq_zero_of_extension` freed of its
    `[Finite R.V]`, which is *never satisfiable* on the canonical syzygy (`R.V = N.V →₀ ℤ[G]` is a
    finitely generated free `ℤ`-module but an infinite type — `ExtChain.freeCoverSES_finite`).
    The dualised resolution `PT.e1aSESgen` needs the finite index type, so before this session the
    *only* usable criterion was restricted to coefficients that cannot occur;
  * `resH1_e1cMap_eq_zero_of_extRes_map_eq_zero` — the finite-place **square**: for `D ≤ Γ` and
    `Dq ≤ G = K ≃ₐ[k] K` with `res k K '' D ⊆ Dq`, `extRes_{Dq} (PhiE R w) = 0` implies
    `resH1_D (e1cMap R (PhiE R w)) = 0` (finite-place analogue of the proved involution square).

* **The `⟹` direction of the criterion is already on disk** as
  `PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf` (`[Module.Finite ℤ R.V]`
  only — found by the review gate this session).  Hence the criterion is an *equivalence*
  `resH1_D (e1cMap R (PhiE R w)) = 0 ↔ ∃ Φ ∈ H⁰(↥D, Hom_ℤ(F_R,Ωˣ)), Φ ∘ κ_R = ΨE w`
  **at the canonical syzygy**; do not re-delegate the `⟹` half.

**Measured correction (this file, `invariant_lift_values_mem_fixedField`).**  Every `D_A`-invariant
lift is `(Ω^H)ˣ`-valued (`H := D_A ⊓ Gal(Ω/K)`): `H` acts trivially on `(E1cF R).V`, so
`D_A`-invariance gives `h • Φ(v) = Φ(ρ (res h) v) = Φ(v)` for `h ∈ H`.  Consequently the two
descriptions of `resH1_{D_A}(e1cMap R z) = 0` — an `Ωˣ`-valued invariant lift, and an `Lˣ`-valued one
(`L := Ω^H = K·Ω^{D_A}`) — *coincide*; the injectivity
`H¹(D_A, Hom(R.V,Lˣ)) → H¹(D_A, Hom(R.V,Ωˣ))` whose failure session 13 §2 recorded as the reason (★)
was not established is thus a **theorem**, not a gap.  So the target is *equivalent* to the honest
input `cc_L(res_{D_q} z) = 0` of session 13 §2/§3 (it is not a reduction, and it is therefore not
delegatable), while the *location* of the arithmetic is pinned to the finite group
`D_q = res k K '' D_A`: the coefficient `Kˣ` versus `Lˣ` at `D_q`, and not a `K`-versus-`K·Ω^{D_A}`
mismatch of the lift.  For the Kˣ-valued `G`-level form `extRes_{D_q} z = 0` (which the square above
would feed) the review gate measured that it is *over-strong* / probably false, exactly because
`Kˣ ⊊ Lˣ`; it must not be requested as the input of this node.  Details, and the list of what not to
re-request, are in `ExtChain/NOTE_session45_himgFin.md`.

**Also landed this session (in this file):**

* `invariant_lift_values_mem_fixedField_gen` — every `D`-invariant lift is
  `Ω^{D ⊓ Gal(Ω/K)}`-valued (the general form of the `D_A` lemma above);
* **`resH1_e1cMap_eq_zero_iff_exists_fixedField_lift`** — the extension criterion in its sharp
  (coordinate-free `cc_L`) form: `resH1_D (e1cMap R (PhiE R w)) = 0` iff there is a `D`-invariant lift
  `Φ ∈ H⁰(↥D, Hom_ℤ(F_R,Ωˣ))` with `Φ ∘ κ_R = ΨE w` **and** values in `Ω^{D ⊓ Gal(Ω/K)}`.  The `⟹`
  half is `PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf` (`[Module.Finite ℤ
  R.V]` only — found on disk by the review gate this session) together with the values lemma; the `⟸`
  half is the harness criterion.  So the target of this file is *equivalent* to the honest input
  recorded in `NOTE_himg_extDelta_session13.md` §2, and `NOTE_session45_himgFin.md` §6 records a new
  route to it: writing `z = extDelta_G(x)`, the input becomes the vanishing of
  `δ_L(x') ∈ H¹(D_q, Hom_ℤ(R.V,Lˣ))` (`x'` = `x` pushed to `C_L`); the hypothesis supplies the local
  lifts of `x'` at *every* place of `L`; what is left is a Hasse principle for
  `H¹(D_q, Hom_ℤ(R.V,Lˣ))` (equivalently `Ext¹_{ℤ[D_q]}(R.V,Lˣ)`) together with the restricted-product
  condition.

## Session record (2026-10-03, later): the reduction of the target to one arithmetic statement

`himgIdelesInput_fin_of_latticeHasse` (this file, sorry-free, axiom-clean) reduces the target to a
single named statement about the *finite* group `Dq := Subgroup.map (res k K) (decomp k A) ≤ G`:

    (hH)  ∀ y : Ext¹_{Dq}( R|, Kˣ| ),   y ∘ mk₀ (resMap_{Dq} ideleIncl) = 0  ⟹  y = 0
          (R := ker (freeCover (e1aN0 p k Ω K T E)))

This is the exact mirror of the *proved* involution reduction
`ExtChain.himg_involution_input_two_of_latticeHasse`, whose input (the C₂-lattice Hasse principle
`ExtChain.hasseExt1_C2_lattice_general`) is already a theorem.  The proof of the reduction uses only
`extToIdeles_e1aSyzShift_eq_zero_iff`, the functoriality of `extRes` and the proved finite-place
square `ExtChain.resH1_e1cMap_eq_zero_of_extRes_map_eq_zero`; no arithmetic.

`ExtChain/NOTE_himgIdelesInput_fin_reduction_session.md` records the reduction, the review verdict
on the `Kˣ`-form `(hH)` (two reviewers: it is *exactly* the residual input, non-vacuous, but every
proved brick of the family is pinned to `|H| = 2`, so the general case has neither proof nor
counterexample), and the sharp form of the arithmetic: by the syzygy shift and
`Hom_ℤ(N.V,Kˣ) = (E ⊗ T) ⊗ μ_p`, `(hH)` becomes the degree-two local–global statement

    ker( H²(Dq, (E⊗T) ⊗ μ_p) → ∏_v H²(Dq,v, (E⊗T) ⊗ μ_p(K_v)) ) = 0 .

Two routes are recorded there: the lattice Hasse principle at `Dq` via a *group induction* on the
solvable group `Dq ≅ Gal(K_w/k_p)` (base cases: cyclic of prime order; for `ℓ = 2` proved, for odd
`ℓ` the `ℓ`-th power Hasse principle has no Grünwald–Wang exceptional case), and the
`Bauer`/Chebotarev descent for finite coefficients (`Work.SSGRoute.hassePrinciple_h1_cocycles`,
proved, gives the degree-one analogue). -/


section ExtBiprod

/-- **`Ext` in the first variable is additive on binary biproducts**, in the `Subsingleton` form:
if `Ext^r(-,A)` vanishes on `X` and on `Y` then it vanishes on `X ⊞ Y`.  This is the transfer along
Mathlib's `Abelian.Ext.biprodAddEquiv : Ext (X₁ ⊞ X₂) A r ≃+ Ext X₁ A r × Ext X₂ A r` (a product of
subsingletons is a subsingleton).

It is the step that lifts the dévissage base case `Ext^{≥2}_G(𝔽_p[G], A) = 0`
(`ExtChain.subsingleton_ext_fpRegular`) to `Ext^{≥2}_G(𝔽_p[G]^n, A) = 0` for every `n`, i.e. to the
honest base case of the dévissage in the coefficient `E` (see `ExtChain/NOTE_devissage_E.md` §1:
the base case is the *free* module, of any rank). -/
theorem subsingleton_ext_biprod {G : Type} [Group G]
    (X Y A : Rep.{0} SSGRoute.PTExt.Coeff G) (r : ℕ)
    (hX : Subsingleton (CategoryTheory.Abelian.Ext.{0} X A r))
    (hY : Subsingleton (CategoryTheory.Abelian.Ext.{0} Y A r)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0} (X ⊞ Y) A r) := by
  have hprod : Subsingleton (CategoryTheory.Abelian.Ext.{0} X A r ×
      CategoryTheory.Abelian.Ext.{0} Y A r) :=
    ⟨fun a b => Prod.ext (hX.elim _ _) (hY.elim _ _)⟩
  exact ⟨fun a b => (CategoryTheory.Abelian.Ext.biprodAddEquiv (X₁ := X) (X₂ := Y)
    (Y := A) (n := r)).injective (hprod.elim _ _)⟩

end ExtBiprod

section ContinuousInflation

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type} [AddCommGroup A] [DistribMulAction G A]

/-- **Cosets of an open subgroup are open.**  For `N ◁ G` open, the composite of any function on
`G ⧸ N` with the quotient map is locally constant: this is the extra ingredient (absent in the
abstract theory) that makes inflation land in the *continuous* cocycles. -/
theorem isLocallyConstant_comp_quotientGroupMk (N : Subgroup G) [N.Normal]
    (hN : IsOpen (N : Set G)) {B : Type} (f : G ⧸ N → B) :
    Work.AbsoluteKummer.IsLocallyConstant (fun g : G => f (QuotientGroup.mk' N g)) := by
  intro x
  refine ⟨(fun y : G => x⁻¹ * y) ⁻¹' (N : Set G),
    hN.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
  intro y hy
  have hyN : x⁻¹ * y ∈ N := hy
  have hq : QuotientGroup.mk' N y = QuotientGroup.mk' N x := by
    rw [QuotientGroup.mk'_eq_mk']
    exact ⟨(x⁻¹ * y)⁻¹, N.inv_mem hyN, by group⟩
  exact congrArg f hq

/-- **Inflation of continuous `1`-cocycles**: `Z¹_c(G ⧸ N, A^N) → Z¹_c(G, A)` for `N ◁ G` open.
The crossed-homomorphism property is the abstract computation; the local constancy is
`isLocallyConstant_comp_quotientGroupMk` (which only needs openness of `N`, i.e. discreteness of
the quotient). -/
noncomputable def infCocycle1_c (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G)) :
    Work.AbsoluteKummer.Z1 (G ⧸ N) (Work.GroupCohomology.invariants N A) →+
      Work.AbsoluteKummer.Z1 G A where
  toFun f :=
    ⟨fun g => ((f.1 (QuotientGroup.mk' N g) : Work.GroupCohomology.invariants N A) : A), by
      rw [Work.AbsoluteKummer.mem_Z1_iff]
      refine ⟨?_, isLocallyConstant_comp_quotientGroupMk N hN
        (fun q => ((f.1 q : Work.GroupCohomology.invariants N A) : A))⟩
      intro g h
      have hf := ((Work.AbsoluteKummer.mem_Z1_iff (G := G ⧸ N)
        (M := Work.GroupCohomology.invariants N A)) f.1).mp f.2 |>.1
          (QuotientGroup.mk' N g) (QuotientGroup.mk' N h)
      simp only [map_mul, Work.GroupCohomology.quotientSMul_mk'] at hf
      exact congrArg (fun y : Work.GroupCohomology.invariants N A => (y : A)) hf⟩
  map_zero' := by
    ext g
    simp
  map_add' f f' := by
    ext g
    simp

/-- Computation rule for the continuous inflation of `1`-cocycles. -/
@[simp] theorem infCocycle1_c_apply (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
    (f : Work.AbsoluteKummer.Z1 (G ⧸ N) (Work.GroupCohomology.invariants N A)) (g : G) :
    ((infCocycle1_c N hN f : Work.AbsoluteKummer.Z1 G A) : G → A) g =
      ((f.1 (QuotientGroup.mk' N g) : Work.GroupCohomology.invariants N A) : A) := rfl

/-- Inflation sends coboundaries on the quotient to coboundaries on `G` (the well-definedness of
`infH1_c`). -/
theorem infCocycle1_c_mem_B1 (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
    {x : Work.AbsoluteKummer.Z1 (G ⧸ N) (Work.GroupCohomology.invariants N A)}
    (hx : (x : G ⧸ N → Work.GroupCohomology.invariants N A) ∈
      Work.AbsoluteKummer.B1 (G ⧸ N) (Work.GroupCohomology.invariants N A)) :
    ((infCocycle1_c N hN x : Work.AbsoluteKummer.Z1 G A) : G → A) ∈
      Work.AbsoluteKummer.B1 G A := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨(a : A), ?_⟩
  funext g
  have h := congrArg (fun y : Work.GroupCohomology.invariants N A => (y : A))
    (congrFun ha (QuotientGroup.mk' N g))
  have hc : (((g • a : Work.GroupCohomology.invariants N A)) : A) = g • (a : A) := rfl
  have h' : (((x : G ⧸ N → Work.GroupCohomology.invariants N A)
        (QuotientGroup.mk' N g)) : A) = g • (a : A) - (a : A) := by
    simpa only [Work.GroupCohomology.d0_apply, Work.GroupCohomology.quotientSMul_mk',
      AddSubgroup.coe_sub, hc] using h.symm
  rw [infCocycle1_c_apply]
  exact h'.symm

/-- **The continuous inflation map** `H¹_c(G ⧸ N, A^N) → H¹_c(G, A)` for `N ◁ G` open. -/
noncomputable def infH1_c (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G)) :
    Work.AbsoluteKummer.H1 (G ⧸ N) (Work.GroupCohomology.invariants N A) →+
      Work.AbsoluteKummer.H1 G A :=
  QuotientAddGroup.lift
    ((Work.AbsoluteKummer.B1 (G ⧸ N) (Work.GroupCohomology.invariants N A)).comap
      (Work.AbsoluteKummer.Z1 (G ⧸ N) (Work.GroupCohomology.invariants N A)).subtype)
    ((Work.AbsoluteKummer.H1π G A).comp (infCocycle1_c N hN)) (by
      intro x hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Work.AbsoluteKummer.H1π,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      exact infCocycle1_c_mem_B1 N hN (AddSubgroup.mem_comap.mp hx))

/-- Computation rule for the continuous inflation map. -/
theorem infH1_c_H1π (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
    (f : Work.AbsoluteKummer.Z1 (G ⧸ N) (Work.GroupCohomology.invariants N A)) :
    infH1_c (A := A) N hN
        (Work.AbsoluteKummer.H1π (G ⧸ N) (Work.GroupCohomology.invariants N A) f) =
      Work.AbsoluteKummer.H1π G A (infCocycle1_c (A := A) N hN f) :=
  QuotientAddGroup.lift_mk' _ _ f

/-- **Injectivity of the continuous inflation map** (mirrors
`Work.GroupCohomology.ker_infH1_eq_bot`; the continuous model adds no new obstruction, because the
primitive produced on the quotient is automatically locally constant — `G ⧸ N` is discrete for
`N` open). -/
theorem infH1_c_injective (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G)) :
    Function.Injective (infH1_c (A := A) N hN) := by
  have key : ∀ x : Work.AbsoluteKummer.H1 (G ⧸ N) (Work.GroupCohomology.invariants N A),
      infH1_c (A := A) N hN x = 0 → x = 0 := by
    intro x hx
    induction x using QuotientAddGroup.induction_on with
    | _ f =>
      rw [show (↑f : Work.AbsoluteKummer.H1 (G ⧸ N) (Work.GroupCohomology.invariants N A)) =
            Work.AbsoluteKummer.H1π (G ⧸ N) (Work.GroupCohomology.invariants N A) f from rfl,
          infH1_c_H1π] at hx
      rw [Work.AbsoluteKummer.H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
        AddSubgroup.mem_comap] at hx
      -- `hx : (infCocycle1_c N hN f : G → A) ∈ AbsoluteKummer.B1 G A`
      obtain ⟨a, ha⟩ := hx
      -- `f` as a crossed homomorphism vanishes at `1`
      have hf1 : f.1 1 = 0 := by
        have hc := ((Work.AbsoluteKummer.mem_Z1_iff (G := G ⧸ N)
          (M := Work.GroupCohomology.invariants N A)) f.1).mp f.2 |>.1 1 1
        simpa using hc
      -- hence `a` descends to the quotient
      have hainv : a ∈ Work.GroupCohomology.invariants N A := by
        rw [Work.GroupCohomology.mem_invariants]
        intro n
        have h := congrFun ha (n : G)
        rw [show (Work.AbsoluteKummer.Z1 G A).subtype (infCocycle1_c N hN f)
              = ((infCocycle1_c N hN f : Work.AbsoluteKummer.Z1 G A) : G → A)
            from rfl] at h
        simp only [Work.GroupCohomology.d0_apply, infCocycle1_c_apply] at h
        have hm : QuotientGroup.mk' N (n : G) = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact n.2
        rw [hm] at h
        simp only [hf1, AddSubgroup.coe_zero] at h
        exact sub_eq_zero.mp h
      rw [show (↑f : Work.AbsoluteKummer.H1 (G ⧸ N) (Work.GroupCohomology.invariants N A)) =
            Work.AbsoluteKummer.H1π (G ⧸ N) (Work.GroupCohomology.invariants N A) f from rfl,
          Work.AbsoluteKummer.H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
          AddSubgroup.mem_comap]
      refine ⟨⟨a, hainv⟩, ?_⟩
      funext q
      induction q using QuotientGroup.induction_on with
      | _ g =>
        show ((QuotientGroup.mk' N g) • (⟨a, hainv⟩ : Work.GroupCohomology.invariants N A) -
            ⟨a, hainv⟩) = f.1 (QuotientGroup.mk' N g)
        rw [Work.GroupCohomology.quotientSMul_mk']
        apply Subtype.ext
        have h := congrFun ha g
        rw [show (Work.AbsoluteKummer.Z1 G A).subtype (infCocycle1_c N hN f)
              = ((infCocycle1_c N hN f : Work.AbsoluteKummer.Z1 G A) : G → A)
            from rfl] at h
        simp only [Work.GroupCohomology.d0_apply, infCocycle1_c_apply] at h
        exact h
  intro x y hxy
  have h : infH1_c (A := A) N hN (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key (x - y) h)

/-- **(a) The inflation–restriction iso, conditional on the exactness half.**  If the lower
continuous cohomology `H¹_c(N, A)` vanishes and `range(infH1_c) = ker(resH1)` (the exactness lemma
`Work.SSGRoute.ExtChain.range_infH1_c_eq_ker_resH1`, delegated and landing separately), then the
continuous inflation map is *bijective*: injective by `infH1_c_injective`, and surjective because
`resH1 = 0` on a subsingleton target, so its kernel is everything.

This is the five-term-sequence step in the continuous model; the `D_A`-instantiation (item (b)) is
`N = (decomp k A ⊓ K.fixingSubgroup).subgroupOf (decomp k A)`, which is open as the trace of the
open `K.fixingSubgroup`. -/
theorem infH1_c_bijective_of_range (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
    (hrange : (infH1_c (A := A) N hN).range =
      (Work.SSGRoute.PT.H2Fin.resH1 N A).ker)
    (hsub : Subsingleton (Work.AbsoluteKummer.H1 ↥N A)) :
    Function.Bijective (infH1_c (A := A) N hN) := by
  refine ⟨infH1_c_injective (A := A) N hN, ?_⟩
  rw [← AddMonoidHom.range_eq_top, hrange]
  refine le_antisymm le_top ?_
  intro x _
  rw [AddMonoidHom.mem_ker]
  exact Subsingleton.elim _ _

end ContinuousInflation

/-! ## Exactness of the continuous inflation–restriction sequence in degree `1`

The last ingredient of the "five-term-sequence step at `D_A`" announced in the module docstring:
the *continuous* counterpart of `Work.GroupCohomology.range_infH1_eq_ker_resH1`, i.e. the
identification of the range of the continuous inflation with the kernel of the continuous
restriction.  The only genuinely new point (compared with the abstract proof) is that the primitive
produced on the quotient has to be *locally constant* — which is automatic because `N` is open, so
that `G ⧸ N` is discrete (`QuotientGroup.discreteTopology`).

The two auxiliary facts `exists_quotientCocycle_descend` and `H1pi_infCocycle1_c_eq_of_value` are the
two halves of that proof, isolated because they are also useful on their own.

**Renaming note (lane `ExtChain`, session 2026-10-02).**  The three declarations of this section
are the *inline* copies used by `infH1_c_bijective` and are therefore named
`exists_quotientCocycle_descend_inline`, `H1pi_infCocycle1_c_eq_of_value_inline` and
`range_infH1_c_eq_ker_resH1_inline`.  The canonical (public) statements of the same content are the
delegated files `ExtChain/exists_quotientCocycle_descend.lean`,
`ExtChain/H1pi_infCocycle1_c_eq_of_value.lean` and `ExtChain/range_infH1_c_eq_ker_resH1.lean`;
the last of these *imports this module* (it needs `infH1_c`), so it cannot be imported here, and
the two copies had to be given distinct names (a public duplicate would make every module
importing both files fail to elaborate).  No mathematics changed. -/

section ContinuousExactness

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type} [AddCommGroup A] [DistribMulAction G A]

/-- **Descending a corrected cocycle to the quotient.**  Let `N ◁ G` be open, `c ∈ Z¹_c(G,A)` a
continuous `1`-cocycle and `a ∈ A` such that the coboundary `d⁰ a` agrees with `c` on `N`
(`d⁰a(n) = c(n)` for `n ∈ N`).  Then the corrected cocycle `b = c - d⁰a` vanishes on `N` and is
`N`-invariant, hence descends to a continuous `1`-cocycle `fcoc ∈ Z¹_c(G ⧸ N, A^N)` with values
`fcoc(g) = c(g) - (g • a - a)`.

The local-constancy of the descended cocycle is free: `N` is open, so `G ⧸ N` is discrete and every
function on it is locally constant. -/
theorem exists_quotientCocycle_descend_inline (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
    (c : ↥(Work.AbsoluteKummer.Z1 G A)) (a : A)
    (ha : ∀ n : N, (n : G) • a - a = (c : G → A) (n : G)) :
    ∃ fcoc : ↥(Work.AbsoluteKummer.Z1 (G ⧸ N) (Work.GroupCohomology.invariants N A)),
      ∀ g : G, ((fcoc : G ⧸ N → Work.GroupCohomology.invariants N A)
          (QuotientGroup.mk' N g) : A) = (c : G → A) g - (g • a - a) := by
  classical
  -- `c` viewed in the (non-continuous) crossed-hom subgroup, and the corrected cocycle `b = c - d⁰a`
  -- there: the crossed-hom property of the difference is then a single application of `bZ.2`.
  let cZ : Work.GroupCohomology.Z1 G A := ⟨c.1, c.2.1⟩
  let bZ : Work.GroupCohomology.Z1 G A :=
    cZ - ⟨Work.GroupCohomology.d0 G A a, Work.GroupCohomology.d0_mem_Z1 G A a⟩
  have hbcross : ∀ g h : G,
      (bZ : G → A) (g * h) = g • (bZ : G → A) h + (bZ : G → A) g := bZ.2
  have hbval : ∀ g : G, (bZ : G → A) g = c.1 g - (g • a - a) := fun _ => rfl
  have hbzero : ∀ n : N, (bZ : G → A) (n : G) = 0 := by
    intro n
    rw [hbval (n : G), ha n, sub_self]
  have hb_inv : ∀ g : G, (bZ : G → A) g ∈ Work.GroupCohomology.invariants N A := by
    intro g
    rw [Work.GroupCohomology.mem_invariants]
    intro n
    show (n : G) • (bZ : G → A) g = (bZ : G → A) g
    have h1 : (bZ : G → A) ((n : G) * g) =
        (n : G) • (bZ : G → A) g + (bZ : G → A) (n : G) := hbcross (n : G) g
    rw [hbzero n, add_zero] at h1
    have hsplit : (n : G) * g = g * (g⁻¹ * (n : G) * g) := by group
    have hmem : g⁻¹ * (n : G) * g ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem (n : G) n.2 g⁻¹
    have h4 : (bZ : G → A) (g * (g⁻¹ * (n : G) * g)) = (bZ : G → A) g := by
      rw [hbcross g (g⁻¹ * (n : G) * g), hbzero ⟨_, hmem⟩, smul_zero, zero_add]
    rw [← h1, hsplit, h4]
  have hfval_wd : ∀ p q : G, QuotientGroup.leftRel N p q →
      (⟨(bZ : G → A) p, hb_inv p⟩ : Work.GroupCohomology.invariants N A) =
        ⟨(bZ : G → A) q, hb_inv q⟩ := by
    intro p q hpq
    rw [QuotientGroup.leftRel_apply] at hpq
    apply Subtype.ext
    show (bZ : G → A) p = (bZ : G → A) q
    rw [show q = p * (p⁻¹ * q) from by group]
    rw [hbcross p (p⁻¹ * q)]
    have hm : (bZ : G → A) (p⁻¹ * q) = 0 := hbzero ⟨p⁻¹ * q, hpq⟩
    rw [hm, smul_zero, zero_add]
  let fval : G → Work.GroupCohomology.invariants N A := fun g => ⟨(bZ : G → A) g, hb_inv g⟩
  let fbar : G ⧸ N → Work.GroupCohomology.invariants N A := Quotient.lift fval hfval_wd
  have hfbar_mk : ∀ g : G, fbar (↑g : G ⧸ N) = fval g := by
    intro g
    show Quotient.lift fval hfval_wd (⟦g⟧) = fval g
    exact Quotient.lift_mk fval hfval_wd g
  have hfbar_cross : ∀ x z : G ⧸ N, fbar (x * z) = x • fbar z + fbar x := by
    intro x z
    induction x using QuotientGroup.induction_on with
    | _ g =>
      induction z using QuotientGroup.induction_on with
      | _ h =>
        rw [← QuotientGroup.mk_mul, hfbar_mk, hfbar_mk, hfbar_mk]
        apply Subtype.ext
        show (bZ : G → A) (g * h) = (g : G) • (bZ : G → A) h + (bZ : G → A) g
        rw [hbcross g h]
  haveI : DiscreteTopology (G ⧸ N) := QuotientGroup.discreteTopology hN
  have hfbar_lc : Work.AbsoluteKummer.IsLocallyConstant fbar := by
    intro x
    exact ⟨{x}, isOpen_discrete _, rfl,
      fun y hy => by rw [Set.mem_singleton_iff.mp hy]⟩
  refine ⟨⟨fbar, (Work.AbsoluteKummer.mem_Z1_iff _).mpr ⟨hfbar_cross, hfbar_lc⟩⟩, ?_⟩
  intro g
  show (fbar (QuotientGroup.mk' N g) : A) = c.1 g - (g • a - a)
  rw [QuotientGroup.mk'_apply, hfbar_mk]
  exact hbval g

/-- **The descended cocycle represents the class of `c`.**  If `fcoc ∈ Z¹_c(G ⧸ N, A^N)` has the
values `fcoc(g) = c(g) - (g • a - a)`, then the inflation of `fcoc` differs from `c` by the
coboundary `d⁰ a`, hence has the same class in `H¹_c(G,A)`. -/
theorem H1pi_infCocycle1_c_eq_of_value_inline (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
    (c : ↥(Work.AbsoluteKummer.Z1 G A)) (a : A)
    (fcoc : ↥(Work.AbsoluteKummer.Z1 (G ⧸ N) (Work.GroupCohomology.invariants N A)))
    (hval : ∀ g : G, ((fcoc : G ⧸ N → Work.GroupCohomology.invariants N A)
          (QuotientGroup.mk' N g) : A) = (c : G → A) g - (g • a - a)) :
    Work.AbsoluteKummer.H1π G A (Work.SSGRoute.ExtChain.infCocycle1_c N hN fcoc) =
      Work.AbsoluteKummer.H1π G A c := by
  rw [Work.AbsoluteKummer.H1π_eq_iff, Work.AbsoluteKummer.mem_B1_iff]
  refine ⟨-a, ?_⟩
  funext g
  show (g • (-a) - (-a)) =
    ((Work.SSGRoute.ExtChain.infCocycle1_c N hN fcoc : Work.AbsoluteKummer.Z1 G A) : G → A) g
      - (c : G → A) g
  simp only [Work.SSGRoute.ExtChain.infCocycle1_c_apply, hval g, smul_neg]
  abel

/-- **Exactness of the continuous inflation–restriction sequence in degree `1`.**  For `N ◁ G` open
(so that `G ⧸ N` is discrete), the range of the continuous inflation map
`infH1_c : H¹_c(G ⧸ N, A^N) → H¹_c(G, A)` is the kernel of the continuous restriction
`resH1 N A : H¹_c(G, A) → H¹_c(N, A)`.

This is the *continuous* counterpart of `Work.GroupCohomology.range_infH1_eq_ker_resH1`, and it is
what makes `infH1_c_bijective_of_range` unconditional. -/
theorem range_infH1_c_eq_ker_resH1_inline (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G)) :
    (Work.SSGRoute.ExtChain.infH1_c (A := A) N hN).range =
      (Work.SSGRoute.PT.H2Fin.resH1 N A).ker := by
  apply le_antisymm
  · intro y hy
    rw [AddMonoidHom.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [AddMonoidHom.mem_ker]
    induction x using QuotientAddGroup.induction_on with
    | _ f =>
      rw [show (↑f : Work.AbsoluteKummer.H1 (G ⧸ N) (Work.GroupCohomology.invariants N A)) =
            Work.AbsoluteKummer.H1π (G ⧸ N) (Work.GroupCohomology.invariants N A) f from rfl,
          Work.SSGRoute.ExtChain.infH1_c_H1π, Work.SSGRoute.PT.H2Fin.resH1_H1π]
      rw [Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff]
      refine ⟨0, ?_⟩
      funext n
      rw [Work.GroupCohomology.d0_apply, smul_zero, sub_zero]
      show (0 : A) = (Work.SSGRoute.ExtChain.infCocycle1_c N hN f : G → A) (n : G)
      rw [Work.SSGRoute.ExtChain.infCocycle1_c_apply]
      have hm : QuotientGroup.mk' N (n : G) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact n.2
      rw [hm]
      have h1 : (f : G ⧸ N → Work.GroupCohomology.invariants N A) 1 = 0 :=
        Work.GroupCohomology.Z1.map_one (G ⧸ N) (Work.GroupCohomology.invariants N A)
          ((Work.AbsoluteKummer.mem_Z1_iff _).mp f.2).1
      simpa using (congrArg Subtype.val h1).symm
  · intro y hy
    rw [AddMonoidHom.mem_ker] at hy
    induction y using QuotientAddGroup.induction_on with
    | _ c =>
      rw [show (↑c : Work.AbsoluteKummer.H1 G A) = Work.AbsoluteKummer.H1π G A c from rfl,
          Work.SSGRoute.PT.H2Fin.resH1_H1π] at hy
      rw [Work.AbsoluteKummer.H1π_eq_zero_iff, Work.AbsoluteKummer.mem_B1_iff] at hy
      obtain ⟨a, ha⟩ := hy
      have hcan : ∀ n : N, (n : G) • a - a = (c : G → A) (n : G) := by
        intro n
        have h := congrFun ha n
        change (n : G) • a - a = (c : G → A) (n : G) at h
        exact h
      obtain ⟨fcoc, hval⟩ := exists_quotientCocycle_descend_inline N hN c a hcan
      refine ⟨Work.AbsoluteKummer.H1π (G ⧸ N) (Work.GroupCohomology.invariants N A) fcoc, ?_⟩
      rw [Work.SSGRoute.ExtChain.infH1_c_H1π]
      exact H1pi_infCocycle1_c_eq_of_value_inline N hN c a fcoc hval

/-- **Unconditional form of `infH1_c_bijective_of_range`**: for `N ◁ G` open with
`H¹_c(N, A) = 0`, the continuous inflation `H¹_c(G ⧸ N, A^N) → H¹_c(G, A)` is bijective.  This is
the continuous five-term-sequence step at `N`. -/
theorem infH1_c_bijective (N : Subgroup G) [N.Normal] (hN : IsOpen (N : Set G))
    (hsub : Subsingleton (Work.AbsoluteKummer.H1 ↥N A)) :
    Function.Bijective (Work.SSGRoute.ExtChain.infH1_c (A := A) N hN) :=
  infH1_c_bijective_of_range N hN (range_infH1_c_eq_ker_resH1_inline N hN) hsub

end ContinuousExactness

/-- **The `H`-fixed points of the coinduced coefficient `Hom_ℤ(M,Ωˣ)` are the maps into the fixed
field `Ω^H`.**  For `H ≤ Gal(Ω/K)` (so that `H` acts trivially on the carrier `M.V`), a
`Γ`-element `φ : homCoind k Ω K M` is fixed by every `σ ∈ H` if and only if every value `φ x` lies
in the fixed field `Ω^H` of `H`.

This identifies the *invariant module* `M^{D_A ⊓ G_K}` in the five-term-sequence reformulation of
the `himg` input. -/
theorem homCoind_fixed_iff_mem_fixedField {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : H ≤ (SSGRoute.res k K).ker)
    (φ : Work.SSGRoute.homCoind k Ω K M) :
    (∀ σ ∈ H, σ • φ = φ) ↔
      ∀ x : M.V, ((Additive.toMul (φ x) : Ωˣ) : Ω) ∈ IntermediateField.fixedField H := by
  constructor
  · intro h x
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hres : SSGRoute.res k K σ = 1 := hH hσ
    have h2 : (σ • φ) x = φ x := by rw [h σ hσ]
    rw [Work.SSGRoute.homCoind.smul_apply, hres] at h2
    have h2' : σ • (φ x) = φ x := by simpa using h2
    have h3 : σ • (Additive.toMul (φ x)) = Additive.toMul (φ x) := h2'
    have h4 := congrArg (fun u : Ωˣ => (u : Ω)) h3
    simpa [AlgEquiv.smul_units_def] using h4
  · intro h σ hσ
    ext x
    rw [Work.SSGRoute.homCoind.smul_apply, hH hσ]
    have hx : σ • (Additive.toMul (φ x)) = Additive.toMul (φ x) := by
      apply Units.ext
      have hmem := (IntermediateField.mem_fixedField_iff H _).mp (h x) σ hσ
      simpa [AlgEquiv.smul_units_def] using hmem
    have hxΩ := congrArg (fun u : Ωˣ => (u : Ω)) hx
    simpa [AlgEquiv.smul_units_def] using hxΩ

/-- **The compositum of `K` with the fixed field of `H` is the fixed field of `H ⊓ Gal(Ω/K)`**
(the decomposition-field identification needed to reformulate the `himg` input: for `H = decomp k A`
the decomposition group of a finite place, the field `K·Ω^{H}` of the five-term-sequence
reformulation is exactly `Ω^{H ⊓ Gal(Ω/K)}`). -/
theorem fixedField_inf_fixingSubgroup {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω))) :
    IntermediateField.fixedField (H ⊓ K.fixingSubgroup) = IntermediateField.fixedField H ⊔ K := by
  have hsub : (IntermediateField.fixedField H ⊔ K).fixingSubgroup = H ⊓ K.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup,
      InfiniteGalois.fixingSubgroup_fixedField (k := k) (K := Ω)
        (⟨H, hH⟩ : ClosedSubgroup (Ω ≃ₐ[k] Ω))]
  rw [← hsub]
  exact InfiniteGalois.fixedField_fixingSubgroup (k := k) (K := Ω)
    (IntermediateField.fixedField H ⊔ K)

/-- **The connecting map `extDelta` of the class formation lands in the idèle localisation kernel.**
For every `x ∈ Ext^r_G(M, C_K)`, the connecting class `extDelta x ∈ Ext^{r+1}_G(M, Kˣ)` dies under
`extToIdeles` (`= postcomposition with Kˣ → 𝕀_K`).

This is the "reverse inclusion" half of the exactness of the class formation
(`ExtChain/extExact.lean` announces it as the formal consequence `extDelta ≫ extToIdeles = 0` of
`ShortComplex.ShortExact.extClass_comp`, but it was not stated separately): the whole composite is
`x ∘ (S.extClass ∘ mk₀ S.f) = x ∘ 0` by associativity of `Ext.comp` and `extClass_comp`, where
`S = Kˣ → 𝕀_K → C_K` and `S.f = ideleIncl k K`.  With
`PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero` (the other inclusion) this makes
`im (extDelta) = ker (extToIdeles)` at the `Ext`-level, i.e. identifies the two equivalent forms of
the hypothesis of the finite-place input. -/
-- NOTE (name clash): `ExtChain/himgIdelesInput_inf.lean` also declares
-- `Work.SSGRoute.ExtChain.extToIdeles_extDelta_eq_zero`.  Keeping this copy `private` is what makes
-- it possible to import *both* `himgIdelesInput_fin` and (transitively) `himgIdelesInput_inf` — e.g.
-- from `ExtChain/himg_of_ideles_input_fin_clean.lean`.  Nothing outside this file used this copy.
private theorem extToIdeles_extDelta_eq_zero (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K]
    {M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (x : CategoryTheory.Abelian.Ext.{0} M (SSGRoute.PTExt.classesK k K) r) :
    SSGRoute.PTExt.extToIdeles (k := k)
      (SSGRoute.PTExt.extDelta (k := k) (K := K) x) = 0 := by
  show (x.comp (NK.HassePrinciple.ideleShortComplex_shortExact k K).extClass rfl).comp
      (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k K)) (add_zero (r + 1)) = 0
  have hS := NK.HassePrinciple.ideleShortComplex_shortExact k K
  have key : hS.extClass.comp
      (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k K)) (add_zero 1) = 0 :=
    CategoryTheory.ShortComplex.ShortExact.extClass_comp hS
  rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero, key]
  simp

/-- **Reduction of the hypothesis.**  The hypothesis `extToIdeles (e1aSyzShift z) = 0` of the
`himg` input is, read through the *idèle* Shapiro injectivity
(`extIdele_localisation_injective_of_finite`, proved on disk), equivalent to the vanishing of the
idèle localisation of `z` itself.  In particular `z` lies in the kernel of the edge map
`Ext¹_G(R,Kˣ) → Ext¹_G(R,𝕀_K)` — i.e. in the image of the connecting map
`Ext⁰_G(R,C_K) → Ext¹_G(R,Kˣ)` of the class formation, by the long exact sequence.

This is a strict *simplification* (not a consequence) of the target: it shows that the hypothesis
is strictly stronger than the one-place condition of the refuted per-place form, and it reduces the
target to a statement about the idèle-boundary subgroup `im δ`. -/
theorem extToIdeles_e1aSyzShift_eq_zero_imp (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0) :
    SSGRoute.PTExt.extToIdeles (k := k) z = 0 := by
  classical
  let N := Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E
  let R := CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite ↥N := Work.SSGRoute.PT.finite_dualMod_tensor p E T
  haveI := hRfin
  -- the hypothesis read place by place, as the vanishing of the localised shifted class
  have hloc : ∀ q : NK.GlobalCFT.Place ↥K,
      SSGRoute.PTExt.extLoc (k := k) q
        (SSGRoute.PTExt.extToIdeles (k := k)
          ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N) z)) = 0 := by
    intro q
    rw [hz]
    exact SSGRoute.PTExt.extLoc_zero (k := k) (K := ↥K) q
  -- the same, transported to `z` itself by the imported brick (the shift-injectivity)
  have hloc' : ∀ q : NK.GlobalCFT.Place ↥K,
      SSGRoute.PTExt.extLoc (k := k) q (SSGRoute.PTExt.extToIdeles (k := k) z) = 0 := by
    intro q
    rw [Work.SSGRoute.SSGStage.extLoc_extToIdeles_eq (k := k) (K := ↥K) q z]
    exact Work.SSGRoute.ExtChain.extLoc_extToIdeles_e1aSyzShift_eq_zero_imp (k := k) (K := K) N q z
      (hloc q)
  -- the idèle Shapiro injectivity finishes
  exact Work.SSGRoute.extIdele_localisation_injective_of_finite k ↥K R 1
    (SSGRoute.PTExt.extToIdeles (k := k) z) hloc'

/-- **The canonical syzygy shift preserves *and* reflects the localisation kernel**
`ker (extToIdeles)`.  For `R_N = ker (freeCover N)` and `z ∈ Ext¹_G(R_N, Kˣ)`:

    extToIdeles (e1aSyzShift N z) = 0  ↔  extToIdeles z = 0.

Both directions are *elementary* here (`Ext`-associativity), with no use of the idèle Shapiro
injectivity:

* `⟸` — the shift is postcomposition with the connecting class `(freeCoverSES N).extClass`, so
  `extToIdeles` of the shift is `extClass ∘ (extToIdeles z) = 0`: this is the coefficient naturality
  `ExtChain.e1aShiftEquiv_natural_coeff` (proved for the general presentation);
* `⟹` — `z = (e1aSyzShift N).symm (e1aSyzShift N z)`, and the connecting map
  `(e1aShiftEquiv … unitsK 1 _).symm` descends to the localisation kernels
  (`ExtChain.shift_symm_extToIdeles_eq_zero_gen`).

Consequently the idèle localisation kernel of `Ext²_G(N, Kˣ)` corresponds exactly to that of its
canonical syzygy `Ext¹_G(R_N, Kˣ)` under `e1aSyzShift N`: the "`Ш²`-image" is independent of the
chosen presentation, which is the coherence that the dévissage in the coefficient `E`
(`NOTE_devissage_E.md`) consumes.  (Compare `extToIdeles_e1aSyzShift_eq_zero_imp` above, whose
`⟹` half is proved through the *idèle Shapiro injectivity* — a heavier arithmetic input; the
present lemma replaces it by the connecting-map naturality.) -/
theorem extToIdeles_e1aSyzShift_eq_zero_iff {k : Type} [Field k] [NumberField k]
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (SSGRoute.PTExt.unitsK k K) 1) :
    (SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z) = 0) ↔
      (SSGRoute.PTExt.extToIdeles (k := k) z = 0) := by
  classical
  constructor
  · intro h
    haveI : CategoryTheory.Projective (Work.SSGRoute.freeCoverSES N).X₂ :=
      Rep.free_projective (k := SSGRoute.PTExt.Coeff) (G := K ≃ₐ[k] K) (α := N.V)
    have hz : z = (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N).symm
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z) :=
      (AddEquiv.symm_apply_apply _ z).symm
    rw [hz]
    exact Work.SSGRoute.ExtChain.shift_symm_extToIdeles_eq_zero_gen (k := k) (Ω := Ω) (K := K)
      (S := Work.SSGRoute.freeCoverSES N) (Work.SSGRoute.freeCoverSES_shortExact N)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z) h
  · intro h
    have hnat := Work.SSGRoute.ExtChain.e1aShiftEquiv_natural_coeff
      (S := Work.SSGRoute.freeCoverSES N) (Work.SSGRoute.freeCoverSES_shortExact N)
      (SSGRoute.PTExt.unitsK k K) (SSGRoute.PTExt.idelesK k K)
      (NK.HassePrinciple.ideleIncl k K) 1 (le_refl 1) z
    show (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z).comp
        (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k K)) (add_zero 2) = 0
    rw [show Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z
        = Work.SSGRoute.PT.e1aShiftEquiv (Work.SSGRoute.freeCoverSES N)
            (Work.SSGRoute.freeCoverSES_shortExact N) (SSGRoute.PTExt.unitsK k K) 1 (le_refl 1) z
        from rfl]
    rw [hnat]
    rw [show z.comp (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k K))
          (add_zero 1) = 0 from h]
    simp

/-- **The hypothesis puts `z` in the image of the idèle connecting map.**  Combining the previous
lemma (`hz` gives `extToIdeles z = 0`) with the long exact sequence of the class formation
(`Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero`, the degree-`r+1` form at
`r = 0`), the class `z` is the image of a *degree-zero* class `w ∈ Ext⁰_G(R,C_K) = Hom_G(R.V,C_K)`
under the connecting map `extDelta`.

So the target is equivalent to the statement that the *local comparison* at the place `A` vanishes
on `range (Ext⁰_G(R,C_K) --extDelta--> Ext¹_G(R,Kˣ))` — i.e. to a genuine *gluing* statement: every
`G`-equivariant map `R.V → C_K` has to give a class whose localisation at `D_A` is trivial. -/
theorem exists_extDelta_eq_of_e1aSyzShift_eq_zero (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0) :
    ∃ w : CategoryTheory.Abelian.Ext.{0}
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
        (SSGRoute.PTExt.classesK k K) 0,
      SSGRoute.PTExt.extDelta (k := k) (K := ↥K) w = z := by
  classical
  haveI := hRfin
  have h1 := extToIdeles_e1aSyzShift_eq_zero_imp p k Ω K ζ hζ hζK T hT E z hz
  exact Work.SSGRoute.PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero k ↥K z h1

/-- **The two connecting maps commute.**  The connecting map of the *canonical presentation*
`0 → R → F → N → 0` in the first variable (`e1aSyzShift N`, precomposition with
`(freeCoverSES N).extClass`) and the connecting map of the *class formation*
`0 → Kˣ → 𝕀_K → C_K` in the second variable (`extDelta`) commute up to the connecting map of the
presentation at degree `0`:

    e1aSyzShift N (extDelta w) = extDelta ((freeCoverSES N).extClass ∘ w)   (w : Ext⁰_G(R,C_K)).

Both sides are the same Yoneda product `(freeCoverSES N).extClass ∘ w ∘ (sesK k K).extClass`, so the
statement is associativity of `Abelian.Ext.comp` (`Ext.comp_assoc_of_second_deg_zero`, since `w` has
degree `0`) together with the computation rule `e1aShiftEquiv_apply` for the syzygy shift. -/
theorem e1aSyzShift_extDelta_comm {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (SSGRoute.PTExt.classesK k K) 0) :
    Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N
        (SSGRoute.PTExt.extDelta (k := k) (K := ↥K) w) =
      SSGRoute.PTExt.extDelta (k := k) (K := ↥K)
        ((Work.SSGRoute.freeCoverSES_shortExact N).extClass.comp w (add_zero 1)) := by
  show (Work.SSGRoute.freeCoverSES_shortExact N).extClass.comp
      (w.comp (NK.HassePrinciple.ideleShortComplex_shortExact k K).extClass rfl) (by omega) =
    ((Work.SSGRoute.freeCoverSES_shortExact N).extClass.comp w (add_zero 1)).comp
      (NK.HassePrinciple.ideleShortComplex_shortExact k K).extClass (by omega)
  exact (CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero
    (Work.SSGRoute.freeCoverSES_shortExact N).extClass w
    (NK.HassePrinciple.ideleShortComplex_shortExact k K).extClass (by omega)).symm

/-- **The two forms of the hypothesis are equivalent.**  For `z ∈ Ext¹_G(R_N, Kˣ)`,

    z ∈ im (extDelta : Ext⁰_G(R_N,C_K) → Ext¹_G(R_N,Kˣ))  ⟺  extToIdeles (e1aSyzShift N z) = 0,

i.e. the hypothesis `hz` of the finite-place input (`extToIdeles (e1aSyzShift z) = 0`) is exactly the
statement that `z` comes from a *degree-zero* class of the class formation, in the form used by the
unconditional `extDelta`-input.  The two directions are
`PTdualControl.exists_extDelta_eq_of_extToIdeles_eq_zero` (on disk) and the commutation
`e1aSyzShift_extDelta_comm` together with `extToIdeles_extDelta_eq_zero` above. -/
theorem exists_extDelta_eq_iff_extToIdeles_e1aSyzShift_eq_zero (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1) :
    (∃ w : CategoryTheory.Abelian.Ext.{0}
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
        (SSGRoute.PTExt.classesK k K) 0,
      SSGRoute.PTExt.extDelta (k := k) (K := ↥K) w = z) ↔
      (SSGRoute.PTExt.extToIdeles (k := k)
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
          (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0) := by
  classical
  haveI := hRfin
  constructor
  · rintro ⟨w, rfl⟩
    rw [Work.SSGRoute.ExtChain.e1aSyzShift_extDelta_comm (k := k) (K := K)
      (N := Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) w]
    exact Work.SSGRoute.ExtChain.extToIdeles_extDelta_eq_zero k ↥K _
  · intro hz
    exact exists_extDelta_eq_of_e1aSyzShift_eq_zero p k Ω K ζ hζ hζK T hT E z hz

/-- **The "base-case engine" of the dévissage in `E`: the target is *vacuous* whenever the level-`2`
`Ext` of the coefficient vanishes.**  If `Ext²_G(e1aN0 p k Ω K T E, Kˣ)` is a subsingleton — which
holds for the *free* coefficient `E = 𝔽_p[Gal(K/k)]`, where `N_E ≅ 𝔽_p[G] ⊗ T^∨` admits the two-term
resolution `0 → ℤ[G]^n --p--> ℤ[G]^n → N_E → 0` by free `ℤ[G]`-modules (the delegated
`ExtChain.subsingleton_ext_dualMod_regular`) — then the hypothesis `extToIdeles (e1aSyzShift z) = 0`
already forces `z = 0`: indeed `e1aSyzShift z` is *some* element of the subsingleton
`Ext²_G(N,Kˣ)`, hence `0`, and `e1aSyzShift` is an additive equivalence.  Both sides of the
conclusion are then `0`. -/
theorem himgIdelesInput_fin_of_subsingleton_ext2 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (h2 : Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) (SSGRoute.PTExt.unitsK k K) 2))
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hns : ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker)) :
    Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0 := by
  haveI := h2
  have hz0 : z = 0 := by
    apply (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)).injective
    rw [map_zero]
    exact Subsingleton.elim _ _
  rw [hz0]
  simp

/-- **The dévissage base case in the coefficient, in the number-field form.**  For `T` a
`p`-cyclotomic dual (hence a line, `hT.1`) and `E = 𝔽_p[Gal(K/k)]` the *regular* coefficient,
`Ext^{≥2}_{Gal(K/k)}(e1aN0 p k Ω K T E, A)` vanishes.

This is exactly the statement requested by `ExtChain/NOTE_devissage_E.md` §1
(`ExtChain.subsingleton_ext_dualMod_regular`, whose file still carries a `sorry`), here deduced from
the abstract-group rank-one version `ExtChain.subsingleton_ext_dualMod_regular_rankOne`. -/
theorem subsingleton_ext_dualMod_e1aN0 (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (r : ℕ) (hr : 2 ≤ r) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T (MonoidAlgebra (ZMod p) (K ≃ₐ[k] K))) A r) :=
  Work.SSGRoute.ExtChain.subsingleton_ext_dualMod_regular_rankOne p (K ≃ₐ[k] K) T hT.1 A r hr

/-- **The dévissage base case for the finite-place target**: the target holds when the coefficient
is the regular module `E = 𝔽_p[Gal(K/k)]`.  It is the specialization of
`himgIdelesInput_fin_of_subsingleton_ext2` to the vanishing supplied by
`subsingleton_ext_dualMod_e1aN0`; the dévissage in the coefficient would propagate it from here to
all finite `E` (that induction's step is the missing chapter — see the module doc). -/
theorem himgIdelesInput_fin_regular (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (hEfin : Finite (MonoidAlgebra (ZMod p) (K ≃ₐ[k] K)))
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T
        (MonoidAlgebra (ZMod p) (K ≃ₐ[k] K)))))]
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T
          (MonoidAlgebra (ZMod p) (K ≃ₐ[k] K)))))
      (SSGRoute.PTExt.unitsK k K) 1)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T (MonoidAlgebra (ZMod p) (K ≃ₐ[k] K))) z) = 0)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hns : ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker)) :
    Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T
            (MonoidAlgebra (ZMod p) (K ≃ₐ[k] K))))))
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T
            (MonoidAlgebra (ZMod p) (K ≃ₐ[k] K))))) z) = 0 := by
  haveI := hEfin
  exact himgIdelesInput_fin_of_subsingleton_ext2 p k Ω K ζ hζ hζK T hT
    (MonoidAlgebra (ZMod p) (K ≃ₐ[k] K))
    (subsingleton_ext_dualMod_e1aN0 p k Ω K ζ hζ hζK T hT
      (SSGRoute.PTExt.unitsK k K) 2 (le_refl 2))
    z hz A hA hns

/-- **The formal reduction of the target to the `H²`-side, at an arbitrary closed subgroup.**

`resH1_D (e1cMap R z) = 0` follows from `resH2_D (e1aChainH N (e1aSyzShift N z)) = 0`: the two are
`δ`-images of each other under the restricted connecting map
`(restrictSES (e1aSES N) D).deltaH2`, which is injective because its kernel is
`H¹(D, homCoindFreeT) = 0` (`homCoindFreeT_H1_subgroup`, `deltaH2_restrictSES_e1aSES_injective'`).

This is the `D = ⟨σ⟩` lemma of `ExtChain/himgIdelesInput_inf.lean` for a general *closed* `D`; it is
the bridge that lets the finite-place target be attacked on the `H²`/`Sha`-side, where the dévissage
in the coefficient `E` (`ExtChain/NOTE_devissage_E.md`) runs. -/
theorem resH1_e1cMap_eq_zero_of_resH2_e1aChainH_eq_zero {k : Type} [Field k] [NumberField k]
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [Module.Finite ℤ ↥(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))]
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (hDcl : IsClosed ((D : Set (Ω ≃ₐ[k] Ω))))
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (SSGRoute.PTExt.unitsK k K) 1)
    (h : Work.SSGRoute.PT.resH2 D
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z)) = 0) :
    Work.SSGRoute.PT.H2Fin.resH1 D
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
      (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z) = 0 := by
  have hInj := Work.SSGRoute.ExtChain.deltaH2_restrictSES_e1aSES_injective'
    (k := k) (Ω := Ω) (K := K) N D hDcl
  have key : (Work.SSGRoute.ExtChain.restrictSES (Work.SSGRoute.ExtChain.e1aSES N) D).deltaH2
      (Work.SSGRoute.PT.H2Fin.resH1 D
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z)) = 0 := by
    rw [← Work.SSGRoute.ExtChain.deltaH2_restriction (Work.SSGRoute.ExtChain.e1aSES N) D
      (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z)]
    have hH : (Work.SSGRoute.ExtChain.e1aSES N).deltaH2
        (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z)
        = Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N
            (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z) := by
      rw [Work.SSGRoute.PT.e1aChainH_apply (k := k) (Ω := Ω) (K := K) N
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z),
        AddEquiv.symm_apply_apply]
      rfl
    rw [hH]
    exact h
  exact hInj (by rw [key, map_zero])

/-- **The converse of the bridge**: the vanishing of `resH1_D (e1cMap R z)` implies the vanishing of
the `H²`-side chain class `resH2_D (e1aChainH N (e1aSyzShift N z))`.  Together with
`resH1_e1cMap_eq_zero_of_resH2_e1aChainH_eq_zero` this makes the finite-place target *equivalent* to
its `H²`/`Sha`-side spelling, in which the dévissage in the coefficient `E` runs.

This direction is formal and even simpler than the other: `e1aChainH N (e1aSyzShift N z)` is
`(e1aSES N).deltaH2 (e1cMap R z)`, and `deltaH2_restriction` computes its restriction to `D` as the
connecting map of the restricted resolution applied to `resH1_D (e1cMap R z)`. -/
theorem resH2_e1aChainH_eq_zero_of_resH1_e1cMap_eq_zero {k : Type} [Field k] [NumberField k]
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [Module.Finite ℤ ↥(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))]
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (SSGRoute.PTExt.unitsK k K) 1)
    (h : Work.SSGRoute.PT.H2Fin.resH1 D
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
      (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z) = 0) :
    Work.SSGRoute.PT.resH2 D
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N
        (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z)) = 0 := by
  rw [Work.SSGRoute.PT.e1aChainH_apply (k := k) (Ω := Ω) (K := K) N
    (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z),
    AddEquiv.symm_apply_apply]
  show Work.SSGRoute.PT.resH2 D
    ((Work.SSGRoute.ExtChain.e1aSES N).deltaH2
      (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z)) = 0
  rw [Work.SSGRoute.ExtChain.deltaH2_restriction (Work.SSGRoute.ExtChain.e1aSES N) D
    (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z), h, map_zero]

/-- **The finite-place target is equivalent to its `H²`-side spelling** (the two bridge lemmas). -/
theorem resH1_e1cMap_eq_zero_iff_resH2_e1aChainH_eq_zero {k : Type} [Field k] [NumberField k]
    {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [Module.Finite ℤ ↥(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))]
    (D : Subgroup (Ω ≃ₐ[k] Ω)) (hDcl : IsClosed ((D : Set (Ω ≃ₐ[k] Ω))))
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) (SSGRoute.PTExt.unitsK k K) 1) :
    (Work.SSGRoute.PT.H2Fin.resH1 D
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z) = 0) ↔
      (Work.SSGRoute.PT.resH2 D
        (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N
          (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N z)) = 0) :=
  ⟨fun h => resH2_e1aChainH_eq_zero_of_resH1_e1cMap_eq_zero N D z h,
    fun h => resH1_e1cMap_eq_zero_of_resH2_e1aChainH_eq_zero N D hDcl z h⟩

section FinitePlaceFiveTerm

open Work.AbsoluteKummer

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

/-- **The subgroup of a decomposition group fixing `K` is open.**

For a place `A` of `Ω` over `k`, put `H₀ := decomp k A ⊓ Gal(Ω/K)`: this is the kernel of the
restriction `decomp k A → Gal(K/k)`, so it has finite index in `decomp k A` (which is profinite),
hence is open.  In the graded form used below, `H₀` is the `subgroupOf`-pullback of the *open*
subgroup `Gal(Ω/K) ≤ Γ` along the inclusion `decomp k A ↪ Γ`.

This is the openness hypothesis of the five-term (inflation–restriction) sequence at the finite
place `A`, i.e. the numerical input of the "missing square" of the finite-place `himg` input
(`NOTE_himgIdelesInput_inf_reduction.md` §9.2, `NOTE_himg_status_session11.md` §3). -/
theorem isOpen_subgroupOf_ker_decomp (A : ValuationSubring Ω) :
    IsOpen (((SSGRoute.res k K).ker.subgroupOf (SSGRoute.decomp k A) :
      Subgroup ↥(SSGRoute.decomp k A)) : Set ↥(SSGRoute.decomp k A)) := by
  have h : IsOpen (((SSGRoute.res k K).ker : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
    rw [IntermediateField.restrictNormalHom_ker K]
    exact IntermediateField.fixingSubgroup_isOpen K
  rw [Subgroup.subgroupOf, Subgroup.coe_comap]
  exact h.preimage continuous_subtype_val

/-- **The five-term step at a finite place, in the shape needed by the finite-place `himg` input.**

For `H₀ = decomp k A ⊓ Gal(Ω/K)` (`= (res k K).ker.subgroupOf (decomp k A)`), the continuous
inflation map

    infH1_c : H¹_c(D_A ⧸ H₀, Hom_ℤ(R.V,Ωˣ)^{H₀}) → H¹_c(D_A, Hom_ℤ(R.V,Ωˣ))

is an isomorphism, provided only that `H¹_c(H₀, Hom_ℤ(R.V,Ωˣ)) = 0` (Hilbert 90 at the closed
subgroup `H₀ ≤ Gal(Ω/K)`, on disk as
`ExtChain.subsingleton_h1_homCoind_decomp_inf_ker`).

Combined with the identification of the invariant module
(`ExtChain.homCoind_invariants_decomp_inf_ker_equiv`: `Hom_ℤ(R.V,Ωˣ)^{H₀} = Hom_ℤ(R.V,(Ω^{H₀})ˣ)`
with `Ω^{H₀} = K·Ω^{D_A}` the decomposition compositum), this identifies `H¹(D_A, Hom_ℤ(R.V,Ωˣ))`
with the `D_q`-level (i.e. `Gal(K/k)`-level, `D_q = res(D_A)`) group
`H¹(D_q, Hom_ℤ(R.V,(K·Ω^{D_A})ˣ))` — the left-hand half of the sharp form (★) of
`NOTE_himg_extDelta_session13.md` §2. -/
theorem infH1_c_decomp_inf_ker_bijective
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] [Module.Free ℤ R.V]
    (A : ValuationSubring Ω)
    (hsub : Subsingleton (Work.AbsoluteKummer.H1
      ↥((SSGRoute.res k K).ker.subgroupOf (SSGRoute.decomp k A))
      (Work.SSGRoute.homCoind k Ω K R))) :
    Function.Bijective (infH1_c (A := Work.SSGRoute.homCoind k Ω K R)
      ((SSGRoute.res k K).ker.subgroupOf (SSGRoute.decomp k A))
      (isOpen_subgroupOf_ker_decomp (k := k) (Ω := Ω) (K := K) A)) :=
  infH1_c_bijective _ _ hsub

/-- **The finite-place target, reduced to a single extension obligation.**

By `E1cGeneric.PhiE_surjective` every `z ∈ Ext¹_G(R, Kˣ)` is `PhiE R y` for some
`y ∈ Ext⁰_G(R₁, Kˣ)` (`R₁ = ker (freeCover R)`), and by the extension criterion
`ExtChain.resH1_e1cMap_eq_zero_of_extension` the conclusion `resH1_{D}(e1cMap R z) = 0` follows as
soon as `y` admits a `D`-invariant lift `Φ : (E1cF R).V →+ Ωˣ` along `kappa R`.

So the *whole* content of the finite-place input is the existence of such a lift: this lemma names
the obligation in the target's own vocabulary, and its converse
(`E1aClean.exists_invariant_extension_of_resH1_e1cMap_eq_zero`) is on disk, so the two together say
the input *is* that extension problem. -/
theorem resH1_e1cMap_eq_zero_of_invariant_extension
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite R.V] [Module.Finite ℤ R.V]
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (z : CategoryTheory.Abelian.Ext.{0} R (SSGRoute.PTExt.unitsK k K) 1)
    (h : ∃ y : CategoryTheory.Abelian.Ext.{0} (Work.SSGRoute.ExtChain.E1cR1 R)
          (SSGRoute.PTExt.unitsK k K) 0,
        Work.SSGRoute.ExtChain.E1cGeneric.PhiE R y = z ∧
          ∃ Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R,
            Φ ∈ Work.AbsoluteKummer.H0 ↥D (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R) ∧
            Φ.comp (Work.SSGRoute.ExtChain.E1cGeneric.kappa R)
              = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
                  (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) y).1) :
    Work.SSGRoute.PT.H2Fin.resH1 D (Work.SSGRoute.homCoind k Ω K R)
      (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap R z) = 0 := by
  obtain ⟨y, rfl, Φ, hΦ, hκ⟩ := h
  exact resH1_e1cMap_eq_zero_of_extension (k := k) (Ω := Ω) (K := K) R y D Φ hΦ hκ

end FinitePlaceFiveTerm

section InvariantLiftValues

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField K]

/-- **Every `D`-invariant lift of the coefficient data is `Ω^{D ⊓ Gal(Ω/K)}`-valued.**  General form
of `invariant_lift_values_mem_fixedField` (no hypothesis whatsoever on the subgroup `D`): an
element of `H⁰(↥D, Hom_ℤ(F_R,Ωˣ))` takes its values in the units of the fixed field of
`D ⊓ Gal(Ω/K)`, because `D ⊓ Gal(Ω/K)` acts trivially on the free coefficient `(E1cF R).V`. -/
theorem invariant_lift_values_mem_fixedField_gen
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (D : Subgroup (Ω ≃ₐ[k] Ω))
    (Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)
    (hΦ : Φ ∈ Work.AbsoluteKummer.H0 ↥D
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)) :
    ∀ v : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF R).V,
      ((Additive.toMul (Φ v) : Ωˣ) : Ω) ∈
        IntermediateField.fixedField (D ⊓ (SSGRoute.res k K).ker) := by
  intro v
  refine (Work.SSGRoute.ExtChain.homCoind_fixed_iff_mem_fixedField
    (k := k) (Ω := Ω) (K := K) (Work.SSGRoute.ExtChain.E1cGeneric.E1cF R)
    (D ⊓ (SSGRoute.res k K).ker) inf_le_right Φ).mp ?_ v
  intro σ hσ
  exact (Work.GroupCohomology.mem_invariants (↥D)
    (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R) Φ).mp hΦ ⟨σ, hσ.1⟩

/-- **Every `D_A`-invariant lift of the coefficient data is `K·Ω^{D_A}`-valued** — the
coefficient-field mismatch of `ExtChain/NOTE_himg_status_session11.md` §2 is *not* an obstruction
on the *lift* side.

Let `A` be a place of `Ω`, `D_A = decomp k A ≤ Γ = Ω ≃ₐ[k] Ω`, `H := D_A ⊓ Gal(Ω/K)`, and
`L := K·Ω^{D_A} = Ω^H` the algebraic decomposition compositum.  For every `D_A`-invariant
`Φ ∈ Hom_ℤ((E1cF R).V, Ωˣ)` — i.e. every element of `H⁰(D_A, Hom_ℤ(F_R, Ωˣ))` — the value `Φ v`
lies in `L`:

    Φ ∈ H⁰(D_A, Hom_ℤ(F_R,Ωˣ))  ⟹  ∀ v, Φ v ∈ (Ω^H)ˣ .

Proof: `H` acts *trivially* on `(E1cF R).V` (its action goes through `res k K`, which kills
`H ≤ ker (res k K)`), so `D_A`-invariance of `Φ` gives `h • Φ(v) = Φ (ρ (res h) v) = Φ v` for
`h ∈ H`; the identification of the `H`-fixed units of `Ω` with the units of the fixed field is
`homCoind_fixed_iff_mem_fixedField` (`IntermediateField.mem_fixedField_iff`).

**Why this matters.**  The extension criterion says `resH1_{D_A}(e1cMap R z) = 0` is equivalent to
the existence of a `D_A`-invariant `Ωˣ`-valued lift of the `Kˣ`-valued data, and the lane has
repeatedly recorded the *sharp form* of the finite-place input as the coefficient-changed statement
`cc_L(res_{D_q} z) = 0` (`L`-valued lift), worrying (`ExtChain/NOTE_himg_extDelta_session13.md` §2)
that the passage `H¹(D_A, Hom(R.V,Lˣ)) → H¹(D_A, Hom(R.V,Ωˣ))` might fail for twisted coefficients.
This lemma shows that the passage is *onto the invariants of the criterion*: there are no
`D_A`-invariant lifts outside `Lˣ`, so the two descriptions of `resH1_{D_A}(e1cMap R z) = 0`
(a `D_A`-invariant `Ωˣ`-lift, equivalently an `Lˣ`-lift) coincide for the canonical syzygy.  The
genuine content of the input is therefore the *coefficient of the local group* (`Kˣ` versus `Lˣ` at
`D_q`), and not a `K`-versus-`K·Ω^{D_A}` mismatch of the lift. -/
theorem invariant_lift_values_mem_fixedField
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (A : ValuationSubring Ω)
    (Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)
    (hΦ : Φ ∈ Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)) :
    ∀ v : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF R).V,
      ((Additive.toMul (Φ v) : Ωˣ) : Ω) ∈
        IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker) :=
  invariant_lift_values_mem_fixedField_gen (k := k) (Ω := Ω) (K := K) R
    (SSGRoute.decomp k A) Φ hΦ

/-- The fixed field in `invariant_lift_values_mem_fixedField` is the decomposition compositum:
`Ω^{D_A ⊓ Gal(Ω/K)} = K ⊔ Ω^{D_A}` (`fixedField_inf_fixingSubgroup`). -/
theorem invariant_lift_values_mem_sup
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (A : ValuationSubring Ω)
    (Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)
    (hΦ : Φ ∈ Work.AbsoluteKummer.H0 ↥(SSGRoute.decomp k A)
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R)) :
    ∀ v : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF R).V,
      ((Additive.toMul (Φ v) : Ωˣ) : Ω) ∈
        (IntermediateField.fixedField (SSGRoute.decomp k A) ⊔ K : IntermediateField k Ω) := by
  intro v
  haveI hGal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  have hHc : IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) :
      Set (Ω ≃ₐ[k] Ω)) :=
    Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring A
  rw [← fixedField_inf_fixingSubgroup (k := k) (Ω := Ω) K (SSGRoute.decomp k A) hHc,
    ← IntermediateField.restrictNormalHom_ker K]
  exact invariant_lift_values_mem_fixedField (k := k) (Ω := Ω) (K := K) R A Φ hΦ v

/-- **The extension criterion in its sharp form: the lift may be taken with values in the fixed
field.**  For `R = ker (freeCover N)` and any subgroup `D ≤ Γ = Ω ≃ₐ[k] Ω`,

    resH1_D (e1cMap R (PhiE R w)) = 0
      ⟺  ∃ Φ ∈ H⁰(↥D, Hom_ℤ(F_R, Ωˣ)),
            Φ ∘ κ_R = ΨE w   and   ∀ v, Φ v ∈ (Ω^{D ⊓ Gal(Ω/K)})ˣ .

The `⟹` direction combines the exactness of the dualised canonical resolution at `H⁰` over `D`
(`PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf`, whose hypothesis is
`[Module.Finite ℤ R.V]` — the `[Finite R.V]` version is unusable on the canonical syzygy) with
`invariant_lift_values_mem_fixedField_gen`; the `⟸` direction is the extension criterion
`ExtChain.resH1_e1cMap_eq_zero_of_invariant_lift` (same harness module).

**Content for the lane.**  With `D = decomp k A` and `D ⊓ Gal(Ω/K) = Ω`-fixed-field `= K·Ω^{D_A}`,
the right-hand side is exactly the *coordinate-free* form of
`cc_{K·Ω^{D_A}}(res_{D_q} z) = 0` (`NOTE_himg_extDelta_session13.md` §2).  So the target of this
file is *equivalent* to the honest input recorded there — the two are the same statement, one level
apart — and the arithmetic must be supplied at the finite level `D_q = res k K '' D_A`
(coefficient `Kˣ` versus `(K·Ω^{D_A})ˣ`), not by coefficient bookkeeping at `D_A`. -/
theorem resH1_e1cMap_eq_zero_iff_exists_fixedField_lift
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (w : CategoryTheory.Abelian.Ext.{0}
      (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) (SSGRoute.PTExt.unitsK k K) 0)
    (D : Subgroup (Ω ≃ₐ[k] Ω)) :
    (Work.SSGRoute.PT.H2Fin.resH1 D (Work.SSGRoute.homCoind k Ω K R)
        (Work.SSGRoute.ExtChain.E1cGeneric.e1cMap R
          (Work.SSGRoute.ExtChain.E1cGeneric.PhiE R w)) = 0) ↔
      (∃ Φ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN R,
        Φ ∈ Work.AbsoluteKummer.H0 ↥D (Work.SSGRoute.ExtChain.E1cGeneric.E1cN R) ∧
        Φ.comp (Work.SSGRoute.ExtChain.E1cGeneric.kappa R)
            = (Work.SSGRoute.ExtChain.E1cGeneric.PsiEMap
                (Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R) w).1 ∧
        ∀ v : (Work.SSGRoute.ExtChain.E1cGeneric.E1cF R).V,
          ((Additive.toMul (Φ v) : Ωˣ) : Ω) ∈
            IntermediateField.fixedField (D ⊓ (SSGRoute.res k K).ker)) := by
  constructor
  · intro h
    obtain ⟨Φ, hΦ, hκ⟩ :=
      Work.SSGRoute.PTdualControl.exists_invariant_extension_of_resH1_e1cMap_eq_zero_inf
        (k := k) (Ω := Ω) (K := K) R D w h
    exact ⟨Φ, hΦ, hκ,
      invariant_lift_values_mem_fixedField_gen (k := k) (Ω := Ω) (K := K) R D Φ hΦ⟩
  · rintro ⟨Φ, hΦ, hκ, _⟩
    exact Work.SSGRoute.ExtChain.resH1_e1cMap_eq_zero_of_invariant_lift
      (k := k) (Ω := Ω) (K := K) R w D Φ hΦ hκ

end InvariantLiftValues

section ReductionToLatticeHasse

/-- **The finite-place half of the `himg` input, reduced to the degree-one Hasse principle for
`ℤ`-lattices at the decomposition group.**

This is the exact mirror of the involution half
(`ExtChain.himg_involution_input_two_of_latticeHasse`): the whole arithmetic content of the
finite-place clause is isolated into one statement about the *finite* group
`Dq := res k K '' decomp k A ≤ Gal(K/k)` — namely, that the coefficient change `Kˣ → 𝕀_K` makes
`Ext¹_{Dq}(M, Kˣ) → Ext¹_{Dq}(M, 𝕀_K)` injective for every finitely generated free `ℤ`-lattice `M`.

Proof of the reduction (no arithmetic): by `extToIdeles_e1aSyzShift_eq_zero_iff` the hypothesis is
`extToIdeles z = 0`; restricting to `Dq` (`Rep.resMap`/`mapExactFunctor_comp`) gives
`(extRes_{Dq} z) ∘ mk₀ (ideleIncl) = 0`, which is the hypothesis of the lattice Hasse principle at
`Dq`; there it yields `extRes_{Dq} z = 0`; and the finite-place restriction square
`ExtChain.resH1_e1cMap_eq_zero_of_extRes_map_eq_zero` (proved) turns that into the conclusion.

Nothing here is `himg`-specific: the *same* reduction works for any finite place `A` and any
`z`, so the finite half of `himg` is *equivalent* to the lattice Hasse principle at the
decomposition groups (for the canonical syzygy `R = ker (freeCover N)`, one needs it only for
`M = R`; the general form is recorded here because that is the shape in which the `C₂` instance was
proved and delegated — `ExtChain.hasseExt1_C2_lattice_general`). -/
theorem himgIdelesInput_fin_of_latticeHasse
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hns : ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker))
    (hH : ∀ y : CategoryTheory.Abelian.Ext.{0}
          (Rep.res (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)).subtype
            (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
              (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
          (Rep.res (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)).subtype
            (SSGRoute.PTExt.unitsK k K)) 1,
        y.comp (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)).subtype
              (NK.HassePrinciple.ideleIncl k K))) (add_zero 1) = 0 → y = 0)
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0) :
    Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0 := by
  classical
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hNfin : Finite (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  -- the hypothesis is the idèle localisation of `z` itself
  have hz' : SSGRoute.PTExt.extToIdeles (k := k) z = 0 :=
    (extToIdeles_e1aSyzShift_eq_zero_iff (k := k) (K := K)
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z).mp hz
  -- its restriction to the image `Dq` of the decomposition group
  have hloc : (SSGRoute.PTExt.extRes
      (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)).subtype z).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)).subtype
          (NK.HassePrinciple.ideleIncl k K))) (add_zero 1) = 0 := by
    show (CategoryTheory.Abelian.Ext.mapExactFunctor
        (Rep.resFunctor (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)).subtype) z).comp
      (CategoryTheory.Abelian.Ext.mk₀
        (Rep.resMap (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)).subtype
          (NK.HassePrinciple.ideleIncl k K))) (add_zero 1) = 0
    rw [← CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀
      (F := Rep.resFunctor (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)).subtype)
      (f := NK.HassePrinciple.ideleIncl k K)]
    rw [← CategoryTheory.Abelian.Ext.mapExactFunctor_comp
      (F := Rep.resFunctor (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)).subtype)
      (α := z)
      (β := CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k K)) (add_zero 1)]
    rw [show z.comp (CategoryTheory.Abelian.Ext.mk₀ (NK.HassePrinciple.ideleIncl k K))
        (add_zero 1) = 0 from hz']
    simp
  -- the degree-one Hasse principle at `Dq` (the arithmetic input)
  have hzD : SSGRoute.PTExt.extRes
      (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)).subtype z = 0 :=
    hH (SSGRoute.PTExt.extRes (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)).subtype z)
      hloc
  -- the finite-place restriction square turns the restricted `Kˣ`-vanishing into the conclusion
  obtain ⟨w, hw⟩ := Work.SSGRoute.ExtChain.E1cGeneric.PhiE_surjective (k := k) (Ω := Ω) (K := K)
    (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z
  rw [← hw]
  refine Work.SSGRoute.ExtChain.resH1_e1cMap_eq_zero_of_extRes_map_eq_zero
    (k := k) (Ω := Ω) (K := K)
    (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover
      (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
    (SSGRoute.decomp k A)
    (Subgroup.map (SSGRoute.res k K) (SSGRoute.decomp k A)) ?_ w ?_
  · intro δ hδ
    exact ⟨δ, hδ, rfl⟩
  · exact (congrArg (fun t => SSGRoute.PTExt.extRes (Subgroup.map (SSGRoute.res k K)
        (SSGRoute.decomp k A)).subtype t) hw).trans hzD

end ReductionToLatticeHasse

/-- **The finite-place half of the `himg` input, in hypothesis form.**  This is a theorem, not a
formal consequence: the hypothesis is the *global* (all-places) vanishing of the idèle localisation,
and the conclusion is the local comparison at one place.  The corresponding *per-place* statement
(`z_w = 0` at the single place below `A`) is FALSE (session 11, quaternion class `(−1,−1)` over
`ℚ(i)`) — the all-places hypothesis is essential. -/
theorem himgIdelesInput_fin (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [hRfin : Module.Finite ℤ ↥(CategoryTheory.Limits.kernel
      (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))]
    (z : CategoryTheory.Abelian.Ext.{0}
      (CategoryTheory.Limits.kernel
        (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E)))
      (SSGRoute.PTExt.unitsK k K) 1)
    (hz : SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K)
        (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E) z) = 0)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hns : ¬ (SSGRoute.decomp k A ≤ (SSGRoute.res k K).ker)) :
    Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
      (Work.SSGRoute.homCoind k Ω K
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))))
      (Work.SSGRoute.ExtChain.e1cMap
        (CategoryTheory.Limits.kernel
          (Work.SSGRoute.freeCover (Work.SSGRoute.SSGStage.e1aN0 p k Ω K T E))) z) = 0 := by
  -- The finite-place clause is proved in full, one module *below* this one (so that
  -- `ExtChain.exists_khLift_of_extToIdeles_eq_zero`, a child of that file, can be used by it
  -- without importing this file): `Submission.Work.SSGRoute.ExtChain.himgIdelesInput_fin_leaf`.
  -- Its statement is verbatim this one.
  exact Work.SSGRoute.ExtChain.himgIdelesInput_fin_leaf p k Ω K ζ hζ hζK T hT E z hz A hA hns

end Work.SSGRoute.ExtChain
