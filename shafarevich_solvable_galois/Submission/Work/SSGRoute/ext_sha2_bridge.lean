import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.ShaCocycles
import Submission.NK.HassePrinciple.locUnits_compatible
import Submission.Work.SSGRoute.extToIdeles_eq_zero_iff_extLoc
import Submission.Work.SSGRoute.ExtChain.FreeCover
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.ExtChain.hC_assembly
import Submission.Work.SSGRoute.ExtChain.himg_of_ideles_input_fin_clean
import Submission.Work.SSGRoute.SSGStage.e1aLandingClause
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_EXT.md (the lead's Ext-core design for Poitou–Tate) + DESIGN_PT.md. Definitions: Submission/Work/SSGRoute/PTDefs.lean (namespace SSGRoute.PTExt; do NOT edit). NK.* CFT library available. Siblings run in parallel.

# E1a `ext_sha2_bridge` — `Ш²(k,E) = ker(Ext²_G(E',Kˣ) → Ext²_G(E',𝕀_K))`

**Statement.** `E' = DualMod p (E ⊗ T)`. There are injective additive maps
`β_E : Ш²(k,E) → Ext²_{Gal(K/k)}(E', Kˣ)` that are natural in `E` (the transpose `F` of `f ⊗ id_T`
acts on `Ext` by precomposition). The image is exactly `ker(extToIdeles)`.

**Route. Do not build a Hochschild–Serre spectral sequence; resolve `E'` instead.**
1. **Resolve `E'`.** Take `0 → R → F → E' → 0` with `F` free over `ℤ[G]` of finite rank and `R` a
   `ℤ[G]`-lattice. Then `Ext²_G(E', X) = Ext¹_G(R, X) = H¹(G, Hom(R, X))` for `X = Kˣ, 𝕀_K`.
2. **Dualise into `Ω̄ˣ`.** Apply `Hom(·, Ω̄ˣ)`; this is exact because `Ω̄ˣ` is divisible. It gives
   `0 → E → Hom(F, Ω̄ˣ) → Hom(R, Ω̄ˣ) → 0`.
   - `Hom(F, Ω̄ˣ)` is coinduced from `G_K`, so its `H¹` is 0 by Hilbert 90 and Shapiro.
   - Hence `δ : H¹(k, Hom(R, Ω̄ˣ)) ↪ H²(k, E)`.
3. **Descend to level `K`.** Inflation–restriction plus Hilbert 90 over `K` give
   `H¹(G, Hom(R, Kˣ)) ≅ H¹(k, Hom(R, Ω̄ˣ))`.
4. **Land `Ш²` in the image.** `Ш²(k,E)` maps into `Ш²(K, E)`, which is 0 (`sha2_restrict_vanish`).
   So `Ш²(k,E) ⊆ ker(H²(k,E) → H²(K,E)) = im δ`.
5. **Match the local conditions.** The local conditions correspond under the same construction with
   `K_wˣ` (Shapiro, as in E2). The image is therefore `ker(extToIdeles)`.

**Deps.** E0b, E2, `sha2_restrict_vanish`, Hilbert 90 (NK `hilbert90_cocycle`, local and global).

**Size.** 2–3k. **Risk:** medium-high. Most of the size is the glue between continuous cochains on
`G_k` and finite-level `groupCohomology`.

**Imports.** `Submission.Work.SSGRoute.PTDefs Submission.Work.SSGRoute.Interfaces Submission.Work.SSGRoute.DualMod.Main Submission.Work.SSGRoute.ShaCocycles`.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct


/-! ## STATUS / ROUTE (recorded by the E1a prover, for continuation)

**What the statement says.** `E' = DualMod p (E ⊗ T) = E^∨(1)` (with `T` the cyclotomic dual of
`μ_p` and `ζ ∈ K`, so `T ⊗ μ_p ≅ 𝔽_p` as `Gal(K/k)`-modules and every completion `K_w` contains
`μ_p`).  The theorem asserts the existence of additive injections
`β_E : Ш²(k,E) → Ext²_G(E',Kˣ)`, natural in `E`, whose image is *exactly*
`ker(Ext²_G(E',Kˣ) → Ext²_G(E',𝕀_K))`.

**The two sides are genuinely isomorphic, and both are usually nonzero.**
* `Ext²_G(E',X) ≅ Ext¹_G(R,X) ≅ H¹(G, Hom_ℤ(R,X))` for **any** `X` (resolve `E'` by
  `0 → R → F → E' → 0` with `F` free over `ℤ[G]` of finite rank; `R` is then a lattice, and the
  dictionary `Ext¹_G(R,X) ≅ H¹(G,Hom(R,X))` is `ExtChain.ext_homRep_addEquiv`).
  **CORRECTION (session 5, see `NOTE_e1a_session5.md` (C1)):** the further step to
  `H²(G, Hom_ℤ(E',X))` — asserted in earlier versions of this STATUS block — is *false* in general;
  it is the connecting map of `Hom(E',X) → Hom(F,X) → Hom(R,X) → Q → 0`, and it is an isomorphism
  **iff** `Hom_ℤ(F,X) → Hom_ℤ(R,X)` is onto, i.e. essentially iff `X` is `ℤ`-injective (divisible).
  For divisible `X` this is the proved `Work.SSGRoute.ext_two_iso_divisible_cohomology`; for
  `X = ℤ` it fails (`G = ℤ/2`, `E' = 𝔽₂`: `Ext²_G(E',ℤ) = ℤ/2` but `H²(G,0) = 0`), and for the
  `X = Kˣ` of this target it is *not* available, so the object `Ext²_G(E',Kˣ)` is pinned only by its
  syzygy description.  Consequences: (i) any appeal to `Ext²_G(E',Kˣ) ≅ H²(G,E)` is replaced by the
  syzygy form; (ii) at an *archimedean* place with `K_w = ℂ` the coefficient `ℂˣ` *is* divisible, so
  the local dictionary there is `Ext²_{D_w}(res E',ℂˣ) ≅ H²(D_w,Hom(E',ℂˣ)) ≅ H²(D_w,E)` — in
  particular it is *not* zero (earlier notes concluding `= 0` from "`H¹` of a divisible module
  vanishes" applied the vanishing to the wrong term of the long exact sequence).
* `Hom_ℤ(E',Kˣ) ≅ E` and `Hom_ℤ(E',K_wˣ) ≅ E` (all `w`), because homs from the `p`-group `E'`
  land in the `p`-torsion, giving `Hom(E',Kˣ) ≅ Hom(E',μ_p) ≅ (E⊗T) ⊗ μ_p ≅ E ⊗ (T ⊗ μ_p) ≅ E`.
  Hence `Ext²_G(E',Kˣ) ≅ H²(G,E)` and `Ext²_G(E',𝕀_K) ≅ ∏'_w H²(D_w,E)`, the map being the
  product of the local restrictions.
* `Ш²(k,E) = Z²_loc/B²` (cocycle form, `ShaCocycles`) is the locally trivial part of `H²(k,E)`:
  `Ш²(k,E) ≅ ker(H²(k,E) → ∏_A H²(D_A,E))` over the finite places `A` of `Ω` over `k` (plus the
  involution conditions), and the intended `β` is this identification followed by
  `H²(k,E) ⊇ ker(H²(k,E) → H²(K,E)) ≅ H¹(k,Hom(R,Ω̄ˣ)) ≅ H¹(G,Hom(R,Kˣ)) ≅ Ext²_G(E',Kˣ)`
  (the design's `DESIGN_EXT.md` §E1a steps 1–3; `sha2_restrict_vanish` supplies the inclusion into
  `ker(H²(k,E) → H²(K,E))`).

**Do NOT expect `Ш²(k,E) = 0`.**  Milne, *Arithmetic Duality Theorems*, Example I.9.1: for
`k = ℚ`, `K = ℚ(√13,√17)` (`Gal = (ℤ/2)²`, all decomposition groups of order ≤ 2) and
`M` the module `0 → M → (ℤ/4)[G] → ℤ/4 → 0`, one has `Ш¹(ℚ,M) ≠ 0` and, by the duality theorem,
`Ш²(ℚ,M) ≠ 0`.  (This also shows that the "`Ш²(k,M)=0` for all finite `M`" route — the
`sha2_image_of_Hm2` route 2 — is *false*; only the trivially-acted case, as in
`sha2_trivial_vanish`, is available.)  So the target must be proved by *constructing* `β`, not by
vanishing: `β = 0` is not an option.

**SESSION NOTE (2026-09-27, second pass) — see `Submission/Work/SSGRoute/NOTE_e1a_next_steps.md`.**

* The local-conditions objection (see the "flagged concern" section of
  `Submission/Work/SSGRoute/sha2_dual_control.lean`) rests on the *naive* finite-level dictionary
  `Ext^r_{D_w}(M,K_wˣ) ≅ H^r(D_w, Hom(M,K_wˣ))`, which the fleet has **refuted by computation**
  (`Submission/Work/SSGRoute/E7a_HANDOFF.md` §4: the finite-level pairing uses
  `Ext¹_D(E,K_wˣ)`, not `H¹(D,Hom(E,K_wˣ))`).  The correct local dictionary is over the **full
  local group** `D_A`: `Ext¹_{ℤ[D_w]}(M,K_wˣ) ≅ H¹(D_A,M)` (`E7a`, `local_ext_h1_bridge.lean`).
  Both sides of the `↔` clause are therefore conditions at `D_A`, as the design intends.  **Do not
  declare this node false on the strength of that concern.**
* Proved in this file: `Work.SSGRoute.extLoc_extToIdeles_eq_mk₀` — the localisation formula for
  `extToIdeles` at a place, for an arbitrary first variable (the general-`M` form of
  `PTembedding.extLoc_extToIdeles_eq`).
* Remaining: (a) the degree-2 local dictionary at the `D_A` level, with its coherence with the
  global dictionary (`extLoc w ∘ extToIdeles` ↦ `res_{D_A}`); (b) naturality in `E` (the
  dictionaries exist only as `Nonempty`-witnesses, and the free covers are chosen by
  `Classical.choose`).  Delegate: `SSGRoute/extToIdeles_eq_zero_iff_extLoc`.

**SESSION NOTE (2026-09-28, third pass) — see `Submission/Work/SSGRoute/NOTE_e1a_session3.md`.**

* The canonical `Ext`-side chain of E1a is now on disk and sorry-free, as the module
  `Submission.Work.SSGRoute.ExtChain.ChainGamma` (imported by this file): the canonical syzygy
  shift with its naturality in the first variable (`e1aSyzShift`, `e1aSyzMap`,
  `syzShift_natural`), the dualised canonical resolution and *its* connecting map
  (`e1aSES`, `e1aDelta`, `e1aDelta_injective`), the `Hom`-side chain (`e1aChainHom`), the canonical
  coefficient identification (`e1aCoeffNat`, `e1aCoeffH2`), and the **full chain**
  `e1aChain : Ext²_G(E',Kˣ) →+ H²(Γ,E)` with `e1aChain_injective`.
* The target is thereby reduced to three statements: (O1) naturality of the `E1c` dictionary in the
  first variable (`SSGRoute/ExtChain/e1c_natural`, statement reviewed and approved, not yet proved),
  (O2) naturality of `δ` under the comparison of the two dualised canonical resolutions, and
  (O3) the arithmetic crux `Ψ(ker extToIdeles) = Ш²(k,E)` (= the local Tate duality in degree 2 of
  the `E7a` lane).  `NOTE_e1a_session3.md` §1–§4 gives the precise statements and the assembly; §5
  records the engineering pitfalls (unfolding `AddEquiv.ofBijective`, the `homCoindFreeT` wrapper,
  `hφ.τ₁` unification).

**SESSION NOTE (2026-09-29, fifth pass) — see `Submission/Work/SSGRoute/NOTE_e1a_session5.md`.**

* No statement of this file was changed; the target still carries exactly one `sorry` (clause 2).
* Corrections of record: (C1) the dictionary `Ext²_G(E',X) ≅ H²(G,Hom_ℤ(E',X))` needs `X` divisible
  (see the corrected bullet above); (C2) the archimedean places with `K_w = ℂ` use the
  *divisible*-coefficient dictionary (`ExtChain.ext_two_iso_divisible_cohomology`) and are nonzero;
  for `p = 2` and `K_w = ℝ` the units are not divisible and the lattice route is needed again.
* The crux (clause 2) is exactly the per-place *comparison square*
  `Λ_w ((extRes_{D_w} y) ∘ mk₀(ι_w)) = res_{D_A}(Ψ y)` for the canonical chain `Ψ = e1aChainNat`
  (assembled from `e1aE1cNat`, `e1aDelta`, `e1aCoeffH2`, each of them a `Nonempty`/`choose`
  witness), i.e. the group-restriction compatibility of the chain; the ⟸-direction additionally
  needs the *injectivity* of `Λ_w` and the ⟹-direction needs the *explicit* construction of a
  locally trivial cocycle from a finite-level 1-cocycle (see `NOTE_e1a_session5.md` §1, including
  the warning that the push-forward `λ_w` is *not* injective, so `res_{D_w} y = 0` cannot be
  replaced by the vanishing of its push-forward without an argument).
* Since session 5, `Work.SSGRoute.ExtChain.ext_homRep_addEquiv`,
  `Work.SSGRoute.ext_two_iso_divisible_cohomology`,
  `Work.SSGRoute.PT.e1aBetaLocalChain.ext_two_local_descent_injective` and
  `Work.SSGRoute.PT.extToIdeles_e1aSyzShift` are on disk; the sibling lane `PT/` is ahead on the
  assembly (`PT.e1a_ext_sha2_bridge_assembly` + `PT.e1aBetaCan_image`), and this node's target is
  the same statement, so it can be closed from the sibling lane's result once the crux lands.

**Local-condition subtlety to be respected.**  The cocycle-level local condition in `Z2loc` is at
the level of the decomposition group `D_A ≤ G_k` of a place `A` of `Ω`
(`IsCoboundary2On (res k K) (decomp k A) c`), i.e. the class lives in `H²(D_A,E) = H²(k_v,E)`,
whereas the `Ext`-side local condition coming from `𝕀_K = ∏ʳ_w K_wˣ` is at the level of
`D_w = Gal(K_w/k_v)` acting on `K_wˣ`.  For `y ∈ H²(G,E)`, `inf y ∈ H²(k,E)` has
`res_{D_A}(inf y) = inf_w(res_{D_w} y)`, so the two conditions differ by `ker(inf_w)`; the statement
of E1a asserts that the *groups* agree (both are `≅ Ш²(k,E) ≅ ker(extToIdeles) ∋ y`), which is the
content of the theorem.

**Missing pieces (all absent from the workspace; each is a separate theorem).**
1. **`Ext²_G(R,X) ≅ H²(G, Hom_ℤ(R,X))` for a `ℤ`-lattice `R`** (i.e. `R.V` free and finitely
   generated over `ℤ`; `Module.Free ℤ R.V` + `Module.Finite ℤ R.V`), with naturality in `R`
   (precomposition by the transpose) and in `X`.
   *Reviewer-verified correction (2026-09-26):* the version with a **finite** `M` instead of a
   lattice is **FALSE**.  Counterexample (both reviewers): `G = ℤ/2`, `M = X =` the trivial rep on
   `ℤ/2`: then `Hom_ℤ(M,X) = ℤ/2` and `H²(G,ℤ/2) = ℤ/2 ≠ 0`, while
   `Ext²_{ℤ[G]}(ℤ/2,ℤ/2) = Ext²_ℤ(ℤ/2,ℤ/2) = 0`.  The reason: for `M` finite there is a
   presentation `0 → R → F → M → 0` with `F` free over `ℤ[G]` and the syzygy `R` a *lattice*, but
   `0 → Hom(M,X) → Hom(F,X) → Hom(R,X) → 0` is exact on the right only when `X` is divisible (or
   when the presentation splits over `ℤ`, which is impossible for torsion `M`).  Hence the correct
   chain is `Ext²(E',X) ≅ Ext¹(R,X) ≅ H¹(G, Hom(R,X))` for the *lattice* `R`, and the step
   `H¹(G,Hom(R,X)) ≅ H²(G,Hom(E',X))` requires `X` divisible — which is exactly why the design
   dualises into `Ω̄ˣ` (divisible) and then descends to `Kˣ` by Hilbert 90.
   *Flag for the lead:* the same false "finite `M`" form of this dictionary appears in
   `Submission/Work/SSGRoute/poitou_tate_degree_two_surj.lean` (~line 242).
   * **Available now**: the colleague's `Submission.Work.SSGRoute.homRep` (module
     `Submission.Work.SSGRoute.homRep`, statement-free) supplies the internal Hom
     `Work.SSGRoute.homRep R N : Rep Coeff G` together with the global instances
     `homRepDistribMulAction` / `homRepSMulCommClass` on `R.V →ₗ[Coeff] N.V` and the computation
     rule `homRep_smul_apply : (g • f) x = N.ρ g (f (R.ρ g⁻¹ x))`.  Use that module; do not
     re-define the Hom (Mathlib has no `DistribMulAction G (M →ₗ[R] N)` instance for simultaneous
     actions, and `↑(Rep.of ρ)` does not reduce to its underlying type).
2. `Hom_ℤ(E',Kˣ) ≅ E` and `Hom_ℤ(E',K_wˣ) ≅ E` as `G`- (resp. `D_w`-) modules (the `μ_p`/`T`
   cancellation; uses `hT` and `ζ ∈ K`).
3. `Ext²_G(E',𝕀_K) ≅ ∏'_w Ext²_{D_w}(E',K_wˣ)` (Shapiro/localisation of the idèles; the design's
   node `E2`).
4. The cocycle bridge: `Z²_loc/B² ≅` the locally trivial part of `H²(k,E)`, compatible with the
   connecting map `δ` of `0 → R → F → E' → 0` (the design's step 4), plus Hilbert 90 over `K`
   for the descent `H¹(k,Hom(R,Ω̄ˣ)) ≅ H¹(G,Hom(R,Kˣ))`.
5. Naturality of the whole construction in `E` (the transpose acts by precomposition, matching the
   `Sha2Map` push-forward).

**SESSION NOTE (2026-10-05) — the node is now down to ONE named declaration.**

* **The landing clause is done, unconditionally and axiom-clean**: the proof below cites
  `Work.SSGRoute.SSGStage.e1aLandingClause` (`#print axioms = [propext, Classical.choice,
  Quot.sound]`), proved from the *finite* crux `PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero`
  (via `E1aClean.finLocalCriterion`), the *archimedean* crux `PTdualControl.archimedeanCruxA`, and the
  seam-carrying place glue `PTdualControl.glue_infinite_place_with_link`.  This replaces the earlier
  route through `SSGStage.e1aBetaCan_le_ker_via_landing`, whose archimedean input
  `SSGStage.archimedeanLocalDictionary` lacks the seam clause `hlink` and is false as written.
* **The `himg` half is routed above the import cycle** through the new
  `Work.SSGRoute.ExtChain.extToIdeles_eq_zero_imp_chainC_locallyTrivial_of_fin`
  (`ExtChain/himg_of_ideles_input_fin_clean.lean`), whose only remaining input is
  `Work.SSGRoute.ExtChain.himgIdelesInput_fin`.  The cycle itself was removed at its root:
  `ExtChain/freeCoverSES_lattice.lean` no longer imports this node (the import was unused by its
  proof); see `ExtChain/PING_landing_leaf_eliminated_and_push_engine.md`.
* **Consequently**: `#print axioms Work.SSGRoute.ext_sha2_bridge = [propext, sorryAx,
  Classical.choice, Quot.sound]`, the `sorryAx` coming *exactly* from
  `ExtChain.himgIdelesInput_fin` — this file's proof has no `sorry` term of its own.
* On that last declaration see `ExtChain/PING_push_route_tension.md`: the
  `(BC)`/`(PUSH)` route of `_lead_design/flags_0030/NOTE.md` §2/§4 appears to conflict with the
  per-place refutation of `NOTE_himg_extDelta_session13.md` §2, so the *global* form of the input
  (for `z` in the kernel of **all** the `cc_{K_w} ∘ res_{D_w}`) should be kept in view.
-/


/-- **Localisation of `extToIdeles` at a place, for an arbitrary first variable** (the general-`M`
form of `Work.SSGRoute.PTembedding.extLoc_extToIdeles_eq`, which is the case `M = ℤ`): the
`w`-component of `extToIdeles y` is the restriction of `y` to the decomposition group `D_w`
followed by the local unit embedding `Kˣ → K_wˣ`.  This is the computation rule by which the image
clause of `ext_sha2_bridge` is reduced to a statement about `Ext`-classes at the finite level
`Gal(K/k)` and their localisations at the `D_w`. -/
theorem extLoc_extToIdeles_eq_mk₀ (k : Type) [Field k] [NumberField k]
    (K : Type) [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) (y : Abelian.Ext.{0} M (unitsK k K) 2)
    (w : NK.GlobalCFT.Place K) :
    extLoc (k := k) w (extToIdeles (k := k) y) =
      (extRes (decompK (k := k) w).subtype y).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.unitsToLocalUnits k K w)) (add_zero 2) := by
  have h1 : extRes (decompK (k := k) w).subtype (extToIdeles (k := k) y)
      = (extRes (decompK (k := k) w).subtype y).comp
          (Abelian.Ext.mk₀ (Rep.resMap (decompK (k := k) w).subtype
            (NK.HassePrinciple.ideleIncl k K))) (add_zero 2) := by
    rw [extToIdeles, extRes, Abelian.Ext.mapExactFunctor_comp,
      Abelian.Ext.mapExactFunctor_mk₀]
    rfl
  rw [extLoc, h1]
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [Abelian.Ext.mk₀_comp_mk₀]
  rw [NK.HassePrinciple.res_ideleIncl_comp_ideleToLocalUnits]


/-! ## The canonical free cover and its functoriality (E1a infrastructure, 2026-09-28)

The `Ext`-side chain of `E1a` starts from a finite free cover `0 → R → F → E' → 0` of `E'` over
`ℤ[G]` (`G = Gal(K/k)`).  Every statement of the workspace so far obtains such a cover by
`Classical.choose` (`ext_level_lift.repFG_free_cover`), which is fatal for the *naturality* clause of
`ext_sha2_bridge`: two different coefficients `E₁`, `E₂` get two unrelated covers, so no comparison
map between the syzygies is available.

Here we introduce the *choice-free* cover

  `freeCover X : Rep.free Coeff G X.V ⟶ X`,

the free representation on the *underlying set* of `X` with the canonical surjection sending the
generator `x` to `x`, together with the canonical map `freeMap h` of covers induced by a morphism
`h : X ⟶ Y` and the naturality square `freeMap h ≫ freeCover Y = freeCover X ≫ h`.  For a finite
`X` (the case of `E' = DualMod p (E ⊗ T)`) the free module `Rep.free Coeff G X.V` is finitely
generated over `ℤ`, so its kernel is a `ℤ`-lattice, exactly the syzygy `R` that the `Ext`-side
dictionary needs.

This is the base of the "canonical chain" replacement for the `Nonempty`-witnessed dictionary: it
is the only place where the *choice* of the resolution is made, and it is made functorially. -/



/-- **E1a.** `Ш²(k, E)` is the kernel of localisation on `Ext²_{Gal(K/k)}(E', Kˣ)`,
`E' = DualMod p (E ⊗ T) = E^∨(1)`: there are injective additive maps
`Ш²(k,E) → Ext²_G(E', Kˣ)`, natural in `E`, whose image is exactly the kernel of
`Ext²_G(E', Kˣ) → Ext²_G(E', 𝕀_K)` (Hochschild–Serre for `Ext` with Hilbert 90, plus
`Ш²(K, E) = 0`). -/
theorem ext_sha2_bridge (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∃ β : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        Sha2 p k Ω K E →+
          Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) (unitsK k K) 2,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E], Function.Injective (β E)) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (y : Abelian.Ext (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))) (unitsK k K) 2),
          (∃ b, β E b = y) ↔ extToIdeles y = 0) ∧
      ∀ (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
        (F : modRep (K ≃ₐ[k] K) (DualMod p (E₂ ⊗[ZMod p] T)) ⟶
          modRep (K ≃ₐ[k] K) (DualMod p (E₁ ⊗[ZMod p] T)))
        (hF : ∀ (φ : DualMod p (E₂ ⊗[ZMod p] T)) (e : E₁) (t : T),
          (show DualMod p (E₁ ⊗[ZMod p] T) from F.hom φ) (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
        (b : Sha2 p k Ω K E₁),
        β E₂ (Sha2Map p k Ω K E₁ E₂ f hf b) = (Abelian.Ext.mk₀ F).comp (β E₁ b) (zero_add 2) := by
  -- The whole node is `ext_sha2_bridge_of` with its two interfaces supplied:
  -- * the landing clause `im β ⊆ ker extToIdeles`, now available unconditionally and axiom-clean
  --   as `SSGStage.e1aLandingClause` (proved through the *finite* crux
  --   `PT.extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero` / `E1aClean.finLocalCriterion` and the
  --   *archimedean* crux `PTdualControl.archimedeanCruxA` together with the seam-carrying place
  --   glue `PTdualControl.glue_infinite_place_with_link`; this replaces the earlier route through
  --   `SSGStage.e1aBetaCan_le_ker_via_landing`, whose archimedean input
  --   `SSGStage.archimedeanLocalDictionary` is stated without the seam clause `hlink` and was
  --   reported false as written);
  -- * the `himg` half of `(C')` (`ExtChain.extToIdeles_eq_zero_imp_chainC_locallyTrivial`), which
  --   is the single remaining leaf of this node.
  -- See `ExtChain/NOTE_A1_A2_session_2026-10-01b.md` §8--§10.
  exact Work.SSGRoute.ExtChain.ext_sha2_bridge_of p k Ω K ζ hζ hζK T hT
    (fun (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] =>
      Work.SSGRoute.ExtChain.extToIdeles_eq_zero_imp_chainC_locallyTrivial_of_fin
        p k Ω K ζ hζ hζK T hT E)
    (fun (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (hmem : ∀ b : Work.SSGRoute.Sha2 p k Ω K E,
          (Classical.choose (Work.SSGRoute.PT.sha2_to_H2AK p k Ω K E)) b ∈
            (Work.SSGRoute.PT.e1aChainC p k Ω K ζ hζ hζK T hT E).range) =>
      Work.SSGRoute.SSGStage.e1aLandingClause p k Ω K ζ hζ hζK T hT E hmem)

end Work.SSGRoute
