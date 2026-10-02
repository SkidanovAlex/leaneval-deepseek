import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.TubeLocalDegree
import Submission.Work.ThomBordism.tautologicalClassSensitivity
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.ThomBordism.gtdU_localDegreeExists
import Submission.Work.ThomBordism.localDegreeSpan
import Submission.Work.ThomBordism.fibreRes_gtdU_canonical
import Submission.Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen
import Submission.Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero
import Submission.Work.ThomBordism.tubeLocalDegreeGlobalSign
import Submission.Work.ThomBordism.nfGen_span
import Submission.Work.ThomBordism.nfRelCohIso
import Submission.Work.ThomBordism.thomClass_eq_smul
import Submission.Work.ThomBordism.tautologicalBundleHoriO

import Submission.Work.ThomBordism.exists_zeroSection_pairing_one
import Submission.Work.ThomBordism.fibreReading_collapseClass
import Submission.Work.ThomBordism.localDegreeGenExists
import Submission.Work.ThomBordism.nfRes_eq_of_span
import Submission.Work.ThomBordism.nfRes_span_top_of_generator
import Submission.Work.ThomBordism.gtdUWith_realThomClassOf_span_top
import Submission.Work.ThomBordism.canonicalGauss_assembly
import Submission.Work.ThomBordism.frameEval_realThomClassOf
import Submission.Work.ThomBordism.tubeChart_collapseToOnePoint_data
import Submission.Work.ThomBordism.nfRelCohIso
import Submission.Work.ThomBordism.tubeLocalDegreeGlobalSign
import Submission.Work.ThomBordism.nfGen_span
import Submission.Work.ThomBordism.coorientationRef

import Submission.Work.ThomBordism.ambientClassDefs
import Submission.Work.ThomBordism.collapseLocalisation_ambientV2
import Submission.Work.ThomBordism.tubeInvHomologyCollapse
import Submission.Work.ThomBordism.KeyLocal.tubePairingConvert
import Submission.Work.ThomBordism.KeyLocal.mixedCupLift
import Submission.Work.ThomBordism.KeyLocal.pointLocalisation
import Submission.Work.ThomBordism.KeyLocal.tubeSets
import Submission.Work.ThomBordism.KeyLocal.exists_admissible
import Submission.Work.ThomBordism.KeyLocal._assAux
import Submission.Work.ThomBordism.BSUG.tubeTanReadingO
import Submission.Work.ThomBordism.KeyLocal.tubeCompareDefs
import Submission.Work.ThomBordism.KeyLocal.chartCompare
import Submission.Work.ThomBordism.KeyLocal.tubePointRelative
import Submission.Work.ThomBordism.BSUG.tubeUnionMem

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000


/-!
# The uniformity of the branch sign of the canonical Gauss candidate

## FINAL PROOF STRUCTURE (proved)

The target is now **proved**; the chain is

* `branchSign_uniform_gauss` ← `branchSign_uniform_of_pairUniform` ← `pairUniform_of_tubeComparison`
  ← `tubeComparison` (all in this file, all sorry-free);
* `tubeComparison` ← `tubeComparison_of_pointRelative` (this file: the *final* identification of the
  tube-level point-relative comparison with the mixed cup of the bump class `π^*(relToAbs o)` and
  with `ambientStandardClass`) applied to `KeyLocal.tubePointRelative k hk (chartCompareAll k hk)`;
* `chartCompareAll` (this file, one line) := `KeyLocal.chartCompare`, the *chart-piece computation*
  (the four pieces (T1) `tubeTanReadingO`, (T2) `tubeNormReading`, (PR) `chartProductFormula`,
  (GM) `gmTubeProduct` assembled, with the `frameSign` cancellation giving the single universal sign
  `tauSign`); an independent development of the same computation is in the scratch file
  `Submission/Work/ThomBordism/_bsug/asmCup.lean`;
* the four pieces are available in two independent copies: the tree's `KeyLocal/*` and my own
  `Submission/Work/ThomBordism/BSUG/*` (both proved sorry-free);
* `admissible_pi` (this file) proves that the bump class `π^*(relToAbs o)` is admissible (the
  hypothesis of `PairUniform`).

Every declaration in this file is axiom-clean: `#print axioms
Work.ThomBordism.branchSign_uniform_gauss` = `propeq, Classical.choice, Quot.sound`.

## What the target says, and what it is equivalent to

`Work.ThomBordism.branchSign_uniform_gauss` asks for a *single* `ε = ±1` with

  `IsLocalDegreeClass C g hg hR hbox (ε • gtdU E ND G hgm)`

for **every** datum (embedding, normal data, pinned Gauss candidate, tube chart, collapse map).
By `Work.ThomBordism.isLocalDegreeClass_eq_of_generating` the local-degree class of a datum is
*unique* (the local-degree functional separates points, `Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero`),
so per datum there is a well-defined sign `δ_D = ±1` with `IsLocalDegreeClass_D (δ_D • gtdU_D)`
(the per-datum *disjunction* is `Work.ThomBordism.gtdU_localDegreeExists`), and the target is
*exactly*

> the sign `δ_D` does not depend on the datum.

Equivalently (moving both sides to the universal bundle `γ_{k,10}` along the canonical Gauss map,
which is an isomorphism on the relevant rank-one free `ℤ`-modules), with
`u_D := (relCohMap G_D)⁻¹ (U_D) ∈ H^k(γ_{k,10}, γ_{k,10}∖0)` the *preimage* of the local-degree
class of the datum,

> `u_D` does not depend on the datum.

Since `H^k(γ,γ∖0) ≅ ℤ` and both `u_D` and `τ := (tautologicalThomClass k 10).τ` are generators,
`u_D = ±τ`; the target says that this sign is *constant over the data*, i.e. that the two
normalisations of the universal Thom class — the one coming from the **collapse class** of the tube
(`U_D ⌢ c_C = z_*(V.c)`, the local-degree convention) and the one coming from `τ` — agree up to a
datum-independent sign.

## Where the reduction stands after the session of 2026-09-27 (read this before working)

**The target is equivalent to a single datum-uniform *sign*.**  All the per-datum machinery is
proved: `localDegreeGenExists`, `isLocalDegreeClass_eq_of_generating`, `gtdU_localDegreeExists`,
`fibreRes_gtdU_canonical` (the fibre reading of `gtdU` is `s • nfGen` with a *single* `s`),
`nfRes_localDegreeClass_eq_pm_nfGen` (per datum), `nfRes_gtdUWith_realThomClassOf_eq_coorFibre`
(the fibre reading of the *canonical* class is the determinate coorientation reference
`coorFibre`), `isLocalDegreeClass_iff_relCapPair`, `gtdUWith_eq_of_normalData` (so `gtdU` for a
*plane/vector-pinned* candidate depends only on `(V, E, k)`), `G_eq_frameEval`, TEL
(`sigmaTelescope_gauss`), `fibreReading_collapseClass` (= `PieceP1`, the localisation of the
collapse functional to the fibre), `exists_zeroSection_pairing_one` (= `PieceA`).

Consequently (with `Ugen` the unique local-degree class of a datum) the target is *exactly*

    ∃ ε, ∀ datum D,  ε • gtdU_D = Ugen_D   in H^k(ν, ν∖0) ≅ ℤ,

i.e. the constancy of the branch `δ_D`; and, by `nfRes`-injectivity and the two uniform fibre
readings above, it is equivalent to the constancy of the ratio
`nfRes Ugen_D / coorFibre_D`.  No per-datum lemma can decide it: `δ_D` is a *global convention*
(its only free choice is the single term `Work.Stems.sphereGenerator (8+k)` inside
`collapseRelK8`, which flips every `δ_D` at once, so the target is invariant under it but every
*pinned* value statement is not — see `NOTE_COORIBRE_SIGNED.md` §14).

**What remains is therefore one geometric statement, now formalised and delegated.**
`Submission/Work/ThomBordism/ambientClassDefs.lean` (this session) defines, with no new choice:

* `tubeInvPunct E C` — the part of the closed tube `C.U` whose tube inverse is punctured;
* `tubeInvMap E C`, `tubeInvHomology E C` — the tube inverse as a map of pairs
  `(C.U, C.U∖tubeInvPunct) → (ν, ν∖0)` and its effect on relative homology (an *isomorphism*, by
  excision: the pair is a neighbourhood pair of the zero section);
* `ambientStandardClass E C x` — the pull-back of the **determinate** standard generator
  `stdModelGen (8+k)` of `H^{k+8}(ℝ^{k+8}, ℝ^{k+8}∖0)` along the translation `y ↦ y - E.e x` on the
  tube: the "ambient" reference class based at the embedding point `E.e x`.

and the crux is

  **`Work.ThomBordism.collapseLocalisation_ambient` — PROVED this session, sorry-free and
  axiom-clean** (`Submission/Work/ThomBordism/collapseLocalisation_ambient.lean`, module
  `Submission.Work.ThomBordism.collapseLocalisation_ambient`, verified
  `#print axioms = {propext, Classical.choice, Quot.sound}`): there is `κ = ±1` such that **for every
  datum** (embedding, tube chart, pinned collapse map, box radius) and every `x`, the pairing of
  `ambientStandardClass E C x` with the tube-side avatar of `collapseRelK8` is `κ`
  (`∀δ, tubeInvHomology E C δ = collapseRelK8 … → ⟨ambientStandardClass E C x, δ⟩ = κ`).  Its proof
  (with the child's supporting modules `ambientLocalDefs`, `ambientLocalDefs2`,
  `chartModelClassDefs` — `chartModelClass`, `ambientStandardClass_eq_chartModelClass` —
  `radialRescale_homologyMap_id` — a positive fibrewise radial rescaling induces the *identity* on
  `H_n(ν,ν∖0)` — `tubeInvMap_pullback_chart`, `value_eq_chartModelClass`, and
  `collapseLocalisation_ambientV2`) is recorded in
  `Submission/Work/ThomBordism/NOTE_COLLAPSE_LOCALISATION_AMBIENT.md`; in particular the crux is
  there reduced to the equivalent ν-side form

      ∃ κ ∈ {±1}, ∀ D,  ⟨chartModelClass E C x, collapseRelK8 C g hg hR hbox⟩ = κ,

  which removes the tube-side bookkeeping.

This is *strictly weaker* than the target (it never mentions `gtdU`, `Ugen` or `IsLocalDegreeClass`)
and is the honest content of "the local class of the collapse at a zero-section point is the ambient
orientation generator, with a datum-independent sign" (the (a) of `NOTE_SESSION41_UNIVERSAL.md` §4
and `NOTE_COORIBRE_SIGNED.md` §4).

**The remaining assembly (the crux has landed; this is what is left).**  With the crux in hand the target is reached by
(i) the *frame half* — already proved, `nfRes_gtdUWith_realThomClassOf_eq_coorFibre` together with
`branchSign_gtdU_eq_pm` above; (ii) the *cap-product localisation* (naturality of `relKronH` under
the tube inverse, which identifies the pairing `⟨ambientStandardClass, tubeInvHomology δ⟩` with
`⟨x ⌣ W, c_D⟩` for the degree-`8` detecting classes `x`, plus the *model contraction* of the
`ℝ^8 × ℝ^k` splitting — TEL `sigmaTelescope_gauss` supplies the orientation of the splitting, and
the residual sign is the universal Mpun/Koszul constant `(-1)^{k(k-1)/2}` read off from the model
classes `Work.Thom.Mpun` / `stdModelGen`); (iii) `nfRes`-injectivity (`relH_zeroSection_localisation_injective`)
and the uniqueness of the local-degree class, then `branchSign_uniform_of_sharp_signed` above.

**The bridge from the crux to the target.**  Let `cCan_D` be the class dual to `chartModelClass`
under the (surjective, hence bijective) pairing `⟨·, ·⟩ : H^{k+8}(ν,ν∖0) × H_{k+8}(ν,ν∖0) → ℤ`.  The
crux says `⟨chartModelClass, c_D⟩ = κ`, hence `c_D = κ • cCan_D`.  So the target follows as soon as
one has the *cup* form of the local degree for the determinate canonical class, i.e. a uniform `ε`
with

    ∀ D ∀ x,  x ⌣ gtdUWith E ND G hgm Ucan
                = ε * ⟨zs^*x, V.c⟩ • chartModelClass E C x hcont

(`ε κ` is then the target's `ε`).  Its content is TEL + the frame half: `gtdUWith Ucan` is the
coorientation Thom class (its fibre reading is `coorFibre`, PROVED) and `chartModelClass` is the
ambient class read through the (ambient-identity) chart, so the residual sign is the universal
Mpun/Koszul constant.  The two general inputs still to formalise are the *localisation of
`relKronH`* to a point pair and the injectivity of the localisation at a point (see
`NOTE_COLLAPSE_LOCALISATION_AMBIENT.md` §5).

**The `ambientUniform`/`ambientFibreLink` route (as it stands).**  `Work.ThomBordism.ambientUniform k hk`
(axiom-clean, PROVED — the (CLA) uniformity of the *ambient* local degree `⟨ambientValueClass E C x,
collapseRelK8⟩`) is available, and `Work.ThomBordism.localDegree_universalThomClass_of_ambient`
(PROVED, axiom-clean) turns `AmbientUniform k` plus the *link* into `localDegree_universalThomClass`,
which is equivalent to this file's target.  **Watch out:** the current `Work.ThomBordism.ambientFibreLink`
takes `Work.ThomBordism.nfRes_uniform_coorFibre` as an input, and that statement *is* the datum-uniform
fibre-restriction statement UF2, i.e. it is already equivalent to the target (`#print axioms` shows
`sorryAx` for `ambientFibreLink` through `nfRes_uniform_coorFibre`); likewise
`Work.ThomBordism.keyLocalProof` is a `sorry`.  So the genuinely remaining bridge is the *ambient
degree → fibre reading* link, in the non-circular form: the frame half
(`nfRes_gtdUWith_realThomClassOf_eq_coorFibre`, PROVED) plus the observation that
`coorFibre` *is* the fibre reading of the ambient class `ambientValueClass` — i.e. the
*cap-product localisation* statement `loc(U ⌢ c)(0_x) = nfRes U ⌢ loc(c)(0_x)` at the zero-section
points, which is what makes the crux usable for the fibre reading.

**Already available (do not re-prove):** `Work.ThomBordism.collapseRelK8_indep_R` and
`Work.ThomBordism.collapseRelK8_indep_tube` — the collapse class `collapseRelK8` does **not** depend
on the tube chart or on the cube radius (only on `E`), so the tube-data axis of the uniformity
question is closed.

## The two ingredients this file isolates

* **(τ-responsibility, proved here)** `branchSign_gtdU_eq_pm`: for *any* Thom class `U` of
  `γ_{k,10}`, the ground classes `gtdU` (used by the target) and `gtdUWith U` differ by a *single*
  sign over *all* data.  This is `Work.ThomBordism.thomClass_eq_smul` (the base `OG k 10` is path
  connected) plus the `ℤ`-linearity of `gtdUWith` in the Thom class.  Consequence: the target is
  *equivalent* to the same uniformity statement with the opaque class replaced by any fixed class,
  and in particular it is invariant under `τ ↦ -τ`.
* **(uniformity, proved here as a reduction)** `branchSign_uniform_gauss_of_sharp`: the target
  *follows* from the sharp statement "`IsLocalDegreeClass_D (gtdUWith U D)` for every `D`" for a
  single Thom class `U` of `γ_{k,10}`.

## State of the reduction (the sharp statement, and where it stands)

The sharp statement is the classical content: the Thom class of the normal bundle, in the
convention of the explicit/canonical construction, caps with the collapse class to the zero-section
push-forward of the fundamental class.  That is the workspace's named geometric gap
(`Work.Tubular.TubeLocalDegree`) and it is *strictly stronger* than the target, which only asks for
the *constancy* of the sign.

The two ingredients are now available:

* `Work.Thom.realThomClassOf` (`Submission/Work/Thom/realThomClassOf_natural.lean`, PROVED): the
  *canonical, natural* Thom class of an oriented real bundle with finite cover.  This removes the
  opaque `Classical.choice` of `thomClass_of_oriented_fintype` — the obstruction recorded by
  `Work.ThomBordism.tautologicalClassSensitivity`.  With a *definite* class the sharp statement is a
  meaningful, definite claim;
* `Work.ThomBordism.canonicalGauss_isLocalDegreeClass` (dispatched): the sharp statement for the
  canonical class of the tautological bundle.

`Work.ThomBordism.branchSign_uniform_of_sharp` (PROVED below) turns the second of these into the
target in one step, via the τ-responsibility `Work.ThomBordism.branchSign_gtdU_eq_pm` (PROVED
below).  The one-line assembly is recorded above the `sorry` in the proof below; it reads

  `branchSign_uniform_of_sharp k hk (realThomClassOf hk (tautologicalBundle k 10) horiO)
     (canonicalGauss_isLocalDegreeClass k hk horiO)`,

with `horiO` the (available) positivity `Grassmann.det_coordChangeO_pos` of the tautological
bundle's transition determinants.
## Where the reduction stands after this session (read `NOTE_CANONICAL_SHARP.md`)

* `Submission/Work/ThomBordism/canonicalGauss_assembly.lean` (PROVED, sorry-free) reduces the
  *sharp* statement for the canonical class to three determinate inputs: `(A1-coor)` — the fibre
  reading of every local-degree class is the geometric reference `coorFibre`
  (`Work.ThomBordism.coorientationRef`) — the frame half `(A2-coor)` (proved from
  `canonicalThomClass_frameEval`), and the generator property of the canonical candidate
  (`gtdUWith_realThomClassOf_span_top`, PROVED).  `nfRes_eq_of_span` (PROVED) supplies the final
  bookkeeping.
* The *pinned* sharp statements are **undetermined**: two independent provers (`H4-L2662`/§8 for the
  unsigned form, `H4-L2673` for the signed form) showed that the orientation of the collapse class
  `Work.Tubular.collapseRelK8` — the reference of `IsLocalDegreeClass` — is fixed by a
  `Classical.choice` inside `Work.Stems.sphereGenerator`, so no statement *asserting a value* for the
  comparison of the canonical class with it is derivable (both `+` and `-` are consistent with the
  recorded API).  The same applies to the signed repair
  `Work.ThomBordism.coorFibre_localDegreeClass_signed` (dispatched, `H4-L2675`).
* **What is *not* affected is the target itself**: it is sign-blind.  By
  `branchSign_gtdU_eq_pm` (PROVED, below) the ground class `gtdU` of the target differs from the
  canonical ground class by *one* sign for *all* data, so the target is *equivalent* to the
  uniformity of the sign for the canonical class — and, more sharply, to the statement that the
  ratio of the (choice-dependent) collapse orientation to the (determinate) canonical class is
  *independent of the datum*.  The remaining work is therefore the localisation chapter in
  *choice-tracking* form: the datum-dependence of `collapseRelK8` must be exhibited and shown to
  enter the comparison only through the (global, datum-independent) choice of the sphere generator
  `Work.Stems.sphereGenerator (8+k)`; the geometric factor is the σ/TEL identification, which is
  datum-independent.  The precise obstructions, and the two refuted pinned forms, are recorded in
  `Submission/Work/ThomBordism/NOTE_CANONICAL_SHARP.md` §8 and
  `Submission/Work/ThomBordism/NOTE_COORFIBRE_SIGNED.md` §14.

-/


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.ThomBordism

open Work.ThomBordism.Grassmann

noncomputable section

/-- **`gtdUWith` depends on the Thom class only through its `τ` field.** -/
theorem gtdUWith_eq_of_tau_eq {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
    {U U' : Work.Thom.ThomClass (tautologicalBundle k 10) k} (h : U.τ = U'.τ) :
    gtdUWith E ND G hgm U = gtdUWith E ND G hgm U' := by
  unfold gtdUWith
  rw [h]

/-- **`gtdUWith` is `ℤ`-linear in the Thom class, in the `neg` form** (the only form in which the
workspace's `ℤ`-scalar multiplications on (co)homology can be used safely). -/
theorem gtdUWith_eq_neg_of_tau_eq_neg {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
    {U U' : Work.Thom.ThomClass (tautologicalBundle k 10) k} (h : U.τ = -U'.τ) :
    gtdUWith E ND G hgm U = - gtdUWith E ND G hgm U' := by
  unfold gtdUWith
  rw [h, map_neg, map_neg]

/-- **The τ-responsibility of the branch sign.**  For *any* Thom class `U` of the tautological
oriented bundle, the ground class `gtdU` of the target and the ground class `gtdUWith U` differ by
one sign, the same for every datum: this is `Work.ThomBordism.thomClass_eq_smul` (a single `s = ±1`
with `τ = s • U.τ`) together with `gtdUWith_eq_of_tau_eq`/`gtdUWith_eq_neg_of_tau_eq_neg`.

In particular the target's `∃ε` is invariant under replacing `τ` by `-τ`, and the target is
equivalent to the same uniformity statement for any fixed Thom class of `γ_{k,10}`. -/
theorem branchSign_gtdU_eq_pm (k : ℕ) (hk : 1 ≤ k)
    (U : Work.Thom.ThomClass (tautologicalBundle k 10) k) :
    (∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10)),
        gtdU E ND G hgm = gtdUWith E ND G hgm U) ∨
    (∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10)),
        gtdU E ND G hgm = - gtdUWith E ND G hgm U) := by
  obtain ⟨s, hs, hτ⟩ := thomClass_eq_smul k (tautologicalThomClass k 10) U
  rcases hs with h | h
  · left
    intro V _ E ND G hgm
    rw [gtdU_eq_gtdUWith]
    exact gtdUWith_eq_of_tau_eq E ND G hgm (by rw [hτ, h, one_smul])
  · right
    intro V _ E ND G hgm
    rw [gtdU_eq_gtdUWith]
    exact gtdUWith_eq_neg_of_tau_eq_neg E ND G hgm (by rw [hτ, h, neg_one_zsmul])

/-- **The reduction of the target to the sharp (per-datum, sign-free) statement for a single Thom
class of the tautological bundle.**

If for one Thom class `U` of `γ_{k,10}` the ground class `gtdUWith U` *is* a local-degree class in
every datum, then the target holds: combine `branchSign_gtdU_eq_pm` (which says that
`gtdU = ± gtdUWith U` with one sign for all data) with the `ℤ`-linearity of `IsLocalDegreeClass` in
its class argument. -/
theorem branchSign_uniform_of_sharp (k : ℕ) (hk : 1 ≤ k)
    (U : Work.Thom.ThomClass (tautologicalBundle k 10) k)
    (hsharp : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
        (hbp : ∀ p, (tautologicalBundle k 10).proj (G p)
          = padGaussFun E ND p.1)
        (hvec : ∀ p, evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
        {ε' : ℝ} (C : Work.Tubular.TubeChart E ε') (q : Work.Tubular.NormalSphSub E ε')
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C.inv y))),
        Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox (gtdUWith E ND G hgm U)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
      (hbp : ∀ p, (tautologicalBundle k 10).proj (G p)
        = padGaussFun E ND p.1)
      (hvec : ∀ p, evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε' : ℝ} (C : Work.Tubular.TubeChart E ε') (q : Work.Tubular.NormalSphSub E ε')
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (ε • gtdU E ND G hgm) := by
  rcases branchSign_gtdU_eq_pm k hk U with hpos | hneg
  · -- `gtdU = gtdUWith U`: the sharp statement is the target with `ε = 1`
    refine ⟨1, Or.inl rfl, ?_⟩
    intro V _ E ND G hgm hbp hvec ε' C q hU R hR hbox g hg hg2
    rw [one_smul, hpos E ND G hgm]
    exact hsharp E ND G hgm hbp hvec C q hU hR hbox g hg hg2
  · -- `gtdU = - gtdUWith U`: the sharp statement is the target with `ε = -1`
    refine ⟨-1, Or.inr rfl, ?_⟩
    intro V _ E ND G hgm hbp hvec ε' C q hU R hR hbox g hg hg2
    have hstep : ((-1 : ℤ) • (- gtdUWith E ND G hgm U)) = gtdUWith E ND G hgm U := by
      rw [neg_one_zsmul]
      exact neg_neg _
    rw [hneg E ND G hgm, hstep]
    exact hsharp E ND G hgm hbp hvec C q hU hR hbox g hg hg2

/-- **The signed form of the reduction.**  If `c • gtdUWith U` is a local-degree class in every
datum for a unit `c = ±1`, then the target holds: reduce to the unsigned statement for `U` (if
`c = 1`) or for `ThomClass.neg U` (if `c = -1`), using `gtdUWith_neg` and `neg_one_zsmul`. -/
theorem branchSign_uniform_of_sharp_signed (k : ℕ) (hk : 1 ≤ k)
    (U : Work.Thom.ThomClass (tautologicalBundle k 10) k) (c : ℤ)
    (hc : c = 1 ∨ c = -1)
    (hsharp : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
        (hbp : ∀ p, (tautologicalBundle k 10).proj (G p)
          = padGaussFun E ND p.1)
        (hvec : ∀ p, evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
        {ε' : ℝ} (C : Work.Tubular.TubeChart E ε') (q : Work.Tubular.NormalSphSub E ε')
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C.inv y))),
        Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox (c • gtdUWith E ND G hgm U)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
      (hbp : ∀ p, (tautologicalBundle k 10).proj (G p)
        = padGaussFun E ND p.1)
      (hvec : ∀ p, evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε' : ℝ} (C : Work.Tubular.TubeChart E ε') (q : Work.Tubular.NormalSphSub E ε')
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (ε • gtdU E ND G hgm) := by
  classical
  rcases hc with h | h
  · subst h
    refine branchSign_uniform_of_sharp k hk U ?_
    intro V _ E ND G hgm hbp hvec ε' C q hU R hR hbox g hg hg2
    simpa only [one_smul] using hsharp E ND G hgm hbp hvec C q hU hR hbox g hg hg2
  · subst h
    refine branchSign_uniform_of_sharp k hk (ThomClass.neg U) ?_
    intro V _ E ND G hgm hbp hvec ε' C q hU R hR hbox g hg hg2
    rw [gtdUWith_neg, ← neg_one_zsmul]
    exact hsharp E ND G hgm hbp hvec C q hU hR hbox g hg hg2





/-! ## The algebraic core: the target from the datum-uniform pairing of `w ⌣ Ucan` with the collapse class

The geometric chapter (the tube comparison of `_kl/NOTE_SESSION9.md`, pieces (T1), (T2), (PR), (GM))
produces, for each datum and each admissible degree-`8` class `w` of the normal total space, the
identity

  `⟨w ⌣ Ucan, collapseRelK8⟩ = s`   (`s = ±1` a *single* sign for all data),

where `Ucan` is the *canonical* (chart-constructed) Thom class of the tautological oriented bundle
pulled back along the Gauss map.  The theorems below are the *algebraic* part of the last mile: they
turn that datum-uniform pairing into the requested uniformity of the branch sign.

The chain (all inputs proved, below this module):

* `nfRes Ucan = coorFibre` (the frame half, `canonicalGauss_assembly`);
* the localisation `⟨nfRes U, z⟩ = ⟨w ⌣ U, c⟩` for a suitable generator `z` of the fibre pair
  (`fibreReading_collapseClass`);
* `localDegreeGenExists`: there is a *generating* local-degree class `Ugen` with
  `⟨nfRes Ugen, z⟩ = 1`;
* `nfRes_eq_of_span`: two generators with equal fibre reading are equal.

So the fibre reading of `Ucan` at `z` is the *same* for every datum, whence `Ucan = ± Ugen` with a
single sign over all data, i.e. `IsLocalDegreeClass Ucan` or `IsLocalDegreeClass (-Ucan)` — one
branch for all data; `branchSign_gtdU_eq_pm` (above) then converts `gtdU` into `± gtdUWith Ucan`
with one sign for all data.

**Import structure (important).**  This module is *below* `localDegree_localisation.lean`, which
imports `fibreRes_localDegreeClass_eq_nfGen_uniform.lean`, which imports *this* file.  Hence the
`KeyLocal` chapter (`keyLocal.lean`, `keyLocalProof.lean`, `coorFibre_fibreGenerator.lean`) is
*above* this module and **cannot be imported here**: the requested theorem must be proved below that
chapter.  The hypothesis `PairUniform` below is therefore the statement whose proof closes this file;
over the tree it is *equivalent* to `KeyLocal` (both are the cross-datum uniformity of the branch
sign), and its proof is the tube comparison assembled from the (now all proved) `KeyLocal.*` pieces
`tubeTanReading` (T1), `tubeNormReading` (T2), `tcmRelCup_stdModelGen` (PR), `germPullbackEucAt`
with `tubeCoordsFDeriv`/`gmSign` (GM). -/

/-- The canonical (chart-constructed) Thom class of the tautological oriented rank-`k` bundle over
`OG k 10`; the Gauss map pulls it back in the statements below. -/
noncomputable abbrev UcanClass (k : ℕ) (hk : 1 ≤ k) :
    Work.Thom.ThomClass (tautologicalBundle k 10) k :=
  Work.Thom.realThomClassOf hk (tautologicalBundle k 10) (tautologicalBundle_horiO k)

/-- **The datum-uniform pairing hypothesis.**  There is a single sign `s = ±1` such that in every
datum there is an *admissible* degree-`8` class `w` of the normal total space (`⟨z^*w, V.c⟩ = 1`)
whose pairing `w ⌣ Ucan` with the collapse class is `s`.  This is the *weak* (witness) form; it is
what the tube comparison `TubeComparison` below produces, and it is what the algebraic core needs. -/
def PairUniform (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
      (hbp : ∀ p, (tautologicalBundle k 10).proj (G p) = padGaussFun E ND p.1)
      (hvec : ∀ p, evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
      ∃ w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
        Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1 ∧
        Work.Tubular.relKronH (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) (k + 8)
            ((Nat.add_comm 8 k) ▸ (Work.Cohomology.mixedCup
              (TopCat.of (Work.Tubular.NormalTotal E))
              (Work.Tubular.normalNonzero E) 8 k w
              (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))))
            (Work.Tubular.collapseRelK8 C g hg hR hbox) = s

/-- Transport of a relative class along an equality of the relative sets. -/
theorem relCohMap_set_cast {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A A' : Set X} (h : A = A') (f : C(X, Y)) (B : Set Y)
    (hf : ∀ x ∈ A, f x ∈ B) (hf' : ∀ x ∈ A', f x ∈ B) (R : Type) [CommRing R] (n : ℕ)
    (x : Work.Thom.RelCoh R n Y B) :
    (Work.Thom.relCohMap f A B hf R n).hom x
      = h ▸ ((Work.Thom.relCohMap f A' B hf' R n).hom x) := by
  subst h
  exact congrArg (fun φ => φ.hom x) (Work.Thom.relCohMap_hcongrA f A B hf hf' R n)

/-- A cast of the relative set commutes with the scalar action. -/
theorem relCoh_set_cast_smul {X : Type} [TopologicalSpace X] {A A' : Set X} {n : ℕ}
    (h : A = A') (c : ℤ) (x : Work.Thom.RelCoh ℤ n X A) :
    h ▸ (c • x) = c • (h ▸ x) := by
  cases h
  rfl

/-- **The point-relative set of the chart piece**: the union of the punctured foot set and the
punctured zero-section set is the complement of the single point `tubeChartPt` of the tube over
`x`.  (The two inclusions are `KeyLocal.mem_of_ne_tubeChartPt` and the delegated lemma
`Work.ThomBordism.BSUG.tubeUnionMem`.) -/
theorem tubeFootPunct_union_tubeBaseSetPunct {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) (x : V.pt)
    (hx : x ∈ ND.D.baseSet i) :
    Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
        ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i
      = {y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i) |
          (y : Work.Tubular.Euc (8 + k)) ≠ E.e x} := by
  ext y
  exact ⟨fun hy => Work.ThomBordism.KeyLocal.mem_of_ne_tubeChartPt E C ND i x hx hy,
    fun hy => Work.ThomBordism.BSUG.tubeUnionMem E C ND i x hx hy⟩

/-- **The class-level tube comparison** (the geometric input produced by the tube chapter, pieces
(T1), (T2), (PR), (GM) of `_kl/NOTE_SESSION9.md`): there is a single sign `s = ±1` such that in every
datum there are an admissible class `w` (with `⟨(zeroSection)^* w, V.c⟩ = 1`) and a point `x` for
which the pullback of the mixed cup `w ⌣ Ucan` along the tube inverse is `s` times the ambient
standard class of the tube at `x`.

This is *strictly stronger* than `PairUniform` below (it is a class-level identity), and it is what
the tube chapter produces; the reduction `TubeComparison → PairUniform` is proved here. -/
def TubeComparison (k : ℕ) (hk : 1 ≤ k) : Prop :=
  ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
      (hbp : ∀ p, (tautologicalBundle k 10).proj (G p) = padGaussFun E ND p.1)
      (hvec : ∀ p, evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
      ∃ x : V.pt, ∃ w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)),
        Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
            ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom w) V.c = 1 ∧
        (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
            (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
            (fun y hy => hy) ℤ (8 + k)).hom
          (Work.Cohomology.mixedCup
            (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) 8 k w
            (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk)))
        = s • Work.ThomBordism.ambientStandardClass E C x

/-- **`TubeComparison` implies `PairUniform`**: pair the class-level identity with the tube avatar
`δ` of the collapse class, using the naturality of the Kronecker pairing along the tube inverse
(`KeyLocal.tubePairingConvert`) and the uniform ambient pairing
(`collapseLocalisation_ambientV2`). -/
theorem pairUniform_of_tubeComparison (k : ℕ) (hk : 1 ≤ k) (H : TubeComparison k hk) :
    PairUniform k hk := by
  classical
  obtain ⟨s, hs, H'⟩ := H
  obtain ⟨κ, hκ, hκpair⟩ := Work.ThomBordism.collapseLocalisation_ambientV2 k hk
  refine ⟨s * κ, ?_, ?_⟩
  · rcases hs with h | h <;> rcases hκ with h' | h' <;> rw [h, h'] <;> norm_num
  · intro V _inst E ND G hgm hbp hvec ε C q hU R hR hbox g hg hg2
    obtain ⟨x, w, hw, hcmp⟩ := H' E ND G hgm hbp hvec C q hU hR hbox g hg hg2
    refine ⟨w, hw, ?_⟩
    obtain ⟨δ, hδ⟩ := Work.ThomBordism.tubeInvHomologyCollapse (V := V) E C g hg hg2 hR hbox
    -- the tube avatar of the mixed cup, paired with the tube avatar of the collapse class
    have hconv := Work.ThomBordism.KeyLocal.tubePairingConvert (V := V) E C g hg hR hbox δ hδ
      (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E) 8 k w
        (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk)))
    -- the class-level identity, cast to degree `k + 8` and paired with `δ`
    have hp0 := relCohCastGen_congr (Work.ThomBordism.tubeInvPunct E C) (Nat.add_comm 8 k) hcmp
    have hp1 := congrArg (fun Y => Work.Tubular.relKronH (TopCat.of ↥C.U)
      (Work.ThomBordism.tubeInvPunct E C) (k + 8) Y δ) hp0
    have hamb : Work.Tubular.relKronH (TopCat.of ↥C.U) (Work.ThomBordism.tubeInvPunct E C)
        (k + 8) (relCohCastGen (Work.ThomBordism.tubeInvPunct E C) (Nat.add_comm 8 k)
          (Work.ThomBordism.ambientStandardClass E C x)) δ = κ :=
      hκpair E C g hg hg2 hR hbox x δ hδ
    rw [← relCohCastGen_smul (Work.ThomBordism.tubeInvPunct E C) (Nat.add_comm 8 k) s
      (Work.ThomBordism.ambientStandardClass E C x)] at hp1
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul, hamb] at hp1
    rw [← hconv]
    exact hp1

/-- **The admissibility of the bump class**: the class `π^* (relToAbs o)` of the normal total space
pairs to `1` against the fundamental class of `V` whenever `o` does (so it is *the* admissible class
of the last mile). -/
theorem admissible_pi {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    (o : Work.Thom.RelCoh ℤ 8 V.pt (Work.ThomBordism.FrameSigns.punct V x))
    (ho : Work.Tubular.relKronH (TopCat.of V.pt) (Work.ThomBordism.FrameSigns.punct V x) 8 o
        (Work.Orient.locClass (TopCat.of V.pt) 8 V.c x) = 1) :
    Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of V.pt)) 8
        ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom
          ((Work.Thom.CohMap
            (⟨Work.Tubular.NormalTotal.proj,
              Work.Tubular.NormalTotal.continuous_proj E⟩ :
                C(Work.Tubular.NormalTotal E, V.pt)) ℤ 8).hom
            ((Work.Thom.relToAbs ℤ (Work.ThomBordism.FrameSigns.punct V x) 8).hom o)))
        V.c = 1 := by
  have hcomp : (⟨Work.Tubular.NormalTotal.proj,
        Work.Tubular.NormalTotal.continuous_proj E⟩ :
          C(Work.Tubular.NormalTotal E, V.pt)).comp (Work.Tubular.zeroSectionNormal E)
      = ContinuousMap.id V.pt := by
    ext y
    exact Work.Tubular.zeroSectionNormal_proj E y
  have hcancel : CategoryTheory.CategoryStruct.comp (Work.Thom.CohMap
        (⟨Work.Tubular.NormalTotal.proj,
          Work.Tubular.NormalTotal.continuous_proj E⟩ :
            C(Work.Tubular.NormalTotal E, V.pt)) ℤ 8)
        (Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8)
      = CategoryTheory.CategoryStruct.id _ := by
    rw [← Work.Thom.CohMap_comp (Work.Tubular.zeroSectionNormal E)
        (⟨Work.Tubular.NormalTotal.proj,
          Work.Tubular.NormalTotal.continuous_proj E⟩ :
            C(Work.Tubular.NormalTotal E, V.pt)) ℤ 8, hcomp, Work.Thom.CohMap_id]
  rw [show ((Work.Thom.CohMap (Work.Tubular.zeroSectionNormal E) ℤ 8).hom
      ((Work.Thom.CohMap (⟨Work.Tubular.NormalTotal.proj,
          Work.Tubular.NormalTotal.continuous_proj E⟩ :
            C(Work.Tubular.NormalTotal E, V.pt)) ℤ 8).hom
        ((Work.Thom.relToAbs ℤ (Work.ThomBordism.FrameSigns.punct V x) 8).hom o)))
      = (Work.Thom.relToAbs ℤ (Work.ThomBordism.FrameSigns.punct V x) 8).hom o from by
    rw [← ModuleCat.comp_apply, hcancel]
    rfl]
  rw [← Work.Tubular.relKronH_relToAbs_apply (Work.ThomBordism.FrameSigns.punct V x) 8 o V.c]
  exact ho

/-- **The chart-level comparison**, produced by the geometry of the tube (the four pieces
(T1), (T2), (PR), (GM) assembled in `KeyLocal.chartCompare`). -/
theorem chartCompareAll (k : ℕ) (hk : 1 ≤ k) : Work.ThomBordism.KeyLocal.ChartCompareAll k hk :=
  fun {V : Work.ThomBordism.Man8} [inst : ConnectedSpace V.pt] E ND G hgm hbp hvec ε C i x hx o ho =>
    Work.ThomBordism.KeyLocal.chartCompare (V := V) hk E ND G hgm hbp hvec C i x hx o ho

/-- **`TubeComparison` from the tube-level point-relative comparison.**

The point-relative comparison of `KeyLocal.tubePointRelative` is restricted to the zero-section
relative pair `(C.U, tubeInvPunct)`; both sides are then identified with the mixed cup of the bump
class and with the ambient standard class. -/
theorem tubeComparison_of_pointRelative (k : ℕ) (hk : 1 ≤ k)
    (H : Work.ThomBordism.KeyLocal.TubePointRelativeAll k hk) : TubeComparison k hk := by
  classical
  refine ⟨KeyLocal.tauSign, KeyLocal.tauSign_eq_one_or_neg_one, ?_⟩
  intro V _inst E ND G hgm hbp hvec ε C q hU R hR hbox g hg hg2
  obtain ⟨x : V.pt⟩ := (inferInstance : Nonempty V.pt)
  obtain ⟨o, ho⟩ := Work.ThomBordism.KeyLocal.exists_admissible x
  set w : Work.Thom.Coh ℤ 8 (TopCat.of (Work.Tubular.NormalTotal E)) :=
    (Work.Thom.CohMap
      (⟨Work.Tubular.NormalTotal.proj, Work.Tubular.NormalTotal.continuous_proj E⟩ :
        C(Work.Tubular.NormalTotal E, V.pt)) ℤ 8).hom
      ((Work.Thom.relToAbs ℤ (Work.ThomBordism.FrameSigns.punct V x) 8).hom o) with hw
  set Tp : Set ↥C.U :=
    Work.ThomBordism.KeyLocal.tubeFootPunctCU E C x ∪ Work.ThomBordism.tubeInvPunct E C with hTp
  refine ⟨x, w, ?_, ?_⟩
  · rw [hw]
    exact admissible_pi E x o ho
  · have hpt := H (V := V) E ND G hgm hbp hvec C x o ho
    -- (i) the restriction of the point-relative identity to the zero-section pair
    have hrestrict := congrArg (fun z => (Work.Thom.relCohMap (ContinuousMap.id ↥C.U)
      (Work.ThomBordism.tubeInvPunct E C) Tp (fun y hy => Or.inr hy) ℤ (8 + k)).hom z) hpt
    rw [map_zsmul] at hrestrict
    -- (ii) the left-hand side
    have hL : (Work.Thom.relCohMap (ContinuousMap.id ↥C.U) (Work.ThomBordism.tubeInvPunct E C)
          Tp (fun y hy => Or.inr hy) ℤ (8 + k)).hom
        ((Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C) Tp
          (Work.ThomBordism.KeyLocal.normalPunctAt E x ∪ Work.Tubular.normalNonzero E)
          (fun y hy => hy) ℤ (8 + k)).hom
          (Work.Whitney.relRelCupOpen (Work.ThomBordism.KeyLocal.normalPunctAt E x)
            (Work.Tubular.normalNonzero E)
            (Work.ThomBordism.KeyLocal.isOpen_normalPunctAt E x)
            (Work.Tubular.isOpen_normalNonzero E) 8 k
            ((Work.Thom.relCohMap
              (⟨Work.Tubular.NormalTotal.proj, Work.Tubular.NormalTotal.continuous_proj E⟩ :
                C(Work.Tubular.NormalTotal E, V.pt))
              (Work.ThomBordism.KeyLocal.normalPunctAt E x) (FrameSigns.punct V x)
              (fun p hp => hp) ℤ 8).hom o)
            (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))))
        = (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C)
            (Work.ThomBordism.tubeInvPunct E C) (Work.Tubular.normalNonzero E)
            (fun y hy => hy) ℤ (8 + k)).hom
          (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) 8 k w
            (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))) := by
      have hA : (Work.Cohomology.mixedCup (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E) 8 k w
            (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk)))
          = (Work.Thom.relCohMap (ContinuousMap.id (Work.Tubular.NormalTotal E))
              (Work.Tubular.normalNonzero E)
              (Work.ThomBordism.KeyLocal.normalPunctAt E x ∪ Work.Tubular.normalNonzero E)
              (fun z hz => Or.inr hz) ℤ (8 + k)).hom
            (Work.Whitney.relRelCupOpen (Work.ThomBordism.KeyLocal.normalPunctAt E x)
              (Work.Tubular.normalNonzero E)
              (Work.ThomBordism.KeyLocal.isOpen_normalPunctAt E x)
              (Work.Tubular.isOpen_normalNonzero E) 8 k
              ((Work.Thom.relCohMap
                (⟨Work.Tubular.NormalTotal.proj, Work.Tubular.NormalTotal.continuous_proj E⟩ :
                  C(Work.Tubular.NormalTotal E, V.pt))
                (Work.ThomBordism.KeyLocal.normalPunctAt E x) (FrameSigns.punct V x)
                (fun p hp => hp) ℤ 8).hom o)
              (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))) := by
        rw [hw]
        exact (Work.ThomBordism.KeyLocal.mixedCup_restrict_relRelCup (V := V) E x o
          (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))).symm
      rw [hA]
      rw [Work.Thom.relCohMap_compA_apply (A := Work.ThomBordism.tubeInvPunct E C) (B := Tp)
        (C := Work.ThomBordism.KeyLocal.normalPunctAt E x ∪ Work.Tubular.normalNonzero E)
        (f := ContinuousMap.id ↥C.U) (g := Work.ThomBordism.tubeInvMap E C)
        (fun y hy => Or.inr hy) (fun y hy => hy) (fun y hy => Or.inr hy) ℤ (8 + k) _]
      rw [Work.Thom.relCohMap_compA_apply (A := Work.ThomBordism.tubeInvPunct E C)
        (B := Work.Tubular.normalNonzero E)
        (C := Work.ThomBordism.KeyLocal.normalPunctAt E x ∪ Work.Tubular.normalNonzero E)
        (f := Work.ThomBordism.tubeInvMap E C)
        (g := ContinuousMap.id (Work.Tubular.NormalTotal E))
        (fun y hy => hy) (fun z hz => Or.inr hz) (fun y hy => Or.inr hy) ℤ (8 + k) _]
      rw [Work.Thom.relCohMap_congrA (A := Work.ThomBordism.tubeInvPunct E C)
        (B := Work.ThomBordism.KeyLocal.normalPunctAt E x ∪ Work.Tubular.normalNonzero E)
        (h := ContinuousMap.comp_id (f := Work.ThomBordism.tubeInvMap E C))
        (hf := fun y hy => Or.inr hy) (hf' := fun y hy => Or.inr hy) ℤ (8 + k)]
      rw [Work.Thom.relCohMap_congrA (A := Work.ThomBordism.tubeInvPunct E C)
        (B := Work.ThomBordism.KeyLocal.normalPunctAt E x ∪ Work.Tubular.normalNonzero E)
        (h := ContinuousMap.id_comp (f := Work.ThomBordism.tubeInvMap E C))
        (hf := fun y hy => Or.inr hy) (hf' := fun y hy => Or.inr hy) ℤ (8 + k)]
    -- (iii) the right-hand side
    have hR : (Work.Thom.relCohMap (ContinuousMap.id ↥C.U) (Work.ThomBordism.tubeInvPunct E C)
          Tp (fun y hy => Or.inr hy) ℤ (8 + k)).hom
        ((Work.Thom.relCohMap
          (⟨fun y : ↥C.U => (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
            C(↥C.U, Work.Tubular.Euc (8 + k))) Tp ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
          (Work.ThomBordism.KeyLocal.tubePoint_neCU E C x) ℤ (8 + k)).hom
          (Work.ThomBordism.stdModelGen (8 + k)))
        = Work.ThomBordism.ambientStandardClass E C x := by
      have hmem : ∀ y ∈ Work.ThomBordism.tubeInvPunct E C,
          (ContinuousMap.id ↥C.U) y ∈ Tp := fun y hy => Or.inr hy
      have hmemT : ∀ y ∈ Work.ThomBordism.tubeInvPunct E C,
          (⟨fun y : ↥C.U => (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
            C(↥C.U, Work.Tubular.Euc (8 + k))) ((ContinuousMap.id ↥C.U) y)
            ∈ ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := by
        intro y hy
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h0
        exact Work.ThomBordism.KeyLocal.tubePoint_notMem_CU E C x (by
          have hyU : y = (⟨E.e x, C.zero_mem_U x⟩ : ↥C.U) := Subtype.ext (sub_eq_zero.mp h0)
          exact Or.inr (by rwa [hyU] at hy))
      rw [Work.Thom.relCohMap_compA_apply (A := Work.ThomBordism.tubeInvPunct E C) (B := Tp)
        (C := ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))) (f := ContinuousMap.id ↥C.U)
        (g := (⟨fun y : ↥C.U => (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
          C(↥C.U, Work.Tubular.Euc (8 + k))))
        hmem (Work.ThomBordism.KeyLocal.tubePoint_neCU E C x) hmemT ℤ (8 + k)
        (Work.ThomBordism.stdModelGen (8 + k))]
      rw [Work.Thom.relCohMap_congrA (A := Work.ThomBordism.tubeInvPunct E C)
        (B := ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))))
        (h := ContinuousMap.comp_id (f := (⟨fun y : ↥C.U =>
            (y : Work.Tubular.Euc (8 + k)) - E.e x, by fun_prop⟩ :
          C(↥C.U, Work.Tubular.Euc (8 + k)))))
        (hf := _) (hf' := _) ℤ (8 + k)]
      rfl
    rw [hL, hR] at hrestrict
    exact hrestrict

/-- **`TubeComparison` holds**: the chart-level geometry of the tube (`KeyLocal.chartCompare`
through `chartCompareAll`), the pair-mismatch step (`KeyLocal.tubePointRelative`) and the final
identification with the mixed cup of the bump class and the ambient standard class
(`tubeComparison_of_pointRelative`). -/
theorem tubeComparison (k : ℕ) (hk : 1 ≤ k) : TubeComparison k hk :=
  tubeComparison_of_pointRelative k hk
    (Work.ThomBordism.KeyLocal.tubePointRelative k hk (chartCompareAll k hk))

/-- **The per-datum core, smul-free form**: under the pairing hypothesis, either `Ucan` is a
local-degree class in *every* datum, or `-Ucan` is (one branch for all data, decided by `s`). -/
theorem isLocalDegreeClass_pm_ucan_of_pairUniform (k : ℕ) (hk : 1 ≤ k)
    (hpair : PairUniform k hk) :
    (∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
        (hbp : ∀ p, (tautologicalBundle k 10).proj (G p) = padGaussFun E ND p.1)
        (hvec : ∀ p, evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
        Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
          (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))) ∨
    (∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
        (hbp : ∀ p, (tautologicalBundle k 10).proj (G p) = padGaussFun E ND p.1)
        (hvec : ∀ p, evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
        Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
          (-(Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk)))) := by
  classical
  obtain ⟨s, hs, hpair'⟩ := hpair
  rcases hs with h1 | h1
  · -- the branch `s = 1`
    left
    subst h1
    intro V _inst E ND G hgm hbp hvec ε C q hU R hR hbox g hg hg2
    obtain ⟨x : V.pt⟩ := (inferInstance : Nonempty V.pt)
    obtain ⟨w, hw, hwval⟩ := hpair' E ND G hgm hbp hvec C q hU hR hbox g hg hg2
    obtain ⟨z, _hzspan, hzrel⟩ :=
      Work.ThomBordism.fibreReading_collapseClass (V := V) hk E C q hU hR hbox g hg hg2 x w hw
    obtain ⟨Ugen, hUgenspan, hUgen⟩ :=
      Work.ThomBordism.localDegreeGenExists (V := V) hk E C.eps_pos C q hU hR hbox g hg hg2
    have h1a : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x) k
        (Work.ThomBordism.nfRes E x k
          (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))) z = 1 := by
      rw [hzrel (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk)), hwval]
    have h2 : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k Ugen) z = 1 := by
      rw [hzrel Ugen, hUgen w, hw]
    have hgen : Submodule.span ℤ ({Work.ThomBordism.nfRes E x k Ugen} : Set
        (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
          (Work.ThomBordism.nfPunct E x))) = ⊤ :=
      Work.ThomBordism.nfRes_span_top_of_generator hk E ND x hUgenspan
    have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℤ
        (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
          (Work.ThomBordism.nfPunct E x)) (Work.ThomBordism.nfRes E x k Ugen)) := by
      rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, hgen]
    obtain ⟨m, hm⟩ := hsurj
      (Work.ThomBordism.nfRes E x k (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk)))
    have hmU : Work.ThomBordism.nfRes E x k
          (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))
        = (LinearMap.toSpanSingleton ℤ
            (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
              (Work.ThomBordism.nfPunct E x)) (Work.ThomBordism.nfRes E x k Ugen)) m := by
      rw [hm]
    rw [LinearMap.toSpanSingleton_apply] at hmU
    have hm_eq : m = 1 := by
      have h := congrArg (fun Y => Work.Tubular.relKronH
        (TopCat.of ↥(Work.ThomBordism.nfSet E x)) (Work.ThomBordism.nfPunct E x) k Y z) hmU
      rw [LinearMap.map_smul, LinearMap.smul_apply, h2, h1a, smul_eq_mul, mul_one] at h
      exact h.symm
    have h1e : (LinearMap.toSpanSingleton ℤ
          (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
            (Work.ThomBordism.nfPunct E x)) (Work.ThomBordism.nfRes E x k Ugen)) 1
        = Work.ThomBordism.nfRes E x k Ugen := by
      rw [LinearMap.toSpanSingleton_apply]
      exact @MulAction.one_smul ℤ
        (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x) (Work.ThomBordism.nfPunct E x)) _
        ((Work.Cohomology.relCohomology ℤ
          (TopCat.of ↥(Work.ThomBordism.nfSet E x)) (Work.ThomBordism.nfPunct E x) k).isModule.toMulAction) _
    rw [hm_eq] at hmU
    have hmU' : Work.ThomBordism.nfRes E x k
          (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))
        = Work.ThomBordism.nfRes E x k Ugen := hmU.trans h1e
    have hUcan_eq : Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk) = Ugen :=
      Work.ThomBordism.nfRes_eq_of_span hk E ND x
        (Work.ThomBordism.gtdUWith_realThomClassOf_span_top k hk
          (Work.ThomBordism.tautologicalBundle_horiO k) E ND G hgm hbp hvec)
        hUgenspan hmU'
    rw [hUcan_eq]
    exact hUgen
  · -- the branch `s = -1`
    right
    subst h1
    intro V _inst E ND G hgm hbp hvec ε C q hU R hR hbox g hg hg2
    obtain ⟨x : V.pt⟩ := (inferInstance : Nonempty V.pt)
    obtain ⟨w, hw, hwval⟩ := hpair' E ND G hgm hbp hvec C q hU hR hbox g hg hg2
    obtain ⟨z, _hzspan, hzrel⟩ :=
      Work.ThomBordism.fibreReading_collapseClass (V := V) hk E C q hU hR hbox g hg hg2 x w hw
    obtain ⟨Ugen, hUgenspan, hUgen⟩ :=
      Work.ThomBordism.localDegreeGenExists (V := V) hk E C.eps_pos C q hU hR hbox g hg hg2
    have h1a : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x) k
        (Work.ThomBordism.nfRes E x k
          (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))) z = -1 := by
      rw [hzrel (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk)), hwval]
    have h2 : Work.Tubular.relKronH (TopCat.of ↥(Work.ThomBordism.nfSet E x))
        (Work.ThomBordism.nfPunct E x) k (Work.ThomBordism.nfRes E x k Ugen) z = 1 := by
      rw [hzrel Ugen, hUgen w, hw]
    have hgen : Submodule.span ℤ ({Work.ThomBordism.nfRes E x k Ugen} : Set
        (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
          (Work.ThomBordism.nfPunct E x))) = ⊤ :=
      Work.ThomBordism.nfRes_span_top_of_generator hk E ND x hUgenspan
    have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℤ
        (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
          (Work.ThomBordism.nfPunct E x)) (Work.ThomBordism.nfRes E x k Ugen)) := by
      rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, hgen]
    obtain ⟨m, hm⟩ := hsurj
      (Work.ThomBordism.nfRes E x k (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk)))
    have hmU : Work.ThomBordism.nfRes E x k
          (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))
        = (LinearMap.toSpanSingleton ℤ
            (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
              (Work.ThomBordism.nfPunct E x)) (Work.ThomBordism.nfRes E x k Ugen)) m := by
      rw [hm]
    rw [LinearMap.toSpanSingleton_apply] at hmU
    have hm_eq : m = -1 := by
      have h := congrArg (fun Y => Work.Tubular.relKronH
        (TopCat.of ↥(Work.ThomBordism.nfSet E x)) (Work.ThomBordism.nfPunct E x) k Y z) hmU
      rw [LinearMap.map_smul, LinearMap.smul_apply, h2, h1a, smul_eq_mul, mul_one] at h
      exact h.symm
    have hspan_neg : Submodule.span ℤ ({(-Ugen)} : Set
        (Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E))) = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro y
      have hy : y ∈ Submodule.span ℤ ({Ugen} : Set
          (Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E))) := by
        rw [hUgenspan]; exact Submodule.mem_top
      refine Submodule.span_le.mpr ?_ hy
      intro zz hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      have hmem : -(-Ugen) ∈ Submodule.span ℤ ({(-Ugen)} : Set
          (Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E))) :=
        Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton (-Ugen)))
      simpa using hmem
    have hme : (LinearMap.toSpanSingleton ℤ
          (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
            (Work.ThomBordism.nfPunct E x)) (Work.ThomBordism.nfRes E x k Ugen)) (-1)
        = -(Work.ThomBordism.nfRes E x k Ugen) := by
      set Ygen := Work.ThomBordism.nfRes E x k Ugen with hYgen
      have hY : (LinearMap.toSpanSingleton ℤ
          (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
            (Work.ThomBordism.nfPunct E x)) Ygen) (-1) = -Ygen := by
        rw [LinearMap.toSpanSingleton_apply]
        exact @neg_one_smul ℤ
          (Work.Thom.RelCoh ℤ k ↥(Work.ThomBordism.nfSet E x)
            (Work.ThomBordism.nfPunct E x)) _ _
          ((Work.Cohomology.relCohomology ℤ
            (TopCat.of ↥(Work.ThomBordism.nfSet E x)) (Work.ThomBordism.nfPunct E x) k).isModule)
          Ygen
      exact hY
    rw [hm_eq] at hmU
    have hmU'' : Work.ThomBordism.nfRes E x k
          (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))
        = -(Work.ThomBordism.nfRes E x k Ugen) := hmU.trans hme
    have hmU' : Work.ThomBordism.nfRes E x k
          (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))
        = Work.ThomBordism.nfRes E x k (-Ugen) := by
      rw [map_neg]; exact hmU''
    have hUcan_eq : Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk) = -Ugen :=
      Work.ThomBordism.nfRes_eq_of_span hk E ND x
        (Work.ThomBordism.gtdUWith_realThomClassOf_span_top k hk
          (Work.ThomBordism.tautologicalBundle_horiO k) E ND G hgm hbp hvec)
        hspan_neg hmU'
    rw [hUcan_eq, neg_neg]
    exact hUgen

/-- **The algebraic core**: the datum-uniform pairing of `w ⌣ Ucan` with the collapse class implies
the uniformity of the branch sign (the target). -/
theorem branchSign_uniform_of_pairUniform (k : ℕ) (hk : 1 ≤ k) (hpair : PairUniform k hk) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (tautologicalBundle k 10))
      (hbp : ∀ p, (tautologicalBundle k 10).proj (G p) = padGaussFun E ND p.1)
      (hvec : ∀ p, evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε' : ℝ} (C : Work.Tubular.TubeChart E ε') (q : Work.Tubular.NormalSphSub E ε')
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (ε • Work.ThomBordism.gtdU E ND G hgm) := by
  classical
  rcases isLocalDegreeClass_pm_ucan_of_pairUniform k hk hpair with hUcan | hUcanNeg
  · rcases branchSign_gtdU_eq_pm k hk (UcanClass k hk) with hpos | hneg
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro V _inst E ND G hgm hbp hvec ε' C q hU R hR hbox g hg hg2
      rw [one_smul, hpos E ND G hgm]
      exact hUcan E ND G hgm hbp hvec C q hU hR hbox g hg hg2
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro V _inst E ND G hgm hbp hvec ε' C q hU R hR hbox g hg hg2
      have hstep : ((-1 : ℤ) • (-(Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk))))
          = Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk) := by
        rw [neg_one_zsmul]; exact neg_neg _
      rw [hneg E ND G hgm, hstep]
      exact hUcan E ND G hgm hbp hvec C q hU hR hbox g hg hg2
  · rcases branchSign_gtdU_eq_pm k hk (UcanClass k hk) with hpos | hneg
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro V _inst E ND G hgm hbp hvec ε' C q hU R hR hbox g hg hg2
      have hstep : ((-1 : ℤ) • (Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk)))
          = -(Work.ThomBordism.gtdUWith E ND G hgm (UcanClass k hk)) := neg_one_zsmul _
      rw [hpos E ND G hgm, hstep]
      exact hUcanNeg E ND G hgm hbp hvec C q hU hR hbox g hg hg2
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro V _inst E ND G hgm hbp hvec ε' C q hU R hR hbox g hg hg2
      rw [one_smul, hneg E ND G hgm]
      exact hUcanNeg E ND G hgm hbp hvec C q hU hR hbox g hg hg2


/-- **The uniformity of the branch sign of the canonical Gauss candidate.**

The sharp statement for a canonical (explicit) Thom class of the tautological oriented bundle —
`Work.Tubular.TubeLocalDegree` for the class constructed by the canonical Thom-class construction
(`Submission/Work/Thom/realThomClassOf_natural.lean`) — is *not* yet in the workspace, so the
proof is left to the stretch of work that supplies it; by `branchSign_uniform_of_sharp` the target
follows from it in one step. -/
theorem branchSign_uniform_gauss (k : ℕ) (hk : 1 ≤ k) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
        = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
      (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε' : ℝ} (C : Work.Tubular.TubeChart E ε') (q : Work.Tubular.NormalSphSub E ε')
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (ε • Work.ThomBordism.gtdU E ND G hgm) := by
  exact branchSign_uniform_of_pairUniform k hk (pairUniform_of_tubeComparison k hk (tubeComparison k hk))

end

end Work.ThomBordism
