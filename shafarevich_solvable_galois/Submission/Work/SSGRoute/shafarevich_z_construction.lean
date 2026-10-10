import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.AuxExistsGapInduction
import Submission.Work.SSGRoute.ZConstruction.ClauseSixKillLambda
import Submission.Work.SSGRoute.ZConstruction.LineAndZeroWitness
import Submission.Work.SSGRoute.ZConstruction.TwinsEndgame
import Submission.Work.SSGRoute.ZConstruction.ZDataFinal
import Submission.Work.SSGRoute.ZConstruction.mupGate_iff_isMupZData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
-- TF-FAST (IsTorsionFree local instance)
/-- Build-speed: `IsAlgClosure k Ω` needs `Module.IsTorsionFree k Ω`, which is otherwise
re-synthesized (about 2 s) at every occurrence. File-local, Prop-valued. -/
private theorem tfFast_isTorsionFree {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] :
    Module.IsTorsionFree k Ω :=
  inferInstance

attribute [local instance] tfFast_isTorsionFree
-- TF-FAST-END

/-!

## STATE (session 8): the p. 18 chase is *proved*, and the node is reduced to two gates

### 1. The diagram chase of p. 18 is a theorem, not a gate

`Submission/Work/SSGRoute/ZConstruction/AuxChase.lean` (module
`Submission.Work.SSGRoute.ZConstruction.AuxChase`) proves

> **`Work.SSGRoute.auxDatum_orthogonal_of_productFormula`** -- for a local Tate system `pair` with the
> product formula (`ZDataMup.IsProductFormula`) and the vanishing of the pairing of two
> inertia-trivial local classes (`Work.SSGRoute.IsUnramifiedOrthogonal`), a place set `T` of pairwise
> level-`K`-non-conjugate finite places which is *conjugate into `S`* and meets every level-`K` class
> of `cs(S)`, a datum `y₁` satisfying `ZHyp` at `(Λ,S)`, and a class `b` which is *relaxed dual at the
> level `Λ`* (`Work.SSGRoute.IsRelaxedDual K Λ T b`),
> `∑_{A ∈ T} pair (decomp k A ⊓ G_K) (auxDatum K S y₁ A) b = 0`.

Axioms: `[propext, Classical.choice, Quot.sound]` (checked).  **The relaxation level must be `Λ`**:
the reciprocity sum has to run over a place set covering the ramification of `y₁`, and the extra
places are `Λ`-split (`ZHyp.hyS`) but not necessarily split in a larger field `M ⊇ Λ` (`M`-split
implies `Λ`-split, since `fixingSubgroup` is antitone).  This is exactly the direction error which
made the retracted gate `Work.SSGRoute.AuxOrthogonalityGate` false (its docstring in
`ZConstruction/AuxInterface.lean` now records the counterexample and the correction).  As a
consequence the chase here needs **no** `hνS₀` hypothesis, unlike
`Work.SSGRoute.ZSplit.levelK_datum_orthogonality` (whose docstring records that hypothesis as the
genuine content of the p. 18 face).

Supporting lemmas in the same file: `Work.SSGRoute.zeroOff` (+ `isCocycleOn_zeroOff`,
`isLocConstOn_zeroOff`, `*_eq_of_mem`) for the zero-extension of the data off `G_K` which the product
formula requires, and `Work.SSGRoute.kConj_of_forall_mem` / `kConj_forall_mem_of_kConj` bridging the
spelling of the level-`K` conjugacy clause of `IsProductFormula` to `Work.SSGRoute.KConj`.

### 2. `AuxExists` from the two gates

`Submission/Work/SSGRoute/ZConstruction/AuxAssembly.lean` (module
`...ZConstruction.AuxAssembly`) proves

> **`Work.SSGRoute.auxExists_of_pairing_and_realisation`** -- `Work.SSGRoute.AuxExists K Λ S` follows
> from `Work.SSGRoute.AuxPairingGate K` and, for every finite Galois level `M ⊇ K`, the gate
> `Work.SSGRoute.AuxRealisationExt K Λ M` defined there.

`AuxRealisationExt` is the Tate--Poitou degree-one realisation in the form the assembly consumes (see
the module docstring): the realisation runs at a place set `T'` of pairwise level-`K`-non-conjugate
finite places *inside `cs(S')`* which contains a base set `T` of level-`K` representatives of `cs(S)`;
the prescribed data `f` vanishes on `T' ∖ T`; the orthogonality hypothesis is stated with the relaxed
duals at the **base** set `T` (`IsRelaxedDual K Λ T b`, the stronger form -- `T ⊆ T'` makes the
conditions at `T'` weaker, so this *is* what the counting identity needs, and it is exactly what the
proved chase supplies); and the conclusion carries, besides the agreement on the local groups of
`T'`, the vanishing on the involutions of `G_K`.

The last clause is free for odd `p`: `Work.SSGRoute.eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot`
proves that an order-two ring automorphism of an algebraically closed field of characteristic `0`
cannot fix a primitive `p`-th root of unity for odd `p`, so for `K ∋ ζ_p` the only `c ∈ G_K` with
`c ^ 2 = 1` is `1` and the clause reduces to `z 1 = 0`.  It is kept in the gate because for `p = 2`
it is a genuine part of the §4 construction.

**The odd-`p` form of the gate.**  Every realisation statement of the `ZDataMup`/`ZSplit` lane
carries `hp : p ≠ 2`, so the lane proves the realisation *without* the involution clause.  That form
is the gate `Work.SSGRoute.AuxRealisationNoInv K Λ M` (same statement as `AuxRealisationExt`, without
the clause), and for odd `p` the clause is automatic:
`Work.SSGRoute.auxRealisationExt_of_noInv` derives `AuxRealisationExt K Λ M` from
`AuxRealisationNoInv K Λ M` given a primitive `p`-th root of unity `ζ ∈ K` and `p ≠ 2` (using
`Work.SSGRoute.eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot`), and
`Work.SSGRoute.auxExists_of_pairing_and_realisation_odd` gives `AuxExists K Λ S` from
`AuxPairingGate K` and `AuxRealisationNoInv K Λ M` for all `M`.  So for odd `p` the node's obligation
is *exactly* the odd-`p` level-`K` counting identity of the lane, plus the pairing gate and `MupGate`.

Supporting place/Galois bookkeeping (all proved, all axiom-clean):
`Work.SSGRoute.ZConstruction.exists_KConj_reps` (one representative per level-`K` class of a finite
place set, *inside* that set) and `Work.SSGRoute.ZConstruction.kConj_of_local_agree` (local conditions
transport along level-`K` conjugacy), together with
`Work.SSGRoute.ZConstruction.exists_finset_KConj_ramification_cover`.

### 2b. Findings about the shared arithmetic lanes (verified this session)

* **The below-node Čebotarev step of the `μ_p` lane is blocked by two lemmas that live above this
  node.**  The `sorry` `Work.SSGRoute.chebotarev_frobenius_split_sketch` (piece 2 of the `μ_p`
  construction, `Submission/Work/SSGRoute/z_data_mup_arith.lean`) is the *unconditional* form of a
  conditional statement: the general-`k` Čebotarev density result is an *input* in this workspace
  (`NK.Reconstruct.ChebotarevDensityInput`, `Submission/NK/Reconstruct/denseChebotarev.lean`), so the
  sketch as written is not provable.  The proved version,
  `Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split`
  (`Submission/Work/SSGRoute/ZDataTwo/chebotarev_frobenius_split.lean`), carries that input as `hc`;
  but (i) it imports `Submission.Work.SSGRoute.shafarevich_theorem13`, hence cannot be used by the
  `μ_p` arithmetic below this node, and (ii) I checked by copying its proof into a module without that
  import that the proof *needs* two lemmas defined in `shafarevich_theorem13.lean`:
  `Work.SSGRoute.exists_isFrobAtPrime_notMem_finite` (line 3065) and
  `Work.SSGRoute.finite_setOf_primeUnder` (line 3333).  So making the Čebotarev step available below
  the node requires moving (or re-proving) those two lemmas below it, and stating the step with `hc`.
* The local groups in the conclusion of `Work.SSGRoute.tatePoitou_h1_realisation_sketch`
  (`z_data_mup_arith.lean`, piece 1) are `SSGRoute.decomp k A`, **not**
  `SSGRoute.decomp k A ⊓ K.fixingSubgroup` as in `ZDataMup.IsLocalTateSystem`; on a local group not
  contained in `G_K` a coboundary is not the same thing as "agreement with the prescribed data"
  (`ZDataMup.isCoboundaryOn_iff_eqOn_zero` needs the group to lie in `G_K`).  Worth a look by the lane
  before a prover spends time on that statement; the vocabulary of the gates here
  (`ZDataMup.IsLocalTateSystem`, `AuxRealisationExt`) uses the level-`K` local groups throughout.

### 3. Where the node now stands

`Work.SSGRoute.z_data_general_of_ramified` (the only `sorry` of this subtree) is, after this session,
**exactly**

  `Work.SSGRoute.MupGate`  +  `Work.SSGRoute.AuxPairingGate`  +  `Work.SSGRoute.AuxRealisationExt`,

where the first is available below the node from the two `μ_p` cores (`ZConstruction/MupGate.lean`,
whose axiom footprint is that of `Work.SSGRoute.sw_z_exists_odd_sketch` and
`Work.SSGRoute.shafarevich_z_data_two_kummerCore`), and the other two are the shared arithmetic of
the `ZDataMup`/`ZSplit` lane (the local Tate pairing with Hilbert reciprocity; the level-`K`
Tate--Poitou realisation / counting identity, cf. `ZSplit/levelK_counting_identity.lean` and
`ZSplit/krelaxed_realisation.lean` above the node).  No obligation private to this node remains
beyond those.
-/

namespace Work.SSGRoute


/-!
## PROGRESS (2026-09-26, second pass): what is proved and what is left

`Submission/Work/SSGRoute/ZConstruction/Reduction.lean` (module
`Submission.Work.SSGRoute.ZConstruction.Reduction`, sorry-free) proves:

* `Work.SSGRoute.exists_open_subgroup_cyclic_transfer` — the **`∃ V` encoding of cyclicity**:
  if `X : Γ → E` is additive on a subgroup `D ≤ Γ` and its image on `D` is cyclic, and `X` vanishes
  on a normal open subgroup intersected with `D`, then there is an open `V` with `D ⊓ V` normal in
  `D`, `D/(D ⊓ V)` cyclic generated by one element, and `X = 0` on `D ⊓ V`.
* `Work.SSGRoute.isCyclic_transfer_of_exists_V` — the converse.
* `Work.SSGRoute.transfer` (the formal corestriction `X_z δ = ∑_s s • z ((sec s)⁻¹ δ sec s)`),
  `transfer_mul_mem`, `exists_normal_open_subgroup_transfer_eq_zero`, and
  `exists_V_of_cyclic_transfer`: **the last conjunct of `shafarevich_z_construction` at a place
  `B` split in `K` is equivalent to the cyclicity of the transfer `transfer z sec` on `decomp k B`**.
* `Work.SSGRoute.shafarevich_z_construction_of_isLine` — **the theorem in the one-dimensional case**
  (`hE : ∀ x y : E, x ≠ 0 → y ∈ AddSubgroup.zmultiples x`, i.e. `E ≅ 𝔽_p`, Schmidt–Wingberg's
  `A = μ_p` case where cyclicity is free): the cochain `z := y` (extended by `0` outside `G_K`)
  satisfies all six conjuncts.

Consequences for the remaining work.

* Conjuncts 1, 2, 4, 5 of the conclusion are automatic for the cochain `z := y` restricted to `G_K`
  (and `0` outside), and conjunct 3 is then the definition of `z`.  So the *only* content of the
  theorem is conjunct 6, and by the two equivalence lemmas above it is **exactly** the statement

      for every finite place `B` outside `cs(S)` that is split in `Λ`:  the image
      `transfer z sec (decomp k B) ⊆ E` is a cyclic subgroup of `E`.

  (A place split in `Λ` is split in `K`, so `decomp k B ≤ G_K`; there the action of `G_K` on `E`
  is trivial, which is what makes the transfer additive on `decomp k B` and makes "cyclic image"
  the right notion.)

* For `dim_{𝔽_p} E = 1` this is free (every subgroup of `𝔽_p` is cyclic) — this is
  `shafarevich_z_construction_of_isLine`.

* For general `E`, the remaining obligation is isolated in
  `Submission/Work/SSGRoute/ZConstruction/SWData.lean` (module
  `Submission.Work.SSGRoute.ZConstruction.SWData`, sorry-free) as

      `Work.SSGRoute.shafarevich_z_construction_of_swData`:
      *if* there is a cochain `z` which is a locally constant `1`-cocycle on `G_K`, agrees with `y`
      on the decomposition groups of `cs(S)`, kills the involutions and the outside inertia, and
      satisfies the sharpened cyclicity condition (b) of Schmidt–Wingberg §4 outside `cs(S)`
      — namely: whenever `B` outside `cs(S)` is split in `Λ` and `z` does **not** vanish on
      `decomp k B ⊓ G_K`, the image of `z` on `decomp k B ⊓ G_K` is cyclic and `z` vanishes on the
      local group `decomp k Q ⊓ G_K` of every conjugate `Q` of `B` that is *not* a `G_K`-conjugate
      of `B` (equivalently: of every other place of `K` above the prime of `K` below `B`; this is
      exactly Schmidt–Wingberg's "`z_{σP} = 0` for `σ ≠ 1`") —
      *then* `z` satisfies all six conjuncts of `shafarevich_z_construction`.

  So the whole remaining content is the **existence** of such a `z`: Schmidt–Wingberg's §4
  construction (the sequence `z₁, z₂, …` of classes each ramifying at exactly one new prime with
  prescribed local behaviour, the pigeonhole principle on Frobenius values, the Hilbert-symbol
  product formula, and, for general `E`, the induction on `dim E` with the auxiliary field `K̃` and
  the Tate–Poitou exactness — the `coker_obstruction` / `shafarevich_existence` nodes).

  The proof of `shafarevich_z_construction_of_swData` is elementary and contains the key
  observation: for `B` outside `cs(S)` split in `Λ`, **at most one** of the conjugates
  `(sec s)⁻¹ • B` can carry a non-zero value of `z` (the sharpened (b) at any one of them kills the
  local groups of all the others), so the transfer at `B` collapses to a single term, whose image is
  cyclic by (b).
-/

/-

STATUS / ANALYSIS (2026-09-26), by the prover of this node.

Verified facts about the statement:

* `hy` on `H = K.fixingSubgroup = ker(res k K)` says `y` is *additive* on `G_K` (the action of
  `H` on `E` through `res` is trivial), so `z|_{G_K}` is likewise forced to be a group
  homomorphism `G_K → E` (a finite abelian group).  Only `z` restricted to `G_K` matters: every
  conjunct of the conclusion is a statement about `z|_{G_K}` (for the last one, note that
  `IsSplitIn k Λ B` gives `decomp k B ≤ Λ.fixingSubgroup ≤ K.fixingSubgroup = G_K`, so all the
  arguments `(sec s)⁻¹ * δ * sec s` lie in `G_K`).

* Conjuncts 1–5 are satisfiable by `z := y` (extended by `0` off `G_K`): use `hy`, `hyc`, `hyinf`
  (`hyinf` kills involutions, hence the subgroup they generate) and `hyS`.  Also `hyT` and `hy0`
  show that `y` already vanishes on `G_K ∩ decomp k B` for every `B` conjugate into `S` that is
  either `¬ IsSplitIn k K B` or has `B.valuation (p:Ω) < 1`; so conjunct 3 below really only bites
  at the places of `cs(S)` that are **split in `K` and prime to `p`**.

* The single piece of genuine content is the last conjunct: for every finite place `B` outside
  `cs(S)` that is completely decomposed in `Λ/k` one must produce an open `V ≤ G_k` with
  `decomp k B ⊓ V ≤ ker X_z` and `decomp k B / (decomp k B ⊓ V)` cyclic, where
  `X_z δ = ∑_{s : K ≃ₐ[k] K} s • z ((sec s)⁻¹ * δ * sec s) = corCocycle k Ω K E z sec δ`
  (`corCocycle_restrict`).  Since `X_z` is a homomorphism, this is *equivalent* to
  `X_z (decomp k B)` being a cyclic subgroup of `E`.  In the case `E = ZMod p` (e.g. `A = μ_p`,
  the heart of Shafarevich's existence theorem) this is automatic.

* A tempting construction — take `z` equal to `y` on the `cs(S)`-decomposition groups and `0` on
  the decomposition groups of all outside-`cs(S)` places decomposed in `Λ` — is **impossible** in
  general.  Two reviewers gave the counterexample `k = K = Λ = ℚ`, `p = 2`, `E = ZMod 2`,
  `S = {A₂, A₃}`, `y` the quadratic character of `ℚ(√17)`: the outside-`S` decomposition groups
  generate (with `G_ℚ`-conjugates) an open subgroup, so killing them all forces `z ≡ 0` by
  Chebotarev, contradicting the agreement with `y` on `decomp(A₃)` where `3` is inert in `ℚ(√17)`.
  Correspondingly the last conjunct can only be met by a `z` whose associated extension has
  *cyclic local decomposition groups* at the new ramification primes — precisely the
  Chebotarev/Grunwald–Wang/Hilbert-reciprocity construction of Shafarevich's §4 (SW Theorem 13,
  paper pp. 13–20), i.e. the "genuine new arithmetic" flagged in DESIGN.md.

So this node is not a formalisation artefact: the hypotheses are consistent, the statement is the
corrected (open-`V`-in-`G_k`) form of the local cyclicity condition, and its proof requires the
arithmetic of SW Theorem 13.
-/



/-!

## DELIVERED RUNG (2026-09-26): Grünwald over a number field for odd `p`

`Work.SSGRoute.grunwald_surjective_odd`
(`Submission/Work/SSGRoute/grunwald_surjective_odd.lean`, sorry-free) is proved: for `K/k` finite
Galois number fields, `μ_p ⊆ K`, `p` odd, a finite set `T` of places (one per prime of `K`) and any
*continuous* additive local data on the local groups `decomp k P ⊓ G_K`, there is a continuous
additive character of `G_K` restricting to the given data.  Via Kummer this is Grünwald's theorem
(the `p`-th-power form of the localisation `Kˣ/(Kˣ)^p → ∏_{P ∈ T} K_Pˣ/(K_Pˣ)^p` being onto, for odd
`p`).  It is the first step of the `z₁, z₂, …` construction of Schmidt–Wingberg §4 (the existence
of the next class with prescribed local behaviour).

## CAVEAT record (2026-09-26, end of session): the trigger of Schmidt–Wingberg's (b)

The interface `Work.SSGRoute.shafarevich_z_construction_of_swData` (in
`ZConstruction/SWData.lean`) is *proved* and sorry-free, but its hypothesis triggers the
conjugate-vanishing clause on

    `∃ δ ∈ decomp k B ⊓ G_K, z δ ≠ 0`   ("`z` does not vanish on the local group at `B`"),

whereas Schmidt–Wingberg's (b) triggers on "`z_P` is **ramified**", i.e. on `z` being non-trivial
on the **inertia** `I_B` (`z_P ∉ H¹_nr`).  The formalised trigger is *weaker* (ramified ⇒ non-zero,
not conversely), so the interface's hypothesis is *stronger* than the paper's (b): a delegated
existence result with that trigger was refuted by its prover (counterexample: `k = ℚ`,
`p = 3`, `K = Λ = ℚ(ζ₃)`, `S = {3, 7}`, `y` = the character of `ℚ(ζ₃)(∛19)/ℚ(ζ₃)`, whose local
class over 7 is *unramified but non-zero*).  Consequence for the remaining work:

* the interface must be restated with the trigger "`z` is ramified at `B`" (non-trivial on
  `I_B ⊓ G_K`), which is also what the paper's argument actually uses; the elementary "at most one
  contributing conjugate" step of `SWData.lean` survives verbatim in that form (it only uses
  `res(D_B) = 1`, i.e. `IsSplitIn k K B`);
* the *unramified* case (no conjugate ramified at all) then needs a separate input: an unramified
  local class is determined by its value on a Frobenius, i.e. the local group modulo inertia is
  procyclic — this is the only place where local field theory (`g_{k_v}/I_v ≅ Ẑ`) enters, and it is
  not available in the workspace yet.

-/


/-!

## STATE at the end of this session, and the exact next request

**Proved and imported** (`ZConstruction/Reduction.lean`, `ZConstruction/SWData.lean`,
`grunwald_surjective_odd.lean`, all sorry-free):

* the `∃ V` encoding of the last conjunct of `shafarevich_z_construction` and its converse, so that
  conjunct is *equivalent* to cyclicity of `transfer z sec` on `decomp k B`;
* the theorem in the case `dim_{𝔽_p} E ≤ 1` (Schmidt–Wingberg's `A = μ_p`);
* `shafarevich_z_construction_of_swData`: the conclusion of the theorem from Schmidt–Wingberg's
  local data (a)+(b), with the "at most one contributing conjugate" observation;
* `Work.SSGRoute.grunwald_surjective_odd`: Grünwald over a number field for odd `p` (continuous
  local data, one place per prime of `K`), proved by a child;
* `Work.SSGRoute.z_eq_zero_of_sq_eq_one`: the involution clause (conjunct 4) of
  `shafarevich_z_construction` is **free for odd `p`** — for a cochain additive on `G_K` one has
  `z c + z c = z (c * c) = z 1 = 0` and `2` is invertible in `ZMod p`.  So no future statement in
  the `z₁, z₂, …` construction needs to carry it as a hypothesis.


**The next request (already reviewed, not yet spawned — the team was busy):**
`SSGRoute/shafarevich_z_step_mup`, the *first step* of the `z₁, z₂, …` construction.  Its statement
must ask for a place `P₁` (outside `cs(S)`, split in `Λ`) and a cochain `z` agreeing with `y` on the
decomposition groups of `cs(S)`, killing the involutions and the outside/non-split inertia, being
**ramified at `P₁`** and **unramified at every other place outside `cs(S)`** — the single new
ramification class is what gives the statement content: without it `z := y` (whose ramification set
is automatically finite) makes the step vacuous (two reviewers caught exactly this).  The arithmetic
engine is `Work.SSGRoute.classField_exists_ramified` (every open subgroup of the idèle class group of
index `p` is a norm group, *no* ramification restriction) together with the Chebotarev choice of
`P₁`; the file of `classField_exists_ramified` names the Grunwald/Shafarevich step lemmas as its
intended consumers.

**Hypothesis mismatch to keep in mind.** Two provers rejected intermediate statements because the
paper's hypothesis (H1) — `y` unramified at *every* `P ∉ T(K)`, in particular at the `Λ`-split
places outside `cs(S)` — is strictly stronger than `hyS` of the theorem, which only forces
unramifiedness at the non-split-in-`Λ` places.  Any intermediate statement in the `z₁, z₂, …`
construction must be phrased so that it is provable from the *weak* `hyS` (as the assigned theorem
is), or must carry the extra unramifiedness as an explicit hypothesis.

-/


/-!

## Recipe for the queued `P₁` lemma (`SSGRoute/exists_split_place_avoiding`)

Reviewed (both reviewers: correct, non-vacuous), spawn refused twice only because the fleet is busy —
re-issue `request_lemma` for that path when a slot frees.  All ingredients are proved and located:

* `NK.UchidaKummer.exists_splitsCompletely_notMem (T : Finset (NK.Chebotarev.PrimeIdeal K))` gives a
  prime of `k` outside `T` splitting completely in `Λ` (density `1/[Λ:k]`);
* `Commons.NumberTheory.NumberField.Valuation.exists_valuationSubring_at_prime` gives a place `P₁` of
  `Ω` with `P₁.comap (algebraMap k Ω) = valuationSubringAtPrime k p`;
* `NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely` converts "split completely" for
  the prime into `SSGRoute.IsSplitIn k Λ P₁` for the place (as used in
  `Work.SSGRoute.bauer_of_chebotarev`);
* `Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top` gives `SSGRoute.IsFinPlace k P₁`;
* for the avoidance clause: `Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq` (two finite places
  with the same `comap` to `k` are conjugate) reduces `¬ IsConjPlace k A P₁` for `A ∈ S` to
  `P₁.comap ≠ A.comap`; the finitely many `comap`s occurring in `S` are themselves
  `valuationSubringAtPrime` of primes of `k`, which one feeds into the `T` of the first item.

-/


/-!

## DELIVERED (latest session, second pass)

* `Work.SSGRoute.local_kummer_dictionary` (module
  `Submission.Work.SSGRoute.ZConstruction.localKummerDictionary`, sorry-free, axiom-clean): **the
  local Kummer dictionary for every prime `p`** --- the Kummer character of `a ∈ Kˣ` (the cochain
  `σ ↦ σ(√[p]a)/√[p]a` of `Work.SSGRoute.kummerCharZMod`) vanishes on the decomposition group of a
  finite place `A` exactly when `a` is a local `p`-th power at the prime `𝔭` below `A`
  (`NK.UchidaKummer.localPowClass K p 𝔭 a = 1`).  Its `p = 2` form `local_kummer_dictionary_two` is
  the statement recorded (still with a `sorry` there) as
  `Work.SSGRoute.kummerChar_eq_zero_iff_local_powClass`, i.e. the "P1" local Kummer dictionary of
  the `p = 2` node `Work.SSGRoute.shafarevich_z_data_two`; it is now available, proved.
  The proof is the chain
  `NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff` (local Kummer theory) +
  `NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one` +
  `NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely` (the local/global bridge) +
  the identification of "the character vanishes at `σ`" with "`σ` fixes a `p`-th root of `a`".

* `Work.SSGRoute.exists_split_place_avoiding` (module
  `Submission.Work.SSGRoute.exists_split_place_avoiding`, sorry-free, axiom-clean): the Chebotarev
  prime `P₁` of Schmidt--Wingberg §4 --- a finite place splitting completely in `Λ` and lying over a
  prime of `k` different from all the primes below the elements of `S`.

## DELIVERED (previous pass): the assembly is complete, the gap is one arithmetic statement

The theorem below is now *assembled*: its proof is the bridge
`Work.SSGRoute.shafarevich_z_construction_of_zData` (module
`Submission.Work.SSGRoute.ZConstruction.ZDataBridge`, sorry-free, axiom-clean) applied to the single
isolated arithmetic statement `Work.SSGRoute.z_data_general` (module
`Submission.Work.SSGRoute.ZConstruction.ZDataGeneral`, the remaining obligation).  The bridge takes
Schmidt--Wingberg's `z`-data with the **corrected trigger**: the sharpened condition (b) is triggered
on *ramification* (non-triviality on the inertia), not on non-vanishing, which is what the paper's
construction actually produces; the unramified-but-non-zero case is handled internally by the
pro-cyclicity of `decomp k B / I_B` (`Work.SSGRoute.decomp_mod_inertia_cyclic`), via

* `Work.SSGRoute.cyclic_transfer_of_vanishing` (module
  `Submission.Work.SSGRoute.cyclic_transfer_of_vanishing`, sorry-free, axiom-clean): if the inertia
  `I_B` lies in an open subgroup `V` on which the transfer vanishes, then the image of the transfer
  on `decomp k B` is cyclic;
* the case analysis of `ZDataBridge`: either no conjugate of `B` is ramified (the `V` above is the
  intersection of the conjugates of `K ⊔ U`, with `U` a normal open subgroup on which `z` vanishes),
  or some conjugate `Q = (sec s)⁻¹ • B` is ramified, in which case all terms of the transfer except
  the `s`-th vanish by (b) at `Q` (distinct conjugates are never `G_K`-conjugate) and the `s`-th term
  is `z` composed with the isomorphism `decomp k B ≅ decomp k Q ⊓ G_K`.

Two further rungs are on disk, both sorry-free and axiom-clean:

* `Work.SSGRoute.exists_split_place_avoiding` (module
  `Submission.Work.SSGRoute.exists_split_place_avoiding`): the Chebotarev prime `P₁` of §4 --- a
  finite place splitting completely in `Λ` and lying over a prime of `k` different from all the
  primes below the elements of `S`;
* `Work.SSGRoute.cyclic_transfer_of_vanishing`, as above.

Two further pieces of bookkeeping are on disk next to the gap: the conversion
`Work.SSGRoute.isCocycleOn_fixingSubgroup_iff_additive` (on `G_K` the crossed-homomorphism condition
*is* additivity, so the `IsCocycleOn`-shaped sibling statements plug into `z_data_general`), and the
hypothesis-shape caveat recorded in `ZDataGeneral.lean` (the target's hypotheses are not the paper's
(H1)/(H2); in particular the induction's auxiliary class `ỹ` is ramified at `T(K) ⊆ cs(S')(K)`, so a
one-dimensional input requiring "vanishing on the inertia of `cs(S)`" cannot be applied to it).

The remaining obligation `Work.SSGRoute.z_data_general` is the *arithmetic core* of Schmidt--Wingberg
§4 in the exact shape consumed by the theorem; its one-dimensional case is the fleet's
`Work.SSGRoute.shafarevich_z_data_mup` / `Work.SSGRoute.shafarevich_z_data_two` /
`Work.SSGRoute.sw_z_exists_odd_sketch`, and the general case is the induction on `dim_{𝔽_p} E` with
the auxiliary field `K̃` and the Poitou--Tate diagram chase.  Note that for `dim_{𝔽_p} E ≤ 1` the
theorem is *already proved* without any of this (`shafarevich_z_construction_of_finrank_le_one`),
because every subgroup of a one-dimensional `𝔽_p`-space is cyclic; so the residual work is exactly
the case `dim_{𝔽_p} E ≥ 2`.
-/



/-!
## PROGRESS (2026-09-26, third pass): the `z`-data calculus and the shape of the induction

`Submission/Work/SSGRoute/ZConstruction/ZDataGlue.lean` (module
`Submission.Work.SSGRoute.ZConstruction.ZDataGlue`, sorry-free, axiom-clean) packages the six
properties of the auxiliary class `z` as `Work.SSGRoute.HasZData K Λ S y z` (conjunct 1 in the
*additivity* form, equivalent to the cocycle form on `G_K` by
`Work.SSGRoute.isCocycleOn_fixingSubgroup_iff_additive`), isolates the *good places*
`Work.SSGRoute.IsGoodPlace Λ S B` (finite, outside `cs(S)`, split in `Λ`), and proves:

* `Work.SSGRoute.hasZData_add` — the `z`-data is closed under addition, given (i) *disjointness* of
  the ramification at every good place (`z` ramified there ⟹ one summand vanishes identically on
  the local group) and (ii) the vanishing of both summands on the local groups of the conjugates
  that are not `G_K`-conjugates.  This is the paper's "it is now easily verified that `z = z⁰ + inf
  z⁰⁰` satisfies (a) and (b)";
* `Work.SSGRoute.hasZData_add_of_split_confined`, `Work.SSGRoute.hasZData_of_component_data` — the
  same, with the two abstract hypotheses replaced by the two *mechanisms* the paper uses:
  the **level change** `kills_decomp_of_split_of_vanishes` (a cochain vanishing on `G_{L'}` kills
  the local group of every place that splits completely in the level `L'`; in the paper `L'` is the
  Galois closure `K̃` of the field cut out by `z⁰`, and the new primes of `z⁰⁰` are chosen to split
  completely in it), and the **prescription of the auxiliary class** (`z¹` vanishes on the local
  groups of the conjugates of the good places where `z⁰` is ramified: the paper's `ỹ_P = 0` for
  `P ∈ T'(K) ∖ T(K)`);
* `Work.SSGRoute.hasZData_map` (change of coefficients along an injective additive map — the way the
  induction passes back from the submodule `ker π ⊆ E` to `E`) and `Work.SSGRoute.hasZData_congr`;
* `Work.SSGRoute.exists_fixingField_vanishing` (`ZConstruction/LevelExistence.lean`) — **the level
  cut out by a cochain**: an additive, locally constant cochain on `G_K` vanishes on `G_L` for some
  finite intermediate field `L ⊆ Ω` (apply `exists_normal_open_of_z_eq_zero` and
  `exists_finiteDimensional_normal_fixingSubgroup_le`).  This is the level `K̃` of the induction,
  and the field is finite over `k`, so its Galois closure over `k` (the field used in the paper) is
  finite as well;
* `Work.SSGRoute.zadd_conj` — **conjugation triviality**: an additive cochain on `G_K` with abelian
  coefficients satisfies `z (τ * u * τ⁻¹) = z u` for `τ, u ∈ G_K`.  Consequently the sharpened
  clause (b) ("`z` kills `D_Q ⊓ G_K` for every conjugate `Q` that is not `G_K`-conjugate to `B`")
  is a condition at *one* place per prime of `K` over a given prime of `k`: it is exactly the
  paper's `z^σ_P = 0` for `σ ∈ G(K|k) ∖ {1}`, no more and no less.

`Work.SSGRoute.hasZData_of_component_data` fixes the **shape of the induction step** on
`dim_{𝔽_p} E`: given a decomposition `y = y₀ + y₁` of the given cochain (in the paper
`E = E₀ ⊕ μ_p`, `y₁ = π ∘ y` for a `𝔽_p`-linear projection `π : E → E` of rank one),
a `z`-data witness `z₀` for `y₀` (the induction hypothesis, applied to the coefficient module
`ker π` and transported back by `hasZData_map`), a level `L'` with `z₀` vanishing on `G_{L'}`, and a
`z`-data witness `z₁` for `y₁` confined at good places to places splitting completely in `L'` and
vanishing on the conjugates of the good places where `z₀` ramifies, the sum `z₀ + z₁` has the
`z`-data for `y`.  The remaining obligation of this node is therefore exactly the **one-dimensional
input** in that shape (Schmidt–Wingberg §4 for `A = μ_p`, together with the auxiliary class `ỹ`),
which the sibling nodes `Work.SSGRoute.sw_z_exists_odd_sketch` / `shafarevich_z_data_two` /
`z_data_mup_core` are building.

### The single remaining `sorry` of the node (state at the end of the third pass)

`Submission/Work/SSGRoute/ZConstruction/ZDataGeneral.lean` isolates the whole arithmetic content of
the node in `Work.SSGRoute.z_data_general_of_ramified` (the case in which `y` is ramified at some
good place), and proves the unramified case `Work.SSGRoute.z_data_general_of_unramified` (`z := y`,
condition (b) vacuous) as well as the reduction `Work.SSGRoute.z_data_general` = unramified case ∨
ramified case.  So the node is complete modulo

* the one-dimensional input of `Work.SSGRoute.hasZData_of_component_data` (Schmidt–Wingberg §4 for
  `A = μ_p`: the sequence `z₁, z₂, …`, the pigeonhole principle, the Hilbert-symbol product formula,
  and the auxiliary class `ỹ`, i.e. the Tate–Poitou degree-one realisation) — being built in the
  sibling nodes `Work.SSGRoute.sw_z_exists_odd_sketch`, `Work.SSGRoute.shafarevich_z_data_two`,
  `Work.SSGRoute.z_data_mup_core`;
* the induction on `dim_{𝔽_p} E`, for which the transfer theorems of `ZDataGlue.lean` above supply
  the complete assembly step.

### The wiring step (next concrete task, interface fixed)

The induction on `dim_{𝔽_p} E` is now to be wired into `Work.SSGRoute.hasZData_of_component_data`.
The theorem to prove is

  `z_data_general_of_component_data` : the conclusion of `Work.SSGRoute.z_data_general`, from
  (i) the induction hypothesis `IH`, quantified over *all* coefficient modules `E'` with
      `Module.finrank (ZMod p) E' < Module.finrank (ZMod p) E` (with the trivial `Gal(K/k)`-action,
      which is enough because the `z`-data never uses the action) and all cochains `y'` with the
      hypotheses of the target;
  (ii) the one-dimensional input `Work.ZDataMup.exists_zData_mup_level` (`A = μ_p`), which is
      delegated and running;

by taking an `𝔽_p`-linear projection `π : E →ₗ[ZMod p] E` with `π ∘ π = π` and
`finrank (ker π) < finrank E`, and

  * `y₀ := y - π ∘ y`, which takes values in `ker π`; its hypotheses follow componentwise from those
    of `y` (all conditions are of the form "`y σ = 0`"), so `IH` applies to it after
    `hasZData_map` (transport along the inclusion `ker π ↪ E` is an injective additive map);
  * `y₁ := π ∘ y`, which takes values in the line `range π ≅ ZMod p`; the one-dimensional input
    applies to it after transport along a `ZMod p`-linear equivalence `range π ≃ₗ ZMod p`;
  * `L'` from `Work.SSGRoute.exists_fixingField_vanishing` applied to `z₀` (and one may replace it by
    its Galois closure over `k`, which exists since the field produced is finite over `k`);
  * the killing set `T` is a finite set of places meeting the `G_k`-conjugacy classes of the good
    places at which `z₀` is ramified, and `z₁` supplies the `hconf`/`hkill` clauses.

`y₀ + y₁ = y` pointwise, so `hasZData_of_component_data` concludes.  The remaining `sorry` of the
node is then exactly the one-dimensional input in (ii) — and the interaction between the induction
hypothesis and the one-dimensional input is precisely the point at which the hypothesis-shape caveat
below has to be re-examined (Schmidt–Wingberg's §4 uses that `y` and the class `α` it constructs
have the same image in the Tate–Poitou dual, which is available for a class in `H¹(k_S|K, A)` but not
for an arbitrary cochain with the target's weaker hypotheses).

### What the arithmetic can and cannot supply (recorded for the record)

* `Work.SSGRoute.grunwald_surjective_odd` (proved, session 2) and
  `NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation` give the **fine local
  Kummer realisation**: prescribed local data at *any* finite set of primes of `K` (one place per
  prime of `k` in the frozen Grünwald statement, but the underlying Kummer surjectivity is stated
  for an arbitrary finite set of prime ideals) is realised by a global class `a ∈ Kˣ/(Kˣ)^p`.
* It does **not** give *ramification control*: the realisation is by an element of `Kˣ`, which may
  and generally does ramify at primes outside the prescribed set.  The stronger "`S`-unit" form
  (realisation by `a` with `a ∈ (K_𝔮ˣ)^p` for all `𝔮 ∉ S`) is false in general — for an odd prime
  `p` and `|S|` primes with `p ∤ N𝔮 - 1` the source `K_Sˣ/(K_Sˣ)^p` has `𝔽_p`-rank `|S| + r` while
  the target `∏_{𝔮 ∈ S} K_𝔮ˣ/(K_𝔮ˣ)^p` has rank `2|S|`, so it cannot be surjective once `|S| > r`.
  This is exactly why Schmidt–Wingberg need the sequence `z₁, z₂, …` with *new primes*, the
  Tate–Poitou exactness (the class-group/Selmer obstruction) and the Hilbert-symbol product formula,
  and not merely Grünwald's theorem.
* Consequently the one-dimensional input above must be stated with its own *confinement* clause (the
  ramification at good places is exactly the ramification of a class in `H¹(k_S|K, μ_p)` plus the
  new primes), which is what `hasZData_of_component_data`'s hypotheses `hconf` and `hkill` encode.

### The hypothesis-shape caveat (re-derived with the paper in hand)

Schmidt–Wingberg's Theorem 13 assumes `y ∈ H¹(k_S|K, A)` with `y_P` unramified for `P ∈ T(K)` and
`y_P = 0` for `P ∩ k ∈ Ram(K|k) ∪ S_p ∪ S₁`; the present statement assumes the weaker conditions
`hyS`, `hyT`, `hy0` of the target (which do not force `y` to be unramified at places outside `S(K)`
that split completely in `Λ`).  The formalised theorem is therefore *stronger* than the published
one; the constructions above are insensitive to the difference (only the local data of `y` at the
places of `cs(S)` and the inertia-vanishing are used), but any appeal to a statement whose
hypotheses include "`y` unramified outside `T(K)`" must be checked against `hyS`/`hyT`/`hy0` first.
-/


/-!

## STATE (session 4): the confinement route retracted, the level-change rung proved

**What was attempted.**  The general-coefficient case of Schmidt--Wingberg's Theorem 13
(`Work.SSGRoute.z_data_general`) is assembled from the one-dimensional case by the induction on
`Module.finrank (ZMod p) E` of the paper (pp. 18--19), whose assembly is already on disk:

* `Work.SSGRoute.hasZData_of_component_data` (`ZConstruction/ZDataGlue.lean`): `E = E₀ ⊕ L` from a
  `z`-data witness for the `E₀`-component and one for the line `L`, given the *level change*
  (`kills_decomp_of_split_of_vanishes`) and the prescription of the auxiliary class;
* the **one-dimensional input** with two extra clauses -- *confinement* of its ramification at good
  places to a level `M`, and *killing* on the local groups of a prescribed set `T''` of good places
  -- which were stated in `Submission/Work/SSGRoute/z_data_mup_level.lean` (odd `p`) and
  `z_data_two_level.lean` (`p = 2`), reviewed by four reviewers ("looks correct as stated"), and
  delegated.

**Outcome of the delegation: the confined form is FALSE.**  Two provers, one per parity of `p`,
showed independently that those statements are mis-stated:

* the odd-`p` prover derived the obstruction from the Poitou--Tate realisation criterion: the
  hypothesis `hyunr` (unramified at places *unramified in `M`*) lets `y` be ramified at
  `M`-ramified places outside `cs(S) ∪ cs(T'')`, while the conclusion forbids `z` to ramify there;
  the local Tate pairing of the ramified part of `y` against the Selmer dual then does not vanish,
  so the datum of `y` cannot be realised with the confinement imposed.  (Schmidt--Wingberg avoid
  this by assuming `(H1)` -- `y` unramified at `P ∉ T(K)` -- and by putting the ramification of the
  level into `T`; the formalised hypotheses were strictly weaker.)
* the `p = 2` prover identified the missing link `M ≤ Λ` between the confinement level and the
  auxiliary field and **proved** (`Submission/Work/SSGRoute/z_data_two_level_proof.lean`,
  `Work.SSGRoute.z_data_two_level_of_le`, axiom-clean) that with `M ≤ Λ` the statement is
  *trivial*, the witness being `z := y` extended by `0` off `G_K`.

Both statement files now carry a retraction note recording this.

**The rung that replaces the confinement clause.**  What the paper's induction actually uses is not
an independent confinement level but a **change of the auxiliary field** `Λ ↦ Λ·L` (`L` = the level
of the other summand), together with the fact that enlarging `Λ` only *strengthens* the `z`-data.
That fact is now proved, sorry-free and axiom-clean, in
`Submission/Work/SSGRoute/ZConstruction/ZDataInduction.lean`:

* `Work.SSGRoute.hasZData_of_le_level`: `HasZData K Λ' S y z → Λ ≤ Λ' → HasZData K Λ S y z`.

That file also provides the rest of the induction's infrastructure:

* `Work.SSGRoute.ZHyp` -- the hypotheses of the target on the datum `y`, packaged, with the
  transport `Work.SSGRoute.ZHyp.comp` along a `ZMod p`-linear map;
* `Work.SSGRoute.Conf` -- the confinement clause at a level `M`, with monotonicity `Conf.mono`;
* `Work.SSGRoute.exists_rankOne_projection` -- for `2 ≤ finrank (ZMod p) E` a line with a complement
  (the `E = E₀ ⊕ L` of the induction);
* `Work.SSGRoute.exists_fixingField_vanishing_finite` -- the *level of a cochain* as a
  finite-dimensional **Galois** intermediate field on whose Galois group a given additive, locally
  continuous cochain vanishes.

**Consequence for the node.**  `Work.SSGRoute.z_data_general` (the `HasZData` obligation of
`ZConstruction/ZDataGeneral.lean`, i.e. Schmidt--Wingberg's conditions (a) and (b)) is *stronger*
than the published Theorem 13 in one respect: the target's hypotheses (`hyS`/`hyT`/`hy0`) allow `y`
to be ramified at the places of `cs(Λ|k)(K)` outside `cs(S)(K)`, whereas the paper assumes `(H1)`.
The verified obstruction above shows that the `HasZData` route cannot absorb that extra ramification
by a confinement clause.  A route for the *theorem* which does not go through (b) at those places is
the equivalence recorded at the top of this file: the sixth conjunct of
`Work.SSGRoute.shafarevich_z_construction` is *cyclicity of the transfer*, which is (i) automatic in
the case `dim_{𝔽_p} E ≤ 1` (already proved) and (ii) only constrains the *finitely many* places at
which the constructed `z` is ramified, so it is compatible with `z` agreeing with `y` on all of
`cs(S)(K)` -- unlike the conjugate-killing clause of `HasZData`.

-/

/-- **The node's conclusion from the four gates, for odd `p`.**

This is the *complete* reduction of `Work.SSGRoute.shafarevich_z_construction` to named statements: a
one-line assembly of `Work.SSGRoute.z_data_general_of_odd_gates`
(`ZConstruction/ZDataGeneral.lean`, which produces the auxiliary `z`-data from `MupGate` and the three
gates of `ZConstruction/AuxExistsAssembly.lean`) with the proved elementary half
`Work.SSGRoute.shafarevich_z_construction_of_zData` (`ZConstruction/ZDataBridge.lean`).

The gates are

* `Work.SSGRoute.MupGate (p := p) K` -- the one-dimensional (`A = μ_p`) statement, available from the
  two arithmetic cores by `Work.SSGRoute.mupGate_of_cores`;
* `Work.SSGRoute.AuxPairingGate (p := p) K` -- the level-`K` local Tate system with the product
  formula and the unramified orthogonality (`ZConstruction/levelK_pairing_productFormula.lean` for
  odd `p`, with Hilbert reciprocity as its single input);
* `ZConstruction.AuxDatumOrthogonalityGate (p := p) (K := K) Λ'` for every `Λ'` -- the p. 18
  orthogonality of the prescribed datum against the honest dual Selmer group; *this is arithmetic*
  (equivalent, with the next gate, to the realisability of the datum: see
  `ZConstruction/NOTE_session19.lean`, §3);
* `ZConstruction.AuxDatumCounting (p := p) (K := K) Λ'` -- the level-`K` Poitou--Tate counting
  inequality at a place set covering the places above `p` and the places ramified in the auxiliary
  level;

together with `hp : p ≠ 2`, whose role is to discharge the involution clause of the auxiliary class
(`Work.SSGRoute.eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot`).  For `p = 2` the same assembly
needs the archimedean analogues of the last three gates (the pairing
`Work.SSGRoute.ZDataTwo.IsMu2LocalTateSystemWithArch` is the shape of the first of them). -/
theorem shafarevich_z_construction_of_odd_gates (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s)
    (hp : p ≠ 2) (hmup : MupGate (p := p) K) (hP : AuxPairingGate (p := p) K)
    (hgate : ∀ (Λ' : IntermediateField k Ω),
      Work.SSGRoute.ZConstruction.AuxDatumOrthogonalityGate (p := p) (K := K) (Λ := Λ'))
    (hcount : ∀ (Λ' : IntermediateField k Ω),
      Work.SSGRoute.ZConstruction.AuxDatumCounting (p := p) (K := K) (Λ := Λ')) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  -- the trivial action of `G_K` on the coefficient module `ZMod p` of the gates
  letI : DistribMulAction (K ≃ₐ[k] K) (ZMod p) :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  letI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p) := ⟨fun _ _ _ => rfl⟩
  obtain ⟨z, hz⟩ :=
    z_data_general_of_odd_gates (p := p) (k := k) (Ω := Ω) hp hmup hP hgate hcount Λ S
      ⟨hKΛ, ζ, hζ, hζK, hSfin, hSdisj, hSram⟩ E y ⟨hy, hyc, hyS, hyT, hy0, hyinf⟩
  exact shafarevich_z_construction_of_zData hKΛ S y sec hsec ⟨z, hz⟩

/-!
## NOTE (session 21): the gate matched by Poitou--Tate, and the no-gap condition

The mixed realisation gate `∀ M, AuxRealisationExt K Λ M` consumed by
`Work.SSGRoute.auxExists_of_pairing_and_realisation` is **not** the statement of the level-`K`
Poitou--Tate exactness.  The exactness matches the primal "unramified at the places outside `cs(T')`
that are not split in `M`" with the dual family `IsRelaxedDual K M T'` (`M`-relaxed) -- the
relaxation level of the dual is the level of the primal -- while the p. 18 chase produces
orthogonality against the *smaller* family `IsRelaxedDual K Λ T`.  The difference is the "slack" of
`ZConstruction/AuxRealisationSlack.lean` (an open, definition-level restatement of the mixed gate).

The present file replaces it by

* the **unmixed** gate `∀ M, AuxRealisationExt K M M` (the statement Poitou--Tate matches), and
* the explicit **no-gap provision** `ZConstruction.AuxGapProv K Λ S`: every one-dimensional datum
  with `ZHyp` at `(Λ,S)` is unramified at the places outside `cs(S)` that are `Λ`-split but not
  `N`-split (for the level `N` of the auxiliary class).

The orthogonality hypothesis of the unmixed gate at level `M` is then supplied by the **proved**
sharp chase `Work.SSGRoute.ZConstruction.auxDatum_orthogonal_relaxed_noGap`, and the assembly is
`Work.SSGRoute.ZConstruction.auxExists_of_pairing_and_unmixed_and_gap`
(`ZConstruction/AuxExistsUnmixed.lean`, axiom-clean).  The no-gap condition is

* *vacuous* in the paper's setting: Schmidt--Wingberg assume (H1) that `y` is unramified at every
  prime `P ∉ T(K)`, so the datum is unramified everywhere outside `cs(S)`
  (`Work.SSGRoute.ZConstruction.auxGapFun_of_unramified`);
* automatic for the *line component* `π ∘ y` of the §4 induction as soon as the span of the
  ramification of `y` at the `Λ`-split places outside `cs(S)` is a proper subspace of the
  coefficient module (`Work.SSGRoute.ZConstruction.auxGapFun_comp_of_junkSpan_le`): the places of
  `junkSpan` are exactly the "gap" places, and if they miss a line then the component can be chosen
  to kill them.

The theorem below is the analogue of `shafarevich_z_construction_of_odd_gates` for this corrected
gate list; it carries **no** parity hypothesis, the involution clause being part of the unmixed
gate. -/

/-- **The node's conclusion from the corrected gate list.**

`hmup` is the one-dimensional gate `MupGate` (the two `μ_p` cores of §4), `hP` the local Tate
system `AuxPairingGate` (local axioms, unramified orthogonality, product formula), `hU` the
**unmixed** degree-one realisation at every level (the level-`K` Poitou--Tate exactness, supplied by
the counting identity of the `ZSplit`/`PT` lanes), and `hgap` the no-gap provision
`ZConstruction.AuxGapProv` of `ZConstruction/AuxExistsUnmixed.lean` (automatic in the paper's (H1)
setting).  There is **no** parity hypothesis: the involution clause is part of `hU`. -/
theorem shafarevich_z_construction_of_unmixed_gates (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s)
    (hmup : MupGate (p := p) K) (hP : AuxPairingGate (p := p) K)
    (hU : ∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M],
      AuxRealisationExt (p := p) K M M)
    (hgap : ∀ (Λ' : IntermediateField k Ω) [FiniteDimensional k Λ'] [IsGalois k Λ']
      (S' : Finset (ValuationSubring Ω)), ZConstruction.AuxGapProv (p := p) K Λ' S') :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  -- the trivial action of `G_K` on the coefficient module `ZMod p` of the gates
  letI : DistribMulAction (K ≃ₐ[k] K) (ZMod p) :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  letI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p) := ⟨fun _ _ _ => rfl⟩
  obtain ⟨z, hz⟩ :=
    ZConstruction.z_data_general_of_unmixed_gates_gap (p := p) (k := k) (Ω := Ω)
      hmup hP hU hgap Λ S ⟨hKΛ, ζ, hζ, hζK, hSfin, hSdisj, hSram⟩ E y
      ⟨hy, hyc, hyS, hyT, hy0, hyinf⟩
  exact shafarevich_z_construction_of_zData hKΛ S y sec hsec ⟨z, hz⟩

/-- **The node's conclusion from the Poitou--Tate-matched gate list.**

As `shafarevich_z_construction_of_unmixed_gates`, but with the realisation hypothesis
`ZConstruction.AuxRealisationT` -- the statement whose primal condition ("unramified at the places
outside `cs(T)` that are not `M`-split") has `IsRelaxedDual K M T` as its Poitou--Tate dual, i.e.
exactly the family against which the p. 18 chase produces orthogonality (under the no-gap provision
`ZConstruction.AuxGapProv`). -/
theorem shafarevich_z_construction_of_realisationT_gates (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s)
    (hmup : MupGate (p := p) K) (hP : AuxPairingGate (p := p) K)
    (hU : ∀ (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M],
      ZConstruction.AuxRealisationT (p := p) K M)
    (hgap : ∀ (Λ' : IntermediateField k Ω) [FiniteDimensional k Λ'] [IsGalois k Λ']
      (S' : Finset (ValuationSubring Ω)), ZConstruction.AuxGapProv (p := p) K Λ' S') :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  letI : DistribMulAction (K ≃ₐ[k] K) (ZMod p) :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  letI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p) := ⟨fun _ _ _ => rfl⟩
  obtain ⟨z, hz⟩ :=
    ZConstruction.z_data_general_of_realisationT_gates (p := p) (k := k) (Ω := Ω)
      hmup hP hU hgap Λ S ⟨hKΛ, ζ, hζ, hζK, hSfin, hSdisj, hSram⟩ E y
      ⟨hy, hyc, hyS, hyT, hy0, hyinf⟩
  exact shafarevich_z_construction_of_zData hKΛ S y sec hsec ⟨z, hz⟩

/-- **The node from the corrected gate list: the one-dimensional gate, the per-datum auxiliary-class
gate, and the Case C gate.**

The gate list of `shafarevich_z_construction_of_unmixed_gates` (`MupGate`, `AuxPairingGate`,
`AuxRealisationExt K M M`, the *uniform* no-gap provision `AuxGapProv`) shares with
`shafarevich_z_construction_of_realisationT_gates` the defect that the uniform no-gap provision is
*not* implied by the node's hypotheses (`ZHyp`) on the datum: the no-gap condition
`AuxGapFun K Λ S N ν` may fail for a one-dimensional datum ramified at a `Λ`-split place outside
`cs(S)` that is not `N`-split.

The corrected list has a *per-datum* obligation and is therefore not subject to that defect:

* `hmup` -- the one-dimensional gate `MupGate` (the two `μ_p` cores of §4);
* `haux` -- the per-datum auxiliary-class obligation
  `Work.SSGRoute.ZConstruction.AuxExistsGap`, which is *derivable* from the pairing gate and the
  unmixed realisation gate (`auxExistsGap_of_pairing_and_unmixed`, proved);
* `hcc` -- the **Case C gate** `Work.SSGRoute.CaseCGate`: the `z`-data for the data
  whose prescribed `cs(S)`-local data *and* whose junk ramification both span the coefficient module
  (the only branch of the case analysis of `ZConstruction/AuxExistsGapInduction.lean` in which
  neither the peeling step nor the line decomposition avoiding the junk span applies). -/
theorem shafarevich_z_construction_of_auxGap_and_caseC (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s)
    (hmup : MupGate (p := p) K)
    (haux : ∀ (Λ' : IntermediateField k Ω) [FiniteDimensional k Λ'] [IsGalois k Λ']
      (S' : Finset (ValuationSubring Ω)), (∀ A ∈ S', SSGRoute.IsFinPlace k A) →
      ZConstruction.AuxExistsGap (p := p) K Λ' S')
    (hcc : CaseCGate (p := p) K) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  letI : DistribMulAction (K ≃ₐ[k] K) (ZMod p) :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  letI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p) := ⟨fun _ _ _ => rfl⟩
  obtain ⟨z, hz⟩ :=
    z_data_general_of_auxGap_and_caseC (p := p) (k := k) (Ω := Ω)
      hmup haux hcc Λ S ⟨hKΛ, ζ, hζ, hζK, hSfin, hSdisj, hSram⟩ E y
      ⟨hy, hyc, hyS, hyT, hy0, hyinf⟩
  exact shafarevich_z_construction_of_zData hKΛ S y sec hsec ⟨z, hz⟩

/-!
## NOTE (session 22): the node from the *inertia-killing* of the transfer -- a second route

The sixth (and only substantial) conjunct of `shafarevich_z_construction` at a finite place `B ∉ cs(S)`
split in `Λ` is, by `Work.SSGRoute.exists_V_of_cyclic_transfer` and
`Work.SSGRoute.isCyclic_transfer_of_exists_V`, *equivalent* to the cyclicity of the image of the
transfer `X_z δ = ∑_{s : Gal(K/k)} s • z ((sec s)⁻¹ δ sec s)` on `decomp k B`.  There are now three
sufficient conditions for it, in increasing generality:

1. `z` vanishes on the inertia of every `G_k`-conjugate of `B`
   (`Work.SSGRoute.transfer_vanishes_of_unramified`); equivalently, by the proved
   `Work.SSGRoute.ZConstruction.transfer_eq_zero_of_vanishes_on_conjugate_inertia`, `X_z` kills the
   inertia of `B`;
2. **`X_z` itself kills the inertia of `B`** — strictly weaker, since it constrains only the *sum* of
   the local components of `z` at the conjugates of `B`, not each of them
   (`Work.SSGRoute.ZConstruction.exists_V_of_transfer_inertia_vanishing`,
   `ZConstruction/transferInertiaVanishing.lean`, proved this session);
3. Schmidt--Wingberg's sharpened condition (b) — incomparable with 1 and 2, and the only one that
   covers the case in which a single conjugate of `B` carries the ramification
   (`Work.SSGRoute.transfer_clause_of_single_conjugate`).

The file `ZConstruction/TransferReduction.lean` (proved this session, axiom-clean) turns (2) into a
reduction of the whole node: the node's conclusion follows from a cochain `z` with the five elementary
clauses and the inertia-killing condition (2)
(`shafarevich_z_construction_of_inertiaKillingZData`), and — taking `z` to be the extension of `y` by
`0` off `G_K` — from the *datum alone*:

    `shafarevich_z_construction_of_transferInertia`:
      if `∀ B ∉ cs(S), IsSplitIn k Λ B, X_y` kills the inertia of `B`, then the node holds.

No arithmetic input whatsoever is needed for this; the residual content of the node is exactly the
difference between that condition on `y` and the hypotheses `ZHyp` on `y`.  The régime in which `y`
vanishes on the inertia of every conjugate of every completely decomposed place outside `cs(S)`
(which contains the paper's hypothesis (H1)) is the corollary
`shafarevich_z_construction_of_conjugateUnramified`, and the (H1) régime itself is
`shafarevich_z_construction_of_unramifiedOutside`.

**The condition is not automatic, and this is where the node's content sits.**  The maximal pro-`p`
quotient of the decomposition group `D_B ≅ Gal(Ω_B/k_B)` of a place of residue characteristic `ℓ ≠ p`
is *not* pro-cyclic: the inertia group is an extension of the pro-`ℓ` wild part by the tame part
`∏_{q ≠ ℓ} Ẑ_q`, whose pro-`p` quotient is `Z_p`, so `D_B^{pro-p}` is a two-generator group.  Hence
the image of the transfer can a priori be two-dimensional, and the inertia-killing condition is a
genuine restriction (it is *not* implied by the mere fact that `E` is a `p`-group).  In the language
of `ZConstruction/NOTE_session21.lean` the "junk" ramification of `y` at the `Λ`-split places outside
`cs(S)` contributes to `X_y (I_B)` through the conjugates of `B`, and the two ways known of making
that contribution vanish are the "unramified" condition (1) and the paper's §4 construction, whose
class `z` satisfies (b) but not (2).

**Caveat (see §5 of `ZConstruction/NOTE_session22.lean`).**  This is *not* a weakening of the node's
obligation: there are data for which no cochain satisfies (1)—(5) together with (2), while the node
holds (e.g. `k = K = Λ = ℚ`, `p = 2`, `E = ZMod 2`, `S = {2,3}`, `y` the quadratic character of
`ℚ(√17)`); and data for which (2) *is* satisfiable and easy (`E = F_3²` over `ℚ`, `S = {3}`), where
the p. 18 obstacle of `NOTE_session21` is absent.  Neither route subsumes the other; what the new one
buys is a *checkable* normal form of the sixth conjunct (the transfer kills the inertia) and a
reduction of the node to a condition on the datum, with no arithmetic input at all.
-/

/-- **The node under one additional hypothesis on the datum: its transfer kills the inertia of the
completely decomposed places outside `cs(S)`.**

This is `Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_transferInertia` stated in the
node's own hypothesis list (the hypotheses `hyT`, `hy0` are not needed by this route, the datum
satisfying them being used only to construct the `z`-data of the older route). -/
theorem shafarevich_z_construction_of_transferInertia (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (_hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (_hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s : K ≃ₐ[k] K, SSGRoute.res k K (sec s) = s)
    (htransfer : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
      ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k B → SSGRoute.IsInertia k B σ →
        Work.SSGRoute.transfer y sec σ = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  exact ZConstruction.shafarevich_z_construction_of_transferInertia (p := p) (k := k) (Ω := Ω)
    (K := K) (Λ := Λ) hKΛ E S y hy hyc hyS hyinf sec hsec htransfer

/-!
## NOTE (session 28): the `G_Λ`-killing régime (a route to conjunct 6 with no condition (b))

`Submission/Work/SSGRoute/ZConstruction/ClauseSixKillLambda.lean` (imported above, sorry-free,
axiom-clean) proves a new *formal* sufficient condition for the node's sixth conjunct, whose proof
uses neither Schmidt--Wingberg's sharpened condition (b) nor any arithmetic input:

* `Work.SSGRoute.transfer_eq_zero_of_mem_fixingSubgroup` -- if a cochain `z` vanishes on the whole
  subgroup `G_Λ = Λ.fixingSubgroup`, then the transfer vanishes at **every** `δ ∈ G_Λ`.  Reason:
  `G_Λ` is normal in `G_k` (`Work.SSGRoute.fixingSubgroup_normal_of_isGalois'`; it is the kernel of
  the restriction `res k Λ`), so every conjugate `(sec s)⁻¹ δ sec s` of `δ ∈ G_Λ` again lies in `G_Λ`,
  where `z` vanishes -- all terms of the transfer are `0`.
* `Work.SSGRoute.exists_V_of_kills_fixingSubgroup` / `clause_six_of_kills_fixingSubgroup` -- the
  sixth conjunct at a place `B` split in `Λ`, with the **explicit** witness `V = G_Λ`: `G_Λ` is open
  (`Λ` being finite over `k`), `D_B ⊓ G_Λ` is normalised by `D_B` (normality of `G_Λ` in `G_k`), and
  it equals `D_B` for `B` split in `Λ`.

Consequently the node follows from the five elementary clauses of its conclusion (which hold for the
candidate `z` = `y` extended by `0` off `G_K`,
`Work.SSGRoute.ZConstruction.zClauses_of_agrees_on_fixingSubgroup`) together with the single extra
condition `z` kills `G_Λ`.  The theorem below states this in the node's own hypothesis list, with the
extra condition imposed on the datum itself (`y` kills `G_Λ`, i.e. `y` factors through
`Gal(Λ|k)`).

## ADDENDUM (session 28): the delegation of the SW §4 assembly came back `declared_false`

The (not-yet-formalised) assembly of the four pieces of the odd-`p` core into
`Work.SSGRoute.sw_z_exists_odd_sketch` was delegated this session (as
`Work.SSGRoute.ZConstruction.sw_z_exists_odd_of_counting`, with the level-`K` local Tate system, the
product formula and the counting inequality as hypotheses).  The prover declared it **false**: the
hypotheses imply no *orthogonality* of the prescribed datum, while the level-`K` realisation
`ZDataMup.tatePoitou_h1_realisation_of_counting` consumes exactly that orthogonality; and for a datum
`y` ramified outside `cs(S)` (the `hyram` case) the product formula does not give it.

That is the "gap" of `ZConstruction/NOTE_session21.lean` §3, re-derived; in Schmidt--Wingberg's
setting `y ∈ H¹(k_S|K, A)`, i.e. `y` is unramified outside `cs(S)`, whereas the formalised `ZHyp`
(and `hyram`) allow and assert ramification at the `Λ`-split places outside `cs(S)`.  See
`PING_sw_z_exists_odd_hyram_gap.md` (workspace root) for the record and the recommendations.

**Bearing on this node.**  The node's sixth conjunct is the `∃ V`/transfer-cyclicity form, strictly
weaker than Schmidt--Wingberg's (b)-clause, and it is reached *without* (b) by both
`Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_transferInertia` (session 22) and
`Work.SSGRoute.shafarevich_z_construction_of_killsLambda` (below).  The obligation recorded in
`ZConstruction/ZDataGeneral.lean` (`Work.SSGRoute.z_data_general_of_ramified`) is, however, the
`(b)`-form, so it may be *stronger than the node needs* in the `hyram` régime; a future session
should consider re-pointing the node's proof at a realisation statement whose conclusion is the
`V`-clause only (session 21's `AuxRealisationT` is the Poitou--Tate-matched version).  The node's
*statement* is not affected, and no part of this addendum refutes it.
-/

/-- **The node under one additional hypothesis on the datum: `y` vanishes on `G_Λ`.**

This is the `G_Λ`-killing régime of `Work.SSGRoute.ZConstruction.clause_six_of_kills_fixingSubgroup`:
with `z` := the extension of `y` by `0` off `G_K` (five elementary clauses,
`Work.SSGRoute.ZConstruction.zClauses_of_agrees_on_fixingSubgroup`), the hypothesis `hyΛ` makes `z`
vanish on the *whole* open subgroup `G_Λ = Λ.fixingSubgroup`, so every term of the transfer
`X δ = ∑_s s • z ((sec s)⁻¹ δ sec s)` at a place `B` split in `Λ` is `0` and the sixth conjunct holds
with the explicit witness `V = G_Λ`.

Neither the sharpened condition (b) of Schmidt--Wingberg's §4 nor any other arithmetic input is used;
the hypotheses `hyT`, `hy0` (used by the older routes) are not needed here. -/
theorem shafarevich_z_construction_of_killsLambda (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (_hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (_hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hyΛ : ∀ σ ∈ Λ.fixingSubgroup, y σ = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s : K ≃ₐ[k] K, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  classical
  set Z : (Ω ≃ₐ[k] Ω) → E := fun σ => if σ ∈ K.fixingSubgroup then y σ else 0 with hZdef
  have hZY : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ K.fixingSubgroup → Z σ = y σ := by
    intro σ hσ
    rw [hZdef]
    simp only [hσ, if_pos]
  have hZΛ : ∀ σ ∈ Λ.fixingSubgroup, Z σ = 0 := by
    intro σ hσ
    rw [hZY σ (IntermediateField.fixingSubgroup_le hKΛ hσ), hyΛ σ hσ]
  obtain ⟨h1, h2, h3, h4, h5, _⟩ :=
    ZConstruction.zClauses_of_agrees_on_fixingSubgroup (p := p) (k := k) (Ω := Ω) (K := K)
      (Λ := Λ) E S y Z hZY hy hyc hyS hyinf sec hsec
  exact ZConstruction.shafarevich_z_construction_of_VClauseZData (p := p) (k := k) (Ω := Ω)
    (K := K) (Λ := Λ) hKΛ E S y sec hsec
    ⟨Z, h1, h2, h3, h4, h5,
      fun B hB hnotS hsplitΛ => clause_six_of_kills_fixingSubgroup S hZΛ B hB hnotS hsplitΛ⟩

/-!
## NOTE (session 23): the stable-line regime, the vanishing-on-`cs(S)` regime, and the spanning reduction

`Submission/Work/SSGRoute/ZConstruction/LineAndZeroWitness.lean` (imported above; sorry-free,
axiom-clean) proves two new sufficient conditions for the conclusion of this theorem, both without
any arithmetic input, together with the algebra they rest on:

* `Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_csLine` --- **if the *local data at
  `cs(S)`* of the datum lies in a `Gal(K|k)`-stable line `⟨v⟩ ≤ E`** (`s • v ∈ ⟨v⟩` for all
  `s : Gal(K|k)`, and `y σ ∈ ⟨v⟩` for every `σ` in a local group `decomp k B ⊓ G_K` with `B`
  conjugate into `S`), then the node's conclusion holds.  Conjuncts 1--5 are immediate for the
  candidate `z`; for conjunct 6, every summand `s • z ((sec s)⁻¹ δ sec s)` of the transfer at a place
  split in `Λ` lies in `⟨v⟩` (the value by construction, and `⟨v⟩` is stable), so the transfer's
  image is a subgroup of the cyclic group `⟨v⟩`, hence cyclic, and
  `Work.SSGRoute.exists_V_of_cyclic_transfer` produces the required `V`.

  The point of the *local* form (as opposed to requiring all the values of `y` to lie in `⟨v⟩`,
  which is the special case `shafarevich_z_construction_of_stableLine`) is that **the six conjuncts
  mention the datum only in conjunct 3**, so the datum may be replaced by *any* cochain agreeing with
  it on the `cs(S)`-local groups --- in particular by its projection onto the span of those values
  (`Work.SSGRoute.ZConstruction.exists_projection_onto_line`, built from `Submodule.exists_isCompl`
  on the line `(ZMod p) ∙ v`).  Hence:

  > the node holds for **every datum whose prescribed local data is one-dimensional**; the residual
  > obligation is the *spanning* case, in which the `cs(S)`-local data spans a subspace of
  > `𝔽_p`-dimension `≥ 2` not contained in a `Gal(K|k)`-stable line.

  (For `|Gal(K|k)| ≤ 2` the action on any line is multiplication by a scalar, so *every* line is
  stable and the residual case is exactly "the `cs(S)`-local data spans a subspace of dimension
  `≥ 2`".)  The supporting algebra is `Work.SSGRoute.ZConstruction.exists_zmultiples_generator`:
  the image of a map additive on a subgroup and taking values in a cyclic subgroup is generated by
  one of its values, by `AddSubgroup.le_zmultiples_iff`.

* `Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_zeroOnCs` --- if the datum vanishes on
  the local group `decomp k B ⊓ G_K` of every place conjugate into `S`, then `z := 0` witnesses the
  conclusion (conjunct 6 with `V = ⊤`, the transfer vanishing identically).  Corollary
  `Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_noResidualPlace`: by the hypothesis
  `hy0`, a place `B` conjugate into `S` can carry a non-zero value of `y` only if it is **split in
  `K` and away from `p`** (`¬ B.valuation (p:Ω) < 1`), so if no such place exists the node holds
  outright.

* `Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_junkLocalDataLine` --- the dual regime,
  in which the **junk** local data (`y`'s values on `decomp k Q ⊓ G_K` for `Q ∉ cs(S)` split in `Λ`)
  lies in a stable line.  Conjunct 6 is decided entirely by those values, so no hypothesis on the
  `cs(S)`-local data is needed here; this strictly generalises `..._of_stableLine`.  The engine is
  `Work.SSGRoute.ZConstruction.exists_V_of_transfer_of_junkData_line`.

* `Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_transferCyclicDatum` --- **the weakest
  form of the node's obligation**: since conjunct 6 is *equivalent* to the cyclicity of the transfer
  on `decomp k B`, the candidate `z :=` (the extension of `y` by `0` off `G_K`) already satisfies it
  as soon as the transfer of **`y`** has cyclic image at the junk places.  This is a condition on the
  *datum*, with no search over `z`, and it strictly generalises the régime of
  `shafarevich_z_construction_of_transferInertia` (killing the inertia forces cyclicity) as well as
  the line régime above.  What is left in the residual case is only the *modification* of `z` by the
  quotient-level freedom `δ ∈ Hom(G_K/H, E)` of §3 of `ZConstruction/NOTE_session23.lean`.

  Its sharpest form, `Work.SSGRoute.shafarevich_z_construction_of_cyclicTransferOnRamified`, needs the
  transfer to be cyclic only at the places `B` for which *some conjugate of `B` carries a non-zero
  value of `y` on its inertia* (else the transfer kills `I_B` and the pro-cyclicity of
  `decomp k B / I_B` gives cyclicity).  Since `y` is locally constant, this is **finitely many**
  places --- the form of the obligation in which the box principle of Schmidt--Wingberg §4 applies.
  The module-level engine is
  `Work.SSGRoute.ZConstruction.isZConclusion_of_cyclicTransferOnRamified`, stated with the predicate
  `Work.SSGRoute.ZConstruction.IsZData5` (the five elementary conjuncts) for the hypothesis.

**Gate status (session 23).**  The level-`K` pairing gate `Work.SSGRoute.AuxPairingGate (p := p) K` for
odd `p` now has a `sorry`-free proof in `ZConstruction/levelK_pairing_productFormula.lean`, but that
module currently fails to build because of a duplicate-declaration clash in its import chain
(`Work.SSGRoute.ZDataMup.exists_cocycle_of_lcHoms` is declared twice, in
`ZDataMup/finrank_lcCocycleImage_eq_one_of_not_residueChar_proj.lean` and in
`ZDataMup/mupH1locLcHoms.lean`).  It is therefore **not** imported here; once the sibling lane
resolves the clash, the hypothesis `hP : AuxPairingGate (p := p) K` of
`shafarevich_z_construction_of_realisationT_gates` can be discharged by
`ZConstruction.levelK_pairing_productFormula p hp k Ω K ζ hζ hζK`.  See
`ZConstruction/NOTE_session23.lean` §7.

* `Work.SSGRoute.ZConstruction.IsZConclusion S sec y z` names the six-fold conjunction with the
  datum and the witness explicit (so `∃ z, IsZConclusion S sec y z` *is* the node's conclusion), and  `...ZConstruction.transfer_add` records that the transfer is additive in the cochain.  These are
  the vocabulary of the assembly lemma delegated this session,
  `Work.SSGRoute.ZConstruction.isZConclusion_add_of_disjointTransfer`: **the conclusion is closed
  under sums of witnesses whose transfers have disjoint support** (for every place `B ∉ cs(S)` split
  in `Λ`, one of the two transfers vanishes on `decomp k B`; then the `V` of the other summand
  serves for the sum, since the summands' transfer images at `B` are not mixed).  This is the formal
  half of the "rank-one decomposition" route to the node: write the local data as a sum of
  one-dimensional pieces, realise each by a line-valued witness (`..._of_csLine`), and arrange the
  new ramification primes (Chebotarev) so that the pieces' transfer supports are disjoint.

**The residual case.**  The two regimes above leave exactly the data for which there is a place

  `B ∈ cs(S)` with `IsSplitIn k K B`, `¬ B.valuation (p:Ω) < 1`, and `y ≠ 0` on `decomp k B ⊓ G_K`

(for a minimal `S` such a `B` is ramified in `Λ` and unramified in `K`; `hyT` then makes `y`
unramified at `B` and `y (decomp k B ⊓ G_K)` cyclic), and for which the values of `y` do not lie in
a single `Gal(K|k)`-stable line.  That is the case in which Schmidt--Wingberg §4 has to act, and it
is where the arithmetic of the gates (`MupGate`, the realisation, the p. 18 chase) remains to be
done.  Nothing here closes the node; the two regimes are recorded because they are *arithmetic-free*
branches of its proof.

Equivalently (and this is the reason the local form of the first regime matters): the residual case
is the **spanning** case --- the `cs(S)`-local data of `y` spans a subspace of `E` of dimension
`≥ 2`.  Everything below that dimension is now discharged without arithmetic.

More precisely, by `Work.SSGRoute.y_mem_zmultiples_on_csLocalGroup` each `cs(S)`-place contributes a
*single* line (a cyclic group `y (decomp k B ⊓ G_K) = ⟨y g_B⟩`), and by `hy0` only the places of
`cs(S)` that are split in `K` and away from `p` contribute at all.  Hence the residual case is
exactly:

* **two or more** such places whose generator values `y g_B` are not contained in a common
  `Gal(K|k)`-stable line, or
* a **single** such place whose line `⟨y g_B⟩` is not `Gal(K|k)`-stable (no other line can serve,
  since `y (decomp k B ⊓ G_K)` generates that line).

**Correction to the record of session 22 (§5(b) of `ZConstruction/NOTE_session22.lean`).**  The
example given there to show that the inertia-killing condition can be unsatisfiable while the node
holds (`k = K = Λ = ℚ`, `p = 2`, `E = ZMod 2`, `S = {2,3}`, `y` the quadratic character of
`ℚ(√17)`) does **not** satisfy the node's hypotheses: with `K = k` we have `IsSplitIn k K B` for
every `B`, so `hy0` at the place `B` over `3` reduces to `false ∨ B.valuation (2:Ω) < 1`, which
holds since `3 ≠ 2`, forcing `y ≡ 0` on `D_3` --- whereas `y (Frob_3) = (17/3) = -1 ≠ 0`.  Hence
that datum is not an instance of the node, and the conclusion drawn from it (that the local routes
of session 22 are *incomparable*) rests on an invalid example.  The theorem proved in session 22
(`Work.SSGRoute.shafarevich_z_construction_of_transferInertia`) is of course unaffected; what is
invalid is only the assertion that its hypothesis is *unsatisfiable* on data for which the node
holds.
-/

/-- **The node in the Galois-stable line regime.**

This is `Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_stableLine` stated in the node's
own hypothesis list, with the two additional hypotheses on the datum: `v : E` spans a line stable
under `Gal(K|k)`, and `y` takes its values in that line. -/
theorem shafarevich_z_construction_of_stableLine (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (v : E) (hstable : ∀ s : K ≃ₐ[k] K, s • v ∈ AddSubgroup.zmultiples v)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hyv : ∀ σ ∈ K.fixingSubgroup, y σ ∈ AddSubgroup.zmultiples v)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) :=
  ZConstruction.shafarevich_z_construction_of_stableLine p k Ω K Λ hKΛ ζ hζ hζK E v hstable
    S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf hyv sec hsec

/-- **The node when the *local data at `cs(S)`* lies in a Galois-stable line.**

This is the strengthened form of `shafarevich_z_construction_of_stableLine`: the values of `y` are
required to lie in the stable line `⟨v⟩` only on the local groups `decomp k B ⊓ G_K` of the places
`B` conjugate into `S`, not everywhere.  Indeed the six conjuncts of the conclusion mention the datum
only in conjunct 3, so the datum may be replaced by its projection onto the span of its `cs(S)`-local
values — which is line-valued as soon as that span is contained in `⟨v⟩`
(`Work.SSGRoute.ZConstruction.exists_projection_onto_line`).

Consequently the node holds for **every datum whose prescribed local data is one-dimensional**; the
residual obligation is the *spanning* case in which that data spans a subspace of `E` of
`𝔽_p`-dimension `≥ 2` not contained in a `Gal(K|k)`-stable line.  (For `|Gal(K|k)| ≤ 2` every line of
`E` is stable, since the action on a line is multiplication by a scalar, so there the residual case is
exactly "the `cs(S)`-local data spans a subspace of dimension `≥ 2`".) -/
theorem shafarevich_z_construction_of_csLine (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (v : E) (hstable : ∀ s : K ≃ₐ[k] K, s • v ∈ AddSubgroup.zmultiples v)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hyv : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ ∈ AddSubgroup.zmultiples v)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) :=
  ZConstruction.shafarevich_z_construction_of_csLine p k Ω K Λ hKΛ ζ hζ hζK E v hstable
    S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf hyv sec hsec

/-- **The node from the cyclicity of the transfer of the datum itself.**

This is the weakest form of the node's obligation: since conjunct 6 is *equivalent* to the cyclicity
of the transfer on `decomp k B` (`Work.SSGRoute.exists_V_of_cyclic_transfer` and
`Work.SSGRoute.isCyclic_transfer_of_exists_V`), the candidate `z :=` (the extension of `y` by `0` off
`G_K`) already satisfies it as soon as the transfer of **`y`** has cyclic image at the junk places —
a condition on the *datum* alone, with no search over `z`.

This strictly generalises the régime of `Work.SSGRoute.shafarevich_z_construction_of_transferInertia`
(killing the inertia forces cyclicity) and that of `shafarevich_z_construction_of_csLine` (line-valued
local data makes the transfer's image a subgroup of a line).  What remains in the residual case is
only the *modification* of `z` by the quotient-level freedom `δ ∈ Hom(G_K/H, E)` described in
`ZConstruction/NOTE_session23.lean` §3. -/
theorem shafarevich_z_construction_of_transferCyclicDatum (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s)
    (hcyc : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
      ∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B,
        Work.SSGRoute.transfer y sec δ ∈ AddSubgroup.zmultiples (Work.SSGRoute.transfer y sec g)) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) :=
  ZConstruction.shafarevich_z_construction_of_transferCyclicDatum p k Ω K Λ hKΛ ζ hζ hζK E
    S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf sec hsec hcyc

/-- **The node from the cyclicity of the transfer of the datum at the places where it is ramified.**

The sharpest form of the node's obligation available on disk: the transfer of `y` need have cyclic
image only at the places `B ∉ cs(S)` split in `Λ` for which *some conjugate of `B` carries a non-zero
value of `y` on its inertia*.  (If no conjugate does, the transfer kills the inertia of `B` and its
image there is cyclic by the pro-cyclicity of `decomp k B / I_B`.)

This is `Work.SSGRoute.ZConstruction.isZConclusion_of_cyclicTransferOnRamified` stated in the node's
own hypothesis list (with `z` instantiated to the extension of `y` by `0` off `G_K`).  Since `y` is
locally constant, its ramification outside `cs(S)` is finite, so this condition has to be checked at
*finitely many* places --- which is what makes the box principle of Schmidt--Wingberg §4 applicable. -/
theorem shafarevich_z_construction_of_cyclicTransferOnRamified (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s)
    (hcyc : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
      (∃ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q ∧
        ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k Q σ ∧ y σ ≠ 0) →
      ∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B,
        Work.SSGRoute.transfer y sec δ ∈ AddSubgroup.zmultiples (Work.SSGRoute.transfer y sec g)) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  classical
  let Z : (Ω ≃ₐ[k] Ω) → E := fun σ => if σ ∈ K.fixingSubgroup then y σ else 0
  have hZy : ∀ σ, σ ∈ K.fixingSubgroup → Z σ = y σ := by
    intro σ hσ
    show (if σ ∈ K.fixingSubgroup then y σ else 0) = y σ
    rw [if_pos hσ]
  obtain ⟨hZ1, hZ2, hZ3, hZ4, hZ5, hZtr⟩ :=
    ZConstruction.zClauses_of_agrees_on_fixingSubgroup p k Ω K Λ E S y Z hZy hy hyc hyS hyinf
      sec hsec
  have h5 : ZConstruction.IsZData5 (K := K) (Λ := Λ) (E := E) S sec y Z :=
    ⟨hZ1, hZ2, hZ3, hZ4, hZ5⟩
  have hcyc' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
      (∃ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q ∧
        ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k Q σ ∧ Z σ ≠ 0) →
      ∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B,
        Work.SSGRoute.transfer Z sec δ ∈ AddSubgroup.zmultiples (Work.SSGRoute.transfer Z sec g) := by
    intro B hB hnotconj hsplitΛ htrig
    obtain ⟨Q, hQ, σ, hσK, hσI, hσne⟩ := htrig
    have hσne' : y σ ≠ 0 := by
      rw [hZy σ hσK] at hσne
      exact hσne
    obtain ⟨g, hg, hgc⟩ := hcyc B hB hnotconj hsplitΛ ⟨Q, hQ, σ, hσK, hσI, hσne'⟩
    have hsplitK : SSGRoute.IsSplitIn k K B :=
      le_trans hsplitΛ (IntermediateField.fixingSubgroup_le hKΛ)
    exact ⟨g, hg, fun δ hδ => by
      rw [hZtr B hsplitK δ hδ, hZtr B hsplitK g hg]
      exact hgc δ hδ⟩
  exact ⟨Z, ZConstruction.isZConclusion_of_cyclicTransferOnRamified p k Ω K Λ hKΛ E S sec hsec
    y Z h5 hcyc'⟩

/-- **The node when the *junk* local data lies in a `Gal(K|k)`-stable line.**

Conjunct 6 of the conclusion concerns the transfer at a place `B ∉ cs(S)` split in `Λ`, and the
arguments of the summands are conjugates of elements of `decomp k B`, i.e. elements of the
decomposition groups of the conjugates of `B`.  So conjunct 6 is decided by the values of the cochain
on the decomposition groups of the *junk* places (`B` outside `cs(S)` and split in `Λ`): if those all
lie in one stable line `⟨v⟩`, then the transfer's image at every junk place is a subgroup of `⟨v⟩`,
hence cyclic, and the candidate `z :=` (the extension of `y` by `0` off `G_K`) witnesses the node.

**No condition on the `cs(S)`-local data is needed** (conjunct 3 is satisfied by that candidate
identically), so this strictly generalises `shafarevich_z_construction_of_stableLine`
(`Work.SSGRoute.ZConstruction.exists_V_of_transfer_of_junkData_line` is the engine; the conjugation
invariances of `IsFinPlace`, `IsSplitIn` and `IsConjPlace` are
`Work.SSGRoute.isFinPlace_smul_iff`, `Work.SSGRoute.isSplitIn_conj` and the accompanying lemma in the
same file). -/
theorem shafarevich_z_construction_of_junkLocalDataLine (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (v : E) (hstable : ∀ s : K ≃ₐ[k] K, s • v ∈ AddSubgroup.zmultiples v)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hval : ∀ Q : ValuationSubring Ω, SSGRoute.IsFinPlace k Q →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A Q) → SSGRoute.IsSplitIn k Λ Q →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k Q → y σ ∈ AddSubgroup.zmultiples v)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  classical
  let Z : (Ω ≃ₐ[k] Ω) → E := fun σ => if σ ∈ K.fixingSubgroup then y σ else 0
  have hZy : ∀ σ, σ ∈ K.fixingSubgroup → Z σ = y σ := by
    intro σ hσ
    show (if σ ∈ K.fixingSubgroup then y σ else 0) = y σ
    rw [if_pos hσ]
  obtain ⟨hZ1, _, hZ3, hZ4, hZ5, _⟩ :=
    ZConstruction.zClauses_of_agrees_on_fixingSubgroup p k Ω K Λ E S y Z hZy hy hyc hyS hyinf
      sec hsec
  have hZadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, Z (g * h) = Z g + Z h := by
    intro g hg h hh
    rw [hZy (g * h) (K.fixingSubgroup.mul_mem hg hh), hZy g hg, hZy h hh, hy g hg h hh]
  have hZloc : SSGRoute.IsLocConstOn K.fixingSubgroup Z := by
    obtain ⟨U, hUopen, hUc⟩ := hyc
    refine ⟨U, hUopen, ?_⟩
    intro g hg u hu huK
    rw [hZy (g * u) (K.fixingSubgroup.mul_mem hg huK), hZy g hg]
    exact hUc g hg u hu huK
  have hvalZ : ∀ Q : ValuationSubring Ω, SSGRoute.IsFinPlace k Q →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A Q) → SSGRoute.IsSplitIn k Λ Q →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k Q → Z σ ∈ AddSubgroup.zmultiples v := by
    intro Q hQ hnc hs σ hσK hσd
    rw [hZy σ hσK]
    exact hval Q hQ hnc hs σ hσK hσd
  refine ⟨Z, hZ1, hZloc, hZ3, hZ4, hZ5, ?_⟩
  intro B hB hnotconj hsplitΛ
  exact ZConstruction.exists_V_of_transfer_of_junkData_line (K := K) (Λ := Λ) hKΛ S Z sec hsec
    hZadd hZloc hstable hvalZ B hB hnotconj hsplitΛ

/-- **The node when the datum vanishes on the local groups of the places of `cs(S)`.**

This is `Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_zeroOnCs` in the node's own
hypothesis list: the witness is `z := 0`. -/
theorem shafarevich_z_construction_of_zeroOnCs (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (h0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) :=
  ZConstruction.shafarevich_z_construction_of_zeroOnCs p k Ω K Λ hKΛ ζ hζ hζK E S hSfin hSdisj
    hSram y h0 sec hsec

/-- **The node when no place of `cs(S)` is both split in `K` and away from `p`.**

Here `hy0` forces the datum to vanish on the local groups of all the places conjugate into `S`; the
witness is again `z := 0`.  This is
`Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_noResidualPlace` in the node's own
hypothesis list. -/
theorem shafarevich_z_construction_of_noResidualPlace (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hres : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1))
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) :=
  ZConstruction.shafarevich_z_construction_of_noResidualPlace p k Ω K Λ hKΛ ζ hζ hζK E S hSfin
    hSdisj hSram y hy hyc hyS hyT hy0 hyinf hres sec hsec

theorem shafarevich_z_construction (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  -- the arithmetic core: Schmidt--Wingberg's auxiliary class `z`
  obtain ⟨z, hzadd, hzloc, hzagree, hzinv, hzS, hzram⟩ :=
    z_data_general p k Ω K Λ hKΛ ζ hζ hζK E S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf
  -- the elementary half: the transfer at the split-in-`Λ` places is cyclic
  exact shafarevich_z_construction_of_zData hKΛ S y sec hsec
    ⟨z, hzadd, hzloc, hzagree, hzinv, hzS, hzram⟩

/-! ## The endgame with the two named gates of the Poitou--Tate route

The node's obligation (the `sorry` of `Work.SSGRoute.z_data_general_of_ramified`,
`ZConstruction/ZDataGeneral.lean`) is *exactly* the pair of gates

* `Work.SSGRoute.MupGate (p := p) K` -- the one-dimensional case of the `z`-data at every pair
  `(Λ,S)` (the two μ_p cores `Work.SSGRoute.z_data_mup_core` for odd `p` and
  `Work.SSGRoute.shafarevich_z_data_two` for `p = 2`, via
  `Work.SSGRoute.mupGate_of_cores`, `ZConstruction/MupGate.lean`); and
* `Work.SSGRoute.AuxExists (p := p) K Λ S` -- the auxiliary class `ỹ` of §4 (Schmidt--Wingberg
  pp. 18--19; `ZConstruction/ZDataAux.lean`), whose own arithmetic is the level-`K` Poitou--Tate
  realisation (`ZConstruction/AuxExistsAssembly.lean`, sessions 18--25).

Both gates are *below* this node in the import DAG (`ZConstruction/`), so the node can be closed by
the corollary below as soon as they are sorry-free; this is `z_data_general_of_ramified_of_gates`
(`ZDataGeneral.lean`, proved) followed by the bridge `shafarevich_z_construction_of_zData`.

The sibling endgame of the Grünwald-with-escape route (`IsMupZData` + `IsAuxiliaryZData`, whose
induction `Work.SSGRoute.z_data_general_of_mup_and_aux_zsplit` lives in `ZSplit/Assembly.lean`) is
`Work.SSGRoute.shafarevich_z_construction_of_mup_and_aux`
(`ZConstruction/MupAuxWire.lean`); by `ZConstruction/NOTE_session26.lean` that route is at present
*above* this node in the import DAG and becomes available once the three import re-pointings listed
there are applied. -/
theorem shafarevich_z_construction_of_mupGate_and_auxExists (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hmup : MupGate (p := p) K) (haux : AuxExists (p := p) K Λ S)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  obtain ⟨z, hz⟩ :=
    z_data_general_of_ramified_of_gates (p := p) k Ω K Λ hKΛ ζ hζ hζK E S hSfin
      hSdisj hSram y hy hyc hyS hyT hy0 hyinf hmup haux
  exact shafarevich_z_construction_of_zData hKΛ S y sec hsec ⟨z, hz⟩

/-- **The node from the Grünwald spelling of the one-dimensional gate and the Poitou--Tate
auxiliary class.**

This is `Work.SSGRoute.shafarevich_z_construction_of_mupGate_and_auxExists` with the one-dimensional
gate fed by `Work.SSGRoute.IsMupZData` (the `ZVocab`/`ZSplit` spelling, the one the Grünwald-with-
escape lane proves via `Work.SSGRoute.z_data_mup_core` and
`Work.SSGRoute.shafarevich_z_data_two`) instead of by `Work.SSGRoute.MupGate`.  The two spells are
the same obligation (`Work.SSGRoute.ZConstruction.mupGate_iff_isMupZData`), so whichever route
proves the `μ_p` core can feed either endgame of the node. -/
theorem shafarevich_z_construction_of_isMupZData_and_auxExists (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hμ : IsMupZData p k Ω K) (haux : AuxExists (p := p) K Λ S)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  exact shafarevich_z_construction_of_mupGate_and_auxExists p k Ω K Λ hKΛ ζ hζ hζK E S hSfin
    hSdisj hSram y hy hyc hyS hyT hy0 hyinf
    ((ZConstruction.mupGate_iff_isMupZData (p := p) (k := k) (Ω := Ω) (K := K) ζ hζ hζK).mpr hμ)
    haux sec hsec


/-! ## The endgame with the `mu_p` cores taken from the fleet's twins (session 30)

`Work.SSGRoute.ZConstruction.mupGate_of_cores_H9` (`ZConstruction/TwinsEndgame.lean`) proves
`Work.SSGRoute.MupGate (p := p) K` from the two Kummer cores of the odd-`p` / `p = 2` lanes' own
files -- `Work.SSGRoute.H9.sw_odd_kummer_core_proved` and
`Work.SSGRoute.H9.shafarevich_z_data_two_kummerCore_proved` -- which carry the same statements as
this node's own `Work.SSGRoute.sw_odd_kummer_core` and
`Work.SSGRoute.shafarevich_z_data_two_kummerCore` but are being closed by their lanes.  The
corollary below is therefore the node with its **entire** `mu_p` side reduced to those two twins;
the only other input is the auxiliary-class obligation `Work.SSGRoute.AuxExists`. -/
theorem shafarevich_z_construction_of_twins_and_auxExists (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (haux : AuxExists (p := p) K Λ S)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0))  := by
  exact shafarevich_z_construction_of_mupGate_and_auxExists p k Ω K Λ hKΛ ζ hζ hζK E S hSfin
    hSdisj hSram y hy hyc hyS hyT hy0 hyinf
    (ZConstruction.mupGate_of_cores_H9 (p := p) (k := k) (Ω := Ω) (K := K)) haux sec hsec

end Work.SSGRoute

/-!

## STATE (session 5): the induction step of §4 proved in this vocabulary, and the route to the
## shared realisation obligation

**What was proved.**

* `Submission/Work/SSGRoute/ZConstruction/ZDataLevelStep.lean`
  (`Work.SSGRoute.hasZData_sum_of_level_data`): the **induction step of Schmidt--Wingberg §4
  (pp. 18--19)** in the `HasZData` vocabulary of this node.  Given
  - `HasZData K Λ S y₀ z₀` for the codimension-one summand (the induction hypothesis),
  - a finite Galois level `N ⊇ Λ` with `z₀ = 0` on `G_N` (available from
    `Work.SSGRoute.exists_fixingField_vanishing_finite`),
  - `HasZData K N S' yAux z₁` for the auxiliary class at the *enlarged* pair `(N, S')`
    (`S' = S ∪ {places over Ram(N|k)}`; every place ramified in `N` is conjugate into `S'`),
  - agreement of `yAux` with `y₁` on the decomposition groups of `cs(S)` and its vanishing on those of
    `cs(S') ∖ cs(S)`,
  the sum `z₀ + z₁` satisfies `HasZData K Λ S (y₀ + y₁)`.  The verification is the paper's case
  analysis: `Case (a)` at the places of `S' ∖ S` (where the paper's (b') for `z⁰` takes over),
  `Case (b1)` at the places split in `N` (the level change
  `Work.SSGRoute.kills_decomp_of_split_of_vanishes`), and `Case (b2)` at the places not split in `N`
  (where both summands kill the inertia, `z⁰` because a place ramified in `N` lies in `cs(S')`).  This
  replaces the *retracted* confinement route (`Submission/Work/SSGRoute/z_data_mup_level.lean`,
  `z_data_two_level.lean`), which asked the one-dimensional input to confine its ramification to a
  prescribed level and is false as stated.

* `Submission/Work/SSGRoute/ZConstruction/ZDataRealisation.lean`
  (`Work.SSGRoute.isZData_iff_hasZData`, `Work.SSGRoute.z_data_general_of_realisation`,
  `Work.SSGRoute.shafarevich_z_construction_of_realisation`): the node's obligation
  (`Work.SSGRoute.z_data_general`, and the target conclusion itself) follows from the *single*
  arithmetic input `Work.SSGRoute.IsRealisationInput p k Ω K` -- the Poitou--Tate degree-one
  realisation of the local data of a global class (the paper's class `ỹ`, pp. 18--19) -- through the
  sibling, complete induction of `Submission/Work/SSGRoute/ZSplit/` and the proved bridge
  `Work.SSGRoute.shafarevich_z_construction_of_zData` of this node.  The two predicates agree
  (`IsZData` and `HasZData` are the same six clauses; `IsZData` merely carries the two unused
  `Gal(K|k)`-action instances on `ZMod p`).

**Consequence.**  The node has exactly one kind of gap left: the *realisation* obligation
`IsRealisationInput` (together with the two one-dimensional statements
`Work.SSGRoute.z_data_mup_core`, `Work.SSGRoute.shafarevich_z_data_two`, which are proved modulo
`sw_z_exists_odd_sketch` resp. `shafarevich_z_data_two_kummerCore`).  The first is the content the
level-`K` layer of `Submission/Work/SSGRoute/ZSplit/` is building
(`ZSplit/LEVELK_STATUS.md`: the counting identity, the local Tate system with reciprocity, the
datum orthogonality, and the Poisson-type passage `krelaxed_realisation`), and the second is the
`A = μ_p` half of §4.

Note on the import order: `IsZData` (`IsYRealisation`, `IsRealisationInput`) is defined in
`Submission/Work/SSGRoute/shafarevich_theorem13.lean`, which lies *above* this file in the import
DAG (it imports this node); hence the rewriting above is recorded in a file above this one, and the
`sorry` of `ZDataGeneral.lean` cannot be discharged through the ZSplit route without a change of the
definition site of `IsZData`.
-/


/-!

## STATE (session 7): the obligation of this node is *exactly* the spanning gate

**What was proved this session** (`Submission/Work/SSGRoute/ZConstruction/ZDataReduction.lean`,
module `Submission.Work.SSGRoute.ZConstruction.ZDataReduction`, `sorry`-free and axiom-clean),
all in the `HasZData` vocabulary of this node, with `K`, `Λ`, `S` fixed:

* `Work.SSGRoute.csData K S y` -- the `𝔽_p`-span of the local data of `y` at the level-`K` local
  groups of the places conjugate into `S` (with `Work.SSGRoute.mem_csData`).  By
  `Work.SSGRoute.hasZData_congr_cs` this is the *only* datum of `y` that the `z`-data sees.
* `Work.SSGRoute.ZHyp.mapAdd` -- the hypotheses `ZHyp` on the datum are preserved by any *additive*
  map (so also by maps into a submodule, which is what the peeling below needs).
* **`Work.SSGRoute.hasZData_of_fixes_data`** -- the *peeling step*: if `π : E →ₗ E` fixes `y`
  pointwise on the local groups of `cs(S)`, then a `z`-data witness for the projected datum
  `π ∘ y` is already a `z`-data witness for `y`.  Taking `π` the projection onto a proper submodule
  containing `csData K S y` reduces the problem at `(Λ,S)` to the coefficient module
  `↥(csData K S y)` of strictly smaller dimension.
* `Work.SSGRoute.ZAmbient` -- the ambient hypotheses of the construction (including `μ_p ⊆ K`),
  and the two **gates**
  * `Work.SSGRoute.MupGate K Λ S` -- the `z`-data for `finrank (ZMod p) E ≤ 1` (the `A = μ_p`
    case), and
  * `Work.SSGRoute.SpanningGate K Λ S` -- the `z`-data for `finrank (ZMod p) E ≥ 2` when the local
    data of `y` *spans* `E` (`csData K S y = ⊤`).
* **`Work.SSGRoute.z_data_general_of_gates`** -- strong induction on `finrank (ZMod p) E`:
  `MupGate` (dimension `≤ 1`) + `SpanningGate` (`≥ 2`, spanning) imply the *full* `z`-data
  `∃ z, HasZData K Λ S y z` for every finite coefficient module and every datum satisfying `ZHyp`.

**Consequence.**  `Work.SSGRoute.z_data_general_of_ramified` (the only `sorry` of this node's
subtree, `ZConstruction/ZDataGeneral.lean`) is, after this session, *exactly* the conjunction of the
two gates:

* `Work.SSGRoute.MupGate` is **already available**: `Submission/Work/SSGRoute/ZConstruction/MupGate.lean`
  proves it from the two arithmetic cores that sit *below* this node,
  `Work.SSGRoute.z_data_mup_core` (odd `p`) and `Work.SSGRoute.shafarevich_z_data_two` (`p = 2`)
  (the two unused action instances of the target are supplied there by the trivial action, so no
  action is needed in the gates' statements).  Its axiom footprint is therefore that of the two
  cores -- `Work.SSGRoute.sw_z_exists_odd_sketch` and
  `Work.SSGRoute.shafarevich_z_data_two_kummerCore`, the *shared* arithmetic obligations of the
  fleet.
* `Work.SSGRoute.SpanningGate` is the genuine residue, and it is *the* place where Schmidt--Wingberg
  §4 enters: the local data of `y` spans `E`, so `y` is a surjective family of local data, and the
  construction has to move its ramification from the split-in-`Λ` places outside `cs(S)` onto new
  primes with cyclic local components (pp. 18--19: the auxiliary class `ỹ`, the Tate--Poitou
  degree-one realisation and the Hilbert-symbol product formula).

**What this buys.**  The non-spanning cases of the construction -- all coefficient modules whose
`cs(S)`-local data is a proper subspace, whatever its dimension -- are now discharged by pure linear
algebra and the elementary `z`-data calculus, with no arithmetic; and the one-dimensional case is
reduced to the two existing cores.  A prover of the spanning gate closes this node together with
`Work.SSGRoute.z_data_general_of_gates` and `Work.SSGRoute.mupGate_of_cores`, without touching the
rest of the development.

### Update (same session): the spanning gate is reduced as well, to the *auxiliary class* of p. 18

`Submission/Work/SSGRoute/ZConstruction/ZDataAux.lean` (imported above) proves the paper's induction
step for the spanning gate, so that the node's obligation becomes a single, classical statement:

* `Work.SSGRoute.exists_level_vanishing_finite` -- the level of a cochain in the action-free form
  (a finite dimensional Galois level `N ⊇ K` with `z = 0` on `G_N`).
* **`Work.SSGRoute.AuxExists K Λ S`** -- the auxiliary-class obligation of p. 18: for every finite
  Galois level `N ⊇ Λ` and every enlargement `S' ⊇ S` containing (up to conjugacy) the places
  ramified in `N`, every one-dimensional datum `y₁` at `(Λ,S)` admits a class `yAux` at `(N,S')`
  with the same local data as `y₁` on `cs(S)` and *vanishing* on the local groups of
  `cs(S') ∖ cs(S)`.  In the paper's notation this is the class `ỹ`.
* `Work.SSGRoute.z_data_of_spanning_of_aux` -- the spanning step: for `E = E₀ ⊕ L`
  (`Work.SSGRoute.line_complement_decomposition`), the induction hypothesis at `E₀` gives `z₀` and
  its level `N`; `ZConstruction.exists_finset_ramifiedPlaces` gives `S' ⊇ S` with the places
  ramified in `N`; `AuxExists` gives `yAux` for `y₁ = π₁ ∘ y`; the one-dimensional gate
  `MupGate` applied to `yAux` at `(N,S')` gives `z₁`; and the assembly
  `Work.SSGRoute.hasZData_sum_of_level_data` concludes `HasZData K Λ S y (z₀ + z₁)`.
* `Work.SSGRoute.z_data_general_of_mup_and_aux` and `Work.SSGRoute.spanningGate_of_mup_and_aux` --
  the full `z`-data, respectively `SpanningGate`, from `MupGate` and `AuxExists`.

**Conclusion for the node.**  The obligation `z_data_general_of_ramified` is *exactly*

  `Work.SSGRoute.MupGate`  +  `Work.SSGRoute.AuxExists`,

where the first is available below the node (`ZConstruction/MupGate.lean`: the two μ_p cores
`Work.SSGRoute.z_data_mup_core` and `Work.SSGRoute.shafarevich_z_data_two`) and the second is the
paper's p. 18 class `ỹ` -- the Tate--Poitou degree-one realisation of the prescribed local data
together with the diagram chase which shows the datum of a global class orthogonal to the dual
Selmer group.  In this workspace the underlying arithmetic is exactly the lane of
`Work.SSGRoute.ZDataMup.tatePoitou_h1_realisation` (`ZDataMup/tatePoitou_h1_realisation.lean`) and
of the level-`K` layer `Submission/Work/SSGRoute/ZSplit/levelK_*`.
-/

/-!

## NOTE (session 11): the Čebotarev new-prime step is now available *below* this node

`Submission/Work/SSGRoute/frobeniusClass_realisation_below.lean` (module
`Submission.Work.SSGRoute.frobeniusClass_realisation_below`, namespace
`Work.SSGRoute.FrobBelow`) is a verbatim *relocation below this node* of the Čebotarev
"new ramification prime" step of Schmidt–Wingberg §4 together with the ten place/ramification
lemmas it rests on (the block `shafarevich_theorem13.lean` lines 3044–3628, which lives *above*
this node):

* `Work.SSGRoute.FrobBelow.exists_isFrobAtPrime_notMem_finite`,
* `Work.SSGRoute.FrobBelow.map_res_decomp_eq_stabilizer_valuationRing`,
  `isSplitIn_iff_primesOver_ncard`,
  `not_isRamifiedIn_of_levelSub_le_fixingSubgroup`,
  `levelSub_le_fixingSubgroup_of_ramificationIdx_eq_one`,
  `isTrivialAtLevel_iff_mem_inertia_general`,
  `finite_setOf_primeUnder`, `finite_setOf_primeUnder_ramified`,
  `isFinPlace_of_comap_valuationSubringAtPrime`, `not_isConjPlace_of_notMem_primeUnder`,
* `Work.SSGRoute.FrobBelow.frobeniusClass_realisation`,
  `frobeniusClass_realisation_of_res_eq_one` (the step itself), and
* `Work.SSGRoute.FrobBelow.chebotarev_frobenius_split_below`, which is the statement of
  Piece 2 of the `μ_p` lane verbatim (`Work.SSGRoute.chebotarev_frobenius_split_sketch`) with
  the conditional Čebotarev input `hc : NK.Reconstruct.ChebotarevDensityInput k Ω` added.

The copies keep their names inside the new namespace, so a module importing both this file and
`shafarevich_theorem13` sees two independently named copies (no clash); all their imports are
below this node (checked on the transitive import closure), so the two arithmetic cores of the
`μ_p` lane — `Work.SSGRoute.sw_z_exists_odd_sketch` (`z_data_mup_arith.lean`, whose Piece 2 is a
`sorry` precisely because the proved step sits above the node) and
`Work.SSGRoute.shafarevich_z_data_two_kummerCore` — may import it.  The wiring of Piece 2 is then
a single `exact` (see the docstring of `chebotarev_frobenius_split_below`); it needs `hc` to be
carried by the core, exactly as in `Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split`.

-/

/-!

## STATE (session 13): the p. 18 interface, and the realisation rung below the node

**New files (both build green):**

* `Submission/Work/SSGRoute/ZConstruction/LevelKRealisationCounting.lean`
  (`Work.SSGRoute.ZConstruction.levelK_realisation_of_counting`,
  `Work.SSGRoute.ZConstruction.sum_subtype_eq_sum_finset`): the level-`K` degree-one realisation of
  prescribed local data, re-established with the level-`K` counting inequality as an **explicit
  hypothesis**.  The standing version of this rung
  (`ZDataMup/tatePoitou_h1_realisation.lean`, with the standing `sorry` `counting_localisation_le`)
  was *deleted from the workspace during this session* by the lane that owns it, after the lane
  established (see `ZDataMup/TATEPOITOU_STATUS.md`, "The counterexample") that the counting
  inequality is false without an `hSram`-type hypothesis on the place set; the module here is
  `sorry`-free and assumes nothing false, and its statement becomes the correct gate as soon as the
  counting inequality is supplied for a place set covering the places above `p` (and the places
  ramified in the auxiliary field).
* `Submission/Work/SSGRoute/ZConstruction/AuxRealisationHonest.lean`:
  * `Work.SSGRoute.ZConstruction.exists_realisation_of_orthogonalToDual` (odd `p`): that rung with
    the coboundary form of its agreement clause rewritten pointwise
    (`Work.SSGRoute.ZDataMup.sub_isCoboundaryOn_iff_eqOn`), i.e. pointwise agreement on the local
    groups of `cs(T)` plus unramifiedness at every finite place outside `cs(T)`, from the *honest*
    dual hypothesis `Work.SSGRoute.ZDataMup.IsOrthogonalToDual`;
  * `Work.SSGRoute.ZConstruction.exists_realisation_of_orthogonalToDual_odd`: the same with the
    *relaxation* and the *involution* clauses of `Work.SSGRoute.AuxRealisationExt` -- i.e. the
    *conclusion* of the gate `Work.SSGRoute.AuxRealisationNoInv`, with the honest dual hypothesis.

**The counting inequality is an explicit hypothesis** in both rungs (`hcount`), together with the
`hSram`-type hypothesis which makes it satisfiable; the node's own statement carries that
hypothesis for its place set `S`, so the intended instantiation has it.

**Delegated this session (both arithmetic-free):**

* `Work.SSGRoute.ZConstruction.auxDatum_orthogonalToDual`
  (`ZConstruction/auxDatum_orthogonalToDual.lean`): the p. 18 chase in its honest form --
  `IsOrthogonalToDual K pair T (auxDatum K S y₁)` under the side condition that no place of
  `cs(T'')∖cs(T)` is `Λ`-split.  This is the hypothesis consumed by the rung above; it replaces the
  relaxed-dual orthogonality of `auxDatum_orthogonal_of_productFormula`, which requires the local
  triviality of `b` at the `Λ`-split places outside `cs(T)` and therefore does *not* imply it.
* `Work.SSGRoute.ZConstruction.hasZData_sum_of_level_data_unram`
  (`ZConstruction/hasZData_sum_of_level_data_unram.lean`): the level step of §4 with the *vanishing*
  hypothesis on the auxiliary class replaced by inertia-killing at `cs(S')∖cs(S)` (which is the
  `hyT` clause of `ZHyp K N S' yAux`, hence free) plus the same side condition.

**The two delegated lemmas landed (`destroy`-free, see their modules):**
`Work.SSGRoute.ZConstruction.auxDatum_orthogonalToDual` and
`Work.SSGRoute.ZConstruction.hasZData_sum_of_level_data_unram`.  Both carry the side condition that
the places of `cs(T'')∖cs(T)` (resp. `cs(S')∖cs(S)`) are not `Λ`-split, which is *automatic* for the
intended choice `S' = S ∪ {representatives of Ram(N|k)}` (a place ramified in `N` is ramified in `Λ`
because `Λ ≤ N`).

**Why the interface has to be weakened (the finding of the session).**  `AuxExists` (and
`AuxExistsWeakened`, `ZConstruction/ZDataAux.lean`) require the auxiliary class to *vanish on the
local groups* of `cs(S')∖cs(S)`.  The realisation can only prescribe data at places of the base set,
and prescribing `0` at a new place is legitimate in Poitou--Tate exactly when the reciprocity sum
over the enlarged place set closes there: the term is `pair(y₁, b)` with `y₁` unramified at the new
place, so it vanishes iff `b` is unramified (respectively locally trivial) there or `y₁` is *trivial*
there.  The chase's dual family controls `b` only through the restricted product of the paper's
p. 18 diagram (`∏_T H¹ × ∏_{S'∖T} H¹/H¹_nr`), i.e. `b` runs over the classes unramified outside
`cs(T)` -- which forces the base set of the realisation to be `T` and yields unramifiedness, not
vanishing, at the new places.  The alternative is the paper's Čebotarev *choice* of the new primes
(so that `y₁` is trivial there); this is a genuine extra input, not a consequence of the hypotheses
as formalised.  See `ZConstruction/NOTE_p18_interface.lean` for the full account, including the
cascade: dropping the vanishing prescription also removes the derivation of `ZHyp.hy0` at the new
places, which is consumed by `MupGate` -- so the weakened route must weaken the one-dimensional gate
(the cores) as well.
-/


/-!

## NOTE (session 15): the honest p. 18 chase is closed, and the node's exact obligation

### 1. A no-go theorem

`Submission/Work/SSGRoute/ZConstruction/AuxChaseVacuity.lean` (imported above) proves

* `Work.SSGRoute.ZConstruction.unramified_outside_cs_of_chase_hypotheses`, and
* `Work.SSGRoute.ZConstruction.not_ramified_outside_cs_of_chase_hypotheses`,

namely: the hypothesis package of the honest p. 18 chase
(`Work.SSGRoute.ZConstruction.auxDatum_orthogonalToDual`: a level `N ⊇ Λ` with `y₁ = 0` on `G_N`,
a place set `T''` covering the places ramified in `N` up to level-`K` conjugacy, and the side
condition that a place of `T''` not level-`K`-conjugate to `T` is not split in `Λ`) is **inconsistent
with `y₁` being ramified outside `cs(S)`**: the `hyS` clause of `ZHyp` forces every such ramification
place to be `Λ`-split, while the side condition together with the covering hypothesis forbids exactly
that.

Since `Work.SSGRoute.z_data_general_of_ramified` carries the hypothesis `hyram` that the datum *is*
ramified outside `cs(S)`, the honest route to the auxiliary class — honest chase plus the honest
realisation `Work.SSGRoute.ZConstruction.exists_realisation_of_orthogonalToDual_odd`
(`ZConstruction/AuxRealisationHonest.lean`) — is closed.  The viable route is the *relaxed* one of
§2 above: the proved chase `Work.SSGRoute.auxDatum_orthogonal_of_productFormula`
(`ZConstruction/AuxChase.lean`) produces the orthogonality hypothesis of the gate
`Work.SSGRoute.AuxRealisationExt`, and
`Work.SSGRoute.auxExists_of_pairing_and_realisation_odd` assembles `Work.SSGRoute.AuxExists` from
that gate together with `Work.SSGRoute.AuxPairingGate`.

### 2. The exact obligation of this node

With that, the assembly of the node is complete on disk: `Work.SSGRoute.z_data_general` follows from
`Work.SSGRoute.MupGate` and `Work.SSGRoute.AuxExists` (`ZConstruction/ZDataAux.lean`,
`z_data_general_of_mup_and_aux`), `MupGate` is proved from the two arithmetic cores by
`Work.SSGRoute.mupGate_of_cores` (`ZConstruction/MupGate.lean`), and `AuxExists` is proved from the
pairing gate and the realisation gate by `auxExists_of_pairing_and_realisation_odd`.  The four
remaining obligations are therefore *all shared arithmetic*, none of them owned by this node:

1. `Work.SSGRoute.AuxPairingGate` (local Tate duality + Hilbert reciprocity + unramified
   orthogonality; the `ZDataMup` lane: `levelK_pairing_productFormula`,
   `localTateSystem_productFormula`);
2. the *relaxed* realisation `∀ M, Work.SSGRoute.AuxRealisationExt K Λ M` — the level-`K`
   Tate--Poitou middle exactness (the `ZSplit`/`PT` lanes: `kRealizable`, the counting identity);
3. the odd-`p` core `Work.SSGRoute.sw_z_exists_odd_sketch` (`z_data_mup_arith.lean`);
4. the `p = 2` core `Work.SSGRoute.shafarevich_z_data_two_kummerCore`
   (`shafarevich_z_data_two.lean`), whose realisation half additionally needs the *involution*
   (archimedean) clause — for `p = 2` the shortcut `auxRealisationExt_of_noInv` is not available.

### 3. Two structural facts proved this session, used by the assembly

* `Work.SSGRoute.ZConstruction.isUnramifiedOutside_of_vanishes_on_level`
  (`ZConstruction/AuxChaseVacuity.lean`): a cochain vanishing on the Galois group `G_N` of a level
  `N` is unramified at every finite place outside the level-`k` classes of a place set `S'` which
  covers (up to conjugacy) the places ramified in `N`.  This is the *confinement* of `z₀` to
  `cs(S')` on which the case `(b2)` of `Work.SSGRoute.hasZData_sum_of_level_data` rests: a `z`-data
  witness at `(Λ, S)` whose level is `N₀` is unramified outside `cs(S')` whenever
  `S' ⊇ Ram(N₀|k)` up to conjugacy — hence it contributes nothing to the *inertia* at a place
  outside `cs(S')`, which is all the level step asks there.
* `Work.SSGRoute.ZConstruction.relaxedOrthogonality_enlarge`
  (`ZConstruction/relaxedOrthogonality_enlarge.lean`): the p. 18 chase's conclusion — the sum over
  the *base* set `T` against the relaxed duals — implies the summation over the enlarged set `T'`
  with which the gate `AuxRealisationExt` is stated (the extra terms carry the zero datum and the
  local pairing vanishes on a coboundary).  This is the formal step by which the chase feeds the
  realisation gate.

`Grünwald` (`Work.SSGRoute.grunwald_surjective_odd`, proved) does not shorten this list: it realises
arbitrary continuous local data at a finite place set but gives no control of the ramification
outside it, so it does not give the `S`-level realisation that items 2--4 need.
-/

/-!
## NOTE (session 16): the confinement of the ramification of a `z`-data witness

Delivered this session, sorry-free and axiom-clean, in
`Submission/Work/SSGRoute/ZConstruction/RamificationConfinement.lean` (module
`Submission.Work.SSGRoute.ZConstruction.RamificationConfinement`, now imported by this file):

* `Work.SSGRoute.ZConstruction.hasZData_ramification_confined` — the *confinement*: a finite place `B`
  outside `cs(S)` at which a `z`-data witness `z` is ramified (i.e. on whose inertia `z` does not
  vanish) splits completely in `Λ`.  This is the contrapositive of clause 5 of
  `Work.SSGRoute.HasZData`, and it is what makes clause 6 a condition on *all* the ramification of
  `z` outside `cs(S)` (there is no other ramification).

* `Work.SSGRoute.ZConstruction.isSplitIn_of_ramified_explained` and
  `Work.SSGRoute.ZConstruction.exists_isSplitIn_of_exists_ramified_explained` — **the new places of
  the level step are split in `Λ`**.  If every place ramified in the level `N` is `k`-conjugate to a
  place at which `z` is ramified (which is the abstracted form of "`N` is the Galois closure over `k`
  of the field cut out by `z`", the choice of the paper), then every place ramified in `N` and not
  conjugate into `S` splits completely in `Λ` — because it is conjugate to a place at which `z` is
  ramified, which is split in `Λ` by the confinement, and splitting is `k`-conjugation invariant.
* `Work.SSGRoute.ZConstruction.exists_level_vanishing_newPlaces_isSplitIn` (proved this session,
  by a delegated child and then assembled in `ZConstruction/RamificationConfinement.lean`) — the same
  conclusion **for a level that actually exists**: for a witness `z` of `HasZData K Λ S y z` there is
  a finite Galois level `N ⊇ K` with `z = 0` on `G_N` such that every place ramified in `N`,
  unramified in `K|k` and not conjugate into `S`, splits completely in `Λ`.  It combines
  `Work.SSGRoute.ZConstruction.exists_level_vanishing_minimal_ramification` (the level cut out by the
  *normal core* of the kernel of `z`, whose ramification is explained by that of `z`; the child's
  contribution) with the confinement above.  This is the unconditional form of the finding below.

**Consequence (a design decision settled).**  The *weakened* level step
`Work.SSGRoute.ZConstruction.hasZData_sum_of_level_data_unram`
(`ZConstruction/hasZData_sum_of_level_data_unram.lean`) replaces the vanishing hypothesis `hvanish`
at the places of `cs(S') ∖ cs(S)` by the inertia-killing of the auxiliary class plus the side
condition `hnoSplitS'` ("no place of `cs(S') ∖ cs(S)` is split in `Λ`").  By the second and third bullets, in the
intended application (`S' = S ∪ Ram(N|k)` with `N` a level of `z₀` whose ramification is explained by
that of `z₀` — which the third bullet shows can be chosen) **every** new place is split in `Λ`: the
side condition `hnoSplitS'` fails at every new place.  The `_unram` route of the session-14 NOTE is therefore not available, and the level step
genuinely needs the last prescription of `Work.SSGRoute.AuxExists` — the *pointwise vanishing* of the
auxiliary class on the decomposition groups of `cs(S') ∖ cs(S)`, i.e. the restricted-product condition
of the p. 18 Poitou--Tate diagram.  This is the clause that the relaxed realisation gate
`Work.SSGRoute.AuxRealisationNoInv` has to supply (see `ZConstruction/NOTE_gate_state.lean`).

**Cross-lane check.**  The sibling `z`-construction of `Submission/Work/SSGRoute/shafarevich_theorem13.lean`
(`def IsYRealisation`, `theorem exists_isYRealisation_of_localisation`) exposes *the same* gate, in the
same form: a realisation theorem for data `f` under orthogonality against the classes `b` which are
cocycles on `G_K`, unramified outside `S₀` at the places not split in `Λ`, and *trivial* at the places
of `S₀` that are split in `Λ`; together with the *same* vanishing prescription at `S₀ ∖ T`.  Two
independent formalisations therefore agree on the interface; the remaining arithmetic is shared.
-/

/-!
## NOTE (session 16, continued): the isotropy half of the relaxed Poitou--Tate gate

Delivered this session (delegated and proved), sorry-free, and staying *below* this node in the
import order: `Submission/Work/SSGRoute/ZConstruction/relaxedSum_pair_eq_zero.lean` (module
`Submission.Work.SSGRoute.ZConstruction.relaxedSum_pair_eq_zero`):

* `Work.SSGRoute.ZConstruction.relaxedSum_pair_eq_zero` — the *isotropy* of the relaxed level-`K`
  localisation image: for a local Tate system `pair` with the product formula, the unramified
  orthogonality and the bilinearity axioms, for a global level-`K` cocycle `z` which is unramified
  outside the level-`K` classes of `T` except at the places splitting in `Λ`, and for a relaxed dual
  class `b` (`Work.SSGRoute.IsRelaxedDual K Λ T b`), the reciprocity sum over `T` vanishes:
  `∑_{A ∈ T} pair (D_A ⊓ G_K) z b = 0`.

This is the relaxed analogue of `Work.SSGRoute.ZDataMup.sum_pair_selmer_eq_zero` (the honest
isotropy), and its proof is the one of the p. 18 chase `auxDatum_orthogonal_of_productFormula` with
the prescribed datum replaced by the global cocycle `z`.  Since `M`-split implies `Λ`-split for
`Λ ≤ M`, a global cocycle unramified at the places outside `T`-classes that are not `M`-split is in
particular one to which the result applies; **so the isotropy of the `M`-relaxed localisation image
is proved**.

**Where the gate now stands.**  By `ZConstruction/AuxAssembly.lean`, `AuxExists` follows from
`AuxPairingGate` and the realisation gate `∀ M, AuxRealisationNoInv K Λ M`; the realisation is a
statement of Tate--Poitou type for the pair of local conditions

* primal: the tuples of level-`K` local data at the places `T'` of a global cocycle unramified at
  the finite places outside the `T'`-classes that are not split in `M`, and
* dual: `Work.SSGRoute.IsRelaxedDual K Λ T` (unramified outside the `T`-classes, locally trivial at
  the `Λ`-split places outside them).

Of the two halves of such a duality statement, the *isotropy* half is now proved below this node
(the result above); the remaining half is the *exactness* (equivalently the counting identity of the
level-`K` localisation for this pair of local conditions), which is the arithmetic rung of the
`ZSplit`/`PT` lanes (`ZSplit/levelK_counting_identity.lean`, `ZSplit/kRealizable`, the
`kRealizable`-normal-form of `ZSplit/kRealizable_normalForm.lean`).
-/


/-!
## NOTE (session 17): the *mixed-level* realisation gate, named and reduced

### The gate as the assembly uses it

`Work.SSGRoute.auxExists_of_pairing_and_realisation` (`ZConstruction/AuxAssembly.lean`) carries the
hypothesis `hR : ∀ M, AuxRealisationNoInv K Λ M` and applies it at `M = N`, the level of the *other*
summand of the section-4 induction (`Work.SSGRoute.z_data_of_spanning_of_aux`, applied at
`N = N₀ ⊔ Λ`).  The orthogonality hypothesis it feeds to `hR` is produced by the proved p. 18 chase
`Work.SSGRoute.auxDatum_orthogonal_of_productFormula`, whose dual family is relaxed at the level
**`Λ`** (that is the only level at which the chase closes: at a larger level the extra places at
which the datum `y₁` ramifies are no longer split, and the retracted statement
`Work.SSGRoute.AuxOrthogonalityGate` is false there).  So the statement the assembly needs is the
**mixed** one: *dual* relaxation at `Λ`, *primal* unramifiedness at `N`.

### What the mixed statement needs

`Submission/Work/SSGRoute/ZConstruction/AuxRealisationLevel.lean` (new, sorry-free, axiom-clean)
reduces the mixed statement to two named ingredients:

* **`Work.SSGRoute.AuxRealisationNoInv K M M`** -- the *unmixed* gate: primal and dual conditions at
  the same level `M`.  This is the standard level-`K` degree-one Poitou--Tate realisation, i.e. the
  statement supplied by the level-`K` **counting identity**
  (`Submission/Work/SSGRoute/PT/pt_counting_identity_h1.lean` is *below* this node, and the
  `ZSplit` interface `Work.SSGRoute.ZSplit.kRealizable_of_orthogonal_of_counting` -- which is *above*
  the node because `ZSplit/levelKCounting.lean` imports `shafarevich_theorem13` -- is its
  `kRealizable`/`kDualSelmer` form); the relocation of that vocabulary below the node is
  `Work.SSGRoute.ZConstruction.{kLocalGroup,kConj,kPrimalClasses,kClassOf,kRealizable,kDualSelmer,kLocalPairing}`
  (`ZConstruction/LevelKVocab.lean`, new this session, a verbatim copy with a strictly below-node
  import list);
* **`Work.SSGRoute.ZConstruction.RelaxedDualsAgree K Λ M`** -- the *relaxation slack*: every class
  satisfying the `M`-relaxed dual conditions agrees, at the places of `T'`, with a class satisfying
  the `Λ`-relaxed ones.  (Both families consist of classes unramified outside the level-`K` classes
  of `T`; they differ exactly by the condition "locally trivial" versus "unramified" at the places
  which are split in `Λ` but not in `M`.)  This is the one piece of the chain that is *not* standard
  Poitou--Tate; it is isolated here for the first time, and it is the statement to attack next (or to
  refute -- a counterexample would mean that the mixed gate is unprovable and that the section-4
  assembly of this lane needs a different decomposition).

With these, `Work.SSGRoute.auxExists_of_pairing_and_realisation_self(_odd)` gives `AuxExists` from
the pairing gate, `∀ N ≥ Λ, AuxRealisationNoInv K N N` and `∀ N ≥ Λ, RelaxedDualsAgree K Λ N`, so the
node's obligation is exactly

  `{AuxPairingGate, ∀M AuxRealisationNoInv K M M, ∀N ≥ Λ RelaxedDualsAgree K Λ N, the two μ_p cores}`

(the last three of which live below this node; the first two are the shared arithmetic of the
`ZDataMup`/`PT` lanes).
-/

/-!
### UPDATE (same session): the relaxation slack is REFUTED; what the assembly really needs

`Work.SSGRoute.RelaxedDualsAgree K Λ M` (`ZConstruction/AuxRealisationLevel.lean`) was put to two
independent reviewers and declared **false**, with the counterexample `p = 2`, `k = K = Λ = ℚ`,
`M = ℚ(i)`, `T = {A₀}` over `2`, `b` = the quadratic character of `ℚ(i)/ℚ`.  So the reduction
`AuxRealisationNoInv K M M + RelaxedDualsAgree K Λ M → AuxRealisationNoInv K Λ M` is true but not
applicable, and the mixed gate is *not* obtained by comparing the local components of the two relaxed
dual families.

The counterexample does **not** refute the mixed gate itself: the local Tate pairing on the level-`K`
local data space is degenerate (its left radical is `ZDataMup.localVanish`, cf.
`ZConstruction/LevelKRealisationCounting.lean`), so the mixed gate is *equivalent* to

  `W_M ⊆ W_Λ^{⊥⊥}`  ==  every `M`-relaxed dual class is orthogonal, over the places of `T'`, to every
  class which is `Λ`-primal (`unramified` at the finite places outside the `T'`-classes that are not
  split in `Λ`),

a **reciprocity** statement rather than a comparison of local components (the counterexample's `b`
satisfies it: its only contributing place is the one over `2`, which lies in `T`).  This -- or an
explicit finrank form of it in `ZDataMup.localDataSpace K T'`, in the style of
`Work.SSGRoute.ZConstruction.levelK_realisation_of_counting` -- is the corrected obligation of the
auxiliary class on top of `{AuxPairingGate, ∀M AuxRealisationNoInv K M M}` and the two μ_p cores.
`Work.SSGRoute.auxExists_of_pairing_and_realisation` (the *existing* assembly) requires the mixed gate
verbatim, so if the reciprocity statement above fails, the level step
`Work.SSGRoute.hasZData_sum_of_level_data` needs a redesign (it is the place where the level `N` of
the induction-hypothesis summand is used to demand unramifiedness of the auxiliary class at the
places that are split in `Λ` but not in `N`).

-/


/-!
## NOTE (session 17, conclusion): the assembly's realisation hypothesis is FALSE

The mixed-level gate that `Work.SSGRoute.auxExists_of_pairing_and_realisation` consumes (dual
relaxation at `Λ`, primal unramifiedness at the level `N ⊋ Λ` of the other summand of the induction)
is **false**: both candidate formulations of the extra content were reviewed and refuted this session
(`Work.SSGRoute.RelaxedDualsAgree`, and the reciprocity statement
`SSGRoute/ZConstruction/relaxedReciprocity_of_le`), and the same conclusion follows from the *proved*
`Work.SSGRoute.ZConstruction.relaxedSum_pair_eq_zero` (which makes a `Λ`-primal class orthogonal to
every `Λ`-relaxed dual, hence a witness for the mixed gate's *hypothesis*) together with the product
formula (which makes it *not* orthogonal to a suitable `M`-relaxed dual).  Details, the exact
counterexample and the two options for a redesign are in
`Submission/Work/SSGRoute/ZConstruction/NOTE_session17.lean`.

Consequence for this node: the obligation remains `Work.SSGRoute.MupGate + Work.SSGRoute.AuxExists`
(`ZConstruction/ZDataAux.lean`), and `AuxExists` is *not* reducible to the pairing gate and the
realisation by the present assembly; the level step `Work.SSGRoute.hasZData_sum_of_level_data` has to
be redesigned (its demand of unramifiedness of the auxiliary class at the places split in `Λ` but not
in `N` is what forces the false mixed statement), or the auxiliary class has to be obtained by the
sibling lane's route (`Work.SSGRoute.IsYRealisation`, whose *pointwise vanishing* prescription at the
new places is exactly the restriction that this lane's gate lacks).  All the statements on disk remain
sound; only this *decomposition* of `AuxExists` is broken.
-/


/-!
## NOTE (session 19): the node is wired to three named gates (odd `p`)

`Work.SSGRoute.ZConstruction.auxExists_of_countingBlocks`
(`Submission/Work/SSGRoute/ZConstruction/AuxExistsAssembly.lean`) proves

    Work.SSGRoute.AuxExists K Λ S      <=   (P) AuxPairingGate K
                                        +   (O) AuxDatumOrthogonalityGate K Λ
                                        +   (C) AuxDatumCounting K Λ
                                        +   (S covers the places above `p` and those ramified in `Λ`)
                                        +   (p ≠ 2, ζ primitive p-th root of unity, ζ ∈ K),

and `Work.SSGRoute.z_data_general_of_odd_gates`
(`Submission/Work/SSGRoute/ZConstruction/ZDataGeneral.lean`) puts this together with
`Work.SSGRoute.MupGate` to obtain the odd-`p` case of `Work.SSGRoute.z_data_general`, hence, through
the already-proved `Work.SSGRoute.shafarevich_z_construction_of_zData`, the odd-`p` case of this
node's theorem.  Axiom prints: `ZConstruction/_axcheck_assembly.lean` (clean:
`[propext, Classical.choice, Quot.sound]`).

Two corrections/findings of this session (details in `ZConstruction/NOTE_session19.lean`):

1. `Work.SSGRoute.ZConstruction.AuxDatumCounting` was **false** as previously stated: it now carries
   the *coverage* hypothesis (the place set contains the places above `p` and the places ramified in
   the auxiliary level), which is Milne ADT I.4.10's hypothesis; without it the inequality fails at
   `(k, Ω, K, p, Te) = (Q, Q-bar, Q, 3, {place over 2})`.
2. Gate (O) is **arithmetic, not a formal chase**.  The proved p. 18 chase
   (`auxDatum_orthogonal_of_productFormula`, `auxDatum_orthogonal_enlarged`) produces orthogonality
   only against the *relaxed* dual family `Work.SSGRoute.IsRelaxedDual K Λ T`, while (O) asks for the
   honest family (`ZDataMup.IsOrthogonalToDual` at the enlarged place set), which is strictly larger;
   and the naive product formula cannot close the gap (the terms at the `Λ`-split places where the
   datum ramifies, and at the places of `cs(S') ∖ cs(S)` where the dual ramifies, are not
   controlled).  By the middle exactness of the level-`K` Poitou--Tate sequence the honest
   orthogonality of the prescribed datum is *equivalent* to its realisability, i.e. to the
   arithmetic that Schmidt--Wingberg supply on pp. 18--19 by decomposing the dual class along the two
   intermediate fields `Λ` and `K~` (the `K~`-component dies by unramified orthogonality, the
   `Λ`-component by the exactness of the level-`Λ` sequence).  So `{(O), (C)}` together are exactly
   the realisation of the datum, and both are the shared arithmetic of the fleet (Tate--Poitou).

The `p = 2` case is not reached by this assembly: there the involution clause of the auxiliary class
is the archimedean condition of Shafarevich's prime-`2` correction (the argument
`Work.SSGRoute.eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot` is vacuous for `p = 2`, since
`IsPrimitiveRoot ζ 2` forces `ζ = -1 ∈ K` for every number field `K`), and the gates `(P)`, `(O)`,
`(C)` have to be restated with the archimedean terms
(`Work.SSGRoute.ZDataTwo.IsMu2LocalTateSystemWithArch` is the shape of the pairing at `p = 2`).
-/

/-!
## NOTE (session 20): the four-gate reduction above is NOT the sound route -- read this first

The block above reduces (the odd-`p` case of) the node to `MupGate`, `AuxPairingGate`,
`AuxDatumOrthogonalityGate` and `AuxDatumCounting`.  The third of these is a **mis-statement** and
should not be attacked; see `Submission/Work/SSGRoute/ZConstruction/NOTE_session20.lean` for the full
account.  In brief:

* **The direction of the level monotonicity.**  `SSGRoute.IsSplitIn k N B` is `decomp k B ≤
  N.fixingSubgroup`, so by antitonicity of `fixingSubgroup`, `Λ ≤ N` gives `cs(N) ⊆ cs(Λ)`: *a larger
  level splits fewer places* (`SSGRoute.isSplitIn_of_le`, `coker_aux.lean`).  Hence the primal
  condition "unramified at the places outside `cs(T')` that are not split in `M`" gets **stronger**
  as `M` grows, while the relaxed dual family `SSGRoute.IsRelaxedDual K M T` gets **larger**.
* **The sound route.**  `Work.SSGRoute.auxExists_of_pairing_and_realisation`
  (`ZConstruction/AuxAssembly.lean`, proved) needs only `AuxPairingGate K` and the *mixed* realisation
  gate `∀ M, AuxRealisationExt K Λ M`, whose orthogonality hypothesis is exactly
  `SSGRoute.IsRelaxedDual K Λ T` -- **proved** for the prescribed datum by the p. 18 chase
  (`auxDatum_orthogonal_of_productFormula`, `auxDatum_orthogonal_enlarged`).  The primal level
  `M = N = N₀ ⊔ Λ` is forced by the level step (`hasZData_sum_of_level_data`), so the gate is mixed;
  its remaining content is the *relaxation step of the level-`K` Poitou--Tate sequence*
  (`ZConstruction/NOTE_session17.lean`), the shared arithmetic of the fleet.
* **Why (O) is not the same gate.**  `AuxDatumOrthogonalityGate` asks for orthogonality against the
  *honest* family at the enlarged place set `Te`, a family strictly larger than `IsRelaxedDual K Λ T`
  in two independent directions: at the places of `Te ∖ T` (inside `cs(Te)`, where an honest dual may
  ramify while the datum is unramified) and at the "junk" places outside `cs(S)` that are `Λ`-split
  and at which the datum ramifies (`ZHyp.hyS` permits exactly those).  Both defects are witnessed by
  the sibling lane's counterexample (docstring of `Work.SSGRoute.IsYRealisation`,
  `SSGRoute/shafarevich_theorem13.lean`).
* **What this session added.**  `Work.SSGRoute.ZConstruction.auxDatum_orthogonal_relaxed_noGap`
  (proved): for `Λ ≤ M`, the datum is orthogonal to the *larger* family `IsRelaxedDual K M T` as soon
  as it is unramified at the places outside `cs(S)` that are `Λ`-split but not `M`-split -- so those
  "gap" places (in the induction: the places where `Λ` is locally trivial while the level `N₀` of the
  first summand is not) are the *exact* obstruction to raising the relaxation level from `Λ` to `M`.
-/

/-!
## NOTE (session 20, continued): the corrected gate list, and the two new files

* `ZConstruction/AuxRealisationSlack.lean` (proved, axiom-clean): the *relaxation slack*
  `Work.SSGRoute.ZConstruction.AuxRealisationSlack K Λ M` of the level-`K` Poitou--Tate sequence, and
  the reductions
  `Work.SSGRoute.ZConstruction.auxRealisationExt_of_unmixed_of_slack`,
  `Work.SSGRoute.ZConstruction.auxExists_of_pairing_and_unmixed_and_slack`,
  `Work.SSGRoute.ZConstruction.z_data_general_of_unmixed_gates`.

  The node's obligation is therefore, with `MupGate` the one-dimensional gate,

      MupGate  +  AuxPairingGate  +  (∀ M, AuxRealisationExt K M M)  +  (∀ M ≥ Λ, AuxRealisationSlack K Λ M),

  i.e. the *standard unmixed* degree-one realisation at every level -- which is what the level-`K`
  counting identity of the `ZSplit`/`PT` lanes supplies -- together with the slack, instead of the
  mixed gate consumed by `Work.SSGRoute.auxExists_of_pairing_and_realisation`.
* `ZConstruction/auxDatum_orthogonal_relaxed_noGap.lean` (proved, axiom-clean,
  delegated this session): `Work.SSGRoute.ZConstruction.auxDatum_orthogonal_relaxed_noGap`, the
  *sharp* orthogonality of the prescribed datum against the dual family relaxed at a level `M ≥ Λ`,
  under the single hypothesis that the datum is unramified at the "gap" places (those outside `cs(S)`
  that are `Λ`-split but not `M`-split).  This exhibits the exact obstruction to raising the
  relaxation level of the chase from `Λ` to `M`.
* `ZConstruction/NOTE_session20.lean`: the full record, including the *open* status of the slack
  (its instantiation at the data of a `Λ`-primal class turns it into the statement session 17
  refuted outside the lane's ambient hypotheses, so inside them its truth is open, and a refutation
  there would refute the mixed gate itself).
-/

/-!
## NOTE (session 25): the sixth conjunct is decided by the *level* of the witness

`ZConstruction/TransferLevel.lean` (proved, axiom-clean) adds three new verifications of the sixth
conjunct — the only non-elementary conjunct of the node's conclusion — which do **not** go through a
computation of the transfer:

* `Work.SSGRoute.exists_V_of_transfer_of_normal_vanishing`: if `Z` vanishes on `V ∩ G_K` for an open
  **normal** `V ≤ G_k` and `decomp k B ⫽ (decomp k B ⊓ V)` is cyclic, then the sixth conjunct holds
  at `B` with this `V`.  The proof is the observation that for `δ ∈ D_B ⊓ V` and every `s` the
  conjugate `(sec s)⁻¹ δ sec s` lies in `V` (normality) and in `G_K` (`G_K ◁ G_k`), where `Z`
  vanishes.  In particular the sixth conjunct is decided by the *level* of the witness.
* `Work.SSGRoute.exists_V_of_transfer_of_cyclic_level` (the case `V = G_M` for a finite normal level
  `M ⊇ K`), and the node-level régime
  `Work.SSGRoute.shafarevich_z_construction_of_cyclicLevel`: the node holds whenever the datum `y`
  vanishes on a finite Galois level `M ⊇ K` whose local decomposition groups at the junk places are
  cyclic.  This covers data at which `y` **is** ramified at the junk places (Case C data of the
  `z`-data induction), e.g. two independent cubic characters of distinct conductors.
* `Work.SSGRoute.transfer_eq_norm_of_commutators_mem` (the transfer of a cochain vanishing on a
  normal level with trivial commutators is the **norm** `∑_s s • z δ`) and
  `Work.SSGRoute.exists_V_of_transfer_of_norm_vanishing` (the sixth conjunct then holds with the
  *whole* group `V = ⊤` as soon as the norm of `z (decomp k B)` vanishes), with the node-level
  régime `Work.SSGRoute.shafarevich_z_construction_of_normVanishing`.

None of the three routes subsumes the others, and all are *verification routes* for the same
condition: by `Work.SSGRoute.exists_V_of_cyclic_transfer` the sixth conjunct at a place `B` split in
`K` is equivalent to the cyclicity of the transfer's image on `decomp k B`, so every criterion is a
sufficient condition for that cyclicity.  The value of the level criterion is that levels are
controllable objects — in the `z`-data induction the level of the witness is a free parameter —
whereas the transfer is derived from the construction.

The residual of the lane (see `ZConstruction/NOTE_session25.lean` §§1--4 for the full account) is
Case C: `csData K S y = ⊤` and `junkSpan K Λ S y = ⊤`, where the conclusion pins `Z = y` on the
`cs(S)`-local groups and the freedom is `z = y + α` with `α ∈ Hom(G_K/P̄, E)`, so that clause 6 is
the cyclicity of `X_y + X_α`.  The level criterion is *optimal* at `α = 0` (a non-zero `α` only
shrinks `ker z`), so Case C is reduced to the junk places whose image in the level of `y` is
non-cyclic and where the transfer is not cyclic by cancellation.

### The exact gate: the admissible variants

The same file formalises the freedom `z = y + α` and shows that it is *exactly* the node's residual
obligation:

* `Work.SSGRoute.ZHyp.add_of_vanishes_on_csGroups`: `y + α` is again a `ZHyp` datum agreeing with `y`
  on the `cs(S)`-local groups, whenever `α` is `ZHyp` and vanishes there (such an `α` automatically
  vanishes on the whole pinned subgroup `P`);
* `Work.SSGRoute.shafarevich_z_construction_of_variant`: **the node holds if some admissible variant
  `y + α` has cyclic transfer at every junk place** — the witness is the one of
  `Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_transferCyclicDatum` for the variant,
  which is a witness for `y` (the conclusion mentions the datum only in its third clause);
* `Work.SSGRoute.exists_variant_of_isZConclusion`: conversely every witness `z` of the node yields
  such an `α`, namely `α := z|G_K - y` (extended by `0` off `G_K`);
* `Work.SSGRoute.shafarevich_z_construction_of_unramifiedVariant`: **the node holds if some
  admissible variant `y + α` is unramified at every junk place** — the interface for the Grünwald
  lane, whose existence statement (an extension problem for continuous homs of profinite groups) is
  the residual arithmetic of Case C; the sixth conjunct is
  `Work.SSGRoute.transfer_vanishes_of_unramified` applied to the extension of `y + α`.

So the node is **equivalent** to the existence of an admissible variant with cyclic transfer at the
junk places; the hypothesis of `shafarevich_z_construction_of_transferCyclicDatum` (`α = 0`) is the
special case, and this is strictly weaker than it.  The right variant condition is the *cyclicity of
the transfer* — not the properness of the junk span of the retracted `JunkVariantGate` (session 24).

### The node's clause is weaker than the paper's `z`-data clause

The sixth conjunct of the node (`IsZConclusion`, the transfer form with `∃ V`) is *not* the sixth
clause of the paper's `z`-data `Work.SSGRoute.HasZData` (`ZConstruction/ZDataGlue.lean`), which asks
for the cyclicity of the *local image* of `z` at the junk places where `z` ramifies (plus a vanishing
clause at the non-conjugate places).  The implication HasZData ⟹ node is the fleet's route
(`Work.SSGRoute.shafarevich_z_construction_of_zData`, proved); the converse fails clause by clause —
a witness with a normal level with trivial commutators and `N = 0` satisfies the node's clause with
`V = ⊤` (its transfer vanishes by `transfer_eq_norm_of_commutators_mem`) while its local image at a
junk place can be non-cyclic.  Hence the "Case C" of the `z`-data induction is not literally the
residual of the node, and the exact residual of the node is the single named condition
`Work.SSGRoute.VariantTransferGate` exhibited above.
-/

/-!
## NOTE (session 25, gate status)

Unchanged from session 24: the node's proof is `Work.SSGRoute.shafarevich_z_construction_of_zData
hKΛ S y sec hsec`, whose only `sorry` in the subtree is
`Work.SSGRoute.z_data_general_of_ramified` (`ZConstruction/ZDataGeneral.lean`).  The odd-`p`
obligation is `MupGate` + `(∀ M, AuxRealisationT K M)` + `CaseCGate`, with `AuxPairingGate`
discharged by `ZConstruction/OddGate/`, and Case C now *partially* discharged by the level criterion
of session 25 (`shafarevich_z_construction_of_cyclicLevel` and
`shafarevich_z_construction_of_normVanishing` are proofs of the node, not of the gate, so they close
data rather than the gate).

The exact residual obligation of the node is the single named condition of session 25,
`Work.SSGRoute.VariantTransferGate K Λ S y sec` (existence of an admissible variant of the datum with
cyclic transfer at the junk places): the node is *equivalent* to it
(`Work.SSGRoute.isZConclusion_iff_variantTransferGate`), and the case `α = 0` is the hypothesis of
`Work.SSGRoute.ZConstruction.shafarevich_z_construction_of_transferCyclicDatum`.
-/


/-!
## NOTE (session 32, node lane): the §4 recursion is now sorry-free, and `HistKummer` was FALSE

Two results of the node lane this session, recorded here because they change the obligation card of
the odd-`p` core (`Work.SSGRoute.MupGate`, hence the node's `z_data_general_of_ramified`).

**1. The recursion is delivered, `sorry`-free and axiom-clean** (no arithmetic input).
`Submission/Work/SSGRoute/ZConstruction/RecursionConvert.lean` proves
`Work.SSGRoute.ZConstruction.swRecursionExists_of_chain`: the statement of
`Work.SSGRoute.ZDataMup.swRecursionExists` -- a history `f` with `HistInv ∧ (the Kummer form)` --
with the *same hypotheses*, converted from the already-proved chain
`Work.SSGRoute.ZDataMup.histInvPref_chain`.  The conversion consumes the two bridge lemmas
`histInvPref_chain_places_iff` / `histInvPref_chain_datum_eq` (the (i)/(ii) of `HistBridge` /
`HistDatumId`) and the place-level transport lemmas of the new module
`Submission/Work/SSGRoute/ZConstruction/HistDatumPrefCongr.lean`
(`gesKConj_congr_right`, `isConjPlace_congr_right`, `kleadReps_isFinPlace`, `histPlaces_isFinPlace`,
`histDatumPref_gesKConj_congr`, `histDatumPref_conj_inv`).  Axiom footprint:
`[propext, Classical.choice, Quot.sound]` (`ZConstruction/_axcheck_s32b.lean`).

**2. `Work.SSGRoute.ZDataMup.HistKummer` is unsatisfiable, so `ZDataMup.swRecursionExists` is
FALSE as stated.**  Its last clause demands that `x` have the *smallest* value among the elements of
value `< 1` at the escape prime, while a uniformiser has the *largest*: in the value group
`A.ValueGroup` (a `LinearOrderedCommGroupWithZero` with bottom `0`), `0 < v < 1` gives
`v * v < v`, so `y := x * x` refutes the comparison.  Formal, axiom-clean refutations:
`Work.SSGRoute.ZConstruction.histKummer_valuation_false`, `not_histKummer`,
`not_swRecursionExists_conclusion`
(`Submission/Work/SSGRoute/ZConstruction/HistKummerValuationFalse.lean`).  The corrected interface is
`Work.SSGRoute.ZConstruction.HistKummerNorm`: the class clause `(f m).2 = χ_b` on `G_K`, and at each
escape prime an `x ∈ (↥K)ˣ` with `count 𝔮 (x) = 1` at the prime `𝔮` below the escape prime together
with `(f m).2 = -χ_x` on the inertia -- exactly what `HistInvPref.znorm` and the escape oracle
produce, and what the two-place reciprocity consumes; the value orientation is recovered by
`HistKummerNorm.value_form`.  The action for the `ZDataMup` lane is spelled out in
`ACTION_histKummer_false_and_swRecursionExists_delivered.md` (workspace root).

**3. The odd-`p` obligation collapses to the one-dimensional gate.**  `zDataGeneralOfMupAndZeta`
(`zDataGeneralOfMupAndZeta.lean`, **proved and axiom-clean**: `#print axioms` =
`[propext, Classical.choice, Quot.sound]`) derives the general-coefficient `z`-data from the
one-dimensional gate `IsMupZData` and the Grünwald-with-escape realisation, whose only extra
hypothesis is `hKimag : p = 2 → ∀ c ∈ G_K, c ^ 2 = 1 → c = 1` -- **vacuous for odd `p`**.  Hence
`Work.SSGRoute.z_data_general_of_ramified_odd` (`ZConstruction/ZDataGeneral.lean`) gives the node's
`z`-data for odd `p` from `IsMupZData` alone, and the node-level corollary
`Work.SSGRoute.shafarevich_z_construction_of_isMupZData_odd` (end of this file, **axiom-clean**) gives
this node for odd `p` from `IsMupZData` alone -- **no `AuxExists`, no Poitou--Tate input, no p = 2
core**, i.e. only the odd-`p` μ_p core `Work.SSGRoute.z_data_mup_core` (through
`Work.SSGRoute.isMupZData_of_odd`).

Consequence for this node: for **odd `p`** the obligation is the odd μ_p core alone (and the §4
recursion feeding it is now clean, see 1.).  For **`p = 2`** the `hKimag` hypothesis is *false* in
the node's setting (Ω is algebraically closed, so `G_K` has involutions), so the Grünwald route
does not apply: there the node still needs `MupGate` + `AuxExists`, or a correction-aware variant of
the Grünwald realisation.  `hKimag` is consumed in exactly two places, and both are precisely the
prime-`2` correction: `Work.SSGRoute.N2v2.kummerChar_archimedean` (it excludes the *real* places of
`K`) and clause (6) of the realisation (`ZRealV2/RealisationV2Own.lean`, "the involutions are
killed").  At `p = 2` the replacement is the prescription that the Kummer element is **totally
positive** (equivalently, that the datum vanishes on the involutions -- the node's `hyinf`), which is
exactly Shafarevich's prime-2 correction.
-/

/-! ## The odd-`p` endgame with the one-dimensional gate alone (session 32)

For odd `p` the whole arithmetic obligation of the node collapses to the *one-dimensional* gate
`Work.SSGRoute.IsMupZData p k Ω K`: the auxiliary class of Schmidt--Wingberg's §4 induction is
supplied by the Grünwald-with-escape realisation rather than by the pairing input `AuxExists`
(`Work.SSGRoute.zDataGeneralOfMupAndZeta`, proved and axiom-clean; its only extra hypothesis
`hKimag : p = 2 → ∀ c ∈ G_K, c^2 = 1 → c = 1` is vacuous for odd `p`).  See
`Work.SSGRoute.z_data_general_of_ramified_odd` (`ZConstruction/ZDataGeneral.lean`). -/

namespace Work.SSGRoute

/-- **The node for odd `p` from the one-dimensional gate alone** (`A = μ_p` at every pair `(Λ,S)`,
i.e. the odd-`p` μ_p core `Work.SSGRoute.z_data_mup_core` through
`Work.SSGRoute.isMupZData_of_odd`).  No `AuxExists`, no Poitou--Tate input. -/
theorem shafarevich_z_construction_of_isMupZData_odd
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hμ : IsMupZData p k Ω K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  obtain ⟨z, hz⟩ := z_data_general_of_ramified_odd p hp k Ω
    ⟨hKΛ, ζ, hζ, hζK, hSfin, hSdisj, hSram⟩ hμ E y
    ⟨hy, hyc, hyS, hyT, hy0, hyinf⟩
  exact shafarevich_z_construction_of_zData hKΛ S y sec hsec ⟨z, hz⟩

/-- **The node from the two named inputs, at every prime `p`** — the *one-dimensional* gate
`Work.SSGRoute.IsMupZData p k Ω K` (`A = μ_p` at every pair `(Λ,S)`, i.e. the odd-`p` μ_p core at
odd `p` and the `p = 2` core `Work.SSGRoute.shafarevich_z_data_two` at `p = 2`) together with the
auxiliary realisation gate `Work.SSGRoute.ZConstruction.AuxRealisationGate`, in which the false
`hKimag` hypothesis of `Work.SSGRoute.isAuxiliaryZData_of_grunwald_v2` is replaced by the
prime-`2` correction (the involutions clause on the realised class, i.e. total positivity of the
escape element).

At odd `p` the gate is `Work.SSGRoute.ZConstruction.auxRealisationGate_odd`; at `p = 2` it is
`Work.SSGRoute.ZConstruction.auxRealisationGate_of_realisationTwo` applied to the two-field narrow
realisation (`Work.SSGRoute.NoKimag`), see `ACTION_p2_twoFieldRealisation.md` and
`PING_NoKimag_realisation_escape_field.md`.  With those, this theorem is the node. -/
theorem shafarevich_z_construction_of_realisationGate
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hreal : Work.SSGRoute.ZConstruction.AuxRealisationGate (p := p) (K := K) (ζ := ζ)
      (hζ := hζ) (hζK := hζK))
    (hμ : IsMupZData p k Ω K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (sec : (K ≃ₐ[k] K) → (Ω ≃ₐ[k] Ω)) (hsec : ∀ s, SSGRoute.res k K (sec s) = s) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        ∃ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) ∧
          (∀ δ ∈ SSGRoute.decomp k B, ∀ u ∈ SSGRoute.decomp k B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
          (∃ g ∈ SSGRoute.decomp k B, ∀ δ ∈ SSGRoute.decomp k B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
          (∀ δ ∈ SSGRoute.decomp k B ⊓ V, (∑ s : K ≃ₐ[k] K, s • z ((sec s)⁻¹ * δ * sec s)) = 0)) := by
  obtain ⟨z, hz⟩ := z_data_general_of_realisationGate_full (p := p) (k := k) (Ω := Ω) (K := K)
    (Λ := Λ) hKΛ ζ hζ hζK hreal hμ E S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf
  exact shafarevich_z_construction_of_zData hKΛ S y sec hsec ⟨z, hz⟩

/-
## NOTE (session 34, node lane): the node is closed modulo the two `μ_p` cores

**State.**  `#print axioms Work.SSGRoute.shafarevich_z_construction = [propext, sorryAx,
Classical.choice, Quot.sound]`; the `sorryAx` enters through exactly `Work.SSGRoute.z_data_mup_core`
(odd `p`) and `Work.SSGRoute.shafarevich_z_data_two` (`p = 2`) --- see
`ZConstruction/_axcheck_s34e.lean`.  Everything else in the cone is axiom-clean.  The statement of
this theorem is unchanged (md5 of the theorem block `765aa5d1adb671c6618d21d7205daa2e`).

**What changed in this file.**  One added import, `Submission.Work.SSGRoute.ZConstruction.ZDataFinal`
(the new home of `Work.SSGRoute.z_data_general`); the proof of the theorem --- and of the endgame
corollaries below (`shafarevich_z_construction_of_mupGate_and_auxExists`,
`..._of_isMupZData_odd`, `..._of_realisationGate`) --- is textually unchanged.  The obligation that
used to be blocked on `ZConstruction/ZDataGeneral.lean`'s `sorry` is now proved:

* odd `p`: `z_data_general_of_ramified_odd` (the Grünwald-with-escape realisation
  `zDataGeneralOfMupAndZeta`, clean) with the one-dimensional gate supplied by
  `Work.SSGRoute.isMupZData_of_kummerCore` (`ZConstruction/MupCoreKummer.lean`), i.e. by the **live**
  Kummer-core route of the `H9` lane (`Work.SSGRoute.ZDataMup.sw_odd_kummer_core` + the proved bridge
  `Work.SSGRoute.z_data_mup_odd_of_grunwald_of_kummerCore`) --- *not* by the stale `z_data_mup_core`
  of `z_data_mup_arith.lean` (whose four sorries have not been touched since 2026-09-26);
* `p = 2`: `ZDataFinal.z_data_general_of_ramified` uses `ZDataGen.zDataGeneralOfMupAndZetaGen` with
  `AuxRealisationGate (p := 2)` built from the `NoKimag` two-field narrow orthogonality
  (`OrthHsplitBridge.twoFieldOrthogonalityAll_of_orthHsplitTwoNarrow`) and the `μ₂` core
  (`isMupZData_of_core_two`).  This is the prime-`2` correction: the escape element is totally
  positive, so the realised class kills the involutions, and no `hKimag`-type hypothesis occurs.

**Obstacle met and solved (details in `ZConstruction/NOTE_session34.lean` §3).**  The `p = 2`
orthogonality lives above `ZDataGeneral` (`NoKimag/`, `ZDataTwo/`, `H9Narrow/`), and importing it
into the node's cone brings `sha2_defs`'s direct instance `Triv.instSMulOfOne : SMul Γ (Triv p)`
(and `Triv p` is an `abbrev` for `ZMod p`) into the cone.  Instance search then resolves the hidden
`SMul (K ≃ₐ[k] K) (ZMod p)` argument of `SMulCommClass` goals from that instance rather than from the
`DistribMulAction`-derived one that the workspace's `IsMupZData`/`IsYRealisation`-style signatures
expect, breaking every downstream statement with a local `[DistribMulAction ...]` binder
(`ZMupGate.lean`, `shafarevich_theorem13.lean`, and this file's own `..._of_realisationGate`).
`ZDataFinal.lean` repairs this for its whole downstream subtree by declaring
`Work.SSGRoute.ssgDistribSMulToSMul`, a `priority := 1300` copy of the projection
`DistribSMul.toSMul`.  (An `attribute [-instance]` removal in the upstream file does *not* work: only
instance *declarations* are inherited by importers.)

**Action for the fleet.**  Both branches of the `z`-construction are now wired to the *deepest live*
statements of the two arithmetic frontiers (`#print` of `z_data_general_of_ramified` uses exactly the
two gates below; audit `ZConstruction/_axcheck_s34j.lean`):

* odd `p`: `Work.SSGRoute.isMupZData_of_kummerCore` (`ZConstruction/MupCoreKummer.lean`) is
  `IsMupZData p` from `Work.SSGRoute.H9.sw_odd_kummer_core_proved`, i.e. from
  `Work.SSGRoute.ZDataMup.sw_odd_kummer_core` --- the `H9` lane's `§4` chain
  (`H9.swHistChi_chain*_proved`, `ZDataMup.swChainValue`);
* `p = 2`: `Work.SSGRoute.isMupZData_of_kummerCoreTwo` (`ZConstruction/MupCoreTwo.lean`) is
  `IsMupZData 2` from `Work.SSGRoute.ZDataTwo.shafarevichZDataTwoKummerCoreH`, i.e. from
  `Work.SSGRoute.ZDataTwo.mu2ThreeHalves` (with `mu2EscapeRealisationH`) --- the `ZDataTwo` lane's
  three-halves core.

No other `sorryAx` occurs in the node's cone, and neither `z_data_mup_arith.lean` nor the `sorry` of
`shafarevich_z_data_two.lean` is needed any more.  See `ACTION_node_endgame_wired.md` and
`ZConstruction/NOTE_session34.lean`.
-/

end Work.SSGRoute

