import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.Reduction
import Submission.Work.SSGRoute.ZConstruction.ZDataGlue
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq
import Submission.Work.SSGRoute.decomp_mod_inertia_cyclic_over_K
import Submission.Work.SSGRoute.grunwald_surjective_two
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.grunwald_setup
import Submission.Work.SSGRoute.kummerChar_eq_zero_of_isInertia_of_unit
import Submission.Work.SSGRoute.exists_kummerChar_of_additive_locConst
import Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase
import Submission.Work.SSGRoute.ZDataTwo.ArchKummer
import Submission.Work.SSGRoute.ZDataTwo.archPair_two_kummer_eq_zero_iff
import Submission.Work.SSGRoute.ZDataTwo.FiniteReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-! ## SESSION 10 (current state: the node is *proved* from its arithmetic core)

**The node `Work.SSGRoute.shafarevich_z_data_two` is no longer a `sorry`.**  It is now proved from
the single arithmetic statement `Work.SSGRoute.shafarevich_z_data_two_kummerCore` (the only `sorry`
of this file), by the assembly theorem `Work.SSGRoute.shafarevich_z_data_two_of_kummerCore`:

* the definitions and the dictionary lemmas were moved to
  `Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase` (imported below), so that the arithmetic core
  can be stated (and delegated/proved) in a separate module without an import cycle;
* `shafarevich_z_data_two_of_kummerCore` reduces an arbitrary one-dimensional `𝔽₂`-coefficient
  module `E` (`finrank ≤ 1`, hence `E = 0` or `E ≅ ZMod 2`) to the case `E = ZMod 2` by transporting
  along a fixed `𝔽₂`-linear equivalence, and then takes `z := z_b`, the Kummer cochain of the element
  `b` produced by the core (`nodeKummerCochar K ζ hζK hζ b`);
* conjuncts (1),(2) of the conclusion come from the Kummer bridge (`kummerCochar_add`,
  `kummerCochar_locConst`), conjuncts (3)–(5) and the vanishing half of (6) are the four clauses of
  the core, and the cyclicity half of (6) is automatic for `dim_{𝔽₂} E ≤ 1`
  (`zmultiples_eq_top_of_finrank_le_one`).

**What the core still owes.**  `shafarevich_z_data_two_kummerCore` is Schmidt–Wingberg §4 for
`p = 2`: the existence of `b ∈ Kˣ` whose Kummer cochain `z_b` agrees with `y` on the decomposition
groups of `cs(S)`, kills the involutions, is unramified outside `cs(S)` at the places not split in
`Λ`, and is *isolated* at the good split places where it is ramified.  The construction of `b` is
the paper's sequence `z₁, z₂, …` (Tate–Poitou realisation + Čebotarev + the pigeonhole principle +
the Hilbert-symbol product formula + the "Claim"), whose only missing ingredient in this workspace
is the Poitou–Tate degree-`1` realisation (`Work.SSGRoute.PT.pt_selmer_relaxed` /
`Work.SSGRoute.H1Pair.SelmerRealization`); the `p = 2` combinatorics are already on disk
(`Submission/Work/SSGRoute/ZDataTwo/*`).

**Arithmetic shape of the core** (recorded so that the remaining obligation can be attacked with
number theory rather than cohomology).  For `A ∤ 2` (automatic at every place outside `cs(S)`,
because `hSram` collects the places over `2` and the places ramified in `Λ` into `S`):

* conjunct (3) is the local Kummer dictionary `kummerCochar_eq_zero_iff_localPowClass`:
  `z_b = y` on `D_A ⊓ G_K` iff `b/h` is a local `2`-power at the prime of `K` below `A`;
* conjunct (5) is `kummerCochar_eq_zero_of_isInertia_of_even_valuation` (this session): `z_b` kills
  the inertia of a place `B ∉ cs(S)` as soon as `v_B(b)` is even, so the condition is only a
  *parity* condition on `b`, not local squarity;
* conjunct (6), vanishing half, is again the local Kummer dictionary: `b` must be a local `2`-power
  at the primes of `K` below the one-sided conjugates `Q` of the places at which `z_b` is ramified;
* conjunct (4) (involutions) is the "`b` is a square at every real place of `K`" condition.
-/

/-! ## SESSION 10, addendum: why the sharpened (b) needs Schmid–Wingberg §4

Two observations recorded here for the next session.

* **The easy case of the core is proved**:
  `Work.SSGRoute.shafarevich_z_data_two_kummerCore_of_unramified` — if `y` vanishes on the inertia
  of *every* finite place outside `cs(S)` (not only of the non-split ones, `hyS`), then the element
  `h` of the Kummer correspondence (`Work.SSGRoute.exists_kummerCochar_of_node_data`) witnesses the
  core, because `z_h = y` on all of `G_K`.  So the core only has content in the case where `y` is
  ramified at some place outside `cs(S)`, necessarily split in `Λ`.

* **The `(6)(b)` clause is *not* free, even for `dim E ≤ 1`.**  The project's
  `Work.SSGRoute.shafarevich_z_construction_of_finrank_le_one`
  (`Submission/Work/SSGRoute/ZConstruction/Reduction.lean`, **proved**) shows that for `dim E ≤ 1` the
  candidate `z := y` (extended by `0` off `G_K`) satisfies a *different, weaker* conclusion in which
  the sharpened vanishing of `(6)(b)` is replaced by the existence of an open normal `V ≤ decomp k B`
  with `decomp k B / V` cyclic and the **transfer** `X δ = ∑_{s} s • z ((sec s)⁻¹ δ sec s)`
  vanishing on `decomp k B ⊓ V`.  For `dim E ≤ 1` *any* subgroup of `E` is cyclic, so the `V`-clause
  is essentially vacuous and `z := y` works; the sharpened `(6)(b)` of this node — which the sibling
  `Work.SSGRoute.sw_z_exists_odd_sketch` / `Work.SSGRoute.shafarevich_z_data_mup` and the general-dim
  induction of `ZConstruction/ZDataGeneral.lean` need — is strictly stronger and is *exactly* the
  point at which Schmidt–Wingberg's §4 construction (moving the ramification of `y` onto new, isolated,
  split-in-`Λ` primes) is required.

* **Roadmap for the core.**  The construction to formalise is the paper's: build
  `z₁, z₂, … ∈ H¹(k_S|K, μ₂)` with `z_i` ramified at exactly one new prime `P_i` (one place per
  prime of `K`, chosen by `Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split`), agreeing with `y` on
  `cs(S)` and carrying a prescribed Frobenius value at `P_i`; obtain the `z_i` from the Poitou–Tate
  degree-`1` realisation (`Work.SSGRoute.PT.pt_selmer_relaxed` /
  `Work.SSGRoute.H1Pair.SelmerRealization`, still the workspace's missing arithmetic input), whose
  orthogonality hypothesis is discharged by reciprocity for the local data built out of previous
  `z_j`'s (all global) plus the Frobenius term; then apply the pigeonhole
  (`Work.SSGRoute.ZDataTwo.pigeonhole_three`), form the three-term sum (`two_partition`,
  `three_term_cancellation`) and verify `(6)(b)` with the "Claim" and the Hilbert-symbol product
  formula.  Nothing else is missing.

  Two further prerequisites, verified in the workspace: (i) the local Tate pairing for `μ₂` is
  needed to *state* the orthogonality hypothesis of the realisation, and its canonical
  construction is `Work.SSGRoute.PTembedding.localTatePairing_canonical` (open); (ii) the
  Hilbert-symbol product formula used in the "Claim" and in the verification of `(6)(b)` is
  formalised in this workspace only over `ℚ` (`Submission/Work/HilbertSymbol/`,
  `Submission/Work/QuadraticLocalGlobal/`), whereas the node is stated over an arbitrary number
  field `k`, so the general-`k` version has to be built as well.
-/

-- Schmidt–Wingberg §4, first half, in the exceptional case `p = 2`: the local data of their
-- (a)+(b) for a one-dimensional coefficient module (`A = μ₂`, where the "cyclicity" half of (b) is
-- automatic).  This is the statement of `Work.SSGRoute.shafarevich_z_data_mup` with the hypothesis
-- `p ≠ 2` replaced by `p = 2`: the paper treats the two parities by different methods (for `p = 2`
-- the sequence `z₁, z₂, …` satisfies the extra conditions (3), (4) of the paper and the final class
-- is a sum of three terms `z = zᵢ + z_j + z_N`, the verification of (b) using the "Claim"
-- `(z_i)_{σP_i} = 0` for σ ∈ G₁ (involutions) whose proof uses a prime Q in the ideal class of 𝔄
-- with Q ≠ Q^σ (Chebotarev in the Hilbert class field) and the `(2b, z̃)` Hilbert-symbol chain).
--
-- The conclusion is exactly the conclusion of `shafarevich_z_data_mup`; only the construction
-- differs.  Like that statement it is consumed by
-- `Work.SSGRoute.shafarevich_z_construction_of_swData` (module
-- `Submission.Work.SSGRoute.ZConstruction.SWData`) and hence feeds
-- `Work.SSGRoute.shafarevich_z_construction` and `Work.SSGRoute.shafarevich_existence`.

/-! ## SESSION 9 (state of the node, and the exact remaining gap)

**Status.**  The only `sorry` of this file is the statement `Work.SSGRoute.shafarevich_z_data_two`
itself.  Everything else builds and is axiom-clean (`#print axioms` = `propext, Classical.choice,
Quot.sound`).

**What was added in this session (the Kummer bridge, section `KummerBridge` below).**  The node's
cochain vocabulary has been connected to the classical arithmetic of the quadratic extensions
`K(√b)/K`:

* `kummerCochar K ζ hζ b` — the global Kummer character of `b ∈ Kˣ`, transported from `Gal(Ω/↥K)`
  to `G_K = K.fixingSubgroup` by `IntermediateField.fixingSubgroupEquiv` and extended by `0` off
  `G_K` (the cochain shape used by `Work.SSGRoute.grunwald_surjective_two`);
* `kummerCochar_add`, `kummerCochar_locConst` — it is additive and locally constant on `G_K`, i.e.
  it satisfies conjuncts (1), (2) of the node (same proof as in `grunwald_surjective_two`);
* `kummerCochar_mul`, `kummerCochar_sq`, `zmodTwo_add_self` — functional calculus: the cochain is a
  homomorphism in the element, a square factor is invisible (`char(c²) = 2·char(c) = 0`);
* `kummerCochar_eq_zero_iff_localPowClass` — **the local Kummer dictionary in the node's
  vocabulary**: the cochain of `b` vanishes on `decomp k A ⊓ G_K` if and only if `b` is a local
  `2`-power at the prime `𝔭` of `K` below `A` (transport of the proved
  `Work.SSGRoute.local_kummer_dictionary_two` along `Work.SSGRoute.grunwaldSetupDecompEquiv`).  This is the
  bridge for conjuncts (3) and (6);
* `Work.SSGRoute.kummerChar_eq_zero_of_isInertia_of_unit` (module
  `Submission.Work.SSGRoute.kummerChar_eq_zero_of_isInertia_of_unit`, delegated this session,
  **proved**): *if `A ∤ 2` and `a ∈ Kˣ` is a unit at `A`, then the Kummer character of `a` vanishes
  on the inertia of `A`* — the "unramified" half of the Kummer dictionary, i.e. the bridge for
  conjunct (5).  Consequence in this file:
  `kummerCochar_eq_zero_of_isInertia_of_sq_mul_unit` (conjunct (5) whenever `b` is a unit at `A`
  times a square).

**The exact remaining gap.**  Write `z_b := kummerCochar K ζ hζ b` for the Kummer cochain of `b`,
and let `y` be the node's data.  By the Kummer correspondence
(`Work.SSGRoute.exists_kummerChar_of_additive_locConst`, delegated this session and **proved**, and
transported into this file as `exists_kummerCochar_of_node_data`) every `y` which is additive and
locally constant on `G_K` is `z_h` for some `h ∈ Kˣ` — so hypothesis (i) below is automatic;
conversely everything the node asks for is a statement about a single further element `b ∈ Kˣ`,
namely the **Kummer core**:

  *there exist `h b ∈ Kˣ` with*
  (i)   `y = z_h` on `G_K`  (the Kummer correspondence for `y`), and
  (ii)  `z_{b h⁻¹}` vanishes on `decomp k A ⊓ G_K` for every `A ∈ S`  (⟹ conjunct (3)),
  (iii) `z_b` kills the inertia of every finite place outside `cs(S)` that is not split in `Λ`
        (⟹ conjunct (5)); in arithmetic form: `v_𝔭(b)` is even at all those primes,
  (iv)  `z_b` kills the involutions of `G_K` (⟹ conjunct (4)); in arithmetic form: `b` is a square
        at every real place of `K`,
  (v)   at every finite place `B ∉ cs(S)` split in `Λ` at which `z_b` is ramified, `z_b` vanishes on
        `decomp k Q ⊓ G_K` for every conjugate `Q` of `B` that is not a `G_K`-conjugate of `B`
        (⟹ conjunct (6)); in arithmetic form: `b` is a local square at those `Q`.

The cyclicity half of conjunct (6) is automatic for `dim_{𝔽₂} E ≤ 1`
(`z_data_two_cyclic_conjunct`, and `zmultiples_eq_top_of_finrank_le_one` from
`ZConstruction/Reduction.lean`).

**(v) is the crux, and it is Schmidt–Wingberg §4.**  Conditions (ii) and (v) say that the
ramification of `z_b` outside `cs(S)` must be moved onto *new, isolated, split-in-`Λ` primes*; the
paper does this with the sequence `z₁, z₂, …` (realised by the Tate–Poitou degree-`1` exactness),
the pigeonhole principle on the Frobenius data and the Hilbert-symbol product formula.  In this
workspace that realisation is still missing (see `Work.SSGRoute.PT.pt_selmer_relaxed` and
`ZConstruction/ZDataGeneral.z_data_general_of_ramified`); the `p = 2`-specific combinatorial
pieces are already on disk (`ZDataTwo/two_partition.lean`, `ZDataTwo/pigeonhole_three.lean`,
`ZDataTwo/three_term_cancellation.lean`, `ZDataTwo/chebotarev_frobenius_split.lean`), and the
"new prime" Chebotarev step is proved in `shafarevich_theorem13.lean`.

**False lead to avoid.**  For `p = 2` the involution clause (iv) is *not* automatic: an additive
map `G_K → 𝔽₂` is a homomorphism, and `2·z c = z(c²) = 0` carries no information in characteristic
`2`; e.g. `K = ℚ`, `b = -1` gives `z_b(c) = 1` at the complex conjugation.  The clause is the
"totally positive" condition on `b` (trivial when `K` has no real places, e.g. `K = ℚ(i)`).
-/


/-! ## SESSION 12: the exact arithmetic content of the core, and where the gap really is

**What is proved where.**  The node is `shafarevich_z_data_two_of_kummerCore` applied to the
arithmetic core `shafarevich_z_data_two_kummerCore` (the only `sorry` of this file).  The core is
Schmidt–Wingberg §4 for `p = 2` with the *weakened* hypothesis of the node (`y` need not be
unramified outside `S`, only at the places that are not split in `Λ`).  The node is therefore
*strictly stronger* than Schmidt–Wingberg's Theorem 13, and the extra content is exactly the
"move the ramification onto new, isolated, split-in-`Λ` primes" half of §4.

**The core in arithmetic form.**  By the Kummer dictionary in `ZDataTwo.KummerCocharBase` the core
is equivalent to the following statement about a single element `b ∈ Kˣ` (write `T` for the set of
primes of `K` lying below `cs(S)`, and `R(b) = {𝔭 : v_𝔭(b) odd}`, `N(b) = {𝔭 : b ∉ (K_𝔭ˣ)²}`):

(A) `b/h ∈ (K_𝔭ˣ)²` for every `𝔭 ∈ T`
    (`⟺ z_b = y` on `decomp k A ⊓ G_K`, by `kummerCochar_eq_zero_iff_localPowClass`);
(B) `v_𝔭(b)` even for every `𝔭 ∉ T` that is not split in `Λ` (`⟺` conjunct (5)); at every
    `𝔭 ∈ T` this is automatic because `hyT` says that `y` kills inertia there;
(C) `b` is a local square at every real place of `K` (`⟺` conjunct (4), the involutions);
(D) for every `𝔭 ∉ T` split in `Λ` with `v_𝔭(b)` odd, and every `G_k`-conjugate prime `𝔭' ≠ 𝔭`:
    `b ∈ (K_{𝔭'}ˣ)²` (`⟺` conjunct (6)(b), again by the Kummer dictionary).

Condition (D) is the whole difficulty; (A) is a finite set of local conditions and (B),(C) are
local conditions at the ramification.  Two reformulations of (D) are useful.

* Because the completion isomorphism `K_𝔭 → K_{𝔭'}` induced by `τ ∈ G_k` with `τ𝔭 = 𝔭'` carries
  the image of `b` to that of `τb`, condition (D) is *equivalent* to: for every `𝔭 ∈ R(b)` and
  every `τ ∈ G_k ∖ D_𝔭`, the conjugate class `τb` is a local square at `𝔭`.  In particular `b`'s
  class is **not** `G_k`-invariant at a ramified prime (so `b` can never be taken in `kˣ`).
* In terms of the two loci: (D) `⟺ N(b) ∩ orbit(R(b)) ⊆ R(b)`.  Only the finitely many orbits of
  primes that meet `R(b)` are constrained; `b` may be a non-square at primes of other orbits
  freely.  Since the support primes must be split in `Λ` (by (B)) their orbit has `[K:k]` elements,
  so (D) is non-vacuous precisely when `[K:k] ≥ 2`.

**Two structural facts found in this session, both relevant to whoever finishes §4.**

* *The local matching is free.*  `NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation`
  (with `isWeakApproximation` and `isOpenEllPowSubgroup`, both proved) shows that the diagonal map
  `Kˣ/(Kˣ)^2 → ∏_{𝔭∈S}(K_𝔭ˣ/(K_𝔭ˣ)²)` is **surjective** for every finite set `S`.  Hence the
  whole difficulty of the core is the *ramification control* ((B) and (D)), never the local
  matching (A).  Equivalently: the core is not a statement realisable by weak approximation.
* *The reciprocity half, and the true role of the prime `2`.*  If `𝔭 ∤ 2` and `v_𝔭(a)`, `v_𝔭(b)`
  are both even, then `K_𝔭(√a)/K_𝔭` is unramified (Hensel: for `𝔭 ∤ 2` the extension is
  unramified exactly when the valuation is even), and by
  `NK.Unramified.NormGroupEqUnramified.normGroup_eq_unramifiedNormGroup` its norm group is the
  even-valuation subgroup — so `b` is a local norm and `(a,b)_𝔭 = 1`.  Consequently
  Hilbert reciprocity gives `∑_{𝔭∈T}(a,b)_𝔭 = 0` for `a,b` unramified outside `T` **as soon as `T`
  contains the primes over `2`**: this is the "reciprocity" (`hrec`) half of the Poitou–Tate
  realisation, and it is provable in the workspace.  The exception is genuinely at the primes over
  `2` (`(-1,-1)₂ = -1` although both valuations are even) — which is why the odd-`p` realisation
  `tatePoitou_h1_realisation_sketch` (`z_data_mup_arith.lean`) cannot be quoted verbatim for
  `p = 2`: its `hrec` hypothesis is stated for an arbitrary `T'`, without the primes over `2`.
  This, not the Grünwald–Wang exception, is the mathematical content of the "prime-2 correction"
  for this node.

**The remaining gap.**  By the two facts above the core is *equivalent* to the `p = 2` instance of
the Poitou–Tate degree-1 exactness (`V = W^⊥`, i.e. "a datum orthogonal to the dual Selmer group is
realisable with ramification confined to the given set"), together with the §4 sequence `z₁,z₂,…`
and its Claim on top of it.  The exactness is *not* in this workspace: the design estimate for it
(`DESIGN_PT.md`, and the header of `PT/pt_selmer_counting_identity.lean`) is 10–19k lines, and
every E-node feeding it is a `sorry`.  Its `p = 2` local Tate system was refused three times as a
fleet lemma ("the project's `p=2` axiom-strength input"), so it should not be re-delegated in the
abstract local-Tate-system form.

**The archimedean (real-place) half — done in this session.**  The new module
`Submission.Work.SSGRoute.ZDataTwo.ArchKummer` (imported below, sorry-free) supplies the archimedean
half of the Kummer dictionary, which is *empty for odd `p`* (`H¹(ℝ, M) = 0`) and is exactly the
reason `p = 2` needs its own treatment:

* `kummerChar_eq_zero_iff_apply_sqrt` — the Kummer character of `a` at `σ ∈ Gal(Ω/K)` vanishes iff
  `σ` fixes the chosen square root of `a`;
* `kummerChar_eq_zero_iff_exists_sqrt_fixed` — equivalently iff some square root of `a` is fixed,
  i.e. iff `a` is a square in the fixed field `Ω^σ`;
* `nodeKummerCochar_eq_zero_iff_exists_sqrt_fixed`, and its corollary
  `nodeKummerCochar_eq_zero_on_involutions_iff` — **the node's clause (C) in arithmetic form**: the
  Kummer cochain of `b` vanishes at every involution of `G_K` exactly when `b` is a square in the
  fixed field of every involution.  Since (Artin–Schreier) the involutions of `G_K` are the
  conjugations at the real places of `K`, this is the "`b` is totally positive" condition, so clause
  (C) — the one archimedean clause of the core — is now reduced to a purely arithmetic condition on
  `b` alone.  This is item 1 of the plan below.

**The archimedean half of the *reciprocity* clause: DONE.**  (The statement of the next
paragraph was delegated and returned sorry-free as
`Work.SSGRoute.ZDataTwo.archPair_two_kummer_eq_zero_iff`, module
`Submission.Work.SSGRoute.ZDataTwo.archPair_two_kummer_eq_zero_iff`, imported below: the archimedean
pairing at `p = 2` vanishes exactly when one of the two Kummer classes is a square in the fixed field
of the involution, i.e. it *is* the real Hilbert symbol.)  Details:  The archimedean
pairing itself (`Ach.archPair` at `p = 2`, cut down to the involution groups by
`E7Arch.pairArchFamily`) has all its clauses (1)–(5) proved (`E7Arch.localGroupClauses`,
`E7Arch/pairFamily.lean`), and its disjointness from the finite-place groups is proved
(`E7Arch.localGroupDisjoint`).  What the reciprocity clause still owes on the archimedean side is its
*arithmetic identification*: at `p = 2` with `E = T = 𝔽₂` the pairing is
`g c (f c ⊗ t₀)` (a two-line value computation, reviewed this session: true but definitional), and
combining that with `kummerChar_eq_zero_iff_exists_sqrt_fixed` gives

  `archPair … c f g = 0  ↔  (c fixes a square root of the class of f) ∨ (c fixes a square root of
  the class of g)`,

i.e. **the archimedean local Tate pairing is the real Hilbert symbol
`(α, β)_ℝ = 1 ⟺ α > 0 or β > 0`**.  With this, and Hilbert reciprocity
(`Work.HilbertSymbolGeneral.hilbertReciprocityTwo`, which counts the archimedean places), the
archimedean contribution to the reciprocity sum becomes arithmetic — which is what the joint
reciprocity `hrecJoint` of `E7Arch.glue_of_finiteHalf` needs (it provably *cannot* be split into a
finite and an archimedean statement: the `k = ℚ`, `p = 2` sign-character counterexample recorded in
`E7Arch/g1Assembly.lean` has `inv₂ = inv_ℝ = 1`).

**The finite-place half of reciprocity, arithmetic form — done in this session.**  The new module
`Submission.Work.SSGRoute.ZDataTwo.FiniteReciprocity` (imported below, sorry-free) proves the
`p = 2` content of the reciprocity clause on the finite side:

* `isLocalNorm_of_unramified_of_val_pow` — at a finite prime `Q` where `L/K` is unramified (some
  `q | Q` of ramification index one), `x ∈ Kˣ` is a local norm as soon as `v_Q(x)` is an `f(q|Q)`-th
  power in the value group (composition of `NK.NUV2.LC.localIncl_mem_range_localNormFinite_iff`,
  i.e. the unramified norm group `NK.Unramified.NormGroupEqUnramified`, with the idèle bridge
  `Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup`);
* `isLocalNorm_of_notMem_of_finite_unramified` — same at every place outside `T`;
* `badSet_subset_and_even` — **the product formula restricted to `T`**: if `b`, `c` are unramified
  outside `T` (the archimedean sign conditions being the `hinf` hypothesis, supplied by the
  ArchKummer dictionary for a quadratic `K(√b)/K`), then the set of places at which the local
  pairing of the two classes is non-trivial is *contained in `T`* and has even cardinality
  (Hilbert reciprocity, `Work.HilbertSymbolGeneral.hilbertReciprocityTwo`).  Consequently the
  reciprocity sum is the sum over `T` and vanishes there.

With the archimedean half above, both summands of `E7Arch.glue_of_finiteHalf`'s `hrecJoint` are now
arithmetic (local norms and signs); what is still owed for the joint statement is the identification
of the *finite-place* local Tate pairing with the local norm/Hilbert-symbol pairing, i.e. the
finite-place half of the `E7` canonicity — the one genuinely large remaining piece of the
realisation, alongside the realisation step itself.

**Item 1, the finite-place identification — its exact shape, and where it is *not* a wall.**  The
finite local Tate pairing at `μ₂`-coefficients has to be identified with the norm/Hilbert-symbol
pairing, i.e. one needs the classical identity `inv(χ_a ∪ χ_c) = (a,c)_𝔭`, equivalently

  the value of the Kummer character of `a` at a Frobenius of `𝔭` is trivial  ⟺  `c` is a local norm
  at `𝔭` from `K_𝔭(√a)/K`,

equivalently "the archimedean argument of the last stretch, at a finite place".  What is already in
the workspace, so that this is a choppable rather than a monolithic task:

* the *local* duality statements are proved (`Work.SSGRoute.local_tate_duality_mup`,
  `local_tate_duality_mup_dim`, `local_tate_duality_02`, `local_tate_duality_euler`,
  `local_tate_duality_archimedean`): the two local `H¹`-groups of the `μ_p`-pair have the same
  dimension — the counting half of non-degeneracy — and the rank-one module algebra
  (`smul_tensor_trivial`) identifies the second coefficient module with the trivial one;
* the *arithmetic* half of the pairing (both variables) is now on disk as well: at a finite place
  unramified in `K(√b)/K`, the pairing of the two classes is trivial as soon as the second class is
  unramified there (`ZDataTwo/FiniteReciprocity.isLocalNorm_of_unramified_of_val_pow`,
  `badSet_subset_and_even`), and at an archimedean place the pairing *is* the sign pairing
  (`ZDataTwo/archPair_two_kummer_eq_zero_iff`).
* what remains is the *definition* of the finite-place family on the node's cocycles (the local
  Kummer class of a cocycle on `decomp k A ⊓ G_K`, transported along the local Kummer dictionary
  `ZDataTwo/KummerCocharBase.kummerCochar_eq_zero_iff_localPowClass`, with the local Kummer
  bijection supplying the class of an arbitrary cocycle) together with the two clauses the family
  still owes at a *ramified* finite place — the tame-symbol/Frobenius computation.  For this node
  only the `μ₂` case is needed (`M = 𝔽₂`, trivial action), which is why the arithmetic route above
  applies at all; the general-`M` family is the `E7` workshop's business.

**Why the §4 verification was *not* decomposed further this stretch.**  Its remaining content after
`ZDataTwo/localPowClass_three_term_agree` is exactly two things: (i) the product-formula instances
`(z_s)_{σP_t} = 0` for `s < t` — these *are* the finite-place identification above, so they must
wait for it; and (ii) the `G₂`/`G₃` case analysis of condition (4) together with the `Φ_N`
bookkeeping, which needs the sequence predicate designed first.  Everything that could be handed out
without those two (the (A)- and (B)-bookkeeping) is already proved, so an extra "bookkeeping" request
now would only duplicate `localPowClass_three_term_agree`; the honest next hand-off is the sequence
predicate itself, once (i) exists.

**Clause (b): the unramified half is closed, and the Frobenius form's exact bottle-neck.**

The pairing of an *unramified* class at a finite prime `Q` (`Q ∤ 2`, some `q | Q` of ramification
index one) is now completely determined, by the two halves of the criterion

  `x` is a local norm at `Q`  ⟺  `v_Q(x) = v_Q(y)^{f(q|Q)}` for some `y`  (i.e. `f(q|Q) ∣ v_Q(x)`),

namely `ZDataTwo/FiniteReciprocity.isLocalNorm_of_unramified_of_val_pow` (⟸) and
`ZDataTwo/exists_inertiaDeg_pow_of_isLocalNorm_of_unramified` (⟹, the tame half, whose proof is the
`.mp` direction of `NK.NUV2.LC.localIncl_mem_range_localNormFinite_iff` after collapsing the `iSup`
of `localNormSubgroup` with `NK.CFTLib.IdeleHasse.range_localNormFinite_eq_of_liesOver`).  In the
quadratic case this reads: the pairing of an unramified class with `x` is trivial exactly when
`v_Q(x)` is even — the arithmetic form of the Frobenius/tame-symbol half of clause (b).

*The Frobenius form of clause (b), stated as it should be proved.*  What the §4 verification still
needs is the sister statement, in the node's own vocabulary:

  for `b ∈ (↥K)ˣ` unramified at the finite place `A` (`A ∤ 2`) and `σ ∈ decomp k A ⊓ G_K` a
  *Frobenius* at `A`:  `nodeKummerCochar … b σ = 0`  ⟺  `b ∈ (K_𝔭ˣ)²`  (⟺ the cochain of `b` vanishes
  on the whole local group `decomp k A ⊓ K.fixingSubgroup`, by
  `ZDataTwo/KummerCocharBase.kummerCochar_eq_zero_iff_localPowClass`).

Its `⟸` half is immediate (an unramified class kills the inertia,
`kummerCochar_eq_zero_of_isInertia_of_even_valuation`, so the character factors through `D/I`).
The `⟹` half is the one place where *the spelling of "σ is a Frobenius" decides the statement*: for a
general `σ ∈ D ∖ I` the implication is **false** (the unramified character of `D/I ≅ Ẑ` vanishes on
the even part of `Ẑ`), so a hypothesis is needed that pins `σ` to the generator modulo inertia.  Two
spellings are available and both fit the workspace's existing material:

* through a finite level, as the banked Chebotarev step `ZDataTwo/chebotarev_frobenius_split` does:
  `res k L σ = res k L τ` for the prescribed `τ` whose class is the Frobenius of the prime of `L`
  below `A` (this is the `IsFrobAt` form of `NK.Chebotarev`), the level `L` ranging over finite
  Galois subextensions;
* through the residue field of `A`: `σ x ≡ x^{q}` modulo the maximal ideal of `A` for all `x ∈ A`,
  `q` the cardinality of the residue field of `K/𝔭` (this is the "geometric Frobenius" form, and it
  makes the determinant step — `D/I ↠ Ẑ` is onto, so its image generates — a residue-field
  computation).

Which spelling the node's consumers prefer is a vocabulary question, not a mathematical one; it is
the first thing to settle before the request goes out, because the statement above with the
hypothesis dropped is false while the same statement with it is a two-step proof from
`kummerCochar_eq_zero_of_isInertia_of_even_valuation`, the dictionary, and the cyclicity of `D/I`.

**Clause (b) is done — both halves are on disk.**

*The arithmetic (tame) half*: the iff `x` is a local norm at an unramified `Q` ⟺ `f(q|Q) ∣ v_Q(x)`
(`ZDataTwo/FiniteReciprocity.isLocalNorm_of_unramified_of_val_pow` together with
`ZDataTwo/exists_inertiaDeg_pow_of_isLocalNorm_of_unramified`), which in the quadratic case reads
"the pairing of an unramified class is trivial exactly when the second valuation is even".

*The Frobenius form, hence the interface to the cochains*:
`Work.SSGRoute.ZDataTwo.kummerCochar_eq_zero_of_isFrobAtPrime_eq_zero` (module of the same name,
proved): for `b ∈ (↥K)ˣ` unramified at a finite place `A` with `A ∤ 2`, and `σ ∈ decomp k A ⊓ G_K`
restricting to a Frobenius at a level `L` (`NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) p`, the
finite-level spelling of the banked Chebotarev step; the accompanying `¬ IsRamifiedIn k L A` is
produced for free by that step), with the cochain of `b` constant on the cosets of `ker (res k L)`
in the local group: the value at `σ` vanishing forces the cochain to vanish on the **whole** local
group — i.e. `b` is a local square at the prime of `K` below `A`, by
`ZDataTwo/KummerCocharBase.kummerCochar_eq_zero_iff_localPowClass`.  This is exactly the step
Schmidt–Wingberg use to turn "the Frobenius value of `z_s` at `σP_t` is `1`" into "the local class
`(z_s)_{σP_t}` vanishes".  The two reviewers split on whether the level-unramifiedness was needed
(one argued the residue-field argument makes it unnecessary, the other that `IsFrobAt` alone is a
weak congruence); since the banked Chebotarev step produces it anyway, the statement carries it and
both readings are satisfied.

**The interface piece, and why it is now purely mechanical.**  Every clause of the core has an
arithmetic form and its bridge is on disk: (A) the quotient dictionary
`kummerCochar_agree_iff_localPowClass` (this file); (B) `v_𝔭(b)` even ⟹ kills inertia
(`kummerCochar_eq_zero_of_isInertia_of_even_valuation`, this file); (C) the archimedean dictionary
`ZDataTwo/ArchKummer.nodeKummerCochar_eq_zero_on_involutions_iff`; (D) the local Kummer dictionary
plus the Frobenius form above.  So the core is now reducible — by bookkeeping alone — to the classical
statement: *there is `b ∈ Kˣ` which is a local square at the primes of `K` under `cs(S)` after
clearing `h`, is unramified at the primes outside `cs(S)` that are not split in `Λ`, is totally
positive, and whose ramification outside `cs(S)` is one-sided with square companions.*  That
reduction is the next thing to write down (and the first candidate to hand out).

**New lemmas proved in this session** (section "The quotient dictionary" below, sorry-free):
`kummerCochar_inv` (`z_{a⁻¹} = z_a`), `kummerCochar_div` (`z_{a b⁻¹} = z_a + z_b`) and
`kummerCochar_agree_iff_localPowClass` — the "agreement" form of the local Kummer dictionary, which
states conjunct (3) of the node as the local squarity condition `b h⁻¹ ∈ (K_𝔭ˣ)²` at the primes of
`K` under `cs(S)` (`b` the constructed class, `h` the Kummer class of `y`).

**Plan for the next stretches (in this order).**

1. *The real-place half of the core.*  The arithmetic form of condition (C) is "`b` is totally
   positive at the real places of `K`" (an involution of `G_K` is the conjugation at a real place,
   and `z_b c = 0` iff `c` fixes a square root of `b`, which for the conjugation at `v` is exactly
   `b > 0` at `v`).  `kummerIdx_eq_zero_of_apply_eq` gives the first half of this translation
   definitionally; only the real-closed-field reading of "`b > 0`" is extra.
2. *The §4 sequence, formally.*  Set up the predicate expressing Schmidt–Wingberg's conditions
   (1)–(4) for a sequence `z₁,…,z_N` of `𝔽₂`-valued cochains on `G_K` (ramified at exactly one new
   prime each, agreeing with `y` at `T`, and the two clauses (3),(4) controlled by the involution /
   non-involution partition `G = G₁ ⊔ G₂ ⊔ G₃`), together with the Claim
   `(z_i)_{σP_i} = 0` for `σ ∈ G₁`.  `ZDataTwo/{two_partition,pigeonhole_three,
   three_term_cancellation}.lean` already supply the combinatorial half, and
   `ZDataTwo/chebotarev_frobenius_split` the new-prime step, so what is missing there is only the
   *realisation* clause of condition (1).
3. *The verification of (a)+(b) from the sequence.*  This needs the identification of the local
   `𝔽₂`-valued pairing with the local Hilbert symbol (so that `z_s(Frob_{σP_t}) = (z_s, σz_t)_{σP_t}`
   and the product formula applies); for `p = 2` this is the same object as the reciprocity half
   recorded above, and it is the natural first target of the arithmetic work.
4. *The realisation with ramification control* (the Poitou–Tate degree-1 exactness at `p = 2`,
   including the archimedean places).  This is the project's outstanding `p = 2` input; everything
   else in §4 is already available or is mechanical.

**Banked pieces verified again in this session (do not redo them).**

* `Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split` (proved) *is* the odd-`p` lane's `sorry`
  `Work.SSGRoute.chebotarev_frobenius_split_sketch` (`z_data_mup_arith.lean`, Piece 2), up to the
  conditional Chebotarev input `NK.Reconstruct.ChebotarevDensityInput k Ω`.  Piece 2 of the odd
  lane can therefore be discharged by wiring this theorem in; the claim in
  `chebotarev_frobenius_split`'s own header that "the sibling's `chebotarev_sameFrobeniusClass_split`
  is false as stated" is what makes the compatibility hypothesis `res k N τ = 1` necessary.
* The `p = 2` combinatorics (`ZDataTwo/{two_partition,pigeonhole_three,three_term_cancellation}.lean`)
  and this session's arithmetic-free assembly lemmas (cyclicity of the image, Frobenius detection,
  splitting monotonicity, the conjugacy bookkeeping) are proved and axiom-clean.
* Re-derived in this session (as a check of the mechanism, for `k = ℚ`, `K = Λ = ℚ(i)`,
  `T = {(1+i),(2+i)}`, `h = 17`): with the single-prime ansatz `b = ρ` a prime element over a split
  rational prime `q`, condition (D) at the companion prime becomes `(Tr(ρ)/q) = 1`
  (`ρ + ρ̄ = Tr(ρ)` while `ρ̄ = q/ρ ∈ qℤ_q`), which is what makes the witness `5 + 4i` (over `q = 41`,
  `(10/41) = 1`) work, and which shows that the isolation condition is *not* automatic even in the
  simplest case.

## SESSION 13: the conjugation equivariance of the Kummer cochain, the ramification criterion, and the
## exact shape of the remaining gap

**Proved this session.**

(a) Module `Submission.Work.SSGRoute.ZDataTwo.kummerCochar_eq_zero_iff_mem_sq` (sorry-free):
`Work.SSGRoute.ZDataTwo.kummerCochar_eq_zero_iff_mem_sq` — **the kernel of the Kummer cochain is the
group of squares**: for `c ∈ Kˣ`, `z_c` vanishes on all of `Gal(Ω/k)` if and only if `c` is a square
in `Kˣ` (the injectivity of `Kˣ/(Kˣ)² ↪ Hom(G_K, μ₂)` in the node's vocabulary, via
`kummerChar_eq_zero_iff_apply_sqrt` and `InfiniteGalois.mem_bot_iff_fixed`).  This makes the Kummer
class of `y` well defined modulo squares and lets a construction replace `h` by any element in its
square class.

(b) Module `Submission.Work.SSGRoute.ZDataTwo.kummerCochar_conjElem` (sorry-free, axiom-clean):

* `Work.SSGRoute.kummerCochar_conjElem` — **the Galois equivariance of the Kummer cochain**:
  `z_{σ • b}(τ) = z_b(σ⁻¹ τ σ)` for `σ ∈ Gal(Ω/k)`, `b ∈ Kˣ` and every `τ ∈ Gal(Ω/k)` (where `σ • b`
  is the action through `AlgEquiv.restrictNormalHom K σ`).  This is the naturality statement that
  Schmidt–Wingberg's conditions `(3)`, `(4)` and the Claim `(z_i)^σ_{P_i} = 0` (for involutions `σ`)
  are phrased in, so every formalisation of §4 needs it.  Off `G_K` both sides vanish by normality
  of `K.fixingSubgroup` (`IsGalois k K`).
* `Work.SSGRoute.kummerIdx_eq_zero_iff_apply_eq` — the Kummer index of `σ` at a `p`-th root `γ`
  vanishes exactly when `σ` fixes `γ` (the converse of the workspace's
  `kummerIdx_eq_zero_of_apply_eq`), and `Work.SSGRoute.kummerChar_eq_zero_iff_fixes` — the same
  criterion at an *arbitrary* square root of the class, plus `Work.SSGRoute.kummerChar_eq_kummerIdx`
  (independence of the chosen root), `Work.SSGRoute.smul_sqrtVal_sq` and
  `Work.SSGRoute.algebraMap_restrictNormalHom` (the `σ`-image of a square root of `b` is a square
  root of the conjugate class).  These are the tools for transferring local class statements along
  conjugates.

**Delegated and returned proved** (module `Submission.Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq`):
`Work.SSGRoute.ZDataTwo.kummerCochar_ne_zero_of_val_not_sq` — the
*ramification* half of the inertia criterion: at a finite place `A` with `A ∤ 2`, if the
`A`-valuation of `b ∈ Kˣ` is not the square of the valuation of an element of `Kˣ` (i.e. `b` is not a
unit times a square at `A`, which for `A ∤ 2` means odd valuation), then the Kummer cochain of `b` is
non-zero somewhere in the inertia of `A`.  Together with the *proved* even-valuation lemma
(`kummerCochar_eq_zero_of_isInertia_of_even_valuation`, this file) this makes the inertia criterion
an equivalence:

  `z_b` kills the inertia of `A`  ⟺  `v_A(b)` is a square of a valuation of an element of `Kˣ`
  (for `A ∤ 2`).

Both directions are needed: the `⟸` half for the construction of `b` (it is what makes `z_b`
unramified at the allowed places), the `⟹` half to see that the *trigger* of the node's clause `(6)`
fires exactly where the valuation is odd — i.e. to verify clause `(D)` of `ArithCore` at the places
that the construction does *not* touch.  The two halves are consolidated, in the form the assembly
consumes, in the module `Submission.Work.SSGRoute.ZDataTwo.InertiaCriterion` (sorry-free):
`Work.SSGRoute.ZDataTwo.kills_inertia_iff_even_valuation` (the equivalence),
`Work.SSGRoute.ZDataTwo.exists_val_sq_of_kills_inertia` (**clause (5) of the node gives clause (B) of
`ArithCore`**) and `Work.SSGRoute.ZDataTwo.exists_decomp_ne_zero_of_not_localPowClass` (the converse
of the local Kummer dictionary, i.e. the form in which the trigger of clause (6) is certified).

**The remaining gap, re-examined; and a candidate alternative route.**  After this session the
remaining content of the node is unchanged: `ArithCore` (SW §4 for `p = 2`), whose blocked inputs are
`P1` (Tate–Poitou degree-1 realisation with ramification control — the SSGRoute PT lane) and, for its
*verification* half, the identification of the `μ₂` local Tate pairing with the local Hilbert symbol
at *ramified* places (the "tame symbol", i.e. the `E7` canonicity, also in the PT lane; the
*unramified* half is available in `ZDataTwo/FiniteReciprocity.lean`).  Note that the interface
`ZDataTwo.ArithCore` is *uniform in `h`* (its hypotheses mention only `K, Λ, ζ, S, h`), so the `∀h`
hypothesis of `kummerCore_of_arithCore` costs nothing extra: no "same Kummer cochain implies the same
square class" brick is needed.

A candidate route that avoids the Poitou–Tate exactness and is worth trying, recorded here so that it
is not lost: let `h` be the Kummer class of `y` and let `𝔮_1, …, 𝔮_m` be the finite set of places at
which `h` is ramified *two-sidedly* (at least two primes of `K` over `𝔮_i` with odd valuation).  Try
the ansatz

  `b = h · ∏_i π_i`,  `π_i` a prime element of `K` at a chosen prime `𝔭_i | 𝔮_i`.

Then `b` has odd valuation at exactly one prime over each `𝔮_i` (choose the `𝔭_i` so that the parities
work out), so clauses `(A)`–`(C)` of `ArithCore` become *finitely many prescribed local classes* of
the elements `π_i` (at the primes below `cs(S)`, at the two primes over each `𝔮_i`, and at the
companions of the surviving ramified primes), and clause `(D)` becomes the same kind of condition at
the companion primes — while clause `(B)` holds *by construction*, because the support of a prime
element is a single prime and the `𝔭_i` are chosen at places split in `Λ`.  So the whole core would
follow from a single **Chebotarev-type existence statement**: for a finite set of primes and prescribed
local square classes, there is a prime `𝔭` with a generator `π` realising them (the prescriptions are
congruence/Kummer conditions, hence Frobenius conditions in a ray class field times Kummer
extensions).  What is *not* automatic — and is exactly the content of Schmidt–Wingberg's pigeonhole —
is the **consistency** of the prescribed classes with the product formula, i.e. with the dual Selmer
group of the primes not controlled by the ansatz; the `π_i`'s local behaviour at all the primes
outside the finite list is free, which is why the ansatz has a chance.  This is the honest candidate
for a *PT-free* proof of the core, and the first thing a next session should test (on the example
`k = ℚ, K = Λ = ℚ(i), T = {(1+i),(2+i)}, h = 17`, where the ansatz predicts the witness
`b = 17 · u · (4+i)`, `u ∈ {±1,±i}`, if the unit `u` can be chosen so that `17 u (4+i)` is a local
square at `(4+i)`, in addition to `u(4+i)` being a local square at `2` and `5`).

*A hand check of that prediction* (not formalised; one arithmetic slip was caught and corrected while
doing it): `u = i` works.  Then `b = 17i(4+i) = -17 + 68i`, whose odd valuations are exactly those
at `(4-i)` (`v_{(4+i)}(b) = v(17) + v(4+i) = 2`, `v_{(4-i)}(b) = 1`), so `b` is ramified at a single
prime.  (A) `b h⁻¹ = i(4+i) = 4i - 1` is a square in `ℚ₂(i)` (`4i - 1 = (i(1+y))²` with
`y² + 2y = -4i`, solvable because `-4i = (1+i)⁴i` is divisible by `π³`) and in `ℚ₅` (the image under
`i ↦ -2` is `-9 = (-1)·3²`, and `-1` is a square in `ℚ₅` since `5 ≡ 1 mod 4`).  (D)
`b/(4+i)² = i(4-i)`, whose image under `i ↦ -4` is `-15 ≡ 2 mod 17`, and `2 = 6² mod 17` is a
square mod `17`, so `b` is a local square at the companion prime `(4+i)`.  (B) is automatic (the
support of `b` is `{(4+i),(4-i)}` and `17 ≡ 1 mod 4` splits in `ℚ(i)`), and `ℚ(i)` has no real
places.  So the ansatz does produce a witness here — a *different* one from the prime-over-`41`
witness recorded above, which is exactly why it deserves a try: it needs no new prime, only the
patience to choose the units.
-/

open scoped Pointwise

/-! ## PROGRESS (this session)

The formal statement is unchanged below.  What is *proved* in this file:

* `smul_eq_self_of_finrank_le_one_two` — **the action of `G_K = K ≃ₐ[k] K` on `E` is trivial.**
  For `p = 2` the module `E` is an `𝔽₂`-vector space of dimension `≤ 1`, so it is `0` or `𝔽₂`
  and every `𝔽₂`-linear automorphism of it is the identity.  This is the only structural fact
  needed to run the *elementary* construction `z := y` (extended by `0` off `G_K`).

* `z_data_two_agreement_conjuncts` — the cochain `z := (y on `G_K`, `0` off it)` satisfies
  conjuncts (1)–(5) of the conclusion: it is a locally constant `1`-cocycle on `G_K`, it agrees
  with `y` on the decomposition groups of `cs(S)`, it kills the involutions, and it kills the
  inertia of every finite place outside `cs(S)` that is not split in `Λ`.

* `z_data_two_cyclic_conjunct` — **the "cyclicity" half of Schmidt–Wingberg's (b) is automatic for
  `p = 2`**: every additive subgroup of a one-dimensional `𝔽₂`-space is cyclic, so the first
  conjunct of (6) needs no hypothesis.

THE REMAINING GAP.  After these reductions the *only* content of the theorem is the second
conjunct of (6) — Schmidt–Wingberg's sharpened (b):

  *if `B` is a finite place outside `cs(S)`, split in `Λ`, at which `z` is ramified
  (`∃ σ ∈ I_B ⊓ G_K, z σ ≠ 0`), then `z` vanishes on the local group `D_Q ⊓ G_K` of every
  `G_k`-conjugate `Q` of `B` that is not a `G_K`-conjugate of `B`.*

For the canonical candidate `z := y` this says `y τ = 0` for `τ ∈ D_Q ⊓ G_K`, which is **not**
a consequence of the hypotheses: the hypotheses constrain `y` only on the inertia of `cs(S)` (hyT),
on the inertia of the non-`cs(S)` places that are not split in `Λ` (hyS), on `D_B ⊓ G_K` for the
places of `cs(S)` that are not split in `K` or lie over `p` (hy0), and on the involutions (hyinf) —
none of them touches `D_Q ⊓ G_K` for a place `Q` that is split in `Λ` and not `G_K`-conjugate to
`B`.  Concretely, for `k = ℚ`, `K = Λ = ℚ(i)`, `p = 2`, `S = {A₂, A₅}` and `y` the class of
`17 ∈ K⁰` (trivial at the place over `2` because `17 ≡ 1 mod 8`; unramified with non-trivial local
component at both places over `5` because `17 ≡ 2` is a non-square mod `5`; trivial at all inert
primes, because for `p ≡ 3 mod 4` the unramified quadratic extension of `ℚ_p(i)` is `ℚ_p(ζ₃)`, so
every non-square unit of `ℚ_p` becomes a square in `ℚ_p(i)`), all hypotheses hold, while `z := y`
is ramified at both places over `17` and non-trivial at both, so (b) fails at the place over `17`.

Hence the theorem is *strictly stronger* than Schmidt–Wingberg's Theorem 13, whose standing
hypothesis is `y ∈ H¹(k_S|K, A)`, i.e. `y` unramified at **all** places outside `S`, whereas the
formalisation only assumes this for the places that are not split in `Λ`.  Note that the classical
"`p = 2` is the exceptional prime of Grünwald–Wang" explanation in the docstring above is **not**
the reason for the difficulty here: for exponent `n = 2` the Grünwald–Wang exceptional case
(`2^{s+1} | n`, `s ≥ 2`) cannot occur, and the realisation step of the construction is now proved
in the workspace as `Work.SSGRoute.grunwald_surjective_two` (the `p = 2` twin of
`grunwald_surjective_odd`), which realises *arbitrary continuous local data* on the decomposition
groups of a finite set of places by a continuous additive character of `G_K`.

What remains is exactly the §4 construction of the paper: build the sequence `z₁, z₂, …` with
`z_{n+1}` realising prescribed local data at `T_n(K)` and at one *new* prime `P_{n+1}` chosen by
Chebotarev (`Work.SSGRoute.bauer_of_chebotarev`), so that `z_{n+1}` is unramified at `P_i^{σ}`
(`i ≤ n`, `σ ≠ 1`); then the pigeonhole principle on the finitely many values of the Frobenius
data `Φ_N` produces `i < j < N` with `Φ_N(z_i) = Φ_N(z_j) = Φ_N(z_N)`, and `z := z_i + z_j + z_N`
satisfies (a) and (b) by the Hilbert-symbol product formula and the "Claim" (`(z_i)_{σP_i} = 0`
for `σ` an involution, whose proof needs a prime `Q` in the ideal class of `𝔄` with `Q ≠ Q^σ`,
via Chebotarev in the Hilbert class field, and the `(2b, z̃)` Hilbert-symbol chain).  The helper
lemmas below are the part of that assembly which does not need arithmetic.

## SESSION 2 (progress, verified statements, and the exact remaining gap)

### 1. The statement is TRUE, and `z := y` fails: a verified witness.

Session 1 produced data (`k = ℚ`, `K = Λ = ℚ(i)`, `p = 2`, `S = {A₂, A₅}`, `y =` the Kummer class
of `17 ∈ Kˣ`) for which all hypotheses hold but the canonical candidate `z := y` violates (6) at the
two places over `17`.  This session verified *explicitly* that a valid `z` does exist for that data:
take `x := 5 + 4i` (so `N(x) = 41` is prime, `41 ≡ 1 mod 8`, `41 ≡ 1 mod 5`, `41 ≡ 1 mod 4`) and
let `z` be the Kummer character of `x`.  Check:
* `z = y` on `D_B ⊓ G_K` for `B ∈ cs(S)`: at the place `𝔭 | 2` one has `(c + di)² = 5 + 4i` for
  `c² = (5 + √41)/2 ≡ 9 ≡ 1 (mod 8)` (so `c ∈ ℚ₂`, `d = 2/c`), hence `[x]_𝔭 = 1 = [17]_𝔭 = [y]_𝔭`;
  at the two places over `5`, `5 + 4r ≡ 3 (mod 5)` resp. `5 - 4r ≡ 2 (mod 5)` (for either root `r`
  of `-1` in `ℚ₅`), both non-square units, i.e. `[x]_𝔮 = [x]_{𝔮'} = [2] = [17] = [y]`.
* (5): `div(x) = (5 + 4i)`, so `x` is unramified at every place except the single place `B₀ | 41`;
  in particular at all inert primes `q ≡ 3 (mod 4)`.
* (6): the only ramified place is `B₀ | 41`, split in `Λ = ℚ(i)`; its conjugate is the other place
  over `41`, where `x ↦ 2a = 10` and `(10/41) = (2/41)(5/41) = 1·1 = 1`, so `x` is trivial there.
* (4): `G_{ℚ(i)}` has no involutions (an involution would fix a real closed field, which cannot
  contain `i`); for general `K` the clause is the "`x` positive at all real places" condition.

So the difficulty is not the shape of the statement but the *existence*, in general, of such an
`x`: the ramification must be moved off the "paired" places of `y` onto new, partner-isolated split
places, while the local data of `y` at `cs(S)` is preserved.  The witness above is the
"one new ramified prime" instance of the SW §4 construction.

### 2. The remaining gap, cut into the same pieces as the odd-`p` sibling

* **P1 (local Kummer dictionary):** `z_a` vanishes on `decomp k A` iff `a` is a local square at the
  prime `𝔭` of `K` below `A`.  Stated in the workspace as
  `Work.SSGRoute.kummerChar_eq_zero_iff_local_powClass`, **still a `sorry`**, but its ingredients
  (`NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff`,
  `splitsCompletely_iff_forall_localDeg_eq_one`, `kummerChar`, `kummerChar_mul`,
  `kummerIdx_mul_apply`) are on disk: a genuine, reachable target.
* **P2 (Tate–Poitou exactness in degree 1, realisation form):** local data at a finite set of
  places, orthogonal to the dual Selmer group, is realised by a global class unramified outside that
  set.  **Not available in this workspace** (`poitou_tate_degree_two_surj.lean` records that "the
  duality itself is *not* available"; the sibling's `tatePoitou_h1_realisation_sketch` is a
  `sorry`).  This is the bottleneck of this node and of the odd-`p` sibling.
* **P3 (Chebotarev new-prime step): DONE.**  `Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split`
  (`Submission/Work/SSGRoute/ZDataTwo/chebotarev_frobenius_split.lean`) is **proved, sorry-free and
  axiom-clean** (`#print axioms` gives `propext, Classical.choice, Quot.sound`): for `τ` with
  `res k N τ = 1` there is a place `B`, avoiding a finite set `T'` of pairwise
  non-`G_k`-conjugate places, with `¬ IsRamifiedIn k L B`, `IsSplitIn k N B` and
  `σ ∈ decomp k B` with `res k L σ = res k L τ`.  Every ingredient is proved in
  `Submission/Work/SSGRoute/shafarevich_theorem13.lean`
  (`exists_isFrobAtPrime_notMem_finite`, `map_res_decomp_eq_stabilizer_valuationRing`,
  `isSplitIn_iff_primesOver_ncard`, `levelSub_le_fixingSubgroup_of_ramificationIdx_eq_one`,
  `not_isRamifiedIn_of_levelSub_le_fixingSubgroup`, `isFinPlace_of_comap_valuationSubringAtPrime`,
  `finite_setOf_primeUnder`, `finite_setOf_primeUnder_ramified`,
  `not_isConjPlace_of_notMem_primeUnder`).  **Caveat found this session:** the general-`k`
  Chebotarev density theorem is *conditional* here — it comes from
  `NK.Chebotarev.ArtinReciprocityInput k L` at every finite Galois level
  (`NK.Reconstruct.chebotarevDensityInput_of_artinReciprocity`,
  `NK.Reconstruct.exists_isFrobAtPrime_mem_of_hasFullDensity`), so it must be carried as a
  hypothesis `hc : NK.Reconstruct.ChebotarevDensityInput k Ω`.  With that hypothesis the
  lemma is a pure assembly, and it is now finished in the module above (the "bad" set there also
  contains the primes of `k` ramified at the levels `L` and `N`, which is what makes the
  unramifiedness bookkeeping immediate).
* **P4 (Hilbert-symbol product formula):** available (`NK.CFTLib.hilbertReciprocity_cyclic`,
  `Work.HilbertSymbol.hilbertReciprocity_prod`); the p = 2 local Tate system is the piece to state.
* **P5 (p = 2 combinatorics): DONE.**  Three sorry-free, axiom-clean modules in
  `Submission/Work/SSGRoute/ZDataTwo/`:
  * `Work.SSGRoute.ZDataTwo.two_partition` (`two_partition.lean`) — the `p = 2` partition of
    `G ∖ {1}` into `G₁` (the involutions), `G₂` and `G₃ = G₂⁻¹`, pairwise disjoint and covering,
    with `σ ∈ G₂ ∪ G₃ ⟹ σ² ≠ 1`; built from the fixed-point-free inversion pairing outside `G₁`
    with `Fintype.equivFin` as the tie-breaker;
  * `Work.SSGRoute.ZDataTwo.pigeonhole_three` (`pigeonhole_three.lean`) — the three-term
    shoe-box principle `∃ i < j < N, a i = a j = a N` for `a : ℕ → ι` with `ι` finite (the
    `p = 2` strengthening of the sibling's two-term `pigeonhole_two_eq`), proved by applying the
    two-term pigeonhole to `k ↦ (a k, decide (∃ i < k, a i = a k))` in `ι × Bool`;
  * `Work.SSGRoute.ZDataTwo.three_term_cancellation` (`three_term_cancellation.lean`) — the
    characteristic-`2` cancellation `x + 0 + x = 0` behind the paper's
    "`(z_i)_{σP_i} + 0 + (z_i)_{σP_i} = 0`".

  All three have `#print axioms = [propext, Classical.choice, Quot.sound]`.  Together with the two
  algebraic reductions proved above (`smul_eq_self_of_finrank_le_one_two`,
  `z_data_two_cyclic_conjunct`) this is the arithmetically free part of the `p = 2` case; the
  remaining `p = 2`-specific input is the arithmetic core P2.

### 2b. Session 3: which pieces are now banked

* **P3 — banked.**  `Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split`
  (`Submission/Work/SSGRoute/ZDataTwo/chebotarev_frobenius_split.lean`, 230 lines) is proved,
  sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`).  Its "bad" set contains the
  primes of `k` below `T'` and those ramified at the levels `M = L ⊔ N`, `L` and `N`; that is what
  makes the unramifiedness bookkeeping immediate (`levelSub_le_fixingSubgroup_of_ramificationIdx_eq_one`
  applied at the level `L`, followed by `not_isRamifiedIn_of_levelSub_le_fixingSubgroup`), while the
  complete-splitting clause goes through the prime–place bridge at the level `N`, the triviality of
  `decompositionSubgroup (P.under (𝓞 ↥N))` (`decompositionSubgroup_eq_zpowers_of_isFrobAt` +
  `IsFrobAtRestrictNormalHomType` + `hτ`), and the Frobenius clause through the bridge at `M`,
  `mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup`,
  `mem_decompositionSubgroup_iff_smul`, `IsFrobAtStabilizes` and
  `IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply`.
* **P1 — stated, refereed, route fixed, delegation filed.**  Both reviewers approved
  `Work.SSGRoute.ZDataTwo.local_kummer_dictionary`
  (`Submission/Work/SSGRoute/ZDataTwo/local_kummer_dictionary`, draft in the queue) and confirmed
  the route: `kummerChar a σ = 0 ↔ σ` fixes the Kummer field `N = K(√a)`
  (`kummerIdx_spec` + `kummerField_eq_adjoin_simple` + `mem_fixingSubgroup_iff`) ⟺
  `D_A ≤ N.fixingSubgroup` ⟺ 𝔭 splits completely (`stabilizer_le_fixingSubgroup_iff_splitCompletely`)
  ⟺ all local degrees are `1` (`splitsCompletely_iff_forall_localDeg_eq_one`) ⟺
  `∃ b, a = b²` in `K_𝔭ˣ` (`localDeg_kummerField_eq_one_iff`) ⟺
  `localPowClass ↥K 2 𝔭 a = 1` (definition of `localPowClass`).  Note the workspace already carries
  an *unproved* copy of this statement at
  `Submission/Work/SSGRoute/kummerChar_eq_zero_iff_local_powClass.lean` (a colleague's file, not to
  be edited); whichever is proved first should be imported by this node.
* **P2 (Tate–Poitou for `μ₂`) — still the blocker**, and still absent from the workspace.

### 2c. Session 3 (cont.): the neighbours have moved; do not duplicate

While this node was being worked on, three sibling nodes landed or were opened in
`Submission/Work/SSGRoute/ZConstruction/`:

* `localKummerDictionary.lean` — **proves `Work.SSGRoute.local_kummer_dictionary` for every prime
  `p`** (in the `ZMod p`-valued `kummerCharZMod` form; `0` sorries at the time of writing).  Its
  proof contains exactly the bridge "the character vanishes at `σ` iff `σ` lies in the fixing
  subgroup of the Kummer field" (`ZConstruction/localKummerDictionary.lean`, the `hchar` step), so
  the two `local_kummer_dictionary` delegations filed for this node (paths
  `Work.SSGRoute.ZDataTwo/local_kummer_dictionary` and
  `Work.SSGRoute.ZDataTwo/kummerChar_eq_zero_iff_mem_kummerField`, both refereed and approved)
  are **superseded by a stronger, already-proved statement** and should not be re-requested.  This
  node should import it (for `p = 2`, via the identity of `Work.SSGRoute.kummerChar` with
  `kummerCharZMod 2`) instead of proving a copy.
* `ZDataBridge.lean` — proves `Work.SSGRoute.shafarevich_z_construction_of_zData`: the interface
  from the `z`-data with Schmidt–Wingberg's **ramification trigger** (exactly the conclusion of this
  node) to `Work.SSGRoute.shafarevich_z_construction`.  This *resolves* the trigger mismatch
  recorded in Session 1 (the older `ZConstruction/SWData.lean` used the weaker trigger
  "`z` does not vanish on `decomp k B ⊓ G_K`"): the chain this node feeds is now
  `shafarevich_z_data_two ⇒ zData-interface ⇒ shafarevich_z_construction`.
* `ZDataGeneral.lean` — isolates `Work.SSGRoute.z_data_general`, the same local-data existence for a
  general coefficient module `A` (all `p`).  Its header states that nothing in it is proved and that
  it records the single remaining obligation of `shafarevich_z_construction`.  If that node lands,
  this node follows from it by specialisation (`p = 2`, `dim_{𝔽_p} E ≤ 1`, trivial action) — so the
  cheap remaining work here is (i) the `p = 2` combinatorics (P5) and (ii) the transport from
  `z_data_general`/`local_kummer_dictionary` to this node's vocabulary.

### 2d. Session 4: the exact interface, and where the Tate–Poitou work stands

* **The interface is literal.**  `Work.SSGRoute.shafarevich_z_construction_of_zData`
  (`Submission/Work/SSGRoute/ZConstruction/ZDataBridge.lean`, sorry-free) takes as its hypothesis
  `hzdata` the *verbatim* conclusion of this node: `z` additive on `G_K` and locally constant there,
  agreeing with `y` on the decomposition groups of `cs(S)`, killing the involutions, killing the
  inertia of the places outside `cs(S)` that are not split in `Λ`, and satisfying (b) with the
  **ramification trigger** — image cyclic on `decomp k B ⊓ G_K` plus vanishing on the local group of
  every conjugate of `B` that is not a `G_K`-conjugate.  So this node plugs into that bridge with no
  rewording, and the bridge plus `Work.SSGRoute.cyclic_transfer_of_vanishing` (both sorry-free) is
  the whole of the consumer side.
* **What is left is exactly Schmidt–Wingberg §4 for `p = 2`.**  Its non-arithmetic parts are now
  banked: the new-prime Chebotarev step
  (`ZDataTwo/chebotarev_frobenius_split`, this session), the partition
  `G(K|k) ∖ {1} = G₁ ⊔ G₂ ⊔ G₃` (`ZDataTwo/two_partition`), the three-term shoe-box
  (`ZDataTwo/pigeonhole_three`) and the characteristic-`2` cancellation
  (`ZDataTwo/three_term_cancellation`).  The arithmetic input — the degree-1 Tate–Poitou
  *realisation* for `μ₂`: local data at a finite set of places, orthogonal to the dual Selmer group,
  is realised by a global class unramified outside that set — is the one missing statement.
* **Where that input now stands** (checked this session).  The Poitou–Tate workshop
  `Submission/Work/SSGRoute/PT/` has the *counting step* **proved and sorry-free**
  (`Work.SSGRoute.PT.wbot_le_of_natCard` in `PT/pt_counting_assembly.lean`: a pairing non-degenerate
  on both sides with `V ⊆ W^⊥` and `|V| · |W| = |P|` gives `W^⊥ ≤ V`), and it names its two
  remaining inputs explicitly: the canonical local pairing (`SSGRoute/PT/pt_canonical_pairing`) and
  the Selmer counting identity (`SSGRoute/PT/pt_selmer_counting_identity`), plus the assembly
  `pt_realization_of_pairing_and_counting` (the statement `Work.SSGRoute.PT.pt_canonical_relaxed`,
  `PT/pt_canonical_relaxed.lean`, still has `5` sorries).  The local Tate duality inputs
  (`local_tate_duality_finite`, `local_tate_duality_mup`, `local_tate_duality_mup_base`,
  `local_tate_duality_mup_dim`) are sorry-free; `PT/localTatePairing_deg02.lean` (6 sorries),
  `PT/localEulerCharacteristic_of_not_residueChar.lean` (4) and `PT/localDuality02.lean` (1) are the
  active work in progress there.  The sibling `Submission/Work/SSGRoute/z_data_mup_arith.lean`
  carries the odd-`p` twin of the same obligation as `tatePoitou_h1_realisation_sketch`.
* **Consequence for this node (corrected after the archimedean finding below).**  The statement to
  be *used* here is the `p = 2` instance of `Work.SSGRoute.PT.pt_selmer_relaxed`
  (`Submission/Work/SSGRoute/pt_selmer_relaxed.lean`, one `sorry` left), which has the right shape
  for `p = 2`: its pairing is indexed by the decomposition groups **and** by the subgroups
  `Subgroup.zpowers c` of the involutions `c` (i.e. the real places), its local axioms are stated
  for those two kinds of `H`, and its reciprocity hypothesis sums over a finite set `S'` of finite
  places *together with* a set `C'` of involution representatives, the conclusion being the
  realisation of the prescribed local data (at `S ∪ C`) by a global cocycle unramified outside
  `S ∪ cs(N)`.  For this node take `p = 2`, `M = T = ZMod 2` (trivial action, so that
  `IsCyclotomicDual 2 (res k K) ζ` holds) — the one-dimensional coefficient module.  Feeding that
  plus `ZDataTwo/chebotarev_frobenius_split`, `ZDataTwo/two_partition`,
  `ZDataTwo/pigeonhole_three`, `ZDataTwo/three_term_cancellation` and the involution clause is the
  remaining assembly work of this node.  Nothing in this node's statement needs a general
  coefficient module.  (The `p = 2`, finite-places-only statement delegated earlier,
  `Work.SSGRoute.ZDataTwo.tatePoitou_h1_realisation_two`, is *not* the right ingredient on its own:
  see the next paragraph.)

### 2e. Session 4 (cont.): the archimedean places are NOT optional for `p = 2`

A referee report on the obvious `p = 2` specialisation of the sibling's
`exists_localTateSystem_productFormula` (path `Work.SSGRoute.ZDataTwo/localTateSystem_productFormula_two`,
statement in the queue) found it **false as stated**: taking `k = K = ℚ`, `T' = {A}` with `A` the
place above `2` and `a = b = χ_{-1}`, all the hypotheses hold, but the conclusion forces the local
Tate pairing to vanish on the two-dimensional space of global characters unramified outside `2`
inside the three-dimensional `H¹(ℚ₂, μ₂)` — contradicting non-degeneracy.  The reason is structural:
for odd `p` the archimedean places contribute trivially to `H²(ℝ, μ_p)` (as `ℝ` contains no
non-trivial `p`-th root of unity), so the Hilbert-symbol product formula over the *finite* places
alone holds; for `p = 2` it acquires the archimedean factor `(a,b)_∞`, so the finite-place sum is
`-(a,b)_∞` in general.

Consequences for this node, which must be respected when the §4 input is stated:

* the `p = 2` analogue of the sibling's `tatePoitou_h1_realisation_sketch` may keep the pairing as a
  *hypothesis* (then it is a genuine conditional statement, and the pairing-free case is restored by
  the archimedean data), but the **producer** of that pairing must include the real places.  The
  project's own Poitou–Tate statement `Work.SSGRoute.PT.pt_selmer_relaxed` already has the right
  shape — "local data at `S` (one place per prime) **and** local data at the real places `C`" — and
  the archimedean pairing machinery exists (`Work.SSGRoute/archPair_nondegenerate.lean`,
  `Work.SSGRoute/LTDArch/`).  A `p = 2` pairing statement must be quoted in *that* shape, not in the
  finite-places-only shape of the odd-`p` sibling;
* this is exactly why the formalisation of the *conclusion* of this node carries the involution
  clause `z c = 0` for `c² = 1` (the real places are encoded as involutions), and why the `p = 2`
  construction of Schmidt–Wingberg needs the three-term sum with `G₁` the involutions
  (`ZDataTwo/two_partition`): the archimedean places are precisely the ones the involution clause,
  the partition and the `(z_i)_{σP_i} = 0` claim for `σ ∈ G₁` handle.

### 2f. Session 4 (cont.): the fleet's verdict on the `p = 2` realisation — it *is* `V^⊥ = V`

The `p = 2`, finite-places-only realisation delegated as
`Work.SSGRoute.ZDataTwo.tatePoitou_h1_realisation_two` came back from the fleet **refused**, with a
machine-checked structural analysis (the prover's judgment; the path is free again):

* for `p = 2` with trivial coefficients every `DistribMulAction` on `ZMod 2` is trivial, so
  `IsCocycleOn` is plain additivity and — unlike the odd-`p` case — `IsCoboundaryOn H f` is
  *exactly* "`f` vanishes on `H`": there is **no coboundary slack**;
* hence, writing `Sel_T` for the verbatim hypothesis class of `horth` and `V` for its image in the
  product of the local groups `∏_{A∈T} Z(D_A ⊓ G_K)`, the lemma is literally the assertion
  **`V^⊥ = V`** — the localisation image of the (relaxed) Selmer group is its own orthogonal
  complement, i.e. a *Lagrangian* in the product of the local Kummer groups;
* the same verdict was recorded by the fleet for `SSGRoute/pt_sha2_core` and
  `SSGRoute/pt_localPairing`, and `Work.SSGRoute.PT.pt_selmer_relaxed` has the same last `sorry`.

So the `p = 2` realisation is neither a formal triviality nor an accident of the statement: it *is*
the Poitou–Tate duality for `μ₂`.  The statement is not mathematically false (the fleet agrees), but
it is the parked arithmetic obligation of this node, and its formalisation must reproduce the
Poitou–Tate machinery (`PT/pt_counting_assembly` proves the counting step; the canonical local
pairing and the Selmer counting identity are the two named open inputs, and the archimedean data
must be carried — §2e).

### 2g. Session 4 (cont.): the chain from the `p = 2` pairing to this node, itemised

Putting §2d–§2f together, the arithmetic input of this node decomposes as follows (each item
labelled with where it lives):

1. **The `p = 2` local Tate system with the archimedean reciprocity** —
   *placed this session*: `Work.SSGRoute.ZDataTwo.mu2_localTateSystem_with_archimedean`
   (`Submission/Work/SSGRoute/ZDataTwo/mu2_localTateSystem_with_archimedean.lean`), refereed and
   approved by two reviewers and delegated.  It asserts the existence of a pairing indexed by the
   finite decomposition groups **and** the involution subgroups `Subgroup.zpowers c`, satisfying
   biadditivity, vanishing on coboundaries and perfectness there (local Tate duality for the
   self-dual module `ZMod 2`), and the **`S' ∪ C'` reciprocity** — the archimedean-corrected
   product formula of §2e.  It is exactly the `p = 2`, `M = T = ZMod 2` specialisation of
   `Work.SSGRoute.canonical_localPairing_with_reciprocity`
   (`Submission/Work/SSGRoute/canonical_localPairing_with_reciprocity.lean`, the workspace's
   `G1 + reciprocity` input, one `sorry` left), so it is the more tractable gate: no naturality
   clauses, no cyclotomic-dual bookkeeping, one coefficient module.
   Its archimedean half is *already proved* in the shape of the concrete pairing
   `SSGRoute.Ach.archPair` — `Work.SSGRoute.archPair_nondegenerate`
   (`Submission/Work/SSGRoute/archPair_nondegenerate.lean`, sorry-free, all `p`) — and the
   archimedean local `H¹` machinery is `Submission/Work/SSGRoute/LTDArch/`,
   `local_tate_duality_archimedean.lean` (sorry-free).
2. **The counting step** — *proved*: `Work.SSGRoute.PT.wbot_le_of_natCard`
   (`PT/pt_counting_assembly.lean`, sorry-free): a pairing non-degenerate on both sides with
   `V ⊆ W^⊥` and `|V| · |W| = |P|` has `W^⊥ ≤ V`.
3. **The Selmer counting identity** `|V| · |W| = |∏_{S ∪ C} H¹|` — still open, named by the PT
   workshop as `SSGRoute/PT/pt_selmer_counting_identity`.
4. **The realisation** — `Work.SSGRoute.PT.pt_selmer_relaxed`
   (`Submission/Work/SSGRoute/pt_selmer_relaxed.lean`): the local data at `S ∪ C`, orthogonal to
   the dual Selmer group, is realised by a global cocycle unramified outside `S ∪ cs(N)`.  Proved
   from 1–3 by the assembly `pt_realization_of_pairing_and_counting`
   (`PT/pt_canonical_relaxed.lean`, 5 sorries).  This is the `p = 2` instance that this node
   consumes; note that `pt_selmer_relaxed` has no `hp : p ≠ 2`, so `p = 2` is covered by taking
   `M = T = ZMod 2` (trivial action on both, so `IsCyclotomicDual 2 (res k K) ζ` holds).
5. **The §4 construction for `p = 2`** on top of 4 — using `ZDataTwo/chebotarev_frobenius_split`
   (new prime with prescribed Frobenius, split in `Λ`), `ZDataTwo/two_partition`,
   `ZDataTwo/pigeonhole_three` (the triple `i < j < N`) and
   `ZDataTwo/three_term_cancellation` (the char-`2` step of the `σ ∈ G₂` verification).  All four
   are sorry-free and axiom-clean; this assembly is the remaining work of *this* node.

### 3. Status of this file

The statement of `shafarevich_z_data_two` is unchanged and still ends in `sorry`; the three helper
theorems above it are sorry-free, as are the four modules now proved for its pieces
(`ZDataTwo/chebotarev_frobenius_split`, `ZDataTwo/two_partition`, `ZDataTwo/pigeonhole_three`,
`ZDataTwo/three_term_cancellation`).  Completion requires P2 (Tate–Poitou for `μ₂`), absent from the
workspace at present; given P1–P5 the assembly is the SW §4 argument for p = 2.
-/

/-! ## SESSION 5: what is now proved, and the exact residual obligation

**New (this session), all sorry-free and axiom-clean (`propext, Classical.choice, Quot.sound`).**

* `kills_decomp_of_smul` — conjugation invariance: for `z` additive on `G_K`, translating a place
  by `τ ∈ G_K` does not change the vanishing of `z` on its local group (`D_{τ•Q} = τ D_Q τ⁻¹` plus
  `zadd_conj`).
* `exists_mem_fixingSubgroup_smul_eq_of_comap_eq` and `exists_mem_fixingSubgroup_smul_eq_iff_comap_eq`
  — **transitivity of the `G_K`-action on the places of `Ω` over a prime of `K`**: two places of `Ω`
  over the same prime of `K` are `G_K`-conjugate, and conversely.  (Infinite-level transitivity of
  the Galois action, `Submission.NeukirchUchida.exists_smul_eq_of_comap_eq'`, at the base field
  `↥K`, transported to `K.fixingSubgroup` through `IntermediateField.fixingSubgroupEquiv`.)
* `comap_ne_of_not_exists_smul` — the bridge between the target's conjunct (6)(b) and
  Schmidt–Wingberg's `z_{σP} = 0` (`σ ≠ 1`): for a `G_k`-conjugate `Q = σ • B` of `B`, the
  hypothesis `¬ ∃ τ ∈ G_K, τ • B = Q` is *equivalent* to `B` and `Q` lying over different primes of
  `K`.  So conjunct (6)(b) is a condition on the primes of `K` over the prime of `k`, and by
  `kills_decomp_of_comap_eq` it has to be checked at one place of `Ω` per prime of `K`, exactly as
  in the paper.
* `shafarevich_z_data_two_of_unramified` — **the node in the unramified case**: if `y` is
  unramified at every finite place outside `cs(S)` then `z := y` (extended by `0` off `G_K`) works
  and (6) is vacuous.  This is the `p = 2` instance of the (already proved, all `p`) workspace lemma
  `Work.SSGRoute.z_data_general_of_unramified`, re-proved here in the target's `IsCocycleOn` form.
* `shafarevich_z_data_two_of_isolated` — **the node in the isolated case**: if at every good place
  `B` at which `y` is ramified, `y` kills the local group of every `k`-conjugate of `B` that is not
  a `G_K`-conjugate, then `z := y` witnesses the whole `z`-data.
* `exists_zmultiples_of_vanishes_inertia_of_isSplitIn` — **the cyclicity clause of Schmidt–Wingberg's
  (b) from unramifiedness, for an arbitrary coefficient module**: an additive, locally constant `z`
  on `G_K` that vanishes on the inertia of a place `B` split in `K` has an image on
  `decomp k B ⊓ G_K` contained in the `zmultiples` of one value `z g`.  The proof assembles
  `Work.SSGRoute.decomp_mod_inertia_cyclic_over_K` (delegated and proved this session, module
  `Submission.Work.SSGRoute.decomp_mod_inertia_cyclic_over_K`) with the fact that `z` vanishes on
  the subgroup generated by the local-constancy subgroup `U ⊓ G_K` and the inertia of `B` (both
  inside `G_K` because `B` splits in `K`).  `decomp_mod_inertia_cyclic_over_K` is the over-`K`
  form of the workspace's `decomp_mod_inertia_cyclic`: the decomposition group over `K`, modulo an
  open subgroup containing its inertia, is generated by one Frobenius element.
* `eq_zero_on_decomp_of_frobenius_eq_zero` — **Frobenius detection**: under the same hypotheses,
  `z` vanishes on the whole local group `decomp k B ⊓ G_K` as soon as it vanishes at the single
  Frobenius element `g`.  This is the exact form in which the verification of (6)(b) at the
  conjugates of a constructed prime is consumed (there `z` is unramified at the conjugate by
  condition (1) of the paper and the Hilbert-symbol chain gives `z (Frob) = 0`).
* `isSplitIn_of_le_of_fixingSubgroup_le`, `inf_fixingSubgroup_eq_of_isSplitIn` — splitting is
  monotone in the extension (`Λ ⊇ K`), and at a place split in `Λ ⊇ K` the local group over `K` is
  the full decomposition group.
* `z_eq_of_mul_inv_mem` — an additive cochain on `G_K` which vanishes on a subgroup `U` is constant
  on the cosets of `U` (`zσ = zσ'` if `σσ'⁻¹ ∈ U`): this is the step which turns local constancy
  into "`z` is pulled back from a finite quotient `Gal(M/K)`" and makes the *Frobenius value*
  `z (Frob_P)` well defined.
* `z_zpow_mem_zmultiples` — `z (g ^ m) ∈ AddSubgroup.zmultiples (z g)` (`X_zpow`), the input of the
  cyclicity clause in the language of the conclusion.
* `comap_eq_of_isConjPlace`, `isConjPlace_iff_comap_eq_of_isFinPlace` — the identification of
  `SSGRoute.IsConjPlace` with "lies over the same prime of `k`" (the construction of the converse
  direction from the infinite-level transitivity of the Galois action at the base field `k`), so
  that the paper's language ("the primes of `K` over a prime of `k`") can be used throughout the
  assembly.  (`isConjPlace_refl/symm/trans` were already in the workspace.)

**The residual obligation, exactly.**  What is left of the node is the *ramified* case: from an
arbitrary `y` (ramified at some good place in an un-isolated way) produce a class `z` that

  (i) agrees with `y` on `decomp k B ⊓ G_K` at the places of `cs(S)`;
  (ii) kills the involutions;
  (iii) is unramified at every place outside `cs(S)` that is not split in `Λ`;
  (iv) has *isolated* ramification at the good places: at a good place `B` where `z` is ramified,
       `z` vanishes on `decomp k Q ⊓ G_K` for every `k`-conjugate `Q` of `B` over a different prime
       of `K`.

This is Schmidt–Wingberg's §4 construction for `p = 2` (the three-term sum `z = zᵢ + z_j + z_N`,
the partition `G(K|k) ∖ {1} = G₁ ⊔ G₂ ⊔ G₃` of `ZDataTwo/two_partition`, the shoe-box principle
`ZDataTwo/pigeonhole_three` and the char-`2` cancellation `ZDataTwo/three_term_cancellation` are
already banked; the new-prime step is `ZDataTwo/chebotarev_frobenius_split`).  In the language of
the project it is *verbatim* the `p = 2`, `dim_{𝔽₂} E ≤ 1` instance of the single open obligation
`Work.SSGRoute.z_data_general_of_ramified`
(`Submission/Work/SSGRoute/ZConstruction/ZDataGeneral.lean`): that theorem is stated for a general
coefficient module `E` and a general prime `p`, so a proof of it finishes this node immediately
(via `smul_eq_self_of_finrank_le_one_two` to convert additivity into the `IsCocycleOn` form).

**Where the arithmetic bottleneck is (surveyed this session, for the lead).**

* The realisation step of §4 (`∃ z` unramified outside `cs(S) ⊆ T` realising prescribed local data
  at `T`) is the degree-`1` **Tate–Poitou exactness for `μ₂`**; in the workspace it is isolated as
  `Work.SSGRoute.PT.pt_selmer_relaxed` (one `sorry`), whose own `X = W^⊥` content is *equivalent* to
  `Work.SSGRoute.PT.pt_selmer_counting_identity` (whose file records that its only missing
  ingredient is again the same exactness — the chain is circular, so the counting identity is not a
  cheaper gate).  Both consume the canonical local Tate pairing
  `Work.SSGRoute.PTembedding.localTatePairing_canonical` (node E7/G1, one `sorry`) — the cup
  product with the local invariant, i.e. local class field theory — and its reciprocity clause.
  The `p = 2`, `M = T = ZMod 2` specialisations of these are
  `Work.SSGRoute.ZDataTwo.mu2_localTateSystem_with_archimedean` (one `sorry`) and the
  `canonical_localPairing_with_reciprocity` (`Work.SSGRoute`, one `sorry`).
* **Session note.**  With the two lemmas above, the *local* half of the §4 assembly that is
  independent of the arithmetic is complete in the general-`A` form: the cyclicity clause at the
  places at which `z` is unramified, and the detection of the vanishing on a local group by one
  Frobenius value.  What is *not* available is the same statement at a place where `z` *is*
  ramified (the paper's "cyclic" local class at a new prime) — that is part of the §4 construction.
* The local *Tate duality* itself (`local_tate_duality_finite`, `local_tate_duality_mup`,
  `local_tate_duality_mup_base`, `local_tate_duality_mup_dim`, `archPair_nondegenerate`) and the
  counting step (`Work.SSGRoute.PT.wbot_le_of_natCard`) are **proved**; the missing piece is the
  *identification of the pairing with the canonical construction* (needed for reciprocity).
* Consequence for this node: no cheaper route is apparent.  `grunwald_surjective_two` gives
  prescribed local data with **no control of the ramification elsewhere** — and "unramified at `P`"
  is a strictly weaker local condition than "locally trivial at `P`", so Grünwald cannot express
  Schmidt–Wingberg's condition (1).  The minimal arithmetic input this node needs is the exactness
  statement above; everything else in the §4 argument is banked or bankable.
* **Reading of §4 confirmed against the paper's own text** (the PS extract `sw.txt` of
  arXiv:math/9809211): the paper's `S` is *not* fixed — each `z_i` lives in `H¹(k_{S_i}|K, ν_p)`
  with `S_i = cs(Λ|k) ∪ T_i` and `T_i = T ∪ {P_1 ∩ k, …, P_i ∩ k}` growing (`T_n ⊆ S`), i.e. the
  new primes are *outside* `T_n(K)` and each `z_i` is ramified at exactly one of them.  Hence the
  constructed `z = zᵢ + z_j + z_N` *is* ramified (at `P_i, P_j, P_N`), the trigger of conjunct (6)
  is not vacuous, and the verification of (6)(b) is the Hilbert-symbol chain of the paper.  The
  realisation step is the exactness of the upper line of the Tate–Poitou diagram (used twice), i.e.
  the same input as above.
* **Caveat on the rendering of "cyclic".**  The paper defines a local class `x ∈ H¹(k_p, A)` to be
  *cyclic* if it is **split by a cyclic extension** of `k_p` (there is a cyclic `K_p/k_p` with `x` in
  the kernel of the restriction), and notes that unramified classes are cyclic.  The conclusion of
  this node (and of `z_data_general`) renders the cyclicity half of (b) instead as *"the image of
  `z` on `decomp k B ⊓ G_K` is contained in the `zmultiples` of one value"* — i.e. the image is a
  cyclic subgroup of `E`.  For a one-dimensional `E` (this node) the two are both automatic, so the
  choice is harmless here; for a general coefficient module the two readings are *not* a priori
  equivalent (the image of the local cochain is cyclic without `z` necessarily being split by a
  cyclic local extension), and the general node `Work.SSGRoute.z_data_general` uses the image
  version.  Whoever formalises §4 for general `A` should decide which of the two is meant, and
  prove the image version (which is what the workspace's statements ask for):
  `Work.SSGRoute.decomp_mod_inertia_cyclic_over_K` (delegated this session) is the local structure
  input for it in the *unramified* case.
-/


/-- **The action of `G_K` on a one-dimensional `𝔽₂`-module is trivial.**

`E` is a finite `𝔽₂`-vector space of dimension `≤ 1`, hence `E = 0` or `E ≅ 𝔽₂`, and
`GL_{𝔽₂}(E) = 1`.  The proof avoids the general linear algebra interface: pick `e ≠ 0`; the
`𝔽₂`-span of `e` is everything (`zmultiples_eq_top_of_finrank_le_one`), so `g • e = m • e`, and
`m ≠ 0` because `g` is bijective; in `𝔽₂` the only non-zero scalar is `1`. -/
theorem smul_eq_self_of_finrank_le_one_two (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (h1 : Module.finrank (ZMod 2) E ≤ 1) :
    ∀ g : K ≃ₐ[k] K, ∀ e : E, g • e = e := by
  intro g e
  by_cases he : e = 0
  · rw [he, smul_zero]
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (zmultiples_eq_top_of_finrank_le_one (p := 2) h1 he (g • e))
  rw [← Int.cast_smul_eq_zsmul (R := ZMod 2) m e] at hm
  have hne : ((m : ZMod 2)) ≠ 0 := by
    intro h0
    have h2 : g • e = 0 := by rw [← hm, h0, zero_smul]
    have : e = 0 := by
      have := congrArg (fun x => g⁻¹ • x) h2
      simpa using this
    exact he this
  have h01 : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by
    intro y
    fin_cases y
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hone : ((m : ZMod 2)) = 1 := by
    rcases h01 ((m : ZMod 2)) with h | h
    · exact absurd h hne
    · exact h
  rw [← hm, hone, one_smul]

/-- **The canonical candidate `z := y` (extended by `0` off `G_K`) satisfies conjuncts (1)–(5).**

The only input beyond the hypotheses is the triviality of the action of `G_K` on `E`
(`smul_eq_self_of_finrank_le_one_two`), which turns the crossed-homomorphism condition into
additivity. -/
theorem z_data_two_agreement_conjuncts (p : ℕ) [Fact p.Prime] (hp2 : p = 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (h1 : Module.finrank (ZMod p) E ≤ 1)
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
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  -- transport the coefficient module across `p = 2`
  subst hp2
  let z : (Ω ≃ₐ[k] Ω) → E := fun σ => if σ ∈ K.fixingSubgroup then y σ else 0
  have htriv : ∀ g : K ≃ₐ[k] K, ∀ e : E, g • e = e :=
    smul_eq_self_of_finrank_le_one_two k Ω K E h1
  have hzy : ∀ σ, σ ∈ K.fixingSubgroup → z σ = y σ := by
    intro σ hσ
    show (if σ ∈ K.fixingSubgroup then y σ else 0) = y σ
    rw [if_pos hσ]
  have hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h := by
    intro g hg h hh
    rw [hzy (g * h) (K.fixingSubgroup.mul_mem hg hh), hzy g hg, hzy h hh, hy g hg h hh]
  have hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z := by
    obtain ⟨U, hUopen, hUc⟩ := hyc
    refine ⟨U, hUopen, ?_⟩
    intro g hg u hu huH
    rw [hzy (g * u) (K.fixingSubgroup.mul_mem hg huH), hzy g hg]
    exact hUc g hg u hu huH
  refine ⟨z, ?_, hzloc, ?_, ?_, ?_⟩
  · intro g hg h hh
    rw [hzadd g hg h hh, htriv (SSGRoute.res k K g) (z h)]
  · intro B hB hconj σ hσ _
    exact hzy σ hσ
  · intro c hc hc2
    rw [hzy c hc]
    exact hyinf c hc hc2
  · intro B hB hconj hnsplit σ hσ hI
    rw [hzy σ hσ]
    exact hyS B hB hconj hnsplit σ hσ hI

/-- **The "cyclicity" half of Schmidt–Wingberg's (b) is automatic for a one-dimensional
coefficient module.**  Every additive subgroup of `E` (an `𝔽₂`-space of dimension `≤ 1`, hence
`0` or `𝔽₂`) is cyclic, so whenever `D_B ⊓ G_K` carries a non-zero value of `z` the image of `z`
there is contained in the `zmultiples` of that value. -/
theorem z_data_two_cyclic_conjunct (p : ℕ) [Fact p.Prime] (hp2 : p = 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    (h1 : Module.finrank (ZMod p) E ≤ 1)
    (B : ValuationSubring Ω) (z : (Ω ≃ₐ[k] Ω) → E)
    (htrig : ∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) :
    ∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        z δ ∈ AddSubgroup.zmultiples (z g) := by
  subst hp2
  obtain ⟨σ, hσI, hσK, hσne⟩ := htrig
  refine ⟨σ, Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩, fun δ _ => ?_⟩
  exact zmultiples_eq_top_of_finrank_le_one (p := 2) h1 hσne (z δ)

/-! ## SESSION 5: conjugation invariance, the reduction to one place per prime of `K`, and the
two cases in which the node is now proved

The node `Work.SSGRoute.shafarevich_z_data_two` is the `p = 2`, one-dimensional case of
`Work.SSGRoute.z_data_general` (`Submission/Work/SSGRoute/ZConstruction/ZDataGeneral.lean`), in the
form in which `Work.SSGRoute.shafarevich_z_construction_of_zData`
(`ZConstruction/ZDataBridge.lean`, sorry-free) consumes it.  The new material below

* proves the **conjugation invariance** of "`z` vanishes on the local group of a place"
  (`kills_decomp_of_smul`) and the consequent **reduction of conjunct (6)(b) to one place per prime
  of `K` over a prime of `k`** (`kills_decomp_of_comap_eq`, via transitivity of the Galois action on
  the places over a prime of `K`): Schmidt--Wingberg's condition `z_{σP} = 0` is stated for the
  *primes* `σP` of `K`, while the target quantifies over the *places* `Q` of `Ω`; this is the bridge;
* proves the node in the two cases in which no arithmetic is needed:
  * `shafarevich_z_data_two_of_unramified` --- `y` itself is already unramified outside `cs(S)`
    (the case isolated as `z_data_general_of_unramified`, already proved for all `p` in the
    workspace); then `z := y` (extended by `0` off `G_K`) works and condition (b) is vacuous;
  * `shafarevich_z_data_two_of_isolated` --- `y` is already ramified *only* in the isolated way
    required by (b): at every good place `B` at which `y` is ramified, `y` kills the local group of
    every `k`-conjugate of `B` that is not a `G_K`-conjugate.  Then again `z := y` works.

The residual obligation of the node is therefore exactly the **ramified case**: starting from an
arbitrary `y` (ramified at some good place in the non-isolated way), produce a class `z` agreeing
with `y` on `cs(S)`, unramified at the non-split places, killing the involutions, and with isolated
ramification at the good places.  This is Schmidt--Wingberg's §4 construction (`p = 2`), i.e. the
`p = 2`, `dim ≤ 1` instance of `Work.SSGRoute.z_data_general_of_ramified`; its arithmetic input is
the degree-`1` Tate--Poitou exactness for `μ₂` with restricted ramification (the "realisation"
half of `Work.SSGRoute.PT.pt_selmer_relaxed`). -/

/-! ## SESSION 14: the dependency chain re-verified against the current workspace

A fresh audit of the whole `SSGRoute` tree (the `PT/`, `ZSplit/`, `ZDataMup/` and `PTembedding/`
lanes) confirms that the node's residual obligation is exactly the `p = 2` realisation, and pins
down its two irreducible inputs.  The findings, so that they are not rediscovered:

* **Everything formal is on disk and clean.**  The reduction node ⟸ `kummerCore`
  (`shafarevich_z_data_two_of_kummerCore`), the Kummer bridge (`KummerCocharBase` + the
  `ZDataTwo/*` dictionary lemmas), the reduction of the level-`K` realisation to the two named
  inputs (`ZSplit/RealisationCounting.lean`,
  `levelK_counting_identity_of_finrank_le`, clean: `[propext, Classical.choice, Quot.sound]`),
  the finiteness of the level-`K` class space (`finite_kPrimalClasses`), and the p.18 `Psi`-leg
  (`levelK_psi_orthogonality_no_fin`).  Measured with `#print axioms`: clean.

* **The `p = 2` level-`K` chain cannot be instantiated as it stands.**  `ZSplit.HasLevelKReciprocity`
  and `ZDataMup.IsProductFormula` sum only over *finite* places, and the sibling
  `ZDataMup.localTateSystem_productFormula` carries `hp : p != 2`.  Both reviewers of
  `ZDataTwo/localTateSystem_productFormula_two` (this session) independently confirmed the reason,
  with the counterexample `k = K = Q`, `T' = {place over 2}`, `a = b = chi_{-1}`: for `p = 2` the
  archimedean term `(a,b)_inf` is a genuine summand, so the finite-place-only sum is `-(a,b)_inf`.
  The correct `p = 2` shape is `PT.pt_selmer_relaxed`'s: the pairing is indexed by the decomposition
  groups **and** the involution subgroups `Subgroup.zpowers c`, and the reciprocity sums over a
  finite set `S'` of finite places *together with* a set `C'` of involution representatives.  The
  archimedean half of the pairing is `Work.SSGRoute.archPair` with the proved non-degeneracy
  `Work.SSGRoute.archPair_nondegenerate`; the finite half is the Hilbert symbol
  (`NK.NUV2.LC.hilbertSymbol` + `Work.HilbertSymbolGeneral`), whose reciprocity --- *with* the
  archimedean place --- is `Work.HilbertSymbolGeneral.hilbertReciprocityTwo` (clean).

* **Both remaining inputs are the workspace's frontier, not this node's private gap.**
  (i) the `p = 2` local Tate system with the archimedean reciprocity (the `mu_2` instance of
  `Work.SSGRoute.canonical_localPairing_with_reciprocity`, nodes `E7`+`G1`); (ii) the Selmer counting
  identity `PT.pt_selmer_counting_identity` (`|V|*|W| = |P|`, Milne ADT I.4.10 / NSW 8.6.8), i.e.
  the middle exactness of the Poitou--Tate sequence for `mu_2` --- the workspace's own audits name it
  *the* deepest open node.  The p.18 realisation `PT.pt_selmer_relaxed` (clean text, `sorryAx`-
  tainted) is proved from (i)+(ii)+the proved counting step `PT.wbot_le_of_natCard`.
  Earlier sessions' verdict, re-confirmed here: the node is not defective, it is parked on
  those two inputs, and every attempt to delegate them came back refused.

* **What is genuinely left to *this* node, on top of those inputs**, is Schmidt--Wingberg's section
  four `p = 2` assembly --- the sequence `z_1, z_2, ...` with conditions (1)--(4), the Claim, the
  pigeonhole triple `i < j < N` and the three-term verification `z = z_i + z_j + z_N` --- whose
  combinatorial ingredients are already banked and proved here (`ZDataTwo/two_partition`,
  `ZDataTwo/pigeonhole_three`, `ZDataTwo/three_term_cancellation`,
  `ZDataTwo/chebotarev_frobenius_split`, `ZDataTwo/map_decomp_res_eq_zpowers_of_isFrobAtPrime`,
  `ZDataTwo/kummerCochar_eq_zero_of_isFrobAtPrime_eq_zero`,
  `ZDataTwo/localPowClass_three_term_agree`).  It consumes the realisation at the enlarged place
  set `S` together with the involutions `C`, and produces the node's sharpened clause (6).

### SESSION 14 (cont.): the section-four `p = 2` assembly started, and the two inputs re-dispatched

* **The two frontier inputs are re-dispatched to fresh teams with the corrected shape.**
  (i) With the help of two reviewers, the `p = 2` local Tate system with the archimedean terms is now
  stated correctly: `Work.SSGRoute.ZDataTwo.IsMu2LocalTateSystemWithArch` (module
  `ZDataTwo/Mu2ArchDefs.lean`, proved, sorry-free) records the shape — local axioms at the
  decomposition groups `decomp k A` *and* the involution subgroups `Subgroup.zpowers c`, and
  archimedean-corrected reciprocity for **global** cochains (`⊤`, not merely on `G_K`, which is what
  the earlier version got wrong: the indicator of an involution outside `G_K` refutes it) over
  `S' ∪ C'` with the excluded places satisfying `B ∤ 2`, `B` unramified in `K`.  The target
  `Work.SSGRoute.ZDataTwo.mu2LocalTateSystemWithArch` (path
  `SSGRoute/ZDataTwo/mu2LocalTateSystemWithArch`) is the `∃ pair` statement of that predicate.
  (ii) `Work.SSGRoute.ZSplit.levelKCountingIdentityTwo` (path
  `SSGRoute/ZSplit/levelKCountingIdentityTwo`) is the level-`K` Selmer counting identity at `p = 2`
  — the odd-`p` sibling `ZSplit.levelK_counting_identity` minus its `hp : p ≠ 2` (the dropped
  `ζ, htriv, hζ, hζK` are automatic at `2`), which the reviewers confirmed is *not* a
  specialisation of the odd lane (at `2` the `C`-coordinates stop being subsingletons: those *are*
  the archimedean terms).  Both requests are queued (the fleet was saturated when filed).

* **The section-four `p = 2` assembly is started**, in the new module
  `Submission/Work/SSGRoute/ZDataTwo/SWFourTwo.lean` (proved, sorry-free):
  * `Work.SSGRoute.ZDataTwo.threeTerm_kills_localGroup` — **the verification step of the paper's
    section four**: for `b₁ b₂ b₃ ∈ Kˣ` and a place `B ∤ 2` unramified in the auxiliary level `L` at
    which the product is unramified, if the Kummer cochain of `b₁b₂b₃` vanishes at a Frobenius
    element of the local group and factors through `res k L`, then the three-term sum
    `z_{b₁} + z_{b₂} + z_{b₃}` vanishes on the whole local group.  This is `z_{b₁b₂b₃} = z_{b₁} +
    z_{b₂} + z_{b₃}` (`kummerCochar_mul`) plus the banked
    `kummerCochar_eq_zero_of_isFrobAtPrime_eq_zero`, i.e. the point at which the paper's
    `z_{σP_i} = 0` becomes vanishing on `D_{σP_i} ⊓ G_K`.
  * `Work.SSGRoute.ZDataTwo.threeTerm_localPowClass_one` — **the arithmetic consequence**: under the
    same hypotheses, `b₁ b₂ b₃` is a local `2`-power at the prime of `K` below `B`, i.e. clause (D)
    of `ArithCore` (the sharpened one-sidedness) in the arithmetic vocabulary of the core, via the
    banked local Kummer dictionary `kummerCochar_eq_zero_iff_localPowClass`.

  What remains of section four is, on top of these and the banked combinatorial lemmas: the
  *construction* of the sequence `z₁, z₂, …` with properties (1)--(4) and its Claim (which consumes
  the `p = 2` realisation (i)+(ii) plus Chebotarev), and the derivation of the Frobenius-value
  relations from the Hilbert-symbol product formula (the paper's `(2b, z̃)` chain).

### SESSION 14 (cont.): outcome of the two dispatches

* **(i) `mu2LocalTateSystemWithArch`** — dispatched; the team built a whole architecture
  (`ZDataTwo/Mu2ArchDefs`, `Mu2ArchReduction`, `Mu2ArchForm`, `Mu2FiniteForm`,
  `Mu2FiniteFormNondeg`, `Mu2InvolutionForm`, `Mu2LocalNormXor`, `Mu2PairForm`, `Mu2Reciprocity`,
  `Mu2Assembly`, and the target file itself).  The target's proof is in place and reduces to two
  concrete arithmetic inputs:
  * `Work.SSGRoute.ZDataTwo.finPairEqZeroOfKillsInertia` at a prime `∤ 2` where both Kummer
    characters kill the inertia (the even-valuation/norm argument) — **proved in this session**
    (module `Submission.Work.SSGRoute.ZDataTwo.finPairEqZeroOfKillsInertia`, and reviewed as "looks
    correct" by two reviewers);
  * `Work.SSGRoute.ZDataTwo.arch_sum_eq_badRealSum` (the archimedean count: the sum of the
    archimedean invariants over a transversal of the involution classes is the number of real places
    at which `β` fails to be a local norm) — its own module is in place and the lane is filling it.
  **Both gaps were closed by the team: the target is now PROVED and axiom-clean**
  (`#print axioms Work.SSGRoute.ZDataTwo.mu2LocalTateSystemWithArch` = `[propext,
  Classical.choice, Quot.sound]`; the whole `Mu2*` cluster is `sorry`-free).  So the `p = 2` local
  Tate system with the archimedean terms -- the `M = T = ZMod 2` instance of the `E7`+`G1` node
  `Work.SSGRoute.canonical_localPairing_with_reciprocity` -- **no longer blocks the node**: it is a
  proved theorem of the workspace, importable as
  `Submission.Work.SSGRoute.ZDataTwo.mu2LocalTateSystemWithArch`.

* **(ii) `levelKCountingIdentityTwo`** — dispatched twice; the second prover **declared it
  FALSE-as-stated** (their judgment: it is the level-`K` relaxed Selmer counting identity, i.e. the
  `p = 2` instance of the deepest open rung — Milne I.4.10(b)/NSW 8.6.8 — and no axiom-clean route
  to it exists in this workspace).  This matches the audits: the counting identity is *equivalent*
  to the middle exactness of the Poitou--Tate sequence, which is what the `PT/`, `ZSplit/` and
  `E7`--`E9` lanes are building towards.  It stays the node's irreducible arithmetic input.

  **A gap in the level-`K`/level-`top` counting-identity *statement* (found by the reviewers while
  re-dispatching it).**  Both reviewers of the restated `p = 2` form
  (`SSGRoute/ZSplit/levelKCountingInequalityTwo`, the dimension inequality
  `finrank (kPrimalClasses) <= 2 * finrank (kDualSelmerSubmodule)`) returned *probably wrong as
  stated*, one of them with a concrete configuration: `k = K = Lambda = Q`, `p = 2`, `S` a place
  over `2`, `C` the class of complex conjugation.  Then `Lambda = k` makes `IsSplitIn k Lambda B`
  true at *every* place, so the mirror conjunct of `kDualSelmer` forces `b` to be locally trivial at
  every place outside `S`; the decomposition groups generate `G_k` (Chebotarev/Bauer), so the only
  admissible class is `b = 0`: `kDualSelmerSubmodule = bottom` while the dyadic coordinate of
  `kPrimalClasses` is the two-dimensional `Q_2^x / (Q_2^x)^2`, so the inequality fails.  The same
  argument applies to `Work.SSGRoute.PT.IsDualSelmerClass` when `N = k`.  Hence the
  counting-identity statements of the `ZSplit` and `PT` lanes need an extra hypothesis excluding the
  trivial auxiliary field (`K < Lambda`, i.e. a non-vacuous relaxation); with it the truth is again
  the open Euler-characteristic gate.  The node itself is *not* affected: its clause (6) is stated
  for every place split in `Lambda`, so at `Lambda = k` it simply demands that the ramification
  outside `cs(S)` be one-sided, which is what section four produces (`IsSplitIn` making clause (5)
  vacuous is harmless, because the realisation used by section four takes its new primes *outside*
  `cs(S)`).

* **Section four (`SWFourTwo.lean`)** now contains the verification half in full: the detection step
  `threeTerm_kills_localGroup`, its arithmetic consequence `threeTerm_localPowClass_one` (clause (D)
  of `ArithCore`), the combinatorial `G₁`-case `sw_frob_vanishing_G1`, and the rewrite
  `threeTerm_eq_of_mul`.  What is left of section four is the *construction* of the sequence
  `z₁, z₂, …` with properties (1)--(4) and its Claim, which consumes the `p = 2` realisation (i)+(ii)
  together with Chebotarev (`ZDataTwo.chebotarev_frobenius_split`), and the Frobenius-value relations
  from the Hilbert-symbol product formula.

### SESSION 15: the `p = 2` clause bookkeeping is DONE; the shape of the remaining recursion

* **New proved module `Submission/Work/SSGRoute/ZDataTwo/ThreeHalves.lean`** (sorry-free,
  axiom-clean `[propext, Classical.choice, Quot.sound]`), containing the whole *place bookkeeping*
  of section four at `p = 2`:
  * `Work.SSGRoute.ZDataTwo.unramified_outside_of_confinement` — clause (3) of the core from the
    confinement of the ramification: if `z` is unramified outside `cs(S)` and the `G_K`-conjugates
    of a set `Pset` of places all split in `Λ`, then `z` is unramified at every place outside `cs(S)`
    that is not split in `Λ` (complete splitting in a normal extension being `G_k`-invariant);
  * `Work.SSGRoute.ZDataTwo.companion_vanishing_of_confinement` — clause (4) of the core: a place
    `B ∉ cs(S)` split in `Λ` at which `z` is ramified must be a `G_K`-conjugate of an escape prime
    (`Pset`), and then the one-sided vanishing at that escape prime transports to the companions of
    `B`;
  * `Work.SSGRoute.ZDataTwo.kummerCore_of_three_halves` — **the assembly**: from three halves
    `b : Fin 3 → (↥K)ˣ` which each agree with `y` at `cs(S)`, each vanish on the involutions, and
    whose *sum* `z = z_{b 0} + z_{b 1} + z_{b 2}` is confined to `cs(S) ∪ Pset` and satisfies the
    one-sided vanishing at the places of `Pset`, the core follows with `b = b 0 * b 1 * b 2`
    (clause (1): `3 · y = y` in `𝔽₂`; clause (2): sum of zeros; clauses (3),(4): the two lemmas
    above).

  So the *entire* place bookkeeping of the exceptional case is out of the way, and what remains of
  the core is exactly the existence of the three halves with those four properties.

* **Clause (4) is not automatic for the Kummer class of `y` itself** (so section four is genuinely
  needed, and the core is an existence statement, not a restatement of Kummer theory).  Witness:
  `k = ℚ`, `K = Λ = ℚ(i)` (so `G_K` has *no* involutions and, with `S` = one place over `2`,
  `cs(S)` = the places over `2`), and `y = z_{17}`, the Kummer cochain of `17 ∈ ℚˣ`.  Then:
  * `hyS` holds: at `B ∤ 2` over `ℓ ≡ 3 mod 4` (the places not split in `Λ`) the class `17` has
    valuation `0` at `B`, so the local extension is trivial or unramified, i.e. `z_{17}` kills the
    inertia;
  * `hyT`/`hy0` hold: `17 = 1 + 16 = 1 + (1+i)^8` is a square in `ℚ₂(i)`, so `z_{17}` is trivial on
    the whole local group at the primes over `2`;
  * `hyinf` is vacuous (`ℚ(i)` has no real places, hence `G_{ℚ(i)}` has no involutions);
  * `17 = (4+i)(4-i)` splits in `ℚ(i)`, so at `B` over `(4+i)` the class `z_{17}` *is* ramified
    (odd valuation), while the companion `Q` over `(4-i)` also carries odd valuation — so `z_{17}`
    does **not** vanish on the local group of `Q` and clause (4) fails for `b = 17`.

  What saves the statement is that the core is an *existence* statement: the escaping class has to
  be a different element (`4+i` itself is a local square at `(4-i)`, since `4+i ≡ 2i = (1+i)²` there),
  and producing such an element is exactly the content of section four.

* **Why `p = 2` needs three terms** (recorded because it pins the shape of the recursion): at
  `p = 2` no half can carry `y/2` at `cs(S)`, so one takes three halves each agreeing with `y` at
  `cs(S)`, whose sum is again `y` (`x + x + x = x`), and the one-sided vanishing at the escape primes
  is obtained by *matching pairs plus a zero*: at a companion of `P_t` the three terms are prescribed
  to be `(x, 0, x)` so that they cancel.  A *single* escape step (one class, unramified outside
  `cs(S) ∪ {Q}`, killing the involutions) does not suffice: that would be the surjectivity of the
  localisation for finitely many "one-sided" conditions, i.e. exactly the Grünwald--Wang exceptional
  case at `2`.  (The workspace's `grunwald_surjective_two` — proved — is the localisation
  surjectivity for local data on decomposition groups, which is why the *first element* of the escape
  is available at `2`; the *correction* step is where the archimedean terms enter.)

* **The `p = 2` escape realisation** — the piece the recursion needs at every step — was stated and
  reviewed (verdict "looks correct as stated", with the archimedean/total-positivity conjunct flagged
  as the only genuinely new `p = 2` content).  Its statement (path `SSGRoute/ZDataTwo/mu2EscapeRealisation`)
  is `escape_realisation_core` at `p = 2` with the conjugacy conventions of the odd-`p` lane
  (`hTdisj` up to `G_K`-conjugacy, so that `T` may contain several places over one prime of `k`; the
  escape prime `Q` avoiding the whole `G_k`-classes of `T`) and with the archimedean conditions
  `hginf`/`hhinf` (the datum kills the involutions) replacing `hKimag`; the conclusion additionally
  asserts that the escaping class `z` kills the involutions.  Intended proof: the odd-`p` one
  (`grunwald_kummer_first_element`, whose proof does *not* in fact use its `hKimag`) together with
  two `p = 2` additions:
  * a *sign adjustment*: multiply the realising element by `s ∈ Kˣ` which is a local square at the
    `T`-primes and whose signs at the real places make the product totally positive;
  * a *correction* with the real places inside the ray modulus: `b := a s / γ` with `(γ) = 𝔡 𝔮`,
    `γ ≡ 1 mod 𝔪`, where `𝔪` contains the `T`-primes (to high exponent) *and* the real places, so
    that `γ` is totally positive; the orthogonality computation then has no archimedean
    contributions because the local classes of the datum at the real places are `0`.  This is the
    `p = 2` input that the odd-`p` lane gets for free from `hKimag`, and the workspace's
    `Mu2LocalTateSystemWithArch` (proved) supplies the archimedean terms of the product formula.
  The odd-`p` twin is complete modulo the single `sorry` in
  `GrunwaldEscapeCore/grunwald_escape_correction.lean` (its orthogonality), so the `p = 2` correction
  inherits that same open rung.

* **Remaining obligations of the node**, in order:
  1. `mu2EscapeRealisation` (the `p = 2` escape step) — stated, to be dispatched/proved;
  2. the section-four *recursion*: iterate the escape step over the growing data set
     `T_n = S ∪ {all places over the primes of the earlier escape primes}` (prescribing at the
     conjugates of the older escape primes the matching values that make the three-term sum cancel),
     and apply the shoe-box principle (`ZDataTwo.pigeonhole_three`, proved) to pick the triple;
  3. the *verification*: at each of the three escape primes the three-term sum vanishes on the whole
     local group, via `ZDataTwo.threeTerm_kills_localGroup` (proved) applied to the Frobenius value
     of the product `b_0 b_1 b_2`, whose vanishing is the paper's `(2b, z̃)` Hilbert-symbol chain
     (the Claim `(z_i)^{σP_i} = 0` for involutions `σ` uses Chebotarev
     `ZDataTwo.chebotarev_frobenius_split`).

### SESSION 15 (cont.): the escape realisation split into its two halves; the recursion analysed

* **Three new proved modules of this lane** (all sorry-free, axiom-clean `[propext,
  Classical.choice, Quot.sound]`):
  * `Submission/Work/SSGRoute/ZDataTwo/ThreeHalves.lean` — the place bookkeeping of §4 at `p = 2`
    (see above): `unramified_outside_of_confinement`, `companion_vanishing_of_confinement`,
    `kummerCore_of_three_halves`.  The core now reduces to the *existence of the three halves*;
  * `Submission/Work/SSGRoute/ZDataTwo/mu2KummerFirstElement.lean` —
    `GrunwaldEscapeCore.kummerFirstElement_noImag`: the Grünwald + Kummer "first element" (Grünwald
    over `K` + Kummer surjectivity) with the unused hypothesis `hKimag` of
    `grunwald_kummer_first_element` **deleted**, hence applicable at `p = 2`;
  * `Submission/Work/SSGRoute/ZDataTwo/Mu2EscapeStep.lean` — the escape realisation *assembled from
    its two halves*: the correction is isolated as the standalone `Prop`
    `Work.SSGRoute.ZDataTwo.Mu2EscapeCorrection` (the `p = 2` analogue of
    `GrunwaldEscapeCore.grunwald_escape_correction`, specialised to `L₁ = N`, `L₂ = K`, with the
    archimedean hypotheses `hginf/hhinf` and the extra conclusion "the corrected class kills the
    involutions"), and `mu2EscapeRealisation_of_correction` proves the `p = 2` escape realisation
    conditional on it (mirroring the assembly of `escape_realisation_core`).

* **Delegation state.**  `SSGRoute/ZDataTwo/mu2EscapeCorrection` was reviewed twice ("looks correct
  as stated": the only deliberate divergence from the odd-`p` template being the `IsConjPlace`
  (k-conjugacy) conventions and the `p = 2` archimedean clauses) and a child was assigned; the child
  finished **without modifying** the file, so `mu2EscapeCorrection.lean` still holds only the
  statement (`:= by sorry`) and the correction remains the one deep rung of the `p = 2` escape.
  Remaining requests hit two obstacles: (a) the lemma slots were saturated for most of the session;
  (b) the `request_review` gate currently *fails to build its `depends_on` closure* because a
  colleague's file in the cone, `Submission/Work/SSGRoute/ZConstruction/LineAndZeroWitness.lean`, is
  mid-edit and does not elaborate, so the review of a new path cannot be obtained until that file is
  repaired (this is a shared-workspace coupling, not an error of this lane).

* **Design facts established while analysing the recursion** (recorded so that the next stretch does
  not have to re-derive them):
  * *The escape class is only uncontrolled at its own prime's orbit.*  The correction produces
    `b = a s / γ` with `div(b)` supported on the `T`-primes and on the single prime `𝔮` of the
    escape place `Q`.  Hence the escaping class `z_b` **is unramified** (even valuation) at every
    *k*-conjugate `σQ` (`σ ∉ G_K`), but its *value* there — its Frobenius value — is not prescribed
    by the datum: the escape statement can prescribe the local data at every place of `T`, and `T`
    may contain all the *k*-conjugates of the previously chosen escape primes (the `hTdisj` of the
    escape statement is `G_K`-conjugacy, so several places over one prime of `k` are allowed), but
    never those of the prime chosen by the *current* step.
  * *This is the only obstruction.*  With the earlier orbits prescribed, the three-term sum
    `z_{i} + z_{j} + z_{N}` cancels at the conjugates of `P_i` and `P_j` by choosing the
    prescriptions `z_j|_{σP_i} = 0`, `z_N|_{σP_i} = z_i|_{σP_i}` and
    `z_N|_{σP_j} = z_i|_{σP_j} + z_j|_{σP_j}`; at the conjugates of the last prime `P_N` nothing can
    be prescribed, and this is exactly the point where the paper's pigeonhole
    (`Ψ_N(z_i) = Ψ_N(z_j) = Ψ_N(z_N)`) and the Hilbert-symbol computation enter.  A *single* escape
    step does not suffice — that would be the surjectivity of the localisation over the finitely many
    "one-sided" conditions, i.e. the Grünwald--Wang exceptional case at `2`.  (Note also that the
    localisation surjectivity itself — `UchidaKummer.isKummerSurjective_of_weakApproximation`, proved
    — is available for any finite set of *finite* primes at `p = 2`, since weak approximation plus
    openness of the `2`-power subgroups gives it; the difficulty is the *lack of control of the
    divisor*, not the local conditions.)
  * *The matching prescriptions are available from the escape statement* because each orbit
    (all places over one prime of `k`) can be put into `T` once its prime is known, and the local data
    of a class is an `𝔽₂`-valued homomorphism on each local group, so prescribing
    `z_{n+1}|_{orbit(P_t)} := 0` or `:= z_t|_{orbit(P_t)}` is legitimate.
  * *The archimedean side is a sign adjustment.*  For the corrected class to kill the involutions of
    `G_K` (i.e. to be totally positive) one multiplies the first element by `s ∈ Kˣ` which is a local
    square at the `T`-primes and has the signs at the real places making `a s` totally positive —
    `UchidaKummer.isWeakApproximation` (finite places) and
    `NumberField.InfinitePlace.denseRange_algebraMap_pi` (Mathlib; infinite places) supply the two
    approximation statements, and the dictionary `z_b(c) = 0 ↔ b` a square in the fixed field of `c`
    is banked (`ZDataTwo.ArchKummer.nodeKummerCochar_eq_zero_on_involutions_iff`, and
    `HRec.kummerChar_eq_zero_iff_not_isNegAt` in the sign form), as is the correspondence between
    involutions of `G_K` and real places
    (`ZDataTwo.orderEmbedding_fixSub_fieldRange`, `ZDataTwo.exists_orderEmbedding_fixSub`).

* **Available tools for the correction / sign adjustment** (identified while working on the two
  pieces, all *proved*, sorry-free):
  * `GrunwaldEscapeCore.exists_prime_mem_rayClass` — every ray class modulo `𝔪` contains a prime
    ideal coprime to `𝔪`, i.e. the Čebotarev input of the correction's steps 1–4;
  * `GrunwaldEscapeCore.grunwald_escape_correction` carries the *single* `sorry` (line 220) of the
    odd-`p` lane — the orthogonality / product-formula computation, which at `p = 2` must be redone
    with the archimedean terms (the workspace's proved `Mu2LocalTateSystemWithArch` and
    `Work.HilbertSymbolGeneral.hilbertReciprocityTwo` are the archimedean inputs available for it);
  * `NK.CFTLib.Arl.exists_integral_sign_adjust` — for `m > 0` and a sign function `r` on the real
    places, an algebraic integer `u` with `1 + m·u` having the sign of `r` at every real place;
    its consumer in the same directory combines it with the Chinese remainder theorem for fractional
    ideals to give an element of a fractional ideal congruent to `1` modulo a modulus and positive at
    the designated real places.  These are exactly the tools for the *sign adjustment* (β) — the
    `p = 2` addition to the escape construction: take `s := 1 + m·u` with `m` divisible by all the
    `T`-primes (to an exponent large enough that `1 + 𝔭^N ⊆ (K_𝔭ˣ)²`, the banked
    `GrunwaldEscapeCore.exists_pow_eq_of_isCongAt`) and `m ≡ 0` at each `T`-prime, so that `s` is a
    local square at the `T`-primes while `a·s` has the prescribed (positive) signs;
  * `ZDataTwo.exists_conjInv_kummerChar_eq_zero_iff` and `HRec.exists_involution_conj_comp` give the
    *real place ⟹ involution* direction of the archimedean dictionary (for the base field, with the
    conjugation embedding spelled out); `HRec.kummerChar_eq_zero_iff_not_isNegAt` is the dictionary
    `z_b(c) = 0 ↔ b` is not negative at the real place `w`.  For (β) the missing bridge is the
    converse statement (every involution of `G_K` is `G_K`-conjugate to the involution of some real
    place of `K`), which together with `z_b(σ c σ⁻¹) = z_{σ⁻¹•b}(c) = z_b(c)` (for `σ ∈ G_K`, since
    `K` is `G_K`-fixed) reduces the second clause of (β) to `¬IsNegAt w (a s)` for every real `w`.

### SESSION 15 (cont.): the Archimedes bridge and the archimedean half of (β) are PROVED

* **`Submission/Work/SSGRoute/ZDataTwo/RealPlaceInvolution.lean`** (sorry-free, axiom-clean):
  * `Work.SSGRoute.ZDataTwo.kummerCharZMod_two_eq_kummerChar` — at `p = 2` the two `ZMod 2`-valued
    encodings of "`σ √b / √b`" agree (`kummerIdx_congr` with the two square roots of `b`);
  * `Work.SSGRoute.ZDataTwo.realPlace_involution_kummerChar_iff` — **the bridge that was missing
    from Mathlib**: for every involutive `c ∈ K.fixingSubgroup` with `c ≠ 1` there is a *real*
    infinite place `w` of `↥K` with
    `kummerCharZMod b c = 0 ↔ ¬IsNegAt w b` for all `b`.  Proof (plumbing): transport `c` along the
    monoid isomorphism `IntermediateField.fixingSubgroupEquiv K : K.fixingSubgroup ≃* (Ω ≃ₐ[↥K] Ω)`
    (preserving `·^2 = 1` and `≠ 1`), apply `HRec.realPlaceOfInvolution_isReal` with the base field
    `↥K` (the instance `IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩`, as
    elsewhere in the workspace), and identify the characters.  So the "converse direction" flagged
    above is no longer an input: **everything the archimedean side needs is on disk**.

* **`Submission/Work/SSGRoute/ZDataTwo/TotallyPositive.lean`** (sorry-free, axiom-clean):
  * `Work.SSGRoute.ZDataTwo.kummerCharZMod_eq_zero_of_forall_not_isNegAt` — **the archimedean half
    (β3) of the sign adjustment**: if `b ∈ (↥K)ˣ` is positive at *every* real place of `↥K`, then the
    Kummer character of `b` vanishes at *every* involution of `G_K` (the identity involution being
    handled by `kummerIdx_one`).  Consequently the second conjunct of `signAdjustment_mu2` reduces
    to the element-level statement "`a·s` is positive at every real place", which is exactly what
    `NK.CFTLib.Arl.exists_integral_sign_adjust` produces.
  The remaining half of (β) is now only the *local* congruence argument: `s := 1 + m·u` with `m`
  divisible by each `T`-prime to an exponent at least the `N` of
  `GrunwaldEscapeCore.exists_pow_eq_of_isCongAt` makes `s` a local square at the `T`-primes, hence
  (`GrunwaldEscapeCore.kummerChar_eq_zero_on_decomp_of_localPow`) kills the local groups at `T`.

### SESSION 15 (cont.): the correction step is ALREADY PROVED for every `p`, and the local route

* **`Work.SSGRoute.GrunwaldEscapeCore.gesCorrectionFromPrime`** (in
  `Submission/Work/SSGRoute/GrunwaldEscapeCore/gesCorrectionFromPrime.lean`) is **sorry-free** and
  proves the correction *for every prime `p`, hence also for `p = 2`*: given the datum at `T`, the
  element `a ∈ Kˣ`, the `T`-free fractional ideal `𝔵` of `a` adjusted at a single new prime `𝔮`
  (`h𝔵div`, `h𝔵𝔮`) and the ray-class membership `hmem : mk(fracIdele 𝔵) ∈ gesU ↥K p T'`, it produces
  `b ∈ Kˣ` with exactly the two `p`-independent clauses of the correction:
  * `b` has the *same* local Kummer data as `a` at every place of `T`
    (`kummerCharZMod a = kummerCharZMod b` on each local group);
  * `b` is unramified at every finite place outside the classes of `T'` and of `𝔮`.

  There is therefore a **second, sorry-free route** to the correction — the `ges` lane
  (`ges_readoff`, `gesChebotarev_rayClass`, `gesEscapePrimeSplit`, `EscapeCoreLib/readOffSupPow`, all
  sorry-free) — alongside the one that runs through the single `sorry` of
  `grunwald_escape_correction` (its orthogonality).  For `Mu2EscapeCorrection` this is the route to
  take: what the `ges` lemma does *not* supply is precisely the **archimedean** content (that `b` can
  be taken totally positive), and that is what the sign adjustment (β) plus the modulus's real-place
  component (`NK.NUV2.RouteB.Modulus.pos`, whose Chebotarev input is the proved
  `GrunwaldEscapeCore.exists_prime_mem_rayClass`) provide.

* **The local congruence half of (β)**, concretely: with `s := 1 + m·u` (`u ∈ 𝓞 ↥K` from
  `exists_integral_sign_adjust`, `m` divisible by each `T`-prime), one shows
  `kummerCharZMod (K := ↥K) 2 (ζ := ζ) hζ s (gesLocalToGalK K σ) = 0` for every local group of `T`
  by the chain
  `s ≡ 1 (mod 𝔭^N)` ⟹ `s` is a square in the completion (`exists_pow_eq_of_isCongAt`, whose modulus
  is the `IsCongAt` of `NK.NUV2.RouteB`, bridged by
  `NK.NUV2.RouteB.CongCount.finite_rayClassGroup_congSubgroup`'s
  `mem_principalUnitBall ↔ IsCongAt`) ⟹ `localPowClass ↥K 2 𝔭 s = 1`
  (`ZConstruction.localPairingValue`'s `localPowClass_eq_one_of_unit_component`, and the dictionary
  `ZConstruction.kummerCharMonoidHom_eq_one_iff` in the other direction) ⟹ vanishing on the local
  group (`GrunwaldEscapeCore.kummerChar_eq_zero_on_decomp_of_localPow`).  The prime `𝔭_A` below a
  place `A ∈ T` is manufactured by
  `Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime` (with
  `isFinPlace_of_isFinPlace_below` and `Submission.NeukirchUchida.primeOf_spec`, as in
  `ZConstruction/localPairingValue.lean`), and the "modulus integer" `m := ∏_{A ∈ T} q_A^{N_A}`
  (`q_A` the rational prime below `𝔭_A`) lies in `𝔭_A^{N_A}` for every `A` because `q_A ∈ 𝔭_A`.

* **The last third of that chain is now a theorem** —
  `Submission/Work/SSGRoute/ZDataTwo/LocalCongruence.lean` (sorry-free, axiom-clean):
  `Work.SSGRoute.ZDataTwo.kummerCharZMod_eq_zero_of_isSquare_completion`: if the image of `s ∈ Kˣ` in
  the completion at `𝔭` is a square (equivalently, lies in the range of
  `NK.UchidaKummer.ellPowSubgroup _ 2`, the squaring map), then
  `kummerCharZMod s (gesLocalToGalK K σ) = 0` for every `σ` in the local group.  The proof is the
  banked chain: membership in `ellPowSubgroup` ⟹ `localPowClass ↥K 2 𝔭 s = 1`
  (`Work.SSGRoute.localPowClass_eq_one_of_unit_component`) ⟹ the vanishing
  (`Work.SSGRoute.GrunwaldEscapeCore.kummerChar_eq_zero_on_decomp_of_localPow`).

  Hence the whole of (β) now reduces to two *element-level* statements, with no cohomology left:
  (i) `∃ s ∈ Kˣ` congruent to `1` modulo every `T`-prime to the exponent of
  `exists_pow_eq_of_isCongAt` with `a·s` positive at every real place — `s := 1 + m·u` from
  `NK.CFTLib.Arl.exists_integral_sign_adjust`; and
  (ii) the adic bridge "`s - 1 ∈ 𝔭^N` ⟹ the completion image of `s` has valuation `≤ exp(-N)`",
  for which `exists_uniformizer_adicCompletionIntegers` (the maximal ideal is the span of a
  uniformizer of valuation `exp(-1)`, with multiplicativity of the valuation) is the input, giving
  the `IsCongAt` hypothesis of `exists_pow_eq_of_isCongAt` (whose exponent comparison is monotone).

  Once `kummerCore_of_three_halves` is applied to the three halves produced by (1)–(3), the core
  `Work.SSGRoute.shafarevich_z_data_two_kummerCore` (the only `sorry` of this file) is discharged and
  the node is complete. -/

/-! ## SESSION 16: the `p = 2` sign adjustment is PROVED, and the archimedean crux is isolated

**Two new proved modules of this lane** (both sorry-free and axiom-clean
`[propext, Classical.choice, Quot.sound]`, measured with `#print axioms`):

* `Submission/Work/SSGRoute/ZDataTwo/AdicBridge.lean` (now builds; it was left broken in the
  previous session): `Work.SSGRoute.ZDataTwo.algebraMap_mem_maximalIdeal_iff` (the `N = 1`
  correspondence between `𝔭.asIdeal` and the maximal ideal of the completion's integers) and
  `Work.SSGRoute.ZDataTwo.isCongAt_adicCompletion_of_mem_asIdeal_pow` — **the adic bridge**: if
  `y ∈ 𝔭^N` and `(y : K) = (s : K) - 1` then the image of `s` in the `𝔭`-adic completion satisfies
  `NK.NUV2.RouteB.IsCongAt K N 𝔭`, the hypothesis of
  `GrunwaldEscapeCore.exists_pow_eq_of_isCongAt`.
  Fixes recorded for the next session: `rw [Valuation.mem_maximalIdeal_iff]` does **not** fire on
  `IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)` (the def is not unfolded); use
  `Valuation.mem_maximalIdeal_iff (𝔭.adicCompletion K) (Valued.v)` applied to the whole iff, then
  `simp only [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply]`
  and `rw [valuedAdicCompletion_eq_valuation', valuation_lt_one_iff_mem]`.  Powers:
  `pow_le_pow_left'` (there is no `pow_le_pow_left` in this Mathlib).
  `Ideal.absNorm_mem I : (Ideal.absNorm I : 𝓞 K) ∈ I` replaces the rational prime below `𝔭`.

* `Submission/Work/SSGRoute/ZDataTwo/SignAdjustment.lean` — **the archimedean half (β) of the `p = 2`
  escape construction is a theorem**: `Work.SSGRoute.ZDataTwo.signAdjustment_mu2` — for `a ∈ (↥K)ˣ`
  and a finite place set `T` there is `s ∈ (↥K)ˣ` which kills the local Kummer character on every
  local group of `T` and such that `a · s` kills every involution of `G_K`.  Construction:
  `s = 1 + m·u` with `m := 2 · ∏_{A ∈ T} (absNorm 𝔭_A)^{N_A}` (`N_A` from
  `exists_pow_eq_of_isCongAt 2 𝔭_A`, so `m ∈ 𝔭_A^{N_A}` and `s ≡ 1 (mod 𝔭_A^{N_A})`) and `u` from
  `NK.CFTLib.Arl.exists_integral_sign_adjust`; the local vanishing is
  `AdicBridge` + `exists_pow_eq_of_isCongAt` + `LocalCongruence`, the total positivity is
  `TotallyPositive`.  Key bridge lemma proved here:
  `ringEquivRealOfIsReal_algebraMap_eq (w) (hw) (y) :
  ringEquivRealOfIsReal hw (algebraMap K w.Completion y) = embedding_of_isReal hw y`
  (via `ringEquivRealOfIsReal_apply` + `extensionEmbeddingOfIsReal_coe`).  If `↥K` has no real place
  the statement is satisfied by `s := 1`.

* `Submission/Work/SSGRoute/ZDataTwo/Mu2EscapeSquare.lean` (sorry-free, axiom-clean):
  `Work.SSGRoute.ZDataTwo.kummerCharZMod_two_mul` — **the `ZMod 2`-valued Kummer character is
  multiplicative in the element** (`kummerCharZMod_two_eq_kummerChar` + `kummerChar_mul`, which is
  the fact that had not been isolated before).  The module also carried a "datum-free" half of the
  escape step, `Mu2EscapeCorrectionPos` (`∀ a`, `a` totally positive, `⟹ ∃ Q b` with the same local
  data, `b` totally positive, unramified outside `cs(T) ∪ {Q}`, `Q` split in `N`), together with the
  reduction `Mu2EscapeCorrectionPos → Mu2EscapeCorrection` via `signAdjustment_mu2`.  **That half is
  FALSE** and has been removed (see the counterexample below); `Mu2EscapeCorrectionPos` and
  `mu2EscapeCorrection_of_pos` no longer exist.  What the module now contains instead is
  `Work.SSGRoute.ZDataTwo.nodeKummerCocharZMod_eq_nodeKummerCochar` — **the bridge between the two
  `p = 2` encodings of the Kummer cochain**: `ZSplit.nodeKummerCocharZMod` (the `kummerCharZMod`-based
  cochain produced by the escape steps) equals `nodeKummerCochar` (the `kummerCochar`-based cochain
  consumed by the §4 assembly of `ZDataTwo/ThreeHalves.lean`, `ZDataTwo/SWFourTwo.lean`).  Without it
  the two halves of §4 speak different languages.

**The precise remaining crux of the `p = 2` escape.**  `Mu2EscapeCorrection` is not obtainable from
the existing odd-`p` route by "same local data + total positivity" bookkeeping, because
`gesCorrectionFromPrime` produces `b = a · γ⁻¹` where `γ` is the read-off element of
`readOff_gesU` (a local `2`-power at the primes of `T`, `2 ∣ count(𝔵) - count(γ)`); the correction
therefore *changes the class in `Kˣ/(Kˣ)²` at the real places* by `[γ]`, so `b` is totally positive
iff `a` is and `γ` **is** totally positive.  The freedom in the decomposition
`fracIdele 𝔵 = principalIdele γ · e` (`e ∈ powTIdeles`) is by elements `δ ∈ Kˣ` which are `T'`-units
and local squares at `T'`; their real signs are not free in general, so this is a genuine arithmetic
condition, not bookkeeping.  Two further findings, so that they are not rediscovered:

* The naive "square-normalised" correction — *keep the Kummer class exactly* (which is what the
  paper's `z̃_i x^{±2}` adjustment does) — is **false** for an arbitrary input: with `k = ℚ`,
  `K = ℚ(i)`, `T` the place over `2`, `a = 17 = (4+i)(4-i)`, every element of the square class of
  `17` has odd valuation at *both* primes `(4+i)`, `(4-i)` of `ℚ(i)`, which lie over different places
  of `K` and are therefore *not* `G_K`-conjugate, so no single escape prime `Q` can absorb them.  In
  the paper the `z̃_i` are already unramified outside `S ∪ {P_i}` (condition (1)), which is what makes
  the square adjustment work there.
* The existing `gesEscapeTrivialPair` route *does* confine the ramification (it produces `b = aγ⁻¹`
  with `div(b)` even away from `T'`), so the confinement part of `Mu2EscapeCorrection` is available
  for an *arbitrary* input — see `ZDataTwo/mu2Correction_confinement` in SESSION 16 (cont.) below.

**THE `p = 2` ESCAPE STEP AS STATED IS FALSE (datum-free form).**  An independent prover (a child
spawned for the earlier `Mu2EscapeCorrectionPos` of `Mu2EscapeSquare.lean`) produced, and this
session re-checked, the following counterexample: `k = ℚ`, `K = ⊥` (so `↥K = ℚ`), `N = ℚ(√5)`,
`T = {A₂, A₅}` (places over `2` and `5`), `a = 3`.  `hTfin`, `hTdisj`, `hTcov` all hold and `a = 3`
is totally positive, yet the conclusion fails: with `q` the rational prime below the escape place,
`¬ gesKConj K A Q` gives `q ∉ {2,5}` and `IsSplitIn k N Q` gives `q ≡ 1, 4 (mod 5)` (reciprocity,
`5 ≡ 1 mod 4`), while the local-data clauses give `[b]₂ = [3]₂`, `[b]₅ = [3]₅` and the unramifiedness
clause forces `b = 2^e 5^f q^g t²`; then `[b]₅ = [3]₅` forces `f = 0`, `[b]₂ = [3]₂` forces
`e = 0` and `q ≡ 3 (mod 8)`, and then `[b]₅ = [q]₅ = [3]₅` forces `q ≡ 2, 3 (mod 5)` — a
contradiction.  Hence the datum-free form is false, and `Mu2EscapeCorrectionPos` /
`mu2EscapeCorrection_of_pos` have been **deleted** from `Mu2EscapeSquare.lean` (only
`kummerCharZMod_two_mul` survives there).

The mechanism: at the places over the primes where `N/k` is ramified (`5` here) the local datum
forces `h(A) ≠ 0`, so `horth` forces the escape prime to be *nonsplit* in `N` there, and the
resulting congruence on `q` is incompatible with `q` splitting in `N`.  The odd-`p` analogue
(`GrunwaldEscapeCore.gesEscapeTrivialPair`, proved) escapes this because (i) there the escape prime
is only required to be split in `K` (produced by the same Čebotarev step), and (ii) the realising
element `a` there is *constructed* by Grünwald + Kummer, so its divisor class can be adjusted —
whereas `Mu2EscapeCorrection` quantifies over an arbitrary input `a`.

**The structural reason, isolated (and it does not depend on `horth`).**  Write `U = gesU ↥K p T'`,
`T'` the primes of `K` below `T`, and `x = mk(fracIdele 𝔡)`, where `𝔡` is the `T'`-free part of the
divisor of a realising element `a ∈ (↥K)ˣ`.  The *datum's* local data at `T` determines `x` modulo
`U`, and the Čebotarev step `gesEscapePrimeSplit` realises a prime `𝔮` with `[𝔮] ∈ x⁻¹U`; requiring
in addition that `𝔮` **split in `N`** is the Čebotarev condition "the coset `x⁻¹U` meets the
preimage of `1` under `Gal(M|k) → Gal(N|k)`" for the class field `M` of `U`.  That intersection is
**empty** as soon as the local data forces a class `x` whose `Gal(N|k)`-image is nontrivial, and for
a place `A ∈ T` over a prime ramified in `N` the datum at `A` is *not* forced to vanish: `horth`
forces the *correction* `h A` to vanish there, but the datum is `g + h A = g`, and `hgram` only
constrains `g` at non-split places *outside* `cs(T)`, so `g`'s (hence `a`'s) local data at `A` is
free and enters `x`.  Concretely, in the counterexample the class condition `[𝔮]·x ∈ gesU` (with
`x = x`) forces, by the computation of the `T'`-free part of the divisor of the realising element,
```
q ≡ 3 or 5 (mod 8),   q ≡ 2 or 3 (mod 5),
```
whereas splitting in `N = ℚ(√5)` reads (quadratic reciprocity, `5 ≡ 1 mod 4`)
```
q ≡ 1 or 4 (mod 5) :
```
(the condition is `±3q ≡ □ (mod 5)`, and `3q ≡ □ (mod 5)` has the solutions `q ≡ 2, 3 (mod 5)`).
So the coset condition and the splitting condition are **disjoint**, `gesEscapePrimeSplit` with the
extra splitting requirement cannot be applied, and the conclusion of `Mu2EscapeCorrection` fails
whenever such a datum is admissible.  This is intrinsic to demanding splitting in a level `N ⊋ K`
at primes of `T`: the escape prime's class is pinned to the inverse of the datum's class.

**But the datum of the §4 recursion is special, and this is what saves the design.**  In the §4
recursion the datum on `cs(S)` is (a restriction of) the *given* `y`, which satisfies
`hyT` (`y` kills the inertia at every finite place of `cs(S)`) and `hy0` (`y` vanishes on the whole
decomposition group of `B ∈ cs(S)` whenever `¬ IsSplitIn k K B ∨ B.valuation 2 < 1`), and at the
earlier escape primes the datum is a prescribed combination of the earlier `z_j`'s.  In particular
the datum at a place over a prime ramified in `Λ` (which lies in `cs(S)` because `T ⊇ Ram(Λ|k)`)
is forced to be *unramified* (hence trivial whenever the place is not split in `K`, or lies over
`2`) — which is exactly the vanishing that the class computation above needs in order for the
coset `x⁻¹U` to meet the splitting condition.  So the counterexample above does **not** show that
the escape step used by §4 is false: it shows that the statement must carry, as a hypothesis on the
datum, the vanishing at the places over the primes that are not split in `N` — `horth`
(`h A = 0` or `A` split in `N`) is the design's (weaker) formulation of that, and the *datum* (not
just the correction `h A`) is what enters the class `x`.  A correct statement therefore has to
control the datum's local data at the non-split places of `T`, e.g. by requiring that the realising
element's local class there be trivial.

**What the next session should do.**  (0) Re-examine the statement of `Mu2EscapeCorrection` (and of
`mu2EscapeRealisation_of_correction`, `Mu2EscapeStep.lean`, which consumes it) against the
counterexample above: the escape prime's splitting in the level `N ⊋ K` cannot be demanded together
with an arbitrary prescribed local datum at the places over the primes ramified in `N`.  Either
`N = K` (proved route: `gesEscapeTrivialPairTwo`, `gesCorrectionFromPrime`,
`mu2Correction_confinement`) or the splitness requirement must be dropped/relaxed (the §4 assembly
`ZDataTwo/ThreeHalves.lean` uses splitness of the escape primes in `Λ`, so this needs care: with
`Λ = K` the available "split in `K`" escape step suffices, and for `Λ ⊋ K` the §4 recursion has to
be redesigned — e.g. by `G_k`-saturating `Pset` and replacing `IsSplitIn k Λ` by a hypothesis on the
orbit).
(1) If the escape step is retained, choose the escape prime `𝔮` by Čebotarev in a ray class whose
*real-place* component forces the read-off element `γ` of `readOff_gesU` to be totally positive (the
paper's construction uses a modulus with real places, `NK.NUV2.RouteB.Modulus.pos`, Čebotarev input
`GrunwaldEscapeCore.exists_prime_mem_rayClass`, both proved) — whilst keeping the ray class
*consistent* with the local datum at `T`, which is precisely what the counterexample forbids in the
datum-free form.
(2) Then the §4 recursion (still unbuilt — the pigeonhole triple, the Claim and the three-term
verification of `ZDataTwo/ThreeHalves.lean` + `ZDataTwo/SWFourTwo.lean`) gives the core.

**Delegation state.**  `request_lemma` at `SSGRoute/ZDataTwo/signAdjustment_mu2` was refused
("the team is busy"); both reviewers had approved the statement, and it has since been proved here
directly.  `Work.SSGRoute.ZDataTwo.mu2EscapeCorrection` (path `SSGRoute/ZDataTwo/mu2EscapeCorrection`,
file `Mu2EscapeCorrection.lean`, statement only, `:= by sorry`) is the earlier, still-open target of
this lane and remains unproved.

### SESSION 16 (cont.): the `hKimag`-free (hence `p = 2`-ready) escape realisation is PROVED

* `Submission/Work/SSGRoute/ZDataTwo/gesEscapeTrivialPairTwo.lean` (proved by a delegated child,
  sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`):
  `Work.SSGRoute.ZDataTwo.gesEscapeTrivialPairTwo` — **the Grünwald-with-escape realisation in the
  case `L₁ = L₂ = K` at every prime `p`, including `p = 2`**: it is
  `GrunwaldEscapeCore.gesEscapeTrivialPair` with the hypothesis
  `hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1` deleted (that hypothesis is false
  precisely in the `p = 2` cases that matter).  The deletion is possible because `hKimag` was used
  only in the single call to `grunwald_kummer_first_element`, for which
  `GrunwaldEscapeCore.kummerFirstElement_noImag` (proved) is the `p = 2`-ready replacement; the rest
  of the proof is copied verbatim.
  **Consequence**: the escape lane now produces, for every prime `p` and every admissible local
  datum `h` on `T`, a class `z` realising `h` on the local groups of `T`, together with a finite
  place `Q` (split in `K`, avoiding the `G_K`-classes of `T`) such that `z` is unramified outside the
  classes of `T` and of `Q`.  This is the previously missing `p = 2` member of the family, in the
  "split in `K`" normalisation — the normalisation under which the escape step is realised by the
  proved Čebotarev machinery (contrast the discussion above of `Mu2EscapeCorrection`'s "split in
  `N`" clause).

### SESSION 16 (cont.): the confinement half of the `p = 2` correction is PROVED for *any* input

* `Submission/Work/SSGRoute/ZDataTwo/Mu2CorrectionConfinement.lean` (builds, sorry-free):
  * `Work.SSGRoute.ZDataTwo.gesKConj_iff_comap_eq` — **two places of `Ω` are `G_K`-conjugate exactly
    when their `K`-primes agree** (the two directions are
    `Work.SSGRoute.comap_smul_eq_of_mem_fixingSubgroup` and
    `Work.SSGRoute.exists_mem_fixingSubgroup_smul_eq_of_comap_eq`, both in this file).  This is the
    bridge between the `ValuationSubring` vocabulary of `Mu2EscapeCorrection` and the prime-ideal
    vocabulary of `gesCorrectionFromPrime`/`gesEscapePrimeSplit`;
  * `Work.SSGRoute.ZDataTwo.mu2Correction_confinement` — **the confinement half of the `p = 2`
    escape correction, for an arbitrary `a ∈ (↥K)ˣ`**: there are `Q` (finite, split in `K`, avoiding
    the `G_K`-classes of `T`) and `b ∈ (↥K)ˣ` with the *same local Kummer data at `T`* as `a` and
    unramified outside the `G_K`-classes of `T` and of `Q`.  This is steps 3–6 of
    `GrunwaldEscapeCore.gesEscapeTrivialPair` re-done with `a` as an input (that file only treats the
    specific element produced by `grunwald_kummer_first_element`, and carries the `p = 2`-unusable
    hypothesis `hKimag`); the coverage hypothesis here is the `gesKConj` form
    (`∀ B, B.valuation 2 < 1 → ∃ A ∈ T, gesKConj K A B`), which is what the Čebotarev step needs.
  So of the two clauses of `Mu2EscapeCorrection` the *local-data* clause is unconditional for every
  input from this construction, and only the *archimedean* clause (`b` totally positive) is missing
  — and that clause is decided by the read-off element `γ` of `readOff_gesU`, whose real-place sign
  is not controllable by the present `gesU` (whose modulus has no real-place component).

* **Statement-shape warning for `Mu2EscapeCorrection`.**  Its coverage hypothesis
  `hTcov : ∀ B, IsFinPlace k B → (…) → ∃ A ∈ T, IsConjPlace k A B` is phrased with *`k`-conjugacy*
  (`IsConjPlace`), whereas the Čebotarev/confinement step needs the `K`-primes of the places over `2`
  to lie in `T'`, which follows only from *`G_K`-conjugacy* coverage
  (`∃ A ∈ T, gesKConj K A B`) — unless `T` is additionally closed under `G_k`-conjugation (as it is
  in the §4 recursion, where `T` is a union of `G_k`-classes).  A proof of `Mu2EscapeCorrection`
  should therefore first convert `hTcov` using that closure (or restate `hTcov` in the `gesKConj`
  form as in `gesEscapeTrivialPair`).

* **Import-cone note.**  `SignAdjustment.lean` now inlines
  `Work.SSGRoute.ZDataTwo.exists_heightOneSpectrum_below` (a copy of
  `GrunwaldEscapeCore.exists_primeIdeal_of_comap_ne_top`) instead of importing
  `gesCorrectionFromPrime.lean`, so that the sign-adjustment module no longer depends on the heavy
  correction-step file.  The tree `SSGRoute.ZConstruction.TransferLevel` →
  `shafarevich_z_construction` → `shafarevich_theorem13` → `ZDataTwo/chebotarev_frobenius_split` is
  imported by `gesEscapePrimeSplit`, so `Mu2CorrectionConfinement` (and hence
  `Mu2EscapeCorrection`) can only be built while that file compiles.

* **The datum hypothesis of `Mu2EscapeCorrection` does constrain signs.**  It is worth recording
  that the "input" `a` of `Mu2EscapeCorrection` is not arbitrary: `a` must *realise* the datum
  `g + h A` on `decomp k A ⊓ G_K` for every `A ∈ T`, and `g` and every `h A` kill involutions, so
  `z_a(c) = 0` for every involution `c` lying in one of those local groups.  Since
  `z_a(c) = 0` says exactly that `a` is positive at the real place of `K` attached to `c`
  (`ZDataTwo.realPlace_involution_kummerChar_iff`), this is genuine archimedean information about
  `a`.  In particular the element of `Kˣ` realising the datum is *not* free, and a proposed
  counterexample to `Mu2EscapeCorrection` must respect this (e.g. `k = K = ℚ`, `T` the unique place
  over `2`, `a = -17`: `-17 ≡ -1 mod 8` is *not* a square in `ℚ₂`, and indeed `z_{-17}` does not
  vanish at the complex conjugation, which lies in that local group, so `a = -17` is *excluded* by
  the datum hypothesis while a direct "same-local-data + totally-positive" search fails for it).
  Consequently a proof of the escape step may — and probably must — use the datum
  hypothesis rather than treating `a` as arbitrary; but this alone does **not** rescue the statement
  (the counterexample of the block above respects `hginf`/`hhinf`/`hgram`/`horth` as far as they
  are checkable, and the real obstruction there is the splitting of the escape prime in `N`). -/

/-! ## SESSION 18: the escape step is *not* false as stated, and the `p = 2` rung is identified

**Correction of the SESSION 16/17 reading of "the escape step as stated is false".**  The refuted
statement was the *datum-free* `Mu2EscapeCorrectionPos` of `ZDataTwo/Mu2EscapeSquare.lean` (a `∀ a`
statement with **no** `hgram` and **no** `horth`), which was correctly deleted.  `Mu2EscapeCorrection`
itself (file `ZDataTwo/Mu2EscapeStep.lean`, statement only in `ZDataTwo/mu2EscapeCorrection.lean`) *does*
carry `hgram`, `horth`, `hginf`, `hhinf`, and with those hypotheses its `IsSplitIn k N Q` clause is
not an obstruction at all: the compatibility `Art_M(𝔡) ∈ Gal(M/(M ⊓ N'))` that the Čebotarev step
`ZDataTwo/…/escape_prime_orthogonality` (proved, sorry-free) consumes is exactly the *orthogonality*
computation, and the route for it is written out in
`GrunwaldEscapeCore/NOTE_hsplit_orthogonality_correct.md` (the `hsplit` trichotomy argument) and
`GrunwaldEscapeCore/NOTE_escape_correction_route.md` §0.  In the specialisation `L₂ = K` the
`hsplit` hypothesis is vacuous and the two third disjuncts are never needed; what remains is the
`L₂ = K` orthogonality `GrunwaldEscapeCore.orthogonality_L2K`, which is a `sorry` on disk, and the
per-place computation of the NOTE's §§3–4.  **This is the rung the `p = 2` escape is missing.**

**The `p = 2` archimedean terms, and the right replacement for `hKimag`.**  The odd-`p` statements
carry `hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1` (vacuously, since they also carry
`hp : p ≠ 2`); it is used in the orthogonality only to make the *archimedean* local terms of the two
Hilbert-symbol product formulas vanish (`K`, hence `N'`, has no real place).  At `p = 2` those terms
reappear and must be killed by the datum, in exactly two ways:

* the pair `(a, c)` (`c` = the Kummer element of the character `χ = χ_c`): the term at a real place
  `v` is the local pairing `(a, c)_v`, which is trivial as soon as `a` is a **local square at `v`**,
  i.e. positive at `v`; hence the hypothesis `hapos` — `kummerCharZMod a c = 0` for every involution
  `c` of `G_K`, equivalently (by `ZDataTwo/RealPlaceInvolution.realPlace_involution_kummerChar_iff`)
  `a` is totally positive;
* the pair `(b_g, c₁)` (`b_g` = the Kummer element of the locally constant additive `g`): the term
  at `v` is the local pairing `(b_g, c₁)_v`, trivial as soon as `b_g` is a local square at `v`, and
  `b_g` realises `g` on all of `G_K`, so this is `g(c_v) = 0` — the hypothesis `hginf`.

Both are already present in `Mu2EscapeCorrection` (`hginf`, `hhinf`) except `hapos`, which is
*constructible*: `Work.SSGRoute.ZDataTwo.firstElement_totallyPositive`
(module `Submission.Work.SSGRoute.ZDataTwo.firstElementTotallyPositive`, **proved this session**,
sorry-free) composes `GrunwaldEscapeCore.kummerFirstElement_noImag` with
`ZDataTwo.signAdjustment_mu2` (via `ZConstruction.kummerCharZMod_add`) to produce an element which
realises the datum on the local groups of `T` **and** is totally positive.  So replacing `a` by that
element, `hapos` is available in the escape construction at no cost.

**The identified rung, henceforth the target of this lane.**
`Work.SSGRoute.ZDataTwo.orthogonality_L2K_two` (path `SSGRoute/ZDataTwo/orthogonality_L2K_two`,
delegated; statement reviewed twice as correct) is `GrunwaldEscapeCore.orthogonality_L2K` verbatim at
`p = 2`, with `hKimag` deleted and `hginf` + `hapos` added.  Together with the **proved**
`GrunwaldEscapeCore.escape_prime_orthogonality` (orthogonality ⟹ escape prime completely split in
`N`), the **proved** `step4_y_escape_v2.correctionFromPrime_supPow` (reading-off), the **proved**
`ZData2.mu2Correction_confinement` (confinement) and the **proved**
`firstElement_totallyPositive` (datum + total positivity), it yields the `p = 2` escape with the
escape prime **split in `Λ`** — the normalisation that `ZDataTwo/ThreeHalves.lean`
(`unramified_outside_of_confinement`) needs.  What is *not* covered by this list is the total
positivity of the **read-off** element `γ` (i.e. of the corrected class `b = a s / γ`), which is the
paper's "the modulus contains the real places" step; it is the second `p = 2` addition and is
recorded as the next obligation after the orthogonality.

**Why a single escape step does not give the core (checked this session).**  With `Pset = {Q}` the
assembly `kummerCore_of_three_halves` still needs `hconj`: the *sum* `z_{b₀}+z_{b₁}+z_{b₂}` vanishes
on the local groups of the one-sided companions of `Q`.  A single escape step only yields
*unramifiedness* (inertia-killing) at those companions, not vanishing — the escaping class is
ramified at `Q` and its `G_k`-conjugates carry the conjugate local class.  This is exactly why the
paper needs three escape primes with the matching prescriptions (conditions (3), (4)) and the
pigeonhole `ZDataTwo.pigeonhole_three`; `three_term_cancellation`, `two_partition` and
`pigeonhole_three` are on disk, so the missing pieces are the *prescription* bookkeeping and the
Claim `(z_i)_{σP_i} = 0` for involutions `σ`.

**The hypothesis at the places of `T`: the *trichotomy*, not the two-disjunct `horth`.**  A second
finding of this session, which fixes the exact shape of the escape primitive that the recursion
needs.  `ZDataTwo/Mu2EscapeStep.lean` (and `GrunwaldEscapeCore/escape_realisation_core.lean`) state
their local hypothesis as

```
horth : ∀ A ∈ T, (∀ σ ∈ D_A ⊓ G_K, h A σ = 0) ∨ IsSplitIn k N A
```

and this two-disjunct form is **not** derivable from the node's hypotheses: take `k = K = ℚ`
(so `IsSplitIn k K B` always holds), `Λ = ℚ(√5)`, and `S = {places over 2, over 5, over 3}` (so
`hSram` holds and `cs(S) ∋` the places over `3`); a place `B` over `3` is in `cs(S)`, satisfies
`B ∤ 2` and `IsSplitIn k K B`, hence `hy0` puts **no** constraint on `y` at `B`, while
`¬ IsSplitIn k Λ B` (3 is inert in `ℚ(√5)`).  Such a datum `y` (unramified at `B` by `hyT`, with
nonzero Frobenius value there, and killing the involutions — the complex conjugation is in every
decomposition group over `ℚ`) satisfies every hypothesis of the node, yet `horth` fails at `B`.
Moreover `B` *must* lie in `T` for clause (1), because clause (1) demands `z_b = y` on `D_B ⊓ G_K`
for **every** `B ∈ cs(S)`.  What does hold is the **trichotomy** `horth₁` of
`grunwald_escape_correction_hsplit`/`orthogonality_hsplit` specialised to `L₁ = N`: its third
disjunct ("`h A` kills the inertia of `A`" — `hyT` — and "every character killing `N.fixingSubgroup`
kills the inertia of `A`" — automatic because `N/↥K` is unramified outside `T'`) covers exactly the
places `A ∈ T'` at which `hy0` is silent.

**The `p = 2` orthogonality in its usable form is therefore
`Work.SSGRoute.ZDataTwo.orthogonality_L2K_trichotomy_two`** (path
`SSGRoute/ZDataTwo/orthogonality_L2K_trichotomy_two`, statement reviewed twice as correct,
delegated): the same conclusion as `orthogonality_L2K_two`, with `horth` replaced by the
trichotomy `horth₁` (at `L₂ = K`, `horth₂` is vacuous — its disjunct (ii) reads
`D̄_A ⊆ K̄₂ = V`, always true — and `hsplit` is automatic since `L₁ = N` gives `K̄₁ = 0`; both facts
are what the NOTE's closing of case (iii) needs).  The two-disjunct statement
`orthogonality_L2K_two` is *stronger as a hypothesis*, hence a corollary of the trichotomy form; it
is worth keeping only as a cross-check.

**The narrow modulus is the right normalisation for `p = 2` (design note for the next stretch).**
The orthogonality `orthogonality_L2K_trichotomy_two` is stated with the *archimedean* hypotheses
`hapos` (the realising element `a` is totally positive) and `hginf` (the Kummer element of `g` is),
which is what makes the two archimedean product-formula sums vanish.  There is a second, cleaner
normalisation: put the *real places* into the modulus, i.e. replace `gesU K 2 T'` by the "narrow"
group whose `T'-free` part is `im(Kˣ · E_{T,unr}^{narrow})` with `E^{narrow}` requiring the *infinite*
components of the idèles to be **positive**.  Then every character `χ` killing the narrow `U'` is
trivial at every real place of `↥K`, so the archimedean summands `(a, c)_v` and `(b_g, c₁)_v` of the
two product formulas vanish **for every `a`** — no `hapos` and no `hginf` are needed at all — and the
*narrow read-off* produces `γ` **totally positive**, so that the corrected class
`b = a s γ⁻¹` is totally positive and the third clause of `Mu2EscapeCorrection` ("`b` kills the
involutions") becomes free.  This is exactly the paper's `T ⊇ S_∞`.  What is missing for it is the
narrow analogue of the `gesU` lane: the definition of the narrow group (`powTIdeles` keeps only
*finitely many* components, so the positivity of the infinite components has to be built in), its
openness and finite index (`isOpen_gesU`, `finiteIndex_gesU` have narrow analogues), the narrow
`readOff`, and the narrow `escape_prime_orthogonality`.  With those, `Mu2EscapeCorrection` (with the
trichotomy `horth₁` in place of the two-disjunct `horth`, see the previous paragraph) becomes
provable from the pieces already on disk plus the orthogonality now being delegated.

**Status of this session.**  (i) `firstElement_totallyPositive` proved (axiom-clean); (ii) the
trichotomy form of the `p = 2` orthogonality delegated (child running); (iii) the coarse form and
the trichotomy form of the orthogonality both reviewed as correct; (iv) the interface findings above
recorded.  The node still builds with exactly one `sorry` (the core).

### SESSION 18 (cont.): the orthogonality is *already proved* in this workspace — the `p = 2` gap is the archimedean layer

This is the single most important thing to know before attacking the escape step again, and it was
found by reading (not by proving).

**Two sorry-free proofs of the orthogonality already exist**, both at *general* `p`, *general*
`L₁ L₂`, with the trichotomy `horth₁`/`horth₂`, with `hsplit`, and with the hypothesis

```
hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1
```

(`↥K` has no real place):

* `Work.SSGRoute.N2v2.orthogonality_hsplit_proved`
  (`Submission/Work/SSGRoute/N2v2/orthogonality_hsplit_proved.lean`, 565 lines, **no `sorry`**;
  its whole `N2v2/` cone — `artin_fixes_of_local_factors`, `artin_fixes_of_local_units`,
  `kummerChar_archimedean`, `heart_localSum_vanishes`, `alpha_fixes_inf_proved`, `levelField`,
  `kummer_level_realisation`, `separation`, `kummerSplit_of_hsplit`, … — is sorry-free too);
* `Work.SSGRoute.ZRealV2.orthogonality_core`
  (`Submission/Work/SSGRoute/ZRealV2/orthogonality_core.lean`, also sorry-free, same hypothesis
  set; the sibling `ZRealV2/alpha_fixes_inf_hsplit.lean` has one `sorry`, at the "`α` fixes the
  level" step).

So the *only* missing case of the orthogonality is **`p = 2` with a real place of `↥K`**.

**What `hKimag` does, exactly.**  It is used only to derive
`hnoReal : ∀ w : NumberField.InfinitePlace ↥K, w.IsComplex` (via
`N2v2.noRealPlace_of_hKimag_zeta` / `SSG8Escape.localField_not_real_of_no_involutions`), i.e. "every
archimedean local factor is `1`".  Concretely it is consumed in four places, all archimedean:

1. `N2v2.mem_normImage_of_localUnits_of_trivialOn` (`N2v2/artin_fixes_of_local_factors.lean:53`),
   used by `N2v2.artin_fixes_of_local_factors` to see that the "unit part" `u'` of the idèle
   decomposition of the Grünwald element is an idèle **norm** — its archimedean case collapses the
   local norm subgroup to `⊤`;
2. `N2v2.kummerChar_archimedean` (`N2v2/kummerChar_archimedean.lean`), i.e. the hypothesis
   `hχarch` of `N2v2.char_eq_neg_localSum`: at an archimedean place the local field is `ℂ`, its unit
   group is divisible, and any homomorphism from a divisible group to the finite group
   `Gal(M/↥K)` is trivial, so the archimedean local factors of the Artin family are killed by `χ`;
3. `N2v2.arch_localFactor_eq_one_aux` (`N2v2/artin_fixes_of_local_units.lean`), used at
   `orthogonality_hsplit_proved.lean:449`;
4. `N2v2.heart_localSum_vanishes` (used at `orthogonality_hsplit_proved.lean:499`), the archimedean
   summands of the diagonal computation.

**What replaces it at `p = 2` (two different, *independent* conditions!).**  At a real place `w` the
local pairing of two Kummer elements `x, y` is `1` unless both are negative at `w`; so an
archimedean term vanishes as soon as **one** of its two arguments is positive at `w`.  Two arguments
occur:

* the **Grünwald element** `a` (pairs with the character's element `c` in the product formula
  `(F_c, a)`, and `u'_w = a` in step 1 above): it can be taken **totally positive** — this is
  `Work.SSGRoute.ZDataTwo.firstElement_totallyPositive` (proved this session, axiom-clean), the
  composition of `GrunwaldEscapeCore.kummerFirstElement_noImag` with
  `ZDataTwo.signAdjustment_mu2`.  In the statement this is `hapos`;
* the Kummer element `b_g` of the **global part** `g` of the datum (pairs with `c₁` in the
  `(b_g, c₁)` product formula): `b_g` is totally positive as soon as `g` kills the involutions,
  since `b_g` realises `g` on all of `G_K` (`ZSplit.exists_kummerCocharZ_of_additive_locConst`) and
  every involution is a complex conjugation (`ZDataTwo.realPlace_involution_kummerChar_iff`).  In
  the statement this is `hginf`.

Both are already available; `hapos` costs nothing (replace `a` by the totally positive element of
`firstElement_totallyPositive`).

**But there is a third archimedean requirement, and it is *not* about `a` or `b_g`.**  `hχarch`
(step 2) asks that the *character* `χ = χ_c` be trivial on the archimedean local groups, i.e. that
the Kummer element `c` of `χ` be **positive at every real place of `↥K`** (a complex place poses no
problem: the local norm is onto there).  That is *not* automatic for the characters in the
annihilator of `U' ⊔ N_{N'}` when `U' = gesU ⊔ pPow` is the *wide* modulus: `powTIdeles` puts no
condition at the infinite places at all (`Place.localUnits K (ofInfinite w) = ⊤`,
`NK/GlobalCFT/Place.lean:170`), so the sign classes are not in `U'` and there are characters with
`c < 0` at a real place.  Consequently:

* the two-disjunct/trichotomy statements `orthogonality_L2K_two` and
  `orthogonality_L2K_trichotomy_two` **as delegated this session are of doubtful provability at
  `p = 2`**: their hypotheses (`hapos`, `hginf`) kill the *`a`-side* and *`b_g`-side* archimedean
  terms of the two product formulas, but not `hχarch` of `char_eq_neg_localSum`.  A correct
  statement must either (a) put the real places into the modulus — the **narrow** `gesU`, whose
  characters are automatically trivial at the real places, this being the paper's `T ⊇ S_∞` — in
  which case `hapos`/`hginf` become unnecessary as well; or (b) restrict the characters in the
  separation step to those with `c > 0` at the real places and show that they already separate
  points modulo `U' ⊔ N_{N'}`.
* `mem_normImage_of_localUnits_real` (`Submission/Work/SSGRoute/ZDataTwo/mem_normImage_of_localUnits_real.lean`,
  proved this session, axiom-clean) is the `p = 2` form of step 1's norm criterion: it replaces
  "`↥K` has no real place" by the honest local condition at the real places, so it is a piece of
  *either* route — with the narrow modulus the hypothesis is supplied by `a`'s positivity, and it
  is not needed at all for complex places.

**A second, independent finding (from the reviewers of an attempted shortcut).**  The
decomposition group of a *finite* place of `Ω` over `k` is `≅ G_{k_𝔭}`, which has **no element of
order two** (`k_𝔭` is not orderable: `-1` is a sum of four squares, so it has no real-closed
subfield).  Hence **involutions never lie in a finite-place local group**, and the core's clause (2)
("`z_b` kills the involutions") can never be obtained from the `T`-prescriptions of the escape step
— it is exactly the *archimedean* clause, i.e. the total positivity of the corrected class.  An
attempted shortcut (`kummerCore_of_three_halves_covered`, `hcov` + `hyinf` in place of `hinv`) was
reviewed and rejected for this reason and is *not* delegated.  This confirms that the `p = 2`
escape step needs the **narrow** modulus (so that the read-off element `γ` is positive, making
`b = a s γ⁻¹` totally positive).

**The remaining `p = 2` obligations, in order.**  (1) the escape step itself
(`Mu2EscapeCorrection` with the trichotomy), from the orthogonality + `escape_prime_orthogonality` +
`correctionFromPrime_supPow` + the positivity of the read-off; (2) the §4 recursion (three escape
steps with the prescriptions (3),(4), the pigeonhole `ZDataTwo.pigeonhole_three`, the Claim
`(z_i)_{σP_i} = 0` for involutions); (3) the assembly into the core via
`kummerCore_of_three_halves`.

### SESSION 18 (cont.): **THE `p = 2` ORTHOGONALITY IS PROVED** — the rung is closed

```
Work.SSGRoute.ZDataTwo.orthogonality_L2K_trichotomy_two
  Submission/Work/SSGRoute/ZDataTwo/orthogonality_L2K_trichotomy_two.lean
```

is **proved and axiom-clean** (`#print axioms` = `[propext, Classical.choice, Quot.sound]`), by a
delegated child.  It is the `L₁ = N`, `L₂ = K` specialisation of `N2v2.orthogonality_hsplit_proved`
at `p = 2`, with `hKimag` deleted and the archimedean behaviour supplied by `hapos` (the realising
element totally positive) and `hginf` (the global part's Kummer element totally positive).  This is
the statement that the escape lane's Čebotarev step (`GrunwaldEscapeCore.escape_prime_orthogonality`,
proved) consumes to produce an escape prime **completely split in the level `N`** — the
normalisation `ZDataTwo/ThreeHalves.lean` needs.  Its two companion statements
(`orthogonality_L2K_two`, the two-disjunct form, and the as-delegated trichotomy form) are both
reviewed correct; the trichotomy form is the one on disk.

**Consequence for the escape step.**  Assembling

* `GrunwaldEscapeCore.kummerFirstElement_noImag` (the realising element),
* `ZDataTwo.firstElement_totallyPositive` (make it totally positive),
* `ZDataTwo.orthogonality_L2K_trichotomy_two` (the orthogonality, just proved),
* `GrunwaldEscapeCore.escape_prime_orthogonality` (the escape prime, split in `N`),
* `Work.SSGRoute.step4_y_escape_v2.correctionFromPrime_supPow` / `gesCorrectionFromPrime` (the
  reading-off), and
* `ZDataTwo.signAdjustment_mu2` (to make the corrected element totally positive),

now gives the `p = 2` escape step with the escape prime split in `N` — **except** for one point: the
total positivity of the *corrected* element `b = a·s·γ⁻¹` requires the read-off element `γ` to be
totally positive, and the *wide* `gesU` (`powTIdeles` imposes nothing at the infinite places,
`NK/GlobalCFT/Place.lean:170`) gives no control over `γ`'s signs.  Controlling them is exactly the
paper's "the modulus contains the real places", i.e. the **narrow** version of the read-off /
Chebotarev step (choose the escape prime in a *narrow* ray class).  Note that the involutions can
*never* be reached by the escape step's finite-place prescriptions (the decomposition group of a
finite place has no element of order two — every such group is `≅ G_{k_𝔭}`, and `k_𝔭` is not
orderable), so the total positivity really has to come from an archimedean (narrow) input.

**Newly proved this session, axiom-clean** (both small, both on the critical path):

* `Work.SSGRoute.ZDataTwo.firstElement_totallyPositive` —
  `Submission/Work/SSGRoute/ZDataTwo/firstElementTotallyPositive.lean`: the `p = 2` realising element
  of the escape, canonicalised to be totally positive (`kummerFirstElement_noImag` composed with
  `signAdjustment_mu2` via `kummerCharZMod_add`);
* `Work.SSGRoute.ZDataTwo.mem_normImage_of_localUnits_real` —
  `Submission/Work/SSGRoute/ZDataTwo/mem_normImage_of_localUnits_real.lean`: the archimedean step of
  the orthogonality as an honest local criterion (`N2v2.mem_normImage_of_localUnits_of_trivialOn`
  with "`↥K` has no real place" replaced by "the components at the real places are local norms").

**Roadmap file.**  `Submission/Work/SSGRoute/ZDataTwo/NOTE_N2v2_route_p2.md` records the whole
adaptation (what `hKimag` is used for, the sign-class argument that replaces it at `p = 2` — `U'`
contains the classes of the idèles `(-1 at v, 1 elsewhere)` because `powTIdeles` is unrestricted at
the infinite places, so the characters of `C_↥K/U'` are trivial at the real places — and the two
templates `N2v2/orthogonality_hsplit_proved` and `ZRealV2/orthogonality_core`). -/

/-! ## SESSION 19: the `p = 2` escape oracle and the first recursion stage — the design is now fixed

**Read `Submission/Work/SSGRoute/ZDataTwo/NOTE_session19_p2_recursion.md` first; it supersedes the
SESSION 18 blocks on the two points below.**  Two facts change the plan this session.

**The `p = 2` escape oracle is proved.**  `Work.SSGRoute.ZDataTwo.mu2EscapeRealisationH`
(`Submission/Work/SSGRoute/ZDataTwo/mu2EscapeRealisationH.lean`, **sorry-free, axiom-clean**, a
delegated child of the same lane) is exactly the primitive the §4 recursion of the exceptional case
consumes: for a finite place set `T` (pairwise non-`gesKConj`, covering the `2`-places and the
`Λ`-ramified places up to `K`-conjugacy), a global datum `g` and a per-block correction `h` with
`horth : h A ≡ 0 ∨ IsSplitIn k Λ A`, `hinertia : g + h A` kills the inertia of `A`, and both killing
the involutions, it returns `b ∈ Kˣ` and a finite `Q`, completely split in `Λ`, outside the
`T`-classes, with `χ_b = g + h A` on `decomp k A ⊓ G_K` for `A ∈ T`, `χ_b` killing the involutions,
and `χ_b` unramified outside the `T`-classes and the `Q`-class.  It is `hKimag`-free (the narrow
modulus and total positivity replace `hKimag`), so the SESSION 16/17 objection to the escape route
("needs `hKimag`") no longer applies to *this* oracle.  Together with the **proved**
`ZDataTwo.kummerCore_of_three_halves` (assembly), `ZDataTwo.threeTerm_kills_localGroup`
(verification) and the combinatorics (`pigeonhole_three`, `two_partition`,
`three_term_cancellation`, `sw_frob_vanishing_G1`, `chebotarev_frobenius_split`), the remaining work
on the core is:

1. `Work.SSGRoute.ZDataTwo.firstEscape_two` (**proved this session, axiom-clean**;
   `Submission/Work/SSGRoute/ZDataTwo/firstEscape_two.lean`, with the helper
   `nodeKummerCochar_conj_two`) — stage 1 of the recursion: the oracle applied to `y` itself on
   `T = krep K (kleadReps K S)`.  Two technical points, both reusable later: `kleadReps` alone is
   **not** pairwise non-`G_K`-conjugate (a place of `cs(S)` may have a nontrivial decomposition
   group in `Gal(K|k)`), so the one-per-class set is `H9.krep K (kleadReps K S)`; and the oracle's
   agreement clause transports from the `T`-blocks to all the `k`-conjugates of `S` by
   `G_K`-conjugation invariance of `χ_b` and of `y` (`additive_conj_invariant`);
   (`ZDataMup.clause_one_of_covering` does the same job with unbundled local-group binders — the two
   spellings `nodeKummerCochar` / `ZSplit.nodeKummerCocharZMod` are definitionally equal at `p = 2`);
2. the recursion of `ZDataTwo/NOTE_session19_p2_recursion.md` §1–§2 (the prescriptions (3)/(4) with
   the branches determined by `N`-minimality of the pigeonhole triple);
3. the two arithmetic tools isolated there: the **crossed two-place reciprocity**
   `z_s(Frob_{σQ_t}) = z_t(Frob_{σ^{-1}Q_s})` (the paper's chain; the slot that
   `H9/swHistChi_chain_proved.lean` found to be missing in the odd-`p` statement, and which at
   `p = 2` is *not* a consequence of the odd-`p` argument because the pairing of two unramified
   classes is no longer trivial — see `ZDataMup/NOTES_LT_localArtinPairing_session.md`), and the
   **involution Claim** `(z_i)_{σP_i} = 0` for `σ ∈ G₁`.

**A correction of the SESSION 18 reading of the pigeonhole.**  The paper's `Ψ_n(z_i)` is the vector
of the values of `z_i` at the siblings of ***its own*** escape prime `P_i` (the extracted text has
`(z_i)_{σ_j P_i}(Frob_{σ_j P_i})`), so the shoe-box condition is
`Ψ_i(z_i) = Ψ_j(z_j) = Ψ_N(z_N)`, i.e. the three selected classes have *equal own-sibling values* —
which is exactly what the verification uses.  The formalised `ZDataTwo.pigeonhole_three` is the
right combinatorial input with `a n := Ψ_n(z_n)`.  The `N`-minimality plus choosing `j` minimal and
`i` maximal makes the two branches of the paper's condition (4) at stages `j` and `N` consistent;
the three equations `(z_i)_{σP_t} + (z_j)_{σP_t} + (z_N)_{σP_t} = 0` (`t = i, j, N`) were verified by
hand for `σ ∈ G₁, G₂, G₃` against the rules of (4) and the crossed reciprocity.  A *symmetric*
prescription rule cannot work: it would force the pigeonhole value `v_σ` to vanish.

**SESSION 19/20 continuation (the recursion stages and the crossed identity):** the recursion now
has its three stages, all proved and axiom-clean — `ZDataTwo/firstEscape_two.lean` (stage 1),
`ZDataTwo/secondEscapeCompanions.lean` (stage 2: cancels the companions of the first escape prime)
and `ZDataTwo/thirdEscapeCompanions.lean` (stage 3: the running-sum prescription, cancelling the
companions of the first two) — together with the minimal shoe box
`ZDataTwo/pigeonhole_three_minimal.lean`, the `k`-level oracle `ZDataTwo/mu2EscapeRealisationHKfresh.lean`
with its Čebotarev gate `ZDataTwo/escapePrimeKfresh.lean`, and the first gate of the crossed
two-place value identity, `ZDataTwo/swCountSiblingOdd.lean` (proved; the H9 lane has been pinged in
`SSGRoute/PING_ZDataTwo_swCountSiblingOdd_proved.md` so that its `swCrossedValueTwo_proved` can cite
it).  The tool that remains is the crossed value identity `Work.SSGRoute.H9.swCrossedValueTwo`
(one `sorry` left, the identity itself), consumed in this lane through
`ZDataTwo/crossedTwoPlaceTwo.lean` (a one-step transport), together with the final assembly through
`kummerCore_of_three_halves`.

**Also on disk (statement only, delegation pending):** `ZDataTwo/secondEscapeCompanions.lean`
(`Work.SSGRoute.ZDataTwo.secondEscapeCompanions`) — the *second* stage of the recursion, which
cancels the companions of the first escape prime (the mechanism that handles the earlier escape
primes in clause (4)); designed and reviewed, with the whole proof recipe in
`ZDataTwo/NOTE_session19_p2_recursion.md` §4.  Two findings of the reviews are recorded there: the
*freshness* clauses (`¬gesKConj K Q₁ Q₂` and `∀A ∈ S, ¬gesKConj K A Q₂`) are essential (without
them `b := a, Q₂ := Q₁` trivialises the statement), and the correction datum at a companion of `Q₁`
must be `y + χ_{b₁}` (the total class, not the correction alone).

**FIXED (same session): the oracle's `k`-level freshness.**  Two new proved modules of this lane
(both `#print axioms`-clean):
`Work.SSGRoute.ZDataTwo.escapePrimeKfresh` (`ZDataTwo/escapePrimeKfresh.lean`) — the escape prime of
the orthogonality with the strengthened exclusion clause `∀ A ∈ T, ¬ IsConjPlace k A Q` (a twin of
`GrunwaldEscapeCore.escape_prime_orthogonality`; the extra content is that the Čebotarev `Bad` set
already contains the `k`-primes below the `T'`-elements, and `Q` lies over the prime `P` with
`k`-prime `𝔭`, so `Q = ρ • A` with `A ∈ T` forces the `↥K`-prime of `A` to lie over `𝔭`) — and
`Work.SSGRoute.ZDataTwo.mu2EscapeRealisationHKfresh` (`ZDataTwo/mu2EscapeRealisationHKfresh.lean`),
the oracle with that clause in its conclusion.  `firstEscape_two` has been strengthened accordingly
(its conclusion now also contains `∀ A ∈ S, ¬ IsConjPlace k A Q`, which is what
`kummerCore_of_three_halves`'s `hPnotS` needs), and the stage-2 statement
`Work.SSGRoute.ZDataTwo.secondEscapeCompanions` (`ZDataTwo/secondEscapeCompanions.lean`, statement
only) carries both freshness levels.

**Open defect (for the record; NOTE §5):** the oracle
`ZDataTwo.mu2EscapeRealisationH` (hence `firstEscape_two`) excludes the escape prime only at the
*`G_K`-conjugacy* level, `∀ A ∈ T, ¬gesKConj K A Q`, while the recursion also needs the *`k`-level*
freshness `∀ A ∈ T, ¬IsConjPlace k A Q` (that is what `kummerCore_of_three_halves`'s
`hPnotS` and the `cs(S)`/companion interface use).  The strengthening is a finite Čebotarev
avoidance condition on the escape prime and should be obtainable by the same argument as
`escape_prime_orthogonality`; it is **not** a consequence of the oracle as currently stated, so the
recursion statements should be written with the `k`-level clause once the oracle is strengthened.

That is the complete state of this lane at the end of SESSION 19. -/

/-! ## SESSION 21: the prescription algebra of the `p = 2` verification — the exact obstruction

**Read `Submission/Work/SSGRoute/ZDataTwo/NOTE_p2_S4_prescription_algebra.md` first; it is the
session's main mathematical output.**  Summary:

**(1) The three verification identities, and what they force.**  At the companion blocks of the
three selected escape primes `Q_i, Q_j, Q_N`, the node's clause (4) is the three requirements
`(α),(β),(γ)` of the NOTE §1; with the *uncorrected* crossed two-place reciprocity
`z_s(Frob_{σQ_t}) = z_t(Frob_{σ^{-1}Q_s})` and the shoe box's `Ψ`-equality, they become six
equations in six *free* unknowns (the prescribed values), and **adding them forces
`V_σ = V_{σ^{-1}}` for every `σ ∈ G(K|k) ∖ {1}` and each of the three classes** (`V_τ` = the value
of the class at the `τ`-sibling of its own escape prime).  This is a statement about the classes,
not about the prescription rules: hence **no prescription rule and no selection can make the
*uncorrected* system hold**.  The "Kummer-symmetry" `V_σ = V_{σ^{-1}}` is not controlled by the
escape construction and not supplied by the shoe box (whose `Ψ` matches different classes at the
same `σ`).  A brute-force check over all `𝔽₂`-linear rules with the `G₂/G₃`-class dependence (the
paper's rule shape) gives **zero** solutions (`_readsw/prescheck.py`).

**(2) The diagnosis.**  The crossed identity's derivation uses the product formula over *all* places
and drops every term except those at `Q_s` and `σQ_t` "by agreement plus alternation" — and
alternation fails at `p = 2`: at a block where the two classes agree, the term is the self-pairing
`(a_B,a_B)_B = (a_B,-1)_B`, nontrivial at the `2`-adic and the archimedean places.  So the correct
identity carries the correction `E_{s,t,σ} = Σ_{B ∈ cs(S)} (z_s,σz_t)_B`, and the compatibility
condition replacing (1) is the scalar identity `(Compat′)` of the NOTE §3.  **This is the prime-2
correction**: it is why `H9.swCrossedValueTwo`'s finite-only form was refuted and why the involution
hypotheses `hinf_s`/`hinf_t` (total positivity) had to be added.

**(3) Consequences.**
* `Work.SSGRoute.NodeS37.crossedTwoPlaceNode` (the uncorrected `σ^{-1}`-form) cannot be proved
  without either the extra hypothesis `V_σ = V_{σ^{-1}}` or the correction terms; the lanes have
  been warned in `Submission/Work/SSGRoute/PING_nodeS37_crossedIdentity_correction.md`.
* The `p = 2` verification must therefore supply *arithmetic* (the vanishing of the corrections),
  not more combinatorics; the plan of `ACTION_mu2_three_halves_plan.md` §2 is not viable as written.

**(4) Proved this session.**
* `Work.SSGRoute.ZDataTwo.confinement_on_conj_blocks`
  (`Submission/Work/SSGRoute/ZDataTwo/confinement_on_conj_blocks.lean`): the `p = 2` confinement
  clause outside `cs(S) ∪ cs(H) ∪ cs(Q)` for a place set `T` that is `G_K`-covered by `S ∪ H` —
  the generalisation of `ZDataMup.clause_two_of_confinement` to a *list* `H` of earlier escape
  primes, needed by the recursion whatever the resolution of (1)/(2).
* `Work.SSGRoute.ZDataTwo.escapeStageOnHBlocks` (delegated; statement reviewed twice as correct):
  the abstract stage — the `p = 2` escape oracle applied to an arbitrary place set `T` covered by
  `S ∪ H`, with an *abstract* per-block correction `h` (additive, locally constant, `horth`,
  killing inertia and involutions, zero on the `S`-blocks), returning `b, Q` with the agreement
  `χ_b = y + h A` at the `T`-blocks, agreement with `y` on the `cs(S)`-blocks, the involution
  clause, the confinement outside `cs(S) ∪ cs(H) ∪ cs(Q)`, and the `G_K`- and `k`-level freshness
  of `Q` against `T` (hence against `S` and `H`).  This is `thirdEscapeCompanions` with the two
  hard-coded earlier classes replaced by an arbitrary place set and the prescriptions abstracted,
  and it is the *only* part of the recursion that is independent of the arithmetic question (1)/(2).
* The lane's existing recursion infrastructure (`firstEscape_two`, `secondEscapeCompanions`,
  `thirdEscapeCompanions`, `pigeonhole_three_minimal`, `mu2EscapeRealisationHKfresh`,
  `escapePrimeKfresh`) is unchanged and remains valid; what (1) shows is that the *prescription
  rules they implement* (running sums / own values) cannot by themselves deliver the final
  three-term verification.

**(5) Where the H9 lane's place-set bookkeeping already is.**  `Work.SSGRoute.H9.histPlacesK`,
`H9.swHistPlacesK_covers`, `H9.swHistPlacesK_isFinPlace` provide the analogues of `hTfin`,
`hTcovS`, `hTcov` for the recursion's place set `T_n = kleadReps K S ∪ ⋃_{j<n} kleadReps K {Q_j}`
(general `p`), so the instantiation of `escapeStageOnHBlocks` at `T_n` needs no new place bookkeeping.
-/

/-! ## SESSION 22: the antisymmetry identity, and the exact status of the "symmetry" obstruction

**Read `Submission/Work/SSGRoute/ZDataTwo/NOTE_p2_antisymmetry_identity.md`; it settles the question
left open by SESSION 21.**  Summary of the new mathematics.

**(1) `V_σ + V_{σ^{-1}}` is an *identity*, not a free condition.**  For any Kummer class
`z = χ_b` (`b ∈ Kˣ`) and `σ ∈ G(K|k)` the product formula for the pair `(z, σz)` gives

  `V_σ + V_{σ^{-1}} = ρ_{z,σ} := Σ_{P ∉ {P_z,σP_z}} (z, σz)_P`   **(AS)**,

with `V_τ = z(Frob_{τP_z})`.  The right-hand side is supported where **both** `z` and `σz` are
unramified — the places over `2`, and the archimedean ones (and, at `p = 2`, the `2`-adic terms are
genuinely there: over `ℚ₂`, `(3,3)_₂ = -1` for the unit `3`).  For a **totally positive** class — the
`hinf`/`hinv` hypothesis of the whole `p = 2` design, which the narrow modulus
(`mu2EscapeRealisationH`, `H9.Narrow*`) enforces — the archimedean part is `1`, so

  `V_σ + V_{σ^{-1}} = Σ_{𝔭 | 2} (z, σz)_𝔭`   **(AS₂)**.

So the SESSION 21 "Kummer-symmetry" `V_σ = V_{σ^{-1}}` is *equivalent* to the vanishing of a specific
`2`-adic self-pairing; it is neither a consequence of the construction nor a hypothesis one may add.

**(2) The crossed identity carries its correction, and with it the rule has enough freedom.**
Writing `A s t = z_s(Frob_{σP_t})`, `B s t = z_s(Frob_{σ^{-1}P_t})`, the crossed identity is
`A s t + B t s = ρ_{s,t,σ}` (**(X)**), and the six block requirements of the paper's condition (b),
read as equations in the six values *prescribed by the stage rule*, have the sum of all six as their
only linear dependency.  Hence they are **solvable iff** the compatibility identity

  `a + b = Σ_{s < t} (ρ_{s,t,σ} + ρ_{s,t,σ^{-1}})`   **(Compat′)**

holds — a condition on the *classes*, not on the rule.  The SESSION 21 obstruction (`a = b`) is the
specialisation `ρ ≡ 0` of `(Compat′)`.  **Both directions are now proved, sorry-free and
axiom-clean**:

* `Work.SSGRoute.ZDataTwo.compat_of_blocks`
  (`Submission/Work/SSGRoute/ZDataTwo/verification_forces_compat.lean`): the six block equations
  force `(Compat′)`; `...symm_of_blocks_of_corrections_vanish`: with `ρ = 0` they force `a = b`;
* `Work.SSGRoute.ZDataTwo.verification_rule_freedom`
  (`Submission/Work/SSGRoute/ZDataTwo/verification_rule_freedom.lean`): `(Compat′)` (with
  `ρ t t = a + b`) makes the six block equations *solvable*.

So **the six block equations of condition (b) are equivalent to `(Compat′)`.**

**(2′) `(Compat′)` is the `2`-adic self-pairing, and `(AS)` supplies it.**  By `(AS)` applied to
each selected class, `a + b = ρ_{t,t,σ}` for `t = i,j,N` and every `σ` — an *unconditional*
identity.  With total positivity killing the archimedean part, the verification therefore turns on

  `Σ_{𝔭 | 2} (z_t, σz_t)_𝔭 = 0`.

Because the oracle's `hTcov` is monotone in `T`, one may pass to `T ∪ {the classes of all places over
`2`}` and *prescribe* the `2`-adic blocks: then `(Compat′)` is a **finite, explicit condition on the
`2`-adic local data of `y`**, and if that data is chosen so that each escape class is a **local square
at every `𝔭 | 2`** then `ρ ≡ 0`, `(AS)` gives `a + b = 0` *automatically*, and the paper's own rule
(condition (4)) satisfies the six block equations.  The node's `hyT`/`hy0` already force local
triviality at every `2`-adic place **not** split in `K`, so the only places that can contribute are
the `K`-split ones — a finite set.  See `NOTE_p2_antisymmetry_identity.md` §6.

**(3) The remaining gap, restated.**  The recursion (stages `firstEscape_two`,
`secondEscapeCompanions`, `thirdEscapeCompanions`, all proved; abstract stage
`escapeStageOnHBlocks`, proved) prescribes the *running sums* at every block of every earlier escape
prime.  The only unprescribed blocks are the companions of the **youngest** escape prime `Q_N`, and
by `(X)` the requirement there is the identity of `NOTE_p2_antisymmetry_identity.md` §3:
`V^{(N)}_σ + Σ_{s<N} z_N(Frob_{σ^{-1}Q_s}) + Σ_{s<N} ρ_{s,N,σ} = 0` with the `z_N(Frob_{σ^{-1}Q_s})`
prescribed.  No choice of the rule (3)/(4) removes it (SESSION 21), and by (2) it is exactly
`(Compat′)` for the selected triple.

**(4) The two candidate routes for the next session.**
* **(a)** prove `(Compat′)` from the `2`-adic pairings: by `(AS₂)` its diagonal part is the
  self-pairing of the class at the places over `2`, which at those places is *prescribed* (the datum
  `g + h A`), so `(Compat′)` is a statement about the prescribed `2`-adic local data of the three
  selected classes — finite data, determinate;
* **(b)** the read-off-unit freedom (`NOTE_p2_S4_prescription_algebra.md` §7(a),
  `H9.Narrow{ReadOff,Correction}`): `γ ↦ γ u` changes `V^{(t)}_σ` by `χ_u(Frob_{σ𝔮_t})`, so the
  symmetry can be arranged iff the residue-character map on the units hits the `(AS₂)` vector.
-/

/-! ## The local image of an additive cochain unramified at a place is cyclic -/

section CyclicImage

/-- **The image of an additive cochain on the local group of a place at which it is unramified is
cyclic.**  For any coefficient module `E` (no dimensionality hypothesis), an additive, locally
constant `z` on `G_K` that vanishes on the inertia of a place `B` split in `K` has an image on
`decomp k B ⊓ G_K` contained in the `zmultiples` of a single value `z g`: the decomposition group
over `K` is generated, modulo the inertia and an open subgroup of `K`-inertia type, by one element
(`decomp_mod_inertia_cyclic_over_K`), and `z` vanishes on the generating subgroup.

This is the *cyclicity* clause of Schmidt–Wingberg's (b) in the case of a one-dimensional `E` (the
node below) for free; in the general case it is the local structure input for the corresponding
clause of `Work.SSGRoute.z_data_general`. -/
theorem exists_zmultiples_of_vanishes_inertia_of_isSplitIn (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (hsplit : SSGRoute.IsSplitIn k K B)
    (z : (Ω ≃ₐ[k] Ω) → E)
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z)
    (hinertia : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) :
    ∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        z δ ∈ AddSubgroup.zmultiples (z g) := by
  classical
  obtain ⟨U, hUopen, hUc⟩ := hzloc
  -- `z` vanishes on `U ⊓ G_K`
  have hzU : ∀ u ∈ U, u ∈ K.fixingSubgroup → z u = 0 := by
    intro u hu huK
    have h1 : z (1 * u) = z 1 := hUc 1 K.fixingSubgroup.one_mem u hu huK
    rw [one_mul, X_one hzadd] at h1
    exact h1
  -- the inertia of `B`, inside `G_K` because `B` splits in `K`
  set S : Set (Ω ≃ₐ[k] Ω) := {σ : Ω ≃ₐ[k] Ω | SSGRoute.IsInertia k B σ} with hSdef
  have hzS : ∀ x ∈ Subgroup.closure S, z x = 0 := by
    intro x hx
    exact (Subgroup.closure_induction (k := S)
      (p := fun x _ => x ∈ K.fixingSubgroup ∧ z x = 0)
      (fun y hy => ⟨hsplit hy.1, hinertia y (hsplit hy.1) hy⟩)
      ⟨K.fixingSubgroup.one_mem, X_one hzadd⟩
      (fun a b _ _ ha hb => ⟨K.fixingSubgroup.mul_mem ha.1 hb.1, by
        rw [hzadd a ha.1 b hb.1, ha.2, hb.2, zero_add]⟩)
      (fun a _ ha => ⟨K.fixingSubgroup.inv_mem ha.1, by rw [X_inv hzadd a ha.1, ha.2, neg_zero]⟩)
      hx).2
  -- the group on which `z` vanishes: generated by the local-constancy subgroup and the inertia
  set V : Subgroup (Ω ≃ₐ[k] Ω) := (U ⊓ K.fixingSubgroup) ⊔ Subgroup.closure S with hVdef
  have hVopen : IsOpen (V : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isOpen_mono le_sup_left (hUopen.inter (IntermediateField.fixingSubgroup_isOpen K))
  have hzV : ∀ v ∈ V, z v = 0 := by
    have hle : V ≤ kerOn K.fixingSubgroup z hzadd := by
      refine sup_le ?_ ?_
      · intro u hu
        obtain ⟨huU, huK⟩ := Subgroup.mem_inf.mp hu
        exact ⟨huK, hzU u huU huK⟩
      · intro x hx
        exact ⟨(Subgroup.closure_induction (k := S)
          (p := fun x _ => x ∈ K.fixingSubgroup ∧ z x = 0)
          (fun y hy => ⟨hsplit hy.1, hinertia y (hsplit hy.1) hy⟩)
          ⟨K.fixingSubgroup.one_mem, X_one hzadd⟩
          (fun a b _ _ ha hb => ⟨K.fixingSubgroup.mul_mem ha.1 hb.1, by
            rw [hzadd a ha.1 b hb.1, ha.2, hb.2, zero_add]⟩)
          (fun a _ ha => ⟨K.fixingSubgroup.inv_mem ha.1, by
            rw [X_inv hzadd a ha.1, ha.2, neg_zero]⟩)
          hx).1, hzS x hx⟩
    exact fun v hv => (hle hv).2
  -- the local structure: `decomp k B ⊓ G_K` modulo `V` is generated by one element
  obtain ⟨g, hg, hgcyc⟩ := decomp_mod_inertia_cyclic_over_K k Ω K V hVopen B hB
    (fun σ hσ hσK =>
      ⟨⟨Subgroup.mem_sup_right (Subgroup.subset_closure hσ), hσ.1⟩, hσK⟩)
  refine ⟨g, hg, fun δ hδ => ?_⟩
  obtain ⟨m, hm⟩ := hgcyc δ hδ
  have hmemV : δ⁻¹ * g ^ m ∈ V := hm.1.1
  have hmemK : δ⁻¹ * g ^ m ∈ K.fixingSubgroup := hm.2
  have hginvK : (g ^ m) ∈ K.fixingSubgroup := Subgroup.zpow_mem K.fixingSubgroup hg.2 m
  have hinvK : ((δ⁻¹ * g ^ m))⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hmemK
  have hdelta : δ = g ^ m * ((δ⁻¹ * g ^ m))⁻¹ := by group
  have hzdelta : z δ = m • z g := by
    rw [hdelta, hzadd _ hginvK _ hinvK, X_zpow hzadd g hg.2 m, hzV _ (V.inv_mem hmemV), add_zero]
  rw [hzdelta]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨m, rfl⟩

/-- **Frobenius detection.**  If `z` is additive and locally constant on `G_K` and unramified at a
place `B` split in `K`, then `z` vanishes on the whole local group `decomp k B ⊓ G_K` as soon as it
vanishes at the single "Frobenius" element `g` produced by the cyclicity lemma.  This is the form in
which the verification of Schmidt–Wingberg's (b) at the conjugates of a constructed prime is
consumed: there `z` is unramified at the conjugate (condition (1)) and the Hilbert-symbol chain
provides `z (Frob) = 0`. -/
theorem eq_zero_on_decomp_of_frobenius_eq_zero (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (hsplit : SSGRoute.IsSplitIn k K B)
    (z : (Ω ≃ₐ[k] Ω) → E)
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z)
    (hinertia : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) :
    ∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      z g = 0 → ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup, z δ = 0 := by
  obtain ⟨g, hg, hgcyc⟩ :=
    exists_zmultiples_of_vanishes_inertia_of_isSplitIn p k Ω K E B hB hsplit z hzadd hzloc hinertia
  refine ⟨g, hg, fun hg0 δ hδ => ?_⟩
  have h := hgcyc δ hδ
  rw [hg0] at h
  obtain ⟨c, hc⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  rw [smul_zero] at hc
  exact hc.symm

end CyclicImage

/-! ## Monotonicity of splitting in a tower, and the local group at a split place -/

section SplitTower

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {K Λ : IntermediateField k Ω}

/-- **Splitting is monotone in the extension.**  If a place splits completely in `Λ`, it splits
completely in every intermediate field `K ≤ Λ` (`Λ.fixingSubgroup ≤ K.fixingSubgroup`). -/
theorem isSplitIn_of_le_of_fixingSubgroup_le (hKΛ : K ≤ Λ) {B : ValuationSubring Ω}
    (h : SSGRoute.IsSplitIn k Λ B) : SSGRoute.IsSplitIn k K B :=
  le_trans h (IntermediateField.fixingSubgroup_le hKΛ)

/-- **At a place split in `Λ ⊇ K`, the local group over `K` is the full decomposition group.**
Hence conjunct (3) of the `z`-data at such a place is a condition on *all* of `decomp k B`, and the
cyclicity clause of (6) is a statement about the image of `z` on `decomp k B` itself. -/
theorem inf_fixingSubgroup_eq_of_isSplitIn (hKΛ : K ≤ Λ) {B : ValuationSubring Ω}
    (h : SSGRoute.IsSplitIn k Λ B) :
    SSGRoute.decomp k B ⊓ K.fixingSubgroup = SSGRoute.decomp k B :=
  inf_eq_left.mpr (le_trans h (IntermediateField.fixingSubgroup_le hKΛ))

end SplitTower

/-! ## Conjugacy of places -/

section IsConjPlaceBasics

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- `G_k`-conjugate places lie over the same prime of `k`.  (`IsConjPlace` is an equivalence
relation and is the same as "lies over the same prime of `k`" — `isConjPlace_refl/symm/trans` are
already in the workspace, and `isConjPlace_iff_comap_eq_of_isFinPlace` below is the identification
with the paper's language.) -/
theorem comap_eq_of_isConjPlace {A B : ValuationSubring Ω} (h : SSGRoute.IsConjPlace k A B) :
    A.comap (algebraMap k Ω) = B.comap (algebraMap k Ω) := by
  obtain ⟨σ, rfl⟩ := h
  exact (comap_algebraMap_smul A σ).symm

/-- **Two finite places of `Ω` are `G_k`-conjugate if and only if they lie over the same prime of
`k`.**  This identifies `SSGRoute.IsConjPlace` with "same prime of `k`", the form in which the paper
states its hypotheses. -/
theorem isConjPlace_iff_comap_eq_of_isFinPlace [NumberField k] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} (hA : SSGRoute.IsFinPlace k A) :
    SSGRoute.IsConjPlace k A B ↔ A.comap (algebraMap k Ω) = B.comap (algebraMap k Ω) := by
  have hSep : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  have hGal : IsGalois k Ω := IsSepClosure.isGalois
  exact ⟨fun h => comap_eq_of_isConjPlace h, fun h =>
    Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq (F := k) (E := Ω) A B h⟩

end IsConjPlaceBasics

section ConjKill

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω} {E : Type} [AddCommGroup E]

/-- **Conjugation invariance of the vanishing on a local group.**  If `z` is additive on `G_K`,
then translating a place by an element `τ ∈ G_K` does not change the vanishing of `z` on its local
group: `D_{τ • Q} = τ D_Q τ⁻¹` (`decomp_conj`) and `z` is constant on `G_K`-conjugacy classes
(`zadd_conj`). -/
theorem kills_decomp_of_smul {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    {Q Q' : ValuationSubring Ω} {τ : Ω ≃ₐ[k] Ω} (hτ : τ ∈ K.fixingSubgroup)
    (hτQ : τ • Q = Q')
    (h : ∀ u ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z u = 0) :
    ∀ u ∈ SSGRoute.decomp k Q' ⊓ K.fixingSubgroup, z u = 0 := by
  intro u hu
  obtain ⟨huD, huK⟩ := Subgroup.mem_inf.mp hu
  have hτinv : τ⁻¹ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hτ
  have hconj : z (τ⁻¹ * u * τ) = z u := by
    have h := zadd_conj hzadd hτinv huK
    rwa [inv_inv] at h
  have hmem : τ⁻¹ * u * τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup := by
    refine Subgroup.mem_inf.mpr
      ⟨?_, K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hτinv huK) hτ⟩
    rw [SSGRoute.decomp, MulAction.mem_stabilizer_iff] at huD ⊢
    calc (τ⁻¹ * u * τ) • Q = τ⁻¹ • (u • (τ • Q)) := by rw [mul_smul, mul_smul]
      _ = τ⁻¹ • Q' := by rw [hτQ, huD]
      _ = Q := by rw [← hτQ, inv_smul_smul]
  rw [← hconj]
  exact h _ hmem

end ConjKill

section TransitivityOverK

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {E : Type} [AddCommGroup E]

/-- **Transitivity of the `G_K`-action on the places of `Ω` over a prime of `K`.**  Two places of
`Ω` whose restrictions to `K` agree are `Gal(Ω/K)`-conjugate.  This is the infinite-level
transitivity of the Galois action (`Submission.NeukirchUchida.exists_smul_eq_of_comap_eq'`) at the
base field `↥K`, made available in terms of the subgroup `K.fixingSubgroup ≤ G_k`. -/
theorem exists_mem_fixingSubgroup_smul_eq_of_comap_eq (K : IntermediateField k Ω)
    [FiniteDimensional k K] {Q Q' : ValuationSubring Ω}
    (hQ : Q.comap (algebraMap ↥K Ω) ≠ ⊤)
    (h : Q.comap (algebraMap ↥K Ω) = Q'.comap (algebraMap ↥K Ω)) :
    ∃ τ ∈ K.fixingSubgroup, τ • Q = Q' := by
  haveI hNum : NumberField ↥K := NumberField.of_module_finite k ↥K
  haveI hAlg : IsAlgClosure ↥K Ω :=
    IsAlgClosure.mk (inferInstance : IsAlgClosure k Ω).isAlgClosed inferInstance
  haveI hSep : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  obtain ⟨σ, hσ⟩ := Submission.NeukirchUchida.exists_smul_eq_of_comap_eq' (K₁ := ↥K) (K₁' := Ω)
    (A := Q) (B := Q') hQ h
  refine ⟨↑((IntermediateField.fixingSubgroupEquiv K).symm σ), ?_, ?_⟩
  · exact ((IntermediateField.fixingSubgroupEquiv K).symm σ).2
  · have hfun : ⇑(σ : Ω ≃ₐ[↥K] Ω) =
        ⇑(↑((IntermediateField.fixingSubgroupEquiv K).symm σ) : Ω ≃ₐ[k] Ω) := by
      have h1 : (((IntermediateField.fixingSubgroupEquiv K)
          ((IntermediateField.fixingSubgroupEquiv K).symm σ) : Ω ≃ₐ[↥K] Ω) : Ω → Ω) =
          ⇑(↑((IntermediateField.fixingSubgroupEquiv K).symm σ) : Ω ≃ₐ[k] Ω) := rfl
      rwa [MulEquiv.apply_symm_apply] at h1
    have hsmul : (↑((IntermediateField.fixingSubgroupEquiv K).symm σ) : Ω ≃ₐ[k] Ω) • Q =
        σ • Q := by
      apply ValuationSubring.ext
      intro x
      rw [ValuationSubring.mem_smul_pointwise_iff_exists,
        ValuationSubring.mem_smul_pointwise_iff_exists]
      constructor
      · rintro ⟨s, hs, hx⟩
        exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def]; exact congrFun hfun s⟩
      · rintro ⟨s, hs, hx⟩
        exact ⟨s, hs, by
          rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def]
          exact (congrFun hfun s).symm⟩
    rw [hsmul, hσ]

/-- **Condition (b) is a condition at one place per prime of `K`.**  For an additive cochain on
`G_K`, the vanishing on `decomp k Q ⊓ G_K` depends only on the prime of `K` below `Q`.  Hence
Schmidt--Wingberg's "`z_{σP} = 0` for `σ ∈ G(K|k) ∖ {1}`" (a condition on the *primes* of `K`)
implies the target's conjunct (6)(b) (a condition on the *places* of `Ω`). -/
theorem kills_decomp_of_comap_eq (K : IntermediateField k Ω) [FiniteDimensional k K]
    {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    {Q Q' : ValuationSubring Ω} (hQ : Q.comap (algebraMap ↥K Ω) ≠ ⊤)
    (hcomap : Q.comap (algebraMap ↥K Ω) = Q'.comap (algebraMap ↥K Ω))
    (h : ∀ u ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z u = 0) :
    ∀ u ∈ SSGRoute.decomp k Q' ⊓ K.fixingSubgroup, z u = 0 := by
  obtain ⟨τ, hτ, hτQ⟩ := exists_mem_fixingSubgroup_smul_eq_of_comap_eq K hQ hcomap
  exact kills_decomp_of_smul hzadd hτ hτQ h

end TransitivityOverK

/-! ## Factoring an additive cochain through a finite quotient -/

section LevelVanishing

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω} {E : Type} [AddCommGroup E]

/-- **`z` only depends on the class modulo a subgroup on which it vanishes.**  If an additive
cochain on `G_K` vanishes on a subgroup `U`, its values are constant on the cosets of `U`: this is
the step which turns "locally constant `z`" into "`z` is pulled back from a finite quotient
`Gal(M/K)`" (take `U = M.fixingSubgroup` for a finite normal `M/k` containing `K`), and it is what
makes it legitimate to speak of the *Frobenius value* `z (Frob_P)` of `z`. -/
theorem z_eq_of_mul_inv_mem {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    {U : Subgroup (Ω ≃ₐ[k] Ω)} (hU : ∀ u ∈ U, u ∈ K.fixingSubgroup → z u = 0)
    {σ σ' : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) (hσ' : σ' ∈ K.fixingSubgroup)
    (h : σ * σ'⁻¹ ∈ U) : z σ = z σ' := by
  have hmem : σ * σ'⁻¹ ∈ K.fixingSubgroup :=
    K.fixingSubgroup.mul_mem hσ (K.fixingSubgroup.inv_mem hσ')
  have h2 : (σ * σ'⁻¹) * σ' = σ := by rw [mul_assoc, inv_mul_cancel, mul_one]
  have h1 : z σ = z (σ * σ'⁻¹) + z σ' := by
    conv_lhs => rw [← h2]
    exact hzadd (σ * σ'⁻¹) hmem σ' hσ'
  rw [h1, hU _ h hmem, zero_add]

/-- **A value of `z` at a power lies in the `zmultiples` of the value at the base point.**  The
ℤ-power form of additivity (`X_zpow`), stated for the `zmultiples`-vocabulary of the sharpened
condition (b). -/
theorem z_zpow_mem_zmultiples {z : (Ω ≃ₐ[k] Ω) → E}
    (hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    {g : Ω ≃ₐ[k] Ω} (hg : g ∈ K.fixingSubgroup) (m : ℤ) :
    z (g ^ m) ∈ AddSubgroup.zmultiples (z g) :=
  AddSubgroup.mem_zmultiples_iff.mpr ⟨m, (X_zpow hzadd g hg m).symm⟩

end LevelVanishing

/-! ## Places over a prime of `K` -/

section PrimesOverK

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- The prime of `K` below a place of `Ω` is invariant under `G_K`. -/
theorem comap_smul_eq_of_mem_fixingSubgroup (K : IntermediateField k Ω) {τ : Ω ≃ₐ[k] Ω}
    (hτ : τ ∈ K.fixingSubgroup) (Q : ValuationSubring Ω) :
    (τ • Q).comap (algebraMap ↥K Ω) = Q.comap (algebraMap ↥K Ω) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have hfix : (τ⁻¹ : Ω ≃ₐ[k] Ω) (algebraMap ↥K Ω x) = algebraMap ↥K Ω x :=
    (IntermediateField.mem_fixingSubgroup_iff K τ⁻¹).mp (K.fixingSubgroup.inv_mem hτ)
      _ x.2
  rw [hfix]

/-- A finite place of `Ω` over `k` is a finite place over every intermediate field. -/
theorem comap_algebraMap_ne_top_of_isFinPlace [NumberField k] (K : IntermediateField k Ω)
    {B : ValuationSubring Ω} (hB : SSGRoute.IsFinPlace k B) :
    B.comap (algebraMap ↥K Ω) ≠ ⊤ := by
  intro htop
  refine hB (le_antisymm le_top ?_)
  intro x _
  rw [ValuationSubring.mem_comap]
  have hx : algebraMap ↥K Ω (algebraMap k ↥K x) ∈ B := by
    have : algebraMap k ↥K x ∈ B.comap (algebraMap ↥K Ω) := by rw [htop]; exact ValuationSubring.mem_top _
    rwa [ValuationSubring.mem_comap] at this
  rwa [IsScalarTower.algebraMap_apply k ↥K Ω]

/-- **Two places of `Ω` over the same prime of `K` are `G_K`-conjugate** (and conversely).  This is
the infinite-level transitivity of the Galois action at the base field `↥K`, in the vocabulary of
`G_K = K.fixingSubgroup`. -/
theorem exists_mem_fixingSubgroup_smul_eq_iff_comap_eq [NumberField k] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] {B Q : ValuationSubring Ω}
    (hB : SSGRoute.IsFinPlace k B) :
    (∃ τ ∈ K.fixingSubgroup, τ • B = Q) ↔
      Q.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact comap_smul_eq_of_mem_fixingSubgroup K hτ B
  · intro h
    exact exists_mem_fixingSubgroup_smul_eq_of_comap_eq K
      (comap_algebraMap_ne_top_of_isFinPlace K hB) h.symm

/-- **The bridge between conjunct (6)(b) and Schmidt–Wingberg's `z_{σP} = 0`.**  For a place `Q`
that is not a `G_K`-conjugate of the finite place `B`, the two lie over *different* primes of `K`;
hence (6)(b) is a condition at the primes of `K` over a prime of `k`, and by
`kills_decomp_of_comap_eq` it has to be verified at one place of `Ω` per prime of `K`. -/
theorem comap_ne_of_not_exists_smul [NumberField k] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] {B Q : ValuationSubring Ω}
    (hB : SSGRoute.IsFinPlace k B) (h : ¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) :
    Q.comap (algebraMap ↥K Ω) ≠ B.comap (algebraMap ↥K Ω) := by
  intro hc
  exact h ((exists_mem_fixingSubgroup_smul_eq_iff_comap_eq K hB).mpr hc)

end PrimesOverK


section TwoCases

open scoped Pointwise

/-- **The node in the unramified case.**  If `y` is unramified at *every* finite place outside
`cs(S)` --- the hypothesis isolated as `hunram` --- then `z := y` (extended by `0` off `G_K`)
satisfies the whole `z`-data; in particular the sharpened condition (b) is vacuous, since `z` is
not ramified at any good place. -/
theorem shafarevich_z_data_two_of_unramified (p : ℕ) [Fact p.Prime] (hp2 : p = 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (h1 : Module.finrank (ZMod p) E ≤ 1)
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
    (hunram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
            z δ ∈ AddSubgroup.zmultiples (z g)) ∧
        (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)) := by
  subst hp2
  classical
  let z : (Ω ≃ₐ[k] Ω) → E := fun σ => if σ ∈ K.fixingSubgroup then y σ else 0
  have htriv : ∀ g : K ≃ₐ[k] K, ∀ e : E, g • e = e :=
    smul_eq_self_of_finrank_le_one_two k Ω K E h1
  have hzy : ∀ σ, σ ∈ K.fixingSubgroup → z σ = y σ := by
    intro σ hσ
    show (if σ ∈ K.fixingSubgroup then y σ else 0) = y σ
    rw [if_pos hσ]
  have hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h := by
    intro g hg h hh
    rw [hzy (g * h) (K.fixingSubgroup.mul_mem hg hh), hzy g hg, hzy h hh, hy g hg h hh]
  have hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z := by
    obtain ⟨U, hUopen, hUc⟩ := hyc
    refine ⟨U, hUopen, ?_⟩
    intro g hg u hu huH
    rw [hzy (g * u) (K.fixingSubgroup.mul_mem hg huH), hzy g hg]
    exact hUc g hg u hu huH
  have hzkill : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0 := by
    intro B hB hconj σ hσK hσI
    rw [hzy σ hσK]
    exact hunram B hB hconj σ hσK hσI
  refine ⟨z, ?_, hzloc, ?_, ?_, ?_, ?_⟩
  · intro g hg h hh
    rw [hzadd g hg h hh, htriv (SSGRoute.res k K g) (z h)]
  · intro B hB hconj σ hσK _
    exact hzy σ hσK
  · intro c hc hc2
    rw [hzy c hc]
    exact hyinf c hc hc2
  · intro B hB hconj hnsplit σ hσK hσI
    exact hzkill B hB hconj σ hσK hσI
  · intro B hB hconj hsplit htrig
    obtain ⟨σ, hσI, hσK, hσne⟩ := htrig
    exact absurd (hzkill B hB hconj σ hσK hσI) hσne



/-- **The node in the case in which `y` already has isolated ramification.**  If at every good
place `B` at which `y` is ramified the cochain `y` kills the local group of every `k`-conjugate of
`B` that is not a `G_K`-conjugate of `B`, then `z := y` (extended by `0` off `G_K`) witnesses the
whole `z`-data: conjuncts (1)--(5) hold by `z_data_two_agreement_conjuncts` (the action of `G_K`
on `E` is trivial, `smul_eq_self_of_finrank_le_one_two`), the cyclicity half of (6) is automatic
(`z_data_two_cyclic_conjunct`), and the vanishing half of (6) is the hypothesis. -/
theorem shafarevich_z_data_two_of_isolated (p : ℕ) [Fact p.Prime] (hp2 : p = 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (h1 : Module.finrank (ZMod p) E ≤ 1)
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
    (hiso : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
      (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ y σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
        ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, y τ = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
            z δ ∈ AddSubgroup.zmultiples (z g)) ∧
        (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)) := by
  subst hp2
  classical
  let z : (Ω ≃ₐ[k] Ω) → E := fun σ => if σ ∈ K.fixingSubgroup then y σ else 0
  have htriv : ∀ g : K ≃ₐ[k] K, ∀ e : E, g • e = e :=
    smul_eq_self_of_finrank_le_one_two k Ω K E h1
  have hzy : ∀ σ, σ ∈ K.fixingSubgroup → z σ = y σ := by
    intro σ hσ
    show (if σ ∈ K.fixingSubgroup then y σ else 0) = y σ
    rw [if_pos hσ]
  have hzadd : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h := by
    intro g hg h hh
    rw [hzy (g * h) (K.fixingSubgroup.mul_mem hg hh), hzy g hg, hzy h hh, hy g hg h hh]
  have hzloc : SSGRoute.IsLocConstOn K.fixingSubgroup z := by
    obtain ⟨U, hUopen, hUc⟩ := hyc
    refine ⟨U, hUopen, ?_⟩
    intro g hg u hu huH
    rw [hzy (g * u) (K.fixingSubgroup.mul_mem hg huH), hzy g hg]
    exact hUc g hg u hu huH
  refine ⟨z, ?_, hzloc, ?_, ?_, ?_, ?_⟩
  · intro g hg h hh
    rw [hzadd g hg h hh, htriv (SSGRoute.res k K g) (z h)]
  · intro B hB hconj σ hσK _
    exact hzy σ hσK
  · intro c hc hc2
    rw [hzy c hc]
    exact hyinf c hc hc2
  · intro B hB hconj hnsplit σ hσK hσI
    rw [hzy σ hσK]
    exact hyS B hB hconj hnsplit σ hσK hσI
  · intro B hB hconj hsplit htrig
    obtain ⟨σ, hσI, hσK, hσne⟩ := htrig
    have htrigy : ∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ y σ ≠ 0 := by
      refine ⟨σ, hσI, hσK, fun h0 => hσne (by rw [hzy σ hσK]; exact h0)⟩
    refine ⟨⟨σ, Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩,
      fun δ _ => zmultiples_eq_top_of_finrank_le_one h1 hσne (z δ)⟩, ?_⟩
    intro Q hQ hne τ hτ
    rw [hzy τ (Subgroup.mem_inf.mp hτ).2]
    exact hiso B hB hconj hsplit htrigy Q hQ hne τ hτ

end TwoCases

/-! ## Reduction of the node to the Kummer core

The sheaf of definitions (`Work.SSGRoute.kummerCochar`, `Work.SSGRoute.nodeKummerCochar`, …) now
lives in `Submission.Work.SSGRoute.ZDataTwo.KummerCocharBase`.  Here we record the reduction of the
node to its *arithmetic core*: the statement that for the data `y` there is an element `b ∈ Kˣ`
whose Kummer cochain `z_b` already satisfies the four arithmetic conjuncts (agreement with `y` on
the decomposition groups of `cs(S)`, vanishing on the involutions, unramifiedness outside `cs(S)`
at the places not split in `Λ`, and the sharpened condition at the good split places).  Once `b` is
produced, the node itself is immediate: it is witnessed by `z := z_b`.

The core `Work.SSGRoute.shafarevich_z_data_two_kummerCore` is the `p = 2` case of Schmidt–Wingberg
§4 (the construction of the class `z` by the Tate–Poitou realisation, Chebotarev's density theorem,
the pigeonhole principle and the Hilbert-symbol product formula); it is the only remaining
arithmetic obligation.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

section KummerCore

open _root_.SSGRoute

/-- **The even-valuation refinement of the inertia dictionary.**  This is the arithmetic form of
conjunct (5) of the node: at a place `A` with `A ∤ 2` (which is automatic for every place outside
`cs(S)`, since `hSram` puts all the places over `2` and all the places ramified in `Λ` into `S`),
the Kummer cochain of `a ∈ Kˣ` kills the inertia of `A` as soon as the `A`-valuation of `a` is the
square of the `A`-valuation of some element `d ∈ Kˣ` — i.e. as soon as `K(√a)/K` is unramified at
`A` (the classical criterion "`v_A(a)` even").  The point of the lemma is that the relevant
arithmetic condition on `b` in the Kummer core is only the *parity* of `v_𝔭(b)` outside `cs(S)`,
not local squarity: so `b` may be constructed with ideal support in `S ∪ cs(Λ|k)`. -/
theorem kummerCochar_eq_zero_of_isInertia_of_even_valuation
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (h2 : ¬ A.valuation (2 : Ω) < 1)
    (a d : (↥K)ˣ)
    (hdv : A.valuation (algebraMap ↥K Ω (a : ↥K)) =
      A.valuation (algebraMap ↥K Ω (d : ↥K)) ^ 2)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup)
    (hσI : SSGRoute.IsInertia (k := ↥K) A
      ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩)) :
    nodeKummerCochar K ζ hζK hζ a σ = 0 := by
  classical
  set u : (↥K)ˣ := a * (d ^ 2)⁻¹ with hu_def
  -- `a = d^2 * u` with `u` a unit at `A`
  have hfac : a = d ^ 2 * u := by
    rw [hu_def]
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  have huval : A.valuation (algebraMap ↥K Ω (u : ↥K)) = 1 := by
    have hmul : (u : ↥K) * (d : ↥K) ^ 2 = (a : ↥K) := by
      have h := congrArg (fun x : (↥K)ˣ => (x : ↥K)) hfac
      simp only [Units.val_mul, Units.val_pow_eq_pow_val] at h
      rw [mul_comm ((d : ↥K) ^ 2) (u : ↥K)] at h
      exact h.symm
    have hmap := congrArg (fun x : ↥K => A.valuation (algebraMap ↥K Ω x)) hmul
    rw [map_mul, map_pow] at hmap
    rw [Valuation.map_mul, Valuation.map_pow] at hmap
    rw [hdv] at hmap
    have hd0 : algebraMap ↥K Ω (d : ↥K) ≠ 0 := by
      have h := (algebraMap ↥K Ω).injective.ne (Units.ne_zero d)
      simpa using h
    have hne : A.valuation (algebraMap ↥K Ω (d : ↥K)) ^ 2 ≠ 0 :=
      pow_ne_zero 2 ((Valuation.ne_zero_iff A.valuation).mpr hd0)
    exact mul_right_cancel₀ hne (hmap.trans (one_mul _).symm)
  have hzero := kummerCochar_eq_zero_of_isInertia_of_sq_mul_unit K ⟨ζ, hζK⟩
    (isPrimitiveRoot_subtype_of_mem hζK hζ) A hA h2 d u huval σ hσ hσI
  rw [hfac]
  exact hzero

/-! ### The quotient dictionary: conjunct (3) of the node in arithmetic form

The node's third conjunct says `z σ = y σ` for `σ ∈ decomp k B ⊓ G_K` and `B` in `cs(S)`.  For the
Kummer candidate `z = z_b` (with `y = z_h`, the Kummer correspondence of
`exists_kummerCochar_of_node_data`) this is a condition on the quotient `b · h⁻¹`: it holds at a
place `A` exactly when `b h⁻¹` is a local `2`-power at the prime of `K` below `A`.  These three
elementary facts (`z_{a⁻¹} = z_a`, `z_{a b⁻¹} = z_a + z_b`, and the dictionary in agreement form)
are what turns the Kummer core into a *purely arithmetic* existence statement about `b`. -/

/-- The Kummer cochain of an inverse is the Kummer cochain: `a⁻¹ = a · (a⁻¹)²` and squares are
invisible (`kummerCochar_sq`), in characteristic `2`. -/
lemma kummerCochar_inv (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (a : (↥K)ˣ) :
    kummerCochar K ζ hζ a⁻¹ = kummerCochar K ζ hζ a := by
  have h : a⁻¹ = a * (a⁻¹) ^ 2 := by group
  rw [h, kummerCochar_mul, kummerCochar_sq, add_zero]

/-- The Kummer cochain of a quotient is the sum of the Kummer cochains (the coefficient module is
of exponent `2`, so a quotient and a product are the same thing). -/
lemma kummerCochar_div (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (a b : (↥K)ˣ) :
    kummerCochar K ζ hζ (a * b⁻¹) = kummerCochar K ζ hζ a + kummerCochar K ζ hζ b := by
  rw [kummerCochar_mul, kummerCochar_inv]

/-- **The local Kummer dictionary in "agreement" form.**  For a finite place `A` of `Ω` with prime
`𝔭` of `K` below it, the Kummer cochains of `b` and `h` agree on the local group
`decomp k A ⊓ K.fixingSubgroup` if and only if the quotient `b · h⁻¹` is a local `2`-power at `𝔭`.

This is the arithmetic form of the node's third conjunct: the condition on the constructed class is
a *local squarity* condition on the single element `b h⁻¹` at the finitely many primes of `K` under
`cs(S)`. -/
theorem kummerCochar_agree_iff_localPowClass (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ 2) (b h : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) :
    (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        kummerCochar K ζ hζ b σ = kummerCochar K ζ hζ h σ) ↔
      NK.UchidaKummer.localPowClass ↥K 2 𝔭 (b * h⁻¹) = 1 := by
  have hdict := kummerCochar_eq_zero_iff_localPowClass K ζ hζ (b * h⁻¹) A hA 𝔭 h𝔭
  constructor
  · intro H
    rw [← hdict]
    intro σ hσ
    have h1 := H σ hσ
    rw [kummerCochar_div k Ω K ζ hζ b h]
    simp only [Pi.add_apply]
    rw [h1, zmodTwo_add_self]
  · intro H σ hσ
    rw [← hdict] at H
    have h0 : kummerCochar K ζ hζ (b * h⁻¹) σ = 0 := H σ hσ
    rw [kummerCochar_div k Ω K ζ hζ b h] at h0
    simp only [Pi.add_apply] at h0
    calc kummerCochar K ζ hζ b σ
        = kummerCochar K ζ hζ b σ + 0 := (add_zero _).symm
      _ = kummerCochar K ζ hζ b σ +
            (kummerCochar K ζ hζ h σ + kummerCochar K ζ hζ h σ) := by
            rw [zmodTwo_add_self, add_zero]
      _ = (kummerCochar K ζ hζ b σ + kummerCochar K ζ hζ h σ) +
            kummerCochar K ζ hζ h σ := by abel
      _ = 0 + kummerCochar K ζ hζ h σ := by rw [h0]
      _ = kummerCochar K ζ hζ h σ := zero_add _


/-- **The Kummer core in the unramified case.**  If `y` vanishes on the inertia of *every* finite
place outside `cs(S)` (a hypothesis stronger than `hyS`: it also forbids ramification at the places
outside `cs(S)` that *are* split in `Λ`), then the Kummer cochain of the element `h` given by the
Kummer correspondence already witnesses the core: it agrees with `y` on all of `G_K`, is therefore
unramified outside `cs(S)`, kills the involutions (`hyinf`), and the sharpened condition of the core
is vacuous.  This is the first case of the proof of the core, complementary to the case in which
`y` is ramified at a good split place (Schmidt–Wingberg §4, where the ramification has to be moved
onto new primes). -/
theorem shafarevich_z_data_two_kummerCore_of_unramified (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
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
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hyunr : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0) :
    ∃ b : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
          nodeKummerCochar K ζ hζK hζ b σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → nodeKummerCochar K ζ hζK hζ b c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          nodeKummerCochar K ζ hζK hζ b σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          nodeKummerCochar K ζ hζK hζ b σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, nodeKummerCochar K ζ hζK hζ b τ = 0) := by
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 := isPrimitiveRoot_subtype_of_mem hζK hζ
  obtain ⟨b, hb⟩ := exists_kummerCochar_of_node_data K ⟨ζ, hζK⟩ hζ' y hy hyc
  have hbσ : ∀ σ (hσ : σ ∈ K.fixingSubgroup), nodeKummerCochar K ζ hζK hζ b σ = y σ := by
    intro σ hσ
    have h1 : nodeKummerCochar K ζ hζK hζ b σ =
        kummerCochar K ⟨ζ, hζK⟩ hζ' b σ := rfl
    rw [h1, hb σ hσ]
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · intro B hB hc σ hσK hσd
    exact hbσ σ hσK
  · intro c hc hc2
    rw [hbσ c hc]
    exact hyinf c hc hc2
  · intro B hB hc hns σ hσK hσI
    rw [hbσ σ hσK]
    exact hyS B hB hc hns σ hσK hσI
  · intro B hB hc hsplit htrig
    obtain ⟨σ, hσI, hσK, hσne⟩ := htrig
    rw [hbσ σ hσK] at hσne
    exact absurd (hyunr B hB hc σ hσK hσI) hσne

/-- **The arithmetic core of Schmidt–Wingberg §4 in the case `p = 2`.**  For any data `y` of the
node (additive and locally constant on `G_K`, unramified at the places outside `cs(S)` that are not
split in `Λ`, vanishing on the involutions, and locally trivial at the places of `cs(S)` outside
the primes over `2` and the ramified ones) there is `b ∈ Kˣ` whose Kummer cochain satisfies the
node's four arithmetic conjuncts. -/
theorem shafarevich_z_data_two_kummerCore (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
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
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ b : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
          nodeKummerCochar K ζ hζK hζ b σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → nodeKummerCochar K ζ hζK hζ b c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          nodeKummerCochar K ζ hζK hζ b σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          nodeKummerCochar K ζ hζK hζ b σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, nodeKummerCochar K ζ hζK hζ b τ = 0) := by
  -- the `p = 2` route is proved in `ZDataTwo.TwoRec.kummerCoreProved`; the single missing step is
  -- the removal of the (unused) import edge `ZSplit/FrobeniusValue → this file`, which today
  -- makes every `p = 2` module unimportable from here — see
  -- `ZDataTwo/PING_node_blocked_by_the_FrobeniusValue_import_edge.md`
  sorry

/-- **The node from the Kummer core.**  If the arithmetic core holds for every admissible datum
`y'` with values in `ZMod 2`, then the node holds (for an arbitrary one-dimensional coefficient
module `E`, which is trivial or isomorphic to `ZMod 2`). -/
theorem shafarevich_z_data_two_of_kummerCore (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (h1 : Module.finrank (ZMod 2) E ≤ 1)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
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
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hcore : ∀ (y' : (Ω ≃ₐ[k] Ω) → ZMod 2),
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y' (g * h) = y' g + y' h) →
      SSGRoute.IsLocConstOn K.fixingSubgroup y' →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y' σ = 0) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y' σ = 0) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y' σ = 0) →
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y' c = 0) →
      ∃ b : (↥K)ˣ,
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
          ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
            nodeKummerCochar K ζ hζK hζ b σ = y' σ) ∧
        (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → nodeKummerCochar K ζ hζK hζ b c = 0) ∧
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
            nodeKummerCochar K ζ hζK hζ b σ = 0) ∧
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
          (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
            nodeKummerCochar K ζ hζK hζ b σ ≠ 0) →
          ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
            (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
            ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, nodeKummerCochar K ζ hζK hζ b τ = 0)) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
            z δ ∈ AddSubgroup.zmultiples (z g)) ∧
        (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)) := by
  classical
  have hres : ∀ g ∈ K.fixingSubgroup, SSGRoute.res k K g = 1 := by
    intro g hg
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
    exact hg
  by_cases htriv : Subsingleton E
  · refine ⟨fun _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg h hh
      rw [zero_add, hres g hg, one_smul]
    · exact ⟨⊤, isOpen_univ, fun g hg u hu huH => rfl⟩
    · intro B hB hc σ hσK hσd
      exact Subsingleton.elim _ _
    · intro c hc hc2
      exact Subsingleton.elim _ _
    · intro B hB hc hns σ hσK hσI
      exact Subsingleton.elim _ _
    · intro B hB hc hsplit htrig
      obtain ⟨σ, hσI, hσK, hσne⟩ := htrig
      exact absurd rfl hσne
  · haveI : Nontrivial E := not_subsingleton_iff_nontrivial.mp htriv
    have hfr : Module.finrank (ZMod 2) E = 1 := by
      have hpos : 0 < Module.finrank (ZMod 2) E := Module.finrank_pos_iff.mpr ‹Nontrivial E›
      omega
    let φ : E ≃ₗ[ZMod 2] ZMod 2 :=
      LinearEquiv.ofFinrankEq E (ZMod 2) (by rw [hfr, Module.finrank_self])
    let y' : (Ω ≃ₐ[k] Ω) → ZMod 2 := fun σ => φ (y σ)
    have hy' : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y' (g * h) = y' g + y' h := by
      intro g hg h hh
      show φ (y (g * h)) = φ (y g) + φ (y h)
      rw [hy g hg h hh, map_add]
    have hyc' : SSGRoute.IsLocConstOn K.fixingSubgroup y' := by
      obtain ⟨U, hUo, hU⟩ := hyc
      exact ⟨U, hUo, fun g hg u hu huH => by
        show φ (y (g * u)) = φ (y g)
        rw [hU g hg u hu huH]⟩
    have hyS' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y' σ = 0 := by
      intro B hB hc hns σ hσK hσI
      show φ (y σ) = 0
      rw [hyS B hB hc hns σ hσK hσI, map_zero]
    have hyT' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y' σ = 0 := by
      intro B hB hc σ hσK hσI
      show φ (y σ) = 0
      rw [hyT B hB hc σ hσK hσI, map_zero]
    have hy0' : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y' σ = 0 := by
      intro B hB hc hsp σ hσK hσd
      show φ (y σ) = 0
      rw [hy0 B hB hc hsp σ hσK hσd, map_zero]
    have hyinf' : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y' c = 0 := by
      intro c hc hc2
      show φ (y c) = 0
      rw [hyinf c hc hc2, map_zero]
    obtain ⟨b, hagree, hinv, hunr, hiso⟩ := hcore y' hy' hyc' hyS' hyT' hy0' hyinf'
    have hzbadd := nodeKummerCochar_add K ζ hζK hζ b
    have hzbloc := nodeKummerCochar_locConst K ζ hζK hζ b
    refine ⟨fun σ => φ.symm (nodeKummerCochar K ζ hζK hζ b σ), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg h hh
      show φ.symm (nodeKummerCochar K ζ hζK hζ b (g * h)) =
        φ.symm (nodeKummerCochar K ζ hζK hζ b g) +
          (SSGRoute.res k K g) • φ.symm (nodeKummerCochar K ζ hζK hζ b h)
      rw [hzbadd g hg h hh, map_add, hres g hg, one_smul]
    · exact ⟨_, hzbloc.choose_spec.1, fun g hg u hu huH => by
        show φ.symm (nodeKummerCochar K ζ hζK hζ b (g * u)) =
          φ.symm (nodeKummerCochar K ζ hζK hζ b g)
        rw [hzbloc.choose_spec.2 g hg u hu huH]⟩
    · intro B hB hc σ hσK hσd
      show φ.symm (nodeKummerCochar K ζ hζK hζ b σ) = y σ
      rw [hagree B hB hc σ hσK hσd, LinearEquiv.symm_apply_apply]
    · intro c hc hc2
      show φ.symm (nodeKummerCochar K ζ hζK hζ b c) = 0
      rw [hinv c hc hc2, map_zero]
    · intro B hB hc hns σ hσK hσI
      show φ.symm (nodeKummerCochar K ζ hζK hζ b σ) = 0
      rw [hunr B hB hc hns σ hσK hσI, map_zero]
    · intro B hB hc hsplit htrig
      obtain ⟨σ, hσI, hσK, hσne⟩ := htrig
      have hzbne : nodeKummerCochar K ζ hζK hζ b σ ≠ 0 := by
        intro h0
        refine hσne ?_
        show φ.symm (nodeKummerCochar K ζ hζK hζ b σ) = 0
        rw [h0, map_zero]
      have htrig' : ∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          nodeKummerCochar K ζ hζK hζ b σ ≠ 0 := ⟨σ, hσI, hσK, hzbne⟩
      refine ⟨⟨σ, Subgroup.mem_inf.mpr ⟨hσI.1, hσK⟩, fun δ hδ => ?_⟩, ?_⟩
      · exact zmultiples_eq_top_of_finrank_le_one h1 hσne (φ.symm (nodeKummerCochar K ζ hζK hζ b δ))
      · intro Q hQ hne τ hτ
        show φ.symm (nodeKummerCochar K ζ hζK hζ b τ) = 0
        rw [hiso B hB hc hsplit htrig' Q hQ hne τ hτ, map_zero]

end KummerCore


theorem shafarevich_z_data_two (p : ℕ) [Fact p.Prime] (hp2 : p = 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (h1 : Module.finrank (ZMod p) E ≤ 1)
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
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
            z δ ∈ AddSubgroup.zmultiples (z g)) ∧
        (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)) := by
  subst hp2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  exact shafarevich_z_data_two_of_kummerCore k Ω K Λ hKΛ ζ hζ hζK E h1 S hSfin hSdisj hSram
    y hy hyc hyS hyT hy0 hyinf
    (fun y' hy' hyc' hyS' hyT' hy0' hyinf' =>
      shafarevich_z_data_two_kummerCore k Ω K Λ hKΛ ζ hζ hζK S hSfin hSdisj hSram
        y' hy' hyc' hyS' hyT' hy0' hyinf')

end Work.SSGRoute
