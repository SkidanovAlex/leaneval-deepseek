import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.swHistKExists_proved
import Submission.Work.SSGRoute.ZDataMup.swHvalAtSiblingSelf
import Submission.Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-!
# State of the target `Work.SSGRoute.ZDataMup.sw_odd_kummer_core` (session notes)

## 0. The statement is TRUE; do not refute it

The target is Schmidt--Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*
(arXiv:math/9809211), **Theorem 13** in the case `A = μ_p`, `p` odd, in Kummer form.  The
hypotheses of the target *imply* the paper's hypotheses, clause by clause:
`hSram` is the paper's "`T ⊇ Ram(Λ|k) ∪ S_p ∪ S_∞`"; `hyS` is "`y_P` unramified for `P ∉ T(K)` not
split in `N`"; `hyT` + `hy0` give "`y_P = 0` for `P|k ∈ Ram(K|k) ∪ S_p`" (`hy0`'s first disjunct is
`¬IsSplitIn k K B`, which holds at a `K`-ramified place because the inertia is non-trivial, and
`Ram(K|k) ⊆ Ram(N|k) ⊆ cs(S)` by `hSram`); `hyinf` is the `S_∞`-condition (a real place of `k` is an
involution of `G_k`, Artin--Schreier).  The conclusion is the paper's (a) + (b) (see the docstring
of the theorem: clause 3 is the paper's `z_P^σ = 0` for `σ ≠ 1`, transported to `Ω`-places: the
`k`-conjugates of `B` that are *not* `K`-conjugates are exactly the `Ω`-places above the other
`K`-primes above `B|_k`, i.e. the paper's `σP` for `σ ∈ G(K|k) ∖ D_{P∩K}` modulo the decomposition
group).

So `declare_false` is *not* an option.  What follows is the exact reduction, so that the next
session does not have to re-derive it.

## 1. What is available (all `#print axioms`-clean: `[propext, Classical.choice, Quot.sound]`)

* `Work.SSGRoute.GrunwaldEscapeCore.escape_realisation_core` — the realisation oracle with escape:
  given a finite pairwise non-`K`-conjugate place set `T` covering the `p`-places and the
  `N`-ramified places, a global datum `g` (additive, locally constant on `G_K`, unramified outside
  `cs(T)` at the places not split in `N`) and a local datum `h` on the `T`-blocks (additive, locally
  constant, and *either* zero on the block *or* the block split in `N`), it produces `z` and an
  escape prime `Q` (finite, **split in `N`**, not `K`-conjugate to any element of `T`) with
  `z σ = g σ + h A σ` on `decomp k A ⊓ G_K` for `A ∈ T`, and `z` unramified at every finite `B`
  outside `cs(T)` and outside the `K`-class of `Q`.
  (Its proof produces `z = nodeKummerCocharZMod K ζ hζK hζ b` for an explicit `b ∈ Kˣ`.)
* `Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst` — the Kummer correspondence:
  every additive locally constant `z` on `G_K` is `χ_b` for some `b ∈ Kˣ`; together with
  `Work.SSGRoute.nodeKummerCocharZMod_mul` (`χ_{ab} = χ_a + χ_b`) this lets one *add* classes.
* `Work.SSGRoute.ZSplit.localValue_eq_zero_of_frob_eq_zero` and
  `Work.SSGRoute.kills_localGroup_of_kills_inertia_and_frob` — an unramified class which kills the
  inertia and vanishes at a Frobenius element vanishes on the *whole* local group (the
  "inertia → decomposition" upgrade of the paper's final step).
* `Work.SSGRoute.pigeonhole_two_eq` — the shoe box.

## 2. The design of the proof (verified by hand against the paper, pp. 14--16)

Since `y` is a *homomorphism* `G_K → ZMod p` (`hy`), the naive candidate `b` with `χ_b = y`
(which exists by the Kummer correspondence) satisfies clauses 1 and 2 but **not** clause 3: clause 3
is a genuine condition on the *divisor* of `b` (at each `k`-place `v ∉ cs(S)` at most one `K`-prime
above `v` may be ramified, and `b` must be a local `p`-th power at the others).  Hence the
Schmidt--Wingberg construction is needed.

* Fix `T₀` = one `Ω`-place per `K`-class above every `k`-place of `S` (finite: `|S| · [K:k]`).
  Prescribe `h A = 0` at the `T₀`-blocks, so every class built below agrees with `½y` there.
* Stage `n ≥ 1`: `T_n = T₀ ∪ {one place per `K`-class above `v_1, …, v_{n-1}`}`, where `v_j` is the
  `k`-place of the `j`-th escape prime `P_j`.  The local datum at the `T_n`-blocks above `v_j`
  (`j < n`) is: `0` at the block of the `K`-class of `P_j` itself, and `-(z_j)|_A` (i.e. the
  negative of the *already constructed* class `z_j`, restricted to the local group at `A`) at the
  other `K`-classes above `v_j`.  Since `v_j` is completely split in `N` (the escape prime is
  `N`-split), every block above `v_j` is split in `N`, so the oracle's orthogonality hypothesis is
  satisfied on those blocks; on the `T₀`-blocks it is satisfied by `h A = 0`.
  The oracle then produces `(z_n, Q_n)`; put `P_n := Q_n`, `v_n := Q_n|_k`.
  *Every* block datum is *unramified*, so `z_n` is unramified outside `cs(S)` and the `K`-class of
    `P_n`.
* Shoe box: with `b_m` the Kummer element of `z_m`, `a_m := v_{P_m ∩ K}(b_m) mod p ∈ (Z/p)^*`, and
  `ψ_{m,σ}` a Frobenius element of the local group at the `K`-prime `σ(P_m ∩ K)`, consider
  `V_m := (a_m, (a_m · z_m(ψ_{m,σ}))_{σ ∈ G(K|k)∖1}) ∈ (Z/p)^* × (Z/p)^{G(K|k)∖1}`.
  `pigeonhole_two_eq` gives `i < N` with `V_i = V_N`, i.e. `a_i = a_N` **and** the *weighted*
  matching `a_i z_i(ψ_{i,σ}) = a_N z_N(ψ_{N,σ})` for all `σ`.
* Final class `z := z_i + z_N` (a Kummer class by `nodeKummerCocharZMod_mul`, hence of the form
  `χ_b`).  Clause 1: every `T₀`-block datum is `½y`, so `z ≡ y` there, and the equality transports
  to the `k`-conjugates of `B ∈ cs(S)` because both `χ_b` and the homomorphism `y` are invariant
  under conjugation by `G_K` (they are, respectively, a Kummer cochain of a `G_K`-fixed element and
  an additive map).  Clause 2: the ramification of `z` is contained in `cs(S) ∪ cs(P_i) ∪ cs(P_N)`
  and the two escape primes are `N`-split.  Clause 3: `z` is *locally trivial* at the `K`-primes
  above `v_i` (because at those blocks `z_N ≡ -(z_i)`), and at the `K`-primes above `v_N` the
  cancellation is the paper's chain (see §3), after which `localValue_eq_zero_of_frob_eq_zero`
  promotes the vanishing at the Frobenius element to the whole local group.

## 3. The one genuine gap: the chain at the last prime

Everything in §2 is bookkeeping *except* the following arithmetic statement (verified by hand to be
exactly what the pigeonhole + clause 3 need).  Write `χ b := nodeKummerCocharZMod K ζ hζK hζ b`,
let `P_i, P_N` be the two escape primes, `ρ ∈ G_k` and let `Q_i ⊂ cs(P_i)`, `Q_N ⊂ cs(P_N)` be the
siblings `τ • (ρ • P_i)`, `τ • (ρ • P_N)` (`τ ∈ G_K`); let `ψ_i` (resp. `ψ_N`) be Frobenius elements
of the local groups at `Q_i` (resp. `Q_N`).  Then:

* **the two-place reciprocity** (the Hilbert-symbol product formula localised at the two escape
  primes, with the normalisation of the local Artin factors): with `a_i := v_{P_i ∩ K}(b_i) mod p`,
  `a_N := v_{P_N ∩ K}(b_N) mod p` (`≠ 0`),
  `a_N · χ b_i ψ_N = a_i · χ b_N ψ_i`;
* combined with the *prescription* `χ b_N ψ_i = - χ b_i ψ_i` (condition (3) of the paper, with the
  **corrected sign**: the printed condition is missing the inverse, see
  `NOTE_z_data_mup_odd_of_grunwald_state.md` §9) this yields
  `χ b_i ψ_N = -(a_i/a_N) · χ b_i ψ_i`, which together with the weighted matching
  `a_i χ b_i ψ_i = a_N χ b_N ψ_N` gives the required `χ b_i ψ_N + χ b_N ψ_N = 0`.

The reciprocity uses the *cyclic Kummer extension* `K(c^{1/p})/K` and its local Artin factors, which
the tree has in two axiom-clean forms: `Work.SSGRoute.ZSplit.localFactor_productFormula_cyclic`
(local norm kernel, Frobenius normalisation at every unramified prime, product formula) and
`Work.SSGRoute.ZDataMup.productFormula_cyclic_kummer`; the pairing
`⟨x, c⟩_v := (the Kummer index of θ_v(x) on a chosen `p`-th root of `c`)` is additive in `x` for
free (θ is a homomorphism), additive in `c` by the diagonal/antisymmetry
(`Work.SSGRoute.GrunwaldEscapeCore.kummerCharZMod_antisymm`, available), and
`⟨π_v, c⟩_v = χ c (a Frobenius at v)` is the Frobenius normalisation combined with the Kummer
dictionary of `Work.SSGRoute.ZSplit.FrobeniusValue`.  The *only* delicate point is the comparison of
the normalisations of `a_i` and `a_N` (the two escape primes live over different `k`-places, so the
"`≡ 1 mod p`" normalisation of the escape class has to be exposed by the oracle; this is exactly
Schmidt--Wingberg's condition (1), `(z_i)_{P_i} ≡ Frob_{P_i} mod H¹_nr`, which the present
`escape_realisation_core` does **not** state).

**Delegation targets** (in order): (i) the strengthened oracle
`escape_realisation_core` + "(the class of `z` at the escape prime `Q` is congruent to the class of a
uniformiser modulo the unramified classes)" — needed to make `a_i/a_N = 1` usable; (ii) the chain
relation of §3 for the two escape primes.  With those two, §2 assembles the target.

## 4. Update after the first delegation round (reviewer findings + landed assembly lemmas)

**(a) The escape normalisation is `-1`, uniformly.**  Both reviewers of the strengthened oracle read
`GrunwaldEscapeCore/escape_correction.lean` (lines 174–246) and `step4_y_escape_v2/CorrectionSupPow.lean`
and determined the exact divisor of the escape element: `𝔵 = 𝔡·(𝔮)`, `count 𝔮 𝔵 = count 𝔮 a + 1`,
`count 𝔮 γ ≡ count 𝔮 𝔵`, `b = a·γ⁻¹`, hence

  `v_𝔮(b) ≡ −1 (mod p)`  at the escape prime, for **every** escape prime.

This is forced (any read-off `γ' = γ·c` has `count 𝔮 c ≡ 0`), so the normalisation is *uniform*: the
ratios `a_i/a_N` of two escapes are `1`, and the shoe box may be run with the **unweighted** vector
`V_m := (z_m(ψ_{m,σ}))_σ`.  The statement of the strengthened oracle was fixed accordingly (`χ_b` on
the *inertia* at `Q` equals `−χ_x` for a uniformiser `x`, i.e. `v_Q(b) ≡ −1`).

**(b) The chain piece must be stated as the two-place reciprocity.**  Both reviewers of
`chain_lastPrime` (first version) showed that the *prescription* + *matching* alone leave
`χ b_i ψ_N` free (the conclusion is a third equation independent of the two hypotheses); the
statement must therefore *be*

  `χ b_i ψ_N = χ b_N ψ_i`   (the two-place Hilbert-symbol product formula, with `a_i = a_N`),

from which `χ b_i ψ_N + χ b_N ψ_N = 0` follows in one line using `hpresc` and `hmatch`.

**(c) Landed in this file (all proved, `#print axioms`-clean).**

* `nodeKummerCocharZMod_conj` — the level-`K` Kummer cochain is invariant under conjugation by
  `K.fixingSubgroup` (proved from `nodeKummerCocharZMod_add` alone: additivity into the additive
  group `ZMod p`).
* `additive_conj_invariant` — the same for any additive `y` (used for the right-hand side of
  clause 1).
* `localAgreement_conj` — the agreement at a place transports to its `K`-conjugates.
* `clause_one_of_covering` — clause 1 of the target from the agreement at a covering set of
  `K`-classes (the two lemmas above plus the covering hypothesis).
* `clause_two_of_confinement` — clause 2 from the oracle's confinement, given that every `K`-class of
  `T` lies above a place of `S` and that the escape prime is `N`-split (the latter transported to the
  `K`-conjugates by `SSGRoute.isSplitIn_conj`).

**(d) What remains.**

1. The *recursion*: build the sequence `(z_m, P_m)` over `ℕ` from the strengthened oracle, with
   `T_n = T₀ ∪ {one place per `K`-class above `v_1, …, v_{n-1}`}` and the datum `0` at the
   `T₀`-blocks, `−(z_j)|_A` at the other blocks above `v_j` (and `0` at the block of `P_j`'s own
   `K`-class, so that no clause-3 trigger fires at the older primes).  The finite set `T₀` (one
   representative per `K`-class above the `k`-classes of `S`) can be built as the image of
   `S × Gal(K/k)` under `(A,σ) ↦ ρ_σ • A` for chosen lifts `ρ_σ`; the deduplication needed for the
   oracle's pairwise-non-`K`-conjugacy hypothesis is the only awkward point of this step.
2. The shoe box (`pigeonhole_two_eq`) applied to `m ↦ V_m ∈ (Z/p)^{G(K|k)∖1}`.
3. Clause 3 via `Work.SSGRoute.ZSplit.sw_conjuncts_five_six` (already proved, in the tree), with its
   three inputs: (i) the confinement of `z` (from the two halves' confinements and the fact that
   every prescribed block datum is *unramified*), (ii) the vanishing at the `K`-conjugates of `P_i`
   (the prescription `z_N ≡ −z_i` there), (iii) the vanishing at the `K`-conjugates of `P_N`
   (the delegated reciprocity + `ZSplit.localValue_eq_zero_of_frob_eq_zero`).
4. Clause 1 via `clause_one_of_covering` and clause 2 via `clause_two_of_confinement`.

## 5. Second delegation round: the well-posedness of the chain statement

The first version of `chain_lastPrime` (with the "generation" hypotheses
`hpow : ∀ τ ∈ H, ∃ m, res k L τ = (res k L g)^m` pinning the Frobenius elements) was **declared
false by its prover**, correctly: `g` can be replaced by `g^m` (any generator of the same cyclic
subgroup) and then `χ b (g^m) = m • χ b g`, so the "value at the Frobenius" is not pinned.  The
repaired statement (now with its own prover) has *two* fixes:

* the Frobenius elements are pinned by the workspace's canonical normalisation
  `NK.Chebotarev.IsFrobAtPrime (K := k) (L := L) 𝔭 (res k L g)` together with
  `¬ SSGRoute.IsRamifiedIn k L Q` and the `HeightOneSpectrum`-correspondence of `Q` (this is the
  hypothesis list of `ZSplit.localValue_eq_zsmul_of_isFrobAtPrime`);
* both *crossed* level-kernel vanishings are assumed,
  `∀ u ∈ decomp k QN ⊓ K.fixingSubgroup, res k L u = 1 → χ b_i u = 0` and its mirror at `Qi`
  (the reviewer's point: perturbation by `ker(res k L) ∩ decomp` preserves every other hypothesis
  but changes the two values).  In the assembly these crossed vanishings come from the confinement
  plus `ZSplit.hker_of_kills_inertia`, exactly as the same-place ones do.

With `hnorm_i`/`hnorm_N` encoding `v ≡ −1` at both escape primes (the uniform normalisation of §4(a)),
the conclusion is the *unweighted* reciprocity `χ b_i ψ_N = χ b_N ψ_i`, from which the assembly's
clause-3 input `χ b_i ψ_N + χ b_N ψ_N = 0` follows in one line from the prescription and the
(unweighted) shoe-box matching.

**For the recursion (§4(d) 1).**  The `K`-class representatives above the places of `S` can be built
as `(S.product univ).image (fun p ↦ galLift K p.2 • p.1)` where
`galLift K σ := Classical.choose (AlgEquiv.restrictNormalHom_surjective σ)`; the covering property
(one representative per `K`-class above each `k`-class of `S`) then follows because two lifts with
the same image under `res k K` differ by an element of `K.fixingSubgroup`.

## 6. Third session: the architecture is in place; the two arithmetic nodes are delegated

**(a) The module split (§6.1).**  The definitions and the *proved* bookkeeping lemmas of the assembly
now live in `Submission/Work/SSGRoute/ZDataMup/swCoreDefs.lean` (module
`Work.SSGRoute.ZDataMup.swCoreDefs`), which this file imports.  The reason is delegation: a lemma
requested in a file that imports *this* file cannot be used by it (import cycles), so every node whose
result the assembly consumes must sit in a module that itself only imports `swCoreDefs`.  All the
earlier definitions (`galLift`, `kleadReps`, `siblingPlace`, `correctionDatum`, `histPlaces`,
`histDatum`, `HistInv`) and the proved assembly lemmas moved there unchanged; `HistKummer` was added
and the old (unproved) `histKummerExists` was deleted.

**(b) What the recursion node must produce.**  The oracle `escape_uniformised`
(`Submission/Work/SSGRoute/ZDataMup/escape_uniformised.lean`, proved, axiom-clean) is the *step*: fed
the place set `histPlaces K S (f|m)`, the global datum `g = ½y` and the accumulated correction datum
`histDatum K y (f|m)`, it produces `(Q_m, z_m, b_m)` with `z_m = χ_{b_m}` on `K.fixingSubgroup`, the
prescribed values on the blocks, the confinement, and the uniformiser normalisation at `Q_m`.  The
node `Work.SSGRoute.ZDataMup.swRecursionExists`
(`Submission/Work/SSGRoute/ZDataMup/swRecursionExists.lean`, delegated) packages the iteration as
`∃ f, HistInv K N S y f ∧ HistKummer K ζ hζ hζK f`; its proof is an induction on the stage, each step
discharging the oracle's hypotheses with `correctionDatum_add`/`correctionDatum_locConst` (the
finite-sum versions), `histDatum_eq_zero_on_T0` (the `horth` first disjunct at the `T₀`-blocks), the
splitness of the escape primes (the second disjunct at the escape blocks) and `kleadReps_covers`.

**(c) The chain, with the signs resolved (§9 of the paper read against the PS source).**  The printed
chain (p. 15 of arXiv:math/9809211) is

  `z_N(Frob_{σP_N}) = z_i(Frob_{σP_i}) = (z_i,σz_i)_{σP_i} = (z_i,σz_i)_{P_i}^{-1}
   = (z_i,σz_N)_{P_i} = (z_i,σz_N)_{σP_N}^{-1} = z_i(Frob_{σP_N})^{-1}`.

Two corrections are needed in the passage to a formal statement (the reviewers of
`swChainTwoPlaceValue` flagged exactly this):
* the *fourth* equality uses the prescription (3) at the sibling `σP_i` **conjugated back to `P_i`**,
  i.e. `σ(b_N) ≡ σ(b_i)^{-1}` at `P_i`, which requires the prescription (3) at *all* the siblings
  `τP_i` (`τ ≠ 1`) — hence the universally quantified `hpresc` of the statement — and the triviality
  of the `(−1)`-symbol (`p` odd, so `⟨x,−1⟩ = 0` since `2⟨x,−1⟩ = ⟨x,1⟩ = 0` and `2` is invertible);
* the composite equality is a *value* identity at the Frobenius and needs the local dictionary
  `⟨a,b⟩_A = χ_α(θ_A(β))` in the situation "the extension of `α` is unramified at `A` and
  `v_A(β) ≡ −1`": then `θ_A(β) = Frob_A^{-1}` (the Artin map at an unramified place is
  `Frob^{v}` and `Frob^p = 1` in the degree-`p` unramified extension), so
  `⟨a,b⟩_A = −a(g)` for any Frobenius element `g` of the local group at `A`.  This is the dictionary
  built from `ZDataMup.localFactor_unramified_eq_frob_pow` and
  `ZSplit.localValue_eq_zsmul_of_isFrobAtPrime`; it is *not* yet on disk.

**Conclusion of the chain** (`swChainTwoPlaceValue`, the delegated node
`Submission/Work/SSGRoute/ZDataMup/swChainTwoPlaceValue.lean`):
`χ_{b_i}(g_N) = −χ_{b_i}(g_i)`, where `g_i`/`g_N` are the canonical Frobenius elements
(`IsFrobAtPrime` at a level `L` unramified at the two sibling places) of the `σ`-siblings of `P_i` and
`P_N`.  Combined with the shoe-box matching `χ_{b_N}(g_N) = χ_{b_i}(g_i)` (the vector equality
`Ψ_N(z_i) = Ψ_N(z_N)`, which the pigeonhole `Work.SSGRoute.pigeonhole_two_eq` supplies) this gives
`(χ_{b_i}+χ_{b_N})(g_N) = 0`, and `ZSplit.localValue_eq_zero_of_frob_eq_zero` (with
`hker_of_kills_inertia` and `localGroup_pow_of_isFrobAtPrime`) promotes it to the whole local group at
the sibling `K`-prime of `P_N` — which is clause 3 for the trigger places in `cs(P_N)`.

**(d) What is proved in `swCoreDefs` for the assembly.**

* `half_add_half` — `½a + ½a = a` in `ZMod p` for odd `p` (needed to see that the two halves sum to
  `y`).
* `histPlaces_mem_conjPlace` — every block is `k`-conjugate to an element of `S` or to one of the
  escape primes of the prefix.
* `hist_escapes_not_conj` — the escape primes of a history are pairwise not `k`-conjugate (the
  covering `kleadReps K {Q_m}` against the exclusion clause); this is what makes the corrections of
  `histDatum` at a block above `v_l` consist of the `l`-th term alone.
* `hist_prescribed_at_T0` — at the `T₀`-blocks every class of the history equals `½y`.
* `hist_sum_kills_inertia` — `z_i + z_N` kills the inertia at every finite place outside `cs(S)` and
  outside the `k`-classes of `Q_0, …, Q_N` (the confinement conjunct of `HistInv` at the two stages,
  with the place-set inclusion).
* `hist_clause_one` — clause 1 of the target in class form (via `kleadReps_covers`,
  `hist_prescribed_at_T0` and the conjugation invariance `additive_conj_invariant` of the additive
  classes, which `HistInv`'s additivity conjunct supplies).
* `hist_clause_two` — clause 2 of the target in class form (from `hist_sum_kills_inertia`, using that
  the escape primes are `N`-split and `isSplitIn_conj`).
* `hist_sum_zero_at_sibling_of_i` — the sum `z_i + z_j` vanishes on the whole local group at every
  `Ω`-place `k`-conjugate but not `K`-conjugate to `Q_i` (Schmidt--Wingberg's condition (3) read at
  the block of the sibling `K`-prime, with `hist_escapes_not_conj` collapsing the correction datum to
  the single `i`-th term); this is the `l = i` half of clause 3.

**Proved elsewhere in the workspace (fourth session).**  `Work.SSGRoute.ZDataMup.swTriggerPlace`
(`Submission/Work/SSGRoute/ZDataMup/swTriggerPlace.lean`, delegated and proved, axiom-clean) is the
trigger analysis of clause 3: a finite place `B` outside `cs(S)`, split in `N`, at which `z_i + z_j`
has a nonzero inertia value, is `K`-conjugate to `Q_i` or to `Q_j`.  Together with
`hist_sum_zero_at_sibling_of_i` and the chain this gives clause 3.  The recursion itself is likewise
already proved elsewhere: the reviewers of `swRecursionExists2` report that
`Work.SSGRoute.ZConstruction.swRecursionExists_of_chain` together with
`HistKummerNorm.value_form` (`ZConstruction/RecursionConvert.lean`) yields `HistInv ∧ HistKummer`
from exactly the hypothesis list of `swRecursionExists2` — if that cone is importable together with
`swCoreDefs` (there are known cone clashes between `ZConstruction` and the `ZDataMup` lane, e.g. two
`OddForm.oPairForm`s), then the assembly can use it directly.

**(e) What the next session must still write (in this file).**

1. The shoe-box wiring: the Frobenius family `G : ℕ → (K ≃ₐ[k] K) → Ω ≃ₐ[k] Ω` with
   `G m σ ∈ decomp k (siblingPlace K σ (Q m)) ⊓ K.fixingSubgroup` and
   `IsFrobAtPrime ... (res k L (G m σ))` is produced by `exists_frobFamily` (`swCoreDefs`), given the
   level `L` (take `L := N`, unramified at the sibling places because they lie outside `cs(S) ⊇
   Ram(N|k)`, using `isRamifiedIn_conj` and `SSGRoute.isFinPlace_smul_iff`) and the
   `HeightOneSpectrum`-correspondence of each sibling place
   (`Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime`, cf.
   `primeOfA` in `exists_mem_closure_decomp_mul_subgroup.lean`).  Then `selection_matching`
   (`swCoreDefs`) gives `i < N` with the matching `z_N(G N σ) = z_i(G i σ)` for all `σ`, and
   `siblingPlace_not_gesKConj` (`swCoreDefs`) supplies the separation hypotheses of the chain.
2. Clause 3: the *trigger analysis*.  If `B` is a finite trigger place (so `z_i + z_N` has a nonzero
   inertia value at `B`) which is not `k`-conjugate to `S` and is split in `N`, then — taking the
   contrapositive of `hist_sum_kills_inertia`, which needs `¬ IsConjPlace k (Q_l) B` for all `l ≤ N`
   (available because `B` is `N`-split and the `Q_l` are) — either `B ∈ cs(S)` (excluded) or `B` is
   `k`-conjugate to some `Q_l` with `l ≤ N`.  The case `l < i` forces `z_i + z_N ≡ 0` (both classes
   are prescribed `0`/`−z_l` there, hence the sum is `0` or `−2z_l`, and `z_l` is unramified at its
   own siblings), the case `i < l < N` forces the sum to be *unramified* (each summand is either
   prescribed or unramified, and `hist_escapes_not_conj` says the escape primes do not interfere),
   and the cases `l = N` and `l = i` are the two live ones.  At `l = N`, `B` must lie in the own
   `K`-prime of `Q_N` (at the siblings the sum is unramified), and the required vanishing at the
   `k`-conjugates `Q ∉ cs(Q_N)` is the chain's conclusion; at `l = i` the same with the prescription.
   Both are local-group statements about an arbitrary `Ω`-place of a sibling `K`-prime, transported
   from the block representative by `additive_conj_invariant`.
3. The final conversion: take `b := b_i · b_N` from `HistKummer`, so that
   `χ_b = z_i + z_N` on `K.fixingSubgroup` by `Work.SSGRoute.nodeKummerCocharZMod_mul`, and
   `HistKummer`'s bridges turn `hist_clause_one`/`hist_clause_two`/clause 3 into the three conjuncts
   of the target.

**Addendum: the pinning of the Frobenius values (third session).**  The first version of the chain
statement was refuted twice, and usefully: (i) the uniformiser clause must be the *maximality*
`val y ≤ val x` (as `escape_uniformised` states it), not `val x ≤ val y`, which is unsatisfiable
(`Work.SSGRoute.ZDataMup.valuationMinimalClause_unsatisfiable`); (ii) a *free* level `L` does not pin
the Frobenius values — with `L = ⊥` the hypothesis `IsFrobAtPrime` is vacuous and the conclusion
fails.  The repaired statement (delegated as `Work.SSGRoute.ZDataMup.swChainValue`,
`Submission/Work/SSGRoute/ZDataMup/swChainValue.lean`) therefore carries, in addition, the four
*kernel* vanishings `∀ u ∈ decomp k (siblingPlace K σ Q) ⊓ K.fixingSubgroup, res k L u = 1 →
χ_{b_m} u = 0` (`m ∈ {i,N}`, `Q ∈ {Pi,PN}`).  In the assembly they are supplied by taking `L` to be
the compositum of the Kummer levels `hLevel(b_0), …, hLevel(b_N)`: each `χ_{b_m}` factors through
`Gal(hLevel(b_m)/K)`, so `res k L u = 1` forces `χ_{b_m} u = 0`; and that `L` is unramified at the two
sibling places because the ramification of `hLevel(b_m)` is confined to `cs(T_m) ∪ cs(Q_m)` by the
confinement conjunct of `HistInv` (the sibling places are `k`-conjugate to no element of `T_m` and
not `K`-conjugate to `Q_m`).  The same four hypotheses supply the `hker` input of the promotion
`localValue_eq_zero_of_frob_eq_zero` used in clause 3, and `hker_of_kills_inertia` is *not* the right
tool for them (`H9.false_of_hLker` shows that the level kernel of a finite level strictly contains the
inertia in this setting).

## 7. Fifth session: the assembly is complete; the reduction to a single piece

The previous designs (the recursion in *class* form plus a free-level chain) are superseded by the
following route, which uses the `H9` lane's proved recursion in *Kummer* form and reduces the whole
theorem to one explicit arithmetic piece.

1. **The history.** `Work.SSGRoute.H9.swHistKExists_proved` (proved, axiom-clean) produces a history
   `f : ℕ → (Q_m, b_m)` with `Work.SSGRoute.H9.HistK K N ζ hζ hζK S y f` from exactly the
   hypotheses `hp, hKN, hSfin, hSdisj, hSram, hy, hyc, hyS` of the target.  (Note `hyT`, `hy0`,
   `hyram`, `hyinf` are not needed for the construction; they remain in the statement because the
   node's hypothesis list is fixed.)
2. **The shoe box.** `Work.SSGRoute.NodeS35.pinValue_pigeonhole` (proved) selects `i < j` whose
   *pinned* Frobenius-value vectors agree: `pinValue j σ = pinValue i σ` for every `σ`.
3. **The chain at the last escape prime.**  This is the one remaining arithmetic input, and it is
   delegated as `Work.SSGRoute.ZDataMup.swHvalAtSibling`
   (`Submission/Work/SSGRoute/ZDataMup/swHvalAtSibling.lean`): at the sibling `σ • Q_j` of the last
   escape prime there is an element `ψ` of the local group, pinned at the compositum
   `M := K(b_i^{1/p}) · K(b_j^{1/p})` of the two Kummer levels, at which `χ_{b_i} + χ_{b_j}`
   vanishes.  Its proof is the two-place product formula of Schmidt--Wingberg §4(b)
   (`NodeS35.swChainValueH9_modp`, i.e. the two-place reciprocity read through the local dictionary
   `H9.swPairingValueFrob_of_kills`), with the pinnings supplied by `NodeS35.exists_pinned_at` and
   `NodeS35.pin_of_le`, the unramifiedness by `NodeS35.isUnramifiedIn_sup_hLevel` (fed by the
   refined confinements `H9.swHistChi_confinement_proved` and `NodeS35.histK_killing`), the escape
   normalisations by `NodeS35.histCount_modp` and `H9.swCount_conjUnit`, and the prescription by
   `H9.swHistChi_presc_proved`.  The *shoebox* input is the hypothesis `hmatch` of step 2.
4. **The promotion (this file).**  At the sibling place `A := σ • Q_j` the level `M` is unramified
   (the sum `χ_{b_i} + χ_{b_j}` kills the inertia there, since both classes are confined away from
   `A`), and the level kernel of `M` is killed by the sum
   (`NodeS34.swKLevel_sum_kills_levelKernel`, because `hLevel (b_i · b_j) ≤ M` by
   `hLevel_mul_le`).  Hence `NodeS34.swKLevel_sum_vanish` (Schmidt--Wingberg's "an unramified class
   is determined by its value at a Frobenius") promotes the value identity of step 3 to the whole
   local group `decomp k A ⊓ G_K`; `NodeS34.swKLevel_localGroup_pow` supplies the cyclicity of the
   local group at the level, via `map_decomp_res_eq_zpowers_of_isFrobAtPrime`.
5. **The chain for all siblings.**  `H9.swSiblingVanishing_all` extends the vanishing from the
   `galLift`-siblings to every `Ω`-place `k`-conjugate but not `K`-conjugate to `Q_j` — this is
   literally the `hchain` input of `H9.ZSix_of_histK`.
6. **The six conjuncts.**  `H9.ZSix_of_histK` (proved) assembles Schmidt--Wingberg's auxiliary class
   `z` from the history, the refined confinements at stages `i` and `j`
   (`H9.swHistChi_confinement_proved`), the prescription `hpresc`
   (`H9.swHistChi_presc_proved`) and `hchain` from step 5.
7. **The Kummer form.**  `ZSplit.exists_kummerCocharZMod_of_additive_locConst` writes the additive
   locally constant class `z` as `χ_b` for some `b ∈ Kˣ`, and the three conjuncts of the target are
   the corresponding clauses of `ZSix` rewritten through `χ_b = z`
   (this is `Work.SSGRoute.H9.sw_odd_kummer_core_of_zSix`, re-proved here because that lemma lives in
   a file that *imports* the present one, so that importing it would create a cycle).

The three `#print axioms`-clean inputs of the whole proof are therefore: the recursion
(`H9.swHistKExists_proved`), the shoe box (`NodeS35.pinValue_pigeonhole`), and the single delegated
chain value identity (`ZDataMup.swHvalAtSibling`).

-/

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest

namespace Work.SSGRoute.ZDataMup

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- **The arithmetic core of `Work.SSGRoute.z_data_mup_odd_of_grunwald` (Schmidt--Wingberg §4, `A = μ_p`, `p` odd, in Kummer form).**

Let `p` be an odd prime, `k` a number field, `Ω` an algebraic closure, `K ≤ N` finite Galois intermediate fields with `ζ_p ∈ K`, and `S` a finite set of pairwise non-`k`-conjugate finite places covering the places above `p` and the places ramified in `N`.  Let `y : G_k → ZMod p` be additive and locally constant on `G_K`, unramified at the finite places outside `cs(S)` that are not split in `N` (`hyS`), locally trivial at the places of `cs(S)` (`hyT`, `hy0`), and vanishing on the involutions of `G_K` (`hyinf`).

Then there is `b ∈ Kˣ` whose Kummer cochain `χ_b = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b`
 * agrees with `y` on the local groups `decomp k B ⊓ K.fixingSubgroup` of every place `B` in `cs(S)`;
 * kills the inertia of every finite place outside `cs(S)` that is not split in `N`;
 * satisfies Schmidt--Wingberg's sharpened condition (b): at every place `B ∉ cs(S)` split in `N` at which `χ_b` is ramified, `χ_b` vanishes on the local group of every `k`-conjugate `Q` of `B` that is not a `K`-conjugate of `B`.

The unramified case is already proved (`Work.SSGRoute.sw_odd_kummer_core_of_unramified`), as is the additivity `χ_{ab} = χ_a + χ_b` needed to compute the final class (`Work.SSGRoute.nodeKummerCocharZMod_mul`), the involution clause (`Work.SSGRoute.nodeKummerCocharZMod_involution_eq_zero`) and the realisation oracle with escape (`Work.SSGRoute.GrunwaldEscapeCore.escape_realisation_core`); the node `Work.SSGRoute.z_data_mup_odd_of_grunwald` is *proved* from this statement by `Work.SSGRoute.z_data_mup_odd_of_grunwald_of_kummerCore`.  A step-by-step roadmap (with the proved ingredients of this workspace, including the corrected sign in condition (3) of the paper) is in `Submission/Work/SSGRoute/NOTE_z_data_mup_odd_of_grunwald_state.md` §9--§9bis. -/
theorem sw_odd_kummer_core (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [Fintype (K ≃ₐ[k] K)] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y σ ≠ 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ b : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = y σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
            Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ = 0) := by
  classical
  -- `↥K` is a number field and `Ω` is a separable closure of it (needed by the `↥K`-relative
  -- level machinery of the §4(b) chain).
  haveI : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField K
  haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  -- ## 1. the Kummer-form history of the §4 recursion
  obtain ⟨f, hf⟩ := Work.SSGRoute.H9.swHistKExists_proved (p := p) hp K N hKN ζ hζ hζK S hSfin
    hSdisj hSram y hy hyc hyS
  -- ## 2. the shoe box selects the pair `i < j`
  obtain ⟨i, j, hij, hmatch⟩ :=
    Work.SSGRoute.NodeS35.pinValue_pigeonhole (K := K) (p := p) ζ hζ hζK f hf.1
  -- ## 3. bookkeeping of the history
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  have hkdisj : ¬ SSGRoute.IsConjPlace k ((f i).1) ((f j).1) :=
    Work.SSGRoute.H9.histK_escape_kdisj (K := K) (N := N) ζ hζ hζK S y f hf hij
  have hQjsplit : SSGRoute.IsSplitIn k K ((f j).1) :=
    fun σ hσ => IntermediateField.fixingSubgroup_le hKN (hf.2.1 j hσ)
  -- ## 4. the promotion level `M = K(b_i^{1/p}) · K(b_j^{1/p})` and its instances
  let M : IntermediateField ↥K Ω := hLevel (Ω := Ω) (K := K) (p := p) (f i).2
    ⊔ hLevel (Ω := Ω) (K := K) (p := p) (f j).2
  haveI hfdM : FiniteDimensional ↥K ↥M := by
    dsimp only [M]
    exact hLevel_sup_finiteDimensional (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ'
      (f i).2 (f j).2
  haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f i).2) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' (f i).2
  haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f i).2) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' (f i).2
  haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f j).2) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' (f j).2
  haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f j).2) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' (f j).2
  have hsupstruct := galois_sup_general (F := ↥K) (Ω := Ω) (p := p)
      (hLevel (Ω := Ω) (K := K) (p := p) (f i).2)
      (hLevel (Ω := Ω) (K := K) (p := p) (f j).2)
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' (f i).2)
      (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' (f j).2)
      (hLevel_aut_pow_eq_one (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' (f i).2)
      (hLevel_aut_pow_eq_one (Ω := Ω) (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K) hζ' (f j).2)
  haveI hgalM : IsGalois ↥K ↥M := by
    dsimp only [M]
    exact hsupstruct.1
  have hcommM : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a := by
    dsimp only [M]
    exact hsupstruct.2.1
  haveI : NumberField ↥M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField M
  -- the Kummer level of the *product* is contained in `M`
  have hroot : ((Work.SSGRoute.kummerSqrtUnitZMod (K := ↥K) (Ω := Ω) p ((f i).2 * (f j).2)
      : Ωˣ) : Ω) ∈ M := by
    have hle : hLevel (Ω := Ω) (K := K) (p := p) ((f i).2 * (f j).2) ≤ M := by
      dsimp only [M]
      exact hLevel_mul_le (Ω := Ω) (K := K) (p := p) (f i).2 (f j).2
    have hpowa : ((Work.SSGRoute.kummerSqrtUnitZMod (K := ↥K) (Ω := Ω) p ((f i).2 * (f j).2)
        : Ωˣ) : Ω) ^ p = algebraMap ↥K Ω (((f i).2 * (f j).2 : (↥K)ˣ) : ↥K) := by
      rw [← Units.val_pow_eq_pow_val, Work.SSGRoute.kummerSqrtUnitZMod_pow]
      rfl
    exact hle (NK.LocalAnabelian.mem_kummerField_of_pow_eq (K' := Ω) hpowa)
  -- ## 5. the chain, promoted to the local group at each sibling of the last escape prime
  have hsib : ∀ σ : K ≃ₐ[k] K, σ ≠ 1 →
      ∀ τ ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.galLift K σ • (f j).1) ⊓ K.fixingSubgroup,
        Work.SSGRoute.H9.histChi K ζ hζK hζ f i τ
          + Work.SSGRoute.H9.histChi K ζ hζK hζ f j τ = 0 := by
    intro σ hσ
    have hA : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.galLift K σ • (f j).1) :=
      (SSGRoute.isFinPlace_smul_iff (k := k) ((f j).1) (Work.SSGRoute.ZDataMup.galLift K σ)).mpr
        (hf.1 j)
    -- the two classes kill the inertia at the sibling, so the level `M` is unramified there
    have hkill_i : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k
        (Work.SSGRoute.ZDataMup.galLift K σ • (f j).1) u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f i).2 u = 0 :=
      (Work.SSGRoute.H9.swHistChi_confinement_proved (p := p) hp K N ζ hζ hζK S y hyT f hf i)
        _ hA (fun hc => hkdisj (SSGRoute.isConjPlace_trans
          (Work.SSGRoute.NodeS35.isConjPlace_of_gesKConj hc)
          ⟨(Work.SSGRoute.ZDataMup.galLift K σ)⁻¹, by rw [inv_smul_smul]⟩))
    have hkill_j : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k
        (Work.SSGRoute.ZDataMup.galLift K σ • (f j).1) u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f j).2 u = 0 :=
      (Work.SSGRoute.H9.swHistChi_confinement_proved (p := p) hp K N ζ hζ hζK S y hyT f hf j)
        _ hA (Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hσ hQjsplit)
    have hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥M)
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
          (Work.SSGRoute.ZDataMup.galLift K σ • (f j).1) hA) :=
      Work.SSGRoute.NodeS35.isUnramifiedIn_sup_hLevel (K := K) (p := p) ζ hζ hζK (f i).2 (f j).2
        _ hA hkill_i hkill_j
    -- the value identity of the chain at the pinned Frobenius
    obtain ⟨ψ, hψ, hpin, hval⟩ :=
      Work.SSGRoute.ZDataMup.swHvalAtSiblingSelf (p := p) hp hKN ζ hζ hζK S y hyT f hf i j hij
        hmatch σ hσ hA
    have hfrob : NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥M)
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
          (Work.SSGRoute.ZDataMup.galLift K σ • (f j).1) hA)
        (AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω) ↥M
          ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩)) :=
      (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq (K := ↥K) (L := ↥M) hcommM
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
          (Work.SSGRoute.ZDataMup.galLift K σ • (f j).1) hA) hunr _).mpr hpin.symm
    -- Schmidt--Wingberg's final step: the unramified class is determined by its Frobenius value
    exact Work.SSGRoute.NodeS34.swKLevel_sum_vanish (K := K) M ζ hζ hζK (f i).2 (f j).2 hroot _
      hA (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.galLift K σ • (f j).1) hA)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K)
        (A := Work.SSGRoute.ZDataMup.galLift K σ • (f j).1) hA)
      hunr ψ hψ hfrob hval
  -- ## 6. the chain at the last escape prime (`hchain` of `H9.ZSix_of_histK`)
  have hchain : ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k ((f j).1) Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • ((f j).1) = Q) →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
        Work.SSGRoute.H9.histChi K ζ hζK hζ f i τ
          + Work.SSGRoute.H9.histChi K ζ hζK hζ f j τ = 0 :=
    Work.SSGRoute.H9.swSiblingVanishing_all (K := K) ζ hζ hζK (f i).2 (f j).2 (f j).1 hsib
  -- ## 7. the six conjuncts (Schmidt--Wingberg's auxiliary class `z`)
  have hpresc := Work.SSGRoute.H9.swHistChi_presc_proved (p := p) hp K N ζ hζ hζK S y f hf i j hij
  have hzsix := Work.SSGRoute.H9.ZSix_of_histK (p := p) hp K N ζ hζ hζK S y hy f hf i j hij
    (Work.SSGRoute.H9.swHistChi_confinement_proved (p := p) hp K N ζ hζ hζK S y hyT f hf i)
    (Work.SSGRoute.H9.swHistChi_confinement_proved (p := p) hp K N ζ hζ hζK S y hyT f hf j)
    hpresc hchain
  -- ## 8. the Kummer form: the class is `χ_b` for some `b ∈ Kˣ`
  obtain ⟨z, hzadd, hzlc, hzT, _hzinf, hzS, hz3⟩ := hzsix
  obtain ⟨b, hb⟩ := Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst
    (p := p) k Ω K ζ hζK hζ z hzadd hzlc
  refine ⟨b, ?_, ?_, ?_⟩
  · intro B hB hconj σ hσK hσd
    rw [← hb σ hσK]
    exact hzT B hB hconj σ hσK hσd
  · intro B hB hS hns σ hσK hσI
    rw [← hb σ hσK]
    exact hzS B hB hS hns σ hσK hσI
  · intro B hB hS hsplit hram Q hQ hnot τ hτ
    rw [← hb τ (Subgroup.mem_inf.mp hτ).2]
    refine hz3 B hB hS hsplit ?_ Q hQ hnot τ hτ
    obtain ⟨σ, hσI, hσK, hσne⟩ := hram
    exact ⟨σ, hσI, hσK, fun h0 => hσne (by rw [← hb σ hσK]; exact h0)⟩


end Work.SSGRoute.ZDataMup
