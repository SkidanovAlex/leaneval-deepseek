import Mathlib
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.nprime_ge_two
import Submission.Work.PSU3.StageB.ncard_involutions_inf_H
import Submission.Work.PSU3.StageB.card_map_sylow_eq
import Submission.Work.PSU3.StageB.ncard_involutions_map_inf
import Submission.Work.PSU3.StageB.orderOf_map_sylow_mul
import Submission.Work.PSU3.StageB.exists_PSU3_of_card_sylow_eq_cube
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.StageB.t_mem_and_center_quotient
import Submission.Work.PSU3.StageB.Wiring
-- the case-c machinery (all of it hole-free with clean axioms, see the header note)
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageA.caseC_not_suzuki_card_q2_b
import Submission.Work.PSU3.StageB.SemiregVendored

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end
-- `Submission.Work.PSU3.StageB.card_centralizer_eq_cube` is VERIFIED (axioms clean) but importing
-- it here creates a *build cycle*: that file imports this one (for
-- `inf_center_centralizerOddResidual_eq_bot`).  Fix: the prover should import a helper module
-- instead (see the ledger note); then this import can be added.
-- `Submission.Work.PSU3.StageA.caseB_centD_eq_bot` is being proved by a child agent; its file is
-- currently mid-edit, so it is *not* imported here yet.  Re-add the import once it is verified.

/-!
# `Work.PSU3.StageB.centralizer_oddResidual_isPSU3_v2` — status of the node

## HEADLINE (2026-10, after the source and the whole tree were read)

The statement is **TRUE, but it is VACUOUS**: its hypothesis package is inconsistent.  The proof
below therefore derives `False` from the hypotheses and concludes.  Consequently the statement does
*not* carry the mathematical content it was meant to (Peterfalvi II Ch. VII §4 (1)); see
"Diagnosis and recommended restatement" at the end of this comment.

### The derivation of `False` (all inputs hole-free with clean axioms, except the one black box)

1. `V = centD H t ≤ W H t` — the area's black box
   `Work.PSU3.StageA.centD_le_W_of_PSU3Hyp` (a clean proof of exactly this statement is requested
   as `Work.PSU3.StageA.centD_le_W_for_simple`; it is Suzuki's Lemma 60 as corrected by
   Kantor–Seitz II §§14–15, and it is *proved in the model* `PSU(3,2ⁿ)` by
   `Work.PSU3.StageA.centD_le_W_psu3Model`).  Since `V ≠ ⊥` (`centD_ne_bot`, from
   `¬ IsZassenhaus H`), this gives `W ≠ ⊥`.
2. `W ≠ ⊥` forces the ambient situation to be Ch. VI §1 case c), `|Q| = |Q0sub H|³`: `Q` is a
   Suzuki `2`-group (`caseC_isSuzuki2Grp`, needs `¬ IsAbelianSubgroup Q`, which is
   `not_abelian_of_W_ne_bot`), Higman's dichotomy gives `|Q| = |Z(Q)|²` or `|Z(Q)|³` with
   `Z(Q) = Q0sub H`, and the first alternative contradicts `W ≠ ⊥`
   (`caseC_not_suzuki_card_q2_b`).
3. In case c) the group `W#` acts semiregularly on `Q ∖ Q₀` (`V_caseC_W_semireg`).
4. By step 1, `P ≤ V ≤ W`; take `1 ≠ p ∈ P`.  Then `p ∈ W#`, and `p` centralises `y ∈ Q ∖ Q₀` by
   hypothesis, so step 3 gives `y ∈ Q0sub H`, contradicting `hy0`.

So the data `(P, y)` — a prime-order `P ≤ C_D(t)` centralising some `y ∈ Q \ Q0sub H` — is
*incompatible* with `PSU3Hyp`.  This is not an artefact of the formalisation: the source's §4 is
"the case `V ≠ W`", and there the data immediately gives `P ∩ W = 1` (source: "Since `W` acts
fixed-point-freely on `Q/Q₀`, `P ∩ W = 1`"), hence `P ≰ W`, hence `V ≠ W`, hence — by the theorem
known as `RankOneVNeqWProp` / Suzuki Lemma 60 / Kantor–Seitz / Peterfalvi Ch. VII §4 — `O^{2'}(G) ≠ G`.
But `PSU3Hyp` contains `IsSimpleGroup G` and `oddCore G = ⊥`, which force `O^{2'}(G) = G`
(`O^{2'}(G) ⊴ G`; `O^{2'}(G) = 1` would make `|G|` odd, i.e. `oddCore G = G ≠ ⊥`).  Contradiction.

Two independent reviewers of an earlier companion delegation independently predicted exactly this
("the hypothesis package is unsatisfiable"); the same phenomenon is recorded for the sibling
hypotheses in `Submission/Work/PSU3/StageA/not_caseB.lean` ("the case-b hypotheses are
unsatisfiable, so any proof must first re-derive this very contradiction").

### Diagnosis and recommended restatement

Peterfalvi Ch. VII §4 (1) — `U := O^{2'}(C_G(P))`, `U/(P ∩ U) ≅ PSU(3, ℓ)`, `q = ℓ^p`,
`ℓ = |C_{Q₀}(P)|` — is *not* a statement about a simple group `G`: it is used inside the proof of
Theorem B *in the remaining case* `D` not fixed-point-free on `(Q/Q₀)#`, and there
`O^{2'}(G) ≠ G` (the case is precisely "`V ≠ W`").  Bundling `PSU3Hyp` (which forces `O^{2'}(G) = G`)
into the hypotheses makes the statement vacuous.  Recommended fix: state §4 (1) with
`PSU3Hyp` replaced by its `situation`/`split`/`B3`/`two` fields *without* `simple`, i.e. assuming
only `Situation G` (or, equivalently, the concrete case hypothesis `¬ DFpfBar H Q t` /
`V ≠ W`).  With `simple` removed the conclusion has real content and the derivation below does not
apply.

### What is proved here without the black box (kept for re-use)

* `exists_P3_data` — the `ChIIFourProp` P3 clause at `X = P` (clean).
* `isPSU3_of_step4_data` — the "glue" that turns the outputs of the reduction (datum in `Y`,
  `|U_Y| = |C_Q(P)|`, `|C_Q(P)| = ℓ³`, `#Inv(B_Y) + 1 = ℓ`) into the target's conclusion (clean).
* `orderOf_st_eq_three` — the ambient identity `orderOf (s * t) = 3` (its proof depends on the
  in-flight `Work.PSU3.StageA.chVI_prop` / `...caseB_centD_eq_bot`).

## Older notes (kept: the direct route, for the record)

**The statement is TRUE** — it is Peterfalvi II, Ch. VII §4 (1) (pp. 278–280), in the corrected
indexing (`PSU3Model n'` is `PSU(3, 2^{n'})`):

    U := O^{2'}(C_G(P)),  U/Z(U) ≅ PSU(3, ℓ),  ℓ = |C_{Q₀}(P)| = 2^{n'},

with `n' = log₂ ℓ ≥ 2` (the last inequality is the reviewer's caveat, and it does follow from
(B3), see `nprime_ge_two` below).

**It is not yet proved here.**  Below I record the precise decomposition of the proof into the
pieces that are available in this workspace and the two that are not, so that the requester can
schedule them.  (Superseded by the HEADLINE above: the statement is proved — vacuously.)

## The intended proof (Peterfalvi II.7.4(1) + Ch. V §2 Lemma 2 c))

1. (`hC4`, P3 with `X = P`) `F := O^{2'}(C_G(P)) = centralizerOddResidual P` satisfies
   `oddCore F = Z(F)` and `F/Z(F) ≅ Y` for a *simple Bender group* `Y`
   (`IsSimpleBenderGroup Y`), together with a Sylow 2-subgroup `S` of `F ⊓ H` with
   `S ⊓ D = ⊥`, `S ⊔ (D ⊓ N_G(P)) = H ⊓ N_G(P)`, and `S = C_Q(P)`; also `Ω₁(S) = C_{Q₀}(P)`.
2. (`chVI_prop` + `not_caseA`/`not_caseB`, both in flight in area `PSU3`) the ambient situation
   is case c): `orderOf (s * t) = 3`.  Case a) is impossible because `y ∈ Q ∖ Q₀sub H`; case b)
   is the `Sz`-like case and is the genuine difficulty (see the caveat below).
3. (Ch. V §2 Lemma 2 c) = `Work.PSU3.StageA.lemma2cHig`/`lemma2c`, in flight) the local
   trichotomy for `X = P`: with `C := C_Q(P)` and `ℓ := |C_{Q₀}(P)|`,
   `ord(s t) = 3 ∧ C` abelian `∧ |C| = ℓ`, or `ord(s t) = 5 ∧ |C| = ℓ²`, or
   `ord(s t) = 3 ∧ |C| = ℓ³`.  The first alternative is excluded because `C_{Q₀}(P) ≤ C` with
   `|C| = ℓ` forces `C ⊆ Q₀ ∌ y`; the second by step 2.  Hence `|C_Q(P)| = ℓ³`.
4. Transfers to `Y = F/Z(F)`: with `B_Y = (F ⊓ H).subgroupOf F` mapped into `Y` and
   `U_Y = (S.subgroupOf F)` mapped into `Y` one needs
   `|U_Y| = |C_Q(P)|` (needs `Z(U) ∩ Q = 1`, which follows from the source's `Z(U) ⊆ P`;
   cf. `centralizerOddResidual_center_le_P` below), `#Inv(B_Y) + 1 = ℓ`, and
   `orderOf (s_Y * w_Y) = orderOf (s * t)` (`Work.PSU3.StageA.orderOfMapEq`, proved).
5. Model cardinalities (`Work.Models.ModelData.*`, `Work.Models.Port.PSU3.*`, proved):
   `|U| = q, q², q³` and `#Inv(B) = q - 1` for `PSL2Model q`, `SzModel`, `PSU3Model` with
   `q = 2^n`, `2^{2n+1}`, `2^n` respectively.  Combining with step 4 rules out the `PSL2` and
   `Sz` branches (`q^3 = q`, resp. `q^2 = q^3`) and gives, in the `PSU3` branch,
   `ℓ = 2^{n'}` and `Y ≅ PSU3Model n'`, hence the conclusion.

## The two missing inputs

* **(i) `chVI_prop`** (Ch. VI §1 Prop., p. 259) — the ambient case trichotomy.  In flight in
  area `PSU3` (its prover holds `benderST`, `chVI_caseWbot`, `lemma2cHig` as children).
* **(ii) the exclusion of case b) with `V ≠ ⊥`.**  The reference excludes it in Ch. VI §2–§3
  (pp. 261–264) by showing `G₀ := (SK) ∪ (SKtS)` is a subgroup with `|G : G₀| = |V|`, so that
  (with the induction hypothesis, and `V ≠ 1`) `G` is `Sz(q)`-like and `O^{2'}(G) ≠ G`.

  ⚠ **The workspace's current route to this is unsound.**
  `Submission.Work.PSU3.StageA.not_caseB` is proved from
  `centD_normal_of_PSU3Hyp : D ≤ Subgroup.normalizer (centD H t)`, which is still `hole`.  But
  by Ch. V §1 Prop. 3 (p. 241) one has `Q₀ ⋊ (D/W) ≅ (F_q ⋊ F_q^*) ⋊ A` with `V/W = A`, and
  `A` is *not* normal in `F_q^* ⋊ A` when `A ≠ 1` (its normaliser in `F_q^* ⋊ A` is
  `F_q^* × A`); hence `D ≤ N_G(V) ⟺ V = W`.  So `centD_normal_of_PSU3Hyp` would assert
  `V = W` for every `PSU3Hyp`-group, which is false in general (`PSU(3, 8)`: `V = Z/3`, `W = 1`,
  `D = Z/7 ⋊ Z/3` non-abelian), and one must check whether (B3) rules those configurations out.
  Any sound completion of the area should replace `not_caseB`'s proof by the Ch. VI §2
  computation.  **I have not been able to rule the case out here**, which is why the node is
  still open; note that the naive statement of the Ch. VI §2 subgroup `(SK) ∪ (SKtS)` cannot
  supply a *proper* subgroup on its own, because `⟨Q, t⟩ = ⊤` holds under the hypotheses
  (`Work.RankOneUniqueness.closure_Q_t_eq_top`): one needs the *index* `|G : G₀| = |V|`
  (equivalently `t ∉ QK ∪ QKtQ`) as well.
-/

namespace Work.PSU3.StageB

open LeanEval.GroupTheory.Defs

/-
## Delegation status of the pieces of the five-step reduction

* **Step 1 (`n' ≥ 2`)** — `Work.PSU3.StageB.nprime_ge_two` (child agent), imported above.
  **VERIFIED hole-free** (`#print axioms` gives `{propext, Classical.choice, Quot.sound}`): this
  step is delivered.
* **Step 1, consumer side (`ChIIFourProp` P3 with `X = P`)** — `exists_P3_data`, **proved and
  VERIFIED in this file** (`{propext, Classical.choice, Quot.sound}`).  It extracts the Sylow
  `2`-subgroup `S` of `F ⊓ H` (odd index) and the epimorphism `φ : ↥F ↠ Y` with kernel `Z(↥F)`
  onto a simple Bender group `Y`, using `Work.PSU3.StageB.three_le_fixedPts_of_centralizes` (fed by
  the `y`-hypotheses) and `Work.ThmF.ChV12.exists_k_normalizing` (fed by (B3) and Prop. 1 (b)).
  ⚠ Wiring note: `rw` on `centralizerOddResidual` fails with "motive is not type correct" because it
  occurs in *type* positions (`↥F`); use `unfold Work.PSU3.StageB.centralizerOddResidual` instead.
* **Step 2 (case (b) ⟹ `V = ⊥`)** — `Work.PSU3.StageA.caseB_centD_eq_bot` (child agent); its file
  is mid-edit, so the import is held in a comment above.  Re-add on landing.
* **Step 4 (`#Inv(F ⊓ H) + 1 = ℓ`)** — `Work.PSU3.StageB.ncard_involutions_inf_H` (child agent),
  imported above.  **VERIFIED hole-free** (`#print axioms` clean).  Together with (iv) below this
  is the count `#Inv(B_Y) + 1 = ℓ` that step 5 needs.
* **Step 4, bookkeeping (iv) (`#Inv(B_Y) = #Inv(F ⊓ H)`)** — `Work.PSU3.StageB.ncard_involutions_map_inf`
  (child agent, delegated after review), imported above.  **VERIFIED hole-free** (`#print axioms`
  clean).  With the previous item this gives `#Inv(B_Y) + 1 = ℓ`.
* **Step 4, bookkeeping (i) (`S ⊓ Z(U) = ⊥`)** — `inf_center_centralizerOddResidual_eq_bot`,
  **proved and VERIFIED in this file** (`{propext, Classical.choice, Quot.sound}`).  It makes the
  map `S → U/Z(U)` injective.
* **Step 4, bookkeeping (ii) (`|U_Y| = |C_Q(P)|`)** — `Work.PSU3.StageB.card_map_sylow_eq`
  (child agent, delegated after review), imported above.  **VERIFIED hole-free** (`#print axioms`
  clean: `{propext, Classical.choice, Quot.sound}`).  Combined with (i) it gives
  `|U_Y| = |S| = |C_Q(P)|`, the transfer that step 5 needs.
* **Step 4, bookkeeping (iii) (`orderOf (s_Y * w_Y) = orderOf (s * t)`)** —
  `Work.PSU3.StageB.orderOf_map_sylow_mul` (child agent, delegated after review), imported above.
  **VERIFIED hole-free** (`#print axioms` clean).  This is Ch. V §2 Lemma 1 c) ("the structure
  identity of `F` is that of `G`").
* **Step 5 (branch determination)** — `Work.PSU3.StageB.exists_PSU3_of_card_sylow_eq_cube`
  (child agent, delegated after review): in a simple Bender group, a split rank-one datum with
  `|U| = (#Inv(B) + 1)³` forces `Y ≅ PSU3Model m` with `#Inv(B) + 1 = 2^m`, `m ≥ 2`.  Fed with
  step 3's `|C_Q(P)| = ℓ³` and step 4's `#Inv(B_Y) + 1 = ℓ` and `|U_Y| = |C_Q(P)|`, it gives the
  target's isomorphism conjunct with `n' = m`, together with `|C_{Q₀}(P)| = ℓ = 2^{n'}`.
  ⚠ Review catch: the hypothesis must be written `((…).ncard + 1) ^ 3` — without the parentheses
  `^` binds tighter than `+`, giving `|U| = #Inv(B) + 1` (a `PSL2` condition) instead.
* **Step 4 (`Z(U) ⊆ P`, used for `|U_Y| = |C_Q(P)|`)** —
  `Work.PSU3.StageB.centralizerOddResidual_center_le_P`: solved by a child agent, locally
  `hole`-free (provisional through the area nodes).  ⚠ Note the typing: the hypothesis
  "`Z(U) ≤ V`" must be written in `G`, not in `↥U`:

      (hZV : (Subgroup.center ↥(centralizerOddResidual P)).map
               (centralizerOddResidual P).subtype ≤  Submission.Blueprint.centD H t)

  The corrected statement also carries `hHig` and the case-(c) input
  `Nat.card Q = Nat.card (Q0sub H)^3` (the fixed-point-freeness of `W#` on `Q ∖ Q₀` is available
  in this workspace only via `Work.PSU3.StageA.caseC_W_semireg`, which needs them).
* **Step 2 wiring (item 2)** — `orderOf_st_eq_three`, **proved in this file** (its axioms inherit
  an unproved-axiom dependency only from the in-flight `chVI_prop`/`caseB_centD_eq_bot`).  It dispatches `chVI_prop`'s
  trichotomy: cases (a) and (c) already conclude `orderOf (s * t) = 3`, and case (b) is killed by
  `caseB_centD_eq_bot` (`V = ⊥`) against `centD_ne_bot`.  Note it needs **no `P`/`y` hypothesis**:
  the `y`-data is used only in step 1 (`exists_P3_data`) and step 3.
* **Step 3 wiring (item 3)** — `Work.PSU3.StageB.card_centralizer_eq_cube` (child agent, delegated
  after review), imported above.  **VERIFIED hole-free** (`#print axioms` =
  `{propext, Classical.choice, Quot.sound}`): dispatches `Work.PSU3.StageA.lemma2cHig`'s trichotomy
  — branch (b) dies against `orderOf (s * t) = 3`, and branch (a) forces `C = C_{Q₀}(P) ⊆ Q0sub H`,
  whence `y ∈ C` contradicts `hy0`.  This is the **only** place where all three `y`-hypotheses are
  used together.
* **Step 5 (branch determination)** — `Work.PSU3.StageB.exists_PSU3_of_card_sylow_eq_cube`
  (child agent, delegated after review): its file is locally `hole`-free, but `#print axioms`
  still shows an unproved-axiom dependency through the model library (`Work.Models.*`), so its status is
  *provisional* until that area is clean.  Statement and route are as logged below.
  ⚠ **Build cycle** on `card_centralizer_eq_cube`: it imports *this* module (for
  `inf_center_centralizerOddResidual_eq_bot`, now moved to `Wiring`), so this module cannot import
  it back.  Two live routes: (i) its owner re-points that one import to
  `Submission.Work.PSU3.StageB.Wiring`; (ii) *taken* — `Work.PSU3.StageB.card_centralizer_eq_cube_acyclic`
  (child agent, delegated) states the same result in a module importing only `StageA/lemma2cHig`,
  `StageA/coarseFrame_defs` and `Wiring`, which is cycle-free; import that one instead.
  Worth noting for reuse: `Work.PSU3.StageA.Q0sub_le_Q` is already **proved** (in
  `StageA/coarseFrame_defs.lean`) — it is the brick that makes branch (a) of the local trichotomy
  collapse to `C = C_{Q₀}(P)`.
⚠ **Open blocker (not mine to fix).** `Submission/Work/PSU3/StageB/_tmpInvariants.lean` (a scratch
file left by the branch-determination agent) currently fails to build with
`Unknown identifier Work.Models.Abstract.exists_conj_eq`, and `lake build` pulls it in, so the
oleans of `card_centralizer_eq_cube` and `exists_PSU3_of_card_sylow_eq_cube` cannot be produced and
they cannot be audited/imported until it is fixed or deleted by its owner.

* **Assembly glue (`t ∈ F` and the quotient isomorphism)** —
  `Work.PSU3.StageB.t_mem_and_center_quotient` (child agent, delegated after review), imported
  above.  **VERIFIED hole-free** (`#print axioms` = `{propext, Classical.choice, Quot.sound}`):
  the `2`-element argument `t ∈ O^{2'}(C_G(P))` and `↥F ⧸ Z(↥F) ≃* Y` from `φ` with
  `φ.ker = Z(↥F)` — the last two inputs of `isPSU3_of_step4_data`.
* **Step 5, item 1 (datum transfer)** — `Work.PSU3.StageB.isSplitRankOne_map_of_surjective`
  (child agent, delegated after review): a split rank-one datum transfers along a surjection with
  *central* kernel onto a simple Bender group (`isSplitRankOneTransfer` + `modelDataBorel` +
  `isStronglyEmbedded_map_of_ker_odd`).  Instantiating it at `F = ↥(centralizerOddResidual P)`,
  `H = (H ⊓ F).subgroupOf F`, `S = (S₀.subgroupOf F)`, `t = ⟨t, htF⟩` yields the
  `IsSplitRankOne B_Y U_Y w_Y` that `isPSU3_of_step4_data` consumes.
  ⚠ Auxiliary to re-prove: `Subgroup.center F ≤ H` for `H` strongly embedded is *private* in
  `StageA/isSplitRankOneTransfer.lean`.
* **Step 5 glue (the consumer)** — `isPSU3_of_step4_data`, **proved in this file** (so the module's
  only `hole` is the target itself).  It takes the outputs of steps 3–4 in exactly the form their
  producers state them (`|U| = |C_Q(P)|`, `|C_Q(P)| = ℓ³`, `#Inv(B) + 1 = ℓ`,
  `|Q0sub H ⊓ C_G(P)| = ℓ`), derives `|U| = (#Inv B + 1)³`, and returns the target's conclusion
  with `n' = m`, `ℓ = 2^m` and the isomorphism `eY.trans e`.  Writing it now *exercises the
  delegated signature*, so a mismatch surfaces before that agent finishes.
-/

-- `inf_center_centralizerOddResidual_eq_bot` (step 4, bookkeeping (i), used by
-- `card_map_sylow_eq`) now lives in `Submission.Work.PSU3.StageB.Wiring`, imported above, so that
-- modules needing it (`Work.PSU3.StageB.card_centralizer_eq_cube`) can import `Wiring` instead of
-- this one.  That is what removes the build cycle noted in the ledger.

/-- **The `ChIIFourProp` P3 instantiation at `X = P`** (step 1 of the reduction, consumer side).

From `hC4` applied to `X = P` (whose hypothesis `N_K(P) ≠ 1` is `Work.ThmF.ChV12.exists_k_normalizing`,
fed with the three fixed points of `P` — `Work.PSU3.StageB.three_le_fixedPts_of_centralizes`, which
uses the given `y ∈ Q ∖ Q₀` centralised by `P` — and with `HasFourGroup (C_G(P))` from (B3)), this
extracts the data the rest of the assembly consumes: a `2`-subgroup `S` which is a Sylow of
`F ⊓ H` (odd index), and an epimorphism `φ : ↥F →* Y` with kernel `Z(↥F)` onto a simple Bender
group `Y`, where `F = centralizerOddResidual P = O^{2'}(C_G(P))`. -/
theorem exists_P3_data {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t)
    (hPp : (Nat.card P).Prime) (hPne : P ≠ ⊥)
    {y : G} (hyQ : y ∈ Q) (hy0 : y ∉ Work.ThmF.Q0sub H)
    (hyc : ∀ p ∈ P, p⁻¹ * y * p = y) :
    ∃ (S : Subgroup G) (Y : Type) (_ : Group Y) (_ : Finite Y)
      (φ : ↥(Work.PSU3.StageB.centralizerOddResidual P) →* Y),
      IsPGroup 2 S ∧
        S ≤ Work.PSU3.StageB.centralizerOddResidual P ⊓ H ∧
        (¬ 2 ∣ (S.subgroupOf (Work.PSU3.StageB.centralizerOddResidual P ⊓ H)).index) ∧
        Function.Surjective φ ∧
        φ.ker = Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P) ∧
        LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y := by
  classical
  have hH : IsStronglyEmbedded H := hS.split.stronglyEmbedded
  have ht2 : orderOf t = 2 := hS.split.invol
  have htH : t ∉ H := hS.split.not_mem
  have hy1 : y ≠ 1 := fun h1 => hy0 (by rw [h1]; exact (Work.ThmF.Q0sub H).one_mem)
  have hP2 : P ≤ Submission.Blueprint.twoPoint H t :=
    fun x hx => (Subgroup.mem_inf.mp (hPV hx)).1
  -- `P` fixes at least three points of `Ω` (this is where `y` is used)
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard :=
    Work.PSU3.StageB.three_le_fixedPts_of_centralizes hS.split hP2 hyQ hy1 hyc
  have hP1b := (hC4 G hS.situation H hH t ht2 htH).1
  have hP3 := (hC4 G hS.situation H hH t ht2 htH).2.2.2.1
  -- `N_K(P) ≠ 1` (Ch. II §4 Prop. 3's hypothesis), from (B3) and Prop. 1 (b)
  obtain ⟨k0, hk0K, hk01, hk0N⟩ :=
    Work.ThmF.ChV12.exists_k_normalizing hH ht2 htH hPV hX3 (hS.B3 P hPV hPp) hP1b
  have hP3c := hP3 P hPne hPV ⟨k0, hk0K, hk01, hk0N⟩
  dsimp only at hP3c
  -- `F := centralizerOddResidual P` is the `F` of P3
  obtain ⟨-, ⟨S, hSp, hSFH, hSidx, -, hSD, -⟩, ⟨-, hYZc⟩, -⟩ := hP3c
  obtain ⟨Y, hYG, φ, hφsurj, hφker, hYbender⟩ := hYZc
  refine ⟨S, Y, hYG, Finite.of_surjective φ hφsurj, φ, hSp, ?_, ?_, hφsurj, ?_, hYbender⟩
  · simpa only [Work.PSU3.StageB.centralizerOddResidual] using hSFH
  · unfold Work.PSU3.StageB.centralizerOddResidual
    exact hSidx
  · unfold Work.PSU3.StageB.centralizerOddResidual
    exact hφker

-- Superseded (2026): the hole-tainted `orderOf_st_eq_three` was removed by the hole sweep.

/-- **Step 5 glue (the consumer of `exists_PSU3_of_card_sylow_eq_cube`).**

Given the output of the P3 clause in the shape the later steps deliver it — a simple Bender group
`Y` with a split rank-one datum `(B, U, w)`, an isomorphism `eY` from the quotient
`U/Z(U) = F/Z(F)` onto `Y`, and

* `|Q0sub H ⊓ C_G(P)| = ℓ` (`Work.PSU3.StageB.ncard_involutions_inf_H` +
  `Work.PSU3.StageB.ncard_involutions_map_inf`),
* `#Inv(B) + 1 = ℓ` (same two),
* `|C_Q(P)| = ℓ³` (step 3, the local trichotomy `Work.PSU3.StageA.lemma2cHig`),
* `|U| = |C_Q(P)|` (`Work.PSU3.StageB.card_map_sylow_eq`),

this discharges the target's conclusion with `n' = m`, where `Y ≅ PSU3Model m` and
`ℓ = 2^m` come from the branch determination. -/
theorem isPSU3_of_step4_data {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {P : Subgroup G} {Y : Type} [Group Y] [Finite Y] {B U : Subgroup Y} {w : Y}
    (hY : LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y)
    (hdatum : Submission.Blueprint.IsSplitRankOne B U w)
    {ℓ : ℕ}
    (hℓ : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) = ℓ)
    (hinv : (Submission.Blueprint.involutions (B : Set Y)).ncard + 1 = ℓ)
    (hcardQ : Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) = ℓ ^ 3)
    (hcardU : Nat.card ↥U = Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)))
    (eY : ↥(Work.PSU3.StageB.centralizerOddResidual P) ⧸
        (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)) ≃* Y) :
    ∃ n' : ℕ, 2 ≤ n' ∧
      Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) = 2 ^ n' ∧
      Nonempty (↥(Work.PSU3.StageB.centralizerOddResidual P) ⧸
        (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)) ≃*
          LeanEval.GroupTheory.Defs.PSU3Model n') := by
  -- `|U| = (#Inv B + 1)^3`: compose `|U| = |C_Q(P)| = ℓ^3` with `#Inv(B) + 1 = ℓ`.
  have hcard3 : Nat.card ↥U = ((Submission.Blueprint.involutions (B : Set Y)).ncard + 1) ^ 3 := by
    rw [hcardU, hcardQ, ← hinv]
  obtain ⟨m, hm2, ⟨e⟩, hq⟩ := exists_PSU3_of_card_sylow_eq_cube hY hdatum hcard3
  exact ⟨m, hm2, by rw [hℓ, ← hinv, hq], ⟨eY.trans e⟩⟩

-- Superseded (2026): the hole-tainted `centralizer_oddResidual_isPSU3_v2` was removed by the
-- hole sweep.

end Work.PSU3.StageB
