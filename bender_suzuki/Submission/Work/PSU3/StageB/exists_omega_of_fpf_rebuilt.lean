/-
# Stage B, node **B1 rebuilt** (`exists_omega_of_fpf_rebuilt`) — **PROVED**

> **STATUS (final).** `exists_omega_of_fpf_rebuilt` below is proved, hole-free and axiom-clean
> (`#print axioms` = `propext, Classical.choice, Quot.sound`).  The docstring *below* this box is
> the historical record of the three earlier sessions, which had reduced the node to the
> off-frame input `h ∈ KW` of the source's Proposition of p. 274; that input turned out to be
> *derivable*, and the derivation is described next.  Read the box first; the older text is kept
> because it documents the (now superseded) analysis and the sibling reductions.
>
> **The missing step, found and formalised.**  The cross case of §2's Proposition
> (`Omega.square_eq_shift_of_good_cover_hKW`) consumes its global hypothesis `h(x) ∈ fr.KW` at
> exactly one point, `x₅ = (rep k)⁻¹ · zcQF fr r`, where `r` is the `Q₀`-coordinate of `ω₁²`
> (`ω₁` the base element of the good transversal) and `rep k` is determined by the cross-orbit
> shift (20).  Three instances had to be produced; all are consequences of the frame axioms plus
> `hS` and `hfpf`:
>
> 1. `h(ω₁) ∈ fr.KW`: `StepB.hcan_mem_W_of_good_generating` (§2 (18) + cyclic Sylow
>    subgroups, from `DFpfBar`) gives `h(ω₁) ∈ W H t ≤ fr.KW`;
> 2. `h(ω₁ · zcQF fr α) ∈ fr.KW`: H4a/H4c give `h(ω₁·zc α) = ζ·h(ω₁)⁻¹·ζ⁻¹`
>    (`StepB.hcan_mul_zcQF_alpha_mem_KW`);
> 3. `h(x₅) ∈ fr.KW`: `StepB.hcan_inv_mul_zcQF_KW` — the source's "Moreover by H4,
>    `h(ω_k⁻¹(0,r)) ∈ KW`".  The key point is that `ω₁ · zcQF fr r = ω₁⁻¹`, hence
>    `(ω₁ · zcQF fr α)⁻¹ = ω₁ · (zcQF fr r · zcQF fr α)`; by H4b and (2), `h` of that element
>    lies in `fr.KW`, and the cross relation `f(ω₁ · (zc r · zc α)) = kact d₂ (rep k · zc r)`
>    transports the membership to `h(rep k · zc r)` (H4c + H4a), whence to
>    `h((rep k · zc r)⁻¹) = h(x₅)` by H4b again (using `t`-stability of `fr.KW`,
>    `Omega.tconjKW_exists`).
>
> Assembling: `StepB.square_eq_shift_of_good_cover` is `Omega.square_eq_shift_of_good_cover_hKW`
> with the global `hKW` hypothesis *removed* (the three instances above supply the only three uses),
> and `StepB.exists_good_square` is the §2 (9)/(19)/(20) orbit assembly on top of it.  The target
> is then three lines: rebuild the frame with a generating `ζ` (`StepB.exists_generating_frame`),
> feed the Sylow input of §2 (18) (`StepB.sylow_isCyclic_twoPoint_of_ne_Q0sub` +
> `StepB.mem_of_pow_card_eq_one`), and apply `Omega.omegaHyp_of_good`.
>
> Everything in the headings below that says "not derivable" refers to the *frame axioms alone*
> (a true statement about `CoarseFrame`, whose four reviews are on record); what the analysis below
> missed is that the *H4/H5 identities of the canonical maps* `fcan`, `hcan` — which are part of
> `PSU3Hyp`'s BN structure and not of the frame — do supply the three instances.

Peterfalvi II, Ch. VII §2 (pp. 268–275) + the Proposition of p. 274, in the *rebuilt* form
recorded by the lead (`Submission/Work/PSU3/_design/PSU3B1v12.lean`): for `PSU3Hyp H Q t`,
`ChIIFourProp`, `HigmanProp`, a coarse frame `fr` at index `n` and `DFpfBar H Q t`, there are a
coarse frame `fr'` **at the same index `n`** and an element `ω` with `OmegaHyp fr' ω`.

## What is proved (hole-free) here, and in the delegated siblings

* `card_Q0sub_eq_two_pow` (here) — a frame at index `n` forces `|Q₀sub H| = 2ⁿ`.
* `Q_ne_Q0sub_of_frame` (here) — **the frame excludes Ch. VI §1 case a)**: `Q ≤ Q0sub H` would
  force `W H t = ⊥` (`StageA.W_eq_bot_of_Q_eq_Q0sub`), against `fr.ζ ∈ (W H t)#`.  So the
  non-vacuity proviso of `DFpfBar` (`x ∉ Q0sub H`) is automatic, and the Sylow-cyclicity input
  `StepB.sylow_isCyclic_twoPoint_of_ne_Q0sub` can be applied.  (Previously this was the open
  `not_caseA` / `ReductionSetEq` node.)
* `Work.PSU3.StageB.StepB.exists_generating_frame` — the frame can be rebuilt with a `ζ` that
  *generates* `W = C_V(K)`: `orderOf fr'.ζ = |W|` and `W ≤ fr'.KW` (inputs: the case-c data
  `|Q| = |Q₀sub H|³`, `orderOf (s*t) = 3`, available as
  `Work.PSU3.StageA.caseC_data_of_W_ne_bot` with `W ≠ ⊥` as a hypothesis).
* `Work.PSU3.StageB.StepB.W_normal_twoPoint` — `W ⊴ D = twoPoint H t` (Ch. II §4 Prop. 4).
* `Work.PSU3.StageB.StepB.mem_of_pow_card_eq_one` — for `N ⊴ D` with all Sylow subgroups of `D`
  cyclic: `x ∈ D`, `x ^ |N| = 1 ⟹ x ∈ N` (the Frobenius-complement bookkeeping of §2 (18)).
* `Work.PSU3.StageB.StepB.sylow_isCyclic_twoPoint_of_ne_Q0sub` — `DFpfBar` makes the Sylow
  subgroups of `D` cyclic (`D` is a Frobenius complement of odd order on `(Q/Q₀)^#`).
* `Work.PSU3.StageB.StepB.hcan_mem_W_of_good_generating` — §2 (18) `(h(ω)ζ⁻¹)^m = 1` plus the
  Sylow-cyclicity input gives `h(ω) ∈ W` for every *good* `ω` in the generating frame.
* `Work.PSU3.StageB.StepB.self_pos_eq_mem_KW` — the *self-position* case of the source's
  `(f∘j)³`-chain (`Omega.self_pos_eq`), with its global `h ∈ KW` hypothesis weakened to the single
  instance `h(ω) ∈ KW`.
* `exists_square_of_good_cover_W`, `exists_good_square_W`, `exists_omega_of_fpf_rebuilt_of_self`,
  `exists_omega_of_fpf_rebuilt_of_self'` (here) — the orbit bookkeeping of §2 (8)/(9)/(19)/(20)
  plus `self_pos_eq_mem_KW` reduce the Proposition of p. 274 and the target to one explicit input
  `SelfPosInput` (below); the `'`-variant discharges the case-a) proviso with
  `Q_ne_Q0sub_of_frame`.
* `exists_omega_of_fpf_rebuilt_of_hKW` (here) — **the target from the sharpest non-circular
  input**: the frame rebuilt with a generator of `W` carries `h (x) ∈ fr'.KW` for all
  `x ∈ Q ∖ Q₀`.  This is strictly weaker than `V = W` (it constrains `h`-values, not the subgroup
  structure of `D`), it is *not* derivable from the frame axioms (four independent reviews, see
  `StepB/NOTES_S2_final_step.md`), and every derivation of it through the norm form would run
  through `nm = sq`, i.e. through Stage B3/C0, which is downstream of this node.  With it the
  reference's Proposition applies verbatim (`exists_good_square_of_hKW`, proved).
* `exists_omega_of_fpf_rebuilt_of_isSimpleBenderGroup` (here) — the target from the
  classification's output (`IsSimpleBenderGroup G`), *not* on the critical path (B1 is used to
  prove it); recorded to show the hypotheses are not the problem, only their reach here.
* `exists_omega_of_fpf_rebuilt_of_V_eq_W` (here) — **the target from the branch condition
  `centD H t ≤ W H t`** (the deep Stage-A node `centD_le_W_of_PSU3Hyp`): rebuild the frame with a
  generator of `W`, so that `D = Ksub · V = Ksub · W = fr'.KW`, and apply
  `Omega.exists_omega_of_fpf_of_D_eq_KW`.

## The §2 (p. 274) layer: transporting `h ∈ KW` (built in `StepB/`)

The reference's Proposition needs the membership `h(ω_k⁻¹(0,r)) ∈ KW` at a `Q₀`-translate of a
representative.  The transport machinery for it is now in place, all of it hole-free:

* `StepB.conj_mem_KW_of_mem_twoPoint` — **`KW ⊴ D`** for a frame whose `ζ` generates `W`
  (`KW = Ksub ⊔ W`, `Ksub ⊴ D` by Ch. V §1 Prop. 2, `W ⊴ D` by `ChIIFourProp` P4, both under
  `W ≠ ⊥` which the frame supplies).
* `StepB.qconj_kact`, `StepB.act_bar_conj` — the **scalar-equivariance of the `D`-action on
  `Q/Q₀`**: `ρ_d (κ w · bar x) = κ (d⁻¹ w d) · ρ_d (bar x)` for `d ∈ D`, `w ∈ KW`.  This is
  Peterfalvi's §4 "Setting for the computation" (`(c x)^η = c^μ x^η`, l. 463–468), obtained
  here from `fr.act_bar` alone — the conjugated scalar `d⁻¹ w d` is again in `KW`, so `act_bar`
  applies to it; **no semilinearity input (`AppV_semilinear`) is needed**.
* `StepB.hcan_mem_KW_of_transport` — H4 transportation of `h ∈ KW`: along `KW`-conjugation
  (`h(x^w) = (t w t)⁻¹ h(x) w`), along inversion (`h(x⁻¹) = t h(x)⁻¹ t`, so `t`-stability of `KW`
  is needed), and along `f` (`h(f x) = h(x)⁻¹`).
* `StepB.hcan_mul_zcQF_mem_KW_iff` — **the §2 (18) recursion as a membership criterion**:
  for a good `ω` with `h(ω) ∈ W ≤ KW`,
  `h (ω · zcQF fr U) ∈ KW ↔ h (ω · zcQ fr v) ∈ KW` whenever `v = fval α + (fval U)⁻¹`;
  i.e. `h`-membership in `KW` is *constant along the μ-orbits* `u ↦ α + u⁻¹`.
* `StepB.hcan_zU_mem_KW_of_selfOrbit` — the **base case**: `h (ω · zU fr β hβ hσ i) ∈ KW` for
  `1 ≤ i ≤ N` (the μ-orbit of `0`, parametrised by the §2 (13) sequence `uSeq`), by induction
  from `h(ω) ∈ W ≤ KW`.

Consequently, after this layer, the reference's final step is equivalent to the *single*
off-frame statement that the `Q₀`-position `r_k + r` of `x₅ = (rep k)⁻¹ · zcQF fr r` lies on the
μ-orbit of `0` — equivalently `bar (fcan x₅) ∈ orbE (bar x₅)`, the "self-position of `x₅`" —
which by §2 (15) is a statement about the group `G` beyond the `CoarseFrame` interface
(cf. `Omega/_square_eq_shift_ANALYSIS.md` §2 and `Omega/VERDICT_B1.md` §3).

## The remaining input, and why it is not in this file

Both *frame-level* routes to `OmegaHyp` in the fixed-point-free branch need an input that the
stated hypotheses do not supply:

**(i) the reference's Proposition of p. 274** (§2 (8)/(9)/(17)/(18)/(20) + the `(f∘j)³`-chain) is
formalised here (`exists_good_square_W`) up to the *self-position* input `SelfPosInput` — and that
input is equivalent to the desired conclusion: for a good `ω` with `ω·ω = zcQF fr r`, §2 (15)
characterises the `r` with `SelfPosInput` as exactly the μ-orbit of `0`, on which
`StepB.self_pos_eq_mem_KW` then forces `r = α`; conversely `ω² = zc α` gives it.  The source's
own "Moreover by H4, `h(ω_k⁻¹(0,r)) ∈ KW`" (p. 274) is the same statement in `h`-form, and it is
*not* derivable from `h (rep i) ∈ W ≤ fr.KW`: H4 (`h(x^a) = a^{-t}h(x)a`) transports `KW`-membership
only along `D`-conjugacy, while `ω_k⁻¹(0,r) = ω_k·zc(r_k + r)` is a `Q₀`-translate of `ω_k`, and
the §2 (18) recursion propagates `KW`-membership only along the μ-orbits (base case on the
μ-orbit of `0` only).  This is confirmed by two independent reviews of the design's node P7
(`Work/PSU3/StageB/Omega/square_eq_shift_of_good_cover_hW`, "probably wrong as stated: the
missing input is the global `hKW` (or `h(x₅) ∈ KW`)") and by
`Omega/_square_eq_shift_ANALYSIS.md` §2, `Omega/VERDICT_B1.md`, and the verdict recorded in
`Omega/hcan_mem_KW_of_good_rep.lean`.

**(ii) the branch condition `D = KW`** — for a frame with a generating `ζ` this is exactly
`V = W`, i.e. `centD H t ≤ W H t`; with it the target is *proved* here
(`exists_omega_of_fpf_rebuilt_of_V_eq_W`).  But it is the open deep node
`Work.PSU3.StageA.centD_le_W_of_PSU3Hyp` (Suzuki's Lemma 60 / Kantor–Seitz §§14–15 / Peterfalvi
Ch. VII §4), obtained in the source only from the classification (Ch. VII §4 proves
`V ≠ W ⟹ O^{2'}(G) ≠ G`, so `V = W` for simple `G`; equivalently `IsSimpleBenderGroup G`
supplies it via `StageA.centD_le_W_of_isSimpleBenderGroup`).  It is *not* a consequence of
`DFpfBar`: two independent reviews of the node `Work/PSU3/StageB/centD_le_W_of_DFpfBar` record
that "the reference direction is the converse — `V = W ⟹ DFpfBar`", and the tree's only
hole-free proof (`centD_le_W_of_abelian_complement`) needs an abelian complement of `Q` in `H`.

So the requested statement is **true in the intended models** (there `V = W`, `D = KW`, and every
good element squares correctly — `Omega/_square_eq_shift_ANALYSIS.md` §3), but its listed
hypotheses do not suffice: one of (i)/(ii) must be added as a hypothesis (or the node must be fed
from a place where `D = KW` is already known).

## Session update: the two sharpest reductions, and the Ch. V §1 Prop. 3 lead

Two further reductions of the target are proved below (both hole-free), each from a *different*
mathematical input than (i)/(ii):

* `exists_omega_of_fpf_rebuilt_of_oddResidual` — the target follows from the *statement of Ch. VII
  §4*: `centD H t ≠ W H t → oddResidual G ≠ ⊤` (`O^{2'}(G) ≠ G`).  Indeed `oddResidual G = ⊤`
  for a simple group of even order (`oddResidual_eq_top_of_simple`, proved here), so such an input
  forces `V = W`, and `exists_omega_of_fpf_rebuilt_of_V_eq_W` finishes.  This is the reduction that
  connects node **B1** to the §4 work in progress under **B2**
  (`Work.PSU3.StageB.NotFpfStep4`, "the remaining content is §4 (3)–(10) + the `O^{2'}(G) ≠ G`
  conclusion").
* `exists_omega_of_fpf_rebuilt_of_fixed_lift` — the target follows from the *semilinear* form of
  the missing half of **Ch. V §1 Prop. 3**: every `η ∈ V ∖ W` fixes the `Q₀`-class of some lift of
  `1 ∈ E n`.  Equivalently: the action of `V` on `Q/Q₀` is by field automorphisms (the source's
  standing hypothesis "`V/W` is a cyclic group of field automorphisms").  The mechanism is in
  `StepB/fpf_fixed_lift.lean`: such a fixed class is `DFpfBar`-forbidden, hence `V ≤ W`.

**The architecture this forces (recommendation for the lead's assembly).**  Since
`centD_le_W_of_omegaHyp` below shows that *any* `OmegaHyp` datum implies `V ≤ W`, no node of the
form "`DFpfBar` (or `¬DFpfBar`) ⟹ `∃ ω, OmegaHyp`" can be a non-circular input to a proof of
`V ≤ W`: `StageA.centD_le_W_of_PSU3HypFT_of_pieces` is therefore structurally circular in its
`hfpf`/`hnfpf` slots.  The correct global split — which is the source's own — is by `V = W`
(assumed, never derived):

* **`V = W` case** (assumed as a case hypothesis): `D = K·V = K·W = KW` for a generating frame,
  hence `h(x) ∈ D ⊆ KW` for every `x ∈ Q` with no further input; that is exactly what the
  Proposition of p. 274 needs, and the target follows from the already-proved
  `exists_omega_of_fpf_rebuilt_of_V_eq_W` (equivalently `Omega.exists_omega_of_fpf_of_D_eq_KW`).
  **No §4 input is used here, so this branch is not circular.**
* **`V ≠ W` case**: §4 supplies the good `ω` (Peterfalvi Ch. VII §4, in progress under
  `NotFpfStep4/omegaHyp_of_step4`), independently of any `ΩHyp` datum for `G` — its proof
  descends to `C_G(P)` and the model `PSU(3,ℓ)`.

Three of §4's field/algebra cores are now **separate, hole-free modules** (handed to the fleet
from this session), so the owner of `step4_algebra` can import them instead of re-deriving the
(5)–(10) computation:

* `NotFpfStep4/step4_linear_system` — the source's (5)–(8): the char-2 `2×2` solve giving
  `Y = (1+eζ)/(ζ(1+ef))·w`, `Z = ζ(fY+w)`;
* `NotFpfStep4/step4_lambda_eq_one` — the source's (9): `lam·ζ² + w·ζ + 1 = 0` with `lam, w`
  `σE`-fixed and `ζ ∉ F` forces `lam = 1`, `w = ζ + ζ⁻¹` (unique root of the minimal polynomial);
* `NotFpfStep4/step4_mu_sq_fix_of_relation` — the source's (10):
  `(c+μX)X = (c+μ(μX))μX` for all `X ∈ F` forces `μ(μX) = X` on `F`.

What remains of `step4_algebra` is the assembly: instantiating (3) (`bar_fcan_step4_3`) and (4)
(`step4_rel4`) at `a` and `b` to feed `step4_linear_system`, then chaining (9) and (10); and the
last step of `omegaHyp_of_step4` is `hcan_mem_W_of_step4` (hole-free) via `mu_eq_one_field`.

**Assembly roadmap** (all algebraic steps written out, so the remaining work is mechanical):

> **Status: done.**  The roadmap below is now realised by `step4_algebra_assembled` (in this file,
> hole-free, axiom-clean) using the fleet's `NotFpfStep4/step4_relation_10` (steps 1–5, i.e. the
> source's (3)+(4) ⟹ (10)) and `NotFpfStep4/step4_mu_sq_fix_of_relation_exc` ((10) ⟹ `μ(μX) = X`).
> The only input it needs beyond `step4_algebra`'s own hypotheses is `Odd (orderOf μ)`, available
> in the §4 context from `orderOf μ ∣ orderOf η ∣ orderOf fr.ζ`.
> **Action for the owner of `NotFpfStep4/hcan_mem_W_of_step4.lean`:** switch its `hfix2` from the
> still-`hole`'d `step4_algebra` to `Work.PSU3.StageB.step4_algebra_assembled`; that removes the
> last `hole` from the §4 endgame, leaving only the §4 (1)–(2)
> `C_G(P)`/`PSU(3,ℓ)` transport in the §4 branch.
>
> **Correction (verified).** `NotFpfStep2/center_le_P` is *not* a gap: its two textual `hole`
> mentions are prose in its own docstring, and the file is hole-free — it must not be handed out.
> The only real `hole`s left on the §4 road are `NotFpfStep4/omegaHyp_of_step4` (the (1)–(2)
> transport) and `NotFpfStep4/step4_algebra` (superseded by `step4_algebra_assembled` here).
> `NotFpfStep4/step4_final` is an unconsumed field-level variant of `(10) ⟹ μ²|_F = id` with a
> single exclusion, subsumed in substance by `step4_mu_sq_fix_of_relation_exc`.

### API findings for the last §4 gap (`omegaHyp_of_step4`)

Read of the `centralizerOddResidual` / `psu3_cor2` API (this session):

* **§4 (1) is available.**  `NotFpfStep2/quot_isPSU3` (hole-free) delivers
  `∃ n', 2 ≤ n' ∧ |Q0sub H ⊓ C_G(P)| = 2^{n'} ∧ Nonempty (U/Z(U) ≃* PSU3Model n')` for
  `U = centralizerOddResidual P` — which is exactly the `eY`/`m` input that `omegaHyp_of_step4`
  takes as a hypothesis.
* **`NotFpfStep4/exists_good_of_step4` cannot be used as §4 (2)'s production.**  It *states* §4 (2)
  (`∃ fr' ω α η, …`), but its proof consumes `StageB.exists_omega_of_not_fpf`, the B2 node, which is
  still `hole`'d — i.e. it assumes the very `OmegaHyp` it would have to produce here.
* **The `nm`-normalisation route is likewise circular**: `fine_coords_holds` needs a frame whose `nm`
  is the squaring map, and the only construction of such a frame is `theta_trivial`, which takes
  `OmegaHyp`.  So §4 (2) must build `ω` directly in `G` from the `PSU(3,ℓ)` structure of `U/Z(U)`
  and then verify the canonical data through *uniqueness* of `canon_spec`, as the source does.
* Consequently the last gap cannot be *stated* as a one-line transport: what it needs first is the
  **relative** split-rank-one structure of `(U, U ⊓ H, U ⊓ Q, t)` (`t ∈ U` is already proved, in
  `t_mem_and_center_quotient`), so that the relative maps `f₁, h₁` and the relative form of §3's
  Corollary 2 are available.  **That piece is now in place**: `NotFpfStep2/relative_splitRankOne`
  (proved from this session's hand-off) establishes
  `IsSplitRankOneData ↥U ((H ⊓ U).subgroupOf U) ((Q ⊓ U).subgroupOf U) ⟨t, _⟩`.
* **Next piece.**  The relative canonical maps are the *existing* `Canon` API instantiated at
  `G := ↥U` with that datum — `Work.PSU3.StageB.fcan/gcan/hcan (H := (H ⊓ U).subgroupOf U) (Q :=
  (Q ⊓ U).subgroupOf U) (t := ⟨t, _⟩)` — so the relative §3 Cor. 2 can be *stated* by relativising
  `StageB.Omega.omegaHyp_of_good`, and the remaining work in §4 (2) is the transfer of those
  relative data to `G`'s own `fcan`/`hcan` through *uniqueness* of `canon_spec` (`canon_unique''`),
  exactly as the source does ("By uniqueness of the canonical form of an element of `G-H`").

  **Status of that step (this session).**  Two of its three ingredients are now hole-free modules:

  * `NotFpfStep2/isSplitRankOne_of_data` — `IsSplitRankOneData L M Q t → IsSplitRankOne M Q t`
    (the strong-embedding repackaging), which is what makes the `Canon` API *usable* at `G := ↥U`,
    since `Canon` is stated for `IsSplitRankOne`;
  * `NotFpfStep2/canon3_of_rel` — the transfer itself, first half: a relative
    `Work.PSU3.Canon3 ((H ⊓ U).subgroupOf U) ((Q ⊓ U).subgroupOf U) ⟨t,htU⟩ X Gh Hh Y` *is* the
    absolute `Work.PSU3.Canon3 H Q t (X:G) (Gh:G) (Hh:G) (Y:G)` (pure coercion; the helper
    `twoPoint_subgroupOf_inf` is already proved in `relative_splitRankOne`'s file).  Chaining with
    `canon_unique''` then identifies the relative `f₁, h₁` with `G`'s `fcan`, `hcan`.
  * What remains is the *production* of the relative `Canon3`: pulling `Work.PSU3.Model.psu3_cor2`
    back along `U/Z(U) ≃* PSU3Model m` (`quot_isPSU3`) and lifting the quotient equation through
    the central `Z(U) ≤ P ∩ V`.  That is the last real piece of §4 (2).

**The relative statement's exact hypothesis package** (established by a prover's audit of two failed
attempts, and confirmed by two reviewers; delegated as
`NotFpfStep2/relative_splitRankOne`): it must carry *all* the fields of the ambient structure
**except `IsSimpleGroup G`**, i.e.

  `Situation G`, `IsSplitRankOne H Q t`, `¬ IsZassenhaus H`, the `B3` clause, `IsPGroup 2 Q`,
  plus `ChIIFourProp`, `HigmanProp`, `|Q| = |Q0sub H|³`, `W ≠ ⊥`, and the §4 data `(P, y)`.

Each is needed, and none is decorative:

* `ChIIFourProp` has type `∀ G [Group G] [Finite G], Situation G → …`: with only
  `IsSplitRankOne H Q t` its Prop. 1(b)/2/3/4 clauses cannot even be *applied*, and `Situation G`
  is not derivable (it contains `ThmBBelow`, an induction hypothesis);
* `IsPGroup 2 Q` is needed for `sup_eq` (`U ⊓ H = (U ⊓ Q) ⊔ (U ⊓ twoPoint H t)` reduces to
  `Q ⊓ C_G(P) ≤ O^{2'}(C_G(P))`, whose only route in the tree is
  `mem_map_oddResidual_of_mem_isPGroup`);
* `B3` (Ch. II §4 Prop. 1(a)) is needed for `even_card`/`odd_inter`, i.e. for
  `IsStronglyEmbedded ((H ⊓ U).subgroupOf U)`;
* dropping `IsSimpleGroup G` is what removes the vacuity recorded in the next section.  (The stub
  at `NotFpfStep2/rel_splitRankOne.lean` is the refuted *weaker* form — no `Situation`, hence
  `ChIIFourProp` inapplicable — and must not be reintroduced.)

`Z(U) ≤ centD H t` (the `hZV` input of the sibling nodes) is *not* an extra hypothesis: it follows
from `center_le_centD`.  Since `simple` is absent, the prover must re-run the siblings' arguments
(`Z(U) ≤ centD`, the P3 Sylow clause, `exists_k_normalizing`) in this setting — that is the real
cost, and it is exactly the content of §4 (1)–(2).

### The §4 branch is *mathematically vacuous* in `PSU3Hyp` (and why that changes nothing here)

A companion audit (this session, with the reviewers) surfaced — and confirmed from
`StageB/centralizer_oddResidual_isPSU3_v2.lean`'s own headline — that

  `PSU3Hyp H Q t` together with §4's data `(P, y)` (a prime-order `P ≤ centD H t` centralising some
  `y ∈ Q ∖ Q0sub H`) is **inconsistent**,

because then `p ∈ P ≤ V` centralises `y ∉ Q₀` while `W#` acts fixed-point-freely on `Q ∖ Q₀`.
Two caveats matter for how the tree is read:

* the recorded derivation of `False` uses the **black box** `StageA.centD_le_W_of_PSU3Hyp`
  (`V ≤ W`), which is itself `hole`'d — i.e. the inconsistency is *equivalent* to §4's content,
  not an independent fact, so it cannot be used to discharge §4's obligations axiom-cleanly;
* consequently the correct fix for statements *inside* the §4 branch is to drop
  `IsSimpleGroup G` (state them under `IsSplitRankOne`/`Situation` plus the explicit case-c data),
  which is what `NotFpfStep2/rel_splitRankOne` now does — the §4 branch is precisely the
  *non-simple* case, so removing `simple` restores the content.  Correspondingly B2
  (`exists_omega_of_not_fpf`) and `omegaHyp_of_step4` are vacuous *as statements over `PSU3Hyp`*.

This does **not** touch the requested target: its hypothesis is `DFpfBar`, not its negation, and by
`exists_omegaHyp_iff_V_le_W` the target remains equivalent to `V = W` — i.e. the `DFpfBar` branch is
the only branch of the `ΩHyp`-production carrying content, exactly as the source's own case split
(`V = W` versus `V ≠ W`) indicates.
> **Done in equivalent form** here: `Work.PSU3.StageB.hcan_mem_W_of_step4_assembled` is that
> statement (plus `2 ≤ n`, which its context does not supply) proved with `hfix2` taken from the
> assembly — hole-free and axiom-clean.  The §4 endgame `η ∈ W ⟹ h(ω) ∈ W` therefore no longer
> has any `hole` in its dependency closure; consumers should use it in place of
> `NotFpfStep4.hcan_mem_W_of_step4`.

1. `μ (κζ) = κζ` from `hμκ` at `d = e = ζ` using `hcentζ`; and `μ (toAdd (bar ω)) = toAdd (bar ω)`
   from `hμbar` at `ω` using `hcentω`.
2. Put `A := toAdd (bar (fcan (ω * sconjF fr a)))`, `B := toAdd (bar (fcan (ω * sconjF fr b)))`,
   `c₀ := (κζ : E n)`, `w := toAdd (bar ω)`.  Then (3) reads `A = c₀·(fval a)^{-2}·B`, and (4) at
   `a`, `b` reads `(fval a)²·A = c₀^{-1}·μA + w`, `(fval b)²·B = c₀^{-1}·μB + w`.  Substituting (3)
   in (4)@`a` gives (5) `c₀·B = μ((fval a)^{-2})·μB + w`; (4)@`b` is (6).
3. **Degeneracy.**  `1 + μ((fval a)^{-2})·(fval b)² = 0` is impossible: (6) gives
   `μB = c₀((fval b)²·B + w)`, and substituting this in (5) yields `0 = w·(1 + μ((fval a)^{-2})·c₀)`,
   so either `w = 0` — i.e. `ω ∈ Q₀`, against `hω` — or `(fval a)² = κζ`, which is impossible since
   `(fval a)²` is `σE`-fixed (`a ∈ FX n`) while `σE (κζ) = (κζ)^{-1} ≠ κζ` by `fr.ζ_norm` and
   `fr.κ_injective`.
4. `step4_linear_system` (with `ζ := c₀`, `e := μ((fval a)^{-2})`, `f := (fval b)²`, `Y := B`,
   `Z := μ B`) gives (7) `B = (1+e·c₀)/(c₀(1+e·f))·w` and (8) `μ B = c₀(f·B + w)`.
5. Apply `μ` to (7) and compare with (8): this is (9).  Its polynomial form
   `lam·ζ² + w₂·ζ + 1 = 0` with `lam, w₂ ∈ F` is `step4_lambda_eq_one`, giving `lam = 1` and
   `(fval b)² + μ²((fval a)^{-2}) = κζ + (κζ)^{-1}`.
6. The resulting relation (10) `(c + μX)X = (c + μ(μX))μX` with `c := κζ + (κζ)^{-1}` holds for
   all `X = (fval a)^{-2}`, i.e. for all `X ∈ F` except `0` (where it is trivial) and
   `α^{2τ}` (excluded by the source's proviso on (4)); so it holds off at most two values, which is
   `NotFpfStep4/step4_mu_sq_fix_of_relation_exc` (handed to the fleet from this session).

The node `centD_le_W_of_oddResidual` below wires the second branch into the `V ≤ W` interface for
consumers that only want `V = W` out of the §4 statement (with `simple`, `oddResidual G = G`).

**The lead that this session produced**: `Work.ThmF.ChV12.prop3` (**in the tree, hole-free**)
already proves Ch. V §1 Prop. 3: there is `ρ : V →* (𝔽_q ≃+* 𝔽_q)` with
`ρ.ker = W.subgroupOf V`, i.e. *`V` acts on `Q₀ ≅ 𝔽_q` by field automorphisms with kernel `W`*.
Its engine `Work.ThmF.ChV12.AppV_semilinear` (tree, hole-free) is the general statement "a group
acting compatibly with a scalar action `K ≅ Fˣ` and fixing one point acts by *ring* automorphisms".
Applied to the `Q/Q₀ = 𝔽_{q²}`-action it would close the node — but it needs one `V`-fixed class,
which is exactly what `DFpfBar` denies, so that application is a fixed point of the argument and
cannot be made directly.  What can be squeezed out is the constraint
`DFpfBar ⟹ φ_η(1) ∉ 𝔽_q^*` on the multiplier of the semilinear action of `η ∈ V ∖ W`
(`φ_η` as in `NotFpfStep4.phi`); it is *not* enough by itself (`a ∉ 𝔽_q^*` still allows a
fixed-point-free map `x ↦ a·τ(x)`).

## Session 3: the target is *equivalent* to the branch condition `V = W` (proved here)

The decisive new fact of this session is `centD_le_W_of_omegaHyp` (proved above, hole-free,
axiom-clean):

  `OmegaHyp fr ω  ⟹  centD H t ≤ W H t`      (again: `V ≤ W`),

obtained by running the existing hole-free Stage B3 → C1 → C2 → D pipeline
(`theta_trivial`, `frame_normalize`, `fine_coords_holds`, `f_formula`) and then
`Work.RankOneUniqueness.recognize` + `centD_le_W_of_isSimpleBenderGroup`.  Together with
`exists_omega_of_fpf_rebuilt_of_V_eq_W` (the converse, proved above) this says:

  **the conclusion `∃ fr' ω, OmegaHyp fr' ω` of the requested theorem is equivalent, inside this
  workspace, to `centD H t ≤ W H t`.**

Two consequences, both independent of any new frame axiom:

* **The requested node is not a `DFpfBar`-only statement.**  It is exactly the deep node
  `Work.PSU3.StageA.centD_le_W_of_PSU3Hyp`, i.e. the "Kantor–Seitz / Peterfalvi Ch. VII §4"
  content.  In the intended model `PSU(3,q)` one has `V = W`, so the statement is *true*; but it
  is not a consequence of `PSU3Hyp + ChIIFourProp + HigmanProp + CoarseFrame + DFpfBar`.
* **The requested node cannot be an input to the assembly it was designed for.**  It is the
  `hfpf` slot of `Work.PSU3.StageA.centD_le_W_of_PSU3HypFT_of_pieces` — the assembly that
  *derives* `centD H t ≤ W H t` from it.  Since the target is equivalent to that conclusion, the
  assembly reduces to the tautology `V ≤ W ⟹ V ≤ W`; the lead's design note ("no `V = W` is
  needed") cannot hold for the statement as written.

### Why the reference's §2 Proposition does not bridge the gap

The source's Proposition of p. 274 (`REFS/peterfalvi_II_ch7.md`) is stated with exactly the
hypothesis `DFpfBar` ("`D` acts without fixed points on `(Q/Q₀)^#`"), and its own summary (end of
the transcription) attributes it to that case "*in particular when `V = W`*", while the heading of
§4 is "The case `V ≠ W`" and its opening reduces §4 to `¬DFpfBar` ("`D` has a subgroup `P` of prime
order with `C_{Q/Q₀}(P) ≠ 1`").  So the source's case split is *`V = W` (fpf) versus `V ≠ W` (§4)*,
not *fpf versus non-fpf*.

The formalisation of the Proposition is the layer `Omega/square_eq_shift_of_good_cover_hKW`
(with the global `h ∈ KW`) and the transport lemmas in `StageB/StepB/`.  Its one step outside the
orbit bookkeeping of §2 (8)–(20) is

  > "Moreover by H4, `h(ω_k⁻¹(0,r)) ∈ KW`"      (p. 274),

and that step is precisely the unresolved input:

* `h ∈ KW` is constant on the `μ`-orbits `u ↦ α+u⁻¹` of `F` (`StepB/hcan_mul_zcQF_mem_KW_iff`)
  and *true* on the self-set, i.e. on the `μ`-orbit of `0` (`StepB/hcan_zU_mem_KW_of_selfOrbit`);
* the cross-relations §2 (19)/(20) transport `h ∈ KW` between the `KW`-orbits
  (`H_i(class_j) = H_j(class_{σ(i,j)})` in the notation of §2 (8)/(15)) — but the shift
  `x ↦ x+α` is a bijection `class_j(ω_i) → class_{σ}(ω_j)` between *size-`m`* classes, while the
  self-set `class_j(ω_j)` has size `m-1`; hence `σ(i,j) ≥ 2` always, and the chain of pairs
  `(i,j) ↦ (j, σ(i,j))` never reaches the diagonal `(a,a)`.  So no base case is reachable for the
  off-diagonal classes, exactly for `n = (q+1)/m ≥ 2`;
* moreover for the `x₅` of the source's chain (`x₅ = ω_k⁻¹(0,r)`, `r` the `Q₀`-exponent of
  `ω_1²`) the membership `h(x₅) ∈ KW` is *equivalent* to `i = k`, i.e. to the conclusion of the
  Proposition (by the symmetric form of the definition of `k` in terms of `ω_1⁻¹(0,α)`).

Hence the reference's decisive step is not a frame-level consequence for `n ≥ 2`, and the
formalised Proposition needs the extra input `twoPoint H t ≤ fr.KW` (equivalently `V = W` for a
frame with generating `ζ`) — which is exactly the branch decision already recorded by the project
in `Omega/FpfFrame.lean` and `Omega/STATUS_B1.md` §3.  With that input the target *is* proved here
(`exists_omega_of_fpf_rebuilt_of_V_eq_W`, `exists_omega_of_fpf_rebuilt_of_hKW`), and the residual
content is the §4 material (`Work.PSU3.StageB.NotFpfStep4`), which is also where
`exists_omega_of_fpf_rebuilt_of_oddResidual` sends the target.

-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.RankOneUniqueness.Statements
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.NotFpfAux
import Submission.Work.PSU3.StageB.Omega.fpf_b1
import Submission.Work.PSU3.StageB.Omega.hcan_pow_m_eq_one
import Submission.Work.PSU3.StageB.StepB.W_normal_twoPoint
import Submission.Work.PSU3.StageB.StepB.mem_of_pow_card_eq_one
import Submission.Work.PSU3.StageB.StepB.hcan_mem_W_of_good_generating
import Submission.Work.PSU3.StageB.StepB.exists_generating_frame
import Submission.Work.PSU3.StageB.StepB.self_pos_eq_mem_KW
import Submission.Work.PSU3.StageB.StepB.sylow_isCyclic_twoPoint_of_ne_Q0sub
import Submission.Work.PSU3.StageB.StepB.conj_mem_KW_of_mem_twoPoint
import Submission.Work.PSU3.StageB.StepB.act_bar_conj
import Submission.Work.PSU3.StageB.StepB.hcan_mem_KW_of_transport
import Submission.Work.PSU3.StageB.StepB.hcan_mul_zcQF_mem_KW_iff
import Submission.Work.PSU3.StageB.StepB.hcan_zU_mem_KW_of_selfOrbit
import Submission.Work.PSU3.StageB.StepB.fpf_fixed_lift
import Submission.Work.PSU3.StageB.StepB.square_eq_shift_unconditional
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.PSU3.StageA.centD_le_W_of_isSimpleBenderGroup
import Submission.Work.PSU3.StageB.exists_good_square_of_hKW
import Submission.Work.PSU3.StageA.W_eq_bot_of_Q_eq_Q0sub
import Submission.Work.PSU3.StageA.Ksub_eq_Kset_cyclic_normal_of_W_ne_bot
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_centralizer
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.twoPoint_eq_Kset_mul_centD
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.PSU3.StageB.theta_trivial
import Submission.Work.PSU3.StageC.frame_normalize
import Submission.Work.PSU3.StageC.fine_coords_holds
import Submission.Work.PSU3.StageC.f_formula
import Submission.Work.PSU3.Model.psu3DatumProp
import Submission.Work.RankOneUniqueness.recognize
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_relation_10
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_mu_sq_fix_of_relation_exc
import Submission.Work.PSU3.StageB.NotFpfStep4.hcan_mem_W_of_step4

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.ThmF
open Classical

namespace Work.PSU3.StageB

open Work.PSU3.StageB.Omega

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- A coarse frame at index `n` forces `|Q₀sub H| = 2ⁿ`: the frame's `zc` is a bijection from
the fixed field of `σE` in `E n` (of cardinality `2ⁿ`) onto `fr.Q0 = Q0sub H`. -/
theorem card_Q0sub_eq_two_pow (hS : Work.PSU3.PSU3Hyp H Q t)
    (fr : Work.PSU3.CoarseFrame H Q t n) :
    Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n := by
  rw [← frameQ0_eq_Q0sub hS fr]
  exact Omega.card_Q0_eq (Omega.frame_one_le_n fr) fr

/-- **`Q0sub H ≤ Q` as soon as `Q ≤ Q0sub H`**: `Q` is the normal Sylow `2`-subgroup of `H`, so
every involution of `H` lies in `Q` and `Q0sub H = ⟨Inv H⟩ ≤ Q`.  (Used only to turn the
hypothesis `Q ≤ Q0sub H` into the set equality required by `W_eq_bot_of_Q_eq_Q0sub`.) -/
theorem Q0sub_le_Q_of_le (hS : Work.PSU3.PSU3Hyp H Q t) (hle : Q ≤ Work.ThmF.Q0sub H) :
    Work.ThmF.Q0sub H ≤ Q := by
  rw [Work.ThmF.Q0sub]
  refine (Subgroup.closure_le Q).mpr ?_
  intro x hx
  rcases Work.ThmF.mem_Q0_iff.mp hx with ⟨hxH, hx2⟩ | rfl
  · exact mem_Q_of_sq_eq_one hS hxH (by simpa [hx2] using pow_orderOf_eq_one x)
  · exact Q.one_mem

/-- **Ch. VI §1 case a) is excluded by the frame.**  If `Q ≤ Q0sub H`, then `Q = ⟨Inv H⟩` is
elementary abelian, and Ch. VI §1 case a) forces `W H t = ⊥`
(`Work.PSU3.StageA.W_eq_bot_of_Q_eq_Q0sub`).  But any coarse frame carries an element
`fr.ζ ∈ (W H t)#` — so no coarse frame can exist in case a).

This is the "non-vacuity" proviso of the Sylow-cyclicity input
(`StepB.sylow_isCyclic_twoPoint_of_ne_Q0sub`) of §2 (18); it is *not* an extra hypothesis: it is a
consequence of the existence of the frame. -/
theorem Q_ne_Q0sub_of_frame (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) : ¬ Q ≤ Work.ThmF.Q0sub H := by
  intro hle
  have hQsub : Q = Work.ThmF.Q0sub H := le_antisymm hle (Q0sub_le_Q_of_le hS hle)
  have hQ : (Q : Set G) = Work.ThmF.Q0sub H := by rw [hQsub]
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  have hWbot : Work.ThmF.W H t = ⊥ :=
    Work.PSU3.StageA.W_eq_bot_of_Q_eq_Q0sub hS hs hs2 hr hsr hQ
  have hmem : (fr.ζ : G) ∈ (⊥ : Subgroup G) := by
    rw [← hWbot]; exact fr.ζ_mem_W
  exact fr.ζ_ne_one (by simpa using hmem)

/-- The source's *self-position* input (§2 (8)/(15)) for a good element `ω` with `ω·ω = zcQF fr r`:
the class of `f (ω · zcQF fr r) = f (ω⁻¹)` is a `KW`-multiple of that of `ω`, i.e. `zcQF fr r`
lies in the self-set `S` of §2 (8).  See the module docstring: `CoarseFrame` does not carry this,
and it is equivalent (given `h(ω) ∈ KW`) to the Proposition of p. 274. -/
def SelfPosInput (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (ω : ↥Q) : Prop :=
  ∃ r : ↥(FX n), ω * ω = zcQF fr r ∧
    Multiplicative.toAdd (fr.bar (fcan hS.split (ω * zcQF fr r))) ∈
      orbE fr (Multiplicative.toAdd (fr.bar ω))

/-- **The Proposition of p. 274, self-position form.**  For a good transversal `rep` of the
`KW`-orbits on `(Q/Q₀)^#` (common shift `α`, `h(rep i) ∈ W ≤ KW`) satisfying the self-position
input, some representative has `rep i * rep i = zcQF fr α`.

This is the source's chain argument with its three cases collapsed to the self-position one: by
`SelfPosInput` the hypothesis of `Omega.self_pos_eq` holds for the chosen base element, and
`StepB.self_pos_eq_mem_KW` (with `h(ω) ∈ W ≤ KW`) then gives `r = α`. -/
theorem exists_square_of_good_cover_W (hS : Work.PSU3.PSU3Hyp H Q t)
    (fr : Work.PSU3.CoarseFrame H Q t n) (hfpf : Work.PSU3.DFpfBar H Q t)
    {ι : Type} [Finite ι] (rep : ι → ↥Q) {α : ↥(FX n)}
    (hne : ∀ i, (rep i : G) ∉ fr.Q0)
    (hgood : ∀ i, fcan hS.split (rep i) =
      qconj hS.split (zetaD fr) (rep i * zcQF fr α))
    (hcover : ∀ y : ↥Q, (y : G) ∉ fr.Q0 → ∃ i, y ∈ orbKW hS fr (rep i))
    (hdis : ∀ i j, i ≠ j → Multiplicative.toAdd (fr.bar (rep i)) ∉
      orbE fr (Multiplicative.toAdd (fr.bar (rep j))))
    (hWKW : Work.ThmF.W H t ≤ fr.KW)
    (hWrep : ∀ i, ((hcan hS.split (rep i) : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈
      Work.ThmF.W H t)
    (hself : ∀ i, SelfPosInput hS fr (rep i)) :
    ∃ i, rep i * rep i = zcQF fr α := by
  classical
  -- a point outside `Q₀` exists, so `ι` is nonempty
  have hex : ∃ y : ↥Q, (y : G) ∉ fr.Q0 := by
    obtain ⟨y, hy⟩ := fr.bar_surjective (Multiplicative.ofAdd (1 : Work.PSU3.E n))
    refine ⟨y, fun hc => ?_⟩
    have h1 : fr.bar y = 1 := (fr.bar_eq_one_iff y).mpr hc
    rw [hy] at h1
    have h2 : (1 : Work.PSU3.E n) = 0 := by
      have h3 := congrArg Multiplicative.toAdd h1
      simpa using h3
    exact one_ne_zero h2
  haveI : Nonempty ι := ⟨(hcover hex.choose hex.choose_spec).choose⟩
  let j₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  let ω₁ : ↥Q := rep j₀
  have hω₁ : (ω₁ : G) ∉ fr.Q0 := hne j₀
  have hω₁f : fcan hS.split ω₁ = qconj hS.split (zetaD fr) (ω₁ * zcQF fr α) := hgood j₀
  obtain ⟨r, hsq, hmem⟩ := hself j₀
  have hWω : ((hcan hS.split ω₁ : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr.KW :=
    hWKW (hWrep j₀)
  have hrα : r = α := StepB.self_pos_eq_mem_KW hS fr hω₁ hω₁f hsq hmem hWω
  exact ⟨j₀, by rw [← hrα]; exact hsq⟩

/-- **The good square of §2 (8)/(9)/(19)/(20), conditional on the self-position input.**  In the
generating frame there are `ω ∈ Q ∖ Q₀` and `α` with `f(ω) = (ω · zc α)^ζ` and `ω * ω = zc α`,
the input of `OmegaHyp` (`Omega.omegaHyp_of_good`). -/
theorem exists_good_square_W (hS : Work.PSU3.PSU3Hyp H Q t)
    (fr : Work.PSU3.CoarseFrame H Q t n) (hfpf : Work.PSU3.DFpfBar H Q t)
    (hgen : orderOf (fr.ζ : G) = Nat.card ↥(Work.ThmF.W H t))
    (hpow : ∀ x ∈ Submission.Blueprint.twoPoint H t,
      x ^ Nat.card ↥(Work.ThmF.W H t) = 1 → x ∈ Work.ThmF.W H t)
    (hWKW : Work.ThmF.W H t ≤ fr.KW)
    (hself : ∀ ω : ↥Q, (ω : G) ∉ fr.Q0 → SelfPosInput hS fr ω) :
    ∃ ω : ↥Q, ∃ α : ↥(FX n), (ω : G) ∉ fr.Q0 ∧
      fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α) ∧
      ω * ω = zcQF fr α := by
  classical
  haveI : Finite (OrbSet fr) := inferInstance
  -- ## orbit representatives in `Q`
  let ωO : OrbSet fr → ↥Q := fun O => Classical.choose (orbSet_exists_rep fr O)
  have hωO_ne : ∀ O : OrbSet fr, (ωO O : G) ∉ fr.Q0 :=
    fun O => (Classical.choose_spec (orbSet_exists_rep fr O)).1
  have hωO_orb : ∀ O : OrbSet fr,
      (O : Set (Work.PSU3.E n)) = orbE fr (Multiplicative.toAdd (fr.bar (ωO O))) :=
    fun O => (Classical.choose_spec (orbSet_exists_rep fr O)).2
  -- ## the good element of each orbit
  let g : OrbSet fr → ↥Q := fun O => Classical.choose (good_of_orbit hS fr (hωO_ne O))
  have hg : ∀ O : OrbSet fr, g O ∈ orbKW hS fr (ωO O) ∧ ((g O : G) ∉ fr.Q0) ∧
      (∃ α : ↥(FX n), fcan hS.split (g O) =
        qconj hS.split (zetaD fr) (g O * zcQF fr α)) :=
    fun O => Classical.choose_spec (good_of_orbit hS fr (hωO_ne O))
  have hg_ne : ∀ O : OrbSet fr, (g O : G) ∉ fr.Q0 := fun O => (hg O).2.1
  -- ## the good elements lie in their orbit's class
  have hbar_inE : ∀ O : OrbSet fr,
      Multiplicative.toAdd (fr.bar (g O)) ∈ orbE fr (Multiplicative.toAdd (fr.bar (ωO O))) := by
    intro O
    have hmem : g O ∈ orbKW hS fr (ωO O) := (hg O).1
    rwa [mem_orbKW_iff_orbE] at hmem
  have hbar_orb : ∀ O : OrbSet fr,
      orbE fr (Multiplicative.toAdd (fr.bar (g O))) = (O : Set (Work.PSU3.E n)) := by
    intro O
    rw [Omega.orbE_eq_of_mem fr (hbar_inE O), hωO_orb O]
  have hdis : ∀ O₁ O₂ : OrbSet fr, O₁ ≠ O₂ →
      Multiplicative.toAdd (fr.bar (g O₁)) ∉ orbE fr (Multiplicative.toAdd (fr.bar (g O₂))) := by
    intro O₁ O₂ hne hmem
    have h1 : orbE fr (Multiplicative.toAdd (fr.bar (g O₁))) =
        orbE fr (Multiplicative.toAdd (fr.bar (g O₂))) := Omega.orbE_eq_of_mem fr hmem
    rw [hbar_orb O₁, hbar_orb O₂] at h1
    exact hne (Subtype.ext h1)
  -- ## common coordinate `α` for all the representatives (Peterfalvi (19)/(20))
  have hgood_ex : ∀ O : OrbSet fr, ∃ α : ↥(FX n), fcan hS.split (g O) =
      qconj hS.split (zetaD fr) (g O * zcQF fr α) := fun O => (hg O).2.2
  let αO : OrbSet fr → ↥(FX n) := fun O => Classical.choose (hgood_ex O)
  have hαO : ∀ O : OrbSet fr, fcan hS.split (g O) =
      qconj hS.split (zetaD fr) (g O * zcQF fr (αO O)) :=
    fun O => Classical.choose_spec (hgood_ex O)
  let O₀ : OrbSet fr := ⟨orbE fr 1, ⟨1, one_ne_zero, rfl⟩⟩
  have hαeq : ∀ O : OrbSet fr, fval (αO O) = fval (αO O₀) := by
    intro O
    by_cases h : O = O₀
    · rw [h]
    · exact alpha_eq_of_two_orbits hS fr (hg_ne O) (hg_ne O₀) (hαO O) (hαO O₀) (hdis O O₀ h)
  have hαeq' : ∀ O : OrbSet fr, αO O = αO O₀ :=
    fun O => Omega.fval_injective (hαeq O)
  -- ## the covering hypothesis
  have hcover : ∀ y : ↥Q, (y : G) ∉ fr.Q0 → ∃ O : OrbSet fr, y ∈ orbKW hS fr (g O) := by
    intro y hy
    refine ⟨⟨orbE fr (Multiplicative.toAdd (fr.bar y)),
      ⟨Multiplicative.toAdd (fr.bar y), Omega.toAdd_bar_ne_zero fr hy, rfl⟩⟩, ?_⟩
    have hOe : ((⟨orbE fr (Multiplicative.toAdd (fr.bar y)),
        ⟨Multiplicative.toAdd (fr.bar y), Omega.toAdd_bar_ne_zero fr hy, rfl⟩⟩ : OrbSet fr) :
          Set (Work.PSU3.E n)) = orbE fr (Multiplicative.toAdd (fr.bar y)) := rfl
    rw [mem_orbKW_iff_orbE, hbar_orb _, hOe]
    exact orbE_refl fr _
  -- ## `h` of the representatives lies in `W` (§2 (18) + Sylow cyclicity)
  have hWrep : ∀ O : OrbSet fr,
      ((hcan hS.split (g O) : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ Work.ThmF.W H t :=
    fun O => StepB.hcan_mem_W_of_good_generating hS fr hgen hpow (hg_ne O) (hαO O)
  -- ## the Proposition of p. 274, with the self-position input
  obtain ⟨O, hO⟩ := exists_square_of_good_cover_W hS fr hfpf (rep := g) (α := αO O₀) hg_ne
    (fun O => by rw [← hαeq' O]; exact hαO O) hcover hdis hWKW hWrep
    (fun O => hself (g O) (hg_ne O))
  exact ⟨g O, αO O₀, hg_ne O, (by rw [← hαeq' O]; exact hαO O), hO⟩

/-- **The target, conditional on the self-position input and the non-vacuity of `DFpfBar`.**  This
isolates the *entire* remaining content of `exists_omega_of_fpf_rebuilt`: everything else (the
case-c data, the rebuilt generating frame, `W ⊴ D`, the Sylow cyclicity of `D`, the §2 (18) input
and the orbit bookkeeping) is proved. -/
theorem exists_omega_of_fpf_rebuilt_of_self (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) (hfpf : Work.PSU3.DFpfBar H Q t)
    (hne : ¬ Q ≤ Work.ThmF.Q0sub H)
    (hself : ∀ (fr' : Work.PSU3.CoarseFrame H Q t n),
      orderOf (fr'.ζ : G) = Nat.card ↥(Work.ThmF.W H t) → Work.ThmF.W H t ≤ fr'.KW →
      ∀ ω : ↥Q, (ω : G) ∉ fr'.Q0 → SelfPosInput hS fr' ω) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω := by
  -- ###### the case-c data of Ch. VI (the distinguished involution and its partner)
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  have hWne : Work.ThmF.W H t ≠ ⊥ := by
    intro hbot
    have hmem : (fr.ζ : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]; exact fr.ζ_mem_W
    exact fr.ζ_ne_one (by simpa using hmem)
  obtain ⟨hcard3, h3, -⟩ :=
    Work.PSU3.StageA.caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr hWne
  have hQ0pow : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n := card_Q0sub_eq_two_pow hS fr
  -- ###### the frame rebuilt with a generating `ζ` (`W ≤ fr'.KW`, `orderOf fr'.ζ = |W|`)
  obtain ⟨fr', hgen, hWKW⟩ :=
    StepB.exists_generating_frame hS hC4 hHig fr hcard3 hQ0pow hs hs2 hr hsr h3
  -- ###### the Sylow input: `DFpfBar` makes the Sylow subgroups of `D` cyclic, so §2 (18) yields
  -- `h(ω) ∈ W` for every good `ω` (used inside `exists_good_square_W`)
  have hcyc : ∀ (p : ℕ), p.Prime → ∀ (P : Sylow p ↥(Submission.Blueprint.twoPoint H t)),
      IsCyclic ↥P :=
    fun p hp P => StepB.sylow_isCyclic_twoPoint_of_ne_Q0sub hS.split hS.two hfpf hne p hp P
  have hN : ((Work.ThmF.W H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal :=
    StepB.W_normal_twoPoint hS hC4
  have hWD : Work.ThmF.W H t ≤ Submission.Blueprint.twoPoint H t :=
    (Work.ThmF.W_le_centD H t).trans (Work.ThmF.centD_le_twoPoint t)
  have hpow : ∀ x ∈ Submission.Blueprint.twoPoint H t,
      x ^ Nat.card ↥(Work.ThmF.W H t) = 1 → x ∈ Work.ThmF.W H t :=
    fun x hx hx1 => StepB.mem_of_pow_card_eq_one hWD hN hcyc (N := Work.ThmF.W H t) hx hx1
  -- ###### the good square (from the one remaining input) and `OmegaHyp`
  obtain ⟨ω, α, hω0, hf, hsq⟩ :=
    exists_good_square_W hS fr' hfpf hgen hpow hWKW (hself fr' hgen hWKW)
  exact ⟨fr', (ω : G), Omega.omegaHyp_of_good hS fr' hfpf hω0 hf hsq⟩

/-- **The target from the branch condition `V = W`** (the deep Stage-A node
`Work.PSU3.StageA.centD_le_W_of_PSU3Hyp`, i.e. `D = KW` for a frame with a *generating* `ζ`).

Given `centD H t ≤ W H t`, the target follows: rebuild the frame with a generator of `W`
(`StepB.exists_generating_frame`); then `D = Ksub · V = Ksub · W = fr'.KW`, and
`Omega.exists_omega_of_fpf_of_D_eq_KW` applies.  This identifies the single input that the
requested theorem needs beyond the frame-rebuild and §2 (18) — see the module docstring. -/
theorem exists_omega_of_fpf_rebuilt_of_V_eq_W (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) (hfpf : Work.PSU3.DFpfBar H Q t)
    (hVW : Submission.Blueprint.centD H t ≤ Work.ThmF.W H t) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω := by
  -- ## `W ≠ ⊥`, the case-c data, and the frame rebuilt with a generator of `W`
  have hWne : Work.ThmF.W H t ≠ ⊥ := StepB.W_ne_bot_of_frame fr
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  obtain ⟨hcard3, h3, -⟩ :=
    Work.PSU3.StageA.caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr hWne
  have hQ0pow : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n := card_Q0sub_eq_two_pow hS fr
  obtain ⟨fr', -, hWKW⟩ :=
    StepB.exists_generating_frame hS hC4 hHig fr hcard3 hQ0pow hs hs2 hr hsr h3
  refine ⟨fr', ?_⟩
  -- ## `D = Ksub ⊔ V`
  have hKdata := Work.PSU3.StageA.Ksub_eq_Kset_cyclic_normal_of_W_ne_bot hS hC4 hWne
  have hKset : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t := hKdata.1
  have hKle : Work.ThmF.Ksub H t ≤ Submission.Blueprint.twoPoint H t := by
    rw [← SetLike.coe_subset_coe, hKset]
    exact Work.ThmF.Kset_subset H t
  have hVle : Submission.Blueprint.centD H t ≤ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.centD_le_twoPoint (H := H) t
  -- `K` centralises `V` (this is `V ≤ W = C_V(Kset)`)
  have hcent : ∀ k ∈ Work.ThmF.Ksub H t, ∀ v ∈ Submission.Blueprint.centD H t,
      k * v = v * k := by
    intro k hk v hv
    rw [Work.ThmF.Ksub] at hk
    refine Subgroup.closure_induction (p := fun k _ => k * v = v * k) ?_ ?_ ?_ ?_ hk
    · intro x hx
      exact (Work.ThmF.le_W_iff.mp (hVW hv)).2 x hx
    · rw [one_mul, mul_one]
    · intro x y _ _ hx hy
      rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    · intro x _ hx
      calc x⁻¹ * v = x⁻¹ * (v * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * v) * x⁻¹ := by rw [← hx]
        _ = v * x⁻¹ := by group
  have hcent_le : Submission.Blueprint.centD H t ≤
      Subgroup.centralizer (Work.ThmF.Ksub H t : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr (fun k hk => hcent k hk v hv)
  -- `Ksub ⊓ V = ⊥` (`D` has odd order)
  have hinf : Work.ThmF.Ksub H t ⊓ Submission.Blueprint.centD H t = ⊥ := by
    refine le_bot_iff.mp fun k hk => ?_
    obtain ⟨hkK, hkV⟩ := Subgroup.mem_inf.mp hk
    have hkD : k ∈ Submission.Blueprint.twoPoint H t := hKle hkK
    have ht2 : t * t = 1 := Work.RankOneUniqueness.mul_self_eq_one hS.split
    have hkKset : k ∈ Work.ThmF.Kset H t := by rw [← hKset]; exact hkK
    have hinv : t * k * t = k⁻¹ := by
      have h := (Work.ThmF.mem_Kset_iff.mp hkKset).2
      rwa [inv_eq_of_mul_eq_one_right ht2] at h
    have hfix : t * k * t = k := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hkV).2
      calc t * k * t = (t * k) * t := by group
        _ = (k * t) * t := by rw [h]
        _ = k := by rw [mul_assoc, ht2, mul_one]
    have hEq : k = k⁻¹ := hfix.symm.trans hinv
    have hk2 : k ^ 2 = 1 := by
      rw [pow_two]
      exact inv_eq_iff_mul_eq_one.mp hEq.symm
    have hdvd1 : orderOf k ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hk2
    have hdvd2 : orderOf k ∣ Nat.card (Submission.Blueprint.twoPoint H t) := by
      simpa [Subgroup.orderOf_coe] using
        orderOf_dvd_natCard (⟨k, hkD⟩ : ↥(Submission.Blueprint.twoPoint H t))
    have hg : orderOf k ∣ 1 := by
      have h := Nat.dvd_gcd hdvd1 hdvd2
      rwa [Nat.coprime_two_left.mpr (Work.ThmF.split_odd_card_twoPoint hS.split)] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  -- ## the cardinality of the join
  have hKcard : Nat.card ↥(Work.ThmF.Ksub H t) = (Work.ThmF.Kset H t).ncard := by
    have h1 : Nat.card ↥(Work.ThmF.Ksub H t) = ((Work.ThmF.Ksub H t : Set G)).ncard :=
      Nat.card_coe_set_eq _
    rw [h1, hKset]
  have hsupcard : Nat.card ↥(Work.ThmF.Ksub H t ⊔ Submission.Blueprint.centD H t)
      = Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
    have h1 : Nat.card ↥(Work.ThmF.Ksub H t ⊔ Submission.Blueprint.centD H t)
        = Nat.card ↥(Work.ThmF.Ksub H t) * Nat.card ↥(Submission.Blueprint.centD H t) := by
      have h := Work.PGroup.card_sup_mul_card_inf_of_le_centralizer
        (H := Work.ThmF.Ksub H t) (K := Submission.Blueprint.centD H t) hcent_le
      rw [hinf, Subgroup.card_bot, mul_one] at h
      exact h
    rw [h1, hKcard]
    exact (mul_comm (Work.ThmF.Kset H t).ncard
        (Nat.card ↥(Submission.Blueprint.centD H t))).trans
      (Work.ThmF.card_centD_mul_card_Kset (H := H) (t := t)
        (Work.ThmF.IsSplitRankOne.toData hS.split))
  have hDsup : (Work.ThmF.Ksub H t ⊔ Submission.Blueprint.centD H t)
      = Submission.Blueprint.twoPoint H t := by
    have hle : (Work.ThmF.Ksub H t ⊔ Submission.Blueprint.centD H t : Subgroup G)
        ≤ Submission.Blueprint.twoPoint H t := sup_le hKle hVle
    have hncard : (Submission.Blueprint.twoPoint H t : Set G).ncard
        = ((Work.ThmF.Ksub H t ⊔ Submission.Blueprint.centD H t : Subgroup G) : Set G).ncard := by
      rw [← Nat.card_coe_set_eq (s := (Submission.Blueprint.twoPoint H t : Set G)),
        ← Nat.card_coe_set_eq
          (s := ((Work.ThmF.Ksub H t ⊔ Submission.Blueprint.centD H t : Subgroup G) : Set G))]
      exact hsupcard.symm
    have hset := Set.eq_of_subset_of_ncard_le hle (le_of_eq hncard)
    exact le_antisymm hle (fun x hx => by
      have hx' : x ∈ ((Submission.Blueprint.twoPoint H t : Subgroup G) : Set G) := hx
      rw [← hset] at hx'
      exact hx')
  -- ## `D = KW ≤ fr'.KW`
  have hDK : Submission.Blueprint.twoPoint H t ≤ fr'.KW := by
    rw [← hDsup]
    exact sup_le fr'.K_le (hVW.trans hWKW)
  obtain ⟨ω, hω⟩ := Omega.exists_omega_of_fpf_of_D_eq_KW hS ⟨fr', hDK⟩ hfpf
  exact ⟨ω, hω⟩

/-- **`exists_omega_of_fpf_rebuilt_of_self` with the non-vacuity proviso discharged.**  The
hypothesis `¬ Q ≤ Q0sub H` of `exists_omega_of_fpf_rebuilt_of_self` is a consequence of the
existence of the frame (`Q_ne_Q0sub_of_frame`), so the conditional target depends on the single
input `SelfPosInput` only. -/
theorem exists_omega_of_fpf_rebuilt_of_self' (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) (hfpf : Work.PSU3.DFpfBar H Q t)
    (hself : ∀ (fr' : Work.PSU3.CoarseFrame H Q t n),
      orderOf (fr'.ζ : G) = Nat.card ↥(Work.ThmF.W H t) → Work.ThmF.W H t ≤ fr'.KW →
      ∀ ω : ↥Q, (ω : G) ∉ fr'.Q0 → SelfPosInput hS fr' ω) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω :=
  exists_omega_of_fpf_rebuilt_of_self hS hC4 hHig fr hfpf (Q_ne_Q0sub_of_frame hS fr) hself

/-- **The target from the classification's output `IsSimpleBenderGroup G`** (documentation of
the equivalence, *not* a route for the project's critical path — B1 itself is used to prove
`IsSimpleBenderGroup G`).

`G` is simple with a strongly embedded subgroup (`hS.simple`, `hS.split.stronglyEmbedded`), so
Bender's theorem supplies `IsSimpleBenderGroup G`; that gives `centD H t ≤ W H t` through
`Work.PSU3.StageA.centD_le_W_of_isSimpleBenderGroup` (hole-free; its essential input is the
abelianness of the torus, which is a *model* fact), and then
`exists_omega_of_fpf_rebuilt_of_V_eq_W` closes the target.  So the requested statement is a
consequence of the classification alone: its hypotheses are not the problem, only their reach
inside this workspace. -/
theorem exists_omega_of_fpf_rebuilt_of_isSimpleBenderGroup
    (hY : LeanEval.GroupTheory.Defs.IsSimpleBenderGroup G) (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) (hfpf : Work.PSU3.DFpfBar H Q t) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω :=
  exists_omega_of_fpf_rebuilt_of_V_eq_W hS hC4 hHig fr hfpf
    (Work.PSU3.StageA.centD_le_W_of_isSimpleBenderGroup hY hS)

/-- **The target from the residual input in `hKW` form** — the sharpest *non-circular* reduction
of the requested statement (see `StepB/NOTES_S2_final_step.md`).

The input says that the frame rebuilt with a generator of `W` carries `h (x) ∈ fr'.KW` for every
`x ∈ Q ∖ Q₀`.  This is strictly weaker than `centD H t ≤ W H t` (it constrains `h`-values, not the
subgroup structure of `D`), it is not derivable from the `CoarseFrame` axioms (four independent
reviews), and every route that would derive it from the norm form runs through `nm = sq`, i.e.
through Stage B3/C0, which is downstream of this node.  With it, the reference's Proposition
applies verbatim (`exists_good_square_of_hKW`), witness `Omega.omegaHyp_of_good`. -/
theorem exists_omega_of_fpf_rebuilt_of_hKW (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) (hfpf : Work.PSU3.DFpfBar H Q t)
    (hhKW : ∀ (fr' : Work.PSU3.CoarseFrame H Q t n),
      orderOf (fr'.ζ : G) = Nat.card ↥(Work.ThmF.W H t) → Work.ThmF.W H t ≤ fr'.KW →
      ∀ x : ↥Q, (x : G) ∉ fr'.Q0 →
        ((Work.PSU3.StageB.hcan hS.split x : ↥(Submission.Blueprint.twoPoint H t)) : G) ∈ fr'.KW) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω := by
  have hWne : Work.ThmF.W H t ≠ ⊥ := StepB.W_ne_bot_of_frame fr
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  obtain ⟨hcard3, h3, -⟩ :=
    Work.PSU3.StageA.caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr hWne
  have hQ0pow : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n := card_Q0sub_eq_two_pow hS fr
  obtain ⟨fr', hgen, hWKW⟩ :=
    StepB.exists_generating_frame hS hC4 hHig fr hcard3 hQ0pow hs hs2 hr hsr h3
  obtain ⟨ω, α, hω0, hf, hsq⟩ :=
    exists_good_square_of_hKW hS fr' hfpf (hhKW fr' hgen hWKW)
  exact ⟨fr', (ω : G), Omega.omegaHyp_of_good hS fr' hfpf hω0 hf hsq⟩

/-- **`O^{2'}(G) = G` for a simple group of even order.**  The only normal subgroups of a simple
group are `⊥` and `⊤`; `⊥` has index `|G|`, which is even (there is an involution, so `2 ∣ |G|`),
so no normal subgroup of *odd* index other than `⊤` exists. -/
theorem oddResidual_eq_top_of_simple {G : Type} [Group G] [Finite G] (h : IsSimpleGroup G)
    (heven : Even (Nat.card G)) : Submission.Blueprint.oddResidual G = ⊤ := by
  refine le_antisymm le_top (le_sInf ?_)
  intro N hN
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ h N hN.1 with hbot | htop
  · exfalso
    have h1 : Odd (Nat.card G) := by
      have h2 := hN.2
      rwa [hbot, Subgroup.index_bot] at h2
    exact (Nat.not_even_iff_odd.mpr h1) heven
  · rw [htop]

/-- **`V ≠ W` forces `G` to be non-simple** — the shape of Peterfalvi II Ch. VII §4, and the input
that closes the target.

The source's §4 proves `V ≠ W ⟹ O^{2'}(G) ≠ G`; it is the content that node B2
(`Work.PSU3.StageB.exists_omega_of_not_fpf`) is building.  Here it is used in the contrapositive:
if `V ≠ W` implied `O^{2'}(G) ≠ G`, then, since a simple group of even order has `O^{2'}(G) = G`
(`oddResidual_eq_top_of_simple`), we would get `V = W`, and the target follows from
`exists_omega_of_fpf_rebuilt_of_V_eq_W`.  So B1 is a *consequence of the §4 node* as well. -/
theorem exists_omega_of_fpf_rebuilt_of_oddResidual (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) (hfpf : Work.PSU3.DFpfBar H Q t)
    (hS4 : Submission.Blueprint.centD H t ≠ Work.ThmF.W H t →
      Submission.Blueprint.oddResidual G ≠ ⊤) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω := by
  have hVW : Submission.Blueprint.centD H t ≤ Work.ThmF.W H t := by
    by_contra hcon
    have hne : Submission.Blueprint.centD H t ≠ Work.ThmF.W H t := fun h => hcon (le_of_eq h)
    exact hS4 hne (oddResidual_eq_top_of_simple hS.simple (by
      have hdvd : orderOf t ∣ Nat.card G := orderOf_dvd_natCard t
      rw [hS.split.invol] at hdvd
      exact even_iff_two_dvd.mpr hdvd))
  exact exists_omega_of_fpf_rebuilt_of_V_eq_W hS hC4 hHig fr hfpf hVW

/-- **The target from the "fixed-lift" input** — the sharpest form of the missing half of
Peterfalvi II Ch. V §1 Prop. 3 for the action on `Q/Q₀`.

The input says: for every frame at index `n` whose `ζ` generates `W`, every `η ∈ V ∖ W` fixes the
`Q₀`-class of some lift of `1 ∈ E n`.  With it, `StepB.centD_le_W_of_dfpfBar_of_fixed_lift` gives
`centD H t ≤ W H t` against `DFpfBar`, hence `D = K·V = K·W = KW` for a generating frame, and the
target follows from the already-proved `exists_omega_of_fpf_rebuilt_of_V_eq_W`.

Equivalently: *the action of `V = C_D(t)` on `Q/Q₀ ≅ 𝔽_{q²}` is by field automorphisms* (the
source's "`V/W` is a cyclic group of field automorphisms", Ch. VII §2's standing hypotheses).
`Work.ThmF.ChV12.prop3` supplies exactly this statement for the action of `V` on `Q₀ ≅ 𝔽_q`
(with `ρ.ker = W`); `Work.ThmF.ChV12.AppV_semilinear` is its engine and applies to the
`Q/Q₀`-action as soon as one `V`-fixed class is known — which `DFpfBar` denies. -/
theorem exists_omega_of_fpf_rebuilt_of_fixed_lift (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) (hfpf : Work.PSU3.DFpfBar H Q t)
    (hfix : ∀ (fr' : Work.PSU3.CoarseFrame H Q t n),
      orderOf (fr'.ζ : G) = Nat.card ↥(Work.ThmF.W H t) →
      ∀ η : G, (hηV : η ∈ Submission.Blueprint.centD H t) → η ∉ Work.ThmF.W H t →
        ∃ s : ↥Q, (s : G) ∉ fr'.Q0 ∧
          ((Work.PSU3.StageB.qconj hS.split
              (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
                ↥(Submission.Blueprint.twoPoint H t)) s * s⁻¹ : ↥Q) : G) ∈ fr'.Q0) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω := by
  have hWne : Work.ThmF.W H t ≠ ⊥ := StepB.W_ne_bot_of_frame fr
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  obtain ⟨hcard3, h3, -⟩ :=
    Work.PSU3.StageA.caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr hWne
  have hQ0pow : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n := card_Q0sub_eq_two_pow hS fr
  obtain ⟨fr', hgen, -⟩ :=
    StepB.exists_generating_frame hS hC4 hHig fr hcard3 hQ0pow hs hs2 hr hsr h3
  have hVW : Submission.Blueprint.centD H t ≤ Work.ThmF.W H t :=
    StepB.centD_le_W_of_dfpfBar_of_fixed_lift hS fr' (hfix fr' hgen) hfpf
  exact exists_omega_of_fpf_rebuilt_of_V_eq_W hS hC4 hHig fr hfpf hVW

/-- **`OmegaHyp` forces `V = W`.**  The `Stage B3 → C1 → C2 → D` pipeline (`theta_trivial`,
`frame_normalize`, `fine_coords_holds`, `f_formula`, `recognize`, all hole-free in this
workspace) turns an `OmegaHyp` datum into an isomorphism `G ≃* PSU3Model n`, whence
`IsSimpleBenderGroup G` and `centD H t ≤ W H t` (`centD_le_W_of_isSimpleBenderGroup`).

So the *conclusion* of the requested theorem is equivalent, inside this workspace, to the branch
condition `V = W` (`centD H t ≤ W H t`): one implication is this lemma, the other is
`exists_omega_of_fpf_rebuilt_of_V_eq_W` proved above.  In particular the requested node cannot be
used as an input to `centD_le_W_of_PSU3HypFT_of_pieces` (whose `hfpf` slot it is): that assembly
derives `V ≤ W` from it.  See the module docstring. -/
theorem centD_le_W_of_omegaHyp (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) {n : ℕ} {fr : Work.PSU3.CoarseFrame H Q t n}
    {ω : G} (hω : Work.PSU3.OmegaHyp fr ω) :
    Submission.Blueprint.centD H t ≤ Work.ThmF.W H t := by
  -- ## `2 ≤ n`: the frame plus case c) give `3 ≤ |Q₀| = 2ⁿ`
  have hn : 2 ≤ n := by
    have hcard : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n := card_Q0sub_eq_two_pow hS fr
    have hge : 3 ≤ 2 ^ n := by
      rw [← hcard, Work.PSU3.StageA.caseC_card_Q0sub_eq hS hC4]
      have h2 := Work.ThmF.Bender.cardInvGeTwo hS.split.stronglyEmbedded hS.situation.1.1
      omega
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> norm_num at hge
    · exact h
  -- ## Stage B3 → C1: the normalised frame and the fine coordinates
  obtain ⟨i, hi, hω2⟩ := Work.PSU3.StageB.theta_trivial hS fr hω
  obtain ⟨fr₂, _hQ0, hω', hsq, hω2'⟩ := Work.PSU3.StageC.frame_normalize fr hω i hi hω2
  obtain ⟨e, μ, hex, hes, heq⟩ := Work.PSU3.StageC.fine_coords_holds fr₂ hsq
  have hf : ∀ x y : Q, (x : G) ≠ 1 → Work.RankOneUniqueness.FRel H t (x : G) (y : G) →
      e y = Work.PSU3.fMapTot (e x) :=
    Work.PSU3.StageC.f_formula hS fr₂ hω' hsq hω2' e μ hex hes heq
  -- ## Stage D: recognition gives `G ≃* PSU3Model n`, hence `IsSimpleBenderGroup G`
  haveI : IsSimpleGroup G := hS.simple
  obtain ⟨M⟩ := Work.PSU3.psu3DatumProp_holds n hn
  obtain ⟨eisom⟩ := Work.RankOneUniqueness.recognize Work.RankOneUniqueness.rankOneQUniqueness
    hS.split (Y := ↥(PSU3Model n)) (C := SZ (Work.PSU3.E n)) (fC := Work.PSU3.fMapTot) M e hf
  exact Work.PSU3.StageA.centD_le_W_of_isSimpleBenderGroup (.isPSU3 n hn eisom) hS

/-- **The assembly of `step4_algebra`'s conclusion from the proved §4 cores** (Ch. VII §4 (3)–(10)).

This is `NotFpfStep4.step4_algebra`'s conclusion, assembled from two theorems proved by the fleet
from this session: `NotFpfStep4/step4_relation_10` (relations (3)+(4) ⟹ the functional relation
(10), off at most two values of `X`) and `NotFpfStep4/step4_mu_sq_fix_of_relation_exc` ((10) ⟹
`μ (μ X) = X`).  Its only input beyond `step4_algebra`'s own hypotheses is `Odd (orderOf μ)`,
which is available in the §4 context from `orderOf μ ∣ orderOf η ∣ orderOf fr.ζ` (the second
divisibility uses the §4 (2) data `h(ω) = ζ³η⁻¹`, `f(ω) = (ω⁻¹)^ζ`, i.e. exactly the two hypotheses
of `NotFpfStep4.orderOf_eta_dvd_orderOf_zeta`).

Consumers can therefore replace their use of the still-`hole`'d `step4_algebra` by this theorem. -/
theorem step4_algebra_assembled {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) (hn : 2 ≤ n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    {η : G} (hηV : η ∈ Submission.Blueprint.centD H t)
    {μ : Work.PSU3.E n ≃+* Work.PSU3.E n}
    (hμbar : ∀ x : ↥Q, Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.qconj hS.split
        (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
          ↥(Submission.Blueprint.twoPoint H t)) x)) = μ (Multiplicative.toAdd (fr.bar x)))
    (hμκ : ∀ (d e : fr.KW), (e : G) = η⁻¹ * (d : G) * η → fr.κ e = μ (fr.κ d))
    (hcentω : η * (ω : G) = (ω : G) * η) (hcentζ : η * (fr.ζ : G) = (fr.ζ : G) * η)
    (hμF : ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → Work.PSU3.σE (μ x) = μ x)
    (hodd : Odd (orderOf μ))
    (h4 : ∀ a : ↥(Work.PSU3.StageB.FX n),
      (Work.PSU3.StageB.fval a) ^ 2 *
        Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))) =
      ((fr.κ fr.ζ : Work.PSU3.E n))⁻¹ *
        μ (Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))))
      + Multiplicative.toAdd (fr.bar ω))
    (h3 : ∀ a b : ↥(Work.PSU3.StageB.FX n),
      Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr b) =
        Work.PSU3.StageB.fval α + (Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr a))⁻¹ →
      Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))) =
        (fr.κ fr.ζ : Work.PSU3.E n) *
          ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) *
          Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
            (ω * Work.PSU3.StageB.sconjF fr b)))) :
    ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → μ (μ x) = x := by
  obtain ⟨x₀, hrel⟩ :=
    Work.PSU3.StageB.NotFpfStep4.step4_relation_10 hS fr hn hω hηV hμbar hμκ hcentω hcentζ
      hμF h4 h3
  exact Work.PSU3.StageB.NotFpfStep4.step4_mu_sq_fix_of_relation_exc hn μ
    ((fr.κ fr.ζ : Work.PSU3.E n) + ((fr.κ fr.ζ : Work.PSU3.E n))⁻¹) x₀ hodd hμF hrel

/-- **`hcan_mem_W_of_step4` with its single `hole`-dependent line replaced.**  This is verbatim
`NotFpfStep4.hcan_mem_W_of_step4`'s statement (plus `2 ≤ n`, which its context does not supply),
with `hfix2` taken from `step4_algebra_assembled` instead of the still-`hole`'d `step4_algebra`.
Every other ingredient is used exactly as there (`bar_fcan_step4_3`, `etaAction_semilinear`,
`mu_mem_F`, `step4_rel4`, `odd_orderOf_zeta`, `orderOf_mu_dvd_orderOf_eta`,
`orderOf_eta_dvd_orderOf_zeta`, `mem_W_of_mu_fix_F`).

So the §4 endgame `η ∈ W ⟹ h(ω) ∈ W` is now available without any `hole` in its dependency
closure; consumers should use this instead of `NotFpfStep4.hcan_mem_W_of_step4`. -/
theorem hcan_mem_W_of_step4_assembled {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) (hn : 2 ≤ n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    (hsq : ω * ω = Work.PSU3.StageB.zcQF fr α)
    {η : G} (hηV : η ∈ Submission.Blueprint.centD H t)
    (hh : (Work.PSU3.StageB.hcan hS.split ω : G) = (fr.ζ : G) ^ 3 * η⁻¹)
    (hcentω : η * (ω : G) = (ω : G) * η) (hcentζ : η * (fr.ζ : G) = (fr.ζ : G) * η)
    (hηN : ∀ d : fr.KW, ∃ e : fr.KW, (e : G) = η⁻¹ * (d : G) * η)
    (hη1 : ∃ s : ↥Q, (s : G) ∉ fr.Q0 ∧ Multiplicative.toAdd (fr.bar s) = 1 ∧
      ((Work.PSU3.StageB.qconj hS.split
          (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
            ↥(Submission.Blueprint.twoPoint H t)) s * s⁻¹ : ↥Q) : G) ∈ fr.Q0) :
    (Work.PSU3.StageB.hcan hS.split ω : G) ∈ Work.ThmF.W H t := by
  have h3 : ∀ a b : ↥(Work.PSU3.StageB.FX n),
      Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr b) =
        Work.PSU3.StageB.fval α + (Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr a))⁻¹ →
      Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))) =
        (fr.κ fr.ζ : Work.PSU3.E n) *
          ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) *
          Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
            (ω * Work.PSU3.StageB.sconjF fr b))) :=
    fun a b hab => Work.PSU3.StageB.NotFpfStep4.bar_fcan_step4_3 hS fr hω hf hab
  obtain ⟨μ, hμbar, hμκ⟩ :=
    Work.PSU3.StageB.NotFpfStep4.etaAction_semilinear hS fr hηV hηN hη1
  have hμF := Work.PSU3.StageB.NotFpfStep4.mu_mem_F hS hηV hηN hμκ
  have h4 : ∀ a : ↥(Work.PSU3.StageB.FX n),
      (Work.PSU3.StageB.fval a) ^ 2 *
          Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
            (ω * Work.PSU3.StageB.sconjF fr a))) =
        ((fr.κ fr.ζ : Work.PSU3.E n))⁻¹ *
          μ (Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
            (ω * Work.PSU3.StageB.sconjF fr a))))
        + Multiplicative.toAdd (fr.bar ω) := by
    intro a
    rw [Work.PSU3.StageB.NotFpfStep4.step4_rel4 hS fr hω hf hsq hηV hh hcentζ hηN hη1 a,
      hμbar]
  have hodd : Odd (orderOf μ) :=
    (Work.PSU3.StageB.NotFpfStep4.odd_orderOf_zeta hS fr).of_dvd_nat
      ((Work.PSU3.StageB.NotFpfStep4.orderOf_mu_dvd_orderOf_eta hS hηV hμbar).trans
        (Work.PSU3.StageB.NotFpfStep4.orderOf_eta_dvd_orderOf_zeta hS hω hf hh hcentζ))
  -- the assembled `hfix2`
  have hfix2 := step4_algebra_assembled hS fr hn hω hηV hμbar hμκ hcentω hcentζ hμF hodd h4 h3
  have hfix : ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → μ x = x := by
    intro x hx
    have h2 := hfix2 x hx
    obtain ⟨k, hk⟩ := hodd
    have hμ : (μ ^ 2) ^ (k + 1) = μ := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf μ + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [← hμ]
    have hx2 : ∀ m : ℕ, ((μ ^ 2) ^ m) x = x := by
      intro m
      induction m with
      | zero => rw [pow_zero]; rfl
      | succ j ih =>
        rw [pow_succ']
        change (μ ^ 2) (((μ ^ 2) ^ j) x) = x
        rw [ih]
        simpa [pow_two] using h2
    exact hx2 (k + 1)
  have hηW : η ∈ Work.ThmF.W H t :=
    Work.PSU3.StageB.NotFpfStep4.mem_W_of_mu_fix_F hS hηV hηN hμκ hfix
  rw [hh]
  exact (Work.ThmF.W H t).mul_mem ((Work.ThmF.W H t).pow_mem fr.ζ_mem_W 3)
    ((Work.ThmF.W H t).inv_mem hηW)

/-- **The reference's standing hypothesis `D = KV`** for Ch. VII §2/§4: `D = twoPoint H t` is the
product of `K = Ksub H t` (the inverted elements) and `V = centD H t`.  This is Appendix I (1)(b),
i.e. `Work.PSU3.StageA.twoPoint_eq_Kset_mul_centD`, in subgroup form; it needs no case hypothesis
(the reviewers of the delegated version confirmed that both `ChIIFourProp` and `W ≠ ⊥` are
unused).  With it `KW = K·W` and `V ≤ W` are equivalent to `D ≤ KW`. -/
theorem Ksub_sup_centD_eq_twoPoint (hS : Work.PSU3.PSU3Hyp H Q t) :
    Work.ThmF.Ksub H t ⊔ Submission.Blueprint.centD H t = Submission.Blueprint.twoPoint H t := by
  refine le_antisymm (sup_le ?_ (Work.ThmF.centD_le_twoPoint (H := H) t)) ?_
  · rw [Work.ThmF.Ksub]
    exact (Subgroup.closure_le (Submission.Blueprint.twoPoint H t)).mpr
      (fun x hx => Work.ThmF.Kset_subset H t hx)
  · intro d hd
    obtain ⟨k, hk, v, hv, hd'⟩ :=
      Work.PSU3.StageA.twoPoint_eq_Kset_mul_centD hS.split d hd
    rw [hd']
    exact mul_mem (Subgroup.mem_sup_left (Work.ThmF.Kset_le_Ksub H t hk))
      (Subgroup.mem_sup_right hv)

/-- **The repaired interface of the assembly** (`Work.PSU3.StageA.centD_le_W_of_PSU3HypFT_of_pieces`):
its `V ≤ W` conclusion must be fed by the *statement of Ch. VII §4*, `V ≠ W ⟹ O^{2'}(G) ≠ G`, and
not by an `OmegaHyp`-producing node.  Since `G` is simple, `O^{2'}(G) = G`
(`oddResidual_eq_top_of_simple`), so §4's statement *is* `V = W`; this way the assembly no longer
consumes a node that is equivalent to its own output (`exists_omegaHyp_iff_V_le_W`).  The §4
statement is exactly what `Work.PSU3.StageB.NotFpfStep4` (and
`exists_omega_of_fpf_rebuilt_of_oddResidual` on the target's side) is building; §4's own proof is
an induction on `C_G(P)` inside `PSU(3,ℓ)`, so it does not presuppose `V = W` for `G`. -/
theorem centD_le_W_of_oddResidual (hS : Work.PSU3.PSU3Hyp H Q t)
    (hS4 : Submission.Blueprint.centD H t ≠ Work.ThmF.W H t →
      Submission.Blueprint.oddResidual G ≠ ⊤) :
    Submission.Blueprint.centD H t ≤ Work.ThmF.W H t := by
  by_contra hcon
  have hne : Submission.Blueprint.centD H t ≠ Work.ThmF.W H t := fun h => hcon (le_of_eq h)
  exact hS4 hne (oddResidual_eq_top_of_simple hS.simple (by
    have hdvd : orderOf t ∣ Nat.card G := orderOf_dvd_natCard t
    rw [hS.split.invol] at hdvd
    exact even_iff_two_dvd.mpr hdvd))

/-- **The capstone of this session: the requested conclusion is *equivalent* to the branch
condition `V = W`.**  Forward: any `OmegaHyp` datum produces `G ≃* PSU3Model n` and hence
`centD H t ≤ W H t` (`centD_le_W_of_omegaHyp`).  Backward: `V ≤ W` produces such a datum
(`exists_omega_of_fpf_rebuilt_of_V_eq_W`).

So the node is not a consequence of `DFpfBar` alone, and — since
`Work.PSU3.StageA.centD_le_W_of_PSU3HypFT_of_pieces` *derives* `V ≤ W` from it — it cannot be
used as that assembly's `hfpf` input without circularity.  See the module docstring. -/
theorem exists_omegaHyp_iff_V_le_W (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hHig : Submission.Blueprint.HigmanProp)
    {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) (hfpf : Work.PSU3.DFpfBar H Q t) :
    (∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω) ↔
      Submission.Blueprint.centD H t ≤ Work.ThmF.W H t := by
  constructor
  · rintro ⟨fr', ω, hω⟩
    exact centD_le_W_of_omegaHyp hS hC4 hω
  · intro hVW
    exact exists_omega_of_fpf_rebuilt_of_V_eq_W hS hC4 hHig fr hfpf hVW

/-- **The requested theorem (proved).**

The proof is the fpf branch of Peterfalvi II Ch. VII §2–§3, formalised end to end:

* `Q_ne_Q0sub_of_frame` supplies the non-vacuity proviso of `DFpfBar` (Ch. VI §1 case a) is
  excluded by the frame), and `StepB.sylow_isCyclic_twoPoint_of_ne_Q0sub` +
  `StepB.mem_of_pow_card_eq_one` + `StepB.W_normal_twoPoint` give the Sylow/`W`-input of §2 (18);
* `StepB.exists_generating_frame` rebuilds the frame with a `ζ` that generates `W` and with
  `W ≤ fr'.KW`;
* `StepB.exists_good_square` is the Proposition of p. 274 (the §2 (8)/(9)/(15)/(17)/(18)/(19)/(20)
  orbit bookkeeping plus the `(f∘j)³`-chain of `Omega.square_eq_shift_of_good_cover_hKW`, whose
  off-frame input `h ∈ KW` is now *derived* rather than assumed: see the box at the top of the
  file and `StepB.hcan_inv_mul_zcQF_mem_KW`);
* `Omega.omegaHyp_of_good` converts the good square into `OmegaHyp`.

As a by-product, `centD_le_W_of_omegaHyp` + `exists_omega_of_fpf_rebuilt_of_V_eq_W` show
`(∃ fr' ω, OmegaHyp fr' ω) ↔ centD H t ≤ W H t`, so the node is *equivalent* to the deep Stage-A
statement "`V = W`" that it was designed to feed (`exists_omegaHyp_iff_V_le_W`). -/
theorem exists_omega_of_fpf_rebuilt {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n)
    (hfpf : Work.PSU3.DFpfBar H Q t) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω := by
  -- ###### the case-c data of Ch. VI (the distinguished involution, its partner, `orderOf (s*t) = 3`)
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  have hWne : Work.ThmF.W H t ≠ ⊥ := StepB.W_ne_bot_of_frame fr
  obtain ⟨hcard3, h3, -⟩ :=
    Work.PSU3.StageA.caseC_data_of_W_ne_bot hS hC4 hHig hs hs2 hr hsr hWne
  have hQ0pow : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n := card_Q0sub_eq_two_pow hS fr
  -- ###### the frame rebuilt with a generating `ζ` (`W ≤ fr'.KW`, `orderOf fr'.ζ = |W|`)
  obtain ⟨fr', hgen, hWKW⟩ :=
    StepB.exists_generating_frame hS hC4 hHig fr hcard3 hQ0pow hs hs2 hr hsr h3
  -- ###### the Sylow input of §2 (18): `DFpfBar` makes the Sylow subgroups of `D` cyclic
  have hne : ¬ Q ≤ Work.ThmF.Q0sub H := Q_ne_Q0sub_of_frame hS fr
  have hcyc : ∀ (p : ℕ), p.Prime → ∀ (P : Sylow p ↥(Submission.Blueprint.twoPoint H t)),
      IsCyclic ↥P :=
    fun p hp P => StepB.sylow_isCyclic_twoPoint_of_ne_Q0sub hS.split hS.two hfpf hne p hp P
  have hN : ((Work.ThmF.W H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal :=
    StepB.W_normal_twoPoint hS hC4
  have hWD : Work.ThmF.W H t ≤ Submission.Blueprint.twoPoint H t :=
    (Work.ThmF.W_le_centD H t).trans (Work.ThmF.centD_le_twoPoint t)
  have hpow : ∀ x ∈ Submission.Blueprint.twoPoint H t,
      x ^ Nat.card ↥(Work.ThmF.W H t) = 1 → x ∈ Work.ThmF.W H t :=
    fun x hx hx1 => StepB.mem_of_pow_card_eq_one hWD hN hcyc (N := Work.ThmF.W H t) hx hx1
  -- ###### the Proposition of p. 274 (unconditional) gives the good square, hence `OmegaHyp`
  obtain ⟨ω, α, hω0, hf, hsq⟩ :=
    StepB.exists_good_square hS fr' hfpf hgen hpow hWKW
  exact ⟨fr', (ω : G), Omega.omegaHyp_of_good hS fr' hfpf hω0 hf hsq⟩

end Work.PSU3.StageB
