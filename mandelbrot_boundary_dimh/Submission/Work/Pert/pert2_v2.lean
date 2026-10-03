/-
# `Work.Pert.pert2_v2` — state of this file (session 2026-10-3x)

**SESSION 46 — read `Submission/Work/Pert/pert2v2/NOTES_pert2v2_session46.md` FIRST.**  S11 and S13
are now PROVED (the file builds with **5** sorries: `hhc`, `hcross`, `hRclose`, `hRupper`,
`horbit`).

* **S11 `hWhigh` and S13 `hDRsub` are done.**  The window `{|Re| < 1}` is covered by the *margin*
  waist by `Work.Pert.pert2v2.window_cover_axis` (PROVED; `window_cover_axis` is
  `waist_window_cover_margin` with the deviation hypothesis moved to the *axis* points `± i t`,
  which is what `Work.Pert.PinLogDev.anchor_dev_le` produces — this avoids the heavy
  `pinned_dev_log_v2` sub-library, whose olean is stale and whose `Pinned.transportHyp_of_v5`
  does not build).  The plumbing: `anchor_dev_le` at `Ξabs` gives `Aan, Can, Y0an, Msan` (datum
  level, before `M`); `Msan` joins the threshold of `coordP_close_pinned`; at that `M` its
  `Lan`/`δan` join `L`/`δ0`; `H := max (max (max y₁ Ξabs) Yc) Hthr + 2` where `Hthr` is the cover's
  threshold.
* **The two refuted refutations stand** (sessions 1/4/17–19/24/35): the statement is TRUE.

## Remaining rows and their blockers (see the session-46 note, §3)

| row | blocker |
|---|---|
| `hhc` (A.4.4) | needs the pin of `Φp` against `d.Φ ∘ τ₀` on the *segment* family `Xc d '' (Ico 0 1 × {y₀})` — i.e. a crux call with a caller-given `Kp ⊇` that segment (`pert2v2.CruxPinned.crux_pinned`, which takes `Kp`, `εp` as inputs), whereas the file now calls `crux_limit_v3_k0`.  `HresRow.hres_at` + `HresRowFull`/`A44Full` then give `‖dlow + 1/α‖ < δ/2` (with `A44Full`'s `∀y₀ ≥ Y` replaced by a single `y₀`, since the segment pin is only known on a *bounded* segment). |
| `hcross` (S12) | needs `(SHADOW)`: `F^[m_x] ς ∈ Qp'` for `ς ∈ Mset`, `w = ΨE ς` in the window; equivalently the walk endpoint coincides with the crux's landing point `ζ_w`.  Tools on disk: `pert2v2.shadow_walk_local`, `ShadowBand.shadow_of_walks`, `PertCrux.liftF_sub_model_le_var`, `Ksub2.F0f_far_translation`, `gate_coord_close_up_to_base`, `Xc_coher_band`, `FatouModulus3`. |
| `hRclose` (S14) | upper half: `high_band_R_close_v2` with `hdec` (`Work.Pert.liftF_defect_decay_exp`, DELEGATED) + the cover.  Lower half (from the present `Uhigh`, which contains `{|Im| > H}` at BOTH signs): needs the *uniform convergence of the horn map at the LOWER end* (`Ẽ_f → Ẽ_{f₀}` on the cylinder), i.e. the paper's (4.2.4) at the lower end — strictly more than the end asymptotics (the lower-end **constant** `cl` of `d.E` has `0 < Im cl`, so the lower end of `R̃_f - Ẽ_{f₀}` is *not* `-1/α`).  NOT settled. |
| `hRupper` (S15) | `R_upper_twoPiece` + `hwin`: the clean route is `retOf_sub_id_tendsto_upper` (PROVED; hypotheses `hinj`, `hcover : ∀ᶠ w in upperEnd, w ∈ Φ '' Qm`, `hproper`, `hEnd : Tendsto (Φ - id) upperEnd (nhds c)` — NO preimage localization), which needs the *unrestricted* upper-end limit of `ΨE - id` (the drift at the upper end) and the *wide* cover (`∃Y, ∀w, Y < w.im → w ∈ ΨE '' Qm`, no `Re` window).  The windowed variant `retOf_sub_id_tendsto_upper_window` instead needs `hloc` (the preimage within a *constant* of the point) which follows from the *boundedness* of `ΨE - id` at the upper end — same content. |
| `horbit` (S16) | OWNED by others: `pert2v2/orbit_twoPiece_v3` (chart-representative telescoping) + `pert2v2/DphiP_segment`.  My part: supply its hypotheses in context (`hchart`, `hpieceLow` = `Rlow_phi_add_nat`, `hpieceHigh` = `retP_phi_shift`, `hAbel` = `hφabel`, `hsegD` = `DphiP_segment`, `hstep` (from `hRclose` + `E_sub_bdd`), `hlevLow`/`hlevHigh` (the session-43 level route)). |

## Session 43 — read `Submission/Work/Pert/pert2v2/NOTES_pert2v2_session43.md` FIRST.  Two
findings settle the long-open question of the `orbit` field:

* **`(INV)` on the low band is a CONE condition, and it FAILS.**  `pert2v2/Tt_gate.lean` proves
  `Tt α z ∈ Qm ξ α ⟺ ξ < z.re + |z.im|` for `z ∈ Qm ξ α` (and `ξ < |z.im|` is necessary), so the
  crux-based low piece is `φ`-invariant only above height `≈ Ξabs ≈ 202` — while `DR_sub` forces
  the whole band (`y₁ > d.η₀`, an *input*) into `DR`.  Do **not** spend more effort on
  `(INV)`/`(GW)`/`hcross` for the low piece; `orbit_of_inv` cannot carry the low band.
* **The level route works, with the offsets `t_j := -k_j`.**  In `orbit_pieces` take the reduced
  chart points `x j := R^[j] w - k j`, `t 0 = 0`, `t m = n`, and `t j := -k j` (`1 ≤ j ≤ m-1`).
  Then `k j + t j = 0` (so `hseg` is the single point `x j ∈ Dφ`), while `lo j = k j - k (j+1)`
  and `P (b j) (x j) + lo j = x (j+1) ∈ Ulow ∪ Uhigh`, so `hymem` is `hside` — free.  `hpiece` is
  `Rlow_phi_add_nat` (`pert2v2.Rlow_phi_shift`), whose proof uses `coordP_eq_iterate_of_level`,
  which has **no orbit condition**.  The level condition `lo j ≥ mₓ` is `≈ 1/a' ≥ mₓ`
  (a `δ₀`-condition: `Re (1/α) ≫ Ξ'`).  The membership clause's one trap (the chart shift `k 0` of
  the *first* step must be `≤ 0`) is handled by `pert2v2.orbit_mem_left_reduce` — see note §3ter.

New, proved, importable (`Submission/Work/Pert/pert2v2/`): `Tt_gate.lean` (`Tt_mem_Qm_iff'`,
`lt_abs_im_of_Tt_mem`, `Tt_mem_Qm_iff_walk`), `liftF_equivariance.lean` (`liftF_add_int_div`,
`iterate_add_shift`, `iterate_sub_shift`, `walk_congruence`, …), `low_piece_inv.lean`
(`coordP_sub_nat_eq_tau`, `RlowPiece_phi_eq_of_walk`, `coordP_sub_nat_eq_tau_Tt`,
`goodP_RlowPiece_add`, `goodP_sub_nat`, `goodP_add_nat_of_walk`, `Rlow_phi_shift`),
`left_reduce.lean` (`orbit_mem_left_reduce`, `phi_left_reduce`), `level_offsets_good.lean`,
`level_offsets_shift.lean`.

**SESSION 41 — read `Submission/Work/Pert/NOTES_pert2v2_session41.md` FIRST.**  It records what is
still open (`PertData.orbit` on the low band is a *universal* statement, not reachable by the
`K♯`-absorption; the crux-based low piece satisfies it structurally only for shifts `n > m_x`, and
for `1 ≤ n ≤ m_x` it needs a *quantitative* injectivity of `f^{m_x-n}` at the two values), what is
now wired in this file (`Yc` from `waist_cover_pinned_v2`, the reduction blob inside `Kb`, the
crux's output `hcruxbody`, and the DATUM-gate `φ := coordP … ΨE (Qm Ξabs α)` with the whole φ-side
transferred), and the two lemmas proved by children this session
(`pert2v2.injOn_iterate_ball_scale`, `pert2v2.exists_reduction_blob`).

**SESSION 40 — read `Submission/Work/Pert/NOTES_pert2v2_session40.md` AND
`Submission/Work/Pert/NOTES_pert2v2_session40_assembly.md` FIRST.**  The `hcross` mechanism of the
two-piece R-block is now SOLVED without any shadowing estimate: the φ-side coordinate must be taken
on the **datum gate**, `φ := coordP f Df τ ΨE (Qm Ξabs α)` (`ΨE` = the `FatouUnique` extension of
the crux's pinned `Φm` from `Qm Ξ'` to `Qm Ξabs`), which makes every overlap point a level-0 point of
`φ` (`φ w = τ (ΨE⁻¹ w)`); `hcross` then follows from the crux clause + a waist walk + the (A.4.2)
normalisation at the datum gate.  `NOTES_pert2v2_session40_assembly.md` §1 lists the tail's
construction row by row.  Session 40 also collected `Work.PertCrux.crux_limit_v5` (**PROVED**, the
crux with a linear landing-time bound) and proved the leaves
`walk_Qp_waist_unified`, `PsiPair_rel`, `Rlow_eq_retOf_crux_walk`, `DphiP_transfer_gate`,
`retOf_add_one_waist`, `retOf_add_int_window`, `hstep_of_close`, `R_close_on_DR`,
`norm_iterate_sub_landed_lt` (all in `Submission/Work/Pert/pert2v2/`).

**SESSION 37 — read `Submission/Work/Pert/NOTES_pert2v2_session37.md` FIRST.**  The whole (A.4.4)
row — the constant mismatch of the two gate coordinates, the blocker identified in sessions 19-36 —
is now **CLOSED**: `pert2v2.HresRowFull.hres_row` proves the segment residual `hres` from the pin of
`Φp` along the curve segment `Kp := Xc d '' {x + i y₀}`, `(RIG)` (`rig_of_coher_segment`), the
modulus of injectivity of `Φm` (`FatouModulus3`) and the gate Lipschitz bound; then
`pert2v2.A44Full.exists_a44_const_of_hres` gives the paper's `‖cm - cp‖ < δ`.  Also:
`Submission.Work.Pert.waist_cover_pinned_v2` **now builds and is sorry-free**, and `Qm Ξ α` is
ANTITONE in `Ξ` (so `Ξabs ≤ Ξ'`, `Φ★ = ΨE` extends `Φm` UP to `Qm Ξabs α`).

**SESSION 24 — read `Submission/Work/Pert/NOTES_pert2v2_session24.md`.**  The formalisation
blocker of the whole area (`PertData.orbit`'s third conjunct `∀ i < n, f^[i] (φ w) ∈ Df`, about the
*future* of `φ w` while `GoodP` controls only its *past*) is **PROVED** in
`Submission/Work/Pert/pert2v2/orbit_mem.lean`: the single structural fact `τ '' Q ⊆ Df` (available
in this file as `tauC '' Qm Ξ' α ⊆ ball 0 rr ⊆ L ⊆ Df`) makes the *walk* `F^j u ∈ Q` deliver
`f^j (τ u) ∈ Df` for free, and the orbit condition of the minimal level of `w'` covers the rest.
The `m = 1` low band is closed (`pert2v2.orbit_one_of_level` + `…orbit_one_of_level_short` +
the proved `shift_pos_of_step` and `Rlow_phi_translate_lt`), and the general `m` is reduced to the
walk, `(INV)`-on-the-walk and the ray (`pert2v2.orbit_general`, `pert2v2.low_inv_of_ray`).
`Work.Pert.orbit_reduce` is NOT usable here (it wants `φ ∘ R = φ` on all of `Dφ`, which is false
for the low piece).

This file is `Work.Pert.asm` (the **whole φ-side** of `PertData`, wired and sorry-free) with the
theorem renamed to `pert2_v2`; the only `sorry` is the trailing `orbit` field, which `asm.lean`
supplies against `R := d.E - 1/rotOf f`, `DR := d.DE` (the `RBDE` route, free for every R-field
except `orbit`).  **That scaffold must be replaced by the two-piece `R` (§4 of the session-20
note); the high band is blocked by `PinLogDev/anchor_point_bound2.lean` (unterminated comment) and
`drift_le.lean`/`walk_clear.lean` (`sorry`), see session-24 §4.**

**READ `Submission/Work/Pert/NOTES_pert2v2_session20.md` — it supersedes the older design
notes and rewrites the tail below.**  In particular:

* the `RBDE` pair (`R := d.E - 1/rotOf f`, `DR := d.DE`) that the tail of this file feeds to
  `pertData_of_orbit_DE` is a **scaffold only**: `d.E - 1/α` is the *unperturbed* return map, so
  `orbit` is false for it (the lead confirmed: "do not ship it as the PertData R").  The tail must
  be rewritten with the two-piece `R` of the note (§4).
* the mechanism of the low piece is §3 of that note: with the gate-walk hypothesis **(GW)** the
  crux formula satisfies `Rlow w = Φ (Tt α ς) + E` for `w = Φ ς + E` (deck translation on the gate
  point, level preserved), hence `φ (Rlow w) = φ w` — which is exactly what `orbit_reduce` needs.
* the two pieces are `Ulow` (crux formula at `k = 0`, `d` the (A.4.2) constant) and `Uhigh`
  (`retP` at the datum-level gate `Ξabs`, where the waist is available), glued by `tSat_glue` and
  height-separated (`Hband := max (max CK y₁) Y + 3`, `Y` the datum-level cover threshold).
* one single gate coordinate `ΨE` (Fatou on `Qm Ξabs α`, agreeing with `Φm` on `Qm Ξ' α`) serves the
  crux, `φ` and the cover — built by `FatouExists` + `FatouUnique`
  (`Work.Pert.pert2v2.exists_fatouCoord_extend_agree`).

Proved and already importable for that route:
`Work.Pert.pert2v2.coordP_mono_gate`, `Work.Pert.pert2v2.Rlow_eq_retOf_level0`,
`Work.Pert.pert2v2.retOf_add_nat_of_mem_image`, `Work.Pert.pert2v2.end_const_le_seg`,
`Work.Pert.pert2v2.Rlow_phi_inv`, `Work.Pert.pert2v2.exists_fatouCoord_extend_agree`,
`Work.Pert.pert2v2.Rlow_gate_value` (the crux formula is a gate value minus the level `m`,
`RlowPiece w = Φ (Tt α ζ_w) - m`; `(INV)` at an arbitrary admissible level in the `Tt`-shift form),
and the definitions `Work.Pert.pert2v2.{LowClause, lowZeta, RlowPiece, GateWalk}`.

**SESSION 21 — READ `Submission/Work/Pert/NOTES_pert2v2_session21.md` (supersedes §2–§3 of the
session-20 note on the low band).**  The geometric picture of the low band is:

* the level points `ς_E = Φ⁻¹ (w - E)` of `w` all lie on **one walk orbit** (`ς_{E+1} = F⁻¹ ς_E`);
  since `F` is a near-translation, that orbit is (nearly) horizontal, so all level points of a
  low-band `w` have `|Re| ≈ M ≫ |Im| ≈ O(1)` (`band_goodP_sqrt`'s witness lives in
  `Dstrip M Tb = {-M-1 ≤ Re ≤ -M, |Im| ≤ Tb}`, `Tb ≤ M/160`).
* hence `ς_E ∉ Qp Ξ' α` (the waist) **for every admissible level `E`**, so (i) `Tt α ς_E ∉ Qm Ξ' α`
  and the two-line `(INV)` `φ (Φ (Tt α ς) + E) = τ (Tt α ς) = τ ς = φ w` (`pert2v2.coordP_gateValue`)
  is **not** available, and (ii) the gate-walk hypothesis `(GW)` of `pert2v2.Rlow_phi_inv` cannot be
  produced at the low band.  Only the far band (above the cover threshold `Y`, where the waist is
  nonempty) uses the `Tt`-shift.
* the low piece is therefore `RlowPiece` with the crux's residual: `R_close` follows from
  `‖crux residual‖ + ‖d + 1/α‖ = ‖crux residual‖ + ‖cm - cp‖` (row **(A.4.4)**, cf.
  `pert2v2.end_const_le_seg`), and `orbit`/`(INV)` needs the **level structure of `R w`**, i.e. the
  backward walk of `ζ_w - 1/α` in `Qm Ξ'` for `m + mIdxP (R w)` steps — which exists iff
  `m ≲ Re (1/α)`.  Hence the delegated `Work.PertCrux.crux_limit_v4` (an explicit, `f`-independent
  upper bound on the crux's landing time `m`, so that the caller can force `‖α‖ ≲ 1/Mmax` through
  `δ₀`).  The remaining fine point (session-21 note §4) is the value comparison
  `f^n (τ ς') = φ w` given only `f^{m+n} (τ ς') = f^m (φ w)`.
-/
import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.normalform_radius
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.SmallData
import Submission.Work.Pert.qadm
import Submission.Work.Pert.gate_scale_L1
import Submission.Work.Pert.LiftNTL2.liftF_nearTranslationL1
import Submission.Work.Pert.Ksub2.abel_on_gate
import Submission.Work.Pert.gate_T_relation
import Submission.Work.Pert.DphiP_open
import Submission.Work.Pert.coordP_holo
import Submission.Work.Pert.coordP_abel
import Submission.Work.Pert.tauC_gate_sub_closedBall
import Submission.Work.Pert.strip_high
import Submission.Work.Pert.Dsub_phi_star
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn
import Submission.Work.PertCrux.coordP_close_dphi
import Submission.Work.PertCrux.crux_limit_v3
import Submission.Work.PertCrux.crux_limit_v3_k0
import Submission.Work.PertCrux.coordP_close_pinned
import Submission.Work.Pert.Pin.strip_of_pin_v2
import Submission.Work.Pert.phi_star_of_close
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.RBlock4.Rlow_holo
import Submission.Work.Pert.RBlock4.retOf_holo
import Submission.Work.Pert.Qm_Qp
import Submission.Work.Pert.tSat_glue
import Submission.Work.Pert.Rlow_add_one
import Submission.Work.Pert.Rlow_eq_retOf
import Submission.Work.Pert.retOf_add_nat
import Submission.Work.Pert.orbit_reduce
import Submission.Work.Pert.retOf_sub_id_tendsto_upper
import Submission.Work.Pert.pert2v2.Rlow_close_of_res
import Submission.Work.Pert.waist_cover_pinned_v2
import Submission.Work.Pert.WaistPinned.deriv_close_on_gate_uniform
import Submission.Work.Pert.pert2v2.waist_window_cover_margin
import Submission.Work.Pert.pert2v2.window_cover_axis
import Submission.Work.Pert.pert2v2.reduction_blob_half
import Submission.Work.Pert.pert2v2.exists_reduction_blob
import Submission.Work.Pert.pert2v2.exists_fatouCoord_extend_agree
import Submission.Work.Pert.pert2v2.DphiP_transfer_gate
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.pert2v2.RBlockDefs
import Submission.Work.Pert.pert2v2.twoPieceR
import Submission.Work.Pert.pert2v2.twoPieceROverlap
import Submission.Work.Pert.pert2v2.liftF_equivariance
import Submission.Work.Pert.pert2v2.PsiPair_rel
import Submission.Work.Pert.pert2v2.retOf_add_one_waist
import Submission.Work.Pert.pert2v2.high_piece_data_wide
import Submission.Work.Pert.pert2v2.HcoincRow
import Submission.Work.Pert.RetPEquiv
import Submission.Work.Horn.gholo
import Submission.Work.Pert.pert2v2.LowChart
import Submission.Work.Pert.pert2v2.lowClause_isOpen
import Submission.Work.Pert.pert2v2.isOpen_clauseSet
import Submission.Work.Pert.pert2v2.RBlockCharts
import Submission.Work.Pert.RBlock7.retPShift
import Submission.Work.Pert.RBlock4.Rlow_add_one_pointwise
import Submission.Work.Pert.pert2v2.low_piece_data_wide
import Submission.Work.Pert.DiffGate.diff_tauC_gate
import Submission.Work.Pert.RBlock7.retPPhi
import Submission.Work.Pert.image_cover_centered
import Submission.Work.Pert.WaistPinned.waist_disc_window
import Submission.Work.Pert.pert2v2.gate_preimage_bounds_window
import Submission.Work.Pert.liftF_defect_decay_exp
import Submission.Work.Pert.pert2v2.gate_coord_end_asymptotic
import Submission.Work.Pert.pert2v2.EndWindowBounded.end_asymptotic_bounded_window
import Submission.Work.Pert.RBlock2.gate_T_relation_constant
import Submission.Work.Pert.pert2v2.RUpperTwoPiece
import Submission.Work.Pert.pert2v2.lower_end_close_of_line
import Submission.Work.Pert.pert2v2.E_sub_bdd
import Submission.Work.Pert.pert2v2.waist_return_bound_up
import Submission.Work.Pert.pert2v2.waist_return_bound_low
import Submission.Work.Pert.liftF_lower_decay_gate
import Submission.Work.PertCrux.crux_limit_v8
import Submission.Work.PertCrux.gateP_coord_converges
import Submission.Work.Analysis.PertCrux.gate_fatou_lipschitz
import Submission.Work.Analysis.PertCrux.small_data
import Submission.Work.Analysis.PertCrux.orbit_shift_close
import Submission.Work.Pert.RBlock3
import Submission.Work.Pert.pert2v2.LeadWire.HhcTools
import Submission.Work.Pert.pert2v2.LeadWire.ShadowTools
import Submission.Work.Pert.pert2v2.LeadWire.OrbitTools
import Submission.Work.Pert.pert2v2.orbit_row_mem
import Submission.Work.Pert.pert2v2.orbit_mem
import Submission.Work.Pert.pert2v2.left_reduce
import Submission.Work.Pert.pert2v2.DphiP_segment
import Submission.Work.Pert.pert2v2.level_translate
import Submission.Work.Pert.pert2v2.retP_phi_shift
import Submission.Work.Pert.pert2v2.E_sub_bdd
import Submission.Work.Pert.pert2v2.ShadowBand
import Submission.Work.Pert.pert2v2.shadow_coinc_v7
import Submission.Work.Pert.pert2v2.Rlow_eq_retOf_crux_walk
import Submission.Work.Pert.pert2v2.walk_Qreg_const
import Submission.Work.Pert.Ksub2.F0f_far_translation
import Submission.Work.Pert.u_close_of_nearOn
import Submission.Work.Pert.pert2v2.A44Row
import Submission.Work.Pert.pert2v2.HdiffRow.EfFloor_hdiff_of_step
import Submission.Work.Pert.pert2v2.tendsto_EfFloor_upperEnd_C

/-!
# `Work.Pert.asm`: WIP TEMPLATE for the final `pert2` assembly

**This file is a work in progress and is NOT imported by `pert2.lean`.**  It records the structure
of the final assembly exactly as prescribed by the lead (`NOTES_pert2_assembly_order.md`, sections
1–3) so that the last step is mechanical once the dispatched lemmas
`Work.Pert.strip_of_coord`, `Work.Pert.phi_star_of_close` (and anything else still `sorry`) are
`sorry`-free.  Every `sorry` below marks a place where either
(a) one of the dispatched lemmas is not yet available, or
(b) the `R`-block bookkeeping (the `d_low`/`(A.4.4)` identity of §2 of the order, and the
    `DR_sub` coverage of §3) is still open.

Do NOT import this from `pert2.lean` until every `sorry` here is gone.
-/

namespace Work.Pert

open _root_.MandelDim Complex Set Metric
open scoped Topology

noncomputable section

set_option maxHeartbeats 4000000

set_option linter.unusedVariables false

/-- **The strong disc cover of the gate at an axis anchor.**  If `Φ` is a Fatou coordinate of a
near-translation on `Qm Ξ α`, `Φ' ≈ 1` on balls of radius `≥ R₂` inside the gate, `Ξ < T/2` and
`R₂ ≤ T/8`, then the disc of radius `T/32` about `Φ z₀` (`z₀` on the imaginary axis at height
`|z₀.im| = T`) is covered by `Φ '' Qm Ξ α`, and every point of it has its pinned preimage inside
`closedBall z₀ (T/8)` (hence inside `Qm Ξ α ∩ Qp Ξ α`).

This is `Work.Pert.pert2v2.WaistCoverDisc.waist_cover_disc`'s inner argument with the *sharp*
radius `T/8` (the file weakens it to `T/4 + 2`), which is what the height gain
`(3 y₀ + Ξ)/4 ≤ ς.im` of the cover needs. -/
theorem disc_cover_strong {Ξ T R₂ : ℝ} {α : ℂ} {F Φ : ℂ → ℂ} {z₀ : ℂ}
    (hInF1 : MandelDim.InF1 α) (hz₀re : z₀.re = 0) (hz₀abs : |z₀.im| = T)
    (hT : Ξ < T / 2) (hTpos : 0 < T) (hR₂ : R₂ ≤ T / 8)
    (hder : ∀ z : ℂ, ∀ R : ℝ, R₂ ≤ R → Metric.ball z R ⊆ Qm Ξ α → ‖deriv Φ z - 1‖ ≤ 1 / 2)
    (hΦ : MandelDim.IsFatouCoordOn F Φ (Qm Ξ α)) :
    Metric.ball (Φ z₀) (T / 32) ⊆ Φ '' (Qm Ξ α) ∧
      (∀ u : ℂ, u ∈ Metric.ball (Φ z₀) (T / 32) →
        invOn Φ (Qm Ξ α) u ∈ Metric.closedBall z₀ (T / 8) ∧
        invOn Φ (Qm Ξ α) u ∈ Qm Ξ α ∧ invOn Φ (Qm Ξ α) u ∈ Qp Ξ α) := by
  set ρ : ℝ := T / 4 with hρ
  set r : ℝ := T / 8 with hr
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hrpos : 0 < r := by rw [hr]; linarith
  have hrρ : r ≤ ρ := by rw [hr, hρ]; linarith
  have hrR₂ : R₂ ≤ ρ - r := by rw [hr, hρ]; linarith
  have hwaist : Ξ + 2 * ρ < T := by rw [hρ]; linarith
  have hdisc : Metric.closedBall z₀ ρ ⊆ Qm Ξ α ∩ Qp Ξ α :=
    Work.Pert.WaistPinned.waist_disc_window (ξ := Ξ) (T := T) (ρ := ρ) (α := α) (z₀ := z₀)
      hInF1 (le_of_lt hρpos) hwaist hz₀re hz₀abs
  have hsub : Metric.closedBall z₀ r ⊆ Qm Ξ α := fun z hz =>
    (hdisc (Metric.closedBall_subset_closedBall hrρ hz)).1
  have hdiff : ∀ ζ ∈ Metric.closedBall z₀ r, DifferentiableAt ℂ Φ ζ := fun ζ hζ =>
    hΦ.1.differentiableAt ((isOpen_Qm Ξ α).mem_nhds (hsub hζ))
  have hder' : ∀ ζ ∈ Metric.closedBall z₀ r, ‖deriv Φ ζ - 1‖ ≤ 1 / 2 := by
    intro ζ hζ
    refine hder ζ (ρ - r) hrR₂ ?_
    intro z hz
    rw [Metric.mem_ball] at hz
    have h1 : dist ζ z₀ ≤ r := by rwa [Metric.mem_closedBall] at hζ
    have h2 : dist z z₀ < ρ := by
      calc dist z z₀ ≤ dist z ζ + dist ζ z₀ := dist_triangle _ _ _
        _ < (ρ - r) + r := by linarith
        _ = ρ := by ring
    exact (hdisc (Metric.mem_closedBall.mpr h2.le)).1
  have hcov : Metric.ball (Φ z₀) (T / 32) ⊆ Φ '' Metric.closedBall z₀ r := by
    have hr4 : r / 4 = T / 32 := by rw [hr]; ring
    rw [← hr4]
    exact Work.Pert.image_cover_centered hrpos hdiff hder'
  refine ⟨fun u hu => Set.image_mono hsub (hcov hu), ?_⟩
  intro u hu
  obtain ⟨ζ, hζ, hζeq⟩ := hcov hu
  have hζQm : ζ ∈ Qm Ξ α := hsub hζ
  have hinv : invOn Φ (Qm Ξ α) u = ζ :=
    Work.Pert.invOn_eq hΦ.2.1 ⟨ζ, hζQm, hζeq⟩ hζQm hζeq
  refine ⟨?_, ?_, ?_⟩
  · rw [hinv]; exact hζ
  · rw [hinv]; exact hζQm
  · rw [hinv]; exact (hdisc (Metric.closedBall_subset_closedBall hrρ hζ)).2

/-- The **upper** half-plane counterpart of `Work.Pert.pert2v2.lower_end_close_of_line`, obtained
from it by the *negated reflection* `w ↦ 1 - w`: the reflection reverses the `+1`-periodicity, and
the extra negation restores it while turning the expression `R w + a - E w` into its negative. -/
theorem upperHalf_close_of_line {R E : ℂ → ℂ} {a : ℂ} {y₁ δ : ℝ}
    (hRd : ∀ w : ℂ, y₁ ≤ w.im → DifferentiableAt ℂ R w)
    (hEd : ∀ w : ℂ, y₁ ≤ w.im → DifferentiableAt ℂ E w)
    (hRper : ∀ w : ℂ, y₁ ≤ w.im → R (w + 1) = R w + 1)
    (hEper : ∀ w : ℂ, y₁ ≤ w.im → E (w + 1) = E w + 1)
    (hbdd : ∃ C : ℝ, ∀ w : ℂ, y₁ ≤ w.im → ‖R w - E w‖ ≤ C)
    (hline : ∀ w : ℂ, w.im = y₁ → ‖R w + a - E w‖ < δ) :
    ∀ w : ℂ, y₁ ≤ w.im → ‖R w + a - E w‖ < δ := by
  obtain ⟨C, hC⟩ := hbdd
  have hrefl : ∀ w : ℂ, (1 - w).im = -w.im := by intro w; simp
  have hRd₂ : ∀ w : ℂ, w.im ≤ -y₁ → DifferentiableAt ℂ (fun u : ℂ => -R (1 - u)) w := by
    intro w hw
    have h1 : y₁ ≤ (1 - w).im := by rw [hrefl w]; linarith
    exact ((hRd (1 - w) h1).neg).comp w
      ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)
  have hEd₂ : ∀ w : ℂ, w.im ≤ -y₁ → DifferentiableAt ℂ (fun u : ℂ => -E (1 - u)) w := by
    intro w hw
    have h1 : y₁ ≤ (1 - w).im := by rw [hrefl w]; linarith
    exact ((hEd (1 - w) h1).neg).comp w
      ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)
  have hperR₂ : ∀ w : ℂ, w.im ≤ -y₁ → (fun u : ℂ => -R (1 - u)) (w + 1)
      = (fun u : ℂ => -R (1 - u)) w + 1 := by
    intro w hw
    have h1 : y₁ ≤ (1 - w).im := by rw [hrefl w]; linarith
    have h2 : y₁ ≤ (-w).im := by rw [Complex.neg_im]; linarith
    have h5 : R (1 - w) = R (-w) + 1 := by
      have h6 : (1 : ℂ) - w = -w + 1 := by ring
      rw [h6]; exact hRper (-w) h2
    show -R (1 - (w + 1)) = -R (1 - w) + 1
    have h7 : (1 : ℂ) - (w + 1) = -w := by ring
    rw [h7, h5]; ring
  have hperE₂ : ∀ w : ℂ, w.im ≤ -y₁ → (fun u : ℂ => -E (1 - u)) (w + 1)
      = (fun u : ℂ => -E (1 - u)) w + 1 := by
    intro w hw
    have h2 : y₁ ≤ (-w).im := by rw [Complex.neg_im]; linarith
    have h5 : E (1 - w) = E (-w) + 1 := by
      have h6 : (1 : ℂ) - w = -w + 1 := by ring
      rw [h6]; exact hEper (-w) h2
    show -E (1 - (w + 1)) = -E (1 - w) + 1
    have h7 : (1 : ℂ) - (w + 1) = -w := by ring
    rw [h7, h5]; ring
  have hbdd₂ : ∃ C : ℝ, ∀ w : ℂ, w.im ≤ -y₁ → ‖(fun u : ℂ => -R (1 - u)) w - (fun u : ℂ => -E (1 - u)) w‖ ≤ C := by
    refine ⟨C, fun w hw => ?_⟩
    have h1 : y₁ ≤ (1 - w).im := by rw [hrefl w]; linarith
    have he : -R (1 - w) - -E (1 - w) = -(R (1 - w) - E (1 - w)) := by ring
    rw [he, norm_neg]
    exact hC (1 - w) h1
  have hline₂ : ∀ w : ℂ, w.im = -y₁ → ‖(fun u : ℂ => -R (1 - u)) w + (-a) - (fun u : ℂ => -E (1 - u)) w‖ < δ := by
    intro w hw
    have h1 : (1 - w).im = y₁ := by rw [hrefl w, hw]; ring
    have he : -R (1 - w) + (-a) - -E (1 - w) = -(R (1 - w) + a - E (1 - w)) := by ring
    rw [he, norm_neg]
    exact hline (1 - w) h1
  have hlow := Work.Pert.pert2v2.lower_end_close_of_line hRd₂ hEd₂ hperR₂ hperE₂ hbdd₂ hline₂
  intro w hw
  have hu : (1 - w).im ≤ -y₁ := by rw [hrefl w]; linarith
  have h3 : ‖-R (1 - (1 - w)) + (-a) - -E (1 - (1 - w))‖ < δ := by
    simpa using hlow (1 - w) hu
  have he : -R (1 - (1 - w)) + (-a) - -E (1 - (1 - w)) = -(R w + a - E w) := by
    have h4 : (1 : ℂ) - (1 - w) = w := by ring
    rw [h4]; ring
  rw [he, norm_neg] at h3
  exact h3

set_option maxHeartbeats 40000000 in
/-- The final assembly: `PertStatement` from `FatouStatement`.  Structure only. -/
theorem pert2_v2 (hF : MandelDim.FatouStatement) : MandelDim.PertStatement := by
  intro f₀ D₀ d hd
  -- ## 0. datum-side constants (depend only on `d`, `hd`, `hF`)
  obtain ⟨η₂, hη₂pos, hη₂clause⟩ := phi_star_of_close d
  obtain ⟨ρnf, hρnfpos, hρnfsub, Cnf, hCnfpos, hNF⟩ := normalform_radius hd
  obtain ⟨r₀, hr₀pos, hr₀sub, Csm, hCsmp, hSmall⟩ := small_of_nearOn hd
  obtain ⟨r₀', hr₀'pos, hr₀'sub, hSmallData⟩ := SmallData hd
  obtain ⟨εb, hεbpos, hεbsub⟩ := Metric.mem_nhds_iff.mp (hd.1.mem_nhds hd.2.1)
  -- the gate scale (`LiftNTL2.liftF_nearTranslationL1` at the working radius `ρ`); it supplies the
  -- scale separation `Ξmin` and the smallness threshold `εmin` for `hNT`/`hNTp` below
  -- the normal-form radius used everywhere (`εb` is halved twice so that `closedBall ⊆ D₀`)
  have h4b : (0 : ℝ) < εb / 4 := by linarith
  set ρ : ℝ := min (min ρnf r₀) (min r₀' (min (εb / 4) 1)) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have hρρnf : ρ ≤ ρnf := by
    rw [hρdef]
    exact le_trans (min_le_left (min ρnf r₀) (min r₀' (min (εb / 4) 1))) (min_le_left ρnf r₀)
  have hρr₀ : ρ ≤ r₀ := by
    rw [hρdef]
    exact le_trans (min_le_left (min ρnf r₀) (min r₀' (min (εb / 4) 1))) (min_le_right ρnf r₀)
  have hρr₀' : ρ ≤ r₀' := by
    rw [hρdef]
    exact le_trans (min_le_right (min ρnf r₀) (min r₀' (min (εb / 4) 1)))
      (min_le_left r₀' (min (εb / 4) 1))
  have hρ4b : ρ ≤ εb / 4 := by
    rw [hρdef]
    exact le_trans (min_le_right (min ρnf r₀) (min r₀' (min (εb / 4) 1)))
      (le_trans (min_le_right r₀' (min (εb / 4) 1)) (min_le_left (εb / 4) 1))
  have hρD₀ : Metric.closedBall (0 : ℂ) ρ ⊆ D₀ :=
    (Metric.closedBall_subset_ball (by linarith : ρ < εb)).trans hεbsub
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the gate scale at the working radius
  obtain ⟨Ξmin, εmin, hΞminpos, hεminpos, hNTclause⟩ :=
    Work.Pert.LiftNTL2.liftF_nearTranslationL1 ρ hρpos
  -- the internal gate parameter of `crux_limit_v3` and its `hsize` slab
  set Ξabs : ℝ := max (max (1 + 64 * Real.pi) (16 * Real.pi / ρ + 1)) Ξmin with hΞabsdef
  have hΞabs : 1 + 64 * Real.pi ≤ Ξabs :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hΞabsmin : Ξmin ≤ Ξabs := le_max_right _ _
  have hbz_sub : Metric.ball (0 : ℂ) (min (εb / 2) 1) ⊆ D₀ :=
    (Metric.ball_subset_ball (min_le_left (εb / 2) 1)).trans
      ((Metric.ball_subset_ball (by linarith : εb / 2 ≤ εb)).trans hεbsub)
  have hρbz : ρ ≤ min (εb / 2) 1 := by
    rw [hρdef]
    exact le_trans (min_le_right (min ρnf r₀) (min r₀' (min (εb / 4) 1)))
      (le_trans (min_le_right r₀' (min (εb / 4) 1))
        (min_le_min (by linarith) le_rfl))
  have hΞabsbz : 16 * Real.pi < (min (εb / 2) 1) * Ξabs := by
    have h1 : 16 * Real.pi / ρ + 1 ≤ Ξabs :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hΞpos : 0 < Ξabs := lt_of_lt_of_le (by positivity) h1
    have h3 : ρ ≤ min (εb / 2) 1 := hρbz
    have h4 : (16 * Real.pi / ρ + 1) * ρ = 16 * Real.pi + ρ := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hρpos), one_mul]
    have h5 : (16 * Real.pi / ρ + 1) * ρ ≤ Ξabs * ρ :=
      mul_le_mul_of_nonneg_right h1 hρpos.le
    have h6 : Ξabs * ρ ≤ Ξabs * (min (εb / 2) 1) :=
      mul_le_mul_of_nonneg_left h3 hΞpos.le
    have h7 : (min (εb / 2) 1) * Ξabs = Ξabs * (min (εb / 2) 1) := by ring
    linarith [h4, h5, h6, h7, hρpos]
  have hΞabspos0 : 0 < Ξabs := lt_of_lt_of_le (by linarith [Real.pi_pos]) hΞabs
  -- ## 0ter. the datum-level AXIS deviation bound and the cover threshold of the window band
  -- `Work.Pert.PinLogDev.anchor_dev_le` at `Ξabs`: the deviation of a pinned coordinate on the
  -- datum gate at the two axis points `± i t` is `≤ A log(t+2) + C + t/64`, with `A, C, Y₀` and
  -- the threshold `Ms` DATUM-level.
  obtain ⟨Aan, Can, Y0an, hAan, hCan, hY0an, Msan, hMsan, hanclause⟩ :=
    Work.Pert.PinLogDev.anchor_dev_le (d := d) (hF := hF) (hd := hd) Ξabs hΞabs
      (rr := ρ) hρpos hρD₀
  -- the datum-level radius on which a gate coordinate has `Φ' ≈ 1`
  obtain ⟨Rtang, hRtang, hderclause⟩ := WaistPinned.deriv_close_on_gate_uniform hF.2.2.2.2.1
  -- the height threshold above which the window `|Re| < 1` is covered by the *margin* waist
  -- (`pert2v2.window_cover_axis`, from the axis deviation bound)
  obtain ⟨Hthr, hHthrpos, hcovthr⟩ :=
    Work.Pert.pert2v2.window_cover_axis (Ξ := Ξabs) (A := Aan) (C := Can) (R₂ := Rtang)
      (Y₀ := Y0an) hΞabspos0 hAan hCan hRtang hY0an
  -- ## 0bis. the datum-level cover threshold for the high band
  -- (`Work.Pert.waist_cover_pinned_v2`, now sorry-free): for every `M ≥ Ms` and every coordinate
  -- `Φ` of `Qm Ξabs α` pinned at `Xc d (-M)`, the band `{|Im| ≥ Yc}` is covered by `Φ '' waist`.
  obtain ⟨Yc, hYcpos, Mc0, hMc0pos, hcover⟩ :=
    Work.Pert.waist_cover_pinned_v2 (d := d) (hF := hF) (hd := hd) Ξabs hΞabs
      (rr := ρ) hρpos hρD₀
  -- the DATUM-level height of the cover with height gain (used by the (A.4.4) row; moved up so
  -- that the single segment height `y₀` can be chosen above it before the crux)
  obtain ⟨Yg, hYgpos, hYg⟩ := Work.Pert.exists_add_mul_log_lt_half Aan (32 * (Can + 1)) hAan
  set Ycov : ℝ := max (max (max (2 * Ξabs + 1) (8 * Rtang + 1)) (max Y0an Yg)) 64 with hYcovdef
  -- the DATUM-level constants of the `(SHADOW)` row (S12): the far translation of the model lift
  -- `F0f f₀` (`Rf`, `Cf`), the far closeness `liftF ≈ F0f` (`Rm`, `Cm`), and the shadow gate `Ξsh`
  obtain ⟨Rf, hRfpos, Cf, hCfpos, hF0f1, hF0f2⟩ := Work.Pert.Ksub2.F0f_far_translation hd
  obtain ⟨Rm, hRm128, Cm, hCmpos, hcloseD⟩ :=
    Work.Pert.pert2v2.LeadWire.liftF_F0f_close_datum hd hρpos
  have hRmpos : 0 < Rm := by linarith
  set Ξsh : ℝ := max Ξabs (max (2 * Rf) (2 * Rm)) with hΞshdef
  have hΞabsΞsh : Ξabs ≤ Ξsh := le_max_left _ _
  have h2RfΞsh : 2 * Rf ≤ Ξsh := le_trans (le_max_left _ _) (le_max_right _ _)
  have h2RmΞsh : 2 * Rm ≤ Ξsh := le_trans (le_max_right _ _) (le_max_right _ _)
  have hYcov64 : (64 : ℝ) ≤ Ycov := le_max_right _ _
  refine ⟨max η₂ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  -- ## 1. the `PertStatement` body
  intro η hη y₁ hy₁ K K' hKc hKDE hK'c hK'Dφ δ hδ
  set H : ℝ := max (max (max (max y₁ Ξabs) Yc) Hthr) (max |y₁| (max Ycov (2 * Ξsh))) + 2
    with hHdef
  have hmaxH : max (max (max y₁ Ξabs) Yc) Hthr ≤ H := by
    rw [hHdef]
    exact le_trans (le_max_left _ _) (le_add_of_nonneg_right (by norm_num))
  have hAbsy₁H : |y₁| ≤ H := by
    rw [hHdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_add_of_nonneg_right (by norm_num))
  have hYcovH : Ycov ≤ H := by
    rw [hHdef]
    exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_add_of_nonneg_right (by norm_num))
  have hΞshH : 2 * Ξsh ≤ H := by
    rw [hHdef]
    exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
      (le_add_of_nonneg_right (by norm_num))
  have hy₁H : y₁ ≤ H :=
    le_trans (le_trans (le_trans (le_max_left y₁ Ξabs) (le_max_left (max y₁ Ξabs) Yc))
      (le_max_left (max (max y₁ Ξabs) Yc) Hthr)) hmaxH
  have hHthrH : Hthr ≤ H :=
    le_trans (le_max_right (max (max y₁ Ξabs) Yc) Hthr) hmaxH
  have hΞabsH : Ξabs ≤ H :=
    le_trans (le_trans (le_trans (le_max_right y₁ Ξabs) (le_max_left (max y₁ Ξabs) Yc))
      (le_max_left (max (max y₁ Ξabs) Yc) Hthr)) hmaxH
  have hYcH : Yc ≤ H :=
    le_trans (le_trans (le_max_right (max y₁ Ξabs) Yc)
      (le_max_left (max (max y₁ Ξabs) Yc) Hthr)) hmaxH
  -- ## 1a. the compact `K̂`: a `Re`-slab containing `K`, intersected with `K` and the band
  -- (the slab is chosen wide enough to contain `K`, so `K ⊆ K̂` and no `ℤ`-translate of `K` is
  -- needed; the band `y₁ ≤ |Im| ≤ H + 3` is the part below the height at which the waist
  -- coordinate takes over)
  obtain ⟨CK, hCK⟩ : ∃ C : ℝ, ∀ w ∈ K, ‖w‖ ≤ C := hKc.isBounded.exists_norm_le
  obtain ⟨RK, hRK⟩ : ∃ R : ℝ, ∀ w ∈ K, |w.re| ≤ R :=
    ⟨CK, fun w hw => le_trans (Complex.abs_re_le_norm w) (hCK w hw)⟩
  set R0 : ℝ := max RK 0 + 2 with hR0def
  have hR0pos : 0 < R0 := by rw [hR0def]; linarith [le_max_right RK 0]
  set S : Set ℂ := {w : ℂ | |w.re| ≤ R0} with hSdef
  -- the reduction blob of `K` (`Work.Pert.pert2v2.exists_reduction_blob`): a compact
  -- `Z ⊆ d.DE` inside the window `|Re| ≤ 1` such that every point of `K` is an integer translate
  -- of a point of `Z`.  It is what makes the low chart (`|Re| < R1`) cover all of `K`.
  obtain ⟨Z, hZc, hZDE, hZwin, hZred⟩ := Work.Pert.pert2v2.reduction_blob_half d hd hKc hKDE
  set Kb : Set ℂ := Z ∪ (S ∩ (K ∪ {w : ℂ | y₁ ≤ |w.im| ∧ |w.im| ≤ H + 3})) with hKbdef
  have hKKb : K ⊆ Kb := by
    intro w hw
    refine Or.inr ⟨?_, Or.inl hw⟩
    show |w.re| ≤ R0
    rw [hR0def]
    linarith [hRK w hw, le_max_left RK 0]
  have hKbc : IsCompact Kb := by
    rw [hKbdef]
    refine hZc.union ?_
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · refine IsClosed.inter ?_ ?_
      · rw [hSdef]
        exact isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
      · refine IsClosed.union hKc.isClosed ?_
        exact (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im)).inter
          (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ))
        (r := R0 + max CK (H + 3) + 1)).subset ?_
      intro w hw
      rw [hSdef] at hw
      obtain ⟨hwS, hwrest⟩ := hw
      have himb : |w.im| ≤ max CK (H + 3) := by
        rcases hwrest with hwK | hwB
        · exact le_trans (Complex.abs_im_le_norm w) (le_trans (hCK w hwK) (le_max_left _ _))
        · exact le_trans hwB.2 (le_max_right _ _)
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
        _ ≤ R0 + max CK (H + 3) := add_le_add hwS himb
        _ ≤ R0 + max CK (H + 3) + 1 := by linarith
  have hKbDE : Kb ⊆ d.DE := by
    intro w hw
    rw [hKbdef] at hw
    rcases hw with hwZ | hwrest
    · exact hZDE hwZ
    · rcases hwrest.2 with hwK | hwB
      · exact hKDE hwK
      · exact d.ends_sub w (lt_of_lt_of_le hy₁ hwB.1)
  -- ## 2. the crux (`Work.PertCrux.crux_limit_v8`: `crux_limit_v7` with the EXPLICIT threshold
  -- `hbig`).  ORDER OF CONSTANTS (all DATUM level, i.e. depending on `d, hF, hd, Ξabs, H, δ, Kb`
  -- only, never on `f`/`α`):
  --   `MK, CW` (Kb) → `ξg, Rgl, Cgl, r₁, M₀s` (the crux's own producers) → the explicit threshold
  --   `Ξthr` → `Ξ' := max Ξthr (max Ξabs H)` → the segment height `y₀ ≥ max (Ycov, 8 Rgl, 32)`,
  --   `4 Ξ' + 32 ≤ y₀` (`LeadWire.seg_setup`; this makes `Kp ⊆ Qreg (some Ξ') none`, the antitone
  --   gate condition of the crux, TRUE: `Ξ'` is now explicit, so `y₀` can be put above it) →
  --   `Kp := Xc d '' {x + i y₀ | x ∈ [0,1]}`, `εp := δ/16`, `ηs := δ/(16 (Cgl+1))`,
  --   `εseg := ηs/(16 y₀²)`, `κ0 := min εseg (1/(64π(y₀+1)))` → the crux call.
  --   Every `α`-dependent threshold of the (A.4.4) row is avoided: the cover/disc height `Ycov`,
  --   the tube radius `Rgl`, and the gate parameters `Ξabs ≤ Ξ'` are all below `y₀`.  The (RIG)
  --   step `ς ≈ Xc d W` is NOT taken from `rig_of_coher_segment` (its radius `r ≤ ρ` is not
  --   available); instead the segment `{x + i y₀}` joins the pinned compact `K_all`, so
  --   `τ ς = φ W ≈ d.φ W = τ₀ (Xc d W)`, and `τ ≈ τ₀` at height `y₀` is a `δ0`-condition (`δτ`).
  have hdEdiff0 : DifferentiableOn ℂ d.E d.DE := Work.Horn.differentiableOn_E d
  obtain ⟨MK0, hMK0b⟩ := hKbc.exists_bound_of_continuousOn (hdEdiff0.continuousOn.mono hKbDE)
  set MK : ℝ := max MK0 0 with hMKdef
  have hMKnn : 0 ≤ MK := le_max_right _ _
  have hMK : ∀ w ∈ Kb, ‖d.E w‖ ≤ MK := fun w hw => le_trans (hMK0b w hw) (le_max_left _ _)
  obtain ⟨CW, hCWpos, hW⟩ := Work.Analysis.PertCrux.orbit_shift_close d hd hKbc hKbDE
    (fun w hw j => d.orbit_avoid (d.φ w) (hKbDE hw).2 j)
  obtain ⟨ξg, hξgpos, hgateP⟩ := Work.PertCrux.gateP_coord_converges d hF hd
  obtain ⟨Rgl, Cgl, hRglpos, hCglpos, hgatelip⟩ := Work.Analysis.PertCrux.gate_fatou_lipschitz hF
  obtain ⟨r₁, M₀s, hr₁pos, hM₀s, hsmallT⟩ := Work.Analysis.PertCrux.small_data hd
  set Ξthr : ℝ := ξg + Ξabs + (1 + 64 * Real.pi) + 2 * (Metric.diam Kb + 1) + (MK + 1) + (CW + 1)
      + (Rgl + 1) + (r₁ + 1) + (M₀s + 1) + (min (εb / 2) 1 + 1) + (1 / (δ / 2) + 1)
      + (δ / 2 + 1) + (Cgl + 1) + (8 * Rgl + 8) + 64 + 5 with hΞthrdef
  -- ## 3. the gate parameter
  set Ξ' : ℝ := max Ξthr (max Ξabs H) with hΞ'def
  have hbig : Ξthr ≤ Ξ' := le_max_left Ξthr (max Ξabs H)
  have hΞabsΞ' : Ξabs ≤ Ξ' :=
    le_trans (le_max_left Ξabs H) (le_max_right Ξthr (max Ξabs H))
  have hΞminΞ' : Ξmin ≤ Ξ' := le_trans hΞabsmin hΞabsΞ'
  have hHΞ' : H ≤ Ξ' :=
    le_trans (le_max_right Ξabs H) (le_max_right Ξthr (max Ξabs H))
  have hΞ'pos : 0 < Ξ' := lt_of_lt_of_le hΞminpos hΞminΞ'
  -- ## 3-S12. the DATUM-level constants of the `(SHADOW)` estimate (horizon `Mn`, Lipschitz
  -- constant `Ksh` at scale `Bsh`, start/step tolerances `ηsh`/`δsh`, the band curve bound `RZ`)
  set Mbd : ℝ := 1000 * (Ξ' + MK + CW + 1) * (2 + Real.log (Ξ' + MK + CW + 2)) with hMbddef
  set Mn : ℕ := ⌈Mbd⌉₊ with hMndef
  set Ksh : ℝ := 1 + 4 * Cf / Rf ^ 2 with hKshdef
  have hKsh1 : 1 ≤ Ksh := by
    rw [hKshdef]; have : 0 ≤ 4 * Cf / Rf ^ 2 := by positivity
    linarith
  set Bsh : ℝ := Rf / 2 with hBshdef
  set Bm : ℝ := min 4 Bsh with hBmdef
  have hBmpos : 0 < Bm := lt_min (by norm_num) (by rw [hBshdef]; positivity)
  have hBm4 : Bm ≤ 4 := min_le_left _ _
  have hBmB : Bm ≤ Bsh := min_le_right _ _
  set ηsh : ℝ := Bm / (4 * Ksh ^ Mn) with hηshdef
  set δsh : ℝ := Bm / (4 * Ksh ^ Mn * ((Mn : ℝ) + 1)) with hδshdef
  have hKMpos : 0 < Ksh ^ Mn := pow_pos (by linarith) _
  have hηshpos : 0 < ηsh := by rw [hηshdef]; positivity
  have hδshpos : 0 < δsh := by rw [hδshdef]; positivity
  have hηsh1 : ηsh ≤ 1 := by
    rw [hηshdef, div_le_one (by positivity)]
    have : 1 ≤ Ksh ^ Mn := one_le_pow₀ hKsh1
    linarith
  obtain ⟨RZ, hRZ⟩ := Work.Pert.pert2v2.LeadWire.Xc_bounded_on_compact d
    (Work.Pert.pert2v2.LeadWire.isCompact_band H (H + 1))
    (fun w hw => d.ends_sub w (lt_of_lt_of_le hy₁ (le_trans hy₁H hw.2.1)))
  set Rs : ℝ := max (2 * (H + 1)) RZ with hRsdef
  have hRspos : 0 < Rs := lt_of_lt_of_le (by linarith [hYcovH, hYcov64]) (le_max_left _ _)
  set εband : ℝ := ηsh / (2 * Rs ^ 2) with hεbanddef
  have hεbandpos : 0 < εband := by rw [hεbanddef]; positivity
  set Rq : ℝ := 4 * (H + 2) + 2 * (Mn : ℝ) + 8 with hRqdef
  set ηu : ℝ := min (δsh / Cm) (min (1 / 1000) (min (1 / (2 * Real.pi)) (1 / Rm))) with hηudef
  have hηupos : 0 < ηu := by
    rw [hηudef]
    exact lt_min (by positivity) (lt_min (by norm_num) (lt_min (by positivity)
      (one_div_pos.mpr hRmpos)))
  have hηuδ : ηu ≤ δsh / Cm := min_le_left _ _
  have hηu1000 : ηu ≤ 1 / 1000 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hηu2π : ηu ≤ 1 / (2 * Real.pi) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hηuRm : ηu ≤ 1 / Rm :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- the S16 constants: the drift bound `CE'` of `R + 1/α - id` on the restricted `DR'`, and the
  -- `Re`-extent of `K'`
  obtain ⟨C_Eo, hC_Eonn, hC_Eo⟩ := Work.Pert.pert2v2.exists_bound_E_sub_id d hy₁
  obtain ⟨CKE0, hCKE0⟩ := hKc.exists_bound_of_continuousOn
    ((hdEdiff0.continuousOn.mono hKDE).sub continuousOn_id)
  obtain ⟨CK', hCK'⟩ : ∃ C : ℝ, ∀ w ∈ K', ‖w‖ ≤ C := hK'c.isBounded.exists_norm_le
  set CE' : ℝ := δ + C_Eo + max CKE0 0 + 1 with hCE'def
  set Nreq : ℝ := Ξsh + H + 2 * (Mn : ℝ) + 16 + (2 * CE' + |η| + |CK'|) with hNreqdef
  have hNextra : 0 ≤ 2 * CE' + |η| + |CK'| := by
    have h1 : 0 ≤ max CKE0 0 := le_max_right _ _
    have h2 : 0 ≤ CE' := by rw [hCE'def]; linarith only [h1, hδ, hC_Eonn]
    have h3 := abs_nonneg η
    have h4 := abs_nonneg CK'
    linarith only [h2, h3, h4]
  obtain ⟨δu, hδupos, hucl⟩ := Work.Pert.u_close_of_nearOn hd hρpos hηupos
  -- ## 3a. the single segment height `y₀` and the pinning compact `Kp`
  obtain ⟨y₀, hy₀Y, hy₀Ξ', hy₀η, hdevZ, hKpc, hKpbasin, hKpcone, hS₀c, hS₀DE⟩ :=
    Work.Pert.pert2v2.LeadWire.seg_setup d hΞ'pos (max (max Ycov (8 * Rgl)) 32)
  have hYcovy₀ : Ycov ≤ y₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy₀Y
  have hRgly₀ : 8 * Rgl ≤ y₀ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy₀Y
  have hy₀32 : (32 : ℝ) ≤ y₀ := le_trans (le_max_right _ _) hy₀Y
  have hy₀pos : 0 < y₀ := by linarith only [hy₀32]
  -- the tolerances of the (A.4.4) residual
  set εp : ℝ := δ / 16 with hεpdef
  have hεppos : 0 < εp := by rw [hεpdef]; positivity
  set ηs : ℝ := δ / (16 * (Cgl + 1)) with hηsdef
  have hηspos : 0 < ηs := by rw [hηsdef]; positivity
  set εseg : ℝ := ηs / (16 * y₀ ^ 2) with hεsegdef
  have hεsegpos : 0 < εseg := by rw [hεsegdef]; positivity
  set κ0 : ℝ := min (min εseg (1 / (64 * Real.pi * (y₀ + 1))))
    (min (min εband (1 / (64 * Real.pi * ((H + 1) + 1))))
      (min ηu (1 / (64 * Real.pi * (Rq / 2 + 1))))) with hκ0def
  have hκ0pos : 0 < κ0 := by
    have hHp : 0 < H + 1 + 1 := by linarith [hYcovH, hYcov64]
    have hRqp : 0 < Rq / 2 + 1 := by
      rw [hRqdef]; have : (0:ℝ) ≤ (Mn : ℝ) := Nat.cast_nonneg _
      linarith [hYcovH, hYcov64]
    rw [hκ0def]
    exact lt_min (lt_min hεsegpos (by positivity))
      (lt_min (lt_min hεbandpos (by positivity)) (lt_min hηupos (by positivity)))
  have hκ0le : κ0 ≤ εseg := le_trans (min_le_left _ _) (min_le_left _ _)
  have hκ0y : κ0 ≤ 1 / (64 * Real.pi * (y₀ + 1)) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hκ0band : κ0 ≤ εband :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hκ0H : κ0 ≤ 1 / (64 * Real.pi * ((H + 1) + 1)) :=
    le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hκ0u : κ0 ≤ ηu :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hκ0q : κ0 ≤ 1 / (64 * Real.pi * (Rq / 2 + 1)) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  -- ## 3bis. the crux at `Ξ'`
  obtain ⟨εc, hεcpos, Lcr, hLcrc, hLcrD, hLcrball, δcr, hδcrpos, hcrux⟩ :=
    Work.PertCrux.crux_limit_v8 d hF hd Ξabs hΞabs (min (εb / 2) 1) (lt_min (by linarith) one_pos)
      hbz_sub hΞabsbz hKbc hKbDE hKpc hKpbasin εp hεppos hMKnn hCWpos.le hMK hW
      (δ := δ / 2) (by linarith) hΞabsΞ' hKpcone hξgpos hgateP hRglpos hCglpos hgatelip
      hr₁pos hM₀s hsmallT hbig
  -- ## 4. the strip lemma (`Work.Pert.Pin.strip_of_pin_v2`): it produces the threshold `Ms` for the
  -- pin point; the coverage statement itself is applied below, once the pin supplies `M`
  obtain ⟨Ms, hMspos, hstripclause⟩ :=
    Work.Pert.Pin.strip_of_pin_v2 d hF hd Ξ' hΞ'pos hρpos hρD₀ hy₁
  -- ## 5. the `phi*` data at `η`
  obtain ⟨hFatD, εη, hεηpos, hphistar⟩ := hη₂clause η (le_trans (le_max_left _ _) hη)
  -- ## 6. the union compact fed to the pin
  set Fatη : Set ℂ := Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
    Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10) with hFatdef
  have hFatD' : Fatη ⊆ d.Dφ := hFatD
  have hFatc : IsCompact Fatη := by
    rw [hFatdef]; exact (isCompact_closedBall _ _).union (isCompact_closedBall _ _)
  set K_all : Set ℂ := Kb ∪ (K' ∪ (Fatη ∪
    ((fun x : ℝ => (x : ℂ) + (y₀ : ℂ) * Complex.I) '' Set.Icc (0 : ℝ) 1))) with hKalldef
  have hKallc : IsCompact K_all := hKbc.union (hK'c.union (hFatc.union hS₀c))
  have hKallD : K_all ⊆ d.Dφ := fun w hw => by
    rcases hw with h | h | h | h
    · exact (hKbDE h).1
    · exact hK'Dφ h
    · exact hFatD' h
    · exact (hS₀DE h).1
  set ε_all : ℝ := min (min δ εc) (min εη (min εseg εband)) with hεalldef
  have hε_all : 0 < ε_all := by
    rw [hεalldef]
    exact lt_min (lt_min hδ hεcpos) (lt_min hεηpos (lt_min hεsegpos hεbandpos))
  -- ## 6bis. the single pinned `Φm` (`Work.PertCrux.coordP_close_pinned`)
  obtain ⟨M, hMM, Lc, hLcc, hLcD, δc, hδcpos, hcoord⟩ :=
    Work.PertCrux.coordP_close_pinned d hF hd Ξ' hΞ'pos hKallc hKallD ε_all hε_all
      (max (max Ms Msan) 1)
  have hMsM : Ms ≤ M :=
    le_trans (le_trans (le_max_left Ms Msan) (le_max_left (max Ms Msan) 1)) hMM
  have hMsanM : Msan ≤ M :=
    le_trans (le_trans (le_max_right Ms Msan) (le_max_left (max Ms Msan) 1)) hMM
  -- ## 6ter. the strip coverage at this pin point
  obtain ⟨Ls, hLsc, hLsD, hLsball, δs, hδspos, hstrip⟩ := hstripclause M hMsM
  -- ## 6quater. the axis deviation bound of `anchor_dev_le` at this pin point
  obtain ⟨Lan, hLanc, hLanD, hLanball, δan, hδanpos, hanmain⟩ := hanclause M hMsanM
  -- ## 7. the emitted neighbourhood: union of the producers' sets, min of the tolerances
  set L : Set ℂ := Lcr ∪ (Lc ∪ (Ls ∪ (Lan ∪ Metric.closedBall (0 : ℂ) ρ))) with hLdef
  -- the tolerance at which the normal-form smallness `‖σ‖, ‖rotOf f‖ ≤ εmin` and the gate
  -- admissibility `4 Ξ' + 8 ≤ 1/‖α‖` hold
  set δsm : ℝ := min (min (min (min (ρ / 4) (ρ / (4 * Csm))) (εmin * ρ / (4 * Csm)))
    (ρ / ((4 * Ξ' + 8) * (4 * Csm)))) (ρ ^ 2 / (2 * Csm)) with hδsmdef
  -- the `δ0`-condition of the (A.4.4) residual: `tauC ≈ τ₀` on the axis disc at height `y₀`
  set δτ : ℝ := ρ ^ 2 * κ0 / (60 * Csm) with hδτdef
  -- the `δ0`-conditions of the `(SHADOW)` row: `u ≈ (f₀ - id)/z²` (`δu`) and the smallness of
  -- `α`, `u 0 - 1` at the scale `θA` (`δA`: `‖α‖ ≤ ηu`, `‖α‖ Rq ≤ 1/8`, `Re (1/α) ≥ 4 Nreq`)
  set θA : ℝ := min ηu (min (1 / (4 * Rq)) (1 / (4 * Nreq))) with hθAdef
  set δA : ℝ := ρ ^ 2 * θA / (2 * Csm) with hδAdef
  set δ0 : ℝ := min (min (min δcr δc) (min δs (min δan (ρ ^ 3 / 32))))
    (min δsm (min δτ (min δu δA))) with hδ0def
  have hLcpt : IsCompact L := by
    rw [hLdef]
    exact hLcrc.union (hLcc.union (hLsc.union (hLanc.union
      (isCompact_closedBall (0 : ℂ) ρ))))
  have hLD : L ⊆ D₀ := by
    rw [hLdef]
    exact Set.union_subset hLcrD (Set.union_subset hLcD (Set.union_subset hLsD
      (Set.union_subset hLanD hρD₀)))
  have hδsmpos : 0 < δsm := by
    rw [hδsmdef]
    exact lt_min (lt_min (lt_min (lt_min (by positivity) (by positivity)) (by positivity))
      (by positivity)) (by positivity)
  have hδ0pos : 0 < δ0 := by
    rw [hδ0def]
    exact lt_min (lt_min (lt_min hδcrpos hδcpos) (lt_min hδspos (lt_min hδanpos
      (by positivity)))) (lt_min hδsmpos (lt_min (by rw [hδτdef]; positivity)
      (lt_min hδupos (by
        have hRqp : 0 < Rq := by
          rw [hRqdef]; have : (0:ℝ) ≤ (Mn : ℝ) := Nat.cast_nonneg _
          linarith [hYcovH, hYcov64]
        have hNp : 0 < Nreq := by
          rw [hNreqdef]; have : (0:ℝ) ≤ (Mn : ℝ) := Nat.cast_nonneg _
          have : 0 ≤ Ξsh := le_trans hΞabspos0.le hΞabsΞsh
          linarith [hYcovH, hYcov64]
        rw [hδAdef, hθAdef]
        have : 0 < min ηu (min (1 / (4 * Rq)) (1 / (4 * Nreq))) :=
          lt_min hηupos (lt_min (by positivity) (by positivity))
        positivity))))
  have hδ0nf : δ0 ≤ ρ ^ 3 / 32 :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_right _ _)))
  have hδ0c : δ0 ≤ δc :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ0s : δ0 ≤ δs :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ0cr : δ0 ≤ δcr :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ0an : δ0 ≤ δan :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_left _ _)))
  have hδ0sm : δ0 ≤ δsm := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ0τ : δ0 ≤ ρ ^ 2 * κ0 / (60 * Csm) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ0u : δ0 ≤ δu :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_left _ _)))
  have hδ0A : δ0 ≤ ρ ^ 2 * θA / (2 * Csm) :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (min_le_right _ _)))
  have hδ0ρ4 : δ0 ≤ ρ / 4 :=
    le_trans hδ0sm (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hδ0σ4 : δ0 ≤ ρ / (4 * Csm) :=
    le_trans hδ0sm (le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
      (le_trans (min_le_left _ _) (min_le_right _ _))))
  have hδ0ε : δ0 ≤ εmin * ρ / (4 * Csm) :=
    le_trans hδ0sm (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hδ0α : δ0 ≤ ρ / ((4 * Ξ' + 8) * (4 * Csm)) :=
    le_trans hδ0sm (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ0rho2 : δ0 ≤ ρ ^ 2 / (2 * Csm) :=
    le_trans hδ0sm (min_le_right _ _)
  have hLcrL : Lcr ⊆ L := by intro x hx; rw [hLdef]; exact Or.inl hx
  have hLcL : Lc ⊆ L := by intro x hx; rw [hLdef]; exact Or.inr (Or.inl hx)
  have hLsL : Ls ⊆ L := by intro x hx; rw [hLdef]; exact Or.inr (Or.inr (Or.inl hx))
  have hLanL : Lan ⊆ L := by
    intro x hx; rw [hLdef]; exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
  have hballL : Metric.closedBall (0 : ℂ) ρ ⊆ L := by
    intro x hx; rw [hLdef]; exact Or.inr (Or.inr (Or.inr (Or.inr hx)))
  have hKbKall : Kb ⊆ K_all := by
    intro x hx; rw [hKalldef]; exact Or.inl hx
  have hεc_all : ε_all ≤ εc := le_trans (min_le_left _ _) (min_le_right δ εc)
  have hεδ_all : ε_all ≤ δ := le_trans (min_le_left _ _) (min_le_left δ εc)
  have hεseg_all : ε_all ≤ εseg :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεband_all : ε_all ≤ εband :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hS₀Kall : (fun x : ℝ => (x : ℂ) + (y₀ : ℂ) * Complex.I) '' Set.Icc (0 : ℝ) 1 ⊆ K_all := by
    intro x hx; rw [hKalldef]; exact Or.inr (Or.inr (Or.inr hx))
  refine ⟨L, hLcpt, hLD, δ0, hδ0pos, ?_⟩
  intro f Df hNear hf0 hInF1
  -- ## 7a. the normal-form data
  have hNearNF : MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρ) (ρ ^ 3 / 32) :=
    nearOn_mono hNear hballL hδ0nf
  obtain ⟨σ, u, huD, hu0ne, hub, hform, hderiv0, hσC⟩ := hNF ρ hρpos hρρnf hNearNF hf0
  set α : ℂ := MandelDim.rotOf f with hαdef
  -- ## 7a'. the normal-form smallness (`Work.Pert.small_of_nearOn`)
  have hNearSm : MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρ) δ0 :=
    nearOn_mono hNear hballL le_rfl
  have h2δ : 2 * δ0 ≤ ρ := by linarith [hδ0ρ4]
  obtain ⟨hu01, hσsmall, hαsmall⟩ :=
    hSmall hρpos hρr₀ hδ0pos h2δ hρpos hNearSm hf0 huD hub hform
  have hσ_eps : ‖σ‖ ≤ εmin := by
    have h1 : Csm * δ0 / ρ ≤ Csm * (εmin * ρ / (4 * Csm)) / ρ := by
      have h2 : 0 < ρ := hρpos
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hδ0ε hCsmp.le) hρpos.le
    have h3 : Csm * (εmin * ρ / (4 * Csm)) / ρ = εmin / 4 := by
      field_simp
    linarith [hσsmall, h1, h3, hεminpos]
  have hσ_half : ‖σ‖ ≤ 1 / 4 := by
    have h1 : Csm * δ0 / ρ ≤ Csm * (ρ / (4 * Csm)) / ρ := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hδ0σ4 hCsmp.le) hρpos.le
    have h3 : Csm * (ρ / (4 * Csm)) / ρ = 1 / 4 := by
      field_simp
    linarith [hσsmall, h1, h3]
  have hα_eps : ‖α‖ ≤ εmin := by
    rw [hαdef]
    exact le_trans hαsmall (by
      have h1 : Csm * δ0 / ρ ≤ Csm * (εmin * ρ / (4 * Csm)) / ρ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hδ0ε hCsmp.le) hρpos.le
      have h3 : Csm * (εmin * ρ / (4 * Csm)) / ρ = εmin / 4 := by field_simp
      linarith [h1, h3, hεminpos])
  have hInF1α : MandelDim.InF1 α := by rw [hαdef]; exact hInF1
  have hαne : α ≠ 0 := by
    intro hz
    rw [hz] at hInF1α
    simp [MandelDim.InF1] at hInF1α
  have hu0b : 1 / 2 ≤ ‖u 0‖ := (hub 0 (Metric.mem_ball_self hρpos)).1
  have hσu_lt : ‖σ * u 0‖ < 1 := by
    rw [norm_mul]
    have h2 : ‖u 0‖ ≤ 2 := (hub 0 (Metric.mem_ball_self hρpos)).2
    nlinarith [hσ_half, norm_nonneg σ, hu0b, h2]
  have hd0 : deriv f 0 ≠ 0 := by
    rw [hderiv0]
    intro hz
    have h1 : σ * u 0 = 1 := by linear_combination -hz
    rw [h1, norm_one] at hσu_lt
    exact absurd hσu_lt (lt_irrefl 1)
  have hexp : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) := by
    rw [hαdef, exp_rotOf f hd0, hderiv0]
  -- ## 7b. the gate hypotheses
  have h4Ξ : 4 * Ξ' + 8 ≤ 1 / ‖α‖ := by
    have h1 : ‖α‖ ≤ 1 / (4 * Ξ' + 8) := by
      rw [hαdef]
      have h2 : ‖MandelDim.rotOf f‖ ≤ Csm * δ0 / ρ := hαsmall
      have h2' : Csm * δ0 / ρ ≤ 1 / (4 * Ξ' + 8) := by
        have h2'' : Csm * δ0 / ρ ≤ Csm * (ρ / ((4 * Ξ' + 8) * (4 * Csm))) / ρ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hδ0α hCsmp.le) hρpos.le
        have h3 : Csm * (ρ / ((4 * Ξ' + 8) * (4 * Csm))) / ρ = 1 / (4 * (4 * Ξ' + 8)) := by
          field_simp
        have h4 : 1 / (4 * (4 * Ξ' + 8)) ≤ 1 / (4 * Ξ' + 8) :=
          one_div_le_one_div_of_le (by linarith [hΞ'pos]) (by linarith [hΞ'pos])
        linarith
      linarith
    rw [le_div_iff₀ (norm_pos_iff.mpr hαne)]
    rw [le_div_iff₀ (by linarith [hΞ'pos] : (0:ℝ) < 4 * Ξ' + 8)] at h1
    linarith
  have hQAdm : MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / α)) (some (-(Ξ' : ℂ))) :=
    (qadm hInF1α hΞ'pos h4Ξ).2
  have h16Ξ : 16 * Real.pi / Ξ' < ρ := by
    have h4 : (16 * Real.pi / ρ + 1) * ρ = 16 * Real.pi + ρ := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hρpos), one_mul]
    have h5 : (16 * Real.pi / ρ + 1) * ρ ≤ Ξ' * ρ :=
      mul_le_mul_of_nonneg_right
        (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΞabsΞ') hρpos.le
    have h6 : 16 * Real.pi < ρ * Ξ' := by
      rw [h4, mul_comm Ξ' ρ] at h5
      linarith only [h5, hρpos]
    rw [div_lt_iff₀ hΞ'pos]
    exact h6
  have hτQ : ∀ z ∈ Work.Pert.Qm Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) ρ := by
    intro z hz
    exact Metric.closedBall_subset_ball h16Ξ
      (Work.Pert.tauC_gate_sub_closedBall hΞ'pos hρpos huD hub hexp hInF1α hQAdm z hz)
  have hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ' α) :=
    (hNTclause hΞminΞ' hInF1α hαne hσ_eps hα_eps huD hub hexp).1
  -- the `Qp` gate (`Work.Pert.Tt_mem_Qm_iff`: `Tt α '' Qp Ξ α = Qm Ξ α`) and its `τ`-bound
  have hQAdm_p : MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α)) :=
    (qadm hInF1α hΞ'pos h4Ξ).1
  have hNTp : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qp Ξ' α) :=
    (hNTclause hΞminΞ' hInF1α hαne hσ_eps hα_eps huD hub hexp).2
  have hτTt : ∀ z : ℂ, Work.Pert.tauC σ α (Work.Pert.Tt α z) = Work.Pert.tauC σ α z := by
    intro z
    have hα1 : (2 * Real.pi * Complex.I * α) * (1 / α) = 2 * Real.pi * Complex.I := by
      rw [one_div, mul_assoc, mul_inv_cancel₀ hαne, mul_one]
    have harg : -(2 * Real.pi * Complex.I * α * (z - 1 / α))
        = 2 * Real.pi * Complex.I + (-(2 * Real.pi * Complex.I * α * z)) := by
      rw [mul_sub, hα1]
      ring
    simp only [Work.Pert.tauC, Work.Pert.Tt]
    rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
  have hτQp : ∀ z ∈ Work.Pert.Qp Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) ρ := by
    intro z hz
    have h1 : Work.Pert.Tt α z ∈ Work.Pert.Qm Ξ' α := Work.Pert.Tt_mem_Qm_iff.mpr hz
    rw [← hτTt z]
    exact hτQ _ h1
  -- ## 7c. the single pinned `Φm`, fed to every remaining producer
  obtain ⟨Φm, hΦm, hKall_sub, hclose_all, hpinmem, hpinval⟩ :=
    hcoord f Df ρ u σ α (nearOn_mono hNear hLcL hδ0c) hf0 hInF1 hαdef hρpos huD hub
      hform hexp hτQ hQAdm hNT
  -- ## 7c-ter. the CRUX at `Kb` with the pinned `Φm`: it produces the low piece's data
  -- (`Φp`, the subgate `Qp'`, the landing time `m_x`, the deck integer `k_x = 0`, the landing
  -- clause and the residual on `Kb`)
  obtain ⟨Φp, Qp', m_x, hcruxbody⟩ :=
    hcrux f Df ρ u σ α (nearOn_mono hNear hLcrL hδ0cr) hf0 hInF1 hαdef hρpos huD hub
      hform hexp hτQ hτQp hQAdm hQAdm_p hNT hNTp Φm hΦm
      (fun w hw => hKall_sub (Or.inl hw))
      (fun w hw => lt_of_lt_of_le (hclose_all w (Or.inl hw)) hεc_all)
  obtain ⟨hmbound, hΦp, hpinKp, hQp'eq, hQp'open, hQp'sub, hinjτ, hretstep, hclause, hresid⟩ :=
    hcruxbody
  -- ## 7d. the DATUM gate `Qm Ξabs α` (the gate of `φ_f`; session 40 §2)
  have hΞabspos : 0 < Ξabs := lt_of_lt_of_le hΞminpos hΞabsmin
  have h4Ξabs : 4 * Ξabs + 8 ≤ 1 / ‖α‖ := le_trans (by linarith only [hΞabsΞ']) h4Ξ
  have hQAdm_abs : MandelDim.QAdm (some ((Ξabs : ℂ) - 1 / α)) (some (-(Ξabs : ℂ))) :=
    (qadm hInF1α hΞabspos h4Ξabs).2
  have hNT_abs : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Qm Ξabs α) :=
    (hNTclause hΞabsmin hInF1α hαne hσ_eps hα_eps huD hub hexp).1
  have hΞabsρ : 16 * Real.pi / Ξabs < ρ := by
    have h1 : 16 * Real.pi / ρ + 1 ≤ Ξabs := le_trans (le_max_right _ _) (le_max_left _ _)
    have h2 : 16 * Real.pi / ρ < Ξabs := by linarith
    have h3 : 16 * Real.pi < Ξabs * ρ := by
      rw [div_lt_iff₀ hρpos] at h2
      linarith
    rw [div_lt_iff₀ hΞabspos]
    linarith
  have hτQ_abs : ∀ z ∈ Qm Ξabs α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) ρ := by
    intro z hz
    exact Metric.closedBall_subset_ball hΞabsρ
      (Work.Pert.tauC_gate_sub_closedBall hΞabspos hρpos huD hub hexp hInF1α hQAdm_abs z hz)
  have hsub_gate : Qm Ξ' α ⊆ Qm Ξabs α := by
    intro z hz
    rw [Work.Pert.Qm_mem_iff] at hz ⊢
    exact ⟨by linarith only [hz.1, hΞabsΞ'], by linarith only [hz.2, hΞabsΞ']⟩
  -- ## 7e. the extension `ΨE` of the crux coordinate to the datum gate
  obtain ⟨ΨE, hΨE, hagree, -, -⟩ :=
    Work.Pert.pert2v2.exists_fatouCoord_extend_agree (hEx := hF.1) (hUn := hF.2.2.1)
      f Df (tauC σ α) hQAdm_abs hNT_abs.1 hQAdm hNT.1 hsub_gate hΦm
  -- ## 7e-bis. the extension `Ψp` of the crux's upper-gate coordinate to the datum upper gate
  -- (session 40 §2: the A.4.2 normalisation and the waist walk live on `Qp Ξabs α`, so the low
  -- piece must be phrased with a coordinate on that gate; on `Qp Ξ' α` it agrees with `Φp`, and
  -- `RlowPiece` evaluates it only on the subgate `Qp' ⊆ Qp Ξ' α`).
  have hQAdm_p_abs : MandelDim.QAdm (some (Ξabs : ℂ)) (some (-(Ξabs : ℂ) + 1 / α)) :=
    (qadm hInF1α hΞabspos h4Ξabs).1
  have hNTp_abs : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Qp Ξabs α) :=
    (hNTclause hΞabsmin hInF1α hαne hσ_eps hα_eps huD hub hexp).2
  have hsub_gate_p : Qp Ξ' α ⊆ Qp Ξabs α := by
    intro z hz
    exact Work.Pert.Tt_mem_Qm_iff.mp (hsub_gate (Work.Pert.Tt_mem_Qm_iff.mpr hz))
  obtain ⟨Ψp, hΨp, hagreep, -, -⟩ :=
    Work.Pert.pert2v2.exists_fatouCoord_extend_agree (hEx := hF.1) (hUn := hF.2.2.1)
      f Df (tauC σ α) hQAdm_p_abs hNTp_abs.1 hQAdm_p hNTp.1 hsub_gate_p hΦp
  -- ## 7f. `φ_f` on the datum gate
  set φ : ℂ → ℂ := coordP f Df (tauC σ α) ΨE (Qm Ξabs α) with hφdef
  set Dφ : Set ℂ := DphiP f Df (tauC σ α) ΨE (Qm Ξabs α) with hDφdef
  -- the transfer of the crux coordinate from `Qm Ξ' α` to `Qm Ξabs α`
  have hTransfer : ∀ w : ℂ, w ∈ DphiP f Df (tauC σ α) Φm (Qm Ξ' α) →
      w ∈ Dφ ∧ φ w = coordP f Df (tauC σ α) Φm (Qm Ξ' α) w := by
    intro w hw
    have h1 := Work.Pert.pert2v2.DphiP_transfer_gate (f := f) (F := Work.Pert.liftF u σ α)
      (τ := tauC σ α) (Φ := Φm) (ΨE := ΨE) (Df := Df) (Q := Qm Ξ' α) (Q' := Qm Ξabs α)
      hsub_gate hΨE.2.1 (fun z hz hz' => hΨE.2.2 z hz hz')
      (fun z hz => Work.Pert.Ksub2.abel_on_gate hρpos hΞabspos hNT_abs hτQ_abs hform hαne hexp
        (fun z hz' => (hub z hz').1) z hz)
      (fun z hz z' hz' k hk => (MandelDim.fatouL1_of_fatou hF).2.1 (some ((Ξabs : ℂ) - 1 / α))
        (some (-(Ξabs : ℂ))) (Work.Pert.liftF u σ α) ΨE hQAdm_abs hNT_abs hΨE z hz z' hz' k hk)
      hΦm.2.1 hagree hw
    exact ⟨h1.1, h1.2.symm⟩
  have hKallDφ : K_all ⊆ Dφ := fun w hw => (hTransfer w (hKall_sub hw)).1
  have hK'Dφ : K' ⊆ Dφ := fun w hw => hKallDφ (Or.inr (Or.inl hw))
  -- ## 7g. the structural facts about `ΨE` and `φ` on the datum gate
  have hQopen : IsOpen (Qm Ξabs α) := isOpen_Qm Ξabs α
  have hτD : DifferentiableOn ℂ (tauC σ α) (Qm Ξabs α) := fun z hz =>
    (differentiableAt_tauC_of_mem_Qm hΞabspos hInF1α hz).differentiableWithinAt
  have hderΦ : ∀ z ∈ Qm Ξabs α, deriv ΨE z ≠ 0 :=
    Work.Parab.inversion.deriv_ne_zero_of_injOn hQopen hΨE.1 hΨE.2.1
  have hAbel : ∀ z ∈ Qm Ξabs α, liftF u σ α z ∈ Qm Ξabs α → ΨE (liftF u σ α z) = ΨE z + 1 :=
    fun z hz hz' => hΨE.2.2 z hz hz'
  have hτF : ∀ z ∈ Qm Ξabs α, tauC σ α (liftF u σ α z) = f (tauC σ α z) :=
    Work.Pert.Ksub2.abel_on_gate hρpos hΞabspos hNT_abs hτQ_abs hform hαne hexp
      (fun z hz => (hub z hz).1)
  have hOrb : ∀ z ∈ Qm Ξabs α, ∀ z' ∈ Qm Ξabs α, ∀ k : ℕ, ΨE z' = ΨE z + (k : ℂ) →
      (∀ j : ℕ, j ≤ k → (liftF u σ α)^[j] z ∈ Qm Ξabs α) ∧
        (liftF u σ α)^[k] z = z' :=
    fun z hz z' hz' k hk =>
      (MandelDim.fatouL1_of_fatou hF).2.1 (some ((Ξabs : ℂ) - 1 / α)) (some (-(Ξabs : ℂ)))
        (Work.Pert.liftF u σ α) ΨE hQAdm_abs hNT_abs hΨE z hz z' hz' k hk
  have hseed : ∀ u' ∈ ΨE '' (Qm Ξabs α),
      seedP (tauC σ α) ΨE (Qm Ξabs α) u' ∈ Df := by
    intro u' hu'
    have hmem : Work.Pert.invOn ΨE (Qm Ξabs α) u' ∈ Qm Ξabs α := Work.Pert.invOn_mem hu'
    have h1 : Work.Pert.tauC σ α (Work.Pert.invOn ΨE (Qm Ξabs α) u') ∈ Metric.ball (0 : ℂ) ρ :=
      hτQ_abs _ hmem
    exact hNear.2.1 (hballL (Metric.ball_subset_closedBall h1))
  have hDφopen : IsOpen Dφ := by
    rw [hDφdef]
    exact DphiP_open hNear.1 hQopen hΨE.1 hτD hΨE.2.1 hderΦ hNear.2.2.1
  have hφholo : DifferentiableOn ℂ φ Dφ := by
    rw [hφdef, hDφdef]
    exact coordP_holo hNear.1 hQopen hΨE.1 hτD hΨE.2.1 hderΦ hNear.2.2.1
      hAbel hτF hOrb hseed
  have hφabel : ∀ w ∈ Dφ, w + 1 ∈ Dφ → φ w ∈ Df ∧ φ (w + 1) = f (φ w) := by
    intro w hw hw1
    have hw' : w ∈ DphiP f Df (tauC σ α) ΨE (Qm Ξabs α) := hw
    have hw1' : w + 1 ∈ DphiP f Df (tauC σ α) ΨE (Qm Ξabs α) := hw1
    have hab := coordP_abel (f := f) (Df := Df) (F := liftF u σ α) (τ := tauC σ α)
      (Φ := ΨE) (Q := Qm Ξabs α) hΨE.2.1 hAbel hτF hOrb hseed hw' hw1'
    rw [hφdef]
    exact hab
  -- the strip `Dφ_strip`: `strip_of_pin_v2` at the crux gate, transferred to the datum gate
  have hstrip' : ∀ w : ℂ, y₁ ≤ |w.im| → |w.re| ≤ 1 → w ∈ Dφ := by
    intro w hw1 hw2
    have h1 := hstrip f Df u σ α (nearOn_mono hNear hLsL hδ0s) hf0 hInF1 hαdef huD hub
      hform hexp hτQ hQAdm hNT Φm hΦm hpinmem hpinval w hw1 hw2
    exact (hTransfer w h1).1
  -- ## 8. the R-block: TWO-PIECE R (lead skeleton 10-02; the RBDE route is dead: its `orbit` is false)
  have hφclose : ∀ w ∈ K', ‖φ w - d.φ w‖ < δ := by
    intro w hw
    have h1 : φ w = coordP f Df (tauC σ α) Φm (Qm Ξ' α) w :=
      (hTransfer w (hKall_sub (Or.inr (Or.inl hw)))).2
    rw [h1]
    exact lt_of_lt_of_le (hclose_all w (Or.inr (Or.inl hw))) hεδ_all
  have hFatKall : Fatη ⊆ K_all := by
    intro x hx; rw [hKalldef]; exact Or.inr (Or.inr (Or.inl hx))
  have hFatU : Fatη ⊆ Dφ := fun x hx => hKallDφ (hFatKall hx)
  have hεη_all : ε_all ≤ εη := le_trans (min_le_right _ _) (min_le_left _ _)
  have hFatClose : ∀ w ∈ Fatη, ‖φ w - d.φ w‖ < εη := by
    intro w hw
    have h1 : φ w = coordP f Df (tauC σ α) Φm (Qm Ξ' α) w :=
      (hTransfer w (hKall_sub (hFatKall hw))).2
    rw [h1]
    exact lt_of_lt_of_le (hclose_all w (hFatKall hw)) hεη_all
  obtain ⟨hDsub, hInjUp, hInjDn, hStarClose, hStarDeriv⟩ :=
    hphistar φ Dφ hDφopen hφholo hFatU hFatClose
  -- ## 8a. the (A.4.2) constant of the crux pair on the extended coordinate
  -- Step 1: on the crux gates, `Work.Pert.gate_T_relation` (`FatouUnique` on `Qp Ξ' α`).
  have hcommF : ∀ z : ℂ, Work.Pert.liftF u σ α (Work.Pert.Tt α z)
      = Work.Pert.Tt α (Work.Pert.liftF u σ α z) := by
    intro z
    have h := Work.Pert.pert2v2.liftF_add_int_div u σ α hαne (-1) z
    have h1 : z + ((-1 : ℤ) : ℂ) / α = Work.Pert.Tt α z := by
      push_cast; rw [Work.Pert.Tt]; ring
    have h2 : Work.Pert.liftF u σ α z + ((-1 : ℤ) : ℂ) / α
        = Work.Pert.Tt α (Work.Pert.liftF u σ α z) := by
      push_cast; rw [Work.Pert.Tt]; ring
    rw [h1, h2] at h
    exact h
  have hA42 : ∃ dlow : ℂ, ∀ z ∈ Work.Pert.Qp Ξ' α, ΨE (Work.Pert.Tt α z) = Φp z + dlow := by
    refine Work.Pert.gate_T_relation (F := Work.Pert.liftF u σ α) (α := α)
      hF.2.2.1 hQAdm_p hQAdm_abs hNTp.1 ?_ (fun w _ => hcommF w) hΨE hΦp
    intro w hw
    exact hsub_gate (Work.Pert.Tt_mem_Qm_iff.mpr hw)
  obtain ⟨dlow, hdlow⟩ := hA42
  -- Step 2: extend the normalisation to the *datum* upper gate `Qp Ξabs α` (both sides are Fatou
  -- coordinates there, so `FatouUnique` + one normalisation point suffice).
  set z₀ : ℂ := Work.Pert.Xc d (((-M : ℝ)) : ℂ) + 1 / α with hz₀def
  have hz₀Qp : z₀ ∈ Work.Pert.Qp Ξ' α := by
    refine Work.Pert.Tt_mem_Qm_iff.mp ?_
    have h : Work.Pert.Tt α z₀ = Work.Pert.Xc d (((-M : ℝ)) : ℂ) := by
      rw [hz₀def, Work.Pert.Tt]; ring
    rw [h]; exact hpinmem
  have hΨp_rel : ∀ z ∈ Work.Pert.Qp Ξabs α, Ψp z = ΨE (Work.Pert.Tt α z) - dlow := by
    intro z hz
    exact Work.Pert.pert2v2.PsiPair_rel (F := Work.Pert.liftF u σ α) (ΨE := ΨE) (Ψp := Ψp)
      (Ξ := Ξabs) (α := α) (d := dlow) (z₀ := z₀)
      hF.2.2.1 hQAdm_p_abs hNTp_abs.1 hΨE hΨp hcommF
      (fun w hw => Work.Pert.Tt_mem_Qm_iff.mpr hw)
      (fun w _ hFw => by rw [hcommF w]; exact Work.Pert.Tt_mem_Qm_iff.mpr hFw)
      (hsub_gate_p hz₀Qp)
      (by rw [hagreep z₀ hz₀Qp]
          exact eq_sub_iff_add_eq.mpr (hdlow z₀ hz₀Qp).symm)
      z hz
  -- ## 8a-ter. the `τ`-Abel relation on the upper datum gate, and the elementary datum facts
  -- `σ ≠ 0` (`σ = 0` would force `α ∈ ℤ`, contradicting `‖α‖ < 1`)
  have hσne : σ ≠ 0 := by
    intro hσ0
    have hexp1 : Complex.exp (2 * Real.pi * Complex.I * α) = 1 := by
      rw [← hexp, hσ0, zero_mul, sub_zero]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
    have hαn : α = (n : ℂ) := by
      have hfac : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
        exact_mod_cast Real.pi_ne_zero
      exact mul_left_cancel₀ hfac (by simpa [mul_comm] using hn)
    have hlt : ‖α‖ < 1 := by
      have hpos : (0 : ℝ) < ‖α‖ := norm_pos_iff.mpr hαne
      have h1 : (1 : ℝ) < 4 * Ξ' + 8 := by linarith [hΞ'pos]
      have h2 : (1 : ℝ) < 1 / ‖α‖ := lt_of_lt_of_le h1 h4Ξ
      rw [lt_div_iff₀ hpos] at h2
      linarith
    have hge : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
      rcases eq_or_ne n 0 with h | h
      · exfalso
        rw [h] at hαn
        simp only [Int.cast_zero] at hαn
        exact hαne hαn
      · simp only [Complex.norm_intCast]; exact_mod_cast Int.one_le_abs h
    rw [hαn] at hlt
    linarith
  -- `IsOpen d.DE`
  have hdDEopen : IsOpen d.DE := by
    rw [isOpen_iff_mem_nhds]
    intro w hw
    have hbasin_open : IsOpen (MandelDim.ParabolicBasin f₀ D₀) := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      obtain ⟨U, hU, hmap, hconv⟩ := hz
      obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
      exact Filter.mem_of_superset (hVopen.mem_nhds hzV) (fun y hy =>
        ⟨V, hVopen.mem_nhds hy, fun n => (hmap n).mono hVU Subset.rfl, hconv.mono hVU⟩)
    have hφcont : ContinuousAt d.φ w :=
      (d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hw.1)).continuousAt
    exact Filter.inter_mem (d.Dφ_open.mem_nhds hw.1)
      (hφcont.preimage_mem_nhds (hbasin_open.mem_nhds hw.2))
  have hdEdiff : DifferentiableOn ℂ d.E d.DE := Work.Horn.differentiableOn_E d
  -- `InF1 α` in the inverted form used by the gate geometry
  have hInF1inv : |(1 / α).im| < (1 / α).re := by
    have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1α
    have hne : α ≠ 0 := fun h => by rw [h] at hre; simp at hre
    have hns : (0 : ℝ) < Complex.normSq α := Complex.normSq_pos.mpr hne
    rw [one_div, Complex.inv_im, Complex.inv_re]
    simp only [abs_div, abs_neg, abs_of_pos hns]
    exact div_lt_div_of_pos_right hInF1α hns
  -- `tauC` is differentiable on the upper gate too (via `tauC ∘ Tt = tauC`)
  have hτp : DifferentiableOn ℂ (tauC σ α) (Qp Ξabs α) := by
    intro z hz
    have hz' : Tt α z ∈ Qm Ξabs α := Work.Pert.Tt_mem_Qm_iff.mpr hz
    have h1 : DifferentiableWithinAt ℂ (tauC σ α) (Qm Ξabs α) (Tt α z) :=
      ((Work.Pert.DiffGate.diff_tauC_gate hΞabspos hInF1α).2) (Tt α z) hz'
    have h2 : DifferentiableWithinAt ℂ (Tt α) (Qp Ξabs α) z :=
      ((differentiableAt_id.sub_const (1 / α)).differentiableWithinAt)
    have h3 := h1.comp z h2 (fun y hy => (Work.Pert.Tt_mem_Qm_iff.mpr hy))
    exact h3.congr (fun y _ => (hτTt y).symm) (hτTt z).symm
  have hτFp : ∀ z ∈ Qp Ξabs α, tauC σ α (liftF u σ α z) = f (tauC σ α z) := by
    intro z hz
    have hz' : Tt α z ∈ Qm Ξabs α := Work.Pert.Tt_mem_Qm_iff.mpr hz
    calc tauC σ α (liftF u σ α z)
        = tauC σ α (Tt α (liftF u σ α z)) := (hτTt (liftF u σ α z)).symm
      _ = tauC σ α (liftF u σ α (Tt α z)) := by rw [hcommF z]
      _ = f (tauC σ α (Tt α z)) := hτF (Tt α z) hz'
      _ = f (tauC σ α z) := by rw [hτTt z]
  -- ## 8b-bis. the cover of the window by the *margin* waist (the input of S11/S13)
  -- the derivative bound on the datum gate (from the datum-level estimate `deriv_close_on_gate_uniform`)
  have hderb : ∀ (z : ℂ) (R : ℝ), Rtang ≤ R → Metric.ball z R ⊆ Qm Ξabs α →
      ‖deriv ΨE z - 1‖ ≤ 1 / 2 :=
    fun z R hR hball => hderclause (liftF u σ α) ΨE α Ξabs hNT_abs hΨE z R hR hball
  -- the pin of `ΨE` at the anchor (`hagree`: `ΨE = Φm` on the crux gate)
  have hpinE : ΨE (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) = (((-M : ℝ)) : ℂ) := by
    rw [hagree _ hpinmem]; exact hpinval
  -- the axis deviation bound of `ΨE` at the current perturbation
  have hdevax : ∀ t : ℝ, Y0an ≤ t →
      ‖ΨE ((t : ℂ) * Complex.I) - (t : ℂ) * Complex.I‖ ≤ Aan * Real.log (t + 2) + Can + t / 64 ∧
      ‖ΨE (-((t : ℂ) * Complex.I)) + (t : ℂ) * Complex.I‖ ≤
        Aan * Real.log (t + 2) + Can + t / 64 :=
    fun t ht => hanmain f Df u σ α (nearOn_mono hNear hLanL hδ0an) hf0 hInF1 hαdef huD hub
      hform hexp hτQ_abs hQAdm_abs hNT_abs ΨE hΨE (hsub_gate hpinmem) hpinE t ht
  -- ## 8d-bis. the datum-level decays, end asymptotics and the gate preimage bounds
  -- (`hdec` on the two datum gates, from `Work.Pert.liftF_defect_decay_exp`)
  have hα64 : ‖α‖ ≤ 1 / 64 := by
    have hpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
    have h4 : 4 * Ξ' + 8 ≤ 1 / ‖α‖ := h4Ξ
    rw [le_div_iff₀ hpos] at h4
    have h1 : (64 : ℝ) ≤ 4 * Ξ' + 8 := by
      have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
      linarith [hΞabs, hΞabsΞ', hp]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64)]
    nlinarith only [h4, h1, norm_nonneg α]
  have hdecQm : ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧ ∀ z ∈ Qm Ξabs α, Y < z.im →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ M * Real.exp (-(κ * z.im)) := by
    obtain ⟨M, κ, Y, hM, hκ, hdec⟩ :=
      Work.Pert.liftF_defect_decay_exp hΞabspos hρpos hσne hαne hα64 hInF1α huD hub hexp hτQ_abs
    exact ⟨M, κ, Y, hM, hκ, fun z hz hy => hdec z hz hy.le⟩
  have hdecQp : ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧ ∀ z ∈ Qp Ξabs α, Y < z.im →
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ M * Real.exp (-(κ * z.im)) := by
    obtain ⟨M, κ, Y, hM, hκ, hdec⟩ := hdecQm
    refine ⟨M * Real.exp (κ * |(1 / α).im|), κ, Y + |(1 / α).im|, by positivity, hκ,
      fun z hz hy => ?_⟩
    have hz' : Work.Pert.Tt α z ∈ Qm Ξabs α := Work.Pert.Tt_mem_Qm_iff.mpr hz
    have hzim : (Work.Pert.Tt α z).im = z.im - (1 / α).im := by
      rw [Work.Pert.Tt]; simp
    have hlift : Work.Pert.liftF u σ α (Work.Pert.Tt α z)
        = Work.Pert.liftF u σ α z - 1 / α := by
      have h := Work.Pert.pert2v2.liftF_add_int_div u σ α hαne (-1) z
      have h1 : z + ((-1 : ℤ) : ℂ) / α = Work.Pert.Tt α z := by
        push_cast; rw [Work.Pert.Tt]; ring
      have h2 : (((-1 : ℤ)) : ℂ) / α = -(1 / α) := by push_cast; ring
      rw [h1, h2] at h
      rw [h]; ring
    have heq : Work.Pert.liftF u σ α z - (z + 1)
        = Work.Pert.liftF u σ α (Work.Pert.Tt α z) - (Work.Pert.Tt α z + 1) := by
      rw [hlift, Work.Pert.Tt]; ring
    have hTt' : Y < (Work.Pert.Tt α z).im := by
      rw [hzim]; linarith [le_abs_self ((1 / α).im)]
    have h0 := hdec _ hz' hTt'
    have hexp : Real.exp (-(κ * (Work.Pert.Tt α z).im))
        ≤ Real.exp (κ * |(1 / α).im|) * Real.exp (-(κ * z.im)) := by
      have h1 : -(κ * (Work.Pert.Tt α z).im)
          ≤ κ * |(1 / α).im| + -(κ * z.im) := by
        rw [hzim]
        have h2 : κ * (1 / α).im ≤ κ * |(1 / α).im| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hκ.le
        have h3 : -(κ * (z.im - (1 / α).im)) = κ * (1 / α).im + -(κ * z.im) := by ring
        rw [h3]; linarith only [h2]
      calc Real.exp (-(κ * (Work.Pert.Tt α z).im))
          ≤ Real.exp (κ * |(1 / α).im| + -(κ * z.im)) := Real.exp_le_exp.mpr h1
        _ = Real.exp (κ * |(1 / α).im|) * Real.exp (-(κ * z.im)) := Real.exp_add _ _
    rw [heq]
    calc ‖Work.Pert.liftF u σ α (Work.Pert.Tt α z) - (Work.Pert.Tt α z + 1)‖
        ≤ M * Real.exp (-(κ * (Work.Pert.Tt α z).im)) := h0
      _ ≤ M * (Real.exp (κ * |(1 / α).im|) * Real.exp (-(κ * z.im))) :=
          mul_le_mul_of_nonneg_left hexp (le_of_lt hM)
      _ = (M * Real.exp (κ * |(1 / α).im|)) * Real.exp (-(κ * z.im)) := by ring
  -- the upper-end constants and the windowed asymptotics of `ΨE` (`Qm`) and `Ψp` (`Qp`)
  obtain ⟨cm, hEndm⟩ :=
    Work.Pert.pert2v2.gate_coord_end_asymptotic_Qm hF hΞabspos hQAdm_abs hNT_abs hΨE hdecQm
  obtain ⟨cp, hEndp⟩ :=
    Work.Pert.pert2v2.gate_coord_end_asymptotic_Qp hF hΞabspos hQAdm_p_abs hNTp_abs hΨp hdecQp
  -- the (A.4.2) normalisation: `dlow = cm - cp - 1/α`
  have hdlow_id : dlow = cm - cp - 1 / α :=
    Work.Pert.RBlock2.gate_T_relation_constant (Ξ := Ξabs) (α := α) (d := dlow) (cm := cm)
      (cp := cp) (fun z hz => by rw [hΨp_rel z hz]; ring) hEndm hEndp
  -- ## 8d-ter. the cover with the height gain, and the gate preimage bounds
  -- the disc cover at every DATUM-level height `t ≥ Ycov`: the window point `x + i t` is a value of
  -- `ΨE` on the waist, with its preimage in the axis disc `closedBall (t i) (t/8)`
  have hcoverD : ∀ t : ℝ, Ycov ≤ t → ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (x : ℂ) + (t : ℂ) * Complex.I ∈ ΨE '' (Qm Ξabs α ∩ Qp Ξabs α) ∧
      ‖Work.Pert.invOn ΨE (Qm Ξabs α) ((x : ℂ) + (t : ℂ) * Complex.I) - (t : ℂ) * Complex.I‖
        ≤ t / 8 := by
    intro t ht x hx
    have hA : max (max (2 * Ξabs + 1) (8 * Rtang + 1)) (max Y0an Yg) ≤ t :=
      le_trans (le_max_left _ _) ht
    have hC : max (2 * Ξabs + 1) (8 * Rtang + 1) ≤ t := le_trans (le_max_left _ _) hA
    have hD : max Y0an Yg ≤ t := le_trans (le_max_right _ _) hA
    have h2Ξ : 2 * Ξabs + 1 ≤ t := le_trans (le_max_left _ _) hC
    have h8R : 8 * Rtang + 1 ≤ t := le_trans (le_max_right _ _) hC
    have hY0 : Y0an ≤ t := le_trans (le_max_left _ _) hD
    have hYg' : Yg ≤ t := le_trans (le_max_right _ _) hD
    have htpos : 0 < t := by linarith
    have hx0 : 0 ≤ x := hx.1
    have hx1 : x < 1 := hx.2
    have hz₀re : ((t : ℂ) * Complex.I).re = 0 := by simp
    have hz₀im : ((t : ℂ) * Complex.I).im = t := by simp
    have hz₀abs : |((t : ℂ) * Complex.I).im| = t := by rw [hz₀im, abs_of_pos htpos]
    obtain ⟨hball, hdc⟩ := disc_cover_strong (Ξ := Ξabs) (T := t) (R₂ := Rtang) (α := α)
      (F := Work.Pert.liftF u σ α) (Φ := ΨE) (z₀ := (t : ℂ) * Complex.I)
      hInF1α hz₀re hz₀abs (by linarith) htpos (by linarith) hderb hΨE
    have hdev₀ : ‖ΨE ((t : ℂ) * Complex.I) - (t : ℂ) * Complex.I‖
        ≤ Aan * Real.log (t + 2) + Can + t / 64 := (hdevax t hY0).1
    have hdist : ‖((x : ℂ) + (t : ℂ) * Complex.I) - ΨE ((t : ℂ) * Complex.I)‖ < t / 32 := by
      have h1 : ‖((x : ℂ) + (t : ℂ) * Complex.I) - (t : ℂ) * Complex.I‖ ≤ 1 := by
        have hwz : ((x : ℂ) + (t : ℂ) * Complex.I) - (t : ℂ) * Complex.I = (x : ℂ) := by ring
        rw [hwz, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith, le_of_lt hx1⟩
      have h2 : ‖(t : ℂ) * Complex.I - ΨE ((t : ℂ) * Complex.I)‖
          ≤ Aan * Real.log (t + 2) + Can + t / 64 := by
        rw [norm_sub_rev]; exact hdev₀
      have h3 : 1 + (Aan * Real.log (t + 2) + Can + t / 64) < t / 32 := by
        have h := hYg t hYg'
        have hlog : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
        nlinarith only [h, hAan, hCan, hlog]
      calc ‖((x : ℂ) + (t : ℂ) * Complex.I) - ΨE ((t : ℂ) * Complex.I)‖
          ≤ ‖((x : ℂ) + (t : ℂ) * Complex.I) - (t : ℂ) * Complex.I‖
            + ‖(t : ℂ) * Complex.I - ΨE ((t : ℂ) * Complex.I)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 1 + (Aan * Real.log (t + 2) + Can + t / 64) := add_le_add h1 h2
        _ < t / 32 := h3
    have hmemB : ((x : ℂ) + (t : ℂ) * Complex.I) ∈ Metric.ball (ΨE ((t : ℂ) * Complex.I)) (t / 32) := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hdist
    have hmemImg : ((x : ℂ) + (t : ℂ) * Complex.I) ∈ ΨE '' (Qm Ξabs α) := hball hmemB
    have hspec : ΨE (Work.Pert.invOn ΨE (Qm Ξabs α) ((x : ℂ) + (t : ℂ) * Complex.I))
        = (x : ℂ) + (t : ℂ) * Complex.I := Work.Pert.invOn_spec hmemImg
    have hmem := hdc _ hmemB
    refine ⟨⟨Work.Pert.invOn ΨE (Qm Ξabs α) ((x : ℂ) + (t : ℂ) * Complex.I),
      ⟨hmem.2.1, hmem.2.2⟩, hspec⟩, ?_⟩
    have h := hmem.1
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    exact h
  have hΞabsYcov : Ξabs < Ycov := by
    have h1 : 2 * Ξabs + 1 ≤ Ycov :=
      le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
    linarith [hΞabspos]
  have hcovGBt : ∀ t : ℝ, Ycov ≤ t → ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (x : ℂ) + (t : ℂ) * Complex.I ∈ ΨE '' (Qm Ξabs α ∩ Qp Ξabs α) ∧
      (3 * t + Ξabs) / 4 ≤ (Work.Pert.invOn ΨE (Qm Ξabs α)
        ((x : ℂ) + (t : ℂ) * Complex.I)).im := by
    intro t ht x hx
    obtain ⟨h1, h2⟩ := hcoverD t ht x hx
    refine ⟨h1, ?_⟩
    have h3 := (Work.Pert.pert2v2.LeadWire.re_im_of_near_axis h2).2
    have h4 := (abs_le.mp h3).1
    have h2Ξ : 2 * Ξabs + 1 ≤ t :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) ht
    linarith
  -- the disc cover at a window point `w` (`|Re w| < 1`, either sign of `Im w`) at a DATUM-level
  -- height `|Im w| ≥ Ycov`: the preimage lies in the axis disc `closedBall ((Im w) i) (|Im w|/8)`
  have hbandD : ∀ w : ℂ, |w.re| < 1 → Ycov ≤ |w.im| →
      w ∈ ΨE '' (Qm Ξabs α ∩ Qp Ξabs α) ∧
      ‖Work.Pert.invOn ΨE (Qm Ξabs α) w - (w.im : ℂ) * Complex.I‖ ≤ |w.im| / 8 := by
    intro w hwre ht
    have hA : max (max (2 * Ξabs + 1) (8 * Rtang + 1)) (max Y0an Yg) ≤ |w.im| :=
      le_trans (le_max_left _ _) ht
    have hC : max (2 * Ξabs + 1) (8 * Rtang + 1) ≤ |w.im| := le_trans (le_max_left _ _) hA
    have hD : max Y0an Yg ≤ |w.im| := le_trans (le_max_right _ _) hA
    have h2Ξ : 2 * Ξabs + 1 ≤ |w.im| := le_trans (le_max_left _ _) hC
    have h8R : 8 * Rtang + 1 ≤ |w.im| := le_trans (le_max_right _ _) hC
    have hY0 : Y0an ≤ |w.im| := le_trans (le_max_left _ _) hD
    have hYg' : Yg ≤ |w.im| := le_trans (le_max_right _ _) hD
    have htpos : 0 < |w.im| := by linarith
    have hz₀re : ((w.im : ℂ) * Complex.I).re = 0 := by simp
    have hz₀abs : |((w.im : ℂ) * Complex.I).im| = |w.im| := by simp
    obtain ⟨hball, hdc⟩ := disc_cover_strong (Ξ := Ξabs) (T := |w.im|) (R₂ := Rtang) (α := α)
      (F := Work.Pert.liftF u σ α) (Φ := ΨE) (z₀ := (w.im : ℂ) * Complex.I)
      hInF1α hz₀re hz₀abs (by linarith) htpos (by linarith) hderb hΨE
    have hdev₀ : ‖ΨE ((w.im : ℂ) * Complex.I) - (w.im : ℂ) * Complex.I‖
        ≤ Aan * Real.log (|w.im| + 2) + Can + |w.im| / 64 := by
      rcases le_or_gt 0 w.im with h | h
      · have hte : |w.im| = w.im := abs_of_nonneg h
        have h2 := (hdevax |w.im| hY0).1
        rw [hte] at h2 ⊢
        exact h2
      · have hte : |w.im| = -w.im := abs_of_neg h
        have h2 := (hdevax |w.im| hY0).2
        have e1 : -(((|w.im| : ℝ) : ℂ) * Complex.I) = (w.im : ℂ) * Complex.I := by
          rw [hte]; push_cast; ring
        have e2 : ((|w.im| : ℝ) : ℂ) * Complex.I = -((w.im : ℂ) * Complex.I) := by
          rw [hte]; push_cast; ring
        rw [e1, e2, ← sub_eq_add_neg] at h2
        exact h2
    have hdist : ‖w - ΨE ((w.im : ℂ) * Complex.I)‖ < |w.im| / 32 := by
      have h1 : ‖w - (w.im : ℂ) * Complex.I‖ ≤ 1 := by
        have hwz : w - (w.im : ℂ) * Complex.I = (w.re : ℂ) := by
          apply Complex.ext <;> simp
        rw [hwz, Complex.norm_real, Real.norm_eq_abs]
        exact hwre.le
      have h2 : ‖(w.im : ℂ) * Complex.I - ΨE ((w.im : ℂ) * Complex.I)‖
          ≤ Aan * Real.log (|w.im| + 2) + Can + |w.im| / 64 := by
        rw [norm_sub_rev]; exact hdev₀
      have h3 : 1 + (Aan * Real.log (|w.im| + 2) + Can + |w.im| / 64) < |w.im| / 32 := by
        have h := hYg |w.im| hYg'
        have hlog : 0 ≤ Real.log (|w.im| + 2) := Real.log_nonneg (by linarith)
        nlinarith only [h, hAan, hCan, hlog]
      calc ‖w - ΨE ((w.im : ℂ) * Complex.I)‖
          ≤ ‖w - (w.im : ℂ) * Complex.I‖
            + ‖(w.im : ℂ) * Complex.I - ΨE ((w.im : ℂ) * Complex.I)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 1 + (Aan * Real.log (|w.im| + 2) + Can + |w.im| / 64) := add_le_add h1 h2
        _ < |w.im| / 32 := h3
    have hmemB : w ∈ Metric.ball (ΨE ((w.im : ℂ) * Complex.I)) (|w.im| / 32) := by
      rw [Metric.mem_ball, dist_eq_norm]; exact hdist
    have hmemImg : w ∈ ΨE '' (Qm Ξabs α) := hball hmemB
    have hspec : ΨE (Work.Pert.invOn ΨE (Qm Ξabs α) w) = w := Work.Pert.invOn_spec hmemImg
    have hmem := hdc _ hmemB
    refine ⟨⟨Work.Pert.invOn ΨE (Qm Ξabs α) w, ⟨hmem.2.1, hmem.2.2⟩, hspec⟩, ?_⟩
    have h := hmem.1
    rw [Metric.mem_closedBall, dist_eq_norm] at h
    exact h
  have hcoverGB : ∃ Y : ℝ, Ξabs < Y ∧ ∀ y₀ : ℝ, Y ≤ y₀ → ∀ x ∈ Set.Ico (0 : ℝ) 1,
      (x : ℂ) + (y₀ : ℂ) * Complex.I ∈ ΨE '' (Qm Ξabs α ∩ Qp Ξabs α) ∧
      (3 * y₀ + Ξabs) / 4 ≤ (Work.Pert.invOn ΨE (Qm Ξabs α)
        ((x : ℂ) + (y₀ : ℂ) * Complex.I)).im :=
    ⟨Ycov, hΞabsYcov, hcovGBt⟩
  obtain ⟨B, C, Yc, hBnn, hCnn, hpre⟩ :=
    Work.Pert.pert2v2.gate_preimage_bounds_window hF hΞabspos hQAdm_abs hNT_abs hΨE hdecQm hcoverGB
  -- the strip forms of the two end asymptotics (half-width `Bst`)
  set Bst : ℝ := B + |(1 / α).re| + 2 with hBstdef
  have hBst : 0 ≤ Bst := by rw [hBstdef]; positivity
  have hEndmS : ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Qm Ξabs α, Y' < z.im → |z.re| ≤ Bst →
      ‖ΨE z - z - cm‖ < ε :=
    Work.Pert.pert2v2.EndWindowBounded.end_asymptotic_bounded_window hBst hEndm
  -- ## 8d-quater. the upper-half estimate on the high chart, and its consequences
  have hEndpS : ∀ ε > 0, ∃ Y' : ℝ, ∀ z ∈ Qp Ξabs α, Y' < z.im → |z.re| ≤ Bst →
      ‖Ψp z - z - cp‖ < ε :=
    Work.Pert.pert2v2.EndWindowBounded.end_asymptotic_bounded_window hBst hEndp
  -- ## 8a-bis. the (A.4.4) constant: `‖dlow + 1/α‖ = ‖cm - cp‖ < δ/2`, by `pert2v2.a44_row` on
  -- the DATUM gate (`Φm := ΨE`, `Φp := Ψp`, gate `Qm Ξabs α`) at the SINGLE height `y₀`:
  -- * `hcover`/`hdiff` from the disc cover `hcoverD` (valid at every height `t ≥ Ycov`, datum level);
  -- * `hlim` from the windowed end asymptotics (an `α`-dependent threshold is harmless in a limit);
  -- * `hres` at `y₀` from `LeadWire.hres_core`: the pin of `Φp` at `Xc d W` (crux, `Kp`), the gate
  --   Lipschitz bound on the waist tube, and `‖ς - Xc d W‖ ≤ ηs` from the pinned `coordP`
  --   closeness on the segment (`⊆ K_all`) and `τ ≈ τ₀` (`δτ`).
  have hΞ'y : Ξ' + y₀ / 2 < y₀ := by linarith only [hy₀Ξ', hΞ'pos]
  have hΞ'y4 : Ξ' + 2 * (y₀ / 8) < y₀ := by linarith only [hy₀Ξ', hΞ'pos]
  have hhc : ‖dlow + 1 / α‖ < δ / 2 := by
    -- the canonical representative of a point above `y₀`
    have hcanon : ∀ w : ℂ, y₀ ≤ w.im →
        w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ ΨE '' (Qm Ξabs α ∩ Qp Ξabs α) ∧
        ‖Work.Pert.invOn ΨE (Qm Ξabs α) (w - (((⌊w.re⌋ : ℤ)) : ℂ)) - (w.im : ℂ) * Complex.I‖
          ≤ w.im / 8 := by
      intro w hw
      have hr : w - (((⌊w.re⌋ : ℤ)) : ℂ)
          = (((w - (((⌊w.re⌋ : ℤ)) : ℂ)).re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      have hre : (w - (((⌊w.re⌋ : ℤ)) : ℂ)).re ∈ Set.Ico (0 : ℝ) 1 := by
        have h1 : (w - (((⌊w.re⌋ : ℤ)) : ℂ)).re = w.re - ((⌊w.re⌋ : ℤ) : ℝ) := by simp
        rw [h1, Set.mem_Ico]
        exact ⟨by linarith [Int.floor_le w.re], by linarith [Int.lt_floor_add_one w.re]⟩
      rw [hr]
      exact hcoverD w.im (le_trans hYcovy₀ hw) _ hre
    -- (i) the cover above `y₀`
    have hcov_a : ∀ y x : ℝ, y₀ ≤ y → x ∈ Set.Ico (0 : ℝ) 1 →
        (x : ℂ) + (y : ℂ) * Complex.I ∈ ΨE '' (Qm Ξabs α) := by
      intro y x hy hx
      obtain ⟨ς, hς, hςe⟩ := (hcoverD y (le_trans hYcovy₀ hy) x hx).1
      exact ⟨ς, hς.1, hςe⟩
    -- (ii) the holomorphy of `EfFloor ΨE Ψp - id` above `y₀`
    have hdiff_a : DifferentiableOn ℂ
        (fun w : ℂ => Work.Pert.pert2v2.EfFloor ΨE Ψp (Qm Ξabs α) w - w)
        {w : ℂ | y₀ ≤ w.im} := by
      have hstepw : ∀ w : ℂ, y₀ ≤ w.im →
          Work.Pert.invOn ΨE (Qm Ξabs α) (w - (((⌊w.re⌋ : ℤ)) : ℂ)) ∈ Qm Ξabs α ∩ Qp Ξabs α ∧
          liftF u σ α (Work.Pert.invOn ΨE (Qm Ξabs α) (w - (((⌊w.re⌋ : ℤ)) : ℂ)))
            ∈ Qm Ξabs α ∩ Qp Ξabs α := by
        intro w hw
        obtain ⟨hmem, hdisc⟩ := hcanon w hw
        have hmemQ : Work.Pert.invOn ΨE (Qm Ξabs α) (w - (((⌊w.re⌋ : ℤ)) : ℂ)) ∈ Qm Ξabs α := by
          obtain ⟨ς, hς, hςe⟩ := hmem
          exact Work.Pert.invOn_mem ⟨ς, hς.1, hςe⟩
        exact Work.Pert.pert2v2.LeadWire.disc_step_waist hInF1α (by linarith only [hy₀32, hw])
          (by linarith only [hy₀Ξ', hΞabsΞ', hw, hΞ'pos]) hdisc (hNT_abs.1.2 _ hmemQ).1
      have hQpabsOpen' : IsOpen (Qp Ξabs α) := by
        unfold Work.Pert.Qp; exact Work.Fatou.Qreg.isOpen_Qreg _ _
      refine Work.Pert.pert2v2.HdiffRow.EfFloor_hdiff_of_step (Q := Qm Ξabs α)
        (Qp := Qp Ξabs α) (F := liftF u σ α) (y := y₀) hQopen hQpabsOpen' hΨE.1 hderΦ hΨE.2.1
        hΨp.1 ?_ ?_ hAbel ?_ ?_ hΨp.2.2
      · intro w hw
        obtain ⟨ς, hς, hςe⟩ := (hcanon w hw).1
        exact ⟨ς, hς.1, hςe⟩
      · intro w hw; exact (hstepw w hw).2.1
      · intro w hw; exact (hstepw w hw).1.2
      · intro w hw; exact (hstepw w hw).2.2
    -- (iii) the upper-end limit
    have hlim_a : Filter.Tendsto
        (fun w : ℂ => Work.Pert.pert2v2.EfFloor ΨE Ψp (Qm Ξabs α) w - w)
        MandelDim.upperEnd (nhds (cp - cm)) := by
      refine Work.Pert.pert2v2.tendsto_EfFloor_upperEnd_C (Ξ := Ξabs) (B := Bst)
        (y := max y₀ Yc) ?_ hBst hΨE.2.1 ?_ ?_ hEndmS hEndpS
      · exact lt_of_lt_of_le (lt_of_lt_of_le hΞabsYcov hYcovy₀) (le_max_left _ _)
      · intro t ht x hx
        exact hcovGBt t (le_trans hYcovy₀ (le_trans (le_max_left _ _) ht)) x hx
      · intro w hw
        have hw₀ : y₀ ≤ w.im := le_trans (le_max_left _ _) hw
        have hwc : Yc ≤ w.im := le_trans (le_max_right _ _) hw
        obtain ⟨hmem, -⟩ := hcanon w hw₀
        have hmemQ : w - (((⌊w.re⌋ : ℤ)) : ℂ) ∈ ΨE '' (Qm Ξabs α) := by
          obtain ⟨ς, hς, hςe⟩ := hmem
          exact ⟨ς, hς.1, hςe⟩
        have hre1 : |(w - (((⌊w.re⌋ : ℤ)) : ℂ)).re| < 1 := by
          have h1 : (w - (((⌊w.re⌋ : ℤ)) : ℂ)).re = w.re - ((⌊w.re⌋ : ℤ) : ℝ) := by simp
          rw [h1, abs_lt]
          exact ⟨by linarith [Int.floor_le w.re], by linarith [Int.lt_floor_add_one w.re]⟩
        have him1 : Yc ≤ (w - (((⌊w.re⌋ : ℤ)) : ℂ)).im := by simpa using hwc
        have hB := (hpre _ him1 hre1 hmemQ).1
        have hBB : B ≤ Bst := by
          rw [hBstdef]; linarith [abs_nonneg ((1 / α).re)]
        exact le_trans hB hBB
    -- (iv) the residual at the single height `y₀`
    have hηsδ : 16 * (Cgl + 1) * ηs = δ := by rw [hηsdef]; field_simp
    have hsplit : δ / 16 = Cgl * ηs + ηs := by linear_combination (-1/16 : ℝ) * hηsδ
    have harith : Cgl * ηs + εp ≤ δ / 2 / 2 := by
      rw [hεpdef]; linarith only [hsplit, hηspos, hδ]
    have hsmallη : 4 * y₀ ^ 2 * (εseg + κ0) ≤ ηs := by
      have h1 : 16 * y₀ ^ 2 * εseg = ηs := by rw [hεsegdef]; field_simp
      have h2 : y₀ ^ 2 * κ0 ≤ y₀ ^ 2 * εseg := mul_le_mul_of_nonneg_left hκ0le (sq_nonneg _)
      linarith only [h1, h2, hηspos]
    have hres_a : ∀ x ∈ Set.Ico (0 : ℝ) 1, ∀ ς ∈ Qm Ξabs α,
        ΨE ς = (x : ℂ) + (y₀ : ℂ) * Complex.I →
        ‖Ψp ς - d.E ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖ < δ / 2 / 2 := by
      intro x hx ς hς hςW
      obtain ⟨-, hdiscW⟩ := hcoverD y₀ hYcovy₀ x hx
      have hinvς : Work.Pert.invOn ΨE (Qm Ξabs α) ((x : ℂ) + (y₀ : ℂ) * Complex.I) = ς :=
        Work.Pert.invOn_eq hΨE.2.1 ⟨ς, hς, hςW⟩ hς hςW
      rw [hinvς] at hdiscW
      have hςw : ς ∈ Qm Ξ' α ∩ Qp Ξ' α :=
        Work.Pert.WaistPinned.waist_disc_window (ξ := Ξ') (T := y₀) (ρ := y₀ / 8) (α := α)
          (z₀ := (y₀ : ℂ) * Complex.I) hInF1α (by positivity) hΞ'y4 (by simp)
          (by simp [abs_of_pos hy₀pos])
          (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hdiscW)
      have hΦmς : Φm ς = (x : ℂ) + (y₀ : ℂ) * Complex.I := by
        rw [← hagree ς hςw.1]; exact hςW
      have hWimg' : (x : ℂ) + (y₀ : ℂ) * Complex.I ∈ Φm '' Qm Ξ' α := ⟨ς, hςw.1, hΦmς⟩
      have hcoordW : coordP f Df (tauC σ α) Φm (Qm Ξ' α) ((x : ℂ) + (y₀ : ℂ) * Complex.I)
          = tauC σ α ς := by
        rw [Work.Pert.coordP_eq_tauC_of_mem_image hΦm.2.1 hWimg',
          Work.Pert.invOn_eq hΦm.2.1 hWimg' hςw.1 hΦmς]
      have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
      have hWK : (x : ℂ) + (y₀ : ℂ) * Complex.I ∈ K_all := hS₀Kall ⟨x, hxI, rfl⟩
      have hτφ : ‖tauC σ α ς - d.φ ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖ ≤ εseg := by
        rw [← hcoordW]
        exact le_trans (le_of_lt (lt_of_lt_of_le (hclose_all _ hWK) le_rfl)) hεseg_all
      obtain ⟨hςn1, hςn2⟩ := Work.Pert.pert2v2.LeadWire.norm_bounds_near_axis hy₀pos hdiscW
      have hτinv : ‖tauC σ α ς + 1 / ς‖ ≤ κ0 :=
        Work.Pert.pert2v2.LeadWire.tau_close_of_small hαne hCsmp hρpos hρ1 hδ0pos.le
          (by linarith only [hy₀32]) hκ0pos hκ0y hδ0τ hαsmall hu01 hexp
          (by linarith only [hςn1, hy₀32]) hςn2
      have hZ : ‖Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I) - (y₀ : ℂ) * Complex.I‖
          ≤ y₀ / 8 := le_trans (hdevZ x hxI) (by linarith only [hy₀pos])
      have hφW : d.φ ((x : ℂ) + (y₀ : ℂ) * Complex.I) ∈ MandelDim.ParabolicBasin f₀ D₀ :=
        (hS₀DE ⟨x, hxI, rfl⟩).2
      have hpinW := hpinKp (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)) ⟨x, hxI, rfl⟩
      have hres := Work.Pert.pert2v2.LeadWire.hres_core d (Ξ' := Ξ') (y₀ := y₀) (Cgl := Cgl)
        (Rgl := Rgl) (εp := εp) (ηs := ηs) (ε1 := εseg) (κ := κ0) (δ' := δ / 2 / 2) (α := α)
        (Φp := Φp) (τ := tauC σ α) (W := (x : ℂ) + (y₀ : ℂ) * Complex.I) (ς := ς)
        hInF1α (by linarith only [hy₀32]) hΞ'y hRglpos.le (by linarith only [hRgly₀]) hdiscW hZ hφW hτφ hτinv hsmallη
        (fun a b htube => hgatelip (Ξ' := Ξ') (le_trans hΞabs hΞabsΞ') le_rfl hQAdm_p hNTp
          hΦp htube)
        hpinW hCglpos.le harith
      rw [hagreep ς hςw.2]
      exact hres
    have hcm : ‖cm - cp‖ < δ / 2 :=
      Work.Pert.pert2v2.a44_row d (Ξ' := Ξabs) (α := α) (Φm := ΨE) (Φp := Ψp) (y₀ := y₀)
        (δ := δ / 2) (cm := cm) (cp := cp) (by linarith only [hδ]) hy₀η hΨE.2.1 hcov_a hres_a hdiff_a hlim_a
    have heq : dlow + 1 / α = cm - cp := by rw [hdlow_id]; ring
    rw [heq]
    exact hcm
  -- ## 8b. the two charts
  -- the *margin* set of the waist: the points of the waist that stay in it under the forward step
  -- `F` (`F z ≈ z + 1`, so a margin `> 1` in the `Re`-direction suffices)
  set Mset : Set ℂ := {z : ℂ | |z.re| < |z.im| - (Ξabs + 2)} with hMsetdef
  have hMsub : Mset ⊆ Qm Ξabs α ∩ Qp Ξabs α := by
    intro z hz
    rw [hMsetdef, Set.mem_setOf_eq] at hz
    rw [Work.Pert.Qm_inter_Qp (ξ := Ξabs) (α := α) hInF1inv]
    show |z.re| < |z.im| - Ξabs
    linarith
  have hMopen : IsOpen Mset := by
    rw [hMsetdef]
    exact isOpen_lt (continuous_abs.comp Complex.continuous_re)
      ((continuous_abs.comp Complex.continuous_im).sub continuous_const)
  have hUhighImgOpen : IsOpen (ΨE '' Mset) :=
    Work.Pert.isOpen_image_of_deriv_ne_zero hMopen
      (hΨE.1.mono (fun z hz => (hMsub hz).1)) (fun z hz => hderΦ z (hMsub hz).1)
  -- the two pieces
  set Rlow : ℂ → ℂ := Work.Pert.pert2v2.RlowPiece f Qp' (tauC σ α) Φp φ m_x dlow with hRlowdef
  set Rhigh : ℂ → ℂ := Work.Pert.pert2v2.RhighOf f Df (tauC σ α) ΨE Ξabs α with hRhighdef
  -- the low chart: the clause set, the window, `d.DE`, `Dφ` **and the estimate itself** (so that
  -- the low half of `R_close` is definitional)
  set Ulow : Set ℂ := {w : ℂ | |w.re| < 1 ∧ |w.im| < H + 1 ∧ w ∈ d.DE ∧ w ∈ Dφ ∧
      Work.Pert.pert2v2.LowClause f Df (liftF u σ α) (tauC σ α) φ Qp' m_x w ∧
      ‖Rlow w + 1 / α - d.E w‖ < δ} with hUlowdef
  -- the high chart: the window above `H`, inside the image of the *margin* waist
  set Uhigh : Set ℂ := {w : ℂ | |w.re| < 1 ∧ H < |w.im| ∧ w ∈ ΨE '' Mset} with hUhighdef
  -- ## 8c. chart-level auxiliary facts
  have hQp'absOpen : IsOpen (Qp Ξ' α) := by
    unfold Work.Pert.Qp; exact Work.Fatou.Qreg.isOpen_Qreg _ _
  have hQpabsOpen : IsOpen (Qp Ξabs α) := by
    unfold Work.Pert.Qp; exact Work.Fatou.Qreg.isOpen_Qreg _ _
  have hQp'sub_abs : Qp' ⊆ Qp Ξabs α := fun z hz => hsub_gate_p (hQp'sub hz)
  have hτne' : ∀ z ∈ Qp', deriv (tauC σ α) z ≠ 0 :=
    Work.Parab.inversion.deriv_ne_zero_of_injOn hQp'open (hτp.mono hQp'sub_abs) hinjτ
  -- the window-and-domain set of the low chart
  set Wv : Set ℂ := {w : ℂ | |w.re| < 1 ∧ |w.im| < H + 1 ∧ w ∈ d.DE ∧ w ∈ Dφ} with hWvdef
  have hWvOpen : IsOpen Wv := by
    rw [hWvdef]
    have h' : {w : ℂ | |w.re| < 1 ∧ |w.im| < H + 1 ∧ w ∈ d.DE ∧ w ∈ Dφ}
        = ({w : ℂ | |w.re| < 1} ∩ {w : ℂ | |w.im| < H + 1}) ∩ (d.DE ∩ Dφ) := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [h']
    exact ((isOpen_lt Complex.continuous_re.abs continuous_const).inter
      (isOpen_lt Complex.continuous_im.abs continuous_const)).inter (hdDEopen.inter hDφopen)
  have hφWv : DifferentiableOn ℂ φ Wv := hφholo.mono (fun w hw => by rw [hWvdef] at hw; exact hw.2.2.2)
  -- the one-step closure of the *margin* waist under `F`
  have hstepQp : ∀ z ∈ Mset, liftF u σ α z ∈ Qp Ξabs α := by
    intro z hzM
    have hzineq : |z.re| < |z.im| - (Ξabs + 2) := by
      have h := hzM; rw [hMsetdef, Set.mem_setOf_eq] at h; exact h
    have hzQp : z ∈ Qp Ξabs α := (hMsub hzM).2
    have hdef : ‖liftF u σ α z - (z + 1)‖ ≤ 1 / 32 := (hNTp_abs.1.2 z hzQp).1
    have hre_sub : (liftF u σ α z - (z + 1)).re ≤ 1 / 32 :=
      le_trans (le_abs_self _) (le_trans (Complex.abs_re_le_norm _) hdef)
    have hre_sub' : -(1 / 32 : ℝ) ≤ (liftF u σ α z - (z + 1)).re :=
      le_trans (neg_le_neg (le_trans (Complex.abs_re_le_norm _) hdef)) (neg_abs_le _)
    have him_sub : |(liftF u σ α z - (z + 1)).im| ≤ 1 / 32 :=
      le_trans (Complex.abs_im_le_norm _) hdef
    have hre_eq : (liftF u σ α z).re = z.re + 1 + (liftF u σ α z - (z + 1)).re := by
      rw [Complex.sub_re, show (z + 1).re = z.re + 1 by simp]; ring
    have him_eq : (liftF u σ α z).im = z.im + (liftF u σ α z - (z + 1)).im := by
      rw [Complex.sub_im, show (z + 1).im = z.im by simp]; ring
    rw [Work.Pert.Qp_mem_iff]
    refine ⟨?_, ?_⟩
    · -- `Ξabs - |Im Fz| < Re Fz`
      have h1 : -( |z.im| - (Ξabs + 2)) < z.re := (abs_lt.mp hzineq).1
      have h2 : |(liftF u σ α z).im| ≤ |z.im| + 1 / 32 := by
        rw [him_eq]
        calc |z.im + (liftF u σ α z - (z + 1)).im|
            ≤ |z.im| + |(liftF u σ α z - (z + 1)).im| := abs_add_le _ _
          _ ≤ |z.im| + 1 / 32 := by linarith
      have h2' : |z.im| - 1 / 32 ≤ |(liftF u σ α z).im| := by
        have hd : |z.im - (liftF u σ α z).im| ≤ 1 / 32 := by
          have h6 : |z.im - (liftF u σ α z).im| = |(liftF u σ α z).im - z.im| := abs_sub_comm _ _
          rw [h6]
          have h7 : (liftF u σ α z).im - z.im = (liftF u σ α z - (z + 1)).im := by
            rw [Complex.sub_im, show (z + 1).im = z.im by simp]
          rw [h7]; exact him_sub
        have h := abs_add_le (z.im - (liftF u σ α z).im) ((liftF u σ α z).im)
        have h5 : z.im - (liftF u σ α z).im + (liftF u σ α z).im = z.im := by ring
        rw [h5] at h
        linarith
      rw [hre_eq]
      linarith
    · -- `Re Fz < Re(1/α) - Ξabs + |Im Fz - Im(1/α)|`
      have h1 : z.re < |z.im| - (Ξabs + 2) := (abs_lt.mp hzineq).2
      have h2 : |z.im| ≤ |z.im - (1 / α).im| + |(1 / α).im| := by
        have h := abs_add_le (z.im - (1 / α).im) ((1 / α).im)
        have h3 : z.im - (1 / α).im + (1 / α).im = z.im := by ring
        rw [h3] at h; exact h
      have h3 : |z.im - (1 / α).im| ≤ |(liftF u σ α z).im - (1 / α).im| + 1 / 32 := by
        have h4 : |(liftF u σ α z).im - z.im| ≤ 1 / 32 := by
          have h5 : (liftF u σ α z).im - z.im = (liftF u σ α z - (z + 1)).im := by
            rw [Complex.sub_im, show (z + 1).im = z.im by simp]
          rw [h5]; exact him_sub
        have h4' : |z.im - (liftF u σ α z).im| ≤ 1 / 32 := by
          rw [abs_sub_comm]; exact h4
        have h5 := abs_sub_le z.im ((liftF u σ α z).im) ((1 / α).im)
        linarith
      have hα1 : |(1 / α).im| < (1 / α).re := hInF1inv
      rw [hre_eq]
      linarith
  -- ## 8d. S3: `Rlow` is holomorphic on the low chart
  have hRlowD : DifferentiableOn ℂ Rlow Ulow := by
    have h1 : DifferentiableOn ℂ (Work.Pert.Rlow f Qp' (tauC σ α) Φp φ m_x 0 dlow)
        {w : ℂ | w ∈ Wv ∧ |w.re| < 1 ∧ |w.im| < H + 1 ∧
          (∀ j : ℕ, j ≤ m_x → f^[j] (φ w) ∈ Df) ∧ f^[m_x] (φ w) ∈ tauC σ α '' Qp'} :=
      (Work.Pert.pert2v2.low_piece_data_wide (V := Wv) (R1 := 1) (Tb := H + 1)
        (k := 0) (dlow := dlow) hWvOpen hφWv hNear.1 hNear.2.2.1 hQp'absOpen hQp'open hQp'sub
        (hτp.mono hsub_gate_p) hτne' hinjτ hΦp.1).2
    rw [hRlowdef, Work.Pert.pert2v2.RlowPiece]
    refine h1.mono (fun w hw => ?_)
    rw [hUlowdef, Set.mem_setOf_eq] at hw
    rw [Work.Pert.pert2v2.LowClause] at hw
    exact ⟨⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1⟩,
      hw.1, hw.2.1, hw.2.2.2.2.1.1, hw.2.2.2.2.1.2.1⟩
  -- ## 8e. S2: the low chart is open
  have hUlowOpen : IsOpen Ulow := by
    rw [hUlowdef]
    rw [isOpen_iff_mem_nhds]
    intro w₀ hw₀
    obtain ⟨hre, him, hDE, hDφm, hclause, hres⟩ := hw₀
    rw [Work.Pert.pert2v2.LowClause] at hclause
    obtain ⟨hwalk₀, hland₀, hret₀⟩ := hclause
    have hw₀V : w₀ ∈ Wv := by rw [hWvdef]; exact ⟨hre, him, hDE, hDφm⟩
    -- the clause holds on a neighbourhood
    have hclauseOpen : IsOpen {w : ℂ | w ∈ Wv ∧
        Work.Pert.pert2v2.LowClause f Df (liftF u σ α) (tauC σ α) φ Qp' m_x w} :=
      Work.Pert.pert2v2.lowClause_isOpen (U := Wv) (F := liftF u σ α) (τ := tauC σ α)
        (φ := φ) (Df := Df) (Qp' := Qp') (m := m_x)
        hWvOpen hNear.1 hNear.2.2.1 hQp'open (hτp.mono hQp'sub_abs) hτne' hinjτ
        (hNTp.1.1.continuousOn.mono hQp'sub) hφWv.continuousOn
    have hA : ∀ᶠ w in nhds w₀, w ∈ Wv ∧ Work.Pert.pert2v2.LowClause f Df (liftF u σ α)
        (tauC σ α) φ Qp' m_x w :=
      hclauseOpen.mem_nhds ⟨hw₀V, by rw [Work.Pert.pert2v2.LowClause]; exact ⟨hwalk₀, hland₀, hret₀⟩⟩
    -- the estimate holds on a neighbourhood (continuity of `Rlow` and `d.E`)
    have hiter : ContinuousAt (fun w : ℂ => f^[m_x] (φ w)) w₀ :=
      Work.Pert.pert2v2.continuousAt_iterate_phi (m := m_x) hWvOpen hφWv hNear.1 hNear.2.2.1
        hw₀V hwalk₀
    have hinv : ContinuousAt
        (fun w : ℂ => Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ w))) w₀ :=
      Work.Pert.pert2v2.continuousAt_invOn_iterate hQp'open (hτp.mono hQp'sub_abs) hinjτ hτne'
        hWvOpen hφWv hNear.1 hNear.2.2.1 hw₀V hwalk₀ hland₀
    have hpre : Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ w₀)) ∈ Qp' :=
      Work.Pert.invOn_mem hland₀
    have hRlowc : ContinuousAt Rlow w₀ := by
      have hΦc : ContinuousAt Φp (Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ w₀))) :=
        ((hΦp.1 _ (hQp'sub hpre)).continuousWithinAt).continuousAt
          (hQp'absOpen.mem_nhds (hQp'sub hpre))
      have h' : ContinuousAt (fun w : ℂ => Φp (Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ w)))) w₀ :=
        hΦc.comp (g := Φp) (f := fun w => Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ w))) hinv
      have h2 : ContinuousAt (fun w : ℂ => Φp (Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ w)))
          - (m_x : ℂ) + dlow) w₀ := (h'.sub continuousAt_const).add continuousAt_const
      have heq : Rlow = fun w => Φp (Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ w)))
          - (m_x : ℂ) + dlow := by
        funext w
        rw [hRlowdef, Work.Pert.pert2v2.RlowPiece]
        simp only [Work.Pert.Rlow, Int.cast_zero, sub_zero]
      rw [heq]
      exact h2
    have hEc : ContinuousAt d.E w₀ :=
      (hdEdiff.differentiableAt (hdDEopen.mem_nhds hDE)).continuousAt
    have hresc : ContinuousAt (fun w : ℂ => Rlow w + 1 / α - d.E w) w₀ :=
      (hRlowc.add continuousAt_const).sub hEc
    have hres_ev : ∀ᶠ w in nhds w₀, ‖Rlow w + 1 / α - d.E w‖ < δ :=
      hresc.norm.eventually (isOpen_Iio.mem_nhds hres)
    refine Filter.mem_of_superset (Filter.inter_mem hA hres_ev) ?_
    rintro w ⟨⟨hwV, hclw⟩, hresw⟩
    rw [hWvdef] at hwV
    exact ⟨hwV.1, hwV.2.1, hwV.2.2.1, hwV.2.2.2, hclw, hresw⟩
  -- ## 8f. S4: the `+1`-relation of the low piece on the chart
  have hRlow1 : ∀ w : ℂ, w ∈ Ulow → w + 1 ∈ Ulow → Rlow (w + 1) = Rlow w + 1 := by
    intro w hw hw1
    rw [hUlowdef, Set.mem_setOf_eq, Work.Pert.pert2v2.LowClause] at hw hw1
    rw [hRlowdef, Work.Pert.pert2v2.RlowPiece]
    have hφa : φ (w + 1) = f (φ w) :=
      (hφabel w hw.2.2.2.1 hw1.2.2.2.1).2
    exact Work.Pert.RBlock4.Rlow_add_one_pointwise (Qp := Qp Ξ' α) (k := 0) (dlow := dlow)
      hφa (fun z hz => hτFp z (hsub_gate_p hz)) hQp'sub hinjτ hw.2.2.2.2.1.2.2
      hΦp.2.2 hw.2.2.2.2.1.2.1 hw1.2.2.2.2.1.2.1
  -- ## 8g. S5/S6: the high chart and its piece
  have hUhighOpen : IsOpen Uhigh := by
    rw [hUhighdef]
    have h' : {w : ℂ | |w.re| < 1 ∧ H < |w.im| ∧ w ∈ ΨE '' Mset}
        = ({w : ℂ | |w.re| < 1} ∩ {w : ℂ | H < |w.im|}) ∩ (ΨE '' Mset) := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [h']
    exact ((isOpen_lt Complex.continuous_re.abs continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im.abs)).inter hUhighImgOpen
  have hRhigh_eq_ret : ∀ w : ℂ, w ∈ Uhigh → Rhigh w = Work.Pert.retOf ΨE (Qm Ξabs α) α w := by
    intro w hw
    rw [hUhighdef, Set.mem_setOf_eq] at hw
    obtain ⟨ζ, hζM, hζΦ⟩ := hw.2.2
    have hζ : ζ ∈ Qm Ξabs α ∩ Qp Ξabs α := hMsub hζM
    rw [hRhighdef]
    unfold Work.Pert.pert2v2.RhighOf
    rw [Work.Pert.retP_eq_retOf_of_mem_image (f := f) (Df := Df) (τ := tauC σ α) (Φ := ΨE)
      (Q := Qm Ξabs α ∩ Qp Ξabs α) (α := α) ⟨ζ, hζ, hζΦ⟩]
    have ha : Work.Pert.invOn ΨE (Qm Ξabs α ∩ Qp Ξabs α) w = ζ :=
      Work.Pert.invOn_eq (hΨE.2.1.mono Set.inter_subset_left) ⟨ζ, hζ, hζΦ⟩ hζ hζΦ
    have hb : Work.Pert.invOn ΨE (Qm Ξabs α) w = ζ :=
      Work.Pert.invOn_eq hΨE.2.1 ⟨ζ, hζ.1, hζΦ⟩ hζ.1 hζΦ
    rw [Work.Pert.retOf, Work.Pert.retOf, ha, hb]
  have hRhighD : DifferentiableOn ℂ Rhigh Uhigh := by
    have h' : DifferentiableOn ℂ (Work.Pert.retOf ΨE (Qm Ξabs α) α) Uhigh := by
      have h := (Work.Pert.pert2v2.high_piece_data_wide (Φ := ΨE) (Ξ := Ξabs) (α := α)
        (Tb := H) (R1 := 1) hΨE.1 hΨE.2.1 hderΦ).2
      refine h.mono (fun w hw => ?_)
      rw [hUhighdef, Set.mem_setOf_eq] at hw
      obtain ⟨ζ, hζM, hζΦ⟩ := hw.2.2
      exact ⟨⟨hw.1, hw.2.1⟩, ⟨ζ, hMsub hζM, hζΦ⟩⟩
    exact h'.congr (fun w hw => hRhigh_eq_ret w hw)
  -- ## 8h. S7: the `+1`-relation of the high piece
  have hRhigh1 : ∀ w : ℂ, w ∈ Uhigh → w + 1 ∈ Uhigh → Rhigh (w + 1) = Rhigh w + 1 := by
    intro w hw hw1
    rw [hUhighdef, Set.mem_setOf_eq] at hw hw1
    obtain ⟨ς, hςM, hςΦ⟩ := hw.2.2
    have hςwa : ς ∈ Qm Ξabs α ∩ Qp Ξabs α := hMsub hςM
    have hmemWa : w ∈ ΨE '' (Qm Ξabs α ∩ Qp Ξabs α) := ⟨ς, hςwa, hςΦ⟩
    have hinvWa : Work.Pert.invOn ΨE (Qm Ξabs α ∩ Qp Ξabs α) w = ς :=
      Work.Pert.invOn_eq (hΨE.2.1.mono Set.inter_subset_left) hmemWa hςwa hςΦ
    have hG : Work.Pert.GoodP f Df (tauC σ α) ΨE (Qm Ξabs α ∩ Qp Ξabs α) w :=
      Work.Pert.goodP_of_mem_image hmemWa
    have hG1 : Work.Pert.GoodP f Df (tauC σ α) ΨE (Qm Ξabs α ∩ Qp Ξabs α) (w + 1) := by
      obtain ⟨ς', hς'M, hς'Φ⟩ := hw1.2.2
      exact Work.Pert.goodP_of_mem_image ⟨ς', hMsub hς'M, hς'Φ⟩
    rw [hRhighdef]
    unfold Work.Pert.pert2v2.RhighOf
    refine Work.Pert.RBlock7.retP_add_one (Ξ := Ξabs) (α := α) (Df := Df)
      hΨE.2.1 hΨE.2.2 hOrb
      hcommF hG hG1 ?hw ?hw1
    · intro j hj
      have hm0 := Work.Pert.mIdxP_eq_zero_of_mem_image (f := f) (Df := Df) (τ := tauC σ α) hmemWa
      rw [hm0] at hj ⊢
      simp only [Nat.cast_zero, sub_zero] at hj ⊢
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl
      · show Work.Pert.invOn ΨE (Qm Ξabs α ∩ Qp Ξabs α) w ∈ Qp Ξabs α
        rw [hinvWa]; exact hςwa.2
      · show liftF u σ α (Work.Pert.invOn ΨE (Qm Ξabs α ∩ Qp Ξabs α) w) ∈ Qp Ξabs α
        rw [hinvWa]; exact hstepQp ς hςM
    · intro j hj
      have hm0 := Work.Pert.mIdxP_eq_zero_of_mem_image (f := f) (Df := Df) (τ := tauC σ α)
        (show w + 1 ∈ ΨE '' (Qm Ξabs α ∩ Qp Ξabs α) from
          ⟨(hw1.2.2).choose, hMsub (hw1.2.2).choose_spec.1, (hw1.2.2).choose_spec.2⟩)
      rw [hm0] at hj ⊢
      simp only [Nat.cast_zero, sub_zero] at hj ⊢
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl
      · show Work.Pert.invOn ΨE (Qm Ξabs α ∩ Qp Ξabs α) (w + 1) ∈ Qp Ξabs α
        obtain ⟨ς', hς'M, hς'Φ⟩ := hw1.2.2
        have hς'wa : ς' ∈ Qm Ξabs α ∩ Qp Ξabs α := hMsub hς'M
        have : Work.Pert.invOn ΨE (Qm Ξabs α ∩ Qp Ξabs α) (w + 1) = ς' :=
          Work.Pert.invOn_eq (hΨE.2.1.mono Set.inter_subset_left) ⟨ς', hς'wa, hς'Φ⟩ hς'wa hς'Φ
        rw [this]; exact hς'wa.2
      · show liftF u σ α (Work.Pert.invOn ΨE (Qm Ξabs α ∩ Qp Ξabs α) (w + 1)) ∈ Qp Ξabs α
        obtain ⟨ς', hς'M, hς'Φ⟩ := hw1.2.2
        have hς'wa : ς' ∈ Qm Ξabs α ∩ Qp Ξabs α := hMsub hς'M
        have : Work.Pert.invOn ΨE (Qm Ξabs α ∩ Qp Ξabs α) (w + 1) = ς' :=
          Work.Pert.invOn_eq (hΨE.2.1.mono Set.inter_subset_left) ⟨ς', hς'wa, hς'Φ⟩ hς'wa hς'Φ
        rw [this]; exact hstepQp ς' hς'M
  have hwinLow : Ulow ⊆ {w : ℂ | |w.re - 0| < 1 ∧ |w.im| < H + 1} := by
    intro w hw
    rw [hUlowdef, Set.mem_setOf_eq] at hw
    exact ⟨by simpa using hw.1, hw.2.1⟩
  have hwinHigh : Uhigh ⊆ {w : ℂ | |w.re - 0| < 1 ∧ H < |w.im|} := by
    intro w hw
    rw [hUhighdef, Set.mem_setOf_eq] at hw
    exact ⟨by simpa using hw.1, hw.2.1⟩
  -- every point of `Kb` inside the low window is in the low chart
  have hKb_window : ∀ w : ℂ, w ∈ Kb → |w.re| < 1 → |w.im| < H + 1 → w ∈ Ulow := by
    intro w hwKb hre him
    have hKall : w ∈ K_all := hKbKall hwKb
    have hDφw : w ∈ Dφ := hKallDφ hKall
    have htr := hTransfer w (hKall_sub hKall)
    have hcl := hclause w hwKb
    have hresidw : ‖Φp (Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ w))) - (m_x : ℂ)
        - d.E w‖ < δ / 2 := by
      have h := hresid w hwKb
      rw [htr.2]
      exact h
    rw [hUlowdef, Set.mem_setOf_eq, Work.Pert.pert2v2.LowClause]
    refine ⟨hre, him, hKbDE hwKb, hDφw, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro j hj; rw [htr.2]; exact hcl.1 j hj
    · rw [htr.2]; exact hcl.2
    · rw [htr.2]; exact hretstep w hwKb
    · have hres := Work.Pert.pert2v2.Rlow_close_of_res (f := f) (Qp' := Qp') (Φp := Φp)
        (φ := φ) (τ := tauC σ α) (E := d.E) (m := m_x) (k := 0) (α := α) (dlow := dlow)
        hδ (by simpa using hresidw) hhc
      simpa only [hRlowdef, Work.Pert.pert2v2.RlowPiece] using hres
  have hWlow : {w : ℂ | |w.re - 0| < 1 ∧ H < |w.im| ∧ |w.im| < H + 1} ⊆ Ulow := by
    intro w hw
    obtain ⟨hre, hH, hH1⟩ := hw
    have hre' : |w.re| < 1 := by simpa using hre
    have hR0ge : (1 : ℝ) ≤ R0 := by rw [hR0def]; linarith [le_max_right RK 0]
    have hKb : w ∈ Kb := by
      rw [hKbdef]
      refine Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩
      · rw [hSdef]; show |w.re| ≤ R0; linarith [le_of_lt hre', hR0ge]
      · linarith [hy₁H, le_of_lt hH]
      · linarith [le_of_lt hH1]
    exact hKb_window w hKb hre' (by linarith)
  -- every window point above height `H` lies in the high chart
  have hTall : ∀ z : ℂ, |z.re| < 1 → H < |z.im| → z ∈ Uhigh := by
    intro z hzre hzH
    obtain ⟨ς, hς, hςΦ, hςm⟩ := hcovthr α ΨE hInF1α hQAdm_abs hQAdm_p_abs hΨE.1 hderb hdevax
      z hzre (le_trans hHthrH hzH.le)
    refine ⟨hzre, hzH, ς, ?_, hςΦ⟩
    rw [hMsetdef, Set.mem_setOf_eq]
    linarith
  have hWhigh : {w : ℂ | |w.re - 0| < 1 ∧ H < |w.im| ∧ |w.im| < H + 1} ⊆ Uhigh := by
    intro w hw
    exact hTall w (by simpa using hw.1) hw.2.1
  -- the normal-form smallness at the scale `θA` (used by S12 and S16)
  have hH64 : (64 : ℝ) ≤ H := le_trans hYcov64 hYcovH
  -- the smallness of `α` and `u 0 - 1` at the scale `θA`
  obtain ⟨hαθ, hu0θ⟩ := Work.Pert.pert2v2.LeadWire.small_of_delta hCsmp hρpos hρ1 hδ0pos.le
    hδ0A hαsmall hu01
  have hθηu : θA ≤ ηu := min_le_left _ _
  have hθRq : θA ≤ 1 / (4 * Rq) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hθN : θA ≤ 1 / (4 * Nreq) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hMn0 : (0 : ℝ) ≤ (Mn : ℝ) := Nat.cast_nonneg _
  have hRqpos : 0 < Rq := by rw [hRqdef]; linarith only [hH64, hMn0]
  have hΞsh0 : 0 ≤ Ξsh := le_trans hΞabspos0.le hΞabsΞsh
  have hNpos : 0 < Nreq := by rw [hNreqdef]; linarith only [hH64, hMn0, hΞsh0, hNextra]
  have hN0 : Nreq ≠ 0 := ne_of_gt hNpos
  have hRq0 : Rq ≠ 0 := ne_of_gt hRqpos
  have hCm0 : Cm ≠ 0 := ne_of_gt hCmpos
  have hθApos : 0 < θA :=
    lt_min hηupos (lt_min (one_div_pos.mpr (by linarith only [hRqpos]))
      (one_div_pos.mpr (by linarith only [hNpos])))
  have hαN : ‖α‖ ≤ 1 / (8 * Nreq) := by
    have : θA / 2 ≤ 1 / (8 * Nreq) := by
      have h := hθN
      rw [show 1 / (8 * Nreq) = (1 / (4 * Nreq)) / 2 by ring]
      linarith
    linarith
  have hAre : 4 * Nreq ≤ (1 / α).re := by
    have h := Work.Pert.inv_re_ge_of_norm_le hInF1α hαN
    have h2 : 1 / (2 * (1 / (8 * Nreq))) = 4 * Nreq := by field_simp; ring
    linarith
  have hαRq : ‖α‖ * Rq ≤ 1 / 8 := by
    have h1 : ‖α‖ ≤ 1 / (8 * Rq) := by
      have : θA / 2 ≤ 1 / (8 * Rq) := by
        rw [show 1 / (8 * Rq) = (1 / (4 * Rq)) / 2 by ring]
        linarith
      linarith
    have := mul_le_mul_of_nonneg_right h1 hRqpos.le
    rw [show 1 / (8 * Rq) * Rq = 1 / 8 by field_simp] at this
    exact this
  -- ## S12. the overlap identity `Rhigh = Rlow` on `Ulow ∩ Uhigh`, by the `(SHADOW)` estimate:
  -- the gate point `ς` of `w` (axis disc, `hbandD`) is `ηsh`-close to the curve point `Xc d w`
  -- (pinned `coordP` closeness on `Kb ⊆ K_all` + `τ ≈ τ₀`); both walks stay in the shadow gate
  -- `Qp Ξsh α` (room `≥ Mn`, a `δ0`-condition) inside `closedBall 0 Rq`, where `F0f` is
  -- `Ksh`-Lipschitz at scale `Bsh` and `liftF ≈ F0f` up to `δsh`; hence after `m_x ≤ Mn` steps the
  -- perturbed walk lands within `4` of the crux centre, i.e. in `Qp'` (`shadow_coinc_v7`), and
  -- `Rlow_eq_retOf_crux_walk` identifies the two pieces.
  have hcross : ∀ w : ℂ, w ∈ Ulow → w ∈ Uhigh → Rhigh w = Rlow w := by
    intro w hwL hwH
    have hwH' := hwH
    rw [hUhighdef, Set.mem_setOf_eq] at hwH'
    obtain ⟨hwre, hwH1, ς, hςM, hςΦ⟩ := hwH'
    have hwL' := hwL
    rw [hUlowdef, Set.mem_setOf_eq] at hwL'
    have hwim1 : |w.im| < H + 1 := hwL'.2.1
    have hςQ : ς ∈ Qm Ξabs α ∩ Qp Ξabs α := hMsub hςM
    -- `w` is a point of the band part of `Kb`
    have hR0ge : (1 : ℝ) ≤ R0 := by rw [hR0def]; linarith [le_max_right RK 0]
    have hwKb : w ∈ Kb := by
      rw [hKbdef]
      refine Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩
      · rw [hSdef]; show |w.re| ≤ R0; linarith [le_of_lt hwre, hR0ge]
      · linarith [hy₁H, le_of_lt hwH1]
      · linarith [le_of_lt hwim1]
    -- the localisation of the gate point
    have hinvς : Work.Pert.invOn ΨE (Qm Ξabs α) w = ς :=
      Work.Pert.invOn_eq hΨE.2.1 ⟨ς, hςQ.1, hςΦ⟩ hςQ.1 hςΦ
    have hdisc : ‖ς - (w.im : ℂ) * Complex.I‖ ≤ |w.im| / 8 := by
      have h := (hbandD w hwre (le_trans hYcovH hwH1.le)).2
      rwa [hinvς] at h
    obtain ⟨hςn1, hςn2⟩ := Work.Pert.pert2v2.LeadWire.norm_bounds_near_axis_abs hdisc
    have hς0 : ς ≠ 0 := by
      intro h; rw [h, norm_zero] at hςn1; linarith
    -- the start closeness `‖ς - Xc d w‖ ≤ ηsh`
    have hφw : φ w = tauC σ α ς := by
      rw [hφdef, ← hςΦ, Work.Pert.coordP_eq_tauC_of_mem_image (Q := Qm Ξabs α) hΨE.2.1
        ⟨ς, hςQ.1, rfl⟩, Work.Pert.invOn_eq (Q := Qm Ξabs α) hΨE.2.1 ⟨ς, hςQ.1, rfl⟩ hςQ.1 rfl]
    have hτφ : ‖tauC σ α ς - d.φ w‖ ≤ εband := by
      have h1 := hTransfer w (hKall_sub (hKbKall hwKb))
      have h2 := hclose_all w (hKbKall hwKb)
      rw [← h1.2, hφw] at h2
      exact le_trans h2.le hεband_all
    have hp0 : d.φ w ≠ 0 := by
      have hb := (d.ends_sub w (lt_of_lt_of_le hy₁ (le_trans hy₁H hwH1.le))).2
      have := d.orbit_avoid _ hb 0
      simpa using this
    have hZ0 : Work.Pert.Xc d w ≠ 0 := by
      show -1 / d.φ w ≠ 0
      exact div_ne_zero (by norm_num) hp0
    have hwband : w ∈ {w : ℂ | |w.re| ≤ 1 ∧ H ≤ |w.im| ∧ |w.im| ≤ H + 1} :=
      ⟨hwre.le, hwH1.le, hwim1.le⟩
    have hZR : ‖Work.Pert.Xc d w‖ ≤ Rs := le_trans (hRZ w hwband) (le_max_right _ _)
    have hςR : ‖ς‖ ≤ Rs :=
      le_trans (by linarith only [hςn2, hwim1] : ‖ς‖ ≤ 2 * (H + 1)) (le_max_left _ _)
    have hτinv : ‖tauC σ α ς + 1 / ς‖ ≤ κ0 :=
      Work.Pert.pert2v2.LeadWire.tau_close_of_small (y₀ := H + 1) hαne hCsmp hρpos hρ1
        hδ0pos.le (by linarith only [hH64]) hκ0pos hκ0H hδ0τ hαsmall hu01 hexp
        (by linarith only [hςn1, hwH1, hH64]) (by linarith only [hςn2, hwim1])
    have hstart : ‖ς - Work.Pert.Xc d w‖ ≤ ηsh := by
      have h := Work.Pert.pert2v2.LeadWire.dist_le_of_tau_close (τ := tauC σ α) hς0 hZ0 hςR hZR
        rfl hp0 hτφ hτinv
      have hRs0 : Rs ≠ 0 := ne_of_gt hRspos
      have h1 : 2 * Rs ^ 2 * εband = ηsh := by rw [hεbanddef]; field_simp
      have h2 : Rs ^ 2 * κ0 ≤ Rs ^ 2 * εband := mul_le_mul_of_nonneg_left hκ0band (sq_nonneg _)
      have h3 : Rs ^ 2 * (εband + κ0) = Rs ^ 2 * εband + Rs ^ 2 * κ0 := by ring
      linarith only [h, h1, h2, h3]
    -- the horizon
    have hmMn : m_x ≤ Mn := by
      have h1 : (m_x : ℝ) ≤ Mbd := hmbound
      have h2 : Mbd ≤ (⌈Mbd⌉₊ : ℝ) := Nat.le_ceil Mbd
      exact_mod_cast le_trans h1 h2
    have hmMnR : (m_x : ℝ) ≤ (Mn : ℝ) := by exact_mod_cast hmMn
    -- the walk of `F` from `ς` in the shadow gate
    have hwpos : (32 : ℝ) ≤ |w.im| := by linarith only [hwH1, hH64]
    have hΞsh_w : Ξsh ≤ |w.im| / 2 := by linarith only [hΞshH, hwH1]
    have hςroom := Work.Pert.pert2v2.LeadWire.qp_room_near_axis (Ξ := Ξsh) (s := w.im)
      (N := (17 / 16) * (Mn : ℝ) + 1) (α := α) (z := ς) hwpos hΞsh_w (by positivity)
      (by linarith only [hdisc]) (by linarith only [hAre, hwim1, hMn0, hNreqdef, hΞsh0, hH64, hNextra])
    have hstepSh : ∀ v ∈ MandelDim.Qreg (some (Ξsh : ℂ)) (some (-(Ξsh : ℂ) + 1 / α)),
        ‖liftF u σ α v - (v + 1)‖ ≤ 1 / 32 :=
      fun v hv => (hNTp_abs.1.2 v (Work.Pert.pert2v2.LeadWire.Qp_anti hΞabsΞsh hv)).1
    have hwalkSh : ∀ j : ℕ, j ≤ m_x → (liftF u σ α)^[j] ς ∈ Qp Ξsh α :=
      Work.Pert.pert2v2.walk_Qreg_const (a := (Ξsh : ℂ)) (b := -(Ξsh : ℂ) + 1 / α)
        (F := liftF u σ α) (z := ς) (m := m_x) (c := 1 / 32) (by norm_num) (by norm_num)
        hstepSh hςroom.1 (by
          have h := hςroom.2
          have : (1 + 2 * (1 / 32 : ℝ)) * (m_x : ℝ) + 1 ≤ (17 / 16) * (Mn : ℝ) + 1 := by
            linarith only [hmMnR]
          linarith)
    have hwalkAbs : ∀ j : ℕ, j ≤ m_x → (liftF u σ α)^[j] ς ∈ Qp Ξabs α :=
      fun j hj => Work.Pert.pert2v2.LeadWire.Qp_anti hΞabsΞsh (hwalkSh j hj)
    -- the model walk from `Xc d w`
    have hZdisc : ‖Work.Pert.Xc d w - (w.im : ℂ) * Complex.I‖ ≤ |w.im| / 8 + 1 := by
      have h := norm_sub_le_norm_sub_add_norm_sub (Work.Pert.Xc d w) ς ((w.im : ℂ) * Complex.I)
      rw [norm_sub_rev] at hstart
      linarith only [h, hstart, hdisc, hηsh1]
    have hZroom := Work.Pert.pert2v2.LeadWire.qp_room_near_axis (Ξ := Ξsh) (s := w.im)
      (N := (5 / 4) * (Mn : ℝ) + 1) (α := α) (z := Work.Pert.Xc d w) hwpos hΞsh_w
      (by positivity) hZdisc (by linarith only [hAre, hwim1, hMn0, hNreqdef, hΞsh0, hH64, hNextra])
    have hfar : ∀ v : ℂ, Rf ≤ ‖v‖ → ‖Work.Pert.F0f f₀ v - (v + 1)‖ ≤ 1 / 8 :=
      fun v hv => (hF0f1 v hv).2.1
    have hΞshpos : 0 < Ξsh := lt_of_lt_of_le hΞabspos0 hΞabsΞsh
    have hwalk0 : ∀ j : ℕ, j ≤ m_x → (Work.Pert.F0f f₀)^[j] (Work.Pert.Xc d w) ∈ Qp Ξsh α :=
      Work.Pert.pert2v2.F0f_walk_Qp_18 (Ξ := Ξsh) (Rf := Rf) (z := Work.Pert.Xc d w) (m := m_x)
        (α := α) hΞshpos h2RfΞsh hfar hZroom.1 (by
          have h := hZroom.2
          have : (5 / 4 : ℝ) * (m_x : ℝ) + 1 ≤ (5 / 4) * (Mn : ℝ) + 1 := by
            linarith only [hmMnR]
          linarith)
    have hnormSh : ∀ v ∈ Qp Ξsh α, Ξsh / 2 ≤ ‖v‖ :=
      fun v hv => Work.Pert.pert2v2.Qp_norm_lower hΞshpos hv
    -- the displacements along the two walks
    have hdispF := Work.Pert.pert2v2.LeadWire.walk_disp (G := liftF u σ α) (z := ς) (m := m_x)
      (c := 1 / 32) (by norm_num) (fun j hj => (hNTp_abs.1.2 _ (hwalkAbs j hj.le)).1)
    have hdisp0 := Work.Pert.pert2v2.LeadWire.walk_disp (G := Work.Pert.F0f f₀)
      (z := Work.Pert.Xc d w) (m := m_x) (c := 1 / 8) (by norm_num)
      (fun j hj => hfar _ (le_trans (by linarith only [h2RfΞsh]) (hnormSh _ (hwalk0 j hj.le))))
    -- the shadow set
    have hstay : ∀ j : ℕ, j ≤ m_x →
        (liftF u σ α)^[j] ς ∈ Qp Ξsh α ∩ Metric.closedBall (0 : ℂ) Rq := by
      intro j hj
      refine ⟨hwalkSh j hj, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 := hdispF j hj
      have h2 : ‖(liftF u σ α)^[j] ς‖ ≤ ‖(liftF u σ α)^[j] ς - ς‖ + ‖ς‖ := by
        have := norm_sub_norm_le ((liftF u σ α)^[j] ς) ς
        linarith
      have hj' : (j : ℝ) ≤ (Mn : ℝ) := by exact_mod_cast le_trans hj hmMn
      rw [hRqdef]
      linarith only [h1, h2, hj', hςn2, hwim1, hH64]
    have hstay0 : ∀ j : ℕ, j ≤ m_x →
        (Work.Pert.F0f f₀)^[j] (Work.Pert.Xc d w) ∈ Qp Ξsh α ∩ Metric.closedBall (0 : ℂ) Rq := by
      intro j hj
      refine ⟨hwalk0 j hj, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 := hdisp0 j hj
      have h2 : ‖(Work.Pert.F0f f₀)^[j] (Work.Pert.Xc d w)‖
          ≤ ‖(Work.Pert.F0f f₀)^[j] (Work.Pert.Xc d w) - Work.Pert.Xc d w‖
            + ‖Work.Pert.Xc d w‖ := by
        have := norm_sub_norm_le ((Work.Pert.F0f f₀)^[j] (Work.Pert.Xc d w)) (Work.Pert.Xc d w)
        linarith
      have h3 : ‖Work.Pert.Xc d w‖ ≤ ‖ς‖ + ηsh := by
        have := norm_sub_norm_le (Work.Pert.Xc d w) ς
        rw [norm_sub_rev] at this
        linarith only [this, hstart]
      have hj' : (j : ℝ) ≤ (Mn : ℝ) := by exact_mod_cast le_trans hj hmMn
      rw [hRqdef]
      linarith only [h1, h2, h3, hj', hςn2, hwim1, hηsh1, hH64]
    -- the local Lipschitz bound of `F0f` and the closeness `liftF ≈ F0f` on the shadow set
    have hlipSh : ∀ a ∈ Qp Ξsh α ∩ Metric.closedBall (0 : ℂ) Rq,
        ∀ b ∈ Qp Ξsh α ∩ Metric.closedBall (0 : ℂ) Rq, ‖a - b‖ ≤ Bsh →
        ‖Work.Pert.F0f f₀ a - Work.Pert.F0f f₀ b‖ ≤ Ksh * ‖a - b‖ := by
      intro a ha b hb hab
      have hanorm : Rf ≤ ‖a‖ := le_trans (by linarith only [h2RfΞsh]) (hnormSh a ha.1)
      have hapos : 0 < ‖a‖ := lt_of_lt_of_le hRfpos hanorm
      have h1 := hF0f2 a hanorm a b (by rw [sub_self, norm_zero]; positivity)
        (by rw [hBshdef] at hab; rw [norm_sub_rev]; linarith only [hab, hanorm])
      have h2 : 4 * Cf / ‖a‖ ^ 2 ≤ 4 * Cf / Rf ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ hRfpos.le hanorm 2
      have h3 : (1 + 4 * Cf / ‖a‖ ^ 2) * ‖a - b‖ ≤ Ksh * ‖a - b‖ := by
        rw [hKshdef]
        exact mul_le_mul_of_nonneg_right (by linarith only [h2]) (norm_nonneg _)
      linarith only [h1, h3]
    have hcloseSh : ∀ a ∈ Qp Ξsh α ∩ Metric.closedBall (0 : ℂ) Rq,
        ‖liftF u σ α a - Work.Pert.F0f f₀ a‖ ≤ δsh := by
      intro a ha
      have hanorm : Ξsh / 2 ≤ ‖a‖ := hnormSh a ha.1
      have haRq : ‖a‖ ≤ Rq := by
        have h := ha.2
        rw [Metric.mem_closedBall, dist_zero_right] at h
        exact h
      have haRm : Rm ≤ ‖a‖ := le_trans (by linarith only [h2RmΞsh]) hanorm
      have hτa : ‖tauC σ α a + 1 / a‖ ≤ κ0 :=
        Work.Pert.pert2v2.LeadWire.tau_close_of_small (y₀ := Rq / 2) hαne hCsmp hρpos hρ1
          hδ0pos.le (by linarith only [hRqdef, hH64, hMn0]) hκ0pos hκ0q hδ0τ hαsmall hu01 hexp
          (by linarith only [haRm, hRm128]) (by linarith only [haRq])
      have hucl' := hucl f Df L u σ hLcpt hballL hLD (nearOn_mono hNear subset_rfl hδ0u) hf0
        huD hub hform
      have hαa : ‖α‖ * ‖a‖ ≤ 1 / 2 := by
        have := mul_le_mul_of_nonneg_left haRq (norm_nonneg α)
        linarith only [this, hαRq]
      have h := hcloseD (u := u) (σ := σ) (α := α) (w := a) (η := ηu) hηupos hηu1000 hηu2π
        hηuRm huD hucl' (le_trans hu0θ hθηu) hαne (by linarith only [hαθ, hθηu, hθApos]) hexp haRm
        (le_trans hτa hκ0u) hαa
      have h2 : Cm * ηu ≤ δsh := by
        have := mul_le_mul_of_nonneg_left hηuδ hCmpos.le
        rw [show Cm * (δsh / Cm) = δsh by field_simp] at this
        exact this
      linarith only [h, h2]
    -- the shadowing estimate
    have harith := Work.Pert.pert2v2.LeadWire.shadow_arith (K := Ksh) (η := ηsh) (δ := δsh)
      (Bm := Bm) (m := m_x) (Mn := Mn) hKsh1 hBmpos hmMn rfl rfl
    have hsh := Work.Pert.pert2v2.shadow_walk_local (F := liftF u σ α) (F₀ := Work.Pert.F0f f₀)
      (Q := Qp Ξsh α ∩ Metric.closedBall (0 : ℂ) Rq) (K := Ksh) (η := ηsh) (δ := δsh) (B := Bsh)
      (m := m_x) (z := ς) (z₀ := Work.Pert.Xc d w) hKsh1 hηshpos.le hδshpos.le hlipSh hcloseSh
      hstay hstay0 hstart (by linarith only [harith, hBmB, hBmpos])
    have hmod : (Work.Pert.F0f f₀)^[m_x] (Work.Pert.Xc d w)
        = MandelDim.tau0 (f₀^[m_x] (d.φ w)) := by
      rw [Work.Pert.pert2v2.F0f_iterate, Work.Pert.pert2v2.tau0_Xc']
    have hshadow : ‖(liftF u σ α)^[m_x] ς - MandelDim.tau0 (f₀^[m_x] (d.φ w))‖ < 4 := by
      rw [← hmod]
      linarith only [hsh, harith, hBm4, hBmpos]
    -- the coincidence and the identification of the two pieces
    obtain ⟨hmemQ, hcoinc⟩ := Work.Pert.pert2v2.shadow_coinc_v7 d hQp'eq hinjτ hwKb hwalkAbs
      hτFp hshadow
    have hkey := Work.Pert.pert2v2.Rlow_eq_retOf_crux_walk (Df := Df) hΨE hΨp_rel hτFp hΨp.2.2
      hinjτ hQp'sub_abs hςQ hwalkAbs hcoinc
    have hφς : coordP f Df (tauC σ α) ΨE (Qm Ξabs α) (ΨE ς) = tauC σ α ς := by
      rw [Work.Pert.coordP_eq_tauC_of_mem_image (Q := Qm Ξabs α) hΨE.2.1 ⟨ς, hςQ.1, rfl⟩,
        Work.Pert.invOn_eq (Q := Qm Ξabs α) hΨE.2.1 ⟨ς, hςQ.1, rfl⟩ hςQ.1 rfl]
    have hagF : Ψp ((liftF u σ α)^[m_x] ς) = Φp ((liftF u σ α)^[m_x] ς) :=
      hagreep _ (hQp'sub hmemQ)
    rw [hRhigh_eq_ret w hwH, ← hςΦ, ← hkey]
    simp only [hRlowdef, hφdef, Work.Pert.pert2v2.RlowPiece, Work.Pert.Rlow]
    rw [hφς, hcoinc, hagF]
  -- ## 8c. the glue
  obtain ⟨R, DR, hDRopen, hRequiv, hRholo, hRlowEq, hRhighEq, hDRdef⟩ :=
    Work.Pert.pert2v2.twoPieceR_overlap (x₀ := 0) (R1 := 1) (Hband := H)
      (by norm_num) le_rfl hUlowOpen hRlowD hRlow1 hUhighOpen hRhighD hRhigh1
      hwinLow hwinHigh hWlow hWhigh hcross
  -- ## 8d. the remaining `PertData` R-fields for the glued `R`
  -- the low half of `R_close`: by definition of `Ulow`, on the low chart the estimate holds
  have hEstLow : ∀ w : ℂ, w ∈ Ulow → ‖Rlow w + 1 / α - d.E w‖ < δ := by
    intro w hw
    rw [hUlowdef, Set.mem_setOf_eq] at hw
    exact hw.2.2.2.2.2
  have hDRsub : K ∪ {w : ℂ | y₁ ≤ |w.im|} ⊆ DR := by
    have hR0ge : (1 : ℝ) ≤ R0 := by rw [hR0def]; linarith [le_max_right RK 0]
    rw [hDRdef]
    intro w hw
    rcases hw with hwK | hwb
    · -- `w ∈ K`: reduce to a point of the blob `Z ⊆ Kb` in the window
      obtain ⟨z, hzZ, n, hn⟩ := hZred w hwK
      have hzre : |z.re| < 1 := lt_of_le_of_lt (hZwin z hzZ) (by norm_num)
      refine Set.mem_iUnion.mpr ⟨n, z, ?_, hn.symm⟩
      by_cases him : |z.im| < H + 1
      · exact Or.inl (hKb_window z (Or.inl hzZ) hzre him)
      · exact Or.inr (hTall z hzre (by push_neg at him; linarith))
    · -- `w` in the band: reduce its real part into `(-1, 1)`
      have hb : y₁ ≤ |w.im| := hwb
      set z : ℂ := w + (((-(⌊w.re⌋)) : ℤ) : ℂ) with hzdef
      have hzfl : (⌊w.re⌋ : ℝ) ≤ w.re := Int.floor_le w.re
      have hzfu : w.re < (⌊w.re⌋ : ℝ) + 1 := Int.lt_floor_add_one w.re
      have hcast : (((-(⌊w.re⌋)) : ℤ) : ℂ) = ((-(⌊w.re⌋ : ℝ)) : ℂ) := by
        rw [Complex.ofReal_intCast]; push_cast; ring
      have hzval : z.re = w.re - (⌊w.re⌋ : ℝ) := by
        rw [hzdef, hcast, Complex.add_re, Complex.neg_re, Complex.ofReal_re]; ring
      have hzval' : z.im = w.im := by
        rw [hzdef, hcast, Complex.add_im, Complex.neg_im, Complex.ofReal_im]; ring
      have hzre' : |z.re| < 1 := by
        rw [hzval, abs_lt]
        exact ⟨by linarith, by linarith⟩
      have hwz : w = z + (((⌊w.re⌋) : ℤ) : ℂ) := by
        rw [hzdef]; push_cast; ring
      refine Set.mem_iUnion.mpr ⟨(⌊w.re⌋ : ℤ), z, ?_, hwz.symm⟩
      by_cases him : |z.im| < H + 1
      · refine Or.inl (hKb_window z ?_ hzre' him)
        -- `z` lies in the band part of `Kb`
        rw [hKbdef]
        refine Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩
        · rw [hSdef]; show |z.re| ≤ R0; linarith [le_of_lt hzre', hR0ge]
        · rw [hzval']; exact hb
        · rw [hzval'] at him ⊢; linarith
      · refine Or.inr (hTall z hzre' ?_)
        push_neg at him
        linarith
  -- `d.E` is uniformly close to the identity at the upper end
  have hUp : ∃ Y : ℝ, ∀ w : ℂ, Y < w.im → ‖d.E w - w‖ < δ / 3 := by
    have hmem : ∀ᶠ w in MandelDim.upperEnd, ‖d.E w - w‖ < δ / 3 := by
      filter_upwards [d.E_upper.eventually
        (Metric.ball_mem_nhds (0 : ℂ) (by linarith : (0 : ℝ) < δ / 3))] with w hw
      simpa [Metric.mem_ball, dist_eq_norm, MandelDim.ParabData.E] using hw
    rw [MandelDim.upperEnd, Filter.eventually_comap, Filter.eventually_atTop] at hmem
    obtain ⟨B₀, hB₀⟩ := hmem
    exact ⟨B₀, fun w hw => hB₀ w.im (le_of_lt hw) w rfl⟩
  have hCim : (0 : ℝ) ≤ |(1 / α).im| := abs_nonneg _
  have hEstHighUp : ∃ Y : ℝ, ∀ w : ℂ, w ∈ Uhigh → Y < w.im →
      ‖Rhigh w + 1 / α - d.E w‖ < δ := by
    obtain ⟨Y1, hY1⟩ := hEndmS (δ / 3) (by linarith)
    obtain ⟨Y2, hY2⟩ := hEndpS (δ / 3) (by linarith)
    obtain ⟨Y3, hY3⟩ := hUp
    set Yt : ℝ := max (max (max Yc Y1) (max Y2 Y3)) 0 + (C + |(1 / α).im| + 1) + 1 with hYtdef
    have hYm : Yc ≤ max (max (max Yc Y1) (max Y2 Y3)) 0 :=
      le_trans (le_trans (le_max_left Yc Y1) (le_max_left (max Yc Y1) (max Y2 Y3)))
        (le_max_left (max (max Yc Y1) (max Y2 Y3)) 0)
    have hY1m : Y1 ≤ max (max (max Yc Y1) (max Y2 Y3)) 0 :=
      le_trans (le_trans (le_max_right Yc Y1) (le_max_left (max Yc Y1) (max Y2 Y3)))
        (le_max_left (max (max Yc Y1) (max Y2 Y3)) 0)
    have hY2m : Y2 ≤ max (max (max Yc Y1) (max Y2 Y3)) 0 :=
      le_trans (le_trans (le_max_left Y2 Y3) (le_max_right (max Yc Y1) (max Y2 Y3)))
        (le_max_left (max (max Yc Y1) (max Y2 Y3)) 0)
    have hY3m : Y3 ≤ max (max (max Yc Y1) (max Y2 Y3)) 0 :=
      le_trans (le_trans (le_max_right Y2 Y3) (le_max_right (max Yc Y1) (max Y2 Y3)))
        (le_max_left (max (max Yc Y1) (max Y2 Y3)) 0)
    refine ⟨Yt, fun w hwU hw => ?_⟩
    have hwYt : Yt < w.im := hw
    have hYcw : Yc + (C + |(1 / α).im| + 1) < w.im := by rw [hYtdef] at hwYt; linarith
    have hY1w : Y1 + (C + |(1 / α).im| + 1) < w.im := by rw [hYtdef] at hwYt; linarith
    have hY2w : Y2 + (C + |(1 / α).im| + 1) < w.im := by rw [hYtdef] at hwYt; linarith
    have hY3w : Y3 < w.im := by rw [hYtdef] at hwYt; linarith
    obtain ⟨ς₀, hς₀M, hς₀Φ⟩ : ∃ ς ∈ Mset, ΨE ς = w := by
      have h := hwU
      rw [hUhighdef, Set.mem_setOf_eq] at h
      exact h.2.2
    have hς₀Qm : ς₀ ∈ Qm Ξabs α := (hMsub hς₀M).1
    have hς₀Qp : ς₀ ∈ Qp Ξabs α := (hMsub hς₀M).2
    have hwre : |w.re| < 1 := by
      have h := hwU
      rw [hUhighdef, Set.mem_setOf_eq] at h
      exact h.1
    have hmemImg : w ∈ ΨE '' (Qm Ξabs α) := ⟨ς₀, hς₀Qm, hς₀Φ⟩
    have hinv : Work.Pert.invOn ΨE (Qm Ξabs α) w = ς₀ :=
      Work.Pert.invOn_eq hΨE.2.1 hmemImg hς₀Qm hς₀Φ
    have hpr := hpre w (by linarith) hwre hmemImg
    have hς₀re : |ς₀.re| ≤ Bst := by
      have h := hpr.1
      rw [hinv] at h
      have h2 : B ≤ Bst := by rw [hBstdef]; linarith [abs_nonneg ((1 / α).re)]
      linarith
    have hς₀im1 : Y1 < ς₀.im := by
      have h := hpr.2
      rw [hinv] at h
      linarith
    have hς₀im2 : Y2 < ς₀.im := by
      have h := hpr.2
      rw [hinv] at h
      linarith
    have hA1 : ‖ΨE ς₀ - ς₀ - cm‖ < δ / 3 := hY1 _ hς₀Qm hς₀im1 hς₀re
    have hA2 : ‖Ψp ς₀ - ς₀ - cp‖ < δ / 3 := hY2 _ hς₀Qp hς₀im2 hς₀re
    have hA3 : ‖d.E w - w‖ < δ / 3 := hY3 w hY3w
    have hRw : Rhigh w = Ψp ς₀ + dlow := by
      rw [hRhigh_eq_ret w hwU, Work.Pert.retOf, hinv]
      rw [hΨp_rel ς₀ hς₀Qp]; ring
    have heq : Rhigh w + 1 / α - d.E w
        = (Ψp ς₀ - ς₀ - cp) - (ΨE ς₀ - ς₀ - cm) - (d.E w - w) := by
      rw [hRw, hdlow_id, hς₀Φ]; ring
    have hbound : ‖(Ψp ς₀ - ς₀ - cp) - (ΨE ς₀ - ς₀ - cm) - (d.E w - w)‖
        ≤ ‖Ψp ς₀ - ς₀ - cp‖ + ‖ΨE ς₀ - ς₀ - cm‖ + ‖d.E w - w‖ := by
      have h1 : ‖(Ψp ς₀ - ς₀ - cp) - (ΨE ς₀ - ς₀ - cm) - (d.E w - w)‖
          ≤ ‖(Ψp ς₀ - ς₀ - cp) - (ΨE ς₀ - ς₀ - cm)‖ + ‖d.E w - w‖ := norm_sub_le _ _
      have h2 : ‖(Ψp ς₀ - ς₀ - cp) - (ΨE ς₀ - ς₀ - cm)‖
          ≤ ‖Ψp ς₀ - ς₀ - cp‖ + ‖ΨE ς₀ - ς₀ - cm‖ := norm_sub_le _ _
      linarith
    rw [heq]
    linarith
  -- ## 8d-quinquies. the estimate on the two boundary lines `im = ±y₁` (via the low chart)
  have hlinLow : ∀ w : ℂ, |w.im| = |y₁| → w.im = y₁ ∨ w.im = -y₁ → w ∈ DR →
      ‖R w + 1 / α - d.E w‖ < δ := by
    intro w hwim hdisj hwDR
    rw [hDRdef] at hwDR
    simp only [Set.mem_iUnion, Set.mem_image] at hwDR
    obtain ⟨n, z, hzU, hzw⟩ := hwDR
    have hzw' : w = z + (n : ℂ) := hzw.symm
    have hzim : |z.im| = |y₁| := by
      have h := hwim
      rw [hzw'] at h
      simpa using h
    have hy₁lt : |y₁| < H + 1 := by linarith [hAbsy₁H]
    have hzUlow : z ∈ Ulow := by
      rcases hzU with h | h
      · exact h
      · exfalso
        have h' := h
        rw [hUhighdef, Set.mem_setOf_eq] at h'
        have h2 : H < |z.im| := h'.2.1
        rw [hzim] at h2
        linarith
    have hzDE : z ∈ d.DE := by
      have h' := hzUlow
      rw [hUlowdef, Set.mem_setOf_eq] at h'
      exact h'.2.2.1
    have hzDR : z ∈ DR := by
      rw [hDRdef]
      exact Set.mem_iUnion.mpr ⟨0, z, Or.inl hzUlow, by simp⟩
    have h1 : R w = R z + (n : ℂ) := by
      rw [hzw']; exact Work.Pert.pert2v2.TEquivOn_add_int hRequiv n hzDR
    have h2 : d.E w = d.E z + (n : ℂ) := by
      rw [hzw']; exact Work.Pert.pert2v2.E_add_int_DE d hd n z hzDE
    have h3 : ‖Rlow z + 1 / α - d.E z‖ < δ := hEstLow z hzUlow
    have h4 : R z = Rlow z := hRlowEq z hzUlow
    rw [h1, h2, show R z + (n : ℂ) + 1 / α - (d.E z + (n : ℂ)) = R z + 1 / α - d.E z by ring,
      h4]
    exact h3
  -- ## 8d-sexies. `R - d.E` is bounded on the upper half plane
  have hBddUp : ∃ C : ℝ, ∀ w : ℂ, y₁ ≤ w.im → ‖R w - d.E w‖ ≤ C := by
    obtain ⟨Yt₀, hYt₀⟩ := hEstHighUp
    set Yt : ℝ := max Yt₀ (H + 1) with hYtdef
    have hYtH : H + 1 ≤ Yt := le_max_right _ _
    have hYt : ∀ w : ℂ, w ∈ Uhigh → Yt < w.im → ‖Rhigh w + 1 / α - d.E w‖ < δ :=
      fun w hwU hw => hYt₀ w hwU (lt_of_le_of_lt (le_max_left _ _) hw)
    set S : Set ℂ := {z : ℂ | y₁ ≤ z.im ∧ z.im ≤ max Yt y₁ ∧ 0 ≤ z.re ∧ z.re ≤ 1} with hSdef
    have hSsubDR : S ⊆ DR := by
      intro z hz
      refine hDRsub (Or.inr ?_)
      show y₁ ≤ |z.im|
      exact le_trans hz.1 (le_abs_self z.im)
    have hSsubDE : S ⊆ d.DE := by
      intro z hz
      refine d.ends_sub z ?_
      exact lt_of_lt_of_le hy₁ (le_trans hz.1 (le_abs_self z.im))
    have hScpt : IsCompact S := by
      rw [hSdef]
      have hcl : IsClosed {z : ℂ | y₁ ≤ z.im ∧ z.im ≤ max Yt y₁ ∧ 0 ≤ z.re ∧ z.re ≤ 1} :=
        (isClosed_le continuous_const Complex.continuous_im).inter
          ((isClosed_le Complex.continuous_im continuous_const).inter
            ((isClosed_le continuous_const Complex.continuous_re).inter
              (isClosed_le Complex.continuous_re continuous_const)))
      refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hcl, ?_⟩
      refine (Metric.isBounded_closedBall (x := (0 : ℂ))
        (r := 2 + |max Yt y₁| + |y₁|)).subset ?_
      intro z hz
      obtain ⟨h1, h2, h3, h4⟩ := hz
      rw [Metric.mem_closedBall, dist_zero_right]
      have h5 : |z.im| ≤ |max Yt y₁| + |y₁| := by
        rw [abs_le]
        exact ⟨by linarith [neg_le_abs y₁, abs_nonneg (max Yt y₁)],
          by linarith [le_abs_self (max Yt y₁), abs_nonneg y₁]⟩
      have h6 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      have h7 : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, h4⟩
      have h8 : (0 : ℝ) ≤ |max Yt y₁| := abs_nonneg _
      linarith
    obtain ⟨Mcomp, hMcomp⟩ : ∃ M : ℝ, ∀ z ∈ S, ‖R z - d.E z‖ ≤ M := by
      have hcont : ContinuousOn (fun z : ℂ => R z - d.E z) S :=
        ((hRholo.continuousOn.mono hSsubDR).sub (hdEdiff.continuousOn.mono hSsubDE))
      obtain ⟨M, hM⟩ := hScpt.exists_bound_of_continuousOn hcont
      exact ⟨M, fun z hz => by simpa using hM z hz⟩
    refine ⟨max Mcomp (δ + ‖1 / α‖ + 1), fun w hw => ?_⟩
    by_cases hfar : Yt < w.im
    · have hwDR : w ∈ DR := hDRsub (Or.inr (le_trans hw (le_abs_self w.im)))
      rw [hDRdef] at hwDR
      simp only [Set.mem_iUnion, Set.mem_image] at hwDR
      obtain ⟨n, z, hzU, hzw⟩ := hwDR
      have hzw' : w = z + (n : ℂ) := hzw.symm
      have hzimw : z.im = w.im := by rw [hzw']; simp
      have hηH : d.η₀ < H := by linarith [hy₁, hy₁H]
      have hHw : H ≤ w.im := by linarith [lt_of_le_of_lt hYtH hfar]
      have hzDE : z ∈ d.DE := by
        rcases hzU with h | h
        · have h' := h
          rw [hUlowdef, Set.mem_setOf_eq] at h'
          exact h'.2.2.1
        · refine d.ends_sub z ?_
          rw [hzimw]
          exact lt_of_lt_of_le hηH (le_trans hHw (le_abs_self w.im))
      have hzDR : z ∈ DR := by
        rw [hDRdef]
        exact Set.mem_iUnion.mpr ⟨0, z, hzU, by simp⟩
      have h1 : R w = R z + (n : ℂ) := by
        rw [hzw']; exact Work.Pert.pert2v2.TEquivOn_add_int hRequiv n hzDR
      have h2 : d.E w = d.E z + (n : ℂ) := by
        rw [hzw']; exact Work.Pert.pert2v2.E_add_int_DE d hd n z hzDE
      have h3 : ‖R z + 1 / α - d.E z‖ < δ := by
        rcases hzU with h | h
        · have h' : ‖Rlow z + 1 / α - d.E z‖ < δ := hEstLow z h
          rw [hRlowEq z h]
          exact h'
        · have h' := hYt z h (by rw [hzimw]; exact hfar)
          rw [hRhighEq z h]
          exact h'
      have harith : ‖R z - d.E z‖ ≤ ‖R z + 1 / α - d.E z‖ + ‖1 / α‖ := by
        have he : R z - d.E z = (R z + 1 / α - d.E z) - 1 / α := by ring
        rw [he]
        exact norm_sub_le _ _
      rw [h1, h2, show R z + (n : ℂ) - (d.E z + (n : ℂ)) = R z - d.E z by ring]
      refine le_trans harith ?_
      linarith [h3, le_max_right Mcomp (δ + ‖1 / α‖ + 1)]
    · -- the middle band: translate into the fundamental window and use compactness
      push_neg at hfar
      set k : ℤ := ⌊w.re⌋ with hk
      set z : ℂ := w - (k : ℂ) with hzdef
      have hcast : ((k : ℤ) : ℂ) = ((k : ℝ) : ℂ) := by rw [Complex.ofReal_intCast]
      have hzre : z.re = w.re - (k : ℝ) := by
        rw [hzdef, Complex.sub_re, hcast, Complex.ofReal_re]
      have hzim : z.im = w.im := by
        rw [hzdef, Complex.sub_im, hcast, Complex.ofReal_im]; ring
      have hzS : z ∈ S := by
        rw [hSdef]
        refine ⟨by rw [hzim]; exact hw, ?_, ?_, ?_⟩
        · rw [hzim]; exact le_trans hfar (le_max_left _ _)
        · rw [hzre]; have := Int.floor_le w.re; linarith
        · rw [hzre]; have := Int.lt_floor_add_one w.re; linarith
      have hzDR : z ∈ DR := hSsubDR hzS
      have hzDE : z ∈ d.DE := hSsubDE hzS
      have hwz : w = z + (k : ℂ) := by rw [hzdef]; ring
      have h1 : R w = R z + (k : ℂ) := by
        rw [hwz]; exact Work.Pert.pert2v2.TEquivOn_add_int hRequiv k hzDR
      have h2 : d.E w = d.E z + (k : ℂ) := by
        rw [hwz]; exact Work.Pert.pert2v2.E_add_int_DE d hd k z hzDE
      rw [h1, h2, show R z + (k : ℂ) - (d.E z + (k : ℂ)) = R z - d.E z by ring]
      exact le_trans (hMcomp z hzS) (le_max_left _ _)
  have hlineUp : ∀ w : ℂ, w.im = y₁ → ‖R w + 1 / α - d.E w‖ < δ := by
    intro w hw
    refine hlinLow w ?_ (Or.inl hw) (hDRsub (Or.inr ?_))
    · show |w.im| = |y₁|
      rw [hw]
    · show y₁ ≤ |w.im|
      rw [hw]; exact le_abs_self y₁
  have hlineDn : ∀ w : ℂ, w.im = -y₁ → ‖R w + 1 / α - d.E w‖ < δ := by
    intro w hw
    refine hlinLow w ?_ (Or.inr hw) (hDRsub (Or.inr ?_))
    · show |w.im| = |y₁|
      rw [hw, abs_neg]
    · show y₁ ≤ |w.im|
      rw [hw, abs_neg]; exact le_abs_self y₁
  -- ## 8d-septies. `R_close` on the upper half plane (Phragmén–Lindelöf)
  have hRcloseUp : ∀ w : ℂ, y₁ ≤ w.im → ‖R w + 1 / α - d.E w‖ < δ := by
    refine upperHalf_close_of_line
      (fun w hw => hRholo.differentiableAt (hDRopen.mem_nhds
        (hDRsub (Or.inr (le_trans hw (le_abs_self w.im))))))
      (fun w hw => hdEdiff.differentiableAt (hdDEopen.mem_nhds
        (d.ends_sub w (lt_of_lt_of_le hy₁ (le_trans hw (le_abs_self w.im))))))
      (fun w hw => ?_) (fun w hw => ?_) hBddUp hlineUp
    · have hDR : w ∈ DR := hDRsub (Or.inr (le_trans hw (le_abs_self w.im)))
      have h := Work.Pert.pert2v2.TEquivOn_add_int hRequiv (1 : ℤ) hDR
      simpa using h
    · have hDE : w ∈ d.DE := d.ends_sub w (lt_of_lt_of_le hy₁ (le_trans hw (le_abs_self w.im)))
      have h := Work.Pert.pert2v2.E_add_int_DE d hd (1 : ℤ) w hDE
      simpa using h
  -- ## 8d-octies. `R_close` on the lower half plane (the `waist_return_bound_*` input)
  have hRcloseDn : ∀ w : ℂ, w.im ≤ -y₁ → ‖R w + 1 / α - d.E w‖ < δ := by
    -- ## the datum-level lower decay of `F` (the input of `waist_return_bound_low`)
    have hσr : ‖σ‖ < ρ := by
      have h1 : Csm * δ0 / ρ ≤ Csm * (ρ ^ 2 / (2 * Csm)) / ρ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hδ0rho2 hCsmp.le) hρpos.le
      have h3 : Csm * (ρ ^ 2 / (2 * Csm)) / ρ = ρ / 2 := by
        field_simp
      linarith [hσsmall, h1, h3, hρpos]
    have hdecL : ∃ ρ' : ℂ, ‖ρ' - 1‖ ≤ 1 / 32 ∧ ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧
        ∀ z ∈ Qm Ξabs α, z.im < -Y →
          ‖Work.Pert.liftF u σ α z - (z + ρ')‖ ≤ M * Real.exp (κ * z.im) :=
      Work.Pert.liftF_lower_decay_gate hΞabspos hρpos hσne hαne hα64 hInF1α huD hub hexp hσr
        hτQ_abs (fun z hz => (hNT_abs.1.2 z hz).1) hQAdm_abs
    obtain ⟨ρlo, hρlo, Mlo, κlo, Ylo, hMlo, hκlo, hdecLo⟩ := hdecL
    -- ## the two far bounds of the margin waist (the children)
    obtain ⟨Ku, Cu, hCu⟩ := Work.Pert.pert2v2.waist_return_bound_up (u := u) (σ := σ) (α := α)
      (d := dlow) (Ξ := Ξabs) (F := Work.Pert.liftF u σ α) (Φm := ΨE) (Φp := Ψp)
      hF hΞabspos hInF1α hQAdm_abs hQAdm_p_abs hNT_abs hNTp_abs hΨE hΨp
      (fun z hz => by rw [hΨp_rel z hz]; ring) hdecQm
    obtain ⟨Kl, Cl, hCl⟩ := Work.Pert.pert2v2.waist_return_bound_low (u := u) (σ := σ) (α := α)
      (d := dlow) (Ξ := Ξabs) (F := Work.Pert.liftF u σ α) (Φm := ΨE) (Φp := Ψp)
      hF hΞabspos hInF1α hQAdm_abs hQAdm_p_abs hNT_abs hNTp_abs hΨE hΨp
      (fun z hz => by rw [hΨp_rel z hz]; ring)
      ⟨ρlo, Mlo, κlo, Ylo, hρlo, hMlo, hκlo, hdecLo⟩
    -- ## the compact middle of the waist
    set T₂ : Set ℂ := {ς : ℂ | |ς.re| + 2 ≤ |ς.im| - Ξabs ∧ |ς.im| ≤ max Ku Kl} with hT₂def
    have hT₂cpt : IsCompact T₂ := by
      rw [hT₂def]
      have hcl : IsClosed {ς : ℂ | |ς.re| + 2 ≤ |ς.im| - Ξabs ∧ |ς.im| ≤ max Ku Kl} :=
        (isClosed_le ((continuous_abs.comp Complex.continuous_re).add continuous_const)
          ((continuous_abs.comp Complex.continuous_im).sub continuous_const)).inter
          (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
      refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hcl, ?_⟩
      refine (Metric.isBounded_closedBall (x := (0 : ℂ))
        (r := 2 * |max Ku Kl| + Ξabs + 1)).subset ?_
      intro ς hς
      obtain ⟨h1, h2⟩ := hς
      rw [Metric.mem_closedBall, dist_zero_right]
      have h3 : |ς.im| ≤ |max Ku Kl| := le_trans h2 (le_abs_self _)
      have h4 : |ς.re| ≤ |ς.im| := by linarith
      have h5 : ‖ς‖ ≤ |ς.re| + |ς.im| := Complex.norm_le_abs_re_add_abs_im ς
      have h6 : (0 : ℝ) ≤ Ξabs := le_of_lt hΞabspos
      have h7 : (0 : ℝ) ≤ |max Ku Kl| := abs_nonneg _
      linarith
    have hT₂Qm : T₂ ⊆ Qm Ξabs α := by
      intro ς hς
      have h1 : |ς.re| + 2 ≤ |ς.im| - Ξabs := hς.1
      rw [Work.Pert.mem_Qm_iff_g]
      refine ⟨?_, ?_⟩
      · show (0 : ℝ) < ς.re - Ξabs + (1 / α).re + |ς.im + (1 / α).im|
        have h2 : -|ς.re| ≤ ς.re := neg_abs_le ς.re
        have h3 : |ς.im| - |(1 / α).im| ≤ |ς.im + (1 / α).im| := by
          have h := abs_sub_abs_le_abs_sub ς.im (-(1 / α).im)
          have h4 : ς.im - -(1 / α).im = ς.im + (1 / α).im := by ring
          rw [h4, abs_neg] at h
          exact h
        have h5 : (1 / α).im ≤ |(1 / α).im| := le_abs_self _
        linarith [hInF1inv.le]
      · show (0 : ℝ) < |ς.im| - Ξabs - ς.re
        have h2 : ς.re ≤ |ς.re| := le_abs_self ς.re
        linarith
    have hTt₂Qm : Work.Pert.Tt α '' T₂ ⊆ Qm Ξabs α := by
      intro ς hς
      obtain ⟨t, ht, rfl⟩ := hς
      have h1 : |t.re| + 2 ≤ |t.im| - Ξabs := ht.1
      rw [Work.Pert.mem_Qm_iff_g]
      refine ⟨?_, ?_⟩
      · show (0 : ℝ) < (Work.Pert.Tt α t).re - Ξabs + (1 / α).re
            + |(Work.Pert.Tt α t).im + (1 / α).im|
        have hTtre : (Work.Pert.Tt α t).re = t.re - (1 / α).re := by rw [Work.Pert.Tt]; simp
        have hTtim : (Work.Pert.Tt α t).im = t.im - (1 / α).im := by rw [Work.Pert.Tt]; simp
        rw [hTtre, hTtim]
        have h3 : t.im - (1 / α).im + (1 / α).im = t.im := by ring
        rw [h3]
        have h2 : -|t.re| ≤ t.re := neg_abs_le t.re
        linarith
      · show (0 : ℝ) < |(Work.Pert.Tt α t).im| - Ξabs - (Work.Pert.Tt α t).re
        have hTtre : (Work.Pert.Tt α t).re = t.re - (1 / α).re := by rw [Work.Pert.Tt]; simp
        have hTtim : (Work.Pert.Tt α t).im = t.im - (1 / α).im := by rw [Work.Pert.Tt]; simp
        rw [hTtre, hTtim]
        have h3 : |t.im - (1 / α).im| ≥ |t.im| - |(1 / α).im| := by
          have h := abs_sub_abs_le_abs_sub t.im ((1 / α).im)
          exact h
        have h4 : (1 / α).im ≤ |(1 / α).im| := le_abs_self _
        have h5 : t.re ≤ |t.re| := le_abs_self t.re
        linarith [hInF1inv.le, h1, h3]
    obtain ⟨Cmid, hCmid⟩ : ∃ C : ℝ, ∀ ς ∈ T₂, ‖ΨE (Work.Pert.Tt α ς) - ΨE ς‖ ≤ C := by
      have hcont : ContinuousOn (fun ς : ℂ => ΨE (Work.Pert.Tt α ς) - ΨE ς) T₂ :=
        (hΨE.1.continuousOn.comp
          (continuousOn_id.sub continuousOn_const) (fun ς hς => hTt₂Qm ⟨ς, hς, rfl⟩)).sub
          (hΨE.1.continuousOn.mono hT₂Qm)
      obtain ⟨M, hM⟩ := hT₂cpt.exists_bound_of_continuousOn hcont
      exact ⟨M, fun ς hς => by simpa using hM ς hς⟩
    -- the `d.E - id` bound on the band
    obtain ⟨C_E, hC_Enn, hC_E⟩ := Work.Pert.pert2v2.exists_bound_E_sub_id d hy₁
    set Call : ℝ := max Cu (max Cl Cmid) + C_E + 1 with hCalldef
    -- ## the lower band rectangle (compact, inside `DR ∩ DE`)
    set S₂ : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ -(H + 2) ≤ z.im ∧ z.im ≤ -y₁} with hS₂def
    have hS₂DR : S₂ ⊆ DR := by
      intro z hz
      rw [hS₂def] at hz
      refine hDRsub (Or.inr ?_)
      show y₁ ≤ |z.im|
      calc y₁ ≤ -z.im := by linarith [hz.2.2.2]
        _ ≤ |z.im| := neg_le_abs z.im
    have hS₂DE : S₂ ⊆ d.DE := by
      intro z hz
      rw [hS₂def] at hz
      refine d.ends_sub z ?_
      calc d.η₀ < y₁ := hy₁
        _ ≤ -z.im := by linarith [hz.2.2.2]
        _ ≤ |z.im| := neg_le_abs z.im
    have hS₂cpt : IsCompact S₂ := by
      rw [hS₂def]
      have hcl : IsClosed {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1 ∧ -(H + 2) ≤ z.im ∧ z.im ≤ -y₁} :=
        (isClosed_le continuous_const Complex.continuous_re).inter
          ((isClosed_le Complex.continuous_re continuous_const).inter
            ((isClosed_le continuous_const Complex.continuous_im).inter
              (isClosed_le Complex.continuous_im continuous_const)))
      refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hcl, ?_⟩
      refine (Metric.isBounded_closedBall (x := (0 : ℂ))
        (r := 1 + (H + 2) + |y₁|)).subset ?_
      intro z hz
      obtain ⟨h1, h2, h3, h4⟩ := hz
      rw [Metric.mem_closedBall, dist_zero_right]
      have h6 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      have h7 : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, h2⟩
      have h9 : (0 : ℝ) ≤ H + 2 := by linarith [hAbsy₁H, abs_nonneg y₁]
      have h8 : |z.im| ≤ H + 2 + |y₁| := by
        rw [abs_le]
        exact ⟨by linarith [abs_nonneg y₁, h3, h9], by linarith [neg_le_abs y₁, h4, h9]⟩
      linarith
    obtain ⟨Mcomp₂, hMcomp₂⟩ : ∃ M : ℝ, ∀ z ∈ S₂, ‖R z - d.E z‖ ≤ M := by
      have hcont : ContinuousOn (fun z : ℂ => R z - d.E z) S₂ :=
        ((hRholo.continuousOn.mono hS₂DR).sub (hdEdiff.continuousOn.mono hS₂DE))
      obtain ⟨M, hM⟩ := hS₂cpt.exists_bound_of_continuousOn hcont
      exact ⟨M, fun z hz => by simpa using hM z hz⟩
    -- ## the boundedness of `R - d.E` on the lower half plane
    have hbddLow : ∃ C : ℝ, ∀ w : ℂ, w.im ≤ -y₁ → ‖R w - d.E w‖ ≤ C := by
      refine ⟨max Mcomp₂ Call, fun w hw => ?_⟩
      by_cases hnear : -(H + 2) ≤ w.im
      · -- the compact band, via the integer translate
        set k : ℤ := ⌊w.re⌋ with hkdef
        set z : ℂ := w - (k : ℂ) with hzdef
        have hcast : ((k : ℤ) : ℂ) = ((k : ℝ) : ℂ) := by rw [Complex.ofReal_intCast]
        have hzre : z.re = w.re - (k : ℝ) := by
          rw [hzdef, Complex.sub_re, hcast, Complex.ofReal_re]
        have hzim : z.im = w.im := by
          rw [hzdef, Complex.sub_im, hcast, Complex.ofReal_im]; ring
        have hzS₂ : z ∈ S₂ := by
          rw [hS₂def]
          refine ⟨?_, ?_, ?_, ?_⟩
          · have hfl := Int.floor_le w.re
            rw [hzre]; linarith
          · rw [hzre]; have := Int.lt_floor_add_one w.re; linarith
          · rw [hzim]; exact hnear
          · rw [hzim]; exact hw
        have hzDR : z ∈ DR := hS₂DR hzS₂
        have hzDE : z ∈ d.DE := hS₂DE hzS₂
        have hwz : w = z + (k : ℂ) := by rw [hzdef]; ring
        have h1 : R w = R z + (k : ℂ) := by
          rw [hwz]; exact Work.Pert.pert2v2.TEquivOn_add_int hRequiv k hzDR
        have h2 : d.E w = d.E z + (k : ℂ) := by
          rw [hwz]; exact Work.Pert.pert2v2.E_add_int_DE d hd k z hzDE
        rw [h1, h2, show R z + (k : ℂ) - (d.E z + (k : ℂ)) = R z - d.E z by ring]
        exact le_trans (hMcomp₂ z hzS₂) (le_max_left _ _)
      · -- far below: the chart representative lies in `Uhigh`
        push_neg at hnear
        have hwneg : w.im < 0 := by linarith [hAbsy₁H, abs_nonneg y₁]
        have hwabs : y₁ ≤ |w.im| := by
          rw [abs_of_nonpos (le_of_lt hwneg)]
          linarith [hAbsy₁H]
        have hwDR : w ∈ DR := hDRsub (Or.inr hwabs)
        rw [hDRdef] at hwDR
        simp only [Set.mem_iUnion, Set.mem_image] at hwDR
        obtain ⟨n, z, hzU, hzw⟩ := hwDR
        have hzw' : w = z + (n : ℂ) := hzw.symm
        have hzimw : z.im = w.im := by rw [hzw']; simp
        have hzUhigh : z ∈ Uhigh := by
          rcases hzU with h | h
          · exfalso
            have h' := h
            rw [hUlowdef, Set.mem_setOf_eq] at h'
            have h2 : H + 1 < |z.im| := by
              rw [hzimw, abs_of_nonpos (le_of_lt hwneg)]
              linarith
            linarith [h'.2.1]
          · exact h
        have hzDE : z ∈ d.DE := by
          refine d.ends_sub z ?_
          have h2 : y₁ ≤ |z.im| := by rw [hzimw]; exact hwabs
          exact lt_of_lt_of_le hy₁ h2
        have hzDR : z ∈ DR := by
          rw [hDRdef]
          exact Set.mem_iUnion.mpr ⟨0, z, hzU, by simp⟩
        have h1 : R w = R z + (n : ℂ) := by
          rw [hzw']; exact Work.Pert.pert2v2.TEquivOn_add_int hRequiv n hzDR
        have h2 : d.E w = d.E z + (n : ℂ) := by
          rw [hzw']; exact Work.Pert.pert2v2.E_add_int_DE d hd n z hzDE
        have hzEst : ‖R z - d.E z‖ ≤ Call := by
          obtain ⟨ς, hςM, hςΦ⟩ : ∃ ς ∈ Mset, ΨE ς = z := by
            have h := hzUhigh
            rw [hUhighdef, Set.mem_setOf_eq] at h
            exact h.2.2
          have hςQm : ς ∈ Qm Ξabs α := (hMsub hςM).1
          have hςwa : |ς.re| + 2 < |ς.im| - Ξabs := by
            have h := hςM
            rw [hMsetdef, Set.mem_setOf_eq] at h
            linarith
          have hinv : Work.Pert.invOn ΨE (Qm Ξabs α) z = ς :=
            Work.Pert.invOn_eq hΨE.2.1 ⟨ς, hςQm, hςΦ⟩ hςQm hςΦ
          have hRz : R z = ΨE (Work.Pert.Tt α ς) := by
            rw [hRhighEq z hzUhigh, hRhigh_eq_ret z hzUhigh, Work.Pert.retOf, hinv]
          have hbound : ‖ΨE (Work.Pert.Tt α ς) - ΨE ς‖ ≤ max Cu (max Cl Cmid) := by
            by_cases hb1 : Ku ≤ ς.im
            · exact le_trans (hCu ς hςwa hb1) (le_max_left _ _)
            · push_neg at hb1
              by_cases hb2 : ς.im ≤ -Kl
              · exact le_trans (hCl ς hςwa hb2)
                  (le_trans (le_max_left _ _) (le_max_right _ _))
              · push_neg at hb2
                refine le_trans (hCmid ς ?_) (le_trans (le_max_right _ _) (le_max_right _ _))
                rw [hT₂def]
                exact ⟨le_of_lt hςwa,
                  abs_le.mpr ⟨by linarith [le_max_right Ku Kl], by linarith [le_max_left Ku Kl]⟩⟩
          have hCz : ‖d.E z - z‖ ≤ C_E := hC_E z (by rw [hzimw]; exact hwabs)
          have hkey : R z - d.E z = (ΨE (Work.Pert.Tt α ς) - ΨE ς) - (d.E z - z) := by
            rw [hRz, hςΦ]; ring
          rw [hkey]
          calc ‖(ΨE (Work.Pert.Tt α ς) - ΨE ς) - (d.E z - z)‖
              ≤ ‖ΨE (Work.Pert.Tt α ς) - ΨE ς‖ + ‖d.E z - z‖ := norm_sub_le _ _
            _ ≤ max Cu (max Cl Cmid) + C_E := add_le_add hbound hCz
            _ ≤ Call := by rw [hCalldef]; linarith [norm_nonneg (1 / α)]
        rw [h1, h2, show R z + (n : ℂ) - (d.E z + (n : ℂ)) = R z - d.E z by ring]
        exact le_trans hzEst (le_max_right _ _)
    -- ## the Phragmén–Lindelöf on the lower half plane
    refine Work.Pert.pert2v2.lower_end_close_of_line (R := R) (E := d.E) (a := 1 / α) ?_ ?_ ?_ ?_
      hbddLow hlineDn
    · intro w hw
      exact hRholo.differentiableAt (hDRopen.mem_nhds (hDRsub (Or.inr
        (le_trans (by linarith [hw] : y₁ ≤ -w.im) (neg_le_abs w.im)))))
    · intro w hw
      exact hdEdiff.differentiableAt (hdDEopen.mem_nhds (d.ends_sub w
        (lt_of_lt_of_le hy₁ (le_trans (by linarith [hw] : y₁ ≤ -w.im) (neg_le_abs w.im)))))
    · intro w hw
      have hDR : w ∈ DR := hDRsub (Or.inr (le_trans (by linarith [hw] : y₁ ≤ -w.im)
        (neg_le_abs w.im)))
      have h := Work.Pert.pert2v2.TEquivOn_add_int hRequiv (1 : ℤ) hDR
      simpa using h
    · intro w hw
      have hDE : w ∈ d.DE := d.ends_sub w (lt_of_lt_of_le hy₁
        (le_trans (by linarith [hw] : y₁ ≤ -w.im) (neg_le_abs w.im)))
      have h := Work.Pert.pert2v2.E_add_int_DE d hd (1 : ℤ) w hDE
      simpa using h
  have hRclose : ∀ w ∈ K ∪ {w : ℂ | y₁ ≤ |w.im|},
      ‖R w + 1 / MandelDim.rotOf f - d.E w‖ < δ := by
    rw [← hαdef]
    intro w hw
    rcases hw with hwK | hwB
    · by_cases hb : y₁ ≤ |w.im|
      · by_cases h : y₁ ≤ w.im
        · exact hRcloseUp w h
        · push_neg at h
          exact hRcloseDn w (by
            by_cases hpos : 0 ≤ w.im
            · have h' : y₁ ≤ |w.im| := hb
              rw [abs_of_nonneg hpos] at h'
              linarith
            · have h' : y₁ ≤ |w.im| := hb
              rw [abs_of_nonpos (le_of_lt (not_le.mp hpos))] at h'
              linarith)
      · -- a point of `K` of small height: its reduction blob lies in the low chart
        push_neg at hb
        obtain ⟨z, hzZ, n, hn⟩ := hZred w hwK
        have hzre : |z.re| < 1 := lt_of_le_of_lt (hZwin z hzZ) (by norm_num)
        have hzim : |z.im| = |w.im| := by rw [hn]; simp
        have hzUlow : z ∈ Ulow := hKb_window z (Or.inl hzZ) hzre (by rw [hzim]; linarith [hy₁H])
        have hzDE : z ∈ d.DE := by
          have h' := hzUlow
          rw [hUlowdef, Set.mem_setOf_eq] at h'
          exact h'.2.2.1
        have hzDR : z ∈ DR := by
          rw [hDRdef]
          exact Set.mem_iUnion.mpr ⟨0, z, Or.inl hzUlow, by simp⟩
        have h1 : R w = R z + (n : ℂ) := by
          rw [hn]; exact Work.Pert.pert2v2.TEquivOn_add_int hRequiv n hzDR
        have h2 : d.E w = d.E z + (n : ℂ) := by
          rw [hn]; exact Work.Pert.pert2v2.E_add_int_DE d hd n z hzDE
        have h3 : ‖Rlow z + 1 / α - d.E z‖ < δ := hEstLow z hzUlow
        have h4 : R z = Rlow z := hRlowEq z hzUlow
        rw [h1, h2, show R z + (n : ℂ) + 1 / α - (d.E z + (n : ℂ)) = R z + 1 / α - d.E z by ring,
          h4]
        exact h3
    · by_cases h : y₁ ≤ w.im
      · exact hRcloseUp w h
      · push_neg at h
        exact hRcloseDn w (by
          by_cases hpos : 0 ≤ w.im
          · have h' : y₁ ≤ |w.im| := hwB
            rw [abs_of_nonneg hpos] at h'
            linarith
          · have h' : y₁ ≤ |w.im| := hwB
            rw [abs_of_nonpos (le_of_lt (not_le.mp hpos))] at h'
            linarith)
  have hRupper : Filter.Tendsto (fun w => R w - w + 1 / MandelDim.rotOf f) MandelDim.upperEnd
      (nhds 0) := by
    rw [← hαdef]
    refine Work.Pert.pert2v2.R_upper_twoPiece hRequiv ?_ (fun w hw => hRhighEq w hw) ?_ ?_
    · -- the high chart lies in `DR`
      intro w hw
      rw [hDRdef]
      exact Set.mem_iUnion.mpr ⟨0, w, Or.inr hw, by simp⟩
    · -- every point high up is an integer translate of a high-chart point
      refine ⟨H + 1, fun w hw => ⟨⌊w.re⌋, ?_⟩⟩
      set z : ℂ := w - ((⌊w.re⌋ : ℤ) : ℂ) with hzdef
      have hcast : (((⌊w.re⌋ : ℤ)) : ℂ) = (((⌊w.re⌋ : ℝ)) : ℂ) := by
        rw [Complex.ofReal_intCast]
      have hzre : z.re = w.re - (⌊w.re⌋ : ℝ) := by
        rw [hzdef, Complex.sub_re, hcast, Complex.ofReal_re]
      have hzim : z.im = w.im := by
        rw [hzdef, Complex.sub_im, hcast, Complex.ofReal_im]; ring
      have hfl : (⌊w.re⌋ : ℝ) ≤ w.re := Int.floor_le w.re
      have hfu : w.re < (⌊w.re⌋ : ℝ) + 1 := Int.lt_floor_add_one w.re
      have hzre' : |z.re| < 1 := by
        rw [hzre, abs_lt]
        exact ⟨by linarith, by linarith⟩
      have hzH : H < |z.im| := by rw [hzim]; linarith [le_abs_self w.im]
      exact hTall z hzre' hzH
    · -- the high piece is a near-translation at the upper end
      intro ε hε
      obtain ⟨Y1, hY1⟩ := hEndmS (ε / 2) (by linarith)
      have hDnn : (0 : ℝ) ≤ C + |(1 / α).im| + 1 := by
        have h1 : (0 : ℝ) ≤ |(1 / α).im| := abs_nonneg _
        linarith
      refine ⟨max (Yc + (C + |(1 / α).im| + 1)) (Y1 + (C + |(1 / α).im| + 1)),
        fun w hwU hw => ?_⟩
      have hYcW : Yc ≤ w.im := by
        have h := le_trans (le_max_left _ _) (le_of_lt hw)
        linarith
      have hY1W : Y1 + (C + |(1 / α).im| + 1) ≤ w.im :=
        le_trans (le_max_right _ _) (le_of_lt hw)
      obtain ⟨ς₀, hς₀M, hς₀Φ⟩ : ∃ ς ∈ Mset, ΨE ς = w := by
        have h := hwU
        rw [hUhighdef, Set.mem_setOf_eq] at h
        exact h.2.2
      have hς₀Qm : ς₀ ∈ Qm Ξabs α := (hMsub hς₀M).1
      have hς₀Qp : ς₀ ∈ Qp Ξabs α := (hMsub hς₀M).2
      have hwre : |w.re| < 1 := by
        have h := hwU
        rw [hUhighdef, Set.mem_setOf_eq] at h
        exact h.1
      have hmemImg : w ∈ ΨE '' (Qm Ξabs α) := ⟨ς₀, hς₀Qm, hς₀Φ⟩
      have hinv : Work.Pert.invOn ΨE (Qm Ξabs α) w = ς₀ :=
        Work.Pert.invOn_eq hΨE.2.1 hmemImg hς₀Qm hς₀Φ
      have hpr := hpre w (by linarith) hwre hmemImg
      have hς₀im : Y1 + |(1 / α).im| < ς₀.im := by
        have h := hpr.2
        rw [hinv] at h
        linarith
      have hς₀reB : |ς₀.re| ≤ B := by
        have h := hpr.1
        rw [hinv] at h
        exact h
      have hς₀re : |ς₀.re| ≤ Bst := by
        have h2 : B ≤ Bst := by rw [hBstdef]; linarith [abs_nonneg ((1 / α).re)]
        linarith
      have hTtQ : Work.Pert.Tt α ς₀ ∈ Qm Ξabs α :=
        Work.Pert.Tt_mem_Qm_iff.mpr hς₀Qp
      have hTtim : (Work.Pert.Tt α ς₀).im = ς₀.im - (1 / α).im := by
        rw [Work.Pert.Tt]; simp
      have hTtim' : Y1 < (Work.Pert.Tt α ς₀).im := by
        rw [hTtim]; linarith [le_abs_self ((1 / α).im)]
      have hTtre : |(Work.Pert.Tt α ς₀).re| ≤ Bst := by
        have h1 : (Work.Pert.Tt α ς₀).re = ς₀.re - (1 / α).re := by
          rw [Work.Pert.Tt]; simp
        rw [h1]
        have h2 : |ς₀.re - (1 / α).re| ≤ |ς₀.re| + |(1 / α).re| := by
          rw [abs_le]
          constructor <;> linarith [neg_abs_le ς₀.re, le_abs_self ς₀.re,
            neg_abs_le ((1 / α).re), le_abs_self ((1 / α).re)]
        have h3 : Bst = B + |(1 / α).re| + 2 := hBstdef
        linarith
      have hkey : ‖ΨE (Work.Pert.Tt α ς₀) - ΨE ς₀ + 1 / α‖ < ε := by
        have hA1 : ‖ΨE (Work.Pert.Tt α ς₀) - (Work.Pert.Tt α ς₀) - cm‖ < ε / 2 :=
          hY1 _ hTtQ hTtim' hTtre
        have hA0 : ‖ΨE ς₀ - ς₀ - cm‖ < ε / 2 :=
          hY1 _ hς₀Qm (by have := abs_nonneg ((1 / α).im); linarith) hς₀re
        have heq : ΨE (Work.Pert.Tt α ς₀) - ΨE ς₀ + 1 / α
            = (ΨE (Work.Pert.Tt α ς₀) - (Work.Pert.Tt α ς₀) - cm) - (ΨE ς₀ - ς₀ - cm) := by
          rw [Work.Pert.Tt]; ring
        rw [heq]
        exact lt_of_le_of_lt (norm_sub_le _ _) (by linarith)
      rw [hRhigh_eq_ret w hwU, Work.Pert.retOf, hinv, ← hς₀Φ]
      exact hkey
  -- ## S16. the orbit relation, on the RESTRICTED domains
  --   `Dφ' := Dφ ∩ {|Re| < A/4}`,  `DR' := DR ∩ {‖R y + 1/α - y‖ < CE'}`  (`A = Re (1/α) ≥ 4 Nreq`).
  -- Every other `PertData` field restricts (`Dsm ±η`, the strip and `K'` lie in `|Re| < A/4`;
  -- `K ∪ {y₁ ≤ |Im|} ⊆ DR'` by `R_close` and the datum bounds of `d.E - id`).  On the restricted
  -- domains the orbit is chart-decomposed (`LeadWire.orbit_chart_decomp_orb`) with the per-step
  -- drop `≥ A - CE'` and the target bound `Re w' > -A/4`, and `orbit_row_mem` gives the value; the
  -- starting point is reduced into the chart by an integer translate `k₀`, `|k₀| < A/4 + 1`
  -- (`DphiP_segment` + the Abel relation).  NOTE: with the UNRESTRICTED `Dφ = DphiP … (Qm Ξabs α)`
  -- the left bound `x₀ - A + Bl ≤ Re w'` that `orbit_chart_decomp` assumes on all of `Dφ` is false
  -- (the gate contains points of arbitrarily negative real part at large `|Im|`).
  have hA4 : Nreq ≤ (1 / α).re / 4 := by linarith only [hAre]
  have hCE'0 : 0 < CE' := by
    rw [hCE'def]; have : 0 ≤ max CKE0 0 := le_max_right _ _
    linarith only [this, hδ, hC_Eonn]
  have hNge : CE' + |η| + |CK'| + (Mn : ℝ) + 16 ≤ Nreq := by
    rw [hNreqdef]
    have h1 : (0 : ℝ) ≤ Ξsh := le_trans hΞabspos0.le hΞabsΞsh
    have h2 : (0 : ℝ) ≤ (Mn : ℝ) := Nat.cast_nonneg _
    linarith only [h1, h2, hCE'0, hH64]
  -- the restricted coordinate domain
  set Dφ' : Set ℂ := Dφ ∩ {z : ℂ | |z.re| < (1 / α).re / 4} with hDφ'def
  have hDφ'open : IsOpen Dφ' :=
    hDφopen.inter (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const)
  have hφholo' : DifferentiableOn ℂ φ Dφ' := hφholo.mono Set.inter_subset_left
  have hφabel' : ∀ w ∈ Dφ', w + 1 ∈ Dφ' → φ w ∈ Df ∧ φ (w + 1) = f (φ w) :=
    fun w hw hw1 => hφabel w hw.1 hw1.1
  have hDsub' : MandelDim.Dsm η ∪ MandelDim.Dsm (-η) ⊆ Dφ' := by
    intro z hz
    refine ⟨hDsub hz, ?_⟩
    show |z.re| < (1 / α).re / 4
    have hb : |z.re| ≤ |η| := by
      rcases hz with hz | hz
      · have h1 : ‖z - Complex.I * η‖ ≤ |η| / 4 := by
          rw [MandelDim.Dsm, Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
        have h2 := Complex.abs_re_le_norm (z - Complex.I * η)
        have h3 : (z - Complex.I * η).re = z.re := by simp
        rw [h3] at h2
        linarith only [h1, h2, abs_nonneg η]
      · have h1 : ‖z - Complex.I * ((-η : ℝ) : ℂ)‖ ≤ |-η| / 4 := by
          rw [MandelDim.Dsm, Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
        have h2 := Complex.abs_re_le_norm (z - Complex.I * ((-η : ℝ) : ℂ))
        have h3 : (z - Complex.I * ((-η : ℝ) : ℂ)).re = z.re := by simp
        rw [h3] at h2
        rw [abs_neg] at h1
        linarith only [h1, h2, abs_nonneg η]
    linarith only [hb, hNge, hA4, hCE'0, abs_nonneg CK', hMn0]
  have hstrip'' : ∀ w : ℂ, y₁ ≤ |w.im| → |w.re| ≤ 1 → w ∈ Dφ' := by
    intro w hw1 hw2
    refine ⟨hstrip' w hw1 hw2, ?_⟩
    show |w.re| < (1 / α).re / 4
    linarith only [hw2, hNge, hA4, hCE'0, abs_nonneg η, abs_nonneg CK', hMn0]
  have hK'Dφ'' : K' ⊆ Dφ' := by
    intro w hw
    refine ⟨hK'Dφ hw, ?_⟩
    show |w.re| < (1 / α).re / 4
    have h1 := Complex.abs_re_le_norm w
    have h2 := hCK' w hw
    linarith only [h1, h2, le_abs_self CK', hNge, hA4, hCE'0, abs_nonneg η, hMn0]
  -- the restricted return-map domain
  have hRcont : ContinuousOn (fun y : ℂ => ‖R y + 1 / α - y‖) DR :=
    ((hRholo.continuousOn.add continuousOn_const).sub continuousOn_id).norm
  set DR' : Set ℂ := DR ∩ {y : ℂ | ‖R y + 1 / α - y‖ < CE'} with hDR'def
  have hDR'open : IsOpen DR' := hRcont.isOpen_inter_preimage hDRopen isOpen_Iio
  have hshiftR : ∀ y ∈ DR, ‖R (y + 1) + 1 / α - (y + 1)‖ = ‖R y + 1 / α - y‖ := by
    intro y hy
    rw [hRequiv.2 y hy]; congr 1; ring
  have hRequiv' : MandelDim.IsTEquivariantOn R DR' := by
    refine ⟨fun y => ⟨fun hy => ⟨(hRequiv.1 y).mp hy.1, ?_⟩, fun hy => ⟨(hRequiv.1 y).mpr hy.1, ?_⟩⟩,
      fun y hy => hRequiv.2 y hy.1⟩
    · show ‖R (y + 1) + 1 / α - (y + 1)‖ < CE'
      rw [hshiftR y hy.1]; exact hy.2
    · show ‖R y + 1 / α - y‖ < CE'
      have h := hy.2
      have hyDR : y ∈ DR := (hRequiv.1 y).mpr hy.1
      change ‖R (y + 1) + 1 / α - (y + 1)‖ < CE' at h
      rwa [hshiftR y hyDR] at h
  have hRholo' : DifferentiableOn ℂ R DR' := hRholo.mono Set.inter_subset_left
  have hDRsub' : K ∪ {w : ℂ | y₁ ≤ |w.im|} ⊆ DR' := by
    intro w hw
    refine ⟨hDRsub hw, ?_⟩
    show ‖R w + 1 / α - w‖ < CE'
    have h1 : ‖R w + 1 / α - d.E w‖ < δ := by
      have := hRclose w hw
      rw [← hαdef] at this
      exact this
    have h2 : ‖d.E w - w‖ ≤ C_Eo + max CKE0 0 := by
      rcases hw with hwK | hwB
      · have : ‖d.E w - w‖ ≤ CKE0 := by simpa using hCKE0 w hwK
        linarith only [this, le_max_left CKE0 0, hC_Eonn]
      · have := hC_Eo w hwB
        linarith only [this, le_max_right CKE0 0]
    have h3 : R w + 1 / α - w = (R w + 1 / α - d.E w) + (d.E w - w) := by ring
    rw [h3]
    calc ‖(R w + 1 / α - d.E w) + (d.E w - w)‖ ≤ ‖R w + 1 / α - d.E w‖ + ‖d.E w - w‖ :=
          norm_add_le _ _
      _ < δ + (C_Eo + max CKE0 0) := add_lt_add_of_lt_of_le h1 h2
      _ < CE' := by rw [hCE'def]; linarith
  -- the gate facts used by the pieces
  have hτDf : ∀ z ∈ Qm Ξabs α, tauC σ α z ∈ Df := fun z hz =>
    hNear.2.1 (hballL (Metric.ball_subset_closedBall (hτQ_abs z hz)))
  have hUlowDφ : Ulow ⊆ Dφ := by
    intro y hy
    rw [hUlowdef, Set.mem_setOf_eq] at hy
    exact hy.2.2.2.1
  have hUhighDφ : Uhigh ⊆ Dφ := by
    intro y hy
    rw [hUhighdef, Set.mem_setOf_eq] at hy
    obtain ⟨ς, hςM, hςΦ⟩ := hy.2.2
    rw [hDφdef, ← hςΦ]
    exact Work.Pert.mem_DphiP_of_mem_image (hMsub hςM).1
  have hchartDR : ∀ y ∈ Ulow ∪ Uhigh, y ∈ DR := by
    intro y hy
    rw [hDRdef]
    exact Set.mem_iUnion.mpr ⟨0, y, hy, by simp⟩
  -- the two pieces as one Bool-indexed family
  set P : Bool → ℂ → ℂ := fun b y => cond b (Rlow y) (Rhigh y) with hPdef
  have hpiece : ∀ (b : Bool) (y : ℂ), (b = true → y ∈ Ulow) → (b = false → y ∈ Uhigh) →
      ∀ l : ℕ, (b = true → m_x ≤ l) → P b y + (l : ℂ) ∈ Dφ →
        φ (P b y + (l : ℂ)) = f^[l] (φ y) ∧ ∀ i : ℕ, i < l → f^[i] (φ y) ∈ Df := by
    intro b y hbL hbH l hl hmemD
    cases b with
    | true =>
      have hy : y ∈ Ulow := hbL rfl
      have hml : m_x ≤ l := hl rfl
      have hmemD' : Rlow y + (l : ℂ) ∈ Dφ := hmemD
      have hyU := hy
      rw [hUlowdef, Set.mem_setOf_eq, Work.Pert.pert2v2.LowClause] at hyU
      obtain ⟨-, -, -, -, ⟨hwalkL, hland, -⟩, -⟩ := hyU
      have hζQp' : Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ y)) ∈ Qp' := Work.Pert.invOn_mem hland
      have hζτ : tauC σ α (Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ y))) = f^[m_x] (φ y) :=
        Work.Pert.invOn_spec hland
      have hTtζ : Work.Pert.Tt α (Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ y))) ∈ Qm Ξabs α :=
        Work.Pert.Tt_mem_Qm_iff.mpr (hQp'sub_abs hζQp')
      have hlc : ((m_x + (l - m_x) : ℕ) : ℂ) = (l : ℂ) := by
        rw [Nat.add_sub_cancel' hml]
      have hDφR : Work.Pert.pert2v2.RlowPiece f Qp' (tauC σ α) Φp φ m_x dlow y
          + ((m_x + (l - m_x) : ℕ) : ℂ) ∈ Work.Pert.DphiP f Df (tauC σ α) ΨE (Qm Ξabs α) := by
        rw [hlc]; exact hmemD'
      have hval := Work.Pert.pert2v2.Rlow_phi_add_nat (f := f) (F := liftF u σ α) (τ := tauC σ α)
        (Φ := ΨE) (Φp := Φp) (φ := φ) (Df := Df) (Q := Qm Ξabs α) (Qp' := Qp') (α := α)
        (d := dlow) (m := m_x) (c := l - m_x) (w := y) hτF hOrb
        (fun z hz => hdlow z (hQp'sub hz)) hland hTtζ hτTt hDφR
      rw [hlc, Nat.add_sub_cancel' hml] at hval
      refine ⟨hval, ?_⟩
      have hΦu : ΨE (Work.Pert.Tt α (Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ y))))
          = (Rlow y + (l : ℂ)) - ((l - m_x : ℕ) : ℂ) := by
        rw [hdlow _ (hQp'sub hζQp'), hRlowdef]
        simp only [Work.Pert.pert2v2.RlowPiece, Work.Pert.Rlow]
        rw [Nat.cast_sub hml]; push_cast; ring
      exact Work.Pert.pert2v2.orbit_mem_low (f := f) (F := liftF u σ α) (τ := tauC σ α)
        (Φ := ΨE) (Df := Df) (Q := Qm Ξabs α) (u := Work.Pert.Tt α
          (Work.Pert.invOn (tauC σ α) Qp' (f^[m_x] (φ y)))) (w := y) (w' := Rlow y + (l : ℂ))
        (m := m_x) (n := l) hτF hτDf hOrb hTtζ hΦu hmemD' (by rw [hτTt]; exact hζτ) hml hwalkL
    | false =>
      have hy : y ∈ Uhigh := hbH rfl
      have hmemD' : Rhigh y + (l : ℂ) ∈ Dφ := hmemD
      have hyU := hy
      rw [hUhighdef, Set.mem_setOf_eq] at hyU
      obtain ⟨ς, hςM, hςΦ⟩ := hyU.2.2
      have hςQ := hMsub hςM
      have hinvς : Work.Pert.invOn ΨE (Qm Ξabs α) y = ς :=
        Work.Pert.invOn_eq hΨE.2.1 ⟨ς, hςQ.1, hςΦ⟩ hςQ.1 hςΦ
      have hTtς : Work.Pert.Tt α ς ∈ Qm Ξabs α := Work.Pert.Tt_mem_Qm_iff.mpr hςQ.2
      have hRy : Rhigh y = ΨE (Work.Pert.Tt α ς) := by
        rw [hRhigh_eq_ret y hy, Work.Pert.retOf, hinvς]
      have hφy : φ y = tauC σ α ς := by
        rw [hφdef, ← hςΦ, Work.Pert.coordP_eq_tauC_of_mem_image (Q := Qm Ξabs α) hΨE.2.1
          ⟨ς, hςQ.1, rfl⟩, Work.Pert.invOn_eq (Q := Qm Ξabs α) hΨE.2.1 ⟨ς, hςQ.1, rfl⟩ hςQ.1 rfl]
      have hRyD : Rhigh y ∈ Dφ := by
        rw [hRy, hDφdef]; exact Work.Pert.mem_DphiP_of_mem_image hTtς
      have hray : ∀ i : ℕ, i ≤ l → Rhigh y + (i : ℂ) ∈ Dφ := by
        have := Work.Pert.pert2v2.DphiP_segment (f := f) (F := liftF u σ α) (τ := tauC σ α)
          (Φ := ΨE) (Df := Df) (Q := Qm Ξabs α) hΨE.2.1 hAbel hτF hτDf hOrb
          (z := Rhigh y) (k := l) hRyD hmemD'
        exact this
      have hgood : Work.Pert.GoodP f Df (tauC σ α) ΨE (Qm Ξabs α ∩ Qp Ξabs α) y :=
        Work.Pert.goodP_of_mem_image ⟨ς, hςQ, hςΦ⟩
      have hval := Work.Pert.pert2v2.retP_phi_shift (f := f) (F := liftF u σ α) (τ := tauC σ α)
        (Φ := ΨE) (Ξ := Ξabs) (α := α) (Df := Df) (w := y) (t := l) hΨE.2.1 hAbel hτF hOrb hτTt
        hgood hray
      refine ⟨hval, ?_⟩
      have hmem := Work.Pert.pert2v2.orbit_mem_of_level (f := f) (F := liftF u σ α)
        (τ := tauC σ α) (Φ := ΨE) (Df := Df) (Q := Qm Ξabs α) (u := Work.Pert.Tt α ς)
        (w' := Rhigh y + (l : ℂ)) (N := l) hτF hτDf hOrb hTtς (by rw [← hRy]; ring) hmemD'
      intro i hi
      rw [hφy, ← hτTt ς]
      exact hmem i hi
  -- the orbit relation itself
  have horbit : ∀ w ∈ Dφ', ∀ w' ∈ Dφ', ∀ m : ℕ, 1 ≤ m → (∀ j < m, R^[j] w ∈ DR') →
      MandelDim.piExp (R^[m] w) = MandelDim.piExp w' →
      |Complex.arg (w' + 1 / (2 * MandelDim.rotOf f) - w)| < 2 * Real.pi / 3 →
      ∃ n : ℕ, 1 ≤ n ∧ f^[n] (φ w) = φ w' ∧ ∀ i < n, f^[i] (φ w) ∈ Df := by
    intro w hw w' hw' m hm hiter hpi _
    have hw2 : w ∈ Dφ ∧ |w.re| < (1 / α).re / 4 := hw
    have hw'2 : w' ∈ Dφ ∧ |w'.re| < (1 / α).re / 4 := hw'
    have hiterDR : ∀ j < m, R^[j] w ∈ DR := fun j hj => (hiter j hj).1
    have hiterC : ∀ j < m, ‖R (R^[j] w) + 1 / α - R^[j] w‖ < CE' := fun j hj => (hiter j hj).2
    -- the chart representative of the starting point
    have hw0DR : w ∈ DR := by simpa using hiterDR 0 (by omega)
    have hw0DR' := hw0DR
    rw [hDRdef, Set.mem_iUnion] at hw0DR'
    obtain ⟨k₀, x₀, hx₀, hx₀w0⟩ := hw0DR'
    have hx₀w : x₀ + (k₀ : ℂ) = w := hx₀w0
    have hx₀eq : x₀ = w - (k₀ : ℂ) := by rw [← hx₀w]; ring
    have hRn : ∀ (n : ℤ) (u : ℂ), u ∈ DR → R (u + (n : ℂ)) = R u + (n : ℂ) :=
      fun n u hu => Work.Pert.pert2v2.TEquivOn_add_int hRequiv n hu
    have hx₀iter : ∀ j, j ≤ m → R^[j] x₀ = R^[j] w - (k₀ : ℂ) := by
      rw [hx₀eq]; exact Work.Pert.pert2v2.LeadWire.iterate_sub_int hRequiv hRn hiterDR k₀
    have hx₀DR : ∀ j < m, R^[j] x₀ ∈ DR := by
      intro j hj
      rw [hx₀iter j hj.le]
      have := Work.Pert.pert2v2.LeadWire.mem_add_int_of_TInv hRequiv.1 (hiterDR j hj) (-k₀)
      have e : R^[j] w - (k₀ : ℂ) = R^[j] w + ((-k₀ : ℤ) : ℂ) := by push_cast; ring
      rw [e]; exact this
    have hstepOrb : ∀ j < m, (R^[j+1] x₀).re ≤ (R^[j] x₀).re - (1 / α).re + CE' := by
      intro j hj
      rw [hx₀iter (j+1) hj, hx₀iter j hj.le, Function.iterate_succ_apply']
      have h1 := hiterC j hj
      have h2 := Complex.abs_re_le_norm (R (R^[j] w) + 1 / α - R^[j] w)
      have h3 : (R (R^[j] w) + 1 / α - R^[j] w).re = (R (R^[j] w)).re + (1 / α).re - (R^[j] w).re := by
        simp
      have h4 : (R (R^[j] w) - (k₀ : ℂ)).re = (R (R^[j] w)).re - (k₀ : ℝ) := by simp
      have h5 : (R^[j] w - (k₀ : ℂ)).re = (R^[j] w).re - (k₀ : ℝ) := by simp
      rw [h4, h5]
      rw [h3] at h2
      linarith only [h1, h2, le_abs_self ((R (R^[j] w)).re + (1 / α).re - (R^[j] w).re)]
    have hpi' : MandelDim.piExp (R^[m] x₀) = MandelDim.piExp w' := by
      rw [hx₀iter m le_rfl, Work.Pert.pert2v2.LeadWire.piExp_sub_int]; exact hpi
    have hwin' : Ulow ∪ Uhigh ⊆ {z : ℂ | |z.re - 0| < 1} := by
      intro z hz
      rcases hz with hz | hz
      · exact (hwinLow hz).1
      · exact (hwinHigh hz).1
    have hmMnR' : (m_x : ℝ) ≤ (Mn : ℝ) := by
      have h1 : (m_x : ℝ) ≤ Mbd := hmbound
      have h2 : Mbd ≤ (⌈Mbd⌉₊ : ℝ) := Nat.le_ceil Mbd
      linarith
    have hAcond : (m_x : ℝ) + CE' + 4 ≤ (1 / α).re := by
      linarith only [hmMnR', hNge, hA4, abs_nonneg η, abs_nonneg CK', hCE'0]
    have hBlcond : (m_x : ℝ) + CE' + 2 ≤ 3 * (1 / α).re / 4 := by
      linarith only [hmMnR', hNge, hA4, abs_nonneg η, abs_nonneg CK', hCE'0]
    have hw'left : 0 - (1 / α).re + 3 * (1 / α).re / 4 ≤ w'.re := by
      have := (abs_lt.mp hw'2.2).1
      linarith only [this]
    obtain ⟨n', x, k, b, hw'eq, hk0, hdec, hside, hanti, hneg, hlvl, hnmono, hmemlast, hnbig⟩ :=
      Work.Pert.pert2v2.LeadWire.orbit_chart_decomp_orb (R := R) (DR := DR) (Ulow := Ulow)
        (Uhigh := Uhigh) (α := α) (w := x₀) (w' := w') (m := m) (m₀ := m_x) (x₀ := 0) (R1 := 1)
        (e := CE') (Bl := 3 * (1 / α).re / 4) hDRdef hwin' le_rfl hstepOrb hAcond hBlcond
        hw'left hm hx₀ hx₀DR hpi'
    -- the piece relation along the chart decomposition
    have hR : ∀ j < m, R (R^[j] x₀) = P (b j) (x j) + (k j : ℂ) := by
      intro j hj
      have hxj := hside j hj
      have hxjDR : x j ∈ DR := by
        by_cases hb : b j = true
        · exact hchartDR _ (Or.inl (hxj.1 hb))
        · exact hchartDR _ (Or.inr (hxj.2 (by simpa using hb)))
      rw [hdec j hj, hRn (k j) (x j) hxjDR]
      congr 1
      cases hbj : b j with
      | true => exact hRlowEq _ (hxj.1 hbj)
      | false => exact hRhighEq _ (hxj.2 hbj)
    have hmem1 : ∀ j, j + 1 < m → x (j+1) ∈ Dφ := by
      intro j hj
      have hxj := hside (j+1) hj
      by_cases hb : b (j+1) = true
      · exact hUlowDφ (hxj.1 hb)
      · exact hUhighDφ (hxj.2 (by simpa using hb))
    obtain ⟨hvalx, hmemx⟩ := Work.Pert.pert2v2.orbit_row_mem (f := f) (φ := φ) (R := R)
      (Df := Df) (Dφ := Dφ) (P := P) (Ulow := Ulow) (Uhigh := Uhigh) (m₀ := m_x) (m := m)
      (n := n') (w := x₀) (w' := w') hφabel hpiece hUlowDφ hUhighDφ hm hk0 hdec hside hR hanti
      hneg hmem1 hw'eq hw'2.1 hlvl hnmono hmemlast
    -- the integer reduction `w = x₀ + k₀`
    have hx₀Dφ : x₀ ∈ Dφ := by
      rcases hx₀ with h | h
      · exact hUlowDφ h
      · exact hUhighDφ h
    have hx₀re : |x₀.re| < 1 := by have := hwin' hx₀; simpa using this
    have hk₀re : (k₀ : ℝ) = w.re - x₀.re := by
      have := congrArg Complex.re hx₀w
      simp at this; linarith
    have hk₀b : |(k₀ : ℝ)| < (1 / α).re / 4 + 1 := by
      have h1 := abs_lt.mp hw2.2
      have h2 := abs_lt.mp hx₀re
      rw [hk₀re]
      exact abs_lt.mpr ⟨by linarith only [h1.1, h2.2], by linarith only [h1.2, h2.1]⟩
    have hseg : ∀ (z : ℂ) (k : ℕ), z ∈ Dφ → z + (k : ℂ) ∈ Dφ →
        ∀ i : ℕ, i ≤ k → z + (i : ℂ) ∈ Dφ := fun z k hz hzk =>
      Work.Pert.pert2v2.DphiP_segment (f := f) (F := liftF u σ α) (τ := tauC σ α)
        (Φ := ΨE) (Df := Df) (Q := Qm Ξabs α) hΨE.2.1 hAbel hτF hτDf hOrb hz hzk
    rcases le_or_gt 0 k₀ with hk | hk
    · -- `w = x₀ + s`, `s = k₀ ≥ 0`
      set s : ℕ := k₀.toNat with hsdef
      have hs : ((s : ℕ) : ℤ) = k₀ := Int.toNat_of_nonneg hk
      have hsC : ((s : ℕ) : ℂ) = (k₀ : ℂ) := by exact_mod_cast hs
      have hwx : w = x₀ + (s : ℂ) := by rw [hsC, ← hx₀w]
      have hray : ∀ i : ℕ, i ≤ s → (w - (s : ℂ)) + (i : ℂ) ∈ Dφ := by
        have h1 : w - (s : ℂ) = x₀ := by rw [hwx]; ring
        rw [h1]
        exact hseg x₀ s hx₀Dφ (by rw [← hwx]; exact hw2.1)
      have hφw : φ w = f^[s] (φ x₀) := by
        have := Work.Pert.pert2v2.phi_left_reduce (f := f) (φ := φ) (Dφ := Dφ) (Df := Df)
          (w := w) (s := s) hφabel hray
        rwa [show w - (s : ℂ) = x₀ by rw [hwx]; ring] at this
      have hsR : (s : ℝ) < (1 / α).re / 4 + 1 := by
        have : (s : ℝ) = (k₀ : ℝ) := by exact_mod_cast hs
        rw [this]; linarith only [hk₀b, le_abs_self (k₀ : ℝ)]
      have hn'big : (s : ℝ) + 1 < (n' : ℝ) := by
        linarith only [hnbig, hsR, hNge, hA4, abs_nonneg η, abs_nonneg CK', hCE'0]
      have hsn : s + 1 ≤ n' := by exact_mod_cast hn'big.le
      refine ⟨n' - s, by omega, ?_, ?_⟩
      · rw [hφw, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
        exact hvalx.symm
      · have := Work.Pert.pert2v2.orbit_mem_left_reduce (f := f) (φ := φ) (Dφ := Dφ) (Df := Df)
          (w := w) (s := s) (N := n' - s) hφabel hray (by
            rw [show w - (s : ℂ) = x₀ by rw [hwx]; ring, Nat.sub_add_cancel (by omega)]
            exact hmemx)
        exact this
    · -- `x₀ = w + s`, `s = -k₀ > 0`
      set s : ℕ := (-k₀).toNat with hsdef
      have hs : ((s : ℕ) : ℤ) = -k₀ := Int.toNat_of_nonneg (by omega)
      have hsC : ((s : ℕ) : ℂ) = -(k₀ : ℂ) := by
        have : ((s : ℕ) : ℂ) = ((-k₀ : ℤ) : ℂ) := by exact_mod_cast hs
        rw [this]; push_cast; ring
      have hxw : x₀ = w + (s : ℂ) := by rw [hsC, hx₀eq]; ring
      have hs1 : 1 ≤ s := by omega
      have hrayw : ∀ i : ℕ, i ≤ s → w + (i : ℂ) ∈ Dφ :=
        hseg w s hw2.1 (by rw [← hxw]; exact hx₀Dφ)
      have hr := Work.Pert.pert2v2.LeadWire.phi_ray_forward hφabel hrayw
      have hφx : φ x₀ = f^[s] (φ w) := by rw [hxw]; exact (hr s le_rfl).1
      refine ⟨n' + s, by omega, ?_, ?_⟩
      · rw [Function.iterate_add_apply, ← hφx]; exact hvalx.symm
      · have := Work.Pert.pert2v2.LeadWire.orbit_mem_right_extend (N := n') hφabel hrayw
          (by rw [← hxw]; exact hmemx)
        exact this
  exact ⟨⟨φ, Dφ', R, DR', hDφ'open, hφholo', hφabel', hDsub', hstrip'', hInjUp, hInjDn,
    hStarClose, hStarDeriv, hK'Dφ'', hφclose, hDR'open, hRequiv', hRholo', hDRsub', hRclose,
    hRupper, horbit⟩⟩
end

end Work.Pert
