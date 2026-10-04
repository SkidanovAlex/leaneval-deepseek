import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Routes for the continuity-at-`0` inputs of `Work.Diff.GE.covRm_frame_evol_abs`

This module contains no mathematics: it is the *plan* (indices, routes and available lemmas) for the
delegated lemmas that supply the continuity at the initial time `t = 0` of the curvature quantities
along a Ricci flow.  The files proving those lemmas import this module, so that the routes below are
available to their provers.

Context.  `Submission.Diff.IsRicciFlow G T` gives joint smoothness of the metric family only on the
*half-open* interval `Ico 0 T`:

`IsRicciFlow G T := JointSmooth G (Ico 0 T) ∧ ∀ t ∈ Ico 0 T, HasDerivWithinAt (…) (Ico 0 T) t`.

Every curvature quantity is a smooth function of the metric family, so it is continuous from the
right at `0`; but the *proof* cannot use the Ricci-flow equation at `t = 0` (the hypotheses of
`Work.Diff.GE.EvolA.rmP_evol_fixed`, `Work.Diff.GE.FixAsm.mvfderiv_rmP_timeDeriv`,
`Work.Diff.T.lc_variation` etc. are stated for `t ∈ Ioo 0 T`, i.e. for families jointly smooth on an
*open* interval).  The way to turn the half-open smoothness into statements at `0` is the
reparametrisation `cfq_sqFlow G τ = G (τ ^ 2)`, which is jointly smooth on an *open* interval
`Ioo (-ρ) ρ` when `ρ ^ 2 < T`:

* `Work.Diff.GE.cfq_jointSmooth_sqFlow` (proved),
* `Work.Diff.GE.cfq_continuousAt_of_jointSmoothAt` (proved): joint smoothness at `(t₀, x)`
  gives continuity in `t` of the slice `t ↦ Φ (t, x)`,
* `Work.Diff.GE.cfq_continuousWithinAt_of_continuousAt_comp_sq` (proved): a statement of
  continuity at `0` for the reparametrised family transfers to `ContinuousWithinAt … (Ico 0 T) 0`
  for the original family (the inverse reparametrisation is `s ↦ √s`).

Two further proved tools, specific to the *spatial* (as opposed to the `t`-) dependence:

* `Work.Diff.GE.rmP_jointSmoothNoCompact` : joint smoothness of `(t, y) ↦ rmP (G t) y (A y) …` for
  fixed smooth fields `A …` and a metric family jointly smooth on an *open* `J`;
* `Work.Diff.EXT.contMDiffAt_mvfderiv_along_field` : joint smoothness of
  `(t, y) ↦ d_y (Φ (t, ·)) (A y)` for a jointly smooth `Φ : ℝ × M → F` and a smooth field `A`.
  (`Work.Diff.EXT.continuousAt_mvfderiv_family` is the corresponding `t`-continuity statement.)

## Route for `Work.Diff.GE.covRm_family_jointSmooth_fixed` (covariant derivative of the curvature)

Goal: joint smoothness at `(t, x)` of `(s, y) ↦ covRm (G s) y (V y) (A y) (B y) (C y) (D y)` for a
metric family `G` jointly smooth on an open set `J ∋ t` and *fixed* smooth fields `V A B C D`.

Unfold the field form of `∇Rm` (`Work.Diff.GE.covRm_eq_dRmPhi`, `Work.Diff.GE.dRmPhi`):

`covRm = mvfderiv (y' ↦ rmP g y' (A y') …) y (V y) − Σ_{slots} rmP g y (lcOf g (slot) y (V y)) (…)`.

* the `mvfderiv` term: `Work.Diff.EXT.contMDiffAt_mvfderiv_along_field` applied to
  `Φ := (s, y') ↦ rmP (G s) y' (A y') (B y') (C y') (D y')`, which is jointly smooth by
  `Work.Diff.GE.rmP_jointSmoothNoCompact`;
* each correction: `(s, y) ↦ lcOf (G s) (slot) y (V y)` is jointly smooth after pairing with the
  coordinate frame (`Work.Diff.T.lcOf_apply_inner_koszul`, `Work.Diff.GE.metric_pairing_family_jointSmooth`,
  `Work.Diff.GE.gramInv_jointSmooth`, `Work.Diff.EXT.eq_sum_frameVector_of_pairing`); expand the
  resulting *time-dependent* field in the chart frame of `x` and use the `ℝ`-multilinearity of
  `rmP` (`Work.Diff.GE.rmP_add_fst`, `rmP_smul_fst`, … — see `ReactionDefs.lean`) to reduce to
  `Work.Diff.GE.rmP_jointSmoothNoCompact` with the fixed frame fields.

## Route for `Work.Diff.GE.lapRmAt_zero_continuous` (`ΔRm` at the initial time)

Goal: `ContinuousWithinAt (fun s ↦ lapRmAt (G s) x a b c d) (Ico 0 T) 0` for a Ricci flow `G`.

`ΔRm` is *frame independent*, so compute it in the chart frame `cFrame x ·`:

`lapRmAt g y (A y) … = Σᵢⱼ (GramInv g x y)ᵢⱼ · cov2Rm g y (cFrame x i y) (cFrame x j y) (A y) …`

(use the `ℝ`-multilinearity of `cov2Rm` in all six slots — `Work.Diff.GE.Kato3.cov2Rm_lin_*`,
`Submission.Work.Diff.GE.kato_cov3RmExt_field` — and `Work.Diff.GE.cfq_cFrame_span` /
`Work.Diff.GE.rmNormSq_eq_N4_of_basis` for the pattern).  Hence it suffices that the
**`cov2Rm`-family** `(s, y) ↦ cov2Rm (G s) y (V y) (W y) (A y) (B y) (C y) (D y)` is jointly smooth
at `(0, ·)` near `x`, which follows from the `covRm`-family (route above) applied one level up: by
definition

`cov2Rm g y (V y) (W y) (A y) … = mvfderiv (y' ↦ covRm g y' (W y') (A y') …) y (V y) − Σ corrections`,

the first term by `Work.Diff.EXT.contMDiffAt_mvfderiv_along_field` and the corrections by expanding
the time-dependent slots `lcOf (G s) (slot) y (V y)` in the chart frame and using the `ℝ`-linearity
of `covRm` in each slot (`Work.Diff.GE.covRm_linear_fst`, `covRm_linear_thd`, `covRm_linear_fth`,
`covRm_linear_slotD`, `covRm_linear_fif`).  This needs the *Yoneda* form: prove first that
`cov2Rm` is `ℝ`-multilinear and only depends on the values of its six field arguments (all proved in
`Submission/Work/Diff/GE/cov2RmExt_prelim.lean`: `cov2RmExt_linear_*`, `cov2RmExt_germ_*`).

Alternative route (avoids `cov2Rm` almost entirely): use the *Ricci flow identity*
`∂ₛ rmP = lapRmAt + reactionFormAt` at interior times (`Work.Diff.GE.EvolA.rmP_evol_fixed`), so that
`lapRmAt (G s) y … = ∂ₛ(rmP (G ·) y …)(s) − reactionFormAt (G s) y …` for `s ∈ Ioo 0 T`.  Both terms
are continuous in `(s, y)`: the first because `(s, y) ↦ rmP (G s) y …` is jointly smooth on
`Ioo 0 T ×ˢ univ` (`rmP_jointSmoothNoCompact`) — differentiate a jointly smooth family in one
variable (`ContMDiffOn.fderivWithin` / the `mvfderiv_joint`/`mvfderiv_clm_apply` machinery already in
the workspace) — and the second is algebraic in the curvature components.  At `s = 0` one must show
that the limit equals `lapRmAt (G 0) y …`; the classical identity

`ΔRm = ∇²Ric + Rm ∗ ∇Rm`

(the trace of the second Bianchi identity `∇_m R_{ijkl} + ∇_i R_{jmkl} + ∇_j R_{mikl} = 0`
differentiated once more, using the Ricci identity `Work.Diff.GE.cov2Rm_ricci` to commute and the
contracted Bianchi identity `Work.Diff.GE.covRic_eq_sum_covRm` for the divergence of `Rm`) expresses
`ΔRm` through `∇²Ric` and products of `Rm` with `∇Rm`; the second covariant derivative of `Ric` is a
spatial derivative of the (jointly smooth, `3`-rd order) family `∇Ric`, which is a contraction of
the jointly smooth `∇Rm`-family, and the products are continuous.  Hence `ΔRm` extends continuously
to `t = 0` with value `ΔRm (G 0)`, which is exactly the statement.

## Route for `Work.Diff.GE.lapCovRmAt_zero_continuous` (`Δ∇Rm` at the initial time)

Goal: `ContinuousWithinAt (fun s ↦ lapCovRmAt (G s) x v a b c d) (Ico 0 T) 0`.

Use the Weitzenböck identity
`Work.Diff.GE.WeitzB.covLapRm_sub_lapCovRm_eq_sum`,
`Work.Diff.GE.EvolB.covLapRm_sub_lapCovRm_eq_B`:

`covLapRmAt − lapCovRmAt = Σ_m (cov3Rm (v, e_m, e_m, …) − cov3Rm (e_m, e_m, v, …))`,

whose summands are expanded by the Ricci identities `Work.Diff.GE.cov3Rm_ricci` and
`Work.Diff.GE.cov3Rm_swap` into products of curvature components with components of `∇Rm` (in the
`Classical.epsilon`-frame `onFrame g x`, which must be replaced by a *smooth* frame — e.g. the
chart frame plus the inverse Gram matrix, or the orthogonal change
`Work.Diff.GE.onFrame_orthogonal_change` — using the `ℝ`-multilinearity of `covRm` in its five
slots).  Hence `covLapRmAt − lapCovRmAt` is continuous at `0`, with limit given by the products of
the limits of the `Rm`- and `∇Rm`-families at the fixed vectors
(`Work.Diff.GE.rmP_jointSmoothNoCompact` and the `∇Rm`-family smoothness above).  On the other hand
`Work.Diff.GE.covRmTimeDeriv` decomposes as

`covRmTimeDerivWithin F G T t x v a b c d = covLapRmAt (G t) x v a b c d
   + covReactionFormAt F (G t) x v a b c d − Σ_{slots} rmP (G t) x (derivative of the connection) …`,

and at interior times `t` the Ricci-flow identity (`Work.Diff.GE.FixAsm.mvfderiv_rmP_timeDeriv`
together with the differentiability lemmas `Work.Diff.GE.EvolB.lapRmAt_fields_diff_B`,
`Work.Diff.GE.reactionFormAt_diff`) identifies the whole expression with `∂ₜ covRm`, so
`covLapRmAt (G t) = ∂ₜ covRm (G t) − covReactionFormAt (G t) + Σ …` has a limit at `0`; combining
with the limit of `lapCovRmAt` gives the statement.

## Route for `Work.Diff.GE.covRm_zero_smooth`

`s ↦ covRm (G s) x v a b c d` (fixed vectors) is the slice of the jointly smooth family of the route
above (the fields are the fixed `smoothExt x ·`), so it is smooth from the right at `0`.  Transfer
the joint smoothness of the reparametrised family `s ↦ covRm (G (s²)) x v a b c d` (open interval,
`cfq_jointSmooth_sqFlow`) to `ContMDiffWithinAt … (Ico 0 T) 0` along `s ↦ √s`
(`cfq_continuousWithinAt_of_continuousAt_comp_sq` is the continuity version; a `ContDiffWithinAt`
version is proved by the same argument, or derive the two consequences separately: existence of the
right derivative, and continuity of its right derivative).

-/

namespace Work.Diff.GE

end Work.Diff.GE
