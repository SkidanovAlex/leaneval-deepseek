import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg

/-!
# Design note for the lemmas supporting `Work.SimplyConnected.ABS.majorant_chartLogClamp`

No declaration in this module: it records the route for the delegated lemmas.

Setting: `X` a Riemann surface, `Omega` open, connected, `!= univ`, `IsCompact (closure Omega)`,
`x0 in Omega`, `rho > 0`, `chartClosedBall (chartAt C x0) ((chartAt C x0) x0) rho subset Omega`,
`0 < s < rho`, and the barrier hypothesis

`hbar : forall p in frontier Omega, exists u V, IsOpen V and p in V and
   SuperharmonicOnX u (Omega inter V) and (forall x in Omega inter V, 0 < u x) and
   ContinuousOn u V and u p = 0`.

Write `c := chartAt C x0`, `a := c x0`, `K_s := chartClosedBall c a s`, `U := Omega \ K_s`, and
`h1 := Submission.limEnvelope U f 1` for data `f` with `f = 1` on `chartSphere c a s` and
`f = 0` on `frontier Omega`.

## 1. `limEnvelope_lt_near_of_localBarrier` (the regularity step; the crux)

Classical regularity: a *local* barrier at `p in frontier Omega` forces the Perron envelope with
data `0` at `frontier Omega` to tend to `0` at `p`.  Statement: for every `eps > 0` there is an open
`N` containing `p` with `limEnvelope U f M x < eps` for all `x in U inter N`.

Route.  Fix `p` and its barrier `(u, V)` from `hbar`, and shrink `V` (T2 + local compactness) to an
open neighbourhood of `p` whose closure avoids `frontier U \ frontier Omega` (in the application
that part is the inner sphere `chartSphere c a s`, compact and not containing `p`).  Fix `C > 0` and
put `u' := fun x => if x in V then min (u x) C else C`.  Then

* `u'` is **upper semicontinuous** on `X` (continuous on `V`, constant `C` off `closure V`, and at
  `zeta in closure V \ V` all values of `u'` are `<= C = u' zeta`);
* `u'` satisfies the circle mean value inequality at every point of `Omega`: at `x in Omega inter V`
  with `u x < C` it agrees near `x` with `min (u .) C`, which is superharmonic by
  `Work.SimplyConnected.ABS.SuperharmonicOnX.inf_const_dev` (in
  `Submission.Work.SimplyConnected.ABS.globalizedBarrier_dev`); at the other points it uses the
  global bound `u' <= C = u' x`;
* `0 <= u'` on `Omega`, and `u' = u` near `p`.

For `v in Submission.limFamily U f M` put `z := fun x => v x - lam * u' x` with
`lam := (M - a' + 1) / C`, `a' := eps / 2`.  Then `z` is upper semicontinuous on `U`, satisfies the
circle MVI at every point of `U` (additivity of `circleAverage`, and `circleAverage u' <= u' x`),
and has limsup `<= a'` at every point of `frontier U`: at `zeta in frontier Omega` by the family
condition for `v` (`f zeta = 0`, `u' >= 0`); at `zeta in frontier U \ frontier Omega` because
`zeta` is outside `closure V`, so `u' = C` near `zeta`, `v <= M` and `lam * C > M - a'`.

The lemma needed at this point is a **maximum principle for upper semicontinuous functions
satisfying the circle mean value inequality**: if `U` is open with compact closure and nonempty
frontier, `z` is upper semicontinuous on `U`, satisfies the MVI at every point of `U`, and has
limsup `<= a` at every frontier point, then `z <= a` on `U`.  This is the classical maximum principle
(whose classical definition of superharmonic is upper semicontinuity plus the MVI).  Its proof is
that of `Submission.SubharmonicOnX.le_of_frontier_limsup` (`Submission/MaxPrincipleRegion.lean`)
with continuity replaced by upper semicontinuity throughout: `{z >= t}` is closed for u.s.c. `z`,
`{z >= a + d} inter U` is compact with an attained maximum, the "level set is open" step uses the
MVI plus upper semicontinuity.  **This maximum principle is self-contained and may be delegated
further**; `Commons.Analysis.Complex.Harmonic.max_principle_subharmonic` is not directly usable
(continuity hypotheses).

Then `z <= a'` on `U`, i.e. `v <= a' + lam * u'` on `U` for every member `v`, hence
`h1 <= a' + lam * u'` on `U` (`Submission.upperEnvelope_le`), and the open set
`N := {x | u x < eps / (2 * lam)}` (a neighbourhood of `p`) gives `h1 x < eps` for `x in U inter N`.

Remark.  The file `Submission/Work/SimplyConnected/ABS/limEnvelope_lt_near_of_barrier.lean` proposes
the same lemma but applies the maximum principle on `W := B inter U` (a chart ball) using the
minimum of the barrier over `(frontier B inter closure U) \ frontier Omega`; that set is **not**
compact - its closure contains points of `frontier Omega`, where the barrier vanishes - so that
route does not close.  Applying the maximum principle on all of `U` avoids this: the points where
`u'` is small are interior points of `U`, where no boundary condition is imposed.

## 2. `dirichletSphereEnvelope_facts_reg`

The six properties of `h1 = Submission.limEnvelope U f 1`.  The statement is *identical* to the
existing `Work.SimplyConnected.ABS.dirichletSphereEnvelope_facts`; its proof is complete except for
the last conjunct (`hfar`), where it invokes `Work.SimplyConnected.ABS.globalizedBarrier` (a
`sorry`).

Route.  Copy the existing proof verbatim - all its helper lemmas
(`frontier_sdiff_subset'`, `frontier_sdiff_chartClosedBall_subset`,
`chartSphere_subset_frontier_sdiff_chartClosedBall`, `chartLogClamp_inv_mul_mem_limFamily`, ...) are
`sorry`-free and exported, as are `Submission.harmonicOnX_limEnvelope`,
`Submission.limFamily_le_limEnvelope`, `Submission.upperEnvelope_le` and
`Work.SimplyConnected.ABS.limEnvelope_le_smul_of_barrier` - and replace only the `hfar` block by the
finite-cover argument fed by the pointwise lemma `limEnvelope_lt_near_of_localBarrier`: for each
`p in frontier Omega` obtain `N_p` from that lemma (barrier `(u_p, V_p)` from `hbar`, shrunk so that
`closure V_p` misses `chartSphere c a s`) and cover the compact `frontier Omega` by finitely many
`N_p` (`IsCompact.elim_finite_subcover`, exactly as in the existing proof).  Do **not** use
`globalizedBarrier`, `globalizedBarrier_dev`, `exists_limEnvelope_lt_one_of_barrier`, or any other
declaration whose proof contains a `sorry`.

## 3. `chartLogEnvelope_outerGap_of_decay`

The *outer gap*: some `theta > 0`, `1 - theta >= 0`, has `h1 x <= 1 - theta` on the chart sphere of
radius `rho` (the interface where the barrier of the Green-function construction changes branch).
It is consumed with `L = log (rho/s)`, `M = (L+1)/theta + 1`, `A = log rho + M`, `B = L + M + 1` and
the inequality `B * (1 - theta) < A - log rho`.

Route (given `h1` harmonic on `U`, `h1 <= 1`, and `h1 < 1/2` on `N inter U` for an open
`N` containing the nonempty `frontier Omega`).  Suppose `h1 y = 1` for some `y` in the outer chart
sphere.  Since `h1` is harmonic and `<= 1`, `E := {x in U : h1 x = 1}` is open and closed in `U`;
let `C` be the component of `y` in `U`.  The open annulus
`chartBall c a rho \ chartClosedBall c a s` is connected and meets `E` (it accumulates at `y`),
hence lies in `C`.  Then `C union K_s` is open in `Omega` (near a point of the inner sphere
`chartSphere c a s`, every point of `Omega` is either in `K_s` or in the annulus, since the annulus
has room around the sphere) and closed in `Omega` (components of the open `U` are closed in `U`).
As `Omega` is preconnected and nonempty, `C union K_s = Omega`, hence `C = U` and `h1 = 1` on `U`;
but `U inter N` is nonempty (`frontier Omega subset closure U`, and `frontier Omega` is nonempty),
contradicting `h1 < 1/2` there.  So `h1 < 1` on the compact outer sphere, and continuity of `h1`
gives the uniform `theta`.

Useful: `Submission.SubharmonicOnXAt.eqOn_of_le` (maximum principle), connectivity of the chart
annulus (prove in the chart, e.g. by path connectedness in polar coordinates), and the elementary
frontier facts of `Submission/Work/SimplyConnected/ABS/dirichletSphereEnvelope_facts.lean`.
-/
