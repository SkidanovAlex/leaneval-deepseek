import Submission.Work.APsi.defs

/-!
# READ ME: guidance for the Area `Ψ_A` delegation

This module contains no mathematics: it is the requester's roadmap for the two analytic
lemmas `Submission.Work.APsi.slit_facts` and `Submission.Work.APsi.lune_facts`, which are
needed for the target `Submission.Work.APsi.psiA_facts`
(`ψ_A = -(4/5) · lune (36/5) (-(slitsA ·))`, CDT arXiv:2408.15403).

The purely algebraic facts are already proved in `Submission.Work.APsi.defs`
(namespace `Work.APsi`).  Everything below is the *analytic* part that is left.

## `slit_facts (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)`

Available from `defs.lean`:

* `slit_eq_formula : slit r z = slitN r z / (8 * ↑r * z)` for `z ≠ 0`, where
  `slitN r z = slitP r z + slitR r z`,
  `slitP r z = (1+r)^2 - 2(r-1)^2 z + (1+r)^2 z^2`,
  `slitQ r z = (1+r)^2 - 2(1-6r+r^2) z + (1+r)^2 z^2`,
  `slitR r z = (1+r)(z-1) √(slitQ r z)`  (principal square root);
* `slit_mul : slit r z = z * (-8↑r/(slitR r z - slitP r z))` for **every** `z`, and
  `slitRP_ne : slitR r z - slitP r z ≠ 0`.  This is the removable-singularity
  factorization: `G z = -8↑r/(slitR r z - slitP r z)` is the holomorphic continuation of
  `slit r z / z` (`slit r 0 = 0` follows);
* `slit_joukowski_ab : slit r z + (slit r z)⁻¹ = ((1+r)^2/(4r)) (z + z⁻¹) - (r-1)^2/(2r)`
  for `z ≠ 0` (and the division-free `slit_quad`);
* `slit_ne_zero : slit r z ≠ 0` for `z ≠ 0`; polynomial identities `slitKey`, `slitR_sq`,
  `slitN_quad`; `cpow_half_sq : (w^(1/2))^2 = w`; `cpow_half_sq_of_pos`.

(1) *Continuity and differentiability*.  Write `A = (1+r)^2`, `D = 2(1-6r+r^2)`.  If
`slitQ r z = -s` with `s ≥ 0` real, then `z` is a root of the real quadratic
`X^2 - (D/A)X + (1 + s/A)`, whose two roots are conjugate with product `1 + s/A ≥ 1`, so
`‖z‖^2 = 1 + s/A ≥ 1`.  Hence `slitQ r z ∈ Complex.slitPlane` for all `z` with `‖z‖ ≤ 1`
except at the two zeros of `slitQ`, which are `(D ± i√(4A^2-D^2))/(2A)` and lie on the unit
circle.  Therefore
  * `z ↦ (slitQ r z)^(1/2)` is continuous on the closed unit ball:
    `Complex.continuousAt_cpow_const` where `slitQ r z ∈ slitPlane`, and
    `Complex.continuousAt_cpow_zero_of_re_pos` at the two zeros (the exponent `1/2` has
    `re = 1/2 > 0`);
  * it is holomorphic on the open unit ball: `DifferentiableOn.cpow_const` /
    `Complex.hasStrictDerivAt_cpow_const`, since `slitQ` maps the open ball into `slitPlane`.
  Dividing by the nowhere-vanishing `slitR r z - slitP r z` and multiplying by `z`
  (`slit_mul`) gives `ContinuousOn (slit r) (closedBall 0 1)` and
  `DifferentiableOn ℂ (slit r) (ball 0 1)`.

(2) `slit r 0 = 0` is `by simp [Submission.CDTPlan.slit]`.

(3) *Bounds*.  Let `alpha = (1+r)^2/(4r)`, `beta = -(r-1)^2/(2r)`.  For `‖w‖ = 1`,
`w + w⁻¹ = 2 Re w ∈ [-2,2]`, so `(w + w⁻¹ - beta)/alpha = (8r·Re w + 2(1-r)^2)/(1+r)^2`
lies in `[-2,2]` (maximum `2` at `Re w = 1`; minimum `2(r^2-6r+1)/(1+r)^2 ≥ -2`).  For
`0 < ‖z‖ < 1`, `z + z⁻¹ ∉ [-2,2]` (Joukowski: if `z + z⁻¹ = u ∈ [-2,2]` then `z` is a root
of the real quadratic `X^2 - uX + 1`, whose roots are conjugate of product `1`, so
`‖z‖ = 1`).  If `‖slit r z‖ = 1` for some `z` with `0 < ‖z‖ < 1`, then by
`slit_joukowski_ab`, `z + z⁻¹ = ((slit r z) + (slit r z)⁻¹ - beta)/alpha ∈ [-2,2]`,
contradiction.  So `z ↦ ‖slit r z‖` is continuous on the open ball (`slit_mul` + continuity
of `G`), never equals `1` there, and equals `0` at `z = 0`; since a preconnected subset of
`ℝ` that meets `(-∞,1)` and omits `1` lies in `(-∞,1)`, we get `‖slit r z‖ < 1` on the open
ball.  The closed-ball bound follows by continuity on the closed ball.

(4) `∀ z, slit r z = 0 → z = 0` is `slit_ne_zero` (for `z ≠ 0`) together with
`slit r 0 = 0`.

## `lune_facts (c : ℝ) (hc : 1 < c)`

Available from `defs.lean`: `luneB c = 1 + c^2` (as `luneBr c : ℝ`), `luneC c = c^2 - 1`,
`luneR c z = (1+c^2)^2(1+z)^2 - 16c^2 z`, `lune_eq`, `luneB_ne_zero`, `luneC_ne_zero`,
`luneBr_pos`, `luneCr_pos`, `lune_zero : lune c 0 = 0`,
`lune_quad : luneC c * (lune c z)^2 + luneB c * (1-z) * lune c z - luneC c * z = 0`,
`lune_pole_ne : luneC c + luneB c * lune c z ≠ 0`,
`luneF_lune : luneF c (lune c z) = z` for `luneF c w = w(B + Cw)/(C + Bw)`, and
`norm_luneF : ‖luneF c w‖ = 1` for `‖w‖ = 1`.

(1) *Continuity and differentiability*.  `luneR c z = B^2(z^2 - 2αz + 1)` with
`α = 8c^2/B^2 - 1`, `|α| < 1` (because `|8c^2 - B^2| < B^2 ⟺ 0 < (c^2-1)^2`).  If
`luneR c z = -s` with `s ≥ 0` real then `z` is a root of the real quadratic
`X^2 - 2αX + (1 + s/B^2)`, whose roots are conjugate with product `1 + s/B^2 ≥ 1`, so
`‖z‖^2 ≥ 1`.  Hence `luneR c z ∈ Complex.slitPlane` on the closed unit disc except at the two
zeros of `luneR c` (of modulus 1).  Then, exactly as for the slit, `z ↦ (luneR c z)^(1/2)`
is continuous on the closed ball (`Complex.continuousAt_cpow_const`,
`Complex.continuousAt_cpow_zero_of_re_pos`) and holomorphic on the open ball
(`DifferentiableOn.cpow_const`); divide by `2 * luneC c ≠ 0`.

(2) *Bounds and zero-freeness*.  If `‖z‖ < 1` then `‖lune c z‖ ≠ 1`; otherwise
`1 = ‖luneF c (lune c z)‖ = ‖z‖` by `norm_luneF` and `luneF_lune`, contradiction.  Since
`z ↦ ‖lune c z‖` is continuous on the ball, is `0` at `z = 0`, and never `1`, it is `< 1` on
the whole open ball (same preconnectedness argument), and `≤ 1` on the closed ball by
continuity.  Finally `lune c z = 0 → z = 0` from `lune_quad` with `w = 0`
(`luneC c ≠ 0`).
-/
