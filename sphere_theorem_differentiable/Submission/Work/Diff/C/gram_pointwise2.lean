import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.cap_avoid
import Submission.Work.Diff.C.gram_along
import Submission.Work.Diff.C.osc_lower
import Submission.Work.Diff.C.ray_cover
import Submission.Work.Diff.C.init_data
import Submission.Work.Diff.C.psi_estimates
import Submission.Work.Diff.C.rgrad_comp_eventuallyEq
import Submission.Work.Diff.C.gp_helpers
import Submission.Work.Diff.C.gp_ode_compare
import Submission.Work.Diff.C.sum_rule_good_ray
import Submission.Work.Diff.C.gram_along_pair
import Submission.Work.Diff.C.ray_model_stay
import Submission.Work.Diff.C.gb2_bad_branch

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

-- ROUTE for the prover (see also the reviewer notes).  Write `qᵢ := qpt hmet p e i`,
-- `fᵢ := fFam ... i`, `Fᵢ := ψ ∘ fᵢ`.  For x ≠ p use `ray_cover`: x = GExp p (s • u),
-- s = rdist p x, |u| = 1; and `fᵢ(γσ) ≈ mᵢ(σ) := fᵢ(p) cos σ + ⟪∇fᵢ(p),u⟫ sin σ`, which by
-- `InitData` is `m₀ = cos σ` and `mᵢ(σ) = ⟪eᵢ,u⟫ sin σ` (i ≥ 1), valid while `fᵢ > -1+c`
-- (`Diff/C/ray_cos_compare`, in the workspace).
-- (1) Smoothness of Fᵢ: for `fᵢ(x) < -1+c` it is locally the constant `-1+c`; for `fᵢ(x) ≥ -1+c`
--     use `hsmC` and compose with ψ.
-- (2) MODEL LEMMA (`Diff/C/ray_model_stay`, in the workspace): if `-1+3c ≤ mᵢ` on `[0,s]` then
--     `fᵢ(γσ) > -1+2c` and `|fᵢ(γσ) - mᵢ(σ)| ≤ 2ε₁s` for all `σ ∈ [0,s]`.  Its trig hypothesis is
--     `Diff/C/model_lower_off_bad` (in the workspace); the hypothesis fails only on the bad set
--     `Bᵢ := {σ ∈ [π/2-α, π/2+α] ∧ ⟪eᵢ,u⟫ ≤ -cos α}`.  At most one index i can be bad, and if i is
--     bad then `|⟪eⱼ,u⟫| ≤ 2 sin(α/2) ≤ α` for every `j ≠ i`.
-- (3) GRAM: with `Aᵢⱼ := gp Fᵢ Fⱼ` one has `Aᵢⱼ' = Eᵢ(γ',∇Fⱼ) + Eⱼ(γ',∇Fᵢ)`, `Eᵢ = Hess fᵢ + fᵢ g`,
--     hence `|Aᵢⱼ'| ≤ 2ε₁` wherever `fᵢ, fⱼ > -1+c` (`gram_along` integrates this).  Where
--     `fᵢ ≤ -1+c`: `Fᵢ ≡ -1+c` locally, so `∇Fᵢ = 0` and `|Aᵢⱼ| ≤ |Fⱼ| ≤ α + 2ε₁π` by (2).  Chaining
--     from `Aᵢⱼ(p) = δᵢⱼ` (`InitData`) gives `|Aᵢⱼ(x) - δᵢⱼ| ≤ α + O(ε₁)`.
-- (4) `Σ Fᵢ(x)² ≈ Σ mᵢ(x)² = cos²s + sin²s = 1` in the good case (Parseval), `≈ 1 + O(α²)` in the
--     bad case; the cutoff ψ perturbs by `O(c)`.

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false




/-! ## STATUS of the assembly (state as of the current session)

PROVED in/around this file:
* `Work.Diff.C.cmDiff_psi_comp` (module `Diff/C/gp_helpers`) — conclusion (1);
* `Work.Diff.C.init_gram` (`Diff/C/gp_helpers`) — the whole statement at `x = p`;
* `Diff/C/ray_cos_compare` (PROVED, sorry-free) — the ODE comparison along a ray;
* `Diff/C/ray_model_stay` + `Diff/C/cap_avoid` + `Diff/C/osx_lower` — the bootstrap
  "trig bound ⟹ `fᵢ > -1+2c` and `|fᵢ(γσ) - mᵢ(σ)| ≤ 2ε₁s` on `[0,s]`";
* `Diff/C/ray_cap_algebra` — Parseval `Σβᵢ² = 1`, at most one index with `βᵢ ≤ -cos α`,
  `|βⱼ| ≤ sin α` for the others;
* `Diff/C/sum_rule_good_ray` — the sum rule (conclusion (2)) in the case where the model
  comparison and the non-clamping hold for *every* index;
* `Diff/C/gram_along_pair` (needs `Diff/C/gp_helpers`) — conclusion (3) for a *pair* `(i,j)`
  that stays above `-1+2c` along the whole ray: `|Aᵢⱼ(x) - δᵢⱼ| ≤ 2ε₁s`;
* `Diff/C/gram_good_ray` — the pair bound when *all* indices stay good (weaker than the pair
  version, but it is the one wired into `psi_comp_eq_self`).

CASE ANALYSIS for `x ≠ p` (write `x = γ s`, `γ σ = GExp p (σ • u)`, `s = rdist p x ≤ π`,
`β k = ⟪e k, u⟫`; `m₀(σ) = cos σ`, `m_{k+1}(σ) = β k sin σ`):
1. all indices good (trig bound `-1+3c ≤ mᵢ` on `[0,s]`): (2) by `sum_rule_good_ray`,
   (3) by `gram_along_pair`, both giving `2ε₁π ≤ 100(n+2)(ε₁π+α+√c)`.
2. index 0 "bad" (i.e. `cos s < -1+3c`, so `s > π-√(6c)`): then `|sin s| ≤ √(6c)` and every
   other index is good, so `|Fⱼ(x)| ≤ α + 2ε₁π` for `j ≥ 1`, `F₀(x) = ψ(cos s) ≤ -1+3c`,
   `|∇F₀(x)| = |ψ'(cos s)| |sin s| ≤ 2√(6c)`: all entries and the sum rule are then bounded by
   `O(√c) + O(α)` — no geometric input needed.
3. one bad index `i = Fin.succ k` (`β k ≤ -cos α`, the trig bound fails).
   (a) `fᵢ(x) ≤ -1+c` (dip at the endpoint): `Fᵢ(x) = -1+c`, `∇Fᵢ(x) = 0`, so
       `Aᵢⱼ(x) = (-1+c) Fⱼ(x)`; for `j ≠ i, j ≥ 1` this is `≤ α + 2ε₁π`, and for `j = 0` one
       needs `|cos s| ≤ small`: this is `Work.Diff.C.dip_equator_crux`
       (`Diff/C/dip_equator_crux`, DELEGATED, statement = `dip_near_equator` with the
       minimising-ray identity `rdist p (GExp p (s•u)) = s` as an explicit hypothesis).
       The sum rule in this case is elementary arithmetic from the crux.
   (b) `fᵢ(x) > -1+c`: then `Fᵢ(x) = fᵢ(x)` and one needs the *model through the dip*: the
       aim is `fᵢ(γs) ≈ β k sin s` **and** `⟪∇fᵢ(x), γ'(s)⟫ ≈ β k cos s` (the energy
       `fᵢ² + (fᵢ')² ≈ β k²` is preserved through the dip); then
       `Aᵢ₀(x) = -sin(s)·⟪∇fᵢ(x),γ'(s)⟫ + fᵢ(x) cos s ≈ -β k sin s cos s + β k sin s cos s = 0`
       and for `j ≥ 1`, writing `∇fᵢ = a γ' + w` with `|w|² = 1 - fᵢ² - a² ≤ α² + O(ε₁)`
       (because `|β k| ≥ cos α`), one has `Aᵢⱼ ≈ β k βⱼ + O(α) ≤ 2α + O(ε₁)`.
       Both facts (value and derivative of `fᵢ` through the dip) are what a strengthened
       `dip_equator_crux` supplies; the value alone is *not* enough (the sign of the
       derivative is needed for the `(i,0)` entry).

LEAD'S PLAN for the two remaining `sorry`s (bad-index branch of (2) and (3)), as of the
latest session: the bad branch is being proved as `Work.Diff.C.gram_bad_case2`
(`Diff/C/gram_bad_case2`, one `sorry` left), which concludes *exactly* the two bounds of this file
for a given point `x = GExp p (s • u)` and a given index/time `(i, σ)` at which the trigonometric
bound fails.  Its inputs are the hypotheses of this file **plus**
`hper : Work.Diff.C.GeoCrux.PerimeterBoundProp` (the kept perimeter bound,
`Diff/C/geoCrux/perimeter_bound`, `Work.Diff.C.GeoCrux.perimeter_bound`) **plus**
`hdiam2 : ∀ x y : M, rdist x y ≤ Real.pi` (a *global* diameter bound, strictly stronger than the
`hdiam : ∀ y, rdist p y ≤ π` of this file!).

DECISION ON THE `hdiam2` FORK (recorded after inspecting the bad-case development):
**commission a `hdiam`-armed variant; do not try to derive `hdiam2`.**  The evidence:
* `hdiam2` is *not* derivable from the hypotheses of this file.  They only give the round-unit-sphere
  Hessian/eikonal structure on the region `{f > -1+c}`, with an error `ε₁` that is `O(ε₁)` at scale
  `π/2`; a near-round metric with all points within `π` of the *chosen* `p` (so `hdiam` holds) can have
  diameter `π + O(ε₁)`.  From `hdiam` alone the triangle inequality gives only `2π`.
* Inside `gram_bad_case2` itself, `hdiam2` occurs only in the binder and in the helper
  `gb2_rdist_qpt_succ`, which has **no call sites in the whole area** (dead), and whose only use is
  `rdist p (qpt … (Fin.succ j)) ≤ π` — available from `hdiam`.  So `gram_bad_case2` with `hdiam`
  instead of `hdiam2` costs essentially one line.
* The expensive half is its hypothesis `hper : Work.Diff.C.GeoCrux.PerimeterBoundProp`
  (`Diff/C/geoCrux/Defs.lean`), which is itself *armed with* `hdiam2` and uses it for **arbitrary**
  triangle vertices (`geoCrux/perimeter_bound.lean:195-197, 214, 227, 231-232`).  So the variant needs
  a perimeter bound armed with `hdiam`; in the bad-case application the triangle is the specific one
  `(p, qᵢ, x)` with the `p`-distances bounded by `hdiam`, so a special-case perimeter bound for that
  configuration is the right-sized piece.
* If instead the lead prefers an interface change (add `hdiam2` to `gram_pointwise2`'s hypotheses — it
  *is* available in the intended application, where `(1,(1+η)]`-pinching gives `diam ≤ π` by
  Bonnet–Myers), that is the lead's call and not mine: the delivered statement is frozen.

REFINED STATUS of the bad-case wiring (after commissioning `perimeter_bound_thin`):
* `Work.Diff.C.perimeter_bound_thin` (DELEGATED, `Diff/C/perimeter_bound_thin`) is the faithful
  rename of `perimeter_bound_aux` with `hdiam2` replaced by the three side bounds `hxy, hyz, hzx`
  and `hhinge` kept as a hypothesis.  Reviewer-verified: every `hdiam2` use in `perimeter_bound_aux`
  is a pair inside the triangle.
* The *hinge* input `hhinge` is the genuinely geometric piece.  A first attempt at a thin instance
  (`Diff/C/ray_far_cos`, same ray from `p`) was reviewed and rejected as *true but useless*: the
  hypothesis `rdist x y + s ≤ π` puts it in the free regime (`hinge_cos_easy`), whereas
  `perimeter_bound_aux` consumes the hinge only in the branch `¬ (rdist x y + s ≤ π)`.  The hard
  content is `Work.Diff.C.GeoCrux.HingeCosHardProp` (`geoCruX/FarDefs.lean`, proved as
  `Work.Diff.C.geoCruX.hinge_cos_hard := by sorry`, `geoCruX/hinge_cos_hard.lean`), whose proof
  skeleton is otherwise complete there (`cot_add_cot`, `sin_L_ge_of_cot_sum`, `arccos_one_sub_le`,
  `phase_sq_of_arccos_add`, `cos_ge_of_far_ball_case`, ...).  NEXT: read `HingeCosHardProp`'s
  hypothesis list and its `hdiam2` uses in that file, then delegate the *thin* hard hinge exactly as
  `perimeter_bound_thin` thins `perimeter_bound_aux` (replace the global diameter bound by the side
  bounds the proof actually consumes).
* Item 3 (`gram_bad_case2` with `hdiam2`/`hper` dropped) is a binder swap, but it should be
  delegated only *after* `gram_bad_case2` is `sorry`-free, since the variant inherits its proof.

REFINED STATUS of the bad-case wiring (after commissioning `perimeter_bound_thin`):
* `Work.Diff.C.perimeter_bound_thin` (DELEGATED, `Diff/C/perimeter_bound_thin`) is the faithful
  rename of `perimeter_bound_aux` with `hdiam2` replaced by the three side bounds `hxy, hyz, hzx`
  and `hhinge` kept as a hypothesis.  Reviewer-verified: every `hdiam2` use in `perimeter_bound_aux`
  is a pair inside the triangle.
* The *hinge* input `hhinge` is the genuinely geometric piece.  A first attempt at a thin instance
  (`Diff/C/ray_far_cos`, same ray from `p`) was reviewed and rejected as *true but useless*: the
  hypothesis `rdist x y + s <= pi` puts it in the free regime (`hinge_cos_easy`), whereas
  `perimeter_bound_aux` consumes the hinge only in the branch `not (rdist x y + s <= pi)`.  The hard
  content is `Work.Diff.C.GeoCrux.HingeCosHardProp` (`geoCruX/FarDefs.lean`, proved as
  `Work.Diff.C.geoCruX.hinge_cos_hard := by sorry`, `geoCruX/hinge_cos_hard.lean`), whose proof
  skeleton is otherwise complete there (`cot_add_cot`, `sin_L_ge_of_cot_sum`, `arccos_one_sub_le`,
  `phase_sq_of_arccos_add`, `cos_ge_of_far_ball_case`, ...).  NEXT: read `HingeCosHardProp`'s
  hypothesis list and its `hdiam2` uses in that file, then delegate the *thin* hard hinge exactly as
  `perimeter_bound_thin` thins `perimeter_bound_aux`.
* **NEGATIVE RESULT on the hard hinge (two independent reviews):** the thin form of
  `HingeCosHardProp` is *not* obtainable by replacing the global bound with ray-local bounds.  The
  hard case needs, besides the entry bound (which is per-pair at `(x,y)`), the *passage bound*
  `s - σ₁ ≤ 7.3 √(c + ε₁π)`, which is derived from the far-ball diameter and the injectivity input
  (`geoCrux/far_ball_diameter.lean`, `geoCrux/sphere_size_bound.lean`,
  `geoCrux/injectivity_radius.lean`).  Those are armed with the *global* `hdiam : ∀ x y, rdist x y ≤ π`
  and use it at **off-ray** points — e.g. `far_ball_diameter` calls `sphere_size_bound` at
  `zt = GExp y (β • u)`, a point on a ray from the *centre* `y`, not on the ray `GExp x (σ • u)`.
  So no hypothesis of the form `∀σ∈[0,s], rdist y (GExp x (σ•u)) ≤ π` can discharge them; thinning
  would require re-deriving `SphereSizeBoundProp` / `FarBallDiameterProp` / `InjectivityProp` with
  per-pair inputs.  **Consequence: the bad case in this file cannot be closed by the library's
  `HingeCosHardProp` route without either (a) the global diameter bound in this file's context, or
  (b) an interface change (the lead's call).**  A third possibility worth exploring (untried):
  the off-ray bound that *is* available here is the cap-depth statement
  `Work.Diff.C.fb_cap_depth` (proved; `far_ball_excess` is now a wrapper around it), which bounds
  `rdist q z` for any `z` at distance `≥ π - arccos (1-c)` from an arbitrary centre `q`; it is
  `π + arcsin (2ε₁)`, i.e. `π` up to `O(ε₁)`, and might be strong enough for the passage bound if the
  consumer is re-stated with that slack.

* **ANSWER to "does the `O(ε₁)` slack in `fb_cap_depth` suffice for the passage bound?" — YES, with
  the quantified constants.**  Reading the consumer chain settles it:
  - `Work.Diff.C.geoCrux.passage_le_of_far_ball_diameter` (`geoCruX/hinge_cos_hard.lean:432`) proves
    the passage bound `s - σ₁ ≤ (73/10)√(c + ε₁π)` from exactly three inputs: the far-ball diameter
    **at the single centre `y`** (`hFB : ∀ z z', rdist y z ≥ π - arccos(1-c) → rdist y z' ≥ … →
    rdist z z' ≤ (73/10)√(c+ε₁π)`), the membership of `γ σ₁`, `γ s` in that far ball, and the
    minimality of the sub-arc.  So the passage bound is **linear in the diameter constant** and the
    passing step needs no global diameter bound at all.
  - `geoCruX/far_ball_diameter.lean` uses the global `hdiam` only at `hdiam y z`, `hdiam y z'`
    (lines 164-165 — the two far points from the centre `y`) plus one recursive propagation
    (line 92).  `fb_cap_depth` supplies exactly that centre bound, at the price of
    `arcsin (2ε₁) ≤ 2ε₁ ≤ 2√(c + ε₁π)`.
  Hence the thin far-ball diameter holds with `+2K` (`K := arcsin (2ε₁)`), which is absorbed by the
  `√(c+ε₁π)` term at the cost of a modest constant increase — delegated as
  `Diff/C/far_ball_diameter_thin` (`Work.Diff.C.far_ball_diameter_thin`; reviewers: "the `+2K` is
  exactly calibrated, one `K` from each of `hDz`, `hDz'`, and `K = 0` recovers the original").
  The residual work is proof-side and real: the sphere-size step (`geoCruX/sphere_size_bound`,
  armed with the global `hdiam`, still a `sorry`) has no diameter-free version yet, so the thin
  prover must supply a **diameter-free sphere-size bound**; the `hdiam` uses there are at points of
  distance exactly `β = π - arccos(1-c) < π` from the centre, where the bound should be automatic.
  Downstream, `hinge_hard_assembly`'s hardcoded `73/10` must be re-derived with the enlarged constant.

* Item 3 (`gram_bad_case2` with `hdiam2`/`hper` dropped) is a binder swap, but delegate it only
  *after* `gram_bad_case2` is `sorry`-free, since the variant inherits its proof.

Recommended next delegations: `perimeter_bound_hdiam` (or the special-case version for the triangle
`(p, qᵢ, x)`), then `gram_bad_case2_hdiam`; wiring lines 316/346 is then mechanical via the `(i, σ)`
witness that the `¬hgood` branch produces.

⚠️ ORIGINAL BLOCKER NOTE (kept for context): `hdiam2` is not among the hypotheses of
`gram_pointwise2`, and it is *not* an immediate consequence of `hdiam` (which only bounds distances
from the single point `p`).  In the intended application (the classical endgame, where the metric is
`(1,(1+η)]`-pinched) it follows from Bonnet–Myers; from `hHess`/`hgrad` alone it needs an argument.
Two ways out: (i) derive `hdiam2` from the hypotheses of this file, or (ii) obtain a variant of
`gram_bad_case2` with `hdiam` in place of `hdiam2`.  Until that is settled the two `sorry`s cannot be
discharged by `gram_bad_case2`.

STATE OF THE ASSEMBLY (this session): conclusions (1), the `x = p` cases of (2)/(3), and the
"every index good" cases of (2)/(3) are proved in this file; what remains is the case in which at
least one index is bad (two `sorry`s below, marked).  The helper `Work.Diff.C.gram_ray_data`
(above) produces the minimising ray and, for every index whose trigonometric bound holds, the
non-clamping and the model comparison.

CONSTANT-TIGHTNESS WARNING for the bad-index entries: `Diff/C/dip_model_through` (DELEGATED)
asserts the value/derivative model with error `K' = 100 (n+2) (ε₁π + α + √c)`, which is *too
loose* for the off-diagonal entries `A_{i0}` and `A_{ij}`: those need the *cancellation*
`-sin(s)·aᵢ + (ψ fᵢ) cos s ≈ 0` (resp. `βᵢβⱼ + O(α)`), so their error is additive in the model
errors and the conclusion is `` ≤ K' ``.  Use instead the sharp form with error
`K₀ := ε₁π + α + √c` (the proofs give `|cos s| ≤ √(3c) + O(ε₁)` and the same order for the
derivative), and only then combine: any constant `C·K₀` with `C ≤ 100 (n+2)` is fine since
`n + 2 ≥ 4`.  A re-delegation of `Diff/C/dip_model_through` with `K₀` in place of `K'` is the
cleanest fix.

TRAPS (recorded so that they are not rediscovered):
* `gram_sum_sq_le` cannot be used for (2): it needs `(n+1)δ ≤ 1/4`.
* the hypotheses are *large-scale*: `hHess` is a comparison statement with error `ε₁` valid on
  `{f > -1+c}`, i.e. at distances `< π-δ` from the centre; at small distance (`r ≲ √ε₁`) it
  carries no curvature information (the model error `cos r - √Λ sin r cot(√Λ r)` is `O(r²)`
  there).  In particular a *pointwise* sectional-curvature bound cannot be extracted, so the
  library Toponogov (`Submission.HingePiece.gcompHolds_pi_apply`, which needs
  `QuarterPinched cov`) is NOT available in this lemma.
* the ray from `p` is minimising: `rdist p (GExp p (τ • u)) = τ` for `τ ∈ [0,s]`; this is
  needed and must be supplied (`Diff/C/ray_cover` gives it for the endpoint `x`).
* do not import a module that imports this file (`gram_along_pair` used to; the shared helpers
  now live in `Diff/C/gp_helpers`).
* NAME CLASH: `Work.Diff.C.inner_rgrad_mvfderiv` is declared both in `Diff/C/grad_smooth` (in the
  `gram_along` cone) and in `Diff/C/grad_smoothAt` (in the `ray_cos_compare` cone), so no file may
  import both.  `Diff/C/gp_ode_compare` is a clash-free port of the ODE comparison
  (`Work.Diff.C.gp_ode_compare`, all auxiliary names prefixed `gpOde_`); this file uses that one.
  `this file` deliberately does NOT import `Diff/C/ray_cos_compare`, `grad_smooth` or `grad_smoothAt`.

RECIPE for delegated statements (the harness elaborates them in a file with only the listed
`depends_on` imports and NO `open`s, so every name must be resolvable without them):
* prefix the statement with `open Bundle in` (a single command) -- without it the fibre instances
  `(x : M) → NormedAddCommGroup/InnerProductSpace (TangentSpace I x)` are not synthesised;
* write `∞` as `((⊤ : ENat) : WithTop ENat)`;
* `Bundle.RiemannianBundle`, `CovariantDerivative.ContMDiffCovariantDerivative`,
  `LeanEval.Geometry.SphereTheorem.IsMetricCompatible`;
* `CMDiffAt ∞ f x` as `ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) f x`;
* names in the `Work.Diff.C` namespace (e.g. `fFam`, `rgrad`, `rhess`, `gp`) are fine unqualified
  when the statement sits in `namespace Work.Diff.C`; `Submission.GlobalExp.GExp` and
  `Submission.Geodesic.curveVelocity` need their full path.
-/


/-- **The ray data and the model comparison.**  For `x ≠ p` this produces the minimising ray from
`p` to `x` (`Diff/C/ray_cover`) together with, for every index whose trigonometric hypothesis
`-1+3c ≤ mᵢ` holds on `[0,s]`, the non-clamping `fᵢ > -1+2c` and the model comparison
`|fᵢ(x) - mᵢ(s)| ≤ 2ε₁s` (via `Diff/C/ray_model_stay`, whose ODE input comes from
`Diff/C/gp_ode_compare`). -/
theorem gram_ray_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} (hc : 0 < c) (hε₁ : 0 ≤ ε₁) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hdiam : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi)
    (hsmC : ∀ (q y : M), -1 + c ≤ fcos (I := I) (M := M) q y →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    {x : M} (hx : x ≠ p) :
    ∃ (u : TangentSpace I p) (s : ℝ), Inner.inner ℝ u u = 1 ∧ 0 < s ∧
      rdist (I := I) (M := M) p x = s ∧
      Submission.GlobalExp.GExp (cov := cov) hmet p (s • u) = x ∧ s ≤ Real.pi ∧
      (∀ (i : Fin (Module.finrank ℝ E + 1)),
          (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos σ
              + Inner.inner ℝ (rgrad (I := I) (M := M)
                  (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin σ) →
          (∀ τ ∈ Set.Icc (0 : ℝ) s, -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e i
              (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))) ∧
          (∀ τ ∈ Set.Icc (0 : ℝ) s,
            |fFam (I := I) (M := M) (cov := cov) hmet p e i
                (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u))
              - (fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos τ
                + Inner.inner ℝ (rgrad (I := I) (M := M)
                    (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin τ)|
              ≤ 2 * ε₁ * s)) := by
  classical
  obtain ⟨u, s, hu, hs0, hrs, hxs⟩ := ray_cover (I := I) (M := M) (cov := cov) hmet htor p hx
  have hu_ne : u ≠ 0 := by
    intro h0
    rw [h0] at hu
    simp at hu
  have hsπ : s ≤ Real.pi := by
    rw [← hrs]
    exact hdiam x
  have hray_cmd : ContMDiff 𝓘(ℝ) I ∞
      (fun σ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u)) :=
    Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hu_ne
  -- the ODE comparison on prefixes of the ray
  have hcmp : ∀ (i : Fin (Module.finrank ℝ E + 1)) (t : ℝ), t ∈ Set.Icc (0 : ℝ) s →
      (∀ σ ∈ Set.Icc (0 : ℝ) t, -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e i
        (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) →
      |fFam (I := I) (M := M) (cov := cov) hmet p e i
          (Submission.GlobalExp.GExp (cov := cov) hmet p (t • u))
        - (fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos t
          + Inner.inner ℝ (rgrad (I := I) (M := M)
              (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin t)|
        ≤ 2 * ε₁ * t := by
    intro i t ht hpre
    have h := gp_ode_compare (I := I) (M := M) (cov := cov) hmet htor
      (q := p) (f := fFam (I := I) (M := M) (cov := cov) hmet p e i) (ε := ε₁) hε₁ hu
      (s := t) ht.1 ?_ ?_
    · refine le_trans h ?_
      have h2 : 0 ≤ ε₁ * t := mul_nonneg hε₁ ht.1
      linarith
    · -- smoothness along the prefix
      intro τ hτ
      exact hsmC _ _ (le_of_lt (hpre τ ⟨hτ.1, hτ.2⟩))
    · -- the Hessian bound in quadratic form
      intro τ hτ V
      have hgt : -1 + c < fFam (I := I) (M := M) (cov := cov) hmet p e i
          (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) :=
        hpre τ ⟨hτ.1, hτ.2⟩
      have hb := hHess (qpt (I := I) (M := M) (cov := cov) hmet p e i)
        (Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u)) V V hgt
      simpa only [fFam, real_inner_self_eq_norm_sq, sq, mul_assoc] using hb
  -- the model comparison and the non-clamping, whenever the trig bound holds
  have hmodel : ∀ (i : Fin (Module.finrank ℝ E + 1)),
      (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos σ
          + Inner.inner ℝ (rgrad (I := I) (M := M)
              (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin σ) →
      (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 2 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e i
          (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))) ∧
      (∀ σ ∈ Set.Icc (0 : ℝ) s,
        |fFam (I := I) (M := M) (cov := cov) hmet p e i
            (Submission.GlobalExp.GExp (cov := cov) hmet p (σ • u))
          - (fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos σ
            + Inner.inner ℝ (rgrad (I := I) (M := M)
                (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin σ)|
          ≤ 2 * ε₁ * s) := by
    intro i htrig
    have h := ray_model_stay (I := I) (M := M) (cov := cov) hmet htor
      (q := p) (f := fFam (I := I) (M := M) (cov := cov) hmet p e i) (u := u) hu
      hs0.le hsπ hc hε₁ (by linarith [hnum2]) ?_ htrig (hcmp i)
    · exact ⟨fun σ hσ => le_of_lt (h.1 σ hσ), fun σ hσ => h.2 σ hσ⟩
    · -- continuity along the ray
      exact ((hcont _).comp hray_cmd.continuous).continuousOn
  exact ⟨u, s, hu, hs0, hrs, hxs, hsπ, fun i htrig => hmodel i htrig⟩

theorem gram_pointwise2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hdiam : ∀ x : M, rdist (I := I) (M := M) p x ≤ Real.pi)
    (hsm : ∀ q : M, SmoothOnRegion (I := I) (M := M) c (fcos (I := I) (M := M) q))
    (hsmC : ∀ (q x : M), -1 + c ≤ fcos (I := I) (M := M) q x →
      CMDiffAt ∞ (fcos (I := I) (M := M) q) x)
    (hHess : ∀ q : M, HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (fcos (I := I) (M := M) q))
    (hgrad : ∀ (q x : M), -1 + c < fcos (I := I) (M := M) q x →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
        = 1 - (fcos (I := I) (M := M) q x) ^ 2)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧
      (∀ s : ℝ, 0 ≤ deriv ψ s ∧ deriv ψ s ≤ 2) ∧
      (∀ s : ℝ, -1 + 2 * c ≤ s → ψ s = s) ∧ (∀ s : ℝ, s ≤ -1 + c → ψ s = -1 + c)) :
    (∀ i : Fin (Module.finrank ℝ E + 1),
        CMDiff ∞ (fun x : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i x))) ∧
    (∀ x : M, |(∑ i, (ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i x)) ^ 2) - 1|
      ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c)) ∧
    (∀ (x : M) (i j : Fin (Module.finrank ℝ E + 1)),
      |gp (I := I) (M := M)
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e i y))
          (fun y : M => ψ (fFam (I := I) (M := M) (cov := cov) hmet p e j y)) x
        - (if i = j then 1 else 0)|
      ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c)) := by
  classical
  have hK : 0 ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) := by
    have h3 : (0 : ℝ) ≤ α := hα.le
    have h4 : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
    have h2 : 0 ≤ ε₁ * Real.pi := mul_nonneg hε₁ Real.pi_pos.le
    have h5 : 0 ≤ ε₁ * Real.pi + α + Real.sqrt c := by linarith
    have h1 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) + 2 := by positivity
    positivity
  have hsqrt6c_le_α : Real.sqrt (6 * c) ≤ α := by
    have h1 : 1 - Real.cos α ≤ α ^ 2 / 2 := by
      have := Real.one_sub_sq_div_two_le_cos (x := α)
      linarith
    have h2 : 6 * c ≤ α ^ 2 := by nlinarith [hnum1, h1]
    have h3 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq hα.le] at h3
  have hc_le_sqrtc : c ≤ Real.sqrt c := by
    have hsq : Real.sqrt c * Real.sqrt c = c := by rw [← sq]; exact Real.sq_sqrt hc.le
    have hle1 : Real.sqrt c ≤ 1 := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
    calc c = Real.sqrt c * Real.sqrt c := hsq.symm
      _ ≤ Real.sqrt c * 1 := mul_le_mul_of_nonneg_left hle1 (Real.sqrt_nonneg c)
      _ = Real.sqrt c := mul_one _
  have hε₁π_lt : ε₁ * Real.pi ≤ Real.sqrt c / 4 := by
    have h1 : ε₁ * Real.pi < c / 4 := by nlinarith [hnum2]
    linarith [hc_le_sqrtc]
  have hn2 : (2 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
  have hKn : 300 * (Real.sqrt c + ε₁ * Real.pi) ≤
      100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) := by
    have h2 : (300 : ℝ) ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) := by
      have h6 : (3 : ℝ) ≤ (Module.finrank ℝ E : ℝ) + 2 := by linarith
      linarith
    have h3 : Real.sqrt c + ε₁ * Real.pi ≤ ε₁ * Real.pi + α + Real.sqrt c := by linarith [hα.le]
    have h4 : 0 ≤ ε₁ * Real.pi + α + Real.sqrt c := by
      have h5 : 0 ≤ Real.sqrt c + ε₁ * Real.pi :=
        add_nonneg (Real.sqrt_nonneg c) (mul_nonneg hε₁ Real.pi_pos.le)
      linarith [hα.le, h5]
    calc 300 * (Real.sqrt c + ε₁ * Real.pi) ≤ 300 * (ε₁ * Real.pi + α + Real.sqrt c) :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) :=
          mul_le_mul_of_nonneg_right h2 h4
  have hKn2 : 125 * ((Module.finrank ℝ E : ℝ) + 1) * (Real.sqrt c + ε₁ * Real.pi) ≤
      100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) := by
    have hb : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
    have ha : 0 ≤ ε₁ * Real.pi := mul_nonneg hε₁ Real.pi_pos.le
    have hα2 : 2 * Real.sqrt c ≤ α := by
      have h1 : Real.sqrt 6 * Real.sqrt c ≤ α := by
        have h2 := hsqrt6c_le_α
        rwa [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 6)] at h2
      have h3 : (2:ℝ) ≤ Real.sqrt 6 := by
        have h4 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
        nlinarith [Real.sqrt_nonneg 6]
      nlinarith [h1, h3, hb]
    have h5 : Real.sqrt c + ε₁ * Real.pi ≤ (5 / 4) * Real.sqrt c := by linarith [hε₁π_lt]
    have h7 : 100 * ((Module.finrank ℝ E : ℝ) + 2) * (3 * Real.sqrt c) ≤
        100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith [hα2, ha]
    calc 125 * ((Module.finrank ℝ E : ℝ) + 1) * (Real.sqrt c + ε₁ * Real.pi)
          ≤ 125 * ((Module.finrank ℝ E : ℝ) + 1) * ((5 / 4) * Real.sqrt c) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (3 * Real.sqrt c) := by
          nlinarith [hn2, hb]
      _ ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (ε₁ * Real.pi + α + Real.sqrt c) := h7
  refine ⟨?_, ?_, ?_⟩
  · -- conclusion (1): every `Fᵢ = ψ ∘ fᵢ` is `C^∞`
    intro i
    refine cmDiff_psi_comp (I := I) (M := M) (c := c) (ψ := ψ)
      (f := fFam (I := I) (M := M) (cov := cov) hmet p e i)
      hψ.1 hψ.2.2.2.2 (hcont _) ?_
    intro x hx
    exact hsmC _ x hx
  · -- conclusion (2): the squared sum
    intro x
    by_cases hx : x = p
    · subst hx
      have h := (init_gram (I := I) (M := M) (cov := cov) hmet hc hc1 hsmC hON hinit hψ).1
      rw [h, sub_self, abs_zero]
      exact hK
    · -- x ≠ p
      obtain ⟨u, s, hu, hs0, hrs, hxs, hsπ, hmodel⟩ :=
        gram_ray_data (I := I) (M := M) (cov := cov) hmet htor hc hε₁ hnum2 hdiam hsmC hHess hcont hx
      by_cases hgood : ∀ (i : Fin (Module.finrank ℝ E + 1)) (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) s →
          -1 + 3 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e i p * Real.cos σ
              + Inner.inner ℝ (rgrad (I := I) (M := M)
                  (fFam (I := I) (M := M) (cov := cov) hmet p e i) p) u * Real.sin σ
      · -- every index is good: the Parseval sum rule
        refine le_trans (sum_rule_good_ray (I := I) (M := M) (cov := cov) hmet hc hε₁ hu hs0.le hsπ hxs
          hON hinit hψ ?_ ?_) ?_
        · intro i
          have h := (hmodel i (hgood i)).1 s ⟨hs0.le, le_rfl⟩
          rwa [hxs] at h
        · intro i
          have h := (hmodel i (hgood i)).2 s ⟨hs0.le, le_rfl⟩
          rwa [hxs] at h
        · have hmono : 0 ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) := by positivity
          exact mul_le_mul_of_nonneg_left (by linarith [hα.le]) hmono
      · -- at least one bad index: the model comparison fails somewhere
        push_neg at hgood
        exact (gb2_bad_branch (I := I) (M := M) (cov := cov) hmet htor hα hα1 hc hc1 hε₁ hnum1
          hnum2 hON hdiam hsmC hHess hcont hgrad hinit hψ (u := u) (s := s) (x := x) hu hs0.le hsπ
          (by rw [hxs]; exact hrs) hxs hmodel hgood hKn hKn2).1
  · -- conclusion (3): the Gram entries
    intro x i j
    by_cases hx : x = p
    · subst hx
      have h := (init_gram (I := I) (M := M) (cov := cov) hmet hc hc1 hsmC hON hinit hψ).2 i j
      rw [h, sub_self, abs_zero]
      exact hK
    · -- x ≠ p
      obtain ⟨u, s, hu, hs0, hrs, hxs, hsπ, hmodel⟩ :=
        gram_ray_data (I := I) (M := M) (cov := cov) hmet htor hc hε₁ hnum2 hdiam hsmC hHess hcont hx
      by_cases hgood : ∀ (k : Fin (Module.finrank ℝ E + 1)) (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) s →
          -1 + 3 * c ≤ fFam (I := I) (M := M) (cov := cov) hmet p e k p * Real.cos σ
              + Inner.inner ℝ (rgrad (I := I) (M := M)
                  (fFam (I := I) (M := M) (cov := cov) hmet p e k) p) u * Real.sin σ
      · -- both indices are good: integrate the derivative of the Gram pairing
        have hpair := gram_along_pair (I := I) (M := M) (cov := cov) hmet htor hc hc1 hε₁
          hu hs0.le hxs hON hsmC hHess hcont hgrad hinit hψ i j ?_
        · refine le_trans hpair ?_
          have h2 : 2 * ε₁ * s ≤ 2 * ε₁ * Real.pi :=
            mul_le_mul_of_nonneg_left hsπ (by linarith)
          have h3 : 0 ≤ 100 * ((Module.finrank ℝ E : ℝ) + 2) * (α + Real.sqrt c) := by
            have : (0:ℝ) ≤ α + Real.sqrt c := by linarith [hα.le, Real.sqrt_nonneg c]
            positivity
          nlinarith [h2, h3, hε₁, Real.pi_pos, hK]
        · -- the two functions of the pair stay above `-1+2c`
          intro σ hσ
          exact ⟨(hmodel i (hgood i)).1 σ hσ,
                 (hmodel j (hgood j)).1 σ hσ⟩
      · -- at least one bad index: the model comparison fails somewhere
        push_neg at hgood
        exact (gb2_bad_branch (I := I) (M := M) (cov := cov) hmet htor hα hα1 hc hc1 hε₁ hnum1
          hnum2 hON hdiam hsmC hHess hcont hgrad hinit hψ (u := u) (s := s) (x := x) hu hs0.le hsπ
          (by rw [hxs]; exact hrs) hxs hmodel hgood hKn hKn2).2 i j

end Work.Diff.C
