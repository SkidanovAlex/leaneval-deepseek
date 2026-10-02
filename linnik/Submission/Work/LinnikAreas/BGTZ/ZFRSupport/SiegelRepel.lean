/-
# Deuring–Heilbronn repulsion for the *other* characters (Heath-Brown 1992, Principle 2)

Target: `Work.LinnikAreas.otherCharRepelSiegel`.  Given a real non-principal character `χ₀` of
level `q` with a real exceptional zero `ρ₀` of minimal `λ = lamOf q ρ = (1 - Re ρ)·log q` (so
`IsMin1 χ₀ ρ₀`) and `λ(ρ₀) ≤ 1/100`, every zero `ρ ≠ ρ₀` of every character `χ ≠ χ₀`, `χ ≠ 1`
with `|Im ρ| ≤ 1` satisfies `c·log(1/λ(ρ₀)) ≤ λ(ρ)` for an absolute `c > 0`.

This is Principle 2 of Heath-Brown (1992) §1 (Linnik's Deuring–Heilbronn phenomenon, refined by
Graham): it is TRUE, and it is the *uncapped* form (no restriction on `λ(ρ)` and no restriction
on `λ(ρ₀)` beyond `≤ 1/100`).  Cf. Benli–Goel–Twiss–Zaman, arXiv:2410.06082, Cor 1.1/1.2, for a
modern explicit form.

## 1. A complete route, assembled from material already PROVED in this workspace

All the analytic machinery of Heath-Brown §5/§6/§8 is available here, and it is enough; the raw
`λ₀`-weighted zero-density estimate used in the first draft below is *not* needed.

Write `λ₀ := lamOf q ρ₀`, `λ := lamOf q ρ`.  The route is:

* **(a) the §6 five-term positivity** `Commons.NumberTheory.Linnik.Ksum_positivity` (PROVED):
  for every `f ≥ 0` supported in `[0,x₀]`,
  `K(β,χ₀) + K(β+iγ,χ) + K(β,1) + ½K(β+iγ,χ₀χ) + ½K(β-iγ,χ₀χ⁻¹) ≥ 0`
  (the curve `χ₀` real forces `γ₀ = Im ρ₀ = 0`), where `K(s,ψ) = Σ' Λ(n)·Re(ψ(n)/n^s)·f(log n/log q)`.

* **(b) the four K-sum bounds** (all PROVED, `scratch_l62app_phi` / `Ksum_principal_le`;
  *window radius `δ` is a free parameter `< 1`*):
  `K(β,1) ≤ L·F(-λ₀) + f(0)εL`, `K(β,χ₀) ≤ -L·F(0) + f(0)(c+ε)L`,
  `K(β+iγ,χ) ≤ -L·F(λ-λ₀) + f(0)(c+ε)L`, `K(β±iγ,χ₀χ^{∓1}) ≤ f(0)(c+ε)L`,
  the required *window maximality* being supplied by `IsMin1` (for window zeros with
  `|Im u| ≤ 1`) and `DhRepel.farZeroLambdaLower` (for `1 ≤ |Im u| ≤ 4`).

* **(c) the L52 (log-derivative) input for a FREE window radius**:
  `DhRepel.l52Hyp_supply` (PROVED by a colleague *after* the first draft of this file) gives
  `L52Hyp χ 2 ε δ` for every `δ ∈ (0,1)`.  Summing (b) with the weights of (a) and dividing
  by `L` then yields Heath-Brown's §8.5/§8.6 inequality
  `0 ≤ F(-λ) - F(0) - F(λ-λ₀) + f(0)(3·2+4ε)`   for every admissible `f`
  (equivalently, since `F(-λ) ≥ F(-λ₀)`: `0 ≤ F(-λ)-F(0)-F(λ-λ₀)+f(0)C`, `C = 6+4ε`).

* **(d) the constant-threshold input for the *real* pair** (`χ² = 1`, `ρ` real):
  `OtherCharRepel.otherCharConstInput` (in this directory; PROVED from the Landau repulsion
  `OtherCharRepel.twoRealCharRepel`) gives `λ ≥ c₀ > 0`; for the non-real case
  `Work.LinnikAreas.siegelZeroFreeRegion` (PROVED) gives `λ ≥ cz > 0`.

* **(e) the extraction**: from (c) with `x₀ := 17`, `C := 6+4ε` (`ε := 1/2`), the elementary
  computation
  `λ₀ ≥ (x₀/2 - C)·λ²·e^{-x₀λ}`  (from `1-e^{-λ t} ≤ λt` and `∫₀^{x₀}t(x₀-t)e^{λt}dt ≤ x₀λ^{-2}e^{x₀λ}`)
  bounds `log(1/λ₀)` above by `x₀λ + |log(x₀/2-C)|`, and with `λ ≥ min(cz,c₀) > 0` in the
  remaining (bounded) range this gives `λ ≥ c·log(1/λ₀)` for an absolute `c > 0`.

Steps (a),(b),(c),(d) are all *proved* in this workspace; only (e) and the assembly of
(a)–(d) are formalisation work, and it requires no new analytic input.  In particular the
`λ₀`-weighted density estimate of §3 below is superseded.

## 1bis. STATUS (what is proved, and exactly where the gap is)

*Proved here*: `siegelLogBound` (Siegel's theorem in logarithmic form: for a real `χ ≠ 1` with a
real zero `β`, `log (1/λ(β)) ≤ (log q)/2`, from `Siegal.lamOf_lower_bound`), and
`largeLambdaRepel` (the target's conclusion for `λ(ρ) ≥ (log q)/2`, with `c = 1`).

*Proved by colleagues in this workspace* (imports available): `OtherCharRepel.twoRealCharRepel`,
`OtherCharRepel.otherCharConstInput` (a *constant* repulsion `c ≤ λ(ρ)` for every zero of every
`χ ≠ χ₀`), `DhRepel.lemma8_5` (HB Lemma 8.5, the five-term inequality evaluated at `β₂`, with the
window radius `δ ≤ √(log log q)/log q`), `DhRepel.l52Hyp_supply` (`L52Hyp χ 2 ε δ` for every
`δ ∈ (0,1)`), `OtherCharRepel.tentLaplaceReNonneg` (Condition 2 for the tent),
`OtherCharRepel.secondMinExistsBox` (existence of the box-minimal second pair).

*The engine at the cap* — **PROVED** as `OtherCharRepel.engineAtCapTent` (weak form,
`λ(ρ₀) ≥ (1/2)·λ(ρ₂)²·e^{-17·λ(ρ₂)}`) and as `OtherCharRepel.engineAtCapTentStrong` (sharp form)
by `fundmath3-linnik-H39-L1679` / `-L1736`:

  for the target's data and a second pair `(χ₂,ρ₂)` with `λ(ρ₂) ≤ √(log log q)`, `λ₀ ≤ λ₂` and
  the radius-`4` maximality, one has
  `256 ≤ λ(ρ₀) · ∫₀^{32} t(32-t)·e^{λ(ρ₂)·t} dt`
  (the sharp form; the tent `f = (32-t)₊` with `Ksum_le_single_ne_of_L52_phi`, `c = 2`,
  `ε = 1/64`, `δ = 1/2`, which actually yields the constant `318`), and hence the weak form
  `λ(ρ₀) ≥ 8·λ(ρ₂)²·e^{-32·λ(ρ₂)}`.

  This is exactly HB §8.6 (with the cruder constants of this workspace), and it is the *only*
  regime in which the smoothed explicit formula of this workspace can be evaluated at
  `β₂ = Re ρ₂`: the K-sum bounds `Ksum_le_*` require `|Re s - 1| ≤ √(log log q)/log q`, i.e.
  `λ ≤ √(log log q)`.  **Use the sharp form for the assembly**: from `256 ≤ λ₀·G(λ₂)`,
  `G(λ₂) := ∫₀^{32} t(32-t)e^{λ₂ t}`, together with `λ₀ ≤ 1/100` (so `G(λ₂) ≥ 25600`) one gets
  `λ₂ ≥ 0.23` and then `log(1/λ(ρ₀)) ≤ log(G(λ₂)/256) ≤ c·λ(ρ₂)` for an absolute `c`
  (`G` is increasing, `G(λ₂) ≤ 32 e^{32λ₂}/λ₂²`, and `λ₂ ≥ 0.23` bounds the `2 log(1/λ₂)` term).
  *Do not* use the weak form for the assembly: for `λ₂ → 0` it only gives
  `log(1/λ₀) ≤ 32λ₂ + 2log(1/λ₂)`, which cannot be turned into `c·log(1/λ₀) ≤ λ(ρ)` with an
  absolute `c`.

*The gap* (this is the honest reason the target is not assembled here).  The target needs
`log(1/λ(ρ₀)) ≤ c·λ(ρ)` for *every* other-character zero with `|Im ρ| ≤ 1`.  Splitting on
`λ(ρ)`:

* `λ(ρ) ≥ (log q)/2`: `log(1/λ(ρ₀)) ≤ (log q)/2 ≤ λ(ρ)` — done here (`largeLambdaRepel`);
* `λ(ρ) ≤ √(log log q)`: the engine at the cap — done modulo `engineAtCapTent`;
* `√(log log q) < λ(ρ) < (log q)/2`: **open**.  In this range the K-sum bounds cannot be
  evaluated at `β₂ = Re ρ` (the evaluation-window condition `|1-β₂| ≤ √(log log q)/log q` fails),
  and every *proved* zero-count/positivity tool in this workspace is either `σ`-blind or else
  requires the evaluation point at distance `≤ √(log log q)/log q` from `1`.  The only route
  within reach of HB §5-§8 is to evaluate the five-term positivity at a point `s` with
  `Re s = 1 - λ₀/log q` (so that the growth `e^{λ(ρ)t}` is visible), and that requires the
  log-derivative bound `L52Hyp` (equivalently HB Lemma 3.1 / Lemma 5.2) at a point a *fixed*
  distance below `1`, which the workspace's `lemma5_2_of_logDeriv_bound_param_free` obtains only
  via the shift `s ↦ 1+η+i·Im s` with `η = 1/(log q log log q)`; the price of that shift is the
  factor `e^{(1-Re s)·log q·x₀}` in the regularity constant `A(g)` of `g(t) = e^{αt}f(t)`, which
  the log-derivative slack `f(0)ε·log q` can absorb only while `(1-Re s)·log q ≲ log log q`.
  The missing mathematics is therefore a genuinely different tool: Graham's Selberg-sieve proof of
  Principle 2 (Linnik 1944; Graham, thesis 1977; the modern explicit form is
  Benli–Goel–Twiss–Zaman, arXiv:2410.06082, Cor. 1.1/1.2), or the `λ₁`-saving log-free
  zero-density estimate (Bombieri, *Le grand crible*, Thm. 14; Jutila 1977).  Both are recorded in
  this workspace as irreducible deep inputs (`SiegelBase.PairDensityInput`,
  `LinnikAreas.OtherCharRepel.otherCharDensityInput`); this is also the conclusion recorded in
  `LinnikAreas/repelOtherNeDH.lean` and in `LinnikPlan/ROUTE_LEAD.md` §Z5, where the project's
  own Route only consumes the capped (`λ₁ ≥ lamS`) form.

## 2. What is proved in this file

`tentFun`, `tentLaplace`, `tentLaplace_zero`, `re_mem_strip_of_zeroMult` (proved here), and the
reduction of §3 (proved here, from one documented deep input).  The tent's Condition 2
(`Re F(z) ≥ 0` for `Re z ≥ 0`), needed for (b), is
`OtherCharRepel.tentLaplaceReNonneg` (proved, this directory).

## 3. The first-draft reduction (kept for the record)

The statement is *reduced* to the single deep input

  `OtherCharRepel.otherCharDensityInput`
  — the `λ₀`-saving ("Deuring–Heilbronn") log-free zero-density estimate for the zeros of the
  other characters in the working region `|Im| ≤ 1`: the multiplicity-weighted number of pairs
  `(χ, ρ)` with `χ ≠ χ₀, 1`, `ρ ≠ ρ₀`, `|Im ρ| ≤ 1` and `λ(ρ) ≤ t` is at most
  `C·λ(ρ₀)·e^{ct}` (`C, c` absolute).

This is the input recorded as irreducible in `SiegelBase.DensityInput` / `PairDensityInput`
(Bombieri, *Le grand crible*, Thm. 14; Jutila; `area6.lean` §7 "true but not a provable lemma
here"); the delegated prover of `otherCharDensityInput` judged it mis-scoped as a *closed*
lemma of this development (its singleton instance is the target itself).  The reduction is:
applying the estimate to the singleton `s = {(χ, ρ)}` with `t = λ(ρ)` gives

  `1 ≤ C·λ(ρ₀)·e^{c·λ(ρ)}`   hence   `log(1/λ(ρ₀)) − log C ≤ c·λ(ρ)`,

and then `λ(ρ) ≥ c₁·log(1/λ(ρ₀))` with `c₁ = min (1/(2c)) (e^{-2K}/(2K))`, `K = max 1 (log C)`:
for `log(1/λ(ρ₀)) ≥ 2K` this is the first bound, and otherwise `λ(ρ₀) > e^{-2K}` and `IsMin1`
gives `λ(ρ) ≥ λ(ρ₀) > e^{-2K} ≥ (e^{-2K}/(2K))·log(1/λ(ρ₀))`.

## 1quater. What is now PROVED here, and the precise remaining gap (session 4)

*Proved in this file, sorry-free*:

* `engineExtract`: the arithmetic extraction from the engine inequality.  From
  `256 ≤ λ₀ · ∫₀³² t(32-t) e^{λ₂t} dt`, `0 < λ₀ ≤ 1/100` and `0 < λ₂` one gets
  `(1/128)·log(1/λ₀) ≤ λ₂`.  Proof: `λ₀ ≤ 1/100` gives `G := ∫₀³²t(32-t)e^{λ₂t} ≥ 25600`, while
  `t(32-t)e^{λ₂t} ≤ t(32-t)e^{32λ₂}` on `[0,32]` gives `G ≤ (16384/3)e^{32λ₂}`; hence
  `e^{32λ₂} ≥ 25600·3/16384 = 4.6875 > 4`, so `32λ₂ ≥ log 4 ≥ 1.38`.  Finally
  `log(1/λ₀) = log G - log(λ₀G) ≤ log G - log 256 ≤ 32λ₂ + log(64/3) ≤ 32λ₂ + 4 ≤ 128λ₂`.
  (The constants are deliberately wasteful; a sharper extraction is possible.)
* `otherCharRepelSiegel_engine`: **the target's conclusion `(1/128)·log(1/λ(ρ₀)) ≤ λ(ρ)` from the
  existence of a pair `(χ₂,ρ₂)` satisfying the hypotheses of `OtherCharRepel.engineAtCapTentStrong`
  together with `λ(ρ₂) ≤ λ(ρ)`.**  This is the complete assembly of HB §8 (engine + arithmetic);
  what it does not contain is the *construction* of the "second maximum" pair.

*Proved by colleagues and used above / available*: `OtherCharRepel.engineAtCapTentStrong`
(the sharp engine, hypotheses: `χ₂ ≠ χ₀,1`, `zeroMult ≠ 0`, `|ρ₂.im| ≤ 2`, `λ(ρ₀) ≤ λ(ρ₂)`,
`λ(ρ₂) ≤ √(log log q)`, and the radius-`4` minimality), and (this session, file
`Submission/Work/OtherCharRepel/engineAtCapTentBall.lean`, module
`Submission.Work.OtherCharRepel.engineAtCapTentBall`) `Work.OtherCharRepel.engineAtCapTentBall` — the same engine with
the *ball* minimality `|u.im| ≤ |ρ₂.im| + 1` and the guard `|ρ₂.im| + 1 ≤ 10 log q` (a genuine
strengthening of the usable hypothesis: the radius-`4` form follows from the ball form whenever
`|ρ₂.im| ≤ 3`).

*The remaining gap, precisely.*  The capped case `λ(ρ) ≤ √(log log q)` needs the "second maximum"
pair.  Write `W(H) := {(ψ,u) : ψ ≠ 1, zeroMult ψ u ≠ 0, |u.im| ≤ H, (ψ,u) ≠ (χ₀,ρ₀)}` and
`m(H) := min_{W(H)} λ`.  Since `(χ,ρ) ∈ W(4)`, `m(4) ≤ λ(ρ) ≤ √(log log q)`.
* If some minimiser of `W(4)` has `χ₂ ≠ χ₀` and `|ρ₂.im| ≤ 3`, then `λ(ρ₂) = m(4)` is the
  minimum over `W(4) ⊇` the ball of radius `|ρ₂.im| + 1`, so the *ball* engine applies and
  `engineExtract` finishes the capped case.  (The radius-`4` engine would need `|ρ₂.im| ≤ 2`.)
* If instead *every* minimiser of `W(4)` with `|u.im| ≤ 3` is a zero `u₀ ≠ ρ₀` of `χ₀`, then
  `u₀` is a zero of `χ₀` with `|u₀.im| ≤ 3`, `λ(u₀) = m(4) ≤ λ(ρ)`, and the ball-minimality
  `∀ψ u, ψ ≠ 1 → ... → |u.im| ≤ |u₀.im| + 1 → (ψ,u) ≠ (χ₀,ρ₀) → λ(u₀) ≤ λ(u)` (the ball
  is contained in `W(4)`).  For such a `u₀` the *same-character* Deuring–Heilbronn bound applies:
  `Work.OtherCharRepel.sameCharRepelLogBoundPublic` (the public form of the private
  `sameCharRepelLogBound` of `sameCharNonRealRepel.lean`; requested this session at path
  `Submission/Work/OtherCharRepel/`) gives, when `|u₀.im| ≤ 1` and
  `λ(u₀) ≤ log log log q / 3`, that `log(1/λ₀) ≤ 8λ(u₀) + log(64/3)`; combined with the
  *constant* repulsion `OtherCharRepel.otherCharRepelConst` (`λ(ρ) ≥ 1/25`) this again gives the
  target's conclusion with an absolute `c`.
* The residual configurations are: (i) all minimisers of `W(4)` lie in the shell
  `3 < |u.im| ≤ 4` (then `m(4) ≥ 1/25` and the argument has to be run at a larger height `H`,
  with the same dichotomy repeating — this is a boundary bookkeeping problem, not new
  mathematics); (ii) the same-character zero `u₀` has `1 < |u₀.im| ≤ 3` or
  `λ(u₀) > log log log q / 3`, where the *local* same-character bound
  (`DhRepel.otherCharRepel.sameCharRepelLogBound`-style, valid only under
  `λ ≤ log log log q/3`) is unavailable and the *wide* one
  (`DhTriangleNear`-style, needs the maximality over the full height `10 log q`) does not apply
  either.

*Beyond the cap*: for `√(log log q) < λ(ρ) < (log q)/2` the K-sum bounds
`Ksum_le_*_of_L52_phi` are unavailable at `β₂ = Re ρ` (they need
`|1 - Re s| ≤ √(log log q)/log q`), which is intrinsic to HB §5–§8 (the `α`-shift of
`lemma5_2_of_logDeriv_bound_param_free` costs `e^{(1-Re s)·log q·x₀}`).  Closing that range needs
Graham's Selberg-sieve proof of Principle 2 (Linnik 1944; Graham 1977; Benli–Goel–Twiss–Zaman,
arXiv:2410.06082) or the `λ₁`-saving log-free zero-density estimate (Bombieri, *Le grand crible*,
Thm. 14; Jutila 1977) — the deep inputs already recorded as `SiegelBase.PairDensityInput`,
`OtherCharRepel.otherCharDensityInput` and consumed by the Route (`ROUTE_LEAD.md` §Z5) through the
capped form `Work.LinnikAreas.repelOtherNeDH_capped`.

The statement of the target is TRUE (HB92 Principle 2); it is *not* to be declared false.
-/
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Work.LinnikAreas.OtherCharRepel.otherCharDensityInput
import Submission.Work.LinnikAreas.OtherCharRepel.engineAtCapTentStrong
import Submission.Work.OtherCharRepel.engineAtCapTentBall
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_TuranOther_twUpper
import Submission.Work.LinnikAreas.BGTZ.ZFRSupport.TuranAssembly
import Submission.Work.LinnikAreas.TuranOther.multL_ne_zero
import Submission.Work.LinnikAreas.TuranOther.turanArith
import Submission.Work.LinnikAreas.DhCapped.offAxisLambdaLower
import Submission.Work.LinnikAreas.LFunction_eq_zero_of_zeroMult

open scoped Real
open DirichletCharacter

namespace Work.LinnikAreas

/-- The tent test function of Heath-Brown (1992), §8: `f(t) = max (x₀ - t) 0`,
supported on `[0, x₀]`. -/
noncomputable def tentFun (x₀ t : ℝ) : ℝ := max (x₀ - t) 0

/-- The Laplace transform of the tent at a real argument:
`F(x₀, λ) = ∫₀^{x₀} e^{-λ t} (x₀ - t) dt`. -/
noncomputable def tentLaplace (x₀ lam : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..x₀, Real.exp (-lam * t) * (x₀ - t)

/-- The tent Laplace transform at `0` is `x₀²/2`. -/
theorem tentLaplace_zero (x₀ : ℝ) : tentLaplace x₀ 0 = x₀ ^ 2 / 2 := by
  simp only [tentLaplace, neg_zero, zero_mul, Real.exp_zero, one_mul]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id]
  rw [intervalIntegral.integral_const, integral_id]
  ring

/-- A `zeroMult`-zero of a non-principal character lies in the open critical strip. -/
theorem re_mem_strip_of_zeroMult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hχ : χ ≠ 1) (hz : Work.LinnikContract.zeroMult χ ρ ≠ 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hψne : χ.primitiveCharacter ≠ 1 := by
    intro h1
    refine hχ ?_
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hlt : analyticOrderNatAt (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ
      ≠ 0 := by
    simpa only [Work.LinnikContract.zeroMult] using hz
  exact Commons.NumberTheory.Linnik.completedL_zero_strip χ.primitiveCharacter hψne
    (DirichletCharacter.primitiveCharacter_isPrimitive χ)
    (apply_eq_zero_of_analyticOrderNatAt_ne_zero hlt)


/-! ## The two cases that are provable with the material already in the workspace

The target splits into `λ(ρ) ≥ log q/2` (Siegel) and `λ(ρ) < log q/2` (the
Deuring–Heilbronn engine).  The first case is discharged here. -/

/-- **Siegel's theorem in logarithmic form.**  For a real non-principal character `χ` mod `q`
with a real zero `β < 1` one has `log (1/λ(β)) ≤ (log q)/2`, where `λ(β) = (1-β)log q`.

This is the only use of the ineffective Siegel bound in the Deuring–Heilbronn analysis: it shows
that the exceptional zero can never be further than `q^{-1/2}` from `σ = 1`, whence for a zero
`ρ` of any other character with `λ(ρ) ≥ (log q)/2` the repulsion `log(1/λ(ρ₀)) ≤ λ(ρ)` is
immediate.  It is proved from `Siegal.lamOf_lower_bound` (`λ(β) ≥ C log q/√q`), which is the
Siegel theorem `1 - β ≥ C q^{-1/2}` for the primitive character inducing `χ`. -/
theorem siegelLogBound : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q) (β : ℝ),
    χ ≠ 1 → χ ^ 2 = 1 → β < 1 → Work.LinnikContract.zeroMult χ (β : ℂ) ≠ 0 →
    Real.log (1 / Work.LinnikContract.lamOf q (β : ℂ)) ≤ (1 / 2) * Real.log q := by
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.Siegel.lamOf_lower_bound
  refine ⟨⌈Real.exp (1 / C)⌉₊ + 2, ?_⟩
  intro q hq _inst χ β hχ hsq hβ hz
  have hq2 : 2 ≤ q := le_trans (Nat.le_add_left 2 _) hq
  have hqpos : 0 < q := by omega
  have hq1 : 1 < q := by omega
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq1)
  have hexp_le : Real.exp (1 / C) ≤ (q : ℝ) := by
    have h1 : Real.exp (1 / C) ≤ (⌈Real.exp (1 / C)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp (1 / C)⌉₊ : ℝ) ≤ ((⌈Real.exp (1 / C)⌉₊ + 2 : ℕ) : ℝ) := by
      push_cast; linarith only []
    have h3 : ((⌈Real.exp (1 / C)⌉₊ + 2 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith only [h1, h2, h3]
  have hCq : 1 ≤ C * Real.log q := by
    have h1 : 1 / C ≤ Real.log q := by
      have h := Real.log_le_log (Real.exp_pos (1 / C)) hexp_le
      rwa [Real.log_exp] at h
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hCpos)
    have h3 : C * (1 / C) = 1 := by field_simp
    rwa [h3] at h2
  have hlow := hC q hq2 χ β hχ hsq hβ hz
  have hlampos : 0 < Work.LinnikContract.lamOf q (β : ℂ) :=
    Work.LinnikAreas.Siegel.lamOf_pos hχ hβ hz
  have hsqrtpos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hqpos)
  have hargpos : 0 < C * Real.log q / Real.sqrt (q : ℝ) :=
    div_pos (mul_pos hCpos hlogq) hsqrtpos
  have hstep1 : 1 / Work.LinnikContract.lamOf q (β : ℂ)
      ≤ 1 / (C * Real.log q / Real.sqrt (q : ℝ)) := by
    rw [one_div, one_div]
    exact (inv_le_inv₀ hlampos hargpos).mpr hlow
  have hstep2 : Real.log (1 / Work.LinnikContract.lamOf q (β : ℂ))
      ≤ Real.log (1 / (C * Real.log q / Real.sqrt (q : ℝ))) :=
    Real.log_le_log (div_pos one_pos hlampos) hstep1
  have hval : Real.log (1 / (C * Real.log q / Real.sqrt (q : ℝ)))
      = (1 / 2) * Real.log q - Real.log C - Real.log (Real.log q) := by
    rw [one_div, Real.log_inv,
      Real.log_div (mul_ne_zero (ne_of_gt hCpos) (ne_of_gt hlogq)) (ne_of_gt hsqrtpos),
      Real.log_mul (ne_of_gt hCpos) (ne_of_gt hlogq),
      Real.log_sqrt (le_of_lt (by exact_mod_cast hqpos))]
    ring
  have hlogprod : 0 ≤ Real.log C + Real.log (Real.log q) := by
    have h1 : Real.log 1 ≤ Real.log (C * Real.log q) := Real.log_le_log (by norm_num) hCq
    rw [Real.log_one, Real.log_mul (ne_of_gt hCpos) (ne_of_gt hlogq)] at h1
    linarith only [h1]
  linarith only [hstep2, hval, hlogprod]

/-- **The large-`λ` case of the target.**  If `ρ₀` is a real zero (`ρ₀.im = 0`) of a real
character `χ₀` and `λ(ρ) ≥ (log q)/2`, then `log(1/λ(ρ₀)) ≤ λ(ρ)` — i.e. the requested repulsion
holds with the constant `c = 1`.  Nothing about `IsMin1` or about `χ` is needed here. -/
theorem largeLambdaRepel : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    χ₀ ≠ 1 → χ₀ ^ 2 = 1 → ρ₀.im = 0 → Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 →
    ∀ (ρ : ℂ), (1 / 2) * Real.log q ≤ Work.LinnikContract.lamOf q ρ →
    (1 : ℝ) * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨q₀, hq₀⟩ := siegelLogBound
  refine ⟨max q₀ 3, ?_⟩
  intro q hq _inst χ₀ ρ₀ hχ₀ hsq him hz ρ hlam
  have hq' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hρ : ρ₀ = ((ρ₀.re : ℝ) : ℂ) := Complex.ext rfl (by rw [him]; simp)
  have hz' : Work.LinnikContract.zeroMult χ₀ ((ρ₀.re : ℝ) : ℂ) ≠ 0 := by
    rwa [← hρ]
  have hβ : ρ₀.re < 1 := (re_mem_strip_of_zeroMult hχ₀ hz).2
  have hS := hq₀ q hq' χ₀ ρ₀.re hχ₀ hsq hβ hz'
  rw [← hρ] at hS
  linarith only [hS, hlam]


/-! ## §1ter.  The Deuring–Heilbronn engine, and the arithmetic extraction

`OtherCharRepel.engineAtCapTentStrong` (proved in this directory, sorry-free) is Heath-Brown's
Lemma 8.5 at the tent test function of width `32`: for the target's data and *any* second pair
`(χ₂,ρ₂)` with `χ₂ ≠ χ₀, 1`, `zeroMult χ₂ ρ₂ ≠ 0`, `|Im ρ₂| ≤ 2`, `λ(ρ₀) ≤ λ(ρ₂)`,
`λ(ρ₂) ≤ √(log log q)` and the radius-`4` minimality

  `∀ ψ u, ψ ≠ 1 → zeroMult ψ u ≠ 0 → |u.im| ≤ 4 → (ψ,u) ≠ (χ₀,ρ₀) → λ(ρ₂) ≤ λ(u)`

one has `256 ≤ λ(ρ₀) · ∫₀³² t (32-t) e^{λ(ρ₂)t} dt`.  Below we extract from this the
*logarithmic* repulsion `λ(ρ) ≥ (1/128)·log(1/λ(ρ₀))` whenever `λ(ρ) ≥ λ(ρ₂)`.

The point of the extraction (`engineExtract`) is that the two constants are harmless: from
`256 ≤ λ₀ G` and `λ₀ ≤ 1/100` one gets `G ≥ 25600`, while `G ≤ (16384/3) e^{32λ₂}` by
`t(32-t)e^{λ₂t} ≤ t(32-t)e^{32λ₂}` on `[0,32]`; hence `e^{32λ₂} ≥ 25600·3/16384 = 4.6875 > 4`
and therefore `32λ₂ ≥ log 4 ≥ 1.38`.  Then
`log(1/λ₀) ≤ log G - log 256 ≤ 32λ₂ + log(64/3) ≤ 32λ₂ + 4 ≤ 128λ₂`. -/

/-- `log (64/3) ≤ 4`. -/
private lemma log_sixtyFour_thirds_le_four : Real.log ((64 : ℝ) / 3) ≤ 4 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have he : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  have hpow : (2.7182818283 : ℝ) ^ 4 < Real.exp 1 ^ 4 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have hnum : ((64 : ℝ) / 3) < (2.7182818283 : ℝ) ^ 4 := by norm_num
  linarith only [hpow]

/-- **Numeric extraction from the §8 engine.**  If `0 < λ₀ ≤ 1/100`, `0 < λ₂` and
`256 ≤ λ₀ · ∫₀³² t(32-t) e^{λ₂t} dt`, then `(1/128)·log(1/λ₀) ≤ λ₂`. -/
theorem engineExtract {lam₀ lam₂ : ℝ} (h₀ : 0 < lam₀) (h₁ : lam₀ ≤ 1 / 100) (h₂ : 0 < lam₂)
    (h : 256 ≤ lam₀ * (∫ t in (0:ℝ)..32, t * (32 - t) * Real.exp (lam₂ * t))) :
    (1 / 128) * Real.log (1 / lam₀) ≤ lam₂ := by
  set G : ℝ := ∫ t in (0:ℝ)..32, t * (32 - t) * Real.exp (lam₂ * t) with hG
  have h256 : (256 : ℝ) ≤ lam₀ * G := h
  have hGge : 25600 ≤ G := by nlinarith only [h256, h₁, h₀, h]
  -- the upper bound `G ≤ (16384/3) e^{32λ₂}`
  have hGle : G ≤ (16384 / 3) * Real.exp (32 * lam₂) := by
    have hpt : ∀ t ∈ Set.Icc (0:ℝ) 32,
        t * (32 - t) * Real.exp (lam₂ * t) ≤ t * (32 - t) * Real.exp (32 * lam₂) := by
      intro t ht
      have hexp : Real.exp (lam₂ * t) ≤ Real.exp (32 * lam₂) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [ht.1, ht.2, h₂, h₀, h₁, ht]
      exact mul_le_mul_of_nonneg_left hexp (by nlinarith only [ht.1, ht.2, h₀, h₁, ht])
    have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (a := (0:ℝ)) (b := 32) (by norm_num)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop) hpt
    have hint0 : (∫ t in (0:ℝ)..32, t * (32 - t)) = 16384 / 3 := by
      rw [show (fun t : ℝ => t * (32 - t)) = fun t => 32 * t - t ^ 2 by ext t; ring]
      rw [intervalIntegral.integral_sub (f := fun t : ℝ => 32 * t) (g := fun t : ℝ => t ^ 2)
          ((continuous_const.mul continuous_id).intervalIntegrable _ _)
          ((continuous_id.pow 2).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, integral_id, integral_pow]
      norm_num
    have hint : (∫ t in (0:ℝ)..32, t * (32 - t) * Real.exp (32 * lam₂))
        = (16384 / 3) * Real.exp (32 * lam₂) := by
      rw [intervalIntegral.integral_mul_const, hint0]
    rw [hG]
    exact le_trans hmono (le_of_eq hint)
  -- hence `32 λ₂ ≥ log 4 ≥ 1.38`
  have h4 : (4 : ℝ) ≤ Real.exp (32 * lam₂) := by
    have h1 : (25600 : ℝ) ≤ (16384 / 3) * Real.exp (32 * lam₂) := le_trans hGge hGle
    have h2 : (25600 : ℝ) / (16384 / 3) ≤ Real.exp (32 * lam₂) := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 16384 / 3)]
      linarith only [hGge, hGle]
    have h3 : (4 : ℝ) ≤ 25600 / (16384 / 3) := by norm_num
    linarith only [h₀, h₁, hGge, hGle]
  have hlog4 : Real.log 4 ≤ 32 * lam₂ := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 4)]
    exact h4
  have hlog4' : (1.38 : ℝ) ≤ Real.log 4 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [h2]; linarith only [Real.log_two_gt_d9, h₀, h₁]
  have hlam : (0.043 : ℝ) ≤ lam₂ := by linarith only [hlog4, hlog4', h₀, h₁]
  -- the main estimate
  have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hGge
  have hlog256 : Real.log (256 : ℝ) ≤ Real.log (lam₀ * G) := Real.log_le_log (by norm_num) h256
  rw [Real.log_mul (ne_of_gt h₀) (ne_of_gt hGpos)] at hlog256
  have hbound : Real.log (1 / lam₀) ≤ 32 * lam₂ + 4 := by
    have hGu : Real.log G ≤ 32 * lam₂ + Real.log ((16384 : ℝ) / 3) := by
      have h1 : Real.log G ≤ Real.log ((16384 / 3) * Real.exp (32 * lam₂)) :=
        Real.log_le_log hGpos hGle
      rw [Real.log_mul (by norm_num : (16384:ℝ) / 3 ≠ 0) (ne_of_gt (Real.exp_pos _)),
        Real.log_exp] at h1
      linarith only [h1]
    have h2 : Real.log ((16384 : ℝ) / 3) = Real.log ((64 : ℝ) / 3) + Real.log 256 := by
      rw [show (16384 : ℝ) / 3 = (64 / 3) * 256 by norm_num,
        Real.log_mul (by norm_num : (64:ℝ)/3 ≠ 0) (by norm_num : (256:ℝ) ≠ 0)]
    have hloginv : Real.log (1 / lam₀) = -Real.log lam₀ := by rw [one_div, Real.log_inv]
    have h3 := log_sixtyFour_thirds_le_four
    rw [hloginv]
    linarith only [hlog256, hGu, h2, h3]
  have habs : (4 : ℝ) ≤ 96 * lam₂ := by linarith only [hlam, h₀, h₁, hlog4, hlog4']
  calc (1 / 128) * Real.log (1 / lam₀)
      ≤ (1 / 128) * (32 * lam₂ + 4) := by
        exact mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ ≤ lam₂ := by linarith only [habs, h₀, h₁, hlog4, hlog4']

/-- A non-principal character of level `q ≠ 0` forces `2 ≤ q`. -/
private lemma two_le_of_ne_one_level {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (h : χ ≠ 1) : 2 ≤ q := by
  by_contra hq
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : q = 1 := by omega
  exact h (DirichletCharacter.level_one' χ hq1)

/-- **The target's conclusion from the engine's pair.**  Given the target's data and a second pair
`(χ₂,ρ₂)` satisfying the hypotheses of Heath-Brown's Lemma 8.5 *in the form proved in this
workspace* (`OtherCharRepel.engineAtCapTentStrong`), one gets the requested repulsion with the
absolute constant `1/128`:

  `(1/128)·log(1/λ(ρ₀)) ≤ λ(ρ)`.

This is the assembly of the §8 engine with the arithmetic extraction `engineExtract`; what is *not*
included is the construction of the pair `(χ₂,ρ₂)` (the "second maximum" of Heath-Brown §6), which
is the remaining input of the capped case — see the STATUS section of the module header. -/
theorem otherCharRepelSiegel_engine : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), χ ≠ χ₀ → χ ≠ 1 →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₀ →
      (∃ (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ),
        χ₂ ≠ χ₀ ∧ χ₂ ≠ 1 ∧ Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 ∧
        Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q ρ₂ ∧
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ ∧
        Work.LinnikContract.lamOf q ρ₂ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) ∧
        |ρ₂.im| ≤ 2 ∧
        (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 →
          Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ 4 → (ψ, u) ≠ (χ₀, ρ₀) →
            Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u)) →
      (1 / 128) * Real.log (1 / Work.LinnikContract.lamOf q ρ₀)
        ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨qE, hE⟩ := OtherCharRepel.engineAtCapTentStrong
  refine ⟨qE, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hsq him hlam χ ρ hχχ₀ hχ1 hzm himρ hneρ hpair
  obtain ⟨χ₂, ρ₂, hχ₂χ₀, hχ₂1, hzm₂, hle0, hle1, hcap, him₂, hminimal⟩ := hpair
  have hq2 : 2 ≤ q := two_le_of_ne_one_level hχ1
  have hlam0pos : 0 < Work.LinnikContract.lamOf q ρ₀ :=
    (OtherCharRepel.zeroMultStripPos hq2 hmin.1.1 hmin.1.2.1).2.2
  have hlam2pos : 0 < Work.LinnikContract.lamOf q ρ₂ :=
    (OtherCharRepel.zeroMultStripPos hq2 hχ₂1 hzm₂).2.2
  have h := hE q hq χ₀ ρ₀ χ₂ ρ₂ hmin hsq him hlam hχ₂χ₀ hχ₂1 hzm₂ him₂ hle0 hcap hminimal
  have hext := engineExtract hlam0pos hlam hlam2pos h
  linarith only [hext, hle1]


/-- **The target's conclusion from the *ball*-minimal engine pair.**

Same as `otherCharRepelSiegel_engine`, but with the (weaker, hence more applicable) hypotheses of
`Work.OtherCharRepel.engineAtCapTentBall`: the ball minimality `λ(ρ₂) ≤ λ(u)` for all zeros `u`
with `|u.im| ≤ |ρ₂.im| + 1` (instead of the radius-`4` minimality), and the height guard
`|ρ₂.im| + 1 ≤ 10 log q` in place of `|ρ₂.im| ≤ 2`. -/
theorem otherCharRepelSiegel_engineBall : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), χ ≠ χ₀ → χ ≠ 1 →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₀ →
      (∃ (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ),
        χ₂ ≠ χ₀ ∧ χ₂ ≠ 1 ∧ Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 ∧
        Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q ρ₂ ∧
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ ∧
        Work.LinnikContract.lamOf q ρ₂ ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) ∧
        |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) ∧
        (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 →
          Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ |ρ₂.im| + 1 →
          (ψ, u) ≠ (χ₀, ρ₀) →
            Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u)) →
      (1 / 128) * Real.log (1 / Work.LinnikContract.lamOf q ρ₀)
        ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨qE, hE⟩ := Work.OtherCharRepel.engineAtCapTentBall
  refine ⟨qE, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hsq him hlam χ ρ hχχ₀ hχ1 hzm himρ hneρ hpair
  obtain ⟨χ₂, ρ₂, hχ₂χ₀, hχ₂1, hzm₂, hle0, hle1, hcap, hguard, hminimal⟩ := hpair
  have hq2 : 2 ≤ q := two_le_of_ne_one_level hχ1
  have hlam0pos : 0 < Work.LinnikContract.lamOf q ρ₀ :=
    (OtherCharRepel.zeroMultStripPos hq2 hmin.1.1 hmin.1.2.1).2.2
  have hlam2pos : 0 < Work.LinnikContract.lamOf q ρ₂ :=
    (OtherCharRepel.zeroMultStripPos hq2 hχ₂1 hzm₂).2.2
  have h := hE q hq χ₀ ρ₀ χ₂ ρ₂ hmin hsq him hlam hχ₂χ₀ hχ₂1 hzm₂ hle0 hcap hguard hminimal
  have hext := engineExtract hlam0pos hlam hlam2pos h
  linarith only [hext, hle1]

/-! ## §1quinquies.  The Turán/Hadamard route to the *uncapped* repulsion

With the twisted Hadamard upper bound (`Work.LinnikAreas.TuranOther.twUpper`, available in this
`rect`-compatible family as
`Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_TuranOther_twUpper`) and the mass
bound below, the Turán/Hadamard argument (`Work.LinnikAreas.turanStep`) gives the repulsion for
*every* zero of every other character with `|Im ρ| ≤ 1` -- no cap on `λ(ρ)`.  This is the route
that replaces the deep `otherCharDensityInput` used by the first-draft proof of the target. -/

/-- `log 105 ≤ 5`. -/
private lemma log_105_le_five : Real.log (105 : ℝ) ≤ 5 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 105)]
  have he : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [he]
  have hpow : (2.7182818283 : ℝ) ^ 5 < Real.exp 1 ^ 5 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have hnum : (105 : ℝ) < (2.7182818283 : ℝ) ^ 5 := by norm_num
  linarith only [hpow]

/-- **The twisted mass bound from the single-character mass bound.**

If for every level `q`, character `ψ` and `Re w ≥ 3/2` the multiplicity-weighted inverse-square
zero sum of `ζ · L(·,ψ)` is `≤ C (log q + log (2+‖w‖) + 2)`, then the twisted Turán mass bound
holds: for every `3 ≤ q` and every `1 ≤ α ≤ 100`, `|γ| ≤ 2`, the family
`u ↦ twMult(u)/‖1+α-u‖²` is summable with total `≤ (24C+100)(log q + 1)`.

Proof: `twMult` is bounded pointwise by the sum of the multiplicities of the four functions
`ζ, L(·,χ₀), L(·+iγ,χ), L(·+iγ,χ₀χ)`; the first two are bounded by the single-character mass
bound at `w = 1+α`, and the last two, after the change of variable `u ↦ u + iγ`, by the
single-character mass bound at `w = 1+α+iγ`. -/
theorem twMassCore_of_single
    (h : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) (w : ℂ),
      (3 / 2 : ℝ) ≤ w.re →
      Summable (fun u : ℂ =>
          ((TuranOther.multZeta u : ℝ) + (TuranOther.multL ψ u : ℝ)) / ‖w - u‖ ^ 2) ∧
      (∑' u : ℂ, ((TuranOther.multZeta u : ℝ) + (TuranOther.multL ψ u : ℝ)) / ‖w - u‖ ^ 2)
        ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2)) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ α : ℝ),
      1 ≤ α → α ≤ 100 → |γ| ≤ 2 →
      Summable (fun u : ℂ => ((TuranOther.twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 + (α : ℂ)) - u‖ ^ 2) ∧
      (∑' u : ℂ, ((TuranOther.twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 + (α : ℂ)) - u‖ ^ 2)
        ≤ C' * (Real.log (q : ℝ) + 1) := by
  obtain ⟨C, hCpos, hC⟩ := h
  refine ⟨24 * C + 100, by positivity, ?_⟩
  intro q hqinst hq3 χ₀ χ β₀ γ α hα1 hα100 hγ
  haveI : NeZero q := hqinst
  set s : ℂ := 1 + (α : ℂ) with hsdef
  set c : ℂ := Complex.I * (γ : ℂ) with hcdef
  have hsre : (3 / 2 : ℝ) ≤ s.re := by rw [hsdef]; simp; linarith only [hα1]
  have hcre : c.re = 0 := by rw [hcdef]; simp
  have hscre : (3 / 2 : ℝ) ≤ (s + c).re := by
    rw [Complex.add_re, hcre, add_zero]; exact hsre
  have hcnorm : ‖c‖ = |γ| := by rw [hcdef]; simp
  -- the three single-character mass bounds
  obtain ⟨hsum1, hbnd1⟩ := hC q χ₀ s hsre
  obtain ⟨hsumχ, hbndχ⟩ := hC q χ (s + c) hscre
  obtain ⟨hsumχχ, hbndχχ⟩ := hC q (χ₀ * χ) (s + c) hscre
  -- extract the `multL` halves (all terms are nonnegative)
  have hleχ : ∀ v : ℂ, (TuranOther.multL χ v : ℝ) / ‖s + c - v‖ ^ 2
      ≤ ((TuranOther.multZeta v : ℝ) + (TuranOther.multL χ v : ℝ)) / ‖s + c - v‖ ^ 2 := by
    intro v
    rw [add_div]
    have h1 : 0 ≤ (TuranOther.multZeta v : ℝ) / ‖s + c - v‖ ^ 2 :=
      div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    linarith only [this, h1]
  have hleχχ : ∀ v : ℂ, (TuranOther.multL (χ₀ * χ) v : ℝ) / ‖s + c - v‖ ^ 2
      ≤ ((TuranOther.multZeta v : ℝ) + (TuranOther.multL (χ₀ * χ) v : ℝ)) / ‖s + c - v‖ ^ 2 := by
    intro v
    rw [add_div]
    have h1 : 0 ≤ (TuranOther.multZeta v : ℝ) / ‖s + c - v‖ ^ 2 :=
      div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    linarith only [this, h1]
  have hsumχL : Summable (fun v : ℂ => (TuranOther.multL χ v : ℝ) / ‖s + c - v‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun v => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hleχ hsumχ
  have hsumχχL : Summable (fun v : ℂ => (TuranOther.multL (χ₀ * χ) v : ℝ) / ‖s + c - v‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun v => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hleχχ hsumχχ
  have hbndχL : (∑' v : ℂ, (TuranOther.multL χ v : ℝ) / ‖s + c - v‖ ^ 2)
      ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖s + c‖) + 2) :=
    (Summable.tsum_le_tsum hleχ hsumχL hsumχ).trans hbndχ
  have hbndχχL : (∑' v : ℂ, (TuranOther.multL (χ₀ * χ) v : ℝ) / ‖s + c - v‖ ^ 2)
      ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖s + c‖) + 2) :=
    (Summable.tsum_le_tsum hleχχ hsumχχL hsumχχ).trans hbndχχ
  -- transport the two shifted families back along `u ↦ u + c`
  have hesumm : ∀ (f : ℂ → ℝ), Summable (fun v : ℂ => f v / ‖s + c - v‖ ^ 2) →
      Summable (fun u : ℂ => f (u + c) / ‖s - u‖ ^ 2) := by
    intro f hf
    have hiff := (Equiv.addRight c).summable_iff (f := fun v : ℂ => f v / ‖s + c - v‖ ^ 2)
    refine hiff.mpr hf |>.congr (fun u => ?_)
    simp only [Function.comp_apply]
    show f ((Equiv.addRight c) u) / ‖s + c - (Equiv.addRight c) u‖ ^ 2
      = f (u + c) / ‖s - u‖ ^ 2
    rw [show (Equiv.addRight c) u = u + c from rfl]
    rw [show s + c - (u + c) = s - u by ring]
  have hetsum : ∀ (f : ℂ → ℝ),
      (∑' u : ℂ, f (u + c) / ‖s - u‖ ^ 2) = (∑' v : ℂ, f v / ‖s + c - v‖ ^ 2) := by
    intro f
    rw [← Equiv.tsum_eq (Equiv.addRight c) (fun v : ℂ => f v / ‖s + c - v‖ ^ 2)]
    refine tsum_congr (fun u => ?_)
    show f (u + c) / ‖s - u‖ ^ 2
      = f ((Equiv.addRight c) u) / ‖s + c - (Equiv.addRight c) u‖ ^ 2
    rw [show (Equiv.addRight c) u = u + c from rfl]
    rw [show s + c - (u + c) = s - u by ring]
  have hsum2' : Summable (fun u : ℂ => (TuranOther.multL χ (u + c) : ℝ) / ‖s - u‖ ^ 2) :=
    hesumm (fun v => (TuranOther.multL χ v : ℝ)) hsumχL
  have hsum3' : Summable (fun u : ℂ => (TuranOther.multL (χ₀ * χ) (u + c) : ℝ) / ‖s - u‖ ^ 2) :=
    hesumm (fun v => (TuranOther.multL (χ₀ * χ) v : ℝ)) hsumχχL
  have hsumMaj : Summable (fun u : ℂ =>
      ((TuranOther.multZeta u : ℝ) + (TuranOther.multL χ₀ u : ℝ)) / ‖s - u‖ ^ 2
      + ((TuranOther.multL χ (u + c) : ℝ) / ‖s - u‖ ^ 2
        + (TuranOther.multL (χ₀ * χ) (u + c) : ℝ) / ‖s - u‖ ^ 2)) :=
    hsum1.add (hsum2'.add hsum3')
  -- the pointwise majorant
  have hpt : ∀ u : ℂ, ((TuranOther.twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖s - u‖ ^ 2 ≤
      ((TuranOther.multZeta u : ℝ) + (TuranOther.multL χ₀ u : ℝ)) / ‖s - u‖ ^ 2
      + ((TuranOther.multL χ (u + c) : ℝ) / ‖s - u‖ ^ 2
        + (TuranOther.multL (χ₀ * χ) (u + c) : ℝ) / ‖s - u‖ ^ 2) := by
    intro u
    have hle : ((TuranOther.twMult χ₀ χ β₀ γ u : ℕ) : ℝ)
        ≤ ((TuranOther.multZeta u : ℝ) + (TuranOther.multL χ₀ u : ℝ))
          + ((TuranOther.multL χ (u + c) : ℝ) + (TuranOther.multL (χ₀ * χ) (u + c) : ℝ)) := by
      have hn1 : (0 : ℝ) ≤ (TuranOther.multZeta u : ℝ) := Nat.cast_nonneg _
      have hn2 : (0 : ℝ) ≤ (TuranOther.multL χ₀ u : ℝ) := Nat.cast_nonneg _
      have hn3 : (0 : ℝ) ≤ (TuranOther.multL χ (u + c) : ℝ) := Nat.cast_nonneg _
      have hn4 : (0 : ℝ) ≤ (TuranOther.multL (χ₀ * χ) (u + c) : ℝ) := Nat.cast_nonneg _
      rw [TuranOther.twMult]
      have hcdef' : u + Complex.I * (γ : ℂ) = u + c := by rw [hcdef]
      by_cases hu : u = 0 ∨ u = (β₀ : ℂ)
      · rw [if_pos hu, hcdef', Nat.cast_zero]
        linarith only [this]
      · rw [if_neg hu, hcdef']
        simp only [Nat.cast_add]
        linarith only [this]
    calc ((TuranOther.twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖s - u‖ ^ 2
        ≤ (((TuranOther.multZeta u : ℝ) + (TuranOther.multL χ₀ u : ℝ))
            + ((TuranOther.multL χ (u + c) : ℝ)
              + (TuranOther.multL (χ₀ * χ) (u + c) : ℝ))) / ‖s - u‖ ^ 2 :=
          div_le_div_of_nonneg_right hle (by positivity)
      _ = ((TuranOther.multZeta u : ℝ) + (TuranOther.multL χ₀ u : ℝ)) / ‖s - u‖ ^ 2
          + ((TuranOther.multL χ (u + c) : ℝ) / ‖s - u‖ ^ 2
            + (TuranOther.multL (χ₀ * χ) (u + c) : ℝ) / ‖s - u‖ ^ 2) := by
          simp only [add_div]
  -- summability and the bound
  have hsumm : Summable (fun u : ℂ => ((TuranOther.twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖s - u‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun u => div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hpt hsumMaj
  refine ⟨hsumm, ?_⟩
  have hmain := Summable.tsum_le_tsum hpt hsumm hsumMaj
  rw [Summable.tsum_add hsum1 (hsum2'.add hsum3'), Summable.tsum_add hsum2' hsum3',
    hetsum (fun v => (TuranOther.multL χ v : ℝ)),
    hetsum (fun v => (TuranOther.multL (χ₀ * χ) v : ℝ))] at hmain
  -- numerical bounds
  have hsnorm : ‖s‖ ≤ 101 := by
    have h1 : s.re = 1 + α := by rw [hsdef]; simp
    have h2 : s.im = 0 := by rw [hsdef]; simp
    have h4 := Complex.norm_le_abs_re_add_abs_im s
    rw [h1, h2, abs_zero, add_zero] at h4
    rw [abs_of_nonneg (by linarith only [hα1] : (0:ℝ) ≤ 1 + α)] at h4
    linarith only [hα100, h4]
  have hscnorm : ‖s + c‖ ≤ 103 := by
    have h1 : ‖s + c‖ ≤ ‖s‖ + ‖c‖ := norm_add_le _ _
    rw [hcnorm] at h1
    have h4 : |γ| ≤ 2 := hγ
    linarith only [hsnorm, hγ, h1]
  have hlog1 : Real.log (2 + ‖s‖) ≤ 5 := by
    have h1 : 2 + ‖s‖ ≤ 105 := by linarith only [hsnorm]
    linarith only [Real.log_le_log (by positivity) h1, log_105_le_five, h1]
  have hlog2 : Real.log (2 + ‖s + c‖) ≤ 5 := by
    have h1 : 2 + ‖s + c‖ ≤ 105 := by linarith only [hscnorm]
    linarith only [Real.log_le_log (by positivity) h1, log_105_le_five, h1]
  have hlq : 1 ≤ Real.log (q : ℝ) := by
    have h1 : Real.log 3 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hq3)
    linarith only [Real.log_three_gt_d9, h1]
  calc (∑' u : ℂ, ((TuranOther.twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖s - u‖ ^ 2)
      ≤ (∑' u : ℂ, ((TuranOther.multZeta u : ℝ) + (TuranOther.multL χ₀ u : ℝ)) / ‖s - u‖ ^ 2)
        + ((∑' v : ℂ, (TuranOther.multL χ v : ℝ) / ‖s + c - v‖ ^ 2)
            + (∑' v : ℂ, (TuranOther.multL (χ₀ * χ) v : ℝ) / ‖s + c - v‖ ^ 2)) := hmain
    _ ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖s‖) + 2)
        + (C * (Real.log (q : ℝ) + Real.log (2 + ‖s + c‖) + 2)
            + C * (Real.log (q : ℝ) + Real.log (2 + ‖s + c‖) + 2)) :=
        add_le_add hbnd1 (add_le_add hbndχL hbndχχL)
    _ ≤ (24 * C + 100) * (Real.log (q : ℝ) + 1) := by
        nlinarith only [hlq, hlog1, hlog2, hCpos]

/-- **The Turán/Hadamard assembly: the target from the single-character mass bound.**

This is the `rect`-compatible assembly of the uncapped Deuring--Heilbronn repulsion for the
*other* characters from
* the twisted Hadamard upper bound `Work.LinnikAreas.TuranOther.twUpper` (imported in the
  `P3RectTuranOther` port, hence available in this family),
* the twisted mass bound `twMassCore_of_single` (from the single-character mass bound),
* the Turán step `Work.LinnikAreas.turanStep` and its arithmetic `repelArith`,
* the off-axis zero-free region `DhCapped.offAxisLambdaLower` (which rules out the case
  `Re ρ = Re ρ₀` for `ρ ≠ ρ₀`: there `λ(ρ) = λ(ρ₀) ≥ c > 0`, and minimality plus `λ₀ ≤ 1/100`
  gives the conclusion).

Everything except the mass bound is discharged here. -/
theorem otherCharRepelSiegel_of_mass
    (h : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (ψ : DirichletCharacter ℂ q) (w : ℂ),
      (3 / 2 : ℝ) ≤ w.re →
      Summable (fun u : ℂ =>
          ((TuranOther.multZeta u : ℝ) + (TuranOther.multL ψ u : ℝ)) / ‖w - u‖ ^ 2) ∧
      (∑' u : ℂ, ((TuranOther.multZeta u : ℝ) + (TuranOther.multL ψ u : ℝ)) / ‖w - u‖ ^ 2)
        ≤ C * (Real.log (q : ℝ) + Real.log (2 + ‖w‖) + 2)) :
    ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), χ ≠ χ₀ → χ ≠ 1 →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₀ →
      c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨Ct, hCtpos, hMBtw0⟩ := twMassCore_of_single h
  obtain ⟨cO, hcOpos, qO, hOFF⟩ := Work.LinnikAreas.DhCapped.offAxisLambdaLower
  -- the constants
  set JB : ℝ := (8 + 1) * (1 + 3) ^ 2 * Ct + 1 with hJBdef
  set A : ℝ := 3 / (8 * JB) with hAdef
  set Bl : ℝ := -A * Real.log (1 * 3 / ((32 + 4 * 1) * 4 * JB)) with hBldef
  set θ : ℝ := min (1 / 2) (1 * 3 / ((32 + 4 * 1) * 4 * Real.exp 1 * JB)) with hθdef
  set c₁' : ℝ := min cO (1 / 2) with hc1def
  set c₂' : ℝ := c₁' / Real.log (1 / c₁') with hc2def
  set c₃' : ℝ := min (A / 2)
      (A / (2 * (max (max Bl 0) 1)) * Real.exp (-(2 * (max (max Bl 0) 1) / A))) with hc3def
  set c₀' : ℝ := θ / Real.log (1 / θ) with hc0def
  have hJBpos : 0 < JB := by rw [hJBdef]; positivity
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hθpos : 0 < θ := by rw [hθdef]; exact lt_min (by norm_num) (by positivity)
  have hθlt1 : θ < 1 := by
    have h1 : θ ≤ 1 / 2 := le_trans (min_le_left _ _) le_rfl
    linarith only [hθpos, h1]
  have hc1pos : 0 < c₁' := lt_min hcOpos (by norm_num)
  have hc1lt1 : c₁' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hlogc1pos : 0 < Real.log (1 / c₁') := by
    rw [one_div]
    exact Real.log_pos ((one_lt_inv₀ hc1pos).mpr hc1lt1)
  have hc2pos : 0 < c₂' := by rw [hc2def]; positivity
  have hc3pos : 0 < c₃' := by
    rw [hc3def]
    exact lt_min (by positivity)
      (mul_pos (div_pos hApos (by positivity)) (Real.exp_pos _))
  have hlogθpos : 0 < Real.log (1 / θ) := by
    rw [one_div]
    exact Real.log_pos ((one_lt_inv₀ hθpos).mpr hθlt1)
  have hc0pos : 0 < c₀' := by
    rw [hc0def]
    exact div_pos hθpos hlogθpos
  refine ⟨min (min c₀' c₃') c₂', lt_min (lt_min hc0pos hc3pos) hc2pos, max qO 3, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hsq him0 hlam0 χ ρ hχχ₀ hχ1 hzm himρ hneρ
  haveI : NeZero q := hqne
  have hqO : qO ≤ q := le_trans (le_max_left _ _) hq
  have hq3 : 3 ≤ q := le_trans (le_max_right _ _) hq
  have hlogq0 : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlogq1 : 1 ≤ Real.log (q : ℝ) := by
    have h1 : Real.log 3 ≤ Real.log (q : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hq3)
    linarith only [Real.log_three_gt_d9, hθpos, hθlt1, h1]
  have hχ₀ne1 : χ₀ ≠ 1 := hmin.1.1
  have hz0 : Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 := hmin.1.2.1
  have hstrip0 : 0 < ρ₀.re ∧ ρ₀.re < 1 := re_mem_strip_of_zeroMult hχ₀ne1 hz0
  have hstrip : 0 < ρ.re ∧ ρ.re < 1 := re_mem_strip_of_zeroMult hχ1 hzm
  have hlam0pos : 0 < Work.LinnikContract.lamOf q ρ₀ := by
    rw [Work.LinnikContract.lamOf]; exact mul_pos (by linarith only [hstrip0.2, hstrip0]) hlogq0
  have hlognn : 0 ≤ Real.log (1 / Work.LinnikContract.lamOf q ρ₀) := by
    apply Real.log_nonneg
    rw [one_div]
    exact (one_le_inv₀ hlam0pos).mpr (by linarith only [hlam0, hlam0pos])
  have hminimal : Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q ρ :=
    hmin.2 χ ρ ⟨hχ1, hzm, himρ⟩
  by_cases hcase : ρ.re = ρ₀.re
  · -- `ρ` is a complex zero with `λ(ρ) = λ(ρ₀)`: the off-axis zero-free region gives `λ₀ ≥ c`
    have himne : ρ.im ≠ 0 := by
      intro h0
      exact hneρ (Complex.ext hcase (by rw [h0, him0]))
    have himle : |ρ.im| ≤ 10 * Real.log (q : ℝ) := by linarith only [himρ, hlogq1, hlam0, hlam0pos]
    have hoff : cO ≤ Work.LinnikContract.lamOf q ρ := hOFF q hqO χ ρ hχ1 hzm himne himle
    have hlam_eq : Work.LinnikContract.lamOf q ρ = Work.LinnikContract.lamOf q ρ₀ := by
      simp only [Work.LinnikContract.lamOf]; rw [hcase]
    have hc1le : c₁' ≤ Work.LinnikContract.lamOf q ρ₀ := by
      rw [hlam_eq] at hoff
      exact le_trans (min_le_left _ _) hoff
    have hlogle : Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Real.log (1 / c₁') := by
      apply Real.log_le_log (by positivity)
      rw [one_div, one_div]
      exact (inv_le_inv₀ hlam0pos hc1pos).mpr hc1le
    calc min (min c₀' c₃') c₂' * Real.log (1 / Work.LinnikContract.lamOf q ρ₀)
        ≤ c₂' * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hlognn
      _ ≤ c₂' * Real.log (1 / c₁') := mul_le_mul_of_nonneg_left hlogle hc2pos.le
      _ = c₁' := by rw [hc2def]; field_simp
      _ ≤ Work.LinnikContract.lamOf q ρ := le_trans hc1le (le_of_eq hlam_eq.symm)
  · -- `Re ρ ≠ Re ρ₀`
    by_cases hbig : θ < Work.LinnikContract.lamOf q ρ₀
    · -- `λ₀` is bounded below by the threshold `θ`: minimality suffices
      have hlogle : Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Real.log (1 / θ) := by
        apply Real.log_le_log (by positivity)
        rw [one_div, one_div]
        exact (inv_le_inv₀ hlam0pos hθpos).mpr hbig.le
      calc min (min c₀' c₃') c₂' * Real.log (1 / Work.LinnikContract.lamOf q ρ₀)
          ≤ c₀' * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) :=
            mul_le_mul_of_nonneg_right (le_trans (min_le_left _ _) (min_le_left _ _)) hlognn
        _ ≤ c₀' * Real.log (1 / θ) := mul_le_mul_of_nonneg_left hlogle hc0pos.le
        _ = θ := by
          rw [hc0def]
          field_simp
        _ ≤ Work.LinnikContract.lamOf q ρ₀ := le_of_lt hbig
        _ ≤ Work.LinnikContract.lamOf q ρ := hminimal
    · -- the Turán step
      push_neg at hbig
      have hstep' : Work.LinnikContract.lamOf q ρ₀ ≤
          min (1 / 2) (1 * 3 / ((32 + 4 * 1) * 4 * Real.exp 1 * JB)) := by
        rw [hθdef] at hbig
        rw [Work.LinnikContract.lamOf] at hbig ⊢
        exact hbig
      have hβ₀ : DirichletCharacter.LFunction χ₀ ((ρ₀.re : ℂ)) = 0 := by
        have hρ₀eq : ((ρ₀.re : ℂ)) = ρ₀ := by rw [← Complex.re_add_im ρ₀, him0]; simp
        exact Work.LinnikAreas.LFunction_eq_zero_of_zeroMult χ₀ hχ₀ne1 hstrip0.1 hstrip0.2
          (by rw [hρ₀eq]; exact hz0)
      have hsq' : χ₀ * χ₀ = 1 := by rw [← pow_two]; exact hsq
      have hχ₀χ : χ₀ * χ ≠ 1 := by
        intro h1
        apply hχχ₀
        calc χ = χ₀ * χ₀ * χ := by rw [hsq']; simp
          _ = χ₀ * (χ₀ * χ) := by rw [mul_assoc]
          _ = χ₀ * 1 := by rw [h1]
          _ = χ₀ := mul_one χ₀
      have hU : TuranOther.TwUpperCore := by
        intro q _inst χ₀ χ h₀ h₀sq hχ hχ₀χ β₀ hβ₀ α hα γ j hj
        exact TuranOther.twUpper χ₀ χ h₀ h₀sq hχ hχ₀χ β₀ hβ₀ α hα γ j hj
      have hmass : ∀ (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ α : ℝ),
          1 ≤ α → α ≤ 100 → |γ| ≤ 2 →
          Summable (fun u : ℂ =>
              ((TuranOther.twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 + (α : ℂ)) - u‖ ^ 2) ∧
          (∑' u : ℂ,
              ((TuranOther.twMult χ₀ χ β₀ γ u : ℕ) : ℝ) / ‖(1 + (α : ℂ)) - u‖ ^ 2)
            ≤ Ct * (Real.log (q : ℝ) + 1) :=
        fun χ₀ χ β₀ γ α h1 h2 h3 => hMBtw0 q hq3 χ₀ χ β₀ γ α h1 h2 h3
      have hstep := turanStep hU Ct hCtpos hmass
        (fun {α ε β β₀} {j J} hα hε hJ hj hjJ hβ hβ₀ hreg hmain =>
          TuranOther.turanArith hα hε hJ hj hjJ hβ hβ₀ hreg hmain)
        (fun χ hχ u hu hzm => TuranOther.multL_ne_zero χ hχ hu hzm)
        χ₀ χ ρ₀ ρ hχ₀ne1 hsq' hχ1 hχ₀χ hβ₀ him0 hstrip0.1 hstrip0.2 hzm himρ hstrip.1 hstrip.2
        hcase hstep' hlogq1
      have hmain : A * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) - Bl
          ≤ Work.LinnikContract.lamOf q ρ := by
        have h := hstep
        simp only [Work.LinnikContract.lamOf, hAdef, hBldef, hJBdef] at h ⊢
        linarith only [hstep]
      have hrepel : c₃' * Real.log (1 / Work.LinnikContract.lamOf q ρ₀)
          ≤ Work.LinnikContract.lamOf q ρ := by
        rw [hc3def]
        exact repelArith hApos hlam0pos (by linarith only [hlam0, hlam0pos]) hminimal hmain
      exact le_trans (mul_le_mul_of_nonneg_right
        (le_trans (min_le_left _ _) (min_le_right _ _)) hlognn) hrepel

theorem otherCharRepelSiegel : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    Work.LinnikContract.lamOf q ρ₀ ≤ 1 / 100 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), χ ≠ χ₀ → χ ≠ 1 →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₀ →
      c * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Work.LinnikContract.lamOf q ρ := by
  obtain ⟨C, hCpos, cD, hcDpos, qA, hA⟩ := OtherCharRepel.otherCharDensityInput
  set K : ℝ := max 1 (Real.log C) with hKdef
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  have hKC : Real.log C ≤ K := le_max_right _ _
  set c₁ : ℝ := min (1 / (2 * cD)) (Real.exp (-(2 * K)) / (2 * K)) with hc₁def
  have hc₁pos : 0 < c₁ := by
    rw [hc₁def]
    exact lt_min (by positivity) (div_pos (Real.exp_pos _) (by positivity))
  refine ⟨c₁, hc₁pos, qA + 10, ?_⟩
  intro q hq hqne χ₀ ρ₀ hmin hreal him hlam0 χ ρ hχne hχne1 hz himρ hneρ
  have hqA : qA ≤ q := by omega
  have hχ₀ne1 : χ₀ ≠ 1 := hmin.1.1
  have hz0 : Work.LinnikContract.zeroMult χ₀ ρ₀ ≠ 0 := hmin.1.2.1
  have hstrip0 := re_mem_strip_of_zeroMult hχ₀ne1 hz0
  have hstrip := re_mem_strip_of_zeroMult hχne1 hz
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlam0pos : 0 < Work.LinnikContract.lamOf q ρ₀ := by
    rw [Work.LinnikContract.lamOf]; exact mul_pos (by linarith only [hstrip0.2, hstrip0]) hlogq
  have hlampos : 0 < Work.LinnikContract.lamOf q ρ := by
    rw [Work.LinnikContract.lamOf]; exact mul_pos (by linarith only [hstrip.2, hstrip]) hlogq
  have hlamle : Work.LinnikContract.lamOf q ρ ≤ Real.log q := by
    rw [Work.LinnikContract.lamOf]; nlinarith only [hstrip.1, hlogq, hstrip0, hstrip]
  -- minimality of `λ(ρ₀)` (this is what lets us treat the moderate range without any
  -- zero-free region or constant bound)
  have hmin1 : Work.LinnikContract.lamOf q ρ₀ ≤ Work.LinnikContract.lamOf q ρ :=
    hmin.2 χ ρ ⟨hχne1, hz, himρ⟩
  have hLpos : 0 < Real.log (1 / Work.LinnikContract.lamOf q ρ₀) := by
    apply Real.log_pos
    have h := one_div_lt_one_div_of_lt hlam0pos
      (by linarith only [hlam0, hlam0pos] : Work.LinnikContract.lamOf q ρ₀ < 1)
    simpa using h
  have hLge : Real.log 100 ≤ Real.log (1 / Work.LinnikContract.lamOf q ρ₀) := by
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ hlam0pos]; linarith only [hlam0]
  -- the density input, at `t = λ(ρ)`, applied to the singleton `{(χ, ρ)}`
  have hden : (1:ℝ)
      ≤ C * Work.LinnikContract.lamOf q ρ₀ * Real.exp (cD * Work.LinnikContract.lamOf q ρ) := by
    have hsum := hA q hqA χ₀ ρ₀ hmin hreal him hlam0 (Work.LinnikContract.lamOf q ρ)
      hlampos hlamle ({(χ, ρ)} : Finset (DirichletCharacter ℂ q × ℂ)) (by
        intro p hp
        have hp' : p = (χ, ρ) := by simpa using hp
        rw [hp']
        exact ⟨hχne, hχne1, hz, himρ, hneρ, le_refl _⟩)
    have hsum' : (Work.LinnikContract.zeroMult χ ρ : ℝ)
        ≤ C * Work.LinnikContract.lamOf q ρ₀ * Real.exp (cD * Work.LinnikContract.lamOf q ρ) := by
      simpa using hsum
    have h1 : (1:ℝ) ≤ (Work.LinnikContract.zeroMult χ ρ : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    linarith only [hqne, hsum', h1]
  have hkey : Real.log (1 / Work.LinnikContract.lamOf q ρ₀) - Real.log C
      ≤ cD * Work.LinnikContract.lamOf q ρ := by
    have hlog : Real.log (C * Work.LinnikContract.lamOf q ρ₀
          * Real.exp (cD * Work.LinnikContract.lamOf q ρ))
        = Real.log C + Real.log (Work.LinnikContract.lamOf q ρ₀)
          + cD * Work.LinnikContract.lamOf q ρ := by
      rw [show C * Work.LinnikContract.lamOf q ρ₀
            * Real.exp (cD * Work.LinnikContract.lamOf q ρ)
          = C * (Work.LinnikContract.lamOf q ρ₀
            * Real.exp (cD * Work.LinnikContract.lamOf q ρ)) by ring]
      rw [Real.log_mul (ne_of_gt hCpos) (ne_of_gt (mul_pos hlam0pos (Real.exp_pos _)))]
      rw [Real.log_mul (ne_of_gt hlam0pos) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
      ring
    have h2 : (0:ℝ) ≤ Real.log C + Real.log (Work.LinnikContract.lamOf q ρ₀)
        + cD * Work.LinnikContract.lamOf q ρ := by
      have h3 := Real.log_le_log (by norm_num : (0:ℝ) < 1) hden
      rw [Real.log_one, hlog] at h3
      linarith only [h3]
    have h3 : Real.log (Work.LinnikContract.lamOf q ρ₀)
        = -Real.log (1 / Work.LinnikContract.lamOf q ρ₀) := by
      rw [one_div, Real.log_inv]; ring
    linarith only [h2, h3]
  by_cases hcase : 2 * Real.log C ≤ Real.log (1 / Work.LinnikContract.lamOf q ρ₀)
  · -- small `λ(ρ₀)`: the density estimate alone already gives the logarithm
    have h2 : c₁ ≤ 1 / (2 * cD) := by rw [hc₁def]; exact min_le_left _ _
    have h3 : c₁ * Real.log (1 / Work.LinnikContract.lamOf q ρ₀)
        ≤ (1 / (2 * cD)) * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) :=
      mul_le_mul_of_nonneg_right h2 hLpos.le
    have h4 : (1 / (2 * cD)) * Real.log (1 / Work.LinnikContract.lamOf q ρ₀)
        = Real.log (1 / Work.LinnikContract.lamOf q ρ₀) / (2 * cD) := by ring
    have h5 : Real.log (1 / Work.LinnikContract.lamOf q ρ₀) / (2 * cD)
        ≤ Work.LinnikContract.lamOf q ρ := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * cD)]
      linarith only [hkey, hcase]
    linarith only [h3, h5, h4]
  · -- moderate `λ(ρ₀)`: `λ(ρ) ≥ λ(ρ₀)` and `λ(ρ₀) > e^{-2K}` settle it
    push Not at hcase
    have h2 : c₁ ≤ Real.exp (-(2 * K)) / (2 * K) := by rw [hc₁def]; exact min_le_right _ _
    have h3 : Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ 2 * K := by linarith only [hcase, hKC]
    have h5 : 1 / Work.LinnikContract.lamOf q ρ₀ ≤ Real.exp (2 * K) := by
      rw [← Real.exp_log (by positivity : (0:ℝ) < 1 / Work.LinnikContract.lamOf q ρ₀)]
      exact Real.exp_le_exp.mpr h3
    have h6 : Real.exp (-(2 * K)) ≤ Work.LinnikContract.lamOf q ρ₀ := by
      have h7 : Real.exp (-(2 * K)) = (1 : ℝ) / Real.exp (2 * K) := by
        rw [Real.exp_neg, one_div]
      rw [h7, div_le_iff₀ (Real.exp_pos _)]
      rw [div_le_iff₀ hlam0pos] at h5
      linarith only [h5]
    have h7 : c₁ * Real.log (1 / Work.LinnikContract.lamOf q ρ₀) ≤ Real.exp (-(2 * K)) := by
      calc c₁ * Real.log (1 / Work.LinnikContract.lamOf q ρ₀)
          ≤ (Real.exp (-(2 * K)) / (2 * K)) * (2 * K) :=
            mul_le_mul h2 h3 hLpos.le (by positivity)
        _ = Real.exp (-(2 * K)) := by
            rw [div_mul_cancel₀ _ (by positivity : (2:ℝ) * K ≠ 0)]
    linarith only [h7, h6, hmin1]

end Work.LinnikAreas
