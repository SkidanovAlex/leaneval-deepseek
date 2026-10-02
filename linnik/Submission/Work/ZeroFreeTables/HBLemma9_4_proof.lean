import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.EngineRoadmap
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.HB4_1
import Submission.Work.A7.exists_isMin1
import Submission.Work.ZeroFreeTables.hbLemma9_3_engine
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine_v2
import Submission.Work.ZeroFreeTables.table10_93_cert
import Submission.Work.ZeroFreeTables.rowcontra92
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.ZeroFreeTables.HB94.L52supply
import Submission.Work.ZeroFreeTables.HB94.L52supply_pow
import Submission.Work.ZeroFreeTables.HB94.rowcontra92_all
import Submission.Work.ZeroFreeTables.HB94.rowcontra93q
import Submission.Work.ZeroFreeTables.HB94.rowcontra62_all
import Submission.Work.ZeroFreeTables.HB94.h5plus_v2
import Submission.Work.ZeroFreeTables.HB94.hbLemma6_2_engine_mixed
import Submission.Work.ZeroFreeTables.HB94.table10_62_cert_real
import Submission.Work.LinnikAreas.DhCapped.L52Hyp_mono

namespace Work.ZeroFreeTables

open DirichletCharacter Complex
open Work.LinnikContract
open scoped Classical BigOperators

noncomputable section

/-!
# `HBLemma9_4` — Heath-Brown's Lemma 9.4 (Table 10 in all cases)

Target: for all large `q`, if `(χ₁,ρ₁)` is HB's exceptional pair (`IsMin1WideAt 10`) with
`λ₁ = lamOf q ρ₁`, then every row `(a,b)` of `hbTable10` gives
`λ₁ ≤ a → Lam2Bound χ₁ b`, i.e. every zero of a character `χ ∉ {χ₁, χ₁⁻¹}` has `λ ≥ b`.

## The paper's proof (and what a formal proof needs)

Table 10 is computed from **HB Lemma 9.3** — the "reversed roles" companion of Lemma 9.2 —
which is derived from the pointwise positivity
`χ₀(n)(1 + Re(χ₂(n)n^{-iγ₂}))(k + Re(χ₁(n)n^{-iγ₁}))² ≥ 0`:

  `(k²+½)(F(−λ₁) − F(0)) − 2k F(λ₂−λ₁) + f(0)(ψ + ε) ≥ 0`,  `ψ = psi92 k = (k²+4k+3/2)/6`,

for `f` of HB's Conditions 1 and 2 (the `θ`-family of Lemma 7.1), provided the seven
characters `χ₁, χ₂, χ₂², χ₁χ₂, χ₁χ₂⁻¹, χ₁χ₂², χ₁χ₂⁻²` are non-principal, i.e.
`χ₂ ∉ {χ₁^{±1}}` and `χ₂² ∉ {χ₀, χ₁, χ₁⁻¹}` (HB: "χ₂² ≠ χ₀, χ₁, χ̄₁").

The *other* route is **HB Lemma 9.2** (Table 9), from
`χ₀(n)(1 + Re(χ₂(n)n^{-iγ₂}))(k + Re(χ₁(n)n^{-iγ₁}))²` with the `−LF(λ₂−λ₁)` term attached
to the *second* character:

  `(k²+½)(F(−λ₁) − F(λ₂−λ₁)) − 2k F(0) + f(0)(ψ + ε) ≥ 0`,

valid when `χ₁² ∉ {χ₀, χ₂, χ₁²}`-type conditions hold, i.e. `χ₁² ≠ 1`, `χ₁² ≠ χ₂`, `χ₁² ≠ χ₂⁻¹`.

Covering all cases (HB's Lemma 9.4) therefore needs three engines:

* **L92** (`hbLemma9_2_engine`): hypothesis `χ₁² ∉ {χ₀, χ₂, χ₂⁻¹}`.
  Numerically the strongest: with `θ = atan 2` fixed and `(k,λ)` chosen per row the
  certificate `(k²+½)(F(−a) − F(b−a)) − 2kF(0) + f(0)ψ < 0` succeeds with margins ≥ `0.006`
  for every row of `hbTable10` (verified numerically; e.g. row `(0.34, 0.929)`: margin `−0.30`).
* **L93** (`hbLemma9_3_engine`): hypothesis `χ₂² ∉ {χ₀, χ₁, χ₁⁻¹}`.
  Numerically much weaker: with `ψ = psi92` and the `θ`-family optimised per row the
  certificate certifies `λ₂ ≥ b` for `b` up to `0.9055, 0.8737, 0.8446, 0.8057, 0.7713,
  0.7415, 0.7064, 0.7056` for the rows `a = 0.36, 0.40, 0.44, 0.50, 0.56, 0.62, 0.70, 0.702`
  — each exactly the printed value plus `0.002` (HB's `δ`), so those rows certify in the
  `b+δ` reading — but only `0.9229` for the row `a = 0.34` (printed `0.929`, needed `0.931`):
  **the first row of `hbTable10` is *not* certifiable from HB (9.14) with `ψ = psi92`.**
* **L62** (HB Lemma 6.2, five-term): `F(−λ₁) − F(0) − F(λ₂−λ₁) + f(0)(ψ+ε) ≥ 0` with
  `ψ = ½φ(χ₁) + ½φ(χ₂) + ¼φ(χ₁χ₂) + ¼φ(χ₁χ̄₂) ≤ 1/2`.  Needed for the case where *both*
  `χ₁² ∈ {χ₀,χ₂,χ₂⁻¹}` and `χ₂² ∈ {χ₀,χ₁,χ₁⁻¹}`; HB notes this forces `χ₁, χ₂` to have order
  `≤ 5`, whence `φ(χ) = 1/4` for all seven characters (HB Lemma 2.5: `φ = 1/4` if `q` is
  cube-free or `ord χ ≤ log q`) and `ψ ≤ 3/8`.  The workspace's
  `Commons.NumberTheory.Linnik.lemma6_2_assembly` already gives the `ψ = 1/2` form; with
  `ψ = 3/8` the certificate for the row `(0.34, 0.929)` succeeds with margin `−0.21`.

## The covering of the rows (updated: the case analysis is now complete)

Write `λ₁ = λ(ρ₁)`, `λ₂ = min {λ(ρ) : χ ∉ {χ₁, χ₁⁻¹}, IsZ χ ρ}`.

* **`λ₁ ≤ 0.348` (in particular `λ₁ ≤ 0.34`).**  HB Theorem 1 (`Z1`) says that the (unique)
  zero of `∏_χ L(s,χ)` in `σ ≥ 1 − 0.348/log q`, `|t| ≤ 1` is **real**, simple, and belongs to a
  **real** non-principal character: `χ₁² = 1`, `ρ₁.im = 0`.  Then HB Table 7 (`HBTable7`, the §8
  real case, Lemma 8.7) gives `λ₂ ≥ 1.42` for `λ₁ ≤ 0.35` — far stronger than any entry of
  Table 10.  So **every** row of `hbTable10` follows for `λ₁ ≤ 0.348` from `HBTheorem1` and
  `HBTable7` (monotonicity `lam2Bound_mono`: `1.42 ≥ 929/1000`).
  In particular the problematic first row `(0.34, 929/1000)` *is* covered
  (and the case `χ₂ = χ₁^{±2}` cannot occur there, since `χ₁² = 1` forces `χ₂ = 1`).
* **`λ₁ ≥ 0.348`, `χ₂ ∉ {χ₁², χ₁⁻²}`.**  Then `χ₁² ∉ {χ₀, χ₂, χ₂⁻¹}`-type conditions hold, and
  the strongest engine, **HB Lemma 9.2** (`L92`), applies — HB's Table 9.  Table 9's values
  dominate Table 10's entry by entry (`1.283 ≥ 0.929`, …, `0.704 ≥ 0.702`), and Table 9's
  twenty `rowcontra`-style certificates are **already formalised** in
  `Submission/Work/ZeroFreeTables/P9F/table9_{certs,expb,rows}.lean`.  So all rows follow from
  Table 9 in this case.
* **`λ₁ ≥ 0.348`, `χ₂ = χ₁^{±2}`.**  Then `χ₁² ∉ {χ₀, χ₂, χ₂⁻¹}` fails, so `L92` is unavailable,
  but `χ₂² = χ₁^{±4} ∉ {χ₀, χ₁, χ₁⁻¹}` holds unless `ord χ₁ ∈ {3,4,5}`; hence **HB Lemma 9.3**
  (`L93`, proved here as `hbLemma9_3_engine`) applies.  Its numerical strength is much lower than
  Table 9's: with `ψ = psi92 k` and the `θ`-family optimised row by row the certificate certifies
  `λ₂ ≥ b` up to `0.9055, 0.8737, 0.8446, 0.8057, 0.7713, 0.7415, 0.7064, 0.7056` at
  `a = 0.36, 0.40, 0.44, 0.50, 0.56, 0.62, 0.70, 0.702` — each exactly the printed Table-10 entry
  plus `≈ 0.0025 ≈ δ` — so these rows certify in HB's `b + δ` reading, but they need their **own**
  certificates (the Table-9 ones do not apply).
* **`(C3)`: `χ₁² ∈ {χ₀,χ₂,χ₂⁻¹}` and `χ₂² ∈ {χ₀,χ₁,χ₁⁻¹}`** (both `L92` and `L93` unavailable).
  Then `χ₁, χ₂` have order `≤ 5` (HB), all seven characters have order `≤ log q`, and HB Lemma 2.5
  gives `φ(χ) = 1/4` instead of `1/3`; HB's Lemma 6.2 then holds with `ψ ≤ 3/8`.  The engine
  `hbLemma6_2_engine` (proved here) supplies the `ψ = 3c` form; with `c = 1/8` this is `3/8`, and
  the certificate succeeds with a comfortable margin (`−0.21` at the row `(0.34, 0.929)`).
  **Missing input:** the log-derivative bound `L52Hyp χ (1/8) ε δ` for characters of order `≤ 5`
  (HB Lemma 2.5's `φ = 1/4` case); the workspace's Area-1 input
  (`Work.LinnikAreas.l31free.lemma3_1_free_gen`) is stated with `φ = 1/3`.

## Remaining work for the proof of `HBLemma9_4`

1. `L93`-certificates for the eight rows `a ≥ 0.36` (mirroring
   `P9F/table9_{certs,expb,rows}.lean`, with the `L93` functional instead of `L92`'s).
2. The `φ = 1/4` log-derivative input for the `(C3)` case (HB Lemma 2.5).
3. The real-case inputs `HBTheorem1` and `HBTable7` for `λ₁ ≤ 0.348` (other agents).
4. The assembly: `HBWideMin` (`λ₁ ≤ 6/7 − 1/1000` gives `IsMin1Wide`), the case split above,
   `lam2Bound_mono`, and `hbTable10` membership arithmetic (`mem_tableR_hbTable10_*`).

## Certificate design (numerically verified, for the prover)

For the rows with `a ≥ 0.36` the `Lemma 9.3` certificate can be taken with the **rational**
test function of `testFn7_2` (HB Lemma 7.2: `F 0 = 8/9`, `F(−λ) = 8/5`, `f 0 = 16λ/15`,
`f(t) = (λ/30)(2−λt)³(4+6λt+λ²t²)` on `[0,2/λ]`), whose real-axis Laplace transform is the
elementary `F_λ(z) = ∫₀² e^{−z u/λ} f₁(u) du = (1/30)(32 I₀ − 40 I₂ + 20 I₃ − I₅)(z/λ)`,
`I_k(w) = ∫₀² u^k e^{−wu} du = k!/w^{k+1} − e^{−2w} Σ_{j≤k} (k!/j!) 2^j / w^{k+1−j}`.
The certificate needed is, per row `(a,b)` with `a ≥ 0.36`, a choice of `λ, k` with

  `(k²+½)(F_λ(−a) − F_λ(0)) − 2k F_λ(b−a) + f_λ(0)·((k²+4k+3/2)(1/6 + ε)) < 0`,

verified numerically at `a = 0.36, 0.40, 0.44, 0.50, 0.56, 0.62, 0.70, 0.702` with margins
`−0.0013, ‑0.0017, ‑0.0022, ‑0.0028, ‑0.0034, ‑0.0041, ‑0.0048, ‑0.0032` (in fact with the
same `λ ≈ 0.75 … 0.88` and `k ≈ 0.92 … 0.86`).  Two monotonicity facts upgrade these point
certificates to the range `λ₁ ∈ [0.348, a]`, `λ₂ ∈ [λ₁, b]`:

* increasing in `λ₂`: `F_λ((λ₂−λ₁))` decreases in `λ₂` (pointwise in `t`, `e^{−zt}`),
* increasing in `λ₁` for the chosen parameters: `d/dλ₁ = (k²+½)|F_λ'(−λ₁)| − 2k|F_λ'(λ₂−λ₁)| ≥ 0`,
  which holds with the tables above (numerically) and is provable from the explicit
  polynomial integrals `I_k` (both terms are computed closed forms in `λ₁`).

The certificate for the `(C3)` case (via `hbLemma6_2_engine`, `c = 1/8`) is much more
comfortable: with the same family, `F_λ(−a) − F_λ(0) − F_λ(b−a) + f_λ(0)·(3(1/8 + ε)) < 0`
at every row with margin `≤ −0.068` (`λ ≈ 1.0 … 1.15`).

## Pipeline status (this workspace, parallel fleet)

* `hbLemma9_3_engine` (proved here) — HB Lemma 9.3; `hbLemma6_2_engine` (proved here) —
  HB Lemma 6.2 with `ψ = 3c`.  **They cannot be imported together**: both define a
  `zeroMult_ne_zero_of_divisor` in `namespace Work.ZeroFreeTables`.  The reductions in this
  file therefore take the *inequality* as a hypothesis where the engine would be needed
  (`row_of_cert62`), or use only `hbLemma9_3_engine` (`row_of_cert93`).  A merged engine file
  (or a rename) is needed before the final assembly.
* `ZeroFreeTables/table10_93_cert` and `ZeroFreeTables/table10_62_cert` (in flight) — the
  region-form numerical certificates for the Table 10 rows used by the two reductions.
* `P9F/*` — HB Lemma 7.1's test function `tf71T`, its real-axis Laplace transform `La` with
  `La_mono`/`La_sub_mono`, the closed form `tf71Fr` and the twenty Table-9 certificates
  (`rowcontra_*`, an `L92` route much stronger than Table 10's needs).
* `L52Hyp_ord_le` — the log-derivative input `L52Hyp χ (1/8) ε δ` for (primitive) characters
  of bounded order (the `(C3)` route's missing input, from `LBoundSmall` = HB Lemma 2.5's
  `φ = 1/4` case); `l52HypRealFixed`, `XY/L52HypEighth*` — the same for the real case.
* `HBTheorem1_*`, `lemma8_7_*` (in flight) — the real-case inputs `HBTheorem1` (Z1) and
  `HBTable7` used for `λ₁ ≤ 0.348`.

## The obstruction found so far (superseded by the case analysis above)

`hbTable10`'s first row `(34/100, 929/1000)` — read, as the frozen statement does, as
`λ₁ ≤ 0.34 → Lam2Bound χ₁ (929/1000)` — needs, in the case `χ₂ = χ₁^{±2}` (where L92 does not
apply), the L93 certificate at `λ₂ = 0.929`; the best certifiable value there is `0.9229`
(`b+δ`-reading: `0.921`), i.e. the printed entry overstates the paper's own method by `≈0.008`.
The mathematical statement is nonetheless expected to be true (for `λ₁ ≤ 0.32` the required
`0.929` follows from Deuring–Heilbronn repulsion, `λ₂ ≳ c log(1/λ₁)`, which is a deep input not
available in this workspace).  Closing that sliver — by a better test function, by the
oscillatory bound for the twisted principal sum in the L92 derivation (for `|γ₂ − 2γ₁|` bounded
away from `0`), or by the Deuring–Heilbronn input — is the remaining mathematical work.

## Status of the supporting pieces in this workspace

* `testFn71_defs` (HB Lemma 7.1's `θ`-family: `tf71g`, `tf71f`, `tf71conv`, `tf71Fc`) — built.
* `P9F.Defs` (`tf71Fr`: the closed form of `F` on the real axis), `P9F.tf71F_real_eq`,
  `P9F._probe_stmt.exp_series_bounds`, `P9F._probe_stmt.arctan_bounds` — the certificate
  infrastructure (`θ = atan m` keeps the trigonometric values rational); in progress.
* `testFn7_2` (HB Lemma 7.2's family as a `TestFn`, with `F 0 = 8/9`, `F(−λ) = 8/5`) — proved.
* `Commons.NumberTheory.Linnik.{Ksum_positivity, Ksum_principal_le, Ksum_le_self_of_L52_phi,
  Ksum_le_single_ne_of_L52_phi, lemma6_2_assembly}` — the §5/§6 machinery used by all engines.
* `Work.LinnikAreas.Density4.Kbound_discharge` — the model for supplying `L52Hyp` from
  Area 1 (`Work.LinnikAreas.l31free.lemma3_1_free_gen`, `φ = 1/3`).
-/

/-! ## The `Lemma 9.3` row reduction

Given a *region-form* numerical certificate for a row `(a,b)` of Table 10 — for every
`λ₁ ∈ [A, a]` and every `λ₂ ∈ [λ₁, b]` the left-hand side of HB (9.14) is negative — the
`Lemma 9.3` engine (`hbLemma9_3_engine`, proved in this workspace) rules out the existence of
zeros `ρ₁` (the exceptional pair) and `ρ₂` (a second zero, of a character with `χ₂²` outside
`{χ₀, χ₁, χ₁⁻¹}`) with `λ(ρ₁) ∈ [A, a]` and `λ(ρ₂) ≤ b`, as long as `b ≤ 1`. -/
/-! ## The `Lemma 6.2` (five-term) row reduction

The `(C3)` case (`χ₁² ∈ {χ₀,χ₂,χ₂⁻¹}` and `χ₂² ∈ {χ₀,χ₁,χ₁⁻¹}`) is not covered by
`Lemma 9.2` or `Lemma 9.3`; HB uses the five-term positivity of `Lemma 6.2` there, with
`ψ = 3c` (`c = φ/2`).  The engine is proved in
`Submission/Work/ZeroFreeTables/hbLemma6_2_engine.lean` (module
`Work.ZeroFreeTables.hbLemma6_2_engine`, which is kept out of the import list here only
because its local helper lemma `zeroMult_ne_zero_of_divisor` collides with the identically
named helper of `hbLemma9_3_engine`); the reduction below takes its *conclusion* at the
given configuration as a hypothesis, exactly as P9F's `rowcontra_*` lemmas do. -/
theorem row_of_cert62 (T : TestFn) (c ε A a b : ℝ) (hε : 0 < ε) (hA : 348/1000 ≤ A)
    (hcert : ∀ u v : ℝ, A ≤ u → u ≤ a → u ≤ v → v ≤ b →
      T.F (-u) - T.F 0 - T.F (v - u) + T.f 0 * (3 * (c + ε)) < 0)
    {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ)
    (hcore : 0 ≤ T.F (-(lamOf q ρ₁)) - T.F 0 - T.F (lamOf q ρ₂ - lamOf q ρ₁) +
      T.f 0 * (3 * (c + ε)))
    (hl1 : A ≤ lamOf q ρ₁) (hl1a : lamOf q ρ₁ ≤ a) (hle : lamOf q ρ₁ ≤ lamOf q ρ₂)
    (hl2 : lamOf q ρ₂ ≤ b) : False := by
  have hneg := hcert (lamOf q ρ₁) (lamOf q ρ₂) hl1 hl1a hle hl2
  linarith only [hcore, hneg]


theorem row_of_cert93 (T : TestFn) (k ε c δ A a b : ℝ) (hk : 0 ≤ k) (hε : 0 < ε)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hA : 348/1000 ≤ A) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (hcert : ∀ u v : ℝ, A ≤ u → u ≤ a → u ≤ v → v ≤ b →
      (k ^ 2 + 1 / 2) * (T.F (-u) - T.F 0) - 2 * k * T.F (v - u) +
        T.f 0 * ((k ^ 2 + 4 * k + 3 / 2) * (c + ε)) < 0) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      (∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ c ε δ) →
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ →
      A ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ a → lamOf q ρ₂ ≤ b → False := by
  obtain ⟨q₀, hq₀⟩ := hbLemma9_3_engine T k c ε δ hk hε hδ0 hδ1
  refine ⟨q₀, fun q hq inst χ₁ χ₂ ρ₁ ρ₂ hH hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hcsq hcsq1 hcsq1'
    hl1 hl1a hl2 => ?_⟩
  have hlam2 : lamOf q ρ₂ ≤ 1 := le_trans hl2 hb1
  have hlam1 : lamOf q ρ₁ ≤ 1 := le_trans hl1a ha1
  have hlam12 : lamOf q ρ₁ ≤ lamOf q ρ₂ := isMin1_lam_le hmin.1 hZ2
  have h92 := hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ hH hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hcsq hcsq1 hcsq1'
    hlam1 hlam2
  have hneg := hcert (lamOf q ρ₁) (lamOf q ρ₂) hl1 hl1a hlam12 hl2
  linarith only [h92, hneg]


/-! ## The `Lemma 9.3` rows, assembled

Combining the region-form certificates `table10_93_cert` with the reduction `row_of_cert93`,
every row `p` of `hbTable10` with `p.1 ≥ 0.36` is covered in the case where the second zero
belongs to a character with `χ₂² ∉ {χ₀, χ₁, χ₁⁻¹}` (so that HB Lemma 9.3 applies), *provided*
the log-derivative input `L52Hyp · (1/6) ε δ` is available for all non-principal characters
(supplied in the workspace by HB Lemma 3.1 through `LBound13`). -/
theorem rowcontra93 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL52 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    {p : ℝ × ℝ} (hp : p ∈ tableR hbTable10) (ha : (36/100 : ℝ) ≤ p.1) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ →
      348/1000 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False := by
  obtain ⟨lam, k, hl, hk, hcert⟩ := table10_93_cert p hp ha
  have hp1 : p.1 ≤ 702/1000 := by
    have hmem := hp
    simp only [tableR, hbTable10, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨r, hr, rfl⟩
    rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> norm_num
  have hp2 : p.2 ≤ 929/1000 := by
    have hmem := hp
    simp only [tableR, hbTable10, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨r, hr, rfl⟩
    rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> norm_num
  obtain ⟨q₀, hq₀⟩ := row_of_cert93 (tf72T lam hl) k (1/1000000) (1/6) δ (348/1000 : ℝ) p.1 p.2
    hk (by norm_num) hδ0 hδ1 (le_refl _) (by linarith) (by linarith) hcert
  refine ⟨q₀, fun q hq inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hcsq hcsq1 hcsq1'
    hl hla hlb => ?_⟩
  exact hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ (hL52 q) hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hcsq hcsq1 hcsq1'
    hl hla hlb


/-! ## The final assembly (main line)

Reduction of `HBLemma9_4` to four route statements: the real case `λ₁ ≤ 0.348`
(`HBTheorem1` + `HBTable7`), and, for `λ₁ > 0.348`, the three F-method routes for the
*second* zero `ρ₂` (`Lemma 9.2`, `Lemma 9.3`, `Lemma 6.2`), each supplied as a
"row-`p`-contrapositive" as in `rowcontra93` above.  The case split is on the characters of the
second-minimal pair `(χ₂,ρ₂)`:
`χ₂² ∉ {χ₀,χ₁,χ₁⁻¹}` (Lemma 9.3), else `χ₁² ∉ {χ₀,χ₂,χ₂⁻¹}` (Lemma 9.2), else `(C3)`
(Lemma 6.2 with `c = 1/8`). -/

/-- Among the pairs `(χ,ρ)` of the working region with `χ ∉ {χ₁, χ₁⁻¹}` there is one of
minimal `λ` — the pair realising `λ₂`. -/
theorem exists_secondMin {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    (h : ∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ ∧ χ ≠ χ₁ ∧ χ ≠ χ₁⁻¹) :
    ∃ (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ), IsZ χ₂ ρ₂ ∧ χ₂ ≠ χ₁ ∧ χ₂ ≠ χ₁⁻¹ ∧
      ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
        lamOf q ρ₂ ≤ lamOf q ρ := by
  classical
  let cands : Finset (DirichletCharacter ℂ q × ℂ) :=
    (Finset.univ.biUnion (fun χ => (Work.A7.zeroSet χ).image (fun ρ => (χ, ρ)))).filter
      (fun p => p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹)
  have hmem_iff : ∀ p : DirichletCharacter ℂ q × ℂ,
      p ∈ cands ↔ IsZ p.1 p.2 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ := by
    intro p
    simp only [cands, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · rintro ⟨⟨χ, ρ, hρ, hpeq⟩, h2, h3⟩
      subst hpeq
      exact ⟨Work.A7.mem_zeroSet.mp hρ, h2, h3⟩
    · rintro ⟨hZ, h2, h3⟩
      exact ⟨⟨p.1, p.2, Work.A7.mem_zeroSet.mpr hZ, rfl⟩, h2, h3⟩
  have hne : cands.Nonempty := by
    obtain ⟨χ, ρ, hZ, h2, h3⟩ := h
    exact ⟨(χ, ρ), (hmem_iff _).mpr ⟨hZ, h2, h3⟩⟩
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image cands (fun p => lamOf q p.2) hne
  obtain ⟨hZ, h2, h3⟩ := (hmem_iff p).mp hp
  exact ⟨p.1, p.2, hZ, h2, h3, fun χ ρ hZ' h2' h3' =>
    hmin (χ, ρ) ((hmem_iff _).mpr ⟨hZ', h2', h3'⟩)⟩


/-- The **Lemma 6.2 route** for the Table 10 rows (the `(C3)` case): using the five-term engine
`hbLemma6_2_engine_v2` with `c = 1/8` (HB Lemma 2.5's `φ = 1/4` for characters of order `≤ 5`)
together with the region-form certificate, no configuration with `λ₁ ∈ [0.348, p.1]` and
`λ₂ ≤ p.2` exists.  The certificate is supplied here as a hypothesis so that this reduction can
be checked independently of the (in-flight) numerical file `table10_62_cert`. -/
theorem rowcontra62 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL52 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ)
    (hcert62 : ∀ p ∈ tableR hbTable10, ∃ (lam : ℝ) (hl : 0 < lam),
      ∀ u v : ℝ, u ≤ p.1 → u ≤ v → v ≤ p.2 →
        (tf72T lam hl).F (-u) - (tf72T lam hl).F 0 - (tf72T lam hl).F (v - u)
          + (tf72T lam hl).f 0 * (3 * ((1:ℝ)/8 + 1/1000000)) < 0)
    {p : ℝ × ℝ} (hp : p ∈ tableR hbTable10) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
      348/1000 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False := by
  have hp1 : p.1 ≤ 702/1000 := by
    have hmem := hp
    simp only [tableR, hbTable10, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨r, hr, rfl⟩
    rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> norm_num
  have hp2 : p.2 ≤ 929/1000 := by
    have hmem := hp
    simp only [tableR, hbTable10, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨r, hr, rfl⟩
    rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> norm_num
  obtain ⟨lam, hl, hcert⟩ := hcert62 p hp
  have hcert' : ∀ u v : ℝ, 348/1000 ≤ u → u ≤ p.1 → u ≤ v → v ≤ p.2 →
      (tf72T lam hl).F (-u) - (tf72T lam hl).F 0 - (tf72T lam hl).F (v - u)
        + (tf72T lam hl).f 0 * (3 * ((1:ℝ)/8 + 1/1000000)) < 0 :=
    fun u v _ hu huv hvb => hcert u v hu huv hvb
  obtain ⟨q₀, hq₀⟩ := hbLemma6_2_engine_v2 (tf72T lam hl) ((1:ℝ)/8) (1/1000000) δ
    (by norm_num) hδ0 hδ1
  refine ⟨q₀, fun q hq inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hl1 hl1a hl2 => ?_⟩
  have hlam12 : lamOf q ρ₁ ≤ lamOf q ρ₂ := isMin1_lam_le hmin.1 hZ2
  have h1 : lamOf q ρ₁ ≤ 1 := le_trans hl1a (by linarith)
  have h2 : lamOf q ρ₂ ≤ 1 := le_trans hl2 (by linarith)
  have hcore := hq₀ q hq χ₁ χ₂ ρ₁ ρ₂ (hL52 q) hmin hZ1 hZ2 hc1 hc2 hc21 hc21' h1 h2
  exact row_of_cert62 (tf72T lam hl) ((1:ℝ)/8) (1/1000000) (348/1000) p.1 p.2
    (by norm_num) (by norm_num) hcert' χ₁ χ₂ ρ₁ ρ₂ hcore hl1 hl1a hlam12 hl2


/-- **Uniform deadlines.**  A family of "for every `a` in a finite set there is a threshold"
statements, monotone in the threshold, has a *single* threshold. -/
theorem exists_uniform_deadline {α : Type*} (s : Finset α) (P : α → ℕ → Prop)
    (hmono : ∀ a n m, n ≤ m → P a n → P a m) (h : ∀ a ∈ s, ∃ n, P a n) :
    ∃ N, ∀ a ∈ s, P a N := by
  classical
  choose! f hf using h
  exact ⟨s.sup f, fun a ha => hmono a (f a) (s.sup f) (Finset.le_sup ha) (hf a ha)⟩

/-! ## Structural facts about the rows of Table 10 -/

/-- Every row of Table 10 has second coordinate at most `929/1000`. -/
theorem table10_p2_le {p : ℝ × ℝ} (hp : p ∈ tableR hbTable10) : p.2 ≤ 929/1000 := by
  have hmem := hp
  simp only [tableR, hbTable10, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨r, hr, rfl⟩ := hmem
  rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> (subst h; push_cast; norm_num)

/-- The first coordinate of a row of Table 10 is either `34/100` or at least `36/100`. -/
theorem table10_p1_cases {p : ℝ × ℝ} (hp : p ∈ tableR hbTable10) :
    p.1 = 34/100 ∨ (36/100 : ℝ) ≤ p.1 := by
  have hmem := hp
  simp only [tableR, hbTable10, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨r, hr, rfl⟩ := hmem
  rcases hr with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> (subst h; push_cast; norm_num)

/-! ## The `(C3)` order arithmetic

If `χ₁² ∈ {1, χ₂, χ₂⁻¹}` and `χ₂² ∈ {1, χ₁, χ₁⁻¹}` then (HB, p. 56) `χ₁` and `χ₂` have order at
most `5`; in particular `χ₁ ^ 60 = χ₂ ^ 60 = 1`. -/
theorem pow60_of_relations {q : ℕ} [NeZero q] {χ₁ χ₂ : DirichletCharacter ℂ q}
    (h1 : χ₁ ^ 2 = 1 ∨ χ₁ ^ 2 = χ₂ ∨ χ₁ ^ 2 = χ₂⁻¹)
    (h2 : χ₂ ^ 2 = 1 ∨ χ₂ ^ 2 = χ₁ ∨ χ₂ ^ 2 = χ₁⁻¹) :
    χ₁ ^ 60 = 1 ∧ χ₂ ^ 60 = 1 := by
  have key : ∀ {χ : DirichletCharacter ℂ q} {m : ℕ}, m ∣ 60 → χ ^ m = 1 → χ ^ 60 = 1 := by
    intro χ m hm h
    obtain ⟨k, hk⟩ := hm
    rw [hk, pow_mul, h, one_pow]
  have hd2 : (2:ℕ) ∣ 60 := ⟨30, rfl⟩
  have hd3 : (3:ℕ) ∣ 60 := ⟨20, rfl⟩
  have hd4 : (4:ℕ) ∣ 60 := ⟨15, rfl⟩
  have hd5 : (5:ℕ) ∣ 60 := ⟨12, rfl⟩
  -- `χ ^ n = χ ^ m` with `m ≤ n` gives `χ ^ (n - m) = 1`
  have pow_eq_one_of : ∀ {χ : DirichletCharacter ℂ q} {m n : ℕ}, m ≤ n → χ ^ n = χ ^ m →
      χ ^ (n - m) = 1 := by
    intro χ m n hmn h
    have h2 : χ ^ m * χ ^ (n - m) = χ ^ m * 1 := by
      rw [← pow_add, Nat.add_sub_of_le hmn, h, mul_one]
    exact mul_left_cancel h2
  -- `χ ^ m = χ⁻¹` gives `χ ^ (m+1) = 1`
  have pow_succ_eq_one_of : ∀ {χ : DirichletCharacter ℂ q} {m : ℕ}, χ ^ m = χ⁻¹ →
      χ ^ (m+1) = 1 := by
    intro χ m h
    rw [pow_succ', h, mul_inv_cancel]
  -- `(χ²) ^ m = 1` from `χ ^ m = 1`
  have pow2 : ∀ {χ : DirichletCharacter ℂ q} {m : ℕ}, χ ^ m = 1 → (χ ^ 2) ^ m = 1 := by
    intro χ m h
    rw [← pow_mul, Nat.mul_comm, pow_mul, h, one_pow]
  have pinv : ∀ {χ : DirichletCharacter ℂ q} {m : ℕ}, χ ^ m = 1 → (χ⁻¹) ^ m = 1 := by
    intro χ m h
    rw [inv_pow, h, inv_one]
  -- `χ ^ 4 = 1` from `χ ^ 2 = ψ` and `ψ ^ 2 = 1`
  have p4 : ∀ {χ ψ : DirichletCharacter ℂ q}, χ ^ 2 = ψ → ψ ^ 2 = 1 → χ ^ 4 = 1 := by
    intro χ ψ h1 h2
    rw [show (4:ℕ) = 2*2 from rfl, pow_mul, h1, h2]
  rcases h1 with ha | ha | ha <;> rcases h2 with hb | hb | hb
  · -- χ₁² = 1, χ₂² = 1
    exact ⟨key hd2 ha, key hd2 hb⟩
  · -- χ₁² = 1, χ₂² = χ₁
    exact ⟨key hd2 ha, key hd4 (p4 hb ha)⟩
  · -- χ₁² = 1, χ₂² = χ₁⁻¹
    exact ⟨key hd2 ha, key hd4 (p4 hb (pinv ha))⟩
  · -- χ₁² = χ₂, χ₂² = 1
    exact ⟨key hd4 (p4 ha hb), key hd2 hb⟩
  · -- χ₁² = χ₂, χ₂² = χ₁  (χ₁ ^ 3 = 1, χ₂ = χ₁²)
    have ha4 : χ₁ ^ 4 = χ₁ := by
      rw [show (4:ℕ) = 2*2 from rfl, pow_mul, ha, hb]
    have ha3 : χ₁ ^ 3 = 1 := by
      have h := pow_eq_one_of (m := 1) (n := 4) (by norm_num) (by rw [ha4, pow_one])
      simpa using h
    refine ⟨key hd3 ha3, key hd3 ?_⟩
    rw [ha.symm]
    exact pow2 ha3
  · -- χ₁² = χ₂, χ₂² = χ₁⁻¹  (χ₁ ^ 5 = 1, χ₂ = χ₁²)
    have ha4 : χ₁ ^ 4 = χ₁⁻¹ := by
      rw [show (4:ℕ) = 2*2 from rfl, pow_mul, ha, hb]
    have ha5 : χ₁ ^ 5 = 1 := by
      have h := pow_succ_eq_one_of (m := 4) ha4
      simpa using h
    refine ⟨key hd5 ha5, key hd5 ?_⟩
    rw [ha.symm]
    exact pow2 ha5
  · -- χ₁² = χ₂⁻¹, χ₂² = 1
    exact ⟨key hd4 (p4 ha (pinv hb)), key hd2 hb⟩
  · -- χ₁² = χ₂⁻¹, χ₂² = χ₁  (χ₁ ^ 5 = 1, χ₂ = (χ₁⁻¹)²)
    have hχ₂eq : χ₂ = (χ₁⁻¹) ^ 2 := by
      have h1 : χ₂ = (χ₁ ^ 2)⁻¹ := by rw [ha, inv_inv]
      rw [h1, inv_pow]
    have ha4 : χ₁ ^ 4 = χ₁⁻¹ := by
      rw [show (4:ℕ) = 2*2 from rfl, pow_mul, ha, inv_pow, hb]
    have ha5 : χ₁ ^ 5 = 1 := by
      have h := pow_succ_eq_one_of (m := 4) ha4
      simpa using h
    refine ⟨key hd5 ha5, key hd5 ?_⟩
    rw [hχ₂eq]
    exact pow2 (pinv ha5)
  · -- χ₁² = χ₂⁻¹, χ₂² = χ₁⁻¹  (χ₁ ^ 3 = 1, χ₂ = (χ₁⁻¹)²)
    have hχ₂eq : χ₂ = (χ₁⁻¹) ^ 2 := by
      have h1 : χ₂ = (χ₁ ^ 2)⁻¹ := by rw [ha, inv_inv]
      rw [h1, inv_pow]
    have ha4 : χ₁ ^ 4 = χ₁ := by
      rw [show (4:ℕ) = 2*2 from rfl, pow_mul, ha, inv_pow, hb, inv_inv]
    have ha3 : χ₁ ^ 3 = 1 := by
      have h := pow_eq_one_of (m := 1) (n := 4) (by norm_num) (by rw [ha4, pow_one])
      simpa using h
    refine ⟨key hd3 ha3, key hd3 ?_⟩
    rw [hχ₂eq]
    exact pow2 (pinv ha3)
/-- `0 ≤ λ(ρ)` for a zero `ρ` of the working region. -/
theorem lamOf_nonneg_of_isZ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hZ : IsZ χ ρ) : 0 ≤ lamOf q ρ := by
  haveI : NeZero χ.conductor := ⟨DirichletCharacter.conductor_ne_zero χ⟩
  have hβ := re_mem_Ioo_of_zeroMult_v2 χ hZ.1 hZ.2.1
  have hlogq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)))
  rw [lamOf]
  exact mul_nonneg (by linarith [hβ.2]) hlogq

/-! ## The real case `χ₁ ^ 2 = 1` (HB Lemma 6.2 with four constants)

If `χ₁ ^ 2 = 1` then `χ₁ ^ 60 = 1`, so the `1/8` supply applies to `χ₁`; with the unconditional
`1/6` supply for the other three characters, the five-term inequality of HB Lemma 6.2
(`HB94.hbLemma6_2_engine_mixed`) holds with `ψ = 1/8 + 1/6 + 1/6 = 11/24`, which the region
certificate `HB94.table10_62_cert_real` contradicts on `λ₁ ∈ [0, 348/1000]`, `λ₂ ≤ 929/1000`
(no reality of `ρ₁` is used). -/
theorem rowcontra_real (q₀ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL6 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    (hL8 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ ^ 60 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ)
    {p : ℝ × ℝ} (hp : p ∈ tableR hbTable10) :
    ∃ q₁ : ℕ, q₀ ≤ q₁ ∧ ∀ q : ℕ, q₁ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ) [NeZero χ₁.conductor]
      [NeZero χ₂.conductor] [NeZero (χ₁ * χ₂).conductor] [NeZero (χ₁ * χ₂⁻¹).conductor],
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₁ ^ 2 = 1 →
      lamOf q ρ₁ < 348/1000 → lamOf q ρ₂ ≤ p.2 → False := by
  obtain ⟨lam, hl, hcert⟩ := HB94.table10_62_cert_real
  obtain ⟨qE, hqE⟩ := HB94.hbLemma6_2_engine_mixed (tf72T lam hl) ((1:ℝ)/8) ((1:ℝ)/6) ((1:ℝ)/6)
    ((1:ℝ)/6) (1/1000000) δ (by norm_num) hδ0 hδ1
  refine ⟨max q₀ qE, le_max_left _ _, ?_⟩
  intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ _i1 _i2 _i3 _i4 hmin hZ1 hZ2 hc1 hc2 hc21 hc21'
    hsq hlt hl2
  haveI : NeZero χ₁.conductor := _i1
  haveI : NeZero χ₂.conductor := _i2
  haveI : NeZero (χ₁ * χ₂).conductor := _i3
  haveI : NeZero (χ₁ * χ₂⁻¹).conductor := _i4
  have hq' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hqE' : qE ≤ q := le_trans (le_max_right _ _) hq
  have h4 : χ₁ ^ 4 = 1 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hsq, one_pow]
  have hχ₁60 : χ₁ ^ 60 = 1 := by rw [show (60:ℕ) = 4*15 from rfl, pow_mul, h4, one_pow]
  have hneA : χ₁ * χ₂ ≠ 1 := fun h => hc21' (eq_inv_of_mul_eq_one_right h)
  have hneB : χ₁ * χ₂⁻¹ ≠ 1 := fun h => hc21 ((mul_inv_eq_one.mp h).symm)
  have hp2 : p.2 ≤ 929/1000 := table10_p2_le hp
  have h1 : lamOf q ρ₁ ≤ 1 := by linarith
  have h2 : lamOf q ρ₂ ≤ 1 := by linarith
  have hcore := hqE q hqE' χ₁ χ₂ ρ₁ ρ₂ (hL8 q hq' χ₁ hc1 hχ₁60) (hL6 q hq' χ₂ hc2)
    (hL6 q hq' (χ₁ * χ₂) hneA) (hL6 q hq' (χ₁ * χ₂⁻¹) hneB)
    hmin hZ1 hZ2 hc1 hc2 hc21 hc21' h1 h2
  have hcoef : ((1:ℝ)/8 + (1:ℝ)/6 + ((1:ℝ)/6 + (1:ℝ)/6)/2 + 1/1000000)
      = (11:ℝ)/24 + 1/1000000 := by norm_num
  rw [hcoef] at hcore
  have h0le : 0 ≤ lamOf q ρ₁ := lamOf_nonneg_of_isZ hZ1
  have hlam12 : lamOf q ρ₁ ≤ lamOf q ρ₂ := isMin1_lam_le hmin.1 hZ2
  have hneg := hcert (lamOf q ρ₁) (lamOf q ρ₂) h0le (by linarith) hlam12 (by linarith)
  linarith

/-! ## The case analysis of Lemma 9.4 -/

/-- **The case analysis of HB Lemma 9.4** for a bad pair `(χ₂,ρ₂)`, given the four routes as
hypotheses.  The four cases are: `χ₁² ∉ {1,χ₂,χ₂⁻¹}` (HB Lemma 9.2, `h92`),
`χ₂² ∉ {1,χ₁,χ₁⁻¹}` with `λ₁ ≥ 0.348` (HB Lemma 9.3, `h93`), both relations
(`(C3)`, HB Lemma 6.2 with `ψ = 3/8`, `h62`), and the small-`λ₁` cases: `χ₁² = 1` (HB Lemma 6.2
with `ψ = 11/24`, `hr`) and `5 ≤ orderOf χ₁` (HB Lemma 9.5, `hH5`). -/
theorem row_core {q : ℕ} [NeZero q] {χ₁ χ₂ : DirichletCharacter ℂ q} {ρ₁ ρ₂ : ℂ}
    (hc1 : χ₁ ≠ 1) (hc21 : χ₂ ≠ χ₁) (hc21' : χ₂ ≠ χ₁⁻¹)
    (h92 : χ₁ ^ 2 ≠ 1 → χ₁ ^ 2 ≠ χ₂ → χ₁ ^ 2 ≠ χ₂⁻¹ → False)
    (h93 : 348/1000 ≤ lamOf q ρ₁ → χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ → False)
    (h62 : (χ₁ ^ 2 = 1 ∨ χ₁ ^ 2 = χ₂ ∨ χ₁ ^ 2 = χ₂⁻¹) →
      (χ₂ ^ 2 = 1 ∨ χ₂ ^ 2 = χ₁ ∨ χ₂ ^ 2 = χ₁⁻¹) → False)
    (hr : χ₁ ^ 2 = 1 → lamOf q ρ₁ < 348/1000 → False)
    (hH5 : 5 ≤ orderOf χ₁ → lamOf q ρ₁ < 348/1000 → False) : False := by
  by_cases hA : χ₁ ^ 2 = 1 ∨ χ₁ ^ 2 = χ₂ ∨ χ₁ ^ 2 = χ₂⁻¹
  · by_cases hlt : lamOf q ρ₁ < 348/1000
    · by_cases h5 : 5 ≤ orderOf χ₁
      · exact hH5 h5 hlt
      · push_neg at h5
        by_cases hsq : χ₁ ^ 2 = 1
        · by_cases hB2 : χ₂ ^ 2 = 1 ∨ χ₂ ^ 2 = χ₁ ∨ χ₂ ^ 2 = χ₁⁻¹
          · exact h62 hA hB2
          · exact hr hsq hlt
        · -- `orderOf χ₁` is `3` or `4`
          have h1 : orderOf χ₁ ≠ 1 := fun hh => hc1 (orderOf_eq_one_iff.mp hh)
          have h2 : orderOf χ₁ ≠ 2 := fun hh => hsq (by rw [← hh]; exact pow_orderOf_eq_one χ₁)
          have h0 : 0 < orderOf χ₁ := orderOf_pos χ₁
          have hord : orderOf χ₁ = 3 ∨ orderOf χ₁ = 4 := by omega
          rcases hord with h3 | h4o
          · -- order `3`: `χ₁ ^ 2 = χ₁⁻¹ ∉ {χ₂, χ₂⁻¹}`, a contradiction
            have hχ₁3 : χ₁ ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one χ₁
            have hsqinv : χ₁ ^ 2 = χ₁⁻¹ := by
              refine eq_inv_of_mul_eq_one_right ?_
              rw [← pow_succ' χ₁ 2, hχ₁3]
            rcases hA with h | h | h
            · exact hsq h
            · exact hc21' (h.symm.trans hsqinv)
            · refine hc21 ?_
              have hχ₂ : χ₂ = (χ₁ ^ 2)⁻¹ := by rw [h, inv_inv]
              rw [hχ₂, hsqinv, inv_inv]
          · -- order `4`: `χ₂ ^ 2 = χ₁ ^ 4 = 1`
            have h4 : χ₁ ^ 4 = 1 := by rw [← h4o]; exact pow_orderOf_eq_one χ₁
            have hsqsq : (χ₁ ^ 2) ^ 2 = 1 := by
              rw [← pow_mul χ₁ 2 2]
              exact h4
            have hB2 : χ₂ ^ 2 = 1 ∨ χ₂ ^ 2 = χ₁ ∨ χ₂ ^ 2 = χ₁⁻¹ := by
              rcases hA with h | h | h
              · exact absurd h hsq
              · exact Or.inl (by rw [← h]; exact hsqsq)
              · refine Or.inl ?_
                have hχ₂ : χ₂ = (χ₁ ^ 2)⁻¹ := by rw [h, inv_inv]
                rw [hχ₂, inv_pow, hsqsq, inv_one]
            exact h62 hA hB2
    · push_neg at hlt
      by_cases hB2 : χ₂ ^ 2 = 1 ∨ χ₂ ^ 2 = χ₁ ∨ χ₂ ^ 2 = χ₁⁻¹
      · exact h62 hA hB2
      · push_neg at hB2
        exact h93 hlt hB2.1 hB2.2.1 hB2.2.2
  · push_neg at hA
    exact h92 hA.1 hA.2.1 hA.2.2

/-! ## The row contrapositive: the four routes combined -/

theorem row_contra (q₀ : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hL6 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ)
    (hL8 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ ^ 60 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ)
    (hH5 : ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → 5 ≤ orderOf χ₁ → 348/1000 ≤ lamOf q ρ₁)
    {p : ℝ × ℝ} (hp : p ∈ tableR hbTable10) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False := by
  obtain ⟨N92, hN92ge, h92⟩ := HB94.rowcontra92_all q₀ δ hδ0 hδ1 hL6 hp
  obtain ⟨N62, hN62ge, h62⟩ := HB94.rowcontra62_all q₀ δ hδ0 hδ1 hL8 hp
  obtain ⟨Nr, hNrge, hr⟩ := rowcontra_real q₀ δ hδ0 hδ1 hL6 hL8 hp
  by_cases hp36 : (36/100 : ℝ) ≤ p.1
  · obtain ⟨N93, hN93ge, h93⟩ := HB94.rowcontra93q q₀ δ hδ0 hδ1 hL6 hp hp36
    refine ⟨max (max (max N92 N62) Nr) N93, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hl1a hl2
    haveI : NeZero χ₁.conductor := ⟨DirichletCharacter.conductor_ne_zero χ₁⟩
    haveI : NeZero χ₂.conductor := ⟨DirichletCharacter.conductor_ne_zero χ₂⟩
    haveI : NeZero (χ₁ * χ₂).conductor := ⟨DirichletCharacter.conductor_ne_zero _⟩
    haveI : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨DirichletCharacter.conductor_ne_zero _⟩
    have hq92 : N92 ≤ q := by omega
    have hq62 : N62 ≤ q := by omega
    have hqr : Nr ≤ q := by omega
    have hq93 : N93 ≤ q := by omega
    have h0le : 0 ≤ lamOf q ρ₁ := lamOf_nonneg_of_isZ hZ1
    refine row_core (χ₁ := χ₁) (χ₂ := χ₂) (ρ₁ := ρ₁) (ρ₂ := ρ₂) hc1 hc21 hc21' ?_ ?_ ?_ ?_ ?_
    · intro a b c
      exact h92 q hq92 χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' a b c h0le hl1a hl2
    · intro hge a b c
      exact h93 q hq93 χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' a b c hge hl1a hl2
    · intro hA hB2
      obtain ⟨ha60, hb60⟩ := pow60_of_relations hA hB2
      have hA60 : (χ₁ * χ₂) ^ 60 = 1 := by rw [mul_pow, ha60, hb60, one_mul]
      have hB60 : (χ₁ * χ₂⁻¹) ^ 60 = 1 := by
        rw [mul_pow, ha60, inv_pow, hb60, one_mul, inv_one]
      exact h62 q hq62 χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21'
        ha60 hb60 hA60 hB60 h0le hl1a hl2
    · intro hsq hlt
      exact hr q hqr χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hsq hlt hl2
    · intro h5 hlt
      exact absurd (hH5 q (by omega) χ₁ ρ₁ hmin h5) (by linarith)
  · refine ⟨max (max N92 N62) Nr, ?_⟩
    intro q hq _inst χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hl1a hl2
    haveI : NeZero χ₁.conductor := ⟨DirichletCharacter.conductor_ne_zero χ₁⟩
    haveI : NeZero χ₂.conductor := ⟨DirichletCharacter.conductor_ne_zero χ₂⟩
    haveI : NeZero (χ₁ * χ₂).conductor := ⟨DirichletCharacter.conductor_ne_zero _⟩
    haveI : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨DirichletCharacter.conductor_ne_zero _⟩
    have hq92 : N92 ≤ q := by omega
    have hq62 : N62 ≤ q := by omega
    have hqr : Nr ≤ q := by omega
    have h0le : 0 ≤ lamOf q ρ₁ := lamOf_nonneg_of_isZ hZ1
    -- the row is `(34/100, 929/1000)`, so `λ₁ ≥ 348/1000` is impossible
    have hp34 : p.1 ≤ 34/100 := by
      by_contra hcon
      push_neg at hcon
      have h1 : p.1 = 34/100 ∨ (36/100 : ℝ) ≤ p.1 := table10_p1_cases hp
      rcases h1 with h | h
      · linarith
      · exact absurd h hp36
    have h93 : 348/1000 ≤ lamOf q ρ₁ → χ₂ ^ 2 ≠ 1 → χ₂ ^ 2 ≠ χ₁ → χ₂ ^ 2 ≠ χ₁⁻¹ → False :=
      fun hge _ _ _ => absurd (le_trans hge hl1a) (by linarith)
    refine row_core (χ₁ := χ₁) (χ₂ := χ₂) (ρ₁ := ρ₁) (ρ₂ := ρ₂) hc1 hc21 hc21' ?_ h93 ?_ ?_ ?_
    · intro a b c
      exact h92 q hq92 χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' a b c h0le hl1a hl2
    · intro hA hB2
      obtain ⟨ha60, hb60⟩ := pow60_of_relations hA hB2
      have hA60 : (χ₁ * χ₂) ^ 60 = 1 := by rw [mul_pow, ha60, hb60, one_mul]
      have hB60 : (χ₁ * χ₂⁻¹) ^ 60 = 1 := by
        rw [mul_pow, ha60, inv_pow, hb60, one_mul, inv_one]
      exact h62 q hq62 χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21'
        ha60 hb60 hA60 hB60 h0le hl1a hl2
    · intro hsq hlt
      exact hr q hqr χ₁ χ₂ ρ₁ ρ₂ hmin hZ1 hZ2 hc1 hc2 hc21 hc21' hsq hlt hl2
    · intro h5 hlt
      exact absurd (hH5 q (by omega) χ₁ ρ₁ hmin h5) (by linarith)

/-! ## HB Lemma 9.4 -/

theorem HBLemma9_4_proof : Work.ZeroFreeTables.HBLemma9_4 := by
  obtain ⟨δ₁₆, hδ₁₆0, hδ₁₆1, q₁₆, h16⟩ := HB94.L52supply16
  obtain ⟨δ₆₀, hδ₆₀0, hδ₆₀1, q₆₀, h60⟩ := HB94.L52supply_pow
  obtain ⟨qH5, hH5⟩ := HB94.h5plus_v2
  set δ : ℝ := min δ₁₆ δ₆₀ with hδdef
  have hδ0 : 0 < δ := lt_min hδ₁₆0 hδ₆₀0
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) hδ₁₆1
  have hL6 : ∀ q : ℕ, max q₁₆ q₆₀ ≤ q →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000000) δ := by
    intro q hq _inst χ _instc hχ
    exact Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ (min_le_left _ _)
      (h16 q (le_trans (le_max_left _ _) hq) χ hχ)
  have hL8 : ∀ q : ℕ, max q₁₆ q₆₀ ≤ q →
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → χ ^ 60 = 1 →
        Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ := by
    intro q hq _inst χ _instc hχ hpow
    exact Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ (min_le_right _ _)
      (h60 q (le_trans (le_max_right _ _) hq) χ hχ hpow)
  set Q : ℕ := max (max q₁₆ q₆₀) (max qH5 3) with hQdef
  have hQsupp : max q₁₆ q₆₀ ≤ Q := by omega
  have hQH5 : qH5 ≤ Q := by omega
  have hrow : ∀ p ∈ (tableR hbTable10).toFinset, ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False := by
    intro p hp
    exact row_contra Q δ hδ0 hδ1
      (fun q hq => hL6 q (le_trans hQsupp hq)) (fun q hq => hL8 q (le_trans hQsupp hq))
      (fun q hq _inst χ₁ ρ₁ hmin h5 => hH5 q (le_trans hQH5 hq) χ₁ ρ₁ hmin h5)
      (List.mem_toFinset.mp hp)
  obtain ⟨N, hN⟩ := exists_uniform_deadline (tableR hbTable10).toFinset
    (fun p n => ∀ q : ℕ, n ≤ q → ∀ [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → IsZ χ₁ ρ₁ → IsZ χ₂ ρ₂ → χ₁ ≠ 1 → χ₂ ≠ 1 →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → lamOf q ρ₁ ≤ p.1 → lamOf q ρ₂ ≤ p.2 → False)
    (fun p n m hnm h q hq => h q (le_trans hnm hq)) hrow
  refine ⟨N, ?_⟩
  intro q hq _inst χ₁ ρ₁ hmin p hp hlam1 χ ρ hZ hne1 hne2
  by_contra hcon
  push_neg at hcon
  exact hN p (List.mem_toFinset.mpr hp) q hq χ₁ χ ρ₁ ρ hmin hmin.1.1 hZ
    hmin.1.1.1 hZ.1 hne1 hne2 hlam1 (le_of_lt hcon)

end

end Work.ZeroFreeTables
