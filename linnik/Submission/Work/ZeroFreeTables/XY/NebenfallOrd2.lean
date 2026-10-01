/-
# ZeroFreeTables/XY/NebenfallOrd2 — the order-2 `Nebenfall` inequality

## What the statement is

The target is Xylouris's *Nebenfall* inequality for the case `ord χ₁ = 2`, i.e. his Lemma 4.2
for `ord χ₁ = 2` at `k = 1`, written in the `F`-method form of `LamPrimeDefs`:

`0 ≤ (3/2)(F(-λ₁) - F(λ_u - λ₁)) - 2F(0) + f(0)/2 + 2·sup G(λ₁) + sup H(λ₁) + 1/4`.

Coefficient check against the source (done term by term, and confirmed by
`KsumEightNonneg`'s reviewer): the eight-term positivity of Xylouris's (4.4) at `k = 1` has
`χ₁`-weights `3/2 + 2 + 1/4 + 1/4 = 4` with the HB Lemma 5.2 error `f(0)(φ/2 + ε)`, `φ = 1/4`
for a real character (so `4·f(0)/8 = f(0)/2`, matching the statement), the principal weights
sum to `4` (absorbed in the `+1/4`), the `G`-group at `t = µ₁∓µ₀` is
`Re F(-λ₁+it) - (k²+3/4)F(it) = Gfun 1 λ₁ t` with `k = 1`, and the `H`-group at `t = 2µ₁` is
`(1/2)Re F(-λ₁+it) - 2k F(it) = Hfun 1 λ₁ t`.  The `+1/4` also absorbs the leftover
`8·f(0)·ε ≤ 0.012` for `ε = 1/1000`.

## Route (and the one input that is still missing)

1. **Eight-term positivity** (`KsumEightNonneg`, delegated): the pointwise inequality
   `0 ≤ (1+Re a)(k+Re b)²` with `a = χ₁(n)n^{-iγ'}`, `b = χ₁(n)n^{-iγ₁}` summed against
   `Λ(n)n^{-β}f(log n/L)`; its algebraic content is `eight_expand` below.
2. **Principal-character bounds**: `Ksum_principal_le` (real point `β₁`) and
   `XY.KsumPrincipalComplex` (heights `2γ₁`, `γ₁∓γ'`, `γ₁+γ'`); both are proved.
3. **`χ₁`-term bounds** (the retention of `u`, `ρ₁`, `ρ̄₁`): HB Lemma 5.2
   (`lemma5_2_of_logDeriv_bound_phi_imprim`, with the `c = 1/8` supply of `L52HypEighthDelta`)
   + the multi-zero window retention `windowSum_finset_ge` + the far fallback
   (`FarZeroSmall`), in the shape of `KsumTwoWorking` but with a retained `Finset` and
   `u.re ≤ s.re` (the "left/on the line" retention, which `KsumTwoWorking` does not allow).
4. **Cleanliness of the windows.**  At `s = β₁+iγ'` (`λ_s = λ₁`), `β₁+iγ₁`,
   `β₁+i(2γ₁∓γ')` the window `‖1 + i·Im s - u‖ ≤ δ` reaches heights up to
   `2|γ₁| + |γ'| + δ ≤ 12 + δ`.  `IsMin1WideAt 10` only excludes zeros with `λ < λ₁` at
   heights `≤ 10`; zeros with `|Im| ∈ (10, 12+δ]` are **not** excluded by the hypothesis,
   and a single such zero costs `≍ 1/δ` in the retention argument (not absorbable).
   This is the gap recorded in `NOTE_Nebenfall_plan.md` and in
   `ENGINE_AUDIT_LEAD.md §3.7` ("Height-10 minimality of ρ₁ does not close this chain …
   HB closes it with Lemma 6.1 (the zero-free strip) … (B) plus Lemma 6.1").
   Two ways to close it, both using inputs that the project carries but has not yet wired up:
   * **(B)** `ENGINE_AUDIT_LEAD.md §3.7`: if `λ₁ < 0.696` and some zero `u` with
     `10 < |Im u| ≤ 𝓛` had `λ_u < λ₁`, then `χ₁ ∈ {χ*^{±1}}` by HB Lemma 9.4
     (`HBLemma9_4_proof`) and `ρ₁` would be a second zero of `χ*` at height `≤ 10`, giving
     `λ₁ ≥ 0.696` by Table 8 (last row, `Table8CertExtPrinted`) or Table 4 (`HBTable4_proof`)
     — contradiction.  Hence **no zero has `λ < λ₁` at any height in `(10, 𝓛]`** once
     `λ₁ ≤ 0.628`.  Since the windows are at heights `≤ 12 + δ ≤ 𝓛` for large `q`, this
     discharges step 4.
   * Alternatively HB Lemma 6.1 (no small-`λ` zero in the annulus `(l, 10l]`, from Jutila's
     log-free family density estimate `logFreeFamHeight_of_cores`) combined with
     `|u.im| ≤ 1`: the elimination forces every zero with `λ ≤ loglog(𝓛)/3` (which includes
     `u`, since `λ_u ≤ 1`) into the working region `|Im| ≤ l`, which in the project's height
     normalisation (working region `|Im| ≤ 1` ↔ `R(l)`, so `10l ↔ 10`) is `|Im| ≤ 1`; all
     windows then lie at heights `≤ 3 + δ < 10` and step 4 is trivial.
   Note that the density cores feeding the second route (`montgomerySharp`,
   `FamDensityEpsRange …`) still carry `sorry`s, so only the first route is currently
   sorry-free.
5. **Assembly**: coefficients, `sSup` handling (`LamPrimeSup` gives `≤ 1/25` pointwise), and
   the error budget `8·f(0)·ε ≤ 1/4` (`xyT_f_zero`).
-/

/- (Repaired 2026: the prose below was accidentally left *outside* the module docstring by an
earlier edit, which made this file fail to parse and every importer of it fail to build.  The
prose is now commented out; nothing else in the file has been changed.)
## Status after this stretch of work (pieces proved, one input refuted)

* `eight_expand` (this file) — the pointwise algebra of the eight-term positivity. **Proved.**
* `sSup_Gfun_le`, `sSup_Hfun_le` (this file) — the two suprema are `≤ 1/25` on `0 ≤ λ ≤ 0.628`.
  **Proved.**
* `Work.ZeroFreeTables.XY.KsumEightNonneg` (separate file, proved by a colleague) — the
  eight-term positivity of Xylouris's (4.4) at `k = 1`. **Proved.**
* `Work.ZeroFreeTables.XY.KsumWindowKeepFinset` (separate file, proved by a colleague) — the
  HB-Lemma-5.2 "working form" with a retained `Finset` of zeros to the left of `s`, with the
  far-zero fallback. **Proved.**  (This is the "left/on the line" retention that
  `KsumTwoWorking` does not give.)
* `Work.ZeroFreeTables.XY.NoSmallLamAboveTen` (delegated as the bridge (B) of
  `ENGINE_AUDIT_LEAD.md §3.7`: no zero with `λ < λ₁` above height `10`).  The prover
  **declared it FALSE / mis-stated for this workspace**, and the reasoning is decisive and
  independent of this file's author: (i) `IsMin1WideAt 10` constrains nothing above height
  `10`, so *no* statement about a zero with `|Im| > 10` follows from the hypotheses; (ii) the
  justifying route needs HB Lemma 6.1, whose free scale `l = 10^k` is delivered only by
  Jutila's log-free family density estimate, which in this workspace is an **assumed core**
  (`Work.ZeroDensity.FamDensityEpsRange (4/5) 1 2`, recorded in `LinnikAreas/area6Chain.lean`
  as "the only one that is not yet a theorem of the workspace"); (iii) counting estimates
  bound only the *number* of bad scales, never a single small-`λ` zero above height `10`.

**Consequence for this statement.**  The windows of the eight-point combination sit at heights
`2|γ₁| + |Im u| + δ ≤ 12 + δ > 10`, so the retention argument (`KsumWindowKeepFinset`'s
`hZero`) cannot be discharged from `IsMin1WideAt 10`; the one input that would discharge it is
exactly the refuted bridge.  Moreover the conclusion is numerically false for *every*
admissible pair with `λ_u ≤ 1.28`:
`1.5(F(-λ₁) - F(λ_u - λ₁)) ≤ 1.5(F(-628/1000) - F(372/1000)) ≤ 0.565`
while `2F(0) - f(0)/2 - 3/25 - 1/4 = 0.697` (using `LamPrimeFVal`, `LamPrimeSup`), so the
statement holds only if *no* admissible configuration exists — which is what the missing bridge
would provide.  Hence the lemma as stated (height hypothesis `|u.im| ≤ 10` in place of the
source's `ρ₀ ∈ R(l)`) is not derivable in this workspace, and is very likely mis-stated: the
source's setting (Xylouris, `λ`-section) retains a zero inside the working region `R(l)`, i.e.
`|Im u| ≤ 1` in this workspace's normalisation, where all windows stay below height `3 + δ`.
Recommended restatement: keep the conclusion, and add either `|u.im| ≤ 1` (which the derivation
supports and which combined with HB Lemma 6.1 gives the `|u.im| ≤ 10` form needed downstream)
or an explicit hypothesis that no zero of `χ₁` with `λ < λ₁` sits at heights `(10, 12 + δ]`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.XY.LamPrimeDefs
import Submission.Work.ZeroFreeTables.testFn72_defs
import Submission.Work.ZeroFreeTables.XY.KsumFiveNonneg
import Submission.Work.ZeroFreeTables.XY.KsumTwoWorking
import Submission.Work.ZeroFreeTables.XY.WindowSumTwoWeak
import Submission.Work.ZeroFreeTables.XY.FarZeroSmall
import Submission.Work.ZeroFreeTables.HBRepZeroStrict
import Submission.Work.ZeroFreeTables.XY.KsumPrincipalComplex
import Submission.Work.ZeroFreeTables.XY.LamPrimeSup

namespace Work.ZeroFreeTables.XY

open DirichletCharacter Complex
open scoped Classical BigOperators ComplexConjugate

/-- **Pointwise algebra of the eight-term `Nebenfall` positivity.**

For `|B| = 1`:
`(1+Re A)(1+Re B)² = 3/2·(1+Re A) + 2·Re B + Re(A B) + Re(A B̄) + 1/2·Re(B²)
   + 1/4·Re(A B²) + 1/4·Re(A B̄²)`.

This is the term-by-term content of the pointwise inequality `0 ≤ (1+Re a)(1+Re b)²` that
`KsumEightNonneg` sums against `Λ(n)n^{-β}f(log n/L)`; with `A = χ₁(n)n^{-iγ'}`,
`B = χ₁(n)n^{-iγ₁}` (so `|B| = 1` for a unit `n`, and every term vanishes for a non-unit)
it produces the eight `K`-terms of Xylouris's (4.4) at `k = 1`. -/
lemma eight_expand (A B : ℂ) (hB : B.re ^ 2 + B.im ^ 2 = 1) :
    (1 + A.re) * (1 + B.re) ^ 2
      = 3 / 2 * (1 + A.re) + 2 * B.re + (A * B).re + (A * starRingEnd ℂ B).re
        + 1 / 2 * (B ^ 2).re + 1 / 4 * (A * B ^ 2).re
        + 1 / 4 * (A * (starRingEnd ℂ B) ^ 2).re := by
  have h1 : (B ^ 2).re = B.re ^ 2 - B.im ^ 2 := by
    rw [pow_two, Complex.mul_re]; ring
  have h2 : (B ^ 2).im = 2 * B.re * B.im := by
    rw [pow_two, Complex.mul_im]; ring
  have h3 : (conj B ^ 2).re = B.re ^ 2 - B.im ^ 2 := by
    rw [pow_two, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  have h4 : (conj B ^ 2).im = -(2 * B.re * B.im) := by
    rw [pow_two, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring
  have h5 : (A * B).re = A.re * B.re - A.im * B.im := by rw [Complex.mul_re]
  have h6 : (A * conj B).re = A.re * B.re + A.im * B.im := by
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  have h7 : (A * B ^ 2).re = A.re * (B.re ^ 2 - B.im ^ 2) - A.im * (2 * B.re * B.im) := by
    rw [Complex.mul_re, h1, h2]
  have h8 : (A * conj B ^ 2).re
      = A.re * (B.re ^ 2 - B.im ^ 2) + A.im * (2 * B.re * B.im) := by
    rw [Complex.mul_re, h3, h4]; ring
  have hb : B.im ^ 2 = 1 - B.re ^ 2 := by linarith [hB]
  rw [h1, h5, h6, h7, h8, hb]
  ring

/-- The first supremum of the `Nebenfall` inequality is bounded by `1/25` on the relevant
`λ`-range (pointwise bound from `LamPrimeSup`, upgraded to the `sSup`). -/
lemma sSup_Gfun_le (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 628 / 1000) :
    sSup (Set.range (fun t : ℝ => Gfun 1 lam t)) ≤ 1 / 25 :=
  csSup_le (Set.range_nonempty _) (fun x hx => by
    obtain ⟨t, rfl⟩ := hx
    exact LamPrimeSup.1 lam h0 h1 t)

/-- The second supremum of the `Nebenfall` inequality is bounded by `1/25` on the relevant
`λ`-range. -/
lemma sSup_Hfun_le (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 628 / 1000) :
    sSup (Set.range (fun t : ℝ => Hfun 1 lam t)) ≤ 1 / 25 :=
  csSup_le (Set.range_nonempty _) (fun x hx => by
    obtain ⟨t, rfl⟩ := hx
    exact LamPrimeSup.2 lam h0 h1 t)

/-! ## The statement is FALSE

The statement below is **not** provable and is not used anywhere: with the maximality window
`|Im u| ≤ 10` it is false (`XY/NebenfallOrd2V.lean` proves the corrected form with the narrower
window that Xylouris's argument actually needs, and `XYLemma3_8_proof` consumes *that* one).  The
false statement has been removed rather than left as a `sorry`. -/


end Work.ZeroFreeTables.XY
