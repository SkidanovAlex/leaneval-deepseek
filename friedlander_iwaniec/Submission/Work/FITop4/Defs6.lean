/-
# `Submission.Work.FITop4.Defs6` — ROUND 6 of the FI area (B) contract: the corrected kernel

Round 5 (`Submission/Work/FITop4/Red5/`) closed the `§§4–5.2` reduction and proved
`prop41_of_areas5 : Area1Sieve → … → Area7 → Prop41StatementPiBig`.  Round 6 repairs the
**main-term kernel**, following the machine-checked finding of `Submission/Work/FIArea2`
(sessions 2–7) and the project lead's `ROUND6_SPEC.md`.

## The defect (area 2's report, machine-checked)

The frozen kernel `Work.FIPlan.G0 z₁ z₂ = 2Σ_{4d|Δ}(φ(d)/d)·(Re(z̄₁z₂)|d)` is **not** *FI*'s `G₀`
of (6.12)/(8.16).  The paper's kernel is the *count*

  `G₀(z₁,z₂) = |Δ|⁻¹·#{(γ₁,γ₂) ∈ (ℤ/|Δ|)² : γ₁²z₂ ≡ γ₂²z₁ (mod |Δ|)}`

and (8.16) evaluates it as `2Σ_{4d|Δ}(φ(d)/d)(a|d)` with `a` the residue **(6.6)** of `z₂/z₁`
(`a ≡ Re(z̄₁z₂)·|z₁|⁻² (mod |Δ|)`), *not* with the symbol of `Re(z̄₁z₂)`.  The two kernels differ
by the quadratic character `(|z₁|²|d)`:

  `G0_frozen = 2Σ_{4d|Δ}(φ(d)/d)(z₂/z₁|d)·(|z₁|²|d)`.

Witnesses (machine-checked, `FIArea2/G0_defect.lean`, `FIArea2/MainTermFix.lean`): at
`z₁ = 1+4i, z₂ = 1+28i` (a pair satisfying every hypothesis of Lemma 8.4) the count is `120`,
so `G₀ = 5`, while `G0_frozen = 1`; at `z₁ = 11−10i, z₂ = 13−12i` the frozen kernel is `0`
(the `4d|Δ`-sum is empty) while the count is `2`, so `G₀ = 1`.  The twist is *not* trivial:
`FIArea7/ReSymbolTwist.lean` (`twist_nontrivial`) exhibits admissible data with `(|z₁|²|d) = −1`
(167908 of 342318 admissible pairs), and area 7's report §31 records that the frozen symbol breaks
the §17 reflection route (`σ` is not a product on the frozen symbol).

The **second** defect is the `f̂(0)` normalisation.  The paper's `f` is a function of `|w|`
(§7: "`f(w) = f(|w|)`", (7.7) `f̂(0) = ∫₀^∞f(u)du ≪ M^{1/2}`), while the frozen vocabulary applies
`f` to `gnorm w = |w|²`, so the frozen `Fhat Pa f = Σ_u f(u)u^{-1/2}` is `2f̂(0)` (§7's measure is
`d|w| = du/(2√u)`).  The frozen `C0mod` carries the factor `2f̂(0)` of (7.10) *together with* an
`f̂(0)` that is already twice the paper's, so the frozen main term is asymptotically twice the
correct one; correspondingly the frozen `cMain = 2f̂(0)N^{-1/2}` must become
`Fhat·N^{-1/2}` (see `C0`, `cMain6` below).

## What this file defines

* the corrected kernel `G0 := Work.FIArea2.G0fix = Cnt/|Δ|` (the count (6.12)), and `C0`, `D0`
  built on it with the paper's (6.13)/(7.10) normalisation in the `|w|²`-convention:
  `C₀ = |z₁z₂|^{-1/2}·f̂(0)·log(2|z₁z₂/Δ|)·G₀` with `f̂(0) = Fhat Pa f`;
* `cMain6 fhat N = fhat·N^{-1/2}`, so that (10.4) reads `D₀ = cMain6·T(β) + O(…)\;
* the paper's `T(β)` (10.5) on the corrected kernel, and the cut family (10.13)/(10.15)–(10.17)
  built on **one** ratio symbol `Work.FIArea7.ratioSym z₁ z₂ d = (z₂/z₁|d)`, the Jacobi symbol of
  the residue (6.6) — shared by `D₀`, `T(β)` and the three cuts, as the lead's addendum requires;
* `IsBetaCoeff6`: the round-4 coefficient of (4.13)/(5.13) *with the (5.7) restriction to one
  class mod 8* built into its support — `β_z = q(α)p(n)μ(n)γ(n;C)` for `z` in the polar box
  (5.14), free of small primes (5.8), with `τ(n) ≤ τ` (5.9) **and `z ≡ z₀ (mod 8)`** (5.7), and
  `0` otherwise;
* `IsMajorant6`: a `C⁴` real function `F` (the paper's §7 hypothesis at (7.1)), with `f := F|_ℤ`
  a round-3 `IsMajorant`, so that every estimate of round 4 transfers (`toMajorant`).
-/
import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FIArea2.G0_defect
import Submission.Work.FIArea7.ReSymbolTwist

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FITop4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The corrected kernel and the main-term objects of §§6–10 -/

/-- **The corrected kernel of (6.12)/(8.16)**: the count `Cnt` of (6.12) divided by `|Δ|`.  This is
*FI*'s `G₀`, equal to `2 Σ_{4d|Δ}(φ(d)/d)(z₂/z₁|d)` by Lemma 8.4
(`Red6.Cnt_eq_two_sum_base`, the clash-free copy of `Work.FIArea2.Cnt_eq_two_sum_of_primitive`),
and *not* the frozen `Work.FIPlan.G0`.

This is *definitionally* `Work.FIArea2.G0fix` (the same formula with the same `Cnt`), but it is
defined from `Submission.Work.FIArea2.G0_defect` + `Red6/Cnt_eq_two_sum_base` rather than from
`G0_fix.lean`, because `G0_fix` reaches `Work.FITop3.Areas3` and `Work.FITop3.Witness.*`, whose
declarations clash with the `Work.FIArea1.shim.*` / `Work.FIArea5` copies that the round-4 → round-6
bridges of `Area1Sieve6`/`Area5_6` must import.  With this definition `Defs6` (and hence `Areas6`)
can be imported alongside those copies. -/
def G0 (z1 z2 : GaussianInt) : ℝ :=
  (Work.FIArea2.Cnt z1 z2 : ℝ) / (Work.FIPlan.absDelta z1 z2 : ℝ)

/-- **(7.9)+(7.10) in the `|w|²`-convention**: `log(8|z₁z₂|/|Δ|)`.

The paper's (7.9)/(7.10) read `E(γ) = log 4δ^{-2} + O(δ²log δ^{-2})` and
`F₀ = f̂(0)·2log(2|z₁z₂/Δ|) + O(…)` with `δ = |Δ|/|z₁z₂|`.  The *exact* asymptotic constant of
the elliptic integral is `64` (`Work.FIArea2.ellInt_asymptotic`: `E(γ) − log(64/δ²) → 0`, the gap to
the paper's `log 4δ^{-2}` being `log 16 = 2.7726…`, checked numerically by the lead at
`δ = 10^{-2} … 10^{-4}`), and in the frozen `|w|²`-convention `f̂(0) = Fhat/2`, so the leading term
of (7.10) is

  `F₀ = (Fhat/2)·log(64|z₁z₂|²/Δ²) + O(δ²log) = Fhat·log(8|z₁z₂|/|Δ|) + O(δ²log)`.

This is the weight shared by `C0`, `Tbeta` and the cuts (so the (10.4) identity
`D₀ = cMain6·T(β)` is consistent); it is `Work.FIArea2.MainTermFix.fLogFix`.  (The round-4/5
vocabulary used `Work.FITop3.logFac = log(2|z₁z₂|/|Δ|)`, the paper's `2log(2|z₁z₂/Δ|)` prefactor
*combined with* the `|w|²`-normalisation of `Fhat` — off by the constant `log 4` in the leading
term and by a factor `2` asymptotically.) -/
def logFac6 (z1 z2 : GaussianInt) : ℝ :=
  Real.log (8 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
    / (Work.FIPlan.absDelta z1 z2 : ℝ))

/-- The index set of (8.16)/(10.13): `1 ≤ d ≤ |Δ|/4 + 1` with `4d ∣ |Δ|`. -/
def Sset (z1 z2 : GaussianInt) : Finset ℕ :=
  (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
    (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2)

/-- ***FI*'s symbol `χ_d(z₂/z₁) = (z₂/z₁|d)`** of (8.14), (10.2), (10.13): the Jacobi symbol of the
*rational* residue (6.6) of the Gaussian ratio `z₂/z₁`, `Re(z̄₁z₂)·|z₁|²⁻¹ (mod d)`.  This is the
single symbol shared by `D₀`, `T(β)` and the three cuts (the lead's round-6 addendum); the frozen
`TcutMod` used the symbol of `Re(z̄₁z₂)` instead, which differs by `(|z₁|²|d)`. -/
abbrev ratioSym := Work.FIArea7.ratioSym

/-- **(6.13)+(7.10) with the corrected kernel and the `|w|²`-convention.**  In the frozen
convention (`f` applied to `gnorm w = |w|²`, `f̂(0) = Fhat Pa f`) the paper's
`F₀ = f̂(0)·E(γ) = f̂(0)·log(64δ^{-2}) + O(δ²log)` with `δ = |Δ|/|z₁z₂|` reads
`F₀ = Fhat·log(2|z₁z₂/Δ|) + O(δ²log)`, because `Fhat = 2f̂(0)`.  Hence

  `C₀ = |z₁z₂|^{-1/2}·Fhat·log(2|z₁z₂/Δ|)·G₀`.

(Compare the frozen `Work.FITop3.C0mod = |z₁z₂|^{-1/2}·2Fhat·log(2|z₁z₂/Δ|)·G0_frozen`.) -/
def C0 (fhat : ℝ) (z1 z2 : GaussianInt) : ℝ :=
  (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) * fhat
    * logFac6 z1 z2 * G0 z1 z2

/-- **(9.11) with the corrected main term**: `D₀(M,N) = Σ_{(z₁,z₂)=1} β_{z₁}β̄_{z₂}C₀(z₁,z₂)`. -/
def D0 (Rz : ℤ) (fhat : ℝ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.GaussCoprime z1 z2 then
      β z1 * star (β z2) * (C0 fhat z1 z2 : ℂ) else 0)

/-- **(10.4) in the `|w|²`-convention**: the paper has `D₀ = 2f̂(0)N^{-1/2}T(β) + O(…)` and
`2f̂(0) = Fhat`, so the composition of (10.10) reads
`D₀ = fhat·N^{-1/2}·T(β) + O((τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^{20}})`.  `cMain6` is that
factor; compare the frozen `Work.FIPlan.cMain fhat N = 2fhat·N^{-1/2}`, too large by a factor
`2`. -/
def cMain6 (fhat N : ℝ) : ℂ := ((fhat * N ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)

/-- **(10.5) on the corrected kernel**: `T(β) = Σ_{(z₁,z₂)=1} β_{z₁}β̄_{z₂}G₀(z₁,z₂)log(2|z₁z₂/Δ|)`
with `G₀ = G0 = Cnt/|Δ|`. -/
def Tbeta (Rz : ℤ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.GaussCoprime z1 z2 then
      β z1 * star (β z2) * ((G0 z1 z2 * logFac6 z1 z2 : ℝ) : ℂ) else 0)

/-- **(10.13) on the corrected kernel**: the *same* `T(β)`, re-expanded by (8.16) and summed over
the modulus `d` with a cut function.  The symbol is `χ_d(z₂/z₁) = (z₂/z₁|d)` — one ratio symbol
for `D₀`, `T(β)` and the cuts.

`T(β) = Tcut (fun _ _ _ => 1) β` is *not* definitional; it is the identity (8.16) applied to the
count kernel, valid on the support of a coefficient satisfying (5.7)+(5.8)
(`Red6.Tbeta_partition`). -/
def Tcut (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ) (β : GaussianInt → ℂ) : ℂ :=
  2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.GaussCoprime z1 z2 then
      (β z1 * star (β z2)) *
        ((∑ d ∈ Sset z1 z2,
            ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
              * (ratioSym z1 z2 d : ℝ) * logFac6 z1 z2) : ℂ)
     else 0)

/-- (10.15) on the corrected kernel: the small moduli `d ≤ X`. -/
def Ucut (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Tcut Rz (fun _ _ d => if d ≤ X then (1 : ℝ) else 0) β

/-- (10.16) on the corrected kernel: the middle moduli `X < d ∧ 4dX < |Δ|`. -/
def Vcut (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Tcut Rz (fun z1 z2 d =>
    if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β

/-- (10.17) on the corrected kernel: the large moduli `X < d ∧ 4dX > |Δ|`. -/
def Wcut (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Tcut Rz (fun z1 z2 d =>
    if X < d ∧ 4 * d * X > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β

/-- The boundary `X < d ∧ 4dX = |Δ|` on the corrected kernel. -/
def Bcut (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Tcut Rz (fun z1 z2 d =>
    if X < d ∧ 4 * d * X = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β

/-- `Tcut` with the constant cut `1` — the (10.13)-expansion of `T(β)`. -/
def TcutOne (Rz : ℤ) (β : GaussianInt → ℂ) : ℂ := Tcut Rz (fun _ _ _ => (1 : ℝ)) β

/-- The class of `z` modulo `8`: `(Re z mod 8, Im z mod 8)`.  `ℤ[i]/(8)` has `64` classes, which
is what the partition of (5.7) by residue classes mod eight realises (the paper's "splitting
`B*(M,N)` into eight such classes" restricts to the primary classes; no estimate below is
sensitive to the extra factor `8`). -/
def cls8 (z : GaussianInt) : ZMod 8 × ZMod 8 := ((z.re : ZMod 8), (z.im : ZMod 8))

/-- **(5.7)**: `z` lies in the fixed class `z₀` modulo eight. -/
def SameClass8 (z z0 : GaussianInt) : Prop := cls8 z = cls8 z0

/-- A representative Gaussian integer of a class modulo eight: the class `c = (a,b)` is
represented by `a.val + b.val·i`.  Every class of `ℤ[i]/(8)` is of this form, so
`ZMod 8 × ZMod 8` indexes the `64` classes. -/
def rep8 (c : ZMod 8 × ZMod 8) : GaussianInt :=
  (Zsqrtd.mk (c.1.val : ℤ) (c.2.val : ℤ) : Zsqrtd (-1))

lemma cls8_rep8 (c : ZMod 8 × ZMod 8) : cls8 (rep8 c) = c := by
  refine Prod.ext ?_ ?_
  · show (((c.1.val : ℤ)) : ZMod 8) = c.1
    push_cast
    exact ZMod.natCast_zmod_val c.1
  · show (((c.2.val : ℤ)) : ZMod 8) = c.2
    push_cast
    exact ZMod.natCast_zmod_val c.2

lemma sameClass8_rep8_iff (z : GaussianInt) (c : ZMod 8 × ZMod 8) :
    SameClass8 z (rep8 c) ↔ cls8 z = c := by
  unfold SameClass8
  rw [cls8_rep8]

/-! ## 2. The coefficient family (4.13)+(5.13)+(5.7), and the §7 majorant -/

/-- **The axis-free region of *FI* §5, at the paper's threshold `ϑ√N`.**

*FI* p. 970, immediately after (5.16): *"We can assume that `|φ mod π/2| > πϑ` because the other
sectors, altogether of angle `≤ 2πϑ`, contribute no more than the bound (4.23) by the estimate
(5.16).  For `z = r + is` in any remaining polar box we are not near either axis, and hence
`√ϑ√N < |r|, |s| < 2√N`."*  A point of a polar box whose sector is at angular distance `> πϑ`
from the axes has `|arg z mod π/2| > πϑ − 2πθ > πϑ/2`, whence `|cos(arg z)| ≥ sin(πϑ/2) ≥ ϑ` and
`|r| = |z||cos(arg z)| > ϑ√(Pa.N)` (using `|z| > √(Pa.N)` from (5.14)); dually for `|s|`.  The
sector-scale threshold is therefore

  `Pa.ϑ * Real.sqrt Pa.N < |Re z| ∧ Pa.ϑ * Real.sqrt Pa.N < |Im z|`

(the paper's written `√ϑ√N` is the same quantity up to the harmless convention that `√ϑ√N` is the
*lower* bound obtained with the `sin ≥ 2x/π` constant, while the elementary form used here is
`ϑ√N`, which is *smaller* by the factor `√ϑ` and hence a weaker — i.e. safer — hypothesis).

**Why not `√(ϑ·N)`?**  The round-6 draft wired `√(Pa.ϑ·Pa.N) < |Re z|` into the support; this
excludes a *band* of angular width `≈ √ϑ` around each axis (`≍ √ϑ·N` lattice points per dyadic
annulus, since `θ ≪ ϑ²` makes every sector of the partition of (5.12) thinner than `√ϑ`), whereas
the paper's §5 exclusion has total angle `≤ 2πϑ`, i.e. `≍ ϑ·N` points.  The two differ by the
factor `ϑ^{-1/2} = (log x)^{A/2}`: with `ϑ = (log x)^{-10^8}` the band's (5.16)-trivial
contribution `≍ √ϑ(MN)^{3/4}(log)^{O(1)} = (log x)^{-5·10^7+O(1)}(MN)^{3/4}` exceeds the frozen
target's allowance `(log x)^{4-Astar}(MN)^{3/4} = (log x)^{-6.7·10^7}(MN)^{3/4}`, so no constant in
the reduction's error term can absorb it, and the reduction *cannot* produce coefficients with the
`√(ϑN)`-support; with the sector-scale threshold above, the excluded zone is the paper's
`≍ ϑ·N`-point zone, whose trivial contribution `≍ ϑ(MN)^{3/4}(log)^{O(1)}` is below both error
terms of the reduction (`ϑ ≤ ϑ^{3/4}` and `(log)^{O(1)} ≤ (log)^{65536}`).  See
`Submission/Work/FITop6/AxisDefs.lean` and `Submission/Work/FITop6/NOTES.md` for the machine-checked
comparison `ϑ√N < √(ϑN)` (strictly, for `0 < ϑ < 1`) and the arithmetic. -/
def IsAxisFree (Pa : Work.FITop.Params) (z : GaussianInt) : Prop :=
  Pa.ϑ * Real.sqrt Pa.N < |(z.re : ℝ)| ∧ Pa.ϑ * Real.sqrt Pa.N < |(z.im : ℝ)|

/-- **The coefficient family `β` of (4.13)+(5.13), with the (5.7) restriction to one class
mod `8`.**  This is round 4's `IsBetaCoeff` with the paper's standing normalisation (5.7)

  `z ≡ z₀ (mod 8)`

built into the support: there are fixed mollifiers `q` (angular, sector (5.12), `C²` with
`|q^{(j)}| ≤ c_jθ^{-j}`, `j ≤ 2`) and `p` (radial, segment (4.12), `C²` with `|p^{(j)}| ≤
c_j(θN)^{-j}`, `j ≤ 2`) with

  `β_z = q(arg z − φ)·p(|z|²)·μ(|z|²)·γ(|z|²;C)`

for every `z` in the polar box (5.14) that is free of small primes (5.8), has `τ(|z|²) ≤ τ` (5.9)
**and** lies in the class of `z₀` modulo eight, and `β_z = 0` otherwise.

(5.7) is *not* a consequence of (4.13)+(5.13): the polar box (5.14) has `≍ θ²N ≫ 1` lattice points
spread over all `64` classes mod eight.  It is imposed as the paper does — "we regard `β_z` as a
function supported on numbers having a fixed residue class modulo eight … this can be accomplished
by splitting `B*(M,N)` into eight such classes" — and it is exactly what the (8.16) evaluation of
`G₀` needs: `z₁ ≡ z₂ (mod 8)` gives `8 ∣ |Δ|` (`eight_dvd_absDelta_of_congr`), hence `4 ∣ |Δ|`
and `a ≡ 1 (mod 8)` (`a_mod_eight`), the two side conditions of Lemma 8.4 that the `z₂/z₁`
residue supplies. -/
def IsBetaCoeff6 (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) : Prop :=
  ∃ q p : ℝ → ℝ,
    ContDiff ℝ 2 q ∧ ContDiff ℝ 2 p ∧
    (∀ α, 0 ≤ q α) ∧ (∀ α, q α ≤ 1) ∧
    (∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ) ∧
    (∀ j : ℕ, j ≤ 2 → ∀ α : ℝ, |iteratedDeriv j q α| ≤ cMoll j * Pa.θ ^ (-(j : ℝ))) ∧
    (∀ u, 0 ≤ p u) ∧ (∀ u, p u ≤ 1) ∧
    (∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) ∧
    (∀ j : ℕ, j ≤ 2 → ∀ u : ℝ,
      |iteratedDeriv j p u| ≤ cMoll j * (Pa.θ * Pa.N) ^ (-(j : ℝ))) ∧
    (∀ z : GaussianInt, β z =
      (if InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
          (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ SameClass8 z z0
          ∧ IsAxisFree Pa z
       then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
       else 0))

/-- The absolute constants `c_j` of the §7 majorant's derivative bounds (round 6.3): `c_0 = 1`,
`c_1 = 8`, `c_2 = 64` — so that the round-3 second-difference clauses follow by the mean-value
theorem — and `2^{12j}` for `j = 3, 4`.  Every one of them is met by a clamped `C⁴` bump of width
`≍ M` rescaled to the annulus (5.19) (see `Defs6.cMaj`'s use in `Witness6`). -/
def cMaj (j : ℕ) : ℝ := if j ≤ 2 then (2 : ℝ) ^ (3 * j) else (2 : ℝ) ^ (12 * j)

/-- **The §7 majorant (round 6.3: FIXED absolute constants).**  *FI*'s §7 (Lemma 7.1, the fourfold
integration by parts whose product weight makes the §9 `h`-sum converge) needs `f` to be the
restriction to `ℤ` of a `C⁴` function of a real variable with **absolute** derivative constants
`|f^{(j)}| ≤ c_j M^{-j}`, `j ≤ 4` — the constants must not depend on `M`, on `Pa` or on `f`, since
they are multiplied together across several integrations by parts.  `IsMajorant6 Pa f` therefore
*asserts the existence* of such an interpolant `F` with `F|_ℤ = f` and the explicit `cMaj j`, together
with the support/size clauses (5.12)/(5.19).  Its last three conjuncts (the polar-box bounds) are the
round-3 `IsMajorant` data, so `IsMajorant6` implies the round-3 predicate (`toMajorant`) and every
estimate of §§5–9 that consumes only the sequence transfers.

(An *existential* `∃ C` version — as in the first round-6 draft — is strictly weaker and provably
unsuitable: round 3's `IsMajorant` implies it (`Red6.exists_isMajorant6_of_isMajorant`), but
`Work.FIArea2.no_strict_interpolant_of_oscillation` shows that some round-3 majorants have integer
values oscillating so fast that *no* `C⁴` interpolant has `|F^{(j)}| ≤ C M^{-j}` with `M`-uniform `C`;
so a coefficient hypothesis quantifying over them makes §7 unusable and round 6's `Area2_6` false.) -/
def IsMajorant6 (Pa : Work.FITop.Params) (f : ℤ → ℝ) : Prop :=
  (∃ F : ℝ → ℝ, ContDiff ℝ 4 F ∧ (∀ n : ℤ, F n = f n) ∧
    (∀ j : ℕ, j ≤ 4 → ∀ u : ℝ, |iteratedDeriv j F u| ≤ cMaj j * Pa.M ^ (-(j : ℝ)))) ∧
  (∀ u, 0 ≤ f u) ∧ (∀ u, f u ≤ 1) ∧
  (∀ w : GaussianInt, Pa.M < (Work.FIPlan.gnorm w : ℝ) →
      (Work.FIPlan.gnorm w : ℝ) ≤ 2 * Pa.M → 1 ≤ f (Work.FIPlan.gnorm w)) ∧
  (∀ u, f u ≠ 0 → Pa.M / 4 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 4 * Pa.M)

/-- **(7.7) for a round-6 majorant**: the discrete mean value of the sequence. -/
abbrev Fhat6 (Pa : Work.FITop.Params) (f : ℤ → ℝ) : ℝ := Fhat Pa f

/-! ## 3. The elementary API -/

/-- A non-zero coefficient of (4.13) lies in the polar box (5.14). -/
theorem IsBetaCoeff6.support {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt} (hz : β z ≠ 0) :
    InPolarBox Pa φ z := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ SameClass8 z z0
      ∧ IsAxisFree Pa z
  · exact hc.1
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- A non-zero coefficient of (4.13) is free of small primes (5.8). -/
theorem IsBetaCoeff6.noSmallPrimes {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt} (hz : β z ≠ 0) :
    NoSmallPrimes Pa z := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ SameClass8 z z0
      ∧ IsAxisFree Pa z
  · exact hc.2.1
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- A non-zero coefficient of (4.13)+(5.13)+(5.7) is **axis-free**: `√(ϑN) < |r|, |s|`. -/
theorem IsBetaCoeff6.isAxisFree {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt} (hz : β z ≠ 0) :
    IsAxisFree Pa z := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ SameClass8 z z0
      ∧ IsAxisFree Pa z
  · exact hc.2.2.2.2
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- **The (5.7) content of a round-6 coefficient**: two points of its support lie in the same
class modulo eight.  This is the hypothesis of Lemma 8.4 that the (8.16) evaluation of the
kernel needs. -/
theorem IsBetaCoeff6.sameClass {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : IsBetaCoeff6 Pa φ z0 β) {z w : GaussianInt}
    (hz : β z ≠ 0) (hw : β w ≠ 0) : SameClass8 z w := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  rw [hβ w] at hw
  by_cases hc : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ SameClass8 z z0
      ∧ IsAxisFree Pa z
  · by_cases hd : InPolarBox Pa φ w ∧ NoSmallPrimes Pa w ∧
        (((Work.FIPlan.gnorm w).divisors.card : ℝ) ≤ Pa.τ) ∧ SameClass8 w z0
        ∧ IsAxisFree Pa w
    · rw [SameClass8] at *
      rw [hc.2.2.2.1, hd.2.2.2.1]
    · rw [if_neg hd] at hw; exact absurd rfl hw
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- A non-zero coefficient point has squarefree norm: the Möbius factor of (5.13). -/
theorem IsBetaCoeff6.squarefree_gnorm {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : IsBetaCoeff6 Pa φ z0 β) {z : GaussianInt} (hz : β z ≠ 0) :
    Squarefree (Work.FIPlan.gnorm z) := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ SameClass8 z z0
      ∧ IsAxisFree Pa z
  · have hmu : (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ) ≠ 0 := by
      intro h0
      exact hz (by rw [if_pos hc, h0, mul_zero, zero_mul])
    exact ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp fun h0 => hmu (by rw [h0]; simp)
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- **Restricting a round-4 coefficient to a class mod eight *and* to the axis-free region**
produces a round-6 coefficient.**  This is the bridge that lets the composition of round 6 use the
pieces produced by the round-5 reduction `Red5.reduction_save` (whose coefficients are round-4
`IsBetaCoeff`): the class restriction supplies (5.7) and the axis restriction supplies
`IsAxisFree`, the two conjuncts by which `IsBetaCoeff6` strengthens the round-4 predicate. -/
theorem classRestrict_isBetaCoeff6 {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : IsBetaCoeff Pa φ β) :
    IsBetaCoeff6 Pa φ z0 (fun z => if SameClass8 z z0 ∧ IsAxisFree Pa z then β z else 0) := by
  obtain ⟨q, p, hc1, hc2, hq0, hq1, hqsupp, hqd, hp0, hp1, hpsupp, hpd, hβ⟩ := h
  refine ⟨q, p, hc1, hc2, hq0, hq1, hqsupp, hqd, hp0, hp1, hpsupp, hpd, ?_⟩
  intro z
  dsimp only
  by_cases h : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ SameClass8 z z0
      ∧ IsAxisFree Pa z
  · have hABC : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
        (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) := ⟨h.1, h.2.1, h.2.2.1⟩
    have hDE : SameClass8 z z0 ∧ IsAxisFree Pa z := ⟨h.2.2.2.1, h.2.2.2.2⟩
    simp only [hβ z, if_pos hDE, if_pos hABC, if_pos h]
  · by_cases hDE : SameClass8 z z0 ∧ IsAxisFree Pa z
    · by_cases hABC : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
          (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
      · exact absurd ⟨hABC.1, hABC.2.1, hABC.2.2, hDE.1, hDE.2⟩ h
      · simp only [hβ z, if_pos hDE, if_neg hABC, if_neg h]
    · simp only [hβ z, if_neg hDE, if_neg h]

/-- **A round-6 coefficient is a class-and-axis restriction of a round-4 one.**  The round-4
coefficient `β'` uses the same mollifiers and drops both the (5.7) clause and `IsAxisFree`. -/
theorem IsBetaCoeff6.exists_toBetaCoeff {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : IsBetaCoeff6 Pa φ z0 β) :
    ∃ β' : GaussianInt → ℂ, IsBetaCoeff Pa φ β' ∧
      (∀ z, β z = if SameClass8 z z0 ∧ IsAxisFree Pa z then β' z else 0) := by
  obtain ⟨q, p, hc1, hc2, hq0, hq1, hqsupp, hqd, hp0, hp1, hpsupp, hpd, hβ⟩ := h
  refine ⟨fun z => if InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
      then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
        * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
        * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
      else 0,
    ⟨q, p, hc1, hc2, hq0, hq1, hqsupp, hqd, hp0, hp1, hpsupp, hpd, fun z => rfl⟩, ?_⟩
  intro z
  dsimp only
  by_cases h : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ SameClass8 z z0
      ∧ IsAxisFree Pa z
  · have hABC : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
        (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) := ⟨h.1, h.2.1, h.2.2.1⟩
    have hDE : SameClass8 z z0 ∧ IsAxisFree Pa z := ⟨h.2.2.2.1, h.2.2.2.2⟩
    simp only [hβ z, if_pos h, if_pos hDE, if_pos hABC]
  · by_cases hDE : SameClass8 z z0 ∧ IsAxisFree Pa z
    · by_cases hABC : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
          (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
      · exact absurd ⟨hABC.1, hABC.2.1, hABC.2.2, hDE.1, hDE.2⟩ h
      · simp only [hβ z, if_neg h, if_pos hDE, if_neg hABC]
    · simp only [hβ z, if_neg h, if_neg hDE]

/-- **The class splitting of `Bfree`**: the free bilinear form of (5.10) is the sum of its
restrictions to the `64` classes modulo eight.  This is how the composition turns the round-5
reduction's pieces (`IsBetaCoeff`) into round-6 pieces (`IsBetaCoeff6`). -/
theorem Bfree_classSplit (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) :
    Bfree Pa β = ∑ c : ZMod 8 × ZMod 8,
      Bfree Pa (fun z => if cls8 z = c then β z else 0) := by
  have key : ∀ w : GaussianInt,
      (∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z)
        = ∑ c ∈ (Finset.univ : Finset (ZMod 8 × ZMod 8)), (∑ z ∈ Work.FITop.boxN Pa,
            (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z) := by
    intro w
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_eq_single (cls8 z)]
    · simp
    · intro b _ hb; simp [hb.symm]
    · intro h; exact absurd (Finset.mem_univ (cls8 z)) h
  simp only [Bfree, Work.FITop3.Bfree]
  refine Eq.trans (Finset.sum_congr rfl (fun w _ => key w)) ?_
  rw [Finset.sum_comm]

/-- Cauchy–Schwarz over the `64` classes, at one `w`: the squared modulus of the inner sum is at
most `64` times the sum of the squared moduli of the class restrictions. -/
theorem normSq_sum_le_classSplit (Pa : Work.FITop.Params) (w : GaussianInt)
    (β : GaussianInt → ℂ) :
    Complex.normSq (∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z)
      ≤ 64 * ∑ c : ZMod 8 × ZMod 8, Complex.normSq (∑ z ∈ Work.FITop.boxN Pa,
          (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z) := by
  have key : (∑ z ∈ Work.FITop.boxN Pa, β z * Work.FITop3.Zc w z)
      = ∑ c ∈ (Finset.univ : Finset (ZMod 8 × ZMod 8)), (∑ z ∈ Work.FITop.boxN Pa,
          (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.sum_eq_single (cls8 z)]
    · simp
    · intro b _ hb; simp [hb.symm]
    · intro h; exact absurd (Finset.mem_univ (cls8 z)) h
  rw [key, Complex.normSq_eq_norm_sq]
  have h1 : ‖∑ c ∈ (Finset.univ : Finset (ZMod 8 × ZMod 8)),
      (∑ z ∈ Work.FITop.boxN Pa, (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z)‖
      ≤ ∑ c ∈ (Finset.univ : Finset (ZMod 8 × ZMod 8)),
        ‖(∑ z ∈ Work.FITop.boxN Pa, (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z)‖ :=
    norm_sum_le _ _
  have h2 : (∑ c ∈ (Finset.univ : Finset (ZMod 8 × ZMod 8)),
        ‖(∑ z ∈ Work.FITop.boxN Pa, (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z)‖) ^ 2
      ≤ ((Finset.univ : Finset (ZMod 8 × ZMod 8)).card : ℝ) *
        ∑ c ∈ (Finset.univ : Finset (ZMod 8 × ZMod 8)),
          ‖(∑ z ∈ Work.FITop.boxN Pa, (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z)‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc ‖∑ c ∈ (Finset.univ : Finset (ZMod 8 × ZMod 8)),
        (∑ z ∈ Work.FITop.boxN Pa, (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z)‖ ^ 2
      ≤ (∑ c ∈ (Finset.univ : Finset (ZMod 8 × ZMod 8)),
        ‖(∑ z ∈ Work.FITop.boxN Pa, (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ ((Finset.univ : Finset (ZMod 8 × ZMod 8)).card : ℝ) *
        ∑ c ∈ (Finset.univ : Finset (ZMod 8 × ZMod 8)),
          ‖(∑ z ∈ Work.FITop.boxN Pa, (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z)‖ ^ 2 := h2
    _ = 64 * ∑ c : ZMod 8 × ZMod 8, Complex.normSq (∑ z ∈ Work.FITop.boxN Pa,
          (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z) := by
        norm_num [Fintype.card_prod, ZMod.card]
        simp [Complex.normSq_eq_norm_sq]

/-- **The class splitting of `Dform`**: Cauchy–Schwarz over the `64` classes. -/
theorem Dform_classSplit (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ)
    (hf : ∀ u, 0 ≤ f u) :
    Dform Pa f β ≤ 64 * ∑ c : ZMod 8 × ZMod 8,
      Dform Pa f (fun z => if cls8 z = c then β z else 0) := by
  have key : ∀ w : GaussianInt,
      f (Work.FIPlan.gnorm w) * Complex.normSq (∑ z ∈ Work.FITop.boxN Pa,
          β z * Work.FITop3.Zc w z)
        ≤ 64 * ∑ c : ZMod 8 × ZMod 8, f (Work.FIPlan.gnorm w) *
            Complex.normSq (∑ z ∈ Work.FITop.boxN Pa,
              (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z) := by
    intro w
    have h1 := normSq_sum_le_classSplit Pa w β
    calc f (Work.FIPlan.gnorm w) * Complex.normSq (∑ z ∈ Work.FITop.boxN Pa,
            β z * Work.FITop3.Zc w z)
        ≤ f (Work.FIPlan.gnorm w) * (64 * ∑ c : ZMod 8 × ZMod 8,
            Complex.normSq (∑ z ∈ Work.FITop.boxN Pa,
              (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z)) :=
          mul_le_mul_of_nonneg_left h1 (hf _)
      _ = 64 * (f (Work.FIPlan.gnorm w) * ∑ c : ZMod 8 × ZMod 8,
            Complex.normSq (∑ z ∈ Work.FITop.boxN Pa,
              (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z)) := by ring
      _ = 64 * ∑ c : ZMod 8 × ZMod 8, f (Work.FIPlan.gnorm w) *
            Complex.normSq (∑ z ∈ Work.FITop.boxN Pa,
              (if cls8 z = c then β z else 0) * Work.FITop3.Zc w z) := by
          rw [Finset.mul_sum]
  simp only [Dform, Work.FITop3.Dform]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => key w

end

end Work.FITop4
