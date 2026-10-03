/-
# `Submission.Work.FITop3.Defs3` — the repaired vocabulary of area (B) of Friedlander–Iwaniec

ROUND 3 of the FI contract.  This is the round-2 file `Submission/Work/FITop/Defs` with the four
machine-checked defects repaired.  Every repair is listed here and mapped in `NOTES.md`.

## Defect 1 — `IsMajorant` was unsatisfiable.
Round 2 required `1 ≤ f (gnorm w)` for **every** `w` in the *square* box `boxM Pa = gBox (radM Pa)`
(which contains `0` and points of norm up to `8M`), while simultaneously requiring `f` to be
supported in the annulus `[M/4, 4M]`.  That is contradictory (`0 ∈ boxM`, `gnorm 0 = 0`,
`M/4 > 0`).  The paper (5.12)/(5.19) asks for `1 ≤ f` only on the **dyadic segment**
`M < |w|² ≤ 2M` (4.18) — that is where the Cauchy step (5.17) needs a majorant — and for `f` to
be supported in the annulus `√M/2 ≤ |w| ≤ 2√M`, i.e. `M/4 ≤ |w|² ≤ 4M` (§7: "`f` is a smooth
function supported on `[1/4 M, 4M]`").  Here `IsMajorant` does exactly that, and the sums over
`w` (`Bfree`, `Bstar`) are restricted to the dyadic annulus `annM Pa`
(`M < gnorm w ≤ 2M`), which is what the *paper* sums over in (4.18)/(5.6).  `Dform`/`Dstar` keep
summing over the support box `boxM Pa` (which contains the support `[M/4,4M]`, since
`gnorm w ≤ 4M ⟹ |re|,|im| ≤ 2√M ≤ radM Pa`), exactly as (5.18)/(5.21) do.

The derivative bounds `|Δf| ≤ 4/M`, `|Δ²f| ≤ 16/M²` are the explicit form of the paper's
`|f^{(j)}| ≪ M^{-j}` (`j ≤ 2`, §7).  The *literal* constants `M^{-j}` are **not** consistent with
the support `[M/4, 4M]` together with `f ≥ 1` on `(M, 2M]` — a monotone ramp from `0` at `M/4`
to `1` at `M` with `|f'| ≤ 1/M` and `|f''| ≤ 1/M²` is impossible (its minimum width is `2M`) —
so the implied constant of `≪` is made explicit here, generously.  `Smoothstep.sm` and
`Majorant.majorant` below exhibit a concrete `f` and prove `IsMajorant` non-empty.

## Defect 2 — the free `fhat` of `Area3`.
`fhat` is no longer a free parameter: it is tied to the majorant by `Fhat Pa f`, the discrete form
of (7.7) `f̂(0) = ∫_0^∞ f(u) u^{-1/2} du` (`Smoothstep`/`Majorant` prove `√M/4 ≤ Fhat ≤ 4√M`
from `IsMajorant`).  Areas 2 and 3 use `Fhat Pa f`, so their left- and right-hand sides scale
together; the round-2 failure (`Area3` was false because `D₀` is linear in `fhat` while the error
term is not) cannot occur.

## Defect 3 — `Area5` without `1 ≤ d`.
`Area5` now carries the hypothesis `1 ≤ d` (the paper's conductor `4d` and the group order
`Φ(d) ≍ d` of (16.12) both need `d ≥ 1`).  Round 2 admitted `d = 0`, where its right-hand side is
identically `0` and the statement asserts a vanishing character sum — refuted by any one-point
`β`.

## Defect 4 — `IsBetaCoeff` was far too weak.
Round 2 allowed an arbitrary `‖p z‖ ≤ 1` *per z*, which destroys the Möbius cancellation.  The
paper's coefficient (4.13)+(5.13) is

  `β_z = q(arg z) · p(|z|²) · μ(|z|²) · γ(|z|²; C)`,

with **one fixed** smooth radial mollifier `p` supported on the segment (4.12) `(N', (1+θ)N']`
with `|p^{(j)}| ≪ (θN)^{-j}` (4.14), **one fixed** smooth angular mollifier `q` supported on the
sector (5.12) `φ < α ≤ φ + 2πθ` with `|q^{(j)}| ≪ θ^{-j}` (used for (16.26)), and with the
support restricted to the polar box (5.14): primary `z`, `N' < |z|² ≤ (1+θ)N'`, the sector, the
free-of-small-primes condition `(z, Π) = 1` (5.8) and `τ(|z|²) ≤ τ` (5.9).  `IsBetaCoeff` below
encodes exactly this.  (Primitivity is *not* assumed: §5 observes that `|z|²` squarefree — which
the Möbius factor forces — implies `(r,s) = 1`, hence `z` primitive; nothing below needs it.)

`IsBoxCoeff` is the *weaker* support-and-size predicate under which the paper proves its
intermediate estimates (Lemma 10.1: "for any `β_z` supported in the polar box (5.14) and
satisfying `|β_z| ≤ τ(|z|²)`"; Proposition 15.1 uses only `(z1,z2) = 1`-removal via (5.8), the
box and `|β| ≤ τ(|z|²)` — see `NOTES.md` defect 4 for the check).  `Area4` (the `V`-bound) is
therefore stated for `IsBoxCoeff`, i.e. as generally as the paper proves it, and
`IsBetaCoeff.toBoxCoeff` shows the strong coefficient is a special case.

`Area5`'s character is isolated in `IsCharMod4d`: a character of modulus `4d` on `ℤ[i]`, extended
by `0` off the units, exactly the condition `Area5` consumes from (16.12)/(16.15).
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FITop.Defs

set_option autoImplicit false

namespace Work.FITop3

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. The targets of the chapter (re-exported from `Work.FITop`) -/

/-- Friedlander–Iwaniec Proposition 4.1 in the form the proved chain consumes — the target of the
whole area (B).  Unchanged from `Work.FITop.Defs`: it speaks only about the rational bilinear
form `BformAtil` and the counting function `Ã`, and none of the defects of area (B) touched it. -/
def Prop41Statement : Prop := Work.FITop.Prop41Statement

/-- The paper's literal Proposition 4.1 (with the `(n, mΠ) = 1` restriction of (4.3)). -/
def Prop41StatementPi : Prop := Work.FITop.Prop41StatementPi

/-! ## 1. The dyadic annulus of the outer variable (4.18) -/

/-- The dyadic segment `M < |w|² ≤ 2M` of (4.18), inside the box `boxM Pa`.  This is the exact
range of the outer summation of the paper's `B(M,N)` (4.20)/(5.6) and the set on which the
majorant has to dominate `1` (5.17). -/
def annM (Pa : Work.FITop.Params) : Finset GaussianInt :=
  (Work.FITop.boxM Pa).filter
    (fun w => Pa.M < (Work.FIPlan.gnorm w : ℝ) ∧ (Work.FIPlan.gnorm w : ℝ) ≤ 2 * Pa.M)

/-- The dyadic segment `N < |z|² ≤ 2N` of (4.18) for the inner variable. -/
def annN (Pa : Work.FITop.Params) : Finset GaussianInt :=
  (Work.FITop.boxN Pa).filter
    (fun z => Pa.N < (Work.FIPlan.gnorm z : ℝ) ∧ (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N)

lemma annM_subset_boxM (Pa : Work.FITop.Params) : annM Pa ⊆ Work.FITop.boxM Pa :=
  Finset.filter_subset _ _

lemma mem_annM {Pa : Work.FITop.Params} {w : GaussianInt} :
    w ∈ annM Pa ↔ w ∈ Work.FITop.boxM Pa ∧
      Pa.M < (Work.FIPlan.gnorm w : ℝ) ∧ (Work.FIPlan.gnorm w : ℝ) ≤ 2 * Pa.M :=
  Finset.mem_filter

/-- The theta coefficient `Z(Re wz)` of (5.2) as a complex number. -/
def Zc (w z : GaussianInt) : ℂ := ((Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℕ) : ℂ)

/-! ## 2. The bilinear forms of §§5–10, with the sums on the annuli of (4.18)

`Bfree` is the paper's `B(M,N)` of (5.10) (free: no coprimality), `Bstar` is `B*(M,N)` of (5.6)
(the same sum restricted to `(ww, zz) = 1`, encoded as Gaussian coprimality `GaussCoprime w z` —
equivalent for the *odd* `w,z` here).  `Dform` is (5.18), `Dstar` is (5.21) before/after the
reduction (5.22).  The `z`-sums run over the box `boxN Pa`; by `IsBetaCoeff`/`IsBoxCoeff` the
coefficient vanishes off the dyadic annulus `annN Pa`, so this is the paper's sum over `(4.12)`. -/

/-- (5.10)/(4.20): the free bilinear form `B(M,N) = Σ_{M<|w|²≤2M} Σ_z β_z Z(Re wz)`. -/
def Bfree (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℂ :=
  ∑ w ∈ annM Pa, ∑ z ∈ Work.FITop.boxN Pa, β z * Zc w z

/-- (5.6): `B*(M,N)`, the same form restricted to `(w,z) = 1`. -/
def Bstar (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℂ :=
  ∑ w ∈ annM Pa, ∑ z ∈ Work.FITop.boxN Pa,
    (if Work.FIPlan.GaussCoprime w z then β z * Zc w z else 0)

/-- (5.18): `D(M,N) = Σ_w f(w) |Σ_z β_z Z(Re wz)|²`, `w` ranging over the support box `boxM Pa`
(which contains the annulus (5.19) on which `f` lives). -/
def Dform (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) : ℝ :=
  ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
    * Complex.normSq (∑ z ∈ Work.FITop.boxN Pa, β z * Zc w z)

/-- (5.21)+(5.22): `D*(M,N)`, the squared-out form restricted to `(z₁, z₂) = 1`. -/
def Dstar (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) : ℝ :=
  ∑ w ∈ Work.FITop.boxM Pa, f (Work.FIPlan.gnorm w)
    * (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if Work.FIPlan.GaussCoprime z1 z2 then
          (β z1 * Zc w z1) * star (β z2 * Zc w z2)
         else 0)).re

/-! ## 2bis. The three cuts of (10.15)–(10.17) and the boundary

`Work.FIPlan.Ubeta/Vbeta/Wbeta` use the predicates `d ≤ X`, `X < d ∧ 4dX < |Δ|` and
`4dX > |Δ|` (with no `X < d`), which do **not** partition the `d`-range: a divisor `d ≤ X` with
`4dX > |Δ|` is counted in both `U` and `W` (e.g. `z₁ = 1+4mi`, `z₂ = 1+4(m+1)i` are primary,
primitive, coprime with `|Δ| = 4`, and then `d = 1` lies in both as soon as `X ≥ 2`).  The
corrected cuts below add the missing `X < d` to `V` and `W` and split off the boundary
`4dX = |Δ|`, so that they *do* partition `{d : 4d ∣ |Δ|}`; see `Tbeta_partition`. -/

/-- (10.15): `d ≤ X`. -/
def UcutC (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Work.FIPlan.Tcut Rz (fun _ _ d => if d ≤ X then (1 : ℝ) else 0) β

/-- (10.16): `X < d` and `4dX < |Δ|`. -/
def VcutC (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Work.FIPlan.Tcut Rz (fun z1 z2 d =>
    if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β

/-- (10.17), *unreflected*: `X < d` and `4dX > |Δ|`. -/
def WcutC (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Work.FIPlan.Tcut Rz (fun z1 z2 d =>
    if X < d ∧ 4 * d * X > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β

/-- The boundary piece `X < d`, `4dX = |Δ|`, which the corrected partition puts on its own and
which `Area7` owns (it is the self-dual case `d = d*` of §17's reflection). -/
def BcutC (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Work.FIPlan.Tcut Rz (fun z1 z2 d =>
    if X < d ∧ 4 * d * X = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β

/-- `Tcut` with the constant cut `1` — the sum that (10.5)/(10.13) define as `T(β)`; the first
conjunct of `Tbeta_partition` identifies it with `Work.FIPlan.Tbeta`. -/
def TcutOne (Rz : ℤ) (β : GaussianInt → ℂ) : ℂ :=
  Work.FIPlan.Tcut Rz (fun _ _ _ => (1 : ℝ)) β

/-! ## 2ter. The main-term objects of §§6–10, with the (7.10) normalisation

`Work.FIPlan.C0`/`D0form`/`Tbeta`/`Tcut` use `gnorm (z₁z₂) = |z₁z₂|²` where the paper uses the
**modulus** `|z₁z₂| = |z₁||z₂|`: (6.13) is `C₀ = |z₁z₂|^{-1/2}F₀G₀` and (7.10) is
`F₀ = f̂(0)·2log(2|z₁z₂/Δ|)`, while `Work.FIPlan.C0` has `|z₁z₂|^{-1}` and `log(2|z₁z₂|²/|Δ|)`.
Since `|z₁z₂| ≍ N` in the polar box, that is an error of a factor `√N` in the main term, and it
makes (10.4)/(10.10) — `D₀ = 2f̂(0)N^{-1/2}T(β) + error` — false as stated against
`Work.FIPlan.D0form` (the round-2 file's own referee recorded this as a secondary observation).
The `⋯Mod` objects below are the paper's: they use the modulus (equivalently, `gnorm^{-1/4}` for
`|z₁z₂|^{-1/2}`), so that `C0mod`, `TbetaMod` and the cuts are consistent with `cMain`
`= 2f̂(0)N^{-1/2}` of (10.4) and with the numerics (10.1) `D₀ ≪ θ⁴M^{1/2}N^{3/2}(log N)^8`. -/

/-- (7.2)/(7.10): `log(2|z₁z₂/Δ|) = log(2|z₁z₂|/|Δ(z₁,z₂)|)`, with `|z₁z₂| = |z₁||z₂|`. -/
def logFac (z1 z2 : GaussianInt) : ℝ :=
  Real.log (2 * Real.sqrt ((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)
    / (Work.FIPlan.absDelta z1 z2 : ℝ))

/-- (6.13)+(7.10): `C₀(z₁,z₂) = |z₁z₂|^{-1/2}·2f̂(0)·log(2|z₁z₂/Δ|)·G₀(z₁,z₂)`, with
`|z₁z₂|^{-1/2} = gnorm(z₁z₂)^{-1/4}`. -/
def C0mod (fhat : ℝ) (z1 z2 : GaussianInt) : ℝ :=
  (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) * (2 * fhat)
    * logFac z1 z2 * Work.FIPlan.G0 z1 z2

/-- (9.11): `D₀(M,N) = Σ_{(z₁,z₂)=1} β_{z₁}β̄_{z₂}C₀(z₁,z₂)` with the (6.13) kernel. -/
def D0formMod (Rz : ℤ) (fhat : ℝ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.GaussCoprime z1 z2 then
      β z1 * star (β z2) * (C0mod fhat z1 z2 : ℂ) else 0)

/-- (10.5): `T(β) = Σ_{(z₁,z₂)=1} β_{z₁}β̄_{z₂}G₀(z₁,z₂)log(2|z₁z₂/Δ|)`, with the (7.10) log. -/
def TbetaMod (Rz : ℤ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.GaussCoprime z1 z2 then
      β z1 * star (β z2) * ((Work.FIPlan.G0 z1 z2 * logFac z1 z2 : ℝ) : ℂ) else 0)

/-- (10.13) with the (7.10) log factor: the generically-cut partial sum of `T(β)`. -/
def TcutMod (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ) (β : GaussianInt → ℂ) : ℂ :=
  2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
    (if Work.FIPlan.GaussCoprime z1 z2 then
      (β z1 * star (β z2)) *
        ((∑ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
              (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
            (((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
              * (jacobiSym ((star z1 * z2).re) d : ℝ) * logFac z1 z2)) : ℂ)
     else 0)

/-- (10.15) for `TbetaMod`: the small moduli `d ≤ X`. -/
def UcutMod (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  TcutMod Rz (fun _ _ d => if d ≤ X then (1 : ℝ) else 0) β

/-- (10.16) for `TbetaMod`: the middle moduli `X < d ∧ 4dX < |Δ|`. -/
def VcutMod (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  TcutMod Rz (fun z1 z2 d =>
    if X < d ∧ 4 * d * X < Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β

/-- (10.17) for `TbetaMod`: the large moduli `X < d ∧ 4dX > |Δ|`. -/
def WcutMod (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  TcutMod Rz (fun z1 z2 d =>
    if X < d ∧ 4 * d * X > Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β

/-- the boundary `X < d ∧ 4dX = |Δ|` for `TbetaMod`. -/
def BcutMod (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  TcutMod Rz (fun z1 z2 d =>
    if X < d ∧ 4 * d * X = Work.FIPlan.absDelta z1 z2 then (1 : ℝ) else 0) β

/-- `TcutMod` with the constant cut `1` — the sum that (10.13) calls `T(β)`. -/
def TcutOneMod (Rz : ℤ) (β : GaussianInt → ℂ) : ℂ :=
  TcutMod Rz (fun _ _ _ => (1 : ℝ)) β

/-! ## 3. The polar box (5.14) and the coefficient predicates -/

/-- **The polar box (5.14)**: primary, norm in the segment `(N, (1+θ)N]` of (4.12), and in the
sector (5.12) `φ < arg z ≤ φ + 2πθ`.  (`φ` is a free real: the sector is defined modulo `2π` and
the paper's normalisation `-π < φ < π` is not imposed — imposing it would only add a case
distinction to the satisfiability witness, and no estimate of the paper uses it.) -/
def InPolarBox (Pa : Work.FITop.Params) (φ : ℝ) (z : GaussianInt) : Prop :=
  Work.FIPlan.IsPrimary z ∧
  Pa.N < (Work.FIPlan.gnorm z : ℝ) ∧ (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N ∧
  φ < Complex.arg z.toComplex ∧ Complex.arg z.toComplex ≤ φ + 2 * Real.pi * Pa.θ

/-- `z` is free of primes `≤ P` (5.8). -/
def NoSmallPrimes (Pa : Work.FITop.Params) (z : GaussianInt) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ Pa.Pz → ¬ q ∣ Work.FIPlan.gnorm z

/-- **The smooth majorant `f` of (5.12)/(5.17)/(5.19)**, repaired (defect 1).  Real, `0 ≤ f ≤ 1`,
`≥ 1` on the dyadic segment `M < |w|² ≤ 2M` of (4.18), supported in the annulus
`M/4 ≤ u ≤ 4M` of (5.19)/§7, with the second-difference bounds `|Δf| ≤ 8/M`,
`|Δ²f| ≤ 64/M²` (the explicit form of `|f^{(j)}| ≪ M^{-j}`, `j ≤ 2`). -/
def IsMajorant (Pa : Work.FITop.Params) (f : ℤ → ℝ) : Prop :=
  (∀ u, 0 ≤ f u) ∧
  (∀ u, f u ≤ 1) ∧
  (∀ w : GaussianInt, Pa.M < (Work.FIPlan.gnorm w : ℝ) →
      (Work.FIPlan.gnorm w : ℝ) ≤ 2 * Pa.M → 1 ≤ f (Work.FIPlan.gnorm w)) ∧
  (∀ u, f u ≠ 0 → Pa.M / 4 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 4 * Pa.M) ∧
  (∀ u : ℤ, |f (u + 1) - f u| ≤ 8 / Pa.M) ∧
  (∀ u : ℤ, |f (u + 2) - 2 * f (u + 1) + f u| ≤ 64 / Pa.M ^ 2)

/-- **(7.7)**, in the discrete form in which the areas consume it:
`f̂(0) = ∫_0^∞ f(u) u^{-1/2} du`, i.e. `Σ_u f(u) u^{-1/2}` over the support of `f`.  This ties
`fhat` to the majorant (defect 2); `Majorant.fhat_bounds` proves `√M/4 ≤ Fhat ≤ 4√M`. -/
def Fhat (Pa : Work.FITop.Params) (f : ℤ → ℝ) : ℝ :=
  ∑ u ∈ Finset.Icc (⌊Pa.M / 4⌋₊ : ℤ) (⌈4 * Pa.M⌉₊ : ℤ),
    f u / Real.sqrt (u : ℝ)

/-- **The support-and-size predicate of §§10–17** (defect 4, second half).  `β` is supported in
the polar box (5.14) with `(z, Π) = 1` (5.8) and satisfies `|β_z| ≤ τ(|z|²)`.  This is exactly
what Lemma 10.1 and Proposition 15.1 use — no Möbius structure and no smoothness — so `Area4`
is stated for it, and `IsBetaCoeff.toBoxCoeff` shows it is implied by the full coefficient. -/
def IsBoxCoeff (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ) : Prop :=
  (∀ z, ‖β z‖ ≤ ((Work.FIPlan.gnorm z).divisors.card : ℝ)) ∧
  (∀ z, β z ≠ 0 → InPolarBox Pa φ z ∧ NoSmallPrimes Pa z)

/-- **The coefficient family `β` of (4.13)+(5.13)**, repaired (defect 4).  There are *fixed*
mollifiers `q` (angular, supported on the sector (5.12), `|q^{(j)}| ≪ θ^{-j}`, `j ≤ 2`) and `p`
(radial, supported on the segment (4.12), `|p^{(j)}| ≪ (θN)^{-j}`, `j ≤ 2`) such that

  `β_z = q(arg z - φ)·p(|z|²)·μ(|z|²)·γ(|z|²; C)`

on the polar box (5.14) with `(z,Π) = 1` (5.8) and `τ(|z|²) ≤ τ` (5.9), and `β_z = 0` elsewhere.
(The `∃ q p` places the *same* `q` and `p` at every `z`, which is the property whose absence made
round 2's predicate admit `β = 1` on squarefree norms and falsify `Area5`.) -/
def IsBetaCoeff (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ) : Prop :=
  ∃ q p : ℝ → ℝ,
    (∀ α, 0 ≤ q α) ∧ (∀ α, q α ≤ 1) ∧
    (∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ) ∧
    (∀ α : ℝ, |q (α + 1) - q α| ≤ 32 / Pa.θ) ∧
    (∀ α : ℝ, |q (α + 2) - 2 * q (α + 1) + q α| ≤ 1024 / Pa.θ ^ 2) ∧
    (∀ u, 0 ≤ p u) ∧ (∀ u, p u ≤ 1) ∧
    (∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) ∧
    (∀ u : ℤ, |p ((u : ℝ) + 1) - p (u : ℝ)| ≤ 32 / (Pa.θ * Pa.N)) ∧
    (∀ u : ℤ, |p ((u : ℝ) + 2) - 2 * p ((u : ℝ) + 1) + p (u : ℝ)| ≤ 1024 / (Pa.θ * Pa.N) ^ 2) ∧
    (∀ z : GaussianInt, β z =
      (if InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
          (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
       then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
       else 0))

/-- **The characters of `Area5`**: a multiplicative function on `ℤ[i]` that is trivial modulo
`4d`, zero off the units modulo `4d`, bounded by `1`, normalised by `χ(1) = 1`.  This is the
character of `(ℤ[i]/4dℤ[i])^*` of (16.12) extended by zero, exactly as consumed by (16.15). -/
def IsCharMod4d (d : ℕ) (chi : GaussianInt → ℂ) : Prop :=
  chi 1 = 1 ∧
  (∀ z w : GaussianInt, chi (z * w) = chi z * chi w) ∧
  (∀ z : GaussianInt, ‖chi z‖ ≤ 1) ∧
  (∀ z w : GaussianInt, (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - w) → chi z = chi w) ∧
  (∀ z : GaussianInt, (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ z → chi z = 0)

/-! ## 4. The elementary API of the predicates -/

/-- `|γ(n;C)| ≤ τ(n)`: a sum of `τ(n)` values of the Möbius function. -/
lemma abs_gammaTrunc_le (C : ℝ) (n : ℕ) :
    |Work.FIPlan.gammaTrunc C n| ≤ (n.divisors.card : ℝ) := by
  unfold Work.FIPlan.gammaTrunc
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C),
      |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    intro d _
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  calc ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C),
        |(ArithmeticFunction.moebius d : ℝ)|
      ≤ ∑ _d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C), (1 : ℝ) := Finset.sum_le_sum h
    _ = ((n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C)).card : ℝ) := by simp
    _ ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-- The Möbius factor is bounded by `1` in `ℂ`. -/
lemma norm_moebius_le_one (n : ℕ) : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- **(defect 4, consistency)**: the full coefficient of (4.13)+(5.13) is a special case of the
support-and-size predicate under which §§10–17 estimate.  This is what lets the composition feed
an `IsBetaCoeff` into `Area4`. -/
theorem IsBetaCoeff.toBoxCoeff {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : IsBetaCoeff Pa φ β) : IsBoxCoeff Pa φ β := by
  obtain ⟨q, p, hq0, hq1, hqsupp, -, -, hp0, hp1, hpsupp, -, -, hβ⟩ := h
  constructor
  · intro z
    rw [hβ z]
    split_ifs with hz
    · have hqp : ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
          ≤ 1 := by
        have hA : 0 ≤ q (Complex.arg z.toComplex - φ) := hq0 _
        have hB : 0 ≤ p (Work.FIPlan.gnorm z) := hp0 _
        have hC : q (Complex.arg z.toComplex - φ) ≤ 1 := hq1 _
        have hD : p (Work.FIPlan.gnorm z) ≤ 1 := hp1 _
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by nlinarith, by simpa using mul_le_mul hC hD hB (by norm_num)⟩
      have hmu := norm_moebius_le_one (Work.FIPlan.gnorm z)
      have hg : ‖((Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
          ≤ ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_gammaTrunc_le _ _
      calc ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
            * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
            * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖
          = ‖(((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ))‖
            * ‖(Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖ := by
            rw [norm_mul]
        _ ≤ (1 * 1) * ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by
            gcongr
            rw [norm_mul]
            exact mul_le_mul hqp hmu (by positivity) (by norm_num)
        _ = ((Work.FIPlan.gnorm z).divisors.card : ℝ) := by ring
    · simp
  · intro z hz
    rw [hβ z] at hz
    have hcond : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
        (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) := by
      by_contra hc
      rw [if_neg hc] at hz
      exact hz rfl
    exact ⟨hcond.1, hcond.2.1⟩

end

end Work.FITop3
