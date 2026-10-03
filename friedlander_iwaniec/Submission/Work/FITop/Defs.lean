/-
# `Submission.Work.FITop.Defs` — the vocabulary shared by `Areas.lean` and `Top.lean`

This module contains **definitions only** (no theorem, no `sorry`, no `axiom`), so that a lemma
about the interface can be delegated to a colleague who imports just this file.

Contents:
* the sequence `ã = atil FIa` and its counting function (`FIaR`, `atilFIa`, `AcountAtil`);
* the numerical set-up `Params` of `(4.4)`–`(4.19)`;
* the coefficient family `IsBetaCoeff` of `(4.13)` and the majorant `IsMajorant` of `(5.12)`;
* the boxes `radM/radN/boxM/boxN`;
* `BformPi` (the paper's `(4.3)`, with `(n,mΠ) = 1`) and `BformAtil` (the `Π`-free form the chain
  consumes);
* `Prop41Statement` (the frozen contract: `(4.5)` for `ã`) and `Prop41StatementPi` (the paper's
  literal Proposition 4.1);
* the explicit parameters of the interface task I-0: `Lam0`, `Delta0`, `Dcut`, `Y0`, `J0`, `s0`,
  `z0`, `Pcut`, `Ctrunc`, `d2`, `Mcut`, `Ysb`, `w0`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.ASP.Defs
import Submission.ASP.S9a
import Submission.ASP.S10

set_option autoImplicit false

namespace Work.FITop

open Finset
open Work.FIPlan
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. The sequence of the chain

The chain `ASP.S19.TheoremOne_full` → `ASP.S27.FI_primeSum_of_estimates` → `Submission.Final`
consumes the bilinear-form input for the **squarefree-supported** sequence
`ã = atil FIa` (`Submission.ASP.atil`, `ASP/S9a.lean`), not for `FIa` itself: `Xsum`/`Xrho`
carry `μ` on the *inner* variable, and only for `ã` is the coprimality `(n,m)=1` automatic.
Stating the input for `FIa` would be *false*. -/

/-- The Friedlander–Iwaniec sequence `a_n = #{(a,c) ∈ ℤ² : a² + c⁴ = n}` (`ASP.FIa`). -/
def FIaR (n : ℕ) : ℝ := Submission.ASP.FIa n

/-- `ã_n = μ(n)² a_n`: the squarefree-supported sequence of the companion's §9. -/
def atilFIa (n : ℕ) : ℝ := Submission.ASP.atil Submission.ASP.FIa n

/-- `Ã(x) = A_ã(x) = Σ_{n ≤ x} μ(n)² a_n`, the counting function of `ã` (companion (9.4)). -/
def AcountAtil (x : ℕ) : ℝ := Submission.ASP.Acount atilFIa (x : ℝ)

/-! ## 1. The numerical set-up (4.4)–(4.19) -/

/-- The numerical set-up of Proposition 4.1: the large parameter `x`, the exponents
`η, A, A'`, the range constant `B` of (4.6), the saving factors
`ϑ = (log x)^{-A}` (4.16) and `θ = (log x)^{-A'}` (4.15), the divisor cutoff `τ` of (4.9),
the small-prime cutoff `P` of (4.4) (`Π = ∏_{p ≤ P} p`), the truncation `C` of (2.12), and the
two scales `M, N` of the dyadic splitting (4.18)/(4.19).  All the relations used anywhere in
§§4–26 are fields, so that a statement quantified over `Params` can never be "about" the wrong
situation. -/
structure Params where
  /-- the large parameter -/
  x : ℕ
  /-- the exponent `η > 0` of the range (4.6) -/
  η : ℝ
  /-- the saving exponent `A > 0` of (4.5) -/
  A : ℝ
  /-- the smoothing exponent `A'` of (4.15) -/
  A' : ℝ
  /-- the range constant `B > 0` of (4.6) -/
  B : ℝ
  /-- the smoothing parameter `θ` of (4.15) -/
  θ : ℝ
  /-- the saving factor `ϑ` of (4.16) -/
  ϑ : ℝ
  /-- the divisor-function cutoff `τ` of (4.9) -/
  τ : ℝ
  /-- the small-prime cutoff `P` of (4.4) -/
  Pz : ℕ
  /-- the truncation `C` of the coefficient (2.12) -/
  C : ℝ
  /-- the outer scale `M` of (4.18) -/
  M : ℝ
  /-- the inner scale `N` of (4.18) -/
  N : ℝ
  hx : 3 ≤ x
  hη : 0 < η
  hA : 0 < A
  /-- (10.12): `A' ≥ 2A + 2^{20}` -/
  hA' : 2 * A + (2 : ℝ) ^ (20 : ℕ) ≤ A'
  hB : 0 < B
  hθ0 : 0 < θ
  hϑ0 : 0 < ϑ
  /-- (4.16): `ϑ = (log x)^{-A}` -/
  hϑ : ϑ = (Real.log (x : ℝ)) ^ (-A)
  /-- (4.15): `θ = (log x)^{-A'}` -/
  hθ : θ = (Real.log (x : ℝ)) ^ (-A')
  /-- (4.11): `τ ≥ (log x)^{A+124}` -/
  hτ1 : (Real.log (x : ℝ)) ^ (A + 124) ≤ τ
  /-- (5.23): `τ ≤ x^{η/3}` -/
  hτ2 : τ ≤ (x : ℝ) ^ (η / 3)
  /-- (4.4), lower end: `(loglog x)² ≤ log P` -/
  hPlo : (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ)
  /-- (4.4), upper end: `log P ≤ (log x)(loglog x)^{-2}` -/
  hPhi : Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ)
  hP2 : 2 ≤ Pz
  /-- (4.6), lower end -/
  hNlo : (x : ℝ) ^ ((1 : ℝ) / 4 + η) < N
  /-- (4.6), upper end -/
  hNhi : N < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B)
  hN1 : 1 ≤ N
  hM1 : 1 ≤ M
  /-- (4.19): `ϑx < MN` -/
  hMN : ϑ * (x : ℝ) < M * N
  /-- (4.19): `MN ≤ x` -/
  hMNx : M * N ≤ (x : ℝ)
  /-- (4.19) plus `B ≥ 2A`: `N ≤ M` -/
  hMge : N ≤ M
  /-- (2.12)/(2.13): `1 ≤ C` -/
  hC1 : 1 ≤ C
  /-- (2.12): `C ≤ N^{1-η}` -/
  hC2 : C ≤ N ^ (1 - η)

/-! ## 2. The coefficient family `β` of (4.13) and the smooth majorant `f` of (5.12) -/

/-- The radius of the outer box of §5: `|w|² ≲ M`, in the `ℤ`-indexed form in which the
analytic objects of `Work.FIPlan` take their boxes. -/
def radM (Pa : Params) : ℤ := (⌈Real.sqrt (4 * Pa.M)⌉₊ : ℤ)

/-- The radius of the inner box of §5: `|z|² ≲ N`. -/
def radN (Pa : Params) : ℤ := (⌈Real.sqrt (4 * Pa.N)⌉₊ : ℤ)

/-- The outer box of §5 as a `Finset`. -/
def boxM (Pa : Params) : Finset GaussianInt := Work.FIPlan.gBox (radM Pa)

/-- The inner box of §5 as a `Finset`. -/
def boxN (Pa : Params) : Finset GaussianInt := Work.FIPlan.gBox (radN Pa)

/-- **The coefficient family `β` of (4.13)**, in the `z`-indexed form of §5–§17:
`β(z) = p(z)·μ(N(z))·γ(N(z);C)` with `|p| ≤ 1`, supported on primary *primitive* `z` in the
polar box (5.14) at scale `N`, free of primes `≤ P` (4.21) and with `τ(N(z)) ≤ τ` (4.22).
Every hypothesis here is used: the primality is (5.8)/(5.10), the norm range is (5.14), the
`P`-condition is (5.8)/(4.21), the `τ`-condition is (4.9)–(4.11), `|p| ≤ 1` is (4.14) `j = 0`,
and `|β| ≤ 1` follows. -/
def IsBetaCoeff (Pa : Params) (β : GaussianInt → ℂ) : Prop :=
  (∀ z, ‖β z‖ ≤ 1) ∧
  (∀ z, β z ≠ 0 → IsPrimary z ∧ IsPrimitive z ∧
      Pa.N < (Work.FIPlan.gnorm z : ℝ) ∧
      (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N ∧
      (∀ q : ℕ, q.Prime → q ≤ Pa.Pz → ¬ q ∣ Work.FIPlan.gnorm z) ∧
      ((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧
  (∃ p : GaussianInt → ℂ, (∀ z, ‖p z‖ ≤ 1) ∧ ∀ z,
      β z = p z * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ))

/-- **The smooth majorant `f` of (5.12)/(5.19)**: real, non-negative, `≥ 1` on the outer box,
supported on the dyadic annulus `[M/4, 4M]`, bounded, with the first and second difference
bounds `|Δf| ≤ 2/M`, `|Δ²f| ≤ 4/M²` (the discrete form of `|f^{(j)}| ≪ M^{-j}`, `j ≤ 2`). -/
def IsMajorant (Pa : Params) (f : ℤ → ℝ) : Prop :=
  (∀ u, 0 ≤ f u) ∧
  (∀ w : GaussianInt, w ∈ boxM Pa → 1 ≤ f (Work.FIPlan.gnorm w)) ∧
  (∀ u, f u ≠ 0 → Pa.M / 4 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 4 * Pa.M) ∧
  (∀ u, f u ≤ 1) ∧
  (∀ u : ℤ, |f (u + 1) - f u| ≤ 2 / Pa.M) ∧
  (∀ u : ℤ, |f (u + 2) - 2 * f (u + 1) + f u| ≤ 4 / Pa.M ^ 2)

/-! ## 2. The target: Proposition 4.1 -/

/-- The bilinear form `B(x;N)` of (4.3)/(2.11) for the squarefree-supported sequence `ã`,
**with** the coprimality condition `(n,mΠ) = 1` of the paper (`Π = ∏_{q ≤ P} q`):

  `B(x;N) = Σ_m |Σ_{N<n≤2N, mn≤x, (n,mΠ)=1} μ(n)γ(n;C)ã(mn)|`.

**The absolute value is inside the `m`-sum** — this is essential: the companion's (B) is
`Σ_m |Σ_{N<n≤2N} ρ(n)μ(mn)a_{mn}| ≤ A(x)(log x)^{-1}` with the bars inside, and only that form
implies the `τ²`-weighted `(B′)` of §2 (via Hölder, whose first factor is `Σ_m|X_m|`).  A form with
the bars outside would be a *strictly weaker* (and useless) hypothesis. -/
def BformPi (x N : ℕ) (C : ℝ) (Pz : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
    (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
        ∧ (∀ q : ℕ, q.Prime → q ≤ Pz → ¬ q ∣ n)
      then (ArithmeticFunction.moebius n : ℝ) * gammaTrunc C n * atilFIa (m * n)
      else 0)|

/-- The same bilinear form **without** the coprimality-to-`Π` condition — the form consumed by
the chain's window hypotheses `BprimeWindow`/`RhoWindow`.  The condition `(n,m) = 1` is
automatic for `ã` (if `mn` is not squarefree then `ã(mn) = 0`) and is kept for faithfulness. -/
def BformAtil (x N : ℕ) (C : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 x, |∑ n ∈ Finset.Icc 1 (2 * N),
    (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m
      then (ArithmeticFunction.moebius n : ℝ) * gammaTrunc C n * atilFIa (m * n)
      else 0)|

/-- **Friedlander–Iwaniec, Proposition 4.1**, in the exact form the proved chain consumes.

The paper's own sufficient form is used (paragraph after (4.7)): **`A` is fixed at the paper's
value `2^26 + 4`**, and the range constant `B` is required to satisfy the paper's §18 value
`B ≈ 2^30`, recorded as `B ≤ 2^31` (a *bounded* existential: since the range (4.6) is monotone in
`B`, an unbounded `∃B` would carry no information about where the window of the chain lies — see
`NOTES.md`, defect 7).  For every `η ∈ (0, 3/32)` there are such `B, K` with

  `B(x;N) ≤ K·Ã(x)·(log x)^{4-(2^26+4)}`   (4.5)

for every `x ≥ x₀`, every `N` in the range (4.6), every `C ∈ [1, N^{1-η}]` and every `P` in the
(4.4) range.  The sequence is `ã = atil FIa` and the counting function `Ã(x)`; the absolute value
is inside the `m`-sum (see `BformAtil`).  The lower end of the range is kept at `x^{1/4+η}` (the
paper's `x^{3/8-η}` is *not* usable here: with the workspace's `Rcut = ⌊x^{11/16}⌋` the window
lower end is `≈ x^{11/32} ≫ x^{3/8-η}` only for the full range). -/
def Prop41Statement : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
    ∃ B K : ℝ, ∃ x₀ : ℕ, 0 < B ∧ B ≤ (2 : ℝ) ^ (31 : ℕ) ∧ 0 < K ∧
    ∀ x : ℕ, x₀ ≤ x → ∀ N : ℕ,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ) →
      (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B) →
      (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) →
      ∀ C : ℝ, 1 ≤ C → C ≤ (N : ℝ) ^ (1 - η) →
      ∀ Pz : ℕ, 2 ≤ Pz →
        (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ) →
        Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) →
        BformAtil x N C ≤ K * AcountAtil x * (Real.log (x : ℝ)) ^ (4 - ((2 : ℝ) ^ (26 : ℕ) + 4))

/-- **The paper's literal Proposition 4.1** — the same statement with the `(n,mΠ) = 1`
restriction of (4.3) (`Π = ∏_{q ≤ P} q`) retained (and with `A` left free).  This is what §25 of
the main paper (= §10 of the companion, Theorem 3) starts from; the step
`Prop41StatementPi → Prop41Statement` is the `Π`-removal, which loses only a power of `log x` in
the lower end of the range. -/
def Prop41StatementPi : Prop :=
  ∀ η A : ℝ, 0 < η → 0 < A →
    ∃ B K : ℝ, ∃ x₀ : ℕ, 0 < B ∧ 0 < K ∧ ∀ x : ℕ, x₀ ≤ x → ∀ N : ℕ,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ) →
      (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B) →
      (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) →
      ∀ C : ℝ, 1 ≤ C → C ≤ (N : ℝ) ^ (1 - η) →
      ∀ Pz : ℕ, 2 ≤ Pz →
        (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ) →
        Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) →
        BformPi x N C Pz ≤ K * AcountAtil x * (Real.log (x : ℝ)) ^ (4 - A)

/-! ## 3. The parameters of the interface task I-0

The companion's §3 (3.3) fixes `Y = Z = Δ^{-1}√D` with `D` the modulus cutoff of `(R)` and `Δ`
the sieve level, and `s` the power of two in `(√x/(8δ√D), √x/(4δ√D)]`.  The main paper's §18
forces `Δ` to be a power of `log x` and `B = B(η,A) ≈ 2^{30}` (risk R-15 of `PLAN.md`); we fix
`Δ = ⌈(log x)^{2^{31}}⌉`, which dominates every condition of §18.  The choices below are the ones
verified in `range_check` (leaf 3). -/

/-- `Λ(x) = (log x)^{2^{31}}`, the sieve level (as a real). -/
def Lam0 (x : ℕ) : ℝ := (Real.log (x : ℝ)) ^ (2 ^ 31 : ℕ)

/-- The sieve level `Δ = ⌈(log x)^{2^{31}}⌉`. -/
def Delta0 (x : ℕ) : ℕ := ⌈Lam0 x⌉₊

/-- The modulus cutoff of `(R)` for the sequence `ã`, `D = Rcut x = ⌊x^{11/16}⌋`
(`Submission.Rcut`, `Submission/ASP_R.lean`). -/
def Dcut (x : ℕ) : ℕ := Submission.Rcut x

/-- The companion's `Y = Z = Δ^{-1}√D`. -/
def Y0 (x : ℕ) : ℝ := (Lam0 x)⁻¹ * Real.sqrt (Dcut x)

/-- The dyadic exponent `J` of `s = 2^J ∈ (√x/(8√D), √x/(4√D)]`. -/
def J0 (x : ℕ) : ℕ :=
  ⌈Real.log (Real.sqrt (x : ℝ) / (8 * Real.sqrt (Dcut x))) / Real.log 2⌉₊

/-- The companion's `s = 2^J`. -/
def s0 (x : ℕ) : ℝ := (2 : ℝ) ^ (J0 x)

/-- The inner scale `z = Y` of §8. -/
def z0 (x : ℕ) : ℝ := Y0 x

/-- The small-prime cutoff `P` of (4.4): `log P = (loglog x)²`. -/
def Pcut (x : ℕ) : ℕ := ⌈Real.exp ((Real.log (Real.log (x : ℝ))) ^ 2)⌉₊

/-- The truncation `C = xD^{-1}` of (2.13)/(B3). -/
def Ctrunc (x : ℕ) : ℝ := (x : ℝ) / (Dcut x : ℝ)

/-- The majorant of `hδ2` of `ASP.S19`: `δ₂ = ⌈64Λ²⌉` dominates `x/(bc)` for `b > sY`, `c > sz`. -/
def d2 (x : ℕ) : ℕ := ⌈64 * Lam0 x ^ 2⌉₊

/-- The cutoff `M` of `hMran`: `c ≤ x/(sY) ≤ ⌈8Λ√x⌉` for `c ∈ cseg`. -/
def Mcut (x : ℕ) : ℕ := ⌈8 * Lam0 x * Real.sqrt (x : ℝ)⌉₊

/-- The bound `Ys = max(δ₂, Δ)` of `hY1`/`hY2`. -/
def Ysb (x : ℕ) : ℕ := max (d2 x) (Delta0 x)

/-- The weight `w(m) = τ(m)² ≥ τ(m)²` of the window hypotheses (satisfies `hw2` of `S19`). -/
def w0 (m : ℕ) : ℝ := ((m.divisors.card : ℝ)) ^ 2


/-! ## 4. The parameters actually needed by the chain (sieve level a power of `x`)
The companion's §3 takes the sieve level `Δ = x^ε` and `δ = (log x)^κ`, and its error term
`O(log δ/log Δ)` is `O(loglog x/log x)` for those choices.  The same requirement comes from
`ASP.S19`'s error `A·C₅·C_sieve·e^{32C₀}C₁/log Δ` and from its `B₁(log M₀)^{-5}` term: both are
`≪ A(log N)^{-1}` **only if `log Δ ≍ log x`**, i.e. only if `Δ` is a *power of `x`* and not a power
of `log x`.  The set below is the one to use; the `0`-set above (`Lam0`, `Delta0`, …) certifies the
*window range* (that is what `range_check` states) but is too small for the error terms. -/
/-- `Λ₁(x) = x^{1/100}`: the sieve level as a real.  The exponent `1/100` is small enough for the
window range (`Δ²√D^{-1} > x^{-(3/32-η)}`) and large enough that `log Δ ≍ log x`. -/
def Lam1 (x : ℕ) : ℝ := (x : ℝ) ^ ((1 : ℝ) / 100)
/-- The sieve level `Δ = ⌈x^{1/100}⌉`. -/
def Delta1 (x : ℕ) : ℕ := ⌈Lam1 x⌉₊
/-- The companion's `δ = δ(x) = (log x)²` (a power of `log x`, so that `log δ/log Δ → 0`). -/
def del1 (x : ℕ) : ℝ := (Real.log (x : ℝ)) ^ 2
/-- The companion's `Y = Z = Δ^{-1}√D`. -/
def Y1 (x : ℕ) : ℝ := (Lam1 x)⁻¹ * Real.sqrt (Dcut x)
/-- The dyadic exponent `J` with `s = 2^J ∈ (√x/(8δ√D), √x/(4δ√D)]`. -/
def J1 (x : ℕ) : ℕ :=
  ⌈Real.log (Real.sqrt (x : ℝ) / (8 * del1 x * Real.sqrt (Dcut x))) / Real.log 2⌉₊
/-- The companion's `s = 2^J`. -/
def s1 (x : ℕ) : ℝ := (2 : ℝ) ^ (J1 x)
/-- The inner scale `z = Y`. -/
def z1 (x : ℕ) : ℝ := Y1 x
/-- `δ₂ = ⌈64 Δ²δ²⌉` dominates `x/(bc)` for `b > sY`, `c > sz`. -/
def d2b (x : ℕ) : ℕ := ⌈64 * (Lam1 x) ^ 2 * (del1 x) ^ 2⌉₊
/-- `M = ⌈8Δδ√x⌉` dominates `x/(sY)` for the `c`-range `cseg`. -/
def Mcutb (x : ℕ) : ℕ := ⌈8 * Lam1 x * del1 x * Real.sqrt (x : ℝ)⌉₊

/-! ### 4bis. The *dyadic scale* `s` of the chain — a correction of `J1`/`s1` (see `NOTES.md` §14)

The chain's `c`-sum runs over `c ∈ (sz, N/(sY)]`, so its **log-width** is
`log(N/(s²Yz))` and `C₅ ≥ L6 ≍ log(N/(s²Yz))`.  Since `ASP.S19`'s error term is
`A·C₅·(δ2)^ε·C_sieve·e^{32C₀}·C₁/log Δ` with `C_sieve = O(1)` for a genuine `λ⁻` weight, the
target `≤ C·A·loglog N/log N` **requires** `C₅/log Δ → 0`, i.e. the `c`-range must be
*log-narrow*: `N/(s²Yz) = (log x)^{O(1)}`.

With `Y = z = Δ^{-1}√D` (the companion's (3.3) scale) this pins the dyadic scale to
`s ≈ √x/(δ·Y) = Δ√x/(δ√D)`, i.e. `s·Y ≈ √x/δ` — **one factor `Δ` larger than `J1`/`s1`** below,
which were built as `s ≈ √x/(8δ√D)` (that is the *paper's* relation for `y = √D`, not for
`y = Δ^{-1}√D`).  With `s1` the width is `N/(s1²Y1²) ≈ Δ²(log x)^4`, a *power of `x`*, hence
`C₅/log Δ ≳ 1` and the chain gives only `|S − HÃ| = O(Ã)` — **not** `o(Ã)`.  Hence the whole
chain must be instantiated with `s1b` (this is the "range check" of the assignment: with the
frozen `s1` the chain needs more from `(B)` than the relative saving it can deliver).

**But `s1b` alone is not the answer**: it needs the window top
`s1b·e·Y1 = e√x/(8(log x)²)` to lie below `x^{1/2}(log x)^{-B}`, i.e. `B < 2`, while the `B` that
`Prop41Statement` *provides* is only known to satisfy `B ≤ 2^31`.  With that `B` the window top
forces `sY ≤ √x(log x)^{-B}/e`, and combining it with `hΔMP : Δ·e·Y·z ≤ D` and the window bottom
`Y > x^{1/4+η}Δ` gives the *sharp* relation for the `c`-width
```
R := N/(s²Yz)  =  e³·Δ·Y²·(log x)^{2B}/D·(1+o(1))      (N = x, Yz = D/(Δ e) at the top),
```
so `R` is a free positive constant times `(log x)^{2B}` and the *corrected* family must be
`B`-dependent:
```
Y = 8√D·Δ^{-3/2}·e^{-3/2}·(log x)^{2-B},    z = D/(Δ e Y)/R',   s = √x(log x)^{-B}/(eY),
```
with `R' = 64(log x)^4 ∈ (log x)^{O(1)}` the prescribed width.  Then `hΔMP`, `hlog_rep`,
`hΔ2`, `hΔ4`, `hM1N`, `hZN` and the two window margins all hold (checked term by term in
`NOTES.md` §14), and `L6 ≪ 4 log log x + log 64`, so `C₅/log Δ → 0` — which is what the chain
needs.  `J1b`/`s1b` below are the *B-free* approximation of that family (correct when `B` is
small, wrong when it is large); they are kept as the simplest instance of the correction and as
the reference for the range-check leaf `RangeCheckChainB`. -/
/-- The dyadic exponent with `s = 2^J ≈ Δ√x/(8δ√D)`, i.e. `s·Y1 ≈ √x/(8δ)` — the value for
which the `c`-range `(s z, N/(sY))` is log-narrow (`≍ (8 log x)²`) instead of `≍ Δ²`. -/
def J1b (x : ℕ) : ℕ :=
  ⌈Real.log (Lam1 x * Real.sqrt (x : ℝ) / (8 * del1 x * Real.sqrt (Dcut x)))
      / Real.log 2⌉₊

/-- The companion's dyadic `s` for the `Δ^{-1}√D` scale: `s = 2^{J1b}`. -/
def s1b (x : ℕ) : ℝ := (2 : ℝ) ^ (J1b x)
/-! ## 5. The `ρ`-weighted window sum, with the companion's `μ`-placement

`ASP.S8b.Xrho` carries **two** Möbius factors, `μ(n)·ρ(n;s)·μ(mn)·a(mn)`.  On the squarefree
support of `ã` the two cancel, `μ(n)μ(mn) = μ(m)`, so that window is the *nonnegative* double count
`Σ_m τ(m)² Σ_n ã(mn)` — no cancellation in the inner variable, and a bound `≪ Ã(x)(log x)^{-3}` on
it is **false** in the range of the chain (that count is `≍ x (log x)^{O(1)}`, while the bound is
`≍ x^{3/4}(log x)^{-3}`).  The companion's (B)/(B₂) carries **one** Möbius factor, on the product
`mn`.  The corrected objects below are the ones the contract uses; `ASP/S8b` needs the same
correction (see `NOTES.md`, defect 11). -/

/-- The §8 bilinear sum with the companion's `μ`-placement:
`Σ_{t<n≤u, mn≤N} ρ(n;s)·μ(mn)·a(mn)`. -/
def XrhoC (a : ℕ → ℝ) (N m : ℕ) (s t u : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m * n ≤ N),
    (if t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u
      then gammaTrunc s n * (ArithmeticFunction.moebius (m * n) : ℝ) * a (m * n) else 0)

/-- The `(B′)`-type `ρ`-window with the companion's `μ`-placement. -/
def RhoWindowC (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (E C lo hi : ℝ) : Prop :=
  ∀ s t : ℝ, 1 ≤ s → s ≤ C → lo ≤ t → t ≤ hi →
    (∑ m ∈ Finset.Icc 1 N, w m * |XrhoC a N m s t (2 * t)|) ≤ E


end

end Work.FITop
