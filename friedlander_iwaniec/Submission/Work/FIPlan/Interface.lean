/-
# `Submission.Work.FIPlan.Interface` — the vocabulary of main-paper Proposition 4.1

PLANNING MODULE.  This file contains **no theorem to be proved**: it defines the objects and
states the *areas* into which the proof of Proposition 4.1 (Friedlander–Iwaniec, *The polynomial
X² + Y⁴ captures its primes*, Ann. of Math. **148** (1998), 945–1040, §§4–26) is cut, so that the
project lead can write the final interfaces against a vocabulary that type-checks.

The corresponding objects of the existing workspace development are recorded in the doc strings
(`Submission.Z`, `Submission.an`, `Submission.ASP.Xsum`, `Submission.ASP.BprimeWindow`, …); the
dictionary is spelled out in `PLAN.md`, §1 and §4.

Equation numbers refer to the main paper unless prefixed `(ASP …)`, which refers to the companion
paper *Asymptotic sieve for primes*, Ann. of Math. **148** (1998), 1041–1065.
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIPlan

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. The Friedlander–Iwaniec sequence and the square-indicator `Z` -/

/-- `Z(b) = #{c : ℤ // c ^ 2 = b}`: the indicator of the squares counted with multiplicity
(`Z(0) = 1`, `Z(c²) = 2` for `c ≠ 0`).  Paper §3; identical to `Submission.Z`
(`Submission/S3.lean`). -/
def Zb (b : ℕ) : ℕ := if b = 0 then 1 else if Nat.sqrt b ^ 2 = b then 2 else 0

/-- `Z` extended to `ℤ` by `Z(b) = 0` for `b < 0`; this is the factor `Z(Re wz)` of (5.2). -/
def Zint (b : ℤ) : ℕ := if b < 0 then 0 else Zb b.natAbs

lemma Zb_zero : Zb 0 = 1 := by unfold Zb; simp

lemma Zint_eq_zero_of_neg {b : ℤ} (hb : b < 0) : Zint b = 0 := by unfold Zint; rw [if_pos hb]

/-- `a_n = #{(a, c) ∈ ℤ² : a² + c⁴ = n}` (paper (3.1)).  Identical to `Submission.an`. -/
def anFI (n : ℕ) : ℕ := ({x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 4 = n}).ncard

/-- `A(x) = ∑_{n ≤ x} a_n` (paper (4.2)).  Identical to `Submission.Aseq`. -/
def AseqFI (x : ℕ) : ℝ := ∑ n ∈ Finset.range (x + 1), (anFI n : ℝ)

/-- The companion paper's normalisation `A(x) = ∑_{1 ≤ n ≤ x} a_n` (`ASP.Acount FIa`). -/
def AcountFI (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (anFI n : ℝ)

/-- `ã_n = μ(n)² · a_n`, the squarefree-supported sequence of companion §9
(`ASP.atil FIa`), for which the companion's Theorem 2 (and hence the (B)-hypothesis that
Prop. 4.1 discharges) is stated. -/
def atilFI (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ) ^ 2 * (anFI n : ℝ)

/-- `γ(n; C) = ∑_{d ∣ n, d ≤ C} μ(d)`, the coefficient `ρ(n; C)` of the companion's (B2)
(`ASP.rhoTrunc`). -/
def gammaTrunc (C : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ C), (ArithmeticFunction.moebius d : ℝ)

/-- The bilinear form of the companion's hypothesis (B) (main paper (2.11), (4.3)):
`B_N(x) = ∑_m ∑_{N < n ≤ 2N, mn ≤ x, n free of primes ≤ P} β(n) μ(mn) a_{mn}`, with
`β(n) = μ(n) γ(n;C) p(n)`, `|p| ≤ 1`.  `noSmall` is the predicate "`n` is free of prime
factors `< P`". -/
def Bform (x N : ℕ) (β : ℕ → ℝ) (noSmall : ℕ → Prop) : ℝ :=
  ∑ m ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 (2 * N),
    (if N < n ∧ m * n ≤ x ∧ noSmall n then
      β n * (ArithmeticFunction.moebius (m * n) : ℝ) * (anFI (m * n) : ℝ) else 0)

/-- The `(B′)`-shape inner sum of `ASP.S7b.Xsum`: `∑_{t < b ≤ u, b ℓ ≤ N} μ(b) a_{bℓ}`. -/
def Xsum (a : ℕ → ℝ) (N ℓ : ℕ) (t u : ℝ) : ℝ :=
  ∑ b ∈ (Finset.Icc 1 N).filter
      (fun b => t < ((b : ℕ) : ℝ) ∧ ((b : ℕ) : ℝ) ≤ u ∧ b * ℓ ≤ N),
    (ArithmeticFunction.moebius b : ℝ) * a (b * ℓ)

/-- The `ρ`-weighted `(B′)`-shape inner sum of `ASP.S8b.Xrho`. -/
def Xrho (a : ℕ → ℝ) (N m : ℕ) (s t u : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m * n ≤ N),
    (if t < ((n : ℕ) : ℝ) ∧ ((n : ℕ) : ℝ) ≤ u
      then (ArithmeticFunction.moebius n : ℝ) * gammaTrunc s n
        * (ArithmeticFunction.moebius (m * n) : ℝ) * a (m * n) else 0)

/-! ## 1. Gaussian vocabulary -/

/-- The paper's **primary** condition (5.3)–(5.5): `z ≡ 1 (mod 2(1+i))`, i.e. `re` odd and
`im ≡ re - 1 (mod 4)`.  (`Commons.NumberTheory.GaussianInt.primary_associate_exists_unique`
uses the same condition inline.) -/
def IsPrimary (z : GaussianInt) : Prop := Odd z.re ∧ Even z.im ∧ z.im ≡ z.re - 1 [ZMOD 4]

/-- `z` is **primitive**: `(z, z̄) = 1`. -/
def IsPrimitive (z : GaussianInt) : Prop := IsCoprime z (star z)

/-- `|z|²` for a Gaussian integer. -/
def gnorm (z : GaussianInt) : ℕ := z.norm.natAbs

/-- `(z₁, z₂) = 1` in `ℤ[i]`. -/
def GaussCoprime (z1 z2 : GaussianInt) : Prop := IsCoprime z1 z2

/-- The determinant `Δ(z₁, z₂) = Im(z̄₁ z₂) = r₁s₂ - r₂s₁` (paper (6.1), (6.5)). -/
def Delta (z1 z2 : GaussianInt) : ℤ := (star z1 * z2).im

/-- `|Δ(z₁,z₂)|` (paper (6.1)). -/
def absDelta (z1 z2 : GaussianInt) : ℕ := (Delta z1 z2).natAbs

/-- `Re(w z)`, the linear form whose square parameterises `w` (paper (6.3)). -/
def cForm (w z : GaussianInt) : ℤ := (w * z).re

/-- The finite box `{|re| ≤ R, |im| ≤ R}` of Gaussian integers; used to make every sum finite. -/
def gBox (R : ℤ) : Finset GaussianInt :=
  ((Finset.Icc (-R) R).product (Finset.Icc (-R) R)).image
    (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt))

/-- The map `(a,b) ↦ a + bi` is injective (so `gBox` really is the box). -/
lemma gaussMk_injective : Function.Injective (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt)) :=
  fun a b h => Prod.ext (by simpa using congrArg Zsqrtd.re h)
    (by simpa using congrArg Zsqrtd.im h)

/-- The polar box (5.14): `N < |z|² ≤ (1+θ)N` and `φ < arg z ≤ φ + 2πθ`, together with the
primary condition (5.3). -/
def PolarBox (N : ℕ) (φ θ : ℝ) : Set GaussianInt :=
  {z | IsPrimary z ∧ (N : ℝ) < (gnorm z : ℝ) ∧ (gnorm z : ℝ) ≤ (1 + θ) * (N : ℝ) ∧
    φ < Complex.arg z.toComplex ∧ Complex.arg z.toComplex ≤ φ + 2 * Real.pi * θ}

/-! ## 2. The bilinear forms of §§5–10 -/

/-- The free bilinear form `B(M,N) = ∑_w ∑_z β_z Z(Re wz)` (paper (5.10)), over the boxes
`gBox RW` (outer variable `w`, `|w|² ∼ M`) and `gBox Rz` (inner variable `z`, `|z|² ∼ N`). -/
def Bfree (RW Rz : ℤ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ w ∈ gBox RW, ∑ z ∈ gBox Rz, β z * (Zint (cForm w z) : ℂ)

/-- The constrained form `B*(M,N)` of (4.20)/(5.6): the free form with `w`, `z` primitive and
`(w,z) = 1`; §5 removes the constraint via (5.10). -/
def Bstar (RW Rz : ℤ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ w ∈ (gBox RW).filter IsPrimitive,
    ∑ z ∈ (gBox Rz).filter IsPrimitive,
      (if GaussCoprime w z then β z * (Zint (cForm w z) : ℂ) else 0)

/-- `C(z₁,z₂) = ∑_w f(w) Z(Re w z₁) Z(Re w z₂)` (paper (5.27)). -/
def Cfun (RW : ℤ) (f : ℤ → ℝ) (z1 z2 : GaussianInt) : ℝ :=
  ∑ w ∈ gBox RW, f (gnorm w) * (Zint (cForm w z1) : ℝ) * (Zint (cForm w z2) : ℝ)

/-- `D(M,N) = ∑_w f(w) |∑_z β_z Z(Re wz)|²` (paper (5.18)). -/
def Dform (RW Rz : ℤ) (f : ℤ → ℝ) (β : GaussianInt → ℂ) : ℝ :=
  ∑ w ∈ gBox RW, f (gnorm w)
    * Complex.normSq (∑ z ∈ gBox Rz, β z * (Zint (cForm w z) : ℂ))

/-- `D*(M,N)`: as `D(M,N)` but with the pair `(z₁, z₂)` restricted by `(z₁, z₂) = 1`
(paper (5.21) after the reduction (5.22)). -/
def Dstar (RW Rz : ℤ) (f : ℤ → ℝ) (β : GaussianInt → ℂ) : ℝ :=
  ∑ w ∈ gBox RW, f (gnorm w)
    * (∑ z1 ∈ gBox Rz, ∑ z2 ∈ gBox Rz,
        (if GaussCoprime z1 z2 then
          (β z1 * (Zint (cForm w z1) : ℂ)) * star (β z2 * (Zint (cForm w z2) : ℂ))
         else 0)).re

/-- The scale `H = M^{-1/4} N^{3/4}` of Lemma 7.1. -/
def Hscale (M N : ℝ) : ℝ := M ^ (-(1 : ℝ) / 4) * N ^ ((3 : ℝ) / 4)

/-- `G₀(z₁,z₂) = 2 ∑_{4d ∣ Δ} (φ(d)/d)(Re(z̄₁z₂)/d)` (paper (8.16)), the Jacobi-symbol main
term.  (`(·/d)` is the Jacobi symbol, extended to even `d` by (8.15) — i.e. only the odd part
of `d` matters; nothing below uses the extension.) -/
def G0 (z1 z2 : GaussianInt) : ℝ :=
  2 * ∑ d ∈ (Finset.Icc 1 (absDelta z1 z2 / 4 + 1)).filter (fun d => 4 * d ∣ absDelta z1 z2),
        ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym ((star z1 * z2).re) d : ℝ)

/-- `C₀(z₁,z₂) = |z₁z₂|^{-1/2} F₀(z₁,z₂) G₀(z₁,z₂)` with `F₀` as in (7.10) (note the factor
`2 log(2|z₁z₂/Δ|)` there, fixed by comparison with (10.10)); (6.13), (7.10), (8.16).
`fhat` is `f̂(0) = ∫_0^∞ f(u)du` of (7.7), kept as a parameter. -/
def C0 (fhat : ℝ) (z1 z2 : GaussianInt) : ℝ :=
  (Real.sqrt ((gnorm (z1 * z2) : ℕ) : ℝ))⁻¹ * (2 * fhat)
    * Real.log (2 * ((gnorm (z1 * z2) : ℕ) : ℝ) / (absDelta z1 z2 : ℝ)) * G0 z1 z2

/-- `D₀(M,N) = ∑_{(z₁,z₂)=1} β_{z₁} β̄_{z₂} C₀(z₁,z₂)` (paper (9.11)). -/
def D0form (Rz : ℤ) (fhat : ℝ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ z1 ∈ gBox Rz, ∑ z2 ∈ gBox Rz,
    (if GaussCoprime z1 z2 then β z1 * star (β z2) * (C0 fhat z1 z2 : ℂ) else 0)

/-- `T(β) = ∑_{(z₁,z₂)=1} β_{z₁} β̄_{z₂} G₀(z₁,z₂) log 2|z₁z₂/Δ|` (paper (10.5)). -/
def Tbeta (Rz : ℤ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ z1 ∈ gBox Rz, ∑ z2 ∈ gBox Rz,
    (if GaussCoprime z1 z2 then
      β z1 * star (β z2) * ((G0 z1 z2
        * Real.log (2 * ((gnorm (z1 * z2) : ℕ) : ℝ) / (absDelta z1 z2 : ℝ))) : ℂ)
     else 0)

/-- The generically-cut partial sum of (10.13): `2 ∑_d (φ(d)/d) f(|Δ|/d) ∑_{(z₁,z₂)=1, 4d ∣ Δ}
β₁β̄₂ χ_d(z₂/z₁) log 2|z₁z₂/Δ|`.  Substituting the indicator of the ranges `d ≤ X`,
`X < d < |Δ|/4X` and its complement for the cut factor gives `U(β)`, `V(β)`, `W(β)` of
(10.15)–(10.17). -/
def Tcut (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ) (β : GaussianInt → ℂ) : ℂ :=
  2 * ∑ z1 ∈ gBox Rz, ∑ z2 ∈ gBox Rz,
    (if GaussCoprime z1 z2 then
      (β z1 * star (β z2)) *
        (∑ d ∈ (Finset.Icc 1 (absDelta z1 z2 / 4 + 1)).filter (fun d => 4 * d ∣ absDelta z1 z2),
          (((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
            * (jacobiSym ((star z1 * z2).re) d : ℝ)
            * Real.log (2 * ((gnorm (z1 * z2) : ℕ) : ℝ) / (absDelta z1 z2 : ℝ))) : ℂ)
     else 0)

/-- `U(β)` (10.15): the small moduli, `d ≤ X`. -/
def Ubeta (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Tcut Rz (fun _ _ d => if d ≤ X then (1 : ℝ) else 0) β

/-- `V(β)` (10.16): the middle moduli, `X < d < |Δ|/4X`. -/
def Vbeta (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Tcut Rz (fun z1 z2 d => if X < d ∧ 4 * d * X < absDelta z1 z2 then (1 : ℝ) else 0) β

/-- `W(β)` (10.17): the large moduli `d > |Δ|/4X`, in reflected (`d* = |Δ|/4d < X`) form. -/
def Wbeta (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Tcut Rz (fun z1 z2 d => if 4 * d * X > absDelta z1 z2 then (1 : ℝ) else 0) β

/-- `2 f̂(0) N^{-1/2}` as a complex factor, for (10.10). -/
def cMain (fhat N : ℝ) : ℂ := ((2 * fhat) * N ^ (-(1 : ℝ) / 2) : ℝ)

/-! ## 3. The Dirichlet symbol, the Jacobi–Kubota symbol, the quadratic eigenvalues
(§§19–23) -/

/-- The **Dirichlet symbol** `ξ_w(z) = (Re wz / |w|²)` of (19.10)–(19.11).  It is defined for
`w` primary primitive, where `|w|²` is computed as a Jacobi-symbol denominator. -/
def dirichletSymbol (w z : GaussianInt) : ℤ := jacobiSym ((w * z).re) (gnorm w)

/-- The **Jacobi–Kubota symbol** `[z] = i^{(r-1)/2} (s/|r|)` for `z = r + is ≡ 1 (mod 2)`
(paper (20.1)). -/
def jacobiKubotaValue (z : GaussianInt) : ℂ :=
  Complex.I ^ ((z.re - 1) / 2) * (jacobiSym z.im z.re.natAbs : ℂ)

/-- The **quadratic eigenvalue** `λ(n) = ∑^∧_{z z̄ = n} ψ(z)[z]` (23.1)–(23.2), `ψ` a Hecke
character (17.17), `jk` the Jacobi–Kubota symbol (20.1). -/
def quadEigen (Rz : ℤ) (ψ jk : GaussianInt → ℂ) (n : ℕ) : ℂ :=
  ∑ z ∈ (gBox Rz).filter (fun z => gnorm z = n ∧ IsPrimary z), ψ z * jk z

/-- `K(N) = ∑^∧_{z ∈ B, |z|² ≤ N} ψ(z)[wz]` (22.1): the special linear form in Jacobi–Kubota
symbols, restricted to the disc `|z|² ≤ N`. -/
def Klin (Rz : ℤ) (N : ℕ) (ψ jk : GaussianInt → ℂ) (w : GaussianInt) : ℂ :=
  ∑ z ∈ (gBox Rz).filter (fun z => IsPrimary z ∧ gnorm z ≤ N), ψ z * jk (w * z)

/-- `K*(N)` (22.2): the reduced linear form, `(z,w) = 1`. -/
def KlinStar (Rz : ℤ) (N : ℕ) (ψ jk : GaussianInt → ℂ) (w : GaussianInt) : ℂ :=
  ∑ z ∈ (gBox Rz).filter (fun z => IsPrimary z ∧ gnorm z ≤ N ∧ GaussCoprime z w),
    ψ z * jk (w * z)

/-- `L(M,N) = ∑_{m ≤ M} ∑_{n ≤ N} α(m)β(n)λ(cmn)` (23.4), the bilinear form in quadratic
eigenvalues. -/
def Lbilin (M Nc c : ℕ) (α β lam : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 Nc, α m * β n * lam (c * m * n)

/-- `L*(M,N)` (23.7): the reduced bilinear form, `(m,n) = 1`. -/
def LbilinStar (M Nc c : ℕ) (α β lam : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 Nc,
    (if Nat.Coprime m n then α m * β n * lam (c * m * n) else 0)

/-! ## 4. The Jacobi-twisted variance of §§11–14 -/

/-- The odd part `d'` of `d` (8.15). -/
def oddPart (d : ℕ) : ℕ := d / 2 ^ d.factorization 2

/-- The local variance `E(d)` of (11.7): for a coefficient matrix `α` supported in the box
`R < r ≤ 2R`, `S < s ≤ 2S`,
`E(d) = ∑_{a (d)} |∑_{r̄s ≡ a (d)} α_{rs} (r/d')|²`. -/
def Evar (R S : ℕ) (d : ℕ) (α : ℕ → ℕ → ℂ) : ℝ :=
  ∑ a ∈ Finset.range d,
    Complex.normSq (∑ r ∈ (Finset.Icc 1 (2 * R)).filter (fun r => Nat.Coprime r d),
      ∑ s ∈ (Finset.Icc 1 (2 * S)).filter
          (fun s' => ((s' : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) * ((a : ℕ) : ZMod d)),
        α r s * (jacobiSym (r : ℤ) (oddPart d) : ℂ))

/-- The global variance `V(D)` of (11.11). -/
def Vvar (R S D : ℕ) (α : ℕ → ℕ → ℂ) : ℝ := ∑ d ∈ Finset.Ioc D (2 * D), Evar R S d α

/-! ## 5. Hecke characters of `ℚ(i)` and their `L`-functions (§16) -/

/-- A **Hecke Grössencharacter of `ℚ(i)`** (paper (16.16)–(16.17)): a multiplicative character
`χ` on `(ℤ[i]/4dℤ[i])^*` together with an integral spin `k`, so that
`ψ(z) = χ(z)(z/|z|)^k` on primary generators of odd ideals; `L` is the associated `L`-function
(defined by the Euler product (16.17), continued meromorphically).  Only the analytic
properties (16.18)–(16.24) and Lemma 16.1 are needed. -/
structure HeckeCharData where
  d : ℕ
  k : ℤ
  hd : 0 < d
  chi : GaussianInt → ℂ
  chi_one : chi 1 = 1
  chi_mul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w
  L : ℂ → ℂ
  EulerProduct : Prop
  meromorphicContinuation : Prop
  functionalEquation : Prop
  real : Prop

/-- The Grössencharacter (16.16) attached to `(χ, k)`: `ψ(z) = χ(z)(z/|z|)^k`. -/
def psiOf (D : HeckeCharData) (z : GaussianInt) : ℂ :=
  D.chi z * (z.toComplex / (Real.sqrt ((gnorm z : ℕ) : ℝ) : ℂ)) ^ D.k

/-! ## 6. The set-up and the areas -/

/-- The numerical set-up of Proposition 4.1: the scale `x`, the exponents `η, A, A'`, the saving
factors `θ = (log x)^{-A'}` and `ϑ = (log x)^{-A}`, the sieve level `P`, the extents `M, N` of the
two variables, and the truncation parameter `C ≤ N^{1-η}`. -/
structure Setup where
  x : ℕ
  (η : ℝ)
  (A : ℝ)
  (A' : ℝ)
  (θ : ℝ)
  (ϑ : ℝ)
  (P : ℝ)
  (M : ℕ)
  (N : ℕ)
  (Cc : ℝ)
  hx : 3 ≤ x
  hη : 0 < η
  hA : 0 < A
  hθ : 0 < θ
  hθ1 : θ ≤ 1
  hϑ : 0 < ϑ
  hP : 2 ≤ P
  hNlo : (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ)
  hNhi : (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2)
  hMN : ϑ * (x : ℝ) < (M : ℝ) * (N : ℝ)
  hMNx : (M : ℝ) * (N : ℝ) ≤ (x : ℝ)
  hC1 : 1 ≤ Cc
  hC2 : Cc ≤ (N : ℝ) ^ (1 - η)
  hϑeq : ϑ = (Real.log (x : ℝ)) ^ (-A)
  hθeq : θ = (Real.log (x : ℝ)) ^ (-A')

/-! ### Area 1 — Gaussian reduction and Cauchy (§5) -/

/-- **Area 1** (§5): (5.10) the passage from `B*(M,N)` to the free form `B(M,N)`; (5.17) the
passage from `B(M,N)` to the squared form `D(M,N)` by Cauchy's inequality; (5.22) the reduction
of `D` to `D*`; and the trivial bound Lemma 5.1.  The majorant `f` is required to be `≥ 1` on the
box (the paper's smooth majorant of the indicator of the dyadic annulus); **without this hypothesis
the second conjunct is false** (`f = 0` gives `D = 0`). -/
def Area1 : Prop :=
  ∃ c : ℝ, 0 < c ∧
  ∀ (S : Setup) (RW Rz : ℤ) (f : ℤ → ℝ) (β : GaussianInt → ℂ),
    (∀ p, p ∈ gBox RW → 1 ≤ f (gnorm p)) →
    (∀ z, ‖β z‖ ≤ 1) →
    (‖Bstar RW Rz β - Bfree RW Rz β‖ ≤ c *
        ((S.M : ℝ) ^ ((1 : ℝ) / 4) * (S.N : ℝ) ^ ((5 : ℝ) / 4)
          + S.P⁻¹ * (S.M : ℝ) ^ ((3 : ℝ) / 4) * (S.N : ℝ) ^ ((3 : ℝ) / 4))
        * (Real.log (S.N : ℝ)) ^ 3) ∧
    (‖Bfree RW Rz β‖ ^ 2 ≤ c * (S.M : ℝ) * Dform RW Rz f β) ∧
    (Dform RW Rz f β ≤ Dstar RW Rz f β + c *
        ((S.M : ℝ) ^ ((3 : ℝ) / 4) * (S.N : ℝ) ^ ((3 : ℝ) / 4)
          + S.P⁻¹ * (S.M : ℝ) ^ ((1 : ℝ) / 2) * (S.N : ℝ) ^ ((3 : ℝ) / 2))
        * (Real.log ((S.M : ℝ) * (S.N : ℝ))) ^ 516)

/-! ### Area 2 — counting points inside the biquadratic ellipse (§§6–9) -/

/-- **Area 2** (§§6–9): the point count `C(z₁,z₂) = C₀(z₁,z₂) + error` (6.9) + (9.1), with the
exact main term (7.10) + (8.16), and the aggregate (9.10)
`D*(M,N) = D₀(M,N) + O(ϑ^{-1} τ² N² (log N)^b)`. -/
def Area2 : Prop :=
  ∃ Cb : ℝ, 0 < Cb ∧
  ∀ (S : Setup) (Rz : ℤ) (f : ℤ → ℝ) (fhat : ℝ) (β : GaussianInt → ℂ) (τ b : ℝ),
    (∀ z, ‖β z‖ ≤ τ) → 0 < fhat →
    (Real.sqrt (S.M : ℝ) / 4 ≤ fhat ∧ fhat ≤ 4 * Real.sqrt (S.M : ℝ)) →
    ‖Dstar Rz Rz f β - D0form Rz fhat β‖
      ≤ Cb * S.ϑ⁻¹ * τ ^ 2 * (S.N : ℝ) ^ 2 * (Real.log (S.N : ℝ)) ^ b

/-! ### Area 3 — the main term (§10) -/

/-- **Area 3** (§10): (10.10) `D₀ = 2f̂(0)N^{-1/2}T(β) + error` with the error admissible by
(10.11)–(10.12); (10.14)–(10.17) the decomposition `T(β) = U(β)+V(β)+W(β)`; and Proposition
10.2: if `U, V, W` satisfy (16.41), (15.8), (17.19) then
`T(β) ≪ N²(log N)^{-σ} + P^{-1}N²log N` for any `σ > 0`. -/
def Area3 : Prop :=
  ∃ Cb : ℝ, 0 < Cb ∧
  ∀ (S : Setup) (Rz : ℤ) (fhat X σ : ℝ) (β : GaussianInt → ℂ),
    (∀ z, ‖β z‖ ≤ 1) → 0 < fhat → 1 ≤ X →
    (‖D0form Rz fhat β - cMain fhat (S.N : ℝ) * Tbeta Rz β‖
        ≤ Cb * ((Real.log (S.x : ℝ)) ^ (-S.A) + S.θ) * S.θ ^ 4
          * (S.M : ℝ) ^ ((1 : ℝ) / 2) * (S.N : ℝ) ^ ((3 : ℝ) / 2)
          * (Real.log (S.N : ℝ)) ^ (2 ^ 20 : ℕ)) ∧
    (Tbeta Rz β = Ubeta Rz ⌊X⌋₊ β + Vbeta Rz ⌊X⌋₊ β + Wbeta Rz ⌊X⌋₊ β) ∧
    (‖Tbeta Rz β‖ ≤ Cb * ((S.N : ℝ) ^ 2 * (Real.log (S.N : ℝ)) ^ (-σ)
        + S.P⁻¹ * (S.N : ℝ) ^ 2 * Real.log (S.N : ℝ)))

/-! ### Area 4 — the Jacobi-twisted variance and `V(β)` (§§11–15) -/

/-- **Area 4** (§§11–15): Proposition 14.1,
`∑_{D<d≤2D} ∑_{a(d)} |∑_{r̄s≡a(d)} α_{rs}(r/d')|² ≤ N(D,R,S) ∑ τ(r)|α_{rs}|²` with
`N(D,R,S) ≪ D + D^{-1/2}RS + D^{1/3}(RS)^{2/3}(log 2RS)^4 + (R+S)^{1/12}(RS)^{11/12+ε}`,
and Proposition 15.1: `V(β) ≪ (P^{-1}+X^{-1/3})N²` for `1 ≤ X ≤ N^{1/9}`. -/
def Area4 : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∀ (D R S : ℕ) (ε : ℝ), 0 < ε → ∀ α : ℕ → ℕ → ℂ,
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →          -- the hypothesis (12.1)
      Vvar R S D α ≤ c * (1 + (D : ℝ) + (D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
          + (D : ℝ) ^ ((1 : ℝ) / 3) * ((R : ℝ) * (S : ℝ)) ^ ((2 : ℝ) / 3)
            * (Real.log (2 * (R : ℝ) * (S : ℝ))) ^ 4
          + ((R : ℝ) + (S : ℝ)) ^ ((1 : ℝ) / 12)
            * ((R : ℝ) * (S : ℝ)) ^ ((11 : ℝ) / 12 + ε))
        * ∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
            ((r : ℝ) + 1) * Complex.normSq (α r s)) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ (Rz : ℤ) (X P N : ℝ) (β : GaussianInt → ℂ),
      0 < P → 1 ≤ X → X ≤ N ^ ((1 : ℝ) / 9) → (∀ z, ‖β z‖ ≤ 1) →
      ‖Vbeta Rz ⌊X⌋₊ β‖ ≤ c * (P⁻¹ + X ^ (-(1 : ℝ) / 3)) * N ^ 2)

/-! ### Area 5 — Hecke `L`-functions of `ℚ(i)` (§16, analytic engine) -/

/-- **Area 5** (§16, analytic engine, external to the paper's own proofs): for a Hecke
Grössencharacter `ψ(z) = χ(z)(z/|z|)^k` of conductor `4d`, the Hecke `L`-function `L(s,ψ)`
(16.17) satisfies the convexity bounds (16.18)–(16.19), has no zeros off the real axis in the
region (16.20), and — for real `ψ` — satisfies the Landau–Siegel bound Lemma 16.1; consequently
`1/L` satisfies (16.23) in the region (16.24). -/
def Area5 : Prop :=
  ∀ D : HeckeCharData, D.EulerProduct → D.meromorphicContinuation → D.functionalEquation →
    (∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 →
      ‖D.L s‖ ≤ c * ((D.d : ℝ) * (‖s‖ + |(D.k : ℝ)| + 1)) ^ (1 - s.re)
        * (Real.log (4 * (D.d : ℝ) * (‖s‖ + |(D.k : ℝ)| + 1) + 2)) ^ 3) ∧
    (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ s : ℂ, D.L s = 0 → s.im ≠ 0 →
      s.re ≤ 1 - c₀ / Real.log (4 * (D.d : ℝ) + |(D.k : ℝ)| + ‖s.im‖ + 3)) ∧
    (D.real → ∃ cf : ℝ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
      ∀ s : ℂ, 1 - cf ε * (D.d : ℝ) ^ (-ε) < s.re → s.re < 1 → D.L s ≠ 0) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ s : ℂ,
      s.re ≥ 1 - c / ((D.d : ℝ) * Real.log (|(D.k : ℝ)| + ‖s.im‖ + 3) ^ 2) →
      ‖(D.L s)⁻¹‖ ≤ (D.d : ℝ) * (Real.log (|(D.k : ℝ)| + ‖s.im‖ + 3)) ^ 2)

/-! ### Area 6 — small moduli: `U(β)` (§16) -/

/-- **Area 6** (§16, Proposition 16.3): the Hecke-character expansion (16.15) of `U(β)`,
Lemma 16.2 and the contour shift (16.36)–(16.38) give
`U(β) ≪ (P^{-1} + X^{-1}) N² log N` for `1 ≤ X ≤ (log N)^ν` (`ν` arbitrary). -/
def Area6 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (Rz : ℤ) (X P N : ℝ) (β : GaussianInt → ℂ),
    0 < P → 1 ≤ X → (∀ z, ‖β z‖ ≤ 1) →
    ‖Ubeta Rz ⌊X⌋₊ β‖ ≤ c * (P⁻¹ + X⁻¹) * N ^ 2 * Real.log N

/-! ### Area 7 — large moduli: `W(β)` via the Jacobi–Kubota symbol (§§17, 19–26) -/

/-- **Area 7** (§§17, 19–26): the multiplier rule (20.3), the bilinear/linear form bounds
(21.13) (Prop. 21.4), (22.3)–(22.4) (Prop. 22.1), the eigenvalue forms (23.8), (23.11)–(23.12)
(Props. 23.1–23.2), the combinatorial identity (24.13) (Prop. 24.2) and Theorem 2ψ (26.2),
yielding Proposition 17.2 `S^k_χ(β') ≪ N^{1-δ}` uniformly for `d(|k|+1) ≤ N^δ` and hence
Proposition 17.3 `W(β) ≪ (P^{-1}+X^{-1})N²log N` for `1 ≤ X < N^ε`.

The objects entering these bounds must be the *actual* ones — the Hecke character `ψ = psiOf D`
(17.17), the Jacobi–Kubota symbol `jacobiKubotaValue` (20.1) and the quadratic eigenvalue
`quadEigen` (23.1); a bound of this shape for arbitrary bounded `ψ`, `jk`, `lam` is **false**
(take `ψ = jk = 1`, or `lam ≡ 1`). -/
def Area7 : Prop :=
  (∃ c : ℝ, 0 < c ∧ ∀ (M Nc cc : ℕ) (D : HeckeCharData) (Rz : ℤ) (α β : ℕ → ℂ),
    (∀ m ∈ Finset.Icc 1 M, ‖α m‖ ≤ 1) → (∀ n ∈ Finset.Icc 1 Nc, ‖β n‖ ≤ 1) →
    ‖Lbilin M Nc cc α β (quadEigen Rz (psiOf D) jacobiKubotaValue)‖
      ≤ c * ((cc.divisors.card : ℝ)) * ((M : ℝ) + (Nc : ℝ)) ^ ((1 : ℝ) / 12)
        * ((M : ℝ) * (Nc : ℝ)) ^ ((11 : ℝ) / 12)) ∧                -- (23.8), Prop. 23.1
  (∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (Rz : ℤ) (D : HeckeCharData) (w : GaussianInt),
    ‖Klin Rz N (psiOf D) jacobiKubotaValue w‖
      ≤ c * (D.d : ℝ) * (|(D.k : ℝ)| + 1) * ((gnorm w : ℝ) + 1) * (N : ℝ) ^ ((3 : ℝ) / 4)
        * Real.log (((gnorm w : ℝ) + 1) * (N : ℝ) + 2)) ∧   -- (22.3), Prop. 22.1
  (∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∀ (Rz : ℤ) (N X P : ℝ) (D : HeckeCharData),
    0 < P → 1 ≤ X → X < N ^ δ →
    ‖Wbeta Rz ⌊X⌋₊ (fun z => psiOf D z * jacobiKubotaValue z)‖
      ≤ c * (P⁻¹ + X⁻¹) * N ^ 2 * Real.log N)                     -- (17.19), Prop. 17.3

/-! ### The target: Proposition 4.1 and its window corollaries -/

/-- **Proposition 4.1, equation (4.5)**: for every `η > 0` and `A > 0` there are `B, C` such that
for every `x`, every `N` in the range (4.6), every truncation `C ∈ [1, N^{1-η}]` and every
coefficient family `β(n) = p(n) μ(n) γ(n;C)` with `|p| ≤ 1`, restricted to `n` free of prime
factors `< P` with `2 ≤ log P ≤ (log x)(log log x)^{-2}` (4.4), the bilinear form `B(x;N)` of
(4.3)/(2.11) satisfies `B(x;N) ≤ C A(x)(log x)^{4-A}`. -/
def Prop41 : Prop :=
  ∀ η A : ℝ, 0 < η → 0 < A → ∃ B C0 : ℝ, 0 < B ∧ 0 < C0 ∧
    ∀ x : ℕ, 3 ≤ x → ∀ N : ℕ,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ) →
      (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B) →
      ∀ Cc : ℝ, 1 ≤ Cc → Cc ≤ (N : ℝ) ^ (1 - η) →
      ∀ P : ℝ, 2 ≤ P → (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log P →
      Real.log P ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) →
      ∀ p : ℕ → ℝ, (∀ n, |p n| ≤ 1) →
      |Bform x N (fun n => (ArithmeticFunction.moebius n : ℝ) * gammaTrunc Cc n * p n)
          (fun n => ∀ q : ℕ, q.Prime → q < P → ¬ q ∣ n)|
        ≤ C0 * AseqFI x * (Real.log (x : ℝ)) ^ (4 - A)

/-- **The two window hypotheses of the proved chain**, for the squarefree-supported sequence
`ã = atil FIa` and the weight `w m = τ(m)²`: the exact form of `(B′)` consumed by
`ASP.S19.TheoremOne_full` (`ASP.BprimeWindow` for `S₂`, `ASP.RhoWindow` for `S₃`). -/
def WindowTarget : Prop :=
  (∃ C0 : ℝ, 0 < C0 ∧ ∀ x N : ℕ, 3 ≤ x → ∀ lo hi E : ℝ,
      E = C0 * AseqFI x * (Real.log (x : ℝ)) ^ (-3 : ℤ) →
      (∀ t : ℝ, lo ≤ t → t ≤ hi →
        (∑ m ∈ Finset.Icc 1 N, ((m.divisors.card : ℝ)) ^ 2
          * |Xsum atilFI N m t (2 * t)|) ≤ E)) ∧
  (∃ C0 : ℝ, 0 < C0 ∧ ∀ x N : ℕ, 3 ≤ x → ∀ C R lo hi E : ℝ,
      C ≤ R → E = C0 * AseqFI x * (Real.log (x : ℝ)) ^ (-3 : ℤ) →
      (∀ s t : ℝ, 1 ≤ s → s ≤ C → lo ≤ t → t ≤ hi →
        (∑ m ∈ Finset.Icc 1 N, ((m.divisors.card : ℝ)) ^ 2
          * |Xrho atilFI N m s t (2 * t)|) ≤ E))

end

end Work.FIPlan
