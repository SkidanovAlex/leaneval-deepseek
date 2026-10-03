/-
# `Submission.Work.FIChain.Defs` — the vocabulary of the FI endgame chapter

This chapter closes the last `sorry` of `Submission/Work/FITop/Top.lean`
(`Work.FITop.primeSum_bound_of_prop41`), restated here under the name
`Work.FIChain.primeSum_bound_of_prop41'`, from the *hypothesis* `Prop41Statement` alone.

The design is dictated by the obstructions recorded in `FITop/NOTES.md` §14 (and in the lead's
request):

**(B) uniform constants.**  `ASP.S14.Tsum_bound_uniform` / `ASP.S15.Tsum2_bound_uniform` choose,
for each `M` in the window `[M₀,M₁]`, a constant `K(M)` and then return `∑_M K(M)`; since `K(M)`
comes from an *existential* statement (`ASP.S4.T_eval`), the caller obtains no uniform constant.
Here the `(4.5)`/`(5.1)` estimates are re-derived with the constants *hoisted out of the `M`
quantifier* (`ChainUniform.lean`), the underlying density constants being the uniform ones of
`Commons.NumberTheory.Sieve.sum_mu_g_div_gcd_le` / `sum_mu_g_div_gcd_log_eq` / `abs_Tnu_le`.

**(C) the B-dependent scale.**  The companion's §3 takes `s` a power of two with
`√x/(8√D) < s ≤ √x/(4√D)`; the chain's `c`-range is then `(sz, x/(s·Y)]`, whose log-width is
`log(x/(s²Yz))`.  For the frozen scale `Y = z = Δ⁻¹√D` this width is `≍ Δ²`, i.e. a *power of x*,
and the §6 factor `C₅ ≥ L₆ ≍ log Δ` makes `E₃ ≍ Ã(x)` — never `o(Ã)`.  The scale below makes the
`c`-range **empty**: with `Y = Δ·x^{1/4+2η}`, `z = 32e²·Y·(log x)^{2B}`,
`s ≈ √x(log x)^{-B}/(4eY)` one has `s²·Y·z ≈ 2x ≥ N`, i.e. `x/(sY) ≤ sz` and `cseg = ∅`, so
`L₆ = C₅ = 0` and the whole sieve term `E₃` vanishes.  This removes obstruction (D) as well (no
`λ⁻` weight is needed: `λ = δ₁` satisfies every remaining axiom).

**(D) the `ρ`-window.**  `ASP.S8b.Xrho` carries `μ(n)·ρ(n;s)·μ(ℓn)`; by `μ(n)μ(ℓn) = μ(ℓ)` on the
squarefree support its window is the *unsigned* tube sum, which is false for `ã` (`FITop/NOTES.md`
defect 11).  The companion's (B) — and hence `Prop41Statement` — gives the window for the
companion's `μ`-placement `ρ(n;s)·μ(ℓn)`, i.e. `Work.FITop.XrhoC` / `RhoWindowC`.  The §8 estimate
for `S₃` therefore has to be redone with the `μ(c)` of the companion's identity
`Λ(c) = λ⁻(c) − λ⁺(c)` *pulled out* of `Σ_{m|c}` (their (8.1)); that layer is `SignedS3.lean`
and its definitions are here.

Everything below is definitions only (no `sorry`, no `axiom`).
-/
import Mathlib
import Submission.Work.FITop.Defs
import Submission.ASP.S8
import Submission.ASP.S8b
import Submission.ASP.S7c
import Submission.ASP.S9g
import Submission.ASP.S27
import Submission.ASP_R

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset Filter
open Submission.ASP
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The corrected `B`-dependent parameters

The design (all conditions checked in `NOTES.md`): with `η = 1/32`, `Δ = ⌈x^{1/100}⌉`,
`D = Rcut x = ⌊x^{11/16}⌋`, `L = log x` and `s` the dyadic number just below
`x^{1/4-2η}/(2L^{B+2})`, put `y = z = √x/(s·L^{B+2})`.  Then

* `s·y = s·z = √x/L^{B+2}`: the two window tops sit a factor `L²` below the top `√x L^{-B}` of the
  range (4.6) of `Prop41Statement` (whose own constant is the paper's `B`);
* the window bottoms are `y/Δ = z/Δ ≈ x^{1/4}/Δ ⋯ x^{1/4+2η}/Δ > x^{1/4+η}`;
* the §6 `c`-range is `(s·z, x/(s·y)] = (√x/L^{B+2}, √x L^{B+2}]`, i.e. **log-narrow**, so that
  the companion's `L(x) ≍ log δ ≍ B·loglog x` and the §6 error is `≍ Ã·loglog x/log x`;
* `x/(s²yz) = L^{2B+4}` is the `δ₂`-cutoff of §6 (the `d`-range is log-narrow too).
-/
/-- The exponent `η` of the window range (4.6).  Fixed at `1/32`: `< 3/32` as `Prop41Statement`
requires, `2η > 1/100` so that `y/Δ > x^{1/4+η}`, and `4η < 7/40` so that `Δ·e·y·z ≤ D`. -/
def etac : ℝ := 1 / 32

/-- The sieve level `Δ = ⌈x^{1/100}⌉` (`log Δ ≍ log x`). -/
def Deltac (x : ℕ) : ℕ := Work.FITop.Delta1 x

/-- The modulus cutoff `D = Rcut x = ⌊x^{11/16}⌋` of `(R)`. -/
def Dc (x : ℕ) : ℕ := Work.FITop.Dcut x

/-- The dyadic exponent `J` with `s = 2^J ≈ x^{1/4-2η}/(2L^{B+2})`. -/
def Jc (x : ℕ) (B : ℝ) : ℕ :=
  ⌈Real.log ((x : ℝ) ^ ((1 : ℝ) / 4 - 2 * etac)
      / (2 * (Real.log (x : ℝ)) ^ (B + 2))) / Real.log 2⌉₊

/-- `s = 2^J`, the dyadic scale of §3–§6. -/
def sc (x : ℕ) (B : ℝ) : ℝ := (2 : ℝ) ^ (Jc x B)

/-- The outer scale `y = √x/(s·L^{B+2})` (the companion's `Y = Z`). -/
def Yc (x : ℕ) (B : ℝ) : ℝ :=
  Real.sqrt (x : ℝ) / (sc x B * (Real.log (x : ℝ)) ^ (B + 2))

/-- The companion's inner scale `Z = ⌊z⌋`, `z = y`. -/
def Zc (x : ℕ) (B : ℝ) : ℕ := ⌊Yc x B⌋₊

/-- `z = ⌊y⌋` as a real. -/
def zc (x : ℕ) (B : ℝ) : ℝ := (Zc x B : ℝ)

/-- The truncation level `C = ⌊s·z⌋` of the `ρ`-integral. -/
def Cc (x : ℕ) (B : ℝ) : ℕ := ⌊sc x B * zc x B⌋₊

/-- The `δ₂`-cutoff of §6: `x/(s²yz) ≤ ⌈2·L^{2B+4}⌉` (the factor `2` absorbs the floor
`z = ⌊y⌋`: `x = s²y²L^{2B+4} ≤ 2·s²y·⌊y⌋·L^{2B+4}` for `y ≥ 1`). -/
def d2c (x : ℕ) (B : ℝ) : ℕ := ⌈2 * (Real.log (x : ℝ)) ^ (2 * B + 4)⌉₊

/-- The `c`-bound of §6: `c ≤ √x·L^{B+2}` for `c` in the (6.1)-range. -/
def Mc (x : ℕ) (B : ℝ) : ℕ := ⌈Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ (B + 2)⌉₊

/-- `ε = 1/log Δ`. -/
def epsc (x : ℕ) : ℝ := 1 / Real.log (Deltac x : ℝ)

/-- The small-prime cutoff `Pz` of (4.4) fed to `Prop41Statement`. -/
def Pzc (x : ℕ) : ℕ := Work.FITop.Pcut x

/-! ## 2. The sequence and its density data -/

/-- `ã = atil FIa`. -/
abbrev atilc : ℕ → ℝ := Work.FITop.atilFIa

/-- The weight of the window hypotheses: `w(m) = τ(m)²`. -/
abbrev wc : ℕ → ℝ := Work.FITop.w0

/-- The counting function `Ã(x) = Σ_{n ≤ x} μ(n)²ã_n`. -/
abbrev AcountAtilC (x : ℕ) : ℝ := Work.FITop.AcountAtil x

/-- The frozen hypothesis: Friedlander–Iwaniec's Proposition 4.1 for `ã = atil FIa`. -/
abbrev Prop41Stmt : Prop := Work.FITop.Prop41Statement

/-- The `ρ`-window with the companion's `μ`-placement (`Work.FITop.RhoWindowC`). -/
abbrev RhoWindowCc (a : ℕ → ℝ) (N : ℕ) (w : ℕ → ℝ) (E C lo hi : ℝ) : Prop :=
  Work.FITop.RhoWindowC a N w E C lo hi

/-- The sieve weight `λ = δ₁` (`λ 1 = 1`, `λ ν = 0` for `ν > 1`). -/
def lamδ : ℕ → ℝ := fun n => if n = 1 then 1 else 0

/-! ## 3. The `μ(c)`-signed splitting of `S₃` (the companion's §8, (8.1)) -/

/-- The companion's §8 inner `c`-sum **with the `μ(c)`**: `Σ_{z<c≤sz, ℓc≤N} μ(c)·λ⁻(c)·a(ℓc)`. -/
def S3minusInnerC (a : ℕ → ℝ) (N ℓ : ℕ) (z sz C : ℝ) : ℝ :=
  ∑ c ∈ (Finset.Icc 1 N).filter
      (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
    (ArithmeticFunction.moebius c : ℝ) * lamMinus c C * a (ℓ * c)

/-- The companion's `λ⁺`-counterpart of `S3minusInnerC`. -/
def S3plusInnerC (a : ℕ → ℝ) (N ℓ : ℕ) (z sz C : ℝ) : ℝ :=
  ∑ c ∈ (Finset.Icc 1 N).filter
      (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
    (ArithmeticFunction.moebius c : ℝ) * lamPlus c C * a (ℓ * c)

/-- The companion's `S₃⁻` of (8.1) in reindexed form (`ℓ = b̃·e` merged). -/
def S3minusC (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 N,
    (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ * S3minusInnerC a N ℓ z sz C

/-- The companion's `S₃⁺` of (8.1) in reindexed form. -/
def S3plusC (a lam : ℕ → ℝ) (N : ℕ) (z sy sz C : ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 N,
    (∑ b ∈ ℓ.divisors.filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ)) * rhoOf lam ℓ * S3plusInnerC a N ℓ z sz C

/-- The `μ(c)`-signed `S₃`: `Σ_{b>sy}μ(b)Σ_{z<c≤sz}μ(c)Λ(c)Σ_e a(bce)ρ(be)`. -/
def S3signed (a lam : ℕ → ℝ) (N : ℕ) (z sy sz : ℝ) : ℝ :=
  ∑ b ∈ (Finset.Icc 1 N).filter (fun b => sy < ((b : ℕ) : ℝ)),
    (ArithmeticFunction.moebius b : ℝ) *
      ∑ c ∈ (Finset.Icc 1 N).filter
          (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz),
        (ArithmeticFunction.moebius c : ℝ) * ArithmeticFunction.vonMangoldt c *
          ∑ e ∈ (Finset.Icc 1 N).filter (fun e => b * (c * e) ≤ N),
            a (b * (c * e)) * rhoOf lam (b * e)

/-! ## 4. The sieve input of the companion's §3/§6 (obstruction (D)) -/

/-- The `h(ν)` of §6 of the companion paper: `h(ν) = ∏_{p ∣ ν} (1 + p^{-ε})/(1 + g(p)p^{-ε})`
(a local copy of `Submission.ASP.hSieve`, which lives in the `ASP.S6c` import-family). -/
def hSieveC (g : ℕ → ℝ) (ε : ℝ) (ν : ℕ) : ℝ :=
  ∏ p ∈ ν.primeFactors, (1 + (p : ℝ) ^ (-ε)) / (1 + (p : ℝ) ^ (-ε) * g p)

/-- **The `λ`-input of the companion's §3/§6** for a density `g`: an "upper-bound sieve of level
`Δ`" `λ` together with the §6 sieve constant.  The conjuncts are exactly the `λ`-axioms of
`ASP.S19.TheoremOne_full` (`hlam1`, `hΔsupp`, `hlam_sq`, `hlam_le`, `hrho`, `hpos`, `hpos'`) plus
the sieve inequality `hSieve`, with the constant `C_sieve` recorded so that it can be asked to be
*uniform in* `Δ` (which is what the endgame needs: `E₃ = Ã·C₅·(δ₂)^ε·C_sieve·e^{32C₀}·C₁/log Δ`
requires `C_sieve = O(1)` uniformly).  The remaining two axioms of `TheoremOne_full`
(`hB₁`, `hB₂`) are size bounds, supplied separately at the instantiation. -/
def SieveInput (g : ℕ → ℝ) (Δ : ℕ) (lam : ℕ → ℝ) (C_sieve : ℝ) : Prop :=
  lam 1 = 1 ∧ (∀ ν : ℕ, Δ < ν → lam ν = 0) ∧ (∀ ν : ℕ, ¬ Squarefree ν → lam ν = 0) ∧
  (∀ ν : ℕ, |lam ν| ≤ 1) ∧ (∀ n : ℕ, 0 ≤ rhoOf lam n) ∧
  (∀ d : ℕ, 0 ≤ ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (Nat.lcm ν d)) ∧
  (∀ d : ℕ, 0 ≤ ∑ ν ∈ Finset.Icc 1 Δ, lam ν * g (ν / Nat.gcd ν d)) ∧
  0 < C_sieve ∧
  (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree, lam ν * (g ν * hSieveC g (1 / Real.log (Δ : ℝ)) ν))
    ≤ C_sieve * ∏ p ∈ Nat.primesBelow Δ, (1 - g p * hSieveC g (1 / Real.log (Δ : ℝ)) p)

end

end Work.FIChain
