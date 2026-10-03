/-
# `Submission.Work.FITop4.Areas6` — ROUND 6 of the FI area (B) contract: the seven areas

The vocabulary is `Submission.Work.FITop4.Defs6` (the corrected kernel `G0 = G0fix`, the paper's
`f̂(0)` normalisation, one ratio symbol `(z₂/z₁|d)` for `D₀`, `T(β)` and the three cuts, the
coefficient `IsBetaCoeff6` with the (5.7) restriction to one class mod `8`, and the `C⁴` majorant
`IsMajorant6`).  This file holds

* §1 the seven areas `Area1Sieve6` … `Area7₆`, each the round-4 statement *at the corrected
  objects*, with the two strengthened hypotheses;
* §2 the per-piece bundle `AreaBounds6` and the composition
  `prop41_of_areas6 : Area1Sieve6 → … → Area7₆ → Prop41StatementPiBig`, **proved**;
* §3 the satisfiability of every hypothesis list at a non-degenerate instance, **proved**.

## What each area is, and what changed from round 4

| area | paper | round-6 change |
|---|---|---|
| `Area1Sieve6` | §5 (5.10)+(5.22) | hypotheses only (`IsMajorant6`, `IsBetaCoeff6`); the objects `Bstar/Bfree/Dform/Dstar` are unchanged |
| `Area2₆` | §6–9 (9.10) | `D0formMod → D0` (count kernel + `Fhat` normalisation) |
| `Area3₆` | §10 (10.10) | `D0formMod → D0`, `TbetaMod → Tbeta`, `cMain → cMain6` (factor `2` removed) |
| `Area4₆` | §§11–15, Prop 15.1 | `VcutMod → Vcut` (ratio symbol) **and, per the lead's addendum and area 4's finding, `IsBoxCoeff` is replaced by `IsBetaCoeff6`**: §15's closing estimate needs the Möbius structure, it is false for arbitrary `IsBoxCoeff` |
| `Area5₆` | §16, Lemma 16.2 | hypotheses only |
| `Area6₆` | §16 (16.41) | `UcutMod → Ucut` |
| `Area7₆` | §§17,19–26 (17.19) | `WcutMod + BcutMod → Wcut + Bcut` |

The `τ`-truncation parameter `τ = Pa.τ`, the (10.10) error `(τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^{20}}`,
the exponent `bFun η`, the budget `Tbudget` and the numeric side conditions `NumHyp`/`PieceFacts`
are *unchanged* from round 4 — they are properties of the sieve, not of the kernel.
## ROUND 6.2 — the side conditions each area carries

The lead's round-6.2 rule: *each area statement carries exactly the side conditions the
composition can supply, and no more generality*.  Two things were wrong in the round-6 shapes:

* **the constant must be allowed to depend on `η`** (and on the area's other parameters): the
  areas are consumed by the composition at one fixed `η ∈ (0,3/32)`, so there is no reason to
  demand a constant uniform in `η`, and the round-4/6 shapes (a single `∃ c` outside the `η`-binders)
  made `Area2_6`, `Area3_6`, `Area6_6`, `Area7_6` strictly stronger than the paper;
* **a threshold on `x`**, i.e. `∃ x₀, x₀ ≤ Pa.x` — the composition supplies one (`x₀` is its own
  existential) and *needs* it: `FIArea6`'s counterexample (`NOTES` §10.6 of that directory) uses
  admissible data with `Pz ≈ e·N^η` and `C ≈ N^{1-η}/2`, for which every proper divisor of a
  support norm is `< C` and `γ(n;C) = −μ(n)`, so `β = −q·p` is one-signed and the bilinear forms sit
  at their *trivial* size.  That regime requires `log Pz ≳ η log N ≥ η(1/4)log x` while (4.4) gives
  `log Pz ≤ log x/(loglog x)²`, hence `loglog x ≲ 2/√η` — an *upper* bound on `x`; a threshold
  `x ≥ x₀` with `x₀ > exp(exp(2/√η))` removes it.  The same mechanism is why the rule is applied to
  **every** area, not only `Area6_6`.

Concretely the shapes are now

| area | shape |
|---|---|
| `Area1Sieve6` | `∃ c x₀, 0 < c ∧ ∀ Pa, x₀ ≤ Pa.x → ∀ F φ z₀ β, …` |
| `Area2_6` / `Area3_6` | `∀ η ∈ (0,3/32), ∃ C x₀, 0 < C ∧ ∀ Pa, x₀ ≤ Pa.x → Pa.η = η → ∀ F φ z₀ β, …` |
| `Area4_6` | `∀ η ∈ (0,3/32), ∃ c x₀, 0 < c ∧ ∀ Pa, x₀ ≤ Pa.x → Pa.η = η → ∀ X φ z₀ β, …` |
| `Area5_6` | `∀ ε ∈ (0,1/4], ∃ c_ε x₀, 0 < c_ε ∧ ∀ Pa, x₀ ≤ Pa.x → ∀ φ ν z₀ d k χ, …` |
| `Area6_6` | `∀ η ∈ (0,3/32), ∃ c_ν x₀, 0 < c_ν ∧ ∀ Pa, x₀ ≤ Pa.x → Pa.η = η → ∀ X φ z₀ β, … → X ≤ (log N)^{nuU} → X³ ≤ exp(√log N) → …` |
| `Area7_6` | `∀ η ∈ (0,3/32), ∃ δ c x₀, 0 < δ ∧ 0 < c ∧ ∀ Pa, x₀ ≤ Pa.x → Pa.η = η → ∀ X φ z₀ β, …` |

`Area6_6` additionally fixes the exponent `ν` at the single value the composition uses,
`nuU = 3·sigmaChoice Asave + 4` (the composition's `σ` is fixed for exactly this reason), and
carries *FI* §16's Fourier-cutoff proviso `X³ ≤ exp(√log N)` explicitly; the composition supplies
it from its own threshold through `Red6.eventually_Xcut_cube_le`.  The (4.4) range
`(loglog x)² ≤ log Pz ≤ log x (loglog x)^{-2}` is already a field of `Params` (`hPlo`/`hPhi`), so
no area repeats it.

`AreaBounds6` (below) is unchanged: it bundles the areas' *conclusions* at one datum, and the
extra `∀ Pa`-threshold arguments of the areas are supplied when the bundle is built (see
`Red6/prop41_of_areas6`).

-/

import Mathlib
import Submission.Work.FITop4.AreaShims
import Submission.Work.FITop4.Defs6
import Submission.Work.FITop4.Red6.IsMajorant6_toMajorant

set_option autoImplicit false

namespace Work.FITop4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

abbrev IsCharMod4d6 := Work.FITop3.IsCharMod4d

/-- **The single value of `ν` that the composition uses** in `Area6_6`: it takes `X = Xcut Pa σ`
with `σ = sigmaChoice Asave`, i.e. `X = ⌈(log N)^{3σ+3}⌉₊`, and `AreaBounds6` feeds the result at
the exponent `σ`; the composition needs no other value of `ν` (`NOTES.md` R6.2).  `FI`'s (16.41)
provides the proviso `X³ ≤ exp(√(log N))`, carried explicitly by `Area6_6` and supplied by the
composition's threshold. -/
def nuU : ℝ := 3 * sigmaChoice Asave + 4


/-! ## 1. The seven areas -/

/-- **`Area1Sieve6`** (*FI* §5), round 4's `Area1Sieve` at the strengthened hypotheses: there is
`c > 0` such that for every admissible datum, every `C⁴` majorant `F` and every coefficient `β`
of (4.13)+(5.13) restricted by (5.7),

* **(5.10)** `‖B*(M,N) − B(M,N)‖ ≤ c(M^{1/4}N^{5/4} + P^{-1}M^{3/4}N^{3/4})(log N)³`;
* **(5.22)** `D(M,N) ≤ D*(M,N) + cτ²(M^{3/4}N^{3/4} + P^{-1}M^{1/2}N^{3/2})(log MN)^{516}`. -/
def Area1Sieve6 : Prop :=
  ∃ c x0 : ℝ, 0 < c ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
  ∀ (f : ℤ → ℝ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ),
    IsMajorant6 Pa f → IsBetaCoeff6 Pa φ z0 β →
    (‖Bstar Pa β - Bfree Pa β‖
        ≤ c * (Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((5 : ℝ) / 4)
            + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4))
          * (Real.log Pa.N) ^ (3 : ℕ)) ∧
    (Dform Pa f β
        ≤ Dstar Pa f β
          + c * Pa.τ ^ (2 : ℕ) * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
              + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
            * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ))

/-- **`Area2₆`** (*FI* §§6–9, (9.10)) at the corrected main term: for some `Cb > 0`, every
admissible datum, majorant `F` and coefficient `β`,

  `‖D*(M,N) − D₀(M,N)‖ ≤ Cb·ϑ^{-1}·τ²·N²·(log N)^{b(η)}`,

with `D₀` the (9.11) sum with the (6.13)/(7.10) main term `C0` built on the *count* kernel
`G0 = Cnt/|Δ|` and the `|w|²`-normalisation `f̂(0) = Fhat Pa f` — the paper's (7.7) mean
value.  This is (9.10) verbatim; the round-4 statement had the frozen kernel
`2Σ_{4d|Δ}(φ(d)/d)(Re(z̄₁z₂)|d)` in place of `G₀` and the normalisation off by `2`. -/
def Area2_6 : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ Cb x0 : ℝ, 0 < Cb ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (f : ℤ → ℝ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ),
    IsMajorant6 Pa f → IsBetaCoeff6 Pa φ z0 β →
    ‖Dstar Pa f β - D0 (radN Pa) (Fhat Pa f) β‖
      ≤ Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2 * (Real.log Pa.N) ^ (bFun Pa.η)

/-- **`Area3₆`** (*FI* §10, (10.10)) at the corrected main term:

  `‖D₀(M,N) − f̂(0)N^{-1/2}T(β)‖ ≤ C3(τ^{-1} + θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^{20}}`,

with `T(β)` the (10.5) sum on the count kernel and `f̂(0) = Fhat Pa f`.  In the paper's
`|w|`-convention (10.10) reads `D₀ = 2f̂(0)N^{-1/2}T(β) + O(…)`; since the frozen `Fhat` is
`2f̂(0)` (§7's measure is `d|w| = du/(2√u)`), the exact translation is
`D₀ = Fhat·N^{-1/2}·T(β) + O(…)` — that is `cMain6`, and *not* the frozen
`cMain = 2Fhat·N^{-1/2}`, which is too large by a factor `2` (and makes the identity false: the
main term would exceed the error by `(log N)^{2A+8}`). -/
def Area3_6 : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ C3 x0 : ℝ, 0 < C3 ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (f : ℤ → ℝ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ),
    IsMajorant6 Pa f → IsBetaCoeff6 Pa φ z0 β →
    ‖D0 (radN Pa) (Fhat Pa f) β - cMain6 (Fhat Pa f) Pa.N * Tbeta (radN Pa) β‖
      ≤ C3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
          * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))

/-- **`Area4₆`** (*FI* §§11–15, Proposition 15.1) at the corrected cut: for some `c > 0`, every
admissible datum, every coefficient `β` of (4.13)+(5.13)+(5.7) and every `1 ≤ X ≤ N^{1/9}`,

  `‖V(β)‖ ≤ c(P^{-1} + X^{-1/3})N²`.

The *object* changed (`Vcut` carries the ratio symbol `(z₂/z₁|d)` of (10.13), not the frozen
`(Re(z̄₁z₂)|d)`), and the *hypothesis* changed from `IsBoxCoeff` to `IsBetaCoeff6`: §15's closing
estimate uses the Möbius structure of (5.13), and area 4's own report found the Proposition-15.1
statement false for arbitrary `IsBoxCoeff` (`FIArea4`, the lead's round-6 addendum). -/
def Area4_6 : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ c x0 : ℝ, 0 < c ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) →
      (X : ℝ) ≤ (Real.log Pa.N) ^ nuU →
    ‖Vcut (radN Pa) X β‖
      ≤ c * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3)) * Pa.N ^ 2

/-- **`Area5₆`** (*FI* §16, Lemma 16.2), round 4's `Area5` at the strengthened hypothesis: for every
`ε ∈ (0, 1/4]` there is an ineffective `c_ε > 0` such that for every admissible datum, every Hecke
twist `χ·(z/|z|)^k` of conductor `4d` with `1 ≤ d ≤ (log N)^ν` (`ν < 1/(2ε)`) and
`|k| ≤ exp(√(log N))`, and every `β` of (4.13)+(5.13)+(5.7),

  `S_χ^k(β) ≪ [exp(-ηc_ε(4d)^{-ε}√(log N)) + exp(-η log N/log P)]·(4d)·N·(log N)^6`. -/
def Area5_6 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ cε x0 : ℝ, 0 < cε ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
    ∀ (φ ν : ℝ) (z0 : GaussianInt) (d : ℕ) (k : ℤ)
      (chi : GaussianInt → ℂ),
      0 < ν → ν < 1 / (2 * ε) → 1 ≤ d → (d : ℝ) ≤ (Real.log Pa.N) ^ ν →
      |(k : ℝ)| ≤ Real.exp (Real.sqrt (Real.log Pa.N)) →
      IsCharMod4d6 d chi →
      ∀ β : GaussianInt → ℂ, IsBetaCoeff6 Pa φ z0 β →
        ‖∑ z ∈ boxN Pa,
            β z * chi z
              * (z.toComplex / (Real.sqrt (gnorm z : ℝ) : ℂ)) ^ k‖
          ≤ cε * (Real.exp (-(Pa.η * cε * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
            * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)

/-- **`Area6₆`** (*FI* §16, Proposition 16.3 = (16.41)) at the corrected cut: for every `ν > 0` there
is `c_ν > 0` (ineffective) such that for every admissible datum, every coefficient `β` of
(4.13)+(5.13)+(5.7) and every `1 ≤ X ≤ (log N)^ν`,

  `‖U(β)‖ ≤ c_ν(P^{-1} + X^{-1})N²log N`. -/
def Area6_6 : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ cν x0 : ℝ, 0 < cν ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → (X : ℝ) ≤ (Real.log Pa.N) ^ nuU →
      (X : ℝ) ^ 3 ≤ Real.exp (Real.sqrt (Real.log Pa.N)) →
    ‖Ucut (radN Pa) X β‖
      ≤ cν * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N

/-- **`Area7₆`** (*FI* §§17, 19–26; (17.19) = Proposition 17.3) at the corrected cut: there are
`δ > 0` and `c > 0` such that for every admissible datum, every coefficient `β` of
(4.13)+(5.13)+(5.7) and every `1 ≤ X < N^δ`,

  `‖W(β) + B(β)‖ ≤ c(P^{-1} + X^{-1})N²log N`. -/
def Area7_6 : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ δ c x0 : ℝ, 0 < δ ∧ 0 < c ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → (X : ℝ) < Pa.N ^ δ →
      (X : ℝ) ≤ (Real.log Pa.N) ^ nuU →
    ‖Wcut (radN Pa) X β + Bcut (radN Pa) X β‖
      ≤ c * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N

/-! ## 2. The per-piece bundle -/

/-- **The seven areas at one datum**, in the exact bundle that the per-piece step consumes, at the
corrected objects: `Area1Sieve6`'s (5.10)+(5.22) with constant `c1`, `Area2₆`'s (9.10) with `Cb`,
`Area3₆`'s (10.10) with `C3`, and the conclusions of `Area6₆`, `Area4₆` and `Area7₆` at the fixed
cut `X` and exponent `σ` with constants `cU`, `cV`, `cW`.  (The first three conjuncts are quantified
over *all* admissible majorants and coefficients, as in the areas themselves, so that the bundle
can be instantiated at a class-restricted coefficient `β_{i,c}` of the reduction's piece.) -/
def AreaBounds6 (Pa : Work.FITop.Params) (f : ℤ → ℝ) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (X : ℕ) (σ : ℝ) (c1 Cb C3 cU cV cW : ℝ) : Prop :=
  (∀ f' φ' z0' β', IsMajorant6 Pa f' → IsBetaCoeff6 Pa φ' z0' β' →
      (‖Bstar Pa β' - Bfree Pa β'‖
          ≤ c1 * (Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((5 : ℝ) / 4)
              + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4))
            * (Real.log Pa.N) ^ (3 : ℕ)) ∧
      (Dform Pa f' β'
          ≤ Dstar Pa f' β'
            + c1 * Pa.τ ^ (2 : ℕ) * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
                + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
              * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ))) ∧
  (∀ f' φ' z0' β', IsMajorant6 Pa f' → IsBetaCoeff6 Pa φ' z0' β' →
      ‖Dstar Pa f' β' - D0 (radN Pa) (Fhat Pa f') β'‖
        ≤ Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2 * (Real.log Pa.N) ^ (bFun Pa.η)) ∧
  (∀ f' φ' z0' β', IsMajorant6 Pa f' → IsBetaCoeff6 Pa φ' z0' β' →
      ‖D0 (radN Pa) (Fhat Pa f') β' - cMain6 (Fhat Pa f') Pa.N * Tbeta (radN Pa) β'‖
        ≤ C3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))) ∧
  (‖Vcut (radN Pa) X β‖
      ≤ cV * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3)) * Pa.N ^ 2) ∧
  (‖Ucut (radN Pa) X β‖
      ≤ cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N) ∧
  (‖Wcut (radN Pa) X β + Bcut (radN Pa) X β‖
      ≤ cW * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N)


/-! ## 3. The round-3 transfer

The round-6 callers spell this `IsMajorant6.toMajorant`; the underlying declaration lives in
`Red6/IsMajorant6_toMajorant` (the harness requires a declaration's name to match its file's last
segment), so it is aliased here, in the module that both imports it and defines the areas. -/

theorem IsMajorant6.toMajorant {Pa : Work.FITop.Params} {f : ℤ → ℝ}
    (h : IsMajorant6 Pa f) : IsMajorant Pa f :=
  Work.FITop4.Red6.IsMajorant6_toMajorant h

end

end Work.FITop4
