/-
# `Submission.Work.FITop4.Defs4` — ROUND 4 of the FI area (B) contract: the repaired vocabulary

This is round 4 of the Friedlander–Iwaniec area (B) contract (`Submission/Work/FITop3/` is round 3,
`FITop/` round 2).  Round 3 was refereed by the area fleet; the two blocking findings were

* `FIArea5/area5_r3` — **`Work.FITop3.IsBetaCoeff` is too weak**: it records the smoothness of the
  mollifiers `q`, `p` of (5.12)/(4.14) by *unit-step differences* `|q(α+1) − q α| ≤ 32/θ` etc.
  For `θ ≤ 16` (true for every `Params`, since `θ = (log x)^{−A'} < 1`) those clauses are satisfied
  by *every* `[0,1]`-valued function supported in `[0,2πθ]`; the paper's `|q^{(j)}| ≪ θ^{−j}` —
  which is what produces the Fourier decay (16.26)/(16.27) used in the only proof of Lemma 16.2 —
  is not recorded, and `Area5` as stated is **false**.
* `FIComp/prop41_comp_r3` — the composition is blocked: `Area3` was `(log x)^A` too weak (the
  doc-string replacement of (10.10)'s `(τ^{-1}+θ)` by `(ϑ+θ)` reverses the inequality `ϑ² < ϑ`),
  and `Area2`'s error exponent `b` was an unbounded existential while the composition needs
  `b ≤ B + O(1)` with `B ≤ 2^31`.

## What this file fixes

**(a) `IsBetaCoeff` (this file).**  The mollifiers are required to be *genuinely smooth*: `q` and
`p` are `C²` (`ContDiff ℝ 2` — *not* `⊤`, which would be `C^∞`) with **absolute constants**
`c_j ≤ 2^{10j}` (`cMoll` below) in `|iteratedDeriv j q| ≤ c_j θ^{−j}`, `|iteratedDeriv j p| ≤
c_j (θN)^{−j}` for `j ≤ 2`, together with the support and size conditions of (4.12)/(5.12) and
the size `0 ≤ q, p ≤ 1`.  The derivatives of orders `j ≤ 2` are exactly what (16.26)–(16.28)
consume (two integrations by parts give `q̂(ℓ) ≪ θ(1+θ²ℓ²)^{−1}` and the Mellin decay of `p`);
see `NOTES.md` §1 for the check against the text of §16.  The witness — an explicit clamped
quintic bump — is in `Submission/Work/FITop4/Witness4/`.

**(b) `Area3` (in `Areas4.lean`).**  The error term is the paper's (10.10)
`(τ^{-1} + θ)θ⁴ M^{1/2}N^{3/2}(log N)^{2^{20}}` with `τ = Pa.τ`, the *same* truncation parameter
of (4.9)/(9.12)/(10.4).  (10.11) `τ ≥ ϑ^{-2}(log x)^{2^{20}}` is **not** a hypothesis of any area:
it is a choice the *composition* makes (`tauOf x A = (log x)^{2A+2^{20}}`), exactly as §18 does
("we may for example take ... `τ = (log x)^{A+2^{20}}`").

**(c) `Area2` (in `Areas4.lean`).**  The exponent `b` of (9.10) is the paper's explicit
`b(η) ≪ η^{−1/η}`: `bFun η = 2^{η^{-1}log η^{-1}+4} + 2^{η^{-1}log η^{-1}+1} + 4`.

**(d) the composition** is proved in `Areas4.lean` from the seven areas **plus** the one
hypothesis `AreaReduce` below; see `NOTES.md` §3 for why `AreaReduce` cannot be dispensed with
(it is the `§§4–5.2` reduction `B(x;N) ↝ B(M,N)`, which *no* round-3 area mentions) and what
its content is.

**(e) satisfiability** of every area's hypotheses is proved in `Witness4/` (see `Areas4.lean`).

**FROZEN (round 4).**  This file is frozen as of round 4.  Any change to a definition here
invalidates the certificates in `Comp/`, `Numeric4/`, `Witness4/` and `Bump4/`, so it must be
accompanied by a re-check.
-/

import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop.Defs

set_option autoImplicit false

namespace Work.FITop4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. The numerical constants of the composition

The paper's §18 lists the conditions that its parameters must satisfy:

* (4.4) `(loglog x)² ≤ log P ≤ (log x)(loglog x)^{-2}`  (in `Params`);
* (4.11) `τ ≥ (log x)^{A+124}` (in `Params`), superseded by
* (10.11) `τ ≥ ϑ^{-2}(log x)^{2^{20}} = (log x)^{2A+2^{20}}`;
* (10.12) `A' ≥ 2A + 2^{20}` (in `Params`);
* (5.11) `B ≥ (3/2)A + A'`;
* (9.12) `τ ≤ (log x)^{B/2 - 7A/4 - 2A' - b/2}`;
* (5.23) `τ ≤ x^{η/3}`.

The composition below *chooses* `A := Astar = 2^26+4` (the paper's value, the one for which the
proved chain consumes Proposition 4.1), `A' := Aprime A = 2A+2^{20}`, `θ := (log x)^{-A'}`,
`ϑ := (log x)^{-A}`, `τ := (log x)^{2A+2^{20}}`, and
`B := Bmax η := bFun η + 2^30`; the only condition of the list that involves `b(η)` is (9.12), and
it forces the `bFun η` summand of `Bmax`.  See `Areas4` (`piece_bound`) and `NOTES.md` §4. -/

/-- The paper's saving exponent `A = 2^{26}+4` (paragraph after (4.7): "it suffices to have (4.5)
with `A = 2^{26}+4`").  This is the exponent frozen in `Work.FITop.Prop41Statement`. -/
def Astar : ℝ := (2 : ℝ) ^ (26 : ℕ) + 4

/-- (10.12): `A' = 2A + 2^{20}` — "`A'` can be chosen much larger than `A`, for example
`A' ⩾ 2A + 2^{20}` would suffice". -/
def Aprime (A : ℝ) : ℝ := 2 * A + (2 : ℝ) ^ (20 : ℕ)

/-- (4.15): `θ = (log x)^{-A'}`. -/
def thetaOf (x : ℕ) (A : ℝ) : ℝ := (Real.log (x : ℝ)) ^ (-(Aprime A))

/-- (4.16): `ϑ = (log x)^{-A}`. -/
def varthetaOf (x : ℕ) (A : ℝ) : ℝ := (Real.log (x : ℝ)) ^ (-A)

/-- (10.11): the truncation parameter of (4.9)/(9.12)/(10.4) is chosen as
`τ = ϑ^{-2}(log x)^{2^{20}} = (log x)^{2A+2^{20}}`.  §18: "we may for example take
`A' = 2A + 2^{20}` and `τ = (log x)^{A+2^{20}}`" (the exponent displayed there is the (10.11) one
with the factor `2` on `A` absorbed into the (4.11) requirement; we keep the conservative
`2A + 2^{20}`, which is what §10's (10.11) actually reads). -/
def tauOf (x : ℕ) (A : ℝ) : ℝ := (Real.log (x : ℝ)) ^ (2 * A + (2 : ℝ) ^ (20 : ℕ))

/-- **The paper's error exponent of (9.10).**  §9: `D*(M,N) = D₀(M,N) + O(ϑ^{-1}τ²N²(log N)^b)`
"for some `b` depending on `η`; precisely `b = 2^{c+4} + 2^{c+1} + 4`" where `c = η^{-1}log η^{-1}`
("it suffices to take `c = η^{-1}log η^{-1}`").  So `b(η) = 2^{η^{-1}log η^{-1}+4} + ...`, which is
`≪ η^{-1/η}`; it is unbounded as `η → 0⁺`. -/
def bFun (η : ℝ) : ℝ :=
  (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) + (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 1) + 4

/-- **The range constant of the round-4 contract.**  The paper requires only "`B` sufficiently
large" (in terms of `η` and `A`); the two explicit conditions its proof uses are (5.11)
`B ⩾ (3/2)A + A'` and (9.12) `τ ⩽ (log x)^{B/2-7A/4-2A'-b/2}`, i.e. — with the composition's
`τ = (log x)^{2A+2^{20}}` (10.11) — the single condition
`B ⩾ b(η) + 7A/2 + 4A' + 4A + 2^{21}`.  We record the explicit (and slightly generous)
`Bmax η = bFun η + 2^{30}`, which dominates that requirement for `A = Astar`
(`7Astar/2 + 4Aprime Astar + 4Astar + 2^{21} ≈ 1.05·10^9 < 2^{30}`), see `Areas4.piece_bound`.

**This replaces the frozen `B ≤ 2^{31}` of `Work.FITop.Prop41Statement`.**  The replacement is
forced by the paper's own numerology: `bFun` is unbounded in `η`, so for every constant `C` there
is `η ∈ (0, 3/32)` with `Bmax η > C` — in particular with `C = 2^{31}`
(`Bmax_gt_two_pow_31` below).  This is exactly the situation the round-4 contract anticipates
("or restate the B range if the paper's numerology demands it, citing (4.6) and the remark after
(4.7)"). -/
def Bmax (η : ℝ) : ℝ := bFun η + (2 : ℝ) ^ (30 : ℕ)

abbrev BformAtil := Work.FITop.BformAtil
abbrev AcountAtil := Work.FITop.AcountAtil
abbrev Prop41Frozen := Work.FITop.Prop41Statement

/-! ## 1. The target: Proposition 4.1 (4.5) with the restated `B`-range -/

/-- **Friedlander–Iwaniec, Proposition 4.1**, in the frozen `Work.FITop.Prop41Statement` form
(the paper's sufficient form after (4.7): `A` fixed at the paper's value `2^{26}+4`), except that
the range constant is bounded by the explicit function `Bmax` of `η` rather than by the constant
`2^{31}`.  The proof `Areas4.prop41_of_areas4` produces `B = Bmax η`; the difference from the
frozen statement is *only* the `B`-range (see `Bmax`). -/
def Prop41Statement4 : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
    ∃ B K : ℝ, ∃ x₀ : ℕ, 0 < B ∧ B ≤ Bmax η ∧ 0 < K ∧
    ∀ x : ℕ, x₀ ≤ x → ∀ N : ℕ,
      (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ) →
      (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-B) →
      (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) →
      ∀ C : ℝ, 1 ≤ C → C ≤ (N : ℝ) ^ (1 - η) →
      ∀ Pz : ℕ, 2 ≤ Pz →
        (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ) →
        Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ) →
        BformAtil x N C ≤ K * AcountAtil x * (Real.log (x : ℝ)) ^ (4 - Astar)

/-- The frozen statement follows from `Prop41Statement4` **whenever** the `B`-range of
`Bmax` fits into `2^{31}` (for instance on a sub-interval of `η`'s).  Since `bFun` is unbounded,
no such implication can hold for *all* `η` (`Bmax_gt_two_pow_31`). -/
theorem Prop41Statement_of_Bmax_le (h : ∀ η : ℝ, 0 < η → η < 3 / 32 → Bmax η ≤ (2 : ℝ) ^ (31 : ℕ))
    (h4 : Prop41Statement4) : Work.FITop.Prop41Statement := by
  intro η hη0 hη1
  obtain ⟨B, K, x₀, hB0, hBle, hK, hbound⟩ := h4 η hη0 hη1
  exact ⟨B, K, x₀, hB0, le_trans hBle (h η hη0 hη1), hK, hbound⟩

/-! ## 2. The coefficient family of (4.13) + (5.13), with genuine smoothness (fix (a)) -/

abbrev InPolarBox := Work.FITop3.InPolarBox
abbrev NoSmallPrimes := Work.FITop3.NoSmallPrimes
abbrev IsBoxCoeff := Work.FITop3.IsBoxCoeff
abbrev IsMajorant := Work.FITop3.IsMajorant
abbrev Fhat := Work.FITop3.Fhat
abbrev annM := Work.FITop3.annM
abbrev Bfree := Work.FITop3.Bfree
abbrev Bstar := Work.FITop3.Bstar
abbrev Dform := Work.FITop3.Dform
abbrev Dstar := Work.FITop3.Dstar
abbrev D0formMod := Work.FITop3.D0formMod
abbrev TbetaMod := Work.FITop3.TbetaMod
abbrev UcutMod := Work.FITop3.UcutMod
abbrev VcutMod := Work.FITop3.VcutMod
abbrev WcutMod := Work.FITop3.WcutMod
abbrev BcutMod := Work.FITop3.BcutMod
abbrev logFac := Work.FITop3.logFac
abbrev C0mod := Work.FITop3.C0mod

/-- The absolute constants `c_j` of the mollifier derivative bounds:
`c_j = 2^{10j}`, so `c_0 = 1`, `c_1 = 1024`, `c_2 = 2^{20}`.  The paper's (4.14)/(5.12) state
`p^{(j)} ≪ (θN)^{-j}`, `q^{(j)} ≪ θ^{-j}` with an *unspecified* absolute implied constant; these
are explicit absolute constants, chosen to be comfortably satisfied by the explicit witness
(`Witness4.quinticStep`, `Witness4.bump`): a clamped-quintic bump of width `W` has
`|bump'| ≤ 4/W`, `|bump''| ≤ 20/W²`. -/
def cMoll (j : ℕ) : ℝ := (2 : ℝ) ^ (10 * j)

lemma cMoll_pos (j : ℕ) : 0 < cMoll j := by
  unfold cMoll; positivity

lemma cMoll_zero : cMoll 0 = 1 := by unfold cMoll; norm_num

/-- **The coefficient family `β` of (4.13)+(5.13)**, round 4 (fix (a)).

There are *fixed* mollifiers `q` (angular, supported on the sector (5.12)
`0 ≤ α ≤ 2πθ`, `0 ≤ q ≤ 1`, `|q^{(j)}| ≤ c_j θ^{-j}` for `j ≤ 2`) and `p` (radial, supported on
the segment (4.12) `(N, (1+θ)N]`, `0 ≤ p ≤ 1`, `|p^{(j)}| ≤ c_j (θN)^{-j}` for `j ≤ 2`), both
`C²` (`ContDiff ℝ 2` — *not* `⊤`, which would be `C^∞`), such that

  `β_z = q(arg z − φ)·p(|z|²)·μ(|z|²)·γ(|z|²; C)`

on the polar box (5.14) with `(z,Π) = 1` (5.8) and `τ(|z|²) ≤ τ` (5.9), and `β_z = 0` elsewhere.

The `C²` + absolute-derivative-bound clauses are what round 3 lacked: the *unit-step* difference
bounds of `Work.FITop3.IsBetaCoeff` are vacuous for `θ ≤ 16` for every `[0,1]`-valued function,
and it was the missing smoothness that made `Work.FITop3.Area5` false
(`FIArea5/area5_r3`, `FIArea5/NOTES.md`).  The bounds are stated for `j ≤ 2`, which is exactly
what (16.26)–(16.28) use (see `NOTES.md` §1). -/
def IsBetaCoeff (Pa : Work.FITop.Params) (φ : ℝ) (β : GaussianInt → ℂ) : Prop :=
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
          (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
       then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
       else 0))

/-- `|γ(n;C)| ≤ τ(n)`: a sum of `τ(n)` values of the Möbius function.  (Round-3 proof, kept
here because `IsBoxCoeff` is consumed by round 4's `Area4` in exactly this form.) -/
lemma abs_gammaTrunc_le (C : ℝ) (n : ℕ) :
    |Work.FIPlan.gammaTrunc C n| ≤ (n.divisors.card : ℝ) :=
  Work.FITop3.abs_gammaTrunc_le C n

/-- The Möbius factor is bounded by `1` in `ℂ`. -/
lemma norm_moebius_le_one (n : ℕ) : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 :=
  Work.FITop3.norm_moebius_le_one n

/-- **(fix (a), consistency)**: the full coefficient of (4.13)+(5.13) — with the *genuine*
smoothness of round 4 — is still a special case of the support-and-size predicate `IsBoxCoeff`
under which Lemma 10.1 and Proposition 15.1 estimate.  This is what lets the composition feed an
`IsBetaCoeff` into `Area4`; it is the round-3 proof `Work.FITop3.IsBetaCoeff.toBoxCoeff` with the
unit-step clauses replaced by `0 ≤ q ≤ 1`, `0 ≤ p ≤ 1` (the only clauses the argument used). -/
theorem IsBetaCoeff.toBoxCoeff {Pa : Work.FITop.Params} {φ : ℝ} {β : GaussianInt → ℂ}
    (h : IsBetaCoeff Pa φ β) : IsBoxCoeff Pa φ β := by
  obtain ⟨q, p, -, -, hq0, hq1, -, -, hp0, hp1, -, -, hβ⟩ := h
  constructor
  · intro z
    rw [hβ z]
    split_ifs with hz
    · have hqp : ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ ≤ 1 := by
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

/-! ## 3. The `§§4–5.2` reduction, as an explicit hypothesis

`BformAtil x N C` (the object of Proposition 4.1, `Work.FITop.Defs`) is the *sieve* bilinear form
`Σ_m |Σ_{N<n≤2N} μ(n)γ(n;C)ã(mn)|`; the seven areas speak *only* about the Gaussian objects
`Bfree/Bstar/Dform/Dstar/D0formMod/TbetaMod/UcutMod/VcutMod/WcutMod/BcutMod`.  The bridge between
the two is the paper's §4 (the `τ`-truncation (4.9), the smooth partition of unity (4.12)–(4.15),
the dyadic splitting (4.18), the absorption of `m ≤ ϑx/N`) together with the Gaussian identity
(5.2) `a_{mn} = (1/4)Σ_{|w|²=m}Σ_{|z|²=n}Z(Re wz)` and the angular splitting (5.12).

Nothing in `Work.FITop3` (nor in rounds 1–2) states this reduction, and it is *not* the analytic
content of any area.  We therefore state it as a separate hypothesis `AreaReduce`, in exactly the
form the composition consumes: the sharp form is dominated by a finite family of *free* Gaussian
forms `Bfree (Pa i) (β i)` at admissible data, up to an error of the size `ϑx^{3/4}(log x)^4`
that the target can absorb.  `NOTES.md` §3 records the proof route (all ingredients are in
`Commons/`) and the partial formalisation. -/

/-- The per-piece data of the reduction are *compatible* with the target's parameters: the same
`x`, `η`, `A = Astar`, `A' = Aprime Astar`, `θ`, `ϑ`, `τ`, `C`, `Pz`, and the piece's inner scale
`Pa.N` lies in the dyadic window `[N, 2N]` of the target.  Note `Pa.B` is *not* constrained: it
only enters `Params`' own range hypothesis `N < x^{1/2}(log x)^{-B}`, which the structure supplies
as a proof. -/
def PieceData (η : ℝ) (x N : ℕ) (C : ℝ) (Pz : ℕ) (Pa : Work.FITop.Params) : Prop :=
  Pa.x = x ∧ Pa.η = η ∧ Pa.A = Astar ∧ Pa.A' = Aprime Astar ∧
  Pa.θ = thetaOf x Astar ∧ Pa.ϑ = varthetaOf x Astar ∧ Pa.τ = tauOf x Astar ∧
  Pa.Pz = Pz ∧ Pa.C = C ∧ (N : ℝ) ≤ Pa.N ∧ Pa.N ≤ 2 * (N : ℝ)

/-- **The `§§4–5.2` reduction.**  There are `c > 0` and `x₀` such that for every datum of
Proposition 4.1 with `x ≥ x₀`, the sieve bilinear form `B(x;N)` is dominated by a finite family
of free Gaussian bilinear forms at *admissible* data (each piece carries `IsMajorant` and
`IsBetaCoeff` and is compatible with the target's parameters), with

* the geometric piece-count (`Σ_i (M_iN_i)^{3/4} ≤ c·θ^{-2}·x^{3/4}`, which is what the dyadic
  splitting (4.18) plus the `θ^{-2}` polar boxes (5.14) produce — the `M`-sum is geometrically
  dominated and the smooth partition contributes `θ^{-1}` radial pieces), and
* an error `c·ϑ·x^{3/4}·(log x)^4`, which is the paper's residual `O(θA(x)(log x)^4)` together
  with the (4.10) `τ`-removal error, and which the target absorbs exactly (its exponent is
  `4 - Astar` and `ϑ = (log x)^{-Astar}`).

This is the *only* hypothesis of the composition besides the seven areas. -/
def AreaReduce : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℕ, ∀ (η : ℝ) (hη0 : 0 < η) (hη1 : η < 3 / 32) (x : ℕ) (hx : x₀ ≤ x)
      (N : ℕ) (hNlo : (x : ℝ) ^ ((1 : ℝ) / 4 + η) < (N : ℝ))
      (hNhi : (N : ℝ) < (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(Bmax η)))
      (hll : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)))
      (C : ℝ) (hC1 : 1 ≤ C) (hC2 : C ≤ (N : ℝ) ^ (1 - η))
      (Pz : ℕ) (hP2 : 2 ≤ Pz)
      (hPlo : (Real.log (Real.log (x : ℝ))) ^ 2 ≤ Real.log (Pz : ℝ))
      (hPhi : Real.log (Pz : ℝ) ≤ Real.log (x : ℝ) * (Real.log (Real.log (x : ℝ))) ^ (-2 : ℤ)),
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (s : Finset ι)
      (Pa : ι → Work.FITop.Params) (f : ι → ℤ → ℝ) (φ : ι → ℝ) (β : ι → GaussianInt → ℂ),
      (∀ i ∈ s, PieceData η x N C Pz (Pa i)) ∧
      (∀ i ∈ s, IsMajorant (Pa i) (f i)) ∧
      (∀ i ∈ s, IsBetaCoeff (Pa i) (φ i) (β i)) ∧
      (∑ i ∈ s, (((Pa i).M * (Pa i).N) ^ ((3 : ℝ) / 4)))
        ≤ c * (thetaOf x Astar) ^ (-(2 : ℝ)) * (x : ℝ) ^ ((3 : ℝ) / 4) ∧
      BformAtil x N C ≤ (∑ i ∈ s, ‖Bfree (Pa i) (β i)‖)
        + c * (varthetaOf x Astar) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log (x : ℝ)) ^ (4 : ℕ)

/-- **The exponent `σ` of Proposition 10.2 used by the composition.**  It is a *fixed* number
(independent of `x`): `σ = 2A + 4A' + 9`.  The paper's condition for the (10.10) error is
`τ^{-1} + θ ≤ 2ϑ²`, and Proposition 10.2 needs `(log N)^{-σ} ≪ ϑ²θ⁴(log MN)^8`, i.e.
`(log N)^σ ≥ 16 (log x)^{2A+4A'}(log MN)^8`; since `log x ≤ (4/(1+4η))log N` this holds for
`σ = 2A + 4A' + 9` once `log x` exceeds an explicit (astronomically large) threshold
`(4/(1+4η))^{2A+4A'+9}·16`, which the composition absorbs into `x₀`.  Keeping `σ` *fixed* is what
makes the cut `X` (§2.3) and hence the constant `c_ν` of `Area6` independent of `x`, so that the
target's constant `K` can be a constant. -/
def sigmaChoice (A : ℝ) : ℝ := 2 * A + 4 * Aprime A + 9

/-- The cut `X = ⌈(log N)^{3σ+3}⌉` of Proposition 10.2. -/
def Xcut (Pa : Work.FITop.Params) (σ : ℝ) : ℕ := ⌈(Real.log Pa.N) ^ (3 * σ + 3)⌉₊

/-- **The (5.20)/(5.25) budget of one dyadic/polar piece**:
`T = ϑ²θ⁴M^{1/2}N^{3/2}(log(MN))^8`.  The composition's per-piece step shows each error term
(`Area1Sieve`'s (5.22), `Area2`'s (9.10), `Area3`'s (10.10), and the main term fed by
`Area4`/`Area6`/`Area7` through Proposition 10.2) is at most a fixed fraction of `T`; see
`Areas4.piece_bound`. -/
def Tbudget (Pa : Work.FITop.Params) : ℝ :=
  Pa.ϑ ^ (2 : ℕ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
    * (Real.log (Pa.M * Pa.N)) ^ (8 : ℕ)

/-- **The numerical side conditions of the per-piece step**, at the explicit choices of
`Defs4`.  Each conjunct says that one of the error terms is at most an eighth of `Tbudget`
(the main term is allowed a half).  They are *not* hypotheses of any area: they are proved from
`θ = thetaOf x A`, `ϑ = varthetaOf x A`, `τ = tauOf x A` and `x ≥ x₀`
(`Numeric4.numHyp`), i.e. they are the log-arithmetic of the composition. -/
def NumHyp (η : ℝ) (x : ℕ) (Pa : Work.FITop.Params) (σ : ℝ)
    (c1 Cb C3 cUVW : ℝ) : Prop :=
  (8 * C3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
      * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ)) ≤ Tbudget Pa) ∧
  (8 * Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2 * (Real.log Pa.N) ^ (bFun η) ≤ Tbudget Pa) ∧
  (8 * c1 * Pa.τ ^ (2 : ℕ) * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
      + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
      * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) ≤ Tbudget Pa) ∧
  (16 * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
      * ((Real.log Pa.N) ^ (-σ) + (Pa.Pz : ℝ)⁻¹ * Real.log Pa.N) ≤ Tbudget Pa)

/-- **The seven areas, evaluated at one datum**, in the exact bundle that the per-piece step
consumes: `Area1Sieve`'s (5.10) and (5.22) (with constant `c1`), `Area2`'s (9.10) (with `Cb`),
`Area3`'s (10.10) (with `C3`), and the conclusions of `Area6` (16.41), `Area4` (Proposition 15.1)
and `Area7` (17.19) at the *fixed* cut `X` and exponent `σ` (with constants `cU`, `cV`, `cW`).

Only the Cauchy step's endpoint is packaged here: `Area4`'s, `Area6`'s and `Area7`'s *range*
hypotheses (`1 ≤ X ≤ N^{1/9}`, `X ≤ (log N)^{3σ+4}`, `X < N^δ`) are consumed by the composition
when it produces this bundle from `Area4`, `Area6`, `Area7` (they are the composition's choice of
`X`); the bundle itself is only the resulting norm bounds. -/
def AreaBounds (Pa : Work.FITop.Params) (f : ℤ → ℝ) (φ : ℝ) (β : GaussianInt → ℂ)
    (X : ℕ) (σ : ℝ) (c1 Cb C3 cU cV cW : ℝ) : Prop :=
  (∀ f' φ' β', IsMajorant Pa f' → IsBetaCoeff Pa φ' β' →
      (‖Bstar Pa β' - Bfree Pa β'‖
          ≤ c1 * (Pa.M ^ ((1 : ℝ) / 4) * Pa.N ^ ((5 : ℝ) / 4)
              + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4))
            * (Real.log Pa.N) ^ (3 : ℕ)) ∧
      (Dform Pa f' β'
          ≤ Dstar Pa f' β'
            + c1 * Pa.τ ^ (2 : ℕ) * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
                + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
              * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ))) ∧
  (∀ f' φ' β', IsMajorant Pa f' → IsBetaCoeff Pa φ' β' →
      ‖Dstar Pa f' β' - D0formMod (Work.FITop.radN Pa) (Fhat Pa f') β'‖
        ≤ Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2 * (Real.log Pa.N) ^ (bFun Pa.η)) ∧
  (∀ f' φ' β', IsMajorant Pa f' → IsBetaCoeff Pa φ' β' →
      ‖D0formMod (Work.FITop.radN Pa) (Fhat Pa f') β'
          - Work.FIPlan.cMain (Fhat Pa f') Pa.N * Work.FITop3.TbetaMod (Work.FITop.radN Pa) β'‖
        ≤ C3 * (Pa.τ⁻¹ + Pa.θ) * Pa.θ ^ (4 : ℕ) * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2)
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (20 : ℕ))) ∧
  (‖Work.FITop3.VcutMod (Work.FITop.radN Pa) X β‖
      ≤ cV * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3)) * Pa.N ^ 2) ∧
  (‖Work.FITop3.UcutMod (Work.FITop.radN Pa) X β‖
      ≤ cU * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N) ∧
  (‖Work.FITop3.WcutMod (Work.FITop.radN Pa) X β + Work.FITop3.BcutMod (Work.FITop.radN Pa) X β‖
      ≤ cW * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N)

/-- **The per-piece facts the composition needs at each piece of `AreaReduce`**, for the *fixed*
choices `σ = sigmaChoice Astar` and the area-7 exponent `δ`:

* the `σ`-hypothesis of `NumHyp`'s fourth conjunct at the piece: with `ϑ = (log x)^{-Astar}` and
  `θ = (log x)^{-Aprime Astar}` it says `16(log(Pa.M·Pa.N))^8(log x)^{2A+4A'} ≤ (log Pa.N)^σ`, i.e.
  `16(log Pa.N)^{-σ} ≤ ϑ²θ⁴(log(MN))^{-8}` — stronger than the `(log ·)^{-σ}` term of `NumHyp`
  needs (Proposition 10.2's saving), and it holds for all `x ≥ x₀` because
  `Pa.N > x^{1/4+η}` and `Pa.M·Pa.N ≤ x`;
* the *range* facts for the cut `X = Xcut Pa σ = ⌈(log Pa.N)^{3σ+3}⌉`: `1 ≤ X`,
  `X ≤ Pa.N^{1/9}` (Area 4), `X ≤ (log Pa.N)^{3σ+4}` (Area 6), `X < Pa.N^δ` (Area 7), all of
  which hold for `x ≥ x₀` by `Numeric4.log_dominance`;
* `16 ≤ Pa.M` (the (7.7) normalisation needs `M ≥ 16`) and `3 ≤ Pa.N` (Proposition 10.2). -/
def PieceFacts (η δ σ : ℝ) (x : ℕ) (Pa : Work.FITop.Params) : Prop :=
  (16 * (Real.log (Pa.M * Pa.N)) ^ (8 : ℕ) * (Real.log (x : ℝ)) ^ (2 * Astar + 4 * Aprime Astar)
      ≤ (Real.log Pa.N) ^ σ) ∧
  (1 ≤ Xcut Pa σ) ∧
  ((Xcut Pa σ : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9)) ∧
  ((Xcut Pa σ : ℝ) ≤ (Real.log Pa.N) ^ (3 * σ + 4)) ∧
  ((Xcut Pa σ : ℝ) < Pa.N ^ δ) ∧
  (16 ≤ Pa.M) ∧ (3 ≤ Pa.N)

/-! ## 4. Elementary properties of the numerology -/

lemma bFun_pos (η : ℝ) : 0 < bFun η := by
  unfold bFun
  have h1 : 0 < (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2 : 0 < (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  linarith

lemma Bmax_pos (η : ℝ) : 0 < Bmax η := by
  unfold Bmax
  have := bFun_pos η
  have : (0:ℝ) < (2:ℝ) ^ (30 : ℕ) := by positivity
  linarith

/-- `b(η)` is unbounded: at `η = 1/32` the paper's exponent already exceeds `2^{30}`, so
`Bmax (1/32) = bFun (1/32) + 2^{30} > 2^{31}`.  This is the machine-checked obstruction to
keeping the frozen `B ≤ 2^{31}`: the round-3 contract's `B`-range is *not* achievable for every
`η ∈ (0, 3/32)` from the areas, by the paper's own (9.10) + (9.12) ((4.6) and the remark after
(4.7) require `B` to grow with `b(η)`). -/
theorem Bmax_gt_two_pow_31 : ∃ η : ℝ, 0 < η ∧ η < 3 / 32 ∧ (2 : ℝ) ^ (31 : ℕ) < Bmax η := by
  refine ⟨1 / 32, by norm_num, by norm_num, ?_⟩
  have hlog : (3 : ℝ) < Real.log 32 := by
    rw [← Real.exp_lt_exp, Real.exp_log (by norm_num : (0 : ℝ) < 32)]
    have h1 : Real.exp 3 = (Real.exp 1) ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h1]
    have h2 : (Real.exp 1) ^ 3 < (3 : ℝ) ^ 3 :=
      pow_lt_pow_left₀ Real.exp_one_lt_three (by positivity) (by norm_num)
    linarith
  have h1 : (2 : ℝ) ^ (32 * Real.log 32 + 1) ≤ bFun (1 / 32) := by
    unfold bFun
    rw [show ((1 / 32 : ℝ))⁻¹ = 32 by norm_num]
    have hp : (0 : ℝ) < (2 : ℝ) ^ (32 * Real.log 32 + 1) := Real.rpow_pos_of_pos (by norm_num) _
    have hle : (2 : ℝ) ^ (32 * Real.log 32 + 1) ≤ (2 : ℝ) ^ (32 * Real.log 32 + 4) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    linarith
  have h2 : (2 : ℝ) ^ (97 : ℝ) ≤ (2 : ℝ) ^ (32 * Real.log 32 + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (31 : ℕ) < (2 : ℝ) ^ (97 : ℝ) := by
    have hn : (2 : ℝ) ^ (31 : ℕ) < (2 : ℝ) ^ (97 : ℕ) :=
      pow_lt_pow_right₀ (by norm_num) (by norm_num)
    have hr : (2 : ℝ) ^ (97 : ℕ) = (2 : ℝ) ^ ((97 : ℕ) : ℝ) :=
      (Real.rpow_natCast (2 : ℝ) 97).symm
    linarith
  unfold Bmax
  have h30 : (0 : ℝ) < (2 : ℝ) ^ (30 : ℕ) := by positivity
  linarith

end

end Work.FITop4
