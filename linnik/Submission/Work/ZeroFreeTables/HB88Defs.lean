/-
# ZeroFreeTables — HB88Defs

Definitions and interfaces for the proof of **HB Lemma 8.8** (Heath-Brown, PLMS 64 (1992)
265–338, p. 47): for `χ₁`, `ρ₁` real, `λ₂ ≥ (12/11 − ε)·log(1/λ₁)` for `q ≥ q(ε, lamS)` whenever
`λ₁ ≥ lamS` (the `λ₁`-floor which removes the cap issue of HB's §8), together with
`λ₁ < 0.696 → λ₂ ≥ 0.745`.

The proof route (see the header of `HBLemma8_8_proof.lean`) is a *parametric row* argument:

* `Lam0RowParam K` — the **same-character** rows: for *every* pair `b < c ≤ K` (a single
  threshold `q₀(K)` serves the whole box), every zero `u ≠ ρ₁` of `χ₁` with `|Im u| ≤ 1` has
  `λ(u) ≥ c` as soon as `λ₁ ≤ b`.  This is HB's §6/§8 second-zero repulsion, proved from
  `Work.LinnikAreas.DhRepel.lemma6_3_fullH` (HB Lemma 6.3) with the §7 extremal test function at
  `k = 2`; the strict failure of the associated inequality at `(b,c)` is the *certificate*
  `Lam0Cert`.
* `Lam2RowParam K` — the **other-character** rows: for every `b < c ≤ K` the hypotheses of the
  five-term configuration (RowBodyB of `HBTable7_of_count` with the χ₁-window supplied
  separately) together with `λ₁ ≤ b`, `λ₂ ≤ c` are contradictory; hence every zero of a character
  `∉ {χ₁,χ₁⁻¹}` in the working region has `λ ≥ c`.  This is HB Lemma 8.5 in the *mixed* constant
  form `c(χ₁) = 1/8`, `c(χ₂) = c(χ₁χ₂) = c(χ₁χ₂⁻¹) = 1/6`, i.e. slack `1/8 + 2·(1/6) = 11/24`
  (HB's `ψ ≤ 11/24`); its certificate is `Lam2Cert`.
* `PairParam K` — the *second pair* of §6 (the pigeonhole of HB's Lemma 6.1): given a zero `ρ`
  of `χ ∉ {χ₁,χ₁⁻¹}` with `λ(ρ) < K`, a pair `(χ₂,ρ₂)` with the same bound and the ball
  minimality at radius `2|ρ₂.im| + 1` exists (a `λ`-minimiser over a doubling sequence of boxes
  terminates because the number of zeros with `λ ≤ K` is bounded — the count `OtherLamCountLeK`).
* `OtherLamCountLeK` — the parametric family zero count: for each `K` there are `C, Q` with
  `otherLamCount χ₁ Λ H ≤ C` for all `Λ ≤ K`, `H ≤ 10 log q`, `q ≥ Q` (from
  `Work.ZeroDensity.LogFree.logFreeNP`).

Everything is stated in the frozen vocabulary (`Work.LinnikContract`, `Work.ZeroFreeTables`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.HBTable7_defs2

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The triangle (tent) test function -/

/-- The tent test function `t ↦ max (x − t) 0` of HB §8.1. -/
def tent (x : ℝ) : ℝ → ℝ := fun t => max (x - t) 0

theorem tent_zero {x : ℝ} (hx : 0 ≤ x) : tent x 0 = x := by
  simpa [tent] using max_eq_left hx

theorem tent_nonneg (x t : ℝ) : 0 ≤ tent x t := le_max_right _ _

theorem tent_supp {x t : ℝ} (h : x ≤ t) : tent x t = 0 := max_eq_right (by linarith)

theorem tent_integral {x : ℝ} (hx : 0 ≤ x) : (∫ t in (0:ℝ)..x, tent x t) = x ^ 2 / 2 := by
  have hcongr : (∫ t in (0:ℝ)..x, tent x t) = ∫ t in (0:ℝ)..x, (x - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    exact max_eq_left (by linarith [ht.2])
  rw [hcongr]
  have hsub : (∫ t in (0:ℝ)..x, (x - t))
      = (∫ t in (0:ℝ)..x, (fun _ : ℝ => x) t) - ∫ t in (0:ℝ)..x, t :=
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _)
  rw [hsub, intervalIntegral.integral_const, integral_id]
  ring

/-! ## The two parametric row predicates -/

/-- **The same-character rows, parametrically in the box `(0,K]²`.**

For every `b, c` with `0 < b`, `b < c`, `c ≤ K` there is a single threshold `q₀` (uniform in
`(b,c)` — the test function of the certificate is *fixed*) such that: for real `χ₁` with real
exceptional zero `ρ₁` (`IsMin1WideAt 10`), `λ₁ ≤ b`, `λ₁ < 0.348` (so that `ρ₁` is simple, HB
Theorem 1) and `zeroMult χ₁ ρ₁ = 1`, every *other* zero `u` of `χ₁` in the working region
(`|Im u| ≤ 1`) has `λ(u) ≥ c`.

This is HB's §6 second-zero repulsion (Lemma 6.3 / Lemma 8.1) with the §7 extremal test function
at `k = 2`, in the parametric form needed by the finitely many rows of the assembly.

**Staircase.**  The pair `(b,c)` must sit on the staircase of the repulsion, i.e.
`c ≤ (12/11)·log(2/b) + 1`: the certificate (strict failure of the engine's inequality at `(b,c)`)
holds exactly below this curve, and without the restriction the statement is false (the engine's
LHS is increasing in `c` and positive for large `c`). -/
def Lam0RowParam (K : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → zeroMult χ₁ ρ₁ = 1 →
    ∀ b c : ℝ, 0 < b → b < c → c ≤ K → c ≤ (12/11) * Real.log (2 / b) + 1 →
      lamOf q ρ₁ ≤ b → lamOf q ρ₁ < 348/1000 →
      ∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ 1 → u ≠ ρ₁ → c ≤ lamOf q u

/-- **The other-character rows, parametrically in the box `(0,K]²`.**

For every `b, c` with `0 < b`, `b < c`, `c ≤ K`, the five-term configuration of HB Lemma 8.5
(the pair `(χ₂,ρ₂)` with the ball minimality over `|Im u| ≤ 2|ρ₂.im| + 1`, the four `L`-function
maximalities, the two divisor conditions, and the χ₁-window maximality at height 1 supplied
separately) is contradictory with `λ₁ ≤ b` and `λ₂ ≤ c`.  Consequently every zero of a character
`χ ∉ {χ₁,χ₁⁻¹}` of the working region has `λ ≥ c` when `λ₁ ≤ b`.

The constants are `c(χ₁) = 1/8`, `c(χ₂) = c(χ₁χ₂) = c(χ₁χ₂⁻¹) = 1/6` (so HB's slack
`11/24 = c(χ₁) + c(χ₂) + (c(χ₁χ₂)+c(χ₁χ₂⁻¹))/2`).  As in `Lam0RowParam` the pair `(b,c)` must sit
on the staircase `c ≤ (12/11)·log(2/b) + 1` (below which the certificate holds); without that
restriction the statement is false, since the engine's left hand side is increasing in `c`. -/
def Lam2RowParam (K : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ)
    (χ₂ : DirichletCharacter ℂ q) [NeZero χ₁.conductor] [NeZero χ₂.conductor],
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ * χ₁ = 1 → ρ₁.im = 0 →
    χ₂ ≠ 1 → χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ →
    zeroMult χ₂ ρ₂ ≠ 0 →
    (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ →
      zeroMult ψ u ≠ 0 → |u.im| ≤ 2 * |ρ₂.im| + 1 → lamOf q ρ₂ ≤ lamOf q u) →
    DirichletCharacter.LFunction χ₁ ((ρ₁.re : ℂ)) = 0 →
    DirichletCharacter.LFunction χ₂ (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) = 0 →
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|ρ₂.im| + 2))) ((ρ₁.re : ℂ)) ≠ 0 →
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
        (Metric.closedBall 0 (|ρ₂.im| + 2))) (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) ≠ 0 →
    (∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
      |u.im| ≤ 1 → u = ((ρ₁.re : ℂ)) ∨ u.re ≤ ρ₂.re) →
    |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) →
    ∀ b c : ℝ, 0 < b → b < c → c ≤ K → c ≤ (12/11) * Real.log (2 / b) + 1 →
      lamOf q ρ₁ ≤ b → lamOf q ρ₂ ≤ c → False

/-- **The parametric family zero count.**  For every `K > 0` there are `C > 0` and `Q` such that
for `q ≥ Q` the multiplicity-weighted number of zeros of the characters `χ ∉ {1, χ₁, χ₁⁻¹}` with
`λ ≤ Λ` and `|Im| ≤ H` is at most `C`, for all `Λ ≤ K` and `H ≤ 10 log q`.

This is the log-free family zero-density estimate (Jutila) in the `λ`-normalisation, with the
level restricted below the fixed constant `K`; it is the input of the §6 pigeonhole. -/
def OtherLamCountLeK (K : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (Λ H : ℝ),
    Λ ≤ K → H ≤ 10 * Real.log (q : ℝ) → otherLamCount χ₁ Λ H ≤ C

/-- **The second pair of HB's §6 numbering, parametrically.**  For every `K > 0` there is a
threshold `Q` such that for `q ≥ Q`: given real `χ₁` with real exceptional zero `ρ₁`
(`IsMin1WideAt 10`, `λ₁ < 0.696`) and a zero `ρ` of a character `χ ∉ {1, χ₁, χ₁⁻¹}` in the
working region with `λ(ρ) < K`, there is a pair `(χ₂,ρ₂)` with `χ₂ ∉ {1,χ₁,χ₁⁻¹}`,
`zeroMult χ₂ ρ₂ ≠ 0`, `λ(ρ₂) ≤ λ(ρ)`, the height condition `2|ρ₂.im| + 1 ≤ 10 log q` and the
window minimality `λ(ρ₂) ≤ λ(u)` for every zero `u` of a character `ψ ∉ {1,χ₁,χ₁⁻¹}` with
`|Im u| ≤ 2|ρ₂.im| + 1`.

This is `Work.ZeroFreeTables.second_pair_wide` with the count hypothesis lifted to the level `K`
(the doubling pigeonhole of HB Lemma 6.1). -/
def PairParam (K : ℝ) : Prop :=
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    (χ : DirichletCharacter ℂ q) (ρ : ℂ),
    IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → lamOf q ρ₁ < 696 / 1000 →
    IsZ χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → lamOf q ρ < K →
    ∃ (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ),
      χ₂ ≠ 1 ∧ χ₂ ≠ χ₁ ∧ χ₂ ≠ χ₁⁻¹ ∧ zeroMult χ₂ ρ₂ ≠ 0 ∧
      lamOf q ρ₂ ≤ lamOf q ρ ∧
      2 * |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) ∧
      ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ →
        zeroMult ψ u ≠ 0 → |u.im| ≤ 2 * |ρ₂.im| + 1 → lamOf q ρ₂ ≤ lamOf q u

end Work.ZeroFreeTables
