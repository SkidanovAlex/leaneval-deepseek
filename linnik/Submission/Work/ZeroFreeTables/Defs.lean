/-
# ZeroFreeTables — Defs.lean  (AREA 3 `ZeroFreeCert` of `LinnikPlan/ROUTE_LEAD.md` §3.1)

This module *is* the interface of AREA 3: it states, verbatim, the mathematical
content of `Z1`–`Z5` and of `ZeroFreeCert` from `ROUTE_LEAD.md` §3.1, in the
vocabulary frozen by the contract subproject `Work.LinnikContract` (module
`Submission.Work.LinnikContract.Defs`).

Sources
* **[HB]** D. R. Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the
  least prime in an arithmetic progression*, Proc. LMS (3) **64** (1992), 265–338.
  Theorems 1–3 (p. 3), Tables 8, 9, 10 (pp. 54–56), Lemma 10.3 (p. 76).
* **[X]** T. Xylouris, *Über die Linniksche Konstante*, Diplomarbeit, arXiv:0906.2749.
  Lemma 3.8 (`l1-abschaetzungen-werte`: `λ₁ > 0.628` for `ord χ₁ = 2`).

Conventions (inherited from `Work.LinnikContract`, do not change)
* `lamOf q ρ = (1 - Re ρ) log q`; `IsZ χ ρ` is HB's working region (`χ ≠ 1`,
  `ρ` a non-trivial zero of `L(s,χ)`, `|Im ρ| ≤ 1`); `zeroMult` counts multiplicity
  through the *primitive* character inducing `χ`.
* `IsMin1 χ₁ ρ₁`: `ρ₁` is a zero of `χ₁` of *maximal* `lamOf` among all
  `(χ,ρ)` with `IsZ χ ρ` — HB's `ρ₁`, `λ₁ = lamOf q ρ₁`.
* `Lam0Bound χ₁ ρ₁ c`: every zero of `χ₁` in the working region other than `ρ₁`
  (and other than `conj ρ₁` when `χ₁` is real) has `λ ≥ c`; and if `ρ₁` is a
  multiple zero then `c ≤ λ₁` as well.
* `Lam2Bound χ₁ c`: every zero of a character `≠ χ₁, χ₁⁻¹` has `λ ≥ c`.
* `Lam3Bound χ₁ c`: there is `χ₂` such that every zero of a character
  `≠ χ₁^{±1}, χ₂^{±1}` has `λ ≥ c`.

The tables `rows15` / `rows14` are *exactly* the lists of `ROUTE_LEAD.md` §3.1:
`rows15` is `(λ₁-interval, λ₀, λ₂, λ₃)`, each numeric entry being the corresponding
entry of HB's Tables 8, 10 and 9 lowered by `0.001` (`λ₃` additionally capped by
`6/7`, itself lowered by `0.001` to `0.856`), read at the *right* end of the
interval; `rows14` is `(λ₁-interval, c)` with `c = min(λ₀,λ₂)` for the
Deuring–Heilbronn range `λ₁ < 0.348`.  The provenance of every entry is proved in
`Submission/Work/ZeroFreeTables/Tables.lean`.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikContract2.Contract

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-! ## The tables of `ROUTE_LEAD.md` §3.1 -/

/-- Rows `(lo, hi, λ₀, λ₂, λ₃)`: HB Tables 8, 10 and 9 (the last capped by `6/7`),
read at `λ₁ = hi` and each lowered by `0.001`.

This is *literally* the frozen `Work.LinnikContract.rows15` of the contract
(`Submission/Work/LinnikContract/Areas.lean`), so that everything proved about it
below applies to the frozen statement verbatim. -/
abbrev rows15 : List (ℝ × ℝ × ℝ × ℝ × ℝ) := Work.LinnikContract.rows15

/-- Rows `(lo, hi, c)` for `λ₁ < 0.348` (`χ₁`, `ρ₁` real): `min(λ₀, λ₂) ≥ c`.
Literally the frozen `Work.LinnikContract.rows14`. -/
abbrev rows14 : List (ℝ × ℝ × ℝ) := Work.LinnikContract.rows14

/-! ## The seven conditions of `ZeroFreeCert` -/

/-- **(Z1) HB Theorem 1.** Below `λ₁ < 0.348` the zero `ρ₁` is a real, simple zero of a
real character `χ₁`, and it is the *only* zero in the region `σ ≥ 1 - 0.348/𝓛`,
`|t| ≤ 1`. -/
def Z1 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  LinnikContract.lamOf q ρ₁ < 0.348 →
    χ₁ ^ 2 = 1 ∧ ρ₁.im = 0 ∧ LinnikContract.zeroMult χ₁ ρ₁ = 1 ∧
      ∀ χ ρ, LinnikContract.IsZ χ ρ → (χ ≠ χ₁ ∨ ρ ≠ ρ₁) → 0.348 ≤ LinnikContract.lamOf q ρ

/-- **(Z2)** If `χ₁` is real and `ρ₁` is not, then `λ₁ ≥ 0.56`.
([X] Lemma 3.8 proves `0.628`; HB Lemma 9.5 only gives `0.518`, which is not enough.) -/
def Z2 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 → 0.56 ≤ LinnikContract.lamOf q ρ₁

/-- **(Z3) The universal bounds**: HB Theorem 2 (`λ₀ ≥ 0.696`, `λ₂ ≥ 0.702`) and
Lemma 10.3 (`λ₃ ≥ 6/7`), each lowered by `0.001`. -/
def Z3 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  LinnikContract.Lam0Bound χ₁ ρ₁ 0.695 ∧ LinnikContract.Lam2Bound χ₁ 0.701 ∧
    LinnikContract.Lam3Bound χ₁ 0.856

/-- **(Z4) The §15 rows**: for every row of `rows15` whose `λ₁`-interval contains `λ₁`,
the three bounds of that row hold. -/
def Z4 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  ∀ r ∈ rows15, r.1 ≤ LinnikContract.lamOf q ρ₁ → LinnikContract.lamOf q ρ₁ ≤ r.2.1 →
    LinnikContract.Lam0Bound χ₁ ρ₁ r.2.2.1 ∧ LinnikContract.Lam2Bound χ₁ r.2.2.2.1 ∧
      LinnikContract.Lam3Bound χ₁ r.2.2.2.2

/-- **(Z5), rows part**: the §14 rows (Deuring–Heilbronn), valid for `λ₁ ≥ lamS`. -/
def Z5rows {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) (lamS : ℝ) : Prop :=
  ∀ r ∈ rows14, lamS ≤ LinnikContract.lamOf q ρ₁ → r.1 ≤ LinnikContract.lamOf q ρ₁ →
    LinnikContract.lamOf q ρ₁ < r.2.1 →
      LinnikContract.Lam0Bound χ₁ ρ₁ r.2.2 ∧ LinnikContract.Lam2Bound χ₁ r.2.2

/-- **(Z5), repulsion part**: the `(1 - ε) log(1/λ₁)` Deuring–Heilbronn repulsion
(HB Lemmas 8.4, 8.6, 8.8; cf. `[X]` §3.6), used for `λ₁ < 0.2`. -/
def Z5rep {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) (lamS : ℝ) : Prop :=
  lamS ≤ LinnikContract.lamOf q ρ₁ → LinnikContract.lamOf q ρ₁ < 0.2 →
    LinnikContract.Lam0Bound χ₁ ρ₁ ((99/100) * Real.log (1 / LinnikContract.lamOf q ρ₁)) ∧
      LinnikContract.Lam2Bound χ₁ ((99/100) * Real.log (1 / LinnikContract.lamOf q ρ₁))

/-- **(Z5)**: the whole Deuring–Heilbronn part of `ZeroFreeCert`. -/
def Z5 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) (lamS : ℝ) : Prop :=
  Z5rows χ₁ ρ₁ lamS ∧ Z5rep χ₁ ρ₁ lamS

/-- **HB's numbering at height `H`.**  `IsMin1WideAt H χ₁ ρ₁` is the frozen `IsMin1`
together with the minimality of `λ₁` among the zeros of *all* non-principal
characters in the strip `|Im| ≤ H`: this is HB's (6.1)–(6.2) with the rectangle of
height `H` in place of the working region `|Im| ≤ 1`.  `IsMin1Wide` is the case
`H = 𝓛 = log q`; HB's proofs only ever see zeros with `|Im| ≤ 3 + δ < 𝓛` (for `q`
large), which is why that height suffices, while any *larger* height (e.g. the
`10𝓛` of HB §6's elimination step) is also admissible, by `IsMin1WideAt.mono`.

This is the shape in which the area is ready to consume a revised contract whose
`λ₁` is defined over HB's rectangle (announced by the project lead as
`LinnikContract2`): a consumer holding minimality over `|Im| ≤ H` with `𝓛 ≤ H`
obtains `IsMin1Wide` by `IsMin1WideAt.mono`. -/
def IsMin1WideAt {q : ℕ} [NeZero q] (H : ℝ) (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  LinnikContract.IsMin1 χ₁ ρ₁ ∧ ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), χ ≠ 1 →
    LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ H → LinnikContract.lamOf q ρ₁ ≤ LinnikContract.lamOf q u


/-! ## The frozen statement -/

/-- **AREA 3 of `ROUTE_LEAD.md` §3.1.**  Heath-Brown's zero-free region theorems
(Theorems 1–3), his Tables 8–10, Lemma 10.3, the §14 rows and the
Deuring–Heilbronn repulsion, uniformly in `q ≥ q₀(lamS)`. -/
def ZeroFreeCert : Prop := ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
  (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), IsMin1WideAt 10 χ₁ ρ₁ →
  Z1 χ₁ ρ₁ ∧ Z2 χ₁ ρ₁ ∧ Z3 χ₁ ρ₁ ∧ Z4 χ₁ ρ₁ ∧ Z5 χ₁ ρ₁ lamS

/-- The same clauses for the **off-axis** pairs of the round-2 numbering (`1 < |Im ρ₁| ≤ 50`),
which the local engine of HB §§6–10 cannot reach (its windows have height `4|γ₁| + δ`).  This is
the single extra input of the round-2 assembly; see `HBProps.HBOffAxis`. -/
def ZeroFreeCertOffAxis : Prop := ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
  ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    LinnikContract2.IsMin1 χ₁ ρ₁ → 1 < |ρ₁.im| →
    Z1 χ₁ ρ₁ ∧ Z2 χ₁ ρ₁ ∧ Z3 χ₁ ρ₁ ∧ Z4 χ₁ ρ₁ ∧ Z5 χ₁ ρ₁ lamS

/-- **AREA 3** as in the contract: with `Area1` (Burgess) as hypothesis. -/
def Area3 (Area1 : Prop) : Prop := Area1 → ZeroFreeCert

end Work.ZeroFreeTables
