/-
# LinnikContract2 — Defs.lean  (**ROUND 2 FINAL, FROZEN**; fixes the height range of `λ₁`)

Round 2 of the Linnik `L = 5.5` contract.  This module is the **revised edition** of
`Submission/Work/LinnikContract/Defs.lean`.  Everything is unchanged *except* the height
range over which the minimising zero `ρ₁` (and hence `λ₁ = λ(ρ₁)`) is defined.

## The defect of round 1

Round 1 defined

    IsMin1 χ₁ ρ₁  :=  IsZ χ₁ ρ₁ ∧ ∀ χ u, IsZ χ u → λ(ρ₁) ≤ λ(u),

i.e. `λ₁` was the minimum of `λ` over the *working region* `IsZ = {|Im| ≤ 1}` only.  Two
independent diagnoses (`../reports/lemma-LinnikAreas_area4.md` and
`Submission/Work/ZeroFreeTables/API.lean`, `dev/README.md`) showed that Heath-Brown's `λ₁`
is *not* that number:

* **HB §6, (6.1)–(6.2).**  HB numbers the zeros of the rectangle
  `R = {s : 1 - (log log 𝓛)/(3𝓛) ≤ σ ≤ 1, |t| ≤ 𝓛}` (`𝓛 = log q`) by decreasing `Re`, and
  `λ₁ = λ(ρ₁)` is the minimum of `λ` over that rectangle.  Every zero `ρ` of any
  `L(s,χ)`, `χ (mod q)`, satisfies
  `Re ρ ≤ Re ρ₁` **or** `|Im ρ| ≥ 10𝓛`  (Lemma 6.1 gives the zero-free strip
  `𝓛 < |t| ≤ 10𝓛`), equivalently `|Im ρ| ≥ 10𝓛` or `λ(ρ) ≥ λ₁`.
* **HB §12, p. 75.**  "It follows from the conventions of §6 that all zeros `ρ`, of any
  `L`-function to modulus `q`, satisfy either `|γ| ≥ 10` or `β ≤ 1 − 𝓛⁻¹λ₁`."  This is the
  form in which `λ₁` is *used*: the proof of HB Lemma 12.1 applies Lemma 5.2 at
  `s = β₁ + i(γ⁽ʲ⁾−γ⁽ᵏ⁾)` with `|Im s| ≤ 2`, and every zero `u` in Lemma 5.2's window
  `|Im s − Im u| ≤ δ`, `δ ∈ (0,1)`, must satisfy `λ(u) ≥ λ₁` so that its term can be dropped
  by Condition 2 (`Re F(z) ≥ 0` for `Re z ≥ 0`).  The same window (`|Im u| ≤ 3 + δ`) is
  what the `P₃` engine of HB §§6–10 drops `λ₁`-terms with (`IsMin1Wide`/`HBWideMin` of
  `ZeroFreeTables/API.lean`).
* **HB §14.**  The numbering (14.1) of §14/§15 and the special treatment of `ρ₁`
  (`|F₂((1-ρ₁)𝓛)|` is a term of the box sum) require `ρ₁` to lie in the *working region*
  `|γ| ≤ 1`; in the §14 branch (`λ₁ < 0.348`) this follows from HB Lemma 9.5/theorem 1
  (`ρ₁` is real).

So round 1's `IsMin1` is simultaneously *too weak* (`λ₁` must control heights up to `10`)
and, as far as the working region is concerned, correctly narrow (`ρ₁` must lie in
`|γ| ≤ 1`).

## The round-2 definitions

We introduce the family, indexed by a **height** `H`,

    IsZH  H χ ρ  :=  χ ≠ 1 ∧ zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ H                     (HB's §6 region)
    IsMin1H H χ₁ ρ₁ := IsZH H χ₁ ρ₁ ∧ ∀ χ u, IsZH H χ u → λ(ρ₁) ≤ λ(u)

and **freeze the height** `H = 50`:

    IsZW  := IsZH 50          -- the wide region
    IsMin1 := IsMin1H 50      -- λ₁ (round 2; the *fixed* minimality)
    IsMin1N := IsMin1H 1      -- round 1's (narrow) minimality, as the `H = 1` member

**Why `50` and not HB §12's literal `10`.**  HB §12 uses the height `10` only as the constant at
which he quotes the consequence of §6 ("either `|γ| ≥ 10` or `β ≤ 1 − 𝓛⁻¹λ₁`"); but his *local*
arguments compare `ρ₁` against zeros of a *taller* region: HB Lemma 9.1 works with windows of
height `21 + δ` and Lemma 9.5 with height `40 + δ` (the `P₃` engine of §§6–10).  Numbering `λ₁` at
height `10` therefore leaves the engine without the clause `λ(u) ≥ λ₁` for zeros with
`10 < |Im u| ≤ 40`.  Since a minimum over a *larger* set is *smaller*, freezing at `50 ≥ 40 + δ`
keeps every clause that only needs `λ ≥ λ₁` on `|Im| ≤ H` for `H ≤ 50` (`IsMin1.window`), and
`IsZW = IsZH 50` makes `(D2)`'s hypothesis available to the engines as well.  The existence
argument (`NumZero/exists_wideMin.lean`) is parametric in `H` and so is unaffected.

`IsMin1N` is *definitionally* round 1's `IsMin1` (`IsZH 1` unfolds to `IsZ`), so every
result proved against round 1 that only *projects* `IsMin1` (in particular all of
`Submission/Work/A7/`, `Submission/Work/LinnikAreas/A7/`, `ZeroFreeTables/`) remains
available — see `Submission.Work.LinnikContract2.Bridge`.

## The §6 numbering

Round 1's `IsMin1` (minimality over the working region) is `IsMin1N = IsMin1H 1`; round 2's is the
*wide* minimality `IsMin1 = IsMin1H 10` with no requirement on `ρ₁` beyond `|Im ρ₁| ≤ 10`.

The existence of the wide minimiser is **provable** and proved
(`Submission.Work.LinnikContract2.exists_wideMin`, `NumZero/exists_wideMin.lean`): the region
`{non-principal zeros with |Im| ≤ H}` is finite (zeros of the completed L-functions in the critical
strip with `|Im| ≤ H`), so `λ` attains its minimum.  Hence round 2 carries **no** extra input: the
numbered pair of HB §6 exists by a theorem of the development, and the areas are the paper's
statements with no added hypotheses.

What is *not* a consequence of the definitions (and was wrongly built into round 1's predicate) is
that this minimiser lies in the working region `|Im| ≤ 1`: in the branch `λ₁ < 0.348` HB derives it
from Lemma 9.5/Theorem 1 (`Z1`: the numbered zero is real, hence `|Im| = 0`).  In the branch
`λ₁ ≥ 0.348` nothing in the paper forces it, and the §§14–15 argument must then be run with the
numbered zero outside the working region (see `A7/Area7.lean` and the report).
-/
import Mathlib

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

/-- `λ(ρ) = (1 - Re ρ) log q`. -/
def lamOf (q : ℕ) (ρ : ℂ) : ℝ := (1 - ρ.re) * Real.log q

/-- multiplicity of `ρ` as a zero of `L(s,χ*)`, `χ*` the primitive character inducing `χ`
    (via the completed L-function, which is entire for `χ ≠ 1`; its zeros = the non-trivial zeros). -/
def zeroMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  analyticOrderNatAt (completedLFunction χ.primitiveCharacter) ρ

/-- HB's working region (unchanged from round 1): a zero of a non-principal `L(s,χ)` with
`|γ| ≤ 1`.  This is the region in which HB §11 defines `N(λ)`, in which HB §13's box
`1 - R/𝓛 ≤ β ≤ 1, |γ| ≤ R/𝓛` lives, and in which HB Theorems 1–3 are stated. -/
def IsZ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop :=
  χ ≠ 1 ∧ zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ 1

/-- HB's §6 region at height `H`: a zero of a non-principal `L(s,χ)` with `|γ| ≤ H`.
(HB's (6.1) takes `H = 𝓛 = log q` together with the cut `λ ≤ (log log 𝓛)/3`; since the
numbered zero `ρ₁` satisfies `λ₁ ≤ (log log 𝓛)/3`, restricting the minimum to the rectangle
does not change its value, so the plain height condition is the right notion.) -/
def IsZH {q : ℕ} [NeZero q] (H : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop :=
  χ ≠ 1 ∧ zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ H

/-- **HB's wide region** (`H = 50`, the frozen round-2 height — see the module docstring):
a zero of a non-principal `L(s,χ)` with `|γ| ≤ 50`. -/
abbrev IsZW {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop := IsZH 50 χ ρ

/-- **`λ₁` (round 2, corrected):** the *wide minimiser*.  `ρ₁` is a non-principal zero with
`|Im ρ₁| ≤ H` whose `λ` is minimal among **all** non-principal zeros with `|Im| ≤ H`; there is *no*
requirement that `ρ₁` lie in the working region.

`H = 1` recovers round 1's predicate (minimality over `|Im| ≤ 1`, which forces `ρ₁ ∈ IsZ`); `H = 50`
is the frozen round-2 choice (see the module docstring: HB's own §12 constant is `10`, but the
engines of §§6–10 compare against zeros up to height `40 + δ`).  In the branch `λ₁ < 0.348`, HB's Lemma 9.5/`Z1` concludes
that the minimiser is *real*, hence in the working region — this is how the working region re-enters
the §§14–15 argument, rather than by assumption. -/
def IsMin1H {q : ℕ} [NeZero q] (H : ℝ) (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  IsZH H χ₁ ρ₁ ∧ ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZH H χ u → lamOf q ρ₁ ≤ lamOf q u

/-- **ROUND-2 `IsMin1` (FROZEN).**  `λ₁ = λ(ρ₁)` is the minimum of `λ` over HB's §6/§12 region
`|Im| ≤ 50`.  The numbered zero is the *wide minimiser*; round 1's `IsMin1` (which additionally
required `ρ₁` to lie in `|Im| ≤ 1`) is kept as `IsMin1N`. -/
def IsMin1 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop := IsMin1H 50 χ₁ ρ₁

/-- **ROUND-1 `IsMin1`** as the `H = 1` member of the family: minimality over the working region
`|Im| ≤ 1` (which forces `ρ₁ ∈ IsZ`).  It is *definitionally* round 1's predicate, which is what
carries the round-1 development over (`Bridge.lean`); it is the hypothesis under which the §§14–15
numerics were derived. -/
def IsMin1N {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop := IsMin1H 1 χ₁ ρ₁

/-! ## The bounds of HB §6, §9, §10 (unchanged from round 1) -/

/-- HB's `λ₀ ≥ c`: every other zero of `χ₁` (and `ρ₁` itself if it is multiple) has `λ ≥ c`.
    When `χ₁` is real, `conj ρ₁` is excluded as well (HB §6, cases 1–3 for `ρ⁰`). -/
def Lam0Bound {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) (c : ℝ) : Prop :=
  (2 ≤ zeroMult χ₁ ρ₁ → c ≤ lamOf q ρ₁) ∧
  ∀ ρ, IsZ χ₁ ρ → ρ ≠ ρ₁ → (χ₁ ^ 2 = 1 → ρ ≠ starRingEnd ℂ ρ₁) → c ≤ lamOf q ρ

/-- HB's `λ₂ ≥ c`: all zeros of characters other than `χ₁, χ̄₁`. -/
def Lam2Bound {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (c : ℝ) : Prop :=
  ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → c ≤ lamOf q ρ

/-- HB's `λ₃ ≥ c`: all zeros outside at most two conjugate pairs `{χ₁^{±1}, χ₂^{±1}}`. -/
def Lam3Bound {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (c : ℝ) : Prop :=
  ∃ χ₂ : DirichletCharacter ℂ q, ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ →
    χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ → c ≤ lamOf q ρ

/-- `N(λ)` of HB §11: number of non-principal `χ` with a zero, `|γ| ≤ 1`, `λ(ρ) ≤ λ`.
This is HB's counting function of the *working region* and stays at height 1 in round 2. -/
def Ncount (q : ℕ) [NeZero q] (lam : ℝ) : ℕ :=
  (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => ∃ ρ, IsZ χ ρ ∧ lamOf q ρ ≤ lam)).card

/-- HB's `λ₀` of §11: `(1/3) log log log q`. -/
def lamMax (q : ℕ) : ℝ := Real.log (Real.log (Real.log q)) / 3

/-- `λ^{(χ)}`: least `λ` over zeros of `χ` with `|γ| ≤ 1` (`0` if there are none). -/
def lamChar {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  sInf {x | ∃ ρ, IsZ χ ρ ∧ lamOf q ρ = x}

/-- HB's density weight `w(λ) = λ / (e^{73λ/30} - e^{16λ/15})` (Lemma 11.1). -/
def wHB (x : ℝ) : ℝ := x / (Real.exp (73/30 * x) - Real.exp (16/15 * x))

/-- HB's test function `F₂(z) = ((1 - e^{-Kz})/z)^2`. -/
def F2 (K : ℝ) (z : ℂ) : ℂ := ((1 - Complex.exp (-(K:ℂ) * z)) / z) ^ 2

/-- HB's `F(z) = e^{-az}F₂(z)` with `a = L - 2K`. -/
def Hk (L K : ℝ) (z : ℂ) : ℂ := Complex.exp (-((L - 2*K : ℝ) : ℂ) * z) * F2 K z

/-- The per-character bound `B(λ)` of HB Lemma 13.3 (with `φ = 1/3`). -/
def Bfun (K lam : ℝ) : ℝ :=
  if lam = 0 then 1/(3*K) + 1
  else (1 - Real.exp (-2*K*lam))/(6*K^2*lam) + (2*K*lam - 1 + Real.exp (-2*K*lam))/(2*K^2*lam^2)

/-- HB's box `1 - R/𝓛 ≤ β, |γ| ≤ R/𝓛` (Lemma 13.2). -/
def InBox (q : ℕ) (R : ℝ) (ρ : ℂ) : Prop := lamOf q ρ ≤ R ∧ |ρ.im| * Real.log q ≤ R

/-- `Σ'_ρ H((1-ρ)𝓛)` for one character (with multiplicity). The support is finite. -/
def boxSum (q : ℕ) [NeZero q] (L K R : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ᶠ ρ : ℂ, if InBox q R ρ then (zeroMult χ ρ : ℂ) * Hk L K ((1 - ρ) * Real.log q) else 0

/-- `Σ'_ρ ‖F₂((1-ρ)𝓛)‖` for one character (with multiplicity). -/
def boxAbs (q : ℕ) [NeZero q] (K R : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑ᶠ ρ : ℂ, if InBox q R ρ then (zeroMult χ ρ : ℝ) * ‖F2 K ((1 - ρ) * Real.log q)‖ else 0

/-- a real zero of a real character with `λ ≤ lamS` (Siegel/exceptional zero). -/
def SiegelZero (q : ℕ) [NeZero q] (lamS : ℝ) : Prop :=
  ∃ χ : DirichletCharacter ℂ q, χ ≠ 1 ∧ χ ^ 2 = 1 ∧
    ∃ β : ℝ, β < 1 ∧ zeroMult χ (β : ℂ) ≠ 0 ∧ (1 - β) * Real.log q ≤ lamS

/-! ## Round-2 documentation lemmas (statement forms, no mathematical content) -/

/-- Round-2 `IsMin1` is the `H = 50` member of the `IsMin1H` family. -/
theorem IsMin1_iff_IsMin1H {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} :
    IsMin1 χ₁ ρ₁ ↔ IsMin1H 50 χ₁ ρ₁ := Iff.rfl

/-- Round-1's `IsMin1` is the `H = 1` member of the family. -/
theorem IsMin1N_iff_IsMin1H1 {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} :
    IsMin1N χ₁ ρ₁ ↔ IsMin1H 1 χ₁ ρ₁ := Iff.rfl

/-- `IsZH 1` is `IsZ` (the two unfold to the same proposition). -/
theorem IsZH_one_iff_IsZ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ} :
    IsZH 1 χ ρ ↔ IsZ χ ρ := Iff.rfl

end Work.LinnikContract2
