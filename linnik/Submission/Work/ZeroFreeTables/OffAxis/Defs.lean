/-
# ZeroFreeTables/OffAxis/Defs

The vocabulary of the **off-axis route** (`OFFAXIS_ROUTE_LEAD.md` §3.0): HB's numbering at a
rectangle height `L`, the strip condition of HB Lemma 6.1, and the height-`H` versions of the
contract's three bounds.

Everything is stated in the round-1 vocabulary (`lamOf`, `zeroMult`) in which `Z1`–`Z5` live;
`IsZAt H χ ρ` is *definitionally* `Work.LinnikContract2.IsZH H χ ρ` (hence `IsZAt 1 = IsZ`),
and `IsRectMin 1` is the round-2 `IsMin1WideAt 10`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.LinnikContract2.API
import Submission.Work.LinnikContract2.NumZero.exists_wideMin

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## The region predicates -/

/-- A non-principal zero at height `≤ H` (definitionally `Work.LinnikContract2.IsZH H`; in
particular `IsZAt 1` is the working region `IsZ`). -/
def IsZAt {q : ℕ} [NeZero q] (H : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop :=
  χ ≠ 1 ∧ zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ H

/-- **HB §6 numbering at rectangle height `L` with room**: `ρ₁` lies at height `≤ L` and `λ₁` is
minimal over *all* non-principal zeros of height `≤ 10L` (every first-level window of
`OFFAXIS_ROUTE_LEAD.md` §2(b) fits in `9L + 3δ`). -/
def IsRectMin {q : ℕ} [NeZero q] (L : ℝ) (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  IsZAt L χ₁ ρ₁ ∧
    ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZAt (10 * L) χ u → lamOf q ρ₁ ≤ lamOf q u

/-- **HB (6.1) + Lemma 6.1 at height `L`**: `ρ₁` is minimal over height `≤ L`, and the strip
`(L, 10L]` carries no zero with `λ ≤ 2` (2 exceeds every constant the §§6–10 contradictions
assume, the largest being the `1.308` of `rows15`).  This is what second-level (β⁰- and
β₂-centred) arguments need. -/
def IsRectStrip {q : ℕ} [NeZero q] (L : ℝ) (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  IsZAt L χ₁ ρ₁ ∧
    (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZAt L χ u → lamOf q ρ₁ ≤ lamOf q u) ∧
    ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZAt (10 * L) χ u → L < |u.im| → 2 < lamOf q u

/-! ## The height-`H` versions of the contract's bounds -/

/-- Height-`H` `λ₀`-bound (`H = 1` gives `Lam0Bound`). -/
def Lam0BoundH {q : ℕ} [NeZero q] (H : ℝ) (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
    (c : ℝ) : Prop :=
  (2 ≤ zeroMult χ₁ ρ₁ → c ≤ lamOf q ρ₁) ∧
    ∀ ρ : ℂ, IsZAt H χ₁ ρ → ρ ≠ ρ₁ → (χ₁ ^ 2 = 1 → ρ ≠ starRingEnd ℂ ρ₁) → c ≤ lamOf q ρ

/-- Height-`H` `λ₂`-bound (`H = 1` gives `Lam2Bound`). -/
def Lam2BoundH {q : ℕ} [NeZero q] (H : ℝ) (χ₁ : DirichletCharacter ℂ q) (c : ℝ) : Prop :=
  ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZAt H χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → c ≤ lamOf q ρ

/-- Height-`H` `λ₃`-bound (`H = 1` gives `Lam3Bound`). -/
def Lam3BoundH {q : ℕ} [NeZero q] (H : ℝ) (χ₁ : DirichletCharacter ℂ q) (c : ℝ) : Prop :=
  ∃ χ₂ : DirichletCharacter ℂ q, ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZAt H χ ρ →
    χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ → c ≤ lamOf q ρ

/-! ## `IsZ` as a special case of `IsZAt` -/

theorem isZAt_of_isZ {q : ℕ} [NeZero q] {H : ℝ} (hH : 1 ≤ H)
    {χ : DirichletCharacter ℂ q} {ρ : ℂ} (h : IsZ χ ρ) : IsZAt H χ ρ :=
  ⟨h.1, h.2.1, h.2.2.trans hH⟩

theorem isZAt_one_iff {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ} :
    IsZAt 1 χ ρ ↔ IsZ χ ρ := Iff.rfl

theorem isZAt_mono {q : ℕ} [NeZero q] {H H' : ℝ} (hHH : H ≤ H')
    {χ : DirichletCharacter ℂ q} {ρ : ℂ} (h : IsZAt H χ ρ) : IsZAt H' χ ρ :=
  ⟨h.1, h.2.1, h.2.2.trans hHH⟩

/-! ## Restriction of the height-`H` bounds to the working region -/

theorem Lam0BoundH.toIsZ {q : ℕ} [NeZero q] {H : ℝ} (hH : 1 ≤ H)
    {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ} {c : ℝ} (h : Lam0BoundH H χ₁ ρ₁ c) :
    Lam0Bound χ₁ ρ₁ c :=
  ⟨h.1, fun ρ hZ hne hconj => h.2 ρ (isZAt_of_isZ hH hZ) hne hconj⟩

theorem Lam2BoundH.toIsZ {q : ℕ} [NeZero q] {H : ℝ} (hH : 1 ≤ H)
    {χ₁ : DirichletCharacter ℂ q} {c : ℝ} (h : Lam2BoundH H χ₁ c) :
    Lam2Bound χ₁ c :=
  fun χ ρ hZ h1 h2 => h χ ρ (isZAt_of_isZ hH hZ) h1 h2

theorem Lam3BoundH.toIsZ {q : ℕ} [NeZero q] {H : ℝ} (hH : 1 ≤ H)
    {χ₁ : DirichletCharacter ℂ q} {c : ℝ} (h : Lam3BoundH H χ₁ c) :
    Lam3Bound χ₁ c := by
  obtain ⟨χ₂, hχ₂⟩ := h
  exact ⟨χ₂, fun χ ρ hZ h1 h2 h3 h4 => hχ₂ χ ρ (isZAt_of_isZ hH hZ) h1 h2 h3 h4⟩

/-! ## The two analytic inputs of the off-axis assembly (`OFFAXIS_ROUTE_LEAD.md` §3.1)

These are the on-axis engine Propositions **restated at a rectangle height `L`**: each occurrence
of `IsMin1WideAt 10 χ₁ ρ₁` becomes `IsRectMin L χ₁ ρ₁` (or `IsRectStrip L` for the second-level,
`β⁰`- and `β₂`-centred arguments), and each `IsZ` in a *conclusion* becomes `IsZAt L`, uniformly
in `∀ L ≥ 1, ∃ q₀`.  At `L = 1` the height-`L` statement degenerates to the on-axis one, so nothing
is stated twice.
-/

/-- **AREA 3 at rectangle height `L`, complex case, first level.**

HB Lemma 9.5 (`λ₁ ≥ 0.348` for a non-real `ρ₁`), the off-axis `Z2` (`F` at `β₁` with the
`χ₀`-shifts `2γ₁`, `4γ₁` pole-free, giving `λ₁ ≥ 0.6074`), Tables 8/10/9/11 and Lemma 10.3, with
`IsRectMin L` supplying every window (all of them fit in `9L + 3δ`). -/
def RectCertC : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      348/1000 ≤ lamOf q ρ₁ ∧ Z2 χ₁ ρ₁ ∧ Z3 χ₁ ρ₁ ∧ Z4 χ₁ ρ₁

/-- **HB Theorems 2 and 3 at rectangle height `L`, all cases** (the real-real case included:
Lemmas 8.2/8.3 for `λ⁰`, Table 7 / Lemma 8.8 (or Lemma 9.4) for `λ₂`, Lemma 10.3 for `λ₃`). -/
def RectCertS : Prop :=
  ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    IsRectStrip L χ₁ ρ₁ →
      Lam0BoundH L χ₁ ρ₁ (695/1000) ∧ Lam2BoundH L χ₁ (701/1000) ∧
        Lam3BoundH L χ₁ (856/1000)

end Work.ZeroFreeTables
