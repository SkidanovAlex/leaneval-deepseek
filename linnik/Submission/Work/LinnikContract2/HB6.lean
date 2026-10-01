/-
# LinnikContract2 — HB6.lean

**HB §6 (6.1)–(6.2) formalised, and its relation to the round-2 `IsMin1`.**

HB's §6 numbers the zeros of the rectangle

    R = {s : 1 − (log log 𝓛)/(3𝓛) ≤ σ ≤ 1, |t| ≤ 𝓛}          (6.1)

(`𝓛 = log q`) by decreasing `Re`, so that `λ₁ = λ(ρ₁) = (1 − Re ρ₁)𝓛` is the *minimum* of `λ`
over `R`.  Since the last cut is `λ(ρ) ≤ (log log 𝓛)/3`, the minimum over `R` is the minimum over

    {non-principal zeros ρ : |Im ρ| ≤ 𝓛, λ(ρ) ≤ (log log 𝓛)/3}.

`IsZRect q H` below is that region at height `H`, and `IsMin1Rect H` is HB's numbering.
The theorem `wide_min_of_rect` then shows, with no further input, that a §6 minimal zero
satisfies the round-2 minimality clause at *every* height `H₀ ≤ H`: any non-principal zero `u`
with `|Im u| ≤ H₀` either lies in `R` (then `λ(u) ≥ λ(ρ₁)` by minimality) or has
`λ(u) > (log log 𝓛)/3 ≥ λ(ρ₁)` (the latter because `ρ₁ ∈ R`).  This is the content of HB §12's
"either `|γ| ≥ 10` or `β ≤ 1 − 𝓛⁻¹λ₁`", in the parametric form the engines of §§6–10 need
(the frozen round-2 height is `50`, see `Defs.lean`).

Hence the *only* part of HB's §6 convention that round 2 carries as an input is that the
numbered zero `ρ₁` lies in the working region `|Im| ≤ 1` (HB (14.1)): `isMin1_of_isMin1Rect_of_isZ`
combines the two.  The existence of the §6 minimiser itself is provable
(`NumZero.exists_wideMin`, `NumZero.exists_min1Rect_of`).
-/
import Submission.Work.LinnikContract2.Defs
import Submission.Work.LinnikContract2.API

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

variable {q : ℕ} [NeZero q]

/-- **HB's rectangle (6.1) at height `H`:** a non-principal zero with `|Im ρ| ≤ H` and
`λ(ρ) ≤ (log log H)/3` (the latter is `β ≥ 1 − (log log 𝓛)/(3𝓛)` in the paper's notation). -/
def IsZRect (q : ℕ) [NeZero q] (H : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) : Prop :=
  χ ≠ 1 ∧ zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ H ∧ lamOf q ρ ≤ Real.log (Real.log H) / 3

/-- **HB's §6 numbering (6.1)–(6.2):** `ρ₁` is a zero of the rectangle of minimal `λ`. -/
def IsMin1Rect {q : ℕ} [NeZero q] (H : ℝ) (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  IsZRect q H χ₁ ρ₁ ∧
    ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZRect q H χ u → lamOf q ρ₁ ≤ lamOf q u

/-- A rectangle zero is a wide-region zero once the rectangle is at least as tall. -/
theorem IsZRect.toIsZH {H H' : ℝ} (hHH : H ≤ H') {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : IsZRect q H χ ρ) : IsZH H' χ ρ :=
  ⟨h.1, h.2.1, h.2.2.1.trans hHH⟩

/-- **HB §6 ⟹ HB §12 (parametric in the target height).**  If `ρ₁` is the zero of HB's
rectangle `(6.1)` of minimal `λ`, then `λ(ρ₁)` is minimal among *all* non-principal zeros of
height `≤ H₀`, provided `H₀ ≤ H`.  (Proof: a zero `u` with `|Im u| ≤ H₀ ≤ H` either satisfies
`λ(u) ≤ (log log H)/3`, hence lies in the rectangle and `λ(u) ≥ λ(ρ₁)`; or
`λ(u) > (log log H)/3 ≥ λ(ρ₁)`, the latter because `ρ₁` is in the rectangle.) -/
theorem wide_min_of_rect {H H₀ : ℝ} (hH : H₀ ≤ H) {χ₁ : DirichletCharacter ℂ q} {ρ₁ : ℂ}
    (h : IsMin1Rect H χ₁ ρ₁) :
    ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), IsZH H₀ χ u → lamOf q ρ₁ ≤ lamOf q u := by
  intro χ u hu
  by_cases hcut : lamOf q u ≤ Real.log (Real.log H) / 3
  · exact h.2 χ u ⟨hu.1, hu.2.1, hu.2.2.trans hH, hcut⟩
  · exact le_trans h.1.2.2.2 (le_of_lt (lt_of_not_ge hcut))

/-- **HB §6 ⟹ round-2 `IsMin1`.**  If the §6 numbered zero has `|Im| ≤ 50` (which it need not
have in (6.1), where the height is `𝓛`), then it satisfies round-2 `IsMin1`: besides its region
membership, `λ₁` dominates every zero of height `≤ 50`, which is HB §12's "either `|γ| ≥ 10` or
`β ≤ 1 − 𝓛⁻¹λ₁`" in the parametric form.

When the (6.1) minimiser lies *above* height `50`, the conclusion is still that it dominates the
height-`50` region — and since that region is inhabited and its zeros are finite, a height-`50`
minimiser exists with `λ = λ(ρ₁)` (`area0`); that is the pair round 2 uses. -/
theorem isMin1_of_isMin1Rect {H : ℝ} (hH : 50 ≤ H) {χ₁ : DirichletCharacter ℂ q}
    {ρ₁ : ℂ} (h : IsMin1Rect H χ₁ ρ₁) (him : |ρ₁.im| ≤ 50) : IsMin1 χ₁ ρ₁ :=
  ⟨⟨h.1.1, h.1.2.1, him⟩, wide_min_of_rect hH h⟩

/-- HB (14.1) additionally asks that the numbered zero lie in the working region; in the branch
`λ₁ < 0.348` this follows from `Z1` (`ρ₁` is real).  Round 2 does *not* assume it. -/
theorem isMin1_of_isMin1Rect_of_isZ {H : ℝ} (hH : 50 ≤ H) {χ₁ : DirichletCharacter ℂ q}
    {ρ₁ : ℂ} (h : IsMin1Rect H χ₁ ρ₁) (him : |ρ₁.im| ≤ 50) (hZ : IsZ χ₁ ρ₁) :
    IsMin1 χ₁ ρ₁ ∧ IsZ χ₁ ρ₁ :=
  ⟨isMin1_of_isMin1Rect hH h him, hZ⟩

/-- The rectangle at height `𝓛 = log q` is the paper's `(6.1)`: the height `𝓛` and the cut
`λ ≤ (log log 𝓛)/3`.  (This is a re-statement for documentation; `IsZRect` is already parametric
in the height.) -/
theorem IsZRect_log_eq {χ : DirichletCharacter ℂ q} {ρ : ℂ} :
    IsZRect q (Real.log q) χ ρ ↔
      (χ ≠ 1 ∧ zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ Real.log q ∧
        lamOf q ρ ≤ Real.log (Real.log (Real.log q)) / 3) := Iff.rfl

end Work.LinnikContract2
