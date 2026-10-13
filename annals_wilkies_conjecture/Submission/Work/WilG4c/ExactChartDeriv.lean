/-
  WilG4c / `ExactChartDeriv` — the two interface conversions between
  `Work.WilkG4c.ChartsExactCell` and the per-cell engines
  `Work.WilG4c.PiecePYLipOfChart` / `Work.WilG4c.PiecePYLipOfChartPw`.

  `ChartsExactCell` produces a chart `φ : ChartTuple p 1`, i.e. a tuple of functions of a point of
  the *one-dimensional* cube `Fin 1 → ℝ`.  The engines expect a *scalar* chart
  `φ : (Fin p → ℝ) → ℝ → ℝ`.  Moreover, the engines need the pointwise differentiability of that
  scalar chart and the bound `|φ'| ≤ 1`; both are *not* among the conjuncts of `ChartsExactCell`'s
  conclusion, but they follow at once from the conjunct about the tuple member that is the
  identity: for that member the composite `τ ↦ T i l (fun _ => φ 0 l (fun _ => τ))` **is**
  `τ ↦ φ 0 l (fun _ => τ)`.

  This file contains the two elementary conversions (`chartFun`, `chartFun_diff`), so that the
  §5.3 assembly can feed `ChartsExactCell`'s output to `PiecePYLipOfChartPw` without repeating
  them.  Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.StepLipPieces
import Submission.Work.WilkG4c.ChartsExactCell

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- The scalar chart underlying a `ChartTuple p 1`: `chartFun φ l τ = φ 0 l (fun _ => τ)`. -/
def chartFun {p : ℕ} (φ : Work.WilkG4c.ChartTuple p 1) : (Fin p → ℝ) → ℝ → ℝ :=
  fun l τ => φ 0 l (fun _ : Fin 1 => τ)

@[simp] theorem chartFun_apply {p : ℕ} (φ : Work.WilkG4c.ChartTuple p 1)
    (l : Fin p → ℝ) (τ : ℝ) : chartFun φ l τ = φ 0 l (fun _ : Fin 1 => τ) := rfl

/-- The `t`-slice of the pullback along `chartFun` is the `φ 0`-slice: `pieceFam` in the
`ChartTuple`-spelling. -/
theorem pieceFam_chartFun {k p n : ℕ} (G : Work.WilkG4c.Family k p (n + 1))
    (φ : Work.WilkG4c.ChartTuple p 1) (i : Fin k) (l : Fin p → ℝ)
    (z : Fin (n + 1) → ℝ) :
    Work.WilkG4c.pieceFam G (chartFun φ) i l z
      = G i l (Fin.cons ((φ 0 l) (fun _ : Fin 1 => z 0)) (Fin.tail z)) := rfl

/-- **The pointwise derivative of the `ChartsExactCell` chart.**  If the tuple member `T i` is the
identity `u ↦ u 0` and `ChartsExactCell`'s conjunct about `T i` holds for the chart `φ`, then the
scalar chart `chartFun φ l` is differentiable on `I` with `|deriv| ≤ 1`.  These are the `hφd` and
`hφb` inputs of `Work.WilG4c.PiecePYLipOfChartPw`. -/
theorem chartFun_diff {p k : ℕ} {Λ : Set (Fin p → ℝ)}
    (T : Fin k → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ) (i : Fin k)
    (hid : ∀ (l : Fin p → ℝ) (u : Fin 1 → ℝ), T i l u = u 0)
    (φ : Work.WilkG4c.ChartTuple p 1)
    (h : ∀ l ∈ Λ, ∀ τ ∈ Work.WilkG4c.I,
      DifferentiableAt ℝ (fun τ' : ℝ => T i l (fun _ : Fin 1 => φ 0 l (fun _ => τ'))) τ ∧
      |deriv (fun τ' : ℝ => T i l (fun _ : Fin 1 => φ 0 l (fun _ => τ'))) τ| ≤ 1) :
    ∀ l ∈ Λ, ∀ τ ∈ Work.WilkG4c.I,
      DifferentiableAt ℝ (chartFun φ l) τ ∧ |deriv (chartFun φ l) τ| ≤ 1 := by
  intro l hl τ hτ
  obtain ⟨hd, hb⟩ := h l hl τ hτ
  have hfun : (fun τ' : ℝ => T i l (fun _ : Fin 1 => φ 0 l (fun _ => τ')))
      = fun τ' : ℝ => φ 0 l (fun _ : Fin 1 => τ') := by
    funext τ'
    exact hid l (fun _ : Fin 1 => φ 0 l (fun _ => τ'))
  rw [hfun] at hd hb
  exact ⟨hd, hb⟩

end Work.WilG4c
