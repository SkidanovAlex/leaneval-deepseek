/-
  WilG4c / Pullback — affine `x`-pullbacks of families, the shapes used by BNZ §5.4.

  BNZ §5.4 reduces `PYLip` to `PYLipDef` by

  1. choosing curves `γ_{i,α}` with the near-maximiser property,
  2. applying Corollary 19 to the tuple of curves and mixed derivatives, giving affine charts
     `x = α(l) + β(l)·t` (`Φ_η(λ,t,y) = (λ, α(l) + β(l)t, y)`) that cover the `x`-interval,
  3. pulling back `F` along each `Φ_η`, and
  4. checking that each pullback satisfies `PYLipDef`, so that `hP2` applies to it.

  The *elementary* half of step 4 is that the pullback still has unit `y`-derivatives
  (`YBound`), is `1`-Lipschitz (`LipOnCube`), and that its mixed derivatives are the
  corresponding mixed derivatives of `F` at `(α l + β l · t, tail t)` — the identity (46)–(47)
  of the paper, where `φ'' = 0` is what makes the affine chart crucial.  This file fixes that
  vocabulary; the jet-norm bookkeeping lives in `Engine.lean`.
-/
import Mathlib
import Submission.Work.WilG4c.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- The family `F` pulled back along the affine `x`-chart `x = α l + β l * t 0`, with the
remaining coordinates unchanged: `pullX F α β i l t = F i l (α l + β l · t 0, tail t)`. -/
def pullX {k p n : ℕ} (F : Family k p (n + 1)) (α β : (Fin p → ℝ) → ℝ) : Family k p (n + 1) :=
  fun i l t => F i l (pt (α l + β l * t 0) (Fin.tail t))

@[simp] theorem pullX_apply {k p n : ℕ} (F : Family k p (n + 1)) (α β : (Fin p → ℝ) → ℝ)
    (i : Fin k) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) :
    pullX F α β i l t = F i l (pt (α l + β l * t 0) (Fin.tail t)) := rfl

/-- The slice of the pullback at fixed first coordinate `s` is the slice of `F` at
`α l + β l · s`, composed with the projection to the remaining coordinates. -/
theorem slice_pullX {k p n : ℕ} (F : Family k p (n + 1)) (α β : (Fin p → ℝ) → ℝ) (i : Fin k)
    (l : Fin p → ℝ) (s : ℝ) :
    slice (pullX F α β i l) s = fun y : Fin n → ℝ => F i l (pt (α l + β l * s) y) := by
  funext y
  simp only [slice, pullX, pt_zero, tail_pt]

/-- The chart point `(α l + β l · t 0, tail t)` of `ℝ^{n+1}`.  This is the point map of the
affine `x`-chart, in `Fin (n+1)` coordinates. -/
def chartPt {p n : ℕ} (α β : (Fin p → ℝ) → ℝ) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  pt (α l + β l * t 0) (Fin.tail t)

theorem pullX_eq {k p n : ℕ} (F : Family k p (n + 1)) (α β : (Fin p → ℝ) → ℝ) (i : Fin k)
    (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) :
    pullX F α β i l t = F i l (chartPt α β l t) := rfl

theorem chartPt_zero {p n : ℕ} (α β : (Fin p → ℝ) → ℝ) (l : Fin p → ℝ) (t : Fin (n + 1) → ℝ) :
    chartPt α β l t 0 = α l + β l * t 0 :=
  pt_zero _ _

theorem chartPt_succ {p n : ℕ} (α β : (Fin p → ℝ) → ℝ) (l : Fin p → ℝ)
    (t : Fin (n + 1) → ℝ) (j : Fin n) : chartPt α β l t j.succ = t j.succ :=
  pt_succ _ _ j

/-- On the cube, the chart point stays in the cube when `0 ≤ α l`, `0 ≤ β l ≤ 1` and
`α l + β l ≤ 1`. -/
theorem chartPt_mem_openCube {p n : ℕ} {α β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ}
    (hα : 0 ≤ α l) (hβ : 0 < β l) (hαβ : α l + β l ≤ 1)
    {t : Fin (n + 1) → ℝ} (ht : t ∈ openCube (n + 1)) : chartPt α β l t ∈ openCube (n + 1) := by
  intro j
  induction j using Fin.cases with
  | zero =>
      rw [chartPt_zero]
      have ht0 : t 0 ∈ Set.Ioo (0 : ℝ) 1 := ht 0
      constructor
      · exact add_pos_of_nonneg_of_pos hα (mul_pos hβ ht0.1)
      · have h1 : β l * t 0 < β l := by
          simpa using mul_lt_mul_of_pos_left ht0.2 hβ
        linarith
  | succ j => rw [chartPt_succ]; exact ht j.succ

end Work.WilkG4c
