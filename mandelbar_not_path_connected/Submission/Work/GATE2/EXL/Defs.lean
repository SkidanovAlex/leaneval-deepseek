/-
# GATE2 / EXL — the vocabulary of the `ρ`-max construction of the exit loop

The lead's design (`Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §4) makes condition (W) of
`Work.GATE2.ExitLoop` *structural* by choosing the leak centre at a near-maximum of the
`1`-periodic quantity

    ρ w := log (green c₀ (fl.Ψ w)) / log 1024 − Re w .

`ρ` is invariant under the unit translation `w ↦ w + 1`: the flower's `Ψ_shift`
(`fl.Ψ (w+1) = F₀ (fl.Ψ w)`) and the Green functional equation `G_c (F_c z) = 1024 G_c z`
(`green_F` below, from `Work.ParamRays.greenFun_orbit` with `F_c = (T_c)^10`) give
`G(Ψ (w+1)) = 1024 G(Ψ w)`, hence `hExp (w+1) = hExp w + 1` and `ρ (w+1) = ρ w`.

The region in which the design loop is confined is the `ℤ`-invariant **Stolz sector**

    S_κ := {w | Re w < −R, fl.Ψ w ∉ K c₀, |deviation (varphiCrit c₀) α₁ (fl.Ψ w)| ≤ κ · G(fl.Ψ w)}.

This module fixes that vocabulary and its first invariances; the construction of the loop itself
is the lemma `Work.GATE2.EXL.exitLoop_exists`.
-/
import Submission.Work.GATE2.ExitPathInputs
import Submission.Work.PARIMPL.All
import Submission.Work.ELRig.All
import Submission.Work.ELNest.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-! ## The Green functional equation under `F_c = (T_c)^10` -/

/-- The Green function of the `n`-th iterate of the antiholomorphic quadratic: `T_c` doubles the
Green function (`Work.ParamRays.greenFun_orbit` at the orbit `(T_c)^[n]`). -/
theorem green_iterate (c z : ℂ) (n : ℕ) :
    Work.Bottcher.green c ((Tantibar c)^[n] z) = (2 : ℝ) ^ n * Work.Bottcher.green c z := by
  rw [Work.Bottcher.CritBasic.green_eq, Work.Bottcher.CritBasic.green_eq]
  simpa [Work.ParamRays.orbit] using Work.ParamRays.greenFun_orbit c z n

/-- **The Green functional equation of the high return map** `F_c = (T_c)^10`:
`G_c (F_c z) = 1024 · G_c z`. -/
theorem green_F (c z : ℂ) :
    Work.Bottcher.green c (Work.EL.F c z) = 1024 * Work.Bottcher.green c z := by
  rw [Work.EL.F_eq_tantibar, green_iterate]
  norm_num

/-! ## `hExp` and `ρ` -/

/-- The **Écalle-height of `w`**: `h w = log G(Ψ w) / log 1024`, i.e. `G(Ψ w) = 1024 ^ (h w)`.
Under the unit shift `h` increases by `1` (`hExp_add_one`). -/
noncomputable def hExp {c₀ : ℂ} {z₁ : ℂ} (fl : Work.EL.ParabolicFlower (Work.EL.F c₀)
    ((Tantibar c₀)^[5]) z₁) (w : ℂ) : ℝ :=
  Real.log (Work.Bottcher.green c₀ (fl.Ψ w)) / Real.log 1024

/-- The **`ρ`-invariant**: `h − Re`.  This is the quantity maximised by the leak centre; it is
`1`-periodic (`rho_add_one`). -/
noncomputable def rho {c₀ : ℂ} {z₁ : ℂ} (fl : Work.EL.ParabolicFlower (Work.EL.F c₀)
    ((Tantibar c₀)^[5]) z₁) (w : ℂ) : ℝ := hExp fl w - w.re

theorem hExp_def {c₀ : ℂ} {z₁ : ℂ} (fl : Work.EL.ParabolicFlower (Work.EL.F c₀)
    ((Tantibar c₀)^[5]) z₁) (w : ℂ) :
    hExp fl w = Real.log (Work.Bottcher.green c₀ (fl.Ψ w)) / Real.log 1024 := rfl

theorem rho_def {c₀ : ℂ} {z₁ : ℂ} (fl : Work.EL.ParabolicFlower (Work.EL.F c₀)
    ((Tantibar c₀)^[5]) z₁) (w : ℂ) : rho fl w = hExp fl w - w.re := rfl

theorem log_1024_pos : 0 < Real.log (1024 : ℝ) := Real.log_pos (by norm_num)

theorem log_1024_ne : Real.log (1024 : ℝ) ≠ 0 := ne_of_gt log_1024_pos

/-- **`hExp` is shifted by `1` under the unit translation** (on the escaping side, where the Green
function is positive). -/
theorem hExp_add_one {c₀ : ℂ} {z₁ : ℂ} (fl : Work.EL.ParabolicFlower (Work.EL.F c₀)
    ((Tantibar c₀)^[5]) z₁) {w : ℂ} (hK : fl.Ψ w ∉ Work.EL.K c₀) :
    hExp fl (w + 1) = hExp fl w + 1 := by
  have hshift : fl.Ψ (w + 1) = Work.EL.F c₀ (fl.Ψ w) := fl.Ψ_shift w
  have hpos : 0 < Work.Bottcher.green c₀ (fl.Ψ w) := Work.PARIMPL.green_pos_of_notMem_K hK
  have hg : Work.Bottcher.green c₀ (fl.Ψ (w + 1)) = 1024 * Work.Bottcher.green c₀ (fl.Ψ w) := by
    rw [hshift, green_F]
  rw [hExp_def, hExp_def, hg,
    Real.log_mul (by norm_num : (1024 : ℝ) ≠ 0) (ne_of_gt hpos), add_div,
    div_self log_1024_ne]
  ring

/-- **`ρ` is `1`-periodic** (on the escaping side). -/
theorem rho_add_one {c₀ : ℂ} {z₁ : ℂ} (fl : Work.EL.ParabolicFlower (Work.EL.F c₀)
    ((Tantibar c₀)^[5]) z₁) {w : ℂ} (hK : fl.Ψ w ∉ Work.EL.K c₀) :
    rho fl (w + 1) = rho fl w := by
  have h1 : hExp fl (w + 1) = hExp fl w + 1 := hExp_add_one fl hK
  rw [rho_def, rho_def, h1]
  simp only [Complex.add_re, Complex.one_re]
  ring

/-! ## The Stolz sector -/

/-- The **Stolz sector** `S_κ = {Re w < −R, Ψ w ∉ K c₀, |deviation| ≤ κ·G}` of the `α₁`-direction,
in the repelling coordinate.  It is the region of the `ρ`-max construction: the design loop from
`u−1` to `u` stays in it. -/
def stolz {c₀ : ℂ} {z₁ : ℂ} (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) z₁)
    (R κ : ℝ) : Set ℂ :=
  {w : ℂ | w.re < -R ∧ fl.Ψ w ∉ Work.EL.K c₀ ∧
    |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha1 (fl.Ψ w)|
      ≤ κ * Work.Bottcher.green c₀ (fl.Ψ w)}

theorem mem_stolz {c₀ : ℂ} {z₁ : ℂ} {fl : Work.EL.ParabolicFlower (Work.EL.F c₀)
    ((Tantibar c₀)^[5]) z₁} {R κ : ℝ} {w : ℂ} :
    w ∈ stolz fl R κ ↔ w.re < -R ∧ fl.Ψ w ∉ Work.EL.K c₀ ∧
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha1 (fl.Ψ w)|
        ≤ κ * Work.Bottcher.green c₀ (fl.Ψ w) := Iff.rfl

/-- Membership gives the escaping property (the point is off `K c₀`). -/
theorem stolz_offK {c₀ : ℂ} {z₁ : ℂ} {fl : Work.EL.ParabolicFlower (Work.EL.F c₀)
    ((Tantibar c₀)^[5]) z₁} {R κ : ℝ} {w : ℂ} (hw : w ∈ stolz fl R κ) :
    fl.Ψ w ∉ Work.EL.K c₀ := (mem_stolz.mp hw).2.1

/-- On the Stolz sector the Green function is positive. -/
theorem stolz_green_pos {c₀ : ℂ} {z₁ : ℂ} {fl : Work.EL.ParabolicFlower (Work.EL.F c₀)
    ((Tantibar c₀)^[5]) z₁} {R κ : ℝ} {w : ℂ} (hw : w ∈ stolz fl R κ) :
    0 < Work.Bottcher.green c₀ (fl.Ψ w) :=
  Work.PARIMPL.green_pos_of_notMem_K (stolz_offK hw)

end Work.GATE2.EXL
