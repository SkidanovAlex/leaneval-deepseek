/-
# `CCSharp/Base` — the `ClassC`-extraction helpers for the `ClassC`-level sharp `N`-difference

This module (owned by the `NDiffClassC` task) collects the elementary facts that the
`ClassC`-variants of the sharp `N`-difference machinery need, and nothing else.

## Context / blueprint

The target `Work.FTS.StrongEps.EpsRLX.NDiffClassC` is the `ClassC`-analogue of
`Work.FTS.GalFields.RHS.sharp_N_diff`: for `W₁, W₂` of class `C` and an elliptic operator `E`
constrained only by `hEll` (`EllPkgGo`/`EllPkgK` on `ClassC`),

```
Xn α (N α (F_*+W₁) (Φ_s+E W₁) − N α (F_*+W₂) (Φ_s+E W₂))
  ≤ K·(1 + |W₁|_{ℋ⁵} + |W₂|_{ℋ⁵})·|W₁−W₂|_{ℋ⁵}
```

together with the `SmoothOpen`- and `HkMem α 4`-clauses.  `sharp_N_diff` itself is unusable
(its hypotheses are `GalClass`, its `hEllSub` is an equality of *functions*), but its whole
development is: `ClassC α h` holds for `h = W₁ − W₂` (`EComparison.classC_sub`) and `hEll`
applies to `h`, so `EllPkgGo α Ce h (E h)` is available exactly as `hell h hh` was.

The plan (see `NDiffClassC.lean` for the assembly) is:

1. **`CCSharp.NDiffIdC`** — the pointwise identity on `Qd`
   `N α (F_*+W₁) (Φ_s+E W₁) − N α (F_*+W₂) (Φ_s+E W₂) = foldr (+) 0 (Sharp.termList α Φs E W₁ W₂ h)`,
   obtained from `Sharp.N_diff_eq_sum` with the single substitution
   `hEls : E h = E W₁ − E W₂` replaced by the *slot identity*
   `SlotR/U/V α h (E W₁ − E W₂) = SlotR/U/V α h (E h)` on the quadrant
   (`EComparison.slot_eq_of_source_quadrant`, with
   `EComparison.EllPkgCls_E_sub_of_theta` for the class membership of `E W₁ − E W₂`), and with
   `L12FK_add_ge0` replaced by `SharpAux.L12_sub_ge0` / `RHS.L12_sub_eq_of_smoothOpen`.
2. **`CCSharp.WlInfTermsBoundC`** / **`CCSharp.HonestTermsBoundC`** — the twenty term bounds of
   `SharpAux.WlInfTermsBound` / `SharpAux.HonestTermsBound` with `GalClass α g, g', h` replaced
   by `ClassC α W₁, ClassC α W₂` (and `h := W₁ − W₂`, `hell h hh := hEll h (classC_sub …)`).
   The adaptation is mechanical; the substitutions are listed in the docstring of this file.
3. the assembly (by `sharp_N_diff_asm`'s tail: `termList` + `HkNorm_listFoldr_le`,
   `HkMem_listFoldr`, `smoothOpen_listFoldr`, `HkSq_congr_open`, `HkMem_congr_Q0`).

### The exact substitutions used to port `GalClass` into `ClassC`

For `hW : ClassC α W`:

* `smoothOpen_of_smoothQuad hW.reg.1`      ↦ `hW.reg`   (i.e. `ClassC.reg`);
* `galClass_HkMem5 hW`                      ↦ `OpenPkg.HkMem_mono_open hW.reg 5 (by norm_num) hW.mem`;
* `galClass_HkMem4 hW`                      ↦ `OpenPkg.HkMem_mono_open hW.reg 4 (by norm_num) hW.mem`;
* `galClass_HQo4 hW`                        ↦ `⟨hW.reg, HkMem_mono_open hW.reg 4 (by norm_num) hW.mem⟩`;
* `RegQ_mono (by norm_num) hW.reg` + `HkMem_dth_of_RegQ_ge`/`HkMem_Dz_quad`
                                             ↦ `IPGen.HkMem_Dth_le (by linarith) hW.reg hW5`
                                               and `IPGen.HkMem_Dz_le hW.reg hW5`;
* `hW.l12 : L12 W 0 = 0`                    ↦ for `h := W₁ − W₂` use `CCSharp.sub_L12_zero`;
* `AuxFK.smoothOpen_FK_radial … hW.reg.1 …` ↦ `ClassCRHS.HkMemXnNAux.smoothOpen_FKw_of_classC hW`;
* `hell h hh`                               ↦ `hEll (fun z θ => W₁ z θ - W₂ z θ) (EComparison.classC_sub hW₁ hW₂)`.

Nothing here is `sorry`-free-critical: this file contains no `sorry`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.StrongEps.EComparison.E_slots_diff_le
import Submission.Work.FTS.StrongEps.EComparison.EllPkgCls_E_sub
import Submission.Work.FTS.GalFields.RHS.sharp_N_diff
import Submission.Work.FTS.GalFields.RHS.L12f_eq_sub_add
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.CCSharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Extraction from `ClassC` -/

/-- `ClassC` gives `SmoothOpen`. -/
theorem cSmooth {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W) :
    Work.FTS.EllipticEst.SmoothOpen W := hW.reg

/-- From `ClassC` (`HkMem α 7`) to any order `≤ 7`. -/
theorem cMem {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W) {k : ℕ} (hk : k ≤ 7) :
    Work.Spaces.HkMem α k W :=
  Work.FTS.OpenPkg.HkMem_mono_open hW.reg k hk hW.mem

/-- `ClassC` gives `HQo α 4`. -/
theorem cHQo {α : ℝ} {W : Fn} (hW : Work.FTS.ClassC.ClassC α W) :
    Work.FTS.VocabO.HQo α 4 W :=
  ⟨hW.reg, cMem hW (by norm_num)⟩

/-- `|W|_{ℋ⁴} ≤ |W|_{ℋ⁵}` for `W` of class `C`. -/
theorem cXn_le_Xn5 {α : ℝ} (hα : 0 < α) {W : Fn} (hW : Work.FTS.ClassC.ClassC α W) :
    Work.FTS.Nonlin.Xn α W ≤ Work.FTS.GalFields.Xn5 α W :=
  Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 5) (k' := 4) (by norm_num) (cMem hW (by norm_num))

/-! ## The difference of two class elements -/

/-- The difference of two class-`C` elements is again of class `C`. -/
theorem sub_classC {α : ℝ} {W₁ W₂ : Fn}
    (h₁ : Work.FTS.ClassC.ClassC α W₁) (h₂ : Work.FTS.ClassC.ClassC α W₂) :
    Work.FTS.ClassC.ClassC α (fun z θ => W₁ z θ - W₂ z θ) :=
  Work.FTS.StrongEps.EComparison.classC_sub h₁ h₂

/-- `L₁₂` of a difference of two class-`C` elements at `z = 0` vanishes: additivity of `L₁₂`
(`Sharp.L12_sub_ge0`, at `z = 0`) plus the class field `L12 W 0 = 0`. -/
theorem sub_L12_zero {α : ℝ} {W₁ W₂ : Fn}
    (h₁ : Work.FTS.ClassC.ClassC α W₁) (h₂ : Work.FTS.ClassC.ClassC α W₂) :
    Work.Construction.L12 (fun z θ => W₁ z θ - W₂ z θ) 0 = 0 := by
  have hd := sub_classC h₁ h₂
  have hsub := Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0 (d := fun z θ => W₁ z θ - W₂ z θ)
    h₁.reg h₂.reg hd.reg (cMem h₁ (by norm_num)) (cMem h₂ (by norm_num))
    (cMem hd (by norm_num)) (fun z θ => rfl) (le_refl 0)
  rw [h₁.l12, h₂.l12] at hsub
  linarith [hsub]

/-- The functions of the `ClassC`-level sharp development, gathered for convenience. -/
theorem sub_facts {α : ℝ} {W₁ W₂ : Fn}
    (h₁ : Work.FTS.ClassC.ClassC α W₁) (h₂ : Work.FTS.ClassC.ClassC α W₂) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => W₁ z θ - W₂ z θ) ∧
    Work.Spaces.HkMem α 5 (fun z θ => W₁ z θ - W₂ z θ) ∧
    Work.FTS.VocabO.HQo α 4 (fun z θ => W₁ z θ - W₂ z θ) ∧
    Work.Construction.L12 (fun z θ => W₁ z θ - W₂ z θ) 0 = 0 := by
  have h := sub_classC h₁ h₂
  exact ⟨h.reg, cMem h (by norm_num), cHQo h, sub_L12_zero h₁ h₂⟩

end Work.FTS.StrongEps.EpsRLX.CCSharp
