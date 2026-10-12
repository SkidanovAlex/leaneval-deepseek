import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.PerBoxNames
import Submission.Work.SlotWord.wSmall1Pair_support_left
import Submission.Work.SlotWord.wSmallPair_support_left
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.wSmallPairGlobalVanish` — the kernel-vanishing helpers, **lower**

Three elementary facts about the sliding kernels, moved out of
`Submission/Work/BoseB1Cube/cubeRowsWindowVanish.lean` into a module that does **not** import the
holder file `Submission/Work/BoseB1Cube/cubeSmallNArb12ExHolds.lean`:

* `wSmallPair_global_vanish` — a kernel vanishing on `B(u) × B(u)` vanishes identically, because
  `χ_{B(u)}` is supported in `B(u)` (`Work.SlotWord.chiSmallB_support_mem_dlBox`,
  `Work.SlotWord.wSmallPair_support_left`);
* `wSmall1Pair_global_vanish` — the same for the `g₀`-numerator;
* `w1MassB_eq_zero_of_vanish` — hence `w1MassB = ∬ wSmall1Pair = 0`.

Statements and proofs are verbatim copies of the three declarations in `cubeRowsWindowVanish.lean`
(same fully-qualified names), so every existing consumer of that file still resolves them.

**Why lower.**  The target declaration `Work.BoseB1Cube.cubeSmallNArb12ExHolds` lives in the holder
file and can only be filled by a proof *inside the holder's import cone*; a module that imports the
holder can never serve that purpose.  `cubeRowsWindowVanish` imports the holder only for the
definitions `Work.BoseB1Cube.CubeRowsOn`/`CubeCoreSet`, which now live in the lower module
`Submission/Work/BoseB1Cube/cubeRowsDefs.lean`; this module has no such need at all, so the thin-box
lemma `Work.BoseB1Cube.cubeRowsOn_of_thinBox` (which uses only `w1MassB_eq_zero_of_vanish` from
here) becomes holder-free as well.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1
  Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `1 ≤ M` at FS's `M = mValue`. -/
private lemma one_le_bM (v : E3 → ℝ) (μ : ℝ) : 1 ≤ Work.BoseFixB1.bM v μ := by
  have h : Work.BoseFixB1.bM v μ = Work.BoseBox.mValue := rfl
  rw [h]
  norm_num [Work.BoseBox.mValue]

/-- **A kernel vanishing on the box vanishes identically** (`wSmallPair`-form, arbitrary numerator):
the factor `χ_{B(u)}(x)` is supported in `bA`, and so is `χ_{B(u)}(y)`. -/
theorem wSmallPair_global_vanish {v : E3 → ℝ} {μ : ℝ} {u : E3} {ρ : E3 → ℝ}
    (hℓ : 0 < bSide v μ) (hd : 0 < bD v μ)
    (hvan : ∀ x y : E3, x ∈ bA v μ u → y ∈ bA v μ u →
      Submission.BoseGases.wSmallPair (bM v μ) (bSide v μ) (bD v μ) u ρ x y = 0) :
    ∀ x y : E3, Submission.BoseGases.wSmallPair (bM v μ) (bSide v μ) (bD v μ) u ρ x y = 0 := by
  intro x y
  by_cases hx : x ∈ bA v μ u
  · by_cases hy : y ∈ bA v μ u
    · exact hvan x y hx hy
    · have hy0 : Submission.BoseGases.chiSmallB (bM v μ) (bSide v μ) (bD v μ) u y = 0 := by
        by_contra hne
        exact hy (Work.SlotWord.chiSmallB_support_mem_dlBox (one_le_bM v μ) hℓ hd hne)
      simp only [Submission.BoseGases.wSmallPair, hy0, mul_zero]
  · exact Work.SlotWord.wSmallPair_support_left (one_le_bM v μ) hℓ hd u ρ hx y

/-- **A kernel vanishing on the box vanishes identically** (`wSmall1Pair`-form). -/
theorem wSmall1Pair_global_vanish {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {u : E3}
    (hℓ : 0 < bSide v μ) (hd : 0 < bD v μ)
    (hvan : ∀ x y : E3, x ∈ bA v μ u → y ∈ bA v μ u →
      Submission.BoseGases.wSmall1Pair h (bM v μ) (bSide v μ) (bD v μ) u x y = 0) :
    ∀ x y : E3, Submission.BoseGases.wSmall1Pair h (bM v μ) (bSide v μ) (bD v μ) u x y = 0 :=
  wSmallPair_global_vanish (ρ := Submission.BoseGases.g0 v h) hℓ hd hvan

/-- **The kernel mass vanishes** when `wSmall1Pair` vanishes identically. -/
theorem w1MassB_eq_zero_of_vanish {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {u : E3}
    (hw1 : ∀ x y : E3,
      Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u x y = 0) :
    Work.BoseFixB1.w1MassB h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bD v μ) u = 0 := by
  rw [Work.BoseFixB1.w1MassB]
  have hfun : (fun x : E3 => ∫ y : E3,
      Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u x y)
      = fun _ : E3 => (0 : ℝ) := by
    funext x
    rw [show (fun y : E3 =>
        Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u x y)
        = fun _ : E3 => (0 : ℝ) from funext (fun y => hw1 x y)]
    simp
  rw [hfun]
  simp

end Work.BoseB1Cube
