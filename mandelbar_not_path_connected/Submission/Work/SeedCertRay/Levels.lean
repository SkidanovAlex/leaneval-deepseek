import Mathlib
import Submission.Work.SeedCertRay.LvlFacts
import Submission.Work.SeedCertRay.stepOKB_sound
import Submission.Work.SeedCertRay.dirOKB_sound
import Submission.Work.SeedCertRay.petalDskB_sound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.SeedCertRay.Levels` — the per-level certificate facts (generated)

For every checked level `k` this module provides

* `hD1_lvl_k : ∀ (j : Fin 10) (i : Fin NC), DiskCover (Dd k (j+1) i) Xb (Dd (k+1) j i)`,
* `hHP_lvl_k : ∀ (j : Fin 10)`, the two half-plane inclusions of `(D2)`,
* `hQ_lvl_k` (for the ten petal levels): the `alpha_1`-column lies in the petal `Re w < -4`,

and the "for all `k ≤ ...`" forms `hD1At`, `hHPAt`, `hQAt` (a match on `k`).
-/
namespace Work.SeedCertRay

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

theorem mem_stepQs {j i : ℕ} (hj : j < 10) (hi : i < 6) : (j, i) ∈ stepQs := by
  interval_cases j <;> interval_cases i <;> decide

theorem mem_dirQs {j : ℕ} (hj : j < 10) : j ∈ dirQs := by
  interval_cases j <;> decide

theorem stepOK_0 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 0) (dsk 1) (crt 0) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 0) (dsk 1) (crt 0) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_0)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_1 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 1) (dsk 2) (crt 1) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 1) (dsk 2) (crt 1) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_1)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_2 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 2) (dsk 3) (crt 2) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 2) (dsk 3) (crt 2) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_2)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_3 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 3) (dsk 4) (crt 3) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 3) (dsk 4) (crt 3) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_3)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_4 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 4) (dsk 5) (crt 4) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 4) (dsk 5) (crt 4) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_4)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_5 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 5) (dsk 6) (crt 5) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 5) (dsk 6) (crt 5) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_5)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_6 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 6) (dsk 7) (crt 6) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 6) (dsk 7) (crt 6) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_6)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_7 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 7) (dsk 8) (crt 7) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 7) (dsk 8) (crt 7) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_7)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_8 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 8) (dsk 9) (crt 8) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 8) (dsk 9) (crt 8) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_8)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_9 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 9) (dsk 10) (crt 9) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 9) (dsk 10) (crt 9) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_9)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_10 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 10) (dsk 11) (crt 10) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 10) (dsk 11) (crt 10) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_10)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_11 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 11) (dsk 12) (crt 11) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 11) (dsk 12) (crt 11) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_11)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_12 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 12) (dsk 13) (crt 12) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 12) (dsk 13) (crt 12) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_12)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_13 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 13) (dsk 14) (crt 13) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 13) (dsk 14) (crt 13) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_13)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_14 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 14) (dsk 15) (crt 14) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 14) (dsk 15) (crt 14) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_14)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_15 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 15) (dsk 16) (crt 15) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 15) (dsk 16) (crt 15) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_15)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_16 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 16) (dsk 17) (crt 16) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 16) (dsk 17) (crt 16) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_16)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_17 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 17) (dsk 18) (crt 17) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 17) (dsk 18) (crt 17) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_17)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_18 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 18) (dsk 19) (crt 18) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 18) (dsk 19) (crt 18) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_18)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_19 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 19) (dsk 20) (crt 19) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 19) (dsk 20) (crt 19) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_19)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_20 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 20) (dsk 21) (crt 20) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 20) (dsk 21) (crt 20) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_20)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_21 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 21) (dsk 22) (crt 21) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 21) (dsk 22) (crt 21) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_21)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_22 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 22) (dsk 23) (crt 22) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 22) (dsk 23) (crt 22) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_22)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_23 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 23) (dsk 24) (crt 23) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 23) (dsk 24) (crt 23) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_23)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_24 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 24) (dsk 25) (crt 24) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 24) (dsk 25) (crt 24) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_24)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_25 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 25) (dsk 26) (crt 25) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 25) (dsk 26) (crt 25) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_25)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_26 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 26) (dsk 27) (crt 26) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 26) (dsk 27) (crt 26) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_26)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_27 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 27) (dsk 28) (crt 27) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 27) (dsk 28) (crt 27) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_27)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_28 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 28) (dsk 29) (crt 28) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 28) (dsk 29) (crt 28) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_28)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_29 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 29) (dsk 30) (crt 29) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 29) (dsk 30) (crt 29) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_29)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_30 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 30) (dsk 31) (crt 30) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 30) (dsk 31) (crt 30) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_30)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_31 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 31) (dsk 32) (crt 31) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 31) (dsk 32) (crt 31) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_31)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_32 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 32) (dsk 33) (crt 32) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 32) (dsk 33) (crt 32) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_32)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_33 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 33) (dsk 34) (crt 33) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 33) (dsk 34) (crt 33) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_33)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_34 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 34) (dsk 35) (crt 34) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 34) (dsk 35) (crt 34) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_34)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_35 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 35) (dsk 36) (crt 35) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 35) (dsk 36) (crt 35) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_35)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_36 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 36) (dsk 37) (crt 36) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 36) (dsk 37) (crt 36) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_36)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_37 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 37) (dsk 38) (crt 37) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 37) (dsk 38) (crt 37) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_37)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_38 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 38) (dsk 39) (crt 38) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 38) (dsk 39) (crt 38) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_38)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_39 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 39) (dsk 40) (crt 39) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 39) (dsk 40) (crt 39) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_39)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_40 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 40) (dsk 41) (crt 40) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 40) (dsk 41) (crt 40) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_40)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_41 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 41) (dsk 42) (crt 41) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 41) (dsk 42) (crt 41) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_41)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_42 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 42) (dsk 43) (crt 42) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 42) (dsk 43) (crt 42) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_42)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_43 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 43) (dsk 44) (crt 43) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 43) (dsk 44) (crt 43) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_43)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_44 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 44) (dsk 45) (crt 44) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 44) (dsk 45) (crt 44) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_44)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_45 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 45) (dsk 46) (crt 45) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 45) (dsk 46) (crt 45) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_45)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_46 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 46) (dsk 47) (crt 46) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 46) (dsk 47) (crt 46) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_46)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_47 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 47) (dsk 48) (crt 47) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 47) (dsk 48) (crt 47) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_47)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_48 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 48) (dsk 49) (crt 48) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 48) (dsk 49) (crt 48) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_48)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_49 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 49) (dsk 50) (crt 49) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 49) (dsk 50) (crt 49) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_49)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_50 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 50) (dsk 51) (crt 50) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 50) (dsk 51) (crt 50) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_50)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_51 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 51) (dsk 52) (crt 51) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 51) (dsk 52) (crt 51) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_51)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_52 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 52) (dsk 53) (crt 52) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 52) (dsk 53) (crt 52) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_52)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_53 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 53) (dsk 54) (crt 53) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 53) (dsk 54) (crt 53) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_53)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_54 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 54) (dsk 55) (crt 54) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 54) (dsk 55) (crt 54) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_54)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_55 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 55) (dsk 56) (crt 55) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 55) (dsk 56) (crt 55) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_55)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_56 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 56) (dsk 57) (crt 56) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 56) (dsk 57) (crt 56) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_56)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_57 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 57) (dsk 58) (crt 57) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 57) (dsk 58) (crt 57) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_57)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_58 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 58) (dsk 59) (crt 58) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 58) (dsk 59) (crt 58) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_58)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_59 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 59) (dsk 60) (crt 59) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 59) (dsk 60) (crt 59) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_59)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_60 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 60) (dsk 61) (crt 60) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 60) (dsk 61) (crt 60) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_60)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_61 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 61) (dsk 62) (crt 61) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 61) (dsk 62) (crt 61) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_61)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_62 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 62) (dsk 63) (crt 62) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 62) (dsk 63) (crt 62) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_62)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_63 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 63) (dsk 64) (crt 63) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 63) (dsk 64) (crt 63) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_63)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_64 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 64) (dsk 65) (crt 64) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 64) (dsk 65) (crt 64) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_64)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_65 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 65) (dsk 66) (crt 65) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 65) (dsk 66) (crt 65) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_65)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_66 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 66) (dsk 67) (crt 66) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 66) (dsk 67) (crt 66) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_66)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_67 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 67) (dsk 68) (crt 67) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 67) (dsk 68) (crt 67) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_67)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_68 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 68) (dsk 69) (crt 68) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 68) (dsk 69) (crt 68) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_68)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_69 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 69) (dsk 70) (crt 69) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 69) (dsk 70) (crt 69) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_69)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_70 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 70) (dsk 71) (crt 70) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 70) (dsk 71) (crt 70) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_70)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_71 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 71) (dsk 72) (crt 71) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 71) (dsk 72) (crt 71) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_71)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_72 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 72) (dsk 73) (crt 72) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 72) (dsk 73) (crt 72) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_72)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_73 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 73) (dsk 74) (crt 73) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 73) (dsk 74) (crt 73) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_73)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_74 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 74) (dsk 75) (crt 74) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 74) (dsk 75) (crt 74) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_74)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_75 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 75) (dsk 76) (crt 75) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 75) (dsk 76) (crt 75) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_75)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_76 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 76) (dsk 77) (crt 76) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 76) (dsk 77) (crt 76) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_76)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_77 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 77) (dsk 78) (crt 77) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 77) (dsk 78) (crt 77) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_77)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_78 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 78) (dsk 79) (crt 78) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 78) (dsk 79) (crt 78) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_78)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_79 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 79) (dsk 80) (crt 79) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 79) (dsk 80) (crt 79) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_79)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem stepOK_80 (j : Fin 10) (i : Fin NC) :
    stepOKB (dsk 80) (dsk 81) (crt 80) PXM PYM RADM (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) = true := by
  have h := allS_sound (f := fun p : ℕ × ℕ => stepOKB (dsk 80) (dsk 81) (crt 80) PXM PYM RADM (((p.1 + 1) % 10)*NC + p.2) (p.1*NC + p.2)) (by simpa [chkSteps] using lvlSteps (lvl_80)) (j.val, i.val) (mem_stepQs j.isLt (by simpa [NC] using i.isLt))
  simpa using h

theorem hD1_lvl_0 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 0 (j.val + 1) i) Xb (Dd 1 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 0) (dsk 1) (crt 0) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_0 j i)

theorem hD1_lvl_1 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 1 (j.val + 1) i) Xb (Dd 2 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 1) (dsk 2) (crt 1) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_1 j i)

theorem hD1_lvl_2 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 2 (j.val + 1) i) Xb (Dd 3 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 2) (dsk 3) (crt 2) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_2 j i)

theorem hD1_lvl_3 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 3 (j.val + 1) i) Xb (Dd 4 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 3) (dsk 4) (crt 3) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_3 j i)

theorem hD1_lvl_4 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 4 (j.val + 1) i) Xb (Dd 5 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 4) (dsk 5) (crt 4) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_4 j i)

theorem hD1_lvl_5 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 5 (j.val + 1) i) Xb (Dd 6 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 5) (dsk 6) (crt 5) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_5 j i)

theorem hD1_lvl_6 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 6 (j.val + 1) i) Xb (Dd 7 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 6) (dsk 7) (crt 6) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_6 j i)

theorem hD1_lvl_7 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 7 (j.val + 1) i) Xb (Dd 8 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 7) (dsk 8) (crt 7) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_7 j i)

theorem hD1_lvl_8 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 8 (j.val + 1) i) Xb (Dd 9 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 8) (dsk 9) (crt 8) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_8 j i)

theorem hD1_lvl_9 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 9 (j.val + 1) i) Xb (Dd 10 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 9) (dsk 10) (crt 9) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_9 j i)

theorem hD1_lvl_10 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 10 (j.val + 1) i) Xb (Dd 11 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 10) (dsk 11) (crt 10) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_10 j i)

theorem hD1_lvl_11 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 11 (j.val + 1) i) Xb (Dd 12 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 11) (dsk 12) (crt 11) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_11 j i)

theorem hD1_lvl_12 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 12 (j.val + 1) i) Xb (Dd 13 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 12) (dsk 13) (crt 12) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_12 j i)

theorem hD1_lvl_13 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 13 (j.val + 1) i) Xb (Dd 14 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 13) (dsk 14) (crt 13) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_13 j i)

theorem hD1_lvl_14 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 14 (j.val + 1) i) Xb (Dd 15 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 14) (dsk 15) (crt 14) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_14 j i)

theorem hD1_lvl_15 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 15 (j.val + 1) i) Xb (Dd 16 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 15) (dsk 16) (crt 15) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_15 j i)

theorem hD1_lvl_16 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 16 (j.val + 1) i) Xb (Dd 17 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 16) (dsk 17) (crt 16) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_16 j i)

theorem hD1_lvl_17 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 17 (j.val + 1) i) Xb (Dd 18 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 17) (dsk 18) (crt 17) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_17 j i)

theorem hD1_lvl_18 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 18 (j.val + 1) i) Xb (Dd 19 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 18) (dsk 19) (crt 18) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_18 j i)

theorem hD1_lvl_19 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 19 (j.val + 1) i) Xb (Dd 20 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 19) (dsk 20) (crt 19) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_19 j i)

theorem hD1_lvl_20 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 20 (j.val + 1) i) Xb (Dd 21 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 20) (dsk 21) (crt 20) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_20 j i)

theorem hD1_lvl_21 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 21 (j.val + 1) i) Xb (Dd 22 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 21) (dsk 22) (crt 21) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_21 j i)

theorem hD1_lvl_22 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 22 (j.val + 1) i) Xb (Dd 23 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 22) (dsk 23) (crt 22) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_22 j i)

theorem hD1_lvl_23 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 23 (j.val + 1) i) Xb (Dd 24 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 23) (dsk 24) (crt 23) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_23 j i)

theorem hD1_lvl_24 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 24 (j.val + 1) i) Xb (Dd 25 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 24) (dsk 25) (crt 24) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_24 j i)

theorem hD1_lvl_25 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 25 (j.val + 1) i) Xb (Dd 26 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 25) (dsk 26) (crt 25) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_25 j i)

theorem hD1_lvl_26 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 26 (j.val + 1) i) Xb (Dd 27 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 26) (dsk 27) (crt 26) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_26 j i)

theorem hD1_lvl_27 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 27 (j.val + 1) i) Xb (Dd 28 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 27) (dsk 28) (crt 27) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_27 j i)

theorem hD1_lvl_28 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 28 (j.val + 1) i) Xb (Dd 29 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 28) (dsk 29) (crt 28) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_28 j i)

theorem hD1_lvl_29 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 29 (j.val + 1) i) Xb (Dd 30 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 29) (dsk 30) (crt 29) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_29 j i)

theorem hD1_lvl_30 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 30 (j.val + 1) i) Xb (Dd 31 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 30) (dsk 31) (crt 30) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_30 j i)

theorem hD1_lvl_31 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 31 (j.val + 1) i) Xb (Dd 32 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 31) (dsk 32) (crt 31) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_31 j i)

theorem hD1_lvl_32 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 32 (j.val + 1) i) Xb (Dd 33 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 32) (dsk 33) (crt 32) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_32 j i)

theorem hD1_lvl_33 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 33 (j.val + 1) i) Xb (Dd 34 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 33) (dsk 34) (crt 33) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_33 j i)

theorem hD1_lvl_34 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 34 (j.val + 1) i) Xb (Dd 35 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 34) (dsk 35) (crt 34) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_34 j i)

theorem hD1_lvl_35 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 35 (j.val + 1) i) Xb (Dd 36 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 35) (dsk 36) (crt 35) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_35 j i)

theorem hD1_lvl_36 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 36 (j.val + 1) i) Xb (Dd 37 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 36) (dsk 37) (crt 36) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_36 j i)

theorem hD1_lvl_37 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 37 (j.val + 1) i) Xb (Dd 38 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 37) (dsk 38) (crt 37) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_37 j i)

theorem hD1_lvl_38 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 38 (j.val + 1) i) Xb (Dd 39 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 38) (dsk 39) (crt 38) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_38 j i)

theorem hD1_lvl_39 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 39 (j.val + 1) i) Xb (Dd 40 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 39) (dsk 40) (crt 39) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_39 j i)

theorem hD1_lvl_40 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 40 (j.val + 1) i) Xb (Dd 41 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 40) (dsk 41) (crt 40) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_40 j i)

theorem hD1_lvl_41 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 41 (j.val + 1) i) Xb (Dd 42 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 41) (dsk 42) (crt 41) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_41 j i)

theorem hD1_lvl_42 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 42 (j.val + 1) i) Xb (Dd 43 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 42) (dsk 43) (crt 42) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_42 j i)

theorem hD1_lvl_43 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 43 (j.val + 1) i) Xb (Dd 44 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 43) (dsk 44) (crt 43) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_43 j i)

theorem hD1_lvl_44 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 44 (j.val + 1) i) Xb (Dd 45 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 44) (dsk 45) (crt 44) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_44 j i)

theorem hD1_lvl_45 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 45 (j.val + 1) i) Xb (Dd 46 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 45) (dsk 46) (crt 45) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_45 j i)

theorem hD1_lvl_46 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 46 (j.val + 1) i) Xb (Dd 47 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 46) (dsk 47) (crt 46) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_46 j i)

theorem hD1_lvl_47 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 47 (j.val + 1) i) Xb (Dd 48 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 47) (dsk 48) (crt 47) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_47 j i)

theorem hD1_lvl_48 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 48 (j.val + 1) i) Xb (Dd 49 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 48) (dsk 49) (crt 48) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_48 j i)

theorem hD1_lvl_49 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 49 (j.val + 1) i) Xb (Dd 50 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 49) (dsk 50) (crt 49) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_49 j i)

theorem hD1_lvl_50 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 50 (j.val + 1) i) Xb (Dd 51 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 50) (dsk 51) (crt 50) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_50 j i)

theorem hD1_lvl_51 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 51 (j.val + 1) i) Xb (Dd 52 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 51) (dsk 52) (crt 51) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_51 j i)

theorem hD1_lvl_52 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 52 (j.val + 1) i) Xb (Dd 53 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 52) (dsk 53) (crt 52) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_52 j i)

theorem hD1_lvl_53 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 53 (j.val + 1) i) Xb (Dd 54 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 53) (dsk 54) (crt 53) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_53 j i)

theorem hD1_lvl_54 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 54 (j.val + 1) i) Xb (Dd 55 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 54) (dsk 55) (crt 54) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_54 j i)

theorem hD1_lvl_55 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 55 (j.val + 1) i) Xb (Dd 56 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 55) (dsk 56) (crt 55) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_55 j i)

theorem hD1_lvl_56 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 56 (j.val + 1) i) Xb (Dd 57 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 56) (dsk 57) (crt 56) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_56 j i)

theorem hD1_lvl_57 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 57 (j.val + 1) i) Xb (Dd 58 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 57) (dsk 58) (crt 57) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_57 j i)

theorem hD1_lvl_58 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 58 (j.val + 1) i) Xb (Dd 59 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 58) (dsk 59) (crt 58) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_58 j i)

theorem hD1_lvl_59 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 59 (j.val + 1) i) Xb (Dd 60 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 59) (dsk 60) (crt 59) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_59 j i)

theorem hD1_lvl_60 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 60 (j.val + 1) i) Xb (Dd 61 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 60) (dsk 61) (crt 60) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_60 j i)

theorem hD1_lvl_61 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 61 (j.val + 1) i) Xb (Dd 62 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 61) (dsk 62) (crt 61) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_61 j i)

theorem hD1_lvl_62 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 62 (j.val + 1) i) Xb (Dd 63 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 62) (dsk 63) (crt 62) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_62 j i)

theorem hD1_lvl_63 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 63 (j.val + 1) i) Xb (Dd 64 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 63) (dsk 64) (crt 63) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_63 j i)

theorem hD1_lvl_64 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 64 (j.val + 1) i) Xb (Dd 65 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 64) (dsk 65) (crt 64) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_64 j i)

theorem hD1_lvl_65 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 65 (j.val + 1) i) Xb (Dd 66 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 65) (dsk 66) (crt 65) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_65 j i)

theorem hD1_lvl_66 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 66 (j.val + 1) i) Xb (Dd 67 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 66) (dsk 67) (crt 66) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_66 j i)

theorem hD1_lvl_67 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 67 (j.val + 1) i) Xb (Dd 68 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 67) (dsk 68) (crt 67) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_67 j i)

theorem hD1_lvl_68 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 68 (j.val + 1) i) Xb (Dd 69 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 68) (dsk 69) (crt 68) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_68 j i)

theorem hD1_lvl_69 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 69 (j.val + 1) i) Xb (Dd 70 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 69) (dsk 70) (crt 69) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_69 j i)

theorem hD1_lvl_70 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 70 (j.val + 1) i) Xb (Dd 71 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 70) (dsk 71) (crt 70) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_70 j i)

theorem hD1_lvl_71 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 71 (j.val + 1) i) Xb (Dd 72 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 71) (dsk 72) (crt 71) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_71 j i)

theorem hD1_lvl_72 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 72 (j.val + 1) i) Xb (Dd 73 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 72) (dsk 73) (crt 72) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_72 j i)

theorem hD1_lvl_73 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 73 (j.val + 1) i) Xb (Dd 74 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 73) (dsk 74) (crt 73) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_73 j i)

theorem hD1_lvl_74 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 74 (j.val + 1) i) Xb (Dd 75 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 74) (dsk 75) (crt 74) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_74 j i)

theorem hD1_lvl_75 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 75 (j.val + 1) i) Xb (Dd 76 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 75) (dsk 76) (crt 75) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_75 j i)

theorem hD1_lvl_76 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 76 (j.val + 1) i) Xb (Dd 77 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 76) (dsk 77) (crt 76) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_76 j i)

theorem hD1_lvl_77 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 77 (j.val + 1) i) Xb (Dd 78 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 77) (dsk 78) (crt 77) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_77 j i)

theorem hD1_lvl_78 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 78 (j.val + 1) i) Xb (Dd 79 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 78) (dsk 79) (crt 78) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_78 j i)

theorem hD1_lvl_79 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 79 (j.val + 1) i) Xb (Dd 80 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 79) (dsk 80) (crt 79) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_79 j i)

theorem hD1_lvl_80 (j : Fin 10) (i : Fin NC) :
    DiskCover (Dd 80 (j.val + 1) i) Xb (Dd 81 j.val i) := by
  have hj : j.val % 10 = j.val := Nat.mod_eq_of_lt j.isLt
  simpa only [Dd, NC, hj] using
    stepOKB_sound (dsk 80) (dsk 81) (crt 80) (((j.val + 1) % 10)*NC + i.val) (j.val*NC + i.val) (stepOK_80 j i)

theorem hHP_lvl_0 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 1 j.val i).toSet ⊆ halfplane (vdir 0 j.val)) ∧
    (∀ i : Fin NC, (Dd 0 j.val i).toSet ⊆ halfplane (vdir 0 j.val)) := by
  have h : dirOKB (dirs 0) (dsk 1) (dsk 0) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 0) (dsk 1) (dsk 0) j) (by simpa [chkDirs] using lvlDirs (lvl_0)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 0) (dsk 1) (dsk 0) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_1 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 2 j.val i).toSet ⊆ halfplane (vdir 1 j.val)) ∧
    (∀ i : Fin NC, (Dd 1 j.val i).toSet ⊆ halfplane (vdir 1 j.val)) := by
  have h : dirOKB (dirs 1) (dsk 2) (dsk 1) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 1) (dsk 2) (dsk 1) j) (by simpa [chkDirs] using lvlDirs (lvl_1)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 1) (dsk 2) (dsk 1) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_2 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 3 j.val i).toSet ⊆ halfplane (vdir 2 j.val)) ∧
    (∀ i : Fin NC, (Dd 2 j.val i).toSet ⊆ halfplane (vdir 2 j.val)) := by
  have h : dirOKB (dirs 2) (dsk 3) (dsk 2) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 2) (dsk 3) (dsk 2) j) (by simpa [chkDirs] using lvlDirs (lvl_2)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 2) (dsk 3) (dsk 2) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_3 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 4 j.val i).toSet ⊆ halfplane (vdir 3 j.val)) ∧
    (∀ i : Fin NC, (Dd 3 j.val i).toSet ⊆ halfplane (vdir 3 j.val)) := by
  have h : dirOKB (dirs 3) (dsk 4) (dsk 3) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 3) (dsk 4) (dsk 3) j) (by simpa [chkDirs] using lvlDirs (lvl_3)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 3) (dsk 4) (dsk 3) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_4 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 5 j.val i).toSet ⊆ halfplane (vdir 4 j.val)) ∧
    (∀ i : Fin NC, (Dd 4 j.val i).toSet ⊆ halfplane (vdir 4 j.val)) := by
  have h : dirOKB (dirs 4) (dsk 5) (dsk 4) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 4) (dsk 5) (dsk 4) j) (by simpa [chkDirs] using lvlDirs (lvl_4)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 4) (dsk 5) (dsk 4) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_5 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 6 j.val i).toSet ⊆ halfplane (vdir 5 j.val)) ∧
    (∀ i : Fin NC, (Dd 5 j.val i).toSet ⊆ halfplane (vdir 5 j.val)) := by
  have h : dirOKB (dirs 5) (dsk 6) (dsk 5) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 5) (dsk 6) (dsk 5) j) (by simpa [chkDirs] using lvlDirs (lvl_5)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 5) (dsk 6) (dsk 5) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_6 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 7 j.val i).toSet ⊆ halfplane (vdir 6 j.val)) ∧
    (∀ i : Fin NC, (Dd 6 j.val i).toSet ⊆ halfplane (vdir 6 j.val)) := by
  have h : dirOKB (dirs 6) (dsk 7) (dsk 6) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 6) (dsk 7) (dsk 6) j) (by simpa [chkDirs] using lvlDirs (lvl_6)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 6) (dsk 7) (dsk 6) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_7 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 8 j.val i).toSet ⊆ halfplane (vdir 7 j.val)) ∧
    (∀ i : Fin NC, (Dd 7 j.val i).toSet ⊆ halfplane (vdir 7 j.val)) := by
  have h : dirOKB (dirs 7) (dsk 8) (dsk 7) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 7) (dsk 8) (dsk 7) j) (by simpa [chkDirs] using lvlDirs (lvl_7)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 7) (dsk 8) (dsk 7) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_8 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 9 j.val i).toSet ⊆ halfplane (vdir 8 j.val)) ∧
    (∀ i : Fin NC, (Dd 8 j.val i).toSet ⊆ halfplane (vdir 8 j.val)) := by
  have h : dirOKB (dirs 8) (dsk 9) (dsk 8) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 8) (dsk 9) (dsk 8) j) (by simpa [chkDirs] using lvlDirs (lvl_8)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 8) (dsk 9) (dsk 8) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_9 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 10 j.val i).toSet ⊆ halfplane (vdir 9 j.val)) ∧
    (∀ i : Fin NC, (Dd 9 j.val i).toSet ⊆ halfplane (vdir 9 j.val)) := by
  have h : dirOKB (dirs 9) (dsk 10) (dsk 9) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 9) (dsk 10) (dsk 9) j) (by simpa [chkDirs] using lvlDirs (lvl_9)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 9) (dsk 10) (dsk 9) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_10 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 11 j.val i).toSet ⊆ halfplane (vdir 10 j.val)) ∧
    (∀ i : Fin NC, (Dd 10 j.val i).toSet ⊆ halfplane (vdir 10 j.val)) := by
  have h : dirOKB (dirs 10) (dsk 11) (dsk 10) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 10) (dsk 11) (dsk 10) j) (by simpa [chkDirs] using lvlDirs (lvl_10)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 10) (dsk 11) (dsk 10) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_11 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 12 j.val i).toSet ⊆ halfplane (vdir 11 j.val)) ∧
    (∀ i : Fin NC, (Dd 11 j.val i).toSet ⊆ halfplane (vdir 11 j.val)) := by
  have h : dirOKB (dirs 11) (dsk 12) (dsk 11) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 11) (dsk 12) (dsk 11) j) (by simpa [chkDirs] using lvlDirs (lvl_11)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 11) (dsk 12) (dsk 11) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_12 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 13 j.val i).toSet ⊆ halfplane (vdir 12 j.val)) ∧
    (∀ i : Fin NC, (Dd 12 j.val i).toSet ⊆ halfplane (vdir 12 j.val)) := by
  have h : dirOKB (dirs 12) (dsk 13) (dsk 12) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 12) (dsk 13) (dsk 12) j) (by simpa [chkDirs] using lvlDirs (lvl_12)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 12) (dsk 13) (dsk 12) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_13 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 14 j.val i).toSet ⊆ halfplane (vdir 13 j.val)) ∧
    (∀ i : Fin NC, (Dd 13 j.val i).toSet ⊆ halfplane (vdir 13 j.val)) := by
  have h : dirOKB (dirs 13) (dsk 14) (dsk 13) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 13) (dsk 14) (dsk 13) j) (by simpa [chkDirs] using lvlDirs (lvl_13)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 13) (dsk 14) (dsk 13) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_14 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 15 j.val i).toSet ⊆ halfplane (vdir 14 j.val)) ∧
    (∀ i : Fin NC, (Dd 14 j.val i).toSet ⊆ halfplane (vdir 14 j.val)) := by
  have h : dirOKB (dirs 14) (dsk 15) (dsk 14) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 14) (dsk 15) (dsk 14) j) (by simpa [chkDirs] using lvlDirs (lvl_14)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 14) (dsk 15) (dsk 14) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_15 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 16 j.val i).toSet ⊆ halfplane (vdir 15 j.val)) ∧
    (∀ i : Fin NC, (Dd 15 j.val i).toSet ⊆ halfplane (vdir 15 j.val)) := by
  have h : dirOKB (dirs 15) (dsk 16) (dsk 15) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 15) (dsk 16) (dsk 15) j) (by simpa [chkDirs] using lvlDirs (lvl_15)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 15) (dsk 16) (dsk 15) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_16 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 17 j.val i).toSet ⊆ halfplane (vdir 16 j.val)) ∧
    (∀ i : Fin NC, (Dd 16 j.val i).toSet ⊆ halfplane (vdir 16 j.val)) := by
  have h : dirOKB (dirs 16) (dsk 17) (dsk 16) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 16) (dsk 17) (dsk 16) j) (by simpa [chkDirs] using lvlDirs (lvl_16)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 16) (dsk 17) (dsk 16) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_17 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 18 j.val i).toSet ⊆ halfplane (vdir 17 j.val)) ∧
    (∀ i : Fin NC, (Dd 17 j.val i).toSet ⊆ halfplane (vdir 17 j.val)) := by
  have h : dirOKB (dirs 17) (dsk 18) (dsk 17) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 17) (dsk 18) (dsk 17) j) (by simpa [chkDirs] using lvlDirs (lvl_17)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 17) (dsk 18) (dsk 17) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_18 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 19 j.val i).toSet ⊆ halfplane (vdir 18 j.val)) ∧
    (∀ i : Fin NC, (Dd 18 j.val i).toSet ⊆ halfplane (vdir 18 j.val)) := by
  have h : dirOKB (dirs 18) (dsk 19) (dsk 18) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 18) (dsk 19) (dsk 18) j) (by simpa [chkDirs] using lvlDirs (lvl_18)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 18) (dsk 19) (dsk 18) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_19 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 20 j.val i).toSet ⊆ halfplane (vdir 19 j.val)) ∧
    (∀ i : Fin NC, (Dd 19 j.val i).toSet ⊆ halfplane (vdir 19 j.val)) := by
  have h : dirOKB (dirs 19) (dsk 20) (dsk 19) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 19) (dsk 20) (dsk 19) j) (by simpa [chkDirs] using lvlDirs (lvl_19)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 19) (dsk 20) (dsk 19) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_20 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 21 j.val i).toSet ⊆ halfplane (vdir 20 j.val)) ∧
    (∀ i : Fin NC, (Dd 20 j.val i).toSet ⊆ halfplane (vdir 20 j.val)) := by
  have h : dirOKB (dirs 20) (dsk 21) (dsk 20) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 20) (dsk 21) (dsk 20) j) (by simpa [chkDirs] using lvlDirs (lvl_20)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 20) (dsk 21) (dsk 20) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_21 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 22 j.val i).toSet ⊆ halfplane (vdir 21 j.val)) ∧
    (∀ i : Fin NC, (Dd 21 j.val i).toSet ⊆ halfplane (vdir 21 j.val)) := by
  have h : dirOKB (dirs 21) (dsk 22) (dsk 21) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 21) (dsk 22) (dsk 21) j) (by simpa [chkDirs] using lvlDirs (lvl_21)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 21) (dsk 22) (dsk 21) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_22 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 23 j.val i).toSet ⊆ halfplane (vdir 22 j.val)) ∧
    (∀ i : Fin NC, (Dd 22 j.val i).toSet ⊆ halfplane (vdir 22 j.val)) := by
  have h : dirOKB (dirs 22) (dsk 23) (dsk 22) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 22) (dsk 23) (dsk 22) j) (by simpa [chkDirs] using lvlDirs (lvl_22)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 22) (dsk 23) (dsk 22) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_23 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 24 j.val i).toSet ⊆ halfplane (vdir 23 j.val)) ∧
    (∀ i : Fin NC, (Dd 23 j.val i).toSet ⊆ halfplane (vdir 23 j.val)) := by
  have h : dirOKB (dirs 23) (dsk 24) (dsk 23) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 23) (dsk 24) (dsk 23) j) (by simpa [chkDirs] using lvlDirs (lvl_23)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 23) (dsk 24) (dsk 23) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_24 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 25 j.val i).toSet ⊆ halfplane (vdir 24 j.val)) ∧
    (∀ i : Fin NC, (Dd 24 j.val i).toSet ⊆ halfplane (vdir 24 j.val)) := by
  have h : dirOKB (dirs 24) (dsk 25) (dsk 24) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 24) (dsk 25) (dsk 24) j) (by simpa [chkDirs] using lvlDirs (lvl_24)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 24) (dsk 25) (dsk 24) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_25 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 26 j.val i).toSet ⊆ halfplane (vdir 25 j.val)) ∧
    (∀ i : Fin NC, (Dd 25 j.val i).toSet ⊆ halfplane (vdir 25 j.val)) := by
  have h : dirOKB (dirs 25) (dsk 26) (dsk 25) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 25) (dsk 26) (dsk 25) j) (by simpa [chkDirs] using lvlDirs (lvl_25)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 25) (dsk 26) (dsk 25) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_26 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 27 j.val i).toSet ⊆ halfplane (vdir 26 j.val)) ∧
    (∀ i : Fin NC, (Dd 26 j.val i).toSet ⊆ halfplane (vdir 26 j.val)) := by
  have h : dirOKB (dirs 26) (dsk 27) (dsk 26) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 26) (dsk 27) (dsk 26) j) (by simpa [chkDirs] using lvlDirs (lvl_26)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 26) (dsk 27) (dsk 26) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_27 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 28 j.val i).toSet ⊆ halfplane (vdir 27 j.val)) ∧
    (∀ i : Fin NC, (Dd 27 j.val i).toSet ⊆ halfplane (vdir 27 j.val)) := by
  have h : dirOKB (dirs 27) (dsk 28) (dsk 27) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 27) (dsk 28) (dsk 27) j) (by simpa [chkDirs] using lvlDirs (lvl_27)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 27) (dsk 28) (dsk 27) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_28 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 29 j.val i).toSet ⊆ halfplane (vdir 28 j.val)) ∧
    (∀ i : Fin NC, (Dd 28 j.val i).toSet ⊆ halfplane (vdir 28 j.val)) := by
  have h : dirOKB (dirs 28) (dsk 29) (dsk 28) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 28) (dsk 29) (dsk 28) j) (by simpa [chkDirs] using lvlDirs (lvl_28)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 28) (dsk 29) (dsk 28) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_29 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 30 j.val i).toSet ⊆ halfplane (vdir 29 j.val)) ∧
    (∀ i : Fin NC, (Dd 29 j.val i).toSet ⊆ halfplane (vdir 29 j.val)) := by
  have h : dirOKB (dirs 29) (dsk 30) (dsk 29) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 29) (dsk 30) (dsk 29) j) (by simpa [chkDirs] using lvlDirs (lvl_29)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 29) (dsk 30) (dsk 29) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_30 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 31 j.val i).toSet ⊆ halfplane (vdir 30 j.val)) ∧
    (∀ i : Fin NC, (Dd 30 j.val i).toSet ⊆ halfplane (vdir 30 j.val)) := by
  have h : dirOKB (dirs 30) (dsk 31) (dsk 30) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 30) (dsk 31) (dsk 30) j) (by simpa [chkDirs] using lvlDirs (lvl_30)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 30) (dsk 31) (dsk 30) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_31 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 32 j.val i).toSet ⊆ halfplane (vdir 31 j.val)) ∧
    (∀ i : Fin NC, (Dd 31 j.val i).toSet ⊆ halfplane (vdir 31 j.val)) := by
  have h : dirOKB (dirs 31) (dsk 32) (dsk 31) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 31) (dsk 32) (dsk 31) j) (by simpa [chkDirs] using lvlDirs (lvl_31)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 31) (dsk 32) (dsk 31) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_32 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 33 j.val i).toSet ⊆ halfplane (vdir 32 j.val)) ∧
    (∀ i : Fin NC, (Dd 32 j.val i).toSet ⊆ halfplane (vdir 32 j.val)) := by
  have h : dirOKB (dirs 32) (dsk 33) (dsk 32) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 32) (dsk 33) (dsk 32) j) (by simpa [chkDirs] using lvlDirs (lvl_32)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 32) (dsk 33) (dsk 32) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_33 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 34 j.val i).toSet ⊆ halfplane (vdir 33 j.val)) ∧
    (∀ i : Fin NC, (Dd 33 j.val i).toSet ⊆ halfplane (vdir 33 j.val)) := by
  have h : dirOKB (dirs 33) (dsk 34) (dsk 33) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 33) (dsk 34) (dsk 33) j) (by simpa [chkDirs] using lvlDirs (lvl_33)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 33) (dsk 34) (dsk 33) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_34 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 35 j.val i).toSet ⊆ halfplane (vdir 34 j.val)) ∧
    (∀ i : Fin NC, (Dd 34 j.val i).toSet ⊆ halfplane (vdir 34 j.val)) := by
  have h : dirOKB (dirs 34) (dsk 35) (dsk 34) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 34) (dsk 35) (dsk 34) j) (by simpa [chkDirs] using lvlDirs (lvl_34)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 34) (dsk 35) (dsk 34) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_35 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 36 j.val i).toSet ⊆ halfplane (vdir 35 j.val)) ∧
    (∀ i : Fin NC, (Dd 35 j.val i).toSet ⊆ halfplane (vdir 35 j.val)) := by
  have h : dirOKB (dirs 35) (dsk 36) (dsk 35) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 35) (dsk 36) (dsk 35) j) (by simpa [chkDirs] using lvlDirs (lvl_35)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 35) (dsk 36) (dsk 35) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_36 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 37 j.val i).toSet ⊆ halfplane (vdir 36 j.val)) ∧
    (∀ i : Fin NC, (Dd 36 j.val i).toSet ⊆ halfplane (vdir 36 j.val)) := by
  have h : dirOKB (dirs 36) (dsk 37) (dsk 36) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 36) (dsk 37) (dsk 36) j) (by simpa [chkDirs] using lvlDirs (lvl_36)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 36) (dsk 37) (dsk 36) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_37 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 38 j.val i).toSet ⊆ halfplane (vdir 37 j.val)) ∧
    (∀ i : Fin NC, (Dd 37 j.val i).toSet ⊆ halfplane (vdir 37 j.val)) := by
  have h : dirOKB (dirs 37) (dsk 38) (dsk 37) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 37) (dsk 38) (dsk 37) j) (by simpa [chkDirs] using lvlDirs (lvl_37)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 37) (dsk 38) (dsk 37) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_38 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 39 j.val i).toSet ⊆ halfplane (vdir 38 j.val)) ∧
    (∀ i : Fin NC, (Dd 38 j.val i).toSet ⊆ halfplane (vdir 38 j.val)) := by
  have h : dirOKB (dirs 38) (dsk 39) (dsk 38) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 38) (dsk 39) (dsk 38) j) (by simpa [chkDirs] using lvlDirs (lvl_38)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 38) (dsk 39) (dsk 38) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_39 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 40 j.val i).toSet ⊆ halfplane (vdir 39 j.val)) ∧
    (∀ i : Fin NC, (Dd 39 j.val i).toSet ⊆ halfplane (vdir 39 j.val)) := by
  have h : dirOKB (dirs 39) (dsk 40) (dsk 39) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 39) (dsk 40) (dsk 39) j) (by simpa [chkDirs] using lvlDirs (lvl_39)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 39) (dsk 40) (dsk 39) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_40 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 41 j.val i).toSet ⊆ halfplane (vdir 40 j.val)) ∧
    (∀ i : Fin NC, (Dd 40 j.val i).toSet ⊆ halfplane (vdir 40 j.val)) := by
  have h : dirOKB (dirs 40) (dsk 41) (dsk 40) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 40) (dsk 41) (dsk 40) j) (by simpa [chkDirs] using lvlDirs (lvl_40)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 40) (dsk 41) (dsk 40) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_41 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 42 j.val i).toSet ⊆ halfplane (vdir 41 j.val)) ∧
    (∀ i : Fin NC, (Dd 41 j.val i).toSet ⊆ halfplane (vdir 41 j.val)) := by
  have h : dirOKB (dirs 41) (dsk 42) (dsk 41) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 41) (dsk 42) (dsk 41) j) (by simpa [chkDirs] using lvlDirs (lvl_41)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 41) (dsk 42) (dsk 41) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_42 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 43 j.val i).toSet ⊆ halfplane (vdir 42 j.val)) ∧
    (∀ i : Fin NC, (Dd 42 j.val i).toSet ⊆ halfplane (vdir 42 j.val)) := by
  have h : dirOKB (dirs 42) (dsk 43) (dsk 42) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 42) (dsk 43) (dsk 42) j) (by simpa [chkDirs] using lvlDirs (lvl_42)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 42) (dsk 43) (dsk 42) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_43 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 44 j.val i).toSet ⊆ halfplane (vdir 43 j.val)) ∧
    (∀ i : Fin NC, (Dd 43 j.val i).toSet ⊆ halfplane (vdir 43 j.val)) := by
  have h : dirOKB (dirs 43) (dsk 44) (dsk 43) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 43) (dsk 44) (dsk 43) j) (by simpa [chkDirs] using lvlDirs (lvl_43)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 43) (dsk 44) (dsk 43) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_44 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 45 j.val i).toSet ⊆ halfplane (vdir 44 j.val)) ∧
    (∀ i : Fin NC, (Dd 44 j.val i).toSet ⊆ halfplane (vdir 44 j.val)) := by
  have h : dirOKB (dirs 44) (dsk 45) (dsk 44) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 44) (dsk 45) (dsk 44) j) (by simpa [chkDirs] using lvlDirs (lvl_44)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 44) (dsk 45) (dsk 44) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_45 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 46 j.val i).toSet ⊆ halfplane (vdir 45 j.val)) ∧
    (∀ i : Fin NC, (Dd 45 j.val i).toSet ⊆ halfplane (vdir 45 j.val)) := by
  have h : dirOKB (dirs 45) (dsk 46) (dsk 45) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 45) (dsk 46) (dsk 45) j) (by simpa [chkDirs] using lvlDirs (lvl_45)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 45) (dsk 46) (dsk 45) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_46 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 47 j.val i).toSet ⊆ halfplane (vdir 46 j.val)) ∧
    (∀ i : Fin NC, (Dd 46 j.val i).toSet ⊆ halfplane (vdir 46 j.val)) := by
  have h : dirOKB (dirs 46) (dsk 47) (dsk 46) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 46) (dsk 47) (dsk 46) j) (by simpa [chkDirs] using lvlDirs (lvl_46)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 46) (dsk 47) (dsk 46) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_47 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 48 j.val i).toSet ⊆ halfplane (vdir 47 j.val)) ∧
    (∀ i : Fin NC, (Dd 47 j.val i).toSet ⊆ halfplane (vdir 47 j.val)) := by
  have h : dirOKB (dirs 47) (dsk 48) (dsk 47) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 47) (dsk 48) (dsk 47) j) (by simpa [chkDirs] using lvlDirs (lvl_47)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 47) (dsk 48) (dsk 47) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_48 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 49 j.val i).toSet ⊆ halfplane (vdir 48 j.val)) ∧
    (∀ i : Fin NC, (Dd 48 j.val i).toSet ⊆ halfplane (vdir 48 j.val)) := by
  have h : dirOKB (dirs 48) (dsk 49) (dsk 48) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 48) (dsk 49) (dsk 48) j) (by simpa [chkDirs] using lvlDirs (lvl_48)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 48) (dsk 49) (dsk 48) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_49 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 50 j.val i).toSet ⊆ halfplane (vdir 49 j.val)) ∧
    (∀ i : Fin NC, (Dd 49 j.val i).toSet ⊆ halfplane (vdir 49 j.val)) := by
  have h : dirOKB (dirs 49) (dsk 50) (dsk 49) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 49) (dsk 50) (dsk 49) j) (by simpa [chkDirs] using lvlDirs (lvl_49)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 49) (dsk 50) (dsk 49) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_50 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 51 j.val i).toSet ⊆ halfplane (vdir 50 j.val)) ∧
    (∀ i : Fin NC, (Dd 50 j.val i).toSet ⊆ halfplane (vdir 50 j.val)) := by
  have h : dirOKB (dirs 50) (dsk 51) (dsk 50) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 50) (dsk 51) (dsk 50) j) (by simpa [chkDirs] using lvlDirs (lvl_50)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 50) (dsk 51) (dsk 50) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_51 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 52 j.val i).toSet ⊆ halfplane (vdir 51 j.val)) ∧
    (∀ i : Fin NC, (Dd 51 j.val i).toSet ⊆ halfplane (vdir 51 j.val)) := by
  have h : dirOKB (dirs 51) (dsk 52) (dsk 51) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 51) (dsk 52) (dsk 51) j) (by simpa [chkDirs] using lvlDirs (lvl_51)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 51) (dsk 52) (dsk 51) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_52 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 53 j.val i).toSet ⊆ halfplane (vdir 52 j.val)) ∧
    (∀ i : Fin NC, (Dd 52 j.val i).toSet ⊆ halfplane (vdir 52 j.val)) := by
  have h : dirOKB (dirs 52) (dsk 53) (dsk 52) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 52) (dsk 53) (dsk 52) j) (by simpa [chkDirs] using lvlDirs (lvl_52)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 52) (dsk 53) (dsk 52) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_53 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 54 j.val i).toSet ⊆ halfplane (vdir 53 j.val)) ∧
    (∀ i : Fin NC, (Dd 53 j.val i).toSet ⊆ halfplane (vdir 53 j.val)) := by
  have h : dirOKB (dirs 53) (dsk 54) (dsk 53) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 53) (dsk 54) (dsk 53) j) (by simpa [chkDirs] using lvlDirs (lvl_53)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 53) (dsk 54) (dsk 53) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_54 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 55 j.val i).toSet ⊆ halfplane (vdir 54 j.val)) ∧
    (∀ i : Fin NC, (Dd 54 j.val i).toSet ⊆ halfplane (vdir 54 j.val)) := by
  have h : dirOKB (dirs 54) (dsk 55) (dsk 54) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 54) (dsk 55) (dsk 54) j) (by simpa [chkDirs] using lvlDirs (lvl_54)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 54) (dsk 55) (dsk 54) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_55 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 56 j.val i).toSet ⊆ halfplane (vdir 55 j.val)) ∧
    (∀ i : Fin NC, (Dd 55 j.val i).toSet ⊆ halfplane (vdir 55 j.val)) := by
  have h : dirOKB (dirs 55) (dsk 56) (dsk 55) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 55) (dsk 56) (dsk 55) j) (by simpa [chkDirs] using lvlDirs (lvl_55)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 55) (dsk 56) (dsk 55) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_56 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 57 j.val i).toSet ⊆ halfplane (vdir 56 j.val)) ∧
    (∀ i : Fin NC, (Dd 56 j.val i).toSet ⊆ halfplane (vdir 56 j.val)) := by
  have h : dirOKB (dirs 56) (dsk 57) (dsk 56) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 56) (dsk 57) (dsk 56) j) (by simpa [chkDirs] using lvlDirs (lvl_56)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 56) (dsk 57) (dsk 56) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_57 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 58 j.val i).toSet ⊆ halfplane (vdir 57 j.val)) ∧
    (∀ i : Fin NC, (Dd 57 j.val i).toSet ⊆ halfplane (vdir 57 j.val)) := by
  have h : dirOKB (dirs 57) (dsk 58) (dsk 57) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 57) (dsk 58) (dsk 57) j) (by simpa [chkDirs] using lvlDirs (lvl_57)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 57) (dsk 58) (dsk 57) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_58 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 59 j.val i).toSet ⊆ halfplane (vdir 58 j.val)) ∧
    (∀ i : Fin NC, (Dd 58 j.val i).toSet ⊆ halfplane (vdir 58 j.val)) := by
  have h : dirOKB (dirs 58) (dsk 59) (dsk 58) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 58) (dsk 59) (dsk 58) j) (by simpa [chkDirs] using lvlDirs (lvl_58)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 58) (dsk 59) (dsk 58) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_59 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 60 j.val i).toSet ⊆ halfplane (vdir 59 j.val)) ∧
    (∀ i : Fin NC, (Dd 59 j.val i).toSet ⊆ halfplane (vdir 59 j.val)) := by
  have h : dirOKB (dirs 59) (dsk 60) (dsk 59) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 59) (dsk 60) (dsk 59) j) (by simpa [chkDirs] using lvlDirs (lvl_59)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 59) (dsk 60) (dsk 59) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_60 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 61 j.val i).toSet ⊆ halfplane (vdir 60 j.val)) ∧
    (∀ i : Fin NC, (Dd 60 j.val i).toSet ⊆ halfplane (vdir 60 j.val)) := by
  have h : dirOKB (dirs 60) (dsk 61) (dsk 60) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 60) (dsk 61) (dsk 60) j) (by simpa [chkDirs] using lvlDirs (lvl_60)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 60) (dsk 61) (dsk 60) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_61 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 62 j.val i).toSet ⊆ halfplane (vdir 61 j.val)) ∧
    (∀ i : Fin NC, (Dd 61 j.val i).toSet ⊆ halfplane (vdir 61 j.val)) := by
  have h : dirOKB (dirs 61) (dsk 62) (dsk 61) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 61) (dsk 62) (dsk 61) j) (by simpa [chkDirs] using lvlDirs (lvl_61)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 61) (dsk 62) (dsk 61) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_62 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 63 j.val i).toSet ⊆ halfplane (vdir 62 j.val)) ∧
    (∀ i : Fin NC, (Dd 62 j.val i).toSet ⊆ halfplane (vdir 62 j.val)) := by
  have h : dirOKB (dirs 62) (dsk 63) (dsk 62) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 62) (dsk 63) (dsk 62) j) (by simpa [chkDirs] using lvlDirs (lvl_62)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 62) (dsk 63) (dsk 62) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_63 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 64 j.val i).toSet ⊆ halfplane (vdir 63 j.val)) ∧
    (∀ i : Fin NC, (Dd 63 j.val i).toSet ⊆ halfplane (vdir 63 j.val)) := by
  have h : dirOKB (dirs 63) (dsk 64) (dsk 63) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 63) (dsk 64) (dsk 63) j) (by simpa [chkDirs] using lvlDirs (lvl_63)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 63) (dsk 64) (dsk 63) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_64 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 65 j.val i).toSet ⊆ halfplane (vdir 64 j.val)) ∧
    (∀ i : Fin NC, (Dd 64 j.val i).toSet ⊆ halfplane (vdir 64 j.val)) := by
  have h : dirOKB (dirs 64) (dsk 65) (dsk 64) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 64) (dsk 65) (dsk 64) j) (by simpa [chkDirs] using lvlDirs (lvl_64)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 64) (dsk 65) (dsk 64) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_65 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 66 j.val i).toSet ⊆ halfplane (vdir 65 j.val)) ∧
    (∀ i : Fin NC, (Dd 65 j.val i).toSet ⊆ halfplane (vdir 65 j.val)) := by
  have h : dirOKB (dirs 65) (dsk 66) (dsk 65) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 65) (dsk 66) (dsk 65) j) (by simpa [chkDirs] using lvlDirs (lvl_65)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 65) (dsk 66) (dsk 65) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_66 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 67 j.val i).toSet ⊆ halfplane (vdir 66 j.val)) ∧
    (∀ i : Fin NC, (Dd 66 j.val i).toSet ⊆ halfplane (vdir 66 j.val)) := by
  have h : dirOKB (dirs 66) (dsk 67) (dsk 66) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 66) (dsk 67) (dsk 66) j) (by simpa [chkDirs] using lvlDirs (lvl_66)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 66) (dsk 67) (dsk 66) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_67 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 68 j.val i).toSet ⊆ halfplane (vdir 67 j.val)) ∧
    (∀ i : Fin NC, (Dd 67 j.val i).toSet ⊆ halfplane (vdir 67 j.val)) := by
  have h : dirOKB (dirs 67) (dsk 68) (dsk 67) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 67) (dsk 68) (dsk 67) j) (by simpa [chkDirs] using lvlDirs (lvl_67)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 67) (dsk 68) (dsk 67) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_68 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 69 j.val i).toSet ⊆ halfplane (vdir 68 j.val)) ∧
    (∀ i : Fin NC, (Dd 68 j.val i).toSet ⊆ halfplane (vdir 68 j.val)) := by
  have h : dirOKB (dirs 68) (dsk 69) (dsk 68) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 68) (dsk 69) (dsk 68) j) (by simpa [chkDirs] using lvlDirs (lvl_68)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 68) (dsk 69) (dsk 68) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_69 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 70 j.val i).toSet ⊆ halfplane (vdir 69 j.val)) ∧
    (∀ i : Fin NC, (Dd 69 j.val i).toSet ⊆ halfplane (vdir 69 j.val)) := by
  have h : dirOKB (dirs 69) (dsk 70) (dsk 69) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 69) (dsk 70) (dsk 69) j) (by simpa [chkDirs] using lvlDirs (lvl_69)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 69) (dsk 70) (dsk 69) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_70 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 71 j.val i).toSet ⊆ halfplane (vdir 70 j.val)) ∧
    (∀ i : Fin NC, (Dd 70 j.val i).toSet ⊆ halfplane (vdir 70 j.val)) := by
  have h : dirOKB (dirs 70) (dsk 71) (dsk 70) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 70) (dsk 71) (dsk 70) j) (by simpa [chkDirs] using lvlDirs (lvl_70)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 70) (dsk 71) (dsk 70) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_71 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 72 j.val i).toSet ⊆ halfplane (vdir 71 j.val)) ∧
    (∀ i : Fin NC, (Dd 71 j.val i).toSet ⊆ halfplane (vdir 71 j.val)) := by
  have h : dirOKB (dirs 71) (dsk 72) (dsk 71) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 71) (dsk 72) (dsk 71) j) (by simpa [chkDirs] using lvlDirs (lvl_71)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 71) (dsk 72) (dsk 71) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_72 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 73 j.val i).toSet ⊆ halfplane (vdir 72 j.val)) ∧
    (∀ i : Fin NC, (Dd 72 j.val i).toSet ⊆ halfplane (vdir 72 j.val)) := by
  have h : dirOKB (dirs 72) (dsk 73) (dsk 72) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 72) (dsk 73) (dsk 72) j) (by simpa [chkDirs] using lvlDirs (lvl_72)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 72) (dsk 73) (dsk 72) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_73 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 74 j.val i).toSet ⊆ halfplane (vdir 73 j.val)) ∧
    (∀ i : Fin NC, (Dd 73 j.val i).toSet ⊆ halfplane (vdir 73 j.val)) := by
  have h : dirOKB (dirs 73) (dsk 74) (dsk 73) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 73) (dsk 74) (dsk 73) j) (by simpa [chkDirs] using lvlDirs (lvl_73)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 73) (dsk 74) (dsk 73) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_74 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 75 j.val i).toSet ⊆ halfplane (vdir 74 j.val)) ∧
    (∀ i : Fin NC, (Dd 74 j.val i).toSet ⊆ halfplane (vdir 74 j.val)) := by
  have h : dirOKB (dirs 74) (dsk 75) (dsk 74) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 74) (dsk 75) (dsk 74) j) (by simpa [chkDirs] using lvlDirs (lvl_74)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 74) (dsk 75) (dsk 74) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_75 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 76 j.val i).toSet ⊆ halfplane (vdir 75 j.val)) ∧
    (∀ i : Fin NC, (Dd 75 j.val i).toSet ⊆ halfplane (vdir 75 j.val)) := by
  have h : dirOKB (dirs 75) (dsk 76) (dsk 75) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 75) (dsk 76) (dsk 75) j) (by simpa [chkDirs] using lvlDirs (lvl_75)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 75) (dsk 76) (dsk 75) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_76 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 77 j.val i).toSet ⊆ halfplane (vdir 76 j.val)) ∧
    (∀ i : Fin NC, (Dd 76 j.val i).toSet ⊆ halfplane (vdir 76 j.val)) := by
  have h : dirOKB (dirs 76) (dsk 77) (dsk 76) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 76) (dsk 77) (dsk 76) j) (by simpa [chkDirs] using lvlDirs (lvl_76)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 76) (dsk 77) (dsk 76) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_77 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 78 j.val i).toSet ⊆ halfplane (vdir 77 j.val)) ∧
    (∀ i : Fin NC, (Dd 77 j.val i).toSet ⊆ halfplane (vdir 77 j.val)) := by
  have h : dirOKB (dirs 77) (dsk 78) (dsk 77) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 77) (dsk 78) (dsk 77) j) (by simpa [chkDirs] using lvlDirs (lvl_77)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 77) (dsk 78) (dsk 77) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_78 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 79 j.val i).toSet ⊆ halfplane (vdir 78 j.val)) ∧
    (∀ i : Fin NC, (Dd 78 j.val i).toSet ⊆ halfplane (vdir 78 j.val)) := by
  have h : dirOKB (dirs 78) (dsk 79) (dsk 78) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 78) (dsk 79) (dsk 78) j) (by simpa [chkDirs] using lvlDirs (lvl_78)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 78) (dsk 79) (dsk 78) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_79 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 80 j.val i).toSet ⊆ halfplane (vdir 79 j.val)) ∧
    (∀ i : Fin NC, (Dd 79 j.val i).toSet ⊆ halfplane (vdir 79 j.val)) := by
  have h : dirOKB (dirs 79) (dsk 80) (dsk 79) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 79) (dsk 80) (dsk 79) j) (by simpa [chkDirs] using lvlDirs (lvl_79)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 79) (dsk 80) (dsk 79) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hHP_lvl_80 (j : Fin 10) :
    (∀ i : Fin NC, (Dd 81 j.val i).toSet ⊆ halfplane (vdir 80 j.val)) ∧
    (∀ i : Fin NC, (Dd 80 j.val i).toSet ⊆ halfplane (vdir 80 j.val)) := by
  have h : dirOKB (dirs 80) (dsk 81) (dsk 80) j.val = true := by
    have h2 := allS_sound (f := fun j : ℕ => dirOKB (dirs 80) (dsk 81) (dsk 80) j) (by simpa [chkDirs] using lvlDirs (lvl_80)) j.val (mem_dirQs j.isLt)
    simpa using h2
  simpa only [vdir, Dd] using dirOKB_sound (dirs 80) (dsk 81) (dsk 80) j.val (by simpa [Nat.mod_eq_of_lt j.isLt] using h)

theorem hQ_lvl_71 (z₁ A : ℂ) (hz1 : Zb.mem z₁) (hA : Ab.mem A) :
    diskUnion (Dd 71 0) ⊆ Petal z₁ A 4 := by
  have hc : petalOKB (dsk 71) ZCX ZCY ETA1 ACX ACY ETAA RRM = true := lvlPetal (pet_71)
  simp only [petalOKB, Bool.and_eq_true, and_assoc] at hc
  intro z hz
  rw [mem_diskUnion] at hz
  obtain ⟨i, hi⟩ := hz
  fin_cases i

  · exact petalDskB_sound _ _ _ hc.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.2 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
theorem hQ_lvl_72 (z₁ A : ℂ) (hz1 : Zb.mem z₁) (hA : Ab.mem A) :
    diskUnion (Dd 72 0) ⊆ Petal z₁ A 4 := by
  have hc : petalOKB (dsk 72) ZCX ZCY ETA1 ACX ACY ETAA RRM = true := lvlPetal (pet_72)
  simp only [petalOKB, Bool.and_eq_true, and_assoc] at hc
  intro z hz
  rw [mem_diskUnion] at hz
  obtain ⟨i, hi⟩ := hz
  fin_cases i

  · exact petalDskB_sound _ _ _ hc.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.2 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
theorem hQ_lvl_73 (z₁ A : ℂ) (hz1 : Zb.mem z₁) (hA : Ab.mem A) :
    diskUnion (Dd 73 0) ⊆ Petal z₁ A 4 := by
  have hc : petalOKB (dsk 73) ZCX ZCY ETA1 ACX ACY ETAA RRM = true := lvlPetal (pet_73)
  simp only [petalOKB, Bool.and_eq_true, and_assoc] at hc
  intro z hz
  rw [mem_diskUnion] at hz
  obtain ⟨i, hi⟩ := hz
  fin_cases i

  · exact petalDskB_sound _ _ _ hc.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.2 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
theorem hQ_lvl_74 (z₁ A : ℂ) (hz1 : Zb.mem z₁) (hA : Ab.mem A) :
    diskUnion (Dd 74 0) ⊆ Petal z₁ A 4 := by
  have hc : petalOKB (dsk 74) ZCX ZCY ETA1 ACX ACY ETAA RRM = true := lvlPetal (pet_74)
  simp only [petalOKB, Bool.and_eq_true, and_assoc] at hc
  intro z hz
  rw [mem_diskUnion] at hz
  obtain ⟨i, hi⟩ := hz
  fin_cases i

  · exact petalDskB_sound _ _ _ hc.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.2 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
theorem hQ_lvl_75 (z₁ A : ℂ) (hz1 : Zb.mem z₁) (hA : Ab.mem A) :
    diskUnion (Dd 75 0) ⊆ Petal z₁ A 4 := by
  have hc : petalOKB (dsk 75) ZCX ZCY ETA1 ACX ACY ETAA RRM = true := lvlPetal (pet_75)
  simp only [petalOKB, Bool.and_eq_true, and_assoc] at hc
  intro z hz
  rw [mem_diskUnion] at hz
  obtain ⟨i, hi⟩ := hz
  fin_cases i

  · exact petalDskB_sound _ _ _ hc.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.2 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
theorem hQ_lvl_76 (z₁ A : ℂ) (hz1 : Zb.mem z₁) (hA : Ab.mem A) :
    diskUnion (Dd 76 0) ⊆ Petal z₁ A 4 := by
  have hc : petalOKB (dsk 76) ZCX ZCY ETA1 ACX ACY ETAA RRM = true := lvlPetal (pet_76)
  simp only [petalOKB, Bool.and_eq_true, and_assoc] at hc
  intro z hz
  rw [mem_diskUnion] at hz
  obtain ⟨i, hi⟩ := hz
  fin_cases i

  · exact petalDskB_sound _ _ _ hc.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.2 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
theorem hQ_lvl_77 (z₁ A : ℂ) (hz1 : Zb.mem z₁) (hA : Ab.mem A) :
    diskUnion (Dd 77 0) ⊆ Petal z₁ A 4 := by
  have hc : petalOKB (dsk 77) ZCX ZCY ETA1 ACX ACY ETAA RRM = true := lvlPetal (pet_77)
  simp only [petalOKB, Bool.and_eq_true, and_assoc] at hc
  intro z hz
  rw [mem_diskUnion] at hz
  obtain ⟨i, hi⟩ := hz
  fin_cases i

  · exact petalDskB_sound _ _ _ hc.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.2 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
theorem hQ_lvl_78 (z₁ A : ℂ) (hz1 : Zb.mem z₁) (hA : Ab.mem A) :
    diskUnion (Dd 78 0) ⊆ Petal z₁ A 4 := by
  have hc : petalOKB (dsk 78) ZCX ZCY ETA1 ACX ACY ETAA RRM = true := lvlPetal (pet_78)
  simp only [petalOKB, Bool.and_eq_true, and_assoc] at hc
  intro z hz
  rw [mem_diskUnion] at hz
  obtain ⟨i, hi⟩ := hz
  fin_cases i

  · exact petalDskB_sound _ _ _ hc.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.2 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
theorem hQ_lvl_79 (z₁ A : ℂ) (hz1 : Zb.mem z₁) (hA : Ab.mem A) :
    diskUnion (Dd 79 0) ⊆ Petal z₁ A 4 := by
  have hc : petalOKB (dsk 79) ZCX ZCY ETA1 ACX ACY ETAA RRM = true := lvlPetal (pet_79)
  simp only [petalOKB, Bool.and_eq_true, and_assoc] at hc
  intro z hz
  rw [mem_diskUnion] at hz
  obtain ⟨i, hi⟩ := hz
  fin_cases i

  · exact petalDskB_sound _ _ _ hc.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.2 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
theorem hQ_lvl_80 (z₁ A : ℂ) (hz1 : Zb.mem z₁) (hA : Ab.mem A) :
    diskUnion (Dd 80 0) ⊆ Petal z₁ A 4 := by
  have hc : petalOKB (dsk 80) ZCX ZCY ETA1 ACX ACY ETAA RRM = true := lvlPetal (pet_80)
  simp only [petalOKB, Bool.and_eq_true, and_assoc] at hc
  intro z hz
  rw [mem_diskUnion] at hz
  obtain ⟨i, hi⟩ := hz
  fin_cases i

  · exact petalDskB_sound _ _ _ hc.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.1 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
  · exact petalDskB_sound _ _ _ hc.2.2.2.2.2 z (by simpa only [Dd, dskOf, NC, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.val_ofNat, Nat.zero_mod, zero_mul, mul_zero, mul_one, zero_add, add_zero] using hi) z₁ hz1 A hA
/-- The `(D1)` fact for every level `k ≤ 80`. -/
def hD1At : (k : ℕ) → k ≤ 80 → ∀ (j : ℕ) (i : Fin NC), DiskCover (Dd k (j + 1) i) Xb (Dd (k + 1) j i)

  | 0, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_0 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 1, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_1 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 2, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_2 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 3, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_3 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 4, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_4 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 5, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_5 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 6, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_6 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 7, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_7 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 8, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_8 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 9, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_9 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 10, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_10 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 11, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_11 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 12, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_12 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 13, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_13 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 14, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_14 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 15, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_15 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 16, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_16 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 17, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_17 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 18, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_18 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 19, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_19 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 20, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_20 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 21, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_21 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 22, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_22 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 23, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_23 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 24, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_24 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 25, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_25 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 26, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_26 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 27, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_27 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 28, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_28 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 29, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_29 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 30, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_30 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 31, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_31 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 32, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_32 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 33, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_33 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 34, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_34 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 35, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_35 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 36, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_36 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 37, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_37 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 38, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_38 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 39, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_39 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 40, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_40 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 41, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_41 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 42, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_42 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 43, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_43 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 44, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_44 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 45, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_45 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 46, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_46 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 47, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_47 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 48, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_48 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 49, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_49 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 50, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_50 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 51, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_51 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 52, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_52 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 53, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_53 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 54, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_54 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 55, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_55 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 56, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_56 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 57, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_57 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 58, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_58 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 59, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_59 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 60, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_60 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 61, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_61 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 62, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_62 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 63, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_63 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 64, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_64 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 65, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_65 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 66, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_66 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 67, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_67 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 68, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_68 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 69, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_69 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 70, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_70 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 71, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_71 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 72, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_72 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 73, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_73 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 74, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_74 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 75, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_75 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 76, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_76 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 77, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_77 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 78, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_78 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 79, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_79 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | 80, _ => fun j i => by
      have h1 : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      simpa only [Dd, h1, h2] using hD1_lvl_80 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩ i
  | n + 81, h => absurd h (by omega)

/-- The `(D2)` fact for every level `k ≤ 80`. -/
def hHPAt : (k : ℕ) → k ≤ 80 → ∀ (j : ℕ),
    (∀ i : Fin NC, (Dd (k + 1) j i).toSet ⊆ halfplane (vdir k j)) ∧
    (∀ i : Fin NC, (Dd k j i).toSet ⊆ halfplane (vdir k j))

  | 0, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_0 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 1, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_1 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 2, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_2 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 3, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_3 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 4, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_4 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 5, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_5 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 6, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_6 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 7, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_7 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 8, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_8 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 9, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_9 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 10, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_10 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 11, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_11 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 12, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_12 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 13, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_13 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 14, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_14 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 15, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_15 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 16, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_16 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 17, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_17 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 18, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_18 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 19, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_19 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 20, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_20 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 21, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_21 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 22, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_22 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 23, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_23 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 24, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_24 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 25, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_25 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 26, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_26 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 27, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_27 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 28, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_28 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 29, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_29 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 30, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_30 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 31, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_31 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 32, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_32 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 33, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_33 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 34, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_34 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 35, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_35 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 36, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_36 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 37, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_37 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 38, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_38 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 39, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_39 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 40, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_40 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 41, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_41 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 42, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_42 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 43, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_43 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 44, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_44 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 45, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_45 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 46, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_46 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 47, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_47 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 48, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_48 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 49, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_49 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 50, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_50 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 51, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_51 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 52, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_52 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 53, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_53 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 54, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_54 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 55, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_55 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 56, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_56 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 57, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_57 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 58, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_58 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 59, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_59 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 60, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_60 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 61, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_61 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 62, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_62 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 63, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_63 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 64, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_64 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 65, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_65 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 66, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_66 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 67, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_67 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 68, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_68 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 69, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_69 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 70, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_70 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 71, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_71 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 72, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_72 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 73, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_73 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 74, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_74 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 75, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_75 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 76, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_76 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 77, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_77 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 78, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_78 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 79, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_79 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | 80, _ => fun j => by
      have h2 : (j % 10) % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
      have hh := hHP_lvl_80 ⟨j % 10, Nat.mod_lt _ (by norm_num)⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [Dd, vdir, h2] using hh.1 i
      · simpa only [Dd, vdir, h2] using hh.2 i
  | n + 81, h => absurd h (by omega)

/-- The `(D3)` fact (petal entry) for the certified levels. -/
def hQAt : (k : ℕ) → 71 ≤ k → k ≤ 80 → ∀ (z₁ A : ℂ), Zb.mem z₁ → Ab.mem A → diskUnion (Dd k 0) ⊆ Petal z₁ A 4

  | 71, _, _ => hQ_lvl_71
  | 72, _, _ => hQ_lvl_72
  | 73, _, _ => hQ_lvl_73
  | 74, _, _ => hQ_lvl_74
  | 75, _, _ => hQ_lvl_75
  | 76, _, _ => hQ_lvl_76
  | 77, _, _ => hQ_lvl_77
  | 78, _, _ => hQ_lvl_78
  | 79, _, _ => hQ_lvl_79
  | 80, _, _ => hQ_lvl_80
  | n + 81, h1, h2 => absurd h2 (by omega)


end Work.SeedCertRay
