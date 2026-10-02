/-
# `Work.SeedCertRay.LvlFacts` — extraction of the per-level certificate facts

Generic lemmas used by the generated per-level facts (`Submission/Work/SeedCertRay/Levels.lean`):

* `Dd_succ`, `Dd_mod` — the `j ↦ j % 10` bookkeeping of the disk family
  (the membership lemmas `mem_stepQs`, `mem_dirQs` are generated in `Levels.lean`);
* `lvlSteps`, `lvlDirs`, `lvlPetal` — read the three components of a level check.
-/
import Mathlib
import Submission.Work.SeedCertRay.Q
import Submission.Work.SeedCertRay.ChkA
import Submission.Work.SeedCertRay.ChkB
import Submission.Work.SeedCertRay.ChkC
import Submission.Work.SeedCertRay.ChkD

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

theorem Dd_succ (k j : ℕ) (i : Fin NC) : Dd k (j + 1) i = Dd k (j % 10 + 1) i := by
  have h : (j + 1) % 10 = (j % 10 + 1) % 10 := by rw [Nat.add_mod]
  simp only [Dd, h]

theorem Dd_mod (k j : ℕ) (i : Fin NC) : Dd k j i = Dd k (j % 10) i := by
  have h : j % 10 % 10 = j % 10 := Nat.mod_eq_of_lt (Nat.mod_lt j (by norm_num))
  simp only [Dd, h]

/-- The `(D1)` component of a level check. -/
theorem lvlSteps {k : ℕ} (h : chkLvl k = true) : chkSteps k = true := by
  have h2 : chkSteps k = true ∧ chkDirs k = true := by
    simpa only [chkLvl, Bool.and_eq_true] using h
  exact h2.1

/-- The `(D2)` component of a level check. -/
theorem lvlDirs {k : ℕ} (h : chkLvl k = true) : chkDirs k = true := by
  have h2 : chkSteps k = true ∧ chkDirs k = true := by
    simpa only [chkLvl, Bool.and_eq_true] using h
  exact h2.2

/-- The `(D3)` component of a petal check. -/
theorem lvlPetal {k : ℕ} (h : chkPetal k = true) :
    petalOKB (dsk k) ZCX ZCY ETA1 ACX ACY ETAA RRM = true := by
  simpa [chkPetal] using h

end Work.SeedCertRay
