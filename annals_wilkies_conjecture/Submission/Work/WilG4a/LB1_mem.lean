import Mathlib
import Submission.Work.WilG4a.fiber_defs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.API
import Submission.Work.WilG1.Calc.lt_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a

open WilkiesDesign

/-- `LB1 p Z = (projLast (pullZ2 p Z ∩ tLtY p))ᶜ` is `Ω`-definable, with a format and degree
bound that is affine in the degree `D` of `Z` (and constant in the format up to `F`).

The four operations are, in order, the coordinate reindexing `pullZ2` (a `coordPre`),
intersection with the half-space `tLtY` (`y`-coordinate less than a fibre coordinate),
projection onto the `y`-axis, and complement. -/
theorem LB1_mem (S : WilkiesDesign.SOMin) (p F : ℕ) :
    ∃ (A c c' : ℕ), ∀ (D : ℕ) (Z : Set (Fin (p + 1) → ℝ)), Z ∈ S.Ω F D (p + 1) →
      Work.WilG4a.LB1 p Z ∈ S.Ω (A + F) (c * D + c') (p + 1) := by
  refine ⟨max (F + 64 * (2 * p + 3) + 64) (p + 5) + 3, 1, 32 * (2 * p + 3) + 35, ?_⟩
  intro D Z hZ
  -- 1. Reindex `Z` to the `(l, y, t)`-ambient along `(l, t) ↦ (l, y, t)`.
  have hPull : pullZ2 p Z ∈ S.Ω (F + 64 * (2 * p + 3) + 64) (D + 32 * (2 * p + 3) + 32)
      (p + 2) :=
    Work.WilG5.mem_mono
      (Work.WilG5.coordPre_mem (S := S) (m := p + 1) (N := p + 2) (F := F) (D := D)
        (ι := iota1 p) (A := Z) hZ)
      (F + 64 * (2 * p + 3) + 64) (D + 32 * (2 * p + 3) + 32) (by omega) (by omega)
  -- 2. The half-space `t < y` is `Ω`-definable with degree `3`, independently of `D`.
  have hlt : tLtY p ∈ S.Ω (p + 5) 3 (p + 2) := by
    have h := Work.WilG1.Calc.lt_mem (S := S) (n := p + 2) 0
      (Fin.last (p + 1)) (Fin.castSucc (Fin.last p))
    exact Work.WilG5.mem_mono h (p + 5) 3 (by omega) (by simp)
  -- 3. Intersection (raise both formats to their common maximum first).
  have hPull' : pullZ2 p Z ∈ S.Ω (max (F + 64 * (2 * p + 3) + 64) (p + 5))
      (D + 32 * (2 * p + 3) + 32) (p + 2) :=
    Work.WilG5.mem_mono hPull _ _ (le_max_left _ _) le_rfl
  have hlt' : tLtY p ∈ S.Ω (max (F + 64 * (2 * p + 3) + 64) (p + 5)) 3 (p + 2) :=
    Work.WilG5.mem_mono hlt _ _ (le_max_right _ _) le_rfl
  have hInt : pullZ2 p Z ∩ tLtY p ∈
      S.Ω (max (F + 64 * (2 * p + 3) + 64) (p + 5) + 1)
        ((D + 32 * (2 * p + 3) + 32) + 3) (p + 2) :=
    Work.WilG0.Omega_inter2 (S := S) hPull' hlt'
  -- 4. Project out `t`, then complement.
  have hProj : projLast (pullZ2 p Z ∩ tLtY p) ∈
      S.Ω (max (F + 64 * (2 * p + 3) + 64) (p + 5) + 2)
        ((D + 32 * (2 * p + 3) + 32) + 3) (p + 1) := S.proj hInt
  have hFinal : LB1 p Z ∈
      S.Ω (max (F + 64 * (2 * p + 3) + 64) (p + 5) + 3)
        ((D + 32 * (2 * p + 3) + 32) + 3) (p + 1) :=
    S.compl hProj
  exact Work.WilG5.mem_mono hFinal _ _ (by omega) (by omega)

end Work.WilG4a
