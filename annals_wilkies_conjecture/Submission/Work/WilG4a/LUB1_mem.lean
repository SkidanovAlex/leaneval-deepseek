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

/-- `LUB1 p Z = (projLast (LUBb p Z))ᶜ` with `LUBb p Z = NIn2hi p Z ∩ tLtY p` and
`NIn2hi p Z = (projLast (In3hi p Z))ᶜ`, `In3hi p Z = pullZ3 p Z ∩ uLtT p`.  So the defining
expression is a composition of

* the coordinate reindexing `pullZ3` (a `coordPre` into the `(l,y,u,t)`-ambient),
* intersection with the half-space `u < t`,
* projection (`t` out), then complement — this is `NIn2hi`,
* intersection with the half-space `t < y`,
* projection (`u` out), then complement.

Every step raises the format by a fixed amount and the degree by a fixed amount; the format
cost of the reindexing is the only term depending on `F`, the degree cost is affine in `D`
with slope `1`. -/
theorem LUB1_mem (S : WilkiesDesign.SOMin) (p F : ℕ) :
    ∃ (A c c' : ℕ), ∀ (D : ℕ) (Z : Set (Fin (p + 1) → ℝ)), Z ∈ S.Ω F D (p + 1) →
      Work.WilG4a.LUB1 p Z ∈ S.Ω (A + F) (c * D + c') (p + 1) := by
  refine ⟨200 * p + 500, 1, 200 * p + 500, ?_⟩
  intro D Z hZ
  -- 1. Reindex `Z` to the `(l, y, u, t)`-ambient along `(l, t) ↦ (l, y, u, t)`.
  have hPull : pullZ3 p Z ∈ S.Ω (F + 64 * (2 * p + 4) + 64) (D + 32 * (2 * p + 4) + 32)
      (p + 3) :=
    Work.WilG5.mem_mono
      (Work.WilG5.coordPre_mem (S := S) (m := p + 1) (N := p + 3) (F := F) (D := D)
        (ι := iota2 p) (A := Z) hZ)
      (F + 64 * (2 * p + 4) + 64) (D + 32 * (2 * p + 4) + 32) (by omega) (by omega)
  -- 2. The half-space `u < t` is `Ω`-definable with degree `3`, independently of `D`.
  have huLtT : uLtT p ∈ S.Ω (p + 6) 3 (p + 3) := by
    have h := Work.WilG1.Calc.lt_mem (S := S) (n := p + 3) 0
      (Fin.castSucc (Fin.last (p + 1))) (Fin.last (p + 2))
    exact Work.WilG5.mem_mono h (p + 6) 3 (by omega) (by simp)
  -- 3. Intersection (raise both formats to their common maximum first).
  have hPull' : pullZ3 p Z ∈ S.Ω (max (F + 64 * (2 * p + 4) + 64) (p + 6))
      (D + 32 * (2 * p + 4) + 32) (p + 3) :=
    Work.WilG5.mem_mono hPull _ _ (le_max_left _ _) le_rfl
  have huLtT' : uLtT p ∈ S.Ω (max (F + 64 * (2 * p + 4) + 64) (p + 6)) 3 (p + 3) :=
    Work.WilG5.mem_mono huLtT _ _ (le_max_right _ _) le_rfl
  have hInt : In3hi p Z ∈
      S.Ω (max (F + 64 * (2 * p + 4) + 64) (p + 6) + 1)
        ((D + 32 * (2 * p + 4) + 32) + 3) (p + 3) :=
    Work.WilG0.Omega_inter2 (S := S) hPull' huLtT'
  -- 4. Project out `t`, then complement: this is `NIn2hi`.
  have hProj : projLast (In3hi p Z) ∈
      S.Ω (max (F + 64 * (2 * p + 4) + 64) (p + 6) + 2)
        ((D + 32 * (2 * p + 4) + 32) + 3) (p + 2) := S.proj hInt
  have hNIn2hi : NIn2hi p Z ∈
      S.Ω (max (F + 64 * (2 * p + 4) + 64) (p + 6) + 3)
        ((D + 32 * (2 * p + 4) + 32) + 3) (p + 2) := S.compl hProj
  -- 5. The half-space `t < y` (read as `tLtY`) in the `(l, y, u)`-ambient.
  have htLtY : tLtY p ∈ S.Ω (p + 5) 3 (p + 2) := by
    have h := Work.WilG1.Calc.lt_mem (S := S) (n := p + 2) 0
      (Fin.last (p + 1)) (Fin.castSucc (Fin.last p))
    exact Work.WilG5.mem_mono h (p + 5) 3 (by omega) (by simp)
  -- 6. Intersection to obtain `LUBb`.
  have hNIn2hi' : NIn2hi p Z ∈
      S.Ω (max (max (F + 64 * (2 * p + 4) + 64) (p + 6) + 3) (p + 5))
        ((D + 32 * (2 * p + 4) + 32) + 3) (p + 2) :=
    Work.WilG5.mem_mono hNIn2hi _ _ (le_max_left _ _) le_rfl
  have htLtY' : tLtY p ∈
      S.Ω (max (max (F + 64 * (2 * p + 4) + 64) (p + 6) + 3) (p + 5)) 3 (p + 2) :=
    Work.WilG5.mem_mono htLtY _ _ (le_max_right _ _) le_rfl
  have hInt2 : LUBb p Z ∈
      S.Ω (max (max (F + 64 * (2 * p + 4) + 64) (p + 6) + 3) (p + 5) + 1)
        (((D + 32 * (2 * p + 4) + 32) + 3) + 3) (p + 2) :=
    Work.WilG0.Omega_inter2 (S := S) hNIn2hi' htLtY'
  -- 7. Project out `u`, then complement: this is `LUB1`.
  have hProj2 : projLast (LUBb p Z) ∈
      S.Ω (max (max (F + 64 * (2 * p + 4) + 64) (p + 6) + 3) (p + 5) + 2)
        (((D + 32 * (2 * p + 4) + 32) + 3) + 3) (p + 1) := S.proj hInt2
  have hFinal : LUB1 p Z ∈
      S.Ω (max (max (F + 64 * (2 * p + 4) + 64) (p + 6) + 3) (p + 5) + 3)
        (((D + 32 * (2 * p + 4) + 32) + 3) + 3) (p + 1) := S.compl hProj2
  exact Work.WilG5.mem_mono hFinal _ _ (by omega) (by omega)

end Work.WilG4a
