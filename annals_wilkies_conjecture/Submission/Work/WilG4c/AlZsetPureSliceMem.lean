/-
  WilG4c / `AlZsetPureSliceMem` — the *fibre* (sliced) selection set

      `AlZsetPureSlice p n f L = coordPre (yIdx p n) (openCube n) ∩ SliceLocus p n f L.length
                                   ∩ (AlViolSlice p n f L)ᶜ`

  (`SlicedAlpha.lean`) is `Ω`-definable, with the same loose format/degree bounds `AlFzs`, `AlDzs`
  as its *joint* twin `AlZsetPure` (`CurveFamAlpha_list_pure.AlZsetPureMem`).  This is the
  membership lemma that the fibre choice lemma of BNZ §5.4 (the sliced analogue of
  `CurveFamAlpha_list_pure`) consumes.

  Nothing new is analytic: each of the three conjuncts is `Ω`-definable —

  * `coordPre (yIdx p n) (openCube n)` is a coordinate pullback of the open unit cube
    (`Work.WilG5.openCube_mem` + `Work.WilG5.coordPre_mem`);
  * `SliceLocus p n f L.length` is the projection `projLast` of the fibre derivative graph
    `AlDgListSlice p n f L` (`projLast_AlDgListSlice` below + `SOMin.proj`), hence controlled by
    the hypothesis `hDg` exactly as `AlLoc` is controlled by `AlDgList`;
  * `(AlViolSlice p n f L)ᶜ` comes from the `Ω`-membership of `AlViolSlice`
    (`AlphaViolSliceMem`, the sliced analogue of `Alpha.AlphaViolMem`) by `SOMin.compl`.

  The three conjuncts are combined by `SOMin.inter` (`Fin 3`-indexed, format `+1`, degree = sum),
  and the resulting constants are dominated by the loose `AlFzs`, `AlDzs` of
  `CurveFamAlphaDefs` — the arithmetic is identical to the joint case, since `AlDgListSlice` sits
  in the same ambient dimension `p + (n+1) + 1` as `AlDgList` and the bounds `AlFviol`, `AlDviol`
  are the same.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedAlpha
import Submission.Work.WilG4c.CurveFamAlphaDefs
import Submission.Work.WilG4c.AlphaViolSliceMem

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c
open Work.WilG5

/-! ## 1. The fibre `C^k`-locus is the projection of the fibre derivative graph -/

/-- `SliceLocus p n f L.length` is the projection (dropping the last, value, coordinate) of the
fibre derivative graph `AlDgListSlice p n f L`.  This is the sliced analogue of
`Work.WilkG4c.Alpha.projLast_AlDgList`. -/
theorem projLast_AlDgListSlice {p n : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} {L : List (Fin (n + 1))} :
    WilkiesDesign.projLast (AlDgListSlice p n f L) = SliceLocus p n f L.length := by
  ext w
  constructor
  · rintro ⟨s, hs⟩
    exact (sliceLocus_iff_exists_mem f L w).mpr ⟨s, hs⟩
  · intro hw
    obtain ⟨s, hs⟩ := (sliceLocus_iff_exists_mem f L w).mp hw
    exact ⟨s, hs⟩

/-! ## 2. The membership lemma -/

theorem AlZsetPureSliceMem {S : WilkiesDesign.SOMin} {p n a1 β : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} (L : List (Fin (n + 1)))
    (hDg : Work.WilkG4c.AlDgListSlice p n f L ∈ S.Ω a1 β (p + (n + 1) + 1)) :
    Work.WilkG4c.AlZsetPureSlice p n f L ∈
      S.Ω (Work.WilkG4c.AlFzs p n a1) (Work.WilkG4c.AlDzs p n β) (p + (n + 1)) := by
  -- the common format at which the three conjuncts are intersected
  let F3 : ℕ := max ((4 * n + 24) + 64 * ((p + (n + 1)) + n) + 64)
    (max (a1 + 1) (AlFu p n a1))
  -- the fibre `C^{|L|}`-locus, as the projection of the fibre derivative graph
  have hloc : SliceLocus p n f L.length ∈ S.Ω (a1 + 1) β (p + (n + 1)) := by
    rw [← projLast_AlDgListSlice (f := f) (L := L)]
    exact S.proj hDg
  -- the cube coordinates
  have hcube : coordPre (yIdx p n) (openCube n) ∈
      S.Ω ((4 * n + 24) + 64 * ((p + (n + 1)) + n) + 64)
        ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) (p + (n + 1)) :=
    Work.WilG5.coordPre_mem (S := S) (m := n) (N := p + (n + 1)) (F := 4 * n + 24)
      (D := 16 * n + 16) (ι := yIdx p n) (Work.WilG5.openCube_mem (S := S) (n := n))
  -- the near-maximality disjunct, from the fibre violation set
  have hcomp : (AlViolSlice p n f L)ᶜ ∈
      S.Ω (AlFviol p n a1 + 1) (AlDviol p n β) (p + (n + 1)) :=
    S.compl (AlphaViolSliceMem (S := S) L hDg)
  -- raise everything to the common format `F3`
  have hcube' : coordPre (yIdx p n) (openCube n) ∈
      S.Ω F3 ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) hcube F3 _ (by dsimp only [F3]; omega) le_rfl
  have hloc' : SliceLocus p n f L.length ∈ S.Ω F3 β (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) hloc F3 β (by dsimp only [F3]; omega) le_rfl
  have hcomp' : (AlViolSlice p n f L)ᶜ ∈
      S.Ω (AlFu p n a1) (AlDviol p n β) (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) hcomp (AlFu p n a1) (AlDviol p n β)
      (by simp only [AlFu]; omega) le_rfl
  have hcomp'' : (AlViolSlice p n f L)ᶜ ∈ S.Ω F3 (AlDviol p n β) (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) hcomp' F3 (AlDviol p n β) (by dsimp only [F3]; omega) le_rfl
  -- the threefold intersection
  have h3 := S.inter (F := F3) (n := p + (n + 1)) (k := 3)
    (fun i : Fin 3 => ![(16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32, β, AlDviol p n β] i)
    (fun i : Fin 3 => ![coordPre (yIdx p n) (openCube n), SliceLocus p n f L.length,
      (AlViolSlice p n f L)ᶜ] i)
    (by intro i; fin_cases i
        · simpa using hcube'
        · simpa using hloc'
        · simpa using hcomp'')
  rw [show (∑ i : Fin 3,
      ![(16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32, β, AlDviol p n β] i)
      = ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) + β + AlDviol p n β from by
    simp [Fin.sum_univ_three]] at h3
  rw [Work.WilkG4c.iInter_fin_three (coordPre (yIdx p n) (openCube n))
    (SliceLocus p n f L.length) ((AlViolSlice p n f L)ᶜ)] at h3
  have hZ : AlZsetPureSlice p n f L ∈ S.Ω (F3 + 1)
      (((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) + β + AlDviol p n β)
      (p + (n + 1)) := by
    rw [show AlZsetPureSlice p n f L =
        coordPre (yIdx p n) (openCube n) ∩ SliceLocus p n f L.length ∩
          (AlViolSlice p n f L)ᶜ from rfl]
    exact h3
  refine Work.WilG5.mem_mono (S := S) hZ (AlFzs p n a1) (AlDzs p n β) ?_ ?_
  · dsimp only [F3]; simp only [AlFzs]; omega
  · simp only [AlDzs, AlDu, AlFalt, AlFviol, AlDviol]; omega

end Work.WilG4c
