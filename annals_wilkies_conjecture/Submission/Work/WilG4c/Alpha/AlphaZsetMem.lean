/-
  WilG4c — `AlphaZsetMem`: the selection set `AlZset` of the `CurveFamAlpha` lemma is
  `Ω`-definable.

  `AlZset p n f L E` is (definitionally)

      `coordPre (yIdx p n) (openCube n) ∩ AlLoc p n f L.length
         ∩ (AlAlt1 p n f L E ∪ AlAlt2 p n f L E ∪ (AlViol p n f L)ᶜ)`,

  so the `Ω`-membership is bookkeeping in the frozen `Ω`-calculus, exactly as for `Xset`
  (`Submission/Work/WilG4c/CurveFam.lean`):

  * `coordPre (yIdx p n) (openCube n)` is a coordinate pullback of `openCube n`
    (`Work.WilG5.openCube_mem` + `Work.WilG5.coordPre_mem`), cost
    `(4n+24) + 64·(N+n) + 64` in format and `(16n+16) + 32·(N+n) + 32` in degree, `N = p+(n+1)`;
  * `AlLoc p n f L.length` is `projLast (AlDgList p n f L)` (`projLast_AlDgList`), hence in
    `Ω (a1+1) β N` by `SOMin.proj` from the hypothesis `hDg`;
  * `AlAlt1`, `AlAlt2` are projections of `AlDgList ∩ coordPre (AlSIdx N) A` with
    `A = AlGeE E`, `AlLeE E`; the half-lines are `Ω`-sets of format `20` and degree `4`
    (`Work.WilG5.leSet_mem`, `geSet_mem` at `n = 1`), so the `coordPre`/`inter`/`projN`
    calculus gives exactly the declared `AlFalt`/`AlDalt` bounds (`AlAltSetMem`);
  * `(AlViol p n f L)ᶜ` comes from the hypothesis `hViol` by `SOMin.compl` (format `+1`).

  The three disjuncts are joined by `SOMin.union` (`Fin 3`-indexed, degree = sum) and the
  three conjuncts by `SOMin.inter` (`Fin 3`-indexed, format `+1`, degree = sum); the loose
  constants `AlFu`, `AlDu`, `AlFzs`, `AlDzs` of `CurveFamAlphaDefs` dominate the result.
-/
import Mathlib
import Submission.Work.WilG4c.CurveFamAlphaDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c.Alpha

open WilkiesDesign Work.WilkG4c Work.WilG5

/-! ## 1. The `C^{|L|}`-locus is the projection of the derivative graph -/

/-- `AlLoc p n f L.length` is the projection of the graph `AlDgList p n f L`. -/
theorem projLast_AlDgList {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (p + (n + 1)))} :
    projLast (AlDgList p n f L) = AlLoc p n f L.length := by
  ext w
  constructor
  · rintro ⟨t, ht⟩
    rw [mem_AlDgList, Fin.init_snoc] at ht
    exact ht.1
  · intro hw
    exact ⟨iterDir L (famFunHat f) w, by
      rw [mem_AlDgList, Fin.init_snoc, Fin.snoc_last]
      exact ⟨hw, rfl⟩⟩

/-! ## 2. The two half-lines are `Ω`-sets with format `20` and degree `4` -/

/-- `AlGeE E = {u : ℝ | 2E ≤ u}` is an `Ω`-set of format `20` and degree `4`
(`Work.WilG5.leSet_mem` at dimension `1`). -/
theorem AlGeE_mem {S : WilkiesDesign.SOMin} (E : ℝ) : AlGeE E ∈ S.Ω 20 4 1 := by
  have h := Work.WilG5.leSet_mem (S := S) (0 : Fin 1) (2 * E)
  have h' := Work.WilG5.mem_mono (S := S) h 20 4 (by omega) (le_refl 4)
  simpa only [AlGeE] using h'

/-- `AlLeE E = {u : ℝ | u ≤ -2E}` is an `Ω`-set of format `20` and degree `4`
(`Work.WilG5.geSet_mem` at dimension `1`). -/
theorem AlLeE_mem {S : WilkiesDesign.SOMin} (E : ℝ) : AlLeE E ∈ S.Ω 20 4 1 := by
  have h := Work.WilG5.geSet_mem (S := S) (0 : Fin 1) (-(2 * E))
  have h' := Work.WilG5.mem_mono (S := S) h 20 4 (by omega) (le_refl 4)
  simpa only [AlLeE] using h'

/-! ## 3. The generic threshold set `projN 1 (AlDgList ∩ coordPre (AlSIdx N) A)` -/

/-- For any `Ω`-set `A ⊆ ℝ` of format `20` and degree `4`, the set
`projN 1 (AlDgList p n f L ∩ coordPre (AlSIdx (p+(n+1))) A)` is an `Ω`-set with exactly the
declared threshold bounds `AlFalt p n a1`, `AlDalt p n β`. -/
theorem AlAltSetMem {S : WilkiesDesign.SOMin} {p n a1 β : ℕ} {A : Set (Fin 1 → ℝ)}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} (L : List (Fin (p + (n + 1))))
    (hA : A ∈ S.Ω 20 4 1)
    (hDg : AlDgList p n f L ∈ S.Ω a1 β (p + (n + 1) + 1)) :
    projN 1 (AlDgList p n f L ∩ coordPre (AlSIdx (p + (n + 1))) A) ∈
      S.Ω (AlFalt p n a1) (AlDalt p n β) (p + (n + 1)) := by
  have hco : coordPre (AlSIdx (p + (n + 1))) A ∈
      S.Ω (20 + 64 * ((p + (n + 1) + 1) + 1) + 64)
          (4 + 32 * ((p + (n + 1) + 1) + 1) + 32) (p + (n + 1) + 1) :=
    Work.WilG5.coordPre_mem (S := S) (m := 1) (N := p + (n + 1) + 1) (F := 20) (D := 4)
      (ι := AlSIdx (p + (n + 1))) hA
  have hdg' : AlDgList p n f L ∈
      S.Ω (max a1 (20 + 64 * ((p + (n + 1) + 1) + 1) + 64)) β (p + (n + 1) + 1) :=
    Work.WilG5.mem_mono (S := S) hDg _ _ (le_max_left _ _) le_rfl
  have hco' : coordPre (AlSIdx (p + (n + 1))) A ∈
      S.Ω (max a1 (20 + 64 * ((p + (n + 1) + 1) + 1) + 64))
        (4 + 32 * ((p + (n + 1) + 1) + 1) + 32) (p + (n + 1) + 1) :=
    Work.WilG5.mem_mono (S := S) hco _ _ (le_max_right _ _) le_rfl
  have hI : AlDgList p n f L ∩ coordPre (AlSIdx (p + (n + 1))) A ∈
      S.Ω (max a1 (20 + 64 * ((p + (n + 1) + 1) + 1) + 64) + 1)
        (β + (4 + 32 * ((p + (n + 1) + 1) + 1) + 32)) (p + (n + 1) + 1) := by
    have h := S.inter (F := max a1 (20 + 64 * ((p + (n + 1) + 1) + 1) + 64))
      (n := p + (n + 1) + 1) (k := 2)
      (fun i : Fin 2 => if i = 0 then β else 4 + 32 * ((p + (n + 1) + 1) + 1) + 32)
      (fun i : Fin 2 => if i = 0 then AlDgList p n f L
        else coordPre (AlSIdx (p + (n + 1))) A)
      (by intro i; fin_cases i
          · simpa using hdg'
          · simpa using hco')
    rw [show (∑ i : Fin 2, (if i = 0 then β else 4 + 32 * ((p + (n + 1) + 1) + 1) + 32))
        = β + (4 + 32 * ((p + (n + 1) + 1) + 1) + 32) from by
      simp [Fin.sum_univ_two]] at h
    rwa [Work.WilG1.Omega.iInter_fin_two] at h
  have hP := Work.WilG5.projN_mem (S := S) (n := p + (n + 1)) 1
    (max a1 (20 + 64 * ((p + (n + 1) + 1) + 1) + 64) + 1)
    (β + (4 + 32 * ((p + (n + 1) + 1) + 1) + 32)) hI
  exact Work.WilG5.mem_mono (S := S) hP _ _
    (by simp only [AlFalt]; omega) (by simp only [AlDalt]; omega)

/-- The first threshold set is an `Ω`-set with the bounds `AlFalt`, `AlDalt`. -/
theorem AlAlt1_mem {S : WilkiesDesign.SOMin} {p n a1 β : ℕ} {E : ℝ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} (L : List (Fin (p + (n + 1))))
    (hDg : AlDgList p n f L ∈ S.Ω a1 β (p + (n + 1) + 1)) :
    AlAlt1 p n f L E ∈ S.Ω (AlFalt p n a1) (AlDalt p n β) (p + (n + 1)) :=
  AlAltSetMem (S := S) L (AlGeE_mem (S := S) E) hDg

/-- The second threshold set is an `Ω`-set with the bounds `AlFalt`, `AlDalt`. -/
theorem AlAlt2_mem {S : WilkiesDesign.SOMin} {p n a1 β : ℕ} {E : ℝ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} (L : List (Fin (p + (n + 1))))
    (hDg : AlDgList p n f L ∈ S.Ω a1 β (p + (n + 1) + 1)) :
    AlAlt2 p n f L E ∈ S.Ω (AlFalt p n a1) (AlDalt p n β) (p + (n + 1)) :=
  AlAltSetMem (S := S) L (AlLeE_mem (S := S) E) hDg

/-! ## 4. The threefold union of the threshold alternative -/

/-- `AlAlt1 ∪ AlAlt2 ∪ AlViolᶜ` is an `Ω`-set with the declared bounds `AlFu`, `AlDu`. -/
theorem AlUnionMem {S : WilkiesDesign.SOMin} {p n a1 β : ℕ} {E : ℝ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} (L : List (Fin (p + (n + 1))))
    (hDg : AlDgList p n f L ∈ S.Ω a1 β (p + (n + 1) + 1))
    (hViol : AlViol p n f L ∈
      S.Ω (AlFviol p n a1) (AlDviol p n β) (p + (n + 1))) :
    (AlAlt1 p n f L E ∪ AlAlt2 p n f L E ∪ (AlViol p n f L)ᶜ) ∈
      S.Ω (AlFu p n a1) (AlDu p n β) (p + (n + 1)) := by
  have h1 : AlAlt1 p n f L E ∈ S.Ω (AlFalt p n a1) (AlDalt p n β) (p + (n + 1)) :=
    AlAlt1_mem (S := S) L hDg
  have h2 : AlAlt2 p n f L E ∈ S.Ω (AlFalt p n a1) (AlDalt p n β) (p + (n + 1)) :=
    AlAlt2_mem (S := S) L hDg
  have h3 : (AlViol p n f L)ᶜ ∈
      S.Ω (AlFviol p n a1 + 1) (AlDviol p n β) (p + (n + 1)) := S.compl hViol
  have h1' : AlAlt1 p n f L E ∈ S.Ω (AlFu p n a1) (AlDalt p n β) (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) h1 _ _ (by simp only [AlFu]; omega) le_rfl
  have h2' : AlAlt2 p n f L E ∈ S.Ω (AlFu p n a1) (AlDalt p n β) (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) h2 _ _ (by simp only [AlFu]; omega) le_rfl
  have h3' : (AlViol p n f L)ᶜ ∈ S.Ω (AlFu p n a1) (AlDviol p n β) (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) h3 _ _ (by simp only [AlFu]; omega) le_rfl
  have hU := S.union (F := AlFu p n a1) (n := p + (n + 1)) (k := 3)
    (fun i : Fin 3 => ![AlDalt p n β, AlDalt p n β, AlDviol p n β] i)
    (fun i : Fin 3 => ![AlAlt1 p n f L E, AlAlt2 p n f L E, (AlViol p n f L)ᶜ] i)
    (by intro i; fin_cases i
        · simpa using h1'
        · simpa using h2'
        · simpa using h3')
  rw [show (∑ i : Fin 3, ![AlDalt p n β, AlDalt p n β, AlDviol p n β] i)
      = AlDalt p n β + AlDalt p n β + AlDviol p n β from by
    simp [Fin.sum_univ_three]] at hU
  rw [Work.WilkG4c.iUnion_fin_three (AlAlt1 p n f L E) (AlAlt2 p n f L E)
    ((AlViol p n f L)ᶜ)] at hU
  exact Work.WilG5.mem_mono (S := S) hU (AlFu p n a1) (AlDu p n β) le_rfl
    (by simp only [AlDu]; omega)

/-! ## 5. The selection set -/

theorem AlphaZsetMem {S : WilkiesDesign.SOMin} {p n a1 β : ℕ} {E : ℝ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} (L : List (Fin (p + (n + 1))))
    (hDg : Work.WilkG4c.AlDgList p n f L ∈ S.Ω a1 β (p + (n + 1) + 1))
    (hViol : Work.WilkG4c.AlViol p n f L ∈
      S.Ω (Work.WilkG4c.AlFviol p n a1) (Work.WilkG4c.AlDviol p n β) (p + (n + 1))) :
    Work.WilkG4c.AlZset p n f L E ∈
      S.Ω (Work.WilkG4c.AlFzs p n a1) (Work.WilkG4c.AlDzs p n β) (p + (n + 1)) := by
  -- the common format at which the three conjuncts are intersected
  let F3 : ℕ := max ((4 * n + 24) + 64 * ((p + (n + 1)) + n) + 64)
    (max (a1 + 1) (AlFu p n a1))
  -- the `C^{|L|}`-locus, as the projection of the derivative graph `AlDgList`
  have hloc : AlLoc p n f L.length ∈ S.Ω (a1 + 1) β (p + (n + 1)) := by
    rw [← projLast_AlDgList]
    exact S.proj hDg
  -- the cube coordinates
  have hcube : coordPre (yIdx p n) (openCube n) ∈
      S.Ω ((4 * n + 24) + 64 * ((p + (n + 1)) + n) + 64)
        ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) (p + (n + 1)) :=
    Work.WilG5.coordPre_mem (S := S) (m := n) (N := p + (n + 1)) (F := 4 * n + 24)
      (D := 16 * n + 16) (ι := yIdx p n) (Work.WilG5.openCube_mem (S := S) (n := n))
  -- the threshold alternative
  have hU := AlUnionMem (S := S) (E := E) L hDg hViol
  -- raise everything to the common format `F3`
  have hcube' : coordPre (yIdx p n) (openCube n) ∈
      S.Ω F3 ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) hcube F3 _ (by dsimp only [F3]; omega) le_rfl
  have hloc' : AlLoc p n f L.length ∈ S.Ω F3 β (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) hloc F3 _ (by dsimp only [F3]; omega) le_rfl
  have hU' : (AlAlt1 p n f L E ∪ AlAlt2 p n f L E ∪ (AlViol p n f L)ᶜ) ∈
      S.Ω F3 (AlDu p n β) (p + (n + 1)) :=
    Work.WilG5.mem_mono (S := S) hU F3 _ (by dsimp only [F3]; omega) le_rfl
  -- the threefold intersection
  have h3 := S.inter (F := F3) (n := p + (n + 1)) (k := 3)
    (fun i : Fin 3 => ![(16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32, β, AlDu p n β] i)
    (fun i : Fin 3 => ![coordPre (yIdx p n) (openCube n), AlLoc p n f L.length,
      (AlAlt1 p n f L E ∪ AlAlt2 p n f L E ∪ (AlViol p n f L)ᶜ)] i)
    (by intro i; fin_cases i
        · simpa using hcube'
        · simpa using hloc'
        · simpa using hU')
  rw [show (∑ i : Fin 3,
      ![(16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32, β, AlDu p n β] i)
      = ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) + β + AlDu p n β from by
    simp [Fin.sum_univ_three]] at h3
  rw [Work.WilkG4c.iInter_fin_three (coordPre (yIdx p n) (openCube n))
    (AlLoc p n f L.length)
    (AlAlt1 p n f L E ∪ AlAlt2 p n f L E ∪ (AlViol p n f L)ᶜ)] at h3
  have hZ : AlZset p n f L E ∈ S.Ω (F3 + 1)
      (((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32) + β + AlDu p n β)
      (p + (n + 1)) := by
    rw [show AlZset p n f L E =
        (coordPre (yIdx p n) (openCube n) ∩ AlLoc p n f L.length) ∩
          (AlAlt1 p n f L E ∪ AlAlt2 p n f L E ∪ (AlViol p n f L)ᶜ) from rfl]
    exact h3
  refine Work.WilG5.mem_mono (S := S) hZ (AlFzs p n a1) (AlDzs p n β) ?_ ?_
  · dsimp only [F3]; simp only [AlFzs]; omega
  · simp only [AlDzs]; omega

end Work.WilkG4c.Alpha

/-! ## 6. The same lemma under the path spelling of the area

The directory of this area is `Submission/Work/WilG4c` (spelling `WilG4c`), while the *namespaces*
of the area's modules — this file, `AlphaViolMem.lean`, `CurveFamAlpha.lean`, … — are spelled
`Work.WilkG4c` (with the `k`); a few older modules of the area use `Work.WilG4c`.  The two
spellings are different constants, and tools that derive a declaration name from the module path
(reading `Submission.Work.WilG4c.Alpha.AlphaZsetMem` and replacing the dots by the namespace
hierarchy) look for `Work.WilG4c.Alpha.AlphaZsetMem`.  So we provide the lemma under *both*
spellings; the second is a one-line application of the first, hence `#print axioms` of either
name reports the same three standard axioms. -/

namespace Work.WilG4c.Alpha

theorem AlphaZsetMem {S : WilkiesDesign.SOMin} {p n a1 β : ℕ} {E : ℝ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} (L : List (Fin (p + (n + 1))))
    (hDg : Work.WilkG4c.AlDgList p n f L ∈ S.Ω a1 β (p + (n + 1) + 1))
    (hViol : Work.WilkG4c.AlViol p n f L ∈
      S.Ω (Work.WilkG4c.AlFviol p n a1) (Work.WilkG4c.AlDviol p n β) (p + (n + 1))) :
    Work.WilkG4c.AlZset p n f L E ∈
      S.Ω (Work.WilkG4c.AlFzs p n a1) (Work.WilkG4c.AlDzs p n β) (p + (n + 1)) :=
  _root_.Work.WilkG4c.Alpha.AlphaZsetMem L hDg hViol

end Work.WilG4c.Alpha
