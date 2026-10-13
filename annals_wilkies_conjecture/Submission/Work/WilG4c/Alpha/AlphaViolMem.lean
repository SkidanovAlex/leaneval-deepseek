/-
  WilG4c/Alpha — `AlphaViolMem`: the violation set `AlViol` of the `CurveFamAlpha` selection
  set is `Ω`-definable whenever its order-`|L|` derivative graph `AlDgList` is.

  `AlViol p n f L` is the projection (dropping the `y',s,s'`-block) of `AlViol1 p n f L`, the
  intersection of four pullbacks of `Ω`-sets of *lower* dimension:

  * `coordPre (iwIdx p n) (AlDgList p n f L)` and `coordPre (izIdx p n) (AlDgList p n f L)`,
    each a pullback of `AlDgList` and hence controlled by the hypothesis `hDg`;
  * `coordPre (icIdx p n) cmpSet`, a pullback of the two-dimensional comparison set
    `4 a² < b²` (`CurveFam.cmpSet_two_mem`);
  * `coordPre (cubeIdx p n) (openCube n)`, a pullback of the open unit cube
    (`Work.WilG5.openCube_mem`).

  This is the order-`|L|` analogue of `CurveFam.badSet_mem` (there with `DgSet` in place of
  `AlDgList`); the same `Ω`-bookkeeping applies, and the loose constants `AlFviol`, `AlDviol`
  are chosen to dominate the resulting sums.
-/
import Mathlib
import Submission.Work.WilG4c.CurveFamAlphaDefs
import Submission.Work.WilG4c.CurveFam.badSet_mem

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical

namespace Work.WilG4c.Alpha

open WilkiesDesign Work.WilkG4c Work.WilG5

theorem AlphaViolMem {S : WilkiesDesign.SOMin} {p n a1 β : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ} (L : List (Fin (p + (n + 1))))
    (hDg : Work.WilkG4c.AlDgList p n f L ∈ S.Ω a1 β (p + (n + 1) + 1)) :
    Work.WilkG4c.AlViol p n f L ∈
      S.Ω (Work.WilkG4c.AlFviol p n a1) (Work.WilkG4c.AlDviol p n β) (p + (n + 1)) := by
  -- ambient dimension `N = p + (n+1) + n + 2`, and the dimension `m = p + (n+1) + 1` of
  -- the `(w,s)`-block carrying the two copies of `AlDgList`.
  let N : ℕ := p + (n + 1) + n + 2
  let m : ℕ := p + (n + 1) + 1
  -- format/degree increments of the four `coordPre` pullbacks
  let cA : ℕ := 64 * (N + m) + 64
  let eA : ℕ := 32 * (N + m) + 32
  let cC : ℕ := 64 * (N + 2) + 64
  let eC : ℕ := 32 * (N + 2) + 32
  let cY : ℕ := 64 * (N + n) + 64
  let eY : ℕ := 32 * (N + n) + 32
  -- degrees of the four blocks
  let dD : ℕ := β + eA
  let dCm : ℕ := 4 + eC
  let dY : ℕ := (16 * n + 16) + eY
  -- common format
  let Fg : ℕ := max (a1 + cA) (max (4 + cC) ((4 * n + 24) + cY))
  -- (1) the four `coordPre` blocks
  have h1 : coordPre (iwIdx p n) (AlDgList p n f L) ∈ S.Ω (a1 + cA) dD N := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := m) (N := N) (ι := iwIdx p n) (h := hDg)
    refine Work.WilG5.mem_mono h (a1 + cA) dD ?_ ?_
    · dsimp only [cA]; omega
    · dsimp only [dD, eA]; omega
  have h2 : coordPre (izIdx p n) (AlDgList p n f L) ∈ S.Ω (a1 + cA) dD N := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := m) (N := N) (ι := izIdx p n) (h := hDg)
    refine Work.WilG5.mem_mono h (a1 + cA) dD ?_ ?_
    · dsimp only [cA]; omega
    · dsimp only [dD, eA]; omega
  have h3 : coordPre (icIdx p n) Work.WilkG4c.cmpSet ∈ S.Ω (4 + cC) dCm N := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := 2) (N := N) (ι := icIdx p n)
      (h := Work.WilG4c.CurveFam.cmpSet_two_mem S)
    refine Work.WilG5.mem_mono h (4 + cC) dCm ?_ ?_
    · dsimp only [cC]; omega
    · dsimp only [dCm, eC]; omega
  have h4 : coordPre (cubeIdx p n) (openCube n) ∈ S.Ω ((4 * n + 24) + cY) dY N := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := n) (N := N) (ι := cubeIdx p n)
      (h := Work.WilG5.openCube_mem (S := S) (n := n))
    refine Work.WilG5.mem_mono h ((4 * n + 24) + cY) dY ?_ ?_
    · dsimp only [cY]; omega
    · dsimp only [dY, eY]; omega
  -- (2) raise all four to the common format
  have h1g : coordPre (iwIdx p n) (AlDgList p n f L) ∈ S.Ω Fg dD N :=
    Work.WilG5.mem_mono h1 Fg dD (by dsimp only [Fg]; omega) le_rfl
  have h2g : coordPre (izIdx p n) (AlDgList p n f L) ∈ S.Ω Fg dD N :=
    Work.WilG5.mem_mono h2 Fg dD (by dsimp only [Fg]; omega) le_rfl
  have h3g : coordPre (icIdx p n) Work.WilkG4c.cmpSet ∈ S.Ω Fg dCm N :=
    Work.WilG5.mem_mono h3 Fg dCm (by dsimp only [Fg]; omega) le_rfl
  have h4g : coordPre (cubeIdx p n) (openCube n) ∈ S.Ω Fg dY N :=
    Work.WilG5.mem_mono h4 Fg dY (by dsimp only [Fg]; omega) le_rfl
  -- (3) the three pairwise intersections, matching the nesting of `AlViol1`
  have h12 : coordPre (iwIdx p n) (AlDgList p n f L) ∩ coordPre (izIdx p n) (AlDgList p n f L) ∈
      S.Ω (Fg + 1) (dD + dD) N := by
    have h := S.inter (F := Fg) (n := N) (k := 2)
      (fun i : Fin 2 => if i = 0 then dD else dD)
      (fun i : Fin 2 => if i = 0 then coordPre (iwIdx p n) (AlDgList p n f L)
        else coordPre (izIdx p n) (AlDgList p n f L))
      (by intro i; fin_cases i
          · simpa using h1g
          · simpa using h2g)
    rw [Work.WilG4c.CurveFam.sum_two_nat dD dD] at h
    rwa [Work.WilG1.Omega.iInter_fin_two _ _] at h
  have h123 : (coordPre (iwIdx p n) (AlDgList p n f L) ∩
        coordPre (izIdx p n) (AlDgList p n f L)) ∩
      coordPre (icIdx p n) Work.WilkG4c.cmpSet ∈ S.Ω (Fg + 2) ((dD + dD) + dCm) N := by
    have h12' : coordPre (iwIdx p n) (AlDgList p n f L) ∩
        coordPre (izIdx p n) (AlDgList p n f L) ∈ S.Ω (Fg + 1) (dD + dD) N := h12
    have h3' : coordPre (icIdx p n) Work.WilkG4c.cmpSet ∈ S.Ω (Fg + 1) dCm N :=
      Work.WilG5.mem_mono h3g (Fg + 1) dCm (by omega) le_rfl
    have h := S.inter (F := Fg + 1) (n := N) (k := 2)
      (fun i : Fin 2 => if i = 0 then (dD + dD) else dCm)
      (fun i : Fin 2 => if i = 0 then
          (coordPre (iwIdx p n) (AlDgList p n f L) ∩ coordPre (izIdx p n) (AlDgList p n f L))
        else coordPre (icIdx p n) Work.WilkG4c.cmpSet)
      (by intro i; fin_cases i
          · simpa using h12'
          · simpa using h3')
    rw [Work.WilG4c.CurveFam.sum_two_nat (dD + dD) dCm] at h
    rwa [Work.WilG1.Omega.iInter_fin_two _ _] at h
  have h1234 : ((coordPre (iwIdx p n) (AlDgList p n f L) ∩
        coordPre (izIdx p n) (AlDgList p n f L)) ∩
      coordPre (icIdx p n) Work.WilkG4c.cmpSet) ∩ coordPre (cubeIdx p n) (openCube n) ∈
      S.Ω (Fg + 3) (((dD + dD) + dCm) + dY) N := by
    have h123' : (coordPre (iwIdx p n) (AlDgList p n f L) ∩
        coordPre (izIdx p n) (AlDgList p n f L)) ∩
        coordPre (icIdx p n) Work.WilkG4c.cmpSet ∈ S.Ω (Fg + 2) ((dD + dD) + dCm) N := h123
    have h4' : coordPre (cubeIdx p n) (openCube n) ∈ S.Ω (Fg + 2) dY N :=
      Work.WilG5.mem_mono h4g (Fg + 2) dY (by omega) le_rfl
    have h := S.inter (F := Fg + 2) (n := N) (k := 2)
      (fun i : Fin 2 => if i = 0 then ((dD + dD) + dCm) else dY)
      (fun i : Fin 2 => if i = 0 then
          ((coordPre (iwIdx p n) (AlDgList p n f L) ∩
            coordPre (izIdx p n) (AlDgList p n f L)) ∩
            coordPre (icIdx p n) Work.WilkG4c.cmpSet)
        else coordPre (cubeIdx p n) (openCube n))
      (by intro i; fin_cases i
          · simpa using h123'
          · simpa using h4')
    rw [Work.WilG4c.CurveFam.sum_two_nat ((dD + dD) + dCm) dY] at h
    rwa [Work.WilG1.Omega.iInter_fin_two _ _] at h
  -- (4) `AlViol1` is exactly this nested intersection
  have hviol1 : Work.WilkG4c.AlViol1 p n f L ∈ S.Ω (Fg + 3) (((dD + dD) + dCm) + dY) N := by
    simpa only [Work.WilkG4c.AlViol1] using h1234
  -- (5) project the `y',s,s'`-block: format `+ (n+2)`, degree unchanged
  have hproj : projN (n + 2) (Work.WilkG4c.AlViol1 p n f L) ∈
      S.Ω (Fg + 3 + (n + 2)) (((dD + dD) + dCm) + dY) (p + (n + 1)) := by
    have h := Work.WilG5.projN_mem (S := S) (n := p + (n + 1)) (n + 2) (Fg + 3)
      (((dD + dD) + dCm) + dY) hviol1
    simpa using h
  -- (6) `AlViol` is that projection, and the loose bounds `AlFviol`, `AlDviol` dominate.
  rw [show Work.WilkG4c.AlViol p n f L = projN (n + 2) (Work.WilkG4c.AlViol1 p n f L) from rfl]
  refine Work.WilG5.mem_mono hproj (Work.WilkG4c.AlFviol p n a1) (Work.WilkG4c.AlDviol p n β)
    ?_ ?_
  · dsimp only [Work.WilkG4c.AlFviol, Fg, cA, cC, cY, N, m]; omega
  · dsimp only [Work.WilkG4c.AlDviol, dD, dCm, dY, eA, eC, eY, N, m]; omega

end Work.WilG4c.Alpha
