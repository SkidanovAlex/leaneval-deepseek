/-
  WilG4c — `badSet_mem`: the selection set `badSet` of the `CurveFam` lemma is `Ω`-definable.

  `badSet p n f` is the projection (dropping the `y',s,s'`-block) of `badSet1 p n f`, which is
  the intersection of four pullbacks of `Ω`-sets of *lower* dimension:

  * `coordPre (iwIdx p n) (DgSet p n f)` and `coordPre (izIdx p n) (DgSet p n f)`, each a
    pullback of `DgSet` and hence controlled by the hypothesis `hDg`;
  * `coordPre (icIdx p n) cmpSet`, a pullback of the two-dimensional comparison set
    `4 a² < b²`, which is `Ω`-definable by the positivity of a degree-two polynomial
    (`Work.WilG1.Calc.pos_mem`);
  * `coordPre (cubeIdx p n) (openCube n)`, a pullback of the open unit cube
    (`Work.WilG5.openCube_mem`).

  Each operation of the `Ω`-calculus has an explicit format/degree cost
  (`Work.WilG5.coordPre_mem`, `SOMin.inter`, `Work.WilG5.projN_mem`); the loose constants
  `Fbad`, `Dbad` are chosen to dominate the resulting sums.  The proof is therefore pure
  bookkeeping in the frozen `Ω`-calculus.
-/
import Mathlib
import Submission.Work.WilG4c.CurveFamDefs
import Submission.Work.WilG1.Calc.pos_mem

namespace Work.WilG4c.CurveFam

open WilkiesDesign Work.WilkG4c Work.WilG5

/-- A binary sum over `Fin 2` of the `if`-selecting family. -/
theorem sum_two_nat (a b : ℕ) : (∑ i : Fin 2, (if i = 0 then a else b)) = a + b := by
  rw [Fin.sum_univ_two]; simp

/-- The comparison set `4 a² < b²` of `Work.WilkG4c.cmpSet` is an `Ω`-set, with the
format/degree bounds used by `badSet_mem`. -/
theorem cmpSet_two_mem (S : SOMin) : Work.WilkG4c.cmpSet ∈ S.Ω 4 4 2 := by
  set P : MvPolynomial (Fin 2) ℝ :=
    MvPolynomial.X (1 : Fin 2) ^ 2 - MvPolynomial.C (4 : ℝ) * MvPolynomial.X (0 : Fin 2) ^ 2
    with hPdef
  have hP : P.totalDegree ≤ 2 := by
    rw [hPdef]
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    constructor
    · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
      rw [MvPolynomial.totalDegree_X]
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : (MvPolynomial.C (4 : ℝ) : MvPolynomial (Fin 2) ℝ).totalDegree = 0 :=
        MvPolynomial.totalDegree_C 4
      have h2 : (MvPolynomial.X (0 : Fin 2) ^ 2 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2 := by
        refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
        rw [MvPolynomial.totalDegree_X]
      omega
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := 2) 0 P
  have hset : {x : Fin 2 → ℝ | 0 < MvPolynomial.eval x P} = Work.WilkG4c.cmpSet := by
    ext u
    rw [hPdef]
    simp only [Work.WilkG4c.cmpSet, Set.mem_ofPred_eq]
    simp only [MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X,
      MvPolynomial.eval_mul, MvPolynomial.eval_C]
    constructor
    · intro h; nlinarith [h]
    · intro h; nlinarith [h]
  rw [← hset]
  refine Work.WilG1.Omega.mono h le_rfl ?_
  simpa using hP

theorem badSet_mem {S : WilkiesDesign.SOMin} {p n a1 L : ℕ}
    {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    (hDg : Work.WilkG4c.DgSet p n f ∈ S.Ω a1 L (p + (n + 1) + 1)) :
    Work.WilkG4c.badSet p n f ∈ S.Ω (Work.WilkG4c.Fbad p n a1) (Work.WilkG4c.Dbad p n L) (p + (n + 1)) := by
  -- ambient dimension `N = p + (n+1) + n + 2`, and the dimension `m = p + (n+1) + 1` of
  -- the `(w,s)`-block carrying the two copies of `DgSet`.
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
  let dD : ℕ := L + eA
  let dCm : ℕ := 4 + eC
  let dY : ℕ := (16 * n + 16) + eY
  -- common format
  let Fg : ℕ := max (a1 + cA) (max (4 + cC) ((4 * n + 24) + cY))
  -- (1) the four `coordPre` blocks
  have h1 : coordPre (iwIdx p n) (DgSet p n f) ∈ S.Ω (a1 + cA) dD N := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := m) (N := N) (ι := iwIdx p n) (h := hDg)
    refine Work.WilG5.mem_mono h (a1 + cA) dD ?_ ?_
    · dsimp only [cA]; omega
    · dsimp only [dD, eA]; omega
  have h2 : coordPre (izIdx p n) (DgSet p n f) ∈ S.Ω (a1 + cA) dD N := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := m) (N := N) (ι := izIdx p n) (h := hDg)
    refine Work.WilG5.mem_mono h (a1 + cA) dD ?_ ?_
    · dsimp only [cA]; omega
    · dsimp only [dD, eA]; omega
  have h3 : coordPre (icIdx p n) cmpSet ∈ S.Ω (4 + cC) dCm N := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := 2) (N := N) (ι := icIdx p n)
      (h := cmpSet_two_mem S)
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
  have h1g : coordPre (iwIdx p n) (DgSet p n f) ∈ S.Ω Fg dD N :=
    Work.WilG5.mem_mono h1 Fg dD (by dsimp only [Fg]; omega) le_rfl
  have h2g : coordPre (izIdx p n) (DgSet p n f) ∈ S.Ω Fg dD N :=
    Work.WilG5.mem_mono h2 Fg dD (by dsimp only [Fg]; omega) le_rfl
  have h3g : coordPre (icIdx p n) cmpSet ∈ S.Ω Fg dCm N :=
    Work.WilG5.mem_mono h3 Fg dCm (by dsimp only [Fg]; omega) le_rfl
  have h4g : coordPre (cubeIdx p n) (openCube n) ∈ S.Ω Fg dY N :=
    Work.WilG5.mem_mono h4 Fg dY (by dsimp only [Fg]; omega) le_rfl
  -- (3) the three pairwise intersections, matching the nesting of `badSet1`
  have h12 : coordPre (iwIdx p n) (DgSet p n f) ∩ coordPre (izIdx p n) (DgSet p n f) ∈
      S.Ω (Fg + 1) (dD + dD) N := by
    have h := S.inter (F := Fg) (n := N) (k := 2)
      (fun i : Fin 2 => if i = 0 then dD else dD)
      (fun i : Fin 2 => if i = 0 then coordPre (iwIdx p n) (DgSet p n f)
        else coordPre (izIdx p n) (DgSet p n f))
      (by intro i; fin_cases i
          · simpa using h1g
          · simpa using h2g)
    rw [sum_two_nat dD dD] at h
    rwa [Work.WilG1.Omega.iInter_fin_two _ _] at h
  have h123 : (coordPre (iwIdx p n) (DgSet p n f) ∩ coordPre (izIdx p n) (DgSet p n f)) ∩
      coordPre (icIdx p n) cmpSet ∈ S.Ω (Fg + 2) ((dD + dD) + dCm) N := by
    have h12' : coordPre (iwIdx p n) (DgSet p n f) ∩ coordPre (izIdx p n) (DgSet p n f) ∈
        S.Ω (Fg + 1) (dD + dD) N := h12
    have h3' : coordPre (icIdx p n) cmpSet ∈ S.Ω (Fg + 1) dCm N :=
      Work.WilG5.mem_mono h3g (Fg + 1) dCm (by omega) le_rfl
    have h := S.inter (F := Fg + 1) (n := N) (k := 2)
      (fun i : Fin 2 => if i = 0 then (dD + dD) else dCm)
      (fun i : Fin 2 => if i = 0 then
          (coordPre (iwIdx p n) (DgSet p n f) ∩ coordPre (izIdx p n) (DgSet p n f))
        else coordPre (icIdx p n) cmpSet)
      (by intro i; fin_cases i
          · simpa using h12'
          · simpa using h3')
    rw [sum_two_nat (dD + dD) dCm] at h
    rwa [Work.WilG1.Omega.iInter_fin_two _ _] at h
  have h1234 : ((coordPre (iwIdx p n) (DgSet p n f) ∩ coordPre (izIdx p n) (DgSet p n f)) ∩
      coordPre (icIdx p n) cmpSet) ∩ coordPre (cubeIdx p n) (openCube n) ∈
      S.Ω (Fg + 3) (((dD + dD) + dCm) + dY) N := by
    have h123' : (coordPre (iwIdx p n) (DgSet p n f) ∩ coordPre (izIdx p n) (DgSet p n f)) ∩
        coordPre (icIdx p n) cmpSet ∈ S.Ω (Fg + 2) ((dD + dD) + dCm) N := h123
    have h4' : coordPre (cubeIdx p n) (openCube n) ∈ S.Ω (Fg + 2) dY N :=
      Work.WilG5.mem_mono h4g (Fg + 2) dY (by omega) le_rfl
    have h := S.inter (F := Fg + 2) (n := N) (k := 2)
      (fun i : Fin 2 => if i = 0 then ((dD + dD) + dCm) else dY)
      (fun i : Fin 2 => if i = 0 then
          ((coordPre (iwIdx p n) (DgSet p n f) ∩ coordPre (izIdx p n) (DgSet p n f)) ∩
            coordPre (icIdx p n) cmpSet)
        else coordPre (cubeIdx p n) (openCube n))
      (by intro i; fin_cases i
          · simpa using h123'
          · simpa using h4')
    rw [sum_two_nat ((dD + dD) + dCm) dY] at h
    rwa [Work.WilG1.Omega.iInter_fin_two _ _] at h
  -- (4) `badSet1` is exactly this nested intersection
  have hbad1 : Work.WilkG4c.badSet1 p n f ∈ S.Ω (Fg + 3) (((dD + dD) + dCm) + dY) N := by
    simpa only [Work.WilkG4c.badSet1] using h1234
  -- (5) project the `y',s,s'`-block: format `+ (n+2)`, degree unchanged
  have hproj : projN (n + 2) (Work.WilkG4c.badSet1 p n f) ∈
      S.Ω (Fg + 3 + (n + 2)) (((dD + dD) + dCm) + dY) (p + (n + 1)) := by
    have h := Work.WilG5.projN_mem (S := S) (n := p + (n + 1)) (n + 2) (Fg + 3)
      (((dD + dD) + dCm) + dY) hbad1
    simpa using h
  -- (6) `badSet` is that projection, and the loose bounds `Fbad`, `Dbad` dominate.
  rw [show Work.WilkG4c.badSet p n f = projN (n + 2) (Work.WilkG4c.badSet1 p n f) from rfl]
  refine Work.WilG5.mem_mono hproj (Work.WilkG4c.Fbad p n a1) (Work.WilkG4c.Dbad p n L) ?_ ?_
  · dsimp only [Work.WilkG4c.Fbad, Fg, cA, cC, cY, N, m]; omega
  · dsimp only [Work.WilkG4c.Dbad, dD, dCm, dY, eA, eC, eY, N, m]; omega

end Work.WilG4c.CurveFam
