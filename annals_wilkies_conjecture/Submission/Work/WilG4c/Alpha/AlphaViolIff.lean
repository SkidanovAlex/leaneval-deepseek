/-
  WilG4c/Alpha — `AlphaViolIff`.

  The violation set `AlViol p n f L` of `CurveFamAlphaDefs` is defined as the projection onto
  `w` of the set `AlViol1` of quadruples `(w,y',s,s')` with `(w,s),(z',s') ∈ AlDgList`,
  `4 s² < s'²` and `y' ∈ openCube`, where `z' = zPt p n w y'` is `w` with its `y`-block
  replaced by `y'`.

  Here the projection is spelled out: since `AlDgList` is the graph of the iterated
  directional derivative `iterDir L (famFunHat f)` (`snoc_mem_AlDgList`), and since the
  `(y',s,s')`-block is exactly `Fin (n+2)`, a point `w` lies in `AlViol` iff there is
  `y' ∈ openCube n` such that `zPt p n w y'` lies in the interior of the `C^{|L|}`-locus and
  `2|∂^{α} f (w)| < |∂^{α} f (zPt p n w y')|` (with `4 a² < b² ↔ 2|a| < |b|`).

  The index-map bookkeeping is exactly that of `CurveFam/mem_badSet_iff` (which does the same
  for `badSet`/`DgSet`); we reuse its lemmas `comp_iwIdx`, `comp_izIdx`, `comp_icIdx`,
  `comp_cubeIdx`, `comp_zIdx`, `comp_zIdx_append`, `comp_cubeIdx_append`, `append_blkS`,
  `append_last`, `map_y`.
-/
import Mathlib
import Submission.Work.WilG4c.CurveFamAlphaDefs
import Submission.Work.WilG4c.CurveFam.mem_badSet_iff

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

open Classical

namespace Work.WilG4c.Alpha

open Work.WilG4c.CurveFam

/-- Membership in `cmpSet` (`4 a² < b²`) is the comparison `2|a| < |b|`. -/
theorem mem_cmpSet_iff (u : Fin 2 → ℝ) :
    u ∈ Work.WilkG4c.cmpSet ↔ 2 * |u 0| < |u 1| := by
  rw [Work.WilkG4c.cmpSet, Set.mem_ofPred_eq]
  constructor
  · intro h
    have h2 : (2 * u 0) ^ 2 < u 1 ^ 2 := by
      rw [show (2 * u 0) ^ 2 = 4 * u 0 ^ 2 by ring]
      exact h
    have habs := (sq_lt_sq (a := 2 * u 0) (b := u 1)).mp h2
    rwa [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] at habs
  · intro h
    have habs : |2 * u 0| < |u 1| := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      exact h
    have h2 := (sq_lt_sq (a := 2 * u 0) (b := u 1)).mpr habs
    rw [show (2 * u 0) ^ 2 = 4 * u 0 ^ 2 by ring] at h2
    exact h2

theorem AlphaViolIff {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) (w : Fin (p + (n + 1)) → ℝ) :
    w ∈ Work.WilkG4c.AlViol p n f L ↔ w ∈ Work.WilkG4c.AlLoc p n f L.length ∧
      ∃ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n ∧
        Work.WilkG4c.zPt p n w y' ∈ Work.WilkG4c.AlLoc p n f L.length ∧
        2 * |Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) w| <
          |Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) (Work.WilkG4c.zPt p n w y')| := by
  constructor
  · intro hw
    rw [Work.WilkG4c.AlViol, Work.WilG5.projN, Set.mem_ofPred_eq] at hw
    obtain ⟨v, hv⟩ := hw
    rw [Work.WilkG4c.AlViol1, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff] at hv
    obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := hv
    -- the `w`-block together with `s`
    have hA₁ : Fin.snoc w (v (Work.WilkG4c.blkS n)) ∈ Work.WilkG4c.AlDgList p n f L := by
      rw [← comp_iwIdx (p := p) (n := n) w v]
      exact hA
    have hA₂ : w ∈ Work.WilkG4c.AlLoc p n f L.length ∧
        v (Work.WilkG4c.blkS n) = Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) w :=
      Work.WilkG4c.snoc_mem_AlDgList.mp hA₁
    -- the `z' = (l,x,y')`-block together with `s'`
    have hB₁ : Fin.snoc ((Fin.append w v) ∘ (Work.WilkG4c.zIdx p n)) (v (Fin.last (n + 1)))
        ∈ Work.WilkG4c.AlDgList p n f L := by
      rw [← comp_izIdx (p := p) (n := n) w v]
      exact hB
    have hB₂ : Work.WilkG4c.zPt p n w (fun j : Fin n => v (Fin.castAdd 2 j))
          ∈ Work.WilkG4c.AlLoc p n f L.length ∧
        v (Fin.last (n + 1)) = Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f)
          (Work.WilkG4c.zPt p n w (fun j : Fin n => v (Fin.castAdd 2 j))) := by
      have h := hB₁
      rw [comp_zIdx (p := p) (n := n) w v] at h
      exact Work.WilkG4c.snoc_mem_AlDgList.mp h
    -- the comparison of the two derivative values
    have hC₁ : (Fin.cons (v (Work.WilkG4c.blkS n))
          (fun _ : Fin 1 => v (Fin.last (n + 1))) : Fin 2 → ℝ) ∈ Work.WilkG4c.cmpSet := by
      rw [← comp_icIdx (p := p) (n := n) w v]
      exact hC
    have hC₂ : 2 * |v (Work.WilkG4c.blkS n)| < |v (Fin.last (n + 1))| := by
      have h := (mem_cmpSet_iff
        (Fin.cons (v (Work.WilkG4c.blkS n)) (fun _ : Fin 1 => v (Fin.last (n + 1))))).mp hC₁
      simpa using h
    -- the `y'`-block
    have hD₁ : (fun j : Fin n => v (Fin.castAdd 2 j)) ∈ WilkiesDesign.openCube n := by
      rw [← comp_cubeIdx (p := p) (n := n) w v]
      exact hD
    refine ⟨hA₂.1, fun j : Fin n => v (Fin.castAdd 2 j), hD₁, hB₂.1, ?_⟩
    rw [← hA₂.2, ← hB₂.2]
    exact hC₂
  · rintro ⟨hLW, y', hy', hLZ, hineq⟩
    set u : Fin 2 → ℝ := Fin.cons (Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) w)
      (fun _ : Fin 1 => Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f)
        (Work.WilkG4c.zPt p n w y')) with hu
    have hblk : (Fin.append y' u) (Work.WilkG4c.blkS n) =
        Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) w := by
      rw [hu]
      exact append_blkS y' (Fin.cons (Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) w)
        (fun _ : Fin 1 => Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f)
          (Work.WilkG4c.zPt p n w y')))
    have hlast : (Fin.append y' u) (Fin.last (n + 1)) =
        Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) (Work.WilkG4c.zPt p n w y') := by
      rw [hu]
      exact append_last y' (Fin.cons (Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) w)
        (fun _ : Fin 1 => Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f)
          (Work.WilkG4c.zPt p n w y')))
    refine ⟨Fin.append y' u, ?_⟩
    rw [Work.WilkG4c.AlViol1, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · -- `(w,s) ∈ AlDgList`
      change (Fin.append w (Fin.append y' u)) ∘ (Work.WilkG4c.iwIdx p n)
        ∈ Work.WilkG4c.AlDgList p n f L
      rw [comp_iwIdx (p := p) (n := n) w (Fin.append y' u)]
      exact Work.WilkG4c.snoc_mem_AlDgList.mpr ⟨hLW, hblk⟩
    · -- `(zPt w y', s') ∈ AlDgList`
      change (Fin.append w (Fin.append y' u)) ∘ (Work.WilkG4c.izIdx p n)
        ∈ Work.WilkG4c.AlDgList p n f L
      rw [comp_izIdx (p := p) (n := n) w (Fin.append y' u),
        comp_zIdx_append (p := p) (n := n) w y' u]
      exact Work.WilkG4c.snoc_mem_AlDgList.mpr ⟨hLZ, hlast⟩
    · -- `4 s² < s'²`
      change (Fin.append w (Fin.append y' u)) ∘ (Work.WilkG4c.icIdx p n) ∈ Work.WilkG4c.cmpSet
      rw [comp_icIdx (p := p) (n := n) w (Fin.append y' u)]
      rw [Work.WilkG4c.cmpSet, Set.mem_ofPred_eq, hblk, hlast]
      have h4 : 4 * (Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) w) ^ 2 <
          (Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f)
            (Work.WilkG4c.zPt p n w y')) ^ 2 := by
        have habs : |2 * Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) w| <
            |Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f)
              (Work.WilkG4c.zPt p n w y')| := by
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
          exact hineq
        have h2 := (sq_lt_sq (a := 2 * Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) w)
          (b := Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f)
            (Work.WilkG4c.zPt p n w y'))).mpr habs
        rw [show (2 * Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) w) ^ 2 =
          4 * (Work.WilkG4c.iterDir L (Work.WilkG4c.famFunHat f) w) ^ 2 by ring] at h2
        exact h2
      simpa using h4
    · -- `y' ∈ openCube n`
      change (Fin.append w (Fin.append y' u)) ∘ (Work.WilkG4c.cubeIdx p n)
        ∈ WilkiesDesign.openCube n
      rw [comp_cubeIdx_append (p := p) (n := n) w y' u]
      exact hy'

end Work.WilG4c.Alpha
