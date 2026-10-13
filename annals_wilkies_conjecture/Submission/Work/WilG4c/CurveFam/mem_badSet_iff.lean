/-
  WilG4c/CurveFam — `mem_badSet_iff`.

  The selection set `badSet p n f` of the `CurveFam` lemma is defined as the projection onto
  `w` of the set `badSet1` of quadruples `(w,y',s,s')` with `(w,s),(z',s') ∈ DgSet`,
  `4 s² < s'²` and `y' ∈ openCube`, where `z'` is `w` with its `y`-block replaced by `y'`.

  Here we spell the projection out: since `DgSet` is the graph of the `x`-derivative
  (`dgVal_eq_xDer`), and since the `(y',s,s')`-block is exactly `Fin (n+2)`, a point `w` lies in
  `badSet` iff there is `y' ∈ openCube n` such that `(w,zPt w y')` lies in the `C¹` locus and
  `4 (∂₀f w)² < (∂₀f (zPt w y'))²`.
-/
import Mathlib
import Submission.Work.WilG4c.CurveFamDefs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical

namespace Work.WilkG4c

/-- The value attached by `DgSet` to a point of the `C¹` locus is its `x`-derivative. -/
theorem dgVal_eq_xDer {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (z : Fin (p + (n + 1)) → ℝ) :
    iteratedFDeriv ℝ 1 (famFunHat f) z (fun _ : Fin 1 => Pi.single (xDirHat p n) 1) =
      xDer p n f z := by
  rw [xDer, iteratedFDeriv_one_apply]

end Work.WilkG4c

namespace Work.WilG4c.CurveFam

open Work.WilkG4c

variable {p n : ℕ}

/-! ## Elementary facts about the index maps -/

/-- The coordinate of `s` in the block `Fin (n+2)` (`=(y',s,s')`) is `n`. -/
lemma blkS_eq_natAdd_zero (n : ℕ) : blkS n = Fin.natAdd n (0 : Fin 2) := by
  ext; simp [blkS]

/-- The coordinate of `s'` in the block `Fin (n+2)` is the last one. -/
lemma last_eq_natAdd_last (n : ℕ) : Fin.last (n + 1) = Fin.natAdd n (Fin.last 1) :=
  Fin.natAdd_last

/-- `Fin.last 1` is `1` in `Fin 2`. -/
lemma fin_last_one : (Fin.last 1 : Fin 2) = 1 := Fin.ext rfl

/-- The two coordinates of `Fin.cons a (fun _ => b) : Fin 2 → ℝ`. -/
lemma cons_zero_val (a b : ℝ) : (Fin.cons a (fun _ : Fin 1 => b) : Fin 2 → ℝ) 0 = a := by simp

lemma cons_one_val (a b : ℝ) : (Fin.cons a (fun _ : Fin 1 => b) : Fin 2 → ℝ) 1 = b := by simp

/-- The values of the block `(y',s,s') = Fin.append y' u` at its three parts. -/
lemma append_blkS (y' : Fin n → ℝ) (u : Fin 2 → ℝ) :
    (Fin.append y' u) (blkS n) = u 0 := by
  rw [blkS_eq_natAdd_zero n, Fin.append_right]

lemma append_last (y' : Fin n → ℝ) (u : Fin 2 → ℝ) :
    (Fin.append y' u) (Fin.last (n + 1)) = u 1 := by
  rw [last_eq_natAdd_last n, Fin.append_right, fin_last_one]

lemma append_castAdd (y' : Fin n → ℝ) (u : Fin 2 → ℝ) (j : Fin n) :
    (Fin.append y' u) (Fin.castAdd 2 j) = y' j :=
  Fin.append_left y' u j

/-- The `y'`-part of a point of the form `Fin.append y' u` is `y'`. -/
lemma map_y (y' : Fin n → ℝ) (u : Fin 2 → ℝ) :
    (fun j : Fin n => (Fin.append y' u) (Fin.castAdd 2 j)) = y' := by
  funext j; exact Fin.append_left y' u j

/-! ## Reading the four index maps through `Fin.append w v` -/

/-- `iwIdx` read through `Fin.append w v`: the block `w` together with `s`. -/
lemma comp_iwIdx (w : Fin (p + (n + 1)) → ℝ) (v : Fin (n + 2) → ℝ) :
    (Fin.append w v) ∘ (iwIdx p n) = Fin.snoc w (v (blkS n)) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [Function.comp_apply, iwIdx, Fin.snoc_last]
    rw [sPos, Fin.append_right]
  · intro j; simp [iwIdx]

/-- `izIdx` read through `Fin.append w v`: the block `z' = (l,x,y')` together with `s'`. -/
lemma comp_izIdx (w : Fin (p + (n + 1)) → ℝ) (v : Fin (n + 2) → ℝ) :
    (Fin.append w v) ∘ (izIdx p n) =
      Fin.snoc ((Fin.append w v) ∘ (zIdx p n)) (v (Fin.last (n + 1))) := by
  rw [izIdx, Fin.comp_snoc]
  congr 1
  rw [sPos', Fin.append_right]

/-- `icIdx` read through `Fin.append w v`: the two derivative values `(s,s')`. -/
lemma comp_icIdx (w : Fin (p + (n + 1)) → ℝ) (v : Fin (n + 2) → ℝ) :
    (Fin.append w v) ∘ (icIdx p n) =
      (Fin.cons (v (blkS n)) (fun _ : Fin 1 => v (Fin.last (n + 1))) : Fin 2 → ℝ) := by
  funext k
  refine Fin.cases ?_ ?_ k
  · simp only [Function.comp_apply, icIdx, Fin.cons_zero]
    rw [sPos, Fin.append_right]
  · intro k'
    simp only [Function.comp_apply, icIdx, Fin.cons_succ]
    rw [sPos', Fin.append_right]

/-- `cubeIdx` read through `Fin.append w v`: the block `y'`. -/
lemma comp_cubeIdx (w : Fin (p + (n + 1)) → ℝ) (v : Fin (n + 2) → ℝ) :
    (Fin.append w v) ∘ (cubeIdx p n) = (fun j : Fin n => v (Fin.castAdd 2 j)) := by
  funext j; simp [cubeIdx, Function.comp_apply]

/-- `zIdx` read through `Fin.append w v`: the point `zPt` obtained from `w` by replacing its
`y`-block by the `y'`-block of `v`. -/
lemma comp_zIdx (w : Fin (p + (n + 1)) → ℝ) (v : Fin (n + 2) → ℝ) :
    (Fin.append w v) ∘ (zIdx p n) = zPt p n w (fun j : Fin n => v (Fin.castAdd 2 j)) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [zIdx, zPt, Function.comp_apply]
  · intro j
    refine Fin.cases ?_ ?_ j
    · simp [zIdx, zPt, Function.comp_apply]
    · intro k; simp [zIdx, zPt, Function.comp_apply]

/-- The two specialisations of `comp_zIdx` and `comp_cubeIdx` used in the backwards direction,
where the ambient point is `Fin.append w (Fin.append y' u)`. -/
lemma comp_zIdx_append (w : Fin (p + (n + 1)) → ℝ) (y' : Fin n → ℝ) (u : Fin 2 → ℝ) :
    (Fin.append w (Fin.append y' u)) ∘ (zIdx p n) = zPt p n w y' := by
  rw [comp_zIdx (p := p) (n := n) w (Fin.append y' u), map_y y' u]

lemma comp_cubeIdx_append (w : Fin (p + (n + 1)) → ℝ) (y' : Fin n → ℝ) (u : Fin 2 → ℝ) :
    (Fin.append w (Fin.append y' u)) ∘ (cubeIdx p n) = y' := by
  rw [comp_cubeIdx (p := p) (n := n) w (Fin.append y' u), map_y y' u]

/-! ## The description of `badSet` -/

theorem mem_badSet_iff {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (w : Fin (p + (n + 1)) → ℝ) :
    w ∈ Work.WilkG4c.badSet p n f ↔ ∃ y' : Fin n → ℝ, y' ∈ WilkiesDesign.openCube n ∧
      w ∈ Work.WilkG4c.LocSet p n f ∧
      Work.WilkG4c.zPt p n w y' ∈ Work.WilkG4c.LocSet p n f ∧
      4 * (Work.WilkG4c.xDer p n f w) ^ 2 < (Work.WilkG4c.xDer p n f (Work.WilkG4c.zPt p n w y')) ^ 2 := by
  constructor
  · intro hw
    rw [badSet, Work.WilG5.projN, Set.mem_ofPred_eq] at hw
    obtain ⟨v, hv⟩ := hw
    rw [badSet1, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff] at hv
    obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := hv
    -- the `w`-block together with `s`
    have hA₁ : Fin.snoc w (v (blkS n)) ∈ DgSet p n f := by
      rw [← comp_iwIdx (p := p) (n := n) w v]
      exact hA
    have hA₂ : w ∈ LocSet p n f ∧
        v (blkS n) = iteratedFDeriv ℝ 1 (famFunHat f) w
          (fun _ : Fin 1 => Pi.single (xDirHat p n) 1) := by
      have h := hA₁
      rw [DgSet, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at h
      exact h
    -- the `z' = (l,x,y')`-block together with `s'`
    have hB₁ : Fin.snoc ((Fin.append w v) ∘ (zIdx p n)) (v (Fin.last (n + 1))) ∈ DgSet p n f := by
      rw [← comp_izIdx (p := p) (n := n) w v]
      exact hB
    have hB₂ : zPt p n w (fun j : Fin n => v (Fin.castAdd 2 j)) ∈ LocSet p n f ∧
        v (Fin.last (n + 1)) = iteratedFDeriv ℝ 1 (famFunHat f)
          (zPt p n w (fun j : Fin n => v (Fin.castAdd 2 j)))
          (fun _ : Fin 1 => Pi.single (xDirHat p n) 1) := by
      have h := hB₁
      rw [comp_zIdx (p := p) (n := n) w v, DgSet, Set.mem_ofPred_eq, Fin.init_snoc,
        Fin.snoc_last] at h
      exact h
    -- the comparison of the two derivative values
    have hC₁ : (Fin.cons (v (blkS n)) (fun _ : Fin 1 => v (Fin.last (n + 1))) : Fin 2 → ℝ)
        ∈ cmpSet := by
      rw [← comp_icIdx (p := p) (n := n) w v]
      exact hC
    have hC₂ : 4 * (v (blkS n)) ^ 2 < (v (Fin.last (n + 1))) ^ 2 := by
      have h := hC₁
      rw [cmpSet, Set.mem_ofPred_eq] at h
      simpa using h
    -- the `y'`-block
    have hD₁ : (fun j : Fin n => v (Fin.castAdd 2 j)) ∈ WilkiesDesign.openCube n := by
      rw [← comp_cubeIdx (p := p) (n := n) w v]
      exact hD
    have hs : v (blkS n) = xDer p n f w := by rw [hA₂.2, dgVal_eq_xDer]
    have hs' : v (Fin.last (n + 1)) =
        xDer p n f (zPt p n w (fun j : Fin n => v (Fin.castAdd 2 j))) := by
      rw [hB₂.2, dgVal_eq_xDer]
    refine ⟨fun j : Fin n => v (Fin.castAdd 2 j), hD₁, hA₂.1, hB₂.1, ?_⟩
    rw [hs, hs'] at hC₂
    exact hC₂
  · rintro ⟨y', hy', hLW, hLZ, hineq⟩
    set u : Fin 2 → ℝ := Fin.cons (xDer p n f w) (fun _ : Fin 1 => xDer p n f (zPt p n w y'))
      with hu
    have hblk : (Fin.append y' u) (blkS n) = xDer p n f w := by
      rw [hu]
      exact append_blkS y' (Fin.cons (xDer p n f w) (fun _ : Fin 1 => xDer p n f (zPt p n w y')))
    have hlast : (Fin.append y' u) (Fin.last (n + 1)) = xDer p n f (zPt p n w y') := by
      rw [hu]
      exact append_last y' (Fin.cons (xDer p n f w) (fun _ : Fin 1 => xDer p n f (zPt p n w y')))
    refine ⟨Fin.append y' u, ?_⟩
    rw [badSet1, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · -- `(w,s) ∈ DgSet`
      change (Fin.append w (Fin.append y' u)) ∘ (iwIdx p n) ∈ DgSet p n f
      rw [comp_iwIdx (p := p) (n := n) w (Fin.append y' u)]
      rw [DgSet, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
      exact ⟨hLW, by rw [hblk, dgVal_eq_xDer]⟩
    · -- `(zPt w y', s') ∈ DgSet`
      change (Fin.append w (Fin.append y' u)) ∘ (izIdx p n) ∈ DgSet p n f
      rw [comp_izIdx (p := p) (n := n) w (Fin.append y' u),
        comp_zIdx_append (p := p) (n := n) w y' u]
      rw [DgSet, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
      exact ⟨hLZ, by rw [hlast, dgVal_eq_xDer]⟩
    · -- `4 s² < s'²`
      change (Fin.append w (Fin.append y' u)) ∘ (icIdx p n) ∈ cmpSet
      rw [comp_icIdx (p := p) (n := n) w (Fin.append y' u)]
      rw [cmpSet, Set.mem_ofPred_eq, hblk, hlast]
      simpa using hineq
    · -- `y' ∈ openCube n`
      change (Fin.append w (Fin.append y' u)) ∘ (cubeIdx p n) ∈ WilkiesDesign.openCube n
      rw [comp_cubeIdx_append (p := p) (n := n) w y' u]
      exact hy'

end Work.WilG4c.CurveFam
