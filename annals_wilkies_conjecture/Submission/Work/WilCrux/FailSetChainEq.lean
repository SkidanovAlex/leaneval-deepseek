/-
  WilCrux — reading lemmas and the set identity for `Work.WilCrux.failSet_mem`.

  We identify the `Ω`-construction `fmChain` (`FailSetChainDefs`) with the failure set
  carrying the level `ε` as a coordinate.  All the coordinate bookkeeping is collected here.
-/
import Mathlib
import Submission.Work.WilCrux.FailSetChainMem

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

variable {a b : ℕ}

/-! ## 1. Reading the coordinate maps -/

theorem fm_read_wD (u : Fin (fmE a) → ℝ) (w : Fin (fmB a b) → ℝ) (i : Fin a) :
    Work.WilG0.snocIt (fmE a) (fmB a b) u w (fmwD a b i) = u (fmwE a i) := by
  simp only [fmwD, Work.WilG0.snocIt_castAdd]

theorem fm_read_wpD (u : Fin (fmE a) → ℝ) (w : Fin (fmB a b) → ℝ) (i : Fin a) :
    Work.WilG0.snocIt (fmE a) (fmB a b) u w (fmwpD a b i) = w (fmwpB a b i) := by
  simp only [fmwpD, Work.WilG0.snocIt_natAdd]

theorem fm_read_zD (u : Fin (fmE a) → ℝ) (w : Fin (fmB a b) → ℝ) (j : Fin b) :
    Work.WilG0.snocIt (fmE a) (fmB a b) u w (fmzD a b j) = w (fmzB a b j) := by
  simp only [fmzD, Work.WilG0.snocIt_natAdd]

theorem fm_read_zpD (u : Fin (fmE a) → ℝ) (w : Fin (fmB a b) → ℝ) (j : Fin b) :
    Work.WilG0.snocIt (fmE a) (fmB a b) u w (fmzpD a b j) = w (fmzpB a b j) := by
  simp only [fmzpD, Work.WilG0.snocIt_natAdd]

theorem fm_read_epsD (u : Fin (fmE a) → ℝ) (w : Fin (fmB a b) → ℝ) :
    Work.WilG0.snocIt (fmE a) (fmB a b) u w (fmepsD a b) = u (fmepsE a) := by
  simp only [fmepsD, Work.WilG0.snocIt_castAdd]

theorem fm_read_etaD (u : Fin (fmE a) → ℝ) (w : Fin (fmB a b) → ℝ) :
    Work.WilG0.snocIt (fmE a) (fmB a b) u w (fmetaD a b) = u (fmetaE a) := by
  simp only [fmetaD, Work.WilG0.snocIt_castAdd]

theorem fm_read_wN (u' : Fin (fmD a b) → ℝ) (vv : Fin 2 → ℝ) (i : Fin a) :
    Work.WilG0.snocIt (fmD a b) 2 u' vv (fmwN a b i) = u' (fmwD a b i) := by
  simp only [fmwN, Work.WilG0.snocIt_castAdd]

theorem fm_read_epsN (u' : Fin (fmD a b) → ℝ) (vv : Fin 2 → ℝ) :
    Work.WilG0.snocIt (fmD a b) 2 u' vv (fmepsN a b) = u' (fmepsD a b) := by
  simp only [fmepsN, Work.WilG0.snocIt_castAdd]

theorem fm_read_wpN (u' : Fin (fmD a b) → ℝ) (vv : Fin 2 → ℝ) (i : Fin a) :
    Work.WilG0.snocIt (fmD a b) 2 u' vv (fmwpN a b i) = u' (fmwpD a b i) := by
  simp only [fmwpN, Work.WilG0.snocIt_castAdd]

theorem fm_read_zN (u' : Fin (fmD a b) → ℝ) (vv : Fin 2 → ℝ) (j : Fin b) :
    Work.WilG0.snocIt (fmD a b) 2 u' vv (fmzN a b j) = u' (fmzD a b j) := by
  simp only [fmzN, Work.WilG0.snocIt_castAdd]

theorem fm_read_zpN (u' : Fin (fmD a b) → ℝ) (vv : Fin 2 → ℝ) (j : Fin b) :
    Work.WilG0.snocIt (fmD a b) 2 u' vv (fmzpN a b j) = u' (fmzpD a b j) := by
  simp only [fmzpN, Work.WilG0.snocIt_castAdd]

theorem fm_read_yN (u' : Fin (fmD a b) → ℝ) (vv : Fin 2 → ℝ) :
    Work.WilG0.snocIt (fmD a b) 2 u' vv (fmyN a b) = vv 0 := by
  simp only [fmyN, Work.WilG0.snocIt_natAdd]

theorem fm_read_ypN (u' : Fin (fmD a b) → ℝ) (vv : Fin 2 → ℝ) :
    Work.WilG0.snocIt (fmD a b) 2 u' vv (fmypN a b) = vv 1 := by
  simp only [fmypN, Work.WilG0.snocIt_natAdd]

theorem fm_readInit_wE (X : Fin (a + 1) → ℝ) (η : ℝ) (i : Fin a) :
    fmsnoc a X η (fmwE a i) = Fin.init X i := by
  simp only [fmsnoc, fmwE, Fin.snoc_castSucc, Fin.init]

theorem fm_readInit_epsE (X : Fin (a + 1) → ℝ) (η : ℝ) :
    fmsnoc a X η (fmepsE a) = X (Fin.last a) := by
  simp only [fmsnoc, fmepsE, Fin.snoc_castSucc]

theorem fm_readInit_etaE (X : Fin (a + 1) → ℝ) (η : ℝ) :
    fmsnoc a X η (fmetaE a) = η := by
  simp only [fmsnoc, fmetaE, Fin.snoc_last]

theorem fmsnoc_last (X : Fin (a + 1) → ℝ) (η : ℝ) :
    fmsnoc a X η (Fin.last (a + 1)) = η := by
  simp only [fmsnoc, Fin.snoc_last]

/-! ## 2. The reindexing computations -/

theorem fm_comp_e1 (u' : Fin (fmD a b) → ℝ) (vv : Fin 2 → ℝ) :
    (Work.WilG0.snocIt (fmD a b) 2 u' vv) ∘ fme1 a b
      = Fin.snoc (Fin.append (u' ∘ fmwpD a b) (u' ∘ fmzD a b)) (vv 0) := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · simp only [fme1, Fin.snoc_last, Function.comp_apply, fm_read_yN, Fin.snoc_last]
  · intro k'
    simp only [fme1, Fin.snoc_castSucc, Function.comp_apply, Fin.snoc_castSucc]
    refine Fin.addCases (motive := fun k' => Work.WilG0.snocIt (fmD a b) 2 u' vv
        (Fin.append (fmwpN a b) (fmzN a b) k')
        = Fin.append (u' ∘ fmwpD a b) (u' ∘ fmzD a b) k') (fun i => ?_) (fun j => ?_) k'
    · simp only [Fin.append_left, Function.comp_apply, fmwpN, fmwpD,
        Work.WilG0.snocIt_castAdd, Work.WilG0.snocIt_natAdd]
    · simp only [Fin.append_right, Function.comp_apply, fmzN, fmzD,
        Work.WilG0.snocIt_castAdd, Work.WilG0.snocIt_natAdd]

theorem fm_comp_e2 (u' : Fin (fmD a b) → ℝ) (vv : Fin 2 → ℝ) :
    (Work.WilG0.snocIt (fmD a b) 2 u' vv) ∘ fme2 a b
      = Fin.snoc (Fin.append (u' ∘ fmwpD a b) (u' ∘ fmzpD a b)) (vv 1) := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · simp only [fme2, Fin.snoc_last, Function.comp_apply, fm_read_ypN, Fin.snoc_last]
  · intro k'
    simp only [fme2, Fin.snoc_castSucc, Function.comp_apply, Fin.snoc_castSucc]
    refine Fin.addCases (motive := fun k' => Work.WilG0.snocIt (fmD a b) 2 u' vv
        (Fin.append (fmwpN a b) (fmzpN a b) k')
        = Fin.append (u' ∘ fmwpD a b) (u' ∘ fmzpD a b) k') (fun i => ?_) (fun j => ?_) k'
    · simp only [Fin.append_left, Function.comp_apply, fmwpN, fmwpD,
        Work.WilG0.snocIt_castAdd, Work.WilG0.snocIt_natAdd]
    · simp only [Fin.append_right, Function.comp_apply, fmzpN, fmzpD,
        Work.WilG0.snocIt_castAdd, Work.WilG0.snocIt_natAdd]

/-! ## 3. Reducing `Fin 2` to two reals -/

theorem projLastIter_two_eq (n : ℕ) (X : Set (Fin (n + 2) → ℝ)) :
    Work.WilG0.projLastIter n 2 X = {x | ∃ y y' : ℝ, Work.WilG0.snocIt n 2 x ![y, y'] ∈ X} := by
  rw [Work.WilG0.projLastIter_eq]
  ext x
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w 0, w 1, ?_⟩
    have : w = ![w 0, w 1] := by funext k; fin_cases k <;> simp
    rwa [this] at hw
  · rintro ⟨y, y', h⟩
    exact ⟨![y, y'], h⟩

/-! ## 4. The hypothesis reading -/

theorem fmHyp_read_general (v : Fin (fmD a b) → ℝ) :
    v ∈ fmHyp a b ↔
      (∀ i : Fin a, |v (fmwpD a b i) - v (fmwD a b i)| < v (fmetaD a b)) ∧
      (∃ j : Fin b, v (fmzD a b j) ≠ 0) ∧
      (∀ j : Fin b, |v (fmzD a b j)| < v (fmetaD a b)) ∧
      (∃ j : Fin b, v (fmzpD a b j) ≠ 0) ∧
      (∀ j : Fin b, |v (fmzpD a b j)| < v (fmetaD a b)) := by
  simp only [fmHyp, fmWdist, fmZne, fmNormZ, fmZpne, fmNormZp, fmWd, fmWu, fmZlow, fmZup,
    fmZlowp, fmZupp, Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff,
    Set.mem_ofPred_eq, ne_eq, not_forall]
  constructor
  · rintro ⟨⟨⟨⟨hW, hZ⟩, hNZ⟩, hZp⟩, hNZp⟩
    refine ⟨?_, hZ, ?_, hZp, ?_⟩
    · intro i
      obtain ⟨h1, h2⟩ := hW i
      rw [abs_lt]; exact ⟨by linarith, by linarith⟩
    · intro j
      obtain ⟨h1, h2⟩ := hNZ j
      rw [abs_lt]; exact ⟨by linarith, by linarith⟩
    · intro j
      obtain ⟨h1, h2⟩ := hNZp j
      rw [abs_lt]; exact ⟨by linarith, by linarith⟩
  · rintro ⟨hW, hZ, hNZ, hZp, hNZp⟩
    refine ⟨⟨⟨⟨?_, hZ⟩, ?_⟩, hZp⟩, ?_⟩
    · intro i
      have := hW i; rw [abs_lt] at this; exact ⟨by linarith, by linarith⟩
    · intro j
      have := hNZ j; rw [abs_lt] at this; exact ⟨by linarith, by linarith⟩
    · intro j
      have := hNZp j; rw [abs_lt] at this; exact ⟨by linarith, by linarith⟩

theorem fmHyp_read (X : Fin (a + 1) → ℝ) (η : ℝ) (w : Fin (fmB a b) → ℝ) :
    Work.WilG0.snocIt (fmE a) (fmB a b) (fmsnoc a X η) w ∈ fmHyp a b ↔
      (∀ i : Fin a, |w (fmwpB a b i) - Fin.init X i| < η) ∧
      (∃ j : Fin b, w (fmzB a b j) ≠ 0) ∧
      (∀ j : Fin b, |w (fmzB a b j)| < η) ∧
      (∃ j : Fin b, w (fmzpB a b j) ≠ 0) ∧
      (∀ j : Fin b, |w (fmzpB a b j)| < η) := by
  rw [fmHyp_read_general]
  simp only [fmsnoc, fm_read_etaD, fm_readInit_etaE, fm_read_wpD, fm_read_wD, fm_readInit_wE,
    fm_read_zD, fm_read_zpD]

end Work.WilCrux
