import Mathlib
import Submission.Work.WilE7.AboveAux.AboveLevelDefs

namespace Work.WilE7.AboveAux

/-! ## Coordinate computations for the gap embedding `gapInj`

`gapInj p q M k : Fin (blkDim p q M k) → Fin (levDim p q M k)` reads a point
`(x, w, z 0, …, z (k-1))` of `ℝ^{blkDim}` off a point `(y, w, z 0, …)` of `ℝ^{levDim}`: the
coordinate `p` of the target (the level `y (Fin.last p)`) is skipped, the coordinates below `p`
(the base `x`) are kept, and everything from `p` on is shifted up by one.  This file records the
elementary consequences of that definition:

* `gapInj` is injective;
* the projection of `V ∘ gapInj` to the first `p + M` coordinates is `(Fin.init y, w)`;
* the projection of `V ∘ gapInj` to the last `(p+q)*k` coordinates is `(z 0, …, z (k-1))`;
* reading the `l`-th block of that point recovers `z l`. -/

/-! ### The value of `gapInj` -/

/-- Below the gap, `gapInj` does not move the coordinate. -/
private theorem gapInj_val_lt (p q M k : ℕ) {i : Fin (blkDim p q M k)} (h : (i : ℕ) < p) :
    (gapInj p q M k i : ℕ) = i := by
  simp only [gapInj, dite_eq_left h, Fin.val_mk]

/-- At and above the gap, `gapInj` shifts the coordinate up by one. -/
private theorem gapInj_val_ge (p q M k : ℕ) {i : Fin (blkDim p q M k)} (h : ¬ (i : ℕ) < p) :
    (gapInj p q M k i : ℕ) = (i : ℕ) + 1 := by
  simp only [gapInj, dite_eq_right h, Fin.val_mk]

/-- `gapInj` is injective: it inserts one coordinate and keeps the order of the others. -/
theorem gapInj_injective (p q M k : ℕ) : Function.Injective (gapInj p q M k) := by
  intro i j hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  by_cases hi : (i : ℕ) < p <;> by_cases hj : (j : ℕ) < p
  · have h1 := gapInj_val_lt p q M k hi
    have h2 := gapInj_val_lt p q M k hj
    omega
  · have h1 := gapInj_val_lt p q M k hi
    have h2 := gapInj_val_ge p q M k hj
    omega
  · have h1 := gapInj_val_ge p q M k hi
    have h2 := gapInj_val_lt p q M k hj
    have hi' : (i : ℕ) < blkDim p q M k := i.isLt
    omega
  · have h1 := gapInj_val_ge p q M k hi
    have h2 := gapInj_val_ge p q M k hj
    omega

/-! ### The projections of `V ∘ gapInj` -/

/-- The first `p + M` coordinates of `V ∘ gapInj` are `(Fin.init y, w)`, i.e. the base read off
`V` together with the witness. -/
theorem gapInj_projFirst (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) :
    WilkiesDesign.E.projFirst (p + M) ((p + q) * k) (fun i => V (gapInj p q M k i)) =
      Fin.append (Fin.init (rdY p q M k V)) (rdW p q M k V) := by
  funext j
  refine Fin.addCases (m := p) (n := M)
    (motive := fun j => WilkiesDesign.E.projFirst (p + M) ((p + q) * k)
        (fun i => V (gapInj p q M k i)) j =
      Fin.append (Fin.init (rdY p q M k V)) (rdW p q M k V) j) ?_ ?_ j
  · intro i
    rw [Fin.append_left]
    simp only [WilkiesDesign.E.projFirst, rdY, Fin.init]
    show V (gapInj p q M k (Fin.castAdd ((p + q) * k) (Fin.castAdd M i))) =
      V (Fin.castAdd (M + (p + q) * k) (Fin.castSucc i))
    congr 1
    apply Fin.ext
    have hlt : (((Fin.castAdd ((p + q) * k) (Fin.castAdd M i)) :
        Fin (blkDim p q M k)) : ℕ) < p := by
      simp only [Fin.val_castAdd]
      exact i.isLt
    rw [gapInj_val_lt p q M k hlt]
    simp only [Fin.val_castAdd, Fin.val_castSucc]
  · intro i
    rw [Fin.append_right]
    simp only [WilkiesDesign.E.projFirst, rdW, WilkiesDesign.E.projSnd]
    show V (gapInj p q M k (Fin.castAdd ((p + q) * k) (Fin.natAdd p i))) =
      V (Fin.natAdd (p + 1) (Fin.castAdd ((p + q) * k) i))
    congr 1
    apply Fin.ext
    have hge : ¬ (((Fin.castAdd ((p + q) * k) (Fin.natAdd p i)) :
        Fin (blkDim p q M k)) : ℕ) < p := by
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      omega
    rw [gapInj_val_ge p q M k hge]
    simp only [Fin.val_natAdd, Fin.val_castAdd]
    omega

/-- The last `(p+q)*k` coordinates of `V ∘ gapInj` are the point `(z 0, …, z (k-1))`. -/
theorem gapInj_projSnd (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) :
    WilkiesDesign.E.projSnd (p + M) ((p + q) * k) (fun i => V (gapInj p q M k i)) =
      rdBlkPt p q M k V := by
  funext j
  simp only [WilkiesDesign.E.projSnd, rdBlkPt]
  show V (gapInj p q M k (Fin.natAdd (p + M) j)) =
    V (Fin.natAdd (p + 1) (Fin.natAdd M j))
  congr 1
  apply Fin.ext
  have hge : ¬ (((Fin.natAdd (p + M) j) : Fin (blkDim p q M k)) : ℕ) < p := by
    simp only [Fin.val_natAdd]
    omega
  rw [gapInj_val_ge p q M k hge]
  simp only [Fin.val_natAdd]
  omega

/-- Reading the `l`-th block of `(z 0, …, z (k-1))` recovers `z l`. -/
theorem fibBlk_rdBlkPt (p q M k : ℕ) (V : Fin (levDim p q M k) → ℝ) (l : Fin k) :
    fibBlk (rdBlkPt p q M k V) l = rdBlk p q M k V l := by
  funext i
  simp only [fibBlk, rdBlk, rdBlkPt, WilkiesDesign.E.projSnd, fibBlkIdx, blkD]
  congr 1
  apply Fin.ext
  simp only [Fin.val_natAdd]
  omega

theorem gapInj_proj (p q M k : ℕ) :
    Function.Injective (Work.WilE7.AboveAux.gapInj p q M k) ∧
    (∀ V : Fin (Work.WilE7.AboveAux.levDim p q M k) → ℝ,
      WilkiesDesign.E.projFirst (p + M) ((p + q) * k)
          (fun i => V (Work.WilE7.AboveAux.gapInj p q M k i)) =
        Fin.append (Fin.init (Work.WilE7.AboveAux.rdY p q M k V))
          (Work.WilE7.AboveAux.rdW p q M k V)) ∧
    (∀ V : Fin (Work.WilE7.AboveAux.levDim p q M k) → ℝ,
      WilkiesDesign.E.projSnd (p + M) ((p + q) * k)
          (fun i => V (Work.WilE7.AboveAux.gapInj p q M k i)) =
        Work.WilE7.AboveAux.rdBlkPt p q M k V) ∧
    (∀ V : Fin (Work.WilE7.AboveAux.levDim p q M k) → ℝ, ∀ l : Fin k,
      Work.WilE7.AboveAux.fibBlk (Work.WilE7.AboveAux.rdBlkPt p q M k V) l =
        Work.WilE7.AboveAux.rdBlk p q M k V l) := by
  refine ⟨gapInj_injective p q M k, ?_, ?_, ?_⟩
  · intro V
    exact gapInj_projFirst p q M k V
  · intro V
    exact gapInj_projSnd p q M k V
  · intro V l
    exact fibBlk_rdBlkPt p q M k V l

end Work.WilE7.AboveAux
