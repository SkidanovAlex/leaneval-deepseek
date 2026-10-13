/-
  Area E7 / sheet data: `Work.WilE7.SheetData.aboveRegionSubPf`.

  The "above region" (below the level `1`) of a sub-Pfaffian set `G ⊆ ℝ^{n+1}` is
  sub-Pfaffian:

      {y : Fin (n+1) → ℝ | y (Fin.last n) < 1 ∧
        ∃ t, Fin.snoc (Fin.init y) t ∈ G ∧ t < y (Fin.last n)}.

  Writing `G = projFirst (n+1) m '' X.set` for a restricted semi-Pfaffian set
  `X : SemiPf ((n+1)+m)`, the target is the projection to the first `n+1` coordinates of the
  points `z = Fin.append y x` of `ℝ^{(n+1) + ((n+1)+m)}` with

  * `z` in the closed cube and `x = projSnd z` in `X.set`;
  * `x (Fin.castAdd m (Fin.castSucc a)) = y (Fin.castSucc a)` for all `a : Fin n`
    (the witness `x` has the same first `n` coordinates as `y`);
  * `x (Fin.castAdd m (Fin.last n)) < y (Fin.last n)` (the last coordinate `t = x_n` lies below
    `y_n`), and `y (Fin.last n) < 1`.

  All three conditions are polynomial in the coordinates of `z`, so they may be imposed on the
  pullback `SemiPf.extend` of `X` along the injection `Fin.natAdd (n+1)` by the file
  `Work.WilE7.LevelFibre.withAtoms`; the resulting restricted semi-Pfaffian set `Z` satisfies
  `projFirst (n+1) ((n+1)+m) '' Z.set =` the target by construction.

  The helper lemmas `projFirst_eq_snoc_iff`, `mem_cubeC_finAppend` and `cubeC_of_snoc_fiber`
  are the `Fin`/cube bookkeeping; `projFirst_eq_snoc_iff` converts between the `Fin.snoc`
  presentation and the coordinate-wise one.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE8.Extend.semipf_set_extend
import Submission.Work.WilE7.LevelFibre.withAtoms

noncomputable section
open WilkiesDesign WilkiesDesign.E

namespace Work.WilE7.SheetData

/-! ## Index bookkeeping -/

/-- The projection of a concatenated point is its first block. -/
private theorem projFirst_finAppend {n m : ℕ} (y : Fin n → ℝ) (x : Fin m → ℝ) :
    projFirst n m (Fin.append y x) = y := by
  funext i; exact Fin.append_left y x i

/-- `projFirst (n+1) m x = Fin.snoc (Fin.init y) t` is the coordinate-wise statement that the
first `n` coordinates of `x` agree with those of `y` and the `(n+1)`-st one is `t`. -/
private theorem projFirst_eq_snoc_iff {n m : ℕ} (x : Fin ((n+1)+m) → ℝ) (y : Fin (n+1) → ℝ)
    (t : ℝ) :
    projFirst (n+1) m x = Fin.snoc (Fin.init y) t ↔
      (∀ a : Fin n, x (Fin.castAdd m (Fin.castSucc a)) = y (Fin.castSucc a)) ∧
      x (Fin.castAdd m (Fin.last n)) = t := by
  constructor
  · intro h
    refine ⟨fun a => ?_, ?_⟩
    · have hh := congrFun h (Fin.castSucc a)
      have hh2 : (Fin.init y) a = y (Fin.castSucc a) := rfl
      simpa [projFirst, Fin.snoc_castSucc, hh2] using hh
    · have hh := congrFun h (Fin.last n)
      simpa [projFirst, Fin.snoc_last] using hh
  · rintro ⟨h1, h2⟩
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simpa [projFirst, Fin.snoc_last] using h2
    · intro a
      have hh2 : (Fin.init y) a = y (Fin.castSucc a) := rfl
      simpa [projFirst, Fin.snoc_castSucc, hh2] using h1 a

/-- The cube of a concatenation is the product of the cubes. -/
private theorem mem_cubeC_finAppend {n m : ℕ} (y : Fin n → ℝ) (x : Fin m → ℝ) :
    Fin.append y x ∈ cubeC (n+m) ↔ y ∈ cubeC n ∧ x ∈ cubeC m := by
  constructor
  · intro h
    exact ⟨fun i => by have := h (Fin.castAdd m i); rwa [Fin.append_left] at this,
      fun j => by have := h (Fin.natAdd n j); rwa [Fin.append_right] at this⟩
  · rintro ⟨hy, hx⟩ i
    exact Fin.addCases (motive := fun i => |Fin.append y x i| ≤ 1)
      (fun j => by rw [Fin.append_left]; exact hy j)
      (fun j => by rw [Fin.append_right]; exact hx j) i

/-- A point `y` whose fibre contains a point `x` of the cube whose last coordinate `t` lies
below `y_n`, with `y_n < 1`, itself lies in the cube (indeed `t ≥ -1`, so `y_n > -1`). -/
private theorem cubeC_of_snoc_fiber {n m : ℕ} {x : Fin ((n+1)+m) → ℝ} {y : Fin (n+1) → ℝ}
    {t : ℝ} (hx : x ∈ cubeC ((n+1)+m))
    (h : projFirst (n+1) m x = Fin.snoc (Fin.init y) t)
    (ht : t < y (Fin.last n)) (h1 : y (Fin.last n) < 1) : y ∈ cubeC (n+1) := by
  obtain ⟨he, hl⟩ := (projFirst_eq_snoc_iff x y t).mp h
  intro i
  rw [abs_le]
  refine Fin.lastCases ?_ ?_ i
  · have hxt : |t| ≤ 1 := by rw [← hl]; exact hx _
    exact ⟨by linarith [(abs_le.mp hxt).1, ht], le_of_lt h1⟩
  · intro a
    have hxa : |x (Fin.castAdd m (Fin.castSucc a))| ≤ 1 := hx _
    rw [he a] at hxa
    exact abs_le.mp hxa

/-! ## The polynomial atoms

These are polynomials in the coordinates `Fin ((n+1) + ((n+1)+m))` of the point
`z = Fin.append y x`: `aboveEq a` encodes `x_a = y_a` (`a : Fin n`), `aboveLo` encodes
`x_n < y_n` and `aboveHi` encodes `y_n < 1`. -/

/-- `x (Fin.castAdd m (Fin.castSucc a)) - y (Fin.castSucc a)`, a polynomial in the coordinates
of `z = Fin.append y x`. -/
private def aboveEq (n m : ℕ) (a : Fin n) : MvPolynomial (Fin ((n+1) + ((n+1)+m))) ℝ :=
  MvPolynomial.X (Fin.natAdd (n+1) (Fin.castAdd m (Fin.castSucc a))) -
    MvPolynomial.X (Fin.castAdd ((n+1)+m) (Fin.castSucc a))

/-- `y (Fin.last n) - x (Fin.castAdd m (Fin.last n))`, the strict inequality `x_n < y_n`. -/
private def aboveLo (n m : ℕ) : MvPolynomial (Fin ((n+1) + ((n+1)+m))) ℝ :=
  MvPolynomial.X (Fin.castAdd ((n+1)+m) (Fin.last n)) -
    MvPolynomial.X (Fin.natAdd (n+1) (Fin.castAdd m (Fin.last n)))

/-- `1 - y (Fin.last n)`, the strict inequality `y_n < 1`. -/
private def aboveHi (n m : ℕ) : MvPolynomial (Fin ((n+1) + ((n+1)+m))) ℝ :=
  (1 : MvPolynomial (Fin ((n+1) + ((n+1)+m))) ℝ) -
    MvPolynomial.X (Fin.castAdd ((n+1)+m) (Fin.last n))

private theorem eval_aboveEq {n m : ℕ} (z : Fin ((n+1) + ((n+1)+m)) → ℝ) (a : Fin n) :
    MvPolynomial.eval z (aboveEq n m a) =
      z (Fin.natAdd (n+1) (Fin.castAdd m (Fin.castSucc a))) -
        z (Fin.castAdd ((n+1)+m) (Fin.castSucc a)) := by
  simp [aboveEq]

private theorem eval_aboveLo {n m : ℕ} (z : Fin ((n+1) + ((n+1)+m)) → ℝ) :
    MvPolynomial.eval z (aboveLo n m) =
      z (Fin.castAdd ((n+1)+m) (Fin.last n)) -
        z (Fin.natAdd (n+1) (Fin.castAdd m (Fin.last n))) := by
  simp [aboveLo]

private theorem eval_aboveHi {n m : ℕ} (z : Fin ((n+1) + ((n+1)+m)) → ℝ) :
    MvPolynomial.eval z (aboveHi n m) = 1 - z (Fin.castAdd ((n+1)+m) (Fin.last n)) := by
  simp [aboveHi]

/-! ## The theorem -/

theorem aboveRegionSubPf {n : ℕ} {G : Set (Fin (n + 1) → ℝ)}
    (hG : WilkiesDesign.E.SubPf (n + 1) G) :
    WilkiesDesign.E.SubPf (n + 1)
      {y : Fin (n + 1) → ℝ | y (Fin.last n) < 1 ∧
        ∃ t : ℝ, Fin.snoc (Fin.init y) t ∈ G ∧ t < y (Fin.last n)} := by
  obtain ⟨m, X, hX⟩ := hG
  -- the semi-Pfaffian set presenting the above region
  obtain ⟨Z, hZ⟩ := Work.WilE7.LevelFibre.withAtoms
    (Work.WilE8.SemiPf.extend (Fin.natAdd (n+1)) X)
    ((List.finRange n).map (aboveEq n m)) [aboveLo n m, aboveHi n m]
  refine ⟨(n+1)+m, Z, ?_⟩
  rw [hX, hZ, Work.WilE8.Extend.semipf_set_extend
    (Fin.natAdd_injective ((n+1)+m) (n+1)) X]
  ext y
  constructor
  · -- `y` in the above region gives the point `Fin.append y x` of `Z`
    rintro ⟨hylt1, t, htG, hty⟩
    obtain ⟨x, hxX, hxproj⟩ := htG
    have hxcube : x ∈ cubeC ((n+1)+m) := hxX.1
    have hxt : x (Fin.castAdd m (Fin.last n)) = t := by
      have hh := congrFun hxproj (Fin.last n); simpa [projFirst, Fin.snoc_last] using hh
    have hxa : ∀ a : Fin n, x (Fin.castAdd m (Fin.castSucc a)) = y (Fin.castSucc a) := by
      intro a
      have hh := congrFun hxproj (Fin.castSucc a)
      have h2 : (Fin.init y) a = y (Fin.castSucc a) := rfl
      simpa [projFirst, Fin.snoc_castSucc, h2] using hh
    have hycube : y ∈ cubeC (n+1) := cubeC_of_snoc_fiber hxcube hxproj hty hylt1
    refine ⟨Fin.append y x, ?_, projFirst_finAppend y x⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · exact (mem_cubeC_finAppend y x).mpr ⟨hycube, hxcube⟩
    · have hfun : (fun i => Fin.append y x (Fin.natAdd (n+1) i)) = x := by
        funext i; exact Fin.append_right y x i
      rw [hfun]; exact hxX
    · rw [List.forall_mem_map]
      intro a _
      rw [eval_aboveEq, sub_eq_zero, Fin.append_right, Fin.append_left]
      exact hxa a
    · intro P hP
      have hP' : P = aboveLo n m ∨ P = aboveHi n m := by simpa using hP
      rcases hP' with rfl | rfl
      · rw [eval_aboveLo, Fin.append_left, Fin.append_right, hxt]; linarith
      · rw [eval_aboveHi, Fin.append_left]; linarith
  · -- a point of `Z` produces a witness `t` for `y`
    rintro ⟨z, hzAB, hzy⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hzAB
    obtain ⟨⟨hzcube, hxX⟩, heqs, hpos⟩ := hzAB
    have hzy_last : z (Fin.castAdd ((n+1)+m) (Fin.last n)) = y (Fin.last n) := by
      have hh := congrFun hzy (Fin.last n); simpa [projFirst] using hh
    have hzy_cast : ∀ a : Fin n,
        z (Fin.castAdd ((n+1)+m) (Fin.castSucc a)) = y (Fin.castSucc a) := by
      intro a
      have hh := congrFun hzy (Fin.castSucc a); simpa [projFirst] using hh
    have heq_a : ∀ a : Fin n, z (Fin.natAdd (n+1) (Fin.castAdd m (Fin.castSucc a))) =
        z (Fin.castAdd ((n+1)+m) (Fin.castSucc a)) := by
      intro a
      have hh := heqs (aboveEq n m a) (List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩)
      rw [eval_aboveEq] at hh
      exact sub_eq_zero.mp hh
    have hlt1 : y (Fin.last n) < 1 := by
      have hh := hpos (aboveHi n m) (by simp)
      rw [eval_aboveHi, hzy_last] at hh
      linarith
    have hlt2 : z (Fin.natAdd (n+1) (Fin.castAdd m (Fin.last n))) < y (Fin.last n) := by
      have hh := hpos (aboveLo n m) (by simp)
      rw [eval_aboveLo, hzy_last] at hh
      linarith
    refine ⟨hlt1, z (Fin.natAdd (n+1) (Fin.castAdd m (Fin.last n))), ?_, hlt2⟩
    refine ⟨fun i => z (Fin.natAdd (n+1) i), hxX, ?_⟩
    exact (projFirst_eq_snoc_iff (fun i => z (Fin.natAdd (n+1) i)) y _).mpr
      ⟨fun a => (heq_a a).trans (hzy_cast a), rfl⟩

end Work.WilE7.SheetData
