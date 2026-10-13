import Mathlib
import Submission.Work.WilG4a.CD.fibreLimitDefs
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd

namespace Work.WilG4a.CD

/-!
  # `snocIt_mem_Gset`

  The point `P := snocIt (p+3) 4 (Fin.snoc (Fin.snoc z ε) δ) w` of `ℝ^{p+7}` glues the
  block `x := (Fin.snoc (Fin.snoc z ε) δ) : Fin (p+3) → ℝ` (coordinates `z 0, …, z p, ε, δ`)
  with the block `w : Fin 4 → ℝ` (coordinates `w 0 = t, w 1 = t', w 2 = v, w 3 = v'`).

  We record the value of `P` at the seven distinguished indices of `Gset`, at the two
  composite substitutions `iota1_y`, `iota2_y`, and then unfold `Gset` and `reading` and match.

  The index computations: with `snocIt_castAdd` (first block) and `snocIt_natAdd` (second
  block) one has
  * `iEps p = castAdd 4 (castSucc (last (p+1)))` and `x (castSucc (last (p+1))) = ε`,
  * `iDel p = castAdd 4 (last (p+2))` and `x (last (p+2)) = δ`,
  * `iC p = castAdd 4 (castSucc (castSucc (last p)))` and `x (…) = z (last p)`,
  * `iT p = natAdd (p+3) 0`, `iT' p = natAdd (p+3) 1`, `iV p = natAdd (p+3) 2`,
    `iV' p = natAdd (p+3) 3`.
-/

/-- The `ε`-coordinate (index `p+1`) of the glued point is `ε`. -/
lemma snocIt_snoc_snoc_iEps (p : ℕ) (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (w : Fin 4 → ℝ) :
    (Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w) (iEps p) = ε := by
  rw [show iEps p = Fin.castAdd 4 (Fin.castSucc (Fin.last (p + 1))) from Fin.ext rfl,
    Work.WilG0.snocIt_castAdd]
  simp

/-- The `δ`-coordinate (index `p+2`) of the glued point is `δ`. -/
lemma snocIt_snoc_snoc_iDel (p : ℕ) (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (w : Fin 4 → ℝ) :
    (Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w) (iDel p) = δ := by
  rw [show iDel p = Fin.castAdd 4 (Fin.last (p + 2)) from Fin.ext rfl,
    Work.WilG0.snocIt_castAdd]
  simp

/-- The `c = z (last p)`-coordinate (index `p`) of the glued point is `z (last p)`. -/
lemma snocIt_snoc_snoc_iC (p : ℕ) (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (w : Fin 4 → ℝ) :
    (Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w) (iC p) = z (Fin.last p) := by
  rw [show iC p = Fin.castAdd 4 (Fin.castSucc (Fin.castSucc (Fin.last p))) from Fin.ext rfl,
    Work.WilG0.snocIt_castAdd]
  simp

/-- The `t`-coordinate (index `p+3`) of the glued point is `w 0`. -/
lemma snocIt_snoc_snoc_iT (p : ℕ) (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (w : Fin 4 → ℝ) :
    (Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w) (iT p) = w 0 := by
  rw [show iT p = Fin.natAdd (p + 3) (0 : Fin 4) from Fin.ext rfl,
    Work.WilG0.snocIt_natAdd]

/-- The `t'`-coordinate (index `p+4`) of the glued point is `w 1`. -/
lemma snocIt_snoc_snoc_iT' (p : ℕ) (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (w : Fin 4 → ℝ) :
    (Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w) (iT' p) = w 1 := by
  rw [show iT' p = Fin.natAdd (p + 3) (1 : Fin 4) from Fin.ext rfl,
    Work.WilG0.snocIt_natAdd]

/-- The `v`-coordinate (index `p+5`) of the glued point is `w 2`. -/
lemma snocIt_snoc_snoc_iV (p : ℕ) (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (w : Fin 4 → ℝ) :
    (Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w) (iV p) = w 2 := by
  rw [show iV p = Fin.natAdd (p + 3) (2 : Fin 4) from Fin.ext rfl,
    Work.WilG0.snocIt_natAdd]

/-- The `v'`-coordinate (index `p+6`) of the glued point is `w 3`. -/
lemma snocIt_snoc_snoc_iV' (p : ℕ) (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (w : Fin 4 → ℝ) :
    (Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w) (iV' p) = w 3 := by
  rw [show iV' p = Fin.natAdd (p + 3) (3 : Fin 4) from Fin.ext rfl,
    Work.WilG0.snocIt_natAdd]

/-- On the `z`-block (indices `Fin.castAdd 6 ∘ Fin.castSucc`), the glued point reads
`Fin.init z`; we state it as `z ∘ Fin.castSucc`, which is the same function. -/
lemma snocIt_snoc_snoc_zblock (p : ℕ) (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (w : Fin 4 → ℝ)
    (k : Fin p) :
    (Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w)
        (Fin.castAdd 6 (Fin.castSucc k)) = z (Fin.castSucc k) := by
  rw [show Fin.castAdd 6 (Fin.castSucc k)
        = Fin.castAdd 4 (Fin.castSucc (Fin.castSucc (Fin.castSucc k))) from Fin.ext rfl,
    Work.WilG0.snocIt_castAdd]
  simp

/-- Composing the glued point with `iota1_y` gives `(init z, w 0, w 2)`. -/
lemma snocIt_snoc_snoc_comp_iota1 (p : ℕ) (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (w : Fin 4 → ℝ) :
    (Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w) ∘ iota1_y p
      = Fin.snoc (Fin.snoc (Fin.init z) (w 0)) (w 2) := by
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp only [Function.comp_apply, iota1_y, Fin.snoc_last]
      exact snocIt_snoc_snoc_iV p z ε δ w
  | cast j =>
      cases j using Fin.lastCases with
      | last =>
          simp only [Function.comp_apply, iota1_y, Fin.snoc_last, Fin.snoc_castSucc]
          exact snocIt_snoc_snoc_iT p z ε δ w
      | cast k =>
          simp only [Function.comp_apply, iota1_y, Fin.snoc_castSucc]
          exact snocIt_snoc_snoc_zblock p z ε δ w k

/-- Composing the glued point with `iota2_y` gives `(init z, w 1, w 3)`. -/
lemma snocIt_snoc_snoc_comp_iota2 (p : ℕ) (z : Fin (p + 1) → ℝ) (ε δ : ℝ) (w : Fin 4 → ℝ) :
    (Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w) ∘ iota2_y p
      = Fin.snoc (Fin.snoc (Fin.init z) (w 1)) (w 3) := by
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp only [Function.comp_apply, iota2_y, Fin.snoc_last]
      exact snocIt_snoc_snoc_iV' p z ε δ w
  | cast j =>
      cases j using Fin.lastCases with
      | last =>
          simp only [Function.comp_apply, iota2_y, Fin.snoc_last, Fin.snoc_castSucc]
          exact snocIt_snoc_snoc_iT' p z ε δ w
      | cast k =>
          simp only [Function.comp_apply, iota2_y, Fin.snoc_castSucc]
          exact snocIt_snoc_snoc_zblock p z ε δ w k

theorem snocIt_mem_Gset (p : ℕ) (A : Set (Fin (p + 2) → ℝ)) (z : Fin (p + 1) → ℝ)
    (ε δ : ℝ) (w : Fin 4 → ℝ) :
    Work.WilG0.snocIt (p + 3) 4 (Fin.snoc (Fin.snoc z ε) δ) w ∈ Gset p A ↔
      reading p A z ε δ (w 0) (w 1) (w 2) (w 3) := by
  simp only [Gset, bA1, bA2, bTne, bTne', bQ1, bQ2, bV, reading, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  rw [snocIt_snoc_snoc_comp_iota1 p z ε δ w, snocIt_snoc_snoc_comp_iota2 p z ε δ w,
    snocIt_snoc_snoc_iC p z ε δ w, snocIt_snoc_snoc_iT p z ε δ w,
    snocIt_snoc_snoc_iT' p z ε δ w, snocIt_snoc_snoc_iEps p z ε δ w,
    snocIt_snoc_snoc_iDel p z ε δ w, snocIt_snoc_snoc_iV p z ε δ w,
    snocIt_snoc_snoc_iV' p z ε δ w]
  tauto

end Work.WilG4a.CD
