/-
  WilG4c / `inflated_mem_m` — the `(n+1)`-dimensional cube version of the "localisation in the
  cube coordinates" Ω-lemma.

  For an Ω-set `X ⊆ ℝ^{p+(n+1)}` (read as `(l, z)` with `l : Fin p → ℝ`, `z : Fin (n+1) → ℝ`)
  the *inflation* is

    `{w | ∃ δ > 0, ∀ y, (∀ j, |y j - z j| < δ) → (l, y) ∈ X}`,

  the set of points `w = (l,z)` such that `X` contains the whole open box of side `2δ` around
  `z` in the cube directions through `l`.  This generalises `Work.WilG4a.CD.inflated_mem`
  (which is the case `n = 0`) to an `(n+1)`-dimensional cube.

  ## The construction

  Work in the auxiliary space `ℝ^{p+(n+1)+1+(n+1)}` with coordinates `(l, z, δ, y)`:

  * `cell`  : the strict box condition `∀ j, (y j - z j)² < δ²`,
  * `pre`   : the pullback `{(l,z,δ,y) | (l,y) ∈ X}` along the index map `iota`,
  * `Q = cell ∩ preᶜ`,

  then

    `inflation X = projLast ( {δ > 0} ∩ (projLastIter_{n+1} Q)ᶜ )`.

  The universal quantifier over `y` is `compl ∘ projLastIter ∘ compl`; iterating the projection
  `n+1` times costs `F + (n+1) + (p+(n+1)+1)`, and the box condition is an intersection of
  `n+1` strict-polynomial-positivity sets, each of degree cost `4`.

  Everything reduces to the coordinate computation
  `(Fin.append (Fin.snoc v δ) y) ∘ iota = Fin.append (parPt v) y` together with
  `(Fin.append (Fin.snoc v δ) y) (yIdx j) = y j`, `... (zIdx j) = cubePt v j`,
  `... (dIdx) = δ`, which `aux_eq` packages into the set equality `aux = tgt`.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilkG4c

namespace Infl

open WilkiesDesign

/-! ## 1. Coordinates of the auxiliary space `ℝ^{p+(n+1)+1+(n+1)} = (l, z, δ, y)` -/

/-- The index of the `l`-coordinate `i`. -/
def lIdx (p n : ℕ) (i : Fin p) : Fin (p + (n + 1) + 1 + (n + 1)) :=
  Fin.castAdd (n + 1) (Fin.castAdd 1 (Fin.castAdd (n + 1) i))

/-- The index of the `z`-coordinate `j`. -/
def zIdx (p n : ℕ) (j : Fin (n + 1)) : Fin (p + (n + 1) + 1 + (n + 1)) :=
  Fin.castAdd (n + 1) (Fin.castAdd 1 (Fin.natAdd p j))

/-- The index of the radius coordinate `δ`. -/
def dIdx (p n : ℕ) : Fin (p + (n + 1) + 1 + (n + 1)) :=
  Fin.castAdd (n + 1) (Fin.last (p + (n + 1)))

/-- The index of the `y`-coordinate `j`. -/
def yIdx (p n : ℕ) (j : Fin (n + 1)) : Fin (p + (n + 1) + 1 + (n + 1)) :=
  Fin.natAdd (p + (n + 1) + 1) j

/-- The pullback index `(l,z) ↦ (l,y)` for the Ω-set `X`. -/
def iota (p n : ℕ) : Fin (p + (n + 1)) → Fin (p + (n + 1) + 1 + (n + 1)) :=
  Fin.append (fun i : Fin p => lIdx p n i) (fun j : Fin (n + 1) => yIdx p n j)

/-- The strict box condition. -/
def cell (p n : ℕ) : Set (Fin (p + (n + 1) + 1 + (n + 1)) → ℝ) :=
  {W | ∀ j : Fin (n + 1), (W (yIdx p n j) - W (zIdx p n j)) ^ 2 < (W (dIdx p n)) ^ 2}

/-- The explicit `Ω`-description of the inflation. -/
def aux (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) : Set (Fin (p + (n + 1)) → ℝ) :=
  projLast ({v : Fin (p + (n + 1) + 1) → ℝ | 0 < v (Fin.last (p + (n + 1)))} ∩
    (Work.WilG0.projLastIter (p + (n + 1) + 1) (n + 1)
      (cell p n ∩ (Work.WilG5.coordPre (iota p n) X)ᶜ))ᶜ)

/-- The inflation itself. -/
def tgt (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) : Set (Fin (p + (n + 1)) → ℝ) :=
  {w | ∃ δ : ℝ, 0 < δ ∧ ∀ y : Fin (n + 1) → ℝ,
    (∀ j, |y j - cubePt w j| < δ) → Fin.append (parPt w) y ∈ X}

/-! ## 2. Elementary closure lemmas -/

/-- Binary intersection with equal formats. -/
theorem inter2_same {S : WilkiesDesign.SOMin} {N F D₁ D₂ : ℕ} {X Y : Set (Fin N → ℝ)}
    (hX : X ∈ S.Ω F D₁ N) (hY : Y ∈ S.Ω F D₂ N) :
    X ∩ Y ∈ S.Ω (F + 1) (D₁ + D₂) N := by
  have h := S.inter (F := F) (n := N) (k := 2)
    (fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (fun i : Fin 2 => if i = 0 then X else Y)
    (by intro i; fin_cases i
        · simpa using hX
        · simpa using hY)
  have hsum : (∑ i : Fin 2, (if i = 0 then D₁ else D₂)) = D₁ + D₂ := by
    rw [Fin.sum_univ_two]; simp
  rw [hsum] at h
  rw [Work.WilG1.Omega.iInter_fin_two] at h
  exact h

/-- `{v | v k > 0}` is `Ω`-definable with constant bounds. -/
theorem posLast_mem (S : WilkiesDesign.SOMin) (p n D : ℕ) :
    {v : Fin (p + (n + 1) + 1) → ℝ | 0 < v (Fin.last (p + (n + 1)))} ∈
      S.Ω (p + (n + 1) + 1 + 2) 3 (p + (n + 1) + 1) := by
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + (n + 1) + 1) D
    (MvPolynomial.X (Fin.last (p + (n + 1))) : MvPolynomial (Fin (p + (n + 1) + 1)) ℝ)
  have hset : {x : Fin (p + (n + 1) + 1) → ℝ | 0 < MvPolynomial.eval x
        (MvPolynomial.X (Fin.last (p + (n + 1))) : MvPolynomial (Fin (p + (n + 1) + 1)) ℝ)}
      = {v : Fin (p + (n + 1) + 1) → ℝ | 0 < v (Fin.last (p + (n + 1)))} := by
    ext x; simp
  rw [hset] at h
  have hdeg : (Polynomial.C ((MvPolynomial.X (Fin.last (p + (n + 1))) :
      MvPolynomial (Fin (p + (n + 1) + 1)) ℝ).totalDegree + 2) : Polynomial ℕ).eval D ≤ 3 := by
    rw [MvPolynomial.totalDegree_X]; simp
  exact Work.WilG1.Omega.mono h le_rfl hdeg

/-- The box cell is `Ω`-definable with constant format and constant degree cost. -/
theorem cell_mem (S : WilkiesDesign.SOMin) (p n D : ℕ) :
    cell p n ∈ S.Ω (p + (n + 1) + 1 + (n + 1) + 3) ((n + 1) * 4)
      (p + (n + 1) + 1 + (n + 1)) := by
  have hbox : ∀ j : Fin (n + 1),
      {W : Fin (p + (n + 1) + 1 + (n + 1)) → ℝ |
        (W (yIdx p n j) - W (zIdx p n j)) ^ 2 < (W (dIdx p n)) ^ 2} ∈
      S.Ω (p + (n + 1) + 1 + (n + 1) + 2) 4 (p + (n + 1) + 1 + (n + 1)) := by
    intro j
    set P : MvPolynomial (Fin (p + (n + 1) + 1 + (n + 1))) ℝ :=
      (MvPolynomial.X (dIdx p n)) ^ 2 -
        (MvPolynomial.X (yIdx p n j) - MvPolynomial.X (zIdx p n j)) ^ 2 with hP
    have htd : P.totalDegree ≤ 2 := by
      rw [hP]
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      rw [max_le_iff]
      refine ⟨?_, ?_⟩
      · refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
        rw [MvPolynomial.totalDegree_X]
      · have hinner : (MvPolynomial.X (yIdx p n j) - MvPolynomial.X (zIdx p n j) :
            MvPolynomial (Fin (p + (n + 1) + 1 + (n + 1))) ℝ).totalDegree ≤ 1 := by
          refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
          rw [max_le_iff]
          exact ⟨le_of_eq (MvPolynomial.totalDegree_X _),
                 le_of_eq (MvPolynomial.totalDegree_X _)⟩
        refine le_trans (MvPolynomial.totalDegree_pow _ 2) ?_
        omega
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := p + (n + 1) + 1 + (n + 1)) D P
    have hset : {W : Fin (p + (n + 1) + 1 + (n + 1)) → ℝ | 0 < MvPolynomial.eval W P}
        = {W : Fin (p + (n + 1) + 1 + (n + 1)) → ℝ |
            (W (yIdx p n j) - W (zIdx p n j)) ^ 2 < (W (dIdx p n)) ^ 2} := by
      ext W
      rw [hP]
      simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_pow,
        MvPolynomial.eval_X]
      constructor <;> intro hh <;> linarith
    rw [hset] at h
    have hdeg : (Polynomial.C (P.totalDegree + 2) : Polynomial ℕ).eval D ≤ 4 := by
      simp only [Polynomial.eval_C]; omega
    exact Work.WilG1.Omega.mono h le_rfl hdeg
  have h := S.inter (F := p + (n + 1) + 1 + (n + 1) + 2)
    (n := p + (n + 1) + 1 + (n + 1)) (k := n + 1)
    (fun _ : Fin (n + 1) => 4)
    (fun j : Fin (n + 1) => {W : Fin (p + (n + 1) + 1 + (n + 1)) → ℝ |
        (W (yIdx p n j) - W (zIdx p n j)) ^ 2 < (W (dIdx p n)) ^ 2})
    (by intro j; simpa using hbox j)
  have hsum : (∑ _ : Fin (n + 1), (4 : ℕ)) = (n + 1) * 4 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hsum] at h
  have hset2 : (⋂ j : Fin (n + 1), {W : Fin (p + (n + 1) + 1 + (n + 1)) → ℝ |
      (W (yIdx p n j) - W (zIdx p n j)) ^ 2 < (W (dIdx p n)) ^ 2}) = cell p n := by
    ext W; simp [cell]
  rw [hset2] at h
  exact Work.WilG1.Omega.mono h (by omega) le_rfl

/-! ## 3. The Fin plumbing -/

/-- `snocIt` is `Fin.append`. -/
theorem snocIt_eq_append (n m : ℕ) (x : Fin n → ℝ) (w : Fin m → ℝ) :
    Work.WilG0.snocIt n m x w = Fin.append x w := by
  funext i
  cases i using Fin.addCases with
  | left i' => rw [Work.WilG0.snocIt_castAdd, Fin.append_left]
  | right j => rw [Work.WilG0.snocIt_natAdd, Fin.append_right]

/-- `Fin.snoc x t` at the index `Fin.castAdd 1 i`. -/
theorem snoc_castAdd_one {n : ℕ} (x : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    (Fin.snoc x t : Fin (n + 1) → ℝ) (Fin.castAdd 1 i) = x i := by
  rw [show (Fin.castAdd 1 i : Fin (n + 1)) = Fin.castSucc i from Fin.ext rfl,
    Fin.snoc_castSucc]

theorem eval_dIdx {p n : ℕ} (v : Fin (p + (n + 1)) → ℝ) (t : ℝ) (y : Fin (n + 1) → ℝ) :
    (Fin.append (Fin.snoc v t) y) (dIdx p n) = t := by
  rw [dIdx, Fin.append_left, Fin.snoc_last]

theorem eval_yIdx {p n : ℕ} (v : Fin (p + (n + 1)) → ℝ) (t : ℝ) (y : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) :
    (Fin.append (Fin.snoc v t) y) (yIdx p n j) = y j := by
  rw [yIdx, Fin.append_right]

theorem eval_zIdx {p n : ℕ} (v : Fin (p + (n + 1)) → ℝ) (t : ℝ) (y : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) :
    (Fin.append (Fin.snoc v t) y) (zIdx p n j) = cubePt v j := by
  rw [zIdx, Fin.append_left, cubePt_apply, snoc_castAdd_one]

/-- The defining property of the pullback index `iota`. -/
theorem comp_iota {p n : ℕ} (v : Fin (p + (n + 1)) → ℝ) (t : ℝ) (y : Fin (n + 1) → ℝ) :
    Fin.append (Fin.snoc v t) y ∘ (iota p n) = Fin.append (parPt v) y := by
  funext i
  cases i using Fin.addCases with
  | left i' =>
      simp only [Function.comp_apply, iota, lIdx, yIdx, Fin.append_left,
        parPt_apply, snoc_castAdd_one]
  | right j =>
      simp only [Function.comp_apply, iota, yIdx, Fin.append_right]

/-! ## 4. Reading the cell and the pullback on the auxiliary point -/

theorem mem_cell_iff {p n : ℕ} (v : Fin (p + (n + 1)) → ℝ) (t : ℝ) (y : Fin (n + 1) → ℝ) :
    Work.WilG0.snocIt (p + (n + 1) + 1) (n + 1) (Fin.snoc v t) y ∈ cell p n ↔
      ∀ j : Fin (n + 1), (y j - cubePt v j) ^ 2 < t ^ 2 := by
  rw [cell, snocIt_eq_append]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h j
    have := h j
    rwa [eval_yIdx, eval_zIdx, eval_dIdx] at this
  · intro h j
    rw [eval_yIdx, eval_zIdx, eval_dIdx]
    exact h j

theorem mem_pre_iff {p n : ℕ} (X : Set (Fin (p + (n + 1)) → ℝ))
    (v : Fin (p + (n + 1)) → ℝ) (t : ℝ) (y : Fin (n + 1) → ℝ) :
    Work.WilG0.snocIt (p + (n + 1) + 1) (n + 1) (Fin.snoc v t) y ∈
        Work.WilG5.coordPre (iota p n) X ↔ Fin.append (parPt v) y ∈ X := by
  rw [snocIt_eq_append, Work.WilG5.coordPre, Set.mem_ofPred_eq, comp_iota]

/-! ## 5. The set identity -/

theorem aux_eq (p n : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)) :
    aux p n X = tgt p n X := by
  ext v
  rw [aux, tgt]
  simp only [projLast, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, Fin.snoc_last]
  constructor
  · rintro ⟨t, ht, hnot⟩
    rw [Work.WilG0.projLastIter_eq] at hnot
    refine ⟨t, ht, fun y hy => ?_⟩
    by_contra hyX
    apply hnot
    refine ⟨y, ?_, ?_⟩
    · rw [mem_cell_iff]
      intro j
      rw [sq_lt_sq, abs_of_pos ht]
      exact hy j
    · rw [Set.mem_compl_iff, mem_pre_iff]
      exact hyX
  · rintro ⟨t, ht, hy⟩
    refine ⟨t, ht, ?_⟩
    rw [Work.WilG0.projLastIter_eq]
    rintro ⟨w, h1, h2⟩
    have hcell := (mem_cell_iff v t w).mp h1
    have hpre : Fin.append (parPt v) w ∈ X := hy w (fun j => by
      rw [← abs_of_pos ht, ← sq_lt_sq]; exact hcell j)
    rw [Set.mem_compl_iff, mem_pre_iff] at h2
    exact h2 hpre

end Infl

/-! ## 6. The main theorem -/

theorem inflated_mem_m (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (A C : ℕ), ∀ (F D : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)), X ∈ S.Ω F D (p + (n + 1)) →
      {w : Fin (p + (n + 1)) → ℝ | ∃ δ : ℝ, 0 < δ ∧ ∀ y : Fin (n + 1) → ℝ,
        (∀ j, |y j - Work.WilkG4c.cubePt w j| < δ) →
          Fin.append (Work.WilkG4c.parPt w) y ∈ X} ∈
        S.Ω (F + A) (D + C) (p + (n + 1)) := by
  refine ⟨64 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + (n + 1)
            + (p + (n + 1) + 1) + 100,
          32 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + (n + 1) * 4 + 100, ?_⟩
  intro F D X hX
  change Infl.tgt p n X ∈ S.Ω (F + (64 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1)))
        + (n + 1) + (p + (n + 1) + 1) + 100))
      (D + (32 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + (n + 1) * 4 + 100))
      (p + (n + 1))
  rw [← Infl.aux_eq]
  unfold Infl.aux
  have hCell : Infl.cell p n ∈ S.Ω (p + (n + 1) + 1 + (n + 1) + 3) ((n + 1) * 4)
      (p + (n + 1) + 1 + (n + 1)) := Infl.cell_mem S p n D
  have hCell' : Infl.cell p n ∈
      S.Ω (F + 64 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + 64 + 1)
        ((n + 1) * 4) (p + (n + 1) + 1 + (n + 1)) :=
    Work.WilG1.Omega.mono hCell (by omega) le_rfl
  have hPre : Work.WilG5.coordPre (Infl.iota p n) X ∈
      S.Ω (F + 64 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + 64)
        (D + 32 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + 32)
        (p + (n + 1) + 1 + (n + 1)) := by
    have h := Work.WilG5.coordPre_mem (S := S) (m := p + (n + 1))
      (N := p + (n + 1) + 1 + (n + 1)) (ι := Infl.iota p n) hX
    exact h
  have hPrec : (Work.WilG5.coordPre (Infl.iota p n) X)ᶜ ∈
      S.Ω (F + 64 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + 64 + 1)
        (D + 32 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + 32)
        (p + (n + 1) + 1 + (n + 1)) :=
    S.compl hPre
  have hQ := Infl.inter2_same hCell' hPrec
  have hH' : Work.WilG0.projLastIter (p + (n + 1) + 1) (n + 1)
      (Infl.cell p n ∩ (Work.WilG5.coordPre (Infl.iota p n) X)ᶜ) ∈
      S.Ω ((F + 64 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + 64 + 1 + 1)
          + (n + 1) + (p + (n + 1) + 1))
        ((n + 1) * 4 + (D + 32 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + 32))
        (p + (n + 1) + 1) :=
    Work.WilG0.projLastIter_mem S (p + (n + 1) + 1) (n + 1) _ _ _ hQ
  have hHc : (Work.WilG0.projLastIter (p + (n + 1) + 1) (n + 1)
      (Infl.cell p n ∩ (Work.WilG5.coordPre (Infl.iota p n) X)ᶜ))ᶜ ∈
      S.Ω ((F + 64 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + 64 + 1 + 1)
          + (n + 1) + (p + (n + 1) + 1) + 1)
        ((n + 1) * 4 + (D + 32 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + 32))
        (p + (n + 1) + 1) :=
    S.compl hH'
  have hPos' : {v : Fin (p + (n + 1) + 1) → ℝ | 0 < v (Fin.last (p + (n + 1)))} ∈
      S.Ω ((F + 64 * ((p + (n + 1) + 1 + (n + 1)) + (p + (n + 1))) + 64 + 1 + 1)
          + (n + 1) + (p + (n + 1) + 1) + 1) 3 (p + (n + 1) + 1) :=
    Work.WilG1.Omega.mono (Infl.posLast_mem S p n D) (by omega) le_rfl
  have hM := Infl.inter2_same hPos' hHc
  have hmain := S.proj hM
  exact Work.WilG1.Omega.mono hmain (by omega) (by omega)

end Work.WilkG4c

/-! ## 7. Same statement under the directory's other namespace spellings

The directory `Submission/Work/WilG4c/` contains files using both the namespace `Work.WilkG4c`
(this file's `SlicedDerivDefs`, `SliceNilDefs`, ...) and the namespace `Work.WilG4c` (the
spelling induced by the directory name).  The alias below makes the theorem available under the
directory-induced name `Work.WilG4c.inflated_mem_m` as well. -/

namespace Work.WilG4c

theorem inflated_mem_m (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (A C : ℕ), ∀ (F D : ℕ) (X : Set (Fin (p + (n + 1)) → ℝ)), X ∈ S.Ω F D (p + (n + 1)) →
      {w : Fin (p + (n + 1)) → ℝ | ∃ δ : ℝ, 0 < δ ∧ ∀ y : Fin (n + 1) → ℝ,
        (∀ j, |y j - Work.WilkG4c.cubePt w j| < δ) →
          Fin.append (Work.WilkG4c.parPt w) y ∈ X} ∈
        S.Ω (F + A) (D + C) (p + (n + 1)) :=
  _root_.Work.WilkG4c.inflated_mem_m S p n

end Work.WilG4c
