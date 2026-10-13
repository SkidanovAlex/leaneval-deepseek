/-
  WilG1 / Cell / Junk / DiscDefs.

  Vocabulary for the proof that the discontinuity locus of an `Ω`-definable function is
  `Ω`-definable (`Work.WilG1.Cell.Junk.disc_mem`).

  For `h : ℝⁿ → ℝ` with `graphOf h` an `Ω`-set, the set `disc h = {y | ¬ ContinuousAt h y}` is

    `{y | ∃ ε > 0, ∀ δ > 0, ∃ x, Q(x,y) < δ² ∧ ε² ≤ (h x - h y)²}`,

  where `Q(x,y) = Σ_j (x_j - y_j)²`.  The quantifiers are eliminated by the standard chain of
  projections and complements in the big space

    `ℝ^big`,  `big = (n+2) + (n+2)`,  coordinates `(y, ε, δ | x, s, t)`

  (`y` the point at which continuity is tested, `ε`, `δ` the tolerances, `x` the nearby point,
  `s` the value `h x` and `t` the value `h y`).  The pieces of the inner (quantifier-free) set
  are

  * `grXSet n h` — `s = h x`, a reindexed copy of `graphOf h` (`coordPre`);
  * `grYSet n h` — `t = h y`, likewise;
  * `ballSet n` — `Q(x,y) < δ²`, the positivity set of `δ² - Σ_j (x_j - y_j)²`;
  * `ineqSet n` — `ε² ≤ (s-t)²`, the complement of the positivity set of `ε² - (s-t)²`.

  The quantifier chain is

    `innerSet`          (no quantifier)
    `bodySet`   = `projN (n+2) innerSet`                     `∃ x s t`
    `existDSet` = `projN 1 (posDSet ∩ bodySetᶜ)`             `∃ δ > 0, ¬ ·`
    `forallDSet` = `existDSetᶜ`                              `∀ δ > 0`
    `resBSet`   = `posESet ∩ forallDSet`                     `ε > 0 ∧ ·`
    `resSet`    = `projN 1 resBSet`                          `∃ ε > 0`

  so that `resSet n h = disc h`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical
open scoped BigOperators

namespace Work.WilG1.Cell.Junk

open WilkiesDesign WilkiesConjecture

variable {S : WilkiesDesign.SOMin}

/-! ## 1. Dimensions and index maps -/

/-- Dimension of the big space `(y, ε, δ | x, s, t)`. -/
abbrev bigDim (n : ℕ) : ℕ := ((n + 1) + 1) + (n + 2)

/-- Dimension of the space `(y, ε, δ)`. -/
abbrev aDim (n : ℕ) : ℕ := (n + 1) + 1

/-- Dimension of the space `(y, ε)`. -/
abbrev bDim (n : ℕ) : ℕ := n + 1

/-- The `j`-th `y`-coordinate in the space `(y, ε)`. -/
def yIdxB (n : ℕ) (j : Fin n) : Fin (bDim n) := Fin.castAdd 1 j

/-- The `ε`-coordinate in the space `(y, ε)`. -/
def eIdxB (n : ℕ) : Fin (bDim n) := Fin.natAdd n (0 : Fin 1)

/-- The `j`-th `y`-coordinate in the space `(y, ε, δ)`. -/
def yIdxA (n : ℕ) (j : Fin n) : Fin (aDim n) := Fin.castAdd 1 (yIdxB n j)

/-- The `ε`-coordinate in the space `(y, ε, δ)`. -/
def eIdxA (n : ℕ) : Fin (aDim n) := Fin.castAdd 1 (eIdxB n)

/-- The `δ`-coordinate in the space `(y, ε, δ)`. -/
def dIdxA (n : ℕ) : Fin (aDim n) := Fin.natAdd (n + 1) (0 : Fin 1)

/-- The `j`-th `y`-coordinate in the big space. -/
def yIdx (n : ℕ) (j : Fin n) : Fin (bigDim n) := Fin.castAdd (n + 2) (yIdxA n j)

/-- The `ε`-coordinate in the big space. -/
def eIdx (n : ℕ) : Fin (bigDim n) := Fin.castAdd (n + 2) (eIdxA n)

/-- The `δ`-coordinate in the big space. -/
def dIdx (n : ℕ) : Fin (bigDim n) := Fin.castAdd (n + 2) (dIdxA n)

/-- The `j`-th `x`-coordinate in the big space. -/
def xIdx (n : ℕ) (j : Fin n) : Fin (bigDim n) := Fin.natAdd (aDim n) (Fin.castAdd 2 j)

/-- The `s`-coordinate (`s = h x`) in the big space. -/
def sIdx (n : ℕ) : Fin (bigDim n) := Fin.natAdd (aDim n) (Fin.natAdd n (0 : Fin 2))

/-- The `t`-coordinate (`t = h y`) in the big space. -/
def tIdx (n : ℕ) : Fin (bigDim n) := Fin.natAdd (aDim n) (Fin.natAdd n (1 : Fin 2))

/-! ## 2. Reading `Fin.append`-points in coordinates -/

/-- A function `Fin 1 → ℝ` is determined by its value at `0`. -/
theorem fin1_ext (e : Fin 1 → ℝ) : e = fun _ => e 0 := by
  funext i
  fin_cases i
  rfl

@[simp] theorem appB_yIdxB (n : ℕ) (y : Fin n → ℝ) (e : Fin 1 → ℝ) (j : Fin n) :
    Fin.append y e (yIdxB n j) = y j := by
  rw [yIdxB, Fin.append_left]

@[simp] theorem appB_eIdxB (n : ℕ) (y : Fin n → ℝ) (e : Fin 1 → ℝ) :
    Fin.append y e (eIdxB n) = e 0 := by
  rw [eIdxB, Fin.append_right]

@[simp] theorem appA_yIdxA (n : ℕ) (u : Fin (bDim n) → ℝ) (d : Fin 1 → ℝ) (j : Fin n) :
    Fin.append u d (yIdxA n j) = u (yIdxB n j) := by
  rw [yIdxA, Fin.append_left]

@[simp] theorem appA_eIdxA (n : ℕ) (u : Fin (bDim n) → ℝ) (d : Fin 1 → ℝ) :
    Fin.append u d (eIdxA n) = u (eIdxB n) := by
  rw [eIdxA, Fin.append_left]

@[simp] theorem appA_dIdxA (n : ℕ) (u : Fin (bDim n) → ℝ) (d : Fin 1 → ℝ) :
    Fin.append u d (dIdxA n) = d 0 := by
  rw [dIdxA, Fin.append_right]

@[simp] theorem appAA_yIdxA (n : ℕ) (y : Fin n → ℝ) (e d : Fin 1 → ℝ) (j : Fin n) :
    Fin.append (Fin.append y e) d (yIdxA n j) = y j := by
  rw [appA_yIdxA, appB_yIdxB]

@[simp] theorem appAA_eIdxA (n : ℕ) (y : Fin n → ℝ) (e d : Fin 1 → ℝ) :
    Fin.append (Fin.append y e) d (eIdxA n) = e 0 := by
  rw [appA_eIdxA, appB_eIdxB]

@[simp] theorem appAA_dIdxA (n : ℕ) (y : Fin n → ℝ) (e d : Fin 1 → ℝ) :
    Fin.append (Fin.append y e) d (dIdxA n) = d 0 := by
  rw [appA_dIdxA]

@[simp] theorem appW_yIdx (n : ℕ) (u : Fin (aDim n) → ℝ) (w : Fin (n + 2) → ℝ) (j : Fin n) :
    Fin.append u w (yIdx n j) = u (yIdxA n j) := by
  rw [yIdx, Fin.append_left]

@[simp] theorem appW_eIdx (n : ℕ) (u : Fin (aDim n) → ℝ) (w : Fin (n + 2) → ℝ) :
    Fin.append u w (eIdx n) = u (eIdxA n) := by
  rw [eIdx, Fin.append_left]

@[simp] theorem appW_dIdx (n : ℕ) (u : Fin (aDim n) → ℝ) (w : Fin (n + 2) → ℝ) :
    Fin.append u w (dIdx n) = u (dIdxA n) := by
  rw [dIdx, Fin.append_left]

@[simp] theorem appW_xIdx (n : ℕ) (u : Fin (aDim n) → ℝ) (w : Fin (n + 2) → ℝ) (j : Fin n) :
    Fin.append u w (xIdx n j) = w (Fin.castAdd 2 j) := by
  rw [xIdx, Fin.append_right]

@[simp] theorem appW_sIdx (n : ℕ) (u : Fin (aDim n) → ℝ) (w : Fin (n + 2) → ℝ) :
    Fin.append u w (sIdx n) = w (Fin.natAdd n (0 : Fin 2)) := by
  rw [sIdx, Fin.append_right]

@[simp] theorem appW_tIdx (n : ℕ) (u : Fin (aDim n) → ℝ) (w : Fin (n + 2) → ℝ) :
    Fin.append u w (tIdx n) = w (Fin.natAdd n (1 : Fin 2)) := by
  rw [tIdx, Fin.append_right]

/-- The point `(y, ε, δ | x, s, t)` of the big space. -/
def asm (n : ℕ) (y : Fin n → ℝ) (ε δ : ℝ) (x : Fin n → ℝ) (s t : ℝ) : Fin (bigDim n) → ℝ :=
  Fin.append (Fin.append (Fin.append y (fun _ : Fin 1 => ε)) (fun _ : Fin 1 => δ))
    (Fin.append x ![s, t])

@[simp] theorem asm_yIdx (n : ℕ) (y : Fin n → ℝ) (ε δ : ℝ) (x : Fin n → ℝ) (s t : ℝ)
    (j : Fin n) : asm n y ε δ x s t (yIdx n j) = y j := by
  simp [asm, Fin.append_left, Fin.append_right]

@[simp] theorem asm_eIdx (n : ℕ) (y : Fin n → ℝ) (ε δ : ℝ) (x : Fin n → ℝ) (s t : ℝ) :
    asm n y ε δ x s t (eIdx n) = ε := by
  simp [asm, Fin.append_left, Fin.append_right]

@[simp] theorem asm_dIdx (n : ℕ) (y : Fin n → ℝ) (ε δ : ℝ) (x : Fin n → ℝ) (s t : ℝ) :
    asm n y ε δ x s t (dIdx n) = δ := by
  simp [asm, Fin.append_left, Fin.append_right]

@[simp] theorem asm_xIdx (n : ℕ) (y : Fin n → ℝ) (ε δ : ℝ) (x : Fin n → ℝ) (s t : ℝ)
    (j : Fin n) : asm n y ε δ x s t (xIdx n j) = x j := by
  simp [asm, Fin.append_left, Fin.append_right]

@[simp] theorem asm_sIdx (n : ℕ) (y : Fin n → ℝ) (ε δ : ℝ) (x : Fin n → ℝ) (s t : ℝ) :
    asm n y ε δ x s t (sIdx n) = s := by
  simp [asm, Fin.append_left, Fin.append_right]

@[simp] theorem asm_tIdx (n : ℕ) (y : Fin n → ℝ) (ε δ : ℝ) (x : Fin n → ℝ) (s t : ℝ) :
    asm n y ε δ x s t (tIdx n) = t := by
  simp [asm, Fin.append_left, Fin.append_right]

/-! ## 3. The pieces of the inner set -/

/-- Reading `(x, s)` as a point of `ℝ^{n+1}`. -/
def lastMapX (n : ℕ) : Fin (n + 1) → Fin (bigDim n) :=
  Fin.lastCases (motive := fun _ => Fin (bigDim n)) (sIdx n) (fun j => xIdx n j)

/-- Reading `(y, t)` as a point of `ℝ^{n+1}`. -/
def lastMapY (n : ℕ) : Fin (n + 1) → Fin (bigDim n) :=
  Fin.lastCases (motive := fun _ => Fin (bigDim n)) (tIdx n) (fun j => yIdx n j)

/-- The condition `s = h x`. -/
def grXSet (n : ℕ) (h : (Fin n → ℝ) → ℝ) : Set (Fin (bigDim n) → ℝ) :=
  Work.WilG5.coordPre (lastMapX n) (graphOf h)

/-- The condition `t = h y`. -/
def grYSet (n : ℕ) (h : (Fin n → ℝ) → ℝ) : Set (Fin (bigDim n) → ℝ) :=
  Work.WilG5.coordPre (lastMapY n) (graphOf h)

/-- The polynomial `δ² - Σ_j (x_j - y_j)²` whose positivity set is `Q(x,y) < δ²`. -/
def ballPoly (n : ℕ) : MvPolynomial (Fin (bigDim n)) ℝ :=
  MvPolynomial.X (dIdx n) ^ 2 -
    ∑ j : Fin n, (MvPolynomial.X (xIdx n j) - MvPolynomial.X (yIdx n j)) ^ 2

/-- The condition `Q(x,y) < δ²`. -/
def ballSet (n : ℕ) : Set (Fin (bigDim n) → ℝ) :=
  {z | 0 < MvPolynomial.eval z (ballPoly n)}

/-- The polynomial `ε² - (s - t)²`. -/
def ineqPoly (n : ℕ) : MvPolynomial (Fin (bigDim n)) ℝ :=
  MvPolynomial.X (eIdx n) ^ 2 - (MvPolynomial.X (sIdx n) - MvPolynomial.X (tIdx n)) ^ 2

/-- The condition `ε² < (s - t)²`, kept as a positivity set. -/
def ineqPosSet (n : ℕ) : Set (Fin (bigDim n) → ℝ) :=
  {z | 0 < MvPolynomial.eval z (ineqPoly n)}

/-- The condition `ε² ≤ (s - t)²`. -/
def ineqSet (n : ℕ) : Set (Fin (bigDim n) → ℝ) := (ineqPosSet n)ᶜ

/-- The quantifier-free matrix of the continuity condition. -/
def innerSet (n : ℕ) (h : (Fin n → ℝ) → ℝ) : Set (Fin (bigDim n) → ℝ) :=
  ((grXSet n h ∩ grYSet n h) ∩ ballSet n) ∩ ineqSet n

/-! ## 4. The quantifier chain -/

/-- `δ > 0` in the space `(y, ε, δ)`. -/
def posDSet (n : ℕ) : Set (Fin (aDim n) → ℝ) := {z | 0 < z (dIdxA n)}

/-- `ε > 0` in the space `(y, ε)`. -/
def posESet (n : ℕ) : Set (Fin (bDim n) → ℝ) := {z | 0 < z (eIdxB n)}

/-- `∃ x s t`: the `(y,ε,δ)`-parameters for which some nearby point witnesses the oscillation. -/
def bodySet (n : ℕ) (h : (Fin n → ℝ) → ℝ) : Set (Fin (aDim n) → ℝ) :=
  Work.WilG5.projN (n := aDim n) (n + 2) (innerSet n h)

/-- `∃ δ > 0` with the body failing. -/
def existDSet (n : ℕ) (h : (Fin n → ℝ) → ℝ) : Set (Fin (bDim n) → ℝ) :=
  Work.WilG5.projN (n := bDim n) 1 (posDSet n ∩ (bodySet n h)ᶜ)

/-- `∀ δ > 0`, the body holding. -/
def forallDSet (n : ℕ) (h : (Fin n → ℝ) → ℝ) : Set (Fin (bDim n) → ℝ) :=
  (existDSet n h)ᶜ

/-- `ε > 0` and the `∀ δ > 0` condition. -/
def resBSet (n : ℕ) (h : (Fin n → ℝ) → ℝ) : Set (Fin (bDim n) → ℝ) :=
  posESet n ∩ forallDSet n h

/-- `∃ ε > 0`; this is the discontinuity locus of `h`. -/
def resSet (n : ℕ) (h : (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) :=
  Work.WilG5.projN (n := n) 1 (resBSet n h)

/-! ## 5. Unfolding the pieces -/

theorem mem_grXSet {n : ℕ} {h : (Fin n → ℝ) → ℝ} {z : Fin (bigDim n) → ℝ} :
    z ∈ grXSet n h ↔ z (sIdx n) = h (fun j => z (xIdx n j)) := by
  simp only [grXSet, Work.WilG5.coordPre, Set.mem_ofPred_eq, graphOf, Function.comp_def]
  have hlast : lastMapX n (Fin.last n) = sIdx n := Fin.lastCases_last
  have hcast : ∀ j : Fin n, lastMapX n (Fin.castSucc j) = xIdx n j :=
    fun j => Fin.lastCases_castSucc j
  have hinit : Fin.init (fun j => z (lastMapX n j)) = fun j : Fin n => z (xIdx n j) := by
    funext j
    show z (lastMapX n (Fin.castSucc j)) = z (xIdx n j)
    rw [hcast j]
  rw [hlast, hinit]

theorem mem_grYSet {n : ℕ} {h : (Fin n → ℝ) → ℝ} {z : Fin (bigDim n) → ℝ} :
    z ∈ grYSet n h ↔ z (tIdx n) = h (fun j => z (yIdx n j)) := by
  simp only [grYSet, Work.WilG5.coordPre, Set.mem_ofPred_eq, graphOf, Function.comp_def]
  have hlast : lastMapY n (Fin.last n) = tIdx n := Fin.lastCases_last
  have hcast : ∀ j : Fin n, lastMapY n (Fin.castSucc j) = yIdx n j :=
    fun j => Fin.lastCases_castSucc j
  have hinit : Fin.init (fun j => z (lastMapY n j)) = fun j : Fin n => z (yIdx n j) := by
    funext j
    show z (lastMapY n (Fin.castSucc j)) = z (yIdx n j)
    rw [hcast j]
  rw [hlast, hinit]

theorem eval_ballPoly (n : ℕ) (z : Fin (bigDim n) → ℝ) :
    MvPolynomial.eval z (ballPoly n) =
      z (dIdx n) ^ 2 - ∑ j : Fin n, (z (xIdx n j) - z (yIdx n j)) ^ 2 := by
  simp only [ballPoly, MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_sum,
    MvPolynomial.eval_X]

theorem mem_ballSet {n : ℕ} {z : Fin (bigDim n) → ℝ} :
    z ∈ ballSet n ↔
      (∑ j : Fin n, (z (xIdx n j) - z (yIdx n j)) ^ 2) < z (dIdx n) ^ 2 := by
  rw [ballSet, Set.mem_ofPred_eq, eval_ballPoly]
  constructor <;> intro h <;> linarith

theorem eval_ineqPoly (n : ℕ) (z : Fin (bigDim n) → ℝ) :
    MvPolynomial.eval z (ineqPoly n) =
      z (eIdx n) ^ 2 - (z (sIdx n) - z (tIdx n)) ^ 2 := by
  simp only [ineqPoly, MvPolynomial.eval_sub, MvPolynomial.eval_pow, MvPolynomial.eval_X]

theorem mem_ineqSet {n : ℕ} {z : Fin (bigDim n) → ℝ} :
    z ∈ ineqSet n ↔ z (eIdx n) ^ 2 ≤ (z (sIdx n) - z (tIdx n)) ^ 2 := by
  show ¬ (0 < MvPolynomial.eval z (ineqPoly n)) ↔
    z (eIdx n) ^ 2 ≤ (z (sIdx n) - z (tIdx n)) ^ 2
  rw [eval_ineqPoly]
  constructor <;> intro h <;> linarith

theorem mem_innerSet {n : ℕ} {h : (Fin n → ℝ) → ℝ} {z : Fin (bigDim n) → ℝ} :
    z ∈ innerSet n h ↔
      z (sIdx n) = h (fun j => z (xIdx n j)) ∧
      z (tIdx n) = h (fun j => z (yIdx n j)) ∧
      (∑ j : Fin n, (z (xIdx n j) - z (yIdx n j)) ^ 2) < z (dIdx n) ^ 2 ∧
      z (eIdx n) ^ 2 ≤ (z (sIdx n) - z (tIdx n)) ^ 2 := by
  show ((z ∈ grXSet n h ∧ z ∈ grYSet n h) ∧ z ∈ ballSet n) ∧ z ∈ ineqSet n ↔
      z (sIdx n) = h (fun j => z (xIdx n j)) ∧
      z (tIdx n) = h (fun j => z (yIdx n j)) ∧
      (∑ j : Fin n, (z (xIdx n j) - z (yIdx n j)) ^ 2) < z (dIdx n) ^ 2 ∧
      z (eIdx n) ^ 2 ≤ (z (sIdx n) - z (tIdx n)) ^ 2
  simp only [mem_grXSet, mem_grYSet, mem_ballSet, mem_ineqSet]
  tauto

/-! ## 6. The existential format/degree wrapper -/

/-- `X ∈ S.Ω a (b.eval D) m` for *some* `a` and `b`: the format is a numeral and the degree a
polynomial in the parameter `D`. -/
def OA (S : WilkiesDesign.SOMin) (D m : ℕ) (X : Set (Fin m → ℝ)) : Prop :=
  ∃ a : ℕ, ∃ b : Polynomial ℕ, X ∈ S.Ω a (b.eval D) m

theorem OA.compl {D m : ℕ} {X : Set (Fin m → ℝ)} (h : OA S D m X) : OA S D m Xᶜ := by
  obtain ⟨a, b, hb⟩ := h
  exact ⟨a + 1, b, S.compl hb⟩

theorem OA.inter {D m : ℕ} {X Y : Set (Fin m → ℝ)} (hX : OA S D m X) (hY : OA S D m Y) :
    OA S D m (X ∩ Y) := by
  obtain ⟨a₁, b₁, h₁⟩ := hX
  obtain ⟨a₂, b₂, h₂⟩ := hY
  exact ⟨max a₁ a₂ + 1, b₁ + b₂, Work.WilG1.Omega.inter₂ h₁ h₂⟩

theorem OA.union {D m : ℕ} {X Y : Set (Fin m → ℝ)} (hX : OA S D m X) (hY : OA S D m Y) :
    OA S D m (X ∪ Y) := by
  obtain ⟨a₁, b₁, h₁⟩ := hX
  obtain ⟨a₂, b₂, h₂⟩ := hY
  exact ⟨max a₁ a₂, b₁ + b₂, Work.WilG1.Omega.union₂ h₁ h₂⟩

theorem OA.projN {D m k : ℕ} {X : Set (Fin (m + k) → ℝ)} (h : OA S D (m + k) X) :
    OA S D m (Work.WilG5.projN k X) := by
  obtain ⟨a, b, hb⟩ := h
  exact ⟨a + k, b, Work.WilG5.projN_mem (S := S) (n := m) k a (b.eval D) hb⟩

theorem OA.coordPre {D m N : ℕ} {ι : Fin m → Fin N} {A : Set (Fin m → ℝ)}
    (h : OA S D m A) : OA S D N (Work.WilG5.coordPre ι A) := by
  obtain ⟨a, b, hb⟩ := h
  exact ⟨a + 64 * (N + m) + 64, b + Polynomial.C (32 * (N + m) + 32),
    by rw [Polynomial.eval_add, Polynomial.eval_C]
       exact Work.WilG5.coordPre_mem (S := S) (F := a) (D := b.eval D) hb⟩

theorem OA.pos {D m : ℕ} (P : MvPolynomial (Fin m) ℝ) :
    OA S D m {z | 0 < MvPolynomial.eval z P} :=
  ⟨m + 2, Polynomial.C (P.totalDegree + 2),
    Work.WilG1.Calc.pos_mem (S := S) (m := m) D P⟩

theorem OA.hyp {D m : ℕ} (P : MvPolynomial (Fin m) ℝ) :
    OA S D m {z | MvPolynomial.eval z P = 0} :=
  ⟨m, Polynomial.C P.totalDegree, by simpa using S.hyp m P⟩

/-! ## 7. `Ω`-membership of the pieces -/

theorem grXSet_mem {n F D : ℕ} {h : (Fin n → ℝ) → ℝ}
    (hh : graphOf h ∈ S.Ω F D (n + 1)) : OA S D (bigDim n) (grXSet n h) := by
  have h : OA S D (n + 1) (graphOf h) := ⟨F, Polynomial.C D, by simpa using hh⟩
  exact OA.coordPre (S := S) (D := D) (m := n + 1) (N := bigDim n) (ι := lastMapX n) h

theorem grYSet_mem {n F D : ℕ} {h : (Fin n → ℝ) → ℝ}
    (hh : graphOf h ∈ S.Ω F D (n + 1)) : OA S D (bigDim n) (grYSet n h) := by
  have h : OA S D (n + 1) (graphOf h) := ⟨F, Polynomial.C D, by simpa using hh⟩
  exact OA.coordPre (S := S) (D := D) (m := n + 1) (N := bigDim n) (ι := lastMapY n) h

theorem ballSet_mem (n D : ℕ) : OA S D (bigDim n) (ballSet n) :=
  OA.pos (S := S) (D := D) (ballPoly n)

theorem ineqSet_mem (n D : ℕ) : OA S D (bigDim n) (ineqSet n) :=
  OA.compl (OA.pos (S := S) (D := D) (ineqPoly n))

theorem posDSet_mem (n D : ℕ) : OA S D (aDim n) (posDSet n) := by
  obtain ⟨a, b, hb⟩ := OA.pos (S := S) (D := D) (m := aDim n)
    (MvPolynomial.X (dIdxA n) : MvPolynomial (Fin (aDim n)) ℝ)
  exact ⟨a, b, by simpa [posDSet, MvPolynomial.eval_X] using hb⟩

theorem posESet_mem (n D : ℕ) : OA S D (bDim n) (posESet n) := by
  obtain ⟨a, b, hb⟩ := OA.pos (S := S) (D := D) (m := bDim n)
    (MvPolynomial.X (eIdxB n) : MvPolynomial (Fin (bDim n)) ℝ)
  exact ⟨a, b, by simpa [posESet, MvPolynomial.eval_X] using hb⟩

theorem innerSet_mem {n F D : ℕ} {h : (Fin n → ℝ) → ℝ}
    (hh : graphOf h ∈ S.Ω F D (n + 1)) : OA S D (bigDim n) (innerSet n h) :=
  (((grXSet_mem (S := S) hh).inter (grYSet_mem (S := S) hh)).inter
    (ballSet_mem (S := S) n D)).inter (ineqSet_mem (S := S) n D)

theorem bodySet_mem {n F D : ℕ} {h : (Fin n → ℝ) → ℝ}
    (hh : graphOf h ∈ S.Ω F D (n + 1)) : OA S D (aDim n) (bodySet n h) :=
  OA.projN (S := S) (m := aDim n) (k := n + 2) (innerSet_mem (S := S) hh)

theorem existDSet_mem {n F D : ℕ} {h : (Fin n → ℝ) → ℝ}
    (hh : graphOf h ∈ S.Ω F D (n + 1)) : OA S D (bDim n) (existDSet n h) :=
  OA.projN (S := S) (m := bDim n) (k := 1)
    ((posDSet_mem (S := S) n D).inter (bodySet_mem (S := S) hh).compl)

theorem forallDSet_mem {n F D : ℕ} {h : (Fin n → ℝ) → ℝ}
    (hh : graphOf h ∈ S.Ω F D (n + 1)) : OA S D (bDim n) (forallDSet n h) :=
  (existDSet_mem (S := S) hh).compl

theorem resBSet_mem {n F D : ℕ} {h : (Fin n → ℝ) → ℝ}
    (hh : graphOf h ∈ S.Ω F D (n + 1)) : OA S D (bDim n) (resBSet n h) :=
  (posESet_mem (S := S) n D).inter (forallDSet_mem (S := S) hh)

/-- The discontinuity locus is `Ω`-definable with a format given by a numeral and a degree
polynomial in `D`. -/
theorem resSet_mem {n F D : ℕ} {h : (Fin n → ℝ) → ℝ}
    (hh : graphOf h ∈ S.Ω F D (n + 1)) : OA S D n (resSet n h) :=
  OA.projN (S := S) (m := n) (k := 1) (resBSet_mem (S := S) hh)

/-! ## 8. Unfolding the existential stages -/

/-- The meaning of `bodySet`: the `(y,ε,δ)`-parameters admitting a nearby point `x` with
`Q(x,y) < δ²` and `ε² ≤ (h x - h y)²`. -/
theorem mem_bodySet {n : ℕ} {h : (Fin n → ℝ) → ℝ} {u : Fin (aDim n) → ℝ} :
    u ∈ bodySet n h ↔
      ∃ x : Fin n → ℝ,
        (∑ j : Fin n, (x j - u (yIdxA n j)) ^ 2) < u (dIdxA n) ^ 2 ∧
        u (eIdxA n) ^ 2 ≤ (h x - h (fun j => u (yIdxA n j))) ^ 2 := by
  rw [bodySet, Work.WilG5.projN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw⟩
    rw [mem_innerSet] at hw
    simp only [appW_yIdx, appW_eIdx, appW_dIdx, appW_xIdx, appW_sIdx, appW_tIdx] at hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    refine ⟨fun j => w (Fin.castAdd 2 j), h3, ?_⟩
    rw [h1, h2] at h4
    exact h4
  · rintro ⟨x, h3, h4⟩
    refine ⟨Fin.append x ![h x, h (fun j => u (yIdxA n j))], ?_⟩
    rw [mem_innerSet]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using h3
    · simpa using h4

/-- `ε > 0` read on a point of the space `(y, ε)`. -/
theorem mem_posESet_append {n : ℕ} {y : Fin n → ℝ} {e : Fin 1 → ℝ} :
    Fin.append y e ∈ posESet n ↔ 0 < e 0 := by
  rw [posESet, Set.mem_ofPred_eq, appB_eIdxB]

/-- `∀ δ > 0` read on a point of the space `(y, ε)`. -/
theorem mem_forallDSet_append {n : ℕ} {h : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ}
    {e : Fin 1 → ℝ} :
    Fin.append y e ∈ forallDSet n h ↔
      ∀ d : Fin 1 → ℝ, 0 < d 0 → Fin.append (Fin.append y e) d ∈ bodySet n h := by
  rw [forallDSet, Set.mem_compl_iff, existDSet, Work.WilG5.projN, Set.mem_ofPred_eq,
    not_exists]
  constructor
  · intro H d hd
    by_contra hc
    refine H d ⟨?_, ?_⟩
    · rw [posDSet, Set.mem_ofPred_eq, appAA_dIdxA]
      exact hd
    · rw [Set.mem_compl_iff]
      exact hc
  · intro H d hd
    obtain ⟨hd1, hd2⟩ := hd
    rw [posDSet, Set.mem_ofPred_eq, appAA_dIdxA] at hd1
    rw [Set.mem_compl_iff] at hd2
    exact hd2 (H d hd1)

/-- The meaning of `resSet`: the standard `ε`-`δ` form of discontinuity. -/
theorem mem_resSet {n : ℕ} {h : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} :
    y ∈ resSet n h ↔
      ∃ ε > 0, ∀ δ > 0, ∃ x : Fin n → ℝ,
        (∑ j : Fin n, (x j - y j) ^ 2) < δ ^ 2 ∧ ε ^ 2 ≤ (h x - h y) ^ 2 := by
  rw [resSet, Work.WilG5.projN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, he⟩
    rw [resBSet, Set.mem_inter_iff] at he
    obtain ⟨he1, he2⟩ := he
    rw [mem_posESet_append] at he1
    rw [mem_forallDSet_append] at he2
    refine ⟨e 0, he1, fun δ hδ => ?_⟩
    have hb := he2 (fun _ : Fin 1 => δ) (by simpa using hδ)
    rw [mem_bodySet] at hb
    simp only [appAA_yIdxA, appAA_eIdxA, appAA_dIdxA] at hb
    exact hb
  · rintro ⟨ε, hε, H⟩
    refine ⟨fun _ : Fin 1 => ε, ?_⟩
    rw [resBSet, Set.mem_inter_iff]
    refine ⟨?_, ?_⟩
    · rw [mem_posESet_append]
      simpa using hε
    · rw [mem_forallDSet_append]
      intro d hd
      rw [mem_bodySet]
      obtain ⟨x, hx1, hx2⟩ := H (d 0) hd
      refine ⟨x, ?_, ?_⟩
      · simpa only [appAA_yIdxA, appAA_eIdxA, appAA_dIdxA] using hx1
      · simpa only [appAA_yIdxA, appAA_eIdxA, appAA_dIdxA] using hx2

end Work.WilG1.Cell.Junk
