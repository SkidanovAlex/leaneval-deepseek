/-
  WilG1 / Plumb / DerivDefs.

  Vocabulary for the proof that the graph of the "junk partial" `junkPartial i f` is an
  `Ω`-set, whenever `graphOf f` is.

  `junkPartial i f` is the `deriv` of the one-variable function
  `t ↦ f (i.insertNth t (i.removeNth x))`, so (Mathlib's) `deriv` is a *first-order* function of
  `graphOf f`: differentiability and the value of the derivative are expressed with an
  `ε`-`δ` formula over the graph.  This file sets up the vocabulary of that construction.

  ## The layout

  Fix `N : ℕ` (the number of variables of `f`) and `i : Fin N`.  The construction lives in the
  big space

    `ℝ^big`,  `big = (N+3) + (N+2)`, with coordinates

      `(x, c, ε, δ | y, u, w)`

  (`x : Fin N` the point at which we differentiate, `c` the candidate derivative, `ε`, `δ` the
  tolerance and radius, `y` a second point, `u`, `w` the values `f y`, `f x`).  The nested
  quantifiers of the `ε`-`δ` formula are eliminated by projecting the *last* coordinates first:

    * `innerSet`     : the matrix of the implication (no quantifiers);
    * `projYSet`     : `(projN (N+2) innerSetᶜ)ᶜ`, i.e. `∀ y u w`;
    * `projDSet`     : `projN 1 (posD ∩ projYSet)`, i.e. `∃ δ > 0`;
    * `Sset`         : `(projN 1 (posE ∩ projDSetᶜ))ᶜ`, i.e. `∀ ε > 0`,

  where `posD` is `δ > 0` (in the space `(x,c,ε,δ)`) and `posE` is `ε > 0` (in `(x,c,ε)`).

  The key estimate is a *polynomial* one: for `ε > 0` (and `δ > 0`) the first-order conditions

    `|y i - x i| < δ`,   `|f y - f x - c * (y i - x i)| ≤ ε * |y i - x i|`

  are equivalent to the polynomial conditions

    `(y i - x i)^2 < δ^2`,  `(f y - f x - c * (y i - x i))^2 ≤ ε^2 * (y i - x i)^2`,

  so no square root and no `abs` has to be eliminated: every piece of `innerSet` is either a
  hypersurface, a positivity set of a polynomial, or a reindexed copy of `graphOf f`.
-/
import Mathlib
import Submission.Work.WilG1.Plumb.Imports
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Calc.pos_mem

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical

namespace Work.WilG1.Plumb

open WilkiesDesign WilkiesConjecture

variable {S : SOMin}

/-! ## 1. The dimensions and the index maps -/

/-- The dimension of the big space `(x, c, ε, δ | y, u, w)`. -/
abbrev bigDim (N : ℕ) : ℕ := (((N+1)+1)+1) + (N+2)

/-- The dimension of the space `(x, c, ε, δ)`. -/
abbrev aDim (N : ℕ) : ℕ := ((N+1)+1)+1

/-- The dimension of the space `(x, c, ε)`. -/
abbrev bDim (N : ℕ) : ℕ := (N+1)+1

/-- The coordinate of `x j` in the space `(x, c)`. -/
def xIdxC (N : ℕ) (j : Fin N) : Fin (N+1) := Fin.castSucc j

/-- The coordinate of `c` in the space `(x, c)`. -/
def cIdxC (N : ℕ) : Fin (N+1) := Fin.last N

/-- The coordinate of `x j` in the space `(x, c, ε)`. -/
def xIdxB (N : ℕ) (j : Fin N) : Fin (bDim N) := Fin.castAdd 1 (xIdxC N j)

/-- The coordinate of `c` in the space `(x, c, ε)`. -/
def cIdxB (N : ℕ) : Fin (bDim N) := Fin.castAdd 1 (cIdxC N)

/-- The coordinate of `ε` in the space `(x, c, ε)`. -/
def eIdxB (N : ℕ) : Fin (bDim N) := Fin.natAdd (N+1) (0 : Fin 1)

/-- The coordinate of `x j` in the space `(x, c, ε, δ)`. -/
def xIdxA (N : ℕ) (j : Fin N) : Fin (aDim N) := Fin.castAdd 1 (xIdxB N j)

/-- The coordinate of `c` in the space `(x, c, ε, δ)`. -/
def cIdxA (N : ℕ) : Fin (aDim N) := Fin.castAdd 1 (cIdxB N)

/-- The coordinate of `ε` in the space `(x, c, ε, δ)`. -/
def eIdxA (N : ℕ) : Fin (aDim N) := Fin.castAdd 1 (eIdxB N)

/-- The coordinate of `δ` in the space `(x, c, ε, δ)`. -/
def dIdxA (N : ℕ) : Fin (aDim N) := Fin.natAdd ((N+1)+1) (0 : Fin 1)

/-- The coordinate of `x j` in the big space. -/
def xIdx (N : ℕ) (j : Fin N) : Fin (bigDim N) := Fin.castAdd (N+2) (xIdxA N j)

/-- The coordinate of `c` in the big space. -/
def cIdx (N : ℕ) : Fin (bigDim N) := Fin.castAdd (N+2) (cIdxA N)

/-- The coordinate of `ε` in the big space. -/
def eIdx (N : ℕ) : Fin (bigDim N) := Fin.castAdd (N+2) (eIdxA N)

/-- The coordinate of `δ` in the big space. -/
def dIdx (N : ℕ) : Fin (bigDim N) := Fin.castAdd (N+2) (dIdxA N)

/-- The coordinate of `y j` in the big space. -/
def yIdx (N : ℕ) (j : Fin N) : Fin (bigDim N) :=
  Fin.natAdd (((N+1)+1)+1) (Fin.castAdd 2 j)

/-- The coordinate of `u` in the big space. -/
def uIdx (N : ℕ) : Fin (bigDim N) :=
  Fin.natAdd (((N+1)+1)+1) (Fin.natAdd N (0 : Fin 2))

/-- The coordinate of `w` in the big space. -/
def wIdx (N : ℕ) : Fin (bigDim N) :=
  Fin.natAdd (((N+1)+1)+1) (Fin.natAdd N (1 : Fin 2))

/-- The point `(x, c, ε, δ, y, u, w)` of the big space, assembled from its parts. -/
def asm (N : ℕ) (x : Fin N → ℝ) (c ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    Fin (bigDim N) → ℝ :=
  Fin.append (Fin.append (Fin.append (Fin.snoc x c) (fun _ : Fin 1 => ε)) (fun _ : Fin 1 => δ))
    (Fin.append y ![u, w])

/-! ## 2. Reading the assembled points -/

@[simp] theorem asm_xIdx (N : ℕ) (x : Fin N → ℝ) (c ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ)
    (j : Fin N) : asm N x c ε δ y u w (xIdx N j) = x j := by
  simp [asm, xIdx, xIdxA, xIdxB, xIdxC, Fin.append_left, Fin.snoc_castSucc]

@[simp] theorem asm_cIdx (N : ℕ) (x : Fin N → ℝ) (c ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    asm N x c ε δ y u w (cIdx N) = c := by
  simp [asm, cIdx, cIdxA, cIdxB, cIdxC, Fin.append_left, Fin.snoc_last]

@[simp] theorem asm_eIdx (N : ℕ) (x : Fin N → ℝ) (c ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    asm N x c ε δ y u w (eIdx N) = ε := by
  simp [asm, eIdx, eIdxA, eIdxB, Fin.append_left, Fin.append_right]

@[simp] theorem asm_dIdx (N : ℕ) (x : Fin N → ℝ) (c ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    asm N x c ε δ y u w (dIdx N) = δ := by
  simp [asm, dIdx, dIdxA, Fin.append_left, Fin.append_right]

@[simp] theorem asm_yIdx (N : ℕ) (x : Fin N → ℝ) (c ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ)
    (j : Fin N) : asm N x c ε δ y u w (yIdx N j) = y j := by
  simp [asm, yIdx, Fin.append_left, Fin.append_right]

@[simp] theorem asm_uIdx (N : ℕ) (x : Fin N → ℝ) (c ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    asm N x c ε δ y u w (uIdx N) = u := by
  simp [asm, uIdx, Fin.append_right]

@[simp] theorem asm_wIdx (N : ℕ) (x : Fin N → ℝ) (c ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    asm N x c ε δ y u w (wIdx N) = w := by
  simp [asm, wIdx, Fin.append_right]

/-! ## 3. The five pieces of the inner set -/

/-- `y` agrees with `x` off the coordinate `i`. -/
def agreeSet (N : ℕ) (i : Fin N) : Set (Fin (bigDim N) → ℝ) :=
  {z | ∀ j : Fin N, j ≠ i → z (yIdx N j) = z (xIdx N j)}

/-- `(y i - x i)^2 < δ^2`. -/
def badSet (N : ℕ) (i : Fin N) : Set (Fin (bigDim N) → ℝ) :=
  {z | (z (yIdx N i) - z (xIdx N i)) ^ 2 < z (dIdx N) ^ 2}

/-- The reindexing that reads `(y, u)` as a point of `ℝ^{N+1}`. -/
def lastMapY (N : ℕ) : Fin (N+1) → Fin (bigDim N) :=
  Fin.lastCases (motive := fun _ => Fin (bigDim N)) (uIdx N) (fun j => yIdx N j)

/-- The reindexing that reads `(x, w)` as a point of `ℝ^{N+1}`. -/
def lastMapX (N : ℕ) : Fin (N+1) → Fin (bigDim N) :=
  Fin.lastCases (motive := fun _ => Fin (bigDim N)) (wIdx N) (fun j => xIdx N j)

/-- The `u`-coordinate is `f y`. -/
def grYSet (N : ℕ) (f : (Fin N → ℝ) → ℝ) : Set (Fin (bigDim N) → ℝ) :=
  Work.WilG5.coordPre (lastMapY N) (graphOf f)

/-- The `w`-coordinate is `f x`. -/
def grXSet (N : ℕ) (f : (Fin N → ℝ) → ℝ) : Set (Fin (bigDim N) → ℝ) :=
  Work.WilG5.coordPre (lastMapX N) (graphOf f)

/-- The polynomial inequality `(u - w - c (y i - x i))^2 ≤ ε^2 (y i - x i)^2`. -/
def ineqSet (N : ℕ) (i : Fin N) : Set (Fin (bigDim N) → ℝ) :=
  {z | (z (uIdx N) - z (wIdx N) - z (cIdx N) * (z (yIdx N i) - z (xIdx N i))) ^ 2
        ≤ z (eIdx N) ^ 2 * (z (yIdx N i) - z (xIdx N i)) ^ 2}

/-- The matrix of the implication defining the derivative, before any quantifier is removed. -/
def innerSet (N : ℕ) (i : Fin N) (f : (Fin N → ℝ) → ℝ) : Set (Fin (bigDim N) → ℝ) :=
  (agreeSet N i)ᶜ ∪ (badSet N i)ᶜ ∪ (grYSet N f)ᶜ ∪ (grXSet N f)ᶜ ∪ ineqSet N i

/-! ## 4. The quantifier chain -/

/-- `δ > 0`, in the space `(x, c, ε, δ)`. -/
def posDSet (N : ℕ) : Set (Fin (aDim N) → ℝ) :=
  {z | 0 < z (dIdxA N)}

/-- `ε > 0`, in the space `(x, c, ε)`. -/
def posESet (N : ℕ) : Set (Fin (bDim N) → ℝ) :=
  {z | 0 < z (eIdxB N)}

/-- `∀ y u w` (removes the last `N+2` coordinates of `innerSetᶜ`). -/
def projYSet (N : ℕ) (i : Fin N) (f : (Fin N → ℝ) → ℝ) : Set (Fin (aDim N) → ℝ) :=
  (Work.WilG5.projN (n := aDim N) (N+2) (innerSet N i f)ᶜ)ᶜ

/-- `∃ δ > 0`. -/
def projDSet (N : ℕ) (i : Fin N) (f : (Fin N → ℝ) → ℝ) : Set (Fin (bDim N) → ℝ) :=
  Work.WilG5.projN (n := bDim N) 1 (posDSet N ∩ projYSet N i f)

/-- `∀ ε > 0`, i.e. the set of points `(x, c)` for which `c` is the derivative. -/
def Sset (N : ℕ) (i : Fin N) (f : (Fin N → ℝ) → ℝ) : Set (Fin (N+1) → ℝ) :=
  (Work.WilG5.projN (n := N+1) 1 (posESet N ∩ (projDSet N i f)ᶜ))ᶜ

/-! ## 5. The `ε`-`δ` condition, and the analytic statement of `Sset` -/

/-- The `ε`-`δ` characterisation of `HasDerivAt`. -/
def epsDeriv (g : ℝ → ℝ) (a c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, |h| < δ → |g (a + h) - g a - c * h| ≤ ε * |h|

/-! ## 6. Reading the reindexed graph pieces -/

theorem mem_grYSet {N : ℕ} {f : (Fin N → ℝ) → ℝ} {z : Fin (bigDim N) → ℝ} :
    z ∈ grYSet N f ↔ z (uIdx N) = f (fun j : Fin N => z (yIdx N j)) := by
  simp only [grYSet, Work.WilG5.coordPre, Set.mem_ofPred_eq, graphOf, Function.comp_def]
  have hlast : lastMapY N (Fin.last N) = uIdx N := Fin.lastCases_last
  have hcast : ∀ j : Fin N, lastMapY N (Fin.castSucc j) = yIdx N j :=
    fun j => Fin.lastCases_castSucc j
  have hinit : Fin.init (fun j => z (lastMapY N j)) = fun j : Fin N => z (yIdx N j) := by
    funext j
    show z (lastMapY N (Fin.castSucc j)) = z (yIdx N j)
    rw [hcast j]
  rw [hlast, hinit]

theorem mem_grXSet {N : ℕ} {f : (Fin N → ℝ) → ℝ} {z : Fin (bigDim N) → ℝ} :
    z ∈ grXSet N f ↔ z (wIdx N) = f (fun j : Fin N => z (xIdx N j)) := by
  simp only [grXSet, Work.WilG5.coordPre, Set.mem_ofPred_eq, graphOf, Function.comp_def]
  have hlast : lastMapX N (Fin.last N) = wIdx N := Fin.lastCases_last
  have hcast : ∀ j : Fin N, lastMapX N (Fin.castSucc j) = xIdx N j :=
    fun j => Fin.lastCases_castSucc j
  have hinit : Fin.init (fun j => z (lastMapX N j)) = fun j : Fin N => z (xIdx N j) := by
    funext j
    show z (lastMapX N (Fin.castSucc j)) = z (xIdx N j)
    rw [hcast j]
  rw [hlast, hinit]

/-- Unfolding of the inner set. -/
theorem mem_innerSet {N : ℕ} {i : Fin N} {f : (Fin N → ℝ) → ℝ} {z : Fin (bigDim N) → ℝ} :
    z ∈ innerSet N i f ↔
      (¬ (∀ j : Fin N, j ≠ i → z (yIdx N j) = z (xIdx N j))) ∨
      (¬ ((z (yIdx N i) - z (xIdx N i)) ^ 2 < z (dIdx N) ^ 2)) ∨
      (¬ (z (uIdx N) = f (fun j : Fin N => z (yIdx N j)))) ∨
      (¬ (z (wIdx N) = f (fun j : Fin N => z (xIdx N j)))) ∨
      ((z (uIdx N) - z (wIdx N) - z (cIdx N) * (z (yIdx N i) - z (xIdx N i))) ^ 2
        ≤ z (eIdx N) ^ 2 * (z (yIdx N i) - z (xIdx N i)) ^ 2) := by
  simp only [innerSet, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, agreeSet, badSet,
    ineqSet, mem_grYSet, mem_grXSet, or_assoc]

/-! ## 7. Decomposing the last block -/

/-- Every `r : Fin (N+2) → ℝ` is determined by the `y`-block and the two last coordinates. -/
theorem append_last_eq {N : ℕ} (r : Fin (N+2) → ℝ) :
    Fin.append (fun j : Fin N => r (Fin.castAdd 2 j))
      ![r (Fin.natAdd N (0 : Fin 2)), r (Fin.natAdd N (1 : Fin 2))] = r := by
  funext k
  refine Fin.addCases (motive := fun k => Fin.append (fun j : Fin N => r (Fin.castAdd 2 j))
      ![r (Fin.natAdd N (0 : Fin 2)), r (Fin.natAdd N (1 : Fin 2))] k = r k) ?_ ?_ k <;> simp

/-- A function `Fin 1 → ℝ` is determined by its value at `0`. -/
theorem fin1_ext (e : Fin 1 → ℝ) : e = fun _ => e 0 := by
  funext i
  fin_cases i
  rfl

/-- The point produced by the quantifier chain is the assembled point. -/
theorem append_asm {N : ℕ} (v : Fin (N+1) → ℝ) (e d : Fin 1 → ℝ) (y : Fin N → ℝ)
    (u w : ℝ) :
    Fin.append (Fin.append (Fin.append v e) d) (Fin.append y ![u, w]) =
      asm N (Fin.init v) (v (Fin.last N)) (e 0) (d 0) y u w := by
  have hv : Fin.snoc (Fin.init v) (v (Fin.last N)) = v := Fin.snoc_init_self v
  simp only [asm]
  rw [hv, fin1_ext e, fin1_ext d]

end Work.WilG1.Plumb
