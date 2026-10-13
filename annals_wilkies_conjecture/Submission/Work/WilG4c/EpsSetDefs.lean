/-
  WilG4c — vocabulary for `EpsFDerivSetMem`: the `ε`-`δ` relation underlying the Fréchet
  derivative, laid out in coordinates so that `Ω`-closure (complement, projection, union,
  hypersurface, positivity set) produces exactly `epsFDerivSet`.

  Fix `N : ℕ` and `φ : ℝ^N → ℝ`.  The construction lives in the big space

    `ℝ^bigDim`,  `bigDim = ((N+N)+1+1) + (N+2)`, with coordinates

      `(x, c, ε, δ | y, u, w)`

  (`x : Fin N` the point at which we differentiate, `c : Fin N` the candidate gradient,
  `ε`, `δ` the tolerance and radius, `y : Fin N` a second point, `u`, `w` the values `φ y`,
  `φ x`).  The nested quantifiers of the `ε`-`δ` formula are removed by projecting the *last*
  coordinates first:

    * `innerSet`   : the matrix of the implication (no quantifiers);
    * `projYSet`   : `(projN (N+2) innerSetᶜ)ᶜ`, i.e. `∀ y u w`;
    * `projDSet`   : `projN 1 (posDSet ∩ projYSet)`, i.e. `∃ δ > 0`;
    * `EpsSet`     : `(projN 1 (posESet ∩ projDSetᶜ))ᶜ`, i.e. `∀ ε > 0`,

  and `EpsSet N φ = epsFDerivSet N φ` (`EpsSet_eq_epsFDerivSet`).

  The `ε`-`δ` condition used is the polynomial (squared, sum-of-squares) one: with
  `v = y - x`,

    `∑ i, (v i)^2 < δ^2  →  (φ y - φ x - ∑ i, c i * v i)^2 ≤ ε^2 * ∑ i, (v i)^2`,

  equivalently `HasFDerivAt φ (Lin c) x` by `hasFDerivAt_iff_epsPoly`, since `∑ v^2` is
  equivalent to the sup-norm `‖v‖` on `ℝ^N`.
-/
import Mathlib
import Submission.Work.WilG4c.SgnEqDefs
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.pos_mem

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesConjecture

/-! ## 1. Dimensions and coordinates -/

/-- The dimension of the big space `(x, c, ε, δ | y, u, w)`. -/
abbrev bigDim (N : ℕ) : ℕ := (((N+N)+1)+1) + (N+2)

/-- The dimension of the space `(x, c, ε, δ)`. -/
abbrev aDim (N : ℕ) : ℕ := ((N+N)+1)+1

/-- The dimension of the space `(x, c, ε)`. -/
abbrev bDim (N : ℕ) : ℕ := (N+N)+1

/-- The coordinate of `x j` in the space `(x, c)`. -/
def xIdxC (N : ℕ) (j : Fin N) : Fin (N+N) := Fin.castAdd N j

/-- The coordinate of `c i` in the space `(x, c)`. -/
def cIdxC (N : ℕ) (i : Fin N) : Fin (N+N) := Fin.natAdd N i

/-- The coordinate of `x j` in the space `(x, c, ε)`. -/
def xIdxB (N : ℕ) (j : Fin N) : Fin (bDim N) := Fin.castAdd 1 (xIdxC N j)

/-- The coordinate of `c i` in the space `(x, c, ε)`. -/
def cIdxB (N : ℕ) (i : Fin N) : Fin (bDim N) := Fin.castAdd 1 (cIdxC N i)

/-- The coordinate of `ε` in the space `(x, c, ε)`. -/
def eIdxB (N : ℕ) : Fin (bDim N) := Fin.natAdd (N+N) (0 : Fin 1)

/-- The coordinate of `x j` in the space `(x, c, ε, δ)`. -/
def xIdxA (N : ℕ) (j : Fin N) : Fin (aDim N) := Fin.castAdd 1 (xIdxB N j)

/-- The coordinate of `c i` in the space `(x, c, ε, δ)`. -/
def cIdxA (N : ℕ) (i : Fin N) : Fin (aDim N) := Fin.castAdd 1 (cIdxB N i)

/-- The coordinate of `ε` in the space `(x, c, ε, δ)`. -/
def eIdxA (N : ℕ) : Fin (aDim N) := Fin.castAdd 1 (eIdxB N)

/-- The coordinate of `δ` in the space `(x, c, ε, δ)`. -/
def dIdxA (N : ℕ) : Fin (aDim N) := Fin.natAdd ((N+N)+1) (0 : Fin 1)

/-- The coordinate of `x j` in the big space. -/
def xIdx (N : ℕ) (j : Fin N) : Fin (bigDim N) := Fin.castAdd (N+2) (xIdxA N j)

/-- The coordinate of `c i` in the big space. -/
def cIdx (N : ℕ) (i : Fin N) : Fin (bigDim N) := Fin.castAdd (N+2) (cIdxA N i)

/-- The coordinate of `ε` in the big space. -/
def eIdx (N : ℕ) : Fin (bigDim N) := Fin.castAdd (N+2) (eIdxA N)

/-- The coordinate of `δ` in the big space. -/
def dIdx (N : ℕ) : Fin (bigDim N) := Fin.castAdd (N+2) (dIdxA N)

/-- The coordinate of `y j` in the big space. -/
def yIdx (N : ℕ) (j : Fin N) : Fin (bigDim N) :=
  Fin.natAdd (((N+N)+1)+1) (Fin.castAdd 2 j)

/-- The coordinate of `u` in the big space. -/
def uIdx (N : ℕ) : Fin (bigDim N) :=
  Fin.natAdd (((N+N)+1)+1) (Fin.natAdd N (0 : Fin 2))

/-- The coordinate of `w` in the big space. -/
def wBigIdx (N : ℕ) : Fin (bigDim N) :=
  Fin.natAdd (((N+N)+1)+1) (Fin.natAdd N (1 : Fin 2))

/-- The point `(x, c, ε, δ, y, u, w)` of the big space, assembled from its parts. -/
def asm (N : ℕ) (x c : Fin N → ℝ) (ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    Fin (bigDim N) → ℝ :=
  Fin.append (Fin.append (Fin.append (Fin.append x c) (fun _ : Fin 1 => ε))
    (fun _ : Fin 1 => δ)) (Fin.append y ![u, w])

/-! ## 2. Reading the assembled points -/

@[simp] theorem asm_xIdx (N : ℕ) (x c : Fin N → ℝ) (ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ)
    (j : Fin N) : asm N x c ε δ y u w (xIdx N j) = x j := by
  rw [asm, xIdx, xIdxA, xIdxB, xIdxC, Fin.append_left, Fin.append_left, Fin.append_left,
    Fin.append_left]

@[simp] theorem asm_cIdx (N : ℕ) (x c : Fin N → ℝ) (ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ)
    (i : Fin N) : asm N x c ε δ y u w (cIdx N i) = c i := by
  rw [asm, cIdx, cIdxA, cIdxB, cIdxC, Fin.append_left, Fin.append_left, Fin.append_left,
    Fin.append_right]

@[simp] theorem asm_eIdx (N : ℕ) (x c : Fin N → ℝ) (ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    asm N x c ε δ y u w (eIdx N) = ε := by
  rw [asm, eIdx, eIdxA, eIdxB, Fin.append_left, Fin.append_left, Fin.append_right]

@[simp] theorem asm_dIdx (N : ℕ) (x c : Fin N → ℝ) (ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    asm N x c ε δ y u w (dIdx N) = δ := by
  rw [asm, dIdx, dIdxA, Fin.append_left, Fin.append_right]

@[simp] theorem asm_yIdx (N : ℕ) (x c : Fin N → ℝ) (ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ)
    (j : Fin N) : asm N x c ε δ y u w (yIdx N j) = y j := by
  rw [asm, yIdx, Fin.append_right, Fin.append_left]

@[simp] theorem asm_uIdx (N : ℕ) (x c : Fin N → ℝ) (ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    asm N x c ε δ y u w (uIdx N) = u := by
  rw [asm, uIdx, Fin.append_right, Fin.append_right]
  simp

@[simp] theorem asm_wIdx (N : ℕ) (x c : Fin N → ℝ) (ε δ : ℝ) (y : Fin N → ℝ) (u w : ℝ) :
    asm N x c ε δ y u w (wBigIdx N) = w := by
  rw [asm, wBigIdx, Fin.append_right, Fin.append_right]
  simp

/-- A function `Fin 1 → ℝ` is determined by its value at `0`. -/
theorem fin1_ext (e : Fin 1 → ℝ) : e = fun _ => e 0 := by
  funext i
  fin_cases i
  rfl

/-- The point produced by the quantifier chain is the assembled point. -/
theorem append_asm (N : ℕ) (x c : Fin N → ℝ) (e d : Fin 1 → ℝ) (y : Fin N → ℝ)
    (u w : ℝ) :
    Fin.append (Fin.append (Fin.append (Fin.append x c) e) d) (Fin.append y ![u, w]) =
      asm N x c (e 0) (d 0) y u w := by
  rw [asm, fin1_ext e, fin1_ext d]

/-- Every `r : Fin (N+2) → ℝ` is determined by the `y`-block and the two last coordinates. -/
theorem append_last_eq (N : ℕ) (r : Fin (N+2) → ℝ) :
    Fin.append (fun j : Fin N => r (Fin.castAdd 2 j))
      ![r (Fin.natAdd N (0 : Fin 2)), r (Fin.natAdd N (1 : Fin 2))] = r := by
  funext k
  refine Fin.addCases (motive := fun k => Fin.append (fun j : Fin N => r (Fin.castAdd 2 j))
      ![r (Fin.natAdd N (0 : Fin 2)), r (Fin.natAdd N (1 : Fin 2))] k = r k) ?_ ?_ k <;> simp

/-! ## 3. The five pieces of the inner set -/

/-- The reindexing that reads `(y, u)` as a point of `ℝ^{N+1}`. -/
def lastMapY (N : ℕ) : Fin (N+1) → Fin (bigDim N) :=
  Fin.lastCases (motive := fun _ => Fin (bigDim N)) (uIdx N) (fun j => yIdx N j)

/-- The reindexing that reads `(x, w)` as a point of `ℝ^{N+1}`. -/
def lastMapX (N : ℕ) : Fin (N+1) → Fin (bigDim N) :=
  Fin.lastCases (motive := fun _ => Fin (bigDim N)) (wBigIdx N) (fun j => xIdx N j)

/-- The `u`-coordinate is `φ y`. -/
def graphYSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) : Set (Fin (bigDim N) → ℝ) :=
  Work.WilG5.coordPre (lastMapY N) (graphOf φ)

/-- The `w`-coordinate is `φ x`. -/
def graphXSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) : Set (Fin (bigDim N) → ℝ) :=
  Work.WilG5.coordPre (lastMapX N) (graphOf φ)

/-- The domain condition `∑ i, (y i - x i)^2 < δ^2`. -/
def hypSet (N : ℕ) : Set (Fin (bigDim N) → ℝ) :=
  {z | ∑ i : Fin N, (z (yIdx N i) - z (xIdx N i)) ^ 2 < z (dIdx N) ^ 2}

/-- The conclusion `(u - w - ∑ i, c i (y i - x i))^2 ≤ ε^2 ∑ i, (y i - x i)^2`. -/
def ineqSet (N : ℕ) : Set (Fin (bigDim N) → ℝ) :=
  {z | (z (uIdx N) - z (wBigIdx N) - ∑ i : Fin N, z (cIdx N i) * (z (yIdx N i) - z (xIdx N i))) ^ 2
        ≤ z (eIdx N) ^ 2 * ∑ i : Fin N, (z (yIdx N i) - z (xIdx N i)) ^ 2}

/-- The matrix of the implication defining the derivative, before any quantifier is removed. -/
def innerSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) : Set (Fin (bigDim N) → ℝ) :=
  (hypSet N)ᶜ ∪ (graphYSet N φ)ᶜ ∪ (graphXSet N φ)ᶜ ∪ ineqSet N

theorem mem_graphYSet {N : ℕ} {φ : (Fin N → ℝ) → ℝ} {z : Fin (bigDim N) → ℝ} :
    z ∈ graphYSet N φ ↔ z (uIdx N) = φ (fun j : Fin N => z (yIdx N j)) := by
  simp only [graphYSet, Work.WilG5.coordPre, Set.mem_ofPred_eq, graphOf, Function.comp_def]
  have hlast : lastMapY N (Fin.last N) = uIdx N := Fin.lastCases_last
  have hcast : ∀ j : Fin N, lastMapY N (Fin.castSucc j) = yIdx N j :=
    fun j => Fin.lastCases_castSucc j
  have hinit : Fin.init (fun j => z (lastMapY N j)) = fun j : Fin N => z (yIdx N j) := by
    funext j
    show z (lastMapY N (Fin.castSucc j)) = z (yIdx N j)
    rw [hcast j]
  rw [hlast, hinit]

theorem mem_graphXSet {N : ℕ} {φ : (Fin N → ℝ) → ℝ} {z : Fin (bigDim N) → ℝ} :
    z ∈ graphXSet N φ ↔ z (wBigIdx N) = φ (fun j : Fin N => z (xIdx N j)) := by
  simp only [graphXSet, Work.WilG5.coordPre, Set.mem_ofPred_eq, graphOf, Function.comp_def]
  have hlast : lastMapX N (Fin.last N) = wBigIdx N := Fin.lastCases_last
  have hcast : ∀ j : Fin N, lastMapX N (Fin.castSucc j) = xIdx N j :=
    fun j => Fin.lastCases_castSucc j
  have hinit : Fin.init (fun j => z (lastMapX N j)) = fun j : Fin N => z (xIdx N j) := by
    funext j
    show z (lastMapX N (Fin.castSucc j)) = z (xIdx N j)
    rw [hcast j]
  rw [hlast, hinit]

/-- Unfolding of the inner set. -/
theorem mem_innerSet {N : ℕ} {φ : (Fin N → ℝ) → ℝ} {z : Fin (bigDim N) → ℝ} :
    z ∈ innerSet N φ ↔
      (¬ (∑ i : Fin N, (z (yIdx N i) - z (xIdx N i)) ^ 2 < z (dIdx N) ^ 2)) ∨
      (¬ (z (uIdx N) = φ (fun j : Fin N => z (yIdx N j)))) ∨
      (¬ (z (wBigIdx N) = φ (fun j : Fin N => z (xIdx N j)))) ∨
      ((z (uIdx N) - z (wBigIdx N)
          - ∑ i : Fin N, z (cIdx N i) * (z (yIdx N i) - z (xIdx N i))) ^ 2
        ≤ z (eIdx N) ^ 2 * ∑ i : Fin N, (z (yIdx N i) - z (xIdx N i)) ^ 2) := by
  simp only [innerSet, hypSet, ineqSet, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq,
    mem_graphYSet, mem_graphXSet, or_assoc]

/-! ## 4. The quantifier chain -/

/-- `δ > 0`, in the space `(x, c, ε, δ)`. -/
def posDSet (N : ℕ) : Set (Fin (aDim N) → ℝ) := {z | 0 < z (dIdxA N)}

/-- `ε > 0`, in the space `(x, c, ε)`. -/
def posESet (N : ℕ) : Set (Fin (bDim N) → ℝ) := {z | 0 < z (eIdxB N)}

/-- `∀ y u w` (removes the last `N+2` coordinates of `innerSetᶜ`). -/
def projYSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) : Set (Fin (aDim N) → ℝ) :=
  (Work.WilG5.projN (N+2) (innerSet N φ)ᶜ)ᶜ

/-- `∃ δ > 0`. -/
def projDSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) : Set (Fin (bDim N) → ℝ) :=
  Work.WilG5.projN 1 (posDSet N ∩ projYSet N φ)

/-- `∀ ε > 0`: the set of `(x, c)` for which `c` is the Fréchet derivative of `φ` at `x`. -/
def EpsSet (N : ℕ) (φ : (Fin N → ℝ) → ℝ) : Set (Fin (N+N) → ℝ) :=
  (Work.WilG5.projN 1 (posESet N ∩ (projDSet N φ)ᶜ))ᶜ

@[simp] theorem eIdxB_append (N : ℕ) (v : Fin (N+N) → ℝ) (e : Fin 1 → ℝ) :
    (Fin.append v e) (eIdxB N) = e 0 := by
  rw [eIdxB, Fin.append_right]

@[simp] theorem dIdxA_append (N : ℕ) (v : Fin (bDim N) → ℝ) (d : Fin 1 → ℝ) :
    (Fin.append v d) (dIdxA N) = d 0 := by
  rw [dIdxA, Fin.append_right]

theorem mem_posESet (N : ℕ) (w : Fin (bDim N) → ℝ) :
    w ∈ posESet N ↔ 0 < w (eIdxB N) := Iff.rfl

theorem mem_posDSet (N : ℕ) (w : Fin (aDim N) → ℝ) :
    w ∈ posDSet N ↔ 0 < w (dIdxA N) := Iff.rfl

theorem mem_projYSet {N : ℕ} (φ : (Fin N → ℝ) → ℝ) (z : Fin (aDim N) → ℝ) :
    z ∈ projYSet N φ ↔ ∀ r : Fin (N+2) → ℝ, Fin.append z r ∈ innerSet N φ := by
  rw [projYSet, Set.mem_compl_iff, Work.WilG5.projN, Set.mem_ofPred_eq, not_exists]
  exact forall_congr' fun r => by rw [Set.mem_compl_iff, not_not]

theorem mem_projDSet {N : ℕ} (φ : (Fin N → ℝ) → ℝ) (u : Fin (bDim N) → ℝ) :
    u ∈ projDSet N φ ↔ ∃ δ : ℝ, 0 < δ ∧
      ∀ r : Fin (N+2) → ℝ,
        Fin.append (Fin.append u (fun _ : Fin 1 => δ)) r ∈ innerSet N φ := by
  rw [projDSet, Work.WilG5.projN, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨d, hd1, hd2⟩
    rw [mem_posDSet, dIdxA_append] at hd1
    rw [mem_projYSet] at hd2
    refine ⟨d 0, hd1, fun r => ?_⟩
    have h := hd2 r
    rwa [fin1_ext d] at h
  · rintro ⟨δ, hδ0, hδ⟩
    refine ⟨fun _ : Fin 1 => δ, ?_, ?_⟩
    · rw [mem_posDSet, dIdxA_append]
      exact hδ0
    · rw [mem_projYSet]
      exact hδ

/-- Unfolding `EpsSet`: `(x, c) ∈ EpsSet N φ` is the `ε`-`δ` formula, with the `∀ y u w`
part still written as membership of the assembled point in `innerSet`. -/
theorem mem_EpsSet_iff {N : ℕ} (φ : (Fin N → ℝ) → ℝ) (x c : Fin N → ℝ) :
    Fin.append x c ∈ EpsSet N φ ↔ ∀ ε > 0, ∃ δ > 0, ∀ (y : Fin N → ℝ) (u w : ℝ),
      asm N x c ε δ y u w ∈ innerSet N φ := by
  rw [EpsSet, Set.mem_compl_iff, Work.WilG5.projN, Set.mem_ofPred_eq, not_exists]
  constructor
  · intro H ε hε
    have hpos : (Fin.append (Fin.append x c) (fun _ : Fin 1 => ε)) ∈ posESet N := by
      rw [mem_posESet, eIdxB_append]
      simpa using hε
    have hpd : (Fin.append (Fin.append x c) (fun _ : Fin 1 => ε)) ∈ projDSet N φ := by
      by_contra hc
      exact H (fun _ : Fin 1 => ε) ⟨hpos, by rwa [Set.mem_compl_iff]⟩
    rw [mem_projDSet] at hpd
    obtain ⟨δ, hδ0, hδ⟩ := hpd
    refine ⟨δ, hδ0, fun y u w => ?_⟩
    have h := hδ (Fin.append y ![u, w])
    simpa [append_asm] using h
  · intro H e hcon
    rw [Set.mem_inter_iff] at hcon
    obtain ⟨hpos, hnot⟩ := hcon
    rw [Set.mem_compl_iff] at hnot
    rw [mem_posESet, eIdxB_append] at hpos
    obtain ⟨δ, hδ0, hδ⟩ := H (e 0) hpos
    rw [mem_projDSet] at hnot
    refine hnot ⟨δ, hδ0, fun r => ?_⟩
    have h := hδ (fun j : Fin N => r (Fin.castAdd 2 j)) (r (Fin.natAdd N (0 : Fin 2)))
      (r (Fin.natAdd N (1 : Fin 2)))
    rw [← append_last_eq N r]
    simpa [append_asm] using h

end Work.WilG4c
