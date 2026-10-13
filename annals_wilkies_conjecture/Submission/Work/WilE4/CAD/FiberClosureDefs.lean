/-
  WilE4 / CAD — the definitions and small tools for the fibrewise-closure step
  `exists_fiberClosure_step`.

  The main object is the iterated last-coordinate projection `projSeq`, which removes the last
  coordinate of a semialgebraic set repeatedly.  We record it as a state `ProjState k j` consisting
  of a set in `ℝ^{k + (j+1)}` together with the family of polynomials at that level, and a step
  function `downStep` that projects out the last coordinate (and pushes the family through
  `projDataT`).  The `j`-fold iteration `projSeq k j` lands in `ℝ^{k+1}`.

  We also isolate the `extend` operation that concatenates a point of `Fin (ℓ+1)` with a point of
  `Fin q` to a point of `Fin (ℓ + (q+1))`, so that the projection of the last `q` coordinates of
  `Z` is `{w | ∃ y', extend w y' ∈ Z.set}`.
-/
import Mathlib
import Submission.Work.WilE4.CAD.Ops
import Submission.Work.WilE4.CAD.Bounds
import Submission.Work.WilE4.CAD.famDeg_tower_le

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

variable {k m n : ℕ}

/-! ## The concatenation `extend` -/

/-- Concatenation of a point of `Fin (ℓ+1)` with a point of `Fin q`, as a point of `Fin (ℓ+(q+1))`.
Written through `Fin.append`/`Fin.cons` of the initial segment, so that appending to the last
coordinate is `Fin.append x (Fin.cons ε y')` (`extend_snoc_cons`). -/
def extend (ℓ q : ℕ) (w : Fin (ℓ+1) → ℝ) (y' : Fin q → ℝ) : Fin (ℓ+(q+1)) → ℝ :=
  Fin.append (Fin.init w) (Fin.cons (w (Fin.last ℓ)) y')

/-- `extend` of a `Fin.snoc` is an append of a `Fin.cons`. -/
@[simp] theorem extend_snoc_cons {ℓ q : ℕ} (x : Fin ℓ → ℝ) (ε : ℝ) (y' : Fin q → ℝ) :
    extend ℓ q (Fin.snoc x ε) y' = Fin.append x (Fin.cons ε y') := by
  simp only [extend, Fin.init_snoc, Fin.snoc_last]

/-- Adding one more coordinate to `extend`: snoc-ing the last coordinate of the extension equals
extending by the snoc.  This is the inductive step of the set identity of `projSeq`. -/
theorem snoc_extend {k j : ℕ} (w : Fin (k+1) → ℝ) (y' : Fin j → ℝ) (t : ℝ) :
    Fin.snoc (extend k j w y') t = extend k (j+1) w (Fin.snoc y' t) := by
  simp only [extend]
  rw [← Fin.append_snoc, ← Fin.cons_snoc_eq_snoc_cons]

/-! ## The state and the iterated projection -/

/-- The state at one level of the iterated projection: a set in `ℝ^{k+(j+1)}` together with the
family of polynomials at that level. -/
abbrev ProjState (k j : ℕ) : Type := SAd (k + (j+1)) × List (MvPolynomial (Fin (k+(j+1))) ℝ)

/-- One step of the iterated projection: project out the last coordinate and push the family through
`projDataT`. -/
def downStep (k j : ℕ) (S : ProjState k (j+1)) : ProjState k j :=
  (projSAd (k := k+j+1) S.2 S.1, projDataT (k+j+1) S.2)

/-- The `j`-fold last-coordinate projection, from `ℝ^{k+(j+1)}` to `ℝ^{k+1}`. -/
def projSeq (k : ℕ) : (j : ℕ) → ProjState k j → ProjState k 0
  | 0, S => S
  | (j+1), S => projSeq k j (downStep k j S)

@[simp] theorem projSeq_zero (k : ℕ) (S : ProjState k 0) : projSeq k 0 S = S := rfl

theorem projSeq_succ (k j : ℕ) (S : ProjState k (j+1)) :
    projSeq k (j+1) S = projSeq k j (downStep k j S) := rfl

/-! ## The ε coordinate and the top family -/

/-- The `ε`-coordinate of the top space `ℝ^{ℓ+(q+1)}`: index `ℓ`. -/
def epsPoly (ℓ q : ℕ) : MvPolynomial (Fin (ℓ+(q+1))) ℝ := MvPolynomial.X ⟨ℓ, by omega⟩

/-- The `ε`-coordinate of the space `ℝ^{ℓ+1}` after removing the `y'`-block: the last coordinate. -/
def epsBase (ℓ : ℕ) : MvPolynomial (Fin (ℓ+1)) ℝ := MvPolynomial.X (Fin.last ℓ)

/-- The family used at the top level: the derivative tower of `ε :: H₀`, together with `0`. -/
def topFam {ℓ q : ℕ} (H₀ : List (MvPolynomial (Fin (ℓ+(q+1))) ℝ)) :
    List (MvPolynomial (Fin (ℓ+(q+1))) ℝ) :=
  tower (epsPoly ℓ q :: H₀) ++ [0]

/-! ## Bound polynomials -/

/-- The `n`-fold iterate of `projDataTBound`, as a polynomial in the size of the initial family:
`famDeg` of the family at the level `n` steps down is at most `(PBiter n).eval (famDeg H)`. -/
def PBiter : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | (n+1) => (PBiter n).comp projDataTBound

/-- A bound for `famDeg (topFam H₀)` in terms of `famDeg H₀`. -/
def topFamBound : Polynomial ℕ :=
  (Polynomial.X + Polynomial.C 2) * (Polynomial.X + Polynomial.C 3) ^ 2 + Polynomial.C 1

/-- A bound for `famDeg (projDataT ℓ Gq)` in terms of `famDeg H`, where `Gq` is the family at level
`ℓ+1` obtained by the `q`-fold projection. -/
def EYbound (q : ℕ) : Polynomial ℕ := projDataTBound.comp (PBiter q)

/-- The degree bound of the fibrewise-closure step, as a polynomial in `famDeg H` of the top family
`H`. -/
def fiberClosureBound (ℓ q : ℕ) : Polynomial ℕ :=
  ((bCellLen ℓ).comp (EYbound q)) * ((bCellDeg ℓ).comp (EYbound q))

/-- The degree bound of the fibrewise-closure step, as a polynomial in `famDeg H₀`. -/
def fiberClosureBoundTop (ℓ q : ℕ) : Polynomial ℕ := (fiberClosureBound ℓ q).comp topFamBound

/-! ## Small lemmas -/

theorem famDeg_cons' {m : ℕ} (P : MvPolynomial (Fin m) ℝ) (l : List (MvPolynomial (Fin m) ℝ)) :
    famDeg (P :: l) = atomDegD P + famDeg l := by
  simp [famDeg]

/-- `famDeg` of the top family is bounded by `topFamBound` in `famDeg H₀`. -/
theorem famDeg_topFam_le {ℓ q : ℕ} (H₀ : List (MvPolynomial (Fin (ℓ+(q+1))) ℝ)) :
    famDeg (topFam H₀) ≤ topFamBound.eval (famDeg H₀) := by
  have heps : atomDegD (epsPoly ℓ q) = 2 := by simp [atomDegD, epsPoly]
  have hcons : famDeg (epsPoly ℓ q :: H₀) = 2 + famDeg H₀ := by rw [famDeg_cons', heps]
  have hD : ∀ P ∈ epsPoly ℓ q :: H₀, P.totalDegree ≤ famDeg H₀ + 2 := by
    intro P hP
    rcases List.mem_cons.mp hP with rfl | hP
    · have : (epsPoly ℓ q).totalDegree = 1 := by simp [epsPoly]
      omega
    · have h := totalDegree_le_famDeg (List.mem_cons_of_mem (epsPoly ℓ q) hP)
      rw [hcons] at h
      omega
  have htower := famDeg_tower_le (X := epsPoly ℓ q :: H₀) (D := famDeg H₀ + 2) hD
  have hzero : famDeg ([0] : List (MvPolynomial (Fin (ℓ+(q+1))) ℝ)) = 1 := by
    simp [famDeg, atomDegD]
  have key : famDeg (topFam H₀) ≤ (famDeg H₀ + 2) * (famDeg H₀ + 3) ^ 2 + 1 := by
    have h2 : famDeg (tower (epsPoly ℓ q :: H₀)) ≤ (2 + famDeg H₀) * (famDeg H₀ + 3) ^ 2 := by
      rw [hcons] at htower
      refine htower.trans (le_of_eq ?_)
      ring
    rw [topFam, famDeg_append, hzero]
    refine (Nat.add_le_add_right h2 1).trans (le_of_eq ?_)
    ring
  refine key.trans (le_of_eq ?_)
  rw [topFamBound]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]

end Work.WilE4.CAD
