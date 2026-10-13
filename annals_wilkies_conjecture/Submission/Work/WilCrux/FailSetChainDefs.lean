/-
  WilCrux — `Work.WilCrux.failSet_mem`.

  The failure set `failSet G j ε` (`Work.WilCrux.SliceCauchyDefs`) is the complement of the
  "uniform Cauchy" set `goodSet G j ε`; the present file exhibits, with the level `ε` as an
  extra coordinate, the set

    `{u : ℝ^{a+1} | 0 < u (last a) ∧ Fin.init u ∈ failSet G j (u (last a))}`

  as an `Ω`-set of format `F + const` and degree `q.eval D`, uniformly in `j`.  The `Ω`-atom
  is the derivative graph `T = Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j)`
  of `Work.WilG4b.derivGraph_mem`.

  The construction follows the template of `Work.WilG4a.CD.fibreLimitMem`: a body
  conjunction in a big ambient space is subjected to a chain of projections (`projLastIter`),
  complements and intersections with positivity blocks.

  Ambient space `ℝ^{fmN a b}`, coordinates `(w | ε | η | w' | z | z' | y | y')`, with

    `fmE a = (a+1)+1` (the `(w,ε,η)` block),  `fmB a b = (a+b)+b` (the `(w',z,z')` block),
    `fmD a b = fmE a + fmB a b` (the space after stripping `y,y'`), `fmN a b = fmD a b + 2`.

  The chain is

    `fmPosEps ∩ (projLast (fmA2ᶜ ∩ fmPosEta))ᶜ`,  with
    `fmA2 = projLastIter (fmE) (fmB) (fmK1ᶜ ∩ fmHyp)`,
    `fmK1 = projLastIter (fmD) 2 fmK`,
    `fmK  = coordPre e1 T ∩ coordPre e2 T ∩ fmAbsLt`.
-/
import Mathlib
import Submission.Work.WilCrux.SliceCauchyDefs
import Submission.Work.WilG4b.badSet_mem
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG0.API
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Basic

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

/-! ## 1. Dimensions and coordinate maps -/

/-- Dimension of the `(w,ε,η)` block. -/
abbrev fmE (a : ℕ) : ℕ := (a + 1) + 1
/-- Dimension of the `(w',z,z')` block. -/
abbrev fmB (a b : ℕ) : ℕ := (a + b) + b
/-- Dimension after stripping `y,y'`. -/
abbrev fmD (a b : ℕ) : ℕ := fmE a + fmB a b
/-- Dimension of the full ambient space. -/
abbrev fmN (a b : ℕ) : ℕ := fmD a b + 2

/-- The format increment contributed by one pullback atom. -/
abbrev fmFpb (a b : ℕ) : ℕ := 64 * (fmN a b + ((a + b) + 1)) + 64
/-- The degree increment of one pullback atom (as a polynomial in the atom degree). -/
abbrev fmDP (a b : ℕ) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (32 * (fmN a b + ((a + b) + 1)) + 32)
/-- The degree of the body conjunction `fmK`. -/
abbrev fmKdeg (a b : ℕ) : Polynomial ℕ := fmDP a b + fmDP a b + Polynomial.C 6

/-- Coordinates of the `(w,ε,η)` block inside `ℝ^{fmE a}`. -/
def fmwE (a : ℕ) (i : Fin a) : Fin (fmE a) := Fin.castSucc (Fin.castSucc i)
def fmepsE (a : ℕ) : Fin (fmE a) := Fin.castSucc (Fin.last a)
def fmetaE (a : ℕ) : Fin (fmE a) := Fin.last (a + 1)

/-- Coordinates of the `(w',z,z')` block inside `ℝ^{fmB a b}`. -/
def fmwpB (a b : ℕ) (i : Fin a) : Fin (fmB a b) := Fin.castAdd b (Fin.castAdd b i)
def fmzB (a b : ℕ) (j : Fin b) : Fin (fmB a b) := Fin.castAdd b (Fin.natAdd a j)
def fmzpB (a b : ℕ) (j : Fin b) : Fin (fmB a b) := Fin.natAdd (a + b) j

/-- Coordinates inside `ℝ^{fmD a b}` (the `(w,ε,η,w',z,z')` space). -/
def fmwD (a b : ℕ) (i : Fin a) : Fin (fmD a b) := Fin.castAdd (fmB a b) (fmwE a i)
def fmepsD (a b : ℕ) : Fin (fmD a b) := Fin.castAdd (fmB a b) (fmepsE a)
def fmetaD (a b : ℕ) : Fin (fmD a b) := Fin.castAdd (fmB a b) (fmetaE a)
def fmwpD (a b : ℕ) (i : Fin a) : Fin (fmD a b) := Fin.natAdd (fmE a) (fmwpB a b i)
def fmzD (a b : ℕ) (j : Fin b) : Fin (fmD a b) := Fin.natAdd (fmE a) (fmzB a b j)
def fmzpD (a b : ℕ) (j : Fin b) : Fin (fmD a b) := Fin.natAdd (fmE a) (fmzpB a b j)

/-- Coordinates inside `ℝ^{fmN a b}`. -/
def fmwN (a b : ℕ) (i : Fin a) : Fin (fmN a b) := Fin.castAdd 2 (fmwD a b i)
def fmepsN (a b : ℕ) : Fin (fmN a b) := Fin.castAdd 2 (fmepsD a b)
def fmwpN (a b : ℕ) (i : Fin a) : Fin (fmN a b) := Fin.castAdd 2 (fmwpD a b i)
def fmzN (a b : ℕ) (j : Fin b) : Fin (fmN a b) := Fin.castAdd 2 (fmzD a b j)
def fmzpN (a b : ℕ) (j : Fin b) : Fin (fmN a b) := Fin.castAdd 2 (fmzpD a b j)
def fmyN (a b : ℕ) : Fin (fmN a b) := Fin.natAdd (fmD a b) 0
def fmypN (a b : ℕ) : Fin (fmN a b) := Fin.natAdd (fmD a b) 1

/-- `Fin.snoc X η` at the `(w,ε,η)` level, with the codomain made explicit so that Lean can
determine the dependent type of `Fin.snoc`. -/
abbrev fmsnoc (a : ℕ) (X : Fin (a + 1) → ℝ) (η : ℝ) : Fin (fmE a) → ℝ :=
  Fin.snoc (α := fun _ : Fin (fmE a) => ℝ) X η

/-- The reindexing reading `(w', z, y)` as a point of the coordinate space of `T`. -/
def fme1 (a b : ℕ) : Fin ((a + b) + 1) → Fin (fmN a b) :=
  Fin.snoc (Fin.append (fmwpN a b) (fmzN a b)) (fmyN a b)

/-- The reindexing reading `(w', z', y')` as a point of the coordinate space of `T`. -/
def fme2 (a b : ℕ) : Fin ((a + b) + 1) → Fin (fmN a b) :=
  Fin.snoc (Fin.append (fmwpN a b) (fmzpN a b)) (fmypN a b)

/-! ## 2. The atoms -/

/-- The atom `|y - y'| < ε`, as the intersection of the two linear positivity sets
`0 < ε - y + y'` and `0 < ε - y' + y`. -/
def fmAbsLt (a b : ℕ) : Set (Fin (fmN a b) → ℝ) :=
  {v | 0 < v (fmepsN a b) - v (fmyN a b) + v (fmypN a b)} ∩
  {v | 0 < v (fmepsN a b) - v (fmypN a b) + v (fmyN a b)}

/-- The body conjunction `(w',z,y) ∈ T ∧ (w',z',y') ∈ T ∧ |y - y'| < ε`. -/
def fmK (a b : ℕ) (T : Set (Fin ((a + b) + 1) → ℝ)) : Set (Fin (fmN a b) → ℝ) :=
  Work.WilG5.coordPre (fme1 a b) T ∩ Work.WilG5.coordPre (fme2 a b) T ∩ fmAbsLt a b

/-- Existentially quantify away `y,y'`. -/
def fmK1 (a b : ℕ) (T : Set (Fin ((a + b) + 1) → ℝ)) : Set (Fin (fmD a b) → ℝ) :=
  Work.WilG0.projLastIter (fmD a b) 2 (fmK a b T)

/-- The atoms of `dist w' w < η`. -/
def fmWd (a b : ℕ) (i : Fin a) : Set (Fin (fmD a b) → ℝ) :=
  {v | 0 < v (fmetaD a b) - v (fmwpD a b i) + v (fmwD a b i)}
def fmWu (a b : ℕ) (i : Fin a) : Set (Fin (fmD a b) → ℝ) :=
  {v | 0 < v (fmetaD a b) - v (fmwD a b i) + v (fmwpD a b i)}

/-- The atoms of `|z_j| < η` and `|z'_j| < η`. -/
def fmZlow (a b : ℕ) (j : Fin b) : Set (Fin (fmD a b) → ℝ) :=
  {v | 0 < v (fmetaD a b) - v (fmzD a b j)}
def fmZup (a b : ℕ) (j : Fin b) : Set (Fin (fmD a b) → ℝ) :=
  {v | 0 < v (fmetaD a b) + v (fmzD a b j)}
def fmZlowp (a b : ℕ) (j : Fin b) : Set (Fin (fmD a b) → ℝ) :=
  {v | 0 < v (fmetaD a b) - v (fmzpD a b j)}
def fmZupp (a b : ℕ) (j : Fin b) : Set (Fin (fmD a b) → ℝ) :=
  {v | 0 < v (fmetaD a b) + v (fmzpD a b j)}

/-- The atoms of `z ≠ 0` and `z' ≠ 0`, as complements of hyperplane conjunctions. -/
def fmZne (a b : ℕ) : Set (Fin (fmD a b) → ℝ) :=
  (⋂ j : Fin b, {v : Fin (fmD a b) → ℝ | v (fmzD a b j) = 0})ᶜ
def fmZpne (a b : ℕ) : Set (Fin (fmD a b) → ℝ) :=
  (⋂ j : Fin b, {v : Fin (fmD a b) → ℝ | v (fmzpD a b j) = 0})ᶜ

/-- The conjunction of the `dist w' w < η` atoms. -/
def fmWdist (a b : ℕ) : Set (Fin (fmD a b) → ℝ) :=
  ⋂ i : Fin a, (fmWd a b i ∩ fmWu a b i)
/-- The conjunction of the `|z_j| < η` atoms. -/
def fmNormZ (a b : ℕ) : Set (Fin (fmD a b) → ℝ) :=
  ⋂ j : Fin b, (fmZlow a b j ∩ fmZup a b j)
/-- The conjunction of the `|z'_j| < η` atoms. -/
def fmNormZp (a b : ℕ) : Set (Fin (fmD a b) → ℝ) :=
  ⋂ j : Fin b, (fmZlowp a b j ∩ fmZupp a b j)

/-- The hypothesis conjunction in the `(w,ε,η,w',z,z')` space. -/
def fmHyp (a b : ℕ) : Set (Fin (fmD a b) → ℝ) :=
  fmWdist a b ∩ fmZne a b ∩ fmNormZ a b ∩ fmZpne a b ∩ fmNormZp a b

/-- The failure body after projecting `y,y'`: `fmHyp ∧ ¬∃yy'(...)`. -/
def fmA1 (a b : ℕ) (T : Set (Fin ((a + b) + 1) → ℝ)) : Set (Fin (fmD a b) → ℝ) :=
  (fmK1 a b T)ᶜ ∩ fmHyp a b

/-- Existentially quantify away `w',z,z'`. -/
def fmA2 (a b : ℕ) (T : Set (Fin ((a + b) + 1) → ℝ)) : Set (Fin (fmE a) → ℝ) :=
  Work.WilG0.projLastIter (fmE a) (fmB a b) (fmA1 a b T)

/-- The positivity block `{0 < η}`. -/
def fmPosEta (a : ℕ) : Set (Fin (fmE a) → ℝ) := {v | 0 < v (Fin.last (a + 1))}
/-- The positivity block `{0 < ε}` at the final level. -/
def fmPosEps (a : ℕ) : Set (Fin (a + 1) → ℝ) := {v | 0 < v (Fin.last a)}

/-- The block `{0 < η} ∩ fmA2ᶜ`. -/
def fmBset (a b : ℕ) (T : Set (Fin ((a + b) + 1) → ℝ)) : Set (Fin (fmE a) → ℝ) :=
  (fmA2 a b T)ᶜ ∩ fmPosEta a

/-- The `Ω`-construction. -/
def fmChain (a b : ℕ) (T : Set (Fin ((a + b) + 1) → ℝ)) : Set (Fin (a + 1) → ℝ) :=
  fmPosEps a ∩ (WilkiesDesign.projLast (fmBset a b T))ᶜ

/-! ## 3. Positivity atoms -/

/-- `{v | 0 < v i - v j}` is `Ω`-definable with format `n+2` and degree `3`. -/
theorem fm_pos2_mem {S : WilkiesDesign.SOMin} {n : ℕ} (i j : Fin n) :
    {v : Fin n → ℝ | 0 < v i - v j} ∈ S.Ω (n + 2) 3 n := by
  have htd : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
    · simp [MvPolynomial.totalDegree_X]
    · simp [MvPolynomial.totalDegree_X]
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := n) 0
    (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℝ)
  have hset : {v : Fin n → ℝ | 0 < MvPolynomial.eval v
        (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin n) ℝ)} =
      {v : Fin n → ℝ | 0 < v i - v j} := by
    ext v; simp [MvPolynomial.eval_sub, MvPolynomial.eval_X]
  rw [hset] at h
  refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) ?_ h
  simp only [Polynomial.eval_C]
  omega

/-- `{v | 0 < v i + v j}` is `Ω`-definable with format `n+2` and degree `3`. -/
theorem fm_pos2p_mem {S : WilkiesDesign.SOMin} {n : ℕ} (i j : Fin n) :
    {v : Fin n → ℝ | 0 < v i + v j} ∈ S.Ω (n + 2) 3 n := by
  have htd : (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · simp [MvPolynomial.totalDegree_X]
    · simp [MvPolynomial.totalDegree_X]
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := n) 0
    (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) ℝ)
  have hset : {v : Fin n → ℝ | 0 < MvPolynomial.eval v
        (MvPolynomial.X i + MvPolynomial.X j : MvPolynomial (Fin n) ℝ)} =
      {v : Fin n → ℝ | 0 < v i + v j} := by
    ext v; simp [MvPolynomial.eval_add, MvPolynomial.eval_X]
  rw [hset] at h
  refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) ?_ h
  simp only [Polynomial.eval_C]
  omega

/-- `{v | 0 < v i - v j + v k}` is `Ω`-definable with format `n+2` and degree `3`. -/
theorem fm_pos3_mem {S : WilkiesDesign.SOMin} {n : ℕ} (i j k : Fin n) :
    {v : Fin n → ℝ | 0 < v i - v j + v k} ∈ S.Ω (n + 2) 3 n := by
  have htd : (MvPolynomial.X i - MvPolynomial.X j + MvPolynomial.X k :
      MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
      · simp [MvPolynomial.totalDegree_X]
      · simp [MvPolynomial.totalDegree_X]
    · simp [MvPolynomial.totalDegree_X]
  have h := Work.WilG1.Calc.pos_mem (S := S) (m := n) 0
    (MvPolynomial.X i - MvPolynomial.X j + MvPolynomial.X k : MvPolynomial (Fin n) ℝ)
  have hset : {v : Fin n → ℝ | 0 < MvPolynomial.eval v
        (MvPolynomial.X i - MvPolynomial.X j + MvPolynomial.X k : MvPolynomial (Fin n) ℝ)} =
      {v : Fin n → ℝ | 0 < v i - v j + v k} := by
    ext v; simp [MvPolynomial.eval_add, MvPolynomial.eval_sub, MvPolynomial.eval_X]
  rw [hset] at h
  refine Work.WilG0.Omega_mono_FD (S := S) (le_refl _) ?_ h
  simp only [Polynomial.eval_C]
  omega


end Work.WilCrux
