import Mathlib
import Submission.Work.Diff.EXT.evolX.jetCalcDefs
import Submission.Work.EXT.lcSmooth_noBoundary
import Submission.Work.Diff.EXT.evolX.ladderAtoms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The composition ladder: vocabulary

This module fixes the vocabulary of the *composition ladder*, which is the tool for the jet bound
`Work.Diff.EXT.evolX.substOp_jets_le_v2`: the jets of the operator

`substOp g k s V F y = ckt g k (update (F ∘ succ) s (smoothExt y (V (F 0) (F (s+1)) y))) y`

(the level-`k` curvature tower `∇^k Rm` with its slot `s` filled by the value of a vector-valued
operator `V` on the arguments `F 0`, `F (s+1)`).

## The decomposition

The tower, being ℝ-multilinear and tensorial in its slots, can be written as the *pairing* of the
two argument vectors of `V` with the value of a vector-valued operator:
`substOp g k s V F = ⟪V (F 0) (F (s+1)), Zsk (U-args)⟫`, where `Zsk` is the *curvature vector* of
level `k` with the insertion at the slot `s` (characterised by
`⟪Zsk Ψ, D⟫ = ckt g k (insert D at slot s into Ψ)`, cf. `Work.Diff.EXT.evolX.Zf` and
`Work.Diff.EXT.evolX.atomZf_pair`).  Hence `substOp = compOp (pairVec g V) (Zsk …)`, where

* `pairVec g V` is the pairing operator of `V` (arity `2 + 1`), whose strength is the hypothesis
  `hV : StrongAt g x 1 CV (pairOp g V)`;
* `Zsk g k s` is a vector-valued operator of arity `k + 3`, whose *pairing* `pairVec (Zsk g k s)` is
  the tower `ckt g k` up to a reindexing of its slots, whose strength is the hypothesis
  `htower : StrongAt g x k CT (ckt g k)`.

## The ladder

For an operator `S = ⟪V (·) (·), U (·)⟫` (a composition, `S = compOp (pairVec g V) U`), the `a`-th
jet of `S` is the sum, over the `2^a` distributions `ε : Fin a → Bool` of the `a` differentiation
directions among the two factors, of the pairing of the `cntT a ε`-fold covariant derivative of `V`
with the `cntF a ε`-fold covariant derivative of `U`; the number of words with `b` `true`s is
`Nat.choose a b`, which is exactly the coefficient of the target.

## The vocabulary of this module

* `dvStep g U` — the covariant-derivative step of a vector-valued operator `U` (the vector-valued
  analogue of `Work.Diff.EXT.extStep`), and `dvc g K U c` — its `c`-fold iteration (arity `K + c`,
  the first `c` entries being the differentiation directions, newest first);
* `pairVec g U` — the ℝ-valued operator `F ↦ ⟪U (F ∘ castSucc), F (last)⟫` (arity `arity U + 1`);
* `compOp g A U` — the operator `A` (arity `K + 1`) with its last slot filled by the value of `U`;
* `St g V U b c A B` — the state of the ladder: the pairing of the `b`-fold derivative of `V` (on
  the tuple `A`) with the `c`-fold derivative of `U` (on the tuple `B`);
* `cntT`/`cntF`/`dT`/`dF` — the word bookkeeping: the number of `true`s / `false`s of a word, and the
  positions of its `r`-th `true` / `false` entry (all total on `ℕ`, junk past the end).

Everything defined here is sorry-free.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The covariant-derivative step of a vector-valued operator, and its iteration -/

/-- **The covariant-derivative step of a vector-valued operator.**  `dvStep g U F y` is
`∇_{F 0}(U (F ∘ succ))` at `y`, with the Leibniz corrections of the `K` slots of `U`.  This is the
vector-valued analogue of `Work.Diff.EXT.extStep`. -/
noncomputable def dvStep (g : SMet I M) {K : ℕ}
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y) :
    (Fin (K + 1) → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y :=
  fun F y => Submission.Diff.lcOf g (U (fun i : Fin K => F i.succ)) y (F 0 y)
    - ∑ r : Fin K, U (Function.update (fun i : Fin K => F i.succ) r
        (Work.Diff.EXT.dirF g ((fun i : Fin K => F i.succ) r) (F 0))) y

/-- **The `c`-fold covariant derivative of a vector-valued operator.**  `dvc g K U c` has arity
`K + c`; its first `c` entries are the differentiation directions (newest first), the last `K` the
arguments of `U`. -/
noncomputable def dvc (g : SMet I M) (K : ℕ)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y) :
    (c : ℕ) → (Fin (K + c) → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y
  | 0 => U
  | c + 1 => dvStep g (dvc g K U c)

@[simp] theorem dvc_zero (g : SMet I M) (K : ℕ)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y) :
    dvc g K U 0 = U := rfl

@[simp] theorem dvc_succ (g : SMet I M) (K : ℕ)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y) (c : ℕ) :
    dvc g K U (c + 1) = dvStep g (dvc g K U c) := rfl

/-! ## The pairing operator of a vector-valued operator, and the composition -/

/-- **The pairing operator of a vector-valued operator** `U` of arity `K`: the ℝ-valued operator of
arity `K + 1` given by `⟪U (F ∘ castSucc), F (last)⟫`. -/
noncomputable def pairVec (g : SMet I M) {K : ℕ}
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y) :
    (Fin (K + 1) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun F y => g.inner y (U (fun i : Fin K => F i.castSucc) y) (F (Fin.last K) y)

/-- **The composition**: the operator `A` (arity `K + 1`) with its *last* slot filled by the value of
the vector-valued operator `U` (arity `K'`). -/
noncomputable def compOp (g : SMet I M) {K K' : ℕ}
    (A : (Fin (K + 1) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ)
    (U : (Fin K' → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y) :
    (Fin (K + K') → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun F y => A (Fin.snoc (fun i : Fin K => F (Fin.castAdd K' i))
    (Submission.Diff.smoothExt y (U (fun r : Fin K' => F (Fin.natAdd K r)) y))) y

/-! ## The states of the ladder -/

/-- **A state of the ladder**: the pairing of the `b`-fold covariant derivative of the
vector-valued operator `V` (arity `2`, on the tuple `A`) with the `c`-fold covariant derivative of
the vector-valued operator `U` (arity `K`, on the tuple `B`). -/
noncomputable def St (g : SMet I M) {K : ℕ}
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin K → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (b c : ℕ) :
    (Fin (2 + b) → Work.Diff.EXT.TField (I := I) (M := M)) →
      (Fin (K + c) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun A B y => g.inner y (dvc g 2 V b A y) (dvc g K U c B y)

/-! ## The word bookkeeping -/

/-- The number of `true`s of a word. -/
def cntT : (a : ℕ) → (Fin a → Bool) → ℕ
  | 0, _ => 0
  | a + 1, ε => cntT a (fun t => ε t.succ) + (ε 0).toNat

/-- The number of `false`s of a word. -/
def cntF : (a : ℕ) → (Fin a → Bool) → ℕ
  | 0, _ => 0
  | a + 1, ε => cntF a (fun t => ε t.succ) + (!(ε 0)).toNat

/-- The position of the `r`-th `true` entry of a word, padded by one (junk values are `a`, which is
not a position of the word). -/
def dT : (a : ℕ) → (Fin a → Bool) → ℕ → Fin (a + 1)
  | 0, _, _ => ⟨0, by omega⟩
  | a + 1, ε, r =>
      if ε 0 then
        (if r = 0 then ⟨0, by omega⟩ else (dT a (fun t => ε t.succ) (r - 1)).succ)
      else (dT a (fun t => ε t.succ) r).succ

/-- The position of the `r`-th `false` entry of a word, padded by one. -/
def dF : (a : ℕ) → (Fin a → Bool) → ℕ → Fin (a + 1)
  | 0, _, _ => ⟨0, by omega⟩
  | a + 1, ε, r =>
      if ε 0 then (dF a (fun t => ε t.succ) r).succ
      else (if r = 0 then ⟨0, by omega⟩ else (dF a (fun t => ε t.succ) (r - 1)).succ)

theorem cntT_succ (a : ℕ) (ε : Fin (a + 1) → Bool) :
    cntT (a + 1) ε = cntT a (fun t => ε t.succ) + (ε 0).toNat := rfl

theorem cntF_succ (a : ℕ) (ε : Fin (a + 1) → Bool) :
    cntF (a + 1) ε = cntF a (fun t => ε t.succ) + (!(ε 0)).toNat := rfl

theorem dT_cons_true_zero (a : ℕ) (ε : Fin a → Bool) :
    dT (a + 1) (Fin.cons true ε) 0 = (⟨0, by omega⟩ : Fin ((a + 1) + 1)) := by
  simp only [dT, Fin.cons_zero, Fin.cons_succ]; simp

theorem dT_cons_true_succ (a : ℕ) (ε : Fin a → Bool) (r : ℕ) :
    dT (a + 1) (Fin.cons true ε) (r + 1) = (dT a ε r).succ := by
  simp only [dT, Fin.cons_zero, Fin.cons_succ]; simp

theorem dT_cons_false (a : ℕ) (ε : Fin a → Bool) (r : ℕ) :
    dT (a + 1) (Fin.cons false ε) r = (dT a ε r).succ := by
  simp only [dT, Fin.cons_zero, Fin.cons_succ]; simp

theorem dF_cons_false_zero (a : ℕ) (ε : Fin a → Bool) :
    dF (a + 1) (Fin.cons false ε) 0 = (⟨0, by omega⟩ : Fin ((a + 1) + 1)) := by
  simp only [dF, Fin.cons_zero, Fin.cons_succ]; simp

theorem dF_cons_false_succ (a : ℕ) (ε : Fin a → Bool) (r : ℕ) :
    dF (a + 1) (Fin.cons false ε) (r + 1) = (dF a ε r).succ := by
  simp only [dF, Fin.cons_zero, Fin.cons_succ]; simp

theorem dF_cons_true (a : ℕ) (ε : Fin a → Bool) (r : ℕ) :
    dF (a + 1) (Fin.cons true ε) r = (dF a ε r).succ := by
  simp only [dF, Fin.cons_zero, Fin.cons_succ]; simp

theorem cntT_cons_true (a : ℕ) (ε : Fin a → Bool) :
    cntT (a + 1) (Fin.cons true ε) = cntT a ε + 1 := rfl

theorem cntT_cons_false (a : ℕ) (ε : Fin a → Bool) :
    cntT (a + 1) (Fin.cons false ε) = cntT a ε := rfl

theorem cntF_cons_true (a : ℕ) (ε : Fin a → Bool) :
    cntF (a + 1) (Fin.cons true ε) = cntF a ε := rfl

theorem cntF_cons_false (a : ℕ) (ε : Fin a → Bool) :
    cntF (a + 1) (Fin.cons false ε) = cntF a ε + 1 := rfl

/-- The number of `true`s and of `false`s add up to the length of the word. -/
theorem cntT_add_cntF (a : ℕ) (ε : Fin a → Bool) : cntT a ε + cntF a ε = a := by
  induction a with
  | zero => simp [cntT, cntF]
  | succ a ih =>
      rw [cntT_succ, cntF_succ]
      have ih' := ih (fun t => ε t.succ)
      cases h : ε 0
      · simp only [h, Bool.toNat_false, Bool.not_false, Bool.toNat_true, Bool.not_true]
        omega
      · simp only [h, Bool.toNat_true, Bool.not_true, Bool.toNat_false, Bool.not_false]
        omega


/-! ## The tuple extraction of the target's layout, and the states of the ladder -/

section Layout

/-- The block position of the `j`-th argument of the inserted operator `U`: the tower's slot
`Fin.succAbove s j` (i.e. the `j`-th slot of the tower different from `s`), which in the tuple of
`substOp` is the entry `(Fin.succAbove s j) + 1`. -/
def upos (k : ℕ) (s : Fin (k + 4)) (j : Fin (k + 3)) : Fin (k + 5) :=
  (Fin.succAbove s j).succ

/-- **The `V`-side tuple of the state of the word `ε`.**  On the tuple
`F : Fin (a + (k+5))` (with the first `a` entries the differentiation directions, newest first, and
the last `k+5` the slot block of `substOp`), this is the `a`-tuple of the `V`-arguments: the
`ε`-true directions (in increasing order), followed by the two `V`-slots `F a` and `F (a + s + 1)`. -/
noncomputable def Apart (k : ℕ) (s : Fin (k + 4)) (a : ℕ) (ε : Fin a → Bool)
    (F : Fin (a + (k + 5)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Fin (2 + cntT a ε) → Work.Diff.EXT.TField (I := I) (M := M) :=
  fun i => if hi : (i : ℕ) < cntT a ε then
      F (Fin.castLE (by omega) (dT a ε i))
    else if (i : ℕ) = cntT a ε then
      F (Fin.natAdd a (⟨0, by omega⟩ : Fin (k + 5)))
    else
      F (Fin.natAdd a (⟨s.val + 1, by omega⟩ : Fin (k + 5)))

/-- **The `U`-side tuple of the state of the word `ε`**: the `ε`-false directions (in increasing
order), followed by the `k+3` slots of the tower different from `s` (at the block positions
`upos k s ·`). -/
noncomputable def Bpart (k : ℕ) (s : Fin (k + 4)) (a : ℕ) (ε : Fin a → Bool)
    (F : Fin (a + (k + 5)) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Fin ((k + 3) + cntF a ε) → Work.Diff.EXT.TField (I := I) (M := M) :=
  fun i => if hi : (i : ℕ) < cntF a ε then
      F (Fin.castLE (by omega) (dF a ε i))
    else
      F (Fin.natAdd a (upos k s ⟨(i : ℕ) - cntF a ε, by omega⟩))

/-- **A state of the ladder, in the layout of `substOp`**: the state of the word `ε` on the tuple
`F`, i.e. the pairing of the `cntT a ε`-fold covariant derivative of `V` on the `V`-side tuple with
the `cntF a ε`-fold covariant derivative of `U` on the `U`-side tuple. -/
noncomputable def StO (k : ℕ) (s : Fin (k + 4)) (g : SMet I M)
    (V : (Fin 2 → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (U : (Fin (k + 3) → Work.Diff.EXT.TField (I := I) (M := M)) → (y : M) → TangentSpace I y)
    (a : ℕ) (ε : Fin a → Bool) :
    (Fin (a + (k + 5)) → Work.Diff.EXT.TField (I := I) (M := M)) → M → ℝ :=
  fun F y => St (I := I) (M := M) g V U (cntT a ε) (cntF a ε)
    (Apart k s a ε F) (Bpart k s a ε F) y

end Layout

/-! ## The extension of a slot permutation to the tuples of `jetAll` -/

/-- **The extension of a permutation `e` of the slots to the tuples of `jetAll`**: the identity on
the `b` differentiation directions and `e` on the `K` slots. -/
def slotPerm {K : ℕ} (e : Fin K ≃ Fin K) (b : ℕ) : Fin (K + b) → Fin (K + b) :=
  fun i => if h : (i : ℕ) < b then i
    else ⟨b + (e ⟨(i : ℕ) - b, by omega⟩ : Fin K).val,
      by have := i.isLt; have := (e ⟨(i : ℕ) - b, by omega⟩ : Fin K).isLt; omega⟩

/-! ## Splitting a `((K+1)+c)`-tuple into its first `K+c` entries and its last entry -/

/-- The first `K+c` entries of a `((K+1)+c)`-tuple. -/
def firstPart {K c : ℕ} (F : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Fin (K + c) → Work.Diff.EXT.TField (I := I) (M := M) :=
  fun i => F (Fin.castLE (by omega) i)

/-- The last entry of a `((K+1)+c)`-tuple. -/
def lastPart {K c : ℕ} (F : Fin ((K + 1) + c) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Work.Diff.EXT.TField (I := I) (M := M) :=
  F (Fin.cast (by omega : (K + c) + 1 = (K + 1) + c) (Fin.last (K + c)))

/-! ## The curvature vector with the insertion at the slot `s` -/

/-- The `j`-th slot of the tower different from `s`, in increasing order, as a map
`Fin (k+4) → Fin (k+3)` (junk at `i = s`). -/
def skipMap (k : ℕ) (s : Fin (k + 4)) (i : Fin (k + 4)) : Fin (k + 3) :=
  if h : (i : ℕ) < (s : ℕ) then ⟨i, by have := i.isLt; omega⟩
  else ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩

/-- **The level-`k` curvature vector with the insertion at the slot `s`**: the vector `Z` with
`⟪Z, D⟫ = ckt g k (the tuple `Ψ` with `D` inserted at the slot `s`)`.  This is
`Work.Diff.EXT.evolX.Zf` (whose canonical insertion is at the *last* slot) with the slots of the
tower relabelled so that the insertion is at `s`. -/
noncomputable def Zsk (g : Submission.Diff.SMet I M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)) (k : ℕ)
    (s : Fin (k + 4)) (Ψ : Fin (k + 3) → Work.Diff.EXT.TField (I := I) (M := M)) :
    Work.Diff.EXT.TField (I := I) (M := M) :=
  fun y => ∑ m : Fin (Module.finrank ℝ E),
    (Work.Diff.EXT.ckt g k (Function.update (fun i : Fin (k + 4) => Ψ (skipMap k s i))
      s (W m)) y) • W m y

end Work.Diff.EXT.evolX
