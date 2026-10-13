/-
  Area E7 / `CoreLT_succ`, case B: the vocabulary of the **pair-germ** argument.

  This file fixes the set-theoretic predicates used by the case-B step of `CoreLT_succ`
  (see `NOTES_S35_pairGerm_counterexample.md`).  Everything is stated for a piece given at the
  absolute split `Stratum 0 (n + (m+1))`, whose `SemiPf` set lives in `Fin (pDim n m)` with
  `pDim n m = 0 + (n + (m+1))`.

  * `pairPt u v` — the point `(absPt u, absPt v)` of the product space `ℝ^N × ℝ^N` (`N = n+(m+1)`);
  * `absVert u` — the vertical (last fibre) coordinate of a piece point;
  * `AbsGermEq T u v` — the two branch-images of `T` at `u` and at `v` (both over the same base
    point) have the same germ;
  * `absPairSet T` — the pair set `{(u,v) ∈ absSet T × absSet T : π_n u = π_n v}`, realised as the
    fibre product of the reindexed piece with itself.

  Nothing here is hard; it exists so that the statements of the geometric nodes
  (`pairStratum_dimDrop`, `persist_of_Zavoid`, `hcof_of_germEq`) can be written down without
  re-deriving the index arithmetic every time.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.levelAgree_semiPf
import Submission.Work.WilE7.FaceAux.InsertCoord

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.CoreStep
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-- The ambient dimension of a piece of `ℝ^{n+(m+1)}` given at the absolute split, in the form in
which `SemiPf` lives (`0 + ·`). -/
abbrev pDim (n m : ℕ) : ℕ := 0 + (n + (m + 1))

/-- The ambient dimension of the *pair* space of a piece. -/
abbrev pPair (n m : ℕ) : ℕ := (n + (m + 1)) + (n + (m + 1))

/-- A point of a piece at the absolute split, mapped to the `Fin (n+(m+1))` coordinates. -/
abbrev absPtInv {n m : ℕ} (u : Fin (pDim n m) → ℝ) : Fin (n + (m + 1)) → ℝ := absPt u

/-- The `absPt`-coordinates of a point of `Fin (n+(m+1))` back in `Fin (pDim n m)`. -/
abbrev absPtUp {n m : ℕ} (u : Fin (n + (m + 1)) → ℝ) : Fin (pDim n m) → ℝ :=
  fun i => u (Fin.cast (Nat.zero_add (n + (m + 1))) i)

/-- The reindexing of a piece across the `0 + ·` bookkeeping. -/
abbrev absReindex {n m : ℕ} (T : E.Stratum 0 (n + (m + 1))) : E.SemiPf (n + (m + 1)) :=
  Work.WilE7.SemiPf.reindex (Work.WilE7.finEquiv (Nat.zero_add (n + (m + 1)))) T.X

/-- `absPtUp` undoes `absPtInv`. -/
theorem absPtUp_absPtInv {n m : ℕ} (u : Fin (pDim n m) → ℝ) :
    absPtUp (n := n) (m := m) (absPtInv u) = u := by
  funext i
  show u (Fin.cast (Nat.zero_add (n + (m + 1))).symm
      (Fin.cast (Nat.zero_add (n + (m + 1))) i)) = u i
  congr 1

/-- `absPtUp` is a left inverse of `absPtInv`. -/
theorem absPtInv_absPtUp {n m : ℕ} (u : Fin (n + (m + 1)) → ℝ) :
    absPtInv (absPtUp (n := n) (m := m) u) = u := by
  funext i
  show u (Fin.cast (Nat.zero_add (n + (m + 1)))
      (Fin.cast (Nat.zero_add (n + (m + 1))).symm i)) = u i
  congr 1

/-- Membership in the reindexed piece is membership in the original one, along `absPt`. -/
theorem mem_absReindex {n m : ℕ} (T : E.Stratum 0 (n + (m + 1))) (u : Fin (n + (m + 1)) → ℝ) :
    u ∈ (absReindex T).set ↔ absPtUp (n := n) (m := m) u ∈ T.X.set := by
  rw [absReindex, Work.WilE7.sp_reindex_set]
  rfl

/-- The point `(absPt u, absPt v)` of the product space `ℝ^{n+(m+1)} × ℝ^{n+(m+1)}`. -/
def pairPt {n m : ℕ} (u v : Fin (pDim n m) → ℝ) : Fin (pPair n m) → ℝ :=
  Fin.append (absPtInv u) (absPtInv v)

/-- The same pair point, in the `Fin (0 + (N+N))` bookkeeping in which `Stratum`/`SemiPf` live. -/
def pairPtUp {n m : ℕ} (u v : Fin (pDim n m) → ℝ) : Fin (0 + pPair n m) → ℝ :=
  fun j => pairPt u v (Fin.cast (Nat.zero_add (pPair n m)) j)

@[simp] theorem projFirst_pairPt {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    E.projFirst (n + (m + 1)) (n + (m + 1)) (pairPt u v) = absPtInv u := by
  funext i
  exact Fin.append_left _ _ i

@[simp] theorem projSnd_pairPt {n m : ℕ} (u v : Fin (pDim n m) → ℝ) :
    E.projSnd (n + (m + 1)) (n + (m + 1)) (pairPt u v) = absPtInv v := by
  funext i
  exact Fin.append_right _ _ i

/-- The vertical coordinate (the last fibre coordinate) of a point of a piece in `ℝ^{n+(m+1)}`. -/
def absVert {n m : ℕ} (u : Fin (pDim n m) → ℝ) : ℝ :=
  absPtInv u ⟨n + m, by omega⟩

/-- The pair set of a piece: `{(u,v) ∈ absSet T × absSet T : π_n u = π_n v}`, realised as the
fibre product of the reindexed piece with itself (in the `0 + ·` bookkeeping). -/
def absPairSet {n m : ℕ} (T : E.Stratum 0 (n + (m + 1))) : E.SemiPf (0 + pPair n m) :=
  Work.WilE7.SemiPf.reindex (Work.WilE7.finEquiv (Nat.zero_add (pPair n m))).symm
    (Work.WilE7.fiberProdZ (absReindex T) (absReindex T))

/-- The level-agreement pair set of two pieces: same base point *and* same value of the last
(vertical) coordinate, i.e. `{(u,v) : π_{n+1} u = π_{n+1} v}`; realised as `levelGlue`. -/
def absLevelPairSet {n m : ℕ} (T T' : E.Stratum 0 (n + (m + 1))) : E.SemiPf (0 + pPair n m) :=
  Work.WilE7.SemiPf.reindex (Work.WilE7.finEquiv (Nat.zero_add (pPair n m))).symm
    (Work.WilE7.levelGlue (absReindex T) (absReindex T'))

/-- Membership of the pair point of two piece points in the pair set. -/
theorem mem_absPairSet {n m : ℕ} (T : E.Stratum 0 (n + (m + 1)))
    (u v : Fin (pDim n m) → ℝ) (hu : u ∈ T.X.set) (hv : v ∈ T.X.set)
    (hbase : E.projFirst n (m + 1) (absPtInv u) = E.projFirst n (m + 1) (absPtInv v)) :
    pairPtUp u v ∈ (absPairSet T).set := by
  rw [absPairSet, Work.WilE7.sp_reindex_set]
  have hup : (fun i : Fin (pPair n m) => pairPtUp u v
      ((Work.WilE7.finEquiv (Nat.zero_add (pPair n m))).symm i)) = pairPt u v := by
    funext i
    show pairPt u v (Fin.cast (Nat.zero_add (pPair n m))
      ((Work.WilE7.finEquiv (Nat.zero_add (pPair n m))).symm i)) = pairPt u v i
    congr 1
  simp only [hup, Work.WilE7.fiberProdZ_set, Set.mem_setOf_eq, projFirst_pairPt,
    projSnd_pairPt, mem_absReindex, absPtUp_absPtInv]
  exact ⟨hu, hv, hbase⟩

/-- **The branch-covering condition for a pair of points** (the predicate the case-B step really
consumes): for every pair of neighbourhoods of the two lifted points `absPtInv u`, `absPtInv v`
there is a neighbourhood `U` of the common base point inside which `C` is covered by *both* local
branch-images.

This is exactly the hypothesis `hpair` of `Work.WilE7.CoreStep.hcof_of_pairCovers` (with the
`V'`-half dropped), so `PairCovers` for all pairs over `C` yields `hcof` over `C`.

It is the formalisation of "the two branch-images have the same germ **and** `C` lies in it":
`PairCovers T C u v` holds precisely when there are arbitrarily small neighbourhoods `V ∋ u`,
`V' ∋ v` with `C ∩ U ⊆ π(absSet T ∩ V) ∩ π(absSet T ∩ V')`, and since `U` may shrink with `V, V'`
this says that `C` is locally contained in the common image of the two branches.  (Do **not**
replace it by a "germ equality" predicate with an unrestricted `∀ V V'`: that is equivalent to
"the base point is isolated in `π(absSet T)`" (`∀` version, refuted in S35) or to `True`
(`∃ V V'` version, refuted by the prover of `pairStratum_dimDrop2`), neither of which is usable.) -/
def PairCovers {n m : ℕ} (T : E.Stratum 0 (n + (m + 1))) (C : Set (Fin n → ℝ))
    (u v : Fin (pDim n m) → ℝ) : Prop :=
  ∀ V ∈ nhds (absPtInv u), ∀ V' ∈ nhds (absPtInv v),
    ∃ U ∈ nhds (E.projFirst n (m + 1) (absPtInv u)),
      C ∩ U ⊆ E.projFirst n (m + 1) '' (absSet T ∩ V) ∧
        C ∩ U ⊆ E.projFirst n (m + 1) '' (absSet T ∩ V')

/-- **DEPRECATED / DO NOT USE.**  This was the first attempted formalisation of "the two
branch-images have the same germ".  With the existential quantifier over `V, V'` it is *trivially
true* (`V = V' = univ` makes both sides the same term — see `absGermEq_trivial` in
`Submission/Work/CoreStep/pairStratum_dimDrop2.lean`), and with a universal quantifier it is
equivalent to "the base point is isolated in `π(absSet T)`"; both were refuted.  The usable
predicate is `PairCovers` above.  It is kept only so that the two refutation files still
elaborate. -/
def AbsGermEq {n m : ℕ} (T : E.Stratum 0 (n + (m + 1)))
    (u v : Fin (pDim n m) → ℝ) : Prop :=
  ∃ U : Set (Fin n → ℝ), IsOpen U ∧ E.projFirst n (m + 1) (absPtInv u) ∈ U ∧
    ∃ V ∈ nhds (absPtInv u), ∃ V' ∈ nhds (absPtInv v),
      U ∩ (E.projFirst n (m + 1) '' (absSet T ∩ V)) =
        U ∩ (E.projFirst n (m + 1) '' (absSet T ∩ V'))


