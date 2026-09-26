import Mathlib
import Submission.Work.Smooth.JordanSeparation.plApprox
import Submission.Work.Smooth.JordanSeparation.plSplit
import Submission.Work.Smooth.JordanSeparation.gridWalk_lift

/-!
# Generic lemmas on joins of paths and on free homotopy

This file collects the space-generic path algebra used in the grid approximation of a loop
(`lwalk_approximation`):

* `cumSum` — partial sums of block lengths, defined by recursion so that
  `cumSum L (k+1) = cumSum L k + L k` *definitionally*;
* `joinNat_congr_lt` — a bounded version of `joinNat_congr`;
* `joinNat_flatten` — the join of a family is the join of the joins of its blocks;
* `trans_conj_cancel` — cancellation of a `E.symm · E` pair inside a product of paths;
* `joinNat_conj` — the join of the three-piece paths `e k · s k · (e (k+1))⁻¹` is
  `e 0 · (join s) · (e N)⁻¹`;
* `homotopic_refl_of_conj` — a loop conjugate to a null-homotopic loop is null-homotopic;
* `Path.liftU_symm` — lifting commutes with reversal.
-/

namespace Work.Smooth.JordanSeparation

open Set

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- Partial sums of a sequence of block lengths, defined by recursion so that
`cumSum L (k+1) = cumSum L k + L k` and `cumSum L 0 = 0` are definitional. -/
def cumSum (L : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => cumSum L n + L n

@[simp] theorem cumSum_zero (L : ℕ → ℕ) : cumSum L 0 = 0 := rfl
@[simp] theorem cumSum_succ (L : ℕ → ℕ) (n : ℕ) : cumSum L (n + 1) = cumSum L n + L n := rfl

/-- A bounded version of `joinNat_congr`: only the first `j` members of the families are
compared. -/
theorem joinNat_congr_lt {p : ℕ → X} {F G : ∀ k, Path (p k) (p (k + 1))} (j : ℕ)
    (h : ∀ k, k < j → Path.Homotopic (F k) (G k)) :
    Path.Homotopic (joinNat F j) (joinNat G j) := by
  induction j with
  | zero => exact Path.Homotopic.refl _
  | succ j ih =>
    rw [show joinNat F (j + 1) = (joinNat F j).trans (F j) from rfl,
        show joinNat G (j + 1) = (joinNat G j).trans (G j) from rfl]
    exact Path.Homotopic.hcomp (ih (fun k hk => h k (Nat.lt_succ_of_lt hk)))
      (h j (Nat.lt_succ_self j))

/-- **Flattening a join.**  The join of the first `cumSum L N` members of a family is homotopic
to the join of the joins of its successive blocks of lengths `L k`. -/
theorem joinNat_flatten {p : ℕ → X} (F : ∀ k, Path (p k) (p (k + 1))) (L : ℕ → ℕ) (N : ℕ) :
    Path.Homotopic (joinNat F (cumSum L N))
      (joinNat (fun k => joinNat (fun j => F (cumSum L k + j)) (L k)) N) := by
  induction N with
  | zero => exact Path.Homotopic.refl _
  | succ N ih =>
    refine (joinNat_add F (cumSum L N) (L N)).trans ?_
    exact Path.Homotopic.hcomp ih (Path.Homotopic.refl _)

/-- **Cancelling a backtrack inside a product of paths.** -/
theorem trans_conj_cancel {a b c d e f : X} (A : Path a b) (B : Path b c) (E : Path d c)
    (S : Path c e) (EN : Path e f) :
    Path.Homotopic ((A.trans (B.trans E.symm)).trans (E.trans (S.trans EN)))
      ((A.trans (B.trans S)).trans EN) := by
  have h1 : Path.Homotopic ((A.trans (B.trans E.symm)).trans (E.trans (S.trans EN)))
      ((A.trans (B.trans E.symm)).trans ((E.trans S).trans EN)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _)
      (Path.Homotopic.trans_assoc E S EN).symm
  have h2 : Path.Homotopic ((A.trans (B.trans E.symm)).trans ((E.trans S).trans EN))
      (((A.trans (B.trans E.symm)).trans (E.trans S)).trans EN) :=
    (Path.Homotopic.trans_assoc _ _ _).symm
  have h3 : Path.Homotopic (((A.trans (B.trans E.symm)).trans (E.trans S)).trans EN)
      ((A.trans ((B.trans E.symm).trans (E.trans S))).trans EN) :=
    Path.Homotopic.hcomp (Path.Homotopic.trans_assoc A (B.trans E.symm) (E.trans S))
      (Path.Homotopic.refl _)
  have h4 : Path.Homotopic ((A.trans ((B.trans E.symm).trans (E.trans S))).trans EN)
      ((A.trans (B.trans (E.symm.trans (E.trans S)))).trans EN) :=
    Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl A)
      (Path.Homotopic.trans_assoc B E.symm (E.trans S))) (Path.Homotopic.refl _)
  have h5 : Path.Homotopic ((A.trans (B.trans (E.symm.trans (E.trans S)))).trans EN)
      ((A.trans (B.trans ((E.symm.trans E).trans S))).trans EN) :=
    Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl A)
      (Path.Homotopic.hcomp (Path.Homotopic.refl B)
        (Path.Homotopic.trans_assoc E.symm E S).symm)) (Path.Homotopic.refl _)
  have h6 : Path.Homotopic ((A.trans (B.trans ((E.symm.trans E).trans S))).trans EN)
      ((A.trans (B.trans ((Path.refl c).trans S))).trans EN) :=
    Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl A)
      (Path.Homotopic.hcomp (Path.Homotopic.refl B)
        (Path.Homotopic.hcomp (Path.Homotopic.symm_trans E) (Path.Homotopic.refl S))))
      (Path.Homotopic.refl _)
  have h7 : Path.Homotopic ((A.trans (B.trans ((Path.refl c).trans S))).trans EN)
      ((A.trans (B.trans S)).trans EN) :=
    Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl A)
      (Path.Homotopic.hcomp (Path.Homotopic.refl B) (Path.Homotopic.refl_trans S)))
      (Path.Homotopic.refl _)
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

/-- **The join of the three-piece paths `e k · s k · (e (k+1))⁻¹`.**  The join of
`e k · s k · (e (k+1))⁻¹`, `k = 0, …, N-1`, is homotopic (relative to its endpoints) to
`e 0 · (s 0 · … · s (N-1)) · (e N)⁻¹`. -/
theorem joinNat_conj {y w : ℕ → X} (e : ∀ k, Path (y k) (w k)) (s : ∀ k, Path (w k) (w (k + 1)))
    (N : ℕ) :
    Path.Homotopic (joinNat (fun k => (e k).trans ((s k).trans ((e (k + 1)).symm))) N)
      ((e 0).trans ((joinNat s N).trans ((e N).symm))) := by
  induction N with
  | zero =>
    exact ((Path.Homotopic.hcomp (Path.Homotopic.refl (e 0))
      (Path.Homotopic.refl_trans ((e 0).symm))).trans
        (Path.Homotopic.trans_symm (e 0))).symm
  | succ N ih =>
    rw [show joinNat (fun k => (e k).trans ((s k).trans ((e (k + 1)).symm))) (N + 1) =
        (joinNat (fun k => (e k).trans ((s k).trans ((e (k + 1)).symm))) N).trans
          ((e N).trans ((s N).trans ((e (N + 1)).symm))) from rfl]
    rw [show joinNat s (N + 1) = (joinNat s N).trans (s N) from rfl]
    exact ((Path.Homotopic.hcomp ih (Path.Homotopic.refl _)).trans
      (trans_conj_cancel (e 0) (joinNat s N) (e N) (s N) ((e (N + 1)).symm))).trans
      (Path.Homotopic.trans_assoc (e 0) ((joinNat s N).trans (s N)) ((e (N + 1)).symm))

/-- A loop which is a conjugate of a null-homotopic loop is null-homotopic. -/
theorem homotopic_refl_of_conj {x y : X} (p : Path x x) (q : Path y y) (a : Path x y)
    (h1 : Path.Homotopic p (a.trans (q.trans a.symm)))
    (h2 : Path.Homotopic q (Path.refl y)) : Path.Homotopic p (Path.refl x) :=
  (h1.trans ((Path.Homotopic.hcomp (Path.Homotopic.refl a)
    (Path.Homotopic.hcomp h2 (Path.Homotopic.refl a.symm))).trans
      ((Path.Homotopic.hcomp (Path.Homotopic.refl a)
        (Path.Homotopic.refl_trans a.symm)).trans
          (Path.Homotopic.trans_symm a))))

/-! ### `Path.liftU` -/

@[simp] theorem Path.liftU_apply {U : Set ℂ} {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) (p : Path a b)
    (hp : ∀ t, p t ∈ U) (t : unitInterval) : ((Path.liftU ha hb p hp t : ↥U) : ℂ) = p t := rfl

/-- Lifting a path to a subtype commutes with reversal. -/
theorem Path.liftU_symm {U : Set ℂ} {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) (p : Path a b)
    (hp : ∀ t, p t ∈ U) :
    (Path.liftU ha hb p hp).symm
      = Path.liftU hb ha p.symm (fun t => hp (unitInterval.symm t)) := by
  ext t
  rfl

end

end Work.Smooth.JordanSeparation
