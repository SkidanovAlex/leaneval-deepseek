import Mathlib
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced

namespace Work.ORBassSerre.Tree.Walk

open Quiver

variable {V : Type*} [Quiver V]

/-!  ## Simplicial walks as chains of arrows

Given a vertex sequence `z : ℕ → V` and steps `F : ℕ → Quiver.Total V` with
`(F k).left = z k` and `(F k).right = z (k+1)`, the `k`-th step is an arrow
`z k ⟶ z (k+1)` (after transporting along the two vertex equalities).  Chaining these
arrows gives the path `closedWalkChain` traced out by the walk.  The main combinatorial fact is
that a backtrack in this path forces an adjacent pair of steps to be mutually inverse.
-/

/-- The `k`-th step of a walk, as an arrow `z k ⟶ z (k + 1)`. -/
noncomputable def closedWalkStep (n : ℕ) (z : ℕ → V) (F : ℕ → Quiver.Total V)
    (hsrc : ∀ k, k < n → (F k).left = z k) (htgt : ∀ k, k < n → (F k).right = z (k + 1))
    (k : ℕ) (hk : k < n) : z k ⟶ z (k + 1) :=
  (F k).hom.cast (hsrc k hk) (htgt k hk)

/-- The `k`-th step, reassembled as a `Quiver.Total`, is the step `F k` of the walk. -/
theorem closedWalkStep_total (n : ℕ) (z : ℕ → V) (F : ℕ → Quiver.Total V)
    (hsrc : ∀ k, k < n → (F k).left = z k) (htgt : ∀ k, k < n → (F k).right = z (k + 1))
    (k : ℕ) (hk : k < n) :
    Total.mk (z k) (z (k + 1)) (closedWalkStep n z F hsrc htgt k hk) = F k := by
  refine Total.ext ?_ ?_ ?_
  · exact (hsrc k hk).symm
  · exact (htgt k hk).symm
  · exact Quiver.Hom.cast_heq _ _ _

/-- The path traced out by the first `d` steps of a walk, from `z 0` to `z d`. -/
noncomputable def closedWalkChain (n : ℕ) (z : ℕ → V) (F : ℕ → Quiver.Total V)
    (hsrc : ∀ k, k < n → (F k).left = z k) (htgt : ∀ k, k < n → (F k).right = z (k + 1)) :
    (d : ℕ) → d ≤ n → Quiver.Path (z 0) (z d)
  | 0, _ => Quiver.Path.nil
  | d + 1, h => (closedWalkChain n z F hsrc htgt d (Nat.le_of_succ_le h)).cons
      (closedWalkStep n z F hsrc htgt d (Nat.lt_of_succ_le h))

/-- Unfolding of `closedWalkChain` at a successor index: the walk path is the walk path of the first
`d` steps with the `d`-th step appended. -/
theorem closedWalkChain_succ (n : ℕ) (z : ℕ → V) (F : ℕ → Quiver.Total V)
    (hsrc : ∀ k, k < n → (F k).left = z k) (htgt : ∀ k, k < n → (F k).right = z (k + 1))
    (d : ℕ) (h : d + 1 ≤ n) :
    closedWalkChain n z F hsrc htgt (d + 1) h =
      (closedWalkChain n z F hsrc htgt d (Nat.le_of_succ_le h)).cons
        (closedWalkStep n z F hsrc htgt d (Nat.lt_of_succ_le h)) := rfl

/-- The walk path of the first `d` steps has length `d`. -/
theorem closedWalkChain_length (n : ℕ) (z : ℕ → V) (F : ℕ → Quiver.Total V)
    (hsrc : ∀ k, k < n → (F k).left = z k) (htgt : ∀ k, k < n → (F k).right = z (k + 1)) :
    ∀ (d : ℕ) (hd : d ≤ n), (closedWalkChain n z F hsrc htgt d hd).length = d := by
  intro d
  induction d with
  | zero => intro hd; rfl
  | succ d ih =>
    intro hd
    rw [closedWalkChain_succ, Quiver.Path.length_cons, ih (Nat.le_of_succ_le hd)]

/-- Transporting a path along equalities of its endpoints preserves its length. -/
theorem qpath_length_cast {u v u' v' : V} (hu : u = u') (hv : v = v') (p : Quiver.Path u v) :
    (p.cast hu hv).length = p.length := by
  subst hu; subst hv; simp

variable [Quiver.HasReverse V]

/-- Reversal commutes with transporting an arrow along equalities of its endpoints. -/
theorem reverse_hom_cast {u v u' v' : V} (hu : u = u') (hv : v = v') (e : u ⟶ v) :
    Quiver.reverse (e.cast hu hv) = (Quiver.reverse e).cast hv hu := by
  subst hu; subst hv; simp

/-- Transporting a reduced path along equalities of its endpoints gives a reduced path. -/
theorem qpath_isReduced_cast {u v u' v' : V} (hu : u = u') (hv : v = v')
    {p : Quiver.Path u v} (h : p.IsReduced) : (p.cast hu hv).IsReduced := by
  subst hu; subst hv; simpa using h

/-- **The junction computation.**  If the `(j+1)`-st step of a walk is the reverse of an arrow
`e'` (of type `z (j+2) ⟶ z (j+1)`) and the `j`-th step is `e'` (transported along the vertex
equality `z j = z (j+2)` forced by a backtrack), then the two `Quiver.Total` steps `j` and `j+1`
of the walk are mutually inverse. -/
theorem closedWalk_total_eq_reverse (n : ℕ) (z : ℕ → V) (F : ℕ → Quiver.Total V)
    (hsrc : ∀ k, k < n → (F k).left = z k) (htgt : ∀ k, k < n → (F k).right = z (k + 1))
    {j : ℕ} (hj : j + 1 < n) (hz : z j = z (j + 2))
    (h : closedWalkStep n z F hsrc htgt (j + 1) (by omega) =
      (Quiver.reverse (closedWalkStep n z F hsrc htgt j (by omega))).cast rfl hz) :
    F (j + 1) = (F j).reverse := by
  have hj1 : j + 1 < n := by omega
  have hj0 : j < n := by omega
  calc F (j + 1)
      = Total.mk (z (j + 1)) (z (j + 2)) (closedWalkStep n z F hsrc htgt (j + 1) hj1) :=
        (closedWalkStep_total n z F hsrc htgt (j + 1) hj1).symm
    _ = Total.mk (z (j + 1)) (z (j + 2))
          ((Quiver.reverse (closedWalkStep n z F hsrc htgt j hj0)).cast rfl hz) := by rw [h]
    _ = Total.mk (z (j + 1)) (z j) (Quiver.reverse (closedWalkStep n z F hsrc htgt j hj0)) := by
        refine Total.ext rfl hz.symm ?_
        exact Quiver.Hom.cast_heq rfl hz (Quiver.reverse (closedWalkStep n z F hsrc htgt j hj0))
    _ = (Total.mk (z j) (z (j + 1)) (closedWalkStep n z F hsrc htgt j hj0)).reverse :=
        (Total.reverse_mk (closedWalkStep n z F hsrc htgt j hj0)).symm
    _ = (F j).reverse := by rw [closedWalkStep_total]

/-- **A walk without immediate backtracking sweeps out a reduced path.**  If no two consecutive
steps of a walk (among the first `d`) are mutually inverse, then the path traced out by those `d`
steps is reduced. -/
theorem closedWalkChain_isReduced_aux (n : ℕ) (z : ℕ → V) (F : ℕ → Quiver.Total V)
    (hsrc : ∀ k, k < n → (F k).left = z k) (htgt : ∀ k, k < n → (F k).right = z (k + 1)) :
    ∀ (d : ℕ) (hd : d ≤ n), (∀ k, k + 1 < d → F (k + 1) ≠ (F k).reverse) →
      (closedWalkChain n z F hsrc htgt d hd).IsReduced := by
  intro d
  induction d with
  | zero => intro hd _; exact Quiver.Path.IsReduced.nil _
  | succ d ih =>
    intro hd hno
    rw [closedWalkChain_succ]
    intro q hq
    rcases (Work.ORBassSerre.Tree.Map.deleteBacktrack_cons_iff
      (closedWalkChain n z F hsrc htgt d (Nat.le_of_succ_le hd))
      (closedWalkStep n z F hsrc htgt d (Nat.lt_of_succ_le hd)) q).mp hq with
      ⟨r₀, hr₀, -⟩ | ⟨p', e', hp', he', -⟩
    · exact ih (Nat.le_of_succ_le hd) (fun k hk => hno k (by omega)) r₀ hr₀
    · cases d with
      | zero =>
        exact (Quiver.Path.cons_ne_nil p' e') hp'.symm
      | succ d' =>
        rw [closedWalkChain_succ] at hp'
        have hz : z d' = z (d' + 2) := Quiver.Path.obj_eq_of_cons_eq_cons hp'
        have hheq : HEq (closedWalkStep n z F hsrc htgt d' (by omega)) e' :=
          Quiver.Path.hom_heq_of_cons_eq_cons hp'
        have hcast : (closedWalkStep n z F hsrc htgt d' (by omega)).cast hz rfl = e' :=
          (Quiver.Hom.cast_eq_iff_heq hz rfl _ _).mpr hheq
        have hstep : closedWalkStep n z F hsrc htgt (d' + 1) (by omega) =
            (Quiver.reverse (closedWalkStep n z F hsrc htgt d' (by omega))).cast rfl hz := by
          rw [he', ← hcast, reverse_hom_cast]
        exact hno d' (by omega) (closedWalk_total_eq_reverse n z F hsrc htgt (by omega) hz hstep)

/-- **Closed walks in a tree backtrack.**  Let `V` be a tree (a quiver with involutive reversal,
`Work.ORBassSerre.IsTree`).  Let `z : ℕ → V` be the vertex sequence of a walk of length `n > 0` and
`F : ℕ → Quiver.Total V` its steps, so that `(F k).left = z k` and `(F k).right = z (k+1)` for
`k < n`.  If the walk is closed, `z n = z 0`, then two consecutive steps are mutually inverse:
there is `k` with `k + 1 < n` and `F (k+1) = (F k).reverse`.-/
theorem exists_consecutive_backtrack_of_closed_walk {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] (hT : Work.ORBassSerre.IsTree V)
    (n : ℕ) (hn : 0 < n) (z : ℕ → V) (F : ℕ → Quiver.Total V)
    (hsrc : ∀ k, k < n → (F k).left = z k)
    (htgt : ∀ k, k < n → (F k).right = z (k + 1))
    (hclosed : z n = z 0) :
    ∃ k, k + 1 < n ∧ F (k + 1) = (F k).reverse := by
  by_contra hcon
  push Not at hcon
  have hred : (closedWalkChain n z F hsrc htgt n le_rfl).IsReduced :=
    closedWalkChain_isReduced_aux n z F hsrc htgt n le_rfl hcon
  have hnil : (closedWalkChain n z F hsrc htgt n le_rfl).cast rfl hclosed = Quiver.Path.nil :=
    hT.2 (z 0) _ (qpath_isReduced_cast rfl hclosed hred)
  have hlen : ((closedWalkChain n z F hsrc htgt n le_rfl).cast rfl hclosed).length = n := by
    rw [qpath_length_cast]
    exact closedWalkChain_length n z F hsrc htgt n le_rfl
  rw [hnil, Quiver.Path.length_nil] at hlen
  omega

end Work.ORBassSerre.Tree.Walk
