import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_cells
import Submission.Work.Smooth.JordanSeparation.gridWalk_approx

/-!
# The lifted walk in an open set, and the corner move

This file sets up the `↥U`-level realization of a lattice walk and the local moves of the
peel (`_LWALK_PEEL_NOTES.md`): the *corner cut* at the lex-max vertex, and the *backtrack
removal*.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

namespace LWalk

variable {W : LWalk} {U : Set ℂ} (hval : ∀ t, W.path t ∈ U)

/-- The `k`-th vertex of the walk, as a point of `↥U`, for `k ≤ W.n`. -/
def ptU (k : ℕ) (hk : k ≤ W.n) : ↥U := ⟨W.pt k, W.pt_mem hval hk⟩

/-- The `k`-th edge of the walk, as a path in `↥U`. -/
def edgeU (k : ℕ) (hk : k < W.n) :
    Path (W.ptU hval k (le_of_lt hk)) (W.ptU hval (k + 1) (Nat.succ_le_of_lt hk)) :=
  Path.liftU (W.pt_mem hval (le_of_lt hk)) (W.pt_mem hval (Nat.succ_le_of_lt hk))
    (W.edge k) (W.edge_mem hval hk)

/-- The lifted realization of the walk, as the join of its lifted edges. -/
def pathU : Path (W.ptU hval 0 (Nat.zero_le _)) (W.ptU hval W.n (le_refl _)) :=
  joinFam W.n (fun i => W.ptU hval i (Nat.lt_succ_iff.mp i.2)) (fun k => W.edgeU hval k k.2)

/-- The lifted loop of the walk, in `↥U`. -/
def loopU : Path (W.ptU hval 0 (Nat.zero_le _)) (W.ptU hval 0 (Nat.zero_le _)) :=
  (W.pathU hval).cast rfl (Subtype.ext W.pt_last.symm)

@[simp] theorem ptU_apply (k : ℕ) (hk : k ≤ W.n) : ((W.ptU hval k hk : ↥U) : ℂ) = W.pt k := rfl

@[simp] theorem edgeU_apply (k : ℕ) (hk : k < W.n) (t : unitInterval) :
    ((W.edgeU hval k hk t : ↥U) : ℂ) = W.edge k t := rfl

end LWalk

end

end Work.Smooth.JordanSeparation

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- The straight segment from `a` to `b`, as a path in `↥U`, when `a`, `b` lie in a convex set
`B ⊆ U`. -/
def segIn {U B : Set ℂ} (hB : Convex ℝ B) (hBU : B ⊆ U) {a b : ℂ} (ha : a ∈ B) (hb : b ∈ B) :
    Path (⟨a, hBU ha⟩ : ↥U) (⟨b, hBU hb⟩ : ↥U) :=
  Path.liftU (hBU ha) (hBU hb) (Path.segment a b)
    (fun t => hBU (hB.segment_subset ha hb (by
      rw [← Path.range_segment]; exact ⟨t, rfl⟩)))

@[simp] theorem segIn_apply {U B : Set ℂ} (hB : Convex ℝ B) (hBU : B ⊆ U) {a b : ℂ}
    (ha : a ∈ B) (hb : b ∈ B) (t : unitInterval) :
    ((segIn hB hBU ha hb t : ↥U) : ℂ) = Path.segment a b t := rfl

/-- **The corner move.**  If `a`, `p`, `b`, `s` lie in a convex `B ⊆ U`, then the two-edge path
`a → p → b` is homotopic in `↥U` to the two-edge path `a → s → b`.  This is the local move of the
peel at the lex-max vertex of a lattice walk (with `p` the corner and `s` the opposite corner of
the corner cell). -/
theorem corner_homotopic {U B : Set ℂ} (hB : Convex ℝ B) (hBne : B.Nonempty) (hBU : B ⊆ U)
    {a p b s : ℂ} (ha : a ∈ B) (hp : p ∈ B) (hb : b ∈ B) (hs : s ∈ B) :
    Path.Homotopic ((segIn hB hBU ha hp).trans (segIn hB hBU hp hb))
      ((segIn hB hBU ha hs).trans (segIn hB hBU hs hb)) := by
  refine homotopic_of_convex_subset hB hBne hBU _ _ ?_ ?_
  · intro t
    rw [Path.trans_apply]
    by_cases h : (t : ℝ) ≤ 1 / 2
    · rw [dif_pos h]
      exact hB.segment_subset ha hp (by rw [← Path.range_segment]; exact ⟨_, rfl⟩)
    · rw [dif_neg h]
      exact hB.segment_subset hp hb (by rw [← Path.range_segment]; exact ⟨_, rfl⟩)
  · intro t
    rw [Path.trans_apply]
    by_cases h : (t : ℝ) ≤ 1 / 2
    · rw [dif_pos h]
      exact hB.segment_subset ha hs (by rw [← Path.range_segment]; exact ⟨_, rfl⟩)
    · rw [dif_neg h]
      exact hB.segment_subset hs hb (by rw [← Path.range_segment]; exact ⟨_, rfl⟩)

/-- **The backtrack move.**  If `a`, `p` lie in a convex `B ⊆ U`, the two-edge path `a → p → a` is
null-homotopic in `↥U`. -/
theorem backtrack_homotopic {U B : Set ℂ} (hB : Convex ℝ B) (hBne : B.Nonempty) (hBU : B ⊆ U)
    {a p : ℂ} (ha : a ∈ B) (hp : p ∈ B) :
    Path.Homotopic ((segIn hB hBU ha hp).trans (segIn hB hBU hp ha))
      (Path.refl (⟨a, hBU ha⟩ : ↥U)) := by
  refine homotopic_of_convex_subset hB hBne hBU _ _ ?_ ?_
  · intro t
    rw [Path.trans_apply]
    by_cases h : (t : ℝ) ≤ 1 / 2
    · rw [dif_pos h]
      exact hB.segment_subset ha hp (by rw [← Path.range_segment]; exact ⟨_, rfl⟩)
    · rw [dif_neg h]
      exact hB.segment_subset hp ha (by rw [← Path.range_segment]; exact ⟨_, rfl⟩)
  · intro t
    simpa using ha


/-! ### Replacing two consecutive pieces of a join

The engine of the corner move: if two `joinNat` families have homotopic prefixes, homotopic
two-path products at two consecutive indices, and homotopic suffixes, then the joins are homotopic.
The two-path product is exactly the piece that `corner_homotopic` moves. -/

theorem joinNat_pair_congr {X : Type*} [TopologicalSpace X] {p : ℕ → X} {i k : ℕ}
    {F F' : ∀ j, Path (p j) (p (j + 1))}
    (hpre : Path.Homotopic (joinNat F i) (joinNat F' i))
    (hpair : Path.Homotopic ((F i).trans (F (i + 1))) ((F' i).trans (F' (i + 1))))
    (hsuf : Path.Homotopic
      (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k)
      (joinNat (p := fun l => p (i + (2 + l))) (fun l => F' (i + (2 + l))) k)) :
    Path.Homotopic (joinNat F (i + (2 + k))) (joinNat F' (i + (2 + k))) := by
  -- the two-path pieces
  have hpair' : Path.Homotopic
      (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2)
      (joinNat (p := fun l => p (i + l)) (fun l => F' (i + l)) 2) := by
    have e1 : joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2
        = ((Path.refl (p i)).trans (F i)).trans (F (i + 1)) := rfl
    have e2 : joinNat (p := fun l => p (i + l)) (fun l => F' (i + l)) 2
        = ((Path.refl (p i)).trans (F' i)).trans (F' (i + 1)) := rfl
    rw [e1, e2]
    exact (Path.Homotopic.hcomp (Path.Homotopic.refl_trans (F i))
        (Path.Homotopic.refl _)).trans
      (hpair.trans (Path.Homotopic.hcomp (Path.Homotopic.refl_trans (F' i))
        (Path.Homotopic.refl _)).symm)
  -- the suffix family at `i + 2` is the one appearing in `hsuf`
  -- split both joins
  have hF : Path.Homotopic (joinNat F (i + (2 + k)))
      ((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) (2 + k))) :=
    joinNat_add F i (2 + k)
  have hF' : Path.Homotopic (joinNat F' (i + (2 + k)))
      ((joinNat F' i).trans (joinNat (p := fun l => p (i + l)) (fun l => F' (i + l)) (2 + k))) :=
    joinNat_add F' i (2 + k)
  have hG : Path.Homotopic (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) (2 + k))
      ((joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k)) :=
    joinNat_add (p := fun l => p (i + l)) (fun l => F (i + l)) 2 k
  have hG' : Path.Homotopic (joinNat (p := fun l => p (i + l)) (fun l => F' (i + l)) (2 + k))
      ((joinNat (p := fun l => p (i + l)) (fun l => F' (i + l)) 2).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F' (i + (2 + l))) k)) :=
    joinNat_add (p := fun l => p (i + l)) (fun l => F' (i + l)) 2 k
  have h1 : Path.Homotopic ((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2)) ((joinNat F' i).trans (joinNat (p := fun l => p (i + l)) (fun l => F' (i + l)) 2)) :=
    Path.Homotopic.hcomp hpre hpair'
  have h2 : Path.Homotopic ((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) (2 + k)))
      ((joinNat F i).trans ((joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2).trans (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k))) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _) hG
  have h3 : Path.Homotopic ((joinNat F i).trans ((joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2).trans (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k)))
      (((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2)).trans (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k)) :=
    (Path.Homotopic.trans_assoc _ _ _).symm
  have h4 : Path.Homotopic (((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2)).trans (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k))
      (((joinNat F' i).trans (joinNat (p := fun l => p (i + l)) (fun l => F' (i + l)) 2)).trans (joinNat (p := fun l => p (i + (2 + l))) (fun l => F' (i + (2 + l))) k)) :=
    Path.Homotopic.hcomp h1 hsuf
  have h5 : Path.Homotopic (((joinNat F' i).trans (joinNat (p := fun l => p (i + l)) (fun l => F' (i + l)) 2)).trans (joinNat (p := fun l => p (i + (2 + l))) (fun l => F' (i + (2 + l))) k))
      ((joinNat F' i).trans ((joinNat (p := fun l => p (i + l)) (fun l => F' (i + l)) 2).trans (joinNat (p := fun l => p (i + (2 + l))) (fun l => F' (i + (2 + l))) k))) :=
    Path.Homotopic.trans_assoc _ _ _
  have h6 : Path.Homotopic ((joinNat F' i).trans ((joinNat (p := fun l => p (i + l)) (fun l => F' (i + l)) 2).trans (joinNat (p := fun l => p (i + (2 + l))) (fun l => F' (i + (2 + l))) k)))
      ((joinNat F' i).trans (joinNat (p := fun l => p (i + l)) (fun l => F' (i + l)) (2 + k))) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _) hG'.symm
  exact hF.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans hF'.symm)))))

/-- **Replacing a two-step piece by an arbitrary homotopic path.**  This is the form of the
surgery that the corner move actually uses: the intermediate vertex of the two-step piece is not
required to be an index of `p`, so the replacement path `Q` may go through any point at all (for
the peel: through the opposite corner of the cell). -/
theorem joinNat_replace {X : Type*} [TopologicalSpace X] {p : ℕ → X} {F : ∀ j, Path (p j) (p (j + 1))}
    {i k : ℕ} (Q : Path (p i) (p (i + 2)))
    (hQ : Path.Homotopic ((F i).trans (F (i + 1))) Q) :
    Path.Homotopic (joinNat F (i + (2 + k)))
      ((joinNat F i).trans (Q.trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k))) := by
  -- normalise the two-step piece
  have hpair : Path.Homotopic
      (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2) Q := by
    have e1 : joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2
        = ((Path.refl (p i)).trans (F i)).trans (F (i + 1)) := rfl
    rw [e1]
    exact (Path.Homotopic.hcomp (Path.Homotopic.refl_trans (F i))
      (Path.Homotopic.refl _)).trans hQ
  -- the two splittings
  have hF : Path.Homotopic (joinNat F (i + (2 + k)))
      ((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) (2 + k))) :=
    joinNat_add F i (2 + k)
  have hG : Path.Homotopic (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) (2 + k))
      ((joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k)) :=
    joinNat_add (p := fun l => p (i + l)) (fun l => F (i + l)) 2 k
  -- assemble
  have h2 : Path.Homotopic ((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) (2 + k)))
      ((joinNat F i).trans ((joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k))) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _) hG
  have h3 : Path.Homotopic
      ((joinNat F i).trans ((joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k)))
      (((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2)).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k)) :=
    (Path.Homotopic.trans_assoc _ _ _).symm
  have h4 : Path.Homotopic
      (((joinNat F i).trans (joinNat (p := fun l => p (i + l)) (fun l => F (i + l)) 2)).trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k))
      ((joinNat F i).trans (Q.trans
        (joinNat (p := fun l => p (i + (2 + l))) (fun l => F (i + (2 + l))) k))) :=
    ((Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl _) hpair)
        (Path.Homotopic.refl _)).trans
      (Path.Homotopic.trans_assoc _ _ _))
  exact hF.trans (h2.trans (h3.trans h4))

end

end Work.Smooth.JordanSeparation
