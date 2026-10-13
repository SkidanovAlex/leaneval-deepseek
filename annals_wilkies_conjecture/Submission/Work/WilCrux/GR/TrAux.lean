/-
  Auxiliary lemmas for `Work.WilCrux.GR.Transfer` (peeling one level off a cylindrical cell).

  This file collects:

  * the elementary `Fin` commutation lemmas for the index reindexings `Fin.cast`/`castAdd`/
    `natAdd`/`castSucc`/`last` that occur when a `Nat` identity is pushed through `Fin.cast`;
  * the fact that the band/graph enumerations `bandIdx`/`graphIdx` are inverse to the ranks
    `bandRank`/`graphRank`, in the two forms needed below (at an index of known rank, and the
    `iff` characterisation of `bandIdx w k = j` by the value of the rank).

  Everything is `sorry`-free and rests only on `propext`, `Quot.sound` and `Classical.choice`.
-/
import Mathlib
import Submission.Work.WilCrux.GR.Defs
import Submission.Work.WilCrux.GR.RankTransfer
import Submission.Work.WilCrux.bandRank_bandIdx
import Submission.Work.WilCrux.graphRank_graphIdx

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux.GR.Tr

open Work.WilCrux

/-! ## 1. `Fin.cast` versus `castAdd`/`natAdd`/`castSucc`/`last` -/

/-- `Fin.cast` of a `Nat` identity through `Nat.add m` commutes with `castAdd`. -/
theorem cast_castAdd {m n n' : ℕ} (h : n = n') (i : Fin m) :
    Fin.cast (congrArg (Nat.add m) h) (Fin.castAdd n i) = Fin.castAdd n' i := by
  apply Fin.ext
  simp

/-- `Fin.cast` of a `Nat` identity through `Nat.add m` commutes with `natAdd`. -/
theorem cast_natAdd {m n n' : ℕ} (h : n = n') (k : Fin n) :
    Fin.cast (congrArg (Nat.add m) h) (Fin.natAdd m k) = Fin.natAdd m (Fin.cast h k) := by
  apply Fin.ext
  simp

/-- The version of `cast_castAdd` with the argument already pushed through `castSucc`
(so that `h : n + 1 = n'`). -/
theorem cast_castSucc_castAdd {m n n' : ℕ} (h : n + 1 = n') (i : Fin m) :
    Fin.cast (congrArg (Nat.add m) h) (Fin.castSucc (Fin.castAdd n i)) = Fin.castAdd n' i := by
  apply Fin.ext
  simp

/-- The version of `cast_natAdd` with the argument already pushed through `castSucc`
(so that `h : n + 1 = n'`). -/
theorem cast_castSucc_natAdd {m n n' : ℕ} (h : n + 1 = n') (k : Fin n) :
    Fin.cast (congrArg (Nat.add m) h) (Fin.castSucc (Fin.natAdd m k)) =
      Fin.natAdd m (Fin.cast h (Fin.castSucc k)) := by
  apply Fin.ext
  simp

/-- `Fin.cast` of a `Nat` identity through `Nat.add m` commutes with the last index. -/
theorem cast_last {m n n' : ℕ} (h : n + 1 = n') :
    Fin.cast (congrArg (Nat.add m) h) (Fin.last (m + n)) =
      Fin.natAdd m (Fin.cast h (Fin.last n)) := by
  apply Fin.ext
  simp

/-- The last index of `Fin (m + n + 1)` is the `natAdd`-image of the last index of `Fin (n + 1)`. -/
theorem last_eq_natAdd (m n : ℕ) : Fin.last (m + n) = Fin.natAdd m (Fin.last n) := by
  apply Fin.ext
  simp

/-- `castSucc` of a `castAdd` is the `castAdd` into the larger index set. -/
theorem castSucc_castAdd {m n : ℕ} (i : Fin m) :
    Fin.castSucc (Fin.castAdd n i) = (Fin.castAdd (n + 1) i : Fin (m + (n + 1))) := by
  apply Fin.ext
  simp

/-! ## 2. The band/graph enumerations are inverse to the ranks -/

/-- `bandIdx w` is the inverse of `bandRank w` on the band levels. -/
theorem bandIdx_bandRank {N : ℕ} (w : Fin N → CellType) {j : Fin N} (hj : bandBit (w j) = 1) :
    bandIdx w ⟨bandRank w j, bandRank_lt_nBand w hj⟩ = j := by
  have hband : bandBit (w (bandIdx w ⟨bandRank w j, bandRank_lt_nBand w hj⟩)) = 1 :=
    bandIdx_band w _
  have hrank : bandRank w (bandIdx w ⟨bandRank w j, bandRank_lt_nBand w hj⟩) = bandRank w j :=
    bandRank_bandIdx w _
  rcases lt_trichotomy (bandIdx w ⟨bandRank w j, bandRank_lt_nBand w hj⟩) j with h | h | h
  · exact absurd (hrank ▸ bandRank_lt_of_lt w hband h) (lt_irrefl _)
  · exact h
  · exact absurd (hrank ▸ bandRank_lt_of_lt w hj h) (lt_irrefl _)

/-- `graphIdx w` is the inverse of `graphRank w` on the graph levels. -/
theorem graphIdx_graphRank {N : ℕ} (w : Fin N → CellType) {j : Fin N} (hj : graphBit (w j) = 1) :
    graphIdx w ⟨graphRank w j, graphRank_lt_nGraph w hj⟩ = j := by
  have hgr : graphBit (w (graphIdx w ⟨graphRank w j, graphRank_lt_nGraph w hj⟩)) = 1 :=
    graphIdx_graph w _
  have hrank : graphRank w (graphIdx w ⟨graphRank w j, graphRank_lt_nGraph w hj⟩) = graphRank w j :=
    graphRank_graphIdx w _
  rcases lt_trichotomy (graphIdx w ⟨graphRank w j, graphRank_lt_nGraph w hj⟩) j with h | h | h
  · exact absurd (hrank ▸ graphRank_lt_of_lt w hgr h) (lt_irrefl _)
  · exact h
  · exact absurd (hrank ▸ graphRank_lt_of_lt w hj h) (lt_irrefl _)

/-- `bandIdx w k = j` exactly when `j` is a band level of rank `k`. -/
theorem bandIdx_eq_iff {N : ℕ} (w : Fin N → CellType) (k : Fin (nBand N w)) (j : Fin N) :
    bandIdx w k = j ↔ bandBit (w j) = 1 ∧ bandRank w j = (k : ℕ) := by
  constructor
  · intro h
    rw [← h]
    exact ⟨bandIdx_band w k, bandRank_bandIdx w k⟩
  · rintro ⟨hb, hr⟩
    have hk : k = ⟨bandRank w j, bandRank_lt_nBand w hb⟩ := Fin.ext hr.symm
    rw [hk]
    exact bandIdx_bandRank w hb

/-- `graphIdx w k = j` exactly when `j` is a graph level of rank `k`. -/
theorem graphIdx_eq_iff {N : ℕ} (w : Fin N → CellType) (k : Fin (nGraph N w)) (j : Fin N) :
    graphIdx w k = j ↔ graphBit (w j) = 1 ∧ graphRank w j = (k : ℕ) := by
  constructor
  · intro h
    rw [← h]
    exact ⟨graphIdx_graph w k, graphRank_graphIdx w k⟩
  · rintro ⟨hb, hr⟩
    have hk : k = ⟨graphRank w j, graphRank_lt_nGraph w hb⟩ := Fin.ext hr.symm
    rw [hk]
    exact graphIdx_graphRank w hb

end Work.WilCrux.GR.Tr
