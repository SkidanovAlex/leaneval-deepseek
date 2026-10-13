import Mathlib
import Submission.Work.WilCrux.GR.Defs

namespace Work.WilCrux.GR

open Work.WilCrux

/-! ## Reindexing helpers

Both the graph case (`resG`/`liftG`) and the band case (`resB`/`lastB`/`mkB`) of the `GR`
bookkeeping are `Fin.cast` along the `Nat` identities of `nBand_snoc_graph`/`nBand_snoc_band`,
together with the `castSucc`/`last` decomposition of `Fin (n+1)`. The two elementary facts used
below are that `Fin.cast` along a *self*-equality is the identity, and that `Fin.snoc` really does
append the last entry to the initial segment. -/

/-- `Fin.cast` along a proof of `n = n` is the identity. -/
theorem finCast_self_eq {n : ℕ} (h : n = n) (x : Fin n) : Fin.cast h x = x :=
  Fin.ext (by simp)

/-- `Fin.snoc` appends the last entry to the initial segment: recovering a function from its
restriction to `castSucc` together with its value at `last`. -/
theorem snoc_eta {n : ℕ} (v : Fin (n + 1) → ℝ) :
    Fin.snoc (fun i => v i.castSucc) (v (Fin.last n)) = v := by
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | hk
  · rw [Fin.snoc_castSucc]
  · subst hk; rw [Fin.snoc_last]

/-- The band/graph coordinate bookkeeping of `Defs.lean`: `resB`/`lastB` and `mkB` are mutually
inverse, as are `resG` and `liftG`. This is the purely combinatorial content of peeling the top
level off a cylindrical cell. -/
theorem PairMaps (m N : ℕ) (w' : Fin N → Work.WilCrux.CellType) :
    (∀ vw : (Fin (m + Work.WilCrux.nBand N w') → ℝ) × ℝ,
        Work.WilCrux.resB m N w' (Work.WilCrux.mkB m N w' vw) = vw.1) ∧
    (∀ vw : (Fin (m + Work.WilCrux.nBand N w') → ℝ) × ℝ,
        Work.WilCrux.lastB m N w' (Work.WilCrux.mkB m N w' vw) = vw.2) ∧
    (∀ v : Fin (m + Work.WilCrux.nBand (N + 1) (Fin.snoc w' Work.WilCrux.CellType.band)) → ℝ,
        Work.WilCrux.mkB m N w' (Work.WilCrux.resB m N w' v,
          Work.WilCrux.lastB m N w' v) = v) ∧
    (∀ v : Fin (m + Work.WilCrux.nBand N w') → ℝ,
        Work.WilCrux.resG m N w' (Work.WilCrux.liftG m N w' v) = v) ∧
    (∀ v : Fin (m + Work.WilCrux.nBand (N + 1) (Fin.snoc w' Work.WilCrux.CellType.graph)) → ℝ,
        Work.WilCrux.liftG m N w' (Work.WilCrux.resG m N w' v) = v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `resB` after `mkB` reads off the initial segment
    intro vw
    funext i
    simp only [resB, mkB]
    rw [Fin.cast_cast, finCast_self_eq, Fin.snoc_castSucc]
  · -- `lastB` after `mkB` reads off the appended last entry
    intro vw
    simp only [lastB, mkB]
    rw [Fin.cast_cast, finCast_self_eq, Fin.snoc_last]
  · -- `mkB` after `(resB, lastB)` is the identity
    intro v
    funext j
    have heta : Fin.snoc (resB m N w' v) (lastB m N w' v)
        = fun k => v (Fin.cast (congrArg (Nat.add m) (nBand_snoc_band N w').symm) k) :=
      snoc_eta (fun k => v (Fin.cast (congrArg (Nat.add m) (nBand_snoc_band N w').symm) k))
    have hcast : Fin.cast (congrArg (Nat.add m) (nBand_snoc_band N w').symm)
        (Fin.cast (congrArg (Nat.add m) (nBand_snoc_band N w')) j) = j := by
      rw [Fin.cast_cast, finCast_self_eq]
    exact (congrFun heta (Fin.cast (congrArg (Nat.add m) (nBand_snoc_band N w')) j)).trans
      (congrArg v hcast)
  · -- `resG` after `liftG`
    intro v
    funext i
    simp only [resG, liftG]
    rw [Fin.cast_cast, finCast_self_eq]
  · -- `liftG` after `resG`
    intro v
    funext j
    simp only [resG, liftG]
    rw [Fin.cast_cast, finCast_self_eq]

end Work.WilCrux.GR
