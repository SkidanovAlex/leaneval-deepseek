import Mathlib
import Submission.Work.WilE7.LevelFibre.Defs
import Submission.Work.WilE7.prodSet

open WilkiesConjecture WilkiesDesign WilkiesDesign.E

namespace Work.WilE7.LevelFibre

/-- The point set of the `m`-fold product `SemiPf.blocks X m` is the set of points all of whose
`m` blocks lie in `X.set`.  (`m = 0` is the point of `ℝ^0`, with the vacuous condition.) -/
theorem blocks_set {N : ℕ} (X : WilkiesDesign.E.SemiPf N) (m : ℕ) :
    (Work.WilE7.LevelFibre.SemiPf.blocks X m).set =
      {Z : Fin (N * m) → ℝ | ∀ l : Fin m, Work.WilE7.LevelFibre.blk Z l ∈ X.set} := by
  induction m with
  | zero =>
    ext Z
    constructor
    · intro _ l; exact l.elim0
    · intro _
      refine ⟨fun i => i.elim0, ⟨⟨[], []⟩, List.mem_singleton.mpr rfl, ?_⟩⟩
      exact ⟨fun f hf => (List.not_mem_nil (a := f) hf).elim,
             fun g hg => (List.not_mem_nil (a := g) hg).elim⟩
  | succ m ih =>
    ext Z
    rw [SemiPf.blocks_succ, Work.WilE7.prodSet, ih]
    change (∀ l : Fin m, blk (projFirst (N*m) N Z) l ∈ X.set) ∧ projSnd (N*m) N Z ∈ X.set ↔
      ∀ l : Fin (m+1), blk Z l ∈ X.set
    -- the first `N*m` coordinates of the block space `ℝ^{N*(m+1)}` are the blocks `0,…,m-1`
    have hcast : ∀ l : Fin m, blk (projFirst (N*m) N Z) l = blk Z (Fin.castSucc l) := by
      intro l; funext i; apply congrArg Z; apply Fin.ext
      simp [blkIdx_val, Fin.castAdd, Fin.castSucc]
    -- the last `N` coordinates are the last block
    have hlast : projSnd (N*m) N Z = blk Z (Fin.last m) := by
      funext i; apply congrArg Z; apply Fin.ext
      simp [blkIdx_val, Fin.natAdd, Nat.mul_comm]
    have hfor : (∀ l : Fin (m+1), blk Z l ∈ X.set) ↔
        ((∀ l : Fin m, blk Z (Fin.castSucc l) ∈ X.set) ∧ blk Z (Fin.last m) ∈ X.set) := by
      constructor
      · intro h; exact ⟨fun l => h _, h _⟩
      · rintro ⟨h1, h2⟩ l
        exact Fin.lastCases h2 (fun i => h1 i) l
    rw [hfor, hlast]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun l => by rw [← hcast l]; exact h1 l, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun l => by rw [hcast l]; exact h1 l, h2⟩

end Work.WilE7.LevelFibre
