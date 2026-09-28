import Mathlib
import Submission.Work.Serre.RangeOne.seqColim
import Submission.Work.RatHurewicz.exists_killed_tower
import Submission.Work.RatHurewicz.compressRel_attachCells_range
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.Serre.piMapN_monoidHom
import Submission.Work.RatHurewicz.AttachPush.CellInterior

/-!
# The truncation tower of `W`: definitions

See `Submission/Work/Serre/RangeOne/PLAN.md` for the plan.  This file contains only the
*definitions* of the tower used by `Work.Serre.RangeOne.colimModel` and the basic (sorry-free)
facts about them:

* `preKill W w₀` — the space obtained by attaching one `3`-cell per element of `π₂(W,w₀)`, with
  inclusion `inclK`, base point `wK`; it kills `π₂` (`preKill_kills`), preserves `π₁` at every base
  point (`preKill_piMap`) and the inclusion is a closed embedding (`preKill_closed`);
* `St W w₀ s` — the `k = 2` truncation tower over `preKill W w₀` (`Work.RatHurewicz.towerState`),
  with steps `tstep` and the resulting `SeqChain` `chain W w₀`;
* compatibility lemmas between the tower and the chain (`chain_X`, `chain_step`, `incl_eq_upAt`).
-/

open scoped Topology

namespace Work.Serre.RangeOne

open Work.RatHurewicz

noncomputable section

/-! ## The pre-kill of `π₂` -/

/-- The space obtained from `W` by attaching one `3`-cell per element of `π₂(W,w₀)`. -/
abbrev preKill (W : Type) [TopologicalSpace W] (w₀ : W) : Type :=
  attachCells 1 W (HomotopyGroup (Fin 2) W w₀) (killFamily 1 W w₀)

/-- The inclusion `W → preKill W w₀`. -/
def inclK (W : Type) [TopologicalSpace W] (w₀ : W) : C(W, preKill W w₀) :=
  attachIncl 1 W _ _

variable {W : Type} [TopologicalSpace W] {w₀ : W}

/-- The base point of the pre-killed space. -/
def wK (w₀ : W) : preKill W w₀ := inclK W w₀ w₀

/-- The pre-kill kills `π₂`. -/
theorem preKill_kills : Subsingleton (HomotopyGroup (Fin 2) (preKill W w₀) (wK w₀)) :=
  killFamily_subsingleton 1 W w₀

/-- The pre-kill preserves `π₁` (at every base point). -/
theorem preKill_piMap (x : W) :
    Function.Bijective (Work.StemsB.πmap (inclK W w₀) 0 x) :=
  attachIncl_piMap_bijective_of_compress 1 W (HomotopyGroup (Fin 2) W w₀)
    (killFamily 1 W w₀) x 1 le_rfl le_rfl

/-- The pre-kill inclusion is a closed embedding. -/
theorem preKill_closed : Topology.IsClosedEmbedding (inclK W w₀) :=
  Topology.IsClosedEmbedding.mk
    (Topology.IsEmbedding.mk (isInducing_attachIncl 1 W _ _)
      (AttachRange.attachIncl_injective 1 W _ _))
    (isClosed_range_attachIncl (n := 1) (Y := W)
      (ι := HomotopyGroup (Fin 2) W w₀) (f := killFamily 1 W w₀))

/-! ## The truncation tower with `k = 2` -/

/-- The stage `s` of the truncation tower (`k = 2`) of the pre-killed space. -/
def St (W : Type) [TopologicalSpace W] (w₀ : W) (s : ℕ) :
    TowerState (preKill W w₀) (wK w₀) 2 s :=
  towerState (x₀ := wK w₀) (k := 2) (by norm_num) s

/-- The step from stage `s` to stage `s+1`: one `(s+4)`-cell per element of `π_{3+s}`. -/
def tstep (W : Type) [TopologicalSpace W] (w₀ : W) (s : ℕ) :
    C((St W w₀ s).Y, (St W w₀ (s + 1)).Y) :=
  attachIncl (2 + s) (St W w₀ s).Y
    (HomotopyGroup (Fin (2 + s + 1)) (St W w₀ s).Y ((St W w₀ s).incl (wK w₀)))
    (killFamily (2 + s) (St W w₀ s).Y ((St W w₀ s).incl (wK w₀)))

/-- The steps are closed embeddings. -/
theorem tstep_closed (s : ℕ) : Topology.IsClosedEmbedding (tstep W w₀ s) := by
  have h1 := isInducing_attachIncl (2 + s) (St W w₀ s).Y
    (HomotopyGroup (Fin (2 + s + 1)) (St W w₀ s).Y ((St W w₀ s).incl (wK w₀)))
    (killFamily (2 + s) (St W w₀ s).Y ((St W w₀ s).incl (wK w₀)))
  have h2 := AttachRange.attachIncl_injective (2 + s) (St W w₀ s).Y
    (HomotopyGroup (Fin (2 + s + 1)) (St W w₀ s).Y ((St W w₀ s).incl (wK w₀)))
    (killFamily (2 + s) (St W w₀ s).Y ((St W w₀ s).incl (wK w₀)))
  have h3 := isClosed_range_attachIncl (n := 2 + s) (Y := (St W w₀ s).Y)
    (ι := HomotopyGroup (Fin (2 + s + 1)) (St W w₀ s).Y ((St W w₀ s).incl (wK w₀)))
    (f := killFamily (2 + s) (St W w₀ s).Y ((St W w₀ s).incl (wK w₀)))
  exact Topology.IsClosedEmbedding.mk (Topology.IsEmbedding.mk h1 h2) h3

/-- The chain of closed embeddings given by the tower. -/
def chain (W : Type) [TopologicalSpace W] (w₀ : W) : SeqChain where
  X := fun s => (St W w₀ s).Y
  top := fun s => (St W w₀ s).inst
  step := fun s => tstep W w₀ s
  closed := fun s => tstep_closed s

@[simp] theorem chain_X (s : ℕ) : (chain W w₀).X s = (St W w₀ s).Y := rfl

theorem chain_step (s : ℕ) : (chain W w₀).step s = tstep W w₀ s := rfl

/-- The composite inclusion of the tower at stage `s` is the first composite of the chain. -/
theorem incl_apply_eq_upAt (s : ℕ) (x : preKill W w₀) :
    (St W w₀ s).incl x = (chain W w₀).upAt 0 s (Nat.zero_le s) x := by
  induction s with
  | zero =>
      exact (SeqChain.upAt_self (C := chain W w₀) (Nat.zero_le 0) x).symm
  | succ s ih =>
      have h1 : (St W w₀ (s + 1)).incl x = (chain W w₀).step s ((St W w₀ s).incl x) := rfl
      rw [h1, ih]
      have h2 : (chain W w₀).upAt 0 (s + 1) (Nat.zero_le (s + 1)) x
          = (chain W w₀).upAt s (s + 1) (Nat.le_succ s)
              ((chain W w₀).upAt 0 s (Nat.zero_le s) x) :=
        (SeqChain.upAt_comp (C := chain W w₀) (Nat.zero_le (s + 1)) (Nat.zero_le s)
          (Nat.le_succ s) x).symm
      rw [h2]
      have h3 : (chain W w₀).upAt s (s + 1) (Nat.le_succ s) = (chain W w₀).step s := by
        funext y
        exact (SeqChain.upAt_step (C := chain W w₀) (Nat.le_succ s) le_rfl (by omega) y).trans
          (SeqChain.upAt_self (C := chain W w₀) le_rfl _)
      rw [h3]

end

end Work.Serre.RangeOne
