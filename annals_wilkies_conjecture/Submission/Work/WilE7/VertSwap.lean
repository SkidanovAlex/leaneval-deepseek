/-
  Area E7 (`Work.WilE7.VertSwap`): moving the *vertical* coordinate of a fibre-cut piece to the last
  fibre position.

  In the level step `Core n → Core (n+1)` (`NOTES_S26_level_step.md` §4.2) the pieces produced by
  `hFC` at `(n, M+1)` are `SemiPf (n + (M+1))`, whose *first* fibre coordinate (ambient index `n`)
  is the vertical coordinate that `π_{n+1}` keeps.  All the S11 cell lemmas (`sheetCells_cyl_noc`,
  `graphCell_subPf`, `bandCell_bd`, …) use the *last* fibre coordinate as the level.  Swapping the
  two ambient coordinates `n` and `n+M` fixes this: the swapped piece has the same format, degree
  and base projection, and its last fibre coordinate is the original vertical one.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.star_proj

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- The transposition of the ambient coordinates `n` and `n+M` in `ℝ^{n+(M+1)}`: it fixes the
base `0, …, n-1` and exchanges the first and the last fibre coordinate. -/
def vertSwap (n M : ℕ) : Equiv.Perm (Fin (n + (M + 1))) :=
  Equiv.swap ⟨n, by omega⟩ ⟨n + M, by omega⟩

theorem vertSwap_apply_left (n M : ℕ) :
    vertSwap n M ⟨n, by omega⟩ = ⟨n + M, by omega⟩ :=
  Equiv.swap_apply_left _ _

theorem vertSwap_apply_right (n M : ℕ) :
    vertSwap n M ⟨n + M, by omega⟩ = ⟨n, by omega⟩ :=
  Equiv.swap_apply_right _ _

theorem vertSwap_apply_castAdd (n M : ℕ) (i : Fin n) :
    vertSwap n M (Fin.castAdd (M + 1) i) = Fin.castAdd (M + 1) i := by
  refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;> intro h
  · have := congrArg Fin.val h
    simp only [Fin.val_castAdd] at this
    omega
  · have := congrArg Fin.val h
    simp only [Fin.val_castAdd] at this
    omega

/-- Reindexing a piece along `vertSwap` does not change its format. -/
theorem vertSwap_fmt (n M : ℕ) (P : WilkiesDesign.E.SemiPf (n + (M + 1))) :
    (Work.WilE7.SemiPf.reindex (vertSwap n M) P).fmt = P.fmt := by
  simp only [WilkiesDesign.E.SemiPf.fmt, Work.WilE7.SemiPf.reindex]

/-- Reindexing a piece along `vertSwap` does not change its degree. -/
theorem vertSwap_deg (n M : ℕ) (P : WilkiesDesign.E.SemiPf (n + (M + 1))) :
    (Work.WilE7.SemiPf.reindex (vertSwap n M) P).deg = P.deg :=
  sp_reindex_deg (vertSwap n M) P

theorem vertSwap_set (n M : ℕ) (P : WilkiesDesign.E.SemiPf (n + (M + 1))) :
    (Work.WilE7.SemiPf.reindex (vertSwap n M) P).set = {y | (fun i => y (vertSwap n M i)) ∈ P.set} :=
  sp_reindex_set (vertSwap n M) P

/-- The base projection is unchanged by `vertSwap`. -/
theorem vertSwap_proj (n M : ℕ) (P : WilkiesDesign.E.SemiPf (n + (M + 1))) :
    WilkiesDesign.E.projFirst n (M + 1) '' (Work.WilE7.SemiPf.reindex (vertSwap n M) P).set
      = WilkiesDesign.E.projFirst n (M + 1) '' P.set := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    rw [vertSwap_set] at hy
    refine ⟨fun i => y (vertSwap n M i), hy, ?_⟩
    funext i
    show y (vertSwap n M (Fin.castAdd (M + 1) i)) = y (Fin.castAdd (M + 1) i)
    rw [vertSwap_apply_castAdd]
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨fun i => z ((vertSwap n M).symm i), ?_, ?_⟩
    · rw [vertSwap_set]
      show (fun i => z ((vertSwap n M).symm (vertSwap n M i))) ∈ P.set
      rw [show (fun i => z ((vertSwap n M).symm (vertSwap n M i))) = z from
        funext fun i => by rw [Equiv.symm_apply_apply]]
      exact hz
    · funext i
      show z ((vertSwap n M).symm (Fin.castAdd (M + 1) i)) = z (Fin.castAdd (M + 1) i)
      congr 1
      refine (vertSwap n M).injective ?_
      rw [Equiv.apply_symm_apply, vertSwap_apply_castAdd]

/-- In the swapped piece, the last fibre coordinate is the first fibre coordinate (the vertical
coordinate kept by `π_{n+1}`) of the original piece. -/
theorem vertSwap_level (n M : ℕ) (P : WilkiesDesign.E.SemiPf (n + (M + 1)))
    {y : Fin (n + (M + 1)) → ℝ} (hy : y ∈ (Work.WilE7.SemiPf.reindex (vertSwap n M) P).set) :
    y ⟨n + M, by omega⟩ = (fun i => y (vertSwap n M i)) ⟨n, by omega⟩ := by
  show y ⟨n + M, by omega⟩ = y (vertSwap n M ⟨n, by omega⟩)
  rw [vertSwap_apply_left]

end Work.WilE7
