/-
  `Work.WilE7.coreLT_succ.reindex_family_base`: the coordinate transfer of a *family* of
  semi-Pfaffian sets from the `((n+1)+m)`-split to the `(n+(m+1))`-split along
  `Work.WilE7.CoreStep.swapEquiv n m`.

  For every `i` the reindexed set `SemiPf.reindex (swapEquiv n m) (X i)` has the same chain
  length `r` (trivial) and the same degree `deg` (`sp_reindex_deg`), its point set is the
  `σ⁻¹`-pullback of `(X i).set` (`sp_reindex_swap_set`), and — the point of the construction —
  the base projection `π_n` of the reindexed set (in the `(n, m+1)` split, i.e. `projFirst n (m+1)`)
  is exactly `basePr n m '' (X i).set`, the base projection of the original set
  (`projFirst_swap_comp`: `swapEquiv n m` fixes the base coordinates).

  The last identity is what lets the level-`(n+1)` arguments of
  `NOTES_S32_CoreLT_succ_design.md` §2 be run in the swapped picture: the base of the design
  (`basePr n m`) coincides with the `π_n` of the reindexed family.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.ProjTopTransfer
import Submission.Work.WilE7.CoreStep.ProjTopDefs
import Submission.Work.WilE7.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E
open Work.WilE7

/-- The point set of a `swapEquiv n m`-reindexed semi-Pfaffian set, in image form: it is the
`σ⁻¹`-pullback of the original set (`σ = swapEquiv n m`).  The inverse direction is the
value-preserving map `z ↦ z ∘ σ⁻¹`. -/
theorem sp_reindex_swap_set {n m : ℕ} (Y : SemiPf ((n + 1) + m)) :
    (SemiPf.reindex (CoreStep.swapEquiv n m) Y).set
      = (fun z j => z ((CoreStep.swapEquiv n m).symm j)) '' Y.set := by
  rw [sp_reindex_set]
  ext y
  constructor
  · intro hy
    exact ⟨fun j => y ((CoreStep.swapEquiv n m) j), hy, by funext j; simp⟩
  · rintro ⟨z, hz, rfl⟩
    simpa using hz

/-- `π_n` (in the `(n, m+1)`-split) of the `σ⁻¹`-pullback of `z` is `basePr n m z`: `σ` fixes the
base coordinates `0, …, n-1`. -/
theorem projFirst_swap_comp {n m : ℕ} (z : Fin ((n + 1) + m) → ℝ) :
    projFirst n (m + 1) (fun j => z ((CoreStep.swapEquiv n m).symm j))
      = MainDesign.basePr n m z := by
  funext i
  refine congrArg z (Fin.ext ?_)
  show ((CoreStep.swapEquiv n m).symm (Fin.castAdd (m + 1) i)).val = i.val
  rw [show Fin.castAdd (m + 1) i = (⟨i.val, by omega⟩ : Fin (n + (m + 1))) from Fin.ext rfl]
  rw [CoreStep.swapEquiv_symm_base (⟨i.val, by omega⟩ : Fin ((n + 1) + m)) i.isLt]

/-- **The coordinate transfer for a family.**  Every family `X : Fin k → SemiPf ((n+1)+m)` can be
reindexed to a family `X' : Fin k → SemiPf (n+(m+1))` with the same chain lengths and degrees,
point set `(X' i).set = (z ↦ z ∘ σ⁻¹) '' (X i).set`, and — the property used in the
`CoreLT_succ` construction — the same `π_n`-image: `π_n((X' i).set) = basePr n m '' (X i).set`. -/
theorem reindex_family_base {n m k : ℕ} (X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)) :
    ∃ X' : Fin k → WilkiesDesign.E.SemiPf (n + (m + 1)),
      (∀ i, (X' i).r = (X i).r) ∧
      (∀ i, (X' i).deg = (X i).deg) ∧
      (∀ i, WilkiesDesign.E.SemiPf.set (X' i)
        = (fun z j => z ((Work.WilE7.CoreStep.swapEquiv n m).symm j)) '' (X i).set) ∧
      (∀ i, WilkiesDesign.E.projFirst n (m + 1) '' (WilkiesDesign.E.SemiPf.set (X' i))
        = Work.WilE7.MainDesign.basePr n m '' (X i).set) := by
  refine ⟨fun i => SemiPf.reindex (CoreStep.swapEquiv n m) (X i), ?_, ?_, ?_, ?_⟩
  · intro i; rfl
  · intro i; exact sp_reindex_deg (CoreStep.swapEquiv n m) (X i)
  · intro i; exact sp_reindex_swap_set (X i)
  · intro i
    rw [sp_reindex_swap_set (X i), Set.image_image]
    have hfun : (fun z : Fin ((n + 1) + m) → ℝ =>
        projFirst n (m + 1) (fun j => z ((CoreStep.swapEquiv n m).symm j)))
        = MainDesign.basePr n m := funext projFirst_swap_comp
    rw [hfun]

end Work.WilE7.coreLT_succ
