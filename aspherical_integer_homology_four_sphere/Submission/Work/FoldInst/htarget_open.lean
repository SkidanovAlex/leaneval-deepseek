/-
# `htarget_open`: the target of the root fold chart is relatively open in the positive orthant

For a fold class `i : Fin 98` of codimension `c = foldCodim i`, the *root* sign index is
`r₀ = fun _ => false`.  This file proves the `htarget_open` field of the fold data of the class
`i`: the image of the root Voronoi piece `Dvor i r₀ ⊆ Xbar` under the glued chart value `foldPsi i`
is *relatively open* in the positive orthant `posOrthant c` of the chart model `E4`.

The image is computed in three steps.

* On its own piece the glued value is the chart map (`foldPsi_eq`), so
  `foldPsi i '' Dvor i r₀ = foldTheta i r₀ '' (VoronoiOpen i r₀ ∩ Q̄)`.
* The chart map of an *open* subset of the Klein ball is open (`isOpen_foldTheta_image`), so
  `O := foldTheta i r₀ '' (VoronoiOpen i r₀ ∩ ball)` is an open subset of `E4`.  This is where the
  Möbius action enters: `foldTheta i r = coordPerm i ∘ mobiusKlein (N_F D_r)`, and `mobiusKlein` of
  a Lorentz matrix is a homeomorphism of the open unit ball onto the upper half space.
* The coordinate identity `fold_theta_coord` identifies the two sides of
  `O ∩ posOrthant c = foldTheta i r₀ '' (VoronoiOpen i r₀ ∩ Q̄)`.  For the root index the sign in
  that identity is `+1`, so a chart value at a point of `Q̄` has nonnegative coordinates
  (`fold_theta_orthant`), while conversely a point of the ball whose chart value lies in the
  orthant has all of its *wall* slacks `≥ 0` (`Qbar_of_mem_VoronoiOpen_root`); the Voronoi
  conditions supply the remaining constraints of `Q̄` with a strict sign.

The relative openness is then read off from the open set `O`: `IsRelOpen (posOrthant c) S` means
`S = V ∩ posOrthant c` for an open `V`, and here `V = O`.
-/
import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.foldPsi_eq
import Submission.Work.FoldInst.isOpen_foldTheta_image
import Submission.Work.FoldInst.Qbar_of_mem_VoronoiOpen_root
import Submission.Work.FoldInst.fold_theta_orthant

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

theorem htarget_open (i : Fin 98) :
    Work.Fold.IsRelOpen (Work.Fold.posOrthant (foldCodim i))
      (foldPsi i '' Dvor i (fun _ => false)) := by
  -- the root sign index is `false` everywhere, so its orthant is the *positive* orthant
  have hsign : Work.Fold.signVecNeg (fun _ : Fin (foldCodim i) => false)
      = Work.Fold.oneSign (foldCodim i) := by
    funext t
    simp [Work.Fold.signVecNeg, Work.Fold.oneSign]
  -- (1) the chart value of the root piece of `Q̄` lies in the positive orthant
  have horth : ∀ {y : E4}, y ∈ Qbar →
      foldTheta i (fun _ : Fin (foldCodim i) => false) y ∈ Work.Fold.posOrthant (foldCodim i) := by
    intro y hy
    have hx : (foldCr i (fun _ : Fin (foldCodim i) => false), (⟨y, hy⟩ : Qbar)) ∈
        Clift i (fun _ : Fin (foldCodim i) => false) :=
      ⟨rfl, fun S _ => hy.1 S⟩
    have h := fold_theta_orthant i (fun _ : Fin (foldCodim i) => false) _ hx
    simpa only [Work.Fold.posOrthant, hsign] using h
  -- (2) the glued value on the root piece is the chart map of `VoronoiOpen ∩ Q̄`
  have himg : foldPsi i '' Dvor i (fun _ : Fin (foldCodim i) => false)
      = foldTheta i (fun _ : Fin (foldCodim i) => false) ''
          (VoronoiOpen i (fun _ : Fin (foldCodim i) => false) ∩ Qbar) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2.1, ⟨(mem_Dvor.mp hx).2, x.2.2⟩, (foldPsi_eq i hx).symm⟩
    · rintro ⟨y, ⟨hyV, hyQ⟩, rfl⟩
      exact ⟨(foldCr i (fun _ : Fin (foldCodim i) => false), (⟨y, hyQ⟩ : Qbar)),
        mem_Dvor.mpr ⟨rfl, hyV⟩, foldPsi_eq i (mem_Dvor.mpr ⟨rfl, hyV⟩)⟩
  -- (3) the chart image of the open Voronoi region (intersected with the ball) is open
  have hVopen : IsOpen (VoronoiOpen i (fun _ : Fin (foldCodim i) => false) ∩ HypModel.ball) :=
    (isOpen_VoronoiOpen i _).inter
      (isOpen_lt continuous_norm continuous_const : IsOpen HypModel.ball)
  refine ⟨foldTheta i (fun _ : Fin (foldCodim i) => false) ''
      (VoronoiOpen i (fun _ : Fin (foldCodim i) => false) ∩ HypModel.ball),
    isOpen_foldTheta_image i _ hVopen (fun y hy => hy.2), ?_⟩
  rw [himg]
  refine Set.Subset.antisymm ?_ ?_
  · -- a point of `VoronoiOpen ∩ Q̄` has chart value in the orthant and lies in the ball
    rintro z ⟨y, ⟨hyV, hyQ⟩, rfl⟩
    exact ⟨⟨y, ⟨hyV, Qbar_subset_ball hyQ⟩, rfl⟩, horth hyQ⟩
  · -- a point of the ball whose chart value is in the orthant lies in `Q̄`
    rintro z ⟨hz1, hz2⟩
    obtain ⟨y, ⟨hyV, hyb⟩, rfl⟩ := hz1
    exact ⟨y, ⟨hyV, Qbar_of_mem_VoronoiOpen_root i hyV hyb hz2⟩, rfl⟩

end Work.FoldInst
