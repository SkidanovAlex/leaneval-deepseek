import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.actX_image_Dvor
import Submission.Work.FoldInst.foldTheta_flip
import Submission.Work.FoldInst.foldPsi_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

theorem foldPsi_image_reflVec (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    foldPsi i '' Dvor i r =
      Work.Fold.reflVec (Work.Fold.signVecNeg r) '' (foldPsi i '' Dvor i (fun _ => false)) := by
  classical
  -- The set of walls at which `r` differs from the base sign index `fun _ => false`.
  set Δ : Finset (Fin (foldCodim i)) := {t | r t = true} with hΔ
  -- Flipping the base index at `Δ` recovers `r`.
  have hflip : flipSet (fun _ : Fin (foldCodim i) => false) Δ = r := by
    funext t
    simp only [hΔ, flipSet, Bool.false_xor, Bool.decide_eq_true, Finset.mem_filter, Finset.mem_univ,
      true_and]
  -- The coordinate reflection of `signVecNeg r` is exactly the reflection at `Δ`.
  have hrefl : Work.Fold.reflVec (Work.Fold.signVecNeg r) = reflCoords Δ := by
    rw [hΔ]; exact reflVec_signVecNeg r
  -- The identification `wallSum i Δ` carries the base Voronoi piece onto the piece of `r`.
  have hDvor : Dvor i r = actX (wallSum i Δ) '' Dvor i (fun _ => false) := by
    rw [← hflip]
    exact (actX_image_Dvor i (fun _ => false) Δ).symm
  rw [hDvor, hrefl, Set.image_image, Set.image_image]
  apply Set.image_congr
  intro x hx
  -- On the base piece the glued chart value transforms by the coordinate reflection `Δ`.
  have hx' : actX (wallSum i Δ) x ∈ Dvor i (flipSet (fun _ => false) Δ) := by
    rw [← actX_image_Dvor i (fun _ => false) Δ]
    exact ⟨x, hx, rfl⟩
  rw [foldPsi_eq i hx', foldPsi_eq i hx, actX_snd]
  exact foldTheta_flip i (fun _ => false) Δ x.2.1

end Work.FoldInst
