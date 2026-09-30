import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.fold_theta_coord
import Submission.Work.FoldInst.actX_image_Dvor
import Submission.Work.FoldInst.foldTheta_flip
import Submission.Work.FoldInst.Ksub_eq_wallSum
import Submission.Work.FoldInst.foldPsi_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FoldInst

/-! ### The reflection `reflCoords` fixes a chart value at a point where the flipped walls are tight

This is the analytic content of the "hagree" identity: on the walls of `r` that lie in `Δ` the
`Δ`-coordinates of the chart point `foldTheta i r y` vanish (`fold_theta_coord`), because the
corresponding slack is `0`; hence the sign reflection `reflCoords Δ` acts as the identity. -/

theorem reflCoords_eq_self (i : Fin 98) (r : Fin (foldCodim i) → Bool)
    {Δ : Finset (Fin (foldCodim i))} {y : E4} (hy : y ∈ HypModel.ball)
    (hΔ : ∀ t ∈ Δ, sideSlack (foldWalls i r t) y = 0) :
    reflCoords Δ (foldTheta i r y) = foldTheta i r y := by
  refine Work.Fold.e4_ext fun j => ?_
  rw [reflCoords_apply]
  by_cases hj : (j : ℕ) < foldCodim i
  · rw [dite_eq_left hj]
    by_cases hjm : (⟨j, hj⟩ : Fin (foldCodim i)) ∈ Δ
    · rw [ite_eq_left hjm]
      have hz : foldTheta i r y j = 0 := by
        have hcoord : Real.sqrt (1 - ‖y‖ ^ 2) * (foldTheta i r y) j =
            (if r (⟨j, hj⟩ : Fin (foldCodim i)) then -1 else 1) *
              sideSlack (foldWalls i r (⟨j, hj⟩ : Fin (foldCodim i))) y *
                (HypModel.mobiusKlein (foldNr i) (act (toG (foldKr i r)) y)) 3 := by
          have h := fold_theta_coord i r y hy (⟨j, hj⟩ : Fin (foldCodim i))
          rwa [show (⟨(⟨j, hj⟩ : Fin (foldCodim i)),
              by have := (⟨j, hj⟩ : Fin (foldCodim i)).isLt
                 have := foldCodim_le i; omega⟩ : Fin 4) = j from Fin.ext rfl] at h
        rw [hΔ (⟨j, hj⟩ : Fin (foldCodim i)) hjm] at hcoord
        simp only [mul_zero, zero_mul] at hcoord
        exact (mul_eq_zero.mp hcoord).resolve_left
          (ne_of_gt (Real.sqrt_pos_of_pos (by
            have hy1 : ‖y‖ < 1 := hy
            nlinarith [norm_nonneg y, hy1])))
      rw [hz, mul_zero]
    · rw [ite_eq_right hjm, one_mul]
  · rw [dite_eq_right hj]

/-- **The glued value `foldPsi i` is invariant under the identification relation `rel` on the
generic part** (the union of the Voronoi pieces).  The two-fold content: the representative
attached to `x` is unique (`foldPsi_eq`), and along an identification `x' = actX γ x` with
`γ ∈ Ksub x` the representative changes by a flip (`actX_image_Dvor`) under which the chart value is
fixed (`foldTheta_flip`, `reflCoords_eq_self`). -/
theorem foldPsi_hagree (i : Fin 98) {x x' : Xbar}
    (hx : x ∈ ⋃ r : Fin (foldCodim i) → Bool, Dvor i r) (h : rel x x') :
    foldPsi i x' = foldPsi i x := by
  classical
  obtain ⟨r, hr⟩ := by simpa using hx
  obtain ⟨γ, hγK, hγx⟩ := h
  obtain ⟨Δ, hΔ, hγΔ⟩ := (Ksub_eq_wallSum i hr γ).mp hγK
  -- `x'` lies in the Voronoi piece of the flipped representative.
  have hx' : x' ∈ Dvor i (flipSet r Δ) := by
    rw [← actX_image_Dvor i r Δ]
    exact ⟨x, hr, by rw [← hγΔ, hγx]⟩
  rw [foldPsi_eq i hx', foldPsi_eq i hr]
  have hsnd : x'.2.1 = act (wallSum i Δ).1 x.2.1 := by
    rw [← hγx, actX_snd, hγΔ]
  rw [hsnd, foldTheta_flip i r Δ x.2.1]
  exact reflCoords_eq_self i r (Dvor_subset_ball i r hr) hΔ

end Work.FoldInst
