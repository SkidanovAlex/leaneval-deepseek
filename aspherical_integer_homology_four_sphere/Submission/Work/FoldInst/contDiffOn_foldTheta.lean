/-
# Smoothness of the fold chart map `foldTheta` on the Klein ball

The chart map of the fold class `i : Fin 98` and the sign index `r` is

  `foldTheta i r y = coordPerm i (mobiusKlein (N_F · D_r) y)`

(`FoldPiece.lean`): the coordinate permutation `coordPerm i` reindexes the model coordinates of
the Möbius image of the Klein point `y` under the developing matrix `N_F · D_r`.

This file upgrades the continuity of `foldTheta i r` on the Klein ball
(`foldPsi_continuousOn.lean`) to **`C^∞`**, which is what the chart-smoothness argument of the
FOLD area of the blueprint consumes.  Nothing new happens mathematically: each of the three
factors is smooth, and the whole point is that the *image* of the Klein lift stays on the upper
sheet, where the height `P₄ − P₃` of the upper half space chart does not vanish.

* `contDiffOn_hypOfKlein` — the Klein lift `y ↦ (y,1)/√(1−‖y‖²)` is `C^∞` on the open ball: its
  coordinates are `(√(1−‖y‖²))⁻¹ · yⱼ` and `(√(1−‖y‖²))⁻¹`, and `1 − ‖y‖² > 0` there;
* `contDiffOn_mobiusKlein` — for a Lorentz matrix `A`, `mobiusKlein A = uhsOfHyp ∘ (A ·) ∘ hypOfKlein`
  is `C^∞` on the ball: the linear map `A ·` is `C^∞`, it carries the ball into the open set where
  the height is positive (`isLorentzMat_mem_upperSheet`), and `uhsOfHyp` is `C^∞` there
  (`contDiffOn_uhsOfHyp_heightPos`);
* `contDiff_coordPerm` — the coordinate permutation `coordPerm i` is a linear reindexing.

Since all of `ContDiffOn.sqrt`, `ContDiffOn.inv`, `ContDiffOn.smul`, `ContDiffOn.comp` and the
workspace lemmas `contDiff_mulVec`, `contDiffOn_uhsOfHyp_heightPos` are available at every order
`n : WithTop ℕ∞`, the composite is proved `C^∞` in the sense of the *top* of `WithTop ℕ∞`
(analytic order); the requested statement, whose order is `↑(⊤ : ℕ∞)`, follows by monotonicity
`ContDiffOn.of_le le_top`.
-/
import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.CertFlip
import Submission.Work.FoldInst.foldTheta_injOn
import Submission.Work.FoldInst.foldPsi_continuousOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.FoldInst

open Set Matrix

/-! ### The Klein lift is smooth on the ball -/

/-- **`hypOfKlein` is `C^∞` on the open unit ball.**  Its coordinates are
`(√(1−‖y‖²))⁻¹ · yⱼ` (`j = 0,1,2,3`) and `(√(1−‖y‖²))⁻¹`, and `1 − ‖y‖² > 0` on the ball, so both
the square root and its inverse are smooth there. -/
theorem contDiffOn_hypOfKlein : ContDiffOn ℝ ⊤ HypModel.hypOfKlein HypModel.ball := by
  have hpos : ∀ y ∈ HypModel.ball, 0 < 1 - ‖y‖ ^ 2 := by
    intro y hy
    have hy' : ‖y‖ < 1 := hy
    nlinarith [norm_nonneg y]
  have hsq : ContDiffOn ℝ ⊤ (fun y : E4 => Real.sqrt (1 - ‖y‖ ^ 2)) HypModel.ball :=
    ((contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffOn).sqrt
      (fun y hy => ne_of_gt (hpos y hy))
  have hc : ContDiffOn ℝ ⊤ (fun y : E4 => (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹) HypModel.ball :=
    hsq.inv (fun y hy => ne_of_gt (Real.sqrt_pos.mpr (hpos y hy)))
  have hray : ContDiffOn ℝ ⊤ HypModel.ray HypModel.ball := by
    rw [contDiffOn_pi]
    intro j
    fin_cases j
    · exact (EuclideanSpace.proj (0 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffOn
    · exact (EuclideanSpace.proj (1 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffOn
    · exact (EuclideanSpace.proj (2 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffOn
    · exact (EuclideanSpace.proj (3 : Fin 4) : E4 →L[ℝ] ℝ).contDiff.contDiffOn
    · exact contDiff_const.contDiffOn
  exact (ContDiffOn.smul hc hray).congr (f₁ := HypModel.hypOfKlein) (fun _ _ => rfl)

/-! ### The Klein action of a Lorentz matrix is smooth on the ball -/

/-- **The Möbius action `mobiusKlein A` of a Lorentz matrix is `C^∞` on the Klein ball.**
`mobiusKlein A y = uhsOfHyp (A *ᵥ hypOfKlein y)`: the Klein lift is smooth there
(`contDiffOn_hypOfKlein`), the linear map `A *ᵥ ·` is smooth, and it carries the ball into the open
set where the height `P₄ − P₃` is positive — the image of `hypOfKlein y` on the upper sheet under
the Lorentz matrix `A` is again on the upper sheet — where `uhsOfHyp` is smooth. -/
theorem contDiffOn_mobiusKlein {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : HypModel.IsLorentzMat A) :
    ContDiffOn ℝ ⊤ (HypModel.mobiusKlein A) HypModel.ball := by
  have hmap : ContDiffOn ℝ ⊤ (fun y : E4 => A *ᵥ HypModel.hypOfKlein y) HypModel.ball :=
    (HypModel.contDiff_mulVec A).comp_contDiffOn contDiffOn_hypOfKlein
  have hmaps : MapsTo (fun y : E4 => A *ᵥ HypModel.hypOfKlein y) HypModel.ball HeightPos :=
    fun y hy => HypModel.upperSheet_four_sub_three_pos
      (HypModel.isLorentzMat_mem_upperSheet hA (HypModel.hypOfKlein_mem_upperSheet hy))
  exact (contDiffOn_uhsOfHyp_heightPos.comp hmap hmaps).congr (fun _ _ => rfl)

/-! ### The coordinate permutation -/

/-- The coordinate permutation `coordPerm i` is a continuous linear reindexing of the coordinates
of `E4` (by the *bijective* `foldTau i`), hence `C^∞`. -/
theorem contDiff_coordPerm (i : Fin 98) : ContDiff ℝ ⊤ (coordPerm i) := by
  have h : coordPerm i = fun y : E4 =>
      WithLp.toLp 2 (fun j : Fin 4 => y (Function.invFun (foldTau i) j)) := by
    funext y
    ext j
    rw [coordPerm_apply]
  rw [h]
  refine PiLp.contDiff_toLp.comp ?_
  rw [contDiff_pi]
  intro j
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) (Function.invFun (foldTau i) j)).contDiff

/-! ### Smoothness of the fold chart -/

/-- **The fold chart map is `C^∞` on the Klein ball**: `foldTheta i r` is the coordinate
permutation `coordPerm i` (linear, so smooth) composed with the Klein action of the Lorentz matrix
`N_F · D_r` (`foldInst_foldNr_mul_foldDrR_isLorentz`), which is smooth on the ball
(`contDiffOn_mobiusKlein`). -/
theorem contDiffOn_foldTheta (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    ContDiffOn ℝ (⊤ : ℕ∞) (foldTheta i r) HypModel.ball := by
  have hmob := contDiffOn_mobiusKlein (foldInst_foldNr_mul_foldDrR_isLorentz i r)
  have h : ContDiffOn ℝ ⊤ (foldTheta i r) HypModel.ball :=
    ((contDiff_coordPerm i).contDiffOn.comp hmob (fun _ _ => Set.mem_univ _)).congr
      (fun _ _ => rfl)
  exact h.of_le le_top

end Work.FoldInst
