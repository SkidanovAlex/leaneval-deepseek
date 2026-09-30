/-
# Continuity of the glued fold-chart value `foldPsi`

The glued value `foldPsi i : Xbar → E4` of the fold class `i` equals `foldTheta i r ∘ snd` on the
Voronoi piece `Dvor i r` (`foldPsi_eq`), and the pieces `Dvor i r` are *pairwise disjoint* and
*open* in `Xbar` (`Dvor_disjoint`, `isOpen_Dvor`).  Hence `foldPsi i` is continuous on their union:
each point of the union has an open neighbourhood on which `foldPsi i` is the continuous map
`x ↦ foldTheta i r x.2.1`, and `ContinuousOn.iUnion_of_isOpen` assembles the local statements.

The only global input is the continuity of the fold chart map `foldTheta i r` on the Klein ball
(so that it is continuous at every point of every piece), and this file proves it here: `foldTheta`
is the coordinate permutation `coordPerm i` (linear, so continuous) composed with the Klein action
`mobiusKlein (N_F · D_r)` of the *Lorentz* matrix `N_F · D_r` on the open unit ball.  For the latter
we prove the general fact that a Möbius action of a Lorentz matrix is continuous on the ball: near
the ball the Klein lift `hypOfKlein` is smooth, its image stays on the upper sheet (so the height
`P₄ − P₃` of the image is positive) and `uhsOfHyp` is continuous where the height is positive.
-/
import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.foldPsi_eq
import Submission.Work.FoldInst.foldTheta_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.FoldInst

open Set

/-! ### Continuity of the Möbius action of a Lorentz matrix on the Klein ball -/

/-- The open set of `ℝ⁵` on which the height `P 4 - P 3` is positive. -/
def HeightPos : Set HypModel.V5 := {P | 0 < P 4 - P 3}

theorem mem_HeightPos {P : HypModel.V5} : P ∈ HeightPos ↔ 0 < P 4 - P 3 := Iff.rfl

/-- **`uhsOfHyp` is smooth where the height is positive**: all four of its coordinates are
`Pᵢ · (P₄ − P₃)⁻¹` (or `(P₄ − P₃)⁻¹`). -/
theorem contDiffOn_uhsOfHyp_heightPos : ContDiffOn ℝ ⊤ HypModel.uhsOfHyp HeightPos := by
  have hsub : ContDiffOn ℝ ⊤ (fun P : HypModel.V5 => P 4 - P 3) HeightPos :=
    (((ContinuousLinearMap.proj (4 : Fin 5) : HypModel.V5 →L[ℝ] ℝ).contDiff).contDiffOn).sub
      (((ContinuousLinearMap.proj (3 : Fin 5) : HypModel.V5 →L[ℝ] ℝ).contDiff).contDiffOn)
  have h1 : ContDiffOn ℝ ⊤ (fun P : HypModel.V5 => (P 4 - P 3)⁻¹) HeightPos :=
    hsub.inv (fun P hP => ne_of_gt hP)
  rw [contDiffOn_piLp (p := 2) (E := fun _ : Fin 4 => ℝ)]
  intro i
  fin_cases i
  · show ContDiffOn ℝ ⊤ (fun P : HypModel.V5 => P 0 * (P 4 - P 3)⁻¹) HeightPos
    exact (((ContinuousLinearMap.proj (0 : Fin 5) : HypModel.V5 →L[ℝ] ℝ).contDiff).contDiffOn).mul h1
  · show ContDiffOn ℝ ⊤ (fun P : HypModel.V5 => P 1 * (P 4 - P 3)⁻¹) HeightPos
    exact (((ContinuousLinearMap.proj (1 : Fin 5) : HypModel.V5 →L[ℝ] ℝ).contDiff).contDiffOn).mul h1
  · show ContDiffOn ℝ ⊤ (fun P : HypModel.V5 => P 2 * (P 4 - P 3)⁻¹) HeightPos
    exact (((ContinuousLinearMap.proj (2 : Fin 5) : HypModel.V5 →L[ℝ] ℝ).contDiff).contDiffOn).mul h1
  · show ContDiffOn ℝ ⊤ (fun P : HypModel.V5 => (P 4 - P 3)⁻¹) HeightPos
    exact h1

theorem continuousOn_uhsOfHyp_heightPos : ContinuousOn HypModel.uhsOfHyp HeightPos :=
  contDiffOn_uhsOfHyp_heightPos.continuousOn

/-- `ray y = (y,1)` is continuous. -/
theorem continuous_ray : Continuous HypModel.ray := by
  refine continuous_pi fun j => ?_
  fin_cases j <;> simp [HypModel.ray]
  · exact PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0
  · exact PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 1
  · exact PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 2
  · exact PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 3
  · exact continuous_const

/-- **The Möbius action of a Lorentz matrix is continuous on the Klein ball.**
`mobiusKlein A y = uhsOfHyp (A *ᵥ hypOfKlein y)`: on the ball `hypOfKlein` is continuous
(`(√(1−‖y‖²))⁻¹ • (y,1)`, denominator nonvanishing), the linear map `A` is continuous, its image
stays on the upper sheet where the height `P₄ − P₃` is positive, and `uhsOfHyp` is continuous
there. -/
theorem continuousOn_mobiusKlein {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : HypModel.IsLorentzMat A) :
    ContinuousOn (HypModel.mobiusKlein A) HypModel.ball := by
  have hsq : ContinuousOn (fun y : E4 => Real.sqrt (1 - ‖y‖ ^ 2)) HypModel.ball :=
    Real.continuous_sqrt.comp_continuousOn
      (((continuous_const : Continuous fun _ : E4 => (1 : ℝ)).sub
        (continuous_norm.pow 2)).continuousOn)
  have hc : ContinuousOn (fun y : E4 => (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹) HypModel.ball :=
    hsq.inv₀ (fun y hy => ne_of_gt (Real.sqrt_pos.mpr (by
      have hy' : ‖y‖ < 1 := hy
      nlinarith [norm_nonneg y])))
  have hhyp : ContinuousOn HypModel.hypOfKlein HypModel.ball :=
    ContinuousOn.smul hc continuous_ray.continuousOn
  have hmap : ContinuousOn (fun y : E4 => A.mulVec (HypModel.hypOfKlein y)) HypModel.ball :=
    (HypModel.contDiff_mulVec A).continuous.comp_continuousOn hhyp
  have hmaps : MapsTo (fun y : E4 => A.mulVec (HypModel.hypOfKlein y)) HypModel.ball HeightPos :=
    fun y hy => HypModel.upperSheet_four_sub_three_pos
      (HypModel.isLorentzMat_mem_upperSheet hA (HypModel.hypOfKlein_mem_upperSheet hy))
  exact (continuousOn_uhsOfHyp_heightPos.comp hmap hmaps).congr (fun y _ => rfl)

/-! ### Continuity of the fold chart on the ball -/

/-- The coordinate permutation `coordPerm i` is a continuous linear reindexing of the coordinates
(by the *bijective* `foldTau i`). -/
theorem continuous_coordPerm (i : Fin 98) : Continuous (coordPerm i) := by
  have h : coordPerm i
      = fun y : E4 => WithLp.toLp 2 (fun j : Fin 4 => y (Function.invFun (foldTau i) j)) := by
    funext y
    ext j
    rw [coordPerm_apply]
  rw [h]
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp
    (continuous_pi fun j =>
      PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (Function.invFun (foldTau i) j))

/-- **The fold chart map is continuous on the Klein ball**: `foldTheta i r` is the continuous map
`coordPerm i` composed with the Klein action of the Lorentz matrix `N_F · D_r`. -/
theorem continuousOn_foldTheta (i : Fin 98) (r : Fin (foldCodim i) → Bool) :
    ContinuousOn (foldTheta i r) HypModel.ball := by
  have hmob := continuousOn_mobiusKlein (foldInst_foldNr_mul_foldDrR_isLorentz i r)
  exact ((continuous_coordPerm i).comp_continuousOn hmob).congr (fun y _ => rfl)

/-! ### The glued value is continuous on the union of the Voronoi pieces -/

/-- **The glued fold-chart value is continuous on the union of the Voronoi pieces.** On the open
piece `Dvor i r` the function `foldPsi i` agrees with `x ↦ foldTheta i r x.2.1`
(`foldPsi_eq`), which is continuous because a point of `Dvor i r` lies in the ball and `foldTheta`
is continuous on the ball; since the pieces are open, the local statements glue. -/
theorem foldPsi_continuousOn (i : Fin 98) :
    ContinuousOn (foldPsi i) (⋃ r : Fin (foldCodim i) → Bool, Dvor i r) := by
  refine ContinuousOn.iUnion_of_isOpen (fun r => ?_) (fun r => isOpen_Dvor i r)
  have hg : ContinuousOn (fun x : Xbar => x.2.1) (Dvor i r) :=
    ((continuous_subtype_val : Continuous (Subtype.val : Qbar → E4)).comp continuous_snd).continuousOn
  have hmaps : MapsTo (fun x : Xbar => x.2.1) (Dvor i r) HypModel.ball :=
    fun x hx => Qbar_subset_ball x.2.2
  have hcomp : ContinuousOn (fun x : Xbar => foldTheta i r x.2.1) (Dvor i r) :=
    (continuousOn_foldTheta i r).comp hg hmaps
  exact hcomp.congr (fun x hx => foldPsi_eq i hx)

end Work.FoldInst
