import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.Lorentz
import Submission.Work.HypModel.dHypOfUHS_comp_dUhsOfHyp
import Submission.Work.HypModel.dotProduct_pos_of_upperSheet
import Submission.Work.HypModel.fderiv_mobius_apply
import Submission.Work.HypModel.four_pos_of_lorentz_pair_neg
import Submission.Work.HypModel.hasFDerivAt_hypOfUHS
import Submission.Work.HypModel.hasFDerivAt_uhsOfHyp
import Submission.Work.HypModel.hemisphere_klein_affine_explicit
import Submission.Work.HypModel.hypOfKlein_bijOn
import Submission.Work.HypModel.hypOfKlein_blockLast
import Submission.Work.HypModel.hypOfKlein_diagonal
import Submission.Work.HypModel.hypOfKlein_injOn
import Submission.Work.HypModel.hypOfKlein_kleinOfHyp
import Submission.Work.HypModel.hypOfKlein_mem_upperSheet
import Submission.Work.HypModel.hypOfKlein_segment_pos_combo
import Submission.Work.HypModel.hypOfUHS_bijOn
import Submission.Work.HypModel.hypOfUHS_four_pos
import Submission.Work.HypModel.hypOfUHS_injOn
import Submission.Work.HypModel.hypOfUHS_uhsOfHyp
import Submission.Work.HypModel.isLorentzMat_blockLast
import Submission.Work.HypModel.isLorentzMat_lorentzReflection
import Submission.Work.HypModel.isLorentzMat_uhsRotation
import Submission.Work.HypModel.isLorentzMat_uhsTranslation
import Submission.Work.HypModel.kleinOfHyp_hypOfKlein
import Submission.Work.HypModel.kleinOfHyp_mem_ball
import Submission.Work.HypModel.lorentzReflection_mulVec
import Submission.Work.HypModel.lorentz_dHypOfUHS
import Submission.Work.HypModel.lorentz_hypOfKlein
import Submission.Work.HypModel.lorentz_hypOfUHS_self
import Submission.Work.HypModel.lorentz_neg_of_upperSheet
import Submission.Work.HypModel.mobiusKlein_isometry
import Submission.Work.HypModel.mobiusKlein_mem
import Submission.Work.HypModel.mobiusKlein_mul
import Submission.Work.HypModel.mobius_contDiffOn
import Submission.Work.HypModel.mobius_height
import Submission.Work.HypModel.mobius_isometry
import Submission.Work.HypModel.mobius_mul
import Submission.Work.HypModel.mobius_one
import Submission.Work.HypModel.mobius_uhsRotation
import Submission.Work.HypModel.mobius_uhsTranslation
import Submission.Work.HypModel.mobius_vertical
import Submission.Work.HypModel.polarToCartesian_isometry
import Submission.Work.HypModel.polarToUHS_isometry
import Submission.Work.HypModel.ray_affine_combo
import Submission.Work.HypModel.reflection_vertical
import Submission.Work.HypModel.tangent_hypOfUHS
import Submission.Work.HypModel.uhsOfHyp_hypOfKlein
import Submission.Work.HypModel.uhsOfHyp_hypOfUHS
import Submission.Work.HypModel.uhsOfHyp_infty
import Submission.Work.HypModel.uhsOfHyp_three_pos
import Submission.Work.HypModel.uhsTranslation_mul
import Submission.Work.HypModel.uhsTranslation_mulVec_infty
import Submission.Work.HypModel.uhs_pullback

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The hyperbolic model chapter: assembled interface

`import Submission.Work.HypModel.Main` gives the whole chapter: the Lorentz form on `ℝ⁵`, the
Klein model (`hypOfKlein : ball → upperSheet`), the upper half space model
(`hypOfUHS`, `uhsOfHyp`, `uhsMetric`), Möbius transformations of the Lorentz group
(`mobius`, `mobiusKlein`) with `mobius_mul`, `mobius_one`, `mobius_contDiffOn`,
`mobius_isometry` and `mobiusKlein_isometry`, the horospherical translations `uhsTranslation`
(`mobius_uhsTranslation`), the rotations `uhsRotation` (`mobius_uhsRotation`), the vertical
reflections `lorentzReflection` (`reflection_vertical`) and the general structure of a Lorentz
matrix fixing `∞` (`mobius_vertical`, `mobius_height`), and the polar ↔ upper-half-space comparison
`polarToUHS`/`warpedMetric` with `polarToUHS_isometry`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-- **The vertical projection of a truncation hemisphere is affine in the Klein coordinates.**
Let `w ∈ E4` be an ideal vertex (`‖w‖ = 1`) and let `δ ≠ 0`.  On the affine hyperplane
`{y : ⟪w,y⟫ = 1 − δ}` of the Klein ball (a totally geodesic hemisphere whose ideal boundary passes
through `w`), the upper half space position `uhsPositionAt w (hypOfKlein y)` — the position of the
hemisphere point in the upper half space chart centred at `w` — is *affine* in `y`:
`uhsPositionAt w (hypOfKlein y) = δ⁻¹ • (y − (1−δ) • w)`. -/
theorem hemisphere_klein_affine (w : E4) (hw : ‖w‖ = 1) {δ : ℝ} (hδ : δ ≠ 0) :
    ∃ (L : E4 →ₗ[ℝ] E4) (c : E4), ∀ y : E4, y ∈ ball → euclid w y = 1 - δ →
      uhsPositionAt w (hypOfKlein y) = L y + c := by
  refine ⟨δ⁻¹ • (LinearMap.id : E4 →ₗ[ℝ] E4), -((δ⁻¹ * (1 - δ))) • w, ?_⟩
  intro y hyb hy
  rw [hemisphere_klein_affine_explicit w hw hδ hyb hy]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  module

/-- **The action of `diag(O,1)` on the Klein model is linear in the Klein coordinates.**  For an
orthogonal `O : Matrix (Fin 4) (Fin 4) ℝ` the Möbius transformation of `blockLast O` sends the
Klein point `y` to the upper half space coordinates of the Klein point `rot4 O y`.  This makes
formal the §1 statement that the symmetry `k = diag(±1,±1,±1,±1,1)` of the 24-cell is *linear in
Klein coordinates*. -/
theorem mobiusKlein_blockLast {O : Matrix (Fin 4) (Fin 4) ℝ} (hO : O.transpose * O = 1) (y : E4) :
    mobiusKlein (blockLast O) y = uhsOfHyp (hypOfKlein (rot4 O y)) := by
  rw [mobiusKlein, hypOfKlein_blockLast hO]

/-- The Klein ball with the Klein metric is isometric to the upper half space model: the chart
`kleinToUHS = mobiusKlein 1` is an isometry. -/
theorem kleintoUHS_isometry {y : E4} (hy : y ∈ ball) (v w : E4) :
    uhsMetric (mobiusKlein 1 y) (fderiv ℝ (mobiusKlein 1) y v) (fderiv ℝ (mobiusKlein 1) y w) =
      kleinMetric y v w :=
  mobiusKlein_isometry IsLorentzMat_one hy v w

/-- The derivative of the Möbius transformation, in the `dHypOfUHS`/`dUhsOfHyp` form (an immediate
consequence of `fderiv_mobius_apply`). -/
theorem fderiv_mobius {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) {q : E4} (hq : 0 < q 3) :
    fderiv ℝ (mobius A) q =
      (dUhsOfHyp (A.mulVec (hypOfUHS q))).comp
        ((Matrix.toLin' A).toContinuousLinearMap.comp (dHypOfUHS q)) := by
  ext v
  rw [fderiv_mobius_apply hA hq]
  simp [ContinuousLinearMap.comp_apply, Matrix.toLin'_apply]


/-- **Straight line segments in the Klein model are hyperbolic geodesic arcs.**  The Klein lift of a
convex combination of two points of the ball is a *nonnegative* linear combination of the lifts of
the endpoints, i.e. it lies in the totally geodesic plane spanned by them. -/
theorem hypOfKlein_segment_mem_span {y z : E4} (hy : y ∈ ball) (hz : z ∈ ball) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    hypOfKlein ((1 - t) • y + t • z) ∈ Submodule.span ℝ ({hypOfKlein y, hypOfKlein z} : Set V5) := by
  obtain ⟨a, b, _ha, _hb, h⟩ := hypOfKlein_segment_pos_combo hy hz ht0 ht1
  rw [h]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end Work.HypModel
