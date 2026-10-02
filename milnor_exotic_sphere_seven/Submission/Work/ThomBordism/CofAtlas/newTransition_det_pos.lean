import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Structure
import Submission.Work.ThomBordism.CofAtlas.newIsManifold
import Submission.Work.ThomBordism.CofAtlas.det_newTransition
import Submission.Work.ThomBordism.CofAtlas.sign_lvlTransition
import Submission.Work.ThomBordism.CofAtlas.sgnConst
import Submission.Work.ThomBordism.CofAtlas.tauConst
import Submission.Work.ThomBordism.CofAtlas.newBoundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The corrected atlas is positive

`Work.ThomBordism.CofAtlas.newTransition_det_pos`: the transition determinants of the corrected
charted-space structure `newChartedSpace D` on the coframed level set are *positive*.  This is the
last ingredient of `Work.ThomBordism.levelSet_positiveAtlas_of_coframing`: together with
`newIsManifold` (smoothness) and `newBoundary` (the boundary) it gives the positive atlas.

The proof combines

* `det_newTransition` — the determinant of the corrected transition is
  `flipSign x · flipSign y · det (d transAux)`;
* `sign_lvlTransition` — the sign of `det (d transAux)` is `sgn x q · sgn y q · tau x q · tau y q`;
* `sgnConst`, `tauConst` — `sgn` and `tau` are constant on the connected source `src x`, so the
  value at `q` is the value at the centre `x`, and the correction `flipSign x = sgn x x · tau x x`
  cancels the product.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric
open Work.PTGeometric.Lvl

namespace Work.ThomBordism.CofAtlas

noncomputable section

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

theorem sign_coe (s : SignType) : SignType.sign ((s : ℝ)) = s := by
  cases s <;> simp

/-- **The transition determinants of the corrected atlas are positive.** -/
theorem newTransition_det_pos (D : Cof k n M) :
    letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre := newChartedSpace D
    ∀ (x y : D.S.Pre), x ∉ (𝓡∂ 9).boundary D.S.Pre → y ∉ (𝓡∂ 9).boundary D.S.Pre →
      ∀ z ∈ (extChartAt (𝓡∂ 9) x).target ∩
          (extChartAt (𝓡∂ 9) x).symm ⁻¹' (extChartAt (𝓡∂ 9) y).source,
        z 0 > 0 →
        0 < LinearMap.det (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 9) =>
          (extChartAt (𝓡∂ 9) y) ((extChartAt (𝓡∂ 9) x).symm w)) z).toLinearMap := by
  letI : ChartedSpace (EuclideanHalfSpace 9) D.S.Pre := newChartedSpace D
  intro x y hx hy z hz hzpos
  -- the ambient boundary memberships
  have hxi : (x : M) ∉ (𝓡∂ (NN k)).boundary M := fun hb => hx (by rw [newBoundary D]; exact hb)
  have hyi : (y : M) ∉ (𝓡∂ (NN k)).boundary M := fun hb => hy (by rw [newBoundary D]; exact hb)
  -- the point `p` of the level set with `z = (extChartAt x) p`
  set p : D.S.Pre := (extChartAt (𝓡∂ 9) x).symm z with hp
  have hsrcx : (extChartAt (𝓡∂ 9) x).source = D.src x := by
    show ((D.newChart x).extend (𝓡∂ 9)).source = D.src x
    rw [OpenPartialHomeomorph.extend_source, newChart_source]
  have hsourcy : (extChartAt (𝓡∂ 9) y).source = D.src y := by
    show ((D.newChart y).extend (𝓡∂ 9)).source = D.src y
    rw [OpenPartialHomeomorph.extend_source, newChart_source]
  have hpx : p ∈ D.src x := by
    rw [← hsrcx]
    exact PartialEquiv.map_target _ hz.1
  have hpy : p ∈ D.src y := by
    rw [← hsourcy]
    rw [hp]
    exact hz.2
  -- `z` is the image of `p` under the corrected chart at `x`
  have hz1 : (extChartAt (𝓡∂ 9) x) p = z := by
    rw [hp]
    exact PartialEquiv.right_inv _ hz.1
  have hz2 : (extChartAt (𝓡∂ 9) x) p = reflectLin D x (D.lvlExt x p) :=
    newChart_extend_apply D x p
  have hzeq : z = reflectLin D x (D.lvlExt x p) := hz1.symm.trans hz2
  have hpos : 0 < (D.lvlExt x p) 0 := by
    have h := congrArg (fun w : EuclideanSpace ℝ (Fin 9) => w 0) hzeq
    rw [reflectLin_coord_zero D x (D.lvlExt x p)] at h
    rw [← h]
    exact hzpos
  -- the non-vanishing of the correction signs
  have hsgnx : D.sgn x (x : M) ≠ 0 := (sgnConst D x hxi).2 x (D.mem_src_self x)
  have htauxx : D.tau x (x : M) ≠ 0 := (tauConst D x hxi).2 x (D.mem_src_self x)
  have hsgny : D.sgn y (y : M) ≠ 0 := (sgnConst D y hyi).2 y (D.mem_src_self y)
  have htauyy : D.tau y (y : M) ≠ 0 := (tauConst D y hyi).2 y (D.mem_src_self y)
  have hnex : D.flipSign x ≠ 0 := by
    rw [Cof.flipSign]; exact mul_ne_zero hsgnx htauxx
  have hney : D.flipSign y ≠ 0 := by
    rw [Cof.flipSign]; exact mul_ne_zero hsgny htauyy
  -- the two inputs
  have hdet := det_newTransition D x y hpx hpy hxi hyi hnex hney
  have hta := sign_lvlTransition D x y hpx hpy hxi hyi
  have e_px : D.sgn x (p : M) = D.sgn x (x : M) := (sgnConst D x hxi).1 p hpx
  have e_py : D.sgn y (p : M) = D.sgn y (y : M) := (sgnConst D y hyi).1 p hpy
  have e_tx : D.tau x (p : M) = D.tau x (x : M) := (tauConst D x hxi).1 p hpx
  have e_ty : D.tau y (p : M) = D.tau y (y : M) := (tauConst D y hyi).1 p hpy
  -- the sign of the transition determinant
  have hsign : SignType.sign (LinearMap.det (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 9) =>
      (extChartAt (𝓡∂ 9) y) ((extChartAt (𝓡∂ 9) x).symm w)) z).toLinearMap) = 1 := by
    rw [hzeq, hdet]
    simp only [sign_mul]
    rw [sign_coe, sign_coe, hta, e_px, e_py, e_tx, e_ty]
    have h1 : D.flipSign x = D.sgn x (x : M) * D.tau x (x : M) := rfl
    have h2 : D.flipSign y = D.sgn y (y : M) * D.tau y (y : M) := rfl
    rw [h1, h2]
    have ha : D.sgn x (x : M) * D.sgn x (x : M) = 1 :=
      mul_self_eq_one_of_ne_zero _ hsgnx
    have hb : D.tau x (x : M) * D.tau x (x : M) = 1 :=
      mul_self_eq_one_of_ne_zero _ htauxx
    have hc : D.sgn y (y : M) * D.sgn y (y : M) = 1 :=
      mul_self_eq_one_of_ne_zero _ hsgny
    have hd : D.tau y (y : M) * D.tau y (y : M) = 1 :=
      mul_self_eq_one_of_ne_zero _ htauyy
    rw [show (D.sgn x (x : M) * D.tau x (x : M)) * (D.sgn y (y : M) * D.tau y (y : M))
          * (D.sgn x (x : M) * D.sgn y (y : M) * D.tau x (x : M) * D.tau y (y : M))
        = (D.sgn x (x : M) * D.sgn x (x : M)) * (D.tau x (x : M) * D.tau x (x : M))
          * (D.sgn y (y : M) * D.sgn y (y : M)) * (D.tau y (y : M) * D.tau y (y : M))
        from by ac_rfl]
    rw [ha, hb, hc, hd]
    simp
  exact sign_eq_one_iff.mp hsign

end

end Work.ThomBordism.CofAtlas
