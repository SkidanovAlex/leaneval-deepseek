import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.seed_mem_polyRegion
import Submission.Work.ELTop.paramRay_disjoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

/-!
# `Work.ELTop.rayPt_midNear_misses_polyCurve`

The reference ray point `rayPt hN (midNear ps) t` at level `1 < t < R` does not lie on the
polygon `polyCurve ps R` of an admissible ray polygon `ps`.

The three pieces of `polyCurve ps R` are handled separately:

* a landing point `P.y` lies in the filled Julia set `K c`, where the potential vanishes, while
  the potential of the ray point at level `t > 1` is `log t > 0`;
* a ray piece `rayPiece hN P.a 0 R` is contained in the parameter ray `paramRay hN P.a`, and the
  reference angle `midNear ps` is not congruent to any angle of the polygon modulo `ℤ`, so
  `rayPt_midNear_notMem_paramRay` applies;
* a point of the equipotential of level `R` has potential `log R`, and `log R ≠ log t` because
  `t < R` and both are positive.

The same computation underlies `seed_mem_polyRegion`, where `t = √R`.
-/

theorem rayPt_midNear_misses_polyCurve {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R t : ℝ} (hR : 1 < R) (ht : 1 < t) (htR : t < R) :
    Work.EL.rayPt hN (Work.EL.midNear ps) t ∉ Work.EL.polyCurve ps R := by
  intro hmem
  rw [Work.EL.polyCurve, Set.mem_ofPred_eq] at hmem
  rcases hmem with ⟨P, hP, hPy | hPa | hPb⟩ | ⟨θ, hθ, hfar, hθeq⟩
  · -- a landing point of `ps`
    have hK : P.y ∈ Work.EL.K c := landsN_mem_K hN P.lands_a
    have hpy : Work.EL.pot hN P.y = 0 := Work.EL.pot_of_mem hN hK
    have hpx : Work.EL.pot hN (Work.EL.rayPt hN (Work.EL.midNear ps) t) = Real.log t :=
      Work.EL.pot_rayPt hN ht
    have hcongr : Work.EL.pot hN (Work.EL.rayPt hN (Work.EL.midNear ps) t) =
        Work.EL.pot hN P.y := by
      rw [hPy]
    exact absurd ((hpx.symm.trans hcongr).trans hpy) (Real.log_pos ht).ne'
  · -- the ray piece at the angle `P.a`
    exact rayPt_midNear_notMem_paramRay hN ps hA
      (List.mem_flatMap.mpr ⟨P, hP, by simp⟩) ht
      (Work.Top.NakaneData.rayPiece_subset_paramRay hPa)
  · -- the ray piece at the angle `P.b`
    exact rayPt_midNear_notMem_paramRay hN ps hA
      (List.mem_flatMap.mpr ⟨P, hP, by simp⟩) ht
      (Work.Top.NakaneData.rayPiece_subset_paramRay hPb)
  · -- a point of the equipotential of level `R`
    have hpx : Work.EL.pot hN (Work.EL.rayPt hN (Work.EL.midNear ps) t) = Real.log t :=
      Work.EL.pot_rayPt hN ht
    have hpθ : Work.EL.pot hN (Work.EL.rayPt hN θ R) = Real.log R := Work.EL.pot_rayPt hN hR
    have hlog : Real.log t = Real.log R :=
      (hpx.symm.trans (congrArg (Work.EL.pot hN) hθeq)).trans hpθ
    have h1 : (0 : ℝ) < t := by linarith
    have h2 : (0 : ℝ) < R := by linarith
    have hRt : t = R := Real.log_injOn_pos h1 h2 hlog
    linarith

end Work.ELTop
