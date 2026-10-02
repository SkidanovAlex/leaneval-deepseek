import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.seed_mem_polyRegion
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.Top.continuousOn_rayPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

namespace Work.ELTop

/-!
# The inner part of the reference ray lies in the region of a ray polygon

In the dynamical plane of `T_c`, let `ps` be an admissible list of co-landing pairs and `R > 1`.
The region `Work.EL.polyRegion ps R` is the connected component of the complement of the ray
polygon `polyCurve ps R` containing the reference ray point of angle `midNear ps` at level
`√R`.  The reference angle `midNear ps` lies in the *near* arc following the first pair of `ps`,
so the piece of the ray of that angle between the levels `1` and `R` runs inside the region:

* it meets no ray of the polygon, because the ray of `midNear ps` is disjoint from the rays of
  the `2m` angles of the polygon (`Work.ELTop.rayPt_midNear_notMem_paramRay`);
* it does not meet the equipotential part of the polygon at level `R`, since its levels are `< R`
  and the potential of a ray point is the logarithm of its level;
* it does not meet the landing points, which lie in `K c` while the ray points do not.

Since that piece is the image of the interval `(1, R)` under the continuous injection
`s ↦ rayPt hN (midNear ps) s`, it is preconnected, and both `rayPt hN (midNear ps) t`
(for `1 < t < R`) and the base point `rayPt hN (midNear ps) (√R)` lie on it.  Hence the former
lies in the component of the latter.
-/

variable {c : ℂ} {φ : ℂ → ℂ}

/-- The piece of the ray of angle `θ` between the levels `1` and `R` is preconnected: it is the
image of the interval `(1, R)` under the continuous (on `(1, ∞)`) level parametrization. -/
theorem isPreconnected_rayPt_image_Ioo (hN : Work.EL.DynB c φ) (θ R : ℝ) :
    IsPreconnected ((fun s : ℝ => Work.EL.rayPt hN θ s) '' Set.Ioo 1 R) :=
  isPreconnected_Ioo.image _ ((Work.Top.continuousOn_rayPt hN θ).mono Set.Ioo_subset_Ioi_self)

/-- For an admissible ray polygon `ps` and `R > 1`, the piece of the ray of angle `midNear ps`
between the levels `1` and `R` misses the ray polygon `polyCurve ps R`. -/
theorem rayPt_image_Ioo_subset_polyCurve_compl (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) {R : ℝ} (hR : 1 < R) :
    (fun s : ℝ => Work.EL.rayPt hN (Work.EL.midNear ps) s) '' Set.Ioo 1 R ⊆
      (Work.EL.polyCurve ps R)ᶜ := by
  rintro z ⟨s, ⟨hs1, hsR⟩, rfl⟩
  -- the ray points of level `> 1` lie off the filled Julia set
  have hsK : Work.EL.rayPt hN (Work.EL.midNear ps) s ∉ Work.EL.K c :=
    Work.EL.rayPt_notMem_K hN hs1
  -- the ray of angle `midNear ps` meets none of the rays of the polygon
  have hnotPar : ∀ X ∈ ps.flatMap (fun P => [P.a, P.b]),
      Work.EL.rayPt hN (Work.EL.midNear ps) s ∉ Work.EL.paramRay hN X :=
    fun X hX => rayPt_midNear_notMem_paramRay hN ps hA hX hs1
  rw [Work.EL.polyCurve]
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨P, hP, hPy | hpa | hpb⟩
    · -- the landing point `P.y` lies in `K c`
      exact hsK (by rw [hPy]; exact landsN_mem_K hN P.lands_a)
    · exact hnotPar P.a (List.mem_flatMap.mpr ⟨P, hP, by simp⟩)
        (Work.Top.NakaneData.rayPiece_subset_paramRay hpa)
    · exact hnotPar P.b (List.mem_flatMap.mpr ⟨P, hP, by simp⟩)
        (Work.Top.NakaneData.rayPiece_subset_paramRay hpb)
  · -- the equipotential part of the polygon sits at level `R > s`
    rintro ⟨θ', _, _, hθeq⟩
    have hpots : Work.EL.pot hN (Work.EL.rayPt hN (Work.EL.midNear ps) s) = Real.log s :=
      Work.EL.pot_rayPt hN hs1
    have hpotR : Work.EL.pot hN (Work.EL.rayPt hN θ' R) = Real.log R := Work.EL.pot_rayPt hN hR
    have hlog : Real.log s = Real.log R := by rw [← hpots, hθeq, hpotR]
    have hspos : (0 : ℝ) < s := by linarith
    have hRpos : (0 : ℝ) < R := by linarith
    have hsReq : s = R := Real.log_injOn_pos hspos hRpos hlog
    linarith

theorem innerRay_subset_polyRegion {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) {R t : ℝ} (hR : 1 < R)
    (h1 : 1 < t) (h2 : t < R) :
    Work.EL.rayPt hN (Work.EL.midNear ps) t ∈ Work.EL.polyRegion ps R := by
  rw [Work.EL.polyRegion]
  have hpre : IsPreconnected
      ((fun s : ℝ => Work.EL.rayPt hN (Work.EL.midNear ps) s) '' Set.Ioo 1 R) :=
    isPreconnected_rayPt_image_Ioo hN (Work.EL.midNear ps) R
  have hsub : (fun s : ℝ => Work.EL.rayPt hN (Work.EL.midNear ps) s) '' Set.Ioo 1 R ⊆
      (Work.EL.polyCurve ps R)ᶜ :=
    rayPt_image_Ioo_subset_polyCurve_compl hN ps hA hR
  have hsqt : Real.sqrt R ∈ Set.Ioo (1 : ℝ) R := by
    refine ⟨(Real.lt_sqrt zero_le_one).mpr (by simpa using hR), ?_⟩
    have h1s : 1 < Real.sqrt R := (Real.lt_sqrt zero_le_one).mpr (by simpa using hR)
    have hsq : Real.sqrt R ^ 2 = R := Real.sq_sqrt (by linarith)
    nlinarith [hsq, h1s]
  have hmem_s : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R) ∈
      (fun s : ℝ => Work.EL.rayPt hN (Work.EL.midNear ps) s) '' Set.Ioo 1 R :=
    ⟨Real.sqrt R, hsqt, rfl⟩
  have hmem_t : Work.EL.rayPt hN (Work.EL.midNear ps) t ∈
      (fun s : ℝ => Work.EL.rayPt hN (Work.EL.midNear ps) s) '' Set.Ioo 1 R :=
    ⟨t, ⟨h1, h2⟩, rfl⟩
  exact hpre.subset_connectedComponentIn hmem_s hsub hmem_t

end Work.ELTop
