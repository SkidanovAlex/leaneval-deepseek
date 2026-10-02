/-
# The landing point of a ray through a near arc lies in the region of a ray polygon

Let `ps` be an admissible list of co-landing pairs of rays of the dynamical plane of `T_c`, let
`1 < R` and suppose that the ray polygon `Work.EL.polyCurve ps R` is a Jordan curve.  Let `θ`
be an angle which lies in no **closed** far arc `[P.a, P.b]` of `ps` — equivalently, `θ` lies in
one of the open *near* arcs of the polygon — and let `y` be the landing point of the ray of
angle `θ`, with `y` different from every landing point `P.y` of `ps`.

Then `y` lies in the region `Work.EL.polyRegion ps R`, the bounded side of the polygon curve.

The proof is a limit argument.  The region is the bounded side `S.I` of the Jordan curve
(`Work.ELTop.polyRegion_eq_sides_I'`).  A landing point lies in the filled Julia set
(`Work.ELTop.landsN_mem_K`), so it cannot lie on the curve except possibly at a vertex `P.y`,
which is excluded by hypothesis; hence `y ∉ polyCurve ps R`.  On the other hand, the *near arc*
containing `θ` is surrounded by a whole gap of angles avoiding all the arcs and all the polygon
angles (`Work.ELTop.exists_gap_of_notInClosedArc`), so every ray point of angle `θ` at a level
`t` with `1 < t < R` lies on the near side of the curve and therefore in the bounded side
(`Work.ELTop.rayPt_mem_sides_I_of_gap`).  As `t ↘ 1` those ray points tend to `y`, so `y` lies
in the closure of the bounded side; the closure of a side is the side together with the curve,
and `y` is not on the curve.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.mem_polyRegion_iff_of_notMem_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

theorem landing_mem_polyRegion {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R))
    {θ : ℝ} {y : ℂ} (hland : Work.EL.LandsN hN θ y)
    (harc : ∀ P ∈ ps, ¬ Work.EL.InClosedArc θ P.a P.b) (hne : ∀ P ∈ ps, y ≠ P.y) :
    y ∈ Work.EL.polyRegion ps R := by
  -- a landing point lies in the filled Julia set
  have hyK : y ∈ Work.EL.K c := landsN_mem_K hN hland
  -- so it can only lie on the polygon curve as a vertex, which is excluded
  have hyC : y ∉ Work.EL.polyCurve ps R := by
    intro hyC
    rw [Work.EL.polyCurve] at hyC
    simp only [Set.mem_ofPred_eq] at hyC
    rcases hyC with ⟨P, hP, hy | hpa | hpb⟩ | ⟨θ', _hθ', _hfar, hy'⟩
    · exact hne P hP hy
    · exact (Work.EL.paramRay_subset_compl hN P.a
        (Work.Top.NakaneData.rayPiece_subset_paramRay hpa)) hyK
    · exact (Work.EL.paramRay_subset_compl hN P.b
        (Work.Top.NakaneData.rayPiece_subset_paramRay hpb)) hyK
    · exact Work.EL.rayPt_notMem_K hN hR (hy' ▸ hyK)
  -- the angle `θ` is surrounded by a gap of angles avoiding every arc and every polygon angle
  obtain ⟨μ₁, μ₂, hμ₁, hμ₂, hgap, hgapne⟩ := exists_gap_of_notInClosedArc (hN := hN) ps harc
  -- every ray point of angle `θ` below the level `R` lies in the bounded side of the curve
  have hmem : ∀ᶠ t : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      Work.EL.rayPt hN θ t ∈
        (Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC).I := by
    have hltR : Set.Iio R ∈ nhdsWithin (1 : ℝ) (Set.Ioi 1) :=
      nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hR)
    filter_upwards [self_mem_nhdsWithin, hltR] with t ht1 ht2
    exact rayPt_mem_sides_I_of_gap hN hJ ps hR hC ⟨hμ₁, hμ₂⟩ hgap hgapne ht1 ht2
  -- hence the landing point lies in the closure of the bounded side
  have hycl : y ∈ closure (Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC).I :=
    mem_closure_of_tendsto hland hmem
  -- and the closure of the bounded side is the side together with the curve
  have hfront : closure (Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC).I
      = (Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC).I
        ∪ Work.EL.polyCurve ps R := by
    rw [closure_eq_self_union_frontier,
      (Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC).frontier_I]
  rw [hfront] at hycl
  have hyI : y ∈ (Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC).I :=
    hycl.resolve_right hyC
  -- the region of an admissible polygon is exactly the bounded side
  rw [polyRegion_eq_sides_I' hN hJ ps hA hR hC]
  exact hyI

end Work.ELTop
