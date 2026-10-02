/-
# The region of a ray polygon is the intersection of the near sides below the level `log R`

For an admissible list `ps` of co-landing pairs of rays of the dynamical plane and `1 < R`,
the region `Work.EL.polyRegion ps R` of the ray polygon is the set of points which lie on the
*near side* `Work.EL.pairSideNear P` of every pair `P ∈ ps` and below the equipotential of
level `R`, `pot hN · < log R`.

The inclusion `⊆` is the pair of previously proved statements `polyRegion_subset_pairSideNear`
and `polyRegion_subset_pot_lt`.  For the reverse inclusion one argues in three steps:

* off the filled Julia set `K c`, membership in the near sides forces the external angle to lie
  in no closed far arc, so `Work.ELTop.mem_polyRegion_iff_of_notMem_K` applies;
* at a point of `∂(K c)` one perturbs slightly off `K c` (the near sides are open) and reduces
  to the previous case: the point lies in the closure of the region, hence in the region;
* at an *interior* point of `K c` the point is surrounded by a whole component `D` of
  `interior (K c)` lying in the near sides; if `D` were in the unbounded side of the polygon,
  then (since the frontier of the region and the polygon meet `K c` only in the landing points)
  the frontier of `D` would be contained in the *finite* set of landing points, forcing the
  bounded `D` to be unbounded -- a contradiction.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.mem_polyRegion_iff_of_notMem_K
import Submission.Work.ELTop.RegionBasics
import Submission.Work.ELTop.polyRegion_subset_pairSideNear
import Submission.Work.ELTop.polyRegion_subset_pot_lt
import Submission.Work.ELTop.isOpen_pairSide
import Submission.Work.ELTop.isClosed_pairCurve
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.nearArc_angle_data
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.frontier_polyRegion_inter_K
import Submission.Work.Top.mem_paramRay_extAngle
import Submission.Work.Top.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option maxHeartbeats 1600000

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ}

/-! ## Landing points are not interior points of the filled Julia set -/

/-- A landing point of a ray lies in the closure of the complement of `K c`, hence is not an
interior point of `K c`. -/
theorem landing_notMem_interior (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ}
    (hland : Work.EL.LandsN hN θ y) : y ∉ interior (Work.EL.K c) := by
  have hcl : y ∈ closure ((Work.EL.K c)ᶜ) :=
    mem_closure_of_tendsto hland (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact Work.EL.rayPt_notMem_K hN ht)
  intro hint
  obtain ⟨w, hw⟩ := mem_closure_iff.mp hcl (interior (Work.EL.K c)) isOpen_interior hint
  exact hw.2 (interior_subset hw.1)

/-! ## The external angle of a point of a near side -/

/-- If a point `w ∉ K c` lies in the near side of the pair `P`, then its external angle lies in
no *closed* far arc of `P`. -/
theorem notInClosedArc_extAngle_of_mem_pairSideNear (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P : Work.EL.CoPair hN) (hnd : Work.EL.arcLen P.a P.b ≠ 0)
    {w : ℂ} (hwK : w ∉ Work.EL.K c) (hw : w ∈ Work.EL.pairSideNear P) :
    ¬ Work.EL.InClosedArc (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) w) P.a P.b := by
  classical
  obtain ⟨-, hdisj, -, -⟩ := pairSides_decomposition hN hJ P hnd
  have hwcomp : w ∈ (Work.EL.pairCurve P)ᶜ := fun h => connectedComponentIn_subset _ _ hw h
  have hwray : w ∈ Work.EL.paramRay hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) w) :=
    Work.Top.mem_paramRay_extAngle hN hwK
  have hne_a : ∀ k : ℤ,
      Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) w ≠ P.a + (k : ℝ) := by
    intro k hk
    have h2 : Work.EL.paramRay hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) w)
        = Work.EL.paramRay hN P.a := by rw [hk]; exact paramRay_add_int hN P.a k
    exact hwcomp ((Work.EL.mem_pairCurve_iff P w).mpr (Or.inl (h2 ▸ hwray)))
  have hne_b : ∀ k : ℤ,
      Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) w ≠ P.b + (k : ℝ) := by
    intro k hk
    have h2 : Work.EL.paramRay hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) w)
        = Work.EL.paramRay hN P.b := by rw [hk]; exact paramRay_add_int hN P.b k
    exact hwcomp ((Work.EL.mem_pairCurve_iff P w).mpr (Or.inr (Or.inr (h2 ▸ hwray))))
  have hnarc : ¬ Work.EL.InArc (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) w) P.a P.b := by
    intro hIn
    exact (Set.disjoint_left.mp hdisj (paramRay_subset_pairSide hN hJ P hIn hwray)) hw
  exact (not_InClosedArc_iff_not_InArc P.a P.b _).mpr ⟨hnarc, hne_a, hne_b⟩

/-! ## The set on which all near sides hold is open -/

/-- The set of points lying in the near side of *every* pair of a finite list is open. -/
theorem isOpen_setOf_forall_mem_pairSideNear (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) :
    IsOpen {w : ℂ | ∀ P ∈ ps, w ∈ Work.EL.pairSideNear P} := by
  induction ps with
  | nil =>
    convert isOpen_univ using 1
    ext w; simp
  | cons P tl ih =>
    have hset : {w : ℂ | ∀ Q ∈ P :: tl, w ∈ Work.EL.pairSideNear Q}
        = Work.EL.pairSideNear P ∩ {w : ℂ | ∀ Q ∈ tl, w ∈ Work.EL.pairSideNear Q} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, List.mem_cons]
      constructor
      · intro h; exact ⟨h P (Or.inl rfl), fun Q hQ => h Q (Or.inr hQ)⟩
      · rintro ⟨h1, h2⟩ Q (rfl | hQ)
        · exact h1
        · exact h2 Q hQ
    rw [hset]
    exact (isOpen_pairSide hN P).2.inter ih

/-! ## The reverse inclusion off `K c` -/

/-- A point off `K c` which lies in the near side of every pair and below the level `log R`
lies in the region. -/
theorem mem_polyRegion_of_notMem_K_of_nearSides (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    (hnd : ∀ P ∈ ps, Work.EL.arcLen P.a P.b ≠ 0)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R))
    {z : ℂ} (hzK : z ∉ Work.EL.K c) (hnear : ∀ P ∈ ps, z ∈ Work.EL.pairSideNear P)
    (hpot : Work.EL.pot hN z < Real.log R) :
    z ∈ Work.EL.polyRegion ps R := by
  rw [mem_polyRegion_iff_of_notMem_K hN hJ ps hA hR hC hzK]
  exact ⟨fun P hP => notInClosedArc_extAngle_of_mem_pairSideNear hN hJ P (hnd P hP) hzK
    (hnear P hP), hpot⟩

/-! ## Perturbation off the interior of `K c` -/

/-- A point `z ∉ interior (K c)` which lies in the near side of every pair and below the level
`log R` lies in the closure of the region: perturbing `z` slightly off `K c` (the near sides
are open) gives points of the region. -/
theorem mem_closure_polyRegion_of_nearSides_of_notMem_interior (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    (hnd : ∀ P ∈ ps, Work.EL.arcLen P.a P.b ≠ 0)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R))
    {z : ℂ} (hnear : ∀ P ∈ ps, z ∈ Work.EL.pairSideNear P)
    (hpot : Work.EL.pot hN z < Real.log R) (hzint : z ∉ interior (Work.EL.K c)) :
    z ∈ closure (Work.EL.polyRegion ps R) := by
  classical
  have hNopen : IsOpen {w : ℂ | ∀ P ∈ ps, w ∈ Work.EL.pairSideNear P} :=
    isOpen_setOf_forall_mem_pairSideNear hN ps
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hNopen z hnear
  have hcont : Continuous (Work.EL.pot hN) := hN.continuous_potential
  obtain ⟨r₁, hr₁pos, hr₁⟩ :=
    Metric.continuousAt_iff.mp hcont.continuousAt (Real.log R - Work.EL.pot hN z) (by linarith)
  have hzc : z ∈ closure ((Work.EL.K c)ᶜ) := by
    rw [closure_compl]
    exact hzint
  rw [Metric.mem_closure_iff]
  intro δ hδpos
  obtain ⟨w, hwKc, hwd⟩ := (Metric.mem_closure_iff.mp hzc) (min δ (min ε r₁))
    (lt_min hδpos (lt_min hεpos hr₁pos))
  have hwd' : dist w z < min δ (min ε r₁) := by rw [dist_comm]; exact hwd
  have hwε : dist w z < ε := lt_of_lt_of_le hwd'
    (le_trans (min_le_right δ (min ε r₁)) (min_le_left ε r₁))
  have hwr₁ : dist w z < r₁ := lt_of_lt_of_le hwd'
    (le_trans (min_le_right δ (min ε r₁)) (min_le_right ε r₁))
  have hwδ : dist w z < δ := lt_of_lt_of_le hwd' (min_le_left δ (min ε r₁))
  refine ⟨w, mem_polyRegion_of_notMem_K_of_nearSides hN hJ ps hA hnd hR hC hwKc ?_ ?_, ?_⟩
  · intro P hP
    exact hε (Metric.mem_ball.mpr hwε) P hP
  · have h1 : dist (Work.EL.pot hN w) (Work.EL.pot hN z) < Real.log R - Work.EL.pot hN z :=
      hr₁ hwr₁
    rw [Real.dist_eq] at h1
    linarith [(abs_lt.mp h1).2]
  · rw [dist_comm]; exact hwδ

/-! ## A bounded open preconnected set has infinite frontier -/

/-- A bounded, open, preconnected, nonempty subset of `ℂ` has an infinite frontier.  We use the
contrapositive form needed below: if its frontier is finite it cannot be bounded. -/
theorem not_isBounded_of_isOpen_isPreconnected_finite_frontier {V : Set ℂ}
    (hopen : IsOpen V) (_hpre : IsPreconnected V) (hne : V.Nonempty)
    (hfin : (frontier V).Finite) : ¬ Bornology.IsBounded V := by
  intro hbdd
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hcomplpre : IsPreconnected ((frontier V)ᶜ) :=
    (hfin.countable.isConnected_compl_of_one_lt_rank hrank).isPreconnected
  have hfront : frontier V = closure V \ V := by rw [frontier, hopen.interior_eq]
  have hcover : ((frontier V)ᶜ) = V ∪ (closure V)ᶜ := by
    rw [hfront]
    ext x; simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_union]; tauto
  have hdisj : ((frontier V)ᶜ) ∩ (V ∩ (closure V)ᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨-, hxV, hxcl⟩
    exact hxcl (subset_closure hxV)
  rcases isPreconnected_iff_subset_of_disjoint.mp hcomplpre V (closure V)ᶜ hopen
    isClosed_closure.isOpen_compl hcover.le hdisj with h | h
  · obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hbdd
    obtain ⟨M', hM'⟩ := (hfin.image (fun w : ℂ => ‖w‖)).bddAbove
    have hlarge : ∃ w : ℂ, w ∉ frontier V ∧ M < ‖w‖ := by
      obtain ⟨n, hn⟩ := exists_nat_gt (max M M')
      have hnM : M < (n : ℝ) := lt_of_le_of_lt (le_max_left M M') hn
      have hinj : Function.Injective (fun k : ℕ => ((n + k : ℕ) : ℂ)) := by
        intro a b hab
        exact Nat.add_left_cancel (Nat.cast_injective hab)
      have hinf : (Set.range (fun k : ℕ => ((n + k : ℕ) : ℂ))).Infinite :=
        Set.infinite_range_of_injective hinj
      have hnotsub : ¬ Set.range (fun k : ℕ => ((n + k : ℕ) : ℂ)) ⊆ frontier V :=
        fun hsub => hinf (hfin.subset hsub)
      rw [Set.not_subset] at hnotsub
      obtain ⟨w, ⟨k, rfl⟩, hwF⟩ := hnotsub
      refine ⟨_, hwF, ?_⟩
      rw [Complex.norm_natCast]
      have hle : (n : ℝ) ≤ ((n + k : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_right n k
      linarith
    obtain ⟨w, hwF, hwM⟩ := hlarge
    exact (not_le.mpr hwM) (hM w (h hwF))
  · refine hne.ne_empty ?_
    rw [Set.eq_empty_iff_forall_notMem]
    intro w hw
    exact (h (fun hfw => (hfront ▸ hfw).2 hw)) (subset_closure hw)

/-! ## The main identity -/

theorem polyRegion_eq_inter_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    (hnd : ∀ P ∈ ps, Work.EL.arcLen P.a P.b ≠ 0)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    Work.EL.polyRegion ps R =
      ({z : ℂ | ∀ P ∈ ps, z ∈ Work.EL.pairSideNear P} ∩ {z : ℂ | Work.EL.pot hN z < Real.log R}) := by
  classical
  apply Set.Subset.antisymm
  · rintro z hz
    exact ⟨fun P hP => polyRegion_subset_pairSideNear hN hJ ps hA hR hC P hP hz,
      polyRegion_subset_pot_lt hN hJ ps hA hR hC hz⟩
  · rintro z ⟨hnear, hpot⟩
    set S : Work.Top.Sides (Work.EL.polyCurve ps R) := hJ.sides (Work.EL.polyCurve ps R) hC with hS
    have hSI : Work.EL.polyRegion ps R = S.I := polyRegion_eq_sides_I' hN hJ ps hA hR hC
    -- `z` is not on the polygon
    have hznotC : z ∉ Work.EL.polyCurve ps R := by
      intro hzC
      rw [Work.EL.polyCurve] at hzC
      simp only [Set.mem_ofPred_eq] at hzC
      have hmemP : ∀ P ∈ ps, z ∉ Work.EL.pairCurve P := fun P hP =>
        connectedComponentIn_subset _ _ (hnear P hP)
      rcases hzC with ⟨P, hP, hy | hr | hr⟩ | ⟨θ, hθ, hfar, hzθ⟩
      · exact hmemP P hP ((Work.EL.mem_pairCurve_iff P z).mpr (Or.inr (Or.inl hy)))
      · exact hmemP P hP ((Work.EL.mem_pairCurve_iff P z).mpr
          (Or.inl (Work.Top.NakaneData.rayPiece_subset_paramRay hr)))
      · exact hmemP P hP ((Work.EL.mem_pairCurve_iff P z).mpr
          (Or.inr (Or.inr (Work.Top.NakaneData.rayPiece_subset_paramRay hr))))
      · have hp : Work.EL.pot hN z < Real.log R := hpot
        rw [hzθ, Work.EL.pot_rayPt hN hR] at hp
        exact lt_irrefl _ hp
    have hcl : closure (Work.EL.polyRegion ps R)
        = Work.EL.polyRegion ps R ∪ Work.EL.polyCurve ps R := by
      rw [closure_eq_self_union_frontier, frontier_polyRegion_eq_polyCurve hN hJ ps hA hR hC]
    have hzcompl : z ∈ (Work.EL.polyCurve ps R)ᶜ := hznotC
    rw [← S.union_eq] at hzcompl
    rcases hzcompl with hI | hO
    · rw [hSI]; exact hI
    · exfalso
      have hznotreg : z ∉ Work.EL.polyRegion ps R := fun hzreg => S.notMem_O_of_mem_I (hSI ▸ hzreg) hO
      by_cases hzint : z ∈ interior (Work.EL.K c)
      · -- interior case
        let D : Set ℂ := connectedComponentIn (interior (Work.EL.K c)) z
        have hzD : z ∈ D := mem_connectedComponentIn hzint
        have hDpre : IsPreconnected D := isPreconnected_connectedComponentIn
        have hDopen : IsOpen D := IsOpen.connectedComponentIn isOpen_interior
        have hDint : D ⊆ interior (Work.EL.K c) := connectedComponentIn_subset _ _
        have hDsubK : D ⊆ Work.EL.K c := fun w hw => interior_subset (hDint hw)
        have hPy_notint : ∀ P ∈ ps, P.y ∉ interior (Work.EL.K c) :=
          fun P hP => landing_notMem_interior hN P.lands_a
        have hDnear : ∀ P ∈ ps, D ⊆ Work.EL.pairSideNear P := by
          intro P hP
          obtain ⟨hdecomp, hdisjP, -, -⟩ := pairSides_decomposition hN hJ P (hnd P hP)
          refine IsPreconnected.subset_left_of_subset_union (isOpen_pairSide hN P).2
            (isOpen_pairSide hN P).1 hdisjP.symm ?_ ?_ hDpre
          · have hsub' : D ⊆ (Work.EL.pairCurve P)ᶜ := by
              intro w hw
              rw [Set.mem_compl_iff]
              intro hwPC
              have hwK : w ∈ Work.EL.K c := hDsubK hw
              have hwy : w = P.y := by
                simpa using (pairCurve_inter_K_subset hN P ⟨hwPC, hwK⟩)
              exact hPy_notint P hP (hwy ▸ hDint hw)
            rw [hdecomp] at hsub'
            rwa [Set.union_comm] at hsub' 
          · exact ⟨z, hzD, hnear P hP⟩
        have hDcompl : D ⊆ (Work.EL.polyCurve ps R)ᶜ := by
          intro w hw
          rw [Set.mem_compl_iff]
          intro hwC
          have hwK : w ∈ Work.EL.K c := hDsubK hw
          have hw2 : w ∈ Work.EL.polyCurve ps R ∩ Work.EL.K c := ⟨hwC, hwK⟩
          rw [polyCurve_inter_K hN ps hR] at hw2
          obtain ⟨P, hP, hPy⟩ := hw2
          exact hPy_notint P hP (hPy ▸ hDint hw)
        rcases S.subset_of_preconnected hDpre hDcompl with hDI | hDO
        · exact (S.notMem_O_of_mem_I (hDI hzD)) hO
        · -- `D` is in the unbounded side: contradiction
          have hPyK : ∀ P ∈ ps, P.y ∈ Work.EL.K c := fun P hP => landsN_mem_K hN P.lands_a
          have hbndN : ∀ q ∈ frontier D,
              q ∉ {w : ℂ | ∀ P ∈ ps, w ∈ Work.EL.pairSideNear P} := by
            intro q hqD hqN
            have hqcl : q ∈ closure D := frontier_subset_closure hqD
            have hqK : q ∈ Work.EL.K c := closure_minimal hDsubK hN.isClosed_mb hqcl
            have hqnotint : q ∉ interior (Work.EL.K c) := by
              intro hqint
              have hqd : q ∈ D := by
                obtain ⟨ρ, hρpos, hρball⟩ := Metric.isOpen_iff.mp isOpen_interior q hqint
                obtain ⟨w, hwD, hwd⟩ := Metric.mem_closure_iff.mp hqcl ρ hρpos
                have hwd' : dist w q < ρ := by rw [dist_comm]; exact hwd
                have hwball : w ∈ Metric.ball q ρ := Metric.mem_ball.mpr hwd'
                have hconn : IsPreconnected (D ∪ Metric.ball q ρ) :=
                  IsPreconnected.union w hwD hwball hDpre (convex_ball q ρ).isPreconnected
                have hsub : D ∪ Metric.ball q ρ ⊆ interior (Work.EL.K c) := by
                  rintro x (hx | hx)
                  · exact hDint hx
                  · exact hρball hx
                have hsubC := IsPreconnected.subset_connectedComponentIn hconn (Or.inl hzD) hsub
                exact hsubC (Or.inr (Metric.mem_ball_self hρpos))
              have hqD2 : q ∉ interior D := by
                simp only [frontier, Set.mem_diff] at hqD
                exact hqD.2
              rw [hDopen.interior_eq] at hqD2
              exact hqD2 hqd
            have hqreg : q ∈ closure (Work.EL.polyRegion ps R) :=
              mem_closure_polyRegion_of_nearSides_of_notMem_interior hN hJ ps hA hnd hR hC hqN
                (by rw [Work.EL.pot_of_mem hN hqK]; exact Real.log_pos hR) hqnotint
            have hqclO : q ∈ closure S.O := closure_mono hDO hqcl
            rw [closure_eq_self_union_frontier, S.frontier_O] at hqclO
            rw [hcl] at hqreg
            have hqC : q ∈ Work.EL.polyCurve ps R := by
              rcases hqclO with h1 | h1
              · rcases hqreg with h2 | h2
                · exfalso
                  exact (S.notMem_O_of_mem_I (hSI ▸ h2)) h1
                · exact h2
              · exact h1
            have hqC2 : q ∈ Work.EL.polyCurve ps R ∩ Work.EL.K c := ⟨hqC, hqK⟩
            rw [polyCurve_inter_K hN ps hR] at hqC2
            obtain ⟨P, hP, hPy⟩ := hqC2
            have hqnearP : q ∈ Work.EL.pairSideNear P := hqN P hP
            have hqPC : q ∈ Work.EL.pairCurve P := hPy ▸ self_mem_pairCurve P
            exact (connectedComponentIn_subset _ _ hqnearP) hqPC
          have hbnd2 : frontier D ⊆ {w : ℂ | ∃ P ∈ ps, w ∈ Work.EL.pairCurve P} := by
            intro q hq
            by_contra hqnot
            simp only [Set.mem_setOf_eq, not_exists, not_and] at hqnot
            have hpns : ∀ P ∈ ps, q ∈ Work.EL.pairSideNear P := by
              intro P hP
              have hqcl2 : q ∈ closure (Work.EL.pairSideNear P) :=
                closure_mono (hDnear P hP) (frontier_subset_closure hq)
              rw [closure_eq_self_union_frontier,
                (pairSides_decomposition hN hJ P (hnd P hP)).2.2.2] at hqcl2
              rcases hqcl2 with h | h
              · exact h
              · exact absurd h (hqnot P hP)
            exact hbndN q hq hpns
          have hbndY : frontier D ⊆ {w : ℂ | ∃ P ∈ ps, P.y = w} := by
            intro q hq
            obtain ⟨P, hP, hqPC⟩ := hbnd2 hq
            have hqK : q ∈ Work.EL.K c :=
              closure_minimal hDsubK hN.isClosed_mb (frontier_subset_closure hq)
            have hqy : q = P.y := Set.mem_singleton_iff.mp (pairCurve_inter_K_subset hN P ⟨hqPC, hqK⟩)
            exact ⟨P, hP, hqy.symm⟩
          have hfinY : ({w : ℂ | ∃ P ∈ ps, P.y = w}).Finite :=
            Set.Finite.subset ((List.finite_toSet ps).image (fun P : Work.EL.CoPair hN => P.y))
              (by rintro w ⟨P, hP, rfl⟩; exact ⟨P, hP, rfl⟩)
          exact (not_isBounded_of_isOpen_isPreconnected_finite_frontier hDopen hDpre ⟨z, hzD⟩
            (Set.Finite.subset hfinY hbndY)) (hN.isBounded_mb.subset hDsubK)
      · -- perturbative case
        have hzc := mem_closure_polyRegion_of_nearSides_of_notMem_interior hN hJ ps hA hnd hR hC
          hnear hpot hzint
        rw [hcl] at hzc
        rcases hzc with h' | h'
        · exact hznotreg h'
        · exact hznotC h'

end Work.ELTop
