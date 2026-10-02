/-
# The region of a ray polygon is the bounded side of the polygon curve

For an admissible list `ps` of co-landing pairs and `R > 1`, the *region*
`Work.EL.polyRegion ps R` — the component of the complement of the polygon curve containing the
ray point of level `√R` in the near arc following the first pair — is the **bounded** side of
the polygon curve `Work.EL.polyCurve ps R`, as soon as that curve is a Jordan curve
(`hC : IsJordanCurve`).

The proof determines which of the two sides of the curve (given by the Jordan curve theorem,
as the abstract hypothesis `hJ : Work.Top.JordanForm`) contains the reference point
`x = rayPt hN (midNear ps) R`.  The decisive input is that the *cylindrical sector*
`cylSector hN (midNear ps - δ) (midNear ps + δ) R` — the points `rayPt θ t` with `θ` in a
genuine neighbourhood of `midNear ps` and `1 < t < R` — is a connected subset of the
complement of the curve which contains the seed: `Work.Top.Sides.sides_of_halves` then puts it
in the bounded side, because the *upper* half of a small neighbourhood of the crossing point
`x` on the equipotential arc meets the unbounded side (the superlevel set
`{pot > log R}` is unbounded and avoids the curve).

Two ingredients are isolated in their own modules:

* `Work.ELTop.nearArc_angle_data` : a neighbourhood of `midNear ps` avoiding every arc
  `(P.a, P.b)` and every angle modulo `ℤ`;
* `Work.ELTop.exists_rayPt_local` : off `K c`, the parametrisation `(θ,t) ↦ rayPt hN θ t` is
  locally surjective at every `(θ₀,t₀)` with `t₀ > 1`.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.nearArc_angle_data
import Submission.Work.ELTop.exists_rayPt_local
import Submission.Work.Top.isPreconnected_gt_potential
import Submission.Work.Top.continuousOn_rayPt

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

variable {c : ℂ} {φ : ℂ → ℂ}

/-! ## Auxiliary facts about the polygon curve -/

/-- `InArc` only depends on the angle modulo `ℤ`. -/
theorem InArc_add_int_aux (θ a b : ℝ) (k : ℤ) :
    Work.EL.InArc (θ + (k : ℝ)) a b ↔ Work.EL.InArc θ a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  rw [show θ + (k : ℝ) - a = (θ - a) + (k : ℝ) by ring, Int.fract_add_intCast]

/-- The joint parametrisation `(θ,t) ↦ rayPt hN θ t` of the rays is continuous above level `1`. -/
theorem continuousOn_rayPt_pair_aux (hN : Work.EL.DynB c φ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.EL.rayPt hN p.1 p.2) (Set.univ ×ˢ Set.Ioi 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hray : Continuous fun p : ↥(Set.univ ×ˢ Set.Ioi (1 : ℝ)) =>
      Work.Top.NakaneData.rayPoint p.1.1 p.1.2 := by
    unfold Work.Top.NakaneData.rayPoint
    fun_prop
  have hp : Continuous fun p : ↥(Set.univ ×ˢ Set.Ioi (1 : ℝ)) =>
      (⟨Work.Top.NakaneData.rayPoint p.1.1 p.1.2,
        Work.Top.NakaneData.rayPoint_mem_exteriorDisc p.2.2⟩ : ↥Work.Top.exteriorDisc) :=
    Continuous.subtype_mk hray _
  refine (continuous_subtype_val.comp (hN.e.symm.continuous.comp hp)).congr fun p => ?_
  rw [Set.domRestrict_apply]
  exact (Work.Top.NakaneData.rayPt_eq_symm hN p.2.2).symm

/-- A point of level `R` whose angle lies in no arc `(P.a, P.b)` of the polygon lies on the
polygon curve: the angle is first reduced into `[0,1)` and the ray point is then the
equipotential part of `polyCurve`. -/
theorem rayPt_mem_polyCurve_of_notInArc (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R θ : ℝ} (_hR : 1 < R) (hθ : ∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b) :
    Work.EL.rayPt hN θ R ∈ Work.EL.polyCurve ps R := by
  set k : ℤ := -⌊θ⌋ with hk
  have hshift : θ + (k : ℝ) = Int.fract θ := by
    rw [hk]
    push_cast
    have h := Int.fract_add_floor θ
    linarith
  have hfar : ∀ P ∈ ps, ¬ Work.EL.InArc (Int.fract θ) P.a P.b := by
    intro P hP
    rw [← hshift, InArc_add_int_aux]
    exact hθ P hP
  rw [Work.EL.polyCurve]
  simp only [Set.mem_ofPred_eq]
  refine Or.inr ⟨Int.fract θ, ⟨Int.fract_nonneg θ, le_of_lt (Int.fract_lt_one θ)⟩, hfar, ?_⟩
  have h' : θ = Int.fract θ + ((-k : ℤ) : ℝ) := by
    rw [← hshift]
    push_cast
    ring
  conv_lhs => rw [h']
  rw [Work.ELTop.rayPt_add_int hN (Int.fract θ) R (-k)]

/-- The polygon curve lies below its own equipotential: every ray piece has potential at most
`log R`, and the equipotential part has potential exactly `log R`. -/
theorem polyCurve_subset_pot_le_aux (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R : ℝ} (hR : 1 < R) :
    Work.EL.polyCurve ps R ⊆ {z : ℂ | Work.EL.pot hN z ≤ Real.log R} := by
  intro z hz
  simp only [Set.mem_ofPred_eq]
  rw [Work.EL.polyCurve] at hz
  simp only [Set.mem_ofPred_eq] at hz
  rcases hz with ⟨P, hP, hyz | hpa | hpb⟩ | ⟨θ, hθ, hfar, hθz⟩
  · rw [hyz, Work.EL.pot_of_mem hN (landsN_mem_K hN P.lands_a)]
    exact Real.log_nonneg (le_of_lt hR)
  · exact Work.Top.NakaneData.rayPiece_subset_le hpa
  · exact Work.Top.NakaneData.rayPiece_subset_le hpb
  · rw [hθz, Work.EL.pot_rayPt hN hR]

/-- The superlevel set `{pot > log R}` of the potential lies in the **unbounded** side of the
polygon curve: it is connected, unbounded and disjoint from the curve. -/
theorem gt_pot_subset_sides_O (hN : Work.EL.DynB c φ) (hJ : Work.Top.JordanForm)
    (ps : List (Work.EL.CoPair hN)) {R : ℝ} (hR : 1 < R)
    (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    {z : ℂ | Real.log R < Work.EL.pot hN z} ⊆ (hJ.sides (Work.EL.polyCurve ps R) hC).O := by
  refine Work.Top.Sides.subset_O_of_unbounded (hJ.sides (Work.EL.polyCurve ps R) hC) ?_ ?_ ?_
  · exact Work.Top.isPreconnected_gt_potential hN hR
  · intro z hz
    simp only [Set.mem_compl_iff]
    intro hzC
    have h1 := polyCurve_subset_pot_le_aux hN ps hR hzC
    simp only [Set.mem_ofPred_eq] at h1 hz
    exact absurd h1 (not_le.mpr hz)
  · intro n
    obtain ⟨R', hR'⟩ := hN.tendsto_potential (Real.log R + 1)
    have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hnorm : ‖(((max R' ((n : ℝ) + 1)) : ℝ) : ℂ)‖ = max R' ((n : ℝ) + 1) := by
      have h1 : ‖(((max R' ((n : ℝ) + 1)) : ℝ) : ℂ)‖ = |max R' ((n : ℝ) + 1)| := by simp
      rw [h1]
      exact abs_of_nonneg (le_trans hnn (le_max_right _ _))
    refine ⟨(((max R' ((n : ℝ) + 1)) : ℝ) : ℂ), ?_, ?_⟩
    · have h1 := hR' _ (by rw [hnorm]; exact le_max_left _ _)
      simp only [Set.mem_ofPred_eq]
      rw [Work.EL.pot_apply]
      linarith
    · rw [hnorm]
      exact le_trans (by linarith : (n : ℝ) ≤ (n : ℝ) + 1) (le_max_right _ _)

/-- The **cylindrical sector** of the angle interval `(μ₁, μ₂)` and the level interval `(1,R)`:
the points of the plane which are `rayPt hN θ t` with `μ₁ < θ < μ₂` and `1 < t < R`. -/
def cylSector (hN : Work.EL.DynB c φ) (μ₁ μ₂ R : ℝ) : Set ℂ :=
  (fun p : ℝ × ℝ => Work.EL.rayPt hN p.1 p.2) '' (Set.Ioo μ₁ μ₂ ×ˢ Set.Ioo 1 R)

/-! ## The region is the bounded side -/

theorem polyRegion_eq_sides_I {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    ∃ S : Work.Top.Sides (Work.EL.polyCurve ps R), Work.EL.polyRegion ps R = S.I := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hlogR : 0 < Real.log R := Real.log_pos hR
  -- a genuine neighbourhood of the reference angle avoiding all the arcs of the polygon
  obtain ⟨δ, hδpos, hδ⟩ := nearArc_angle_data ps hA
  -- room around the level `R`
  set δt : ℝ := min ((R - 1) / 2) (1 / 2) with hδtdef
  have hδtpos : 0 < δt := by rw [hδtdef]; exact lt_min (by linarith) (by norm_num)
  have hδtle : δt ≤ (R - 1) / 2 := by rw [hδtdef]; exact min_le_left _ _
  -- every point off `K c` near the reference point is a `rayPt` with parameters close to `(θ₀,R)`
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := exists_rayPt_local hN hR hδpos hδtpos
  have hpotx : Work.EL.pot hN (Work.EL.rayPt hN (Work.EL.midNear ps) R) = Real.log R :=
    Work.EL.pot_rayPt hN hR
  -- room where the potential exceeds `log R / 2`, hence `K c` is avoided
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.continuousAt_iff.mp hN.continuous_potential.continuousAt
    (Real.log R / 2) (by linarith)
  set ε : ℝ := min ε₁ ε₂ with hεdef
  have hεpos : 0 < ε := lt_min hε₁pos hε₂pos
  have hε₁le : ε ≤ ε₁ := by rw [hεdef]; exact min_le_left _ _
  have hε₂le : ε ≤ ε₂ := by rw [hεdef]; exact min_le_right _ _
  let S : Work.Top.Sides (Work.EL.polyCurve ps R) := hJ.sides (Work.EL.polyCurve ps R) hC
  -- the reference ray point lies on the curve
  have hxC : Work.EL.rayPt hN (Work.EL.midNear ps) R ∈ Work.EL.polyCurve ps R :=
    rayPt_mem_polyCurve_of_notInArc hN ps hR
      (fun P hP => (hδ (Work.EL.midNear ps)
        (by rw [sub_self, abs_zero]; exact hδpos)).1 P hP)
  -- the sector lies off the curve
  have hNsub : cylSector hN (Work.EL.midNear ps - δ) (Work.EL.midNear ps + δ) R ⊆
      (Work.EL.polyCurve ps R)ᶜ := by
    rintro z ⟨⟨θ, t⟩, ⟨hθ, ht⟩, rfl⟩
    have hθabs : |θ - Work.EL.midNear ps| < δ := by
      rw [abs_lt]; exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
    have ht1 : 1 < t := ht.1
    simp only [Set.mem_compl_iff]
    intro hzC
    rw [Work.EL.polyCurve] at hzC
    simp only [Set.mem_ofPred_eq] at hzC
    rcases hzC with ⟨P, hP, hyz | hpa | hpb⟩ | ⟨θ', hθ', hfar, hθ'z⟩
    · exact Work.EL.rayPt_notMem_K hN ht1 (hyz ▸ landsN_mem_K hN P.lands_a)
    · exact (Set.disjoint_left.mp (paramRay_disjoint hN (θ := P.a) (θ' := θ)
        (fun k => ((hδ θ hθabs).2 P hP).1 k))
        (Work.Top.NakaneData.rayPiece_subset_paramRay hpa))
        (Work.EL.rayPt_mem_paramRay hN ht1)
    · exact (Set.disjoint_left.mp (paramRay_disjoint hN (θ := P.b) (θ' := θ)
        (fun k => ((hδ θ hθabs).2 P hP).2 k))
        (Work.Top.NakaneData.rayPiece_subset_paramRay hpb))
        (Work.EL.rayPt_mem_paramRay hN ht1)
    · have h1 : Work.EL.pot hN (Work.EL.rayPt hN θ t)
          = Work.EL.pot hN (Work.EL.rayPt hN θ' R) := by
        rw [hθ'z]
      rw [Work.EL.pot_rayPt hN ht1, Work.EL.pot_rayPt hN hR] at h1
      have ht_eq : t = R := by
        rw [← Real.exp_log (by linarith : (0 : ℝ) < t), h1, Real.exp_log hRpos]
      linarith [ht.2]
  -- the sector is preconnected, being the image of a rectangle under `(θ,t) ↦ rayPt hN θ t`
  have hNconn :
      IsPreconnected (cylSector hN (Work.EL.midNear ps - δ) (Work.EL.midNear ps + δ) R) := by
    show IsPreconnected ((fun p : ℝ × ℝ => Work.EL.rayPt hN p.1 p.2)
      '' (Set.Ioo (Work.EL.midNear ps - δ) (Work.EL.midNear ps + δ) ×ˢ Set.Ioo 1 R))
    exact IsPreconnected.image (isPreconnected_Ioo.prod isPreconnected_Ioo) _
      ((continuousOn_rayPt_pair_aux hN).mono (fun p hp => ⟨trivial, Set.Ioo_subset_Ioi_self hp.2⟩))
  -- the superlevel set of the potential is connected, off the curve, and meets the unbounded side
  have hHconn : IsPreconnected {z : ℂ | Real.log R < Work.EL.pot hN z} :=
    Work.Top.isPreconnected_gt_potential hN hR
  have hHsub : {z : ℂ | Real.log R < Work.EL.pot hN z} ⊆ (Work.EL.polyCurve ps R)ᶜ := by
    intro z hz
    simp only [Set.mem_compl_iff]
    intro hzC
    have h1 := polyCurve_subset_pot_le_aux hN ps hR hzC
    simp only [Set.mem_ofPred_eq] at h1 hz
    exact absurd h1 (not_le.mpr hz)
  have hHmeets : ∃ z ∈ {z : ℂ | Real.log R < Work.EL.pot hN z}, z ∈ S.O := by
    have hz : Work.EL.rayPt hN 0 (R + 1) ∈ {z : ℂ | Real.log R < Work.EL.pot hN z} := by
      simp only [Set.mem_ofPred_eq]
      rw [Work.EL.pot_rayPt hN (by linarith)]
      exact (Real.log_lt_log_iff hRpos (by linarith)).mpr (by linarith)
    exact ⟨_, hz, gt_pot_subset_sides_O hN hJ ps hR hC hz⟩
  -- the local dichotomy: a point of the ball around the reference point off the curve is either
  -- in the sector (level below `R`) or in the superlevel set (level above `R`)
  have hcov : ∀ z : ℂ, z ∈ Metric.ball (Work.EL.rayPt hN (Work.EL.midNear ps) R) ε →
      z ∉ Work.EL.polyCurve ps R →
      z ∈ cylSector hN (Work.EL.midNear ps - δ) (Work.EL.midNear ps + δ) R ∪
        {z : ℂ | Real.log R < Work.EL.pot hN z} := by
    intro z hzball hzC
    have hb₁ : ‖z - Work.EL.rayPt hN (Work.EL.midNear ps) R‖ < ε₁ := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le (Metric.mem_ball.mp hzball) hε₁le
    have hb₂ : dist z (Work.EL.rayPt hN (Work.EL.midNear ps) R) < ε₂ :=
      lt_of_lt_of_le (Metric.mem_ball.mp hzball) hε₂le
    have hzK : z ∉ Work.EL.K c := by
      intro hzKm
      have h := hε₂ hb₂
      rw [Real.dist_eq, Work.Top.potential_of_mem hzKm,
        Work.Top.NakaneData.potential_rayPt hN hR] at h
      have h2 := (abs_lt.mp h).1
      linarith [hlogR]
    obtain ⟨θ, t, hθ, ht, hzt⟩ := hε₁ z hzK hb₁
    rcases lt_trichotomy t R with hlt | heq | hgt
    · refine Or.inl ⟨(θ, t), ⟨?_, ?_⟩, hzt.symm⟩
      · rw [abs_lt] at hθ; exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      · refine ⟨?_, hlt⟩
        have h1 : R - δt < t := by rw [abs_lt] at ht; linarith [ht.1]
        have h2 : (1 : ℝ) < R - δt := by linarith [hδtle]
        linarith
    · refine Or.inr ?_
      refine absurd ?_ hzC
      rw [hzt, heq]
      exact rayPt_mem_polyCurve_of_notInArc hN ps hR (fun P hP => (hδ θ hθ).1 P hP)
    · refine Or.inr ?_
      simp only [Set.mem_ofPred_eq]
      rw [hzt, Work.EL.pot_rayPt hN (by linarith : (1 : ℝ) < t)]
      exact (Real.log_lt_log_iff hRpos (by linarith : (0 : ℝ) < t)).mpr hgt
  -- local two-sidedness: the sector lies in the bounded side
  have hNsubI : cylSector hN (Work.EL.midNear ps - δ) (Work.EL.midNear ps + δ) R ⊆ S.I :=
    S.sides_of_halves (Metric.isOpen_ball)
      ⟨Work.EL.rayPt hN (Work.EL.midNear ps) R, Metric.mem_ball_self hεpos, hxC⟩
      (fun z hz => hcov z hz.1 hz.2)
      hNconn hHconn
      (Set.disjoint_left.mpr fun z hzN hzC => hNsub hzN hzC)
      (Set.disjoint_left.mpr fun z hzQ hzC => hHsub hzQ hzC) hHmeets
  -- the seed point of the region lies in the sector, hence in the bounded side
  have hseed : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R) ∈
      cylSector hN (Work.EL.midNear ps - δ) (Work.EL.midNear ps + δ) R := by
    refine ⟨(Work.EL.midNear ps, Real.sqrt R), ⟨?_, ?_⟩, rfl⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨(Real.lt_sqrt (by norm_num)).mpr (by simpa using hR),
        (Real.sqrt_lt' hRpos).mpr (by nlinarith)⟩
  have hseedI : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R) ∈ S.I := hNsubI hseed
  have hseed_mem : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R) ∈
      Work.EL.polyRegion ps R := by
    rw [Work.EL.polyRegion]
    exact mem_connectedComponentIn (S.subset_compl_I hseedI)
  -- the region is the component of the seed, and `S.I` is the component of the seed
  refine ⟨S, ?_⟩
  refine Set.Subset.antisymm ?_ ?_
  · rcases S.subset_of_preconnected (Work.EL.isPreconnected_polyRegion ps R)
      (Work.EL.polyRegion_subset_compl ps R) with h | h
    · exact h
    · exact absurd (h hseed_mem) (S.notMem_O_of_mem_I hseedI)
  · exact S.preconnected_I.subset_connectedComponentIn hseedI S.subset_compl_I

end Work.ELTop
