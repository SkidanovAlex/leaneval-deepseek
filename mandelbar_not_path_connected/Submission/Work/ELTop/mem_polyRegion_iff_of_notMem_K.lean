/-
# The ray-polygon region off the filled Julia set

This module proves the exact description of the region `Work.EL.polyRegion ps R` of a ray polygon
away from the filled Julia set: a point `z ∉ K c` lies in the region exactly when its external
angle lies in none of the *far* arcs `(P.a, P.b)` of the polygon (`P ∈ ps`) and its potential is
below `log R`.

The proof is the "Böttcher sector" argument of the EL design.

* Off `K c` the plane is the exterior disc in the Böttcher coordinate `dynPhi c φ`.  The set of
  angles avoiding all the closed far arcs is *open* (`isOpen_setOf_forall_not_InClosedArc`), so
  the angle of a point is surrounded by a whole *gap* `(μ₁, μ₂)` of angles which meet no arc and
  are congruent to no angle of the polygon (`exists_gap_of_notInClosedArc`).

* The *near sector* of a gap, `nearSector hN μ₁ μ₂ R`, is the image of the rectangle
  `(μ₁, μ₂) × (1, R)` under the (jointly) continuous map `(θ, t) ↦ rayPt hN θ t`; it is
  preconnected and, by the gap property, disjoint from the polygon
  (`nearSector_subset_compl`).

* Near the ray point `p = rayPt θ R` of a gap angle, the parametrisation is a local
  homeomorphism (`exists_rayPt_local`), so a small disc `B` around `p`, chosen to miss `K c`, is
  split by the polygon curve into the piece below level `R` (contained in the sector) and the
  piece above level `R` (which lies in the unbounded side); points of `B` at level exactly `R`
  lie on the curve.  Local two-sidedness (`Sides.sides_of_halves`) therefore puts the sector in
  the bounded side, and with it every ray point of the gap below level `R`.  This gives the
  implication *angle in a near arc and `pot < log R`* ⟹ *in the region*.

* Conversely, the bounded side of an arbitrary ray polygon is contained in `{pot < log R}`
  (`sides_I_subset_pot_lt`); and a point whose angle lies in a far arc `(P.a, P.b)` escapes to
  infinity inside the complement of the curve along its own ray (the open far arc contains no
  angle of the polygon, so the ray meets no ray piece, and it is not on the equipotential part),
  so it lies in the unbounded side.

## Main statements

* `Work.ELTop.exists_gap_of_notInClosedArc` : the gap of angles around an angle avoiding the
  closed far arcs;
* `Work.ELTop.rayPt_mem_sides_I_of_gap` : the ray piece of a gap angle below level `R` lies in
  the bounded side;
* `Work.ELTop.polyRegion_eq_sides_I'` : the region *is* the bounded side;
* `Work.ELTop.mem_polyRegion_iff_of_notMem_K` : the description of the region.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.seed_mem_polyRegion
import Submission.Work.ELTop.notInArc_midNear
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.rayPt_inj
import Submission.Work.ELTop.isClosed_polyCurve
import Submission.Work.ELTop.gt_potential_subset_sidesO
import Submission.Work.ELTop.level_eq_subset_sidesO
import Submission.Work.ELTop.sides_I_subset_pot_lt
import Submission.Work.ELTop.nearArc_angle_data
import Submission.Work.ELTop.PolyCurve.cyclicStrict_angle_data
import Submission.Work.ELTop.midNear_nearArc_nbhd
import Submission.Work.ELTop.exists_rayPt_local
import Submission.Work.ELTop.mem_pairSideNear_of_nearArc
import Submission.Work.ELTop.farArc_no_angle
import Submission.Work.Top.Jordan
import Submission.Work.Top.mem_eqArc_of
import Submission.Work.Top.isPreconnected_gt_potential

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


/-! ## Elementary facts about the closed cyclic arc -/

/-- An angle congruent to the left end of an arc lies in the closed arc. -/
theorem InClosedArc.add_int_left (a b : ℝ) (k : ℤ) : Work.EL.InClosedArc (a + (k : ℝ)) a b := by
  have h1 : a + (k : ℝ) - a = (k : ℝ) := by ring
  constructor
  · rw [h1, Int.fract_intCast]
  · rw [h1, Int.fract_intCast]
    exact Work.EL.arcLen_nonneg a b

/-- An angle congruent to the right end of an arc lies in the closed arc. -/
theorem InClosedArc.add_int_right (a b : ℝ) (k : ℤ) : Work.EL.InClosedArc (b + (k : ℝ)) a b := by
  refine ⟨Int.fract_nonneg _, ?_⟩
  have h1 : b + (k : ℝ) - a = (b - a) + (k : ℝ) := by ring
  rw [h1, Int.fract_add_intCast]
  exact le_refl _

/-- **The gap of an angle avoiding all the closed far arcs.**  Around such an angle there is a
whole interval of angles which lie in no (open) arc of the polygon and are congruent to no angle
of the polygon. -/
theorem exists_gap_of_notInClosedArc {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) {θ : ℝ}
    (h : ∀ P ∈ ps, ¬ Work.EL.InClosedArc θ P.a P.b) :
    ∃ μ₁ μ₂ : ℝ, μ₁ < θ ∧ θ < μ₂ ∧
      (∀ y ∈ Set.Ioo μ₁ μ₂, ∀ P ∈ ps, ¬ Work.EL.InArc y P.a P.b) ∧
      (∀ y ∈ Set.Ioo μ₁ μ₂, ∀ P ∈ ps, ∀ k : ℤ, y ≠ P.a + (k : ℝ) ∧ y ≠ P.b + (k : ℝ)) := by
  obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp (isOpen_setOf_forall_not_InClosedArc ps) θ h
  have hiff : ∀ y : ℝ, |y - θ| < δ ↔ y ∈ Metric.ball θ δ := by
    intro y; rw [Metric.mem_ball, Real.dist_eq]
  refine ⟨θ - δ / 2, θ + δ / 2, by linarith, by linarith, ?_, ?_⟩
  · intro y hy P hP
    have hyb : y ∈ Metric.ball θ δ := by
      rw [← hiff]
      obtain ⟨h1, h2⟩ := hy
      rw [abs_lt]; constructor <;> linarith
    intro hIn
    exact hδ hyb P hP (Work.EL.InArc.inClosedArc hIn)
  · intro y hy P hP k
    have hyb : y ∈ Metric.ball θ δ := by
      rw [← hiff]
      obtain ⟨h1, h2⟩ := hy
      rw [abs_lt]; constructor <;> linarith
    have hnc := hδ hyb P hP
    constructor
    · intro hyk
      exact hnc (hyk ▸ InClosedArc.add_int_left P.a P.b k)
    · intro hyk
      exact hnc (hyk ▸ InClosedArc.add_int_right P.a P.b k)

/-! ## The ray point of a point off the filled Julia set -/

/-- The exponential of the potential of a point off the filled Julia set is `> 1`. -/
theorem one_lt_exp_pot (hN : Work.EL.DynB c φ) {z : ℂ} (hz : z ∉ Work.EL.K c) :
    1 < Real.exp (Work.EL.pot hN z) := by
  have h1 : 1 < ‖Work.EL.dynPhi c φ z‖ := Work.Top.NakaneData.Phi_mem_exteriorDisc hN hz
  have hpos : 0 < Work.EL.pot hN z := by
    rw [Work.EL.pot_of_notMem hN hz]
    exact Real.log_pos h1
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ < Real.exp (Work.EL.pot hN z) := Real.exp_lt_exp.mpr hpos

/-- `exp (pot z) < R` is equivalent to `pot z < log R`. -/
theorem exp_pot_lt_iff (hN : Work.EL.DynB c φ) {R : ℝ} (hR : 1 < R) {z : ℂ}
    (hz : z ∉ Work.EL.K c) :
    Real.exp (Work.EL.pot hN z) < R ↔ Work.EL.pot hN z < Real.log R := by
  have hpos : 0 < Real.exp (Work.EL.pot hN z) := Real.exp_pos _
  rw [← Real.log_lt_log_iff hpos (by linarith : (0:ℝ) < R), Real.log_exp]

/-- **A point off the filled Julia set is the ray point of its own external angle at the level
`exp (pot z)`.** -/
theorem rayPt_extAngle_exp_pot (hN : Work.EL.DynB c φ) {z : ℂ} (hz : z ∉ Work.EL.K c) :
    Work.EL.rayPt hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z)
      (Real.exp (Work.EL.pot hN z)) = z := by
  have hΦ0 : Work.EL.dynPhi c φ z ≠ 0 := Work.Top.NakaneData.Phi_ne_zero hN hz
  have hnorm : ‖Work.EL.dynPhi c φ z‖ = Real.exp (Work.EL.pot hN z) := by
    rw [Work.EL.pot_of_notMem hN hz, Real.exp_log (norm_pos_iff.mpr hΦ0)]
  have hgt : 1 < Real.exp (Work.EL.pot hN z) := one_lt_exp_pot hN hz
  refine Work.Top.NakaneData.injOn_Phi hN (Work.EL.rayPt_notMem_K hN hgt) hz ?_
  rw [Work.Top.NakaneData.Phi_rayPt hN hgt]
  show Work.Top.NakaneData.rayPoint (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z)
    (Real.exp (Work.EL.pot hN z)) = Work.EL.dynPhi c φ z
  rw [← hnorm]
  exact (Work.Top.Phi_eq_norm_mul_exp_extAngle hN hΦ0).symm

/-- The ray point of angle `θ` at level `R` is the ray point of the reduced angle. -/
theorem rayPt_fract (hN : Work.EL.DynB c φ) (θ R : ℝ) :
    Work.EL.rayPt hN θ R = Work.EL.rayPt hN (Int.fract θ) R := by
  conv_lhs => rw [← Int.fract_add_floor θ]
  rw [Work.ELTop.rayPt_add_int]

/-- `InArc` depends on the angle only modulo `ℤ`. -/
theorem InArc_add_angle_int (θ a b : ℝ) (n : ℤ) :
    Work.EL.InArc (θ + (n : ℝ)) a b ↔ Work.EL.InArc θ a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  have h1 : Int.fract ((θ + (n : ℝ)) - a) = Int.fract (θ - a) := by
    have h : (θ + (n : ℝ)) - a = (θ - a) + (n : ℝ) := by ring
    rw [h, Int.fract_add_intCast]
  rw [h1]

/-- The near sector of the angle interval `(μ₁, μ₂)`: the points of the plane whose Böttcher
coordinate has angle in `(μ₁, μ₂)` and modulus in `(1, R)`. -/
def nearSector (hN : Work.EL.DynB c φ) (μ₁ μ₂ R : ℝ) : Set ℂ :=
  (fun p : ℝ × ℝ => Work.EL.rayPt hN p.1 p.2) '' (Set.Ioo μ₁ μ₂ ×ˢ Set.Ioo 1 R)

/-! ## The near sector -/

/-- The point of a ray depends continuously on the angle and the level, jointly, above level
`1`. -/
theorem continuousOn_rayPt_pair (hN : Work.EL.DynB c φ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.EL.rayPt hN p.1 p.2) (Set.univ ×ˢ Set.Ioi (1:ℝ)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hray : Continuous fun p : ℝ × ℝ => Work.Top.NakaneData.rayPoint p.1 p.2 := by
    unfold Work.Top.NakaneData.rayPoint
    fun_prop
  have hray' : Continuous fun p : ↥(Set.univ ×ˢ Set.Ioi (1:ℝ)) =>
      Work.Top.NakaneData.rayPoint (p.1 : ℝ × ℝ).1 (p.1 : ℝ × ℝ).2 :=
    hray.comp continuous_subtype_val
  have hp : Continuous fun p : ↥(Set.univ ×ˢ Set.Ioi (1:ℝ)) =>
      (⟨Work.Top.NakaneData.rayPoint (p.1 : ℝ × ℝ).1 (p.1 : ℝ × ℝ).2,
        Work.Top.NakaneData.rayPoint_mem_exteriorDisc p.2.2⟩ : ↥Work.Top.exteriorDisc) :=
    Continuous.subtype_mk hray' _
  have hg : Continuous fun p : ↥(Set.univ ×ˢ Set.Ioi (1:ℝ)) =>
      ((hN.e.symm (⟨Work.Top.NakaneData.rayPoint (p.1 : ℝ × ℝ).1 (p.1 : ℝ × ℝ).2,
        Work.Top.NakaneData.rayPoint_mem_exteriorDisc p.2.2⟩ : ↥Work.Top.exteriorDisc) :
        ↥(Work.EL.K c)ᶜ) : ℂ) :=
    continuous_subtype_val.comp (hN.e.symm.continuous.comp hp)
  refine hg.congr fun p => ?_
  rw [Set.domRestrict_apply]
  exact (Work.Top.NakaneData.rayPt_eq_symm hN p.2.2).symm

/-- The near sector `(μ₁, μ₂) × (1, R)` of the Böttcher plane is preconnected. -/
theorem isPreconnected_nearSector (hN : Work.EL.DynB c φ) (μ₁ μ₂ R : ℝ) :
    IsPreconnected (nearSector hN μ₁ μ₂ R) := by
  rw [nearSector]
  refine IsPreconnected.image (isPreconnected_Ioo.prod isPreconnected_Ioo) _ ?_
  refine (continuousOn_rayPt_pair hN).mono ?_
  intro p hp
  exact ⟨Set.mem_univ _, hp.2.1⟩

/-- The near sector of a gap misses the ray polygon. -/
theorem nearSector_subset_compl (hN : Work.EL.DynB c φ) (ps : List (Work.EL.CoPair hN))
    {R μ₁ μ₂ : ℝ} (hR : 1 < R)
    (hgap : ∀ y ∈ Set.Ioo μ₁ μ₂, ∀ P ∈ ps, ¬ Work.EL.InArc y P.a P.b)
    (hne : ∀ y ∈ Set.Ioo μ₁ μ₂, ∀ P ∈ ps, ∀ k : ℤ, y ≠ P.a + (k : ℝ) ∧ y ≠ P.b + (k : ℝ)) :
    nearSector hN μ₁ μ₂ R ⊆ (Work.EL.polyCurve ps R)ᶜ := by
  rintro z ⟨p, hp, rfl⟩
  obtain ⟨hy, hs⟩ := hp
  have hs1 : 1 < p.2 := hs.1
  rw [Set.mem_compl_iff, Work.EL.polyCurve]
  simp only [Set.mem_ofPred_eq, not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨P, hP, hyy | hpa | hpb⟩
    · exact Work.EL.rayPt_notMem_K hN hs1 (hyy ▸ landsN_mem_K hN P.lands_a)
    · exact notMem_paramRay_of_ne_int hN (fun k => (hne p.1 hy P hP k).1) hs1
        (Work.Top.NakaneData.rayPiece_subset_paramRay hpa)
    · exact notMem_paramRay_of_ne_int hN (fun k => (hne p.1 hy P hP k).2) hs1
        (Work.Top.NakaneData.rayPiece_subset_paramRay hpb)
  · rintro ⟨θ', hθ', hfar, heq⟩
    have h1 : Work.EL.pot hN (Work.EL.rayPt hN p.1 p.2) = Real.log p.2 :=
      Work.EL.pot_rayPt hN hs1
    have h2 : Work.EL.pot hN (Work.EL.rayPt hN θ' R) = Real.log R := Work.EL.pot_rayPt hN hR
    rw [heq] at h1
    have hlog : Real.log p.2 = Real.log R := by rw [← h1, h2]
    have h2R : p.2 = R :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr (lt_trans zero_lt_one hs1))
        (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < R)) hlog
    linarith [hs.2]

/-! ## The ray piece of a gap angle lies in the bounded side -/

/-- **Main local step.**  Let `(μ₁, μ₂)` be a gap of angles which lie in no arc of the polygon
and are congruent to no angle of the polygon, and let `θ ∈ (μ₁, μ₂)`.  Then the ray point
`rayPt hN θ t` (for `1 < t < R`) lies in the *bounded* side of the polygon. -/
theorem rayPt_mem_sides_I_of_gap {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) {R : ℝ} (hR : 1 < R)
    (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) {μ₁ μ₂ θ t : ℝ}
    (hθ : θ ∈ Set.Ioo μ₁ μ₂)
    (hgap : ∀ y ∈ Set.Ioo μ₁ μ₂, ∀ P ∈ ps, ¬ Work.EL.InArc y P.a P.b)
    (hne : ∀ y ∈ Set.Ioo μ₁ μ₂, ∀ P ∈ ps, ∀ k : ℤ, y ≠ P.a + (k : ℝ) ∧ y ≠ P.b + (k : ℝ))
    (ht1 : 1 < t) (ht2 : t < R) :
    Work.EL.rayPt hN θ t ∈ (Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC).I := by
  classical
  set S : Work.Top.Sides (Work.EL.polyCurve ps R) :=
    Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC with hSdef
  have hRpos : 0 < R := by linarith
  -- the angular tolerance of the gap
  set δθ : ℝ := min (θ - μ₁) (μ₂ - θ) / 2 with hδθdef
  have hδθ : 0 < δθ := by
    rw [hδθdef]
    have h1 : 0 < θ - μ₁ := by linarith [hθ.1]
    have h2 : 0 < μ₂ - θ := by linarith [hθ.2]
    positivity
  have hδθ₁ : δθ ≤ θ - μ₁ := by
    rw [hδθdef]; linarith [min_le_left (θ - μ₁) (μ₂ - θ)]
  have hδθ₂ : δθ ≤ μ₂ - θ := by
    rw [hδθdef]; linarith [min_le_right (θ - μ₁) (μ₂ - θ)]
  -- the local parametrisation near `p₀ = rayPt θ R`
  obtain ⟨ε, hεpos, hloc⟩ :=
    exists_rayPt_local (c := c) (φ := φ) hN (θ₀ := θ) (t₀ := R) hR hδθ (by linarith : 0 < (R - 1) / 2)
  -- shrink the disc so that it misses `K c`
  have hp₀pot : Work.EL.pot hN (Work.EL.rayPt hN θ R) = Real.log R := Work.EL.pot_rayPt hN hR
  have hev : ∀ᶠ z in 𝓝 (Work.EL.rayPt hN θ R), Real.log R / 2 < Work.EL.pot hN z := by
    have hmem : Set.Ioi (Real.log R / 2) ∈ 𝓝 (Work.EL.pot hN (Work.EL.rayPt hN θ R)) := by
      apply IsOpen.mem_nhds isOpen_Ioi
      show Real.log R / 2 < Work.EL.pot hN (Work.EL.rayPt hN θ R)
      rw [hp₀pot]
      linarith [Real.log_pos hR]
    exact (hN.continuous_potential.continuousAt).eventually hmem
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.eventually_nhds_iff.mp hev
  set ε' : ℝ := min ε ε₁ with hε'def
  have hε'pos : 0 < ε' := lt_min hεpos hε₁pos
  have hε'le : ε' ≤ ε := min_le_left _ _
  set B : Set ℂ := Metric.ball (Work.EL.rayPt hN θ R) ε' with hBdef
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBK : B ⊆ (Work.EL.K c)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzK
    have h1 : Real.log R / 2 < Work.EL.pot hN z :=
      hε₁ (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _))
    rw [Work.EL.pot_of_mem hN hzK] at h1
    linarith [Real.log_pos hR]
  have hp₀B : Work.EL.rayPt hN θ R ∈ B := Metric.mem_ball_self hε'pos
  have hp₀C : Work.EL.rayPt hN θ R ∈ Work.EL.polyCurve ps R := by
    rw [rayPt_fract hN θ R, Work.EL.polyCurve]
    simp only [Set.mem_ofPred_eq]
    refine Or.inr ⟨Int.fract θ, ⟨Int.fract_nonneg θ, le_of_lt (Int.fract_lt_one θ)⟩, ?_, rfl⟩
    intro P hP
    have h := InArc_add_angle_int (Int.fract θ) P.a P.b ⌊θ⌋
    rw [Int.fract_add_floor] at h
    exact fun hin => hgap θ hθ P hP (h.mpr hin)
  -- the sector
  have hPconn : IsPreconnected (nearSector hN μ₁ μ₂ R) := isPreconnected_nearSector hN μ₁ μ₂ R
  have hPsub : nearSector hN μ₁ μ₂ R ⊆ (Work.EL.polyCurve ps R)ᶜ :=
    nearSector_subset_compl hN ps hR hgap hne
  have hPdisj : Disjoint (nearSector hN μ₁ μ₂ R) (Work.EL.polyCurve ps R) :=
    Set.disjoint_left.mpr fun z hz hzC => hPsub hz hzC
  -- the outer half
  have hQconn : IsPreconnected {z : ℂ | Real.log R < Work.EL.pot hN z} :=
    Work.Top.isPreconnected_gt_potential hN hR
  have hQdisj : Disjoint {z : ℂ | Real.log R < Work.EL.pot hN z} (Work.EL.polyCurve ps R) := by
    rw [Set.disjoint_left]
    intro z hz hzC
    have hle : Work.EL.pot hN z ≤ Real.log R := polyCurve_subset_pot_le hN ps hR hzC
    exact absurd hle (not_le.mpr hz)
  have hQz : ∃ z ∈ {z : ℂ | Real.log R < Work.EL.pot hN z}, z ∈ S.O := by
    have hlog1 : Real.log R < Real.log (R + 1) := Real.log_lt_log hRpos (by linarith)
    refine ⟨Work.EL.rayPt hN θ (R + 1), ?_, ?_⟩
    · show Real.log R < Work.EL.pot hN (Work.EL.rayPt hN θ (R + 1))
      rw [Work.EL.pot_rayPt hN (by linarith)]
      exact hlog1
    · refine gt_potential_subset_sidesO hN hJ ps hR hC ?_
      show Real.log R < Work.EL.pot hN (Work.EL.rayPt hN θ (R + 1))
      rw [Work.EL.pot_rayPt hN (by linarith)]
      exact hlog1
  -- the covering of the disc minus the curve
  have hcov : B \ Work.EL.polyCurve ps R ⊆
      nearSector hN μ₁ μ₂ R ∪ {z : ℂ | Real.log R < Work.EL.pot hN z} := by
    intro z hz
    obtain ⟨hzB, hzC⟩ := hz
    have hdist : ‖z - Work.EL.rayPt hN θ R‖ < ε := by
      rw [← dist_eq_norm]
      exact lt_of_lt_of_le (Metric.mem_ball.mp hzB) hε'le
    obtain ⟨θ', t', hθ', ht', rfl⟩ := hloc z (hBK hzB) hdist
    have hθ'gap : θ' ∈ Set.Ioo μ₁ μ₂ := by
      have := abs_lt.mp hθ'
      exact ⟨by linarith [this.1, hδθ₁], by linarith [this.2, hδθ₂]⟩
    have ht'1 : 1 < t' := by
      have := abs_lt.mp ht'
      linarith
    rcases lt_trichotomy t' R with hlt | heq | hgt
    · exact Or.inl ⟨(θ', t'), ⟨hθ'gap, ⟨ht'1, hlt⟩⟩, rfl⟩
    · exfalso
      apply hzC
      rw [← heq, rayPt_fract (hN := hN), Work.EL.polyCurve]
      simp only [Set.mem_ofPred_eq]
      refine Or.inr ⟨Int.fract θ', ⟨Int.fract_nonneg θ', le_of_lt (Int.fract_lt_one θ')⟩, ?_, rfl⟩
      intro P hP
      have h := InArc_add_angle_int (Int.fract θ') P.a P.b ⌊θ'⌋
      rw [Int.fract_add_floor] at h
      exact fun hin => hgap θ' hθ'gap P hP (h.mpr hin)
    · refine Or.inr ?_
      show Real.log R < Work.EL.pot hN (Work.EL.rayPt hN θ' t')
      rw [Work.EL.pot_rayPt hN ht'1]
      exact Real.log_lt_log (by linarith) hgt
  have hsubI : nearSector hN μ₁ μ₂ R ⊆ S.I :=
    S.sides_of_halves hBopen ⟨Work.EL.rayPt hN θ R, hp₀B, hp₀C⟩ hcov hPconn hQconn hPdisj
      hQdisj hQz
  exact hsubI ⟨(θ, t), ⟨hθ, ⟨ht1, ht2⟩⟩, rfl⟩

/-! ## The region is the bounded side -/

/-- **The region of a ray polygon is its bounded side.** -/
theorem polyRegion_eq_sides_I' {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) :
    Work.EL.polyRegion ps R = (Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC).I := by
  classical
  set S : Work.Top.Sides (Work.EL.polyCurve ps R) :=
    Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC with hSdef
  -- the angle of the reference point avoids the closed far arcs
  have harc : ∀ P ∈ ps, ¬ Work.EL.InClosedArc (Work.EL.midNear ps) P.a P.b := by
    intro P hP
    rw [not_InClosedArc_iff_not_InArc]
    exact ⟨notInArc_midNear ps hA P hP,
      fun k => midNear_ne_angle_add_int ps hA
        (List.mem_flatMap.mpr ⟨P, hP, by simp⟩) k,
      fun k => midNear_ne_angle_add_int ps hA
        (List.mem_flatMap.mpr ⟨P, hP, by simp⟩) k⟩
  obtain ⟨μ₁, μ₂, hμ₁, hμ₂, hgap, hne⟩ := exists_gap_of_notInClosedArc (hN := hN) ps harc
  -- the seed lies in the bounded side
  have hsqt1 : 1 < Real.sqrt R := (Real.lt_sqrt zero_le_one).mpr (by simpa using hR)
  have hsqt2 : Real.sqrt R < R := by
    have hsq := Real.sq_sqrt (le_of_lt (by linarith : (0:ℝ) < R))
    nlinarith
  have hseedI : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R) ∈ S.I :=
    rayPt_mem_sides_I_of_gap hN hJ ps hR hC ⟨hμ₁, hμ₂⟩ hgap hne hsqt1 hsqt2
  have hseedD : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R) ∈ Work.EL.polyRegion ps R :=
    seed_mem_polyRegion hN ps hA hR
  have hseedC : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R)
      ∈ (Work.EL.polyCurve ps R)ᶜ := Work.EL.polyRegion_subset_compl ps R hseedD
  have hreg_sub : Work.EL.polyRegion ps R ⊆ S.I := by
    rcases S.subset_of_preconnected (Work.EL.isPreconnected_polyRegion ps R)
      (Work.EL.polyRegion_subset_compl ps R) with h | h
    · exact h
    · exact absurd (h hseedD) (S.notMem_O_of_mem_I hseedI)
  have hI_sub : S.I ⊆ Work.EL.polyRegion ps R :=
    S.preconnected_I.subset_connectedComponentIn hseedI S.subset_compl_I
  exact Set.Subset.antisymm hreg_sub hI_sub

/-! ## The far arc lies in the unbounded side -/

/-- A ray point whose angle is congruent to no angle of the polygon and whose ray of angle `θ`
does not lie in any arc of the polygon is off the polygon curve. -/
theorem rayPt_notMem_polyCurve_of_far {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) {R θ : ℝ} (hR : 1 < R)
    (hne : ∀ P ∈ ps, ∀ k : ℤ, θ ≠ P.a + (k : ℝ) ∧ θ ≠ P.b + (k : ℝ))
    (hfar : ∃ P ∈ ps, Work.EL.InArc θ P.a P.b)
    {s : ℝ} (hs : 1 < s) :
    Work.EL.rayPt hN θ s ∉ Work.EL.polyCurve ps R := by
  intro hmem
  rw [Work.EL.polyCurve] at hmem
  simp only [Set.mem_ofPred_eq] at hmem
  -- the congruence of the angle of a ray point lying on a polygon ray
  have hcongr : ∀ {x : ℝ}, Work.EL.rayPt hN θ s ∈ Work.EL.paramRay hN x →
      ∃ k : ℤ, x = θ + (k : ℝ) := by
    intro x hx
    obtain ⟨-, t', ht', hΦ⟩ := hx
    have h1 : Work.Top.NakaneData.rayPoint θ s = Work.Top.NakaneData.rayPoint x t' := by
      rw [← Work.Top.NakaneData.Phi_rayPt hN hs, hΦ]
    have ht't : t' = s := by
      have h2 := congrArg norm h1
      rw [Work.Top.NakaneData.norm_rayPoint, Work.Top.NakaneData.norm_rayPoint] at h2
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at h2
      exact h2.symm
    rw [ht't] at h1
    exact rayPoint_angle_eq_int (by linarith) h1
  rcases hmem with ⟨P', hP', hy | hpa | hpb⟩ | ⟨θ', hθ', hfar', heq⟩
  · exact Work.EL.rayPt_notMem_K hN hs (hy ▸ landsN_mem_K hN P'.lands_a)
  · obtain ⟨k, hk⟩ := hcongr (Work.Top.NakaneData.rayPiece_subset_paramRay hpa)
    exact (hne P' hP' (-k)).1 (by rw [hk]; push_cast; ring)
  · obtain ⟨k, hk⟩ := hcongr (Work.Top.NakaneData.rayPiece_subset_paramRay hpb)
    exact (hne P' hP' (-k)).2 (by rw [hk]; push_cast; ring)
  · -- the equipotential part of the curve
    rcases lt_trichotomy s R with hlt | heq1 | hgt
    · have h1 : Work.EL.pot hN (Work.EL.rayPt hN θ s) = Real.log s := Work.EL.pot_rayPt hN hs
      have h2 : Work.EL.pot hN (Work.EL.rayPt hN θ' R) = Real.log R := Work.EL.pot_rayPt hN hR
      rw [heq] at h1
      have hlogs : Real.log s = Real.log R := h1.symm.trans h2
      have hsR : s = R :=
        Real.log_injOn_pos (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by linarith)) hlogs
      linarith
    · -- the two angles are congruent, and `θ` lies in the far arc
      have h1 : Work.Top.NakaneData.rayPoint θ s = Work.Top.NakaneData.rayPoint θ' R := by
        rw [← Work.Top.NakaneData.Phi_rayPt hN hs, ← Work.Top.NakaneData.Phi_rayPt hN hR]
        exact congrArg (Work.EL.dynPhi c φ) heq
      rw [heq1] at h1
      obtain ⟨k, hk⟩ := rayPoint_angle_eq_int hR h1
      obtain ⟨P, hP, harc⟩ := hfar
      refine hfar' P hP ?_
      rw [hk]
      exact (InArc_add_angle_int θ P.a P.b k).mpr harc
    · have h1 : Work.EL.pot hN (Work.EL.rayPt hN θ s) = Real.log s := Work.EL.pot_rayPt hN hs
      have h2 : Work.EL.pot hN (Work.EL.rayPt hN θ' R) = Real.log R := Work.EL.pot_rayPt hN hR
      rw [heq] at h1
      have hlogs : Real.log s = Real.log R := h1.symm.trans h2
      have hsR : s = R :=
        Real.log_injOn_pos (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by linarith)) hlogs
      linarith

/-- **A point whose angle lies in the open far arc of a pair of the polygon lies in the
unbounded side**: it escapes to infinity along its own ray, inside the complement of the curve. -/
theorem mem_sides_O_of_farArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) {z : ℂ}
    (hz : z ∉ Work.EL.K c) {P : Work.EL.CoPair hN} (hP : P ∈ ps)
    (harc : Work.EL.InArc (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) P.a P.b) :
    z ∈ (Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC).O := by
  classical
  set S : Work.Top.Sides (Work.EL.polyCurve ps R) :=
    Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC with hSdef
  set θ : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z with hθdef
  have hθarc : Work.EL.InArc θ P.a P.b := harc
  -- the two angles of the pair are ordered
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hP
  have hPlt : P.a < P.b := by
    have hdata := PolyCurve.cyclicStrict_angle_data ps (List.length_pos_iff.mpr hA.ne) hA.cyc
    simpa only [hi] using hdata.1 i
  -- write the angle as `P.a + k + f` with `f ∈ (0, arcLen P.a P.b)`
  set k : ℤ := ⌊θ - P.a⌋ with hkdef
  have hθsplit : θ - P.a = (k : ℝ) + Int.fract (θ - P.a) :=
    (Int.floor_add_fract (θ - P.a)).symm
  set x : ℝ := θ - (k : ℝ) with hxdef
  have hx_eq : x = P.a + Int.fract (θ - P.a) := by rw [hxdef]; linarith
  have hx1 : P.a < x := by rw [hx_eq]; linarith [hθarc.1]
  have hx2 : x < P.b := by
    have hlen : Work.EL.arcLen P.a P.b ≤ P.b - P.a := by
      have := midNear_fract_le_self (le_of_lt (by linarith : (0:ℝ) < P.b - P.a))
      simpa only [Work.EL.arcLen] using this
    rw [hx_eq]
    linarith [hθarc.2, hlen]
  -- the far arc contains no angle of the polygon
  have hnoangle : ∀ P' ∈ ps, ∀ j : ℤ, θ ≠ P'.a + (j : ℝ) ∧ θ ≠ P'.b + (j : ℝ) := by
    intro P' hP' j
    obtain ⟨h1, h2⟩ := farArc_no_angle ps hA i x (by rw [hi]; exact hx1) (by rw [hi]; exact hx2)
      P' hP' (j - k)
    constructor
    · intro hc
      exact h1 (by rw [hxdef, hc]; push_cast; ring)
    · intro hc
      exact h2 (by rw [hxdef, hc]; push_cast; ring)
  -- the escape along the ray of angle `θ`
  set T : Set ℂ := (fun s : ℝ => Work.EL.rayPt hN θ s) '' Set.Ici (Real.exp (Work.EL.pot hN z))
    with hTdef
  have hTsub : T ⊆ (Work.EL.polyCurve ps R)ᶜ := by
    rintro w ⟨s, hs, rfl⟩
    exact rayPt_notMem_polyCurve_of_far hN ps hR hnoangle ⟨P, hP, hθarc⟩
      (lt_of_lt_of_le (one_lt_exp_pot hN hz) hs)
  have hTconn : IsPreconnected T := by
    rw [hTdef]
    refine IsPreconnected.image isPreconnected_Ici _ ?_
    refine (Work.Top.continuousOn_rayPt hN θ).mono ?_
    intro s hs
    exact lt_of_lt_of_le (one_lt_exp_pot hN hz) hs
  have hunb : ∀ n : ℕ, ∃ w ∈ T, (n : ℝ) ≤ ‖w‖ := by
    intro n
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ c : ℂ, ‖c‖ ≤ max (n : ℝ) 1 → Work.EL.pot hN c ≤ M := by
      have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) (max (n : ℝ) 1) := by
        rw [Metric.mem_closedBall, dist_self]
        exact le_trans zero_le_one (le_max_right (n : ℝ) 1)
      obtain ⟨x₀, hx₀⟩ := (isCompact_closedBall (0 : ℂ) (max (n : ℝ) 1)).exists_isMaxOn
        (f := fun c : ℂ => Work.EL.pot hN c) ⟨0, h0⟩ hN.continuous_potential.continuousOn
      refine ⟨Work.EL.pot hN x₀, fun c hc => ?_⟩
      exact hx₀.2 (by rw [Metric.mem_closedBall, dist_zero_right]; exact hc)
    set s : ℝ := max (Real.exp (Work.EL.pot hN z)) (Real.exp M + 1) with hsdef
    refine ⟨Work.EL.rayPt hN θ s,
      ⟨s, (le_max_left (Real.exp (Work.EL.pot hN z)) (Real.exp M + 1)), rfl⟩, ?_⟩
    by_contra hcon
    rw [not_le] at hcon
    have hs1 : 1 < s := lt_of_lt_of_le (one_lt_exp_pot hN hz) (le_max_left _ _)
    have hle : Work.EL.pot hN (Work.EL.rayPt hN θ s) ≤ M :=
      hM _ (le_trans (le_of_lt hcon) (le_max_left _ _))
    rw [Work.EL.pot_rayPt hN hs1] at hle
    have hgt : M < Real.log s := by
      have hlt : Real.exp M < s := lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
      rw [← Real.log_exp M]
      exact Real.log_lt_log (Real.exp_pos M) hlt
    linarith
  have hzT : z ∈ T :=
    ⟨Real.exp (Work.EL.pot hN z), le_refl (Real.exp (Work.EL.pot hN z)),
      rayPt_extAngle_exp_pot hN hz⟩
  exact S.subset_O_of_unbounded hTconn hTsub hunb hzT

/-! ## The target theorem -/

/-- **The region of a ray polygon off the filled Julia set.**  For `z ∉ K c` the point `z` lies
in the region exactly when its external angle avoids every closed far arc `[P.a, P.b]` of the
polygon and its potential is below the level `log R` of the polygon. -/
theorem mem_polyRegion_iff_of_notMem_K {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R)) {z : ℂ}
    (hz : z ∉ Work.EL.K c) :
    z ∈ Work.EL.polyRegion ps R ↔
      (∀ P ∈ ps, ¬ Work.EL.InClosedArc (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) P.a P.b)
        ∧ Work.EL.pot hN z < Real.log R := by
  classical
  set S : Work.Top.Sides (Work.EL.polyCurve ps R) :=
    Work.Top.JordanForm.sides hJ (Work.EL.polyCurve ps R) hC with hSdef
  rw [polyRegion_eq_sides_I' hN hJ ps hA hR hC]
  constructor
  · intro hzI
    have hpot : Work.EL.pot hN z < Real.log R := sides_I_subset_pot_lt hN ps hR S hzI
    refine ⟨?_, hpot⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨P, hP, hParc⟩ := hcon
    by_cases harc : Work.EL.InArc (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z) P.a P.b
    · exact S.notMem_I_of_mem_O (mem_sides_O_of_farArc hN hJ ps hA hR hC hz hP harc) hzI
    · -- the angle is congruent to an endpoint: `z` lies on a ray piece
      have hcases : Int.fract (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - P.a) = 0 ∨
          Int.fract (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z - P.a) =
            Work.EL.arcLen P.a P.b := by
        rcases lt_or_eq_of_le hParc.1 with hpos | hzero
        · rcases lt_or_eq_of_le hParc.2 with hlt | heq
          · exact absurd ⟨hpos, hlt⟩ harc
          · exact Or.inr heq
        · exact Or.inl hzero.symm
      have hz_eq : z = Work.EL.rayPt hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z)
          (Real.exp (Work.EL.pot hN z)) := (rayPt_extAngle_exp_pot hN hz).symm
      have hray : z ∈ Work.EL.paramRay hN P.a ∨ z ∈ Work.EL.paramRay hN P.b := by
        rcases hcases with h0 | hlen
        · left
          obtain ⟨j, hj⟩ := Int.fract_eq_zero_iff.mp h0
          have hθj : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z = P.a + (j : ℝ) := by
            linarith
          rw [hz_eq, hθj, Work.ELTop.rayPt_add_int]
          exact Work.EL.rayPt_mem_paramRay hN (one_lt_exp_pot hN hz)
        · right
          obtain ⟨j, hj⟩ := Int.fract_eq_fract.mp hlen
          have hθj : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) z = P.b + (j : ℝ) := by
            linarith
          rw [hz_eq, hθj, Work.ELTop.rayPt_add_int]
          exact Work.EL.rayPt_mem_paramRay hN (one_lt_exp_pot hN hz)
      have hCmem : z ∈ Work.EL.polyCurve ps R := by
        rcases hray with hray | hray
        · exact Or.inl ⟨P, hP, Or.inr (Or.inl ((mem_rayPiece_iff hN P.a 0 R z).mpr
            ⟨hray, Work.EL.pot_nonneg hN z, le_of_lt hpot⟩))⟩
        · exact Or.inl ⟨P, hP, Or.inr (Or.inr ((mem_rayPiece_iff hN P.b 0 R z).mpr
            ⟨hray, Work.EL.pot_nonneg hN z, le_of_lt hpot⟩))⟩
      exact (S.subset_compl_I hzI) hCmem
  · rintro ⟨harc, hpot⟩
    obtain ⟨μ₁, μ₂, hμ₁, hμ₂, hgap, hne⟩ := exists_gap_of_notInClosedArc (hN := hN) ps harc
    have hmem := rayPt_mem_sides_I_of_gap hN hJ ps hR hC ⟨hμ₁, hμ₂⟩ hgap hne
      (one_lt_exp_pot hN hz) ((exp_pot_lt_iff hN hR hz).mpr hpot)
    rw [← rayPt_extAngle_exp_pot hN hz]
    exact hmem

end Work.ELTop
