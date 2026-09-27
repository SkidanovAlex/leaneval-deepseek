import Mathlib
import Submission.Work.Drive.cappingSpaceHomeoProj_confPiece
import Submission.Work.Drive.projRot
import Submission.Work.Drive.cappedPlaneDisjoint
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.sideOf_covariant
import Submission.Work.Drive.hcRotation

/-!
# The class datum of a configuration point: `(normalized midpoint, doubled direction) ↦ ℝP³`

The capping space is `CappingSpace ≃ₜ (0,∞) × ℝP³` (`Work.Drive.cappingSpaceHomeoProj`); its first
coordinate is the **level** `levelOf` and its second the **class** `cls`.  For a *configuration* point
(the datum `(midpoint, doubled direction, length)`) the class is computed by
`Work.Drive.cappingSpaceHomeoProj_confPiece_proj`:

`cls = [confProjVecOf u d]`,  `d = midpoint/‖(midpoint, length)‖`,  `u² = circleOf (doubled direction)`.

This file records the consequences that make every statement about a class image a statement about
chords:

* `Work.Drive.classOfConf` — the class as a function of the pair `(d, η)` (normalized midpoint,
  doubled direction), **independent of the level**;
* `Work.Drive.cls_confPiece_eq_classOfConf` — the bridge from the capping space to the dictionary
  (`cls = classOfConf ((confOf p).2.1) ((confOf p).2.2)`);
* `Work.Drive.classOfConf_eq_of_snd_eq` — **the class depends only on `(d, η)`**;
* `Work.Drive.projRot_classOfConf` — the rotation `projRot` acts on the dictionary by `η ↦ η + t`:
  it *shifts the doubled direction and preserves the normalized midpoint*;
* `Work.Drive.classOfConf_zero_midpoint_injective` — on the "axis" `d = 0` (configuration points whose
  midpoint is the origin) the class determines the doubled direction;
* `Work.Drive.disjoint_of_subset_cappedPlane` — **the geometric content of the profile route's
  non-vanishing hypothesis**: if a set of the capping space (e.g. the chart's plane) is contained in
  the proved capped plane `cappedPlane … 0`, then it is disjoint from each of its rotations
  `rotCapping t` with `t ∈ Zc γ`, by the proved `Work.Drive.cappedPlaneDisjoint`.

The last lemma is the reason for the file: it converts the profile route's design condition `hne`
("the profiles of the plane and of its rotation differ on the union of the two class images") into the
*set inclusion* "chart's plane ⊆ capped plane at `u = 0`", which is a property of the concrete chart
that can be checked clause by clause, while the disjointness itself is already proved for every smooth
`γ`.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff LinearAlgebra.Projectivization
open Set

noncomputable section

/-! ## The dictionary `(d, η) ↦ ℝP³` -/

/-- A chosen square root of `circleOf η` on the unit circle (`Work.Drive.exists_sq_circleOf`). -/
def classRoot (η : UnitAddCircle) : ℂ := (exists_sq_circleOf η).choose

lemma classRoot_norm (η : UnitAddCircle) : ‖classRoot η‖ = 1 :=
  (exists_sq_circleOf η).choose_spec.1

lemma classRoot_sq (η : UnitAddCircle) : classRoot η ^ 2 = circleOf η :=
  (exists_sq_circleOf η).choose_spec.2

lemma classRoot_ne_zero (η : UnitAddCircle) : classRoot η ≠ 0 :=
  fun h => by simpa [h] using classRoot_norm η

/-- **The class datum of a configuration point.**  The point of `ℝP³` attached to a normalized
midpoint `d` of the disk of the capping model and a doubled direction `η`. -/
def classOfConf (d : ℂ) (hd : ‖d‖ ≤ 1) (η : UnitAddCircle) : ℙ ℝ (Eucl 3) :=
  Projectivization.mk ℝ (confProjVecOf (classRoot η) d)
    (confProjVecOf_ne_zero (classRoot_norm η) hd)

lemma classOfConf_eq_mk (d : ℂ) (hd : ‖d‖ ≤ 1) (η : UnitAddCircle) :
    classOfConf d hd η
      = Projectivization.mk ℝ (confProjVecOf (classRoot η) d)
        (confProjVecOf_ne_zero (classRoot_norm η) hd) := rfl

/-- Two complex numbers with the same square are equal or opposite. -/
lemma classDatum_eq_or_eq_neg_of_sq_eq {u u' : ℂ} (h : u ^ 2 = u' ^ 2) : u = u' ∨ u = -u' := by
  have h1 : (u - u') * (u + u') = 0 := by linear_combination h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact Or.inl (sub_eq_zero.mp h2)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

/-- Negating the square root of `circleOf η` negates the vector `confProjVecOf · d`. -/
lemma classDatum_confProjVecOf_neg (u d : ℂ) : confProjVecOf (-u) d = -confProjVecOf u d := by
  conv_lhs => rw [← ofComplex_c₁_c₂ (confProjVecOf (-u) d)]
  conv_rhs => rw [← ofComplex_c₁_c₂ (confProjVecOf u d)]
  rw [show c₁ (confProjVecOf (-u) d) = -c₁ (confProjVecOf u d) by
        rw [c₁_confProjVecOf, c₁_confProjVecOf]; ring,
      show c₂ (confProjVecOf (-u) d) = -c₂ (confProjVecOf u d) by
        rw [c₂_confProjVecOf, c₂_confProjVecOf, star_neg]; ring]
  exact ofComplex_neg _ _

/-- **The bridge from the capping space to the dictionary.**  The class of a configuration point is
`classOfConf` of its normalized midpoint and doubled direction — *independently of the level*. -/
theorem cls_confPiece_eq_classOfConf (p : (ℝ × ℝ) × UnitAddCircle × ℝ)
    (h1 : 0 < (confOf p).1) (h2 : ‖(confOf p).2.1‖ ≤ 1) :
    (cappingSpaceHomeoProj
        (Quotient.mk'' (Sum.inl (confPiece p h1 h2) : ConfigPiece ⊕ CapPiece))).2
      = classOfConf ((confOf p).2.1) h2 ((confOf p).2.2) := by
  rw [classOfConf_eq_mk, cappingSpaceHomeoProj_confPiece_proj p h1 h2 (classRoot_sq ((confOf p).2.2))]

/-- **The class depends only on the normalized midpoint and the doubled direction.**  Two
configuration points with the same `(confOf ·).2` have the same class, whatever their levels. -/
theorem classOfConf_eq_of_snd_eq {p p' : (ℝ × ℝ) × UnitAddCircle × ℝ}
    (h1 : 0 < (confOf p).1) (h2 : ‖(confOf p).2.1‖ ≤ 1)
    (h1' : 0 < (confOf p').1) (h2' : ‖(confOf p').2.1‖ ≤ 1)
    (h : (confOf p).2 = (confOf p').2) :
    (cappingSpaceHomeoProj
        (Quotient.mk'' (Sum.inl (confPiece p h1 h2) : ConfigPiece ⊕ CapPiece))).2
      = (cappingSpaceHomeoProj
        (Quotient.mk'' (Sum.inl (confPiece p' h1' h2') : ConfigPiece ⊕ CapPiece))).2 := by
  obtain ⟨hd, hη⟩ := Prod.ext_iff.mp h
  rw [cls_confPiece_eq_classOfConf p h1 h2, cls_confPiece_eq_classOfConf p' h1' h2',
    classOfConf_eq_mk, classOfConf_eq_mk]
  refine (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul, hd, ← hη]

/-! ## The rotation in the dictionary -/

/-- **The rotation shifts the doubled direction.**  In the dictionary `(d, η) ↦ ℝP³` the rotation
`projRot t` of `ℝP³` acts by `(d, η) ↦ (d, η + t)`: it preserves the normalized midpoint and adds the
angle to the doubled direction. -/
theorem projRot_classOfConf (t : ℝ) (d : ℂ) (hd : ‖d‖ ≤ 1) (η : UnitAddCircle) :
    projRot t (classOfConf d hd η) = classOfConf d hd (η + ((t : ℝ) : UnitAddCircle)) := by
  rw [classOfConf_eq_mk, classOfConf_eq_mk,
    projRot_mk t (confProjVecOf (classRoot η) d) (confProjVecOf_ne_zero (classRoot_norm η) hd)]
  have hsq : classRoot (η + ((t : ℝ) : UnitAddCircle)) ^ 2 = (circ t * classRoot η) ^ 2 := by
    rw [classRoot_sq, mul_pow, classRoot_sq, circ_sq, ← circleOf_add, add_comm]
  rcases classDatum_eq_or_eq_neg_of_sq_eq hsq with h | h
  · refine (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨1, ?_⟩
    rw [one_smul, h, diagRot_confProjVecOf]
  · refine (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨(-1 : ℝ), ?_⟩
    rw [neg_one_smul, h, diagRot_confProjVecOf, classDatum_confProjVecOf_neg, neg_neg]

/-! ## The axis `d = 0` -/

/-- The first complex coordinate of `confProjVecOf u 0` is `u`. -/
lemma c₁_confProjVecOf_zero (u : ℂ) : c₁ (confProjVecOf u (0 : ℂ)) = u := by
  rw [c₁_confProjVecOf]; norm_num

/-- The second complex coordinate of `confProjVecOf u 0` vanishes. -/
lemma c₂_confProjVecOf_zero (u : ℂ) : c₂ (confProjVecOf u (0 : ℂ)) = 0 := by
  rw [c₂_confProjVecOf]; norm_num

/-- **On the axis the class determines the doubled direction.**  For configuration points whose
normalized midpoint is `0` (i.e. whose midpoint is the origin) the class is injective in the doubled
direction: `η ↦ classOfConf 0 · η` embeds the circle of directions into `ℝP³`. -/
theorem classOfConf_zero_midpoint_injective {η η' : UnitAddCircle}
    (h : classOfConf (0 : ℂ) (by simp) η = classOfConf (0 : ℂ) (by simp) η') : η = η' := by
  rw [classOfConf_eq_mk, classOfConf_eq_mk] at h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mp h
  have h1 : c₁ (confProjVecOf (classRoot η) (0 : ℂ))
      = (a : ℂ) * c₁ (confProjVecOf (classRoot η') (0 : ℂ)) := by
    rw [← c₁_smul, ha]
  rw [c₁_confProjVecOf_zero, c₁_confProjVecOf_zero] at h1
  have h2 : classRoot η = (a : ℂ) * classRoot η' := h1
  have ha2 : a ^ 2 = 1 := by
    have h3 : (1 : ℝ) = ‖(a : ℂ)‖ ^ 2 := by
      have h4 := congrArg norm h2
      rw [norm_mul, classRoot_norm, classRoot_norm, mul_one] at h4
      rw [← h4]
      norm_num
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal] at h3
    nlinarith
  have hsq : classRoot η ^ 2 = classRoot η' ^ 2 := by
    rw [h2, mul_pow,
      show (↑a : ℂ) ^ 2 = 1 by rw [← Complex.ofReal_pow, ha2, Complex.ofReal_one], one_mul]
  rw [classRoot_sq, classRoot_sq] at hsq
  exact circleOf_injective hsq

/-! ## The strip half of the containment `chart's plane ⊆ capped plane`

The `hne` input of the profile route is, on the overlap of the two class images, the disjointness of
the chart's plane and its rotation (`disjoint_of_subset_cappedPlane`, below).  The *set inclusion*
`Q '' closedBall 0 1 ⊆ cappedPlane r₀ ρ Ψ Θ μ 0` that feeds it splits into two halves: the strip half —
the chart's values on the annulus lie in the proved capped plane — which is a theorem, and the cap
half, which is a condition on the concrete construction.  This section proves the strip half. -/

/-- Configuration points with equal data have equal associated configuration pieces (the two side
conditions are irrelevant). -/
lemma classDatum_confPiece_congr {p p' : (ℝ × ℝ) × UnitAddCircle × ℝ} (h : p = p')
    (h1 : 0 < (confOf p).1) (h2 : ‖(confOf p).2.1‖ ≤ 1)
    (h1' : 0 < (confOf p').1) (h2' : ‖(confOf p').2.1‖ ≤ 1) :
    confPiece p h1 h2 = confPiece p' h1' h2' :=
  Subtype.ext (by rw [confPiece_val, confPiece_val, h])

/-- **The strip values of the chart lie in the capped plane.**  If `μ` is the configuration band of
`γ` (`hμ : μ q = muOrd γ q`), then the value of the strip chart at rotation `v` is a point of the
capped plane `cappedPlane r₀ ρ Ψ Θ μ v`: it is the rotation of the configuration point of a chord,
which is a point of `stripImage μ`. -/
theorem stripChart_mem_cappedPlane (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμ : ∀ x y : Circle, μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    {r₀ : ℝ} {ρ Ψ Θ : ℝ → ℝ} (v : UnitAddCircle) (w : EuclideanSpace ℝ (Fin 2)) :
    stripChart γ hγne v w ∈ cappedPlane r₀ ρ Ψ Θ μ v := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, (t : UnitAddCircle) = v := ⟨v.out, Quotient.out_eq v⟩
  set q : Circle × Circle := (Circle.exp (w 0), Circle.exp (w 1)) with hq
  have hq1 : q.1 = Circle.exp (w 0) := rfl
  have hq2 : q.2 = Circle.exp (w 1) := rfl
  have h1 : 0 < (confOf (Submission.Configuration.muOrd γ q)).1 := stripData_pos hγne w
  have h2 : ‖(confOf (Submission.Configuration.muOrd γ q)).2.1‖ ≤ 1 := confOf_snd_norm_le_one _
  have hstrip : stripChart γ hγne v w
      = rotCapping v (Quotient.mk'' (Sum.inl (confPiece (Submission.Configuration.muOrd γ q)
          h1 h2) : ConfigPiece ⊕ CapPiece)) := by
    rw [stripChart]
    exact (rotCapping_mk_inl v _).symm
  have hcon : ((Quotient.mk'' (Sum.inl (confPiece (μ q)
      (by rw [hμ]; exact h1) (by rw [hμ]; exact h2)) : ConfigPiece ⊕ CapPiece)) : CappingSpace)
      = ((Quotient.mk'' (Sum.inl (confPiece (Submission.Configuration.muOrd γ q)
          h1 h2) : ConfigPiece ⊕ CapPiece)) : CappingSpace) := by
    rw [classDatum_confPiece_congr (hμ q.1 q.2) (by rw [hμ]; exact h1) (by rw [hμ]; exact h2) h1 h2]
  have hmem : ((Quotient.mk'' (Sum.inl (confPiece (μ q)
      (by rw [hμ]; exact h1) (by rw [hμ]; exact h2)) : ConfigPiece ⊕ CapPiece)) : CappingSpace)
      ∈ stripImage μ :=
    mem_stripImage_iff.mpr ⟨q, (by rw [hμ]; exact h1), (by rw [hμ]; exact h2), rfl⟩
  refine ⟨_, Set.mem_union_left _ hmem, ?_⟩
  rw [hcon, hstrip]

/-! ## The non-vanishing hypothesis of the profile route, from the proved disjointness -/

/-- **The geometric content of the profile route's non-vanishing `hne`.**  If a set `K` of the capping
space — think of the chart's plane `Q '' closedBall 0 1` — is contained in the *proved* capped plane
`cappedPlane r₀ ρ Ψ Θ μ 0` (`Work.Drive.exists_strip_cap_disk`), then it is disjoint from each of its
rotations `rotCapping t '' K` at every collision-free angle `t ∈ Zc γ`, by the proved
`Work.Drive.cappedPlaneDisjoint`.  This turns the profile route's design condition "the profiles of
the plane and of its rotation differ on the union of the two class images" into the set inclusion
`K ⊆ cappedPlane … 0`, a property of the concrete chart. -/
theorem disjoint_of_subset_cappedPlane {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {ρ Ψ Θ : ℝ → ℝ} (hρc : Continuous ρ) (hΨc : Continuous Ψ) (hΘc : Continuous Θ)
    (hρpos : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΨper : ∀ t : ℝ, circleOf (Ψ (t + 2 * Real.pi)) = circleOf (Ψ t))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    {r₀ : ℝ} (hr₀pos : 0 < r₀) (hr₀ : ∀ t : ℝ, ρ t ≠ r₀)
    {K : Set CappingSpace} (hK : K ⊆ cappedPlane r₀ ρ Ψ Θ μ 0)
    {t : UnitAddCircle} (ht : t ∈ Zc γ) :
    Disjoint K (rotCapping t '' K) := by
  have hdisj := cappedPlaneDisjoint hγ hμne hμdiag hρc hΨc hΘc hρpos hpolar hΨper hΘper hΘclass
    hr₀pos hr₀ (u := 0) (v := t) (by simpa using ht)
  have hrot : rotCapping t '' K ⊆ cappedPlane r₀ ρ Ψ Θ μ t := by
    rintro y ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    simpa [cappedPlane, rotCapping_zero] using hK hx
  exact hdisj.mono hK hrot


/-! ## The overlap half of the separation, from the disjointness of the plane and its rotation

The profile route's non-vanishing input `hne u : ∀ q ∈ Y₀, FQ (projRot u q) ≠ FQ q` splits into the
*overlap* `q ∈ Y₀ ∩ projRot (-u) '' Y₀`, where both profiles are pinned, and the complement, where the
value of the extension is free.  On the overlap the condition is *exactly* the disjointness of the
plane and its rotation, and this section proves that:

* `Work.Drive.sep_of_disjoint_rot` — if `K` contains the chart's plane, `FQ` is pinned on the disk, and
  `K` is disjoint from its rotation by `-t`, then the two profiles differ at every pair of disk points
  whose classes differ by `projRot t` (this is the overlap half of `hne` for the angle `t`);
* `Work.Drive.sep_of_subset_cappedPlane` — the end-to-end form: the containment of the chart's plane in
  the proved capped plane, together with `t ∈ Zc γ`, gives the same conclusion (via the proved
  `cappedPlaneDisjoint` and `disjoint_of_subset_cappedPlane`, using `Zc γ = -Zc γ`).

Hence the *only* part of `hne` that is not a consequence of the proved disjointness is the
*off-overlap* one (the choice of the extension off the pinned class image), exactly as recorded in
`CLASS_DATUM_STATUS.md` §2bis. -/

/-- **The overlap half of the separation, from the disjointness of the plane and its rotation.**  If the
level profile `FQ` is pinned on the chart's disk, and the set `K` containing the chart's plane is
disjoint from its rotation by `-t`, then two disk points whose classes differ by `projRot t` have
different profile values. -/
theorem sep_of_disjoint_rot {Q : ℂ → CappingSpace} {K : Set CappingSpace}
    (hKmem : ∀ z : ℂ, ‖z‖ ≤ 1 → Q z ∈ K)
    (FQ : Projectivization ℝ (Eucl 3) → ℝ)
    (hFQval : ∀ z : ℂ, ‖z‖ ≤ 1 → FQ ((cappingSpaceHomeoProj (Q z)).2) = levelOf (Q z))
    (t : ℝ) (hdisj : Disjoint K (rotCapping (((-t : ℝ)) : UnitAddCircle) '' K))
    {z z' : ℂ} (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1)
    (hcls : (cappingSpaceHomeoProj (Q z')).2 = projRot t ((cappingSpaceHomeoProj (Q z)).2)) :
    FQ ((cappingSpaceHomeoProj (Q z')).2) ≠ FQ ((cappingSpaceHomeoProj (Q z)).2) := by
  intro hEq
  have hlev : levelOf (Q z') = levelOf (Q z) := by
    rw [← hFQval z' hz', ← hFQval z hz, hEq]
  have heq : rotCapping (((-t : ℝ)) : UnitAddCircle) (Q z') = Q z := by
    apply cappingSpaceHomeoProj.injective
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      show levelOf (rotCapping (((-t : ℝ)) : UnitAddCircle) (Q z')) = levelOf (Q z)
      rw [sna_levelOf_rotCapping]
      exact hlev
    · rw [sna_cls_rotCapping, hcls, ← projRot_add_apply, neg_add_cancel, projRot_zero_apply]
  exact (Set.disjoint_left.mp hdisj (hKmem z hz)) ⟨Q z', hKmem z' hz', heq⟩

/-- **The overlap half of the separation, in the end-to-end form.**  If the chart's plane is contained in
the proved capped plane `cappedPlane r₀ ρ Ψ Θ μ 0` and `t ∈ Zc γ`, then the profile values at two disk
points whose classes differ by `projRot t` differ. -/
theorem sep_of_subset_cappedPlane {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {ρ Ψ Θ : ℝ → ℝ} (hρc : Continuous ρ) (hΨc : Continuous Ψ) (hΘc : Continuous Θ)
    (hρpos : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΨper : ∀ t : ℝ, circleOf (Ψ (t + 2 * Real.pi)) = circleOf (Ψ t))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    {r₀ : ℝ} (hr₀pos : 0 < r₀) (hr₀ : ∀ t : ℝ, ρ t ≠ r₀)
    {Q : ℂ → CappingSpace}
    (hsub : Q '' Metric.closedBall (0 : ℂ) 1 ⊆ cappedPlane r₀ ρ Ψ Θ μ 0)
    (FQ : Projectivization ℝ (Eucl 3) → ℝ)
    (hFQval : ∀ z : ℂ, ‖z‖ ≤ 1 → FQ ((cappingSpaceHomeoProj (Q z)).2) = levelOf (Q z))
    {t : ℝ} (ht : ((t : ℝ) : UnitAddCircle) ∈ Zc γ)
    {z z' : ℂ} (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1)
    (hcls : (cappingSpaceHomeoProj (Q z')).2 = projRot t ((cappingSpaceHomeoProj (Q z)).2)) :
    FQ ((cappingSpaceHomeoProj (Q z')).2) ≠ FQ ((cappingSpaceHomeoProj (Q z)).2) := by
  have hdisj := disjoint_of_subset_cappedPlane hγ hμne hμdiag hρc hΨc hΘc hρpos hpolar hΨper hΘper
    hΘclass hr₀pos hr₀ hsub (neg_mem_Zc ht)
  exact sep_of_disjoint_rot (K := Q '' Metric.closedBall (0 : ℂ) 1)
    (fun z hz => ⟨z, by simpa [Metric.mem_closedBall, dist_eq_norm] using hz, rfl⟩)
    FQ hFQval t (by simpa using hdisj) hz hz' hcls

/-! ## The strip chart of the band, in the dictionary -/

/-- `classOfConf` does not depend on the proof of the disk condition. -/
lemma classOfConf_congr_proof (d : ℂ) (hd hd' : ‖d‖ ≤ 1) (η : UnitAddCircle) :
    classOfConf d hd η = classOfConf d hd' η := by
  refine (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨1, ?_⟩
  rw [one_smul]

/-- **The strip chart of the band, in the dictionary.**  `stripChart γ hγne v w` is the configuration
point of the chord with parameters `(w 0, w 1)` rotated by `v`; in the dictionary of
`(normalized midpoint, doubled direction)` its class is therefore the class datum of the chord's
normalized midpoint and of the *shifted* doubled direction `(confOf (muOrd γ …)).2.2 + v`.  At `v = 0`
this says that the class image of the strip chart is the set of classes of the chords of `γ`. -/
theorem cls_stripChart (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (v : UnitAddCircle) (w : EuclideanSpace ℝ (Fin 2)) :
    (cappingSpaceHomeoProj (stripChart γ hγne v w)).2
      = classOfConf ((confOf (Submission.Configuration.muOrd γ
            (Circle.exp (w 0), Circle.exp (w 1)))).2.1)
          (confOf_snd_norm_le_one _)
          ((confOf (Submission.Configuration.muOrd γ
            (Circle.exp (w 0), Circle.exp (w 1)))).2.2 + v) := by
  have h1 : 0 < (confOf (Submission.Configuration.muOrd γ
      (Circle.exp (w 0), Circle.exp (w 1)))).1 := stripData_pos hγne w
  have h2 : ‖(confOf (Submission.Configuration.muOrd γ
      (Circle.exp (w 0), Circle.exp (w 1)))).2.1‖ ≤ 1 := confOf_snd_norm_le_one _
  obtain ⟨t, ht⟩ : ∃ t : ℝ, (t : UnitAddCircle) = v := ⟨v.out, Quotient.out_eq v⟩
  have hstrip : stripChart γ hγne v w
      = rotCapping v (Quotient.mk'' (Sum.inl (confPiece (Submission.Configuration.muOrd γ
          (Circle.exp (w 0), Circle.exp (w 1))) h1 h2) : ConfigPiece ⊕ CapPiece)) := by
    rw [stripChart]
    exact (rotCapping_mk_inl v _).symm
  rw [hstrip, show v = ((t : ℝ) : UnitAddCircle) from ht.symm, cls_rotCapping_coe t,
    cls_confPiece_eq_classOfConf _ h1 h2, projRot_classOfConf]

/-- The `v = 0` case: the class image of the strip chart is the set of classes of the chords of `γ`. -/
theorem cls_stripChart_zero (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (w : EuclideanSpace ℝ (Fin 2)) :
    (cappingSpaceHomeoProj (stripChart γ hγne 0 w)).2
      = classOfConf ((confOf (Submission.Configuration.muOrd γ
            (Circle.exp (w 0), Circle.exp (w 1)))).2.1)
          (confOf_snd_norm_le_one _)
          ((confOf (Submission.Configuration.muOrd γ
            (Circle.exp (w 0), Circle.exp (w 1)))).2.2) := by
  simpa using cls_stripChart γ hγne 0 w

end

end Work.Drive
