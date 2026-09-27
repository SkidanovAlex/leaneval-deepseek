import Mathlib
import Submission.Work.Drive.cappedPlaneFamily
import Submission.Work.Drive.capDisks_disjoint

/-!
# Stage 2, item 1: the capped planes `P_u = u·M ∪ cap_u` are pairwise disjoint

`Work.Drive.exists_strip_cap_disk` supplies the capped plane `P_u = u·M ∪ cap_u` of the configuration
strip of `γ` at the boundary level, and `Work.Drive.cappedPlane` records it as a subset of the capping
space.  Hugelmeyer's Theorem 2 is applied to a *pairwise disjoint* family of projective planes, and the
present file proves the disjointness

`v - u ∈ Zc γ → Disjoint (P_u) (P_v)`,

i.e. the hypothesis of Theorem 2.

The capped plane is the union of two pieces in `CappingSpace`: the image `M = stripImage μ` of the
configuration strip and the image `cap = mk '' (inr '' capCone …)` of the cap disk.  The two pieces are
glued along the boundary circle `∂M = ∂cap`, and the intersections split accordingly:

* `M ∩ w·M = ∅` for `w ∈ Zc γ` — this is the proved `Work.Drive.disjoint_stripImage_rot`;
* `cap ∩ w·cap = ∅` for `w ≠ 0` — `Work.Drive.capDisks_disjoint` (the norm of the third coordinate
  reads off the cone parameter `s`), transferred through `Work.Drive.cappingRel_inr_inr`;
* `M ∩ w·cap = ∅` and `cap ∩ w·M = ∅` for `w ∈ Zc γ` — the mixed cases.  The intersection of a
  configuration class with a cap class is always a *boundary* point of both pieces
  (`Work.Drive.norm_thd_eq_one_of_mk_inl_eq_mk_inr`, `Work.Drive.norm_snd_eq_one_of_mk_inr_eq_mk_inl`);
  for the cap side this forces the cone parameter `s = 1` (`capCone_eq_capBdy_of_norm_eq_one`), for the
  configuration side the length to vanish (`len_eq_zero_of_norm_confOf_snd_eq_one`), so both points are
  on the glued boundary circle of the strip.  Rotating that circle back by `w` gives a point of
  `M ∩ w·M` (via `Work.Drive.mk_confBdy_eq_mk_capBdy` and the class relation
  `Θ = doubled tangent - 2·Ψ`), which is empty.  The computation uses the injectivity of `γ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Work.Drive

open scoped Topology
open Manifold
open scoped Manifold ContDiff
open Submission.Collision (dirC)
open Submission.Geometry (eucNorm eucNorm_pos)

/-! ## Elementary facts -/

/-- **The curve misses the origin** as soon as it is the polar lift of a positive radial function. -/
lemma gamma_ne_zero_of_polarLift {γ : Circle → ℝ × ℝ} {ρ Ψ : ℝ → ℝ}
    (hρpos : ∀ t : ℝ, 0 < ρ t) (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t)) :
    ∀ x : Circle, γ x ≠ 0 := by
  intro x
  obtain ⟨t, ht⟩ := Circle.exp_surjective x
  rw [← ht, ← hpolar t]
  exact polarLift_ne_zero (hρpos t)

/-- **A configuration point whose normalised midpoint-length vector has norm one has zero length.**
The norm of the disk coordinate of `confOf (m, η, ℓ)` is
`√(m.1² + m.2²) / √(m.1² + m.2² + ℓ²)`, so it is `1` only for `ℓ = 0`. -/
lemma len_eq_zero_of_norm_confOf_snd_eq_one {m : ℝ × ℝ} {η : UnitAddCircle} {ℓ : ℝ}
    (h : ‖(confOf (m, η, ℓ)).2.1‖ = 1) : ℓ = 0 := by
  set r : ℝ := Real.sqrt (m.1 ^ 2 + m.2 ^ 2 + ℓ ^ 2) with hr
  have hr2 : r ^ 2 = m.1 ^ 2 + m.2 ^ 2 + ℓ ^ 2 := Real.sq_sqrt (by positivity)
  have hzn : ‖(confOf (m, η, ℓ)).2.1‖ ^ 2 = 1 := by rw [h]; norm_num
  have h1 : ‖(confOf (m, η, ℓ)).2.1‖ ^ 2 = (m.1 ^ 2 + m.2 ^ 2) * (r ^ 2)⁻¹ := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [confOf, ← hr]
    rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow]
    ring
  have h2 : (m.1 ^ 2 + m.2 ^ 2) * (r ^ 2)⁻¹ = 1 := by rw [← h1]; exact hzn
  have h3 : m.1 ^ 2 + m.2 ^ 2 = r ^ 2 := by
    rcases eq_or_ne (r ^ 2) 0 with h0 | h0
    · rw [h0, inv_zero, mul_zero] at h2
      exact absurd h2 (by norm_num)
    · calc m.1 ^ 2 + m.2 ^ 2 = (m.1 ^ 2 + m.2 ^ 2) * (r ^ 2)⁻¹ * r ^ 2 := by
            rw [mul_assoc, inv_mul_cancel₀ h0, mul_one]
        _ = 1 * r ^ 2 := by rw [h2]
        _ = r ^ 2 := one_mul _
  have : ℓ ^ 2 = 0 := by nlinarith [hr2, h3]
  exact sq_eq_zero_iff.mp this

/-- **The cap cone point of norm-one disk coordinate is a boundary cap point.**  A point of
`capCone r₀ ρ Ψ Θ 0` whose disk coordinate has norm one comes from the parameter `s = 1`, hence is the
cap boundary point `capBdy (ρ t) (Θ t) (Ψ t)` for some `t`. -/
lemma capCone_eq_capBdy_of_norm_eq_one {r₀ : ℝ} {ρ Ψ Θ : ℝ → ℝ} {hρpos : ∀ t : ℝ, 0 < ρ t}
    {q : CapPiece} (hq : q ∈ capCone r₀ ρ Ψ Θ 0) (h : ‖q.1.2.2‖ = 1) :
    ∃ t : ℝ, q = capBdy (ρ t) (hρpos t) (Θ t) (Ψ t) := by
  obtain ⟨s, t, hs, hval⟩ := hq
  have h3 : q.1.2.2 = (s : ℂ) * circleOf ((Ψ t : ℝ) : UnitAddCircle) :=
    congrArg (fun z : ℝ × UnitAddCircle × ℂ => z.2.2) hval
  have hs1 : s = 1 := by
    have : ‖(s : ℂ) * circleOf ((Ψ t : ℝ) : UnitAddCircle)‖ = 1 := by rw [← h3]; exact h
    rwa [norm_mul, norm_circleOf, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs.1] at this
  have hq1 : q.1.1 = ρ t := by
    have h' := congrArg (fun z : ℝ × UnitAddCircle × ℂ => z.1) hval
    simpa [hs1] using h'
  have hq2 : q.1.2.1 = ((Θ t : ℝ) : UnitAddCircle) := by
    have h' := congrArg (fun z : ℝ × UnitAddCircle × ℂ => z.2.1) hval
    have hcast : (((Θ 0 + 1 * (Θ t - Θ 0) : ℝ)) : UnitAddCircle)
        = ((Θ t : ℝ) : UnitAddCircle) := by
      rw [show Θ 0 + 1 * (Θ t - Θ 0) = Θ t by ring]
    simpa [hs1, hcast] using h'
  have hq3 : q.1.2.2 = circleOf ((Ψ t : ℝ) : UnitAddCircle) := by
    rw [h3, hs1]; simp
  refine ⟨t, ?_⟩
  refine Subtype.ext (Prod.ext hq1 (Prod.ext hq2 hq3))

/-- **The polar lift is recovered from the diagonal capping coordinates.**  If the capping coordinates
of the length-zero configuration point `(m, η, 0)` are `(r, circleOf ψ, η)` with `r > 0`, then
`m = polarLift (r, ψ)`.  (Both points have the same `confOf` and `confOf` is injective on non-negative
lengths.) -/
lemma polarLift_eq_of_confOf_diag {m : ℝ × ℝ} {η : UnitAddCircle} {r ψ : ℝ} (hrpos : 0 < r)
    (h : confOf (m, η, 0) = (r, circleOf ((ψ : ℝ) : UnitAddCircle), η)) :
    polarLift (r, ψ) = m := by
  have h1 : confOf (polarLift (r, ψ), η, 0) = (r, circleOf ((ψ : ℝ) : UnitAddCircle), η) :=
    confOf_eq_of_polarLift hrpos rfl η
  have heq : (polarLift (r, ψ), η, (0 : ℝ)) = (m, η, 0) :=
    confOf_injective_of_nonneg (le_refl 0) (le_refl 0) (h1.trans h.symm)
  exact congrArg Prod.fst heq

/-! ## The rotation maps on the boundary parametrisations -/

@[simp] lemma rotCap_capBdy (v : UnitAddCircle) (r : ℝ) (hr : 0 < r) (θ φ : UnitAddCircle) :
    rotCap v (capBdy r hr θ φ) = capBdy r hr (θ + v) φ := rfl

@[simp] lemma rotConfig_confBdy (v : UnitAddCircle) (r : ℝ) (hr : 0 < r) (φ η : UnitAddCircle) :
    rotConfig v (confBdy r hr φ η) = confBdy r hr φ (η + v) := rfl

/-- Membership in the image of the cap cone in the capping space. -/
lemma mem_capConeImage_iff {r₀ : ℝ} {ρ Ψ Θ : ℝ → ℝ} {p : CappingSpace} :
    p ∈ (Quotient.mk'' '' (Sum.inr '' capCone r₀ ρ Ψ Θ 0)) ↔
      ∃ q ∈ capCone r₀ ρ Ψ Θ 0, p = Quotient.mk'' (Sum.inr q) := by
  constructor
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨Sum.inr q, ⟨q, hq, rfl⟩, rfl⟩

/-- `Zc γ` does not contain `0`. -/
lemma ne_zero_of_mem_Zc {γ : Circle → ℝ × ℝ} {w : UnitAddCircle} (hw : w ∈ Zc γ) : w ≠ 0 :=
  fun h0 => zero_notMem_Zc γ (h0 ▸ hw)

/-! ## The glued boundary circle of the strip and the cap -/

/-- **The boundary cap point at parameter `t` is a point of the strip.**  The diagonal point
`(γ (exp t), tangentDirC γ (exp t), 0)` of the configuration strip has capping coordinates
`(ρ t, circleOf (Ψ t), tangentDirC γ (exp t))`, i.e. it is the configuration boundary point
`confBdy (ρ t) (Ψ t) (Θ t + 2·Ψ t)`; by the gluing `mk_confBdy_eq_mk_capBdy` its class in the capping
space is the cap boundary point `capBdy (ρ t) (Θ t) (Ψ t)`. -/
lemma mk_capBdy_mem_stripImage {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {ρ Ψ Θ : ℝ → ℝ} (hρpos : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    (t : ℝ) (hr : 0 < ρ t) :
    (Quotient.mk'' (Sum.inr (capBdy (ρ t) hr (Θ t) (Ψ t)) : ConfigPiece ⊕ CapPiece)
      : CappingSpace) ∈ stripImage μ := by
  have hconf : confOf (μ (Circle.exp t, Circle.exp t))
      = (ρ t, circleOf ((Ψ t : ℝ) : UnitAddCircle), tangentDirC γ (Circle.exp t)) := by
    rw [hμdiag (Circle.exp t),
      confOf_eq_of_polarLift (hρpos t) (hpolar t) (tangentDirC γ (Circle.exp t))]
  have h1 : 0 < (confOf (μ (Circle.exp t, Circle.exp t))).1 := by rw [hconf]; exact hρpos t
  have h2 : ‖(confOf (μ (Circle.exp t, Circle.exp t))).2.1‖ ≤ 1 := confOf_snd_norm_le_one _
  refine ⟨(Circle.exp t, Circle.exp t), h1, h2, ?_⟩
  have hval : (confPiece (μ (Circle.exp t, Circle.exp t)) h1 h2 : ℝ × ℂ × UnitAddCircle)
      = (confBdy (ρ t) hr (Ψ t) (Θ t + 2 • (Ψ t)) : ℝ × ℂ × UnitAddCircle) := by
    rw [confPiece_val, confBdy_val, hconf]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    rw [hΘclass t]
    abel
  rw [show (Quotient.mk'' (Sum.inl (confPiece (μ (Circle.exp t, Circle.exp t)) h1 h2)
        : ConfigPiece ⊕ CapPiece) : CappingSpace)
      = Quotient.mk'' (Sum.inl (confBdy (ρ t) hr (Ψ t) (Θ t + 2 • (Ψ t)))
        : ConfigPiece ⊕ CapPiece) from
    congrArg (fun z => (Quotient.mk'' (Sum.inl z) : CappingSpace)) (Subtype.ext hval)]
  exact (mk_confBdy_eq_mk_capBdy (ρ t) hr (Θ t) (Ψ t)).symm

/-! ## The mixed intersections `M ∩ w·cap` and `cap ∩ w·M` -/

open Manifold in
open scoped Manifold ContDiff in
/-- **The configuration strip does not meet the rotated cap disk** (`M ∩ w·cap = ∅` for `w ∈ Zc γ`).
A point of both is at once a configuration class and a cap class, hence lies on the glued boundary
circle: the cap parameter is `s = 1`, and rotating back by `w` puts the point in `w·M`, so the point is
in `M ∩ w·M`, which is empty by `disjoint_stripImage_rot`. -/
theorem disjoint_stripImage_capConeImage_rot {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {ρ Ψ Θ : ℝ → ℝ} (hρpos : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    {r₀ : ℝ} {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    Disjoint (stripImage μ)
      (rotCapping w '' (Quotient.mk'' '' (Sum.inr '' capCone r₀ ρ Ψ Θ 0))) := by
  rw [Set.disjoint_left]
  intro p hpM hpC
  rw [Set.mem_image] at hpC
  obtain ⟨s, hs, hsp⟩ := hpC
  obtain ⟨q, hq, rfl⟩ := mem_capConeImage_iff.mp hs
  rw [rotCapping_mk, rotSum_inr] at hsp
  obtain ⟨q', h1', h2', rfl⟩ := mem_stripImage_iff.mp hpM
  have hnorm : ‖(rotCap w q).1.2.2‖ = 1 :=
    norm_thd_eq_one_of_mk_inl_eq_mk_inr (p := confPiece (μ q') h1' h2')
      (q := rotCap w q) hsp.symm
  have hnormq : ‖q.1.2.2‖ = 1 := by simpa [rotCap] using hnorm
  obtain ⟨t, ht⟩ := capCone_eq_capBdy_of_norm_eq_one hq hnormq
  have hmem : (Quotient.mk'' (Sum.inr (capBdy (ρ t) (hρpos t) (Θ t) (Ψ t)))
      : CappingSpace) ∈ stripImage μ :=
    mk_capBdy_mem_stripImage hμdiag hρpos hpolar hΘclass t (hρpos t)
  exact (Set.disjoint_left.mp (disjoint_stripImage_rot hγ hμne hμdiag hw)
      (mem_stripImage_iff.mpr ⟨q', h1', h2', rfl⟩))
    ⟨_, hmem, by rw [rotCapping_mk, rotSum_inr, ← ht]; exact hsp⟩

open Manifold in
open scoped Manifold ContDiff in
/-- **The cap disk does not meet the rotated configuration strip** (`cap ∩ w·M = ∅` for `w ∈ Zc γ`).
A point of both lies on the glued boundary circle: the configuration point is a diagonal point of the
strip, so rotating it back by `w` gives a point of `w·M` that is also on the cap, and comparing the two
descriptions of the cap parameter gives `w = 0`, excluded by `0 ∉ Zc γ`. -/
theorem disjoint_capConeImage_rot_stripImage {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {ρ Ψ Θ : ℝ → ℝ} (hρpos : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    {r₀ : ℝ} {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    Disjoint (Quotient.mk'' '' (Sum.inr '' capCone r₀ ρ Ψ Θ 0))
      (rotCapping w '' stripImage μ) := by
  rw [Set.disjoint_left]
  intro p hpC hpM
  obtain ⟨q, hq, rfl⟩ := mem_capConeImage_iff.mp hpC
  rw [Set.mem_image] at hpM
  obtain ⟨s, hs, hsp⟩ := hpM
  obtain ⟨⟨a, b⟩, h1, h2, hsq⟩ := mem_stripImage_iff.mp hs
  rw [hsq, rotCapping_mk, rotSum_inl] at hsp
  have hnorm : ‖(rotConfig w (confPiece (μ (a, b)) h1 h2)).1.2.1‖ = 1 :=
    norm_snd_eq_one_of_mk_inr_eq_mk_inl hsp.symm
  have hnorm' : ‖(confOf (μ (a, b))).2.1‖ = 1 := by
    simpa [rotConfig, confPiece_val] using hnorm
  have hlen : (μ (a, b)).2.2 = 0 := len_eq_zero_of_norm_confOf_snd_eq_one hnorm'
  have hinj : Function.Injective γ := hγ.isEmbedding.injective
  have hab : a = b := by
    rcases eq_or_ne a b with h | h
    · exact h
    · exfalso
      have hzero : eucNorm (γ a - γ b) = 0 := by
        rw [hμne a b h] at hlen
        simpa [Submission.Configuration.muOrd] using hlen
      have hne : γ a - γ b ≠ 0 := fun h0 => h (hinj (sub_eq_zero.mp h0))
      linarith [eucNorm_pos hne, hzero]
  have hμab : μ (a, b) = (γ a, tangentDirC γ a, 0) := by
    rw [← hab, hμdiag a]
  have hγa : γ a ≠ 0 := gamma_ne_zero_of_polarLift hρpos hpolar a
  obtain ⟨φ, hφ⟩ := confOf_diag_eq_confBdy hγa (tangentDirC γ a)
  set r : ℝ := Real.sqrt ((γ a).1 ^ 2 + (γ a).2 ^ 2) with hr
  have hconf : confOf (μ (a, b)) = (r, circleOf φ, tangentDirC γ a) := by
    rw [hμab]
    exact hφ
  have hrpos : 0 < r := by
    have := h1
    rw [hconf] at this
    exact this
  have hp0 : confPiece (μ (a, b)) h1 h2 = confBdy r hrpos φ (tangentDirC γ a) := by
    refine Subtype.ext ?_
    rw [confPiece_val, confBdy_val]
    exact hconf
  have hbdy : (Quotient.mk'' (Sum.inl (confBdy r hrpos φ (tangentDirC γ a + w)))
        : CappingSpace)
      = (Quotient.mk'' (Sum.inl (rotConfig w (confPiece (μ (a, b)) h1 h2)))
        : CappingSpace) := by
    rw [hp0, rotConfig_confBdy]
  have hcap : (Quotient.mk'' (Sum.inr (capBdy r hrpos (tangentDirC γ a + w - 2 • φ) φ))
        : CappingSpace)
      = (Quotient.mk'' (Sum.inl (confBdy r hrpos φ (tangentDirC γ a + w)))
        : CappingSpace) := by
    have hh := (mk_confBdy_eq_mk_capBdy r hrpos (tangentDirC γ a + w - 2 • φ) φ).symm
    rw [show tangentDirC γ a + w - 2 • φ + 2 • φ = tangentDirC γ a + w by abel] at hh
    exact hh
  have hqeq : (Quotient.mk'' (Sum.inr (capBdy r hrpos (tangentDirC γ a + w - 2 • φ) φ))
        : CappingSpace) = Quotient.mk'' (Sum.inr q) := (hcap.trans hbdy).trans hsp
  have hq_eq : q = capBdy r hrpos (tangentDirC γ a + w - 2 • φ) φ :=
    (cappingRel_inr_inr.mp (Quotient.exact hqeq)).symm
  have hnormq : ‖q.1.2.2‖ = 1 := by rw [hq_eq, capBdy_val, norm_circleOf]
  obtain ⟨t, ht⟩ := capCone_eq_capBdy_of_norm_eq_one hq hnormq
  have hcapBdy_eq : capBdy r hrpos (tangentDirC γ a + w - 2 • φ) φ
      = capBdy (ρ t) (hρpos t) (Θ t) (Ψ t) := hq_eq.symm.trans ht
  obtain ⟨hrr, hθθ, hφφ⟩ := capBdy_inj hcapBdy_eq
  -- `γ a = polarLift (ρ t, Ψ t) = γ (exp t)`
  have hdiag : confOf (γ a, tangentDirC γ a, 0)
      = (r, circleOf ((Ψ t : ℝ) : UnitAddCircle), tangentDirC γ a) := by
    rw [hφ, hφφ]
  have hpol : polarLift (r, Ψ t) = γ a := polarLift_eq_of_confOf_diag hrpos hdiag
  have hγa_eq : γ a = γ (Circle.exp t) := by rw [← hpol, hrr, hpolar t]
  have hae : a = Circle.exp t := hinj hγa_eq
  have hfinal : w = 0 := by
    have h1' : tangentDirC γ a + w - 2 • φ = ((Θ t : ℝ) : UnitAddCircle) := hθθ
    rw [hae, hΘclass t, hφφ] at h1'
    have h4 : (tangentDirC γ (Circle.exp t) + w) + (- (2 • ((Ψ t : ℝ) : UnitAddCircle)))
        = tangentDirC γ (Circle.exp t) + (- (2 • ((Ψ t : ℝ) : UnitAddCircle))) := by
      simpa [sub_eq_add_neg] using h1'
    have h5 : tangentDirC γ (Circle.exp t) + w = tangentDirC γ (Circle.exp t) + 0 := by
      simpa using add_right_cancel h4
    simpa using add_left_cancel h5
  exact ne_zero_of_mem_Zc hw hfinal

/-! ## The cap against the rotated cap -/

open Manifold in
open scoped Manifold ContDiff in
/-- **The cap disks are pairwise disjoint as the rotation varies** (`cap ∩ w·cap = ∅` for `w ≠ 0`).
The norm of the third coordinate reads off the cone parameter `s`, so a coincidence of a point of
`cap` with a point of `w·cap` is exactly the hypothesis of `Work.Drive.capDisks_disjoint`, which
returns `w = 0`. -/
theorem disjoint_capConeImage_rot_capCone {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (hγne : ∀ x : Circle, γ x ≠ 0)
    {ρ Ψ Θ : ℝ → ℝ} (hρc : Continuous ρ) (hΨc : Continuous Ψ) (hΘc : Continuous Θ)
    (hρpos : ∀ t : ℝ, 0 < ρ t) (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΨper : ∀ t : ℝ, circleOf (Ψ (t + 2 * Real.pi)) = circleOf (Ψ t))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    {r₀ : ℝ} (hr₀pos : 0 < r₀) (hr₀ : ∀ t : ℝ, ρ t ≠ r₀) {w : UnitAddCircle} (hw : w ≠ 0) :
    Disjoint (Quotient.mk'' '' (Sum.inr '' capCone r₀ ρ Ψ Θ 0))
      (rotCapping w '' (Quotient.mk'' '' (Sum.inr '' capCone r₀ ρ Ψ Θ 0))) := by
  rw [Set.disjoint_left]
  intro p hp1 hp2
  obtain ⟨q₁, hq₁, rfl⟩ := mem_capConeImage_iff.mp hp1
  rw [Set.mem_image] at hp2
  obtain ⟨s, hs, hsp⟩ := hp2
  obtain ⟨q₂, hq₂, rfl⟩ := mem_capConeImage_iff.mp hs
  rw [rotCapping_mk, rotSum_inr] at hsp
  have hqeq : rotCap w q₂ = q₁ := cappingRel_inr_inr.mp (Quotient.exact hsp)
  obtain ⟨s, t, hs01, hv1⟩ := hq₁
  obtain ⟨s', t', hs'01, hv2⟩ := hq₂
  have hA1 : q₁.1.1 = (1 - s) * r₀ + s * ρ t := congrArg (fun z : ℝ × UnitAddCircle × ℂ => z.1) hv1
  have hB1 : q₁.1.2.1 = (((Θ 0 + s * (Θ t - Θ 0) : ℝ)) : UnitAddCircle) := by
    simpa using congrArg (fun z : ℝ × UnitAddCircle × ℂ => z.2.1) hv1
  have hC1 : q₁.1.2.2 = (s : ℂ) * circleOf ((Ψ t : ℝ) : UnitAddCircle) :=
    congrArg (fun z : ℝ × UnitAddCircle × ℂ => z.2.2) hv1
  have hA2 : q₂.1.1 = (1 - s') * r₀ + s' * ρ t' := congrArg (fun z : ℝ × UnitAddCircle × ℂ => z.1) hv2
  have hB2 : q₂.1.2.1 = (((Θ 0 + s' * (Θ t' - Θ 0) : ℝ)) : UnitAddCircle) := by
    simpa using congrArg (fun z : ℝ × UnitAddCircle × ℂ => z.2.1) hv2
  have hC2 : q₂.1.2.2 = (s' : ℂ) * circleOf ((Ψ t' : ℝ) : UnitAddCircle) :=
    congrArg (fun z : ℝ × UnitAddCircle × ℂ => z.2.2) hv2
  have hv0 : ((q₂.1.1, q₂.1.2.1 + w, q₂.1.2.2) : ℝ × UnitAddCircle × ℂ)
      = (q₁.1.1, q₁.1.2.1, q₁.1.2.2) := by
    have hval : ((rotCap w q₂ : CapPiece) : ℝ × UnitAddCircle × ℂ)
        = (q₁ : ℝ × UnitAddCircle × ℂ) := congrArg Subtype.val hqeq
    simpa [rotCap] using hval
  have hv : ((1 - s') * r₀ + s' * ρ t', (((Θ 0 + s' * (Θ t' - Θ 0) : ℝ)) : UnitAddCircle) + w,
        (s' : ℂ) * circleOf ((Ψ t' : ℝ) : UnitAddCircle))
      = ((1 - s) * r₀ + s * ρ t, (((Θ 0 + s * (Θ t - Θ 0) : ℝ)) : UnitAddCircle) + 0,
        (s : ℂ) * circleOf ((Ψ t : ℝ) : UnitAddCircle)) := by
    rw [← hA2, ← hB2, ← hC2, ← hA1, ← hB1, ← hC1, add_zero]
    exact hv0
  obtain ⟨huv, -⟩ := capDisks_disjoint hγ hγne hρc hΨc hρpos hpolar hΨper hΘc hΘper hr₀pos hr₀
    w 0 s' s t' t hs'01 hs01 hv
  exact hw huv

/-! ## The capped planes are pairwise disjoint -/

open Manifold in
open scoped Manifold ContDiff in
theorem cappedPlaneDisjoint {γ : Circle → ℝ × ℝ}
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
    {u v : UnitAddCircle} (h : v - u ∈ Zc γ) :
    Disjoint (cappedPlane r₀ ρ Ψ Θ μ u) (cappedPlane r₀ ρ Ψ Θ μ v) := by
  have hγne : ∀ x : Circle, γ x ≠ 0 := gamma_ne_zero_of_polarLift hρpos hpolar
  have hMM := disjoint_stripImage_rot hγ hμne hμdiag h
  have hMC := disjoint_stripImage_capConeImage_rot hγ hμne hμdiag hρpos hpolar hΘclass
    (r₀ := r₀) h
  have hCM := disjoint_capConeImage_rot_stripImage hγ hμne hμdiag hρpos hpolar hΘclass
    (r₀ := r₀) h
  have hCC := disjoint_capConeImage_rot_capCone hγ hγne hρc hΨc hΘc hρpos hpolar hΨper hΘper
    hr₀pos hr₀ (ne_zero_of_mem_Zc h)
  rw [Set.disjoint_left]
  intro p hp hp'
  rw [cappedPlane] at hp hp'
  rw [Set.mem_image] at hp hp'
  obtain ⟨a, ha, hap⟩ := hp
  obtain ⟨b, hb, hbp⟩ := hp'
  have hab : a = rotCapping (v - u) b := by
    have h2 : rotCapping (-u) (rotCapping u a) = rotCapping (-u) (rotCapping v b) := by
      rw [hap, hbp]
    have e1 : rotCapping (-u) (rotCapping u a) = a := by
      simp only [rotCapping_apply_add, neg_add_cancel, rotCapping_zero, id_eq]
    have e2 : rotCapping (-u) (rotCapping v b) = rotCapping (v - u) b := by
      rw [rotCapping_apply_add, show -u + v = v - u from by abel]
    rw [e1, e2] at h2
    exact h2
  simp only [Set.mem_union] at ha hb
  rcases ha with haM | haC
  · rcases hb with hbM | hbC
    · exact (Set.disjoint_left.mp hMM haM) ⟨b, hbM, hab.symm⟩
    · exact (Set.disjoint_left.mp hMC haM) ⟨b, hbC, hab.symm⟩
  · rcases hb with hbM | hbC
    · exact (Set.disjoint_left.mp hCM haC) ⟨b, hbM, hab.symm⟩
    · exact (Set.disjoint_left.mp hCC haC) ⟨b, hbC, hab.symm⟩

end Work.Drive
