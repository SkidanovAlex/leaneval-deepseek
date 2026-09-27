import Mathlib
import Submission.Work.Drive.capAngleOfSmooth
import Submission.Work.Drive.stripConfigInterface
import Submission.Work.Drive.exists_embedded_configuration_strip

/-!
# Stage 2, item 1: the capped plane `P_u = u·M ∪ cap_u` of the configuration strip

`Submission/Work/Drive/OMEGA_CHAIN_STATUS.md` (item 1 of "What is still missing for a general strip")
asks for the capped configuration strip of a smooth embedding `γ`:

* the strip side is `Work.Drive.exists_embedded_configuration_strip` (`μ`, whose diagonal is
  `x ↦ (γ x, tangentDirC γ x, 0)`) and its image in the capping space is
  `Work.Drive.stripImage` with the boundary identification `Work.Drive.strip_diag_mk_eq`;
* the cap side is the disk of `Work.Drive.exists_cap_disk_gluing_strip`.

This file supplies the missing wiring: the cap angle and the position angle of the strip's diagonal are
extracted from the *proved* chain `Work.Drive.exists_periodic_cap_angle_polar`
(`Submission/Work/Drive/capAngleOfSmooth.lean`), rescaled from period `2π` to the period `1` used by
the capping API, fed into `Work.Drive.exists_cap_disk_gluing_strip`, and *identified* with the
configuration coordinates of the strip's diagonal: every point of `∂M` seen in `CappingSpace` is the
cap-side boundary point `(Θc, circleOf Θ)` of the disk `D`, i.e. `D` closes `stripImage`.

Main results:

* `Work.Drive.confOf_eq_of_polarLift` — the capping coordinates of a length-zero configuration point
  `(m, η, 0)` are the polar decomposition `(ρ, circleOf Θ, η)` of its midpoint `m = polarLift (ρ, Θ)`;
* `Work.Drive.polarLift_ne_zero` — `polarLift (ρ, Θ) ≠ 0` for `ρ > 0`;
* `Work.Drive.exists_strip_cap_disk` — the capped plane of the configuration strip of `γ` (translated
  so that the origin is off the curve), with the disk closing its boundary.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open scoped Topology

open Submission.Geometry (eucNorm eucNorm_sq eucDot)

open Submission.Collision (dirC)

/-- The complex number attached to a point of the plane, used to compare with `circleOf`. -/
private lemma cplx_ext_re_im {z w : ℂ} (h1 : z.re = w.re) (h2 : z.im = w.im) : z = w :=
  Complex.ext h1 h2

/-- **The polar lift `(ρ, Θ)` of `m` gives the capping coordinates of the length-zero configuration
point `(m, η, 0)`**: the radial coordinate is `ρ`, the disk coordinate is `circleOf Θ` and the
direction coordinate is `η`.  This is the identification of the configuration boundary torus of
`Work.Drive.confOf` with the boundary circle parametrisation `circleOf` of the capping. -/
lemma confOf_eq_of_polarLift {m : ℝ × ℝ} {ρ Θ : ℝ} (hρ : 0 < ρ)
    (hm : polarLift (ρ, Θ) = m) (η : UnitAddCircle) :
    confOf (m, η, 0) = (ρ, circleOf ((Θ : ℝ) : UnitAddCircle), η) := by
  have hm1 : m.1 = ρ * Real.cos (2 * Real.pi * Θ) := by rw [← hm, polarLift]
  have hm2 : m.2 = ρ * Real.sin (2 * Real.pi * Θ) := by rw [← hm, polarLift]
  have hsq : m.1 ^ 2 + m.2 ^ 2 = ρ ^ 2 := by
    rw [hm1, hm2, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  have hsqrt : Real.sqrt (m.1 ^ 2 + m.2 ^ 2) = ρ := by
    rw [hsq, Real.sqrt_sq hρ.le]
  have hfst : (confOf (m, η, 0)).1 = ρ := by
    simp only [confOf, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    rw [hsqrt]
  have hsnd : (confOf (m, η, 0)).2.1 = circleOf ((Θ : ℝ) : UnitAddCircle) := by
    refine cplx_ext_re_im ?_ ?_
    · simp only [confOf, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, hsqrt]
      rw [circleOf_coe_re, hm1]
      field_simp
    · simp only [confOf, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, hsqrt]
      rw [circleOf_coe_im, hm2]
      field_simp
  exact Prod.ext hfst (Prod.ext hsnd rfl)

/-- `polarLift (ρ, Θ) ≠ 0` for `ρ > 0`. -/
lemma polarLift_ne_zero {ρ Θ : ℝ} (hρ : 0 < ρ) : polarLift (ρ, Θ) ≠ 0 := by
  intro h
  have h1 : (polarLift (ρ, Θ)).1 = 0 := by rw [h]; rfl
  have h2 : (polarLift (ρ, Θ)).2 = 0 := by rw [h]; rfl
  rw [polarLift] at h1 h2
  have hcos : Real.cos (2 * Real.pi * Θ) = 0 := by
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact absurd h' hρ.ne'
    · exact h'
  have hsin : Real.sin (2 * Real.pi * Θ) = 0 := by
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd h' hρ.ne'
    · exact h'
  have h3 := Real.cos_sq_add_sin_sq (2 * Real.pi * Θ)
  rw [hcos, hsin] at h3
  norm_num at h3

/-- **The capped plane of the configuration strip** (Stage 2, item 1 of `OMEGA_CHAIN_STATUS.md`).

For a smooth embedding `γ` there are

* a point `c` off the curve (so that the origin is off the translate `γ - c`, i.e. the diagonal of the
  configuration strip stays away from the axis of the configuration space);
* a continuous positive radial function `ρ`, the position angle `Θ` of `γ (exp ·) - c`, and the
  tangent lift `Φ` of the doubled tangent direction, all from the proved cap-angle chain
  `Work.Drive.exists_periodic_cap_angle_polar`;
* the `2π`-periodic cap angle `Θc` of class `Φ - 2·Θ`;
* a disk `D` (from `Work.Drive.exists_cap_disk_gluing_strip`, with the rescaling `τ ↦ 2πτ` of the
  parameter to the period `1` of the capping API) filling the cap-side boundary curve
  `τ ↦ (Θc (2πτ), circleOf (Θ (2πτ)))` of the strip;

and the **gluing**: for every parameter `t`, the configuration-side class in `CappingSpace` of the
diagonal point of the strip of `γ - c` is the cap-side boundary point
`(Θc (2πt), circleOf (Θ (2πt)))` of the disk.  This is the statement `∂M = D (1, ·)` with the two
pieces of `CappingSpace` glued along `Work.Drive.cappingRel`, i.e. `D` closes `Work.Drive.stripImage`
and `P_u = u·M ∪ cap_u` is a closed surface. -/
theorem exists_strip_cap_disk (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∃ (c : ℝ × ℝ) (ρ Θ Φ Θc : ℝ → ℝ) (D : ℝ × ℝ → UnitAddCircle × ℂ),
      Continuous ρ ∧ Continuous Θ ∧ Continuous Φ ∧ Continuous Θc ∧ Continuous D ∧
      (∀ t, 0 < ρ t) ∧
      (∀ t, polarLift (ρ t, Θ t) = γ (Circle.exp t) - c) ∧
      (∀ t, ((Φ t : ℝ) : UnitAddCircle) = dirC (deriv (Work.Drive.curve γ) t)) ∧
      (∀ t, ((Θc t : ℝ) : UnitAddCircle) = (Φ t : UnitAddCircle) - 2 • (Θ t : UnitAddCircle)) ∧
      (∀ t, D (1, t) =
        (((Θc (2 * Real.pi * t) : ℝ) : UnitAddCircle), circleOf ((Θ (2 * Real.pi * t) : ℝ)))) ∧
      (∀ t, D (0, t) = D (0, 0)) ∧
      (∀ ρ' t, D (ρ', t + 1) = D (ρ', t)) ∧
      (∀ ρ' t, ρ' ∈ Set.Icc (0 : ℝ) 1 → ‖(D (ρ', t)).2‖ ≤ 1) ∧
      (∀ t, ∃ (h1 : 0 < (confOf (γ (Circle.exp (2 * Real.pi * t)) - c,
              tangentDirC γ (Circle.exp (2 * Real.pi * t)), 0)).1)
            (h2 : ‖(confOf (γ (Circle.exp (2 * Real.pi * t)) - c,
              tangentDirC γ (Circle.exp (2 * Real.pi * t)), 0)).2.1‖ ≤ 1)
            (hr : 0 < ρ (2 * Real.pi * t)),
        ((Quotient.mk'' (Sum.inl (confPiece (γ (Circle.exp (2 * Real.pi * t)) - c,
            tangentDirC γ (Circle.exp (2 * Real.pi * t)), 0) h1 h2)
              : ConfigPiece ⊕ CapPiece) : CappingSpace)
          = (Quotient.mk'' (Sum.inr (capBdy (ρ (2 * Real.pi * t)) hr
              ((Θc (2 * Real.pi * t) : ℝ) : UnitAddCircle)
              ((Θ (2 * Real.pi * t) : ℝ) : UnitAddCircle))
              : ConfigPiece ⊕ CapPiece) : CappingSpace))) := by
  obtain ⟨c, ρ, Θ, Ψ, Φ, Θc, hρc, hΘc, hΨc, hΦc, hΘcc, hρpos, hlift, hΨ, hΦ, hΘper, hε,
    hΘcper, hΘcclass⟩ := exists_periodic_cap_angle_polar γ hγ
  set Θ₁ : ℝ → ℝ := fun τ => Θc (2 * Real.pi * τ) with hΘ₁
  set Φ₁ : ℝ → ℝ := fun τ => Θ (2 * Real.pi * τ) with hΦ₁
  have hΘ₁c : Continuous Θ₁ := hΘcc.comp (continuous_const.mul continuous_id)
  have hΦ₁c : Continuous Φ₁ := hΘc.comp (continuous_const.mul continuous_id)
  have hΘ₁per : ∀ τ, Θ₁ (τ + 1) = Θ₁ τ := by
    intro τ
    have h1 : 2 * Real.pi * (τ + 1) = 2 * Real.pi * τ + 2 * Real.pi := by ring
    simp only [Θ₁]
    rw [h1, hΘcper]
  have hΦ₁per : ∀ τ, circleOf (Φ₁ (τ + 1)) = circleOf (Φ₁ τ) := by
    intro τ
    have h1 : 2 * Real.pi * (τ + 1) = 2 * Real.pi * τ + 2 * Real.pi := by ring
    simp only [Φ₁]
    rw [h1]
    exact congrArg circleOf (hΘper (2 * Real.pi * τ))
  obtain ⟨D, hDc, hD1, -, hD00, hDper, hDnorm, -⟩ :=
    exists_cap_disk_gluing_strip 1 one_pos Θ₁ Φ₁ hΘ₁c hΦ₁c hΘ₁per hΦ₁per
  refine ⟨c, ρ, Θ, Φ, Θc, D, hρc, hΘc, hΦc, hΘcc, hDc, hρpos, hlift, hΦ, hΘcclass,
    ?_, hD00, hDper, hDnorm, ?_⟩
  · intro t
    simpa only [Θ₁, Φ₁] using hD1 t
  · intro t
    set τ : ℝ := 2 * Real.pi * t with hτ
    set m : ℝ × ℝ := γ (Circle.exp τ) - c with hm
    set η : UnitAddCircle := tangentDirC γ (Circle.exp τ) with hη
    have hρposτ : 0 < ρ τ := hρpos τ
    have hliftτ : polarLift (ρ τ, Θ τ) = m := hlift τ
    have hconf : confOf (m, η, 0) =
        (ρ τ, circleOf (((Θ τ) : ℝ) : UnitAddCircle), η) :=
      confOf_eq_of_polarLift hρposτ hliftτ η
    have h1 : 0 < (confOf (m, η, 0)).1 := by rw [hconf]; exact hρposτ
    have h2 : ‖(confOf (m, η, 0)).2.1‖ ≤ 1 := confOf_snd_norm_le_one _
    have hηΦ : η = ((Φ τ : ℝ) : UnitAddCircle) := by
      rw [hη, tangentDirC_exp γ hγ τ]
      exact (hΦ τ).symm
    have hconfBdy : confPiece (m, η, 0) h1 h2 =
        confBdy (ρ τ) hρposτ (((Θ τ) : ℝ) : UnitAddCircle)
          (((Φ τ) : ℝ) : UnitAddCircle) := by
      apply Subtype.ext
      rw [confPiece_val, confBdy_val, hconf, hηΦ]
    have hθ : (((Φ τ) : ℝ) : UnitAddCircle)
        = (((Θc τ) : ℝ) : UnitAddCircle) + 2 • (((Θ τ) : ℝ) : UnitAddCircle) := by
      rw [hΘcclass τ]; abel
    refine ⟨h1, h2, hρposτ, ?_⟩
    rw [hconfBdy, hθ]
    exact mk_confBdy_eq_mk_capBdy (ρ τ) hρposτ (((Θc τ) : ℝ) : UnitAddCircle)
      (((Θ τ) : ℝ) : UnitAddCircle)

/-! ## The two pieces of the capping space meet only along the glued boundary

`Work.Drive.CappingSpace` is the quotient of the disjoint union of the configuration piece
`(0,∞) × D² × S¹` and the cap piece `(0,∞) × S¹ × D²` by the relation `Work.Drive.cappingRel`, which
identifies *boundary* points only (`confBdy r hr φ η` with `capBdy r hr θ φ`).  Consequently the
*interiors* of the two pieces are disjoint in the quotient — the fact that makes the capped plane
`P_u = u·M ∪ cap_u` a genuine surface with `M` and `cap` meeting along `∂M` and nowhere else, and
which underlies the disjointness of the capped planes for `v - u ∈ Zc γ`. -/

/-- **A configuration interior point is not a cap point.**  If the disk coordinate of a configuration
point is *strictly* inside the disk (`‖z‖ < 1`, i.e. the chord has positive length), the point is not
in the image of the cap piece in `CappingSpace`. -/
lemma mk_inl_ne_mk_inr_of_norm_lt_one {p : ConfigPiece} {q : CapPiece}
    (hp : ‖p.1.2.1‖ < 1) :
    (Quotient.mk'' (Sum.inl p) : CappingSpace) ≠ Quotient.mk'' (Sum.inr q) := by
  intro h
  have hrel : cappingRel (Sum.inl p) (Sum.inr q) := Quotient.exact h
  rcases hrel with h | ⟨r, hr, θ, φ, h | h⟩
  · exact absurd h inl_ne_inr
  · obtain ⟨hx, -⟩ := h
    have hp' : p = confBdy r hr φ (θ + 2 • φ) := Sum.inl.inj hx
    have hz : p.1.2.1 = circleOf φ := by rw [hp']; rfl
    rw [hz, norm_circleOf] at hp
    exact lt_irrefl 1 hp
  · obtain ⟨hy, -⟩ := h
    exact absurd hy inr_ne_inl

/-- **A cap interior point is not a configuration point.**  The mirror image of
`mk_inl_ne_mk_inr_of_norm_lt_one`: a cap point whose disk coordinate is strictly inside the disk is not
a configuration class. -/
lemma mk_inr_ne_mk_inl_of_norm_lt_one {p : CapPiece} {q : ConfigPiece}
    (hp : ‖p.1.2.2‖ < 1) :
    (Quotient.mk'' (Sum.inr p) : CappingSpace) ≠ Quotient.mk'' (Sum.inl q) := by
  intro h
  have hrel : cappingRel (Sum.inr p) (Sum.inl q) := Quotient.exact h
  rcases hrel with h | ⟨r, hr, θ, φ, h | h⟩
  · exact absurd h inr_ne_inl
  · obtain ⟨hx, -⟩ := h
    exact absurd hx inr_ne_inl
  · obtain ⟨-, hp'⟩ := h
    have hp'' : p = capBdy r hr θ φ := Sum.inr.inj hp'
    have hz : p.1.2.2 = circleOf φ := by rw [hp'']; rfl
    rw [hz, norm_circleOf] at hp
    exact lt_irrefl 1 hp
/-- **A cap point identified with a configuration point is a boundary point of the cap piece.**
Whenever `mk (inl p) = mk (inr q)` in the capping space, the cap point `q` lies on the gluing circle
(`‖q.1.2.2‖ = 1`); equivalently, the *interior* of the cap piece (`‖q.1.2.2‖ < 1`) meets the
configuration side only trivially.  This is the precise sense in which `cappingRel` identifies boundary
points only. -/
lemma norm_thd_eq_one_of_mk_inl_eq_mk_inr {p : ConfigPiece} {q : CapPiece}
    (h : (Quotient.mk'' (Sum.inl p) : CappingSpace) = Quotient.mk'' (Sum.inr q)) :
    ‖q.1.2.2‖ = 1 := by
  have hrel : cappingRel (Sum.inl p) (Sum.inr q) := Quotient.exact h
  rcases hrel with h | ⟨r, hr, θ, φ, h | h⟩
  · exact absurd h inl_ne_inr
  · obtain ⟨-, hq⟩ := h
    have hq' : q = capBdy r hr θ φ := Sum.inr.inj hq
    have hz : q.1.2.2 = circleOf φ := by rw [hq']; rfl
    rw [hz, norm_circleOf]
  · obtain ⟨hy, -⟩ := h
    exact absurd hy inr_ne_inl

/-- **A configuration point identified with a cap point is a boundary point of the configuration
piece** (the mirror of `norm_thd_eq_one_of_mk_inl_eq_mk_inr`). -/
lemma norm_snd_eq_one_of_mk_inr_eq_mk_inl {p : CapPiece} {q : ConfigPiece}
    (h : (Quotient.mk'' (Sum.inr p) : CappingSpace) = Quotient.mk'' (Sum.inl q)) :
    ‖q.1.2.1‖ = 1 := by
  have hrel : cappingRel (Sum.inr p) (Sum.inl q) := Quotient.exact h
  rcases hrel with h | ⟨r, hr, θ, φ, h | h⟩
  · exact absurd h inr_ne_inl
  · obtain ⟨hx, -⟩ := h
    exact absurd hx inr_ne_inl
  · obtain ⟨hq, -⟩ := h
    have hq' : q = confBdy r hr φ (θ + 2 • φ) := Sum.inl.inj hq
    have hz : q.1.2.1 = circleOf φ := by rw [hq']; rfl
    rw [hz, norm_circleOf]

/-- **The interior of the cap piece.**  The points of the cap solid torus whose disk coordinate is
strictly inside the disk; these are the points of the cap piece that are disjoint from the
configuration side, and hence from the configuration strip. -/
def capInterior : Set CappingSpace :=
  {p | ∃ q : CapPiece, ‖q.1.2.2‖ < 1 ∧ p = Quotient.mk'' (Sum.inr q)}

/-- **The configuration strip does not meet the interior of the cap piece.**  The strip of `γ` (its
image in `CappingSpace`) is glued to the cap piece along `∂M` only: every point of `capInterior` is a
cap-interior point, and a configuration class can only be a cap class of the glued boundary.  This is
the statement that `P_u = u·M ∪ cap_u` is a genuine surface with `M` and the cap meeting exactly along
`∂M`. -/
lemma disjoint_stripImage_capInterior
    (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ) :
    Disjoint (stripImage μ) capInterior := by
  rw [Set.disjoint_left]
  rintro p hp hp'
  obtain ⟨q, h1, h2, rfl⟩ := mem_stripImage_iff.mp hp
  obtain ⟨q', hq', hp''⟩ := hp'
  have hzero : (Quotient.mk'' (Sum.inl (confPiece (μ q) h1 h2) : ConfigPiece ⊕ CapPiece)
        : CappingSpace) = Quotient.mk'' (Sum.inr q') := hp''
  exact absurd (norm_thd_eq_one_of_mk_inl_eq_mk_inr hzero) (ne_of_lt hq')


/-- **The diagonal of the configuration strip, in the capping coordinates.**  For the strip map `μ` of
`γ` (with the origin off `γ`), a polar lift `polarLift (ρ t, Θ t) = γ (exp t)` and the cap angle `Θc`
of class `tangent - 2Θ`, the capping coordinates of the diagonal point of the strip at
`x = exp t` are

`(ρ t, circleOf (Θ t), Θc t + 2·Θ t)`,

i.e. exactly the shape `confBdy r hr φ (θ + 2φ)` of the configuration boundary points that
`Work.Drive.exists_cap_disk_gluing_strip` glues to the cap disk (with `φ = Θ t` and `θ = Θc t`).
This identifies the boundary `∂M` of the strip, on the configuration side, with the boundary curve of
the cap. -/
theorem strip_diag_confOf {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {ρ Θ Θc : ℝ → ℝ} (hρpos : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Θ t) = γ (Circle.exp t))
    (hΘc : ∀ t : ℝ, ((Θc t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Θ t : ℝ) : UnitAddCircle)) :
    ∀ t : ℝ, confOf (μ (Circle.exp t, Circle.exp t))
      = (ρ t, circleOf ((Θ t : ℝ) : UnitAddCircle),
          ((Θc t : ℝ) : UnitAddCircle) + 2 • ((Θ t : ℝ) : UnitAddCircle)) := by
  intro t
  rw [hμdiag (Circle.exp t), ← hpolar t]
  rw [confOf_eq_of_polarLift (hρpos t) rfl (tangentDirC γ (Circle.exp t))]
  have htan : tangentDirC γ (Circle.exp t)
      = ((Θc t : ℝ) : UnitAddCircle) + 2 • ((Θ t : ℝ) : UnitAddCircle) := by
    rw [hΘc t]; abel
  rw [htan]

end Work.Drive
