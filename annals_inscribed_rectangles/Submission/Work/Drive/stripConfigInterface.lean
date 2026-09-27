import Mathlib
import Submission.Work.Drive.CappingSpace
import Submission.Work.Drive.cappingSpace_homeomorph_prod
import Submission.Work.Drive.CappingDefs
import Submission.Work.Drive.exists_embedded_configuration_strip
import Submission.Work.Drive.LensSpaceGlue
import Submission.Work.Drive.exists_disk_filling_of_meridian_class

/-!
# Stage 2: the strip-to-`ConfigPiece` interface (item (i) of `OMEGA_CHAIN_STATUS.md`)

The configuration strip of `γ` (`Work.Drive.exists_embedded_configuration_strip`) is a map
`μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ`, `μ (x,y) = (midpoint, doubled direction, length)`.
The capping (`Work.Drive.CappingSpace`) reads a configuration point off the axis
(`midpoint = 0 ∧ length = 0`) in the coordinates `(r, z, η)` of the configuration piece
`ConfigPiece = (0,∞) × D² × S¹`, where `r = ‖(midpoint, length)‖` and `z` is the normalised
`(midpoint, length)` seen in the disk of the hemisphere (`Work.Drive.cappingFibration`).

This file defines that read-off map

* `Work.Drive.confOf` — the coordinates `(r, z, η) ∈ ℝ × ℂ × UnitAddCircle` of a configuration point;
* `Work.Drive.confPiece` — the same, as an element of `ConfigPiece` (the two side conditions are taken
  as arguments, so that nothing here needs a proof obligation);

and the interface lemmas are delegated (see `OMEGA_CHAIN_STATUS.md`):

* `Work.Drive.confOf_mem_and_continuous` — `r > 0` exactly off the axis, `‖z‖ ≤ 1` always, and the
  coordinates are continuous where `r > 0` (so the strip, which avoids the axis once the origin is off
  `γ`, gives a continuous map into `ConfigPiece`);
* `Work.Drive.confOf_diag_eq_confBdy` — on the diagonal of the strip (`length = 0`, `midpoint ≠ 0`)
  the coordinates land on the **gluing boundary** `Work.Drive.confBdy` of the configuration piece, i.e.
  the boundary `∂M` of the strip is the curve along which the cap is glued on. -/

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open scoped Topology

/-- **The capping coordinates of a configuration point.**  For a point `(midpoint, η, length)` (with
`η` the doubled direction) the capping reads the radial coordinate `r = ‖(midpoint, length)‖`, the
normalised `(midpoint, length)` as a point `z` of the disk of the hemisphere, and the doubled direction
`η` again. -/
def confOf (p : (ℝ × ℝ) × UnitAddCircle × ℝ) : ℝ × ℂ × UnitAddCircle :=
  (Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2), ⟨p.1.1 / Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2),
    p.1.2 / Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2)⟩, p.2.1)

/-- **The radial coordinate is positive exactly off the axis.**  The axis of the configuration space
is `midpoint = 0 ∧ length = 0`; elsewhere the capping radius `r = ‖(midpoint, length)‖` is positive. -/
lemma confOf_pos_iff (p : (ℝ × ℝ) × UnitAddCircle × ℝ) :
    0 < (confOf p).1 ↔ p.1.1 ≠ 0 ∨ p.1.2 ≠ 0 ∨ p.2.2 ≠ 0 := by
  have hS : (0 : ℝ) ≤ p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2 := by positivity
  simp only [confOf]
  rw [Real.sqrt_pos]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rw [hc.1, hc.2.1, hc.2.2] at h
    norm_num at h
  · rintro (h | h | h) <;> nlinarith [sq_pos_of_ne_zero h]

/-- **The normalised midpoint-length vector lies in the disk.**  The second capping coordinate always
has norm `≤ 1` (at the axis, `0 / 0 = 0` in `ℝ`), so only the positivity of the radius has to be
checked to produce an element of `ConfigPiece`. -/
lemma confOf_snd_norm_le_one (p : (ℝ × ℝ) × UnitAddCircle × ℝ) :
    ‖(confOf p).2.1‖ ≤ 1 := by
  have hS : (0 : ℝ) ≤ p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2 := by positivity
  have hsqr : Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) ^ 2
      = p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2 := Real.sq_sqrt hS
  have hsq : ‖(confOf p).2.1‖ ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [confOf]
    rcases eq_or_ne (Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2)) 0 with hr | hr
    · rw [hr]; norm_num
    · have hDpos : 0 < p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2 := by
        nlinarith [hsqr, Real.sqrt_nonneg (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2),
          lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hr)]
      have hle : p.1.1 ^ 2 + p.1.2 ^ 2 ≤ p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2 := by
        nlinarith [sq_nonneg p.2.2]
      have hkey : (p.1.1 / Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2))
              * (p.1.1 / Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2))
            + (p.1.2 / Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2))
              * (p.1.2 / Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2))
          = (p.1.1 ^ 2 + p.1.2 ^ 2) / (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) := by
        rw [← sq, ← sq, div_pow, div_pow, ← add_div, hsqr]
      rw [hkey, div_le_one hDpos]
      exact hle
  nlinarith [hsq, norm_nonneg (confOf p).2.1, sq_nonneg (‖(confOf p).2.1‖ - 1)]

/-- **The capping coordinates are continuous off the axis.**  On `{r > 0}` the normalised
midpoint-length vector `(midpoint.1/r, midpoint.2/r)` is written in `ℂ` as
`(midpoint.1 + midpoint.2 · i)/r`, which is continuous as long as `r ≠ 0`.  Hence the strip, once the
origin is off `γ` (so that the strip avoids the axis), gives a *continuous* map into `ConfigPiece`. -/
lemma continuousOn_confOf :
    ContinuousOn (fun p : (ℝ × ℝ) × UnitAddCircle × ℝ => confOf p)
      {p | 0 < (confOf p).1} := by
  have hpt : ∀ p ∈ {p : (ℝ × ℝ) × UnitAddCircle × ℝ | 0 < (confOf p).1},
      confOf p = (Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2),
        (((p.1.1 : ℝ) : ℂ) + (((p.1.2 : ℝ) : ℂ) * Complex.I))
          / (((Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) : ℝ) : ℂ)), p.2.1) := by
    intro p hp
    have hpos : (0 : ℝ) < Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) := by
      have h := hp
      simp only [Set.mem_setOf_eq, confOf] at h
      exact h
    have hr : Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) ≠ 0 := hpos.ne'
    refine Prod.ext rfl ?_
    refine Prod.ext ?_ rfl
    apply Complex.ext <;>
      simp only [confOf, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re,
        Complex.I_im, Complex.normSq_apply, Complex.ofReal_zero] <;>
      (field_simp; ring_nf)
  refine ContinuousOn.congr ?_ hpt
  refine ContinuousOn.prodMk (Continuous.sqrt (by fun_prop)).continuousOn ?_
  refine ContinuousOn.prodMk ?_ (by fun_prop)
  refine ContinuousOn.div (by fun_prop) ?_ ?_
  · exact (Complex.continuous_ofReal.comp
      (Continuous.sqrt (by fun_prop))).continuousOn
  · intro p hp
    have hpos : (0 : ℝ) < Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2) := by
      have h := hp
      simp only [Set.mem_setOf_eq, confOf] at h
      exact h
    exact fun h => hpos.ne' (Complex.ofReal_eq_zero.mp h)

/-- The configuration point as an element of the configuration piece of the capping space.  The two
side conditions are arguments (they are supplied by `Work.Drive.confOf_mem_and_continuous`). -/
def confPiece (p : (ℝ × ℝ) × UnitAddCircle × ℝ) (h1 : 0 < (confOf p).1)
    (h2 : ‖(confOf p).2.1‖ ≤ 1) : ConfigPiece :=
  ⟨confOf p, h1, h2⟩

@[simp] lemma confPiece_val (p : (ℝ × ℝ) × UnitAddCircle × ℝ) (h1 : 0 < (confOf p).1)
    (h2 : ‖(confOf p).2.1‖ ≤ 1) :
    (confPiece p h1 h2 : ℝ × ℂ × UnitAddCircle) = confOf p := rfl

/-- The strip of `γ` seen in the configuration piece: the capping coordinates of `μ (x,y)`. -/
def stripConfPiece (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ) (q : Circle × Circle)
    (h1 : 0 < (confOf (μ q)).1) (h2 : ‖(confOf (μ q)).2.1‖ ≤ 1) : ConfigPiece :=
  confPiece (μ q) h1 h2

@[simp] lemma stripConfPiece_val (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ)
    (q : Circle × Circle) (h1 : 0 < (confOf (μ q)).1) (h2 : ‖(confOf (μ q)).2.1‖ ≤ 1) :
    (stripConfPiece μ q h1 h2 : ℝ × ℂ × UnitAddCircle) = confOf (μ q) := rfl

/-- **The diagonal of the strip lands on the gluing circle.**  At length `0` the chord is a point
`m` of the curve; if `m ≠ 0` the capping coordinates have radial part `‖m‖` and disk coordinate
`m/‖m‖` of norm one, i.e. they lie on the boundary circle `circleOf` of the configuration piece — the
curve along which the cap is glued on (`Work.Drive.cappingRel`, via `Work.Drive.confBdy`). -/
lemma confOf_diag_eq_confBdy {m : ℝ × ℝ} (hm : m ≠ 0) (η : UnitAddCircle) :
    ∃ φ : UnitAddCircle,
      confOf (m, η, 0) = (Real.sqrt (m.1 ^ 2 + m.2 ^ 2), circleOf φ, η) := by
  have hm' : m.1 ≠ 0 ∨ m.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (Prod.ext h.1 h.2)
  have hpos : 0 < Real.sqrt (m.1 ^ 2 + m.2 ^ 2) := by
    refine Real.sqrt_pos.mpr ?_
    rcases hm' with h | h <;> nlinarith [sq_pos_of_ne_zero h]
  have hsqr : Real.sqrt (m.1 ^ 2 + m.2 ^ 2) ^ 2 = m.1 ^ 2 + m.2 ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hz : ‖(⟨m.1 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2),
      m.2 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2)⟩ : ℂ)‖ = 1 := by
    have h2 : ‖(⟨m.1 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2),
        m.2 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2)⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hkey : (m.1 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2)) * (m.1 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2))
            + (m.2 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2)) * (m.2 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2))
          = (m.1 ^ 2 + m.2 ^ 2) / (m.1 ^ 2 + m.2 ^ 2) := by
        rw [← sq, ← sq, div_pow, div_pow, ← add_div, hsqr]
      have hD : m.1 ^ 2 + m.2 ^ 2 ≠ 0 := by
        rcases hm' with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg m.1, sq_nonneg m.2]
      rw [hkey, div_self hD]
    nlinarith [h2, norm_nonneg (⟨m.1 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2),
      m.2 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2)⟩ : ℂ), sq_nonneg (‖(⟨m.1 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2),
      m.2 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2)⟩ : ℂ)‖ - 1)]
  refine ⟨circOf _ hz, ?_⟩
  simp only [confOf]
  rw [circleOf_circOf]
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]

/-! ## The strip's image in the capping space, and its boundary on the gluing torus -/

/-- **The gluing identification in the capping space.**  The configuration boundary point with
parameters `(r, φ, θ + 2φ)` *is* the cap boundary point with parameters `(r, θ, φ)`: this is the
sense in which the boundary `∂M` of the strip (where the length coordinate vanishes, so the disk
coordinate has norm one) lies on the gluing torus and is filled by the cap disk. -/
lemma mk_confBdy_eq_mk_capBdy (r : ℝ) (hr : 0 < r) (θ φ : UnitAddCircle) :
    (Quotient.mk'' (Sum.inl (confBdy r hr φ (θ + 2 • φ)) : ConfigPiece ⊕ CapPiece) : CappingSpace)
      = Quotient.mk'' (Sum.inr (capBdy r hr θ φ) : ConfigPiece ⊕ CapPiece) :=
  Quotient.sound (Or.inr ⟨r, hr, θ, φ, Or.inl ⟨rfl, rfl⟩⟩)

/-- **The image of the configuration strip in the capping space.**  Away from the diagonal a chord
`(x,y)` has positive length, so its capping coordinates `confOf (μ (x,y))` are those of a point of the
configuration piece (the axis is avoided as soon as the origin is off `γ`); at the diagonal the same
formula gives a point of the *gluing torus* (`confOf_diag_eq_confBdy`), which the previous lemma
identifies with a point of the cap piece. -/
def stripImage (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ) : Set CappingSpace :=
  {p | ∃ (q : Circle × Circle) (h1 : 0 < (confOf (μ q)).1) (h2 : ‖(confOf (μ q)).2.1‖ ≤ 1),
      p = Quotient.mk'' (Sum.inl (confPiece (μ q) h1 h2) : ConfigPiece ⊕ CapPiece)}

lemma mem_stripImage_iff {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    {p : CappingSpace} :
    p ∈ stripImage μ ↔ ∃ (q : Circle × Circle) (h1 : 0 < (confOf (μ q)).1)
      (h2 : ‖(confOf (μ q)).2.1‖ ≤ 1),
      p = Quotient.mk'' (Sum.inl (confPiece (μ q) h1 h2) : ConfigPiece ⊕ CapPiece) :=
  Iff.rfl

/-- **The diagonal of the strip, seen on the cap side.**  For a diagonal configuration point — the
chord degenerating to a point `m = γ x` of the curve — the configuration-side capping class is the
cap-side boundary point with cap angle `θ = η - 2φ`, where `η` is the doubled tangent direction and
`φ` is the position angle of `m` (so that `circleOf φ = m/‖m‖`).  This is the form of the statement
that the cap disk of `Work.Drive.exists_disk_filling_of_meridian_class` is glued onto `∂M`. -/
theorem strip_diag_mk_eq {m : ℝ × ℝ} (hm : m ≠ 0) (η : UnitAddCircle)
    (h1 : 0 < (confOf (m, η, 0)).1) (h2 : ‖(confOf (m, η, 0)).2.1‖ ≤ 1) :
    ∃ (θ φ : UnitAddCircle) (hr : 0 < Real.sqrt (m.1 ^ 2 + m.2 ^ 2)),
      (Quotient.mk'' (Sum.inl (confPiece (m, η, 0) h1 h2) : ConfigPiece ⊕ CapPiece) : CappingSpace)
        = Quotient.mk'' (Sum.inr (capBdy (Real.sqrt (m.1 ^ 2 + m.2 ^ 2)) hr θ φ)
            : ConfigPiece ⊕ CapPiece) := by
  obtain ⟨φ, hφ⟩ := confOf_diag_eq_confBdy hm η
  have hD : 0 < m.1 ^ 2 + m.2 ^ 2 := by
    have h : m.1 ≠ 0 ∨ m.2 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hm (Prod.ext hc.1 hc.2)
    rcases h with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg m.1, sq_nonneg m.2]
  set r : ℝ := Real.sqrt (m.1 ^ 2 + m.2 ^ 2) with hrdef
  have hr : 0 < r := by rw [hrdef]; exact Real.sqrt_pos.mpr hD
  refine ⟨η - 2 • φ, φ, hr, ?_⟩
  have hval : (confOf (m, η, 0) : ℝ × ℂ × UnitAddCircle) = (r, circleOf φ, η) := by
    rw [hrdef]
    exact hφ
  have hconf : (confPiece (m, η, 0) h1 h2 : ℝ × ℂ × UnitAddCircle)
      = (confBdy r hr φ ((η - 2 • φ) + 2 • φ) : ℝ × ℂ × UnitAddCircle) := by
    rw [confPiece_val]
    rw [hval, confBdy_val]
    exact Prod.ext rfl (Prod.ext rfl (by abel))
  rw [show (Quotient.mk'' (Sum.inl (confPiece (m, η, 0) h1 h2) : ConfigPiece ⊕ CapPiece)
        : CappingSpace)
      = Quotient.mk'' (Sum.inl (confBdy r hr φ ((η - 2 • φ) + 2 • φ)) : ConfigPiece ⊕ CapPiece)
      from congrArg Quotient.mk'' (congrArg Sum.inl (Subtype.ext hconf))]
  exact mk_confBdy_eq_mk_capBdy r hr (η - 2 • φ) φ

/-! ## The disk filling the strip's boundary (the gluing) -/

/-- **The cap disk closes the strip's boundary.**  The cap-side boundary curve of the configuration
strip is `t ↦ (Θ t, circleOf (Φ t))` in the boundary torus of the cap solid torus, where `Θ` is the
cap angle (the doubled tangent direction minus twice the position angle of the midpoint) and `Φ` the
position angle; both are periodic — the twisted degree `±2 - 2·(±1) = 0` being exactly the content of
the Umlaufsatz together with the position-angle winding (`CAPPING_ANALYSIS.md`, inputs A and B).

The disk-filling theorem `Work.Drive.exists_disk_filling_of_meridian_class` provides the disk `D` in
the solid torus filling that curve; the extra conjunct recorded here is the **gluing**: for every `t`
the configuration-side boundary point of the strip at doubled direction `Θ t + 2·Φ t` and position
angle `Φ t` — which is what `Work.Drive.strip_diag_mk_eq` produces — is the *same class* in
`Work.Drive.CappingSpace` as the cap-side boundary point `(Θ t, circleOf (Φ t))` of the disk. -/
theorem exists_cap_disk_gluing_strip (r : ℝ) (hr : 0 < r) (Θ Φ : ℝ → ℝ)
    (hΘ : Continuous Θ) (hΦ : Continuous Φ) (hΘper : ∀ t, Θ (t + 1) = Θ t)
    (hΦper : ∀ t, circleOf (Φ (t + 1)) = circleOf (Φ t)) :
    ∃ D : ℝ × ℝ → UnitAddCircle × ℂ,
      Continuous D ∧
      (∀ t, D (1, t) = (((Θ t : ℝ) : UnitAddCircle), circleOf (Φ t))) ∧
      (∀ t, D (0, t) = (((Θ 0 : ℝ) : UnitAddCircle), 0)) ∧
      (∀ t, D (0, t) = D (0, 0)) ∧
      (∀ ρ t, D (ρ, t + 1) = D (ρ, t)) ∧
      (∀ ρ t, ρ ∈ Set.Icc (0 : ℝ) 1 → ‖(D (ρ, t)).2‖ ≤ 1) ∧
      (∀ t, (Quotient.mk'' (Sum.inl (confBdy r hr (Φ t) ((Θ t) + 2 • (Φ t)))
              : ConfigPiece ⊕ CapPiece) : CappingSpace)
          = (Quotient.mk'' (Sum.inr (capBdy r hr (Θ t) (Φ t))
              : ConfigPiece ⊕ CapPiece) : CappingSpace)) := by
  obtain ⟨D, hcont, h1, h0, h00, hper, hnorm⟩ :=
    exists_disk_filling_of_meridian_class Θ Φ hΘ hΦ hΘper hΦper
  exact ⟨D, hcont, h1, h0, h00, hper, hnorm, fun t => mk_confBdy_eq_mk_capBdy r hr (Θ t) (Φ t)⟩

/-! ## The cap angle of the strip's diagonal, and its periodicity -/

/-- **The cap angle `Θc = Φ - 2Θ` of the strip's diagonal is periodic.**  Here `Φ` is a continuous lift
of the doubled tangent direction of the curve, with total change `2ε` over the period (`ε = ±1` — Hopf's
Umlaufsatz, `Work.Drive.doubledTangent_winding`), and `Θ` a continuous lift of the position angle of the
midpoint, with total change the *same* `ε` (`CAPPING_ANALYSIS.md`, input A: the position winding of a
Jordan curve about an interior point equals its rotation index).  The degree computation
`2ε - 2·ε = 0` then says that the cap angle is a function of the parameter on the *circle*: `∂M` is a
meridian of the cap solid torus, which is what lets `Work.Drive.exists_cap_disk_gluing_strip` fill it. -/
theorem exists_periodic_cap_angle (Φ Θ : ℝ → ℝ) (ε : ℤ) (hΦc : Continuous Φ) (hΘc : Continuous Θ)
    (hΦper : ∀ t, Φ (t + 2 * Real.pi) - Φ t = (2 * ε : ℝ))
    (hΘper : ∀ t, Θ (t + 2 * Real.pi) - Θ t = (ε : ℝ)) :
    ∃ Θc : ℝ → ℝ, Continuous Θc ∧ (∀ t, Θc (t + 2 * Real.pi) = Θc t) ∧
      (∀ t, ((Θc t : ℝ) : UnitAddCircle)
        = (Φ t : UnitAddCircle) - 2 • (Θ t : UnitAddCircle)) := by
  refine ⟨fun t => Φ t - 2 * Θ t, hΦc.sub (hΘc.const_mul 2), ?_, ?_⟩
  · intro t
    have h1 := hΦper t
    have h2 := hΘper t
    have : Φ (t + 2 * Real.pi) - 2 * Θ (t + 2 * Real.pi) - (Φ t - 2 * Θ t) = 0 := by
      push_cast at h1 h2
      linarith
    linarith
  · intro t
    change ((Φ t - 2 * Θ t : ℝ) : UnitAddCircle)
      = (Φ t : UnitAddCircle) - 2 • (Θ t : UnitAddCircle)
    rw [show (Φ t - 2 * Θ t : ℝ) = Φ t - 2 • Θ t by rw [nsmul_eq_mul]; norm_num]
    rw [AddCircle.coe_sub, AddCircle.coe_nsmul]

end Work.Drive
