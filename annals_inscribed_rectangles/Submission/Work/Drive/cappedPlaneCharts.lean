import Mathlib
import Submission.Work.Drive.capConeParam
import Submission.Work.Drive.essential_loop
import Submission.Work.Drive.stripImage_eq_offset_image
import Submission.Work.Drive.stripOffset_confOf_injective

/-!
# The charts of the capped plane: the strip chart and the cap chart

`Work.Drive.cappedPlane r₀ ρ Ψ Θ μ u` is the copy of `ℝP²` obtained by capping the configuration
Möbius strip `M = stripImage μ` of a smooth Jordan curve `γ` with the cone
`capCone r₀ ρ Ψ Θ 0`, rotated by `u`.  This file sets up the two **charts** of that surface and the way
they glue, in the form in which the disk presentation of `P_u` (and the chain route's transport, see
`SWEEP_TRANSPORT_NOTES.md` §3) uses them:

* `Work.Drive.stripPt` — the class in the capping space of the offset chord `(x, s)`, i.e. of the
  configuration point `stripOffsetPt μ x s`; its range is the strip `rotCapping u '' stripImage μ`.
  `Work.Drive.stripPt_eq_iff` is its injectivity, exactly up to the Möbius identification: the two
  presentations `(x, 1/2)` and `(-x, 1/2)` of a diameter give the same point and nothing else does.
* `Work.Drive.stripOffset_confOf_fst_pos` — the offset chord of `[0,1/2]` never lies on the axis of
  the configuration space (the origin is off `γ` and `γ` is injective), so the capping coordinates
  `confOf` of `stripOffsetPt μ x s` define a genuine point of `ConfigPiece`.
* `Work.Drive.capPtClass` — the class in the capping space of the cone point `capConePt` of the cap
  disk, i.e. the cap chart.
* `Work.Drive.stripPt_zero_eq_capPtClass_one` — **the gluing of the two charts**: the diagonal point
  of the strip at `Circle.exp t` is the boundary point of the cap disk at parameter `t`.  This is
  `∂M = ∂cap`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open scoped Topology

open Submission.Geometry (eucNorm eucNorm_pos eucNorm_nonneg)
open Submission.Configuration (muOrd)

/-! ## The offset chord of `[0, 1/2]` is non-degenerate -/

/-- **For `s ∈ (0,1/2]` the offset chord of `x` is non-degenerate**: `x ≠ x * exp (2π i s)`. -/
lemma offset_chord_ne (x : Circle) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) (1 / 2)) :
    x ≠ x * Circle.exp (2 * Real.pi * s) := by
  intro h
  have h1 : Circle.exp (2 * Real.pi * s) = 1 := by
    have h2 : x * 1 = x * Circle.exp (2 * Real.pi * s) := by rw [mul_one]; exact h
    exact (mul_left_cancel h2).symm
  obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp h1
  have hn' : s = (n : ℝ) := by
    have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp at hn
    linarith [hn]
  have h0 : (0 : ℤ) < n := by exact_mod_cast (by linarith [hs.1, hn'] : (0:ℝ) < (n:ℝ))
  have h1' : (n : ℝ) ≤ 1 / 2 := by linarith [hs.2, hn']
  have : (1 : ℤ) ≤ n := h0
  have : (n : ℝ) ≥ 1 := by exact_mod_cast this
  linarith

/-! ## The offset points lie off the axis of the configuration space -/

/-- **The capping radius of an offset point is positive.**  For `s ∈ [0,1/2]` the configuration point
`stripOffsetPt μ x s` is the chord of `γ` from `γ x` to `γ (x * exp (2π i s))`: for `s > 0` the chord
is non-degenerate (so its length coordinate is positive), and for `s = 0` the chord degenerates to the
point `γ x`, which is not the origin. -/
lemma stripOffset_confOf_fst_pos {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hγinj : Function.Injective γ) (hγne : ∀ x : Circle, γ x ≠ 0)
    (x : Circle) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    0 < (confOf (stripOffsetPt μ x s)).1 := by
  rcases eq_or_lt_of_le hs.1 with h0 | hpos
  · -- the diagonal: the chord is the point `γ x ≠ 0`
    subst h0
    have hconf : confOf (stripOffsetPt μ x 0) = confOf (γ x, tangentDirC γ x, 0) := by
      rw [stripOffsetPt_zero, hμdiag x]
    rw [hconf]
    have hne : (γ x).1 ≠ 0 ∨ (γ x).2 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hγne x (Prod.ext hc.1 hc.2)
    have hx : 0 < (γ x).1 ^ 2 + (γ x).2 ^ 2 + (0 : ℝ) ^ 2 := by
      rcases hne with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg (γ x).1,
        sq_nonneg (γ x).2]
    simp only [confOf]
    exact Real.sqrt_pos.mpr hx
  · -- a genuine chord: the length coordinate is positive
    have hne : x ≠ x * Circle.exp (2 * Real.pi * s) := offset_chord_ne x ⟨hpos, hs.2⟩
    have hlen : 0 < (stripOffsetPt μ x s).2.2 := by
      rw [stripOffsetPt, hμne x _ hne, muOrd]
      exact eucNorm_pos (fun h0 => hne (hγinj (sub_eq_zero.mp h0)))
    have hsq : (stripOffsetPt μ x s).2.2 ^ 2 ≤ (stripOffsetPt μ x s).1.1 ^ 2
        + (stripOffsetPt μ x s).1.2 ^ 2 + (stripOffsetPt μ x s).2.2 ^ 2 := by
      nlinarith [sq_nonneg (stripOffsetPt μ x s).1.1, sq_nonneg (stripOffsetPt μ x s).1.2]
    simp only [confOf]
    exact Real.sqrt_pos.mpr (lt_of_lt_of_le (pow_pos hlen 2) hsq)

/-! ## The strip chart -/

/-- **The strip chart of the capped plane.**  The class in the capping space of the offset chord with
endpoint `x` and offset `s`; the two side conditions are the ones supplied by
`Work.Drive.stripOffset_confOf_fst_pos` and `Work.Drive.confOf_snd_norm_le_one`. -/
def stripPt (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ) (u : UnitAddCircle) (x : Circle)
    (s : ℝ) (h1 : 0 < (confOf (stripOffsetPt μ x s)).1)
    (h2 : ‖(confOf (stripOffsetPt μ x s)).2.1‖ ≤ 1) : CappingSpace :=
  rotCapping u (Quotient.mk'' (Sum.inl (confPiece (stripOffsetPt μ x s) h1 h2)
    : ConfigPiece ⊕ CapPiece))

@[simp] lemma stripPt_def (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ) (u : UnitAddCircle)
    (x : Circle) (s : ℝ) (h1 : 0 < (confOf (stripOffsetPt μ x s)).1)
    (h2 : ‖(confOf (stripOffsetPt μ x s)).2.1‖ ≤ 1) :
    stripPt μ u x s h1 h2 = rotCapping u (Quotient.mk'' (Sum.inl
      (confPiece (stripOffsetPt μ x s) h1 h2) : ConfigPiece ⊕ CapPiece)) := rfl

/-- **The strip chart is injective up to the Möbius identification.**  Two offset chords give the same
point of the capped plane exactly when they are the same chord, or the two presentations `(x, 1/2)`
and `(-x, 1/2)` of a diameter. -/
lemma stripPt_eq_iff {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))
    (hlen : ∀ p : Circle × Circle, 0 ≤ (μ p).2.2)
    {u : UnitAddCircle} {x x' : Circle} {s s' : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (1 / 2))
    (hs' : s' ∈ Set.Icc (0 : ℝ) (1 / 2))
    (h1 : 0 < (confOf (stripOffsetPt μ x s)).1)
    (h2 : ‖(confOf (stripOffsetPt μ x s)).2.1‖ ≤ 1)
    (h1' : 0 < (confOf (stripOffsetPt μ x' s')).1)
    (h2' : ‖(confOf (stripOffsetPt μ x' s')).2.1‖ ≤ 1) :
    stripPt μ u x s h1 h2 = stripPt μ u x' s' h1' h2' ↔
      (x = x' ∧ s = s') ∨ (s = 1 / 2 ∧ s' = 1 / 2 ∧ x' = -x) := by
  rw [stripPt_def, stripPt_def, (rotCapping_injective u).eq_iff, Quotient.eq'']
  change cappingRel (Sum.inl (confPiece (stripOffsetPt μ x s) h1 h2))
      (Sum.inl (confPiece (stripOffsetPt μ x' s') h1' h2')) ↔
    ((x = x' ∧ s = s') ∨ (s = 1 / 2 ∧ s' = 1 / 2 ∧ x' = -x))
  rw [cappingRel_inl_inl, Subtype.ext_iff, confPiece_val, confPiece_val]
  constructor
  · intro h
    exact stripOffsetPt_confOf_injective μ hsym hinj hlen x x' s s' hs hs' h
  · rintro (⟨rfl, rfl⟩ | ⟨hs1, hs1', rfl⟩)
    · rfl
    · rw [hs1, hs1', (stripOffset_param μ hsym hinj).1 x]

/-! ## The cap chart -/

/-- **The cap chart of the capped plane.**  The class in the capping space of the cone point
`Work.Drive.capConePt` of the cap disk; the two side conditions are those of the `CapPiece` of the cone
(`Work.Drive.capConePt_pos`, `Work.Drive.capConePt_thd_norm_le_one`). -/
def capPtClass (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (s t : ℝ)
    (h1 : 0 < (capConePt r₀ ρ Ψ Θ u s t).1)
    (h2 : ‖(capConePt r₀ ρ Ψ Θ u s t).2.2‖ ≤ 1) : CappingSpace :=
  Quotient.mk'' (Sum.inr (⟨capConePt r₀ ρ Ψ Θ u s t, h1, h2⟩ : CapPiece)
    : ConfigPiece ⊕ CapPiece)

@[simp] lemma capPtClass_def (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) (s t : ℝ)
    (h1 : 0 < (capConePt r₀ ρ Ψ Θ u s t).1)
    (h2 : ‖(capConePt r₀ ρ Ψ Θ u s t).2.2‖ ≤ 1) :
    capPtClass r₀ ρ Ψ Θ u s t h1 h2 = Quotient.mk'' (Sum.inr
      (⟨capConePt r₀ ρ Ψ Θ u s t, h1, h2⟩ : CapPiece) : ConfigPiece ⊕ CapPiece) := rfl

/-- **The cap chart is injective in the cone parameter modulo `2π`.**  Two cone points with the same
class have the same cone parameter `s`, and if `s ≠ 0` then the two parameters `t`, `t'` define the
same point of the curve, i.e. `Circle.exp t = Circle.exp t'`. -/
lemma capPtClass_eq_imp {γ : Circle → ℝ × ℝ} {ρ Ψ : ℝ → ℝ}
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hγinj : Function.Injective γ) {Θ : ℝ → ℝ} {r₀ : ℝ} {u : UnitAddCircle} {s s' t t' : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hs' : s' ∈ Set.Icc (0 : ℝ) 1)
    (h1 : 0 < (capConePt r₀ ρ Ψ Θ u s t).1)
    (h2 : ‖(capConePt r₀ ρ Ψ Θ u s t).2.2‖ ≤ 1)
    (h1' : 0 < (capConePt r₀ ρ Ψ Θ u s' t').1)
    (h2' : ‖(capConePt r₀ ρ Ψ Θ u s' t').2.2‖ ≤ 1)
    (h : capPtClass r₀ ρ Ψ Θ u s t h1 h2 = capPtClass r₀ ρ Ψ Θ u s' t' h1' h2') :
    s = s' ∧ (s = 0 ∨ Circle.exp t = Circle.exp t') := by
  rw [capPtClass_def, capPtClass_def, Quotient.eq''] at h
  have hval : capConePt r₀ ρ Ψ Θ u s t = capConePt r₀ ρ Ψ Θ u s' t' :=
    congrArg Subtype.val (cappingRel_inr_inr.mp h)
  have h3 : (s : ℂ) * circleOf ((Ψ t : ℝ) : UnitAddCircle)
      = (s' : ℂ) * circleOf ((Ψ t' : ℝ) : UnitAddCircle) := by
    simpa only [capConePt_thd] using
      congrArg (fun p : ℝ × UnitAddCircle × ℂ => p.2.2) hval
  have hfr : (1 - s) * r₀ + s * ρ t = (1 - s') * r₀ + s' * ρ t' := by
    simpa only [capConePt_fst] using congrArg (fun p : ℝ × UnitAddCircle × ℂ => p.1) hval
  have hss : s = s' := by
    have hn : ‖(s : ℂ) * circleOf ((Ψ t : ℝ) : UnitAddCircle)‖
        = ‖(s' : ℂ) * circleOf ((Ψ t' : ℝ) : UnitAddCircle)‖ := by rw [h3]
    rw [norm_mul, norm_mul, norm_circleOf, norm_circleOf, mul_one, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs.1,
      abs_of_nonneg hs'.1] at hn
    exact hn
  refine ⟨hss, ?_⟩
  rcases eq_or_ne s 0 with h0 | hne
  · exact Or.inl h0
  · refine Or.inr ?_
    have hs'ne : s' ≠ 0 := by rw [← hss]; exact hne
    have hρeq : ρ t = ρ t' := by
      rw [hss] at hfr
      have h4 : s' * ρ t = s' * ρ t' := add_left_cancel hfr
      exact mul_left_cancel₀ hs'ne h4
    have hcc : circleOf ((Ψ t : ℝ) : UnitAddCircle)
        = circleOf ((Ψ t' : ℝ) : UnitAddCircle) := by
      rw [hss] at h3
      exact mul_left_cancel₀ (by exact_mod_cast hs'ne) h3
    have hpol : polarLift (ρ t, Ψ t) = polarLift (ρ t', Ψ t') :=
      polarLift_eq_of_circleOf_eq hρeq hcc
    rw [hpolar t, hpolar t'] at hpol
    exact hγinj hpol

/-! ## The two charts glue along the diagonal of the strip -/

/-- **The diagonal of the strip chart is the boundary of the cap chart.**  The strip point of the
degenerate chord at `x = Circle.exp t` is the cap point of parameter `s = 1` and the same `t`: this is
the gluing `∂M = ∂cap` of the capped plane. -/
lemma stripPt_zero_eq_capPtClass_one {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    {u : UnitAddCircle} (t : ℝ)
    (h1 : 0 < (confOf (stripOffsetPt μ (Circle.exp t) 0)).1)
    (h2 : ‖(confOf (stripOffsetPt μ (Circle.exp t) 0)).2.1‖ ≤ 1)
    (h1' : 0 < (capConePt r₀ ρ Ψ Θ u 1 t).1)
    (h2' : ‖(capConePt r₀ ρ Ψ Θ u 1 t).2.2‖ ≤ 1) :
    stripPt μ u (Circle.exp t) 0 h1 h2 = capPtClass r₀ ρ Ψ Θ u 1 t h1' h2' := by
  have hconf : confOf (γ (Circle.exp t), tangentDirC γ (Circle.exp t), 0)
      = (ρ t, circleOf ((Ψ t : ℝ) : UnitAddCircle), tangentDirC γ (Circle.exp t)) :=
    confOf_eq_of_polarLift (hρ t) (hpolar t) (tangentDirC γ (Circle.exp t))
  have hdiag1 : 0 < (confOf (γ (Circle.exp t), tangentDirC γ (Circle.exp t), 0)).1 := by
    rw [hconf]; exact hρ t
  have hdiag2 : ‖(confOf (γ (Circle.exp t), tangentDirC γ (Circle.exp t), 0)).2.1‖ ≤ 1 :=
    confOf_snd_norm_le_one _
  have hstrip : (confPiece (stripOffsetPt μ (Circle.exp t) 0) h1 h2 : ConfigPiece)
      = confPiece (γ (Circle.exp t), tangentDirC γ (Circle.exp t), 0) hdiag1 hdiag2 := by
    apply Subtype.ext
    rw [confPiece_val, confPiece_val, stripOffsetPt_zero, hμdiag]
  rw [stripPt_def, capPtClass_def, hstrip]
  exact (mk_capConePt_one_eq_rot_diag hr₀ hρ hpolar hΘclass t hdiag1 hdiag2).symm

/-! ## The two charts meet exactly along the gluing circle -/

/-- **The strip chart and the cap chart meet exactly along the gluing circle.**  If a strip point and a
cap point of the capped plane coincide, then the strip point is a diagonal point (`s = 0`), the cap
point is a boundary point of the cap disk (`s' = 1`) and the two parameters agree:
`x = Circle.exp t`. -/
lemma stripPt_eq_capPtClass_imp {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hγinj : Function.Injective γ)
    {ρ Ψ Θ : ℝ → ℝ} (hρpos : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    {r₀ : ℝ} {u : UnitAddCircle} {x : Circle} {s s' t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) (1 / 2)) (hs' : s' ∈ Set.Icc (0 : ℝ) 1)
    (h1 : 0 < (confOf (stripOffsetPt μ x s)).1)
    (h2 : ‖(confOf (stripOffsetPt μ x s)).2.1‖ ≤ 1)
    (h1' : 0 < (capConePt r₀ ρ Ψ Θ u s' t).1)
    (h2' : ‖(capConePt r₀ ρ Ψ Θ u s' t).2.2‖ ≤ 1)
    (h : stripPt μ u x s h1 h2 = capPtClass r₀ ρ Ψ Θ u s' t h1' h2') :
    s = 0 ∧ s' = 1 ∧ x = Circle.exp t := by
  set A : ConfigPiece := confPiece (stripOffsetPt μ x s) h1 h2 with hAdef
  set B : CapPiece := ⟨capConePt r₀ ρ Ψ Θ u s' t, h1', h2'⟩ with hBdef
  have hstripA : stripPt μ u x s h1 h2 = rotCapping u (Quotient.mk'' (Sum.inl A)) := by
    rw [stripPt_def, hAdef]
  have hcapB : capPtClass r₀ ρ Ψ Θ u s' t h1' h2' = Quotient.mk'' (Sum.inr B) := by
    rw [capPtClass_def, hBdef]
  have heq : rotCapping u (Quotient.mk'' (Sum.inl A)) = Quotient.mk'' (Sum.inr B) := by
    rw [← hstripA, ← hcapB]; exact h
  -- rotate back by `-u`
  have h0 : (Quotient.mk'' (Sum.inl A) : CappingSpace)
      = Quotient.mk'' (Sum.inr (rotCap (-u) B)) := by
    have h1 : rotCapping (-u) (Quotient.mk'' (Sum.inr B) : CappingSpace)
        = Quotient.mk'' (Sum.inr (rotCap (-u) B)) := by
      rw [rotCapping_mk, rotSum_inr]
    have h2 : rotCapping (-u) (rotCapping u (Quotient.mk'' (Sum.inl A) : CappingSpace))
        = Quotient.mk'' (Sum.inl A) := by
      rw [rotCapping_apply_add, neg_add_cancel, rotCapping_zero]; rfl
    rw [← h1, ← h2]
    exact congrArg (rotCapping (-u)) heq
  -- the cap parameter is `s' = 1`
  have hB3 : (rotCap (-u) B : CapPiece).1.2.2
      = (s' : ℂ) * circleOf ((Ψ t : ℝ) : UnitAddCircle) := by
    rw [hBdef]; rfl
  have hs'1 : s' = 1 := by
    have hnormB : ‖(rotCap (-u) B).1.2.2‖ = 1 := norm_thd_eq_one_of_mk_inl_eq_mk_inr h0
    rw [hB3, norm_mul, norm_circleOf, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs'.1] at hnormB
    exact hnormB
  have hrel := Quotient.exact h0
  rcases hrel with hcontra | ⟨r, hr, θ, φ, hcase | hcase⟩
  · exact absurd hcontra inl_ne_inr
  · obtain ⟨hA, hB⟩ := hcase
    have hA' : A = confBdy r hr φ (θ + 2 • φ) := Sum.inl.inj hA
    have hB' : rotCap (-u) B = capBdy r hr θ φ := Sum.inr.inj hB
    -- the configuration point is on the gluing circle, hence the chord degenerates: `s = 0`
    have hAval : (A : ℝ × ℂ × UnitAddCircle) = confOf (stripOffsetPt μ x s) := by
      rw [hAdef]; exact confPiece_val _ _ _
    have hAz : (A : ℝ × ℂ × UnitAddCircle).2.1 = circleOf φ := by rw [hA']; rfl
    have hlen0 : (stripOffsetPt μ x s).2.2 = 0 := by
      have hnorm1 : ‖(confOf (stripOffsetPt μ x s)).2.1‖ = 1 := by
        rw [← hAval, hAz, norm_circleOf]
      exact len_eq_zero_of_norm_confOf_snd_eq_one hnorm1
    have hs0 : s = 0 := by
      by_contra hsne
      have hpos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsne)
      have hne : x ≠ x * Circle.exp (2 * Real.pi * s) := offset_chord_ne x ⟨hpos, hs.2⟩
      have hlen : (stripOffsetPt μ x s).2.2
          = eucNorm (γ x - γ (x * Circle.exp (2 * Real.pi * s))) := by
        rw [stripOffsetPt, hμne x _ hne, muOrd]
      rw [hlen] at hlen0
      exact absurd hlen0 (ne_of_gt (eucNorm_pos (fun h0 => hne (hγinj (sub_eq_zero.mp h0)))))
    -- the angular parameters agree
    have hB3' : (rotCap (-u) B : CapPiece).1.2.2 = circleOf φ := by rw [hB']; rfl
    have hcφ : circleOf φ = circleOf ((Ψ t : ℝ) : UnitAddCircle) := by
      rw [← hB3', hB3, hs'1]
      simp
    have hφ : φ = ((Ψ t : ℝ) : UnitAddCircle) := circleOf_injective hcφ
    -- the configuration point is the diagonal point of `γ x`, whose radius is `r = ρ t`
    have hAval' : (A : ℝ × ℂ × UnitAddCircle) = confOf (γ x, tangentDirC γ x, 0) := by
      rw [hAdef, confPiece_val, hs0, stripOffsetPt_zero, hμdiag]
    have hconf : confOf (γ x, tangentDirC γ x, 0) = (r, circleOf φ, tangentDirC γ x) := by
      have h1 : confOf (γ x, tangentDirC γ x, 0) = (r, circleOf φ, θ + 2 • φ) := by
        rw [← hAval', hA']; rfl
      have h3 : θ + 2 • φ = tangentDirC γ x := by
        have h4 : (confOf (γ x, tangentDirC γ x, 0)).2.2 = tangentDirC γ x := rfl
        rw [h1] at h4
        exact h4
      rw [h1, h3]
    have hB1 : (rotCap (-u) B : CapPiece).1.1 = ρ t := by
      rw [hBdef]
      show (capConePt r₀ ρ Ψ Θ u s' t).1 = ρ t
      rw [hs'1, capConePt_one_fst]
    have hrρ : r = ρ t := by rw [← hB1, hB']; rfl
    have hrpos : 0 < r := by rw [hrρ]; exact hρpos t
    have hconf' : confOf (γ x, tangentDirC γ x, 0)
        = (ρ t, circleOf ((Ψ t : ℝ) : UnitAddCircle), tangentDirC γ x) := by
      rw [hconf, hφ, hrρ]
    have hpol : confOf (polarLift (ρ t, Ψ t), tangentDirC γ x, 0)
        = (ρ t, circleOf ((Ψ t : ℝ) : UnitAddCircle), tangentDirC γ x) :=
      confOf_eq_of_polarLift (hρpos t) rfl (tangentDirC γ x)
    have heq2 : polarLift (ρ t, Ψ t) = γ x := by
      have h := confOf_injective_of_nonneg (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
        (hpol.trans hconf'.symm)
      exact congrArg Prod.fst h
    exact ⟨hs0, hs'1, hγinj (by rw [← heq2, hpolar t])⟩
  · exact absurd hcase.1 inr_ne_inl

/-! ## The unit complex of a non-zero complex number -/

/-- The unit complex `z / ‖z‖` as an element of the circle `Circle = {w : ℂ // ‖w‖ = 1}`. -/
noncomputable def unitOf (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / (‖z‖ : ℂ), by
    change z / (‖z‖ : ℂ) ∈ (Submonoid.unitSphere ℂ : Set ℂ)
    rw [Submonoid.coe_unitSphere, Metric.mem_sphere, dist_eq_norm, sub_zero, norm_div,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z),
      div_self (norm_ne_zero_iff.mpr hz)]⟩

@[simp] lemma unitOf_coe (z : ℂ) (hz : z ≠ 0) :
    ((unitOf z hz : Circle) : ℂ) = z / (‖z‖ : ℂ) := rfl

/-- **`Circle.exp (arg z)` is the unit complex `z / ‖z‖`.** -/
lemma circle_exp_arg (z : ℂ) (hz : z ≠ 0) :
    ((Circle.exp (Complex.arg z) : Circle) : ℂ) = z / (‖z‖ : ℂ) := by
  rw [Circle.coe_exp]
  have h := Complex.norm_mul_exp_arg_mul_I z
  have hne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr hz
  rw [eq_div_iff hne, mul_comm]
  exact h

/-- The unit complex of `z` is `Circle.exp (arg z)`. -/
lemma unitOf_eq_circle_exp_arg (z : ℂ) (hz : z ≠ 0) :
    unitOf z hz = Circle.exp (Complex.arg z) :=
  Circle.ext (by rw [unitOf_coe, circle_exp_arg z hz])

/-- **The disk coordinate of a non-zero complex number in polar form**: `z = ‖z‖ · exp (arg z)`. -/
lemma norm_mul_circle_exp_arg (z : ℂ) (hz : z ≠ 0) :
    ((‖z‖ : ℂ) * ((Circle.exp (Complex.arg z) : Circle) : ℂ)) = z := by
  rw [mul_comm, circle_exp_arg z hz]
  have hne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr hz
  exact div_mul_cancel₀ z hne

/-! ## The two charts as maps on the disk -/

/-- **The cap branch of the disk presentation.**  On the inner disk `‖z‖ ≤ 1/2` the capped plane is
the cone `capCone`, parametrised by the cone parameter `s = 2‖z‖` and the angle `t = arg z` of `z`. -/
noncomputable def capDiskPt (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle)
    (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t) (z : ℂ) (hz : ‖z‖ < 1 / 2) : CappingSpace :=
  capPtClass r₀ ρ Ψ Θ u (2 * ‖z‖) (Complex.arg z)
    (capConePt_pos hr₀ hρ Ψ Θ u ⟨by linarith [norm_nonneg z], by linarith⟩)
    (capConePt_thd_norm_le_one r₀ ρ Ψ Θ u ⟨by linarith [norm_nonneg z], by linarith⟩)

@[simp] lemma capDiskPt_def (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle)
    (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t) (z : ℂ) (hz : ‖z‖ < 1 / 2) :
    capDiskPt r₀ ρ Ψ Θ u hr₀ hρ z hz =
      capPtClass r₀ ρ Ψ Θ u (2 * ‖z‖) (Complex.arg z)
        (capConePt_pos hr₀ hρ Ψ Θ u ⟨by linarith [norm_nonneg z], by linarith⟩)
        (capConePt_thd_norm_le_one r₀ ρ Ψ Θ u
          ⟨by linarith [norm_nonneg z], by linarith⟩) := rfl

/-- **The strip branch of the disk presentation.**  On the outer annulus `1/2 ≤ ‖z‖ ≤ 1` the capped
plane is the configuration strip, parametrised by the chord `(x, s)` with `x = z/‖z‖` and
`s = ‖z‖ - 1/2`. -/
noncomputable def stripDiskPt {γ : Circle → ℝ × ℝ}
    (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ) (u : UnitAddCircle)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (z : ℂ) (hz : 1 / 2 ≤ ‖z‖) (hz1 : ‖z‖ ≤ 1) : CappingSpace :=
  stripPt μ u (unitOf z (by
      have h0 : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hz
      exact norm_ne_zero_iff.mp (ne_of_gt h0))) (‖z‖ - 1 / 2)
    (stripOffset_confOf_fst_pos hμne hμdiag hγinj hγne _
      ⟨by linarith [norm_nonneg z], by linarith⟩)
    (confOf_snd_norm_le_one _)

/-- **The disk presentation of the capped plane.**  The map from the closed unit disk onto the capped
plane `P_u = u·M ∪ cap_u`: the inner disk `‖z‖ ≤ 1/2` is the cap cone (with the cone parameter
`s = 2‖z‖` and the angle `arg z`), the outer annulus `1/2 ≤ ‖z‖ ≤ 1` is the configuration strip (with
the chord `(z/‖z‖, ‖z‖ - 1/2)`), and the two pieces glue along the circle `‖z‖ = 1/2`. -/
noncomputable def diskPt {γ : Circle → ℝ × ℝ}
    (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ) (ρ Ψ Θ : ℝ → ℝ) (r₀ : ℝ)
    (u : UnitAddCircle) (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (z : ℂ) (hz1 : ‖z‖ ≤ 1) : CappingSpace :=
  if h : ‖z‖ < 1 / 2 then capDiskPt r₀ ρ Ψ Θ u hr₀ hρ z h
  else stripDiskPt μ u hγne hγinj hμne hμdiag z (le_of_not_gt h) hz1

lemma diskPt_of_lt {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ} {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ}
    {u : UnitAddCircle} {hr₀ : 0 < r₀} {hρ : ∀ t : ℝ, 0 < ρ t}
    {hγne : ∀ x : Circle, γ x ≠ 0} {hγinj : Function.Injective γ}
    {hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y)}
    {hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0)}
    {z : ℂ} {hz1 : ‖z‖ ≤ 1} (h : ‖z‖ < 1 / 2) :
    diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z hz1
      = capDiskPt r₀ ρ Ψ Θ u hr₀ hρ z h := by
  rw [diskPt, dif_pos h]

lemma diskPt_of_ge {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ} {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ}
    {u : UnitAddCircle} {hr₀ : 0 < r₀} {hρ : ∀ t : ℝ, 0 < ρ t}
    {hγne : ∀ x : Circle, γ x ≠ 0} {hγinj : Function.Injective γ}
    {hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y)}
    {hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0)}
    {z : ℂ} {hz1 : ‖z‖ ≤ 1} (h : 1 / 2 ≤ ‖z‖) :
    diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z hz1
      = stripDiskPt μ u hγne hγinj hμne hμdiag z h hz1 := by
  rw [diskPt, dif_neg (not_lt.mpr h)]

/-! ## The chart points lie in the capped plane -/

section Memberships

variable {γ : Circle → ℝ × ℝ}
variable {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
variable {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ} {u : UnitAddCircle}

/-- The strip chart is independent of the two side-condition proofs. -/
lemma stripPt_congr {x : Circle} {s : ℝ} (h1 : 0 < (confOf (stripOffsetPt μ x s)).1)
    (h2 : ‖(confOf (stripOffsetPt μ x s)).2.1‖ ≤ 1)
    (h1' : 0 < (confOf (stripOffsetPt μ x s)).1)
    (h2' : ‖(confOf (stripOffsetPt μ x s)).2.1‖ ≤ 1) :
    stripPt μ u x s h1 h2 = stripPt μ u x s h1' h2' := by
  rw [stripPt_def]

/-- The cap chart is independent of the two side-condition proofs. -/
lemma capPtClass_congr {s t : ℝ} (h1 : 0 < (capConePt r₀ ρ Ψ Θ u s t).1)
    (h2 : ‖(capConePt r₀ ρ Ψ Θ u s t).2.2‖ ≤ 1)
    (h1' : 0 < (capConePt r₀ ρ Ψ Θ u s t).1)
    (h2' : ‖(capConePt r₀ ρ Ψ Θ u s t).2.2‖ ≤ 1) :
    capPtClass r₀ ρ Ψ Θ u s t h1 h2 = capPtClass r₀ ρ Ψ Θ u s t h1' h2' := by
  rw [capPtClass_def]

/-- The strip chart lands in the capped plane. -/
lemma stripPt_mem_cappedPlane (x : Circle) (s : ℝ)
    (h1 : 0 < (confOf (stripOffsetPt μ x s)).1)
    (h2 : ‖(confOf (stripOffsetPt μ x s)).2.1‖ ≤ 1) :
    stripPt μ u x s h1 h2 ∈ cappedPlane r₀ ρ Ψ Θ μ u :=
  ⟨Quotient.mk'' (Sum.inl (confPiece (stripOffsetPt μ x s) h1 h2)
      : ConfigPiece ⊕ CapPiece), Or.inl ⟨_, h1, h2, rfl⟩, by rw [stripPt_def]⟩

/-- The cap chart lands in the capped plane. -/
lemma capPtClass_mem_cappedPlane {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (h1 : 0 < (capConePt r₀ ρ Ψ Θ u s t).1)
    (h2 : ‖(capConePt r₀ ρ Ψ Θ u s t).2.2‖ ≤ 1) :
    capPtClass r₀ ρ Ψ Θ u s t h1 h2 ∈ cappedPlane r₀ ρ Ψ Θ μ u := by
  set Q₁ : CapPiece := ⟨capConePt r₀ ρ Ψ Θ u s t, h1, h2⟩ with hQ₁
  set Q₀ : CapPiece := ⟨capConePt r₀ ρ Ψ Θ 0 s t,
    capConePt_pos hr₀ hρ Ψ Θ 0 hs, capConePt_thd_norm_le_one r₀ ρ Ψ Θ 0 hs⟩ with hQ₀
  have hrot : rotCap u Q₀ = Q₁ := by
    refine Subtype.ext ?_
    show (((capConePt r₀ ρ Ψ Θ 0 s t).1, (capConePt r₀ ρ Ψ Θ 0 s t).2.1 + u,
      (capConePt r₀ ρ Ψ Θ 0 s t).2.2) : ℝ × UnitAddCircle × ℂ) = capConePt r₀ ρ Ψ Θ u s t
    simp only [capConePt_fst, capConePt_snd, capConePt_thd]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    show (((Θ 0 + s * (Θ t - Θ 0) : ℝ) : UnitAddCircle) + 0) + u
      = (((Θ 0 + s * (Θ t - Θ 0) : ℝ) : UnitAddCircle)) + u
    rw [add_zero]
  refine ⟨Quotient.mk'' (Sum.inr Q₀ : ConfigPiece ⊕ CapPiece), Or.inr ⟨_, ?_, rfl⟩, ?_⟩
  · exact ⟨Q₀, capConePt_mem_capCone hr₀ hρ Ψ Θ 0 hs, rfl⟩
  · rw [rotCapping_mk, rotSum_inr, capPtClass_def, hrot, hQ₁]

end Memberships

/-! ## The range of the disk presentation -/

section DiskRange

variable {γ : Circle → ℝ × ℝ}
variable {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
variable {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ} {u : UnitAddCircle}

/-- Iterated `2π`-periodicity of a real-valued function. -/
lemma periodic_int_mul {B : Type*} {f : ℝ → B} (h : ∀ t : ℝ, f (t + 2 * Real.pi) = f t)
    (n : ℤ) (t : ℝ) : f (t + n * (2 * Real.pi)) = f t := by
  have hp : Function.Periodic f (2 * Real.pi) := h
  have h' := (hp.zsmul n) t
  rwa [zsmul_eq_mul] at h'

/-- Iterated `2π`-periodicity of `circleOf ∘ Ψ`. -/
lemma periodic_int_mul_circle {Ψ : ℝ → ℝ}
    (h : ∀ t : ℝ, circleOf ((Ψ (t + 2 * Real.pi) : ℝ) : UnitAddCircle)
      = circleOf ((Ψ t : ℝ) : UnitAddCircle)) (n : ℤ) (t : ℝ) :
    circleOf ((Ψ (t + n * (2 * Real.pi)) : ℝ) : UnitAddCircle)
      = circleOf ((Ψ t : ℝ) : UnitAddCircle) :=
  periodic_int_mul (f := fun τ : ℝ => circleOf ((Ψ τ : ℝ) : UnitAddCircle)) h n t

/-- The disk presentation maps the closed disk into the capped plane. -/
lemma diskPt_mem (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {z : ℂ} (hz1 : ‖z‖ ≤ 1) :
    diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z hz1
      ∈ cappedPlane r₀ ρ Ψ Θ μ u := by
  by_cases h : ‖z‖ < 1 / 2
  · rw [diskPt_of_lt h, capDiskPt_def]
    exact capPtClass_mem_cappedPlane (s := 2 * ‖z‖) (t := Complex.arg z)
      ⟨by linarith [norm_nonneg z], by linarith⟩ hr₀ hρ _ _
  · rw [diskPt_of_ge (le_of_not_gt h), stripDiskPt]
    exact stripPt_mem_cappedPlane _ _ _ _

/-- The two cap charts agree as soon as the cone points agree. -/
lemma capPtClass_congr' {s s' t t' : ℝ}
    (h1 : 0 < (capConePt r₀ ρ Ψ Θ u s t).1)
    (h2 : ‖(capConePt r₀ ρ Ψ Θ u s t).2.2‖ ≤ 1)
    (h1' : 0 < (capConePt r₀ ρ Ψ Θ u s' t').1)
    (h2' : ‖(capConePt r₀ ρ Ψ Θ u s' t').2.2‖ ≤ 1)
    (hv : capConePt r₀ ρ Ψ Θ u s t = capConePt r₀ ρ Ψ Θ u s' t') :
    capPtClass r₀ ρ Ψ Θ u s t h1 h2 = capPtClass r₀ ρ Ψ Θ u s' t' h1' h2' := by
  rw [capPtClass_def, capPtClass_def]
  exact congrArg (fun Q : CapPiece => Quotient.mk'' (Sum.inr Q : ConfigPiece ⊕ CapPiece))
    (Subtype.ext hv)

/-- The value of a rotated cap point. -/
lemma rotCap_val (v : UnitAddCircle) (Q : CapPiece) :
    ((rotCap v Q : CapPiece) : ℝ × UnitAddCircle × ℂ)
      = ((Q : ℝ × UnitAddCircle × ℂ).1, (Q : ℝ × UnitAddCircle × ℂ).2.1 + v,
          (Q : ℝ × UnitAddCircle × ℂ).2.2) := rfl

/-- The strip branch of the disk map at a point of the annulus, written as the strip chart. -/
lemma stripDiskPt_eq_of {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ} {u : UnitAddCircle}
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {z : ℂ} {x : Circle} {s : ℝ} (hzne : z ≠ 0)
    (hunit : ∀ h : z ≠ 0, unitOf z h = x) (hs : ‖z‖ - 1 / 2 = s)
    (h1 : 0 < (confOf (stripOffsetPt μ x s)).1)
    (h2 : ‖(confOf (stripOffsetPt μ x s)).2.1‖ ≤ 1)
    (hge : 1 / 2 ≤ ‖z‖) (hz1 : ‖z‖ ≤ 1) :
    stripDiskPt μ u hγne hγinj hμne hμdiag z hge hz1 = stripPt μ u x s h1 h2 := by
  rw [stripDiskPt, stripPt_def]
  refine congrArg (fun S : ConfigPiece =>
    rotCapping u (Quotient.mk'' (Sum.inl S : ConfigPiece ⊕ CapPiece))) (Subtype.ext ?_)
  rw [confPiece_val, confPiece_val, hunit, hs]

/-- **The disk presentation is surjective onto the capped plane.** -/
theorem exists_diskPt_eq_of_mem (hρper : ∀ t : ℝ, ρ (t + 2 * Real.pi) = ρ t)
    (hΨper : ∀ t : ℝ, circleOf ((Ψ (t + 2 * Real.pi) : ℝ) : UnitAddCircle)
      = circleOf ((Ψ t : ℝ) : UnitAddCircle))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))
    {p : CappingSpace} (hp : p ∈ cappedPlane r₀ ρ Ψ Θ μ u) :
    ∃ (z : ℂ) (hz : ‖z‖ ≤ 1),
      diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z hz = p := by
  rw [cappedPlane] at hp
  obtain ⟨q, hq, hpq⟩ := hp
  rw [Set.mem_union] at hq
  rcases hq with hqs | hqc
  · -- a point of the strip
    rw [stripImage_eq_offset_image μ hsym hinj] at hqs
    rw [Set.mem_image] at hqs
    obtain ⟨y, ⟨q', hq'mem, hy⟩, hqy⟩ := hqs
    obtain ⟨x, s, hs, hval⟩ := hq'mem
    have hval' : confOf (stripOffsetPt μ x s) = (q' : ℝ × ℂ × UnitAddCircle) := hval.symm
    have hq1 : 0 < (confOf (stripOffsetPt μ x s)).1 := by rw [hval']; exact q'.2.1
    have hq2 : ‖(confOf (stripOffsetPt μ x s)).2.1‖ ≤ 1 := by rw [hval']; exact q'.2.2
    have hq' : q' = confPiece (stripOffsetPt μ x s) hq1 hq2 := by
      refine Subtype.ext ?_
      rw [confPiece_val]
      exact hval'.symm
    set z : ℂ := ((1 / 2 + s : ℝ) : ℂ) * (x : ℂ) with hzdef
    have hznorm : ‖z‖ = 1 / 2 + s := by
      rw [hzdef, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [hs.1]),
        Circle.norm_coe, mul_one]
    have hz1 : ‖z‖ ≤ 1 := by rw [hznorm]; linarith [hs.2]
    have hzne : z ≠ 0 := by rw [← norm_ne_zero_iff, hznorm]; linarith [hs.1]
    have hge : 1 / 2 ≤ ‖z‖ := by rw [hznorm]; linarith [hs.1]
    have hunit : ∀ h : z ≠ 0, unitOf z h = x := by
      intro h
      refine Circle.ext ?_
      rw [unitOf_coe, hznorm, hzdef]
      exact mul_div_cancel_left₀ _ (by rw [Complex.ofReal_ne_zero]; linarith [hs.1])
    refine ⟨z, hz1, ?_⟩
    rw [← hpq, ← hqy, ← hy, hq']
    rw [diskPt_of_ge hge,
      stripDiskPt_eq_of hγne hγinj hμne hμdiag hzne hunit (by rw [hznorm]; ring) hq1 hq2 hge hz1,
      stripPt_def]
  · -- a point of the cap
    rw [Set.mem_image] at hqc
    obtain ⟨y, ⟨qC, hqCmem, hy⟩, hqy⟩ := hqc
    obtain ⟨s, t, hs, hval⟩ := hqCmem
    have hp' : p = rotCapping u (Quotient.mk'' (Sum.inr qC : ConfigPiece ⊕ CapPiece)) := by
      rw [← hpq, ← hqy, ← hy]
    have hvalT : (qC : ℝ × UnitAddCircle × ℂ) = ((1 - s) * r₀ + s * ρ t,
        (((Θ 0 + s * (Θ t - Θ 0) : ℝ)) : UnitAddCircle) + 0,
        (s : ℂ) * circleOf ((Ψ t : ℝ) : UnitAddCircle)) := hval
    by_cases hs1 : s = 1
    · -- the boundary of the cap disk is the diagonal of the strip
      set z : ℂ := ((1 / 2 : ℝ) : ℂ) * ((Circle.exp t : Circle) : ℂ) with hzdef
      have hznorm : ‖z‖ = 1 / 2 := by
        rw [hzdef, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), Circle.norm_coe, mul_one]
      have hz1 : ‖z‖ ≤ 1 := by rw [hznorm]; norm_num
      have hzne : z ≠ 0 := by rw [← norm_ne_zero_iff, hznorm]; norm_num
      have hge : 1 / 2 ≤ ‖z‖ := by rw [hznorm]
      have hunit : ∀ h : z ≠ 0, unitOf z h = Circle.exp t := by
        intro h
        refine Circle.ext ?_
        rw [unitOf_coe, hznorm, hzdef]
        exact mul_div_cancel_left₀ _ (by norm_num : (((1 / 2 : ℝ)) : ℂ) ≠ 0)
      have h1s : 0 < (confOf (stripOffsetPt μ (Circle.exp t) 0)).1 :=
        stripOffset_confOf_fst_pos hμne hμdiag hγinj hγne (Circle.exp t)
          ⟨le_refl 0, by norm_num⟩
      have h2s : ‖(confOf (stripOffsetPt μ (Circle.exp t) 0)).2.1‖ ≤ 1 :=
        confOf_snd_norm_le_one _
      have h1c : 0 < (capConePt r₀ ρ Ψ Θ u 1 t).1 :=
        capConePt_pos hr₀ hρ Ψ Θ u (s := 1) (t := t) ⟨by norm_num, by norm_num⟩
      have h2c : ‖(capConePt r₀ ρ Ψ Θ u 1 t).2.2‖ ≤ 1 :=
        capConePt_thd_norm_le_one r₀ ρ Ψ Θ u (s := 1) (t := t) ⟨by norm_num, by norm_num⟩
      have hang : Θ 0 + 1 * (Θ t - Θ 0) = Θ t := by ring
      refine ⟨z, hz1, ?_⟩
      rw [hp', diskPt_of_ge hge,
        stripDiskPt_eq_of hγne hγinj hμne hμdiag hzne hunit
          (show ‖z‖ - 1 / 2 = 0 from by rw [hznorm]; ring) h1s h2s hge hz1,
        stripPt_zero_eq_capPtClass_one hμdiag hr₀ hρ hpolar hΘclass t h1s h2s h1c h2c,
        capPtClass_def, rotCapping_mk, rotSum_inr]
      refine congrArg (fun Q : CapPiece =>
        Quotient.mk'' (Sum.inr Q : ConfigPiece ⊕ CapPiece)) (Subtype.ext ?_)
      rw [rotCap_val, hvalT]
      change (capConePt r₀ ρ Ψ Θ u 1 t : ℝ × UnitAddCircle × ℂ) = _
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp only [capConePt_fst, hs1]
      · simp only [capConePt_snd, hs1]; rw [hang]; simp
      · simp only [capConePt_thd, hs1]
    · by_cases hs0 : s = 0
      · -- the apex
        have hz1 : ‖(0 : ℂ)‖ ≤ 1 := by norm_num
        have hlt : ‖(0 : ℂ)‖ < 1 / 2 := by norm_num
        refine ⟨0, hz1, ?_⟩
        rw [hp', diskPt_of_lt hlt, capDiskPt_def, capPtClass_def, rotCapping_mk, rotSum_inr]
        refine congrArg (fun Q : CapPiece =>
          Quotient.mk'' (Sum.inr Q : ConfigPiece ⊕ CapPiece)) (Subtype.ext ?_)
        rw [rotCap_val, hvalT]
        change (capConePt r₀ ρ Ψ Θ u (2 * ‖(0 : ℂ)‖) (Complex.arg 0) : ℝ × UnitAddCircle × ℂ) = _
        rw [show (2 : ℝ) * ‖(0 : ℂ)‖ = 0 from by norm_num, Complex.arg_zero]
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · simp only [capConePt_fst, hs0]; ring
        · simp only [capConePt_snd, hs0]; simp
        · simp only [capConePt_thd, hs0]; simp
      · -- a genuine interior point of the cap disk
        have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
        have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
        set z : ℂ := (((s / 2 : ℝ)) : ℂ) * ((Circle.exp t : Circle) : ℂ) with hzdef
        have hznorm : ‖z‖ = s / 2 := by
          rw [hzdef, norm_mul, Complex.norm_real,
            Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ s / 2), Circle.norm_coe, mul_one]
        have hz1 : ‖z‖ ≤ 1 := by rw [hznorm]; linarith
        have hzne : z ≠ 0 := by rw [← norm_ne_zero_iff, hznorm]; linarith
        have hlt : ‖z‖ < 1 / 2 := by rw [hznorm]; linarith
        refine ⟨z, hz1, ?_⟩
        -- the angle of `z` is `t` modulo `2π`
        have hcirc : Circle.exp (Complex.arg z) = Circle.exp t := by
          refine Circle.ext ?_
          rw [circle_exp_arg z hzne, hznorm, hzdef]
          exact mul_div_cancel_left₀ _ (by rw [Complex.ofReal_ne_zero]; linarith)
        obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcirc
        have hρeq : ρ (Complex.arg z) = ρ t := by
          rw [hm]; exact periodic_int_mul hρper m t
        have hΘeq : Θ (Complex.arg z) = Θ t := by
          rw [hm]; exact periodic_int_mul hΘper m t
        have hΨeq : circleOf ((Ψ (Complex.arg z) : ℝ) : UnitAddCircle)
            = circleOf ((Ψ t : ℝ) : UnitAddCircle) := by
          rw [hm]; exact periodic_int_mul_circle hΨper m t
        rw [hp', diskPt_of_lt hlt, capDiskPt_def, capPtClass_def, rotCapping_mk, rotSum_inr]
        refine congrArg (fun Q : CapPiece =>
          Quotient.mk'' (Sum.inr Q : ConfigPiece ⊕ CapPiece)) (Subtype.ext ?_)
        rw [rotCap_val, hvalT]
        change (capConePt r₀ ρ Ψ Θ u (2 * ‖z‖) (Complex.arg z) : ℝ × UnitAddCircle × ℂ) = _
        rw [show (2 : ℝ) * ‖z‖ = s from by rw [hznorm]; ring]
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · simp only [capConePt_fst]; rw [hρeq]
        · simp only [capConePt_snd]; rw [hΘeq]; simp
        · simp only [capConePt_thd]; rw [hΨeq]
end DiskRange

/-! ## The fibres of the disk presentation -/

section DiskFibres

variable {γ : Circle → ℝ × ℝ}
variable {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
variable {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ} {u : UnitAddCircle}

/-- The length coordinate of the configuration point `μ (x, y)` is non-negative. -/
lemma stripOffsetPt_len_nonneg
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0)) :
    ∀ p : Circle × Circle, 0 ≤ (μ p).2.2 := by
  rintro ⟨x, y⟩
  rcases eq_or_ne x y with h | h
  · rw [h, hμdiag]
  · rw [hμne x y h, muOrd]; exact eucNorm_nonneg _

/-- A non-zero complex number is its norm times its unit complex. -/
lemma eq_norm_mul_unitOf (z : ℂ) (hz : z ≠ 0) :
    z = ((‖z‖ : ℝ) : ℂ) * ((unitOf z hz : Circle) : ℂ) := by
  rw [unitOf_coe, mul_comm, div_mul_cancel₀ z (by
    rw [Complex.ofReal_ne_zero]
    exact norm_ne_zero_iff.mpr hz)]

/-- A non-zero complex number is its norm times the exponential of its argument. -/
lemma eq_norm_mul_circle_exp_arg (z : ℂ) (hz : z ≠ 0) :
    z = ((‖z‖ : ℝ) : ℂ) * ((Circle.exp (Complex.arg z) : Circle) : ℂ) :=
  (norm_mul_circle_exp_arg z hz).symm

/-- **The cap branch of the disk presentation is injective.** -/
lemma capDiskPt_eq_imp (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hγinj : Function.Injective γ) {z z' : ℂ} (hlt : ‖z‖ < 1 / 2) (hlt' : ‖z'‖ < 1 / 2)
    (h : capDiskPt r₀ ρ Ψ Θ u hr₀ hρ z hlt = capDiskPt r₀ ρ Ψ Θ u hr₀ hρ z' hlt') :
    z = z' := by
  rw [capDiskPt_def, capDiskPt_def] at h
  have h' := capPtClass_eq_imp hpolar hγinj
    (s := 2 * ‖z‖) (t := Complex.arg z) (s' := 2 * ‖z'‖) (t' := Complex.arg z')
    ⟨by linarith [norm_nonneg z], by linarith⟩ ⟨by linarith [norm_nonneg z'], by linarith⟩
    _ _ _ _ h
  obtain ⟨hs, hcase⟩ := h'
  have hn : ‖z‖ = ‖z'‖ := by linarith
  rcases hcase with h0 | harg
  · -- both points are the centre
    have hz : ‖z‖ = 0 := by linarith
    have hz' : ‖z'‖ = 0 := by linarith
    have hz0 : z = 0 := by rw [← norm_eq_zero]; exact hz
    have hz0' : z' = 0 := by rw [← norm_eq_zero]; exact hz'
    rw [hz0, hz0']
  · -- same argument, same norm
    rcases eq_or_ne z 0 with hz0 | hz0
    · have hz' : z' = 0 := by
        rw [← norm_eq_zero, ← hn, hz0, norm_zero]
      rw [hz0, hz']
    · have hz'ne : z' ≠ 0 := by
        intro hz''; rw [hz'', norm_zero] at hn
        exact hz0 (by rw [← norm_eq_zero]; exact hn)
      rw [eq_norm_mul_circle_exp_arg z hz0, eq_norm_mul_circle_exp_arg z' hz'ne, ← hn, harg]

/-- **The strip branch of the disk presentation is injective** up to the antipodal
identification of the boundary circle. -/
lemma stripDiskPt_eq_imp
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))
    (hlen : ∀ p : Circle × Circle, 0 ≤ (μ p).2.2)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {z z' : ℂ} (hge : 1 / 2 ≤ ‖z‖) (hge' : 1 / 2 ≤ ‖z'‖) (hz1 : ‖z‖ ≤ 1) (hz1' : ‖z'‖ ≤ 1)
    (h : stripDiskPt μ u hγne hγinj hμne hμdiag z hge hz1
      = stripDiskPt μ u hγne hγinj hμne hμdiag z' hge' hz1') :
    z = z' ∨ (‖z‖ = 1 ∧ ‖z'‖ = 1 ∧ z' = -z) := by
  have hzne : z ≠ 0 := by
    intro hz; rw [hz, norm_zero] at hge; linarith
  have hz'ne : z' ≠ 0 := by
    intro hz; rw [hz, norm_zero] at hge'; linarith
  rw [stripDiskPt, stripDiskPt] at h
  rw [stripPt_eq_iff hsym hinj hlen (x := unitOf z _) (x' := unitOf z' _)
    (s := ‖z‖ - 1 / 2) (s' := ‖z'‖ - 1 / 2)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ _ _ _ _] at h
  rcases h with ⟨hx, hs⟩ | ⟨hs, hs', hx⟩
  · -- the same chord
    refine Or.inl ?_
    have hn : ‖z‖ = ‖z'‖ := by linarith
    have hxe : ((unitOf z hzne : Circle) : ℂ) = ((unitOf z' hz'ne : Circle) : ℂ) :=
      congrArg Subtype.val hx
    rw [eq_norm_mul_unitOf z hzne, eq_norm_mul_unitOf z' hz'ne, hn, hxe]
  · -- the two presentations of a diameter
    refine Or.inr ⟨by linarith, by linarith, ?_⟩
    have hn : ‖z‖ = ‖z'‖ := by linarith
    have hxe : ((unitOf z' hz'ne : Circle) : ℂ) = -((unitOf z hzne : Circle) : ℂ) := by
      rw [hx]; rfl
    rw [eq_norm_mul_unitOf z hzne, eq_norm_mul_unitOf z' hz'ne, hn, hxe]
    norm_num

end DiskFibres

/-! ## Periodicity of the polar data

The `2π`-periodicity of the radius `ρ` and of the direction `circleOf ∘ Ψ` is a consequence of the
polar relation `polarLift (ρ t, Ψ t) = γ (Circle.exp t)` alone: `Circle.exp` is `2π`-periodic, and the
polar lift determines both the radius (through its euclidean norm) and the direction. -/

section PolarPeriodic

open Submission.Geometry (eucNorm eucNorm_sq eucNorm_nonneg eucDot eucDot_mk)

variable {γ : Circle → ℝ × ℝ} {ρ Ψ : ℝ → ℝ}

/-- `Circle.exp` is `2π`-periodic. -/
lemma circle_exp_add_two_pi (t : ℝ) : Circle.exp (t + 2 * Real.pi) = Circle.exp t := by
  rw [Circle.exp_eq_exp]
  exact ⟨1, by ring⟩

/-- The euclidean norm of a polar lift is the radius (up to the sign). -/
lemma eucNorm_polarLift (r ψ : ℝ) : eucNorm (polarLift (r, ψ)) = |r| := by
  have hdot : eucDot (polarLift (r, ψ)) (polarLift (r, ψ)) = r ^ 2 := by
    simp only [eucDot_mk, polarLift]
    rw [← sq, ← sq, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  rw [eucNorm, hdot, Real.sqrt_sq_eq_abs]

/-- The direction of a polar lift is `circleOf ψ`. -/
lemma polarLift_div_eq_circleOf {r ψ : ℝ} (hr : 0 < r) :
    (⟨(polarLift (r, ψ)).1 / r, (polarLift (r, ψ)).2 / r⟩ : ℂ)
      = circleOf ((ψ : ℝ) : UnitAddCircle) := by
  refine Complex.ext ?_ ?_
  · rw [circleOf_coe_re]
    simp only [Complex.ofReal_re, polarLift, Prod.fst]
    field_simp
  · rw [circleOf_coe_im]
    simp only [Complex.ofReal_im, polarLift, Prod.snd]
    field_simp

/-- **The polar data is `2π`-periodic.** -/
lemma polarLift_periodic_of_eq (hρpos : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t)) :
    (∀ t : ℝ, ρ (t + 2 * Real.pi) = ρ t) ∧
      (∀ t : ℝ, circleOf ((Ψ (t + 2 * Real.pi) : ℝ) : UnitAddCircle)
        = circleOf ((Ψ t : ℝ) : UnitAddCircle)) := by
  have hstep : ∀ t : ℝ, polarLift (ρ (t + 2 * Real.pi), Ψ (t + 2 * Real.pi))
      = polarLift (ρ t, Ψ t) := by
    intro t
    rw [hpolar (t + 2 * Real.pi), hpolar t, circle_exp_add_two_pi t]
  have hnorm : ∀ t : ℝ, eucNorm (polarLift (ρ (t + 2 * Real.pi), Ψ (t + 2 * Real.pi)))
      = eucNorm (polarLift (ρ t, Ψ t)) := fun t => congrArg eucNorm (hstep t)
  constructor
  · intro t
    have h := hnorm t
    rw [eucNorm_polarLift, eucNorm_polarLift, abs_of_pos (hρpos _), abs_of_pos (hρpos _)] at h
    exact h
  · intro t
    have hpairs := congrArg (fun x : ℝ × ℝ => (⟨x.1, x.2⟩ : ℂ)) (hstep t)
    have hre : (polarLift (ρ (t + 2 * Real.pi), Ψ (t + 2 * Real.pi))).1
        = (polarLift (ρ t, Ψ t)).1 := by
      have := congrArg Complex.re hpairs
      simpa using this
    have him : (polarLift (ρ (t + 2 * Real.pi), Ψ (t + 2 * Real.pi))).2
        = (polarLift (ρ t, Ψ t)).2 := by
      have := congrArg Complex.im hpairs
      simpa using this
    have h1 := polarLift_div_eq_circleOf (r := ρ (t + 2 * Real.pi)) (ψ := Ψ (t + 2 * Real.pi))
      (hρpos (t + 2 * Real.pi))
    have h2 := polarLift_div_eq_circleOf (r := ρ t) (ψ := Ψ t) (hρpos t)
    have hr : ρ (t + 2 * Real.pi) = ρ t := by
      have h := hnorm t
      rw [eucNorm_polarLift, eucNorm_polarLift, abs_of_pos (hρpos _), abs_of_pos (hρpos _)] at h
      exact h
    have hcomp : (⟨(polarLift (ρ (t + 2 * Real.pi), Ψ (t + 2 * Real.pi))).1
            / ρ (t + 2 * Real.pi),
          (polarLift (ρ (t + 2 * Real.pi), Ψ (t + 2 * Real.pi))).2
            / ρ (t + 2 * Real.pi)⟩ : ℂ)
        = ⟨(polarLift (ρ t, Ψ t)).1 / ρ t, (polarLift (ρ t, Ψ t)).2 / ρ t⟩ := by
      rw [hre, him, hr]
    rw [← h1, hcomp, h2]

end PolarPeriodic

section DiskPresentation

variable {γ : Circle → ℝ × ℝ}
variable {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
variable {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ} {u : UnitAddCircle}

/-- The unit complex of `-z` is the negative of the unit complex of `z`. -/
lemma unitOf_neg (z : ℂ) (hz : z ≠ 0) (hz' : -z ≠ 0) :
    unitOf (-z) hz' = - unitOf z hz := by
  refine Circle.ext ?_
  rw [unitOf_coe, norm_neg, Circle.coe_neg, unitOf_coe, neg_div]

/-- **The disk presentation of the capped plane is a bijection onto the capped plane modulo the
antipodal identification of the boundary circle.**  Two points of the closed unit disk have the same
image in `P_u = u·M ∪ cap_u` exactly when they are equal, or are antipodal points of the boundary
circle `‖z‖ = 1` (the circle that maps onto the core of the Möbius band). -/
theorem diskPt_eq_iff (hρper : ∀ t : ℝ, ρ (t + 2 * Real.pi) = ρ t)
    (hΨper : ∀ t : ℝ, circleOf ((Ψ (t + 2 * Real.pi) : ℝ) : UnitAddCircle)
      = circleOf ((Ψ t : ℝ) : UnitAddCircle))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x'))
    {z z' : ℂ} (hz1 : ‖z‖ ≤ 1) (hz1' : ‖z'‖ ≤ 1) :
    diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z hz1
        = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z' hz1'
      ↔ z = z' ∨ (‖z‖ = 1 ∧ ‖z'‖ = 1 ∧ z' = -z) := by
  have hlen := stripOffsetPt_len_nonneg (γ := γ) hμne hμdiag
  by_cases h : ‖z‖ < 1 / 2
  · by_cases h' : ‖z'‖ < 1 / 2
    · -- both points are in the cap disk
      simp only [diskPt_of_lt h, diskPt_of_lt h']
      constructor
      · intro heq
        exact Or.inl (capDiskPt_eq_imp hr₀ hρ hpolar hγinj h h' heq)
      · rintro (hzz | ⟨hz1eq, -, -⟩)
        · subst hzz; rfl
        · exact absurd hz1eq (by linarith)
    · -- `z` in the cap disk but `z'` in the strip: impossible
      have hge' : 1 / 2 ≤ ‖z'‖ := le_of_not_gt h'
      simp only [diskPt_of_lt h, diskPt_of_ge hge']
      constructor
      · intro heq
        exfalso
        have hsp : stripPt μ u (unitOf z' _) (‖z'‖ - 1 / 2) _ _
            = capPtClass r₀ ρ Ψ Θ u (2 * ‖z‖) (Complex.arg z) _ _ := heq.symm
        obtain ⟨h0, h1c, -⟩ := stripPt_eq_capPtClass_imp hμne hμdiag hγinj hρ hpolar
          (s := ‖z'‖ - 1 / 2) (s' := 2 * ‖z‖) (t := Complex.arg z) (x := unitOf z' _)
          ⟨by linarith, by linarith⟩ ⟨by linarith [norm_nonneg z], by linarith⟩
          _ _ _ _ hsp
        linarith
      · rintro (hzz | ⟨hz1eq, -, -⟩)
        · subst hzz; linarith
        · exact absurd hz1eq (by linarith)
  · -- `z` is in the strip
    have hge : 1 / 2 ≤ ‖z‖ := le_of_not_gt h
    by_cases h' : ‖z'‖ < 1 / 2
    · -- `z'` in the cap disk but `z` in the strip: impossible
      simp only [diskPt_of_ge hge, diskPt_of_lt h']
      constructor
      · intro heq
        exfalso
        have hsp : stripPt μ u (unitOf z _) (‖z‖ - 1 / 2) _ _
            = capPtClass r₀ ρ Ψ Θ u (2 * ‖z'‖) (Complex.arg z') _ _ := heq
        obtain ⟨h0, h1c, -⟩ := stripPt_eq_capPtClass_imp hμne hμdiag hγinj hρ hpolar
          (s := ‖z‖ - 1 / 2) (s' := 2 * ‖z'‖) (t := Complex.arg z') (x := unitOf z _)
          ⟨by linarith, by linarith⟩ ⟨by linarith [norm_nonneg z'], by linarith⟩
          _ _ _ _ hsp
        linarith
      · rintro (hzz | ⟨-, hz1eq, -⟩)
        · subst hzz; linarith
        · exact absurd hz1eq (by linarith)
    · -- both points are in the strip
      have hge' : 1 / 2 ≤ ‖z'‖ := le_of_not_gt h'
      simp only [diskPt_of_ge hge, diskPt_of_ge hge']
      constructor
      · intro heq
        rcases stripDiskPt_eq_imp hsym hinj hlen hγne hγinj hμne hμdiag hge hge' hz1 hz1' heq
          with hzz | ⟨h1, h2, h3⟩
        · exact Or.inl hzz
        · exact Or.inr ⟨h1, h2, h3⟩
      · rintro (hzz | ⟨h1, h2, h3⟩)
        · subst hzz; rfl
        · -- antipodal points of the boundary circle: the two presentations of a diameter
          have hzn : ‖z‖ = 1 := h1
          have hzne : z ≠ 0 := by rw [← norm_ne_zero_iff, hzn]; norm_num
          have hnegne : -z ≠ 0 := neg_ne_zero.mpr hzne
          subst h3
          simp only [diskPt_of_ge (by rw [hzn]; norm_num),
            diskPt_of_ge (by rw [norm_neg, hzn]; norm_num),
            stripDiskPt, unitOf_neg z hzne hnegne]
          refine (stripPt_eq_iff hsym hinj hlen (x := unitOf z _) (x' := - unitOf z _)
            (s := ‖z‖ - 1 / 2) (s' := ‖-z‖ - 1 / 2) ⟨by linarith, by linarith⟩
            ⟨by rw [norm_neg]; linarith, by rw [norm_neg]; linarith⟩ _ _ _ _).mpr ?_
          exact Or.inr ⟨by rw [hzn]; norm_num, by rw [norm_neg, hzn]; norm_num, rfl⟩

/-- **The disk presentation maps the closed unit disk onto the capped plane.** -/
theorem diskPt_range (hρper : ∀ t : ℝ, ρ (t + 2 * Real.pi) = ρ t)
    (hΨper : ∀ t : ℝ, circleOf ((Ψ (t + 2 * Real.pi) : ℝ) : UnitAddCircle)
      = circleOf ((Ψ t : ℝ) : UnitAddCircle))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) :
    Set.range (fun w : {z : ℂ // ‖z‖ ≤ 1} =>
      diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag w.1 w.2)
      = cappedPlane r₀ ρ Ψ Θ μ u := by
  ext p
  constructor
  · rintro ⟨w, rfl⟩
    exact diskPt_mem hr₀ hρ hγne hγinj hμne hμdiag w.2
  · intro hp
    obtain ⟨z, hz, hzeq⟩ := exists_diskPt_eq_of_mem hρper hΨper hΘper hr₀ hρ hpolar hΘclass
      hγne hγinj hμne hμdiag hsym hinj hp
    exact ⟨⟨z, hz⟩, hzeq⟩

/-- **The capped plane is the disk with its boundary circle identified antipodally.**  The disk
presentation `Work.Drive.diskPt` maps the closed unit disk onto `P_u = u·M ∪ cap_u`, and two points
have the same image exactly when they are equal or antipodal points of the boundary circle.  This is
the disk model `D̄/∼` of `ℝP²` used by the intersection-form chapter
(`Submission/Work/Drive/Surf/Model.lean`): the boundary circle maps two-to-one onto the core of the
Möbius band `M`, and the two halves of the disk are the cap (`‖z‖ ≤ 1/2`) and the strip
(`1/2 ≤ ‖z‖ ≤ 1`). -/
theorem cappedPlane_diskPresentation (hρper : ∀ t : ℝ, ρ (t + 2 * Real.pi) = ρ t)
    (hΨper : ∀ t : ℝ, circleOf ((Ψ (t + 2 * Real.pi) : ℝ) : UnitAddCircle)
      = circleOf ((Ψ t : ℝ) : UnitAddCircle))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) :
    Set.range (fun w : {z : ℂ // ‖z‖ ≤ 1} =>
        diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag w.1 w.2)
        = cappedPlane r₀ ρ Ψ Θ μ u ∧
      (∀ (z z' : ℂ) (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1),
        diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z hz
            = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z' hz'
          ↔ z = z' ∨ (‖z‖ = 1 ∧ ‖z'‖ = 1 ∧ z' = -z)) :=
  ⟨diskPt_range hρper hΨper hΘper hr₀ hρ hpolar hΘclass hγne hγinj hμne hμdiag hsym hinj,
    fun z z' hz hz' => diskPt_eq_iff hρper hΨper hΘper hr₀ hρ hpolar hΘclass hγne hγinj
      hμne hμdiag hsym hinj hz hz'⟩

/-- **The capped plane is the disk with its boundary circle identified antipodally**, with the
`2π`-periodicity of the radius `ρ` and of the direction `circleOf ∘ Ψ` derived from the polar relation
`polarLift (ρ t, Ψ t) = γ (Circle.exp t)` (so that only the cap angle `Θ` needs its periodicity as a
hypothesis). -/
theorem cappedPlane_diskPresentation_of_polarLift
    (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hpolar : ∀ t : ℝ, polarLift (ρ t, Ψ t) = γ (Circle.exp t))
    (hΘper : ∀ t : ℝ, Θ (t + 2 * Real.pi) = Θ t)
    (hΘclass : ∀ t : ℝ, ((Θ t : ℝ) : UnitAddCircle)
      = tangentDirC γ (Circle.exp t) - 2 • ((Ψ t : ℝ) : UnitAddCircle))
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (hsym : ∀ x y : Circle, μ (y, x) = μ (x, y))
    (hinj : ∀ x y x' y' : Circle, μ (x, y) = μ (x', y') →
      (x = x' ∧ y = y') ∨ (x = y' ∧ y = x')) :
    Set.range (fun w : {z : ℂ // ‖z‖ ≤ 1} =>
        diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag w.1 w.2)
        = cappedPlane r₀ ρ Ψ Θ μ u ∧
      (∀ (z z' : ℂ) (hz : ‖z‖ ≤ 1) (hz' : ‖z'‖ ≤ 1),
        diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z hz
            = diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z' hz'
          ↔ z = z' ∨ (‖z‖ = 1 ∧ ‖z'‖ = 1 ∧ z' = -z)) :=
  cappedPlane_diskPresentation (polarLift_periodic_of_eq hρ hpolar).1
    (polarLift_periodic_of_eq hρ hpolar).2 hΘper hr₀ hρ hpolar hΘclass hγne hγinj hμne hμdiag
    hsym hinj

end DiskPresentation

/-! ## The boundary circle maps onto the core of the Möbius band -/

section BoundaryCore

variable {γ : Circle → ℝ × ℝ}
variable {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
variable {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ} {u : UnitAddCircle}
variable {hr₀ : 0 < r₀} {hρ : ∀ t : ℝ, 0 < ρ t}
variable {hγne : ∀ x : Circle, γ x ≠ 0}
variable {hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0)}

open Submission.Configuration (muOrd)

/-- A configuration point whose length coordinate is positive has positive capping radius. -/
lemma confOf_fst_pos_of_len_pos {p : (ℝ × ℝ) × UnitAddCircle × ℝ} (h : 0 < p.2.2) :
    0 < (confOf p).1 := by
  have hsq : p.2.2 ^ 2 ≤ p.1.1 ^ 2 + p.1.2 ^ 2 + p.2.2 ^ 2 := by
    nlinarith [sq_nonneg p.1.1, sq_nonneg p.1.2]
  simp only [confOf]
  exact Real.sqrt_pos.mpr (lt_of_lt_of_le (pow_pos h 2) hsq)

/-- No element of the circle is its own antipode. -/
lemma circle_ne_neg_self (x : Circle) : x ≠ -x := by
  intro h
  have hc : (x : ℂ) = -(x : ℂ) := congrArg Subtype.val h
  have h' : (2 : ℂ) * (x : ℂ) = 0 := by linear_combination hc
  have hx : (x : ℂ) = 0 := by
    rcases mul_eq_zero.mp h' with h2 | h2
    · norm_num at h2
    · exact h2
  have := Circle.norm_coe x
  rw [hx, norm_zero] at this
  norm_num at this

/-- The length coordinate of the diametral configuration `coreLoopPt γ θ` is positive. -/
lemma coreLoopPt_len_pos {γ : Circle → ℝ × ℝ} (hγinj : Function.Injective γ) (θ : ℝ) :
    0 < (coreLoopPt γ θ).2.2 := by
  rw [coreLoopPt, muOrd]
  refine eucNorm_pos ?_
  intro h0
  exact circle_ne_neg_self (corePt θ) (hγinj (sub_eq_zero.mp h0))

/-- The unit complex of a point of the unit circle is the core parameter `corePt (arg z / π)`. -/
lemma unitOf_eq_corePt {z : ℂ} (hz : ‖z‖ = 1) (hzne : z ≠ 0) :
    unitOf z hzne = corePt (Complex.arg z / Real.pi) := by
  refine Circle.ext ?_
  rw [unitOf_coe, corePt, Circle.coe_exp, hz]
  rw [show z / (((1 : ℝ)) : ℂ) = z from by rw [Complex.ofReal_one, div_one]]
  have h2 : ↑(‖z‖) * Complex.exp (↑z.arg * Complex.I) = z := Complex.norm_mul_exp_arg_mul_I z
  rw [hz] at h2
  have hexp : Complex.exp (↑z.arg * Complex.I) = z := by simpa using h2
  rw [show Real.pi * (z.arg / Real.pi) = z.arg from by field_simp]
  exact hexp.symm

/-- The offset chord at offset `1/2` through `corePt θ` is the diametral configuration. -/
lemma stripOffsetPt_half_eq_coreLoopPt {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y)) (θ : ℝ) :
    stripOffsetPt μ (corePt θ) (1 / 2) = coreLoopPt γ θ := by
  have hπ : (2 : ℝ) * Real.pi * (1 / 2) = Real.pi := by ring
  rw [stripOffsetPt, hπ, circle_exp_pi, mul_neg, mul_one, coreLoopPt]
  exact hμne _ _ (circle_ne_neg_self _)

/-- **The boundary circle of the disk maps onto the core of the Möbius band.**  The disk point `z`
with `‖z‖ = 1` is the class of the diametral configuration `coreLoopPt γ (arg z / π)`: the boundary
circle of the disk model is the core of `M`, i.e. the projective line of `P_u`. -/
theorem diskPt_boundary_eq_core
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hγinj : Function.Injective γ) {z : ℂ} (hz : ‖z‖ = 1) (hz1 : ‖z‖ ≤ 1) :
    diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z hz1
      = rotCapping u (Quotient.mk'' (Sum.inl (confPiece
          (coreLoopPt γ (Complex.arg z / Real.pi))
          (confOf_fst_pos_of_len_pos (coreLoopPt_len_pos hγinj _))
          (confOf_snd_norm_le_one _)) : ConfigPiece ⊕ CapPiece)) := by
  have hzne : z ≠ 0 := by rw [← norm_ne_zero_iff, hz]; norm_num
  have hge : 1 / 2 ≤ ‖z‖ := by rw [hz]; norm_num
  have hs : ‖z‖ - 1 / 2 = 1 / 2 := by rw [hz]; norm_num
  rw [diskPt_of_ge hge, stripDiskPt, stripPt_def]
  refine congrArg (fun S : ConfigPiece =>
    rotCapping u (Quotient.mk'' (Sum.inl S : ConfigPiece ⊕ CapPiece))) (Subtype.ext ?_)
  rw [confPiece_val, confPiece_val]
  rw [show unitOf z _ = corePt (Complex.arg z / Real.pi) from unitOf_eq_corePt hz hzne, hs,
    stripOffsetPt_half_eq_coreLoopPt hμne]

/-- **Every point of the core is the image of a boundary point of the disk**: the core loop
`coreLoopPt` (the projective line of `P_u`) is exhausted by the image of the boundary circle under the
disk presentation. -/
theorem exists_diskPt_eq_coreLoopPt
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hγinj : Function.Injective γ) (θ : ℝ) :
    ∃ (z : ℂ) (hz : ‖z‖ = 1),
      diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z (le_of_eq hz)
        = rotCapping u (Quotient.mk'' (Sum.inl (confPiece (coreLoopPt γ θ)
            (confOf_fst_pos_of_len_pos (coreLoopPt_len_pos hγinj θ))
            (confOf_snd_norm_le_one _)) : ConfigPiece ⊕ CapPiece)) := by
  refine ⟨((corePt θ : Circle) : ℂ), Circle.norm_coe _, ?_⟩
  have hexp : Circle.exp (Complex.arg (((corePt θ : Circle) : ℂ))) = corePt θ := by
    refine Subtype.ext ?_
    rw [circle_exp_arg _ (by rw [← norm_ne_zero_iff, Circle.norm_coe]; norm_num),
      Circle.norm_coe]
    rw [show (((corePt θ : Circle) : ℂ) / (((1 : ℝ)) : ℂ)) = ((corePt θ : Circle) : ℂ) from by
      rw [Complex.ofReal_one, div_one]]
  have hexp2 : Circle.exp (Complex.arg (((corePt θ : Circle) : ℂ))) = Circle.exp (Real.pi * θ) := by
    rw [hexp]; rfl
  obtain ⟨n, hn⟩ := circle_exp_eq_iff_exists_int.mp hexp2
  have harg : Complex.arg (((corePt θ : Circle) : ℂ)) / Real.pi = θ + 2 * (n : ℝ) := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have hn' : Complex.arg (((corePt θ : Circle) : ℂ)) = Real.pi * θ + 2 * Real.pi * (n : ℝ) := by
      linarith [hn]
    rw [hn']
    field_simp
  rw [diskPt_boundary_eq_core hμne hγinj (Circle.norm_coe _) (le_of_eq (Circle.norm_coe _))]
  refine congrArg (fun S : ConfigPiece =>
    rotCapping u (Quotient.mk'' (Sum.inl S : ConfigPiece ⊕ CapPiece))) (Subtype.ext ?_)
  have hper : Function.Periodic (coreLoopPt γ) 1 := coreLoopPt_periodic γ
  have hcore : coreLoopPt γ (Complex.arg (((corePt θ : Circle) : ℂ)) / Real.pi) = coreLoopPt γ θ := by
    rw [harg]
    have h2 := (hper.zsmul (2 * n)) θ
    simpa [zsmul_one, two_mul] using h2
  rw [confPiece_val, confPiece_val, hcore]

end BoundaryCore

end Work.Drive
