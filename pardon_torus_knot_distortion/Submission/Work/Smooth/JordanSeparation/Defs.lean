import Mathlib
import Submission.Work.Smooth.Jordan.All

/-!
# The vocabulary of the smooth Jordan separation chapter

This file fixes the objects in which the proof of the **Jordan separation theorem for a simple
closed plane curve** is carried out (the hypothesis `Work.Smooth.Jordan.PlaneJordanSchoenflies`
of the sibling chapter `Submission/Work/Smooth/Jordan`).

The strategy is the classical one, in the *regular neighbourhood* form:

* for a `C¹` closed curve `c : ℝ → ℂ` which is an immersion (`deriv c.γ t ≠ 0`), the
  **normal field** `normalField c t = I·γ'(t)/‖γ'(t)‖` is a continuous unit field perpendicular
  to the curve;
* choosing instead a field `v` which is *uniformly transverse* to the curve
  (`IsTransverseUnitField c κ v`) and *Lipschitz*, the **offset map**
  `offset c v (t,u) = c.γ t + u·v t` is injective on the strip `ℝ × (-δ,δ)` modulo the period
  `2π` for small `δ`; its image `annulus c v δ` is thus a genuine product neighbourhood of the
  trace, whose trace-complement splits into the two **sides** `posPart c v δ`, `negPart c v δ`;
* every component of `c.traceᶜ` contains one of the two sides, so there are at most two
  (`atMostTwo_connectedComponentIn`);
* the index `ind c` jumps by `±1` when one crosses the curve at a regular point (`ind_jump`),
  so there are at least two.

## Main definitions

* `detV u w` — the oriented determinant (area) of two vectors of `ℂ ≅ ℝ²`;
* `unitTangent c t`, `normalField c t` — the unit tangent `γ'(t)/‖γ'(t)‖` and the unit normal
  `I·γ'(t)/‖γ'(t)‖`;
* `IsTransverseUnitField c κ v` — `v` is a unit field subtending an angle of at least `arcsin κ`
  with the curve at every point;
* `IsLipschitzField L v` — a global Lipschitz bound on a field;
* `offset c v p` — the normal-offset map `(t,u) ↦ c.γ t + u·v t`;
* `annulus c v δ`, `posPart c v δ`, `negPart c v δ`, `zeroPart c v` — the product neighbourhood
  of the trace and its two open halves and its core.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-! ## The oriented determinant of two vectors of `ℂ` -/

/-- The **oriented determinant** of two vectors of `ℂ = ℝ²`: for `u = u₁ + i u₂` and
`w = w₁ + i w₂` this is `u₁w₂ - u₂w₁ = Im(conj u * w)`.  It vanishes exactly when the two vectors
are parallel, and `|detV u w| = ‖u‖‖w‖·|sin θ|` where `θ` is the angle between them. -/
def detV (u w : ℂ) : ℝ := ((starRingEnd ℂ) u * w).im

theorem detV_def (u w : ℂ) : detV u w = ((starRingEnd ℂ) u * w).im := rfl

/-- The oriented determinant in terms of the real coordinates. -/
theorem detV_eq (u w : ℂ) : detV u w = u.re * w.im - u.im * w.re := by
  rw [detV, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

@[simp] theorem detV_self (u : ℂ) : detV u u = 0 := by rw [detV_eq]; ring

@[simp] theorem detV_zero_left (w : ℂ) : detV 0 w = 0 := by rw [detV_eq]; simp

@[simp] theorem detV_zero_right (u : ℂ) : detV u 0 = 0 := by rw [detV_eq]; simp

@[simp] theorem detV_neg_left (u w : ℂ) : detV (-u) w = -detV u w := by
  rw [detV_eq, detV_eq]; simp only [Complex.neg_re, Complex.neg_im]; ring

@[simp] theorem detV_neg_right (u w : ℂ) : detV u (-w) = -detV u w := by
  rw [detV_eq, detV_eq]; simp only [Complex.neg_re, Complex.neg_im]; ring

theorem detV_swap (u w : ℂ) : detV w u = -detV u w := by
  rw [detV_eq, detV_eq]; ring

theorem detV_smul_left (r : ℝ) (u w : ℂ) : detV ((r : ℂ) * u) w = r * detV u w := by
  rw [detV_eq, detV_eq]; simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]; ring

theorem detV_smul_right (r : ℝ) (u w : ℂ) : detV u ((r : ℂ) * w) = r * detV u w := by
  rw [detV_eq, detV_eq]; simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]; ring

theorem detV_add_left (u₁ u₂ w : ℂ) : detV (u₁ + u₂) w = detV u₁ w + detV u₂ w := by
  rw [detV_eq, detV_eq, detV_eq]; simp only [Complex.add_re, Complex.add_im]; ring

theorem detV_add_right (u w₁ w₂ : ℂ) : detV u (w₁ + w₂) = detV u w₁ + detV u w₂ := by
  rw [detV_eq, detV_eq, detV_eq]; simp only [Complex.add_re, Complex.add_im]; ring

/-- `detV u w = 0` exactly when the two vectors are linearly dependent over `ℝ`. -/
theorem detV_eq_zero_iff (u w : ℂ) :
    detV u w = 0 ↔ ∃ r : ℝ, w = (r : ℂ) * u ∨ u = (r : ℂ) * w := by
  constructor
  · intro h
    rcases eq_or_ne u 0 with hu | hu
    · subst hu; exact ⟨0, Or.inr (by simp)⟩
    · have him : (w / u).im = detV u w / Complex.normSq u := by
        rw [Complex.div_im, detV_eq]; ring
      have h0 : (w / u).im = 0 := by rw [him, h]; simp
      have hw : w / u = ((w / u).re : ℂ) := by
        refine Complex.ext (by simp) ?_
        simpa using h0
      refine ⟨(w / u).re, Or.inl ?_⟩
      rw [← hw]
      exact (div_mul_cancel₀ w hu).symm
  · rintro ⟨r, h | h⟩
    · rw [h, detV_smul_right, detV_self, mul_zero]
    · rw [h, detV_smul_left, detV_self, mul_zero]

/-- The determinant is bounded by the product of the norms: it is an area. -/
theorem abs_detV_le (u w : ℂ) : |detV u w| ≤ ‖u‖ * ‖w‖ := by
  rw [detV_def, ← norm_star u, ← norm_mul]
  exact Complex.abs_im_le_norm _

theorem detV_ne_zero_iff (u w : ℂ) :
    detV u w ≠ 0 ↔ ∀ r : ℝ, w ≠ (r : ℂ) * u ∧ u ≠ (r : ℂ) * w := by
  rw [ne_eq, detV_eq_zero_iff]
  constructor
  · intro h r
    exact ⟨fun hw => h ⟨r, Or.inl hw⟩, fun hu => h ⟨r, Or.inr hu⟩⟩
  · rintro h ⟨r, hr | hr⟩
    · exact (h r).1 hr
    · exact (h r).2 hr

/-! ## The unit tangent and the normal field of an immersed curve -/

/-- The **unit tangent** of a `C¹` curve: `γ'(t)/‖γ'(t)‖`.  For a non-immersion the
denominator vanishes and the field is `0`; all statements about it carry `c.IsImmersion`. -/
def unitTangent (c : SmoothPlaneCurve) (t : ℝ) : ℂ :=
  deriv c.γ t / ((‖deriv c.γ t‖ : ℝ) : ℂ)

/-- The **normal field** of a `C¹` curve: `I·γ'(t)/‖γ'(t)‖`, the unit tangent rotated by `90°`. -/
def normalField (c : SmoothPlaneCurve) (t : ℝ) : ℂ := Complex.I * unitTangent c t

theorem unitTangent_def (c : SmoothPlaneCurve) (t : ℝ) :
    unitTangent c t = deriv c.γ t / ((‖deriv c.γ t‖ : ℝ) : ℂ) := rfl

theorem normalField_def (c : SmoothPlaneCurve) (t : ℝ) :
    normalField c t = Complex.I * unitTangent c t := rfl

theorem norm_unitTangent (c : SmoothPlaneCurve) (h : c.IsImmersion) (t : ℝ) :
    ‖unitTangent c t‖ = 1 := by
  have hd : deriv c.γ t ≠ 0 := h t
  have hpos : (0 : ℝ) < ‖deriv c.γ t‖ := norm_pos_iff.mpr hd
  refine Eq.trans ?_ (div_self (ne_of_gt hpos))
  rw [unitTangent, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos.le]

theorem norm_normalField (c : SmoothPlaneCurve) (h : c.IsImmersion) (t : ℝ) :
    ‖normalField c t‖ = 1 := by
  rw [normalField, norm_mul, Complex.norm_I, one_mul, norm_unitTangent c h t]

theorem continuous_unitTangent (c : SmoothPlaneCurve) (h : c.IsImmersion) :
    Continuous (unitTangent c) := by
  have hnorm : Continuous fun t : ℝ => ‖deriv c.γ t‖ := c.continuous_deriv.norm
  refine c.continuous_deriv.div (Complex.continuous_ofReal.comp hnorm) (fun t => ?_)
  simp only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]
  exact h t

theorem continuous_unitTangent' (c : SmoothPlaneCurve) (h : c.IsImmersion) :
    Continuous (unitTangent c) := continuous_unitTangent c h

theorem continuous_normalField (c : SmoothPlaneCurve) (h : c.IsImmersion) :
    Continuous (normalField c) := continuous_const.mul (continuous_unitTangent c h)

theorem periodic_unitTangent (c : SmoothPlaneCurve) (h : c.IsImmersion) :
    Function.Periodic (unitTangent c) (2 * Real.pi) := by
  intro t
  have hfun : (fun s : ℝ => c.γ (s + 2 * Real.pi)) = c.γ := funext fun s => c.periodic_apply s
  have hderiv : deriv c.γ (t + 2 * Real.pi) = deriv c.γ t := by
    rw [← deriv_comp_add_const c.γ (2 * Real.pi) t, hfun]
  simp only [unitTangent, hderiv]

theorem periodic_normalField (c : SmoothPlaneCurve) (h : c.IsImmersion) :
    Function.Periodic (normalField c) (2 * Real.pi) :=
  fun t => by simp only [normalField, periodic_unitTangent c h t]

theorem detV_deriv_normalField (c : SmoothPlaneCurve) (h : c.IsImmersion) (t : ℝ) :
    detV (deriv c.γ t) (normalField c t) = ‖deriv c.γ t‖ := by
  have hd : deriv c.γ t ≠ 0 := h t
  have hr : (0 : ℝ) < ‖deriv c.γ t‖ := norm_pos_iff.mpr hd
  have hreal : normalField c t
      = (((‖deriv c.γ t‖)⁻¹ : ℝ) : ℂ) * (Complex.I * deriv c.γ t) := by
    rw [normalField, unitTangent, div_eq_mul_inv, ← Complex.ofReal_inv]; ring
  have hsq : detV (deriv c.γ t) (Complex.I * deriv c.γ t) = ‖deriv c.γ t‖ ^ 2 := by
    rw [detV_eq, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    simp only [zero_mul, zero_sub, one_mul, sub_zero, sub_neg_eq_add]
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hreal, detV_smul_right, hsq, pow_two, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), one_mul]

/-! ## Transverse Lipschitz unit fields -/

/-- `IsTransverseUnitField c κ v` says that `v` is a field of **unit** vectors which is
**uniformly transverse** to the immersed curve `c`: the oriented determinant of the derivative of
`c` with `v` is at least `κ‖γ'‖` in absolute value, i.e. the angle between `v t` and the tangent
is at least `arcsin κ` everywhere. -/
def IsTransverseUnitField (c : SmoothPlaneCurve) (κ : ℝ) (v : ℝ → ℂ) : Prop :=
  (∀ t : ℝ, ‖v t‖ = 1) ∧
    (∀ t : ℝ, κ * ‖deriv c.γ t‖ ≤ |detV (deriv c.γ t) (v t)|)

/-- `IsLipschitzField L v` says that `v` is globally `L`-Lipschitz. -/
def IsLipschitzField (L : ℝ) (v : ℝ → ℂ) : Prop := ∀ t t' : ℝ, ‖v t - v t'‖ ≤ L * |t - t'|

/-! ## The offset map of a field -/

/-- The **offset map** of a field `v` along a curve `c`: `(t,u) ↦ c.γ t + u·v t`.  For `v` the
normal field this is the normal parametrisation of a tubular neighbourhood of the curve. -/
def offset (c : SmoothPlaneCurve) (v : ℝ → ℂ) (p : ℝ × ℝ) : ℂ := c.γ p.1 + p.2 * v p.1

theorem offset_def (c : SmoothPlaneCurve) (v : ℝ → ℂ) (p : ℝ × ℝ) :
    offset c v p = c.γ p.1 + p.2 * v p.1 := rfl

@[simp] theorem offset_zero (c : SmoothPlaneCurve) (v : ℝ → ℂ) (t : ℝ) :
    offset c v (t, 0) = c.γ t := by simp [offset]

theorem continuous_offset (c : SmoothPlaneCurve) {v : ℝ → ℂ} (hv : Continuous v) :
    Continuous (offset c v) := by
  unfold offset
  exact (c.cont.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul (hv.comp continuous_fst))

theorem offset_periodic (c : SmoothPlaneCurve) {v : ℝ → ℂ} (hv : Function.Periodic v (2 * Real.pi))
    (t : ℝ) (u : ℝ) :
    offset c v (t + 2 * Real.pi, u) = offset c v (t, u) := by
  simp only [offset, c.periodic_apply t, hv t]

/-- The **core** of the offset neighbourhood: the offset at `u = 0`, which is the curve itself. -/
def zeroPart (c : SmoothPlaneCurve) (v : ℝ → ℂ) : Set ℂ :=
  offset c v '' ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ))

/-- The **positive side** of the offset neighbourhood: the offsets with `0 < u < δ`. -/
def posPart (c : SmoothPlaneCurve) (v : ℝ → ℂ) (δ : ℝ) : Set ℂ :=
  offset c v '' ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 δ)

/-- The **negative side** of the offset neighbourhood: the offsets with `-δ < u < 0`. -/
def negPart (c : SmoothPlaneCurve) (v : ℝ → ℂ) (δ : ℝ) : Set ℂ :=
  offset c v '' ((Set.univ : Set ℝ) ×ˢ Set.Ioo (-δ) 0)

/-- The **offset neighbourhood** of the curve: the union of the two sides and the core. -/
def annulus (c : SmoothPlaneCurve) (v : ℝ → ℂ) (δ : ℝ) : Set ℂ :=
  offset c v '' ((Set.univ : Set ℝ) ×ˢ Set.Ioo (-δ) δ)

theorem zeroPart_eq_trace (c : SmoothPlaneCurve) (v : ℝ → ℂ) :
    zeroPart c v = c.trace := by
  ext z
  constructor
  · rintro ⟨p, ⟨-, hp⟩, rfl⟩
    have h2 : p.2 = 0 := by simpa using hp
    exact ⟨p.1, by rw [offset, h2]; simp⟩
  · rintro ⟨t, rfl⟩
    exact ⟨(t, 0), ⟨trivial, rfl⟩, by simp [offset]⟩

theorem annulus_eq (c : SmoothPlaneCurve) (v : ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    annulus c v δ = posPart c v δ ∪ negPart c v δ ∪ zeroPart c v := by
  ext z
  constructor
  · rintro ⟨p, ⟨-, hp⟩, rfl⟩
    rcases lt_trichotomy p.2 0 with h | h | h
    · exact Or.inl (Or.inr ⟨p, ⟨trivial, ⟨by linarith [hp.1], h⟩⟩, rfl⟩)
    · exact Or.inr ⟨p, ⟨trivial, by simpa using h⟩, rfl⟩
    · exact Or.inl (Or.inl ⟨p, ⟨trivial, ⟨h, hp.2⟩⟩, rfl⟩)
  · rintro ((⟨p, ⟨-, hp⟩, hz⟩ | ⟨p, ⟨-, hp⟩, hz⟩) | ⟨p, ⟨-, hp⟩, hz⟩)
    · exact ⟨p, ⟨trivial, ⟨by linarith [hδ, hp.1], hp.2⟩⟩, hz⟩
    · exact ⟨p, ⟨trivial, ⟨hp.1, by linarith [hδ, hp.2]⟩⟩, hz⟩
    · have hp0 : p.2 = 0 := by simpa using hp
      refine ⟨p, ⟨trivial, ?_⟩, hz⟩
      rw [hp0]; exact ⟨neg_lt_zero.mpr hδ, hδ⟩

theorem posPart_subset_annulus (c : SmoothPlaneCurve) (v : ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    posPart c v δ ⊆ annulus c v δ :=
  fun z hz => (annulus_eq c v hδ).symm ▸ Or.inl (Or.inl hz)

theorem negPart_subset_annulus (c : SmoothPlaneCurve) (v : ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    negPart c v δ ⊆ annulus c v δ :=
  fun z hz => (annulus_eq c v hδ).symm ▸ Or.inl (Or.inr hz)

theorem zeroPart_subset_annulus (c : SmoothPlaneCurve) (v : ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    zeroPart c v ⊆ annulus c v δ :=
  fun z hz => (annulus_eq c v hδ).symm ▸ Or.inr hz

theorem trace_subset_annulus (c : SmoothPlaneCurve) (v : ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ) :
    c.trace ⊆ annulus c v δ := by
  rw [← zeroPart_eq_trace c v]
  exact zeroPart_subset_annulus c v hδ

theorem posPart_isPreconnected (c : SmoothPlaneCurve) {v : ℝ → ℂ} (hv : Continuous v) (δ : ℝ) :
    IsPreconnected (posPart c v δ) :=
  IsPreconnected.image (isPreconnected_univ.prod isPreconnected_Ioo) _
    (continuous_offset c hv).continuousOn

theorem negPart_isPreconnected (c : SmoothPlaneCurve) {v : ℝ → ℂ} (hv : Continuous v) (δ : ℝ) :
    IsPreconnected (negPart c v δ) :=
  IsPreconnected.image (isPreconnected_univ.prod isPreconnected_Ioo) _
    (continuous_offset c hv).continuousOn

end

end Work.Smooth.JordanSeparation
