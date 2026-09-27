import Mathlib
import Submission.Work.Drive.LensSpaceGlue

/-!
# The two branches of the glueing map `S³ → LensSpace` agree on the common boundary torus

`Submission.Work.Drive.LensSpaceGlue` defines the two branches `capPt` and `confPt` of the glueing map
`phi : S³ → LensSpace = L(2,1)`:

* on the cap hemisphere `{|z₁| ≤ |z₂|}` (where `z₁ = c₁ v`, `z₂ = c₂ v`),
  `capPt (z₁,z₂) = ( (‖z₂‖/z₂)² , √2 z₁z₂/‖z₂‖ ) ∈ S¹ × D²`,
* on the configuration hemisphere `{|z₂| ≤ |z₁|}`,
  `confPt (z₁,z₂) = ( √2 z₂z₁/‖z₁‖ , (z₁/‖z₁‖)² ) ∈ D² × S¹`,

and `lensRel` identifies the cap boundary point `(θ, w)` with the configuration boundary point
`(w, θ w²)`.

This file proves that the two branches *agree in the quotient* on the common boundary
`{|z₁| = |z₂|} = {|z₁| = |z₂| = 1/√2}`, where writing `z₁ = e^{iα}/√2`, `z₂ = e^{iβ}/√2`:

`capPt = (e^{-2iβ}, e^{i(α+β)})`  and  `confPt = (e^{i(α+β)}, e^{2iα})`,

so that the cap point `(θ, w) = (e^{-2iβ}, e^{i(α+β)})` is glued by `lensRel` to
`(w, θ w²) = (e^{i(α+β)}, e^{2iα}) = confPt`.

The proof is the algebraic identity `(m/z₂)² · (√2 z₁z₂/m)² = (z₁/m)²` for `m = ‖z₁‖ = ‖z₂‖ = 1/√2`,
which is exactly `2 m² = 1`.
-/

namespace Work.Drive

noncomputable section

/-! ## Unfolding the two branch maps

The four lemmas below read off the coordinates of `capPt` and `confPt`: they are definitional, but
stated in the general form (with the subtype proof still the variable `w.2`) so that `rfl` applies. -/

lemma capPt_fst (w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖}) :
    (capPt w).1 = circOf ((((‖c₂ w.1.1‖ : ℝ) : ℂ) / c₂ w.1.1) ^ 2)
      (norm_sq_self_div _ (ne_zero_of_norm_le w.2 (sq_norm_eq_one w.1))) := rfl

lemma capPt_snd (w : {v : unitSphere 3 // ‖c₁ v.1‖ ≤ ‖c₂ v.1‖}) :
    ((capPt w).2 : ℂ) =
      (Real.sqrt 2 : ℂ) * c₁ w.1.1 * c₂ w.1.1 / ((‖c₂ w.1.1‖ : ℝ) : ℂ) := rfl

lemma confPt_fst (w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖}) :
    ((confPt w).1 : ℂ) =
      (Real.sqrt 2 : ℂ) * c₂ w.1.1 * c₁ w.1.1 / ((‖c₁ w.1.1‖ : ℝ) : ℂ) := rfl

lemma confPt_snd (w : {v : unitSphere 3 // ‖c₂ v.1‖ ≤ ‖c₁ v.1‖}) :
    (confPt w).2 = circOf ((c₁ w.1.1 / ((‖c₁ w.1.1‖ : ℝ) : ℂ)) ^ 2)
      (norm_sq_div_self _ (ne_zero_of_norm_le w.2 (sq_norm_eq_one_comm w.1))) := rfl

/-! ## The arithmetic of the Clifford torus `m = 1/√2` -/

/-- If `2 m² = 1` and `m ≥ 0` (so `m = 1/√2`) then `√2 · m = 1`. -/
lemma sqrt_two_mul_eq_one {m : ℝ} (hm : 2 * m ^ 2 = 1) (hm0 : 0 ≤ m) :
    Real.sqrt 2 * m = 1 := by
  have hsq : (Real.sqrt 2 * m) ^ 2 = 1 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  rcases sq_eq_one_iff.mp hsq with hh | hh
  · exact hh
  · nlinarith [Real.sqrt_nonneg 2, hm0]

/-- The disk coordinate `√2 z₁z₂/‖z₂‖` of `capPt` lies on the unit circle when `z₁` and `z₂` have the
common norm `m = 1/√2`. -/
lemma norm_sqrt_two_mul_mul_div {z₁ z₂ : ℂ} {m : ℝ} (hm : 2 * m ^ 2 = 1)
    (h₁ : ‖z₁‖ = m) (h₂ : ‖z₂‖ = m) :
    ‖(Real.sqrt 2 : ℂ) * z₁ * z₂ / ((m : ℝ) : ℂ)‖ = 1 := by
  have hm0 : 0 ≤ m := h₂ ▸ norm_nonneg z₂
  have hne : m ≠ 0 := by intro h0; rw [h0] at hm; norm_num at hm
  have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hne)
  rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg hm0,
    h₁, h₂]
  rw [mul_div_cancel_right₀ _ hne]
  exact sqrt_two_mul_eq_one hm hm0

/-- **The defining identity of the glueing on the Clifford torus.**  For `m = 1/√2` (i.e. `2 m² = 1`)
the two boundary coordinates match:

`(m/z₂)² · (√2 z₁z₂/m)² = (z₁/m)²`.

Indeed the left hand side is `(m²/z₂²)·(2 z₁²z₂²/m²) = 2z₁²` and the right hand side is
`z₁²/m² = 2z₁²`. -/
lemma div_sq_mul_div_sq {z₁ z₂ : ℂ} {m : ℝ} (hm : 2 * m ^ 2 = 1) (hz₂ : z₂ ≠ 0) :
    (z₁ / (m : ℂ)) ^ 2 = ((m : ℂ) / z₂) ^ 2 * ((Real.sqrt 2 : ℂ) * z₁ * z₂ / (m : ℂ)) ^ 2 := by
  have hmne : m ≠ 0 := by intro h0; rw [h0] at hm; norm_num at hm
  have hmC : ((m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmne
  have hs2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hmcsq : 2 * ((m : ℂ)) ^ 2 = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hm
    push_cast at this
    simpa using this
  have hm2 : ((m : ℂ)) ^ 2 = 1 / 2 := by
    rw [eq_div_iff (two_ne_zero)]; rw [mul_comm]; exact hmcsq
  field_simp
  ring_nf
  rw [hs2, hm2]
  ring

/-! ## The two branches agree on the Clifford torus -/

/-- **The two branches of the glueing map `S³ → LensSpace` agree on the common boundary torus.**
On `{|z₁| = |z₂|} = {|z₁| = |z₂| = 1/√2}` write `z₁ = e^{iα}/√2`, `z₂ = e^{iβ}/√2`.  Then
`capPt = ((‖z₂‖/z₂)², √2 z₁z₂/‖z₂‖) = (e^{-2iβ}, e^{i(α+β)})` and
`confPt = (√2 z₂z₁/‖z₁‖, (z₁/‖z₁‖)²) = (e^{i(α+β)}, e^{2iα})`, so the two points are related by
`Work.Drive.lensRel` (the cap boundary point `(θ, w)` is glued to `(w, θ w²)`). -/
theorem phiCap_eq_phiConf (v : unitSphere 3) (h : ‖c₁ v.1‖ = ‖c₂ v.1‖) :
    phiCap v = phiConf v := by
  have hle : ‖c₁ v.1‖ ≤ ‖c₂ v.1‖ := h.le
  have hge : ‖c₂ v.1‖ ≤ ‖c₁ v.1‖ := h.ge
  -- the Clifford torus: `2 m² = 1` for `m = ‖z₂‖`
  have h2 : 2 * ‖c₂ v.1‖ ^ 2 = 1 := by
    have := sq_norm_eq_one v
    rw [h] at this
    linarith
  have hz2 : c₂ v.1 ≠ 0 := ne_zero_of_norm_le hle (sq_norm_eq_one v)
  -- the disk coordinate `√2 z₁z₂/‖z₂‖` lies on the unit circle
  have hbz : ‖(Real.sqrt 2 : ℂ) * c₁ v.1 * c₂ v.1 / ((‖c₂ v.1‖ : ℝ) : ℂ)‖ = 1 :=
    norm_sqrt_two_mul_mul_div h2 h rfl
  -- the boundary parameters of the cap point
  set θ : UnitAddCircle := circOf ((((‖c₂ v.1‖ : ℝ) : ℂ) / c₂ v.1) ^ 2)
      (norm_sq_self_div _ hz2) with hθ
  set φ : UnitAddCircle :=
    circOf ((Real.sqrt 2 : ℂ) * c₁ v.1 * c₂ v.1 / ((‖c₂ v.1‖ : ℝ) : ℂ)) hbz with hφ
  -- the cap boundary point is `(θ, bdy φ)`
  have hx : (Sum.inl (capPt ⟨v, hle⟩) : CapTorus ⊕ ConfTorus) = Sum.inl (θ, bdy φ) := by
    rw [Sum.inl.injEq]
    refine Prod.ext ?_ ?_
    · rw [capPt_fst, ← hθ]
    · refine Subtype.ext ?_
      rw [capPt_snd, bdy_coe, hφ, circleOf_circOf]
  -- the configuration boundary point is `(bdy φ, θ + 2 • φ)`
  have hy : (Sum.inr (confPt ⟨v, hge⟩) : CapTorus ⊕ ConfTorus) =
      Sum.inr (bdy φ, θ + 2 • φ) := by
    rw [Sum.inr.injEq]
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      rw [confPt_fst, bdy_coe, hφ, circleOf_circOf, h]
      ring
    · rw [confPt_snd, hθ, hφ]
      apply circleOf_injective
      rw [circleOf_circOf, circleOf_add, circleOf_nsmul, circleOf_circOf, circleOf_circOf, h]
      exact div_sq_mul_div_sq h2 hz2
  rw [phiCap, phiConf, dif_pos hle, dif_pos hge]
  exact Quotient.sound (Or.inr ⟨θ, φ, Or.inl ⟨hx, hy⟩⟩)

end

end Work.Drive
