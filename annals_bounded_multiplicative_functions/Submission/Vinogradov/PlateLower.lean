/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.Descent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The scale-covariant torsion layer (`PlateLower`) — GLYZ §3.3, second route

## Why this module exists

GLYZ Lemma 3.6 (`Tower.curveDec_tower`) is applied in §3.4 to the *projected* moment curve
restricted to a coarse block, which has to be reparametrised to `[0,1]`
(`CurveLayer.intervalCurve`).  The Gram-determinant torsion hypothesis `CurveTorsion l D cT`
is **not scale-covariant** under that reparametrisation: for `D_I i σ = c^i • D i (a + cσ)` the
Gram determinant of `(D_I^{(i)}(σ))_{i=1}^{l}` equals `c^{l(l+1)}` times the original one, while
the *geometric* radius of the ball inside the plate scales only like `c^l`.  Since the constant
`tubeRho` of the tube lemma (`Descent.lean`) is linear in `cT`, the tower would then require a
plate enlargement `ε ≳ c^{-l²}`, which is not a fixed constant and therefore destroys the
induction.

The fix is to use the **anisotropic** (i.e. genuinely scale-covariant) form of the torsion
condition: the plate map at scale `1` is bounded below.  This is exactly what
`curvePlateLin_norm_lower_bound_at` produces from the Gram determinant (`Descent.tubeK`), but
the *constant* is now transported under reparametrisation with the correct scaling `c^l`
(`PlateLower.intervalCurve`), because the scaling is applied to a *fixed* list of vectors
rather than to a determinant.

## Contents

* `PlateLowerAt l D c t₀` — the anisotropic torsion condition at a point;
* `PlateLower l D c` — the same for all `t ∈ [0,1]`;
* `PlateLower_intervalCurve` — the transport with the loss `c^l` (this is the whole point);
* `curveAffLin_lower_of_plateLowerAt` — the straightening map expands norms by `c ρ^l (l!)⁻¹`;
* `exists_ball_subset_curveAff_plate_pl` and `tubeCB_ball_pl` — the ball inside the straightened
  plate, now with the scale-covariant constant;
* `tubeRhoP`, `tubeCGP` — the tube radius and its fixed geometric lower bound, free of the
  dimensional constant `A` of the old route;
* `ball_subset_taylorPlateLin_pl` and `curvePlate_subset_taylorPlate_pl` — the two tube lemmas.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The anisotropic torsion condition -/

/-- **The anisotropic torsion condition at a point.**  The map
`y ↦ ∑ i, y i • D (i+1) t₀` (the plate map of scale `1`) is bounded below by `c`. -/
def PlateLowerAt (l : ℕ) (D : ℕ → ℝ → E l) (c t₀ : ℝ) : Prop :=
  ∀ y : E l, c * ‖y‖ ≤ ‖∑ i : Fin l, y i • D (i.val + 1) t₀‖

/-- **The anisotropic torsion condition on `[0,1]`.** -/
def PlateLower (l : ℕ) (D : ℕ → ℝ → E l) (c : ℝ) : Prop :=
  ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → PlateLowerAt l D c t

/-- **The Taylor-remainder bound at the TOP truncation order `l`.**  This is the `m = l` case of
`CurveLayer.CurveTaylor` — and it is the *only* case used by the tube lemma.  Separating it out is
essential for the reparametrisation: the full `CurveTaylor` constant of `intervalCurve l a c D` is
`R * c` (the `m = 0` case dominates), while the constant of the `m = l` case is exactly
`R * c^(l+1)`; only the latter is scale-covariant enough for the tower. -/
def CurveTaylorTop (l : ℕ) (D : ℕ → ℝ → E l) (R : ℝ) : Prop :=
  ∀ (i : ℕ) (t u : ℝ), i ≤ l → t ∈ Set.Icc (0 : ℝ) 1 → |u| ≤ 1 →
    ‖D i (t + u) - ∑ j ∈ Finset.Icc i l, ((u ^ (j - i)) / ((j - i).factorial : ℝ)) • D j t‖
      ≤ R * |u| ^ (l + 1 - i)

lemma curveTaylorTop_of_curveTaylor {l : ℕ} {D : ℕ → ℝ → E l} {R : ℝ}
    (h : CurveTaylor l D R) : CurveTaylorTop l D R :=
  fun i t u hi ht hu => h i l t u hi le_rfl ht hu

/-- The plate map of scale `1` is the sum of the derivatives. -/
lemma curvePlateLin_one_apply (l : ℕ) (D : ℕ → ℝ → E l) (t : ℝ) (y : E l) :
    curvePlateLin l D 1 t y = ∑ i : Fin l, y i • D (i.val + 1) t := by
  rw [curvePlateLin_apply]
  exact Finset.sum_congr rfl fun i _ => by rw [one_pow, one_smul]

/-! ## 2. Two norm lemmas -/

/-- **The vector of `E l` with prescribed coordinates.** -/
noncomputable def coordVec (l : ℕ) (v : Fin l → ℝ) : E l :=
  (WithLp.equiv 2 (Fin l → ℝ)).symm v

lemma coordVec_apply (l : ℕ) (v : Fin l → ℝ) (i : Fin l) : coordVec l v i = v i := rfl

/-- Scaling each coordinate `y i` by `δ^(i+1)` loses at most the factor `δ^l` (`0 < δ ≤ 1`). -/
lemma norm_pow_mul_lower {l : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (y : E l) :
    δ ^ l * ‖y‖ ≤ ‖coordVec l (fun i : Fin l => δ ^ (i.val + 1) * y i)‖ := by
  have hcoe : ∀ i : Fin l, coordVec l (fun i : Fin l => δ ^ (i.val + 1) * y i) i
      = δ ^ (i.val + 1) * y i := fun i => rfl
  have hz : (0 : ℝ) ≤ δ ^ l * ‖y‖ := by positivity
  have hsq : (δ ^ l * ‖y‖) ^ 2
      ≤ ‖coordVec l (fun i : Fin l => δ ^ (i.val + 1) * y i)‖ ^ 2 := by
    rw [mul_pow, norm_sq_coord_sum l (coordVec l (fun i : Fin l => δ ^ (i.val + 1) * y i)),
      norm_sq_coord_sum l y, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hcoe i]
    have hi : i.val + 1 ≤ l := by have := i.isLt; omega
    have hle : δ ^ l ≤ δ ^ (i.val + 1) := pow_le_pow_of_le_one hδ0.le hδ1 hi
    have hyi : 0 ≤ |y i| := abs_nonneg _
    calc (δ ^ l) ^ 2 * (y i) ^ 2 = ((δ ^ l) * |y i|) ^ 2 := by rw [mul_pow, sq_abs]
      _ ≤ ((δ ^ (i.val + 1)) * |y i|) ^ 2 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          exact mul_le_mul_of_nonneg_right hle hyi
      _ = (δ ^ (i.val + 1) * y i) ^ 2 := by rw [mul_pow, sq_abs, mul_pow]
  nlinarith [hsq, hz,
    norm_nonneg (coordVec l (fun i : Fin l => δ ^ (i.val + 1) * y i))]

/-! ## 3. The plate bound at every scale -/

/-- **The plate map at scale `δ` is bounded below by `c δ^l`.** -/
lemma curvePlateLin_lower_of_plateLowerAt {l : ℕ} {D : ℕ → ℝ → E l} {c t : ℝ}
    (hc : 0 < c) (h : PlateLowerAt l D c t) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (y : E l) :
    c * δ ^ l * ‖y‖ ≤ ‖curvePlateLin l D δ t y‖ := by
  have h1 := h (coordVec l (fun i : Fin l => δ ^ (i.val + 1) * y i))
  have h2 := norm_pow_mul_lower hδ0 hδ1 y
  have hcoe : ∀ i : Fin l, coordVec l (fun i : Fin l => δ ^ (i.val + 1) * y i) i
      = δ ^ (i.val + 1) * y i := fun i => rfl
  have h3 : 0 ≤ c := hc.le
  have hsum : curvePlateLin l D δ t y
      = ∑ i : Fin l, (δ ^ (i.val + 1) * y i) • D (i.val + 1) t := by
    rw [curvePlateLin_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  rw [hsum]
  calc c * δ ^ l * ‖y‖ = c * (δ ^ l * ‖y‖) := by ring
    _ ≤ c * ‖coordVec l (fun i : Fin l => δ ^ (i.val + 1) * y i)‖ :=
        mul_le_mul_of_nonneg_left h2 h3
    _ ≤ ‖∑ i : Fin l, coordVec l (fun i : Fin l => δ ^ (i.val + 1) * y i) i
          • D (i.val + 1) t‖ := h1
    _ = ‖∑ i : Fin l, (δ ^ (i.val + 1) * y i) • D (i.val + 1) t‖ := by
        have hs : (∑ i : Fin l, coordVec l (fun i : Fin l => δ ^ (i.val + 1) * y i) i
              • D (i.val + 1) t)
            = ∑ i : Fin l, (δ ^ (i.val + 1) * y i) • D (i.val + 1) t :=
          Finset.sum_congr rfl fun i _ => by rw [hcoe i]
        rw [hs]

/-! ## 4. Transport under reparametrisation (the scale covariance) -/

/-- **The anisotropic torsion condition is scale-covariant**: the reparametrised curve
`σ ↦ D (a + cσ)` has plate map `y ↦ ∑ y_i c^{i+1} D^{(i+1)}(a+cσ)`, so the constant is scaled
by `c^l` — and *not* by the determinant factor `c^{l(l+1)}`. -/
lemma plateLower_intervalCurve {l : ℕ} {D : ℕ → ℝ → E l} {a c cL : ℝ}
    (hcL : 0 < cL) (hc0 : 0 < c) (hc1 : c ≤ 1)
    (h : ∀ σ ∈ Set.Icc (0 : ℝ) 1, PlateLowerAt l D cL (a + c * σ)) :
    PlateLower l (intervalCurve l a c D) (cL * c ^ l) := by
  intro σ hσ y
  have h1 := h σ hσ (coordVec l (fun i : Fin l => c ^ (i.val + 1) * y i))
  have h2 := norm_pow_mul_lower hc0 hc1 y
  have hcoe : ∀ i : Fin l, coordVec l (fun i : Fin l => c ^ (i.val + 1) * y i) i
      = c ^ (i.val + 1) * y i := fun i => rfl
  have hsum : (∑ i : Fin l, y i • intervalCurve l a c D (i.val + 1) σ)
      = ∑ i : Fin l, (c ^ (i.val + 1) * y i) • D (i.val + 1) (a + c * σ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalCurve_apply, smul_smul, mul_comm]
  rw [hsum]
  calc cL * c ^ l * ‖y‖ = cL * (c ^ l * ‖y‖) := by ring
    _ ≤ cL * ‖coordVec l (fun i : Fin l => c ^ (i.val + 1) * y i)‖ :=
        mul_le_mul_of_nonneg_left h2 hcL.le
    _ ≤ ‖∑ i : Fin l, coordVec l (fun i : Fin l => c ^ (i.val + 1) * y i) i
          • D (i.val + 1) (a + c * σ)‖ := h1
    _ = ‖∑ i : Fin l, (c ^ (i.val + 1) * y i) • D (i.val + 1) (a + c * σ)‖ := by
        have hs : (∑ i : Fin l, coordVec l (fun i : Fin l => c ^ (i.val + 1) * y i) i
              • D (i.val + 1) (a + c * σ))
            = ∑ i : Fin l, (c ^ (i.val + 1) * y i) • D (i.val + 1) (a + c * σ) :=
          Finset.sum_congr rfl fun i _ => by rw [hcoe i]
        rw [hs]

/-! ## 5. The straightening map expands norms (anisotropic version) -/

/-- **The straightening map expands norms**, with the anisotropic torsion constant.  The constant
is `c ρ^l (l!)⁻¹` — it contains neither the dimensional factor `tubeK` nor the Gram determinant,
which is what makes it transport correctly under reparametrisation. -/
lemma curveAffLin_lower_of_plateLowerAt {l : ℕ} {D : ℕ → ℝ → E l} {c t₀ : ℝ}
    (hc : 0 < c) (hlow : PlateLowerAt l D c t₀) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (y : E l) :
    c * ρ ^ l * ((l.factorial : ℝ))⁻¹ * ‖y‖ ≤ ‖curveAffLin l D ρ t₀ y‖ := by
  rw [curveAffLin_eq_curvePlateLin]
  have h1 := curvePlateLin_lower_of_plateLowerAt hc hlow hρ0 hρ1 (diagInv l y)
  have h2 := norm_diagInv_lower l y
  have h3 : 0 ≤ c * ρ ^ l := by positivity
  calc c * ρ ^ l * ((l.factorial : ℝ))⁻¹ * ‖y‖
      = (c * ρ ^ l) * (((l.factorial : ℝ))⁻¹ * ‖y‖) := by ring
    _ ≤ (c * ρ ^ l) * ‖diagInv l y‖ := mul_le_mul_of_nonneg_left h2 h3
    _ ≤ ‖curvePlateLin l D ρ t₀ (diagInv l y)‖ := h1

/-- **The moment-curve ball transported by the straightening map** (anisotropic version): the ball
inside the straightened plate has radius `cb · c ρ^l (l!)⁻¹ δ^l`, where `c` is the anisotropic
torsion constant. -/
theorem exists_ball_subset_curveAff_plate_pl (l : ℕ) (hl : 1 ≤ l) :
    ∃ cb : ℝ, 0 < cb ∧ ∀ (D : ℕ → ℝ → E l) (c ρ t₀ δ c' : ℝ), 0 < c → 0 < ρ → ρ ≤ 1 →
      0 < δ → δ ≤ 1 → |c'| ≤ 1 → PlateLowerAt l D c t₀ →
      Metric.ball (curveAff l D ρ t₀ (gammaVec l c'))
        (cb * (c * ρ ^ l * ((l.factorial : ℝ))⁻¹ * δ ^ l))
        ⊆ curveAff l D ρ t₀ '' plate l δ c' := by
  obtain ⟨cb, hcb, hball⟩ := exists_ball_subset_plate l hl
  refine ⟨cb, hcb, ?_⟩
  intro D c ρ t₀ δ c' hc hρ0 hρ1 hδ0 hδ1 hc' hlow
  set cΛ : ℝ := c * ρ ^ l * ((l.factorial : ℝ))⁻¹ with hcΛ
  have hΛpos : 0 < cΛ := by rw [hcΛ]; positivity
  have hexp : ∀ y : E l, cΛ * ‖y‖ ≤ ‖curveAffLin l D ρ t₀ y‖ := by
    intro y
    rw [hcΛ]
    exact curveAffLin_lower_of_plateLowerAt hc hlow hρ0 hρ1 y
  have hinj : Function.Injective (curveAffLin l D ρ t₀) := by
    intro x y hxy
    have h : curveAffLin l D ρ t₀ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h2 := hexp (x - y)
    rw [h, norm_zero] at h2
    have h3 : ‖x - y‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      by_contra hcont
      push_neg at hcont
      have h4 : 0 < cΛ * ‖x - y‖ := mul_pos hΛpos hcont
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp h3)
  have hsurj : Function.Surjective (curveAffLin l D ρ t₀) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (rfl : Module.finrank ℝ (E l) = Module.finrank ℝ (E l))).mp hinj
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  obtain ⟨u, hu⟩ := hsurj (z - curveAff l D ρ t₀ (gammaVec l c'))
  have hnorm : cΛ * ‖u‖ < cb * (cΛ * δ ^ l) := by
    have h3 := hexp u
    rw [hu] at h3
    refine lt_of_le_of_lt h3 ?_
    rw [hcΛ]
    exact hz
  have hupper : ‖u‖ < cb * δ ^ l := by
    have h6 : cΛ * ‖u‖ < cΛ * (cb * δ ^ l) := by
      have h7 : cb * (cΛ * δ ^ l) = cΛ * (cb * δ ^ l) := by ring
      linarith [hnorm, h7]
    exact lt_of_mul_lt_mul_left h6 hΛpos.le
  refine ⟨gammaVec l c' + u, ?_, ?_⟩
  · apply hball δ c' hδ0 hδ1 hc'
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hupper
  · rw [curveAff, map_add, hu, curveAff]
    abel

/-! ## 6. The tube radius with the anisotropic constant -/

/-- The constant of `exists_ball_subset_curveAff_plate_pl`, fixed by choice. -/
noncomputable def tubeCBP (l : ℕ) : ℝ :=
  if h : 1 ≤ l then Classical.choose (exists_ball_subset_curveAff_plate_pl l h) else 1

lemma tubeCBP_pos {l : ℕ} (hl : 1 ≤ l) : 0 < tubeCBP l := by
  rw [tubeCBP, dif_pos hl]
  exact (Classical.choose_spec (exists_ball_subset_curveAff_plate_pl l hl)).1

/-- The ball inside the straightened plate, with the anisotropic torsion constant. -/
lemma tubeCBP_ball {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l) {c t₀ δ c' : ℝ}
    (hc : 0 < c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hc' : |c'| ≤ 1)
    (hlow : PlateLowerAt l D c t₀) :
    Metric.ball (curveAff l D 1 t₀ (gammaVec l c'))
      (tubeCBP l * (c * 1 ^ l * ((l.factorial : ℝ))⁻¹ * δ ^ l))
      ⊆ curveAff l D 1 t₀ '' plate l δ c' := by
  rw [tubeCBP, dif_pos hl]
  exact (Classical.choose_spec (exists_ball_subset_curveAff_plate_pl l hl)).2 D c 1 t₀ δ c'
    hc one_pos le_rfl hδ0 hδ1 hc' hlow

/-- The ball radius of the straightened plate at the model scale `σ`. -/
noncomputable def tubeRhoP (l : ℕ) (c σ : ℝ) : ℝ :=
  tubeCBP l * (c * ((l.factorial : ℝ))⁻¹) * (min (Ctube l * σ) 1) ^ l

/-- The fixed geometric constant of the quantitative lower bound for `tubeRhoP`. -/
noncomputable def tubeCGP (l : ℕ) (c : ℝ) : ℝ := tubeCBP l * (c * ((l.factorial : ℝ))⁻¹)

lemma tubeRhoP_eq (l : ℕ) (c σ : ℝ) :
    tubeCGP l c * (min (Ctube l * σ) 1) ^ l = tubeRhoP l c σ := by
  rw [tubeRhoP, tubeCGP]

lemma tubeRhoP_ge (l : ℕ) (c σ : ℝ) :
    tubeCGP l c * (min (Ctube l * σ) 1) ^ l ≤ tubeRhoP l c σ :=
  le_of_eq (tubeRhoP_eq l c σ)

lemma tubeCGP_pos {l : ℕ} (hl : 1 ≤ l) {c : ℝ} (hc : 0 < c) : 0 < tubeCGP l c := by
  rw [tubeCGP]
  exact mul_pos (tubeCBP_pos hl) (mul_pos hc (inv_pos.mpr (by positivity)))

lemma curveAffLin_injective_of_plateLowerAt {l : ℕ} {D : ℕ → ℝ → E l} {c t₀ : ℝ}
    (hc : 0 < c) (hlow : PlateLowerAt l D c t₀) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Function.Injective (curveAffLin l D ρ t₀) := by
  intro x y hxy
  have h := curveAffLin_lower_of_plateLowerAt hc hlow hρ0 hρ1 (x - y)
  rw [map_sub, hxy, sub_self, norm_zero] at h
  have hpos : 0 < c * ρ ^ l * ((l.factorial : ℝ))⁻¹ :=
    mul_pos (mul_pos hc (pow_pos hρ0 l)) (inv_pos.mpr (by positivity))
  have h3 : ‖x - y‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    by_contra hcont
    push_neg at hcont
    have h4 : 0 < c * ρ ^ l * ((l.factorial : ℝ))⁻¹ * ‖x - y‖ := mul_pos hpos hcont
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)

lemma tubeRhoP_pos {l : ℕ} (hl : 1 ≤ l) {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
    0 < tubeRhoP l c σ := by
  rw [tubeRhoP]
  have h6 : (0 : ℝ) < min (Ctube l * σ) 1 := lt_min (mul_pos (Ctube_pos l) hσ) one_pos
  exact mul_pos (mul_pos (tubeCBP_pos hl) (mul_pos hc (inv_pos.mpr (by positivity))))
    (pow_pos h6 l)

lemma tubeRhoP_mono {l : ℕ} (hl : 1 ≤ l) {c : ℝ} (hc : 0 ≤ c) {σ₁ σ₂ : ℝ}
    (h0 : 0 ≤ σ₁) (h : σ₁ ≤ σ₂) : tubeRhoP l c σ₁ ≤ tubeRhoP l c σ₂ := by
  rw [tubeRhoP, tubeRhoP]
  have h1 : (0 : ℝ) ≤ tubeCBP l * (c * ((l.factorial : ℝ))⁻¹) := by
    have h2 : (0 : ℝ) ≤ c * ((l.factorial : ℝ))⁻¹ := by positivity
    exact mul_nonneg (tubeCBP_pos hl).le h2
  have h3 : min (Ctube l * σ₁) 1 ≤ min (Ctube l * σ₂) 1 :=
    min_le_min (mul_le_mul_of_nonneg_left h (Ctube_pos l).le) le_rfl
  have h4 : (0 : ℝ) ≤ min (Ctube l * σ₁) 1 :=
    le_min (mul_nonneg (Ctube_pos l).le h0) zero_le_one
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h4 h3 l) h1

/-! ## 7. The ball inside the plate of the Taylor polynomial -/

/-- **The ball inside the plate of the Taylor polynomial** (anisotropic version). -/
lemma ball_subset_taylorPlateLin_pl {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l) {c σ : ℝ}
    (hc : 0 < c) (hσ : 0 < σ) {t₀ u : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1) (hu : |u| ≤ 1)
    (hlow : PlateLowerAt l D c t₀) :
    Metric.ball 0 (tubeRhoP l c σ)
      ⊆ curvePlateLin l (taylorDeriv l D t₀) (min (Ctube l * σ) 1) (t₀ + u) '' unitBox l := by
  have ht₀' : t₀ ∈ Set.Icc (0 : ℝ) 1 := ht₀
  set σ₁ : ℝ := min (Ctube l * σ) 1 with hσ₁def
  have hσ₁0 : 0 < σ₁ := lt_min (mul_pos (Ctube_pos l) hσ) one_pos
  have hσ₁1 : σ₁ ≤ 1 := min_le_right _ _
  have hball := tubeCBP_ball (D := D) hl hc hσ₁0 hσ₁1 hu hlow
  have hcen : curveAff l D 1 t₀ (gammaVec l u) = taylorDeriv l D t₀ 0 (t₀ + u) := by
    rw [curveAff, curveAff_gammaVec, one_mul]
  have hrad : tubeCBP l * (c * 1 ^ l * ((l.factorial : ℝ))⁻¹ * σ₁ ^ l) = tubeRhoP l c σ := by
    rw [tubeRhoP, hσ₁def]; ring
  rw [hcen, hrad, curveAff_image_plate, one_mul] at hball
  intro z hz
  have hz' : taylorDeriv l D t₀ 0 (t₀ + u) + z
      ∈ Metric.ball (taylorDeriv l D t₀ 0 (t₀ + u)) (tubeRhoP l c σ) := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    rwa [Metric.mem_ball, dist_zero_right] at hz
  obtain ⟨y, hy, hyz⟩ := hball hz'
  refine ⟨y, hy, ?_⟩
  simp only [one_mul] at hyz
  exact add_left_cancel hyz

/-! ## 8. The tube lemma (anisotropic version) -/

theorem curvePlate_subset_taylorPlate_pl {l : ℕ} (hl : 1 ≤ l) (D : ℕ → ℝ → E l)
    {ct R : ℝ} (hct : 0 < ct) (hlow : PlateLower l D ct) (htay : CurveTaylorTop l D R)
    (hR : 0 ≤ R)
    {c_I c c_i δ σ ε : ℝ} (hcI : c_I ∈ Set.Icc (0 : ℝ) 1) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (hci : c_i ∈ Set.Icc (0 : ℝ) 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hσ : 0 < σ) (hε : 0 < ε)
    (hclose : max δ |c_i - c| ≤ σ) (hκ1 : |c_i - c_I| ≤ 1)
    (hnum : 2 * (R * ((l : ℝ) + 1) * (max δ |c_i - c_I|) ^ (l + 1)) < ε * tubeRhoP l ct σ) :
    curvePlate l D δ c_i ⊆ curvePlate l (taylorDeriv l D c_I) ((1 + ε) * (Ctube l * σ)) c := by
  have hdist1 : ∀ {a b : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 → |a - b| ≤ 1 := by
    intro a b ha hb
    rw [abs_sub_le_iff]
    exact ⟨by linarith [ha.2, hb.1], by linarith [ha.1, hb.2]⟩
  have huab : |c - c_I| ≤ 1 := hdist1 hc hcI
  have hvab : |c_i - c_I| ≤ 1 := hκ1
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy1 : ∀ i : Fin l, |y i| ≤ 1 := hy
  set u : ℝ := c - c_I with hu
  set v : ℝ := c_i - c_I with hv
  have hcu : c_I + u = c := by rw [hu]; ring
  have hcv : c_I + v = c_i := by rw [hv]; ring
  obtain ⟨w, hw, hweq⟩ := moment_tube l hl hy1 (δ := δ) (σ := σ) (u := u) (v := v) hδ0.le hσ
    (by rw [show v - u = c_i - c by rw [hv, hu]; ring]; exact hclose)
  set Λ : E l →ₗ[ℝ] E l := curveAffLin l D 1 c_I with hΛ
  have hlam0 : ∀ t : ℝ, Λ (gammaVec l t) = taylorDeriv l D c_I 0 (c_I + t) - D 0 c_I := by
    intro t
    have h := curveAff_gammaVec l D 1 c_I t
    rw [← hΛ, one_mul] at h
    exact eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact h)
  have hlamd : ∀ (i : ℕ) (t : ℝ), Λ (gammaDeriv l (i + 1) t)
      = taylorDeriv l D c_I (i + 1) (c_I + t) := by
    intro i t
    have h := curveAffLin_gammaDeriv l D 1 c_I t (i + 1) (by omega)
    rw [← hΛ, one_mul, one_pow, one_smul] at h
    exact h
  have hZ : Λ (tubeVec l y δ v) = (taylorDeriv l D c_I 0 (c_I + v) - D 0 c_I)
      + ∑ i : Fin l, y i • (δ ^ (i.val + 1) • taylorDeriv l D c_I (i.val + 1) (c_I + v)) := by
    rw [tubeVec_apply, map_add, map_sum]
    congr 1
    · exact hlam0 v
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, hlamd]
  have htransfer : Λ (curvePlateLin l (gammaDeriv l) (Ctube l * σ) u w)
      = curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c w := by
    rw [curvePlateLin_apply, map_sum, curvePlateLin_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, hlamd, hcu]
  set B : E l := ∑ i : Fin l,
    y i • (δ ^ (i.val + 1) • taylorDeriv l D c_I (i.val + 1) (c_I + v)) with hB
  set C : E l := curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c w with hC
  have hZ' : Λ (tubeVec l y δ v) = (taylorDeriv l D c_I 0 (c_I + v) - D 0 c_I) + B := by
    rw [hZ, hB]
  have h1 : Λ (tubeVec l y δ v) - Λ (gammaVec l u) = C := by
    rw [← map_sub]
    have hprev : tubeVec l y δ v - gammaVec l u
        = gammaVec l v - gammaVec l u
          + ∑ i : Fin l, y i • (δ ^ (i.val + 1) • gammaDeriv l (i.val + 1) v) := by
      rw [tubeVec_apply]; abel
    rw [hprev, hweq, htransfer, hC]
  have hkey : taylorDeriv l D c_I 0 c_i + B = taylorDeriv l D c_I 0 c + C := by
    rw [← hcv, ← hcu]
    have h3 : C = (taylorDeriv l D c_I 0 (c_I + v) - D 0 c_I) + B
        - (taylorDeriv l D c_I 0 (c_I + u) - D 0 c_I) := by
      rw [← h1, hZ', hlam0 u]
    rw [h3]
    abel
  set err : E l := (D 0 c_i - taylorDeriv l D c_I 0 c_i)
      + ∑ i : Fin l,
          y i • (δ ^ (i.val + 1) • (D (i.val + 1) c_i - taylorDeriv l D c_I (i.val + 1) c_i))
    with herrdef
  have hxsplit : D 0 c_i + curvePlateLin l D δ c_i y = taylorDeriv l D c_I 0 c + C + err := by
    have hmain : D 0 c_i + curvePlateLin l D δ c_i y
        = (taylorDeriv l D c_I 0 c_i + B) + err := by
      have hA : curvePlateLin l D δ c_i y
          = ∑ i : Fin l, y i • (δ ^ (i.val + 1) • D (i.val + 1) c_i) :=
        curvePlateLin_apply l D δ c_i y
      have hB' : B = ∑ i : Fin l,
          y i • (δ ^ (i.val + 1) • taylorDeriv l D c_I (i.val + 1) c_i) := by
        rw [hB]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcv]
      have herr' : err = (D 0 c_i + ∑ i : Fin l, y i • (δ ^ (i.val + 1) • D (i.val + 1) c_i))
          - (taylorDeriv l D c_I 0 c_i + ∑ i : Fin l,
              y i • (δ ^ (i.val + 1) • taylorDeriv l D c_I (i.val + 1) c_i)) := by
        rw [herrdef]
        simp only [smul_sub, Finset.sum_sub_distrib]
        abel
      rw [hA, hB', herr']
      abel
    rw [hmain]
    exact congrArg (· + err) hkey
  have hM0 : (0 : ℝ) ≤ max δ |c_i - c_I| := le_trans (abs_nonneg _) (le_max_right _ _)
  have hM1 : max δ |c_i - c_I| ≤ 1 := max_le hδ1 hκ1
  have hsum_eq : ∀ i : ℕ, (∑ j ∈ Finset.Icc i l,
        (v ^ (j - i) / ((j - i).factorial : ℝ)) • D j c_I) = taylorDeriv l D c_I i c_i := by
    intro i
    rw [taylorDeriv_apply]
  have h1err : ‖D 0 c_i - taylorDeriv l D c_I 0 c_i‖ ≤ R * (max δ |c_i - c_I|) ^ (l + 1) := by
    have h := htay 0 c_I v (by omega) hcI hvab
    rw [show c_I + v = c_i from hcv, hsum_eq 0] at h
    rw [show |v| = |c_i - c_I| by rw [hv]] at h
    exact le_trans h (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _) hR)
  have h2err : ∀ i : Fin l,
      ‖y i • (δ ^ (i.val + 1) • (D (i.val + 1) c_i - taylorDeriv l D c_I (i.val + 1) c_i))‖
        ≤ R * (max δ |c_i - c_I|) ^ (l + 1) := by
    intro i
    have h := htay (i.val + 1) c_I v (by omega) hcI hvab
    rw [show c_I + v = c_i from hcv, hsum_eq (i.val + 1)] at h
    rw [show |v| = |c_i - c_I| by rw [hv]] at h
    have hexp : l + 1 - (i.val + 1) = l - i.val := by omega
    rw [hexp] at h
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hδ0.le _)]
    have h5 : |y i| ≤ 1 := hy1 i
    have h7 : |c_i - c_I| ^ (l - i.val) ≤ (max δ |c_i - c_I|) ^ (l - i.val) :=
      pow_le_pow_left₀ (abs_nonneg _) (le_max_right _ _) _
    calc |y i| * (δ ^ (i.val + 1) * ‖D (i.val + 1) c_i - taylorDeriv l D c_I (i.val + 1) c_i‖)
        ≤ 1 * (δ ^ (i.val + 1) * (R * |c_i - c_I| ^ (l - i.val))) :=
          mul_le_mul h5 (mul_le_mul_of_nonneg_left h (by positivity)) (by positivity) zero_le_one
      _ = R * (δ ^ (i.val + 1) * |c_i - c_I| ^ (l - i.val)) := by ring
      _ ≤ R * (max δ |c_i - c_I|) ^ (l + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hR
          calc δ ^ (i.val + 1) * |c_i - c_I| ^ (l - i.val)
              ≤ (max δ |c_i - c_I|) ^ (i.val + 1)
                  * (max δ |c_i - c_I|) ^ (l - i.val) :=
                mul_le_mul (pow_le_pow_left₀ hδ0.le (le_max_left _ _) (i.val + 1)) h7
                  (pow_nonneg (abs_nonneg _) _) (pow_nonneg hM0 _)
            _ = (max δ |c_i - c_I|) ^ (i.val + 1 + (l - i.val)) := (pow_add _ _ _).symm
            _ = (max δ |c_i - c_I|) ^ (l + 1) := by
                congr 1; omega
  have herrbound : ‖err‖ < ε * tubeRhoP l ct σ := by
    have h3 : ‖err‖ ≤ R * (max δ |c_i - c_I|) ^ (l + 1)
        + ∑ _i : Fin l, R * (max δ |c_i - c_I|) ^ (l + 1) := by
      rw [herrdef]
      refine le_trans (norm_add_le _ _) (add_le_add h1err ?_)
      exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => h2err i)
    have h4 : (∑ _i : Fin l, R * (max δ |c_i - c_I|) ^ (l + 1))
        = (l : ℝ) * (R * (max δ |c_i - c_I|) ^ (l + 1)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [h4] at h3
    have h5 : R * (max δ |c_i - c_I|) ^ (l + 1)
        + (l : ℝ) * (R * (max δ |c_i - c_I|) ^ (l + 1))
        = ((l : ℝ) + 1) * (R * (max δ |c_i - c_I|) ^ (l + 1)) := by ring
    rw [h5] at h3
    have hρ0 : 0 < tubeRhoP l ct σ := tubeRhoP_pos hl hct hσ
    nlinarith [h3, hnum, hε, hρ0]
  have hconv : Convex ℝ (curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c '' unitBox l) :=
    (convex_unitBox l).linear_image _
  have h0u : (0 : E l) ∈ unitBox l := by
    show ∀ i : Fin l, |(0 : E l) i| ≤ 1
    intro i
    simp
  have h0P : (0 : E l) ∈ curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c '' unitBox l :=
    ⟨0, h0u, by rw [curvePlateLin_apply]; simp⟩
  have hballP : Metric.ball 0 (tubeRhoP l ct σ)
      ⊆ curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c '' unitBox l := by
    have hball := ball_subset_taylorPlateLin_pl (D := D) hl hct hσ hcI huab (hlow c_I hcI)
    rw [hcu] at hball
    intro z hz
    have hmono : curvePlateLin l (taylorDeriv l D c_I) (min (Ctube l * σ) 1) c '' unitBox l
        ⊆ curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c '' unitBox l := by
      rintro _ ⟨y', hy', rfl⟩
      have hle : min (Ctube l * σ) 1 ≤ Ctube l * σ := min_le_left _ _
      have hmem : taylorDeriv l D c_I 0 c
            + curvePlateLin l (taylorDeriv l D c_I) (min (Ctube l * σ) 1) c y'
          ∈ curvePlate l (taylorDeriv l D c_I) (Ctube l * σ) c :=
        curvePlate_mono (D := taylorDeriv l D c_I) (δ := min (Ctube l * σ) 1)
          (δ' := Ctube l * σ) (t := c)
          (le_of_lt (lt_min (mul_pos (Ctube_pos l) hσ) one_pos)) hle ⟨y', hy', rfl⟩
      obtain ⟨y'', hy'', hy''eq⟩ := hmem
      refine ⟨y'', hy'', ?_⟩
      exact add_left_cancel hy''eq
    exact hmono (hball hz)
  have hPw : curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c w
      ∈ curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c '' unitBox l :=
    ⟨w, fun i => hw i, rfl⟩
  obtain ⟨q, hq, hqeq⟩ :=
    absorb_ball_smul hconv h0P (tubeRhoP_pos hl hct hσ) hballP hε hPw herrbound
  have hscaled : (1 + ε) • q
      ∈ curvePlateLin l (taylorDeriv l D c_I) ((1 + ε) * (Ctube l * σ)) c '' unitBox l := by
    obtain ⟨y', hy', rfl⟩ := hq
    refine smul_curvePlateLin_subset (taylorDeriv l D c_I) (le_add_of_nonneg_right hε.le)
      ⟨curvePlateLin l (taylorDeriv l D c_I) (Ctube l * σ) c y', ⟨y', hy', rfl⟩, rfl⟩
  rw [curvePlate]
  obtain ⟨y'', hy'', hy''eq⟩ := hscaled
  refine ⟨y'', hy'', ?_⟩
  change taylorDeriv l D c_I 0 c
      + curvePlateLin l (taylorDeriv l D c_I) ((1 + ε) * (Ctube l * σ)) c y''
    = D 0 c_i + curvePlateLin l D δ c_i y
  have hy''eq' : curvePlateLin l (taylorDeriv l D c_I) ((1 + ε) * (Ctube l * σ)) c y''
      = (1 + ε) • q := hy''eq
  rw [hy''eq', ← hqeq, ← hC, ← add_assoc, ← hxsplit]


end Submission.Vinogradov
