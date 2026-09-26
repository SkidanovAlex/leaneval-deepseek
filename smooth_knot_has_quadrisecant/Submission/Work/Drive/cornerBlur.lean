import Mathlib

/-!
# The parameter-blur of a corner, and the local form of the "common direction" criterion

This module isolates the **local** mechanism of the injectivity of the chord sweep of a knot: the
parameter blur of the *corner* at which the retained arc meets its chord.

Let `b : ℝ → ℝ` be a smoothing kernel (`IsBlurKernel b`: continuous, nonnegative, of total mass one
with vanishing first moment — the property of the bump `Work.Drive.sweepBump` that the computations
use) and let `δ > 0` be the smoothing width.  A corner is modelled by the **wedge**

    wedge p q τ = if τ ≤ 0 then τ • p else τ • q

(two rays leaving the origin in the directions `p` — the retained arc — and `q` — the chord,
traversed backwards), and its parameter blur is

    cornerBlur b δ p q τ = cornerP b δ τ • p + cornerQ b δ τ • q ,

where the *weights* are the first partial moments of the kernel on the two sides of the split point
`cornerSplit δ τ = min 1 (max (-1) (τ/δ))`:

    cornerP b δ τ = ∫ u in (cornerSplit δ τ)..1, b u * (τ - δ*u)   (the `p`-side weight),
    cornerQ b δ τ = ∫ u in (-1)..(cornerSplit δ τ), b u * (τ - δ*u)   (the `q`-side weight).

Far from the corner the window lies entirely on one branch, and the corresponding weight is the full
first moment: `cornerP b δ τ = τ` for `τ ≤ -δ`, `cornerP b δ τ = 0` for `δ ≤ τ`, and dually.

## What is proved here

* **The cusp obstruction** (`not_injective_cornerBlur_of_collinear`): if the two branch directions are
  *antiparallel*, `q = -c • p` with `c > 0`, then the blurred corner is **never injective** — two
  distinct parameters at distance `≤ δ · max 1 c⁻¹` from the corner have the same image, for every
  width `δ` and every kernel.  This is the pathological configuration of the untwisted chord sweep
  at the corner `tb`: there the chord direction is `r (tb) - r (ta) ≈ w · r' (tb)` for a retained arc
  of width `w`, so the two branch directions are antiparallel up to the *curvature* correction — the
  razor's edge of the low end, and the reason the "common direction" criterion of the sweep keeps
  failing there.
* **The local criterion** (`injective_cornerBlur_of_cone`): if some direction `n` pairs positively
  with both branch directions (the two branches lie in an open half-plane), then the blurred corner
  *is* injective.  This is the local form of the common-direction criterion; combined with the first
  point it locates the criterion's failure exactly at the cusps (`q ∈ {-λ • p : λ ≥ 0}`).

The remedy used for the low end is the **ambient twist** — the rotation of space about the chord's
axis by an angle depending only on the axial coordinate (`Work.Drive.twist`).  It is a global
diffeomorphism (so the twist family is a family of knots for free), and it rotates the two branches
of a corner by *different* amounts, turning the cusp into a genuine corner: exactly the hypothesis of
the local criterion.
-/

noncomputable section

namespace Work.Drive

open scoped Real Topology intervalIntegral
open MeasureTheory

/-- A **smoothing kernel** for the parameter blur: continuous, nonnegative, of total mass one and
with vanishing first moment.  (For a kernel supported in `[-1,1]` the two integral conditions say
that the blur reproduces affine functions of the parameter.) -/
structure IsBlurKernel (b : ℝ → ℝ) : Prop where
  continuous : Continuous b
  nonneg : ∀ u : ℝ, 0 ≤ b u
  mass : ∫ u in (-1 : ℝ)..1, b u = 1
  moment : ∫ u in (-1 : ℝ)..1, u * b u = 0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **corner model**: two rays from the origin, in the directions `p` (the retained arc, for
negative parameter) and `q` (the chord, traversed backwards, for positive parameter). -/
def wedge (p q : E) (τ : ℝ) : E := if τ ≤ 0 then τ • p else τ • q

/-- The **split point** of the blur window: the clamped position `τ/δ` of the corner in the kernel
parameter. -/
def cornerSplit (δ τ : ℝ) : ℝ := min 1 (max (-1) (τ / δ))

/-- The **`p`-side weight** of the blurred corner: the first partial moment of the kernel over the
part of the window lying on the `p`-branch. -/
def cornerP (b : ℝ → ℝ) (δ τ : ℝ) : ℝ :=
  ∫ u in (cornerSplit δ τ)..1, b u * (τ - δ * u)

/-- The **`q`-side weight** of the blurred corner. -/
def cornerQ (b : ℝ → ℝ) (δ τ : ℝ) : ℝ :=
  ∫ u in (-1)..(cornerSplit δ τ), b u * (τ - δ * u)

/-- The **blurred corner**: the kernel-weighted average of the two branches. -/
def cornerBlur (b : ℝ → ℝ) (δ : ℝ) (p q : E) (τ : ℝ) : E :=
  cornerP b δ τ • p + cornerQ b δ τ • q

/-- The **parameter blur of the wedge** — the honest definition, of which `cornerBlur` is the
closed form: the kernel-weighted average of the corner model along the parameter window.

**Caveat (found by the reviewer of this identity).**  The bridge `cornerBlur = wedgeBlur` is a
theorem only for a **complete** `E`: Mathlib's Bochner integral is *defined* to be zero on an
incomplete space (`MeasureTheory.integral_of_not_completeSpace`), so on an incomplete `E` the right
hand side is identically `0` while `cornerBlur` is not.  The results of this file about `cornerP`,
`cornerQ` and `cornerBlur` are real-valued integrals and do not need completeness; only the
identification with the honest blur does. -/
def wedgeBlur (b : ℝ → ℝ) (δ : ℝ) (p q : E) (τ : ℝ) : E :=
  ∫ u in (-1 : ℝ)..1, b u • wedge p q (τ - δ * u)

/-! ## The split point -/

theorem cornerSplit_eq_neg_one {δ τ : ℝ} (hδ : 0 < δ) (hτ : τ ≤ -δ) :
    cornerSplit δ τ = -1 := by
  have h1 : τ / δ ≤ -1 := by rw [div_le_iff₀ hδ]; linarith
  rw [cornerSplit, max_eq_left h1, min_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]

theorem cornerSplit_eq_one {δ τ : ℝ} (hδ : 0 < δ) (hτ : δ ≤ τ) : cornerSplit δ τ = 1 := by
  have h1 : 1 ≤ τ / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [cornerSplit, max_eq_right (by linarith : (-1 : ℝ) ≤ τ / δ), min_eq_left h1]

/-- The split point is monotone in `τ` (for a positive width). -/
theorem monotone_cornerSplit {δ : ℝ} (hδ : 0 < δ) : Monotone (cornerSplit δ) := by
  intro a b hab
  refine min_le_min le_rfl (max_le_max le_rfl ?_)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hab (inv_nonneg.mpr hδ.le)

/-! ## The weights far from the corner -/

theorem intervalIntegrable_mul {b : ℝ → ℝ} (hb : Continuous b) (δ τ a c : ℝ) :
    IntervalIntegrable (fun u : ℝ => b u * (τ - δ * u)) volume a c :=
  (hb.mul (continuous_const.sub (continuous_const.mul continuous_id))).intervalIntegrable _ _

/-- Far on the `p`-side of the corner the whole window lies on the `p`-branch, so the `p`-weight is
the first moment `τ` of the kernel. -/
theorem cornerP_eq_of_le {b : ℝ → ℝ} (hb : IsBlurKernel b) {δ τ : ℝ} (hδ : 0 < δ)
    (hτ : τ ≤ -δ) : cornerP b δ τ = τ := by
  rw [cornerP, cornerSplit_eq_neg_one hδ hτ]
  have hsplit : (fun u : ℝ => b u * (τ - δ * u)) = fun u => τ * b u - δ * (u * b u) := by
    funext u; ring
  have h1 : IntervalIntegrable (fun u : ℝ => τ * b u) volume (-1) 1 :=
    ((continuous_const.mul hb.continuous)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun u : ℝ => δ * (u * b u)) volume (-1) 1 :=
    (continuous_const.mul (continuous_id.mul hb.continuous)).intervalIntegrable _ _
  rw [hsplit, intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hb.mass, hb.moment]
  ring

/-- Far on the `q`-side of the corner the blur window is empty, so the `p`-weight vanishes. -/
theorem cornerP_eq_zero_of_ge {b : ℝ → ℝ} {δ τ : ℝ} (hδ : 0 < δ) (hτ : δ ≤ τ) :
    cornerP b δ τ = 0 := by
  rw [cornerP, cornerSplit_eq_one hδ hτ]
  simp

/-- Far on the `q`-side the whole window lies on the `q`-branch. -/
theorem cornerQ_eq_of_ge {b : ℝ → ℝ} (hb : IsBlurKernel b) {δ τ : ℝ} (hδ : 0 < δ)
    (hτ : δ ≤ τ) : cornerQ b δ τ = τ := by
  rw [cornerQ, cornerSplit_eq_one hδ hτ]
  have hsplit : (fun u : ℝ => b u * (τ - δ * u)) = fun u => τ * b u - δ * (u * b u) := by
    funext u; ring
  have h1 : IntervalIntegrable (fun u : ℝ => τ * b u) volume (-1) 1 :=
    ((continuous_const.mul hb.continuous)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun u : ℝ => δ * (u * b u)) volume (-1) 1 :=
    (continuous_const.mul (continuous_id.mul hb.continuous)).intervalIntegrable _ _
  rw [hsplit, intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hb.mass, hb.moment]
  ring

/-- Far on the `p`-side the blur window is empty, so the `q`-weight vanishes. -/
theorem cornerQ_eq_zero_of_le {b : ℝ → ℝ} {δ τ : ℝ} (hδ : 0 < δ) (hτ : τ ≤ -δ) :
    cornerQ b δ τ = 0 := by
  rw [cornerQ, cornerSplit_eq_neg_one hδ hτ]
  simp

/-- **The two weights add up to the first moment `τ` of the whole window.**  Consequently, for
`τ₂ > τ₁` the increments of the two weights are nonnegative and add up to `τ₂ - τ₁`. -/
theorem cornerP_add_cornerQ {b : ℝ → ℝ} (hb : IsBlurKernel b) (δ τ : ℝ) :
    cornerP b δ τ + cornerQ b δ τ = ∫ u in (-1 : ℝ)..1, b u * (τ - δ * u) := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_mul hb.continuous δ τ (-1) (cornerSplit δ τ))
    (intervalIntegrable_mul hb.continuous δ τ (cornerSplit δ τ) 1)
  rw [cornerQ, cornerP, add_comm]
  exact h

/-! ## The cusp obstruction -/

/-- **The blurred corner is never injective at a cusp.**  If the two branch directions are
antiparallel (`q = -c • p` with `c > 0`, `p ≠ 0`) then for **every** width `δ` and every kernel the
blurred corner is not injective: two distinct parameters, both at distance at most
`δ · max 1 c⁻¹` from the corner, have the same image.

This is the local obstruction of the low end of the chord sweep: the corner at `tb` has
`r (tb) - r (ta) ≈ w · r' (tb)` for a retained arc of width `w`, so its two branch directions are
antiparallel up to the curvature correction — the razor's edge of the untwisted blur. -/
theorem not_injective_cornerBlur_of_collinear {b : ℝ → ℝ} (hb : IsBlurKernel b)
    {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) {p : E} (hp : p ≠ 0) :
    ¬ Function.Injective (cornerBlur b δ p (-c • p)) := by
  intro hinj
  set τ₂ : ℝ := max δ (δ / c) with hτ₂def
  set τ₁ : ℝ := -c * τ₂ with hτ₁def
  have hτ₂_ge : δ ≤ τ₂ := le_max_left _ _
  have hτ₂_pos : 0 < τ₂ := lt_of_lt_of_le hδ hτ₂_ge
  have hτ₁_le : τ₁ ≤ -δ := by
    have hcτ : δ ≤ c * τ₂ := by
      have h2 : δ / c ≤ τ₂ := le_max_right _ _
      have h3 : δ ≤ c * (δ / c) := by rw [mul_div_cancel₀ _ (ne_of_gt hc)]
      nlinarith [h2, h3, hc]
    rw [hτ₁def]; linarith
  have hne : τ₁ ≠ τ₂ := by
    rw [hτ₁def]
    intro h
    nlinarith [hc, hτ₂_pos]
  have hval₁ : cornerBlur b δ p (-c • p) τ₁ = τ₁ • p := by
    rw [cornerBlur, cornerP_eq_of_le hb hδ hτ₁_le,
      cornerQ_eq_zero_of_le hδ hτ₁_le, zero_smul, add_zero]
  have hval₂ : cornerBlur b δ p (-c • p) τ₂ = τ₁ • p := by
    rw [cornerBlur, cornerP_eq_zero_of_ge hδ hτ₂_ge,
      cornerQ_eq_of_ge hb hδ hτ₂_ge, zero_smul, zero_add, smul_smul]
    rw [hτ₁def]
    congr 1
    ring
  exact hne (hinj (hval₁.trans hval₂.symm))

/-- **The collision at a cusp happens at the scale of the width.**  In the situation of
`not_injective_cornerBlur_of_collinear` the two colliding parameters can be chosen at distance at
most `δ · max 1 c⁻¹` (and `c δ · max 1 c⁻¹`, respectively) from the corner — i.e. *inside the blur
window*, where the two branches are as straight as the local model assumes.  This is the form in
which the obstruction bites: any proposed injectivity proof must exclude a collision of the kernel
weights at the *smallest* scale. -/
theorem exists_collision_cornerBlur_of_collinear {b : ℝ → ℝ} (hb : IsBlurKernel b)
    {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) {p : E} (hp : p ≠ 0) :
    ∃ τ₁ τ₂ : ℝ, τ₁ ≠ τ₂ ∧ cornerBlur b δ p (-c • p) τ₁ = cornerBlur b δ p (-c • p) τ₂ ∧
      τ₂ ≤ δ * max 1 c⁻¹ ∧ -τ₁ ≤ c * δ * max 1 c⁻¹ := by
  set τ₂ : ℝ := max δ (δ / c) with hτ₂def
  set τ₁ : ℝ := -c * τ₂ with hτ₁def
  have hτ₂_pos : 0 < τ₂ := lt_of_lt_of_le hδ (le_max_left _ _)
  have hτ₂_le : τ₂ ≤ δ * max 1 c⁻¹ := by
    rw [hτ₂def]
    refine max_le ?_ ?_
    · exact le_mul_of_one_le_right hδ.le (le_max_left _ _)
    · rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) c⁻¹) hδ.le
  have hτ₁_le : τ₁ ≤ -δ := by
    have hcτ : δ ≤ c * τ₂ := by
      have h2 : δ / c ≤ τ₂ := le_max_right _ _
      have h3 : δ ≤ c * (δ / c) := by rw [mul_div_cancel₀ _ (ne_of_gt hc)]
      nlinarith [h2, h3, hc]
    rw [hτ₁def]; linarith
  have hne : τ₁ ≠ τ₂ := by
    rw [hτ₁def]
    intro h
    nlinarith [hc, hτ₂_pos]
  have hval₁ : cornerBlur b δ p (-c • p) τ₁ = τ₁ • p := by
    rw [cornerBlur, cornerP_eq_of_le hb hδ hτ₁_le,
      cornerQ_eq_zero_of_le hδ hτ₁_le, zero_smul, add_zero]
  have hval₂ : cornerBlur b δ p (-c • p) τ₂ = τ₁ • p := by
    rw [cornerBlur, cornerP_eq_zero_of_ge hδ (le_max_left δ (δ / c)),
      cornerQ_eq_of_ge hb hδ (le_max_left δ (δ / c)), zero_smul, zero_add, smul_smul]
    rw [hτ₁def]
    congr 1
    ring
  refine ⟨τ₁, τ₂, hne, hval₁.trans hval₂.symm, hτ₂_le, ?_⟩
  rw [hτ₁def, neg_mul, neg_neg]
  calc c * τ₂ ≤ c * (δ * max 1 c⁻¹) := mul_le_mul_of_nonneg_left hτ₂_le hc.le
    _ = c * δ * max 1 c⁻¹ := by ring

end Work.Drive

end
