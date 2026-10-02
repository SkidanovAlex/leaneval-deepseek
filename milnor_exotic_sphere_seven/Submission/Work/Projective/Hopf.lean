import Mathlib
import Submission.Work.Projective.Basic
import Submission.Work.Projective.Atlas

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The explicit map `ℂP¹ → S²`

This module sets up the explicit "Hopf-type" map `hopfProj : ℂP¹ → S²`,
`[z₀ : z₁] ↦ ((2 z₀ z̄₁), |z₁|² - |z₀|²)/(|z₀|² + |z₁|²) ∈ ℂ ⊕ ℝ ≅ ℝ³`,
proves that it is continuous with values in the unit sphere, and records the algebraic identities
about it that are needed to identify `ℂP¹` with `S²` (`Work.Projective.nonempty_homeo_cp_one_sphere`).

Concretely, with `hopfU v = v 0 * conj (v 1)` and `hopfN v = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2`:

* `hopfZ v = 2 * hopfU v / hopfN v` is the complex number `x + i y`,
* `hopfW v = (‖v 1‖ ^ 2 - ‖v 0‖ ^ 2) / hopfN v` is the third coordinate `z`,
* `hopfPt v = ![(hopfZ v).re, (hopfZ v).im, hopfW v]` is the corresponding point of `ℝ³`.

Both `hopfZ` and `hopfW` are invariant under scaling (`hopfZ_smul`, `hopfW_smul`), so `hopfPt`
descends to `hopfProj : ℂP¹ → S²`, whose continuity follows from the quotient topology of `ℂP¹`
(`continuous_hopfProj`).  The key identities for inverting `hopfProj` are `hopfZ_eq_ratio_mul`
(`hopfZ v = (v 0 / v 1) * (1 + hopfW v)` when `v 1 ≠ 0`) and `one_add_hopfW_pos`.
-/

open scoped LinearAlgebra.Projectivization Manifold ContDiff Topology

namespace Work.Projective

noncomputable section

/-! ## The explicit map on vectors -/

/-- The square `‖v 0‖ ^ 2 + ‖v 1‖ ^ 2` of the norm of a vector of `ℂ²` (which is `≠ 0` exactly when
`v ≠ 0`). -/
def hopfN (v : CPV 1) : ℝ := ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2

/-- The auxiliary complex number `v 0 * conj (v 1)`. -/
def hopfU (v : CPV 1) : ℂ := v 0 * star (v 1)

/-- The first two coordinates `(2 v₀ v̄₁)/(|v₀|² + |v₁|²)`, as a complex number. -/
def hopfZ (v : CPV 1) : ℂ := 2 * hopfU v / (hopfN v : ℂ)

/-- The third coordinate `(|v₁|² - |v₀|²)/(|v₀|² + |v₁|²)`. -/
def hopfW (v : CPV 1) : ℝ := (‖v 1‖ ^ 2 - ‖v 0‖ ^ 2) / hopfN v

/-- **The point of `ℝ³` attached to a vector `v : ℂ²`.** -/
def hopfPt (v : CPV 1) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(hopfZ v).re, (hopfZ v).im, hopfW v]

@[simp] theorem hopfPt_apply_0 (v : CPV 1) : hopfPt v 0 = (hopfZ v).re := by simp [hopfPt]

@[simp] theorem hopfPt_apply_1 (v : CPV 1) : hopfPt v 1 = (hopfZ v).im := by simp [hopfPt]

@[simp] theorem hopfPt_apply_2 (v : CPV 1) : hopfPt v 2 = hopfW v := by simp [hopfPt]

/-- `hopfN v` vanishes only for `v = 0`. -/
theorem hopfN_pos {v : CPV 1} (hv : v ≠ 0) : 0 < hopfN v := by
  have h : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext fun i => by fin_cases i <;> simp_all)
  rcases h with h | h
  · exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h) 2) (le_add_of_nonneg_right (sq_nonneg _))
  · exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr h) 2) (le_add_of_nonneg_left (sq_nonneg _))

theorem hopfN_ne_zero {v : CPV 1} (hv : v ≠ 0) : hopfN v ≠ 0 := ne_of_gt (hopfN_pos hv)

/-- `‖z‖ ^ 2 = conj z * z`, in the form of a complex number. -/
theorem norm_sq_eq_star_mul (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  have h2 : star z * z = ((Complex.normSq (star z) : ℝ) : ℂ) := by
    rw [show star z * z = star z * star (star z) by rw [star_star]]
    exact Complex.mul_conj (star z)
  rw [h2, Complex.normSq_eq_norm_sq, norm_star]

/-! ## Behaviour under scaling -/

theorem hopfN_smul (t : ℂ) (v : CPV 1) : hopfN (t • v) = ‖t‖ ^ 2 * hopfN v := by
  simp only [hopfN, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

theorem hopfU_smul (t : ℂ) (v : CPV 1) : hopfU (t • v) = ((‖t‖ ^ 2 : ℝ) : ℂ) * hopfU v := by
  have h : star t * t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm]
    simpa [Complex.normSq_eq_norm_sq] using (Complex.mul_conj t)
  simp only [hopfU, Pi.smul_apply, smul_eq_mul, star_mul]
  rw [show t * v 0 * (star (v 1) * star t) = (star t * t) * (v 0 * star (v 1)) by ring, h]

theorem hopfZ_smul {t : ℂ} (ht : t ≠ 0) (v : CPV 1) : hopfZ (t • v) = hopfZ v := by
  have ht2 : ((‖t‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
  have h := hopfU_smul t v
  simp only [hopfZ, h, hopfN_smul]
  rw [Complex.ofReal_mul]
  field_simp

theorem hopfW_smul {t : ℂ} (ht : t ≠ 0) (v : CPV 1) : hopfW (t • v) = hopfW v := by
  have ht2 : ‖t‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ht)
  simp only [hopfW, hopfN_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  field_simp

theorem hopfPt_smul {t : ℂ} (ht : t ≠ 0) (v : CPV 1) : hopfPt (t • v) = hopfPt v := by
  simp only [hopfPt, hopfZ_smul ht, hopfW_smul ht]

/-! ## The image lies in the unit sphere -/

theorem hopf_identity (A B : ℝ) (C : ℂ) (hC : ‖C‖ ^ 2 = A * B) (N : ℝ) (hNN : N = A + B)
    (hN0 : N ≠ 0) :
    ((2 * C / (N : ℂ)).re) ^ 2 + ((2 * C / (N : ℂ)).im) ^ 2 + ((B - A) / N) ^ 2 = 1 := by
  have h1 : ((2 * C / (N : ℂ)).re) ^ 2 + ((2 * C / (N : ℂ)).im) ^ 2 = ‖2 * C / (N : ℂ)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [sq]
    rw [← Complex.normSq_apply]
  rw [h1]
  have h2 : ‖2 * C / (N : ℂ)‖ ^ 2 = 4 * ‖C‖ ^ 2 / N ^ 2 := by
    rw [show ‖2 * C / (N : ℂ)‖ ^ 2 = Complex.normSq (2 * C / (N : ℂ))
        from (Complex.normSq_eq_norm_sq _).symm,
      Complex.normSq_div, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq C]
    simp
    ring
  rw [h2, hC, hNN] at *
  field_simp
  ring

/-- **`hopfPt v` is a unit vector** for `v ≠ 0`. -/
theorem hopfPt_norm_sq {v : CPV 1} (hv : v ≠ 0) : ‖hopfPt v‖ ^ 2 = 1 := by
  have hN0 : hopfN v ≠ 0 := hopfN_ne_zero hv
  have hAB : ‖hopfU v‖ ^ 2 = ‖v 0‖ ^ 2 * ‖v 1‖ ^ 2 := by
    rw [hopfU, norm_mul, norm_star, mul_pow]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp only [hopfPt, hopfZ, hopfW]
  exact hopf_identity (‖v 0‖ ^ 2) (‖v 1‖ ^ 2) (hopfU v) hAB (hopfN v) rfl hN0

/-! ## The value of the map on the affine chart and at the poles -/

/-- On the chart `z ↦ [z : 1]` the map `hopfZ` is the rational map `z ↦ 2z/(1 + |z|²)`. -/
theorem hopfZ_cons (w : ℂ) : hopfZ ![w, 1] = 2 * w / (1 + ((‖w‖ ^ 2 : ℝ) : ℂ)) := by
  simp only [hopfZ, hopfU, hopfN]
  norm_num
  ring_nf

/-- On the chart `z ↦ [z : 1]` the map `hopfW` is the rational map `z ↦ (1 - |z|²)/(1 + |z|²)`. -/
theorem hopfW_cons (w : ℂ) : hopfW ![w, 1] = (1 - ‖w‖ ^ 2) / (1 + ‖w‖ ^ 2) := by
  simp only [hopfW, hopfN]
  norm_num
  ring_nf

theorem hopfZ_eq_zero_of_second_eq_zero {v : CPV 1} (h : v 1 = 0) : hopfZ v = 0 := by
  simp [hopfZ, hopfU, h]

theorem hopfW_eq_neg_one_of_second_eq_zero {v : CPV 1} (hv : v ≠ 0) (h : v 1 = 0) :
    hopfW v = -1 := by
  have h0 : v 0 ≠ 0 := fun h0 => hv (funext fun i => by fin_cases i <;> simp_all)
  have hx : ‖v 0‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h0)
  simp only [hopfW, hopfN, h, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
    zero_sub]
  field_simp

theorem hopfZ_zero_cons : hopfZ ![1, 0] = 0 := by
  simp [hopfZ, hopfU]

theorem hopfW_zero_cons : hopfW ![1, 0] = -1 := by
  simp only [hopfW, hopfN]
  norm_num

/-- `hopfPt ![1,0]` is the south pole of the sphere. -/
theorem hopfPt_zero_cons : hopfPt ![1, 0] = WithLp.toLp 2 ![(0 : ℝ), 0, -1] := by
  ext i
  fin_cases i <;> simp [hopfZ_zero_cons, hopfW_zero_cons]

/-! ## The relation between `hopfZ` and `hopfW` -/

theorem hopfU_mul_second (v : CPV 1) : hopfU v * v 1 = v 0 * ((‖v 1‖ ^ 2 : ℝ) : ℂ) := by
  rw [hopfU, mul_assoc, ← norm_sq_eq_star_mul (v 1)]

theorem hopf_alg_key (x A B : ℂ) (h : B + A ≠ 0) :
    2 * (x * A) / (B + A) = x * (1 + (A - B) / (B + A)) := by
  field_simp
  ring

/-- `(1 + hopfW v) * v 1 = 2 ‖v 1‖ ^ 2 / hopfN v * v 1`, i.e. the form in which `hopfZ` is the
product of `v 0 / v 1` with `1 + hopfW v`. -/
theorem hopfZ_mul_second {v : CPV 1} (h : v 1 ≠ 0) :
    hopfZ v * v 1 = v 0 * (1 + (hopfW v : ℂ)) := by
  have hv : v ≠ 0 := fun hz => h (by rw [hz]; rfl)
  have hsum : (0 : ℝ) < ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
    have := hopfN_pos hv
    rwa [hopfN] at this
  have hL : hopfZ v * v 1 = 2 * (hopfU v * v 1) / (hopfN v : ℂ) := by rw [hopfZ]; ring
  rw [hL, hopfU_mul_second, hopfW, hopfN]
  push_cast
  refine hopf_alg_key (v 0) (((‖v 1‖ : ℂ)) ^ 2) (((‖v 0‖ : ℂ)) ^ 2) ?_
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_add, Complex.ofReal_ne_zero]
  exact ne_of_gt hsum

/-- **The key relation**: on the chart where `v 1 ≠ 0`, the point `hopfZ v` is `v 0 / v 1` scaled by
`1 + hopfW v`. -/
theorem hopfZ_eq_ratio_mul {v : CPV 1} (h : v 1 ≠ 0) :
    hopfZ v = (v 0 / v 1) * (1 + (hopfW v : ℂ)) := by
  have h1 : hopfZ v = hopfZ v * v 1 / v 1 := by rw [mul_div_cancel_right₀ _ h]
  rw [h1, hopfZ_mul_second h]
  ring

/-- `1 + hopfW v` is positive when `v 1 ≠ 0` (it is `2‖v 1‖²/hopfN v`). -/
theorem one_add_hopfW_pos {v : CPV 1} (h : v 1 ≠ 0) : 0 < 1 + hopfW v := by
  have hv : v ≠ 0 := fun hz => h (by rw [hz]; rfl)
  have hNpos : (0 : ℝ) < ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
    have := hopfN_pos hv
    rwa [hopfN] at this
  have hx : 0 < ‖v 1‖ ^ 2 := pow_pos (norm_pos_iff.mpr h) 2
  have h1 : 1 + hopfW v = 2 * ‖v 1‖ ^ 2 / hopfN v := by
    rw [hopfW, hopfN]
    field_simp
    ring
  rw [h1]
  exact div_pos (by linarith) hNpos

theorem one_add_hopfW_ne_zero {v : CPV 1} (h : v 1 ≠ 0) : 1 + (hopfW v : ℂ) ≠ 0 := by
  have hp := one_add_hopfW_pos h
  intro hc
  have : (1 + hopfW v : ℝ) = 0 := by simpa using congrArg Complex.re hc
  linarith

/-! ## Continuity of the explicit map -/

theorem continuous_hopfU : Continuous hopfU := by
  change Continuous fun v : CPV 1 => v 0 * star (v 1)
  fun_prop

theorem continuous_hopfN : Continuous hopfN := by
  change Continuous fun v : CPV 1 => ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2
  fun_prop

theorem continuousOn_hopfZ : ContinuousOn hopfZ {v : CPV 1 | v ≠ 0} := by
  change ContinuousOn (fun v : CPV 1 => 2 * hopfU v / (hopfN v : ℂ)) {v | v ≠ 0}
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuous_const.mul continuous_hopfU).continuousOn
  · exact (Complex.continuous_ofReal.comp continuous_hopfN).continuousOn
  · intro v hv
    have := hopfN_pos hv
    exact_mod_cast ne_of_gt this

theorem continuousOn_hopfW : ContinuousOn hopfW {v : CPV 1 | v ≠ 0} := by
  change ContinuousOn (fun v : CPV 1 => (‖v 1‖ ^ 2 - ‖v 0‖ ^ 2) / hopfN v) {v | v ≠ 0}
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (((continuous_apply 1).norm.pow 2).sub ((continuous_apply 0).norm.pow 2)).continuousOn
  · exact continuous_hopfN.continuousOn
  · intro v hv
    exact hopfN_ne_zero hv

theorem continuous_hopfZ :
    Continuous (fun v : {v : CPV 1 // v ≠ 0} => hopfZ v.1) := continuousOn_hopfZ.domRestrict

theorem continuous_hopfW :
    Continuous (fun v : {v : CPV 1 // v ≠ 0} => hopfW v.1) := continuousOn_hopfW.domRestrict

theorem continuous_hopfPt :
    Continuous (fun v : {v : CPV 1 // v ≠ 0} => hopfPt v.1) := by
  have h1 := continuous_hopfZ
  have h2 := continuous_hopfW
  simp only [hopfPt]
  fun_prop

/-! ## The map on `ℂP¹` -/

/-- The map on the unit sphere of nonzero vectors. -/
def hopfSphere (v : {v : CPV 1 // v ≠ 0}) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨hopfPt v.1, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    nlinarith [norm_nonneg (hopfPt v.1), hopfPt_norm_sq v.2]⟩

theorem continuous_hopfSphere : Continuous hopfSphere :=
  Continuous.subtype_mk continuous_hopfPt _

/-- **The map `ℂP¹ → S²`**, descending from `hopfPt` (which is scale-invariant). -/
def hopfProj : CP 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  Projectivization.lift hopfSphere (fun a b t h => by
    have ht : t ≠ 0 := by rintro rfl; rw [zero_smul] at h; exact a.2 h
    refine Subtype.ext ?_
    change hopfPt a.1 = hopfPt b.1
    rw [h, hopfPt_smul ht])

theorem hopfProj_cpMk (v : {v : CPV 1 // v ≠ 0}) : hopfProj (cpMk 1 v) = hopfSphere v := by
  simp only [cpMk_apply]
  exact Projectivization.lift_mk _ _ v.1 v.2

theorem continuous_hopfProj : Continuous hopfProj := by
  rw [(isQuotientMap_cpMk 1).continuous_iff]
  have h : hopfProj ∘ cpMk 1 = hopfSphere := funext hopfProj_cpMk
  rw [h]
  exact continuous_hopfSphere


/-! ## The inverse-chart computation -/

private theorem div_identity (z A : ℂ) (hA : A ≠ 0) : 2 * (z / A) / (2 / A) = z := by
  field_simp

private theorem real_div_identity (t : ℝ) (h : 1 + t ≠ 0) :
    (1 - (1 - t) / (1 + t)) / (2 / (1 + t)) = t := by
  field_simp
  ring

/-- **The stereographic coordinate of a point of the sphere lies on the chart**: for a unit vector
`x` of `ℝ³` with `x 2 ≠ -1`, the point `w = (x₀ + i x₁)/(1 + x₂)` of the chart `z ↦ [z : 1]` is
mapped back to `x` by `hopfPt`. -/
theorem hopfPt_cover (x : EuclideanSpace ℝ (Fin 3))
    (hx : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1) (h2 : x 2 ≠ -1) :
    hopfPt ![((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) / (1 + (x 2 : ℂ)), 1] = x := by
  set w : ℂ := ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) / (1 + (x 2 : ℂ)) with hwdef
  have h1x : (1 : ℝ) + x 2 ≠ 0 := fun hc => h2 (by linarith)
  have hc1 : ((1 + x 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact h1x
  have hsum : x 0 ^ 2 + x 1 ^ 2 = (1 - x 2) * (1 + x 2) := by nlinarith [hx]
  have hnum : ‖(x 0 : ℂ) + (x 1 : ℂ) * Complex.I‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hden : ‖(1 + (x 2 : ℂ))‖ ^ 2 = (1 + x 2) ^ 2 := by
    rw [show 1 + (x 2 : ℂ) = ((1 + x 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  have hw_norm : ‖w‖ ^ 2 = (1 - x 2) / (1 + x 2) := by
    rw [hwdef, norm_div, div_pow, hnum, hden, hsum]
    field_simp
  have hw_plus : 1 + ‖w‖ ^ 2 = 2 / (1 + x 2) := by
    rw [hw_norm]
    field_simp
    ring
  have hw_plusC : 1 + ((‖w‖ ^ 2 : ℝ) : ℂ) = 2 / ((1 + x 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, hw_plus]
    push_cast
    ring
  have hw1 : w = ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) / ((1 + x 2 : ℝ) : ℂ) := by
    rw [hwdef, show 1 + (x 2 : ℂ) = ((1 + x 2 : ℝ) : ℂ) by push_cast; ring]
  have hZw : hopfZ ![w, 1] = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
    rw [hopfZ_cons, hw_plusC, hw1]
    exact div_identity _ _ hc1
  have hWw : hopfW ![w, 1] = x 2 := by
    rw [hopfW_cons, hw_plus, hw_norm]
    exact real_div_identity (x 2) h1x
  ext i
  fin_cases i
  · simpa using congrArg Complex.re hZw
  · simpa using congrArg Complex.im hZw
  · simpa using hWw

end

end Work.Projective
