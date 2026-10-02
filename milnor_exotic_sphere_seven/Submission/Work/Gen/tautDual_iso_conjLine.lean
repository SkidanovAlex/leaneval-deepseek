import Mathlib
import Submission.Work.Gen.ConjLine
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Gen.EulerGauge
import Submission.Work.Gen.DualLineCore

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# `O(1) ≅ \overline{O(-1)}` over `ℂPⁿ`

The dual `O(1)` of the tautological line bundle `O(-1)` of `ℂPⁿ` is isomorphic to the conjugate
`\overline{O(-1)}` of the tautological bundle, as complex line bundles:
`Work.Gen.tautDual_iso_conjLine`.

In the gluing model over the standard `(n+1)`-chart cover,
* `tautDual n` has transition functions `h(i,j) = z_j/z_i` carried by `coordChange i j = h(j,i)`,
* `conjLine n` has the conjugated transitions `\overline{h(i,j)}`.

The isomorphism is the pointwise gauge `Φ i t x = \overline{h(i,t)(x)} / g_i(x)` where
`g_i(x) = 1 + ∑_k ‖chartFun i x k‖²` is the squared norm of the normalised representative in the
chart `i` (`Work.Gen.gaugeFun n i x`); the cocycle identity `g_i = ‖h(i,j)‖² · g_j` on the overlap
(`Work.Gen.gaugeFun_homCoord_real`) makes the gauge descend to a bundle isomorphism, and
`Work.Thom.nonempty_bundleIso_of_gauge` assembles it from the pointwise identities.
-/

open Work.Projective

namespace Work.Gen

noncomputable section

variable {n : ℕ}

/-! ## Elementary lemmas about `homCoord` -/

/-- On the overlap of the charts `i` and `j`, the homogeneous ratios `z_j/z_i` and `z_i/z_j` are
mutually inverse. -/
theorem homCoord_mul_inv_eq_one (i j : Fin (n + 1)) {x : CP n}
    (hi : x ∈ chartSet i) (hj : x ∈ chartSet j) :
    homCoord n j i x * homCoord n i j x = 1 := by
  have h := homCoord_mul i j i hi hj hi
  rw [homCoord_self] at h
  exact h.symm

/-- On the overlap of the charts `i` and `j`, the homogeneous ratio `z_j/z_i` is nonzero. -/
theorem homCoord_ne_zero_of_mem (i j : Fin (n + 1)) {x : CP n}
    (hi : x ∈ chartSet i) (hj : x ∈ chartSet j) : homCoord n i j x ≠ 0 := by
  intro h0
  have h := homCoord_mul i j i hi hj hi
  rw [homCoord_self, h0, mul_zero] at h
  exact one_ne_zero h

/-- On the overlap, `z_i/z_j` is the inverse of `z_j/z_i`. -/
theorem homCoord_eq_inv_of_mem (i j : Fin (n + 1)) {x : CP n}
    (hi : x ∈ chartSet i) (hj : x ∈ chartSet j) :
    homCoord n j i x = (homCoord n i j x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (homCoord_mul_inv_eq_one i j hi hj)

/-- The scalar `Work.Gen.lam` is the homogeneous ratio. -/
theorem lam_eq_homCoord (i j : Fin (n + 1)) (u : Fin n → ℂ) :
    lam i j u = homCoord n i j (chartInv i u) := by
  rw [lam, vVec, homCoord_chartInv_eq]

/-! ## The squared-norm gauge and its cocycle property -/

/-- The squared norm `∑_m ‖vVec i u m‖²` of the normalised representative is the gauge
`Work.Gen.gaugeFun n i` read in the chart `i`. -/
theorem gaugeFun_chartInv (i : Fin (n + 1)) (u : Fin n → ℂ) :
    gaugeFun n i (chartInv i u) = ∑ m : Fin (n + 1), ‖vVec i u m‖ ^ 2 := by
  rw [gaugeFun, chartFun_chartInv,
    Fin.sum_univ_succAbove (fun m : Fin (n + 1) => ‖vVec i u m‖ ^ 2) i]
  simp only [vVec, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, norm_one, one_pow]

/-- `(‖z‖² : ℂ) = z * \bar z` for a complex number. -/
theorem ofReal_norm_sq_eq_mul_star (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [Complex.star_def]

/-- The same identity after pushing the coercion inside the square. -/
theorem ofReal_norm_sq_eq_mul_star' (z : ℂ) :
    ((‖z‖ : ℂ)) ^ 2 = z * star z := by
  rw [← Complex.ofReal_pow, ofReal_norm_sq_eq_mul_star]

/-- **The cocycle property of the squared-norm gauge**: on the overlap of the charts `i` and `j`,
`gaugeFun n i x = ‖z_j/z_i‖² · gaugeFun n j x`. -/
theorem gaugeFun_homCoord_real (i j : Fin (n + 1)) {x : CP n}
    (hi : x ∈ chartSet i) (hj : x ∈ chartSet j) :
    gaugeFun n i x = ‖homCoord n i j x‖ ^ 2 * gaugeFun n j x := by
  obtain ⟨u, rfl⟩ := hi
  have h1 := gaugeFun_chartInv (n := n) i u
  have h2 : gaugeFun n j (chartInv i u) =
      ∑ m : Fin (n + 1), ‖vVec j (Phi i j u) m‖ ^ 2 := by
    conv_lhs => rw [← chartInv_chartFun j (chartInv i u) hj]
    exact gaugeFun_chartInv (n := n) j (Phi i j u)
  have hmain : gaugeFun n i (chartInv i u) = ‖lam i j u‖ ^ 2 * gaugeFun n j (chartInv i u) := by
    rw [h1, h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [vVec_eq_lam_smul (n := n) hj]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  rw [lam_eq_homCoord] at hmain
  exact hmain

/-! ## The scalar gauge identities -/

/-- The complexified gauge function. -/
def gaugeC (n : ℕ) (i : Fin (n + 1)) (x : CP n) : ℂ := (gaugeFun n i x : ℂ)

/-- The forward gauge scalar `Φ i t`. -/
def phiC (n : ℕ) (i t : Fin (n + 1)) (x : CP n) : ℂ :=
  star (homCoord n i t x) / gaugeC n i x

/-- The inverse gauge scalar `Φ⁻¹ i t`. -/
def phiInvC (n : ℕ) (i t : Fin (n + 1)) (x : CP n) : ℂ :=
  gaugeC n i x / star (homCoord n i t x)

theorem gaugeC_ne_zero (i : Fin (n + 1)) (x : CP n) : gaugeC n i x ≠ 0 := by
  rw [gaugeC, Complex.ofReal_ne_zero]
  exact ne_of_gt (gaugeFun_pos n i x)

/-- The complexified cocycle identity of the gauge. -/
theorem gaugeC_mul (i j : Fin (n + 1)) {x : CP n}
    (hi : x ∈ chartSet i) (hj : x ∈ chartSet j) :
    gaugeC n i x = homCoord n i j x * star (homCoord n i j x) * gaugeC n j x := by
  rw [gaugeC, gaugeC, gaugeFun_homCoord_real i j hi hj]
  push_cast
  rw [ofReal_norm_sq_eq_mul_star']

/-- **`Φ` transforms the target chart correctly**: `\overline{h(t,t')} · Φ i t = Φ i t'`. -/
theorem phiC_htgt (i t t' : Fin (n + 1)) {b : CP n}
    (hb_i : b ∈ chartSet i) (hb_t : b ∈ chartSet t) (hb_t' : b ∈ chartSet t') :
    star (homCoord n t t' b) * phiC n i t b = phiC n i t' b := by
  have hm : homCoord n i t' b = homCoord n t t' b * homCoord n i t b :=
    homCoord_mul i t t' hb_i hb_t hb_t'
  have hG : gaugeC n i b ≠ 0 := gaugeC_ne_zero i b
  simp only [phiC]
  rw [hm, star_mul]
  field_simp

/-- **`Φ` transforms the source chart correctly**: `Φ i t · h(i,i') = Φ i' t`. -/
theorem phiC_hsrc (i t i' : Fin (n + 1)) {b : CP n}
    (hb_i : b ∈ chartSet i) (hb_i' : b ∈ chartSet i') (hb_t : b ∈ chartSet t) :
    phiC n i t b * homCoord n i i' b = phiC n i' t b := by
  have hm : homCoord n i t b = homCoord n i' t b * homCoord n i i' b :=
    homCoord_mul i i' t hb_i hb_i' hb_t
  have hg : gaugeC n i b = homCoord n i i' b * star (homCoord n i i' b) * gaugeC n i' b :=
    gaugeC_mul i i' hb_i hb_i'
  have hGi : gaugeC n i b ≠ 0 := gaugeC_ne_zero i b
  have hGi' : gaugeC n i' b ≠ 0 := gaugeC_ne_zero i' b
  have hH : homCoord n i i' b ≠ 0 := homCoord_ne_zero_of_mem i i' hb_i hb_i'
  have hHst : star (homCoord n i i' b) ≠ 0 := star_ne_zero.mpr hH
  have hden : homCoord n i i' b * star (homCoord n i i' b) * gaugeC n i' b ≠ 0 := by
    rw [← hg]; exact hGi
  simp only [phiC]
  rw [hm, star_mul, hg]
  field_simp

/-- **`Φ⁻¹` transforms the target chart correctly**. -/
theorem phiInvC_htgtinv (i t t' : Fin (n + 1)) {b : CP n}
    (hb_i : b ∈ chartSet i) (hb_t : b ∈ chartSet t) (hb_t' : b ∈ chartSet t') :
    phiInvC n i t b * star (homCoord n t' t b) = phiInvC n i t' b := by
  have hm : homCoord n i t b = homCoord n t' t b * homCoord n i t' b :=
    homCoord_mul i t' t hb_i hb_t' hb_t
  have hG : gaugeC n i b ≠ 0 := gaugeC_ne_zero i b
  have hA : homCoord n t' t b ≠ 0 := homCoord_ne_zero_of_mem t' t hb_t' hb_t
  have hB : homCoord n i t' b ≠ 0 := homCoord_ne_zero_of_mem i t' hb_i hb_t'
  have hAst : star (homCoord n t' t b) ≠ 0 := star_ne_zero.mpr hA
  have hBst : star (homCoord n i t' b) ≠ 0 := star_ne_zero.mpr hB
  simp only [phiInvC]
  rw [hm, star_mul]
  field_simp

/-- **`Φ⁻¹` transforms the source chart correctly**. -/
theorem phiInvC_hsrcinv (i t i' : Fin (n + 1)) {b : CP n}
    (hb_i : b ∈ chartSet i) (hb_i' : b ∈ chartSet i') (hb_t : b ∈ chartSet t) :
    homCoord n i' i b * phiInvC n i t b = phiInvC n i' t b := by
  have hm : homCoord n i t b = homCoord n i' t b * homCoord n i i' b :=
    homCoord_mul i i' t hb_i hb_i' hb_t
  have hg : gaugeC n i b = homCoord n i i' b * star (homCoord n i i' b) * gaugeC n i' b :=
    gaugeC_mul i i' hb_i hb_i'
  have hinv : homCoord n i' i b = (homCoord n i i' b)⁻¹ :=
    homCoord_eq_inv_of_mem i i' hb_i hb_i'
  have hH : homCoord n i i' b ≠ 0 := homCoord_ne_zero_of_mem i i' hb_i hb_i'
  have hHst : star (homCoord n i i' b) ≠ 0 := star_ne_zero.mpr hH
  have hGi : gaugeC n i b ≠ 0 := gaugeC_ne_zero i b
  have hGi' : gaugeC n i' b ≠ 0 := gaugeC_ne_zero i' b
  have hB : homCoord n i' t b ≠ 0 := homCoord_ne_zero_of_mem i' t hb_i' hb_t
  have hBst : star (homCoord n i' t b) ≠ 0 := star_ne_zero.mpr hB
  have hden : homCoord n i i' b * star (homCoord n i i' b) * gaugeC n i' b ≠ 0 := by
    rw [← hg]; exact hGi
  simp only [phiInvC]
  rw [hinv, hm, star_mul, hg]
  field_simp

/-- `Φ⁻¹ i i'` is a left inverse to `Φ i i'`. -/
theorem phiInvC_phiC (i i' : Fin (n + 1)) {b : CP n}
    (hb_i : b ∈ chartSet i) (hb_i' : b ∈ chartSet i') :
    phiInvC n i i' b * phiC n i i' b = 1 := by
  have hH : homCoord n i i' b ≠ 0 := homCoord_ne_zero_of_mem i i' hb_i hb_i'
  have hHst : star (homCoord n i i' b) ≠ 0 := star_ne_zero.mpr hH
  have hG : gaugeC n i b ≠ 0 := gaugeC_ne_zero i b
  simp only [phiC, phiInvC]
  field_simp

/-- `Φ i i'` is a right inverse to `Φ⁻¹ i i'`. -/
theorem phiC_phiInvC (i i' : Fin (n + 1)) {b : CP n}
    (hb_i : b ∈ chartSet i) (hb_i' : b ∈ chartSet i') :
    phiC n i i' b * phiInvC n i i' b = 1 := by
  have hH : homCoord n i i' b ≠ 0 := homCoord_ne_zero_of_mem i i' hb_i hb_i'
  have hHst : star (homCoord n i i' b) ≠ 0 := star_ne_zero.mpr hH
  have hG : gaugeC n i b ≠ 0 := gaugeC_ne_zero i b
  simp only [phiC, phiInvC]
  field_simp

/-! ## Continuity of the gauge -/

theorem continuousOn_gaugeC (i : Fin (n + 1)) :
    ContinuousOn (fun x => gaugeC n i x) (chartSet i) := by
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  unfold gaugeFun
  refine ContinuousOn.add continuousOn_const ?_
  refine continuousOn_finsetSum Finset.univ ?_
  intro k _
  exact ((continuous_apply k).comp_continuousOn (continuousOn_chartFun i)).norm.pow 2

theorem continuousOn_phiC (i t : Fin (n + 1)) :
    ContinuousOn (fun b => phiC n i t b) (chartSet i ∩ chartSet t) := by
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuousOn_homCoord i t).star.mono Set.inter_subset_left
  · exact (continuousOn_gaugeC i).mono Set.inter_subset_left
  · intro b _; exact gaugeC_ne_zero i b

theorem continuousOn_phiInvC (i t : Fin (n + 1)) :
    ContinuousOn (fun b => phiInvC n i t b) (chartSet i ∩ chartSet t) := by
  refine ContinuousOn.div ?_ ?_ ?_
  · exact (continuousOn_gaugeC i).mono Set.inter_subset_left
  · exact (continuousOn_homCoord i t).star.mono Set.inter_subset_left
  · intro b hb
    exact star_ne_zero.mpr (homCoord_ne_zero_of_mem i t hb.1 hb.2)

/-- Multiplication of two scalar multiples of the identity on the line `ℂ`. -/
theorem smul_id_comp_smul_id (a b : ℂ) :
    (a • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) ∘SL
        (b • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1))) =
      (a * b) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    smul_smul]

/-! ## The isomorphism -/

theorem tautDual_iso_conjLine (n : ℕ) :
    Nonempty (Work.Thom.BundleIso (Work.Gen.tautDual n) (Work.Gen.conjLine n)) := by
  refine Work.Thom.nonempty_bundleIso_of_gauge (tautDual n) (conjLine n)
    (fun i t b => phiC n i t b • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
    (fun i t b => phiInvC n i t b • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i i'
    change ContinuousOn
      (fun b => phiC n i i' b • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
      (chartSet i ∩ chartSet i')
    exact ContinuousOn.smul (continuousOn_phiC i i') continuousOn_const
  · intro i i'
    change ContinuousOn
      (fun b => phiInvC n i i' b • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)))
      (chartSet i ∩ chartSet i')
    exact ContinuousOn.smul (continuousOn_phiInvC i i') continuousOn_const
  · intro i t t' b hb_i hb_t hb_t'
    simp only [tautDual_baseSet, conjLine_baseSet] at hb_i hb_t hb_t'
    simp only [conjLine_coordChange]
    rw [smul_id_comp_smul_id, phiC_htgt i t t' hb_i hb_t hb_t']
  · intro i t i' b hb_i hb_i' hb_t
    simp only [tautDual_baseSet, conjLine_baseSet] at hb_i hb_i' hb_t
    simp only [tautDual_coordChange]
    rw [smul_id_comp_smul_id, phiC_hsrc i t i' hb_i hb_i' hb_t]
  · intro i t t' b hb_i hb_t hb_t'
    simp only [tautDual_baseSet, conjLine_baseSet] at hb_i hb_t hb_t'
    simp only [conjLine_coordChange]
    rw [smul_id_comp_smul_id, phiInvC_htgtinv i t t' hb_i hb_t hb_t']
  · intro i t i' b hb_i hb_i' hb_t
    simp only [tautDual_baseSet, conjLine_baseSet] at hb_i hb_i' hb_t
    simp only [tautDual_coordChange]
    rw [smul_id_comp_smul_id, phiInvC_hsrcinv i t i' hb_i hb_i' hb_t]
  · intro i i' b x hb
    simp only [Set.mem_inter_iff, tautDual_baseSet, conjLine_baseSet] at hb
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    rw [phiInvC_phiC i i' hb.1 hb.2, one_smul]
  · intro i i' b y hb
    simp only [Set.mem_inter_iff, tautDual_baseSet, conjLine_baseSet] at hb
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    rw [phiC_phiInvC i i' hb.1 hb.2, one_smul]

end

end Work.Gen
