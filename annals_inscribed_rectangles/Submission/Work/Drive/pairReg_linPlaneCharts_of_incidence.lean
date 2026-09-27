import Mathlib
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.unrestrictedFromBox
import Submission.Work.Drive.pairReg_of_loopBoxData
import Submission.Work.Drive.linPlaneTripleRange
import Submission.Work.Drive.sqDisk_foldBox_fderiv_single_ne_zero
import Submission.Work.Drive.sqDisk_foldBox_corner

namespace Work.Drive

open Filter
open Manifold
open scoped Manifold ContDiff Topology

/-! ## Auxiliary development for the incidence criterion -/

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-! ### The folded disk coordinate of a box parameter -/

/-- The disk coordinate attached to a box parameter: `sqDisk ∘ foldBox`. -/
noncomputable def boxZ (y : EuclideanSpace ℝ (Fin 2)) : ℂ := sqDisk (foldBox y)

lemma boxZ_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) boxZ :=
  sqDisk_contDiff.comp (contMDiff_iff_contDiff.mp foldBox_contMDiff)

lemma boxZ_differentiableAt (y : EuclideanSpace ℝ (Fin 2)) : DifferentiableAt ℝ boxZ y :=
  (boxZ_contDiff.differentiable (by simp)).differentiableAt

lemma boxZ_hasFDerivAt (y : EuclideanSpace ℝ (Fin 2)) : HasFDerivAt boxZ (fderiv ℝ boxZ y) y :=
  (boxZ_differentiableAt y).hasFDerivAt

/-! ### The symmetries of the fold

`foldFun x = (1 - cos (π x))/2` is even and symmetric about `1`, so the path `t ↦ foldFun (c ± t)`
is symmetric about `t = 0` for `c ∈ {0,1}`. -/

lemma foldFun_neg_eq (x : ℝ) : foldFun (-x) = foldFun x := by
  simp [foldFun]

lemma foldFun_one_add_eq (x : ℝ) : foldFun (1 + x) = foldFun (1 - x) := by
  have h : Real.cos (Real.pi * x + Real.pi) = Real.cos (Real.pi - Real.pi * x) := by
    rw [Real.cos_add_pi, Real.cos_pi_sub]
  simp only [foldFun]
  have h1 : Real.pi * (1 + x) = Real.pi * x + Real.pi := by ring
  have h2 : Real.pi * (1 - x) = Real.pi - Real.pi * x := by ring
  rw [h1, h2, h]

lemma foldFun_add_eq_sub {c : ℝ} (hc : c = 0 ∨ c = 1) (t : ℝ) :
    foldFun (c - t) = foldFun (c + t) := by
  rcases hc with rfl | rfl
  · simpa using foldFun_neg_eq t
  · exact (foldFun_one_add_eq t).symm

/-! ### The seam of the box -/

lemma pairInc_coord_eq_zero_or_one_of_not_openSquare {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (hn : ¬ openSquare y) :
    ∃ i : Fin 2, y i = 0 ∨ y i = 1 := by
  by_contra hcon
  push Not at hcon
  refine hn ⟨?_, ?_⟩
  · exact ⟨lt_of_le_of_ne (hy 0).1 (Ne.symm (hcon 0).1), lt_of_le_of_ne (hy 0).2 (hcon 0).2⟩
  · exact ⟨lt_of_le_of_ne (hy 1).1 (Ne.symm (hcon 1).1), lt_of_le_of_ne (hy 1).2 (hcon 1).2⟩

lemma pairInc_mem_Ioo_of_not_eq_zero_one {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (i : Fin 2) (h0 : y i ≠ 0) (h1 : y i ≠ 1) :
    y i ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨lt_of_le_of_ne (hy i).1 (Ne.symm h0), lt_of_le_of_ne (hy i).2 h1⟩

lemma foldBox_apply_eq (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    (foldBox y) i = foldFun (y i) := by
  fin_cases i <;> simp [foldBox_apply_zero, foldBox_apply_one]

lemma foldFun_eq_zero_or_one {c : ℝ} (hc : c = 0 ∨ c = 1) : foldFun c = 0 ∨ foldFun c = 1 := by
  rcases hc with rfl | rfl
  · exact Or.inl foldFun_zero
  · exact Or.inr foldFun_one

lemma pairInc_onSeam2_foldBox {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1)
    (hn : ¬ openSquare y) : onSeam2 (foldBox y) := by
  obtain ⟨i, hi⟩ := pairInc_coord_eq_zero_or_one_of_not_openSquare hy hn
  have hfi : (foldBox y) i = 0 ∨ (foldBox y) i = 1 := by
    rw [foldBox_apply_eq]
    exact foldFun_eq_zero_or_one hi
  rcases hfi with h | h
  · fin_cases i
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · fin_cases i
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

/-- On the seam of the box the disk coordinate lies on the unit circle. -/
lemma boxZ_norm_eq_one {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1)
    (hn : ¬ openSquare y) : ‖boxZ y‖ = 1 :=
  (norm_sqDisk_eq_one_iff (foldBox y) (foldBox_mem_unitBox y)).mpr
    (pairInc_onSeam2_foldBox hy hn)


/-! ### The tangent line of the disk coordinate on the seam

At a seam point of the box, the path `t ↦ boxZ (y + t • eᵢ)` is symmetric about `t = 0` when the
`i`-th coordinate folds (equals `0` or `1`), and stays on the unit circle when the other coordinate
folds.  In both cases the derivative of `boxZ` in the direction `eᵢ` is orthogonal to `boxZ y`. -/

lemma single_add_apply_same (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) (t : ℝ) :
    (y + t • EuclideanSpace.single i (1 : ℝ)) i = y i + t := by
  simp [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply]

lemma single_sub_apply_same (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) (t : ℝ) :
    (y - t • EuclideanSpace.single i (1 : ℝ)) i = y i - t := by
  simp [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply]

lemma single_add_apply_ne (y : EuclideanSpace ℝ (Fin 2)) {i j : Fin 2} (hji : j ≠ i) (t : ℝ) :
    (y + t • EuclideanSpace.single i (1 : ℝ)) j = y j := by
  simp [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, hji]

lemma single_sub_apply_ne (y : EuclideanSpace ℝ (Fin 2)) {i j : Fin 2} (hji : j ≠ i) (t : ℝ) :
    (y - t • EuclideanSpace.single i (1 : ℝ)) j = y j := by
  simp [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, hji]

/-- The path `t ↦ boxZ (y + t • eᵢ)` is symmetric about `t = 0` when `y i ∈ {0,1}`. -/
lemma boxZ_add_single_eq_sub_single {y : EuclideanSpace ℝ (Fin 2)} {i : Fin 2} {c : ℝ}
    (hy : y i = c) (hc : c = 0 ∨ c = 1) (t : ℝ) :
    boxZ (y - t • EuclideanSpace.single i (1 : ℝ))
      = boxZ (y + t • EuclideanSpace.single i (1 : ℝ)) := by
  apply congrArg sqDisk
  ext j
  rw [foldBox_apply_eq, foldBox_apply_eq]
  by_cases hji : j = i
  · subst hji
    rw [single_sub_apply_same, single_add_apply_same, hy]
    exact foldFun_add_eq_sub hc t
  · rw [single_sub_apply_ne y hji, single_add_apply_ne y hji]

/-- The affine path `t ↦ y + t • v` has derivative `v` at `0`. -/
lemma hasDerivAt_add_smul (y v : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  simpa using h1.const_add y

/-- The derivative of the disk coordinate along an affine path. -/
lemma hasDerivAt_boxZ_path (y v : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun t : ℝ => boxZ (y + t • v)) (fderiv ℝ boxZ y v) 0 := by
  have hF : HasFDerivAt boxZ (fderiv ℝ boxZ y) (y + (0 : ℝ) • v) := by
    simpa using boxZ_hasFDerivAt y
  have h := hF.comp_hasDerivAt (0 : ℝ) (hasDerivAt_add_smul y v)
  simpa [Function.comp_def] using h

/-- **The derivative of the disk coordinate in a folding direction vanishes.** -/
lemma fderiv_boxZ_single_eq_zero {y : EuclideanSpace ℝ (Fin 2)} {i : Fin 2} {c : ℝ}
    (hy : y i = c) (hc : c = 0 ∨ c = 1) :
    fderiv ℝ boxZ y (EuclideanSpace.single i (1 : ℝ)) = 0 := by
  have hg : HasDerivAt (fun t : ℝ => boxZ (y + t • EuclideanSpace.single i (1 : ℝ)))
      (fderiv ℝ boxZ y (EuclideanSpace.single i (1 : ℝ))) 0 :=
    hasDerivAt_boxZ_path y (EuclideanSpace.single i (1 : ℝ))
  have hg' : HasDerivAt (fun t : ℝ => boxZ (y - t • EuclideanSpace.single i (1 : ℝ)))
      (-(fderiv ℝ boxZ y (EuclideanSpace.single i (1 : ℝ)))) 0 := by
    have h := hasDerivAt_boxZ_path y (-(EuclideanSpace.single i (1 : ℝ)))
    simpa [smul_neg, sub_eq_add_neg, map_neg] using h
  have hsym : (fun t : ℝ => boxZ (y - t • EuclideanSpace.single i (1 : ℝ)))
      = fun t : ℝ => boxZ (y + t • EuclideanSpace.single i (1 : ℝ)) :=
    funext fun t => boxZ_add_single_eq_sub_single hy hc t
  rw [hsym] at hg'
  have hzero := HasDerivAt.unique hg hg'
  have h2 : (2 : ℝ) • fderiv ℝ boxZ y (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hzero
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- A box point whose `i`-th coordinate does not fold is on the seam through one of the other
coordinates. -/
lemma pairInc_other_coord_eq_zero_or_one {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (hn : ¬ openSquare y) {i : Fin 2}
    (h0 : y i ≠ 0) (h1 : y i ≠ 1) : ∃ k : Fin 2, k ≠ i ∧ (y k = 0 ∨ y k = 1) := by
  obtain ⟨k, hk⟩ := pairInc_coord_eq_zero_or_one_of_not_openSquare hy hn
  have hki : k ≠ i := by
    rintro rfl
    exact hk.elim h0 h1
  exact ⟨k, hki, hk⟩

lemma pairInc_add_single_mem_unitBox {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (i : Fin 2) {t : ℝ}
    (ht0 : -(y i) ≤ t) (ht1 : t ≤ 1 - y i) :
    y + t • EuclideanSpace.single i (1 : ℝ) ∈ Submission.Drive.unitBox 1 := by
  intro l
  by_cases hli : l = i
  · subst hli
    rw [single_add_apply_same]
    exact ⟨by linarith, by linarith⟩
  · rw [single_add_apply_ne y hli]
    exact hy l

/-- If the `k`-th coordinate of `y` folds and `k ≠ i`, then the `k`-th coordinate of
`y + t • eᵢ` folds as well. -/
lemma pairInc_onSeam2_foldBox_add_single {y : EuclideanSpace ℝ (Fin 2)} {i k : Fin 2} (hki : k ≠ i)
    (hk : y k = 0 ∨ y k = 1) (t : ℝ) :
    onSeam2 (foldBox (y + t • EuclideanSpace.single i (1 : ℝ))) := by
  have h1 : (y + t • EuclideanSpace.single i (1 : ℝ)) k = y k := single_add_apply_ne y hki t
  have h2 : (foldBox (y + t • EuclideanSpace.single i (1 : ℝ))) k = 0
      ∨ (foldBox (y + t • EuclideanSpace.single i (1 : ℝ))) k = 1 := by
    rw [foldBox_apply_eq, h1]
    exact foldFun_eq_zero_or_one hk
  rcases h2 with h | h
  · fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · fin_cases k
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))

/-- Along a non-folding direction of the seam the disk coordinate stays on the unit circle. -/
lemma boxZ_norm_eq_one_add_single {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) {i k : Fin 2} (hki : k ≠ i) (hk : y k = 0 ∨ y k = 1)
    {t : ℝ} (ht0 : -(y i) ≤ t) (ht1 : t ≤ 1 - y i) :
    ‖boxZ (y + t • EuclideanSpace.single i (1 : ℝ))‖ = 1 :=
  (norm_sqDisk_eq_one_iff _
      (foldBox_mem_unitBox (y + t • EuclideanSpace.single i (1 : ℝ)))).mpr
    (pairInc_onSeam2_foldBox_add_single hki hk t)

/-- **The derivative of the disk coordinate along a direction of the seam is tangent.** -/
lemma pairInc_inner_fderiv_single_eq_zero {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (hn : ¬ openSquare y) (i : Fin 2) :
    inner ℝ (boxZ y) (fderiv ℝ boxZ y (EuclideanSpace.single i (1 : ℝ))) = 0 := by
  by_cases hi : y i = 0 ∨ y i = 1
  · rw [fderiv_boxZ_single_eq_zero (c := y i) rfl hi, inner_zero_right]
  · push Not at hi
    have hIoo := pairInc_mem_Ioo_of_not_eq_zero_one hy i hi.1 hi.2
    obtain ⟨k, hki, hk⟩ := pairInc_other_coord_eq_zero_or_one hy hn hi.1 hi.2
    have hδ : 0 < min (y i) (1 - y i) := lt_min hIoo.1 (by linarith [hIoo.2])
    have hev : (fun t : ℝ => ‖boxZ (y + t • EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
        =ᶠ[𝓝 0] fun _ => (1 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
      have hb : |t| < min (y i) (1 - y i) := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
        exact ht
      have ht0 : -(y i) ≤ t := by
        have h1 := (abs_lt.mp hb).1
        have h2 : min (y i) (1 - y i) ≤ y i := min_le_left _ _
        linarith
      have ht1 : t ≤ 1 - y i := by
        have h1 := (abs_lt.mp hb).2
        have h2 : min (y i) (1 - y i) ≤ 1 - y i := min_le_right _ _
        linarith
      rw [boxZ_norm_eq_one_add_single hy hki hk ht0 ht1]
      norm_num
    have hconst : HasDerivAt (fun t : ℝ =>
        ‖boxZ (y + t • EuclideanSpace.single i (1 : ℝ))‖ ^ 2) 0 0 :=
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).congr_of_eventuallyEq hev
    have hpath := hasDerivAt_boxZ_path y (EuclideanSpace.single i (1 : ℝ))
    have hns : HasDerivAt (fun t : ℝ => ‖boxZ (y + t • EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
        (2 * inner ℝ (boxZ y) (fderiv ℝ boxZ y (EuclideanSpace.single i (1 : ℝ)))) 0 := by
      have hF : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 2) => ‖boxZ x‖ ^ 2)
          (2 • (innerSL ℝ) (boxZ y) ∘SL (fderiv ℝ boxZ y))
          (y + (0 : ℝ) • EuclideanSpace.single i (1 : ℝ)) := by
        simpa using (boxZ_hasFDerivAt y).norm_sq
      have h := hF.comp_hasDerivAt (0 : ℝ) (hasDerivAt_add_smul y (EuclideanSpace.single i (1 : ℝ)))
      have h2 : (2 • ((innerSL ℝ) (boxZ y) ∘SL (fderiv ℝ boxZ y)))
          (EuclideanSpace.single i (1 : ℝ))
          = 2 * inner ℝ (boxZ y) (fderiv ℝ boxZ y (EuclideanSpace.single i (1 : ℝ))) := by
        rw [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
        ring
      rw [h2] at h
      simpa [Function.comp_def] using h
    have hzero := HasDerivAt.unique hns hconst
    have h2 : 2 * inner ℝ (boxZ y) (fderiv ℝ boxZ y (EuclideanSpace.single i (1 : ℝ))) = 0 :=
      hzero
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

lemma pairInc_eq_smul_single (v : EuclideanSpace ℝ (Fin 2)) :
    v = v 0 • EuclideanSpace.single 0 (1 : ℝ) + v 1 • EuclideanSpace.single 1 (1 : ℝ) := by
  ext j
  fin_cases j <;> simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- **The derivative of the disk coordinate at a seam point is tangent to the circle.** -/
lemma pairInc_inner_fderiv_eq_zero {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (hn : ¬ openSquare y)
    (v : EuclideanSpace ℝ (Fin 2)) : inner ℝ (boxZ y) (fderiv ℝ boxZ y v) = 0 := by
  have hdecomp : fderiv ℝ boxZ y v
      = v 0 • fderiv ℝ boxZ y (EuclideanSpace.single 0 (1 : ℝ))
        + v 1 • fderiv ℝ boxZ y (EuclideanSpace.single 1 (1 : ℝ)) := by
    conv_lhs => rw [pairInc_eq_smul_single v]
    rw [map_add, map_smul, map_smul]
  rw [hdecomp, inner_add_right, inner_smul_right, inner_smul_right,
    pairInc_inner_fderiv_single_eq_zero hy hn 0, pairInc_inner_fderiv_single_eq_zero hy hn 1]
  simp

/-- A vector of `ℂ` orthogonal to a non-zero `z` is a real multiple of `I * z`. -/
lemma pairInc_mem_span_I_of_inner_eq_zero {z w : ℂ} (hz : z ≠ 0) (h : inner ℝ z w = 0) :
    w ∈ Submodule.span ℝ ({Complex.I * z} : Set ℂ) := by
  rw [Submodule.mem_span_singleton]
  have hco : w.re * z.re + w.im * z.im = 0 := by
    have h' := h
    rw [Complex.inner] at h'
    simpa [Complex.mul_re, Complex.conj_im, Complex.conj_re] using h'
  have hd : z.re * z.re + z.im * z.im ≠ 0 := by
    have hpos := Complex.normSq_pos.mpr hz
    rw [Complex.normSq_apply] at hpos
    exact ne_of_gt hpos
  refine ⟨(w.im * z.re - w.re * z.im) / (z.re * z.re + z.im * z.im), ?_⟩
  rw [Complex.ext_iff]
  constructor
  · rw [Complex.smul_re, Complex.I_mul_re, smul_eq_mul, div_mul_eq_mul_div, div_eq_iff hd]
    linear_combination (-(z.re)) * hco
  · rw [Complex.smul_im, Complex.I_mul_im, smul_eq_mul, div_mul_eq_mul_div, div_eq_iff hd]
    linear_combination (-(z.im)) * hco

/-- **The derivative of the disk coordinate at a seam point lies on the tangent line of the unit
circle.** -/
lemma pairInc_range_fderiv_boxZ_le_span_I {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (hn : ¬ openSquare y) :
    (fderiv ℝ boxZ y).toLinearMap.range ≤
      Submodule.span ℝ ({Complex.I * boxZ y} : Set ℂ) := by
  rintro w ⟨v, rfl⟩
  refine pairInc_mem_span_I_of_inner_eq_zero
    (norm_ne_zero_iff.mp (by rw [boxZ_norm_eq_one hy hn]; norm_num))
    (pairInc_inner_fderiv_eq_zero hy hn v)


/-! ### The complex coordinates of `ℂ² ≅ ℝ⁴` -/

lemma pairInc_ofComplex_zero_eq_smul (w : ℂ) :
    ofComplex w 0 = w.re • linE0 + w.im • linE1 := by
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i <;>
    simp [ofComplex, linE0, linE1, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]

lemma pairInc_ofComplex_zero_mem_span (w : ℂ) :
    ofComplex w 0 ∈ Submodule.span ℝ ({linE0, linE1} : Set (Eucl 3)) := by
  rw [pairInc_ofComplex_zero_eq_smul]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- On the unit circle the disk lift `linVecC` is the vector `(z, 0)`. -/
lemma pairInc_linVecC_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : linVecC z = ofComplex z 0 := by
  rw [linVecC, hz]
  norm_num

/-- The derivative of the disk lift in the direction `I * z`: it is the vector `(I * z, 0)`. -/
lemma pairInc_fderiv_linVecC_I_mul (z : ℂ) :
    fderiv ℝ linVecC z (Complex.I * z) = ofComplex (Complex.I * z) 0 := by
  have hinner : inner ℝ z (Complex.I * z) = 0 := by
    simp [Complex.inner, Complex.I_mul_re, Complex.I_mul_im]
    ring
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i
  · show ((fderiv ℝ linVecC z) (Complex.I * z)).ofLp 0 = (ofComplex (Complex.I * z) 0).ofLp 0
    rw [LinChart.fderiv_linVecC_coord0, ofComplex, WithLp.ofLp_toLp]
    simp
  · show ((fderiv ℝ linVecC z) (Complex.I * z)).ofLp 1 = (ofComplex (Complex.I * z) 0).ofLp 1
    rw [LinChart.fderiv_linVecC_coord1, ofComplex, WithLp.ofLp_toLp]
    simp
  · show ((fderiv ℝ linVecC z) (Complex.I * z)).ofLp 2 = (ofComplex (Complex.I * z) 0).ofLp 2
    rw [LinChart.fderiv_linVecC_coord2, hinner, ofComplex, WithLp.ofLp_toLp]
    simp
  · show ((fderiv ℝ linVecC z) (Complex.I * z)).ofLp 3 = (ofComplex (Complex.I * z) 0).ofLp 3
    rw [LinChart.fderiv_linVecC_coord3, ofComplex, WithLp.ofLp_toLp]
    simp

/-- **The linear-combination identity for the basis vector `e₀`.** -/
lemma pairInc_smul_linE0_eq (z : ℂ) :
    (z.re * z.re + z.im * z.im) • linE0
      = z.re • ofComplex z 0 - z.im • ofComplex (Complex.I * z) 0 := by
  rw [pairInc_ofComplex_zero_eq_smul z, pairInc_ofComplex_zero_eq_smul (Complex.I * z),
    Complex.I_mul_re, Complex.I_mul_im]
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i <;>
    simp [linE0, linE1, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply,
      smul_eq_mul] <;>
    ring

/-- **The linear-combination identity for the basis vector `e₁`.** -/
lemma pairInc_smul_linE1_eq (z : ℂ) :
    (z.re * z.re + z.im * z.im) • linE1
      = z.im • ofComplex z 0 + z.re • ofComplex (Complex.I * z) 0 := by
  rw [pairInc_ofComplex_zero_eq_smul z, pairInc_ofComplex_zero_eq_smul (Complex.I * z),
    Complex.I_mul_re, Complex.I_mul_im]
  refine WithLp.ofLp_injective 2 ?_
  funext i
  fin_cases i <;>
    simp [linE0, linE1, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply,
      smul_eq_mul] <;>
    ring

/-- The lift is the composite `φ ∘ linVecC ∘ boxZ` (definitional unfolding). -/
lemma pairInc_linPlaneLift_eq (φ : Eucl 3 ≃L[ℝ] Eucl 3) (y : EuclideanSpace ℝ (Fin 2)) :
    linPlaneLift φ y = φ (linVecC (boxZ y)) := rfl

/-! ### The chain rule for the lift of a linear plane chart -/

lemma pairInc_fderiv_linPlaneLift (φ : Eucl 3 ≃L[ℝ] Eucl 3)
    (y : EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (linPlaneLift φ) y
      = ((φ : Eucl 3 →L[ℝ] Eucl 3).comp (fderiv ℝ linVecC (boxZ y))).comp
          (fderiv ℝ boxZ y) := by
  have h1 : HasFDerivAt (fun z : ℂ => φ (linVecC z))
      ((φ : Eucl 3 →L[ℝ] Eucl 3).comp (fderiv ℝ linVecC (boxZ y))) (boxZ y) :=
    (φ : Eucl 3 →L[ℝ] Eucl 3).hasFDerivAt.comp (boxZ y)
      ((linVecC_contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have h2 := h1.comp y (boxZ_hasFDerivAt y)
  exact h2.fderiv

lemma pairInc_range_fderiv_linPlaneLift (φ : Eucl 3 ≃L[ℝ] Eucl 3)
    (y : EuclideanSpace ℝ (Fin 2)) :
    LinearMap.range (fderiv ℝ (linPlaneLift φ) y).toLinearMap
      = Submodule.map (φ : Eucl 3 →L[ℝ] Eucl 3).toLinearMap
          (Submodule.map (fderiv ℝ linVecC (boxZ y)).toLinearMap
            (LinearMap.range (fderiv ℝ boxZ y).toLinearMap)) := by
  rw [pairInc_fderiv_linPlaneLift]
  rw [show (((φ : Eucl 3 →L[ℝ] Eucl 3).comp (fderiv ℝ linVecC (boxZ y))).comp
        (fderiv ℝ boxZ y)).toLinearMap
      = ((φ : Eucl 3 →L[ℝ] Eucl 3).toLinearMap.comp
          (fderiv ℝ linVecC (boxZ y)).toLinearMap).comp (fderiv ℝ boxZ y).toLinearMap from rfl]
  rw [LinearMap.range_comp, Submodule.map_comp]

/-- The disk coordinate is a submersion on the open square. -/
lemma pairInc_range_fderiv_boxZ_eq_top {y : EuclideanSpace ℝ (Fin 2)} (hy : openSquare y) :
    LinearMap.range (fderiv ℝ boxZ y).toLinearMap = ⊤ := by
  have hinj : Function.Injective (fderiv ℝ boxZ y).toLinearMap :=
    injective_fderiv_sqDisk_foldBox y hy.1 hy.2
  have hker : LinearMap.ker (fderiv ℝ boxZ y).toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ boxZ y).toLinearMap
  rw [hker, finrank_bot, add_zero] at h
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [h, Complex.finrank_real_complex]
  simp

/-- **The tangent space of the disk lift.**  The range of the derivative of `linVecC` together with
its value span the standard plane `linStd`. -/
lemma pairInc_range_fderiv_linVecC_sup (z : ℂ) :
    LinearMap.range (fderiv ℝ linVecC z).toLinearMap
      ⊔ Submodule.span ℝ ({linVecC z} : Set (Eucl 3)) = linStd := by
  have hinj : Function.Injective (fderiv ℝ linVecC z).toLinearMap := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have hw' : (fderiv ℝ linVecC z) w = 0 := hw
    have h0 : (fderiv ℝ linVecC z w).ofLp 0 = 0 := by rw [hw']; rfl
    have h1 : (fderiv ℝ linVecC z w).ofLp 1 = 0 := by rw [hw']; rfl
    rw [LinChart.fderiv_linVecC_coord0] at h0
    rw [LinChart.fderiv_linVecC_coord1] at h1
    exact Complex.ext h0 h1
  have hnot : linVecC z ∉ LinearMap.range (fderiv ℝ linVecC z).toLinearMap := by
    rintro ⟨χ, hχ⟩
    have h0 : χ = 0 := LinChart.linVecC_fderiv_span_eq_zero (z := z) (χ := χ) (lam := 1)
      (by simpa using hχ)
    rw [h0, map_zero] at hχ
    exact linVecC_ne_zero z hχ.symm
  have hinf : LinearMap.range (fderiv ℝ linVecC z).toLinearMap
      ⊓ Submodule.span ℝ ({linVecC z} : Set (Eucl 3)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro w ⟨hw1, hw2⟩
    have hw2' : w ∈ Submodule.span ℝ ({linVecC z} : Set (Eucl 3)) := hw2
    rw [Submodule.mem_span_singleton] at hw2'
    obtain ⟨a, rfl⟩ := hw2'
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · refine absurd ?_ hnot
      obtain ⟨χ, hχ⟩ := LinearMap.mem_range.mp hw1
      exact ⟨a⁻¹ • χ, by rw [map_smul, hχ, smul_smul, inv_mul_cancel₀ ha, one_smul]⟩
  have hle : LinearMap.range (fderiv ℝ linVecC z).toLinearMap
      ⊔ Submodule.span ℝ ({linVecC z} : Set (Eucl 3)) ≤ linStd := by
    refine sup_le ?_ ?_
    · rintro w ⟨χ, rfl⟩
      rw [linStd_eq_kerProj]
      simpa using LinChart.fderiv_linVecC_coord3 z χ
    · exact Submodule.span_singleton_le_iff_mem _ _ |>.mpr (linVecC_mem_linStd z)
  have hker : Module.finrank ℝ ↥(LinearMap.ker (fderiv ℝ linVecC z).toLinearMap) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot]
  have hfr : Module.finrank ℝ ↥(LinearMap.range (fderiv ℝ linVecC z).toLinearMap) = 2 := by
    have h := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ linVecC z).toLinearMap
    rw [hker, add_zero] at h
    rw [h, Complex.finrank_real_complex]
  have hsup' : Module.finrank ℝ ↥(LinearMap.range (fderiv ℝ linVecC z).toLinearMap
      ⊔ Submodule.span ℝ ({linVecC z} : Set (Eucl 3))) = 3 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range (fderiv ℝ linVecC z).toLinearMap)
      (Submodule.span ℝ ({linVecC z} : Set (Eucl 3)))
    rw [hinf, finrank_bot, add_zero, hfr, finrank_span_singleton (linVecC_ne_zero z)] at h
    omega
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [hsup', linStd_finrank]


/-! ### The tangent `2`-plane of the linear plane chart -/

/-- **The tangent plane of the chart, from the tangent plane of the model.**  If the derivative range
`S` of the lift of `diskPlane (linPlaneChart ·)` together with the value spans `linStd`, then the image
under `φ` together with the image of the value spans `linSub φ`. -/
lemma pairInc_map_sup_span_of_sup_span_eq (φ : Eucl 3 ≃L[ℝ] Eucl 3) (S : Submodule ℝ (Eucl 3))
    (v : Eucl 3) (h : S ⊔ Submodule.span ℝ ({v} : Set (Eucl 3)) = linStd) :
    Submodule.map (φ : Eucl 3 →L[ℝ] Eucl 3).toLinearMap S
      ⊔ Submodule.span ℝ ({φ v} : Set (Eucl 3)) = linSub φ := by
  have hgoal : Submodule.map (φ : Eucl 3 →L[ℝ] Eucl 3).toLinearMap S
      ⊔ Submodule.map (φ : Eucl 3 →L[ℝ] Eucl 3).toLinearMap
          (Submodule.span ℝ ({v} : Set (Eucl 3))) = linSub φ := by
    rw [← Submodule.map_sup, h]
    rfl
  rwa [Submodule.map_span, Set.image_singleton] at hgoal

/-- **The tangent plane of the chart at an interior parameter**: the derivative range together with
the value spans `linSub φ`. -/
lemma pairInc_interior_range {φ : Eucl 3 ≃L[ℝ] Eucl 3} {y : EuclideanSpace ℝ (Fin 2)}
    (hy : openSquare y) :
    LinearMap.range (fderiv ℝ (linPlaneLift φ) y).toLinearMap
      ⊔ Submodule.span ℝ ({linPlaneLift φ y} : Set (Eucl 3)) = linSub φ := by
  rw [pairInc_range_fderiv_linPlaneLift, pairInc_range_fderiv_boxZ_eq_top hy, Submodule.map_top]
  exact pairInc_map_sup_span_of_sup_span_eq φ _ _ (pairInc_range_fderiv_linVecC_sup (boxZ y))

/-! ### The fold curve of the chart -/

/-- **The value of the lift at a seam parameter lies on the fold line `linBdry φ`**: the disk parameter
is on the unit circle, where `linVecC z = (z, 0)` spans the standard boundary line. -/
lemma pairInc_linPlaneLift_mem_linBdry (φ : Eucl 3 ≃L[ℝ] Eucl 3)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1) (hn : ¬ openSquare y) :
    linPlaneLift φ y ∈ linBdry φ := by
  rw [linBdry, Submodule.mem_map]
  refine ⟨linVecC (boxZ y), ?_, rfl⟩
  rw [pairInc_linVecC_of_norm_eq_one (boxZ_norm_eq_one hy hn)]
  exact pairInc_ofComplex_zero_mem_span _

/-- **At a seam parameter the derivative of the lift lies in the fold line**: the derivative of the
disk coordinate is tangent to the unit circle there, and the tangent direction of the model is
`(I * z, 0)`, whose span is the boundary line. -/
lemma pairInc_range_fderiv_linPlaneLift_le_linBdry (φ : Eucl 3 ≃L[ℝ] Eucl 3)
    {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1) (hn : ¬ openSquare y) :
    LinearMap.range (fderiv ℝ (linPlaneLift φ) y).toLinearMap ≤ linBdry φ := by
  rw [pairInc_range_fderiv_linPlaneLift, linBdry]
  refine Submodule.map_mono ?_
  refine (Submodule.map_mono (pairInc_range_fderiv_boxZ_le_span_I hy hn)).trans ?_
  rw [Submodule.map_span, Set.image_singleton]
  have hX : (fderiv ℝ linVecC (boxZ y)).toLinearMap (Complex.I * boxZ y)
      = ofComplex (Complex.I * boxZ y) 0 := pairInc_fderiv_linVecC_I_mul (boxZ y)
  rw [hX]
  exact (Submodule.span_singleton_le_iff_mem _ _).mpr (pairInc_ofComplex_zero_mem_span _)

/-- **Two values of the model at a non-zero disk parameter, both landing in `linSub Ψ` under `Φ`,
force `linBdry Φ ≤ linSub Ψ`.**  The two vectors `(z, 0)` and `(I z, 0)` span the boundary line of
the model whenever `z ≠ 0`. -/
lemma pairInc_linBdry_le_of_ofComplex_mem {Φ Ψ : Eucl 3 ≃L[ℝ] Eucl 3} {z : ℂ} (hz : z ≠ 0)
    (h1 : Φ (ofComplex z 0) ∈ linSub Ψ) (h2 : Φ (ofComplex (Complex.I * z) 0) ∈ linSub Ψ) :
    linBdry Φ ≤ linSub Ψ := by
  have hd : z.re * z.re + z.im * z.im ≠ 0 := by
    have hpos := Complex.normSq_pos.mpr hz
    rw [Complex.normSq_apply] at hpos
    exact ne_of_gt hpos
  have hgen : Submodule.span ℝ ({ofComplex z 0, ofComplex (Complex.I * z) 0} : Set (Eucl 3))
      ≤ Submodule.comap (Φ : Eucl 3 →L[ℝ] Eucl 3).toLinearMap (linSub Ψ) := by
    rw [Submodule.span_le]
    rintro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact h1
    · exact h2
  rw [linBdry, Submodule.map_le_iff_le_comap]
  refine (Submodule.span_le.mpr ?_).trans hgen
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · have hmem : (z.re * z.re + z.im * z.im) • linE0 ∈
        Submodule.span ℝ ({ofComplex z 0, ofComplex (Complex.I * z) 0} : Set (Eucl 3)) := by
      rw [pairInc_smul_linE0_eq z]
      exact Submodule.sub_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hsplit : linE0 = (z.re * z.re + z.im * z.im)⁻¹
        • ((z.re * z.re + z.im * z.im) • linE0) := by
      rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [hsplit]
    exact Submodule.smul_mem _ _ hmem
  · have hmem : (z.re * z.re + z.im * z.im) • linE1 ∈
        Submodule.span ℝ ({ofComplex z 0, ofComplex (Complex.I * z) 0} : Set (Eucl 3)) := by
      rw [pairInc_smul_linE1_eq z]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hsplit : linE1 = (z.re * z.re + z.im * z.im)⁻¹
        • ((z.re * z.re + z.im * z.im) • linE1) := by
      rw [smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [hsplit]
    exact Submodule.smul_mem _ _ hmem

/-! ### The collapsing of a `3`-plane and a kernel -/

/-- **A subspace whose derivative range does not lie in a hyperplane spans together with it.** -/
lemma pairInc_sup_ker_eq_top {ℓ : Eucl 3 →ₗ[ℝ] ℝ} {S : Submodule ℝ (Eucl 3)}
    (h : ∃ s ∈ S, ℓ s ≠ 0) : S ⊔ ℓ.ker = ⊤ := by
  obtain ⟨s, hs, hℓs⟩ := h
  rw [Submodule.eq_top_iff']
  intro w
  have hmem : w - (ℓ w / ℓ s) • s ∈ ℓ.ker := by
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  have h2 : w = (w - (ℓ w / ℓ s) • s) + (ℓ w / ℓ s) • s := by abel
  rw [h2]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hmem)
    (Submodule.smul_mem _ _ (Submodule.mem_sup_left hs))

/-- The kernel of the normal functional of a linear chart is the plane of the chart. -/
lemma pairInc_ker_linFun (φ : Eucl 3 ≃L[ℝ] Eucl 3) : (linFun φ).ker = linSub φ := by
  ext v
  rw [LinearMap.mem_ker, linFun_apply, linSub, Submodule.mem_map]
  constructor
  · intro hv
    exact ⟨φ.symm v, by rw [linStd_eq_kerProj]; exact hv, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    rw [linStd_eq_kerProj] at hw
    simpa using hw

/-- The normal functional of a linear chart is non-zero. -/
lemma pairInc_linFun_ne_zero (φ : Eucl 3 ≃L[ℝ] Eucl 3) : linFun φ ≠ 0 := by
  intro h
  have h2 := congrArg (fun (f : Eucl 3 →ₗ[ℝ] ℝ) => f (φ (EuclideanSpace.single 3 (1 : ℝ)))) h
  simp [linFun_apply] at h2

/-- The finrank of the plane of a linear chart. -/
lemma pairInc_finrank_linSub (φ : Eucl 3 ≃L[ℝ] Eucl 3) :
    Module.finrank ℝ ↥(linSub φ) = 3 := by
  rw [← pairInc_ker_linFun φ]
  have hrk := Module.Dual.finrank_ker_add_one_of_ne_zero (f := linFun φ) (pairInc_linFun_ne_zero φ)
  have h4 : Module.finrank ℝ (Eucl 3) = 4 := by simp
  omega

/-- **Two distinct linear planes span `ℝ⁴`.** -/
lemma pairInc_linSub_sup_eq_top {Φ₀ Φ₁ : Eucl 3 ≃L[ℝ] Eucl 3} (hne : linSub Φ₀ ≠ linSub Φ₁) :
    linSub Φ₀ ⊔ linSub Φ₁ = ⊤ := by
  have h4 : Module.finrank ℝ (Eucl 3) = 4 := by simp
  have hlt : Module.finrank ℝ ↥(linSub Φ₀ ⊓ linSub Φ₁) < 3 := by
    by_contra hcon
    push Not at hcon
    have hle0 : Module.finrank ℝ ↥(linSub Φ₀ ⊓ linSub Φ₁) ≤ 3 :=
      (Submodule.finrank_mono inf_le_left).trans (le_of_eq (pairInc_finrank_linSub Φ₀))
    have hfr : Module.finrank ℝ ↥(linSub Φ₀ ⊓ linSub Φ₁) = 3 := le_antisymm hle0 hcon
    have e0 : linSub Φ₀ ⊓ linSub Φ₁ = linSub Φ₀ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hfr, pairInc_finrank_linSub Φ₀])
    have e1 : linSub Φ₀ ⊓ linSub Φ₁ = linSub Φ₁ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hfr, pairInc_finrank_linSub Φ₁])
    exact hne (e0.symm.trans e1)
  have h := Submodule.finrank_sup_add_finrank_inf_eq (linSub Φ₀) (linSub Φ₁)
  rw [pairInc_finrank_linSub Φ₀, pairInc_finrank_linSub Φ₁] at h
  have hle : Module.finrank ℝ ↥(linSub Φ₀ ⊔ linSub Φ₁) ≤ 4 := by
    simpa [h4] using Submodule.finrank_le (linSub Φ₀ ⊔ linSub Φ₁)
  have hsup : Module.finrank ℝ ↥(linSub Φ₀ ⊔ linSub Φ₁) = 4 := by omega
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hsup, h4]

/-- **The range of the projective quotient of `ℝ⁴` is all of `ℝ³`.** -/
lemma pairInc_range_projCoordFunDerivE_eq_top {i : Fin 4} {v : Eucl 3} (hv : v.ofLp i ≠ 0) :
    LinearMap.range (projCoordFunDerivE i v).toLinearMap = ⊤ := by
  have hker : LinearMap.ker (projCoordFunDerivE i v).toLinearMap
      = Submodule.span ℝ ({v} : Set (Eucl 3)) := by
    ext w
    rw [LinearMap.mem_ker]
    exact projCoordFunDerivE_eq_zero_iff hv w
  have hv0 : v ≠ 0 := fun h => hv (by rw [h]; rfl)
  have h := LinearMap.finrank_range_add_finrank_ker (projCoordFunDerivE i v).toLinearMap
  rw [hker, finrank_span_singleton hv0] at h
  refine Submodule.eq_top_of_finrank_eq ?_
  have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have h4 : Module.finrank ℝ (Eucl 3) = 4 := by simp
  omega


/-! ### The spanning of the two tangent planes

The case analysis: at a common value the derivative ranges of the two charts span the tangent space,
unless one of the forbidden incidences (fold–fold, corner–plane) occurs. -/

lemma pairInc_span_smul_eq {t : ℝ} (ht : t ≠ 0) (v : Eucl 3) :
    Submodule.span ℝ ({t • v} : Set (Eucl 3)) = Submodule.span ℝ ({v} : Set (Eucl 3)) := by
  have key : ∀ a : ℝ, a ≠ 0 → ∀ w : Eucl 3,
      Submodule.span ℝ ({a • w} : Set (Eucl 3)) ≤ Submodule.span ℝ ({w} : Set (Eucl 3)) := by
    intro a ha w
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.smul_mem (Submodule.span ℝ ({w} : Set (Eucl 3))) a
      (Submodule.mem_span_singleton_self w)
  refine le_antisymm (key t ht v) ?_
  have h2 := key t⁻¹ (inv_ne_zero ht) (t • v)
  rwa [show t⁻¹ • (t • v) = v from by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]] at h2

/-- At a seam point where the disk coordinate is not constant, its range is the tangent line. -/
lemma pairInc_range_fderiv_boxZ_eq_span_I {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (hn : ¬ openSquare y)
    (hne : LinearMap.range (fderiv ℝ boxZ y).toLinearMap ≠ ⊥) :
    LinearMap.range (fderiv ℝ boxZ y).toLinearMap
      = Submodule.span ℝ ({Complex.I * boxZ y} : Set ℂ) := by
  refine le_antisymm (pairInc_range_fderiv_boxZ_le_span_I hy hn) ?_
  rw [Submodule.span_singleton_le_iff_mem]
  by_contra hmem
  refine hne ?_
  rw [Submodule.eq_bot_iff]
  intro w hw
  by_contra hw0
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (pairInc_range_fderiv_boxZ_le_span_I hy hn hw)
  have ha0 : a ≠ 0 := fun h => hw0 (by rw [← ha, h, zero_smul])
  have hI : Complex.I * boxZ y = a⁻¹ • w := by
    rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  exact hmem (hI ▸ Submodule.smul_mem _ _ hw)

/-- A linear map with zero range is zero. -/
lemma pairInc_eq_zero_of_range_eq_bot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E →L[ℝ] F}
    (h : f.toLinearMap.range = ⊥) : f = 0 := by
  ext v
  have h2 := congrArg (fun (g : E →ₗ[ℝ] F) => g v) (LinearMap.range_eq_bot.mp h)
  simpa using h2

/-- The differential of the disk lift is injective (its first two coordinates are the argument). -/
lemma pairInc_fderiv_linVecC_injective (z : ℂ) : Function.Injective (fderiv ℝ linVecC z) := by
  intro a b hab
  have h0 : (fderiv ℝ linVecC z (a - b)).ofLp 0 = 0 := by rw [map_sub, hab, sub_self]; rfl
  have h1 : (fderiv ℝ linVecC z (a - b)).ofLp 1 = 0 := by rw [map_sub, hab, sub_self]; rfl
  rw [LinChart.fderiv_linVecC_coord0] at h0
  rw [LinChart.fderiv_linVecC_coord1] at h1
  exact sub_eq_zero.mp (Complex.ext h0 h1)

/-- **If the chain of differentials of the folded disk coordinate has zero range, the disk
coordinate is critical.** -/
lemma pairInc_boxZ_eq_zero_of_range_eq_bot (φ : Eucl 3 ≃L[ℝ] Eucl 3)
    (y : EuclideanSpace ℝ (Fin 2))
    (h : Submodule.map φ.toLinearMap
        (Submodule.map (fderiv ℝ linVecC (boxZ y)).toLinearMap
          (LinearMap.range (fderiv ℝ boxZ y).toLinearMap)) = ⊥) :
    fderiv ℝ boxZ y = 0 := by
  have hinj := pairInc_fderiv_linVecC_injective (boxZ y)
  have h1 : ∀ v ∈ LinearMap.range (fderiv ℝ boxZ y).toLinearMap,
      (fderiv ℝ linVecC (boxZ y)).toLinearMap v = 0 := by
    intro v hv
    have hmem : φ ((fderiv ℝ linVecC (boxZ y)).toLinearMap v) ∈
        Submodule.map φ.toLinearMap (Submodule.map (fderiv ℝ linVecC (boxZ y)).toLinearMap
          (LinearMap.range (fderiv ℝ boxZ y).toLinearMap)) :=
      ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact φ.injective (by rw [Submodule.eq_bot_iff _ |>.mp h _ hmem, map_zero])
  have h2 : LinearMap.range (fderiv ℝ boxZ y).toLinearMap = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hv0 : (fderiv ℝ linVecC (boxZ y)) v = 0 := h1 v hv
    exact hinj (by rw [hv0, map_zero])
  exact pairInc_eq_zero_of_range_eq_bot h2

/-- **At a critical point of the disk coordinate on the seam, the value is a corner value.** -/
lemma pairInc_corner_of_fderiv_eq_zero {y : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (hn : ¬ openSquare y) (h0 : fderiv ℝ boxZ y = 0) :
    ∃ (c s : ℝ), c ≠ 0 ∧ (s = 1 ∨ s = -1) ∧
      linVecC (boxZ y) = c • (linE0 + s • linE1) := by
  have hboth : ∀ j : Fin 2, y j = 0 ∨ y j = 1 := by
    intro j
    by_contra hj
    push Not at hj
    have hIoo := pairInc_mem_Ioo_of_not_eq_zero_one hy j hj.1 hj.2
    have hne := sqDisk_foldBox_fderiv_single_ne_zero y hy (i := j) hIoo
    rw [show (fun z : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox z)) = boxZ from rfl, h0] at hne
    exact hne rfl
  exact sqDisk_foldBox_corner y (hboth 0) (hboth 1)

lemma pairInc_sup_eq_top (Φ₀ Φ₁ : Eucl 3 ≃L[ℝ] Eucl 3) {y y' : EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ Submission.Drive.unitBox 1) (hy' : y' ∈ Submission.Drive.unitBox 1)
    {t : ℝ} (ht : t ≠ 0) (hVt : linPlaneLift Φ₁ y' = t • linPlaneLift Φ₀ y)
    (hl : linBdry Φ₀ ⊓ linBdry Φ₁ = ⊥) (h0 : ¬ linBdry Φ₀ ≤ linSub Φ₁)
    (h1 : ¬ linBdry Φ₁ ≤ linSub Φ₀)
    (hc0 : ∀ s : ℝ, (s = 1 ∨ s = -1) → Φ₀ (linE0 + s • linE1) ∉ linSub Φ₁)
    (hc1 : ∀ s : ℝ, (s = 1 ∨ s = -1) → Φ₁ (linE0 + s • linE1) ∉ linSub Φ₀)
    (hne : linSub Φ₀ ≠ linSub Φ₁) :
    LinearMap.range (fderiv ℝ (linPlaneLift Φ₀) y).toLinearMap
      ⊔ LinearMap.range (fderiv ℝ (linPlaneLift Φ₁) y').toLinearMap
      ⊔ Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3)) = ⊤ := by
  -- the value of the second lift lies in the second plane, hence so does the first
  have hu_mem : linPlaneLift Φ₀ y ∈ linSub Φ₁ := by
    have h := linPlaneLift_mem_linSub Φ₁ y'
    rw [hVt] at h
    have h2 := Submodule.smul_mem (linSub Φ₁) t⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at h2
  by_cases hIy : openSquare y
  · by_cases hIy' : openSquare y'
    · -- (I) both parameters interior
      have hS₀ := pairInc_interior_range (φ := Φ₀) hIy
      have hS₁ : LinearMap.range (fderiv ℝ (linPlaneLift Φ₁) y').toLinearMap
          ⊔ Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3)) = linSub Φ₁ := by
        rw [← pairInc_interior_range (φ := Φ₁) hIy', hVt, pairInc_span_smul_eq ht]
      refine le_antisymm le_top ?_
      rw [← pairInc_linSub_sup_eq_top (Φ₀ := Φ₀) (Φ₁ := Φ₁) hne, ← hS₀, ← hS₁]
      exact le_of_eq (by ac_rfl)
    · -- (III) the first parameter is interior, the second folds
      have hz' : boxZ y' ≠ 0 := by
        rw [← norm_ne_zero_iff, boxZ_norm_eq_one hy' hIy']
        norm_num
      have hS₀ : LinearMap.range (fderiv ℝ (linPlaneLift Φ₀) y).toLinearMap
          ⊔ Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3)) = linSub Φ₀ :=
        pairInc_interior_range (φ := Φ₀) hIy
      have hmem_val : Φ₁ (ofComplex (boxZ y') 0) ∈ linSub Φ₀ := by
        have h : linPlaneLift Φ₁ y' ∈ linSub Φ₀ := by
          rw [hVt]
          exact Submodule.smul_mem _ _ (linPlaneLift_mem_linSub Φ₀ y)
        rw [pairInc_linPlaneLift_eq Φ₁ y',
          pairInc_linVecC_of_norm_eq_one (boxZ_norm_eq_one hy' hIy')] at h
        exact h
      by_cases hSbot : LinearMap.range (fderiv ℝ (linPlaneLift Φ₁) y').toLinearMap = ⊥
      · have hlift0 : fderiv ℝ (linPlaneLift Φ₁) y' = 0 :=
          pairInc_eq_zero_of_range_eq_bot hSbot
        have hZ0 : fderiv ℝ boxZ y' = 0 := by
          have h1' : Submodule.map (Φ₁ : Eucl 3 →L[ℝ] Eucl 3).toLinearMap
              (Submodule.map (fderiv ℝ linVecC (boxZ y')).toLinearMap
                (LinearMap.range (fderiv ℝ boxZ y').toLinearMap)) = ⊥ := by
            rw [← pairInc_range_fderiv_linPlaneLift, hlift0]
            simp
          exact pairInc_boxZ_eq_zero_of_range_eq_bot Φ₁ y' h1'
        obtain ⟨cc, ss, hcc, hss, hval⟩ := pairInc_corner_of_fderiv_eq_zero hy' hIy' hZ0
        have hmem : linPlaneLift Φ₁ y' ∈ linSub Φ₀ := by
          rw [hVt]
          exact Submodule.smul_mem _ _ (linPlaneLift_mem_linSub Φ₀ y)
        have hmem2 : cc • Φ₁ (linE0 + ss • linE1) ∈ linSub Φ₀ := by
          have h := hmem
          rw [pairInc_linPlaneLift_eq Φ₁ y', hval, map_smul] at h
          exact h
        have hX : Φ₁ (linE0 + ss • linE1) ∈ linSub Φ₀ := by
          have h := Submodule.smul_mem (linSub Φ₀) cc⁻¹ hmem2
          rwa [smul_smul, inv_mul_cancel₀ hcc, one_smul] at h
        exact absurd hX (hc1 ss hss)
      · have hspan : LinearMap.range (fderiv ℝ (linPlaneLift Φ₁) y').toLinearMap ⊔ linSub Φ₀ = ⊤ := by
          rw [← pairInc_ker_linFun Φ₀]
          refine pairInc_sup_ker_eq_top (ℓ := linFun Φ₀) ?_
          by_contra hcon
          push Not at hcon
          have hmem_der : Φ₁ (ofComplex (Complex.I * boxZ y') 0) ∈ linSub Φ₀ := by
            have hW_eq := pairInc_range_fderiv_boxZ_eq_span_I hy' hIy'
              (fun hWbot => hSbot (by rw [pairInc_range_fderiv_linPlaneLift, hWbot,
                Submodule.map_bot, Submodule.map_bot]))
            have hW : Submodule.span ℝ ({Complex.I * boxZ y'} : Set ℂ) ≤
                LinearMap.range (fderiv ℝ boxZ y').toLinearMap := by
              rw [← hW_eq]
            have hmem : (fderiv ℝ linVecC (boxZ y')).toLinearMap (Complex.I * boxZ y')
                ∈ Submodule.map (fderiv ℝ linVecC (boxZ y')).toLinearMap
                    (LinearMap.range (fderiv ℝ boxZ y').toLinearMap) :=
              ⟨Complex.I * boxZ y', hW (Submodule.mem_span_singleton_self _), rfl⟩
            have hmem₂ : Φ₁ ((fderiv ℝ linVecC (boxZ y')).toLinearMap (Complex.I * boxZ y'))
                ∈ LinearMap.range (fderiv ℝ (linPlaneLift Φ₁) y').toLinearMap := by
              rw [pairInc_range_fderiv_linPlaneLift]
              exact ⟨_, hmem, rfl⟩
            have hfin := hcon _ hmem₂
            have hX : (fderiv ℝ linVecC (boxZ y')).toLinearMap (Complex.I * boxZ y')
                = ofComplex (Complex.I * boxZ y') 0 :=
              pairInc_fderiv_linVecC_I_mul (boxZ y')
            rw [hX] at hfin
            have hker : Φ₁ (ofComplex (Complex.I * boxZ y') 0) ∈ (linFun Φ₀).ker :=
              LinearMap.mem_ker.mpr hfin
            rwa [pairInc_ker_linFun Φ₀] at hker
          exact h1 (pairInc_linBdry_le_of_ofComplex_mem hz' hmem_val hmem_der)
        refine le_antisymm le_top ?_
        rw [← hspan, ← hS₀]
        exact le_of_eq (by ac_rfl)
  · by_cases hIy' : openSquare y'
    · -- (II) the first parameter folds, the second is interior
      have hz : boxZ y ≠ 0 := by
        rw [← norm_ne_zero_iff, boxZ_norm_eq_one hy hIy]
        norm_num
      have hS₁ : LinearMap.range (fderiv ℝ (linPlaneLift Φ₁) y').toLinearMap
          ⊔ Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3)) = linSub Φ₁ := by
        rw [← pairInc_interior_range (φ := Φ₁) hIy', hVt, pairInc_span_smul_eq ht]
      have hmem_val : Φ₀ (ofComplex (boxZ y) 0) ∈ linSub Φ₁ := by
        have h := hu_mem
        rw [pairInc_linPlaneLift_eq Φ₀ y,
          pairInc_linVecC_of_norm_eq_one (boxZ_norm_eq_one hy hIy)] at h
        exact h
      by_cases hSbot : LinearMap.range (fderiv ℝ (linPlaneLift Φ₀) y).toLinearMap = ⊥
      · have hlift0 : fderiv ℝ (linPlaneLift Φ₀) y = 0 :=
          pairInc_eq_zero_of_range_eq_bot hSbot
        have hZ0 : fderiv ℝ boxZ y = 0 := by
          have h1' : Submodule.map (Φ₀ : Eucl 3 →L[ℝ] Eucl 3).toLinearMap
              (Submodule.map (fderiv ℝ linVecC (boxZ y)).toLinearMap
                (LinearMap.range (fderiv ℝ boxZ y).toLinearMap)) = ⊥ := by
            rw [← pairInc_range_fderiv_linPlaneLift, hlift0]
            simp
          exact pairInc_boxZ_eq_zero_of_range_eq_bot Φ₀ y h1'
        obtain ⟨cc, ss, hcc, hss, hval⟩ := pairInc_corner_of_fderiv_eq_zero hy hIy hZ0
        have hmem2 : cc • Φ₀ (linE0 + ss • linE1) ∈ linSub Φ₁ := by
          have h := hu_mem
          rw [pairInc_linPlaneLift_eq Φ₀ y, hval, map_smul] at h
          exact h
        have hX : Φ₀ (linE0 + ss • linE1) ∈ linSub Φ₁ := by
          have h := Submodule.smul_mem (linSub Φ₁) cc⁻¹ hmem2
          rwa [smul_smul, inv_mul_cancel₀ hcc, one_smul] at h
        exact absurd hX (hc0 ss hss)
      · have hspan : LinearMap.range (fderiv ℝ (linPlaneLift Φ₀) y).toLinearMap ⊔ linSub Φ₁ = ⊤ := by
          rw [← pairInc_ker_linFun Φ₁]
          refine pairInc_sup_ker_eq_top (ℓ := linFun Φ₁) ?_
          by_contra hcon
          push Not at hcon
          have hmem_der : Φ₀ (ofComplex (Complex.I * boxZ y) 0) ∈ linSub Φ₁ := by
            have hW_eq := pairInc_range_fderiv_boxZ_eq_span_I hy hIy
              (fun hWbot => hSbot (by rw [pairInc_range_fderiv_linPlaneLift, hWbot,
                Submodule.map_bot, Submodule.map_bot]))
            have hW : Submodule.span ℝ ({Complex.I * boxZ y} : Set ℂ) ≤
                LinearMap.range (fderiv ℝ boxZ y).toLinearMap := by
              rw [← hW_eq]
            have hmem : (fderiv ℝ linVecC (boxZ y)).toLinearMap (Complex.I * boxZ y)
                ∈ Submodule.map (fderiv ℝ linVecC (boxZ y)).toLinearMap
                    (LinearMap.range (fderiv ℝ boxZ y).toLinearMap) :=
              ⟨Complex.I * boxZ y, hW (Submodule.mem_span_singleton_self _), rfl⟩
            have hmem₂ : Φ₀ ((fderiv ℝ linVecC (boxZ y)).toLinearMap (Complex.I * boxZ y))
                ∈ LinearMap.range (fderiv ℝ (linPlaneLift Φ₀) y).toLinearMap := by
              rw [pairInc_range_fderiv_linPlaneLift]
              exact ⟨_, hmem, rfl⟩
            have hfin := hcon _ hmem₂
            have hX : (fderiv ℝ linVecC (boxZ y)).toLinearMap (Complex.I * boxZ y)
                = ofComplex (Complex.I * boxZ y) 0 :=
              pairInc_fderiv_linVecC_I_mul (boxZ y)
            rw [hX] at hfin
            have hker : Φ₀ (ofComplex (Complex.I * boxZ y) 0) ∈ (linFun Φ₁).ker :=
              LinearMap.mem_ker.mpr hfin
            rwa [pairInc_ker_linFun Φ₁] at hker
          exact h0 (pairInc_linBdry_le_of_ofComplex_mem hz hmem_val hmem_der)
        refine le_antisymm le_top ?_
        rw [← hspan, ← hS₁]
        exact le_of_eq (by ac_rfl)
    · -- (IV) both parameters fold
      have hv₀ : linPlaneLift Φ₀ y ∈ linBdry Φ₀ := pairInc_linPlaneLift_mem_linBdry Φ₀ hy hIy
      have hv₁ : linPlaneLift Φ₁ y' ∈ linBdry Φ₁ := pairInc_linPlaneLift_mem_linBdry Φ₁ hy' hIy'
      have hv₁' : linPlaneLift Φ₀ y ∈ linBdry Φ₁ := by
        have h := hv₁
        rw [hVt] at h
        have h2 := Submodule.smul_mem (linBdry Φ₁) t⁻¹ h
        rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at h2
      have hbot : linPlaneLift Φ₀ y ∈ (⊥ : Submodule ℝ (Eucl 3)) := by
        rw [← hl]
        exact ⟨hv₀, hv₁'⟩
      exact absurd (by simpa using hbot) (linPlaneLift_ne_zero Φ₀ y)

theorem pairReg_linPlaneCharts_of_incidence (Φ₀ Φ₁ : Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3)
    (c : ℝ) (hc : 0 < c)
    (hl : Work.Drive.linBdry Φ₀ ⊓ Work.Drive.linBdry Φ₁ = ⊥)
    (h0 : ¬ Work.Drive.linBdry Φ₀ ≤ Work.Drive.linSub Φ₁)
    (h1 : ¬ Work.Drive.linBdry Φ₁ ≤ Work.Drive.linSub Φ₀)
    (hc0 : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      Φ₀ (Work.Drive.linE0 + s • Work.Drive.linE1) ∉ Work.Drive.linSub Φ₁)
    (hc1 : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      Φ₁ (Work.Drive.linE0 + s • Work.Drive.linE1) ∉ Work.Drive.linSub Φ₀)
    (hne : Work.Drive.linSub Φ₀ ≠ Work.Drive.linSub Φ₁) :
    Work.Drive.PairReg
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart Φ₀ c hc)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart Φ₁ c hc))) := by
  refine pairReg_diskPlane_of_box (linPlaneChart Φ₀ c hc) (linPlaneChart Φ₁ c hc)
    (contMDiff_diskPlane (linPlaneChart_contMDiff Φ₀ c hc))
    (contMDiff_diskPlane (linPlaneChart_contMDiff Φ₁ c hc)) ?_
  intro y y' hy hy' hval
  -- normalise both class maps to the projectivised lifts
  rw [planeClassMap_diskPlane_linPlaneChart_eq Φ₀ c hc,
    planeClassMap_diskPlane_linPlaneChart_eq Φ₁ c hc] at hval ⊢
  -- the two lift values are proportional
  obtain ⟨t, ht, hVt⟩ : ∃ t : ℝ, t ≠ 0 ∧ linPlaneLift Φ₁ y' = t • linPlaneLift Φ₀ y := by
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ (linPlaneLift Φ₀ y) (linPlaneLift Φ₁ y')
      (linPlaneLift_ne_zero Φ₀ y) (linPlaneLift_ne_zero Φ₁ y')).mp hval
    have ha0 : a ≠ 0 := fun h => linPlaneLift_ne_zero Φ₀ y
      (by rw [h, zero_smul] at ha; exact ha.symm)
    refine ⟨a⁻¹, inv_ne_zero ha0, ?_⟩
    rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  have hspan := pairInc_sup_eq_top Φ₀ Φ₁ hy hy' ht hVt hl h0 h1 hc0 hc1 hne
  -- smoothness of the two lifts
  have hV₀sm : ContMDiffAt (𝓡 2) (𝓘(ℝ, Eucl 3)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (linPlaneLift Φ₀) y :=
    contMDiffAt_iff_contDiffAt.mpr (linPlaneLift_contDiff Φ₀).contDiffAt
  have hV₁sm : ContMDiffAt (𝓡 2) (𝓘(ℝ, Eucl 3)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (linPlaneLift Φ₁) y' :=
    contMDiffAt_iff_contDiffAt.mpr (linPlaneLift_contDiff Φ₁).contDiffAt
  -- the range computations for the two class maps
  rw [range_mfderiv_projMk (n := 3) (k := 2) (linPlaneLift Φ₀) (linPlaneLift_ne_zero Φ₀) y hV₀sm,
    range_mfderiv_projMk (n := 3) (k := 2) (linPlaneLift Φ₁) (linPlaneLift_ne_zero Φ₁) y' hV₁sm]
  -- both images are taken under one and the same projective quotient
  have hidx : projChartIndexOf (Projectivization.mk ℝ (linPlaneLift Φ₁ y')
        (linPlaneLift_ne_zero Φ₁ y'))
      = projChartIndexOf (Projectivization.mk ℝ (linPlaneLift Φ₀ y)
        (linPlaneLift_ne_zero Φ₀ y)) :=
    congrArg projChartIndexOf hval.symm
  have hvi : (linPlaneLift Φ₀ y).ofLp (projChartIndexOf (Projectivization.mk ℝ (linPlaneLift Φ₀ y)
      (linPlaneLift_ne_zero Φ₀ y))) ≠ 0 :=
    (mem_projChartSource_iff' (linPlaneLift_ne_zero Φ₀ y)).mp (projChartIndexOf_spec _)
  have hQeq : Submodule.map (projCoordFunDerivE (projChartIndexOf (Projectivization.mk ℝ
        (linPlaneLift Φ₁ y') (linPlaneLift_ne_zero Φ₁ y'))) (linPlaneLift Φ₁ y')).toLinearMap
      (LinearMap.range (fderiv ℝ (linPlaneLift Φ₁) y').toLinearMap)
      = Submodule.map (projCoordFunDerivE (projChartIndexOf (Projectivization.mk ℝ
        (linPlaneLift Φ₀ y) (linPlaneLift_ne_zero Φ₀ y))) (linPlaneLift Φ₀ y)).toLinearMap
      (LinearMap.range (fderiv ℝ (linPlaneLift Φ₁) y').toLinearMap) := by
    rw [hidx, hVt, map_projCoordFunDerivE_smul _ _ ht]
  rw [hQeq]
  set F : Eucl 3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) := (projCoordFunDerivE (projChartIndexOf
      (Projectivization.mk ℝ (linPlaneLift Φ₀ y) (linPlaneLift_ne_zero Φ₀ y)))
      (linPlaneLift Φ₀ y)).toLinearMap with hF
  set S₀ : Submodule ℝ (Eucl 3) := LinearMap.range (fderiv ℝ (linPlaneLift Φ₀) y).toLinearMap
    with hS₀
  set S₁ : Submodule ℝ (Eucl 3) := LinearMap.range (fderiv ℝ (linPlaneLift Φ₁) y').toLinearMap
    with hS₁
  have hker : LinearMap.ker F = Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3)) := by
    rw [hF]
    ext w
    rw [LinearMap.mem_ker]
    exact projCoordFunDerivE_eq_zero_iff hvi w
  have hmapbot : Submodule.map F (Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3))) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro w ⟨v, hv, rfl⟩
    rw [← hker] at hv
    exact LinearMap.mem_ker.mp hv
  have hspan' : S₀ ⊔ S₁ ⊔ Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3)) = ⊤ := by
    rw [hS₀, hS₁]
    exact hspan
  have hmain : Submodule.map F (S₀ ⊔ S₁) = ⊤ := by
    have hstep : Submodule.map F (S₀ ⊔ S₁ ⊔ Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3)))
        = Submodule.map F (S₀ ⊔ S₁) := by
      calc Submodule.map F (S₀ ⊔ S₁ ⊔ Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3)))
          = Submodule.map F (S₀ ⊔ S₁)
            ⊔ Submodule.map F (Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3))) :=
            Submodule.map_sup (S₀ ⊔ S₁) (Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3))) F
        _ = Submodule.map F (S₀ ⊔ S₁) ⊔ ⊥ := by rw [hmapbot]
        _ = Submodule.map F (S₀ ⊔ S₁) := by rw [sup_bot_eq]
    calc Submodule.map F (S₀ ⊔ S₁)
        = Submodule.map F (S₀ ⊔ S₁ ⊔ Submodule.span ℝ ({linPlaneLift Φ₀ y} : Set (Eucl 3))) :=
          hstep.symm
      _ = Submodule.map F ⊤ := by rw [hspan']
      _ = ⊤ := by
          rw [Submodule.map_top, hF]
          exact pairInc_range_projCoordFunDerivE_eq_top hvi
  exact (Submodule.map_sup S₀ S₁ F).symm.trans hmain

end Work.Drive
