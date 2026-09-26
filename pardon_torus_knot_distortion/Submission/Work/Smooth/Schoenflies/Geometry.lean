import Submission.Work.Smooth.Schoenflies.ChordDefs

/-!
# The chord geometry of the unit disc: the main lemmas

Companion of `ChordDefs.lean`: the facts about the chord, the caps and the arcs that the
boundary-correspondence argument (`Work.Smooth.Schoenflies.Injectivity`) needs.

* `det`, `dot`, `lagrange`, `norm_segPoint_sq`, `dot_lt_one`, `abs_det_sub_lt_norm` — the
  elementary metric algebra of the unit disc;
* `chord_eq_seg` — the chord is the closed segment between its endpoints;
* `seg_diff_subset_ball` — the open chord lies in the open disc;
* `chord_inter_circle` — the chord meets the circle exactly in its endpoints;
* `arcPos_nonempty`, `arcNeg_nonempty` — both arcs are non-empty (with explicit witnesses);
* `circle_eq_arcPos_union_arcNeg` — the circle is the union of the two arcs and the two endpoints;
* `arcPos_subset_closure_capPos`, `arcNeg_subset_closure_capNeg` — each arc lies in the closure of
  the cap on the same side.  This is what pushes a boundary value of a Carathéodory extension into
  the closure of the image of a cap.
-/

open Set Metric
open scoped Topology ComplexConjugate

namespace Work.Smooth.Schoenflies

noncomputable section

def dot (x y : ℂ) : ℝ := x.re * y.re + x.im * y.im

theorem dot_eq_conj_mul_re (x y : ℂ) : dot x y = (conj x * y).re := by
  rw [dot, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem dot_le_norm (x y : ℂ) : dot x y ≤ ‖x‖ * ‖y‖ := by
  calc dot x y = (conj x * y).re := dot_eq_conj_mul_re x y
    _ ≤ ‖conj x * y‖ := Complex.re_le_norm _
    _ = ‖x‖ * ‖y‖ := by rw [norm_mul, Complex.norm_conj]

theorem dot_comm (x y : ℂ) : dot x y = dot y x := by
  rw [dot, dot]; ring

theorem dot_self (x : ℂ) : dot x x = ‖x‖ ^ 2 := by
  rw [dot, Complex.sq_norm, Complex.normSq_apply]

theorem lagrange (x y : ℂ) : det x y ^ 2 + dot x y ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [det_apply, dot, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  ring

theorem det_sub_left (a b c : ℂ) : det (a - b) c = det a c - det b c := by
  rw [det_apply, det_apply, det_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

theorem det_sub_self (x y : ℂ) : det (y - x) x = det y x := by
  rw [det_sub_left, det_self, sub_zero]

theorem det_I_mul_self (a : ℂ) : det a (Complex.I * a) = ‖a‖ ^ 2 := by
  rw [det_apply, Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring

theorem exists_smul_of_det_eq_zero {a w : ℂ} (h : det a w = 0) (ha : a ≠ 0) :
    ∃ s : ℝ, w = s • a := by
  refine ⟨(w / a).re, ?_⟩
  have him : (w / a).im = 0 := by
    have h1 : (w / a).im = det a w / Complex.normSq a := by
      rw [Complex.div_im, det_apply]; ring
    rw [h1, h, zero_div]
  have hw : w / a = (((w / a).re : ℝ) : ℂ) := by
    refine Complex.ext rfl ?_
    simp [him]
  rw [Complex.real_smul, ← hw, div_mul_cancel₀ w ha]

theorem norm_segPoint_sq (x y : ℂ) (s : ℝ) :
    ‖segPoint s x y‖ ^ 2
      = (1 - s) ^ 2 * ‖x‖ ^ 2 + 2 * (1 - s) * s * dot x y + s ^ 2 * ‖y‖ ^ 2 := by
  simp only [segPoint, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, dot]
  ring

theorem norm_segPoint_sq_of_unit {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (s : ℝ) :
    ‖segPoint s x y‖ ^ 2 = 1 - 2 * s * (1 - s) * (1 - dot x y) := by
  rw [norm_segPoint_sq, hx, hy]; ring

theorem norm_add_sq (u v : ℂ) : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + 2 * dot u v + ‖v‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, dot]
  ring

theorem dot_lt_one {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) :
    dot x y < 1 := by
  rcases lt_or_eq_of_le (dot_le_norm x y) with h | h
  · rwa [hx, hy, mul_one] at h
  · exfalso
    have h1 : dot x y = 1 := by rw [h, hx, hy, mul_one]
    have hnorm : ‖conj x * y‖ = 1 := by rw [norm_mul, Complex.norm_conj, hx, hy, one_mul]
    have hre : (conj x * y).re = 1 := by rw [← dot_eq_conj_mul_re, h1]
    have him : (conj x * y).im = 0 := by
      have h2 := Complex.sq_norm (conj x * y)
      rw [hnorm, Complex.normSq_apply] at h2
      nlinarith [h2, hre]
    have hone : conj x * y = 1 := by
      refine Complex.ext hre ?_
      simpa using him
    have hxx : conj x * x = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, hx]
      norm_num
    have hyx : y = x := by
      calc y = (conj x * x) * y := by rw [hxx, one_mul]
        _ = x * (conj x * y) := by ring
        _ = x * 1 := by rw [hone]
        _ = x := mul_one x
    exact hxy hyx.symm

/-- **Strict Cauchy–Schwarz for `det (y - x) x`**: for two distinct unit vectors. -/
theorem abs_det_sub_lt_norm {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) :
    |det (y - x) x| < ‖y - x‖ := by
  have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hc : 0 < ‖y - x‖ := norm_pos_iff.mpr hne
  have h1 : |det (y - x) x| ≤ ‖y - x‖ * ‖x‖ := abs_det_le _ _
  rw [hx, mul_one] at h1
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exfalso
    -- equality forces `dot (y-x) x = 0`, whence `‖y‖ ^ 2 = 1 + ‖y-x‖ ^ 2 > 1`
    have h2 : dot (y - x) x = 0 := by
      have h3 := lagrange (y - x) x
      rw [hx, one_pow, mul_one] at h3
      have h4 : det (y - x) x ^ 2 = ‖y - x‖ ^ 2 := by
        rw [pow_two, pow_two, ← abs_mul_abs_self (det (y - x) x), h]
      nlinarith [sq_nonneg (dot (y - x) x), h3, h4]
    have h5 : y = x + (y - x) := by ring
    have h6 := norm_add_sq x (y - x)
    rw [show x + (y - x) = y by ring, hy, hx, dot_comm x (y - x), h2, one_pow] at h6
    nlinarith [h6, hc]

theorem chord_eq_seg {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) :
    chord x y = seg x y := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨hzball, hzero⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hzball
    obtain ⟨s, hs⟩ := exists_smul_of_det_eq_zero (a := y - x) (w := z - x) hzero
      (sub_ne_zero.mpr (Ne.symm hxy))
    have hz : z = segPoint s x y := by
      have h' : z = x + (z - x) := by ring
      rw [h', hs, Complex.real_smul, segPoint]
      push_cast
      ring
    have hsq := norm_segPoint_sq_of_unit hx hy s
    have hd := dot_lt_one hx hy hxy
    have hle : ‖segPoint s x y‖ ^ 2 ≤ 1 := by rw [← hz]; nlinarith [norm_nonneg z]
    have hpos : 0 < 1 - dot x y := by linarith
    have hprod : s * (1 - s) * (1 - dot x y) ≥ 0 := by nlinarith [hsq, hle]
    have hprod' : (1 - dot x y) * (s * (1 - s)) ≥ 0 := by nlinarith [hprod]
    have hs01 : s * (1 - s) ≥ 0 := nonneg_of_mul_nonneg_right hprod' hpos
    exact ⟨s, ⟨by nlinarith [hs01, sq_nonneg (s - 1 / 2)],
      by nlinarith [hs01, sq_nonneg (s - 1 / 2)]⟩, hz.symm⟩
  · rintro z ⟨t, ht, rfl⟩
    refine ⟨seg_subset_closedBall (le_of_eq hx) (le_of_eq hy) ⟨t, ht, rfl⟩, ?_⟩
    show chordFun x y (segPoint t x y) = 0
    rw [segPoint, chordFun_affine, chordFun_x, chordFun_y]
    ring

theorem seg_diff_subset_ball {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) :
    seg x y \ {x, y} ⊆ Metric.ball (0 : ℂ) 1 := by
  rintro z ⟨⟨s, hs, rfl⟩, hznot⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hsq := norm_segPoint_sq_of_unit hx hy s
  have hd := dot_lt_one hx hy hxy
  have hs0 : s ≠ 0 := by rintro h0; exact hznot (by rw [h0]; simp)
  have hs1 : s ≠ 1 := by rintro h1; exact hznot (by rw [h1]; simp)
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
  have hprod : 0 < s * (1 - s) := mul_pos hspos (by linarith)
  have hlt : ‖segPoint s x y‖ ^ 2 < 1 := by nlinarith [hsq, hd, hprod]
  nlinarith [norm_nonneg (segPoint s x y), hlt]

theorem chord_inter_circle {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) :
    chord x y ∩ Metric.sphere (0 : ℂ) 1 = {x, y} := by
  rw [chord_eq_seg hx hy hxy]
  ext z
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hzsph⟩
    rw [Metric.mem_sphere, dist_zero_right] at hzsph
    have hsq := norm_segPoint_sq_of_unit hx hy s
    have hd := dot_lt_one hx hy hxy
    have hprod : s * (1 - s) = 0 := by nlinarith [hsq, hzsph, hd]
    rcases mul_eq_zero.mp hprod with h | h
    · have : s = 0 := by linarith
      subst this; simp
    · have : s = 1 := by linarith
      subst this; simp
  · rintro (rfl | rfl)
    · exact ⟨left_mem_seg _ _, by rw [Metric.mem_sphere, dist_zero_right]; exact hx⟩
    · exact ⟨right_mem_seg _ _, by rw [Metric.mem_sphere, dist_zero_right]; exact hy⟩

theorem chordFun_swap (x y z : ℂ) : chordFun y x z = - chordFun x y z := by
  rw [chordFun_eq, chordFun_eq, det_apply, det_apply]
  simp only [Complex.sub_re, Complex.sub_im]
  ring

/-! ## The witnesses in the caps -/

/-- The point `I * (y - x) / ‖y - x‖` is on the circle. -/
theorem norm_I_div (a : ℂ) (ha : a ≠ 0) :
    ‖(Complex.I * a) / ((‖a‖ : ℝ) : ℂ)‖ = 1 := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos, div_self (ne_of_gt hpos)]

/-- The point `-(I * (y - x)) / ‖y - x‖` is on the circle. -/
theorem norm_neg_I_div (a : ℂ) (ha : a ≠ 0) :
    ‖(-(Complex.I * a)) / ((‖a‖ : ℝ) : ℂ)‖ = 1 := by
  rw [neg_div, norm_neg]
  exact norm_I_div a ha

/-- The chord functional at the positive witness. -/
theorem chordFun_I_div {x y : ℂ} (hne : y - x ≠ 0) :
    chordFun x y ((Complex.I * (y - x)) / ((‖y - x‖ : ℝ) : ℂ))
      = ‖y - x‖ - det (y - x) x := by
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.mpr hne
  have hdiv : (Complex.I * (y - x)) / ((‖y - x‖ : ℝ) : ℂ)
      = (((1 / ‖y - x‖ : ℝ)) : ℂ) * (Complex.I * (y - x)) := by
    rw [div_eq_inv_mul, ← Complex.ofReal_inv, one_div]
  rw [hdiv, chordFun_eq_sub, det_smul_right, det_I_mul_self]
  rw [show (1 / ‖y - x‖) * ‖y - x‖ ^ 2 = ‖y - x‖ by field_simp]

/-- The chord functional at the negative witness. -/
theorem chordFun_neg_I_div {x y : ℂ} (hne : y - x ≠ 0) :
    chordFun x y (-(Complex.I * (y - x)) / ((‖y - x‖ : ℝ) : ℂ))
      = -‖y - x‖ - det (y - x) x := by
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.mpr hne
  have hdiv : (-(Complex.I * (y - x))) / ((‖y - x‖ : ℝ) : ℂ)
      = (((1 / ‖y - x‖ : ℝ)) : ℂ) * (-(Complex.I * (y - x))) := by
    rw [div_eq_inv_mul, ← Complex.ofReal_inv, one_div]
  rw [hdiv, chordFun_eq_sub, det_smul_right, det_neg_right, det_I_mul_self]
  rw [show (1 / ‖y - x‖) * (-‖y - x‖ ^ 2) = -‖y - x‖ by field_simp]

/-- **Both arcs are non-empty.** -/
theorem arcPos_nonempty {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) :
    (arcPos x y).Nonempty := by
  have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hlt := abs_det_sub_lt_norm hx hy hxy
  rw [abs_lt] at hlt
  refine ⟨(Complex.I * (y - x)) / ((‖y - x‖ : ℝ) : ℂ), ?_, ?_⟩
  · rw [Metric.mem_sphere, dist_zero_right]
    exact norm_I_div _ hne
  · rw [chordFun_I_div hne]
    linarith [hlt.2]

/-- **Both arcs are non-empty** (the negative one). -/
theorem arcNeg_nonempty {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) :
    (arcNeg x y).Nonempty := by
  have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hlt := abs_det_sub_lt_norm hx hy hxy
  rw [abs_lt] at hlt
  refine ⟨-(Complex.I * (y - x)) / ((‖y - x‖ : ℝ) : ℂ), ?_, ?_⟩
  · rw [Metric.mem_sphere, dist_zero_right]
    exact norm_neg_I_div _ hne
  · rw [chordFun_neg_I_div hne]
    linarith [hlt.1]

/-- **The circle is the union of the two arcs and the two endpoints.** -/
theorem circle_eq_arcPos_union_arcNeg {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : x ≠ y) :
    Metric.sphere (0 : ℂ) 1 = arcPos x y ∪ arcNeg x y ∪ {x, y} := by
  ext z
  constructor
  · intro hz
    by_cases h0 : chordFun x y z = 0
    · have hzc : z ∈ chord x y := ⟨Metric.sphere_subset_closedBall hz, h0⟩
      have hmem : z ∈ chord x y ∩ Metric.sphere (0 : ℂ) 1 := ⟨hzc, hz⟩
      rw [chord_inter_circle hx hy hxy] at hmem
      exact Or.inr hmem
    · rcases lt_or_gt_of_ne h0 with h | h
      · exact Or.inl (Or.inr ⟨hz, h⟩)
      · exact Or.inl (Or.inl ⟨hz, h⟩)
  · rintro ((hz | hz) | hz)
    · exact hz.1
    · exact hz.1
    · rcases hz with rfl | rfl
      · rw [Metric.mem_sphere, dist_zero_right]; exact hx
      · rw [Metric.mem_sphere, dist_zero_right]; exact hy

/-! ## The arcs lie in the closures of the caps -/

theorem chordFun_ray (x y z : ℂ) (s : ℝ) :
    chordFun x y (((1 - s : ℝ)) • z)
      = (1 - s) * chordFun x y z + s * chordFun x y 0 := by
  have h := chordFun_affine x y s z 0
  have h1 : ((1 - s : ℝ) : ℂ) * z + ((s : ℝ) : ℂ) * 0 = ((1 - s : ℝ) : ℂ) * z := by ring
  rw [h1, ← Complex.real_smul] at h
  rw [← h]

/-- **Each arc lies in the closure of the cap on the same side.** -/
theorem arcPos_subset_closure_capPos (x y : ℂ) : arcPos x y ⊆ closure (capPos x y) := by
  intro z hz
  obtain ⟨hzsph, hzpos⟩ := hz
  have hz1 : ‖z‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hzsph
  have hA : 0 < chordFun x y z := hzpos
  rw [Metric.mem_closure_iff]
  intro ε hε
  set A : ℝ := chordFun x y z with hAdef
  set B : ℝ := chordFun x y 0 with hBdef
  have hval : ∀ s : ℝ, chordFun x y (((1 - s : ℝ)) • z) = A - s * (A - B) := by
    intro s
    rw [chordFun_ray, hAdef, hBdef]; ring
  set q : ℝ := if 0 < A - B then A / (A - B) else 1 with hqdef
  have hqpos : 0 < q := by
    rw [hqdef]
    split_ifs with h
    · exact div_pos hA (by linarith)
    · norm_num
  set s : ℝ := min (min (ε / 2) q) 1 / 2 with hsdef
  have hs_pos : 0 < s := by
    rw [hsdef]
    exact half_pos (lt_min (lt_min (by linarith) hqpos) one_pos)
  have hs_half : s ≤ 1 / 2 := by
    rw [hsdef]
    have h1 : min (min (ε / 2) q) 1 ≤ 1 := min_le_right _ _
    linarith
  have hs_lt_eps : s < ε := by
    have h1 : min (min (ε / 2) q) 1 ≤ ε / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    rw [hsdef]
    linarith
  have hs_lt_q : s < q := by
    have h1 : min (min (ε / 2) q) 1 ≤ q := le_trans (min_le_left _ _) (min_le_right _ _)
    rw [hsdef]
    linarith
  have hposval : 0 < chordFun x y (((1 - s : ℝ)) • z) := by
    rw [hval s]
    rw [hqdef] at hs_lt_q
    split_ifs at hs_lt_q with hq
    · have h2 : s * (A - B) < A := (lt_div_iff₀ hq).mp hs_lt_q
      linarith
    · have h2 : s * (A - B) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs_pos)
        (by linarith)
      linarith
  refine ⟨((1 - s : ℝ)) • z, ?_, ?_⟩
  · rw [capPos_def, Set.mem_inter_iff]
    refine ⟨?_, hposval⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have h1s : (0 : ℝ) < 1 - s := by linarith
    rw [abs_of_pos h1s, hz1, mul_one]
    linarith
  · have hsub : z - (((1 - s : ℝ)) • z) = (s : ℝ) • z := by
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    have hdist : dist z (((1 - s : ℝ)) • z) = s := by
      rw [dist_eq_norm, hsub]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos, hz1, mul_one]
    rw [hdist]
    exact hs_lt_eps

/-- **Each arc lies in the closure of the cap on the same side** (negative side). -/
theorem arcNeg_subset_closure_capNeg (x y : ℂ) : arcNeg x y ⊆ closure (capNeg x y) := by
  intro z hz
  obtain ⟨hzsph, hzneg⟩ := hz
  have hz1 : ‖z‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hzsph
  have hA : chordFun x y z < 0 := hzneg
  rw [Metric.mem_closure_iff]
  intro ε hε
  set A : ℝ := chordFun x y z with hAdef
  set B : ℝ := chordFun x y 0 with hBdef
  have hval : ∀ s : ℝ, chordFun x y (((1 - s : ℝ)) • z) = A - s * (A - B) := by
    intro s
    rw [chordFun_ray, hAdef, hBdef]; ring
  set q : ℝ := if 0 < B - A then A / (A - B) else 1 with hqdef
  have hqpos : 0 < q := by
    rw [hqdef]
    split_ifs with h
    · exact div_pos_of_neg_of_neg hA (by linarith)
    · norm_num
  set s : ℝ := min (min (ε / 2) q) 1 / 2 with hsdef
  have hs_pos : 0 < s := by
    rw [hsdef]
    exact half_pos (lt_min (lt_min (by linarith) hqpos) one_pos)
  have hs_half : s ≤ 1 / 2 := by
    rw [hsdef]
    have h1 : min (min (ε / 2) q) 1 ≤ 1 := min_le_right _ _
    linarith
  have hs_lt_eps : s < ε := by
    have h1 : min (min (ε / 2) q) 1 ≤ ε / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    rw [hsdef]
    linarith
  have hs_lt_q : s < q := by
    have h1 : min (min (ε / 2) q) 1 ≤ q := le_trans (min_le_left _ _) (min_le_right _ _)
    rw [hsdef]
    linarith
  have hposval : chordFun x y (((1 - s : ℝ)) • z) < 0 := by
    rw [hval s]
    rw [hqdef] at hs_lt_q
    split_ifs at hs_lt_q with hq
    · have hAB : A - B < 0 := by linarith
      have hne : A - B ≠ 0 := ne_of_lt hAB
      have hprod : (A / (A - B)) * (A - B) = A := div_mul_cancel₀ A hne
      have h2 : A < s * (A - B) := by
        have h3 := mul_lt_mul_of_neg_left hs_lt_q hAB
        rw [mul_comm (A - B) (A / (A - B)), hprod, mul_comm (A - B) s] at h3
        exact h3
      linarith
    · have h2 : s * (A - B) ≥ 0 := mul_nonneg (le_of_lt hs_pos) (by linarith)
      linarith
  refine ⟨((1 - s : ℝ)) • z, ?_, ?_⟩
  · rw [capNeg_def, Set.mem_inter_iff]
    refine ⟨?_, hposval⟩
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have h1s : (0 : ℝ) < 1 - s := by linarith
    rw [abs_of_pos h1s, hz1, mul_one]
    linarith
  · have hsub : z - (((1 - s : ℝ)) • z) = (s : ℝ) • z := by
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    have hdist : dist z (((1 - s : ℝ)) • z) = s := by
      rw [dist_eq_norm, hsub]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos, hz1, mul_one]
    rw [hdist]
    exact hs_lt_eps

end

end Work.Smooth.Schoenflies
