import Mathlib
import Submission.Work.Mostow.localIsomDefs

/-!
# Unit speed of the explicit geodesic segment `segfun`

This file proves that the chart-expression `segfun p q s` is an arclength-parametrised
geodesic: its derivative has unit length for the hyperbolic metric `gH`.

The proof goes through the hyperboloid model.  Writing `P = hlift p`, `Q = hlift q` and
`d = hdist p q`, the ambient curve
`c(s) = (sinh (d - s) / sinh d) • P + (sinh s / sinh d) • Q`
lies on the upper sheet of `⟪x,x⟫ = -1` and satisfies `⟪c,c'⟫ = 0`, `⟪c',c'⟫ = 1`.
Since `spatial (c s) = segfun p q s` and `spatial (c' s)` is the vector appearing in the
statement, the result follows from the general identity
`mink_localIsomDefs D D = gH (spatial C) (spatial D)` valid whenever `mink_localIsomDefs C C = -1` and `mink_localIsomDefs C D = 0`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-! ## Toolkit for the Minkowski form `mink_localIsomDefs` -/

lemma inner_eq_sum_segfunSpeed (u v : E n) : inner ℝ u v = ∑ i : Fin n, u i * v i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma mink_smul (r t : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink_localIsomDefs (r • x) (t • y) = r * t * mink_localIsomDefs x y := by
  rw [mink_localIsomDefs, mink_localIsomDefs]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ i : Fin n, r * x (Sum.inl i) * (t * y (Sum.inl i))) =
      r * t * ∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  ring

lemma mink_add_left (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink_localIsomDefs (x + y) z = mink_localIsomDefs x z + mink_localIsomDefs y z := by
  have hsum : (∑ i : Fin n, (x + y) (Sum.inl i) * z (Sum.inl i)) =
      (∑ i : Fin n, x (Sum.inl i) * z (Sum.inl i)) +
        ∑ i : Fin n, y (Sum.inl i) * z (Sum.inl i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.add_apply, add_mul]
  rw [mink_localIsomDefs, mink_localIsomDefs, mink_localIsomDefs, hsum]
  simp only [Pi.add_apply]
  ring

lemma mink_add_right (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink_localIsomDefs x (y + z) = mink_localIsomDefs x y + mink_localIsomDefs x z := by
  have hsum : (∑ i : Fin n, x (Sum.inl i) * (y + z) (Sum.inl i)) =
      (∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i)) +
        ∑ i : Fin n, x (Sum.inl i) * z (Sum.inl i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [Pi.add_apply, mul_add]
  rw [mink_localIsomDefs, mink_localIsomDefs, mink_localIsomDefs, hsum]
  simp only [Pi.add_apply]
  ring

lemma mink_hlift (u v : E n) : mink_localIsomDefs (hlift u) (hlift v) = inner ℝ u v - tpart u * tpart v := by
  have hsum : (∑ i : Fin n, hlift u (Sum.inl i) * hlift v (Sum.inl i)) =
      ∑ i : Fin n, u i * v i := Finset.sum_congr rfl fun i _ => by simp [hlift]
  rw [mink_localIsomDefs, inner_eq_sum_segfunSpeed, hsum]
  simp [hlift]

lemma mink_hlift_self (u : E n) : mink_localIsomDefs (hlift u) (hlift u) = -1 := by
  rw [mink_hlift, real_inner_self_eq_norm_sq]
  have h := tpart_sq u
  nlinarith

/-- `mink_localIsomDefs` in terms of the spatial part and the time coordinate. -/
lemma mink_spatial (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink_localIsomDefs x y = inner ℝ (spatial x) (spatial y) - x (Sum.inr 0) * y (Sum.inr 0) := by
  have hsum : (∑ i : Fin n, (spatial x) i * (spatial y) i) =
      ∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i) :=
    Finset.sum_congr rfl fun i _ => by simp [spatial]
  rw [mink_localIsomDefs, inner_eq_sum_segfunSpeed, hsum]

/-! ## Elementary facts about `hdist` -/

lemma one_le_cosh_hdist (u v : E n) : 1 ≤ tpart u * tpart v - inner ℝ u v := by
  have h1 : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have h2 : 1 + ‖u‖ * ‖v‖ ≤ tpart u * tpart v := by
    have ha : tpart u * tpart v = Real.sqrt ((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) := by
      rw [tpart, tpart, Real.sqrt_mul (by nlinarith [sq_nonneg ‖u‖])]
    rw [ha]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (‖u‖ - ‖v‖)]
  linarith

lemma cosh_hdist (u v : E n) : Real.cosh (hdist u v) = tpart u * tpart v - inner ℝ u v := by
  rw [hdist]
  exact Real.cosh_arcosh (one_le_cosh_hdist u v)

lemma hdist_nonneg (u v : E n) : 0 ≤ hdist u v := by
  rw [hdist]
  exact Real.arcosh_nonneg (one_le_cosh_hdist u v)

/-- `cdist p q = 1` iff `p = q`. -/
lemma cdist_eq_one_iff (p q : E n) : tpart p * tpart q - inner ℝ p q = 1 ↔ p = q := by
  constructor
  · intro h
    have hsq : (tpart p * tpart q) ^ 2 = (1 + inner ℝ p q) ^ 2 := by
      have h1 : tpart p * tpart q = 1 + inner ℝ p q := by linarith
      rw [h1]
    have hp := tpart_sq p
    have hq := tpart_sq q
    have hcs : (inner ℝ p q) ^ 2 ≤ (‖p‖ * ‖q‖) ^ 2 := by
      have h0 : |inner ℝ p q| ≤ ‖p‖ * ‖q‖ := abs_real_inner_le_norm p q
      have h0' : |inner ℝ p q| ^ 2 ≤ (‖p‖ * ‖q‖) ^ 2 := by
        have := mul_self_le_mul_self (abs_nonneg _) h0
        simpa [sq] using this
      rwa [sq_abs] at h0'
    have hns : ‖p - q‖ ^ 2 = ‖p‖ ^ 2 - 2 * inner ℝ p q + ‖q‖ ^ 2 := norm_sub_sq_real p q
    have hkey : ‖p - q‖ ^ 2 ≤ 0 := by
      rw [hns]; nlinarith [hsq, hp, hq, hcs]
    have hzero : ‖p - q‖ ^ 2 = 0 := le_antisymm hkey (sq_nonneg _)
    have hnorm : ‖p - q‖ = 0 := by nlinarith [hzero, norm_nonneg (p - q)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  · intro h
    subst h
    rw [real_inner_self_eq_norm_sq]
    have := tpart_sq p
    linarith

lemma hdist_eq_zero_iff (p q : E n) : hdist p q = 0 ↔ p = q := by
  have h : hdist p q = Real.arcosh (tpart p * tpart q - inner ℝ p q) := rfl
  rw [h, Real.arcosh_eq_zero_iff (one_le_cosh_hdist p q)]
  exact cdist_eq_one_iff p q

lemma hdist_pos_of_ne {p q : E n} (h : p ≠ q) : 0 < hdist p q :=
  lt_of_le_of_ne (hdist_nonneg p q) fun h0 => h ((hdist_eq_zero_iff p q).mp h0.symm)

lemma sinh_hdist_ne_zero {p q : E n} (h : p ≠ q) : Real.sinh (hdist p q) ≠ 0 := by
  intro hh
  exact h ((hdist_eq_zero_iff p q).mp (Real.sinh_eq_zero.mp hh))

/-! ## Pure hyperbolic-function identities -/

lemma sinh_add_sq_aux (A B : ℝ) :
    Real.sinh (A + B) ^ 2 - Real.sinh A ^ 2 - Real.sinh B ^ 2
      = 2 * Real.cosh (A + B) * Real.sinh A * Real.sinh B := by
  rw [Real.sinh_add, Real.cosh_add]
  nlinarith [Real.cosh_sq A, Real.cosh_sq B]

lemma seg_deriv_aux (A B : ℝ) :
    Real.sinh B * Real.cosh B - Real.sinh A * Real.cosh A
      + Real.cosh (A + B) * (Real.sinh A * Real.cosh B - Real.sinh B * Real.cosh A) = 0 := by
  rw [Real.cosh_add]
  linear_combination (Real.sinh A * Real.cosh A) * (Real.cosh_sq B)
    - (Real.sinh B * Real.cosh B) * (Real.cosh_sq A)

lemma seg_speed_aux (A B : ℝ) :
    Real.cosh A ^ 2 + Real.cosh B ^ 2
        - 2 * Real.cosh (A + B) * Real.cosh A * Real.cosh B
      = 1 - Real.cosh (A + B) ^ 2 := by
  rw [Real.cosh_add]
  nlinarith [Real.cosh_sq A, Real.cosh_sq B]

/-! ## The ambient geodesic and its derivative -/

/-- The ambient lift of `segfun p q s`: a linear combination of `hlift p`, `hlift q`. -/
noncomputable def amb (p q : E n) (s : ℝ) : Fin n ⊕ Fin 1 → ℝ :=
  (Real.sinh (hdist p q - s) / Real.sinh (hdist p q)) • hlift p +
    (Real.sinh s / Real.sinh (hdist p q)) • hlift q

/-- The (formal) derivative of `amb p q` at `s`. -/
noncomputable def ambD (p q : E n) (s : ℝ) : Fin n ⊕ Fin 1 → ℝ :=
  (- Real.cosh (hdist p q - s) / Real.sinh (hdist p q)) • hlift p +
    (Real.cosh s / Real.sinh (hdist p q)) • hlift q

lemma spatial_amb (p q : E n) (s : ℝ) : spatial (amb p q s) = segfun p q s := by
  simp only [amb, segfun, spatial_add, spatial_smul, spatial_hlift]

lemma spatial_ambD (p q : E n) (s : ℝ) :
    spatial (ambD p q s) = (- Real.cosh (hdist p q - s) / Real.sinh (hdist p q)) • p +
      (Real.cosh s / Real.sinh (hdist p q)) • q := by
  simp only [ambD, spatial_add, spatial_smul, spatial_hlift]

/-! ## The three Minkowski pairings -/

lemma mink_amb_self (p q : E n) (s : ℝ) (hsh : Real.sinh (hdist p q) ≠ 0) :
    mink_localIsomDefs (amb p q s) (amb p q s) = -1 := by
  have hP : mink_localIsomDefs (hlift p) (hlift p) = -1 := mink_hlift_self p
  have hQ : mink_localIsomDefs (hlift q) (hlift q) = -1 := mink_hlift_self q
  have hPQ : mink_localIsomDefs (hlift p) (hlift q) = -Real.cosh (hdist p q) := by
    rw [mink_hlift, cosh_hdist]; ring
  have hQP : mink_localIsomDefs (hlift q) (hlift p) = -Real.cosh (hdist p q) := by
    rw [mink_hlift, cosh_hdist, real_inner_comm]; ring
  have htrig := sinh_add_sq_aux (hdist p q - s) s
  rw [sub_add_cancel] at htrig
  simp only [amb, mink_add_left, mink_add_right, mink_smul, hP, hQ, hPQ, hQP]
  field_simp
  nlinarith [htrig]

lemma mink_amb_tangent (p q : E n) (s : ℝ) (hsh : Real.sinh (hdist p q) ≠ 0) :
    mink_localIsomDefs (amb p q s) (ambD p q s) = 0 := by
  have hP : mink_localIsomDefs (hlift p) (hlift p) = -1 := mink_hlift_self p
  have hQ : mink_localIsomDefs (hlift q) (hlift q) = -1 := mink_hlift_self q
  have hPQ : mink_localIsomDefs (hlift p) (hlift q) = -Real.cosh (hdist p q) := by
    rw [mink_hlift, cosh_hdist]; ring
  have hQP : mink_localIsomDefs (hlift q) (hlift p) = -Real.cosh (hdist p q) := by
    rw [mink_hlift, cosh_hdist, real_inner_comm]; ring
  have htrig := seg_deriv_aux (hdist p q - s) s
  rw [sub_add_cancel] at htrig
  simp only [amb, ambD, mink_add_left, mink_add_right, mink_smul, hP, hQ, hPQ, hQP]
  field_simp
  nlinarith [htrig]

lemma mink_ambD_speed (p q : E n) (s : ℝ) (hsh : Real.sinh (hdist p q) ≠ 0) :
    mink_localIsomDefs (ambD p q s) (ambD p q s) = 1 := by
  have hP : mink_localIsomDefs (hlift p) (hlift p) = -1 := mink_hlift_self p
  have hQ : mink_localIsomDefs (hlift q) (hlift q) = -1 := mink_hlift_self q
  have hPQ : mink_localIsomDefs (hlift p) (hlift q) = -Real.cosh (hdist p q) := by
    rw [mink_hlift, cosh_hdist]; ring
  have hQP : mink_localIsomDefs (hlift q) (hlift p) = -Real.cosh (hdist p q) := by
    rw [mink_hlift, cosh_hdist, real_inner_comm]; ring
  have htrig := seg_speed_aux (hdist p q - s) s
  rw [sub_add_cancel] at htrig
  simp only [ambD, mink_add_left, mink_add_right, mink_smul, hP, hQ, hPQ, hQP]
  field_simp
  nlinarith [htrig, Real.cosh_sq_sub_sinh_sq (hdist p q)]

/-! ## From the ambient pairings to `gH` -/

/-- If `C` lies on the hyperboloid and `D` is tangent to it at `C`, then `mink_localIsomDefs D D` is the
hyperbolic length-squared of the spatial part of `D` at the chart point `spatial C`. -/
lemma gH_spatial_of_tangent (C D : Fin n ⊕ Fin 1 → ℝ)
    (hC : mink_localIsomDefs C C = -1) (hCD : mink_localIsomDefs C D = 0) :
    gH (spatial C) (spatial D) = mink_localIsomDefs D D := by
  have h1 : (C (Sum.inr 0)) ^ 2 = 1 + ‖spatial C‖ ^ 2 := by
    have h := mink_spatial C C
    rw [hC, real_inner_self_eq_norm_sq] at h
    linarith
  have hCne : C (Sum.inr 0) ≠ 0 := by nlinarith [h1, sq_nonneg ‖spatial C‖]
  have h2 : inner ℝ (spatial C) (spatial D) = C (Sum.inr 0) * D (Sum.inr 0) := by
    have h := mink_spatial C D
    rw [hCD] at h
    linarith
  have h3 : mink_localIsomDefs D D = ‖spatial D‖ ^ 2 - (D (Sum.inr 0)) ^ 2 := by
    rw [mink_spatial, real_inner_self_eq_norm_sq]
    ring
  rw [h3, gH, h2]
  have hden : 1 + ‖spatial C‖ ^ 2 = (C (Sum.inr 0)) ^ 2 := h1.symm
  rw [hden]
  field_simp

/-! ## Main theorem -/

theorem segfunSpeed {n : ℕ} (p q : E n) (hpq : p ≠ q) (s : ℝ) (hs : s ∈ Set.Icc 0 (hdist p q)) :
    gH (segfun p q s) ((- Real.cosh (hdist p q - s) / Real.sinh (hdist p q)) • p +
      (Real.cosh s / Real.sinh (hdist p q)) • q) = 1 := by
  have hsh : Real.sinh (hdist p q) ≠ 0 := sinh_hdist_ne_zero hpq
  rw [← spatial_amb p q s, ← spatial_ambD p q s,
    gH_spatial_of_tangent (amb p q s) (ambD p q s)
      (mink_amb_self p q s hsh) (mink_amb_tangent p q s hsh),
    mink_ambD_speed p q s hsh]

end Work.Mostow
