import Mathlib
import Submission.Work.Mostow.localIsomDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-!
# The "between vector" identity for points on a hyperbolic geodesic

For `x y z : ℍⁿ` (chart model `E n`) with `y` on the geodesic segment from `x` to `z`
(expressed by the triangle equality `hdist x z = hdist x y + hdist y z` and `x ≠ z`),
the hyperboloid lift of `y` is the affine combination

`hlift y = (sinh (hdist y z) / sinh (hdist x z)) • hlift x + (sinh (hdist x y) / sinh (hdist x z)) • hlift z`.

This is the standard hyperboloid computation: the vector
`V = sinh c • Y - sinh b • X - sinh a • Z` (with `a = hdist x y`, `b = hdist y z`, `c = hdist x z = a+b`)
is Minkowski-orthogonal to the timelike vector `X = hlift x` and Minkowski-null; the only such
vectors are zero (reverse Cauchy–Schwarz).
-/

namespace Btw

variable {n : ℕ}

/-! ## Minkowski toolkit for `Fin n ⊕ Fin 1 → ℝ` -/

/-- `inner ℝ u v` on `E n = EuclideanSpace ℝ (Fin n)`, in coordinates. -/
lemma inner_eq_sum (u v : E n) : inner ℝ u v = ∑ i : Fin n, u i * v i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma norm_sq_eq_sum (w : E n) : ‖w‖ ^ 2 = ∑ i : Fin n, w i * w i := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_sum]

lemma mink_hlift (u v : E n) : mink_localIsomDefs (hlift u) (hlift v) = inner ℝ u v - tpart u * tpart v := by
  rw [mink_localIsomDefs, inner_eq_sum]
  simp only [hlift, Sum.elim_inl, Sum.elim_inr]

lemma mink_hlift_self (u : E n) : mink_localIsomDefs (hlift u) (hlift u) = -1 := by
  rw [mink_hlift, real_inner_self_eq_norm_sq]
  have h := tpart_sq u
  nlinarith

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
  rw [hdist]; exact Real.cosh_arcosh (one_le_cosh_hdist u v)

lemma mink_hlift_neg_cosh (u v : E n) : mink_localIsomDefs (hlift u) (hlift v) = -Real.cosh (hdist u v) := by
  rw [mink_hlift, cosh_hdist]; ring

/-! ### Bilinearity of `mink_localIsomDefs` -/

lemma mink_comm (x y : Fin n ⊕ Fin 1 → ℝ) : mink_localIsomDefs x y = mink_localIsomDefs y x := by
  rw [mink_localIsomDefs, mink_localIsomDefs]; congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · ring

lemma mink_smul_left (r : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) : mink_localIsomDefs (r • x) y = r * mink_localIsomDefs x y := by
  simp only [mink_localIsomDefs, Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro i _; ring
  · ring

lemma mink_smul_right (x : Fin n ⊕ Fin 1 → ℝ) (r : ℝ) (y : Fin n ⊕ Fin 1 → ℝ) :
    mink_localIsomDefs x (r • y) = r * mink_localIsomDefs x y := by
  rw [mink_comm x (r • y), mink_smul_left, mink_comm]

lemma mink_add_left (x y z : Fin n ⊕ Fin 1 → ℝ) : mink_localIsomDefs (x + y) z = mink_localIsomDefs x z + mink_localIsomDefs y z := by
  simp only [mink_localIsomDefs, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring

lemma mink_add_right (x y z : Fin n ⊕ Fin 1 → ℝ) : mink_localIsomDefs x (y + z) = mink_localIsomDefs x y + mink_localIsomDefs x z := by
  rw [mink_comm x (y+z), mink_add_left, mink_comm y x, mink_comm z x]

lemma mink_neg_left (x y : Fin n ⊕ Fin 1 → ℝ) : mink_localIsomDefs (-x) y = - mink_localIsomDefs x y := by
  have := mink_smul_left (-1) x y; simpa using this

lemma mink_neg_right (x y : Fin n ⊕ Fin 1 → ℝ) : mink_localIsomDefs x (-y) = - mink_localIsomDefs x y := by
  rw [mink_comm x (-y), mink_neg_left, mink_comm]

lemma mink_sub_left (x y z : Fin n ⊕ Fin 1 → ℝ) : mink_localIsomDefs (x - y) z = mink_localIsomDefs x z - mink_localIsomDefs y z := by
  rw [sub_eq_add_neg, mink_add_left, mink_neg_left]; ring

lemma mink_sub_right (x y z : Fin n ⊕ Fin 1 → ℝ) : mink_localIsomDefs x (y - z) = mink_localIsomDefs x y - mink_localIsomDefs x z := by
  rw [sub_eq_add_neg, mink_add_right, mink_neg_right]; ring

/-! ### The chart coordinates of `mink_localIsomDefs` -/

lemma spatial_mink_hlift (W : Fin n ⊕ Fin 1 → ℝ) (p : E n) :
    mink_localIsomDefs W (hlift p) = inner ℝ (spatial W) p - tcoord W * tpart p := by
  have h : (∑ i : Fin n, W (Sum.inl i) * p i) = inner ℝ (spatial W) p := by
    rw [inner_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [spatial]
  simp only [mink_localIsomDefs, hlift, Sum.elim_inl, Sum.elim_inr, tcoord]
  rw [h]

lemma mink_self_spatial (W : Fin n ⊕ Fin 1 → ℝ) :
    mink_localIsomDefs W W = ‖spatial W‖ ^ 2 - tcoord W ^ 2 := by
  have h : (∑ i : Fin n, W (Sum.inl i) * W (Sum.inl i)) = ‖spatial W‖ ^ 2 := by
    rw [norm_sq_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [spatial]
  simp only [mink_localIsomDefs, tcoord]
  rw [h]; ring

/-! ### Reverse Cauchy–Schwarz: `X^⊥` is positive definite for a timelike `X` -/

/-- If `mink_localIsomDefs W (hlift p) = 0` then `mink_localIsomDefs W W = gH p (spatial W)`, and `mink_localIsomDefs W W = 0` forces `W = 0`. -/
lemma minkTangent (p : E n) (W : Fin n ⊕ Fin 1 → ℝ) (h : mink_localIsomDefs W (hlift p) = 0) :
    mink_localIsomDefs W W = gH p (spatial W) ∧ (mink_localIsomDefs W W = 0 ↔ W = 0) := by
  have hsp := spatial_mink_hlift W p
  rw [h] at hsp
  have hinner : inner ℝ (spatial W) p = tcoord W * tpart p := by linarith
  have htpar : tpart p ≠ 0 := ne_of_gt (tpart_pos p)
  constructor
  · have h1 : inner ℝ p (spatial W) = tcoord W * tpart p := by rw [real_inner_comm, hinner]
    rw [mink_self_spatial, gH, h1, ← tpart_sq p]
    field_simp
  · constructor
    · intro h0
      have hsq : ‖spatial W‖ ^ 2 = tcoord W ^ 2 := by
        have := mink_self_spatial W; rw [h0] at this; linarith
      have hcs2 : (inner ℝ (spatial W) p) ^ 2 ≤ ‖spatial W‖ ^ 2 * ‖p‖ ^ 2 := by
        have h3 : (inner ℝ (spatial W) p) ^ 2 ≤ (‖spatial W‖ * ‖p‖) ^ 2 := by
          rw [sq_le_sq, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
          exact abs_real_inner_le_norm _ _
        rwa [mul_pow] at h3
      rw [hinner, mul_pow, tpart_sq p] at hcs2
      rw [← hsq] at hcs2
      have ht0 : tcoord W = 0 := by nlinarith [sq_nonneg ‖p‖, sq_nonneg (tcoord W)]
      have hsp0 : spatial W = 0 := by
        have h2 : ‖spatial W‖ ^ 2 = 0 := by rw [hsq, ht0]; ring
        exact norm_eq_zero.mp (by nlinarith [norm_nonneg (spatial W)])
      funext k
      rcases k with i | j
      · have := congrArg (fun x : E n => x i) hsp0
        simpa [spatial] using this
      · fin_cases j
        exact ht0
    · intro hW; rw [hW]; simp [mink_localIsomDefs]

/-! ### Elementary facts about `hdist` -/

lemma hlift_injective : Function.Injective (hlift : E n → Fin n ⊕ Fin 1 → ℝ) := by
  intro u v hh
  ext i
  have := congrFun hh (Sum.inl i)
  simpa [hlift] using this

lemma hdist_self (u : E n) : hdist u u = 0 := by
  rw [hdist]
  have h : tpart u * tpart u - inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq]; have := tpart_sq u; nlinarith
  rw [h, Real.arcosh_zero]

lemma hdist_eq_zero (u v : E n) : hdist u v = 0 ↔ u = v := by
  constructor
  · intro h0
    have hc : Real.cosh (hdist u v) = 1 := by rw [h0, Real.cosh_zero]
    rw [cosh_hdist] at hc
    have hmink : mink_localIsomDefs (hlift u) (hlift v) = -1 := by rw [mink_hlift]; linarith
    have hW0 : hlift u - hlift v = 0 := by
      have horth : mink_localIsomDefs (hlift u - hlift v) (hlift u) = 0 := by
        rw [mink_sub_left, mink_hlift_self]
        have : mink_localIsomDefs (hlift v) (hlift u) = -1 := by rw [mink_comm, hmink]
        rw [this]; ring
      have hnull : mink_localIsomDefs (hlift u - hlift v) (hlift u - hlift v) = 0 := by
        rw [mink_sub_left, mink_sub_right, mink_sub_right, mink_hlift_self u, mink_hlift_self v, hmink]
        have : mink_localIsomDefs (hlift v) (hlift u) = -1 := by rw [mink_comm, hmink]
        rw [this]; ring
      exact ((minkTangent u (hlift u - hlift v) horth).2).mp hnull
    exact hlift_injective (sub_eq_zero.mp hW0)
  · intro h; rw [h]; exact hdist_self v

/-! ## Hyperbolic-function identities with `c = a + b` -/

lemma trig1 (a b : ℝ) :
    Real.sinh b + Real.sinh a * Real.cosh (a + b) = Real.cosh a * Real.sinh (a + b) := by
  rw [Real.cosh_add, Real.sinh_add]
  linear_combination (-Real.sinh b) * (Real.cosh_sq_sub_sinh_sq a)

lemma trig3 (a b : ℝ) :
    -(Real.sinh (a+b))^2 - (Real.sinh b)^2 - (Real.sinh a)^2
      + 2 * Real.sinh (a+b) * Real.sinh b * Real.cosh a
      + 2 * Real.sinh (a+b) * Real.sinh a * Real.cosh b
      - 2 * Real.sinh b * Real.sinh a * Real.cosh (a+b) = 0 := by
  rw [Real.cosh_add, Real.sinh_add]
  ring_nf
  nlinarith [Real.cosh_sq_sub_sinh_sq a, Real.cosh_sq_sub_sinh_sq b]

end Btw

open Work.Mostow.Btw

theorem betweenVec {n : ℕ} (x y z : E n) (hxz : x ≠ z)
    (h : hdist x z = hdist x y + hdist y z) :
    hlift y = (Real.sinh (hdist y z) / Real.sinh (hdist x z)) • hlift x +
      (Real.sinh (hdist x y) / Real.sinh (hdist x z)) • hlift z := by
  have hsc : Real.sinh (hdist x z) ≠ 0 := by
    rw [Real.sinh_ne_zero]
    intro hc0
    exact hxz ((hdist_eq_zero x z).mp hc0)
  set a := hdist x y with ha
  set b := hdist y z with hb
  set c := hdist x z with hc
  -- after the `set`s:  `h : c = a + b`, `hsc : Real.sinh c ≠ 0`
  have hsum : c = a + b := h
  have t1 : Real.sinh b + Real.sinh a * Real.cosh c = Real.cosh a * Real.sinh c := by
    rw [hsum]; exact trig1 a b
  have t3 : -(Real.sinh c)^2 - (Real.sinh b)^2 - (Real.sinh a)^2
      + 2 * Real.sinh c * Real.sinh b * Real.cosh a
      + 2 * Real.sinh c * Real.sinh a * Real.cosh b
      - 2 * Real.sinh b * Real.sinh a * Real.cosh c = 0 := by
    rw [hsum]; exact trig3 a b
  -- Minkowski pairings, in terms of `a`, `b`, `c`
  have hYY : mink_localIsomDefs (hlift y) (hlift y) = -1 := mink_hlift_self y
  have hXX : mink_localIsomDefs (hlift x) (hlift x) = -1 := mink_hlift_self x
  have hZZ : mink_localIsomDefs (hlift z) (hlift z) = -1 := mink_hlift_self z
  have hYX : mink_localIsomDefs (hlift y) (hlift x) = -Real.cosh a := by
    rw [mink_hlift_neg_cosh, hdist_comm' y x, ← ha]
  have hXY : mink_localIsomDefs (hlift x) (hlift y) = -Real.cosh a := by
    rw [mink_hlift_neg_cosh, ← ha]
  have hYZ : mink_localIsomDefs (hlift y) (hlift z) = -Real.cosh b := by
    rw [mink_hlift_neg_cosh, ← hb]
  have hZY : mink_localIsomDefs (hlift z) (hlift y) = -Real.cosh b := by
    rw [mink_hlift_neg_cosh, hdist_comm' z y, ← hb]
  have hXZ : mink_localIsomDefs (hlift x) (hlift z) = -Real.cosh c := by
    rw [mink_hlift_neg_cosh, ← hc]
  have hZX : mink_localIsomDefs (hlift z) (hlift x) = -Real.cosh c := by
    rw [mink_hlift_neg_cosh, hdist_comm' z x, ← hc]
  -- orthogonality of `V` to `hlift x`
  have horth : mink_localIsomDefs (Real.sinh c • hlift y - Real.sinh b • hlift x
      - Real.sinh a • hlift z) (hlift x) = 0 := by
    simp only [mink_sub_left, mink_smul_left]
    rw [hYX, hXX, hZX]
    linarith [t1]
  -- `V` is Minkowski-null
  have hnull : mink_localIsomDefs (Real.sinh c • hlift y - Real.sinh b • hlift x
      - Real.sinh a • hlift z) (Real.sinh c • hlift y - Real.sinh b • hlift x
      - Real.sinh a • hlift z) = 0 := by
    simp only [mink_sub_left, mink_sub_right, mink_smul_left, mink_smul_right]
    rw [hYY, hXX, hZZ, hYX, hXY, hYZ, hZY, hXZ, hZX]
    linarith [t3]
  have hV : Real.sinh c • hlift y - Real.sinh b • hlift x - Real.sinh a • hlift z = 0 :=
    ((minkTangent x _ horth).2).mp hnull
  have hkey : Real.sinh c • hlift y = Real.sinh b • hlift x + Real.sinh a • hlift z := by
    have h1 : Real.sinh c • hlift y - Real.sinh b • hlift x = Real.sinh a • hlift z :=
      sub_eq_zero.mp hV
    have h2 : Real.sinh c • hlift y = Real.sinh a • hlift z + Real.sinh b • hlift x :=
      eq_add_of_sub_eq h1
    rw [h2, add_comm]
  have hgoal : hlift y = (Real.sinh b / Real.sinh c) • hlift x
      + (Real.sinh a / Real.sinh c) • hlift z := by
    have h2 := congrArg (fun W => (Real.sinh c)⁻¹ • W) hkey
    rw [smul_add, smul_smul, smul_smul, smul_smul] at h2
    rw [inv_mul_cancel₀ hsc, one_smul] at h2
    rw [inv_mul_eq_div, inv_mul_eq_div] at h2
    exact h2
  exact hgoal

end Work.Mostow
