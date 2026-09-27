import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.BaryBase

/-!
# Specification of the explicit geodesic `geo` (chart model of ℍⁿ)

`Work.Mostow.geo u v s` is the point at parameter `s` of the hyperbolic geodesic from `u` to `v`.
In `QIDefs` it is defined as the *spatial part* of the normalised linear combination of the lifts
`P = hlift u`, `Q = hlift v` on the hyperboloid `⟨x,x⟩ = -1`:

* `geoVec u v s = hlift u` if `u = v`;
* `geoVec u v s = (sinh d)⁻¹ • (sinh ((1-s) d) • hlift u + sinh (s d) • hlift v)`, `d = hdist u v`.

Main results (`geoSpec`):

* `geo u v 0 = u`, `geo u v 1 = v`;
* `hdist (geo u v s) (geo u v t) = |s - t| * hdist u v` for `s, t ∈ [0,1]`.

The proof is the standard hyperboloid computation: the linear combination above lies on the upper
sheet with time coordinate `> 0` (so it *is* `hlift (geo u v s)`), and its Minkowski pairing is
`-cosh ((s-t) d)`, whence the distance formula via `arcosh ∘ cosh = |·|`.

This file is self-contained (`Mathlib`, `QIDefs`, `BaryBase`); the two independent algebraic
ingredients it uses are also verified library modules in their own right,
`Submission.Work.Mostow.minkGeoSeg` (`Work.Mostow.minkGeoSeg`) and
`Submission.Work.Mostow.geoVecTimePos` (`Work.Mostow.geoVecTimePos`).
-/

open Submission.Mostow

namespace Work.Mostow

variable {n : ℕ}

/-! ## Toolkit for the Minkowski form on `Fin n ⊕ Fin 1 → ℝ` -/

/-- The spatial part of a vector of `ℝ^{Fin n ⊕ Fin 1}`. -/
private def spat (x : Fin n ⊕ Fin 1 → ℝ) : E n := WithLp.toLp 2 fun i => x (Sum.inl i)

private lemma spat_hlift (u : E n) : spat (hlift u) = u := by
  simp [spat, hlift]

private lemma hlift_injective : Function.Injective (hlift : E n → Fin n ⊕ Fin 1 → ℝ) := by
  intro u v hh
  ext i
  have := congrFun hh (Sum.inl i)
  simpa [hlift] using this

private lemma norm_sq_eq_sum (w : E n) : ‖w‖ ^ 2 = ∑ i : Fin n, w i * w i := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]

private lemma inner_eq_sum (u v : E n) : inner ℝ u v = ∑ i : Fin n, u i * v i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private lemma mink_smul (r s : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink (r • x) (s • y) = r * s * mink x y := by
  rw [mink, mink]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : (∑ i : Fin n, r * x (Sum.inl i) * (s * y (Sum.inl i))) =
      r * s * ∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1]
  ring

private lemma mink_add_left (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink (x + y) z = mink x z + mink y z := by
  simp only [mink, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private lemma mink_add_right (x y z : Fin n ⊕ Fin 1 → ℝ) :
    mink x (y + z) = mink x y + mink x z := by
  simp only [mink, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

private lemma mink_comm (x y : Fin n ⊕ Fin 1 → ℝ) : mink x y = mink y x := by
  have h : (∑ i : Fin n, x (Sum.inl i) * y (Sum.inl i)) =
      ∑ i : Fin n, y (Sum.inl i) * x (Sum.inl i) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp only [mink, h]
  ring

/-- Bilinearity expansion of `mink` on a two-dimensional linear combination. -/
private lemma mink_bilin (A B A' B' : ℝ) (P Q : Fin n ⊕ Fin 1 → ℝ) :
    mink (A • P + B • Q) (A' • P + B' • Q)
      = A * A' * mink P P + A * B' * mink P Q + B * A' * mink Q P + B * B' * mink Q Q := by
  simp only [mink_add_left, mink_add_right, mink_smul]
  ring

/-- Cancelling the normalisation factor `(sinh d)^{-1}`. -/
private lemma inv_sq_mul_sinh_sq (d c : ℝ) (hd : Real.sinh d ≠ 0) :
    (Real.sinh d)⁻¹ * (Real.sinh d)⁻¹ * -(Real.sinh d ^ 2 * c) = -c := by
  field_simp [hd]

private lemma mink_hlift (u v : E n) : mink (hlift u) (hlift v) = inner ℝ u v - tpart u * tpart v := by
  rw [mink, inner_eq_sum]
  simp only [hlift, Sum.elim_inl, Sum.elim_inr]

private lemma mink_hlift_self (u : E n) : mink (hlift u) (hlift u) = -1 := by
  rw [mink_hlift, real_inner_self_eq_norm_sq]
  have h := tpart_sq u
  nlinarith

private lemma neg_mink_hlift (a b : E n) :
    -mink (hlift a) (hlift b) = tpart a * tpart b - inner ℝ a b := by
  rw [mink_hlift]; ring

/-- A vector on the upper sheet of the hyperboloid is the lift of its spatial part. -/
private lemma hlift_spat_of_mink (y : Fin n ⊕ Fin 1 → ℝ) (hy : mink y y = -1)
    (hpos : 0 < y (Sum.inr 0)) : hlift (spat y) = y := by
  have hsum : (∑ i : Fin n, y (Sum.inl i) * y (Sum.inl i)) = y (Sum.inr 0) * y (Sum.inr 0) - 1 := by
    rw [mink] at hy
    linarith
  have hnorm : ‖spat y‖ ^ 2 = ∑ i : Fin n, y (Sum.inl i) * y (Sum.inl i) := by
    rw [norm_sq_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [spat]
  have hsq : y (Sum.inr 0) ^ 2 = 1 + ‖spat y‖ ^ 2 := by
    rw [hnorm, hsum]; ring
  have hsqrt : y (Sum.inr 0) = tpart (spat y) := by
    rw [tpart, ← hsq, Real.sqrt_sq (le_of_lt hpos)]
  funext z
  rcases z with i | j
  · simp [hlift, spat]
  · fin_cases j
    simp [hlift, hsqrt]

/-! ## Elementary facts about `hdist` -/

/-- Equality case of Cauchy–Schwarz in the chart: `tpart u * tpart v - ⟪u,v⟫ = 1` forces `u = v`. -/
private theorem cdist_eq_one {u v : E n} (h : tpart u * tpart v - inner ℝ u v = 1) : u = v := by
  have hkey : tpart u * tpart v = 1 + inner ℝ u v := by linarith
  have htw : tpart u * tpart v = Real.sqrt ((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) := by
    rw [tpart, tpart, Real.sqrt_mul (by positivity)]
  have hsq : (1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2) = (1 + inner ℝ u v) ^ 2 := by
    have h1 : Real.sqrt ((1 + ‖u‖ ^ 2) * (1 + ‖v‖ ^ 2)) = 1 + inner ℝ u v := by
      rw [← htw]; exact hkey
    rw [← h1, Real.sq_sqrt (by positivity)]
  obtain ⟨hle2, hle1⟩ := abs_le.mp (abs_real_inner_le_norm u v)
  have hiv : (inner ℝ u v) ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    have h1 : (inner ℝ u v - ‖u‖ * ‖v‖) ≤ 0 := by linarith
    have h2 : 0 ≤ inner ℝ u v + ‖u‖ * ‖v‖ := by linarith
    have h3 : (inner ℝ u v - ‖u‖ * ‖v‖) * (inner ℝ u v + ‖u‖ * ‖v‖) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg h1 h2
    nlinarith [h3]
  have hab : (‖u‖ - ‖v‖) ^ 2 = 0 := by nlinarith [hsq, hle1, hiv]
  have heq : ‖u‖ = ‖v‖ := sub_eq_zero.mp (sq_eq_zero_iff.mp hab)
  have hsq2 : (1 + inner ℝ u v) ^ 2 = (1 + ‖u‖ ^ 2) ^ 2 := by
    have hh := hsq
    rw [heq] at hh
    nlinarith [hh]
  have hp : 0 < 1 + inner ℝ u v := by
    rw [← hkey]; exact mul_pos (tpart_pos u) (tpart_pos v)
  have hq : 0 < 1 + ‖u‖ ^ 2 := by positivity
  have hi : inner ℝ u v = ‖u‖ * ‖v‖ := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with h' | h'
    · rw [heq]; linarith
    · exfalso; linarith
  have hinner : inner ℝ (u - v) (u - v) = 0 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [← real_inner_comm v u, hi, heq]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hinner)

/-- `hdist u v = 0` iff `u = v`. -/
private theorem hdist_zero_iff (u v : E n) : hdist u v = 0 ↔ u = v := by
  refine ⟨fun h0 => ?_, fun h => by rw [h, hdist_self]⟩
  refine cdist_eq_one ?_
  have hh := cosh_hdist u v
  rw [h0, Real.cosh_zero] at hh
  exact hh.symm

private theorem hdist_pos_of_ne {u v : E n} (h : u ≠ v) : 0 < hdist u v :=
  lt_of_le_of_ne (hdist_nonneg u v)
    (Ne.symm fun h0 => h ((hdist_zero_iff u v).mp h0))

private theorem sinh_hdist_ne_zero {u v : E n} (h : u ≠ v) : Real.sinh (hdist u v) ≠ 0 := by
  intro h0
  exact h ((hdist_zero_iff u v).mp (Real.sinh_eq_zero.mp h0))

/-! ## Pure hyperbolic-function identities -/

private lemma sinh_add_sq_aux (A B : ℝ) :
    Real.sinh (A + B) ^ 2 - Real.sinh A ^ 2 - Real.sinh B ^ 2
      = 2 * Real.cosh (A + B) * Real.sinh A * Real.sinh B := by
  rw [Real.sinh_add, Real.cosh_add]
  nlinarith [Real.cosh_sq A, Real.cosh_sq B]

private lemma seg_gram_aux (d B B' : ℝ) :
    Real.sinh (d - B) * Real.sinh (d - B') + Real.sinh B * Real.sinh B' +
      Real.cosh d * (Real.sinh (d - B) * Real.sinh B' + Real.sinh B * Real.sinh (d - B'))
      = Real.sinh d ^ 2 * Real.cosh (B - B') := by
  rw [Real.sinh_sub, Real.sinh_sub, Real.cosh_sub]
  linear_combination (-Real.sinh B * Real.sinh B') * (Real.cosh_sq_sub_sinh_sq d)

/-! ## The Minkowski pairing along the geodesic -/

/-- The Minkowski pairing of two points of the geodesic segment through two hyperboloid points:
if `⟨P,P⟩ = ⟨Q,Q⟩ = -1` and `⟨P,Q⟩ = -cosh d`, then the normalised interpolation at parameters
`s` and `t` has pairing `-cosh ((s-t) d)`.  (The hyperboloid form of the law of cosines.) -/
private theorem minkGeoSeg_aux {n : ℕ} (P Q : Fin n ⊕ Fin 1 → ℝ) (d s t : ℝ)
    (hP : mink P P = -1) (hQ : mink Q Q = -1)
    (hPQ : mink P Q = -Real.cosh d) (hd : d ≠ 0) :
    mink ((Real.sinh d)⁻¹ • (Real.sinh ((1 - s) * d) • P + Real.sinh (s * d) • Q))
      ((Real.sinh d)⁻¹ • (Real.sinh ((1 - t) * d) • P + Real.sinh (t * d) • Q))
      = -Real.cosh ((s - t) * d) := by
  have hs : Real.sinh d ≠ 0 := fun h0 => hd (Real.sinh_eq_zero.mp h0)
  have hQP : mink Q P = -Real.cosh d := by rw [mink_comm]; exact hPQ
  have hstep : mink ((Real.sinh d)⁻¹ • (Real.sinh ((1 - s) * d) • P + Real.sinh (s * d) • Q))
      ((Real.sinh d)⁻¹ • (Real.sinh ((1 - t) * d) • P + Real.sinh (t * d) • Q))
      = (Real.sinh d)⁻¹ * (Real.sinh d)⁻¹ *
        -(Real.sinh ((1 - s) * d) * Real.sinh ((1 - t) * d)
          + Real.sinh (s * d) * Real.sinh (t * d)
          + Real.cosh d * (Real.sinh ((1 - s) * d) * Real.sinh (t * d)
              + Real.sinh (s * d) * Real.sinh ((1 - t) * d))) := by
    rw [mink_smul, mink_bilin, hP, hQ, hPQ, hQP]
    ring
  rw [hstep]
  have h1 : (1 - s) * d = d - s * d := by ring
  have h2 : (1 - t) * d = d - t * d := by ring
  have h3 : s * d - t * d = (s - t) * d := by ring
  have hkey := seg_gram_aux d (s * d) (t * d)
  rw [h1, h2, ← h3, hkey, inv_sq_mul_sinh_sq d (Real.cosh (s * d - t * d)) hs]

private theorem geoSeg_pair {u v : E n} (h : u ≠ v) (s t : ℝ) :
    mink (geoVec u v s) (geoVec u v t) = -Real.cosh ((s - t) * hdist u v) := by
  have hd : 0 < hdist u v := hdist_pos_of_ne h
  have hPQ : mink (hlift u) (hlift v) = -Real.cosh (hdist u v) := by
    rw [mink_hlift, cosh_hdist]; ring
  have hseg := minkGeoSeg_aux (hlift u) (hlift v) (hdist u v) s t
    (mink_hlift_self u) (mink_hlift_self v) hPQ (ne_of_gt hd)
  rw [geoVec, if_neg h, geoVec, if_neg h]
  exact hseg

private theorem geoSeg_self {u v : E n} (h : u ≠ v) (s : ℝ) :
    mink (geoVec u v s) (geoVec u v s) = -1 := by
  rw [geoSeg_pair h s s, sub_self, zero_mul, Real.cosh_zero]

/-! ## `geoVec` is the lift of `geo` -/

/-- The time coordinate of the interpolation vector is positive on `[0,1]`. -/
private theorem geoVec_time_pos {u v : E n} (hd : 0 < hdist u v) {s : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) 1) : 0 < geoVec u v s (Sum.inr 0) := by
  have huv : u ≠ v := fun h => by rw [h, hdist_self] at hd; exact lt_irrefl 0 hd
  have htime : geoVec u v s (Sum.inr 0)
      = (Real.sinh (hdist u v))⁻¹ *
        (Real.sinh ((1 - s) * hdist u v) * tpart u + Real.sinh (s * hdist u v) * tpart v) := by
    rw [geoVec, if_neg huv]
    simp [hlift, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [htime]
  have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
  have hs0 : 0 ≤ s := hs.1
  have hB : 0 ≤ Real.sinh (s * hdist u v) :=
    Real.sinh_nonneg_iff.mpr (mul_nonneg hs0 (le_of_lt hd))
  have hsum : 0 < Real.sinh ((1 - s) * hdist u v) * tpart u +
      Real.sinh (s * hdist u v) * tpart v := by
    rcases lt_or_eq_of_le hs1 with hlt | heq
    · have hpos : 0 < Real.sinh ((1 - s) * hdist u v) :=
        Real.sinh_pos_iff.mpr (mul_pos (by linarith) hd)
      have h1 : 0 < Real.sinh ((1 - s) * hdist u v) * tpart u := mul_pos hpos (tpart_pos u)
      have h2 : 0 ≤ Real.sinh (s * hdist u v) * tpart v := mul_nonneg hB (le_of_lt (tpart_pos v))
      linarith
    · have hse : s = 1 := by linarith
      have hzero : Real.sinh ((1 - s) * hdist u v) = 0 := by
        rw [hse]; ring_nf; simp
      have hpos : 0 < Real.sinh (s * hdist u v) := by
        rw [hse, one_mul]; exact Real.sinh_pos_iff.mpr hd
      have h2 : 0 < Real.sinh (s * hdist u v) * tpart v := mul_pos hpos (tpart_pos v)
      rw [hzero, zero_mul, zero_add]
      exact h2
  exact mul_pos (inv_pos.mpr (Real.sinh_pos_iff.mpr hd)) hsum

theorem hlift_geoVec {u v : E n} (h : u ≠ v) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    hlift (geo u v s) = geoVec u v s := by
  have hd : 0 < hdist u v := hdist_pos_of_ne h
  have key := hlift_spat_of_mink (geoVec u v s) (geoSeg_self h s) (geoVec_time_pos hd hs)
  rw [show geo u v s = spat (geoVec u v s) from rfl]
  exact key

/-! ## Endpoints and the diagonal case -/

theorem geo_self (u : E n) (s : ℝ) : geo u u s = u := by
  rw [geo, geoVec, if_pos rfl]
  exact spat_hlift u

theorem geoVec_zero {u v : E n} (h : u ≠ v) : geoVec u v 0 = hlift u := by
  have hd := sinh_hdist_ne_zero h
  rw [geoVec, if_neg h, sub_zero, one_mul, zero_mul, Real.sinh_zero, zero_smul, add_zero,
    smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem geoVec_one {u v : E n} (h : u ≠ v) : geoVec u v 1 = hlift v := by
  have hd := sinh_hdist_ne_zero h
  rw [geoVec, if_neg h, sub_self, zero_mul, Real.sinh_zero, zero_smul, zero_add, one_mul,
    smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem geo_zero_of_ne {u v : E n} (h : u ≠ v) : geo u v 0 = u := by
  have h0 := hlift_geoVec h (s := 0) ⟨le_refl 0, zero_le_one⟩
  rw [geoVec_zero h] at h0
  exact hlift_injective h0

theorem geo_one_of_ne {u v : E n} (h : u ≠ v) : geo u v 1 = v := by
  have h1 := hlift_geoVec h (s := 1) ⟨zero_le_one, le_refl 1⟩
  rw [geoVec_one h] at h1
  exact hlift_injective h1

/-! ## The distance formula -/

private lemma arcosh_cosh_abs (x : ℝ) : Real.arcosh (Real.cosh x) = |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, Real.arcosh_cosh hx]
  · rw [abs_of_nonpos hx, ← Real.cosh_neg, Real.arcosh_cosh (neg_nonneg.mpr hx)]

theorem hdist_geo_of_ne {u v : E n} (h : u ≠ v) {s t : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    hdist (geo u v s) (geo u v t) = |s - t| * hdist u v := by
  have hls := hlift_geoVec h hs
  have hlt := hlift_geoVec h ht
  have hkey : -mink (hlift (geo u v s)) (hlift (geo u v t)) = Real.cosh ((s - t) * hdist u v) := by
    rw [hls, hlt, geoSeg_pair h s t, neg_neg]
  rw [hdist, ← neg_mink_hlift (geo u v s) (geo u v t), hkey, arcosh_cosh_abs, abs_mul,
    abs_of_nonneg (hdist_nonneg u v)]

/-! ## `geoSpec` -/

theorem geoSpec {n : ℕ} (u v : Submission.Mostow.E n) (s t : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Work.Mostow.geo u v 0 = u ∧ Work.Mostow.geo u v 1 = v ∧
      Submission.Mostow.hdist (Work.Mostow.geo u v s) (Work.Mostow.geo u v t)
        = |s - t| * Submission.Mostow.hdist u v := by
  rcases eq_or_ne u v with rfl | h
  · refine ⟨geo_self u 0, geo_self u 1, ?_⟩
    rw [geo_self u s, geo_self u t, hdist_self, mul_zero]
  · exact ⟨geo_zero_of_ne h, geo_one_of_ne h, hdist_geo_of_ne h hs ht⟩

end Work.Mostow
