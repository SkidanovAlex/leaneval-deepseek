import Mathlib
import Submission.Work.Analysis.IonescuWainger.iwP_element_le

/-!
# Separation of the Ionescu–Wainger arithmetic frequency set `(ℚ/ℤ)_{≤l}`

Appendix A of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages* (Annals of Math. 195 (2022)), needs two pieces of information about the
arithmetic frequency set `(ℚ/ℤ)_{≤l}`: that it is small (a cardinality bound, the sibling module
`iw_height_card_le`) and that its elements are *well separated* (this file, the lemma
`iw_height_separated`).

The separation statement is elementary once the element bound `iwP_element_le` is available.
Indeed, an element of `(ℚ/ℤ)_{≤l}` is a rational point `a/q` with `q ∈ P_{≤l}`, and `1/(qq')`
bounds the distance between the classes of `a/q` and `b/q'`: in the normed group
`Circle = ℝ ⧸ ℤ` this is exactly the statement

`1 / (q * q') ≤ ‖(a/q : Circle) - (b/q' : Circle)‖`   for `q, q' > 0` and `a/q ≠ b/q'`,

which follows from `AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder`: a non-zero torsion
point `u` of order dividing `Q` satisfies `1 ≤ Q * ‖u‖`.  Since each element of `P_{≤l}` is at
most `2^{C 2^{ρl}}`, two distinct elements of `(ℚ/ℤ)_{≤l}` are separated by
`2^{-2C 2^{ρl}}`.

## Main result

* `Work.Analysis.IonescuWainger.iw_height_separated`
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

/-! ## The circle `ℝ ⧸ ℤ` and its integral points -/

/-- An integer, viewed in the circle `Circle = ℝ ⧸ ℤ`, is zero. -/
private lemma intCast_circle_eq_zero (n : ℤ) : ((n : ℝ) : Circle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simp⟩

/-- A natural number, viewed in the circle `Circle = ℝ ⧸ ℤ`, is zero. -/
private lemma natCast_circle_eq_zero (n : ℕ) : ((n : ℝ) : Circle) = 0 := by
  simpa using intCast_circle_eq_zero (n : ℤ)

/-- The rational point `a/q` of the circle is killed by `q`, for `q ≠ 0`. -/
private lemma nsmul_rat_circle_eq_zero (q : ℕ) (hq : q ≠ 0) (a : ℕ) :
    q • (((a : ℝ) / (q : ℝ)) : Circle) = 0 := by
  have hqR : ((q : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hdiv : ((a : ℝ) / (q : ℝ)) = (q : ℝ)⁻¹ * (a : ℝ) := by rw [div_eq_inv_mul]
  rw [hdiv, ← AddCircle.coe_nsmul (p := (1 : ℝ)), nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hqR, one_mul]
  exact natCast_circle_eq_zero a

/-- Every element of `(ℚ/ℤ)_{≤l}` is killed by some positive denominator from `P_{≤l}`. -/
lemma iwArithFreqs_exists_den {ρ : ℝ} {l : ℕ} {α : Circle} (hα : α ∈ iwArithFreqs ρ l) :
    ∃ q : ℕ, 0 < q ∧ q ∈ iwP ρ l ∧ q • α = 0 := by
  simp only [iwArithFreqs, Finset.mem_biUnion, Finset.mem_image] at hα
  obtain ⟨q, hqP, a, -, ha⟩ := hα
  exact ⟨q, pos_of_mem_iwP hqP, hqP,
    by rw [← ha]; exact nsmul_rat_circle_eq_zero q (pos_of_mem_iwP hqP).ne' a⟩

/-! ## Separation of torsion points of `ℝ ⧸ ℤ` -/

/-- A non-zero point of `Circle = ℝ ⧸ ℤ` killed by `Q ≠ 0` has norm at least `1/Q`. -/
private lemma separation_aux {Q : ℕ} (hQ : Q ≠ 0) {u : Circle} (hu : u ≠ 0)
    (h : Q • u = 0) : (1 : ℝ) / (Q : ℝ) ≤ ‖u‖ := by
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ
  have hfin : IsOfFinAddOrder u :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨Q, hQpos, h⟩
  have hle := AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder (p := (1 : ℝ)) hfin hu
  rw [nsmul_eq_mul] at hle
  have hdvd : addOrderOf u ∣ Q := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
  have hleQ : ((addOrderOf u : ℕ) : ℝ) ≤ (Q : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hQpos hdvd
  have hnorm_nn : (0 : ℝ) ≤ ‖u‖ := norm_nonneg _
  have hmul : (1 : ℝ) ≤ (Q : ℝ) * ‖u‖ :=
    le_trans hle (mul_le_mul_of_nonneg_right hleQ hnorm_nn)
  rw [div_le_iff₀ (by exact_mod_cast hQpos)]
  linarith [hmul]

/-- Two distinct points of `Circle = ℝ ⧸ ℤ` killed by `q` and `q'` respectively are separated by
`1/(q q')`. -/
private lemma separation_of_killing {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q') {α β : Circle}
    (hα : q • α = 0) (hβ : q' • β = 0) (hne : α ≠ β) :
    (1 : ℝ) / ((q * q' : ℕ) : ℝ) ≤ ‖α - β‖ := by
  refine separation_aux (Nat.mul_ne_zero hq.ne' hq'.ne') (sub_ne_zero.mpr hne) ?_
  have h1 : (q * q') • α = 0 := by rw [mul_smul, smul_comm q q' α, hα, smul_zero]
  have h2 : (q * q') • β = 0 := by rw [mul_smul, hβ, smul_zero]
  rw [smul_sub, h1, h2, sub_self]

/-- **Separation of the Ionescu–Wainger arithmetic frequency set.**  Two distinct elements of
`(ℚ/ℤ)_{≤l}` are at distance at least `2^{-C 2^{ρ l}}` in `ℝ ⧸ ℤ`. -/
theorem iw_height_separated {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ l ⦃α β : Circle⦄, α ∈ iwArithFreqs ρ l → β ∈ iwArithFreqs ρ l → α ≠ β →
      (2 : ℝ) ^ (-(C * (2 : ℝ) ^ (ρ * (l : ℝ)))) ≤ ‖α - β‖ := by
  obtain ⟨K, hKpos, hKelem⟩ := iwP_element_le hρ
  refine ⟨2 * K + 1, by linarith, ?_⟩
  intro l α β hα hβ hne
  obtain ⟨q, hqpos, hqP, hqα⟩ := iwArithFreqs_exists_den hα
  obtain ⟨q', hq'pos, hq'P, hq'β⟩ := iwArithFreqs_exists_den hβ
  set S : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ)) with hS
  have hSnn : 0 ≤ S := by rw [hS]; positivity
  have hqb : (q : ℝ) ≤ (2 : ℝ) ^ (K * S) := by rw [hS]; exact hKelem l q hqP
  have hq'b : (q' : ℝ) ≤ (2 : ℝ) ^ (K * S) := by rw [hS]; exact hKelem l q' hq'P
  have hQb : ((q * q' : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((2 * K) * S) := by
    rw [Nat.cast_mul]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (K * S) := Real.rpow_pos_of_pos (by norm_num) _
    calc (q : ℝ) * (q' : ℝ)
        ≤ (2 : ℝ) ^ (K * S) * (2 : ℝ) ^ (K * S) :=
          mul_le_mul hqb hq'b (by positivity) hpos.le
      _ = (2 : ℝ) ^ ((2 * K) * S) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 1; ring
  have hposQ : (0 : ℝ) < ((q * q' : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hqpos hq'pos
  have hkey : (2 : ℝ) ^ (-((2 * K) * S)) ≤ (1 : ℝ) / ((q * q' : ℕ) : ℝ) := by
    rw [Real.rpow_neg (by norm_num), inv_eq_one_div]
    exact one_div_le_one_div_of_le hposQ hQb
  have hexp : -((2 * K + 1) * S) ≤ -((2 * K) * S) := by
    have : (2 * K) * S ≤ (2 * K + 1) * S := by nlinarith [hSnn]
    linarith
  have hstep := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hexp
  calc (2 : ℝ) ^ (-((2 * K + 1) * S)) ≤ (2 : ℝ) ^ (-((2 * K) * S)) := hstep
    _ ≤ (1 : ℝ) / ((q * q' : ℕ) : ℝ) := hkey
    _ ≤ ‖α - β‖ := separation_of_killing hqpos hq'pos hqα hq'β hne

end Work.Analysis.IonescuWainger
