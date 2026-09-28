import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.gcd_sum

/-!
# Auxiliary lemmas for `Work.HP.MDEstimates.mu_sum_bound`

Self-contained elementary facts used in the proof of `mu_sum_bound`:

* `isPrim_ne_zero` : the zero vector is not primitive;
* `linIndep_of_ne_pm` : two primitive vectors with `x ≠ ±y` are `ℤ`-linearly independent
  (needed because `Omega d n B` only records primitivity and `x ≠ ±y`);
* `muXY_le_split` : `μ(x,y) ≤ 3n²(𝔡₂/𝔡₃ + ‖x‖‖y‖/𝔡₂²)`, the trivial bound by the sum of the
  two terms inside the maximum.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset
open scoped BigOperators

namespace Work.HP.MDEstimates

/-- The zero vector is not primitive. -/
lemma isPrim_ne_zero {n : ℕ} {v : Fin (n + 1) → ℤ} (hv : IsPrim v) : v ≠ 0 := by
  intro h
  have h1 : Finset.univ.gcd v = 1 := hv
  have h2 : Finset.univ.gcd v = 0 := by
    rw [Finset.gcd_eq_zero_iff]
    intro i _
    simp [h]
  rw [h1] at h2
  exact one_ne_zero h2

/-- Two primitive vectors with `x ≠ ±y` are `ℤ`-linearly independent. -/
theorem linIndep_of_ne_pm {n : ℕ} {x y : Fin (n + 1) → ℤ}
    (hx : IsPrim x) (hy : IsPrim y) (hxy : x ≠ y) (hxy' : x ≠ -y) :
    LinearIndependent ℤ ![x, y] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 : c 0 • x + c 1 • y = 0 := by
    have h := hc
    rw [Fin.sum_univ_two] at h
    simpa using h
  have hci : ∀ i, c 0 * x i + c 1 * y i = 0 := by
    intro i
    have h := congrFun h0 i
    simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  have hx0 : x ≠ 0 := isPrim_ne_zero hx
  have hy0 : y ≠ 0 := isPrim_ne_zero hy
  obtain ⟨ix, hix⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (funext fun i => by simpa using hcon i)
  obtain ⟨iy, hiy⟩ : ∃ i, y i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hy0 (funext fun i => by simpa using hcon i)
  have key : ∀ {d : ℤ} {w : Fin (n + 1) → ℤ}, (∀ i, d * w i = 0) → (∃ i, w i ≠ 0) → d = 0 := by
    intro d w hdw hwit
    obtain ⟨i, hi⟩ := hwit
    exact (mul_eq_zero.mp (hdw i)).resolve_right hi
  by_cases hc0 : c 0 = 0
  · have hc1 : c 1 = 0 := by
      refine key (d := c 1) (w := y) (fun i => ?_) ⟨iy, hiy⟩
      have h := hci i
      rw [hc0] at h
      simpa only [zero_mul, zero_add] using h
    intro j
    fin_cases j
    · simpa using hc0
    · simpa using hc1
  · have hc1 : c 1 ≠ 0 := by
      intro h1
      refine hc0 (key (d := c 0) (w := x) (fun i => ?_) ⟨ix, hix⟩)
      have h := hci i
      rw [h1] at h
      simpa only [zero_mul, add_zero] using h
    obtain ⟨u, hu⟩ := gcd_sum x
    have hu1 : ∑ i, u i * x i = 1 := by rw [hu, hx]
    obtain ⟨v, hv⟩ := gcd_sum y
    have hv1 : ∑ i, v i * y i = 1 := by rw [hv, hy]
    have hbez : ∀ w : Fin (n + 1) → ℤ,
        (∑ i, w i * x i) * c 0 + (∑ i, w i * y i) * c 1 = 0 := by
      intro w
      have hzero : ∑ i, w i * (c 0 * x i + c 1 * y i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hci i, mul_zero]
      have hid : ∑ i, w i * (c 0 * x i + c 1 * y i)
          = ∑ i, (w i * x i * c 0 + w i * y i * c 1) :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [hid, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul] at hzero
      exact hzero
    have hdiv1 : c 1 ∣ c 0 := by
      refine ⟨-(∑ i, u i * y i), ?_⟩
      have h := hbez u
      simp only [hu1, one_mul] at h
      linear_combination h
    have hdiv2 : c 0 ∣ c 1 := by
      refine ⟨-(∑ i, v i * x i), ?_⟩
      have h := hbez v
      simp only [hv1, one_mul] at h
      linear_combination h
    obtain ⟨k, hk⟩ := hdiv1
    obtain ⟨l, hl⟩ := hdiv2
    have hkl : k * l = 1 := by
      have hcalc : c 1 = c 1 * (k * l) := by
        calc c 1 = c 0 * l := hl
          _ = (c 1 * k) * l := by rw [hk]
          _ = c 1 * (k * l) := by ring
      have h1' : c 1 * (k * l) = c 1 * 1 := by
        rw [mul_one]
        exact hcalc.symm
      exact mul_left_cancel₀ hc1 h1'
    have hkpm : k = 1 ∨ k = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hkl
    have hxy_eq : x = y ∨ x = -y := by
      rcases hkpm with hk1 | hkm1
      · right
        funext i
        have h := hci i
        have hc1' : c 1 = c 0 := by
          have h0 := hk
          rw [hk1, mul_one] at h0
          omega
        rw [hc1'] at h
        have : c 0 * x i = c 0 * (-y i) := by
          rw [mul_neg]
          linarith
        exact mul_left_cancel₀ hc0 this
      · left
        funext i
        have h := hci i
        have hc1' : c 1 = -c 0 := by
          have h0 := hk
          rw [hkm1, mul_neg_one] at h0
          omega
        rw [hc1'] at h
        have : c 0 * x i = c 0 * y i := by
          rw [neg_mul] at h
          linarith
        exact mul_left_cancel₀ hc0 this
    rcases hxy_eq with h | h
    · exact absurd h hxy
    · exact absurd h hxy'

/-- `μ(x,y)` is at most `3n²` times the sum of the two terms of the maximum. -/
lemma muXY_le_split (n : ℕ) {x y : Fin (n + 1) → ℤ}
    (hA : 0 ≤ dmin 2 {x, y} / dmin 3 {x, y})
    (hB : 0 ≤ eNorm x * eNorm y / dmin 2 {x, y} ^ 2) :
    muXY n x y ≤ 3 * (n : ℝ) ^ 2 * (dmin 2 {x, y} / dmin 3 {x, y} +
      eNorm x * eNorm y / dmin 2 {x, y} ^ 2) := by
  unfold muXY
  exact mul_le_mul_of_nonneg_left (max_le_add_of_nonneg hA hB) (by positivity)

end Work.HP.MDEstimates
