import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.NumberTheory.Linnik.tentF1_laplace

open Complex
open scoped Interval

namespace Commons.NumberTheory.Linnik

private lemma norm_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x := by
  rw [norm_real]
  rw [Real.norm_eq_abs]
  exact abs_of_nonneg hx

private lemma denom_add_ge {x : ℝ} (hx : 0 ≤ x) (z : ℂ) : ‖z‖ - x ≤ ‖(x : ℂ) + z‖ := by
  have htri := norm_le_norm_add_norm_sub ((x : ℂ) + z) z
  have hz : ‖((x : ℂ) + z) - z‖ = x := by
    rw [show ((x : ℂ) + z) - z = (x : ℂ) by ring]
    exact norm_ofReal_nonneg hx
  rw [hz] at htri
  linarith

private lemma denom_sub_ge {x : ℝ} (hx : 0 ≤ x) (z : ℂ) : ‖z‖ - x ≤ ‖z - (x : ℂ)‖ := by
  have htri := norm_le_norm_add_norm_sub (z - (x : ℂ)) z
  have hz : ‖(z - (x : ℂ)) - z‖ = x := by
    rw [show (z - (x : ℂ)) - z = -(x : ℂ) by ring]
    rw [norm_neg]
    exact norm_ofReal_nonneg hx
  rw [hz] at htri
  linarith

private lemma denom_sq_ge {x : ℝ} (hx : 0 ≤ x) (z : ℂ) (h : x ≤ ‖z‖) :
    ‖z‖ ^ 2 - x ^ 2 ≤ ‖(x : ℂ) ^ 2 - z ^ 2‖ := by
  have htri := norm_le_norm_add_norm_sub (z ^ 2 - (x : ℂ) ^ 2) (z ^ 2)
  have hz : ‖(z ^ 2 - (x : ℂ) ^ 2) - z ^ 2‖ = x ^ 2 := by
    rw [show (z ^ 2 - (x : ℂ) ^ 2) - z ^ 2 = -((x : ℂ) ^ 2) by ring]
    rw [norm_neg]
    have hpow : ((x ^ 2 : ℝ) : ℂ) = (x : ℂ) ^ 2 := by norm_num
    rw [← hpow]
    exact norm_ofReal_nonneg (sq_nonneg x)
  have hnz : ‖z ^ 2‖ = ‖z‖ ^ 2 := by rw [norm_pow]
  have hnz2 : ‖z ^ 2 - (x : ℂ) ^ 2‖ = ‖(x : ℂ) ^ 2 - z ^ 2‖ := by
    exact norm_sub_rev (a := z ^ 2) (b := (x : ℂ) ^ 2)
  rw [hz, hnz, hnz2] at htri
  have hx2 : x ^ 2 ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg ‖z‖]
  linarith

private lemma norm_exp_real_mul (x K : ℝ) : ‖Complex.exp (x * (K : ℂ))‖ = Real.exp (x * K) := by
  rw [Complex.norm_exp]
  congr 1
  simp

private lemma norm_exp_neg_xK (x K : ℝ) : ‖Complex.exp (-(x * (K : ℂ)))‖ = Real.exp (-(x * K)) := by
  rw [Complex.norm_exp]
  congr 1
  simp

private lemma re_z_mul_ofReal {K : ℝ} {z : ℂ} : (z * (K : ℂ)).re = z.re * K := by
  rw [show z * (K : ℂ) = (K : ℂ) * z by ring]
  rw [Complex.re_ofReal_mul]
  ring

private lemma norm_exp_neg_zK_le_one {K : ℝ} (hK : 0 < K) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖Complex.exp (-(z * (K : ℂ)))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hle : (-(z * (K : ℂ))).re ≤ 0 := by
    calc
      (-(z * (K : ℂ))).re = -(z.re * K) := by
        rw [Complex.neg_re]
        congr 1
        exact re_z_mul_ofReal
      _ ≤ 0 := by
        nlinarith [mul_nonneg hz (le_of_lt hK)]
  have he := (Real.exp_le_exp).2 hle
  simpa using he

private lemma term1_norm_le {K x : ℝ} (hx : 0 < x) (z : ℂ) (hN : 2 * x ≤ ‖z‖) :
    ‖Complex.exp (x * (K : ℂ)) / ((x : ℂ) + z)‖ ≤ Real.exp (x * K) / (‖z‖ - x) := by
  have hpos : 0 < ‖z‖ - x := by nlinarith
  have hden := denom_add_ge (le_of_lt hx) z
  calc
    ‖Complex.exp (x * (K : ℂ)) / ((x : ℂ) + z)‖
        = ‖Complex.exp (x * (K : ℂ))‖ / ‖(x : ℂ) + z‖ := by rw [norm_div]
    _ ≤ Real.exp (x * K) / (‖z‖ - x) := by
        rw [norm_exp_real_mul]
        exact div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos (x * K))) hpos hden

private lemma term2_norm_le {K x : ℝ} (hx : 0 < x) (z : ℂ) (hN : 2 * x ≤ ‖z‖) :
    ‖Complex.exp (-(x * (K : ℂ))) / ((x : ℂ) - z)‖ ≤ Real.exp (-(x * K)) / (‖z‖ - x) := by
  have hpos : 0 < ‖z‖ - x := by nlinarith
  have hd1 := denom_sub_ge (le_of_lt hx) z
  have hden : ‖z‖ - x ≤ ‖(x : ℂ) - z‖ := by
    have hsym := norm_sub_rev (a := (x : ℂ)) (b := z)
    rw [hsym]
    exact hd1
  calc
    ‖Complex.exp (-(x * (K : ℂ))) / ((x : ℂ) - z)‖
        = ‖Complex.exp (-(x * (K : ℂ)))‖ / ‖(x : ℂ) - z‖ := by rw [norm_div]
    _ ≤ Real.exp (-(x * K)) / (‖z‖ - x) := by
        rw [norm_exp_neg_xK]
        exact div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos (-(x * K)))) hpos hden

private lemma term3_norm_le {K x : ℝ} (hK : 0 < K) (hx : 0 < x) (z : ℂ) (hz : 0 ≤ z.re)
    (hN : 2 * x ≤ ‖z‖) :
    ‖2 * (x : ℂ) * Complex.exp (-(z * (K : ℂ))) / (((x : ℂ) ^ 2 - z ^ 2))‖ ≤
      2 * x / (‖z‖ ^ 2 - x ^ 2) := by
  have hpos : 0 < ‖z‖ ^ 2 - x ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg ‖z‖]
  have hd1 := denom_sq_ge (le_of_lt hx) z (by nlinarith : x ≤ ‖z‖)
  have hnum_le : ‖2 * (x : ℂ) * Complex.exp (-(z * (K : ℂ)))‖ ≤ 2 * x := by
    calc
      ‖2 * (x : ℂ) * Complex.exp (-(z * (K : ℂ)))‖
          = ‖2 * (x : ℂ)‖ * ‖Complex.exp (-(z * (K : ℂ)))‖ := by rw [norm_mul]
      _ = ‖2 * (x : ℂ)‖ * Real.exp (-(z * (K : ℂ))).re := by rw [Complex.norm_exp]
      _ ≤ ‖2 * (x : ℂ)‖ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg (2 * (x : ℂ)))
          have harg : -(z * (K : ℂ)).re ≤ 0 := by
            calc
              (-(z * (K : ℂ))).re = -(z.re * K) := by
                rw [Complex.neg_re]
                congr 1
                exact re_z_mul_ofReal
              _ ≤ 0 := by nlinarith [mul_nonneg hz (le_of_lt hK)]
          have he := (Real.exp_le_exp).2 harg
          simpa using he
      _ = 2 * x := by
          have hnorm2x : ‖2 * (x : ℂ)‖ = 2 * x := by
            rw [show 2 * (x : ℂ) = ((2 * x : ℝ) : ℂ) by norm_num]
            rw [norm_ofReal_nonneg (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)) (le_of_lt hx))]
          rw [hnorm2x]
          ring
  have hdenpos : 0 < ‖((x : ℂ) ^ 2 - z ^ 2)‖ := lt_of_lt_of_le hpos hd1
  calc
    ‖2 * (x : ℂ) * Complex.exp (-(z * (K : ℂ))) / (((x : ℂ) ^ 2 - z ^ 2))‖
        = ‖2 * (x : ℂ) * Complex.exp (-(z * (K : ℂ)))‖ / ‖((x : ℂ) ^ 2 - z ^ 2)‖ := by
            rw [norm_div]
    _ ≤ (2 * x) / ‖((x : ℂ) ^ 2 - z ^ 2)‖ := by
            exact div_le_div₀ (by positivity : 0 ≤ 2 * x) hnum_le hdenpos le_rfl
    _ ≤ 2 * x / (‖z‖ ^ 2 - x ^ 2) := by
            exact div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * x) hpos hd1

private lemma h12 {n e1 : ℝ} (hnpos : 0 < n) :
    (1 / 2 : ℝ) * ((2 * e1) / n) ≤ e1 / n := by
  have hnne : n ≠ 0 := ne_of_gt hnpos
  field_simp [hnne]
  exact le_rfl

private lemma bound_aux {n x e1 e2 : ℝ} (hx : 0 < x) (hn2x : 2 * x ≤ n) (hn1 : 1 ≤ n)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    (1 / 2 : ℝ) * (e1 / (n - x) + e2 / (n - x) + 2 * x / (n ^ 2 - x ^ 2)) ≤
      (e1 + e2 + (4 / 3) * x) / n := by
  have hnpos : 0 < n := by nlinarith
  have hnne : n ≠ 0 := ne_of_gt hnpos
  have hnmx : 0 < n - x := by nlinarith
  have hdn : 0 < n ^ 2 - x ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg n]
  have h1 : (1 / 2 : ℝ) * (e1 / (n - x)) ≤ e1 / n := by
    have hA1 : e1 / (n - x) ≤ (2 * e1) / n := by
      rw [div_le_div_iff₀ hnmx hnpos]
      have hprod : 0 ≤ e1 * (n - 2 * x) := mul_nonneg he1 (by linarith)
      nlinarith
    have hm : (1 / 2 : ℝ) * (e1 / (n - x)) ≤ (1 / 2 : ℝ) * ((2 * e1) / n) :=
      mul_le_mul_of_nonneg_left hA1 (by norm_num)
    exact le_trans hm (h12 hnpos)
  have h2 : (1 / 2 : ℝ) * (e2 / (n - x)) ≤ e2 / n := by
    have hA2 : e2 / (n - x) ≤ (2 * e2) / n := by
      rw [div_le_div_iff₀ hnmx hnpos]
      have hprod : 0 ≤ e2 * (n - 2 * x) := mul_nonneg he2 (by linarith)
      nlinarith
    have hm : (1 / 2 : ℝ) * (e2 / (n - x)) ≤ (1 / 2 : ℝ) * ((2 * e2) / n) :=
      mul_le_mul_of_nonneg_left hA2 (by norm_num)
    exact le_trans hm (h12 hnpos)
  have h3 : (1 / 2 : ℝ) * (2 * x / (n ^ 2 - x ^ 2)) ≤ (4 / 3) * x / n := by
    have hxnn : 0 ≤ x := le_of_lt hx
    have hD : n ^ 2 - x ^ 2 ≥ (3 / 4) * n ^ 2 := by
      have h4x : 4 * x ^ 2 ≤ n ^ 2 := by
        have h1x : 0 ≤ n - 2 * x := by linarith
        have h2x : 0 ≤ n + 2 * x := by nlinarith
        have hp : 0 ≤ (n - 2 * x) * (n + 2 * x) := mul_nonneg h1x h2x
        nlinarith
      nlinarith
    have hrec : 1 / (n ^ 2 - x ^ 2) ≤ (4 / 3) / n ^ 2 := by
      rw [div_le_div_iff₀ hdn (sq_pos_of_pos hnpos)]
      nlinarith
    have hxrec : x / (n ^ 2 - x ^ 2) ≤ (4 / 3) * x / n ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hrec hxnn
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
    have h4n : (4 / 3) * x / n ^ 2 ≤ (4 / 3) * x / n := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hnpos) hnpos]
      have hmn : n ≤ n ^ 2 := by nlinarith [sq_nonneg n]
      exact mul_le_mul_of_nonneg_left hmn (by positivity : 0 ≤ (4 / 3) * x)
    calc
      (1 / 2 : ℝ) * (2 * x / (n ^ 2 - x ^ 2)) = x / (n ^ 2 - x ^ 2) := by
        field_simp [hdn.ne']
      _ ≤ (4 / 3) * x / n ^ 2 := hxrec
      _ ≤ (4 / 3) * x / n := h4n
  have hsumL : (1 / 2 : ℝ) * (e1 / (n - x) + e2 / (n - x) + 2 * x / (n ^ 2 - x ^ 2)) =
      (1 / 2 : ℝ) * (e1 / (n - x)) + (1 / 2 : ℝ) * (e2 / (n - x)) +
        (1 / 2 : ℝ) * (2 * x / (n ^ 2 - x ^ 2)) := by
        ring
  have hsumR : e1 / n + e2 / n + (4 / 3) * x / n = (e1 + e2 + (4 / 3) * x) / n := by
        field_simp [hnne]
  rw [hsumL, ← hsumR]
  exact add_le_add (add_le_add h1 h2) h3

private lemma norm_half : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
  norm_num

private lemma integral_bound {K x : ℝ} (hK : 0 < K) (hx : 0 < x) (z : ℂ)
    (hz : 0 ≤ z.re) (hN1 : 1 ≤ ‖z‖) (hN2 : 2 * x ≤ ‖z‖) :
    ‖(∫ u in (0 : ℝ)..(K : ℝ), Complex.exp (-(z * (u : ℂ))) * ((Real.sinh ((K - u) * x) : ℝ) : ℂ))‖ ≤
      (Real.exp (x * K) + Real.exp (-(x * K)) + (4 / 3) * x) / ‖z‖ := by
  have hz1 : z ≠ (x : ℂ) := by
    intro h
    have hnorm : ‖z‖ = x := by
      calc ‖z‖ = ‖(x : ℂ)‖ := by rw [h]
           _ = x := norm_ofReal_nonneg (le_of_lt hx)
    nlinarith
  have hz2 : z ≠ -(x : ℂ) := by
    intro h
    have hnorm : ‖z‖ = ‖(x : ℂ)‖ := by rw [h]; simp
    have hnorm' : ‖z‖ = x := by
      calc ‖z‖ = ‖(x : ℂ)‖ := hnorm
           _ = x := norm_ofReal_nonneg (le_of_lt hx)
    nlinarith
  rw [tentF1_laplace hK x hx z hz1 hz2]
  set A : ℂ := Complex.exp (x * (K : ℂ)) / ((x : ℂ) + z)
  set B : ℂ := Complex.exp (-(x * (K : ℂ))) / ((x : ℂ) - z)
  set C : ℂ := 2 * (x : ℂ) * Complex.exp (-(z * (K : ℂ))) / (((x : ℂ) ^ 2 - z ^ 2))
  let S : ℂ := A + B - C
  let n : ℝ := ‖z‖
  let e1 : ℝ := Real.exp (x * K)
  let e2 : ℝ := Real.exp (-(x * K))
  have htriA : ‖A + B - C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
    have h1 : ‖(A + B) - C‖ ≤ ‖A + B‖ + ‖C‖ := norm_sub_le (A + B) C
    have h2 : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le A B
    linarith
  have hscal : ‖(1 / 2 : ℂ) * S‖ = (1 / 2 : ℝ) * ‖S‖ := by
    rw [norm_mul, norm_half]
  have hA := term1_norm_le (K := K) hx z hN2
  have hB := term2_norm_le (K := K) hx z hN2
  have hC := term3_norm_le hK hx z hz hN2
  have hsumN : ‖A‖ + ‖B‖ + ‖C‖ ≤ e1 / (n - x) + e2 / (n - x) + 2 * x / (n ^ 2 - x ^ 2) := by
    dsimp [A, B, C, n, e1, e2]
    exact add_le_add (add_le_add hA hB) hC
  have hb := bound_aux hx hN2 hN1 (by exact le_of_lt (Real.exp_pos (x * K)))
    (by exact le_of_lt (Real.exp_pos (-(x * K))))
  have hT1 : ‖(1 / 2 : ℂ) * S‖ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖B‖ + ‖C‖) := by
    calc
      ‖(1 / 2 : ℂ) * S‖ = (1 / 2 : ℝ) * ‖S‖ := hscal
      _ = (1 / 2 : ℝ) * ‖A + B - C‖ := by rfl
      _ ≤ (1 / 2 : ℝ) * (‖A‖ + ‖B‖ + ‖C‖) := by
          exact mul_le_mul_of_nonneg_left htriA (by norm_num)
  have hT2 : (1 / 2 : ℝ) * (‖A‖ + ‖B‖ + ‖C‖) ≤
      (1 / 2 : ℝ) * (e1 / (n - x) + e2 / (n - x) + 2 * x / (n ^ 2 - x ^ 2)) := by
    exact mul_le_mul_of_nonneg_left hsumN (by norm_num)
  have hb' : (1 / 2 : ℝ) * (e1 / (n - x) + e2 / (n - x) + 2 * x / (n ^ 2 - x ^ 2)) ≤
      (e1 + e2 + (4 / 3) * x) / n := by
    simpa [n, e1, e2] using hb
  exact le_trans (le_trans hT1 hT2) hb'

theorem tentF1_decay {K : ℝ} (hK : 0 < K) (x : ℝ) (hx : 0 < x) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 ≤ z.re → R ≤ ‖z‖ →
      ‖∫ u in (0 : ℝ)..(K : ℝ),
          Complex.exp (-(z * (u : ℂ))) * ((Real.sinh ((K - u) * x) : ℝ) : ℂ)‖ < ε := by
  intro ε hε
  let D : ℝ := Real.exp (x * K) + Real.exp (-(x * K)) + (4 / 3) * x
  let R : ℝ := max (2 * x) (max 1 (2 * D / ε))
  refine ⟨R, ?_⟩
  intro z hz hzR
  have hN2 : 2 * x ≤ ‖z‖ := le_trans (le_max_left (2 * x) (max 1 (2 * D / ε))) hzR
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact le_trans (le_max_left 1 (2 * D / ε)) (le_max_right (2 * x) (max 1 (2 * D / ε)))
  have hN1 : 1 ≤ ‖z‖ := le_trans hR1 hzR
  have hRD : 2 * D / ε ≤ ‖z‖ := by
    have h1 : 2 * D / ε ≤ max 1 (2 * D / ε) := le_max_right 1 (2 * D / ε)
    have h2 : max 1 (2 * D / ε) ≤ R := by
      dsimp [R]
      exact le_max_right (2 * x) (max 1 (2 * D / ε))
    exact le_trans (le_trans h1 h2) hzR
  have hb := integral_bound hK hx z hz hN1 hN2
  have hzpos : 0 < ‖z‖ := by linarith
  have h2D : 2 * D ≤ ‖z‖ * ε := by
    have hm : (2 * D / ε) * ε ≤ ‖z‖ * ε := mul_le_mul_of_nonneg_right hRD (le_of_lt hε)
    have hfield : (2 * D / ε) * ε = 2 * D := by
      field_simp [ne_of_gt hε]
    rwa [hfield] at hm
  have hle : D / ‖z‖ ≤ ε / 2 := by
    rw [div_le_div_iff₀ hzpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [h2D]
  have hlt : ε / 2 < ε := by linarith
  have hbD : ‖(∫ u in (0 : ℝ)..(K : ℝ),
      Complex.exp (-(z * (u : ℂ))) * ((Real.sinh ((K - u) * x) : ℝ) : ℂ))‖ ≤ D / ‖z‖ := by
    simpa [D] using hb
  exact lt_of_le_of_lt (le_trans hbD hle) hlt

end Commons.NumberTheory.Linnik