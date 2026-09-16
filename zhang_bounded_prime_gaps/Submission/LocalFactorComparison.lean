import Mathlib
import Submission.FiniteEuler

open scoped BigOperators Topology
open Filter

/-!
# P8 Lemma 4.1 (40): the per-prime local-factor comparison, k = 1

From the finite Euler-product factorization (`Submission.FiniteEuler`) the
single-coordinate (`k = 1`) local factor at a prime `p` is
`K_p = 1 − p^{−1−a} − p^{−1−b} + p^{−1−a−b}`, with `a := (1+iξ)/log x`,
`b := (1+iξ′)/log x` in the application and the `−1` in each exponent coming
from the `1/[d,d′]` denominator.  Polymath8a (40) compares it with the ratio
form `R_p := (1−p^{−1−a})(1−p^{−1−b})/(1−p^{−1−a−b})`, `K_p = (1+O(p⁻²))·R_p`.

This module proves the k=1 comparison with explicit constants, over any
`a, b : ℂ` with non-negative real part (which is all the application needs,
since `Re a = Re b = 1/log x > 0`):
`‖K_p − R_p‖ ≤ 8/p²` (absolute) and `‖K_p/R_p − 1‖ ≤ 48/p²` (the
`1 + O(p⁻²)` form).  The general-k factor is then obtained by multiplying
these per-prime estimates (together with the convergence of
`∏_p (1+O(p⁻²))`) — a later step; this file is the single-prime core.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The per-prime local factor `K_p` for one coordinate (k = 1):
`1 − p^{−1−a} − p^{−1−b} + p^{−1−a−b}`. -/
noncomputable def locK (p : ℕ) (a b : ℂ) : ℂ :=
  1 - (p : ℂ) ^ (-(1 + a)) - (p : ℂ) ^ (-(1 + b)) + (p : ℂ) ^ (-(1 + a + b))

/-- The ratio form of the local factor (P8 (40) with k = 1):
`R_p = (1−p^{−1−a})(1−p^{−1−b})/(1−p^{−1−a−b})`. -/
noncomputable def locR (p : ℕ) (a b : ℂ) : ℂ :=
  ((1 - (p : ℂ) ^ (-(1 + a))) * (1 - (p : ℂ) ^ (-(1 + b)))) /
    (1 - (p : ℂ) ^ (-(1 + a + b)))

/-- Exact modulus of `(p:ℂ)^z` for `p ≠ 0`: `‖(p:ℂ)^z‖ = (p:ℝ) ^ z.re`. -/
lemma norm_cpow_nat_eq {p : ℕ} (hp : p ≠ 0) (z : ℂ) :
    ‖(p : ℂ) ^ z‖ = (p : ℝ) ^ z.re := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) :=
    (Complex.ofReal_log (by exact_mod_cast (by omega : 0 ≤ p))).symm
  have hmain : (p : ℂ) ^ z = Complex.exp ((Real.log (p : ℝ) : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero hpC, hlog]
  rw [hmain, Complex.norm_exp]
  have hzre : (((Real.log (p : ℝ) : ℂ) * z).re) = Real.log (p : ℝ) * z.re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hzre]
  exact (Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < p)) z.re).symm

/-- For `p ≥ 2` and `1 ≤ s.re`, `‖(p:ℂ)^(-s)‖ ≤ 1/p`. -/
lemma norm_cpow_neg_le_inv {p : ℕ} (hp2 : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ (p : ℝ)⁻¹ := by
  have hz : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s).re := norm_cpow_nat_eq (by omega : p ≠ 0) (-s)
  rw [hz, Complex.neg_re]
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
  have hle : -s.re ≤ -1 := by linarith
  have hmul : Real.log (p : ℝ) * (-s.re) ≤ Real.log (p : ℝ) * (-1) := by
    exact mul_le_mul_of_nonneg_left hle hlogp
  have hb : Real.exp (Real.log (p : ℝ) * (-s.re)) ≤ Real.exp (Real.log (p : ℝ) * (-1)) :=
    Real.exp_le_exp.mpr hmul
  have he1 : Real.exp (Real.log (p : ℝ) * (-1)) = (p : ℝ)⁻¹ := by
    have hring : Real.log (p : ℝ) * (-1) = -Real.log (p : ℝ) := by ring
    rw [hring, Real.exp_neg, Real.exp_log (by exact_mod_cast (by omega : 0 < p))]
  have hrpow : (p : ℝ) ^ (-s.re) = Real.exp (Real.log (p : ℝ) * (-s.re)) :=
    Real.rpow_def_of_pos (by exact_mod_cast (by omega : 0 < p)) (-s.re)
  rw [hrpow]
  exact hb.trans (by rw [he1])

/-- Product form of `cpow_add`: `x^y · x^z = x^(y+z)` for `x ≠ 0`. -/
lemma cpow_sum {x : ℂ} (hx : x ≠ 0) (y z : ℂ) : x ^ y * x ^ z = x ^ (y + z) :=
  (Complex.cpow_add y z hx).symm

/-- The two `1/[d,d′]`-denominator exponents merge: `p^{−1−a}·p^{−1−b} =
p^{−1−a−b}·p^{−1}`. -/
lemma cpow_negOneAdd_mul {p : ℕ} {a b : ℂ} (hp0 : (p : ℂ) ≠ 0) :
    (p : ℂ) ^ (-(1 + a)) * (p : ℂ) ^ (-(1 + b)) =
      (p : ℂ) ^ (-(1 + a + b)) * (p : ℂ)⁻¹ := by
  calc
    (p : ℂ) ^ (-(1 + a)) * (p : ℂ) ^ (-(1 + b))
        = (p : ℂ) ^ (-(1 + a) + -(1 + b)) := cpow_sum hp0 (-(1 + a)) (-(1 + b))
    _ = (p : ℂ) ^ (-(1 + a + b) + -1) := by congr 1; ring
    _ = (p : ℂ) ^ (-(1 + a + b)) * (p : ℂ) ^ (-1) := (cpow_sum hp0 (-(1 + a + b)) (-1)).symm
    _ = (p : ℂ) ^ (-(1 + a + b)) * (p : ℂ)⁻¹ := by
            rw [Complex.cpow_neg_one]

/-- Exact difference between the ratio form `R_p` and the local factor `K_p`. -/
lemma locR_sub_locK {p : ℕ} (a b : ℂ) (hp0 : (p : ℂ) ≠ 0)
    (hden : 1 - (p : ℂ) ^ (-(1 + a + b)) ≠ 0) :
    locR p a b - locK p a b =
      ((p : ℂ) ^ (-(1 + a + b))) *
        ((p : ℂ)⁻¹ - (p : ℂ) ^ (-(1 + a)) - (p : ℂ) ^ (-(1 + b)) +
          (p : ℂ) ^ (-(1 + a + b))) / (1 - (p : ℂ) ^ (-(1 + a + b))) := by
  classical
  let u : ℂ := (p : ℂ) ^ (-(1 + a))
  let v : ℂ := (p : ℂ) ^ (-(1 + b))
  let w : ℂ := (p : ℂ) ^ (-(1 + a + b))
  have huvw : u * v = w * (p : ℂ)⁻¹ := by
    dsimp [u, v, w]
    exact cpow_negOneAdd_mul hp0
  have hw : 1 - w ≠ 0 := by simpa [w] using hden
  calc
    locR p a b - locK p a b
        = ((1 - u) * (1 - v)) / (1 - w) - (1 - u - v + w) := by
            simp [locR, locK, u, v, w]
    _ = ((1 - u) * (1 - v) - (1 - u - v + w) * (1 - w)) / (1 - w) := by
            field_simp [hw]
    _ = (w * ((p : ℂ)⁻¹ - u - v + w)) / (1 - w) := by
            have hnum : (1 - u) * (1 - v) - (1 - u - v + w) * (1 - w) =
                w * ((p : ℂ)⁻¹ - u - v + w) := by
              calc
                (1 - u) * (1 - v) - (1 - u - v + w) * (1 - w)
                    = u * v - u * w - v * w + w ^ 2 := by ring
                _ = w * ((p : ℂ)⁻¹ - u - v + w) := by rw [huvw]; ring
            rw [hnum]
    _ = w * ((p : ℂ)⁻¹ - u - v + w) / (1 - w) := by ring
    _ = ((p : ℂ) ^ (-(1 + a + b))) *
        ((p : ℂ)⁻¹ - (p : ℂ) ^ (-(1 + a)) - (p : ℂ) ^ (-(1 + b)) +
          (p : ℂ) ^ (-(1 + a + b))) / (1 - (p : ℂ) ^ (-(1 + a + b))) := by
            simp [u, v, w]



/-- **Consistency with `FiniteEuler` naming.**  The k=1 local factor `locK` is
exactly the `pairLocal` local factor of the finite Euler-product factorization
(`Submission.FiniteEuler`) at the divisor-weight values
`x_p := p^{−a}`, `y_p := p^{−b}`, `z_p := p^{−1}` (the `1/[d,d′]`
denominator per prime):  `locK p a b = pairLocal x y z p`. -/
theorem locK_eq_pairLocal_cpow (p : ℕ) (a b : ℂ) (hp0 : (p : ℂ) ≠ 0) :
    locK p a b =
      pairLocal (R := ℂ) (ι := ℕ)
        (x := fun q : ℕ => (q : ℂ) ^ (-a))
        (y := fun q : ℕ => (q : ℂ) ^ (-b))
        (z := fun q : ℕ => (q : ℂ) ^ (-1 : ℂ)) p := by
  have hx : (p : ℂ) ^ (-a) * (p : ℂ) ^ (-1 : ℂ) = (p : ℂ) ^ (-(1 + a)) := by
    calc
      (p : ℂ) ^ (-a) * (p : ℂ) ^ (-1 : ℂ) = (p : ℂ) ^ (-a + -1) := cpow_sum hp0 (-a) (-1 : ℂ)
      _ = (p : ℂ) ^ (-(1 + a)) := by congr 1; ring
  have hy : (p : ℂ) ^ (-b) * (p : ℂ) ^ (-1 : ℂ) = (p : ℂ) ^ (-(1 + b)) := by
    calc
      (p : ℂ) ^ (-b) * (p : ℂ) ^ (-1 : ℂ) = (p : ℂ) ^ (-b + -1) := cpow_sum hp0 (-b) (-1 : ℂ)
      _ = (p : ℂ) ^ (-(1 + b)) := by congr 1; ring
  have hz : (p : ℂ) ^ (-a) * (p : ℂ) ^ (-b) * (p : ℂ) ^ (-1 : ℂ) = (p : ℂ) ^ (-(1 + a + b)) := by
    calc
      (p : ℂ) ^ (-a) * (p : ℂ) ^ (-b) * (p : ℂ) ^ (-1 : ℂ)
          = (p : ℂ) ^ (-a + -b) * (p : ℂ) ^ (-1 : ℂ) := by rw [cpow_sum hp0 (-a) (-b)]
      _ = (p : ℂ) ^ (-a + -b + -1) := by rw [cpow_sum hp0 (-a + -b) (-1 : ℂ)]
      _ = (p : ℂ) ^ (-(1 + a + b)) := by congr 1; ring
  calc
    locK p a b = 1 - (p : ℂ) ^ (-(1 + a)) - (p : ℂ) ^ (-(1 + b)) + (p : ℂ) ^ (-(1 + a + b)) := by
            rfl
    _ = 1 - (p : ℂ) ^ (-a) * (p : ℂ) ^ (-1 : ℂ) - (p : ℂ) ^ (-b) * (p : ℂ) ^ (-1 : ℂ) +
          (p : ℂ) ^ (-a) * (p : ℂ) ^ (-b) * (p : ℂ) ^ (-1 : ℂ) := by
            rw [← hx, ← hy, ← hz]
    _ = pairLocal (R := ℂ) (ι := ℕ)
          (x := fun q : ℕ => (q : ℂ) ^ (-a))
          (y := fun q : ℕ => (q : ℂ) ^ (-b))
          (z := fun q : ℕ => (q : ℂ) ^ (-1 : ℂ)) p := by
            unfold pairLocal
            rfl

section Bounds

variable {p : ℕ}

/-- `‖1 − w‖ ≥ 1/2` given `‖w‖ ≤ 1/2`. -/
lemma norm_one_sub_ge {w : ℂ} (hw : ‖w‖ ≤ (1 / 2 : ℝ)) : (1 / 2 : ℝ) ≤ ‖1 - w‖ := by
  have h1 : (1 : ℝ) ≤ ‖1 - w‖ + ‖w‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
      _ = ‖(1 - w) + w‖ := by congr 1; ring
      _ ≤ ‖1 - w‖ + ‖w‖ := norm_add_le (1 - w) w
  linarith

/-- `‖1 − w‖ ≤ 3/2` given `‖w‖ ≤ 1/2`. -/
lemma norm_one_sub_le {w : ℂ} (hw : ‖w‖ ≤ (1 / 2 : ℝ)) : ‖1 - w‖ ≤ (3 / 2 : ℝ) := by
  have h1 : ‖1 - w‖ ≤ (1 : ℝ) + ‖w‖ := by
    simpa using (norm_sub_le (1 : ℂ) w)
  linarith

/-- **P8 (40), k = 1, absolute form.**  For `p ≥ 2`, `Re a, Re b ≥ 0`:
`‖K_p − R_p‖ ≤ 8/p²`. -/
theorem locK_sub_locR_bound (a b : ℂ) (hp2 : 2 ≤ p) (ha0 : 0 ≤ a.re) (hb0 : 0 ≤ b.re) :
    ‖locK p a b - locR p a b‖ ≤ 8 / (p : ℝ) ^ 2 := by
  classical
  let u : ℂ := (p : ℂ) ^ (-(1 + a))
  let v : ℂ := (p : ℂ) ^ (-(1 + b))
  let w : ℂ := (p : ℂ) ^ (-(1 + a + b))
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hre_a : 1 ≤ (1 + a).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hre_b : 1 ≤ (1 + b).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hre_ab : 1 ≤ (1 + a + b).re := by
    rw [Complex.add_re, Complex.add_re, Complex.one_re]; linarith
  have hu : ‖u‖ ≤ (p : ℝ)⁻¹ := by
    dsimp [u]; exact norm_cpow_neg_le_inv hp2 (s := 1 + a) (by simpa using hre_a)
  have hv : ‖v‖ ≤ (p : ℝ)⁻¹ := by
    dsimp [v]; exact norm_cpow_neg_le_inv hp2 (s := 1 + b) (by simpa using hre_b)
  have hw : ‖w‖ ≤ (p : ℝ)⁻¹ := by
    dsimp [w]; exact norm_cpow_neg_le_inv hp2 (s := 1 + a + b) (by simpa using hre_ab)
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hinv_le : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    rw [one_div]
    exact (inv_le_inv₀ (by linarith : 0 < (p : ℝ)) (by norm_num)).mpr hp2r
  have hw12 : ‖w‖ ≤ (1 / 2 : ℝ) := hw.trans hinv_le
  have hu12 : ‖u‖ ≤ (1 / 2 : ℝ) := hu.trans hinv_le
  have hv12 : ‖v‖ ≤ (1 / 2 : ℝ) := hv.trans hinv_le
  have hw_nz : 1 - w ≠ 0 := by
    have h : (1 / 2 : ℝ) ≤ ‖1 - w‖ := norm_one_sub_ge hw12
    intro hz
    rw [hz] at h
    norm_num at h
  have hden_ge : (1 / 2 : ℝ) ≤ ‖1 - w‖ := norm_one_sub_ge hw12
  have hden_pos : 0 < ‖1 - w‖ := by linarith
  have hB1 : ‖(1 - w)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hle : ‖1 - w‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := (inv_le_inv₀ hden_pos (by norm_num)).mpr hden_ge
    have h12 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    simpa [h12] using hle
  have hiden := locR_sub_locK (p := p) a b hp0 hw_nz
  have hnormX : ‖(p : ℂ)⁻¹ - u - v + w‖ ≤ 4 * (p : ℝ)⁻¹ := by
    have h1 : ‖(p : ℂ)⁻¹ - u‖ ≤ ‖(p : ℂ)⁻¹‖ + ‖u‖ := norm_sub_le ((p : ℂ)⁻¹) u
    have h2 : ‖((p : ℂ)⁻¹ - u) - v‖ ≤ ‖(p : ℂ)⁻¹ - u‖ + ‖v‖ := norm_sub_le ((p : ℂ)⁻¹ - u) v
    have h3 : ‖((p : ℂ)⁻¹ - u - v) + w‖ ≤ ‖(p : ℂ)⁻¹ - u - v‖ + ‖w‖ :=
      norm_add_le ((p : ℂ)⁻¹ - u - v) w
    have hnorm_inv : ‖(p : ℂ)⁻¹‖ ≤ (p : ℝ)⁻¹ := by
      rw [norm_inv]
      norm_num
    calc
      ‖(p : ℂ)⁻¹ - u - v + w‖
          ≤ ‖(p : ℂ)⁻¹ - u - v‖ + ‖w‖ := h3
      _ ≤ (‖(p : ℂ)⁻¹ - u‖ + ‖v‖) + ‖w‖ := by nlinarith [h2]
      _ ≤ ((‖(p : ℂ)⁻¹‖ + ‖u‖) + ‖v‖) + ‖w‖ := by nlinarith [h1]
      _ ≤ 4 * (p : ℝ)⁻¹ := by nlinarith [hnorm_inv, hu, hv, hw]
  have hprod : ‖w‖ * ‖(p : ℂ)⁻¹ - u - v + w‖ ≤ (p : ℝ)⁻¹ * (4 * (p : ℝ)⁻¹) := by
    exact mul_le_mul hw hnormX (norm_nonneg _) (by positivity : 0 ≤ (p : ℝ)⁻¹)
  have hpR : (p : ℝ) ≠ 0 := by positivity
  calc
    ‖locK p a b - locR p a b‖
        = ‖locR p a b - locK p a b‖ := by rw [norm_sub_rev]
    _ = ‖w * ((p : ℂ)⁻¹ - u - v + w) / (1 - w)‖ := by
            rw [hiden]
    _ = (‖w‖ * ‖(p : ℂ)⁻¹ - u - v + w‖) * ‖(1 - w)⁻¹‖ := by
            rw [div_eq_mul_inv, norm_mul, norm_mul]
    _ ≤ (‖w‖ * ‖(p : ℂ)⁻¹ - u - v + w‖) * 2 := by
            exact mul_le_mul_of_nonneg_left hB1
              (mul_nonneg (norm_nonneg w) (norm_nonneg ((p : ℂ)⁻¹ - u - v + w)))
    _ ≤ ((p : ℝ)⁻¹ * (4 * (p : ℝ)⁻¹)) * 2 := by
            exact mul_le_mul_of_nonneg_right hprod (by norm_num)
    _ = 8 / (p : ℝ) ^ 2 := by
            field_simp [hpR]
            ring


/-- Lower bound on the ratio form: `‖R_p‖ ≥ 1/6` for `p ≥ 2`, `Re a, Re b ≥ 0`. -/
theorem locR_norm_ge_sixth (a b : ℂ) (hp2 : 2 ≤ p) (ha0 : 0 ≤ a.re) (hb0 : 0 ≤ b.re) :
    (1 / 6 : ℝ) ≤ ‖locR p a b‖ := by
  classical
  let u : ℂ := (p : ℂ) ^ (-(1 + a))
  let v : ℂ := (p : ℂ) ^ (-(1 + b))
  let w : ℂ := (p : ℂ) ^ (-(1 + a + b))
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hinv_le : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    rw [one_div]
    exact (inv_le_inv₀ (by linarith : 0 < (p : ℝ)) (by norm_num)).mpr hp2r
  have hre_a : 1 ≤ (1 + a).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hre_b : 1 ≤ (1 + b).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hre_ab : 1 ≤ (1 + a + b).re := by
    rw [Complex.add_re, Complex.add_re, Complex.one_re]; linarith
  have hu12 : ‖u‖ ≤ (1 / 2 : ℝ) := by
    dsimp [u]
    exact (norm_cpow_neg_le_inv hp2 (s := 1 + a) (by simpa using hre_a)).trans hinv_le
  have hv12 : ‖v‖ ≤ (1 / 2 : ℝ) := by
    dsimp [v]
    exact (norm_cpow_neg_le_inv hp2 (s := 1 + b) (by simpa using hre_b)).trans hinv_le
  have hw12 : ‖w‖ ≤ (1 / 2 : ℝ) := by
    dsimp [w]
    exact (norm_cpow_neg_le_inv hp2 (s := 1 + a + b) (by simpa using hre_ab)).trans hinv_le
  have h1u : (1 / 2 : ℝ) ≤ ‖1 - u‖ := norm_one_sub_ge hu12
  have h1v : (1 / 2 : ℝ) ≤ ‖1 - v‖ := norm_one_sub_ge hv12
  have h1w : ‖1 - w‖ ≤ (3 / 2 : ℝ) := norm_one_sub_le hw12
  have hnum : (1 / 4 : ℝ) ≤ ‖1 - u‖ * ‖1 - v‖ := by
    have h1 : (1 / 2 : ℝ) * (1 / 2) ≤ ‖1 - u‖ * (1 / 2) :=
      mul_le_mul_of_nonneg_right h1u (by norm_num)
    have h2 : ‖1 - u‖ * (1 / 2) ≤ ‖1 - u‖ * ‖1 - v‖ :=
      mul_le_mul_of_nonneg_left h1v (norm_nonneg (1 - u))
    norm_num at h1
    exact h1.trans h2
  have hw_nz : 1 - w ≠ 0 := by
    have h : (1 / 2 : ℝ) ≤ ‖1 - w‖ := norm_one_sub_ge hw12
    intro hz
    rw [hz] at h
    norm_num at h
  have hden_pos : 0 < ‖1 - w‖ := by linarith [norm_one_sub_ge hw12]
  have hdeninv : (2 / 3 : ℝ) ≤ ‖1 - w‖⁻¹ := by
    have hle : (3 / 2 : ℝ)⁻¹ ≤ ‖1 - w‖⁻¹ :=
      (inv_le_inv₀ (by norm_num : 0 < (3 / 2 : ℝ)) hden_pos).mpr h1w
    have h23 : (3 / 2 : ℝ)⁻¹ = 2 / 3 := by norm_num
    simpa [h23] using hle
  have hlocR : locR p a b = ((1 - u) * (1 - v)) / (1 - w) := by
    simp [locR, u, v, w]
  calc
    (1 / 6 : ℝ) ≤ (1 / 4 : ℝ) * (2 / 3) := by norm_num
    _ ≤ (‖1 - u‖ * ‖1 - v‖) * ‖1 - w‖⁻¹ := by
            exact mul_le_mul hnum hdeninv (by norm_num)
              (mul_nonneg (norm_nonneg (1 - u)) (norm_nonneg (1 - v)))
    _ = ‖((1 - u) * (1 - v)) / (1 - w)‖ := by
            rw [norm_div, norm_mul]
            ring
    _ = ‖locR p a b‖ := by rw [hlocR]

/-- **P8 (40), k = 1, multiplicative form.**  For `p ≥ 2`, `Re a, Re b ≥ 0`:
`‖K_p/R_p − 1‖ ≤ 48/p²`, i.e. `K_p = (1+O(p⁻²))·R_p`. -/
theorem locK_div_locR_sub_one_bound (a b : ℂ) (hp2 : 2 ≤ p) (ha0 : 0 ≤ a.re)
    (hb0 : 0 ≤ b.re) :
    ‖locK p a b / locR p a b - 1‖ ≤ 48 / (p : ℝ) ^ 2 := by
  classical
  have habs := locK_sub_locR_bound a b hp2 ha0 hb0
  have hRge := locR_norm_ge_sixth a b hp2 ha0 hb0
  have hRpos : 0 < ‖locR p a b‖ := by linarith
  have hR_nz : locR p a b ≠ 0 := by
    intro hz
    rw [hz] at hRpos
    norm_num at hRpos
  have hp2r : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hpR : (p : ℝ) ≠ 0 := by positivity
  have hRinv : ‖locR p a b‖⁻¹ ≤ 6 := by
    have hle : ‖locR p a b‖⁻¹ ≤ (1 / 6 : ℝ)⁻¹ :=
      (inv_le_inv₀ hRpos (by norm_num : 0 < (1 / 6 : ℝ))).mpr hRge
    have h6 : (1 / 6 : ℝ)⁻¹ = 6 := by norm_num
    simpa [h6] using hle
  calc
    ‖locK p a b / locR p a b - 1‖
        = ‖(locK p a b - locR p a b) / locR p a b‖ := by
            congr 1
            field_simp [hR_nz]
    _ = ‖locK p a b - locR p a b‖ / ‖locR p a b‖ := by
            rw [norm_div]
    _ ≤ (8 / (p : ℝ) ^ 2) * 6 := by
            -- ‖K−R‖/‖R‖ = ‖K−R‖ · ‖R‖⁻¹  ≤ (8/p²)·6
            calc
              ‖locK p a b - locR p a b‖ / ‖locR p a b‖
                  = ‖locK p a b - locR p a b‖ * ‖locR p a b‖⁻¹ := by ring
              _ ≤ (8 / (p : ℝ) ^ 2) * 6 := by
                      exact mul_le_mul habs hRinv
                        (by positivity : 0 ≤ ‖locR p a b‖⁻¹)
                        (by positivity : 0 ≤ 8 / (p : ℝ) ^ 2)
    _ = 48 / (p : ℝ) ^ 2 := by
            field_simp [hpR]
            ring

end Bounds

end Commons.NumberTheory.MaynardSieve
