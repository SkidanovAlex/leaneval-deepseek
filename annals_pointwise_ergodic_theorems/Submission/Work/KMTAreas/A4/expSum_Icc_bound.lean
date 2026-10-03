import Mathlib
import Submission.Work.KMTAreas.A4.denseMultiples_kern

/-!
# The two-sided geometric (Dirichlet-kernel) bound

`∑_{j = -n}^{n} e^{2 π i j θ}` is the Dirichlet kernel
`sin ((2n+1) π θ) / sin (π θ)`; its absolute value is at most `1 / (2 · nDist θ)`,
where `nDist θ` is the distance from `θ` to the nearest integer.

The proof is the elementary telescoping estimate for a geometric sum on the unit
circle, together with the trigonometric bound `2 · nDist θ ≤ |sin (π θ)|`.

The file also exposes the three ingredients separately (`sum_Icc_zpow_eq`,
`norm_sum_Icc_zpow_le`, `two_nDist_le_abs_sin_pi`, `norm_exp_two_pi_I_sub_one`),
which are of independent use.

## Main statement

* `Work.KMTAreas.A4.expSum_Icc_bound`
-/

set_option autoImplicit false

namespace Work.KMTAreas.A4

open scoped BigOperators

/-- A two-sided geometric sum reindexed as `z^{-n}` times a one-sided one. -/
theorem sum_Icc_zpow_eq (z : ℂ) (hz0 : z ≠ 0) (n : ℕ) :
    ∑ j ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), z^j
      = z^(-(n:ℤ)) * ∑ k ∈ Finset.range (2*n+1), z^k := by
  rw [Finset.mul_sum]
  refine Finset.sum_bij' (fun a _ => (a + (n:ℤ)).toNat) (fun b _ => (b:ℤ) - (n:ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_range]
    have h1 : -(n:ℤ) ≤ a := (Finset.mem_Icc.mp ha).1
    have h2 : a ≤ (n:ℤ) := (Finset.mem_Icc.mp ha).2
    have hnn : 0 ≤ a + (n:ℤ) := by omega
    rw [Int.toNat_lt hnn]
    push_cast
    omega
  · intro b hb
    rw [Finset.mem_range] at hb
    rw [Finset.mem_Icc]
    omega
  · intro a ha
    have hnn : 0 ≤ a + (n:ℤ) := by have := (Finset.mem_Icc.mp ha).1; omega
    rw [Int.toNat_of_nonneg hnn]
    ring
  · intro b hb
    rw [Finset.mem_range] at hb
    rw [show (b:ℤ) - (n:ℤ) + (n:ℤ) = (b:ℤ) by ring, Int.toNat_natCast]
  · intro a ha
    have hnn : 0 ≤ a + (n:ℤ) := by have := (Finset.mem_Icc.mp ha).1; omega
    have hcast : ((a + (n:ℤ)).toNat : ℤ) = a + (n:ℤ) := Int.toNat_of_nonneg hnn
    have haeq : a = -(n:ℤ) + ((a + (n:ℤ)).toNat : ℤ) := by rw [hcast]; ring
    conv_lhs => rw [haeq]
    rw [zpow_add₀ hz0, zpow_natCast]

/-- **The geometric bound.**  For `z` on the unit circle with `z ≠ 1`, the two-sided
geometric sum of length `2n+1` is at most `2/‖z-1‖`. -/
theorem norm_sum_Icc_zpow_le (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (n : ℕ) :
    ‖∑ j ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), z^j‖ ≤ 2 / ‖z - 1‖ := by
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; norm_num at hz
  have hpos : 0 < ‖z - 1‖ := by rw [norm_pos_iff]; exact sub_ne_zero.mpr hz1
  have hreind := sum_Icc_zpow_eq z hz0 n
  rw [hreind, norm_mul, norm_zpow, hz, one_zpow, one_mul]
  rw [le_div_iff₀ hpos]
  rw [← norm_mul, geom_sum_mul]
  calc ‖z ^ (2*n+1) - 1‖ ≤ ‖z ^ (2*n+1)‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, one_pow]; norm_num

/-- The trigonometric input: `2 · nDist x ≤ |sin (π x)|`. -/
theorem two_nDist_le_abs_sin_pi (x : ℝ) : 2 * nDist x ≤ |Real.sin (Real.pi * x)| := by
  have hnd : nDist x = |x - (round x : ℝ)| := rfl
  have hsin : |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * (x - (round x : ℝ)))| := by
    have h : Real.pi * x = Real.pi * (x - (round x : ℝ)) + (round x : ℝ) * Real.pi := by ring
    rw [h, Real.sin_add_int_mul_pi, abs_mul]
    have h1 : |((-1:ℝ) ^ (round x))| = 1 := by rw [abs_zpow]; norm_num
    rw [h1, one_mul]
  rw [hnd, hsin]
  set u := x - (round x : ℝ) with hu
  have hu2 : |u| ≤ 1/2 := by rw [hu]; exact nDist_le_half x
  have hmul : 2 * |u| ≤ Real.sin (Real.pi * |u|) := by
    have h0 : 0 ≤ Real.pi * |u| := by positivity
    have h1 : Real.pi * |u| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos, hu2]
    have hm := Real.mul_le_sin h0 h1
    have he : 2 / Real.pi * (Real.pi * |u|) = 2 * |u| := by field_simp
    rw [he] at hm
    exact hm
  have hkey : |Real.sin (Real.pi * u)| = Real.sin (Real.pi * |u|) := by
    rcases abs_cases u with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1]
      have hu' : u ≤ 1/2 := by rw [← h1]; exact hu2
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [Real.pi_pos, hu']))]
    · rw [h1, show Real.pi * -u = -(Real.pi * u) by ring, Real.sin_neg]
      have hneg : Real.sin (Real.pi * u) ≤ 0 := by
        have h0 : 0 ≤ -(Real.pi * u) := by nlinarith [Real.pi_pos, h2]
        have hu' : -u ≤ 1/2 := by rw [← h1]; exact hu2
        have h3 : -(Real.pi * u) ≤ Real.pi := by
          have : -(Real.pi * u) = Real.pi * (-u) := by ring
          rw [this]; nlinarith [Real.pi_pos, hu']
        have hs := Real.sin_nonneg_of_nonneg_of_le_pi h0 h3
        rw [Real.sin_neg] at hs
        linarith
      rw [abs_of_nonpos hneg]
  rw [hkey]
  exact hmul

/-- The distance from `e^{2 π i θ}` to `1` is `2 |sin (π θ)|`. -/
theorem norm_exp_two_pi_I_sub_one (θ : ℝ) :
    ‖Complex.exp (2*Real.pi*Complex.I*(θ:ℂ)) - 1‖ = 2 * |Real.sin (Real.pi * θ)| := by
  rw [show (2:ℂ)*Real.pi*Complex.I*(θ:ℂ) = Complex.I * ((2*Real.pi*θ : ℝ):ℂ) by
    push_cast; ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2*Real.pi*θ)/2 = Real.pi*θ by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

/-- **The Dirichlet-kernel bound**: the two-sided exponential sum over `[-n, n]` is bounded by
`1 / (2 · nDist θ)`. -/
theorem expSum_Icc_bound (n : ℕ) (θ : ℝ) (hθ : nDist θ ≠ 0) :
    ‖∑ j ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ))‖
      ≤ 1/(2*nDist θ) := by
  have hn : 0 < nDist θ := lt_of_le_of_ne (nDist_nonneg θ) (Ne.symm hθ)
  set z : ℂ := Complex.exp (2*Real.pi*Complex.I*(θ:ℂ)) with hzdef
  have hterm : ∀ j : ℤ, Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ)) = z^j := by
    intro j
    rw [hzdef, ← Complex.exp_int_mul]
    congr 1
    ring
  have hsum : (∑ j ∈ Finset.Icc (-(n:ℤ)) (n:ℤ),
        Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(θ:ℂ)))
      = ∑ j ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), z^j :=
    Finset.sum_congr rfl (fun j _ => hterm j)
  rw [hsum]
  have hzn : ‖z‖ = 1 := by
    rw [hzdef, show (2:ℂ)*Real.pi*Complex.I*(θ:ℂ) = ((2*Real.pi*θ : ℝ):ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hb2 : 4 * nDist θ ≤ ‖z - 1‖ := by
    rw [hzdef, norm_exp_two_pi_I_sub_one θ]
    linarith [two_nDist_le_abs_sin_pi θ]
  have hz1 : z ≠ 1 := by
    intro h
    have h0 : ‖z - 1‖ = 0 := by rw [h]; simp
    linarith [hb2, hn]
  calc ‖∑ j ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), z^j‖ ≤ 2 / ‖z - 1‖ :=
        norm_sum_Icc_zpow_le z hzn hz1 n
    _ ≤ 1 / (2 * nDist θ) := by
        have h42 : 0 < 4 * nDist θ := by linarith
        calc 2 / ‖z - 1‖ ≤ 2 / (4 * nDist θ) :=
              div_le_div_of_nonneg_left (by norm_num) h42 hb2
          _ = 1 / (2 * nDist θ) := by
              rw [show (4:ℝ) * nDist θ = 2 * (2 * nDist θ) by ring, div_mul_eq_div_div,
                  div_self (by norm_num : (2:ℝ) ≠ 0)]

end Work.KMTAreas.A4
