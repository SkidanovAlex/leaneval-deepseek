import Mathlib
import Submission.Work.FIArea2.SmoothSec6Defs
import Submission.Work.FIArea2.sec9_frequency_sum_bound
import Submission.Work.FIPlan.Interface
import Submission.Work.FITop.Defs

namespace Work.FIArea2

/-! ## Elementary identities behind the (9.1) weights

`gamOf z₁ z₂ = Re(z̄₁z₂)/√(|z₁|²|z₂|²)` is the cosine `γ` of the angle between `z₁` and `z₂`, so
`1 − γ² = Im(z̄₁z₂)²/(|z₁|²|z₂|²) = Δ(z₁,z₂)²/(|z₁|²|z₂|²)`: the two terms of the Pythagorean
identity add up to the product of the norms.  Consequently `√(1−γ²) = |Δ|/(|z₁||z₂|)` and the
factor `|Δ|` cancels in the weights `c_j = √(1−γ²)√M/(|Δ|·|z_{3−j}|)` of (9.1), leaving
`c₁ = √M/(|z₁||z₂|²)`, `c₂ = √M/(|z₂||z₁|²)`. -/

/-- `|z|²` is the sum of the squares of the coordinates, as a real number. -/
private lemma gnorm_cast_coord_sq (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  rw [Nat.cast_natAbs, Nat.cast_natAbs]
  rw [Int.cast_abs, Int.cast_abs, ← sq, ← sq, sq_abs, sq_abs]

/-- `|z̄₁z₂|² = |z₁|²|z₂|²`. -/
private lemma gnorm_star_mul_eq (z1 z2 : GaussianInt) :
    Work.FIPlan.gnorm (star z1 * z2) = Work.FIPlan.gnorm z1 * Work.FIPlan.gnorm z2 := by
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_mul, Work.FIArea2.norm_star_eq, Int.natAbs_mul]

/-- **Pythagoras for `z̄₁z₂`**: `Re(z̄₁z₂)² + Im(z̄₁z₂)² = |z₁|²|z₂|²`. -/
private lemma star_mul_coord_sq (z1 z2 : GaussianInt) :
    (((star z1 * z2).re : ℤ) : ℝ) ^ 2 + (((star z1 * z2).im : ℤ) : ℝ) ^ 2
      = ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
  rw [← gnorm_cast_coord_sq (star z1 * z2), gnorm_star_mul_eq, Nat.cast_mul]

/-- **`1 − γ²` in terms of `Δ`**: `1 − gamOf z₁ z₂² = Δ(z₁,z₂)²/(|z₁|²|z₂|²)`. -/
private lemma one_sub_gamOf_sq (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) :
    1 - (gamOf z1 z2) ^ 2
      = (((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ) ^ 2)
        / (((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
  have hz1 : z1 ≠ 0 := by intro h; exact hΔ (by simp [Work.FIPlan.Delta, h])
  have hz2 : z2 ≠ 0 := by intro h; exact hΔ (by simp [Work.FIPlan.Delta, h])
  have hg1 : (0 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea2.gnorm_pos_of_ne_zero z1 hz1
  have hg2 : (0 : ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea2.gnorm_pos_of_ne_zero z2 hz2
  have hG : (0 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) :=
    mul_pos hg1 hg2
  have hcoord := star_mul_coord_sq z1 z2
  have hD : (((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ))
      = (((star z1 * z2).im : ℤ) : ℝ) := rfl
  unfold gamOf
  rw [div_pow, Real.sq_sqrt (le_of_lt hG), hD]
  rw [eq_div_iff (ne_of_gt hG), sub_mul, div_mul_cancel₀ _ (ne_of_gt hG), one_mul]
  linarith [hcoord]

/-- `δ = √(1−γ²) = |Δ(z₁,z₂)|/(|z₁||z₂|)`. -/
private lemma sqrt_one_sub_gamOf_sq (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) :
    Real.sqrt (1 - (gamOf z1 z2) ^ 2)
      = ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
        / Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
  rw [one_sub_gamOf_sq z1 z2 hΔ, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs,
    Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs]

/-- `Δ(z₁,z₂) ≠ 0` makes the denominator `|Δ|` of the (9.1) weights nonzero. -/
private lemma absDelta_cast_ne_zero (z1 z2 : GaussianInt) (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) :
    (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ≠ 0 := by
  rw [Work.FIPlan.absDelta, Nat.cast_natAbs, Int.cast_abs]
  simpa using hΔ

/-- The elementary field identity behind `secWeight₁_eq_closed`:
`(A/(√g₁√g₂))·s/(A√g₂) = s/(√g₁g₂)` for `A ≠ 0`, `g₁,g₂ > 0`. -/
private lemma secWeight_alg₁ (A s g1 g2 : ℝ) (hA : A ≠ 0) (hg1 : 0 < g1) (hg2 : 0 < g2) :
    A / (Real.sqrt g1 * Real.sqrt g2) * s / (A * Real.sqrt g2)
      = s / (Real.sqrt g1 * g2) := by
  have hs1 : Real.sqrt g1 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hg1)
  have hs2 : Real.sqrt g2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hg2)
  field_simp
  rw [Real.sq_sqrt (le_of_lt hg2)]
  ring

/-- The elementary field identity behind `secWeight₂_eq_closed`:
`(A/(√g₁√g₂))·s/(A√g₁) = s/(√g₂g₁)` for `A ≠ 0`, `g₁,g₂ > 0`. -/
private lemma secWeight_alg₂ (A s g1 g2 : ℝ) (hA : A ≠ 0) (hg1 : 0 < g1) (hg2 : 0 < g2) :
    A / (Real.sqrt g1 * Real.sqrt g2) * s / (A * Real.sqrt g1)
      = s / (Real.sqrt g2 * g1) := by
  have hs1 : Real.sqrt g1 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hg1)
  have hs2 : Real.sqrt g2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hg2)
  field_simp
  rw [Real.sq_sqrt (le_of_lt hg1)]
  ring

/-- **The closed form of the first (9.1) weight**: `c₁ = √M/(|z₁||z₂|²)`. -/
private lemma secWeight₁_eq_closed (Pa : Work.FITop.Params) (z1 z2 : GaussianInt)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) :
    secWeight₁ Pa z1 z2
      = Real.sqrt Pa.M
        / (Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)) := by
  have hz1 : z1 ≠ 0 := by intro h; exact hΔ (by simp [Work.FIPlan.Delta, h])
  have hz2 : z2 ≠ 0 := by intro h; exact hΔ (by simp [Work.FIPlan.Delta, h])
  have hg1 : (0 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea2.gnorm_pos_of_ne_zero z1 hz1
  have hg2 : (0 : ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea2.gnorm_pos_of_ne_zero z2 hz2
  unfold secWeight₁
  rw [sqrt_one_sub_gamOf_sq z1 z2 hΔ, Real.sqrt_mul (le_of_lt hg1)]
  exact secWeight_alg₁ _ _ _ _ (absDelta_cast_ne_zero z1 z2 hΔ) hg1 hg2

/-- **The closed form of the second (9.1) weight**: `c₂ = √M/(|z₂||z₁|²)`. -/
private lemma secWeight₂_eq_closed (Pa : Work.FITop.Params) (z1 z2 : GaussianInt)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) :
    secWeight₂ Pa z1 z2
      = Real.sqrt Pa.M
        / (Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) * ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)) := by
  have hz1 : z1 ≠ 0 := by intro h; exact hΔ (by simp [Work.FIPlan.Delta, h])
  have hz2 : z2 ≠ 0 := by intro h; exact hΔ (by simp [Work.FIPlan.Delta, h])
  have hg1 : (0 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea2.gnorm_pos_of_ne_zero z1 hz1
  have hg2 : (0 : ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by
    exact_mod_cast Work.FIArea2.gnorm_pos_of_ne_zero z2 hz2
  unfold secWeight₂
  rw [sqrt_one_sub_gamOf_sq z1 z2 hΔ, Real.sqrt_mul (le_of_lt hg1)]
  exact secWeight_alg₂ _ _ _ _ (absDelta_cast_ne_zero z1 z2 hΔ) hg1 hg2

/-! ## The uniform lower bound

`((H = M^{-1/4}N^{3/4})²)⁻¹ = √M·N^{-3/2}` by the `rpow` laws, and `√2·√(2N)·2N = 2^{3/2}N^{3/2}`,
so the content of the estimate is `√g₁·g₂ ≤ 2^{3/2}N^{3/2}`, which is `g₁ ≤ 2N`, `g₂ ≤ 2N` read
off under the monotone `√`. -/

/-- `(x^{-1/4})² = (√x)⁻¹` — the `M`-half of `((Hscale M N)²)⁻¹`. -/
private lemma rpow_quarter_sq (x : ℝ) (hx : 0 < x) :
    (x ^ (-(1 : ℝ) / 4)) ^ 2 = (Real.sqrt x)⁻¹ := by
  have h1 : (x ^ (-(1 : ℝ) / 4)) ^ 2 = x ^ ((-(1 : ℝ) / 4) * ((2 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (x ^ (-(1 : ℝ) / 4)) 2,
      ← Real.rpow_mul (le_of_lt hx) (-(1 : ℝ) / 4) ((2 : ℕ) : ℝ)]
  rw [h1, show (-(1 : ℝ) / 4) * ((2 : ℕ) : ℝ) = -(1 / 2) by norm_num,
    Real.rpow_neg (le_of_lt hx), ← Real.sqrt_eq_rpow]

/-- `(x^{3/4})² = x·√x` — the `N`-half of `((Hscale M N)²)⁻¹`. -/
private lemma rpow_three_quarters_sq (x : ℝ) (hx : 0 < x) :
    (x ^ ((3 : ℝ) / 4)) ^ 2 = x * Real.sqrt x := by
  have h1 : (x ^ ((3 : ℝ) / 4)) ^ 2 = x ^ (((3 : ℝ) / 4) * ((2 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (x ^ ((3 : ℝ) / 4)) 2,
      ← Real.rpow_mul (le_of_lt hx) ((3 : ℝ) / 4) ((2 : ℕ) : ℝ)]
  rw [h1, show ((3 : ℝ) / 4) * ((2 : ℕ) : ℝ) = (3 : ℝ) / 2 by norm_num,
    show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-- `((Hscale M N)²)⁻¹ = √M/(N√N)`. -/
private lemma Hscale_inv_sq (M N : ℝ) (hM : 1 ≤ M) (hN : 0 < N) :
    ((Work.FIPlan.Hscale M N) ^ 2)⁻¹ = Real.sqrt M / (N * Real.sqrt N) := by
  have hMpos : (0 : ℝ) < M := by linarith
  rw [Work.FIPlan.Hscale,
    show (M ^ (-(1 : ℝ) / 4) * N ^ ((3 : ℝ) / 4)) ^ 2
      = (M ^ (-(1 : ℝ) / 4)) ^ 2 * (N ^ ((3 : ℝ) / 4)) ^ 2 by ring,
    rpow_quarter_sq M hMpos, rpow_three_quarters_sq N hN]
  rw [mul_inv, inv_inv, div_eq_mul_inv]

/-- `2^{−3/2} = (2√2)^{−1}`. -/
private lemma two_rpow_neg_three_halves : (2 : ℝ) ^ (-(3 : ℝ) / 2) = (2 * Real.sqrt 2)⁻¹ := by
  rw [show (-(3 : ℝ) / 2) = -(3 / 2) by norm_num, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- **The uniform content of the estimate**: if `0 < g₁ ≤ 2N` and `0 < g₂ ≤ 2N` then
`2^{−3/2}·((Hscale M N)²)⁻¹ ≤ √M/(√g₁·g₂)`. -/
private theorem secWeight_uniform_aux (M N g1 g2 : ℝ) (hM : 1 ≤ M) (hN : 0 < N)
    (hg1 : 0 < g1) (hg1' : g1 ≤ 2 * N) (hg2 : 0 < g2) (hg2' : g2 ≤ 2 * N) :
    (2 : ℝ) ^ (-(3 : ℝ) / 2) * ((Work.FIPlan.Hscale M N) ^ 2)⁻¹
      ≤ Real.sqrt M / (Real.sqrt g1 * g2) := by
  have hH := Hscale_inv_sq M N hM hN
  have key : Real.sqrt g1 * g2 ≤ 2 * Real.sqrt 2 * (N * Real.sqrt N) := by
    have h1 : Real.sqrt g1 ≤ Real.sqrt 2 * Real.sqrt N := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt hg1'
    calc Real.sqrt g1 * g2 ≤ (Real.sqrt 2 * Real.sqrt N) * (2 * N) :=
          mul_le_mul h1 hg2' hg2.le (by positivity)
      _ = 2 * Real.sqrt 2 * (N * Real.sqrt N) := by ring
  rw [two_rpow_neg_three_halves, hH,
    show (2 * Real.sqrt 2)⁻¹ * (Real.sqrt M / (N * Real.sqrt N))
      = Real.sqrt M / (2 * Real.sqrt 2 * (N * Real.sqrt N)) by field_simp]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg M) (by positivity) key

/-- **The polar-box lower bound for the (9.1) weights.**  For a pair with `Δ(z₁,z₂) ≠ 0` whose
Gaussian norms lie in the polar box `N < |z_j|² ≤ (1+θ)N`, the weight constants of Lemma 7.1,
`secWeight₁ = δ√M/(|Δ|·|z₂|)` and `secWeight₂ = δ√M/(|Δ|·|z₁|)` with `δ = √(1−γ²)`, are each at
least `2^{−3/2}·H^{−2}`, `H = M^{−1/4}N^{3/4}` the scale of (9.2)/(9.3). -/
theorem secWeight_ge_uniform (Pa : Work.FITop.Params) (z1 z2 : GaussianInt)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0) (hθ0 : 0 < Pa.θ) (hθ : Pa.θ ≤ 1) (hM : 1 ≤ Pa.M)
    (hn1 : Pa.N < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ))
    (hn1' : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N)
    (hn2 : Pa.N < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))
    (hn2' : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N) :
    (2 : ℝ) ^ (-(3 : ℝ) / 2) * ((Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹
        ≤ Work.FIArea2.secWeight₁ Pa z1 z2 ∧
    (2 : ℝ) ^ (-(3 : ℝ) / 2) * ((Work.FIPlan.Hscale Pa.M Pa.N) ^ 2)⁻¹
        ≤ Work.FIArea2.secWeight₂ Pa z1 z2 := by
  have hNpos : (0 : ℝ) < Pa.N := by
    have : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
    linarith
  have hg1 : (0 : ℝ) < ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by linarith
  have hg2 : (0 : ℝ) < ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) := by linarith
  have hle : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by nlinarith [hθ, hNpos]
  have hg1' : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ 2 * Pa.N := le_trans hn1' hle
  have hg2' : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ 2 * Pa.N := le_trans hn2' hle
  refine ⟨?_, ?_⟩
  · rw [secWeight₁_eq_closed Pa z1 z2 hΔ]
    exact secWeight_uniform_aux Pa.M Pa.N _ _ hM hNpos hg1 hg1' hg2 hg2'
  · rw [secWeight₂_eq_closed Pa z1 z2 hΔ]
    exact secWeight_uniform_aux Pa.M Pa.N _ _ hM hNpos hg2 hg2' hg1 hg1'

end Work.FIArea2
