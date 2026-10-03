import Mathlib
import Submission.Work.Repel.Koebe.seriesMulCircleIntegral

/-!
# The circle integral of `(β/z + ∑ αₘ zᵐ)(1 + ∑ γₖ / z^{k+1})`

For `r > 0`, coefficients `α γ : ℕ → ℂ` with `∑ ‖αₘ‖ rᵐ < ∞` and `∑ ‖γₖ‖ / r^{k+1} < ∞`, and any
`β : ℂ`,

`∮_{|z| = r} (β/z + ∑ₘ αₘ zᵐ)(1 + ∑ₖ γₖ / z^{k+1}) dz = 2πi (β + ∑ₘ αₘ γₘ)`.

Only the `z⁻¹` coefficient of the product survives: it is `β` (from `β/z · 1`) plus
`∑ₘ αₘ γₘ` (from `αₘ zᵐ · γₘ / z^{m+1}`), while `A · 1` and `β/z · B` contribute nothing.

The proof rewrites the integrand on the circle as a product of two Laurent series in the normal
form handled by `circleIntegral_tsum_mul_tsum_div'`:

`(β/z + A(z))(1 + B(z)) = (β + z A(z)) · z⁻¹ (1 + B(z))`,

i.e. `(∑ₙ dₙ zⁿ)(∑ₖ qₖ z^{-k})` with `d = (β, α₀, α₁, …)` and `q = (0, 1, γ₀, γ₁, …)`, and then
evaluates the diagonal sum `∑ₙ dₙ q_{n+1} = β + ∑ₘ αₘ γₘ`.
-/

noncomputable section

open Filter MeasureTheory

namespace Work.Repel.Koebe

/-! ### Shifted coefficient sequences

`shiftHead b a = (b, a 0, a 1, …)`, `shiftZero a = (0, a 0, a 1, …)`,
`shiftOne a = (1, a 0, a 1, …)`. -/

/-- `shiftHead b a` is the sequence `b, a 0, a 1, …`. -/
def shiftHead (b : ℂ) (a : ℕ → ℂ) : ℕ → ℂ := fun n => Nat.rec b (fun m _ => a m) n

/-- `shiftZero a` is the sequence `0, a 0, a 1, …`. -/
def shiftZero (a : ℕ → ℂ) : ℕ → ℂ := fun n => Nat.rec 0 (fun m _ => a m) n

/-- `shiftOne a` is the sequence `1, a 0, a 1, …`. -/
def shiftOne (a : ℕ → ℂ) : ℕ → ℂ := fun n => Nat.rec 1 (fun m _ => a m) n

@[simp] theorem shiftHead_zero (b : ℂ) (a : ℕ → ℂ) : shiftHead b a 0 = b := rfl

@[simp] theorem shiftHead_succ (b : ℂ) (a : ℕ → ℂ) (n : ℕ) : shiftHead b a (n + 1) = a n := rfl

@[simp] theorem shiftZero_zero (a : ℕ → ℂ) : shiftZero a 0 = 0 := rfl

@[simp] theorem shiftZero_succ (a : ℕ → ℂ) (n : ℕ) : shiftZero a (n + 1) = a n := rfl

@[simp] theorem shiftOne_zero (a : ℕ → ℂ) : shiftOne a 0 = 1 := rfl

@[simp] theorem shiftOne_succ (a : ℕ → ℂ) (n : ℕ) : shiftOne a (n + 1) = a n := rfl

/-! ### Summability and `tsum` normal forms for the shifted series -/

/-- The diagonal of two coefficient sequences summable against the reciprocal geometric weights
`rᵐ` and `r^{-k}` is summable. -/
theorem summable_mul_diag {α γ : ℕ → ℂ} {r : ℝ} (hr : 0 < r)
    (hα : Summable (fun m : ℕ => ‖α m‖ * r ^ m))
    (hγ : Summable (fun k : ℕ => ‖γ k‖ / r ^ k)) :
    Summable (fun m : ℕ => α m * γ m) := by
  have hprod : Summable (fun p : ℕ × ℕ => (‖α p.1‖ * r ^ p.1) * (‖γ p.2‖ / r ^ p.2)) :=
    Summable.mul_of_nonneg hα hγ (fun m => mul_nonneg (norm_nonneg _) (pow_nonneg hr.le m))
      (fun k => div_nonneg (norm_nonneg _) (pow_nonneg hr.le k))
  have hdiag : Summable (fun m : ℕ => (‖α m‖ * r ^ m) * (‖γ m‖ / r ^ m)) :=
    hprod.comp_injective (i := fun m : ℕ => (m, m)) (fun x y h => (Prod.ext_iff.mp h).1)
  refine Summable.of_norm ?_
  refine hdiag.congr (fun m => ?_)
  rw [norm_mul, div_eq_mul_inv]
  field_simp

/-- Splitting off the head of `∑' n, shiftHead b a n * zⁿ`. -/
theorem tsum_shiftHead_mul (b : ℂ) (a : ℕ → ℂ) (z : ℂ)
    (h : Summable (fun n : ℕ => a n * z ^ n)) :
    (∑' n : ℕ, shiftHead b a n * z ^ n) = b + z * ∑' n : ℕ, a n * z ^ n := by
  have hz : Summable (fun n : ℕ => a n * z ^ (n + 1)) := by
    refine (h.mul_right z).congr (fun n => ?_)
    rw [pow_succ]; ring
  have hs : Summable (fun n : ℕ => shiftHead b a n * z ^ n) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa only [shiftHead_succ] using hz
  have hsplit : (∑' n : ℕ, shiftHead b a n * z ^ n)
      = b + ∑' n : ℕ, a n * z ^ (n + 1) := by
    rw [hs.tsum_eq_zero_add]
    simp only [shiftHead_zero, shiftHead_succ, pow_zero, mul_one]
  rw [hsplit, show (∑' n : ℕ, a n * z ^ (n + 1)) = (∑' n : ℕ, a n * z ^ n) * z from
    (tsum_congr (fun n => by rw [pow_succ]; ring)).trans
      (tsum_mul_right (f := fun n : ℕ => a n * z ^ n) (a := z))]
  ring

/-- Splitting off the head of `∑' k, shiftZero a k / z^k`. -/
theorem tsum_shiftZero_div (a : ℕ → ℂ) (z : ℂ) (hz : z ≠ 0)
    (h : Summable (fun k : ℕ => a k / z ^ k)) :
    (∑' k : ℕ, shiftZero a k / z ^ k) = z⁻¹ * ∑' k : ℕ, a k / z ^ k := by
  have hz1 : Summable (fun k : ℕ => a k / z ^ (k + 1)) := by
    refine (h.mul_left z⁻¹).congr (fun k => ?_)
    rw [div_eq_mul_inv, div_eq_mul_inv, pow_succ, mul_inv_rev]
    ring
  have hs : Summable (fun k : ℕ => shiftZero a k / z ^ k) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa only [shiftZero_succ] using hz1
  have hsplit : (∑' k : ℕ, shiftZero a k / z ^ k)
      = ∑' k : ℕ, a k / z ^ (k + 1) := by
    rw [hs.tsum_eq_zero_add]
    simp only [shiftZero_zero, shiftZero_succ, zero_div, zero_add]
  rw [hsplit]
  refine (tsum_congr (fun k => ?_)).trans
    (tsum_mul_left (f := fun k : ℕ => a k / z ^ k) (a := z⁻¹))
  rw [div_eq_mul_inv, div_eq_mul_inv, pow_succ, mul_inv_rev]
  ring

/-- Splitting off the head of `∑' k, shiftOne a k / z^k`. -/
theorem tsum_shiftOne_div (a : ℕ → ℂ) (z : ℂ) (hz : z ≠ 0)
    (h : Summable (fun k : ℕ => a k / z ^ (k + 1))) :
    (∑' k : ℕ, shiftOne a k / z ^ k) = 1 + ∑' k : ℕ, a k / z ^ (k + 1) := by
  have hs : Summable (fun k : ℕ => shiftOne a k / z ^ k) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa only [shiftOne_succ] using h
  rw [hs.tsum_eq_zero_add]
  simp only [shiftOne_zero, shiftOne_succ, pow_zero, div_one]

/-- The pointwise normal form of the integrand on the circle `‖z‖ = r`: the product
`(β/z + A(z))(1 + B(z))` is the product of the two Laurent series `∑ₙ dₙ zⁿ` and
`∑ₖ qₖ z^{-k}` with `d = shiftHead β α` and `q = shiftZero (shiftOne γ)`. -/
theorem integrand_eq (α γ : ℕ → ℂ) (β z : ℂ) (hz : z ≠ 0)
    (hA : Summable (fun m : ℕ => α m * z ^ m))
    (hB : Summable (fun k : ℕ => γ k / z ^ (k + 1))) :
    (β / z + ∑' m : ℕ, α m * z ^ m) * (1 + ∑' k : ℕ, γ k / z ^ (k + 1))
      = (∑' n : ℕ, shiftHead β α n * z ^ n)
          * (∑' k : ℕ, shiftZero (shiftOne γ) k / z ^ k) := by
  have he : Summable (fun k : ℕ => shiftOne γ k / z ^ k) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa only [shiftOne_succ] using hB
  rw [tsum_shiftHead_mul β α z hA, tsum_shiftZero_div (shiftOne γ) z hz he,
    tsum_shiftOne_div γ z hz hB]
  field_simp

/-! ### The requested residue computation -/

theorem circleIntegral_series_residue {α γ : ℕ → ℂ} {β : ℂ} {r : ℝ} (hr : 0 < r)
    (hα : Summable (fun m : ℕ => ‖α m‖ * r ^ m))
    (hγ : Summable (fun k : ℕ => ‖γ k‖ / r ^ (k + 1))) :
    circleIntegral (fun z : ℂ =>
        (β / z + ∑' m : ℕ, α m * z ^ m) * (1 + ∑' k : ℕ, γ k / z ^ (k + 1))) 0 r
      = 2 * (Real.pi : ℂ) * Complex.I * (β + ∑' m : ℕ, α m * γ m) := by
  -- the weight sequence `‖γ k‖ / r ^ k`
  have hγk : Summable (fun k : ℕ => ‖γ k‖ / r ^ k) := by
    refine (hγ.mul_left r).congr (fun k => ?_)
    rw [pow_succ]
    field_simp
  -- summability of the `d`-weights
  have hd : Summable (fun n : ℕ => ‖shiftHead β α n‖ * r ^ n) := by
    refine (summable_nat_add_iff 1).mp ?_
    refine (hα.mul_left r).congr (fun n => ?_)
    rw [shiftHead_succ, pow_succ]
    ring
  -- summability of the `q`-weights
  have hq : Summable (fun k : ℕ => ‖shiftZero (shiftOne γ) k‖ / r ^ k) := by
    refine (summable_nat_add_iff 2).mp ?_
    refine (hγ.div_const r).congr (fun k => ?_)
    have h1 : shiftZero (shiftOne γ) (k + 2) = γ k := by
      rw [show k + 2 = (k + 1) + 1 from rfl, shiftZero_succ, shiftOne_succ]
    rw [h1, div_div]
    rfl
  -- the diagonal sum `∑ₙ dₙ q_{n+1} = β + ∑ₘ αₘ γₘ`
  have hαγ : Summable (fun m : ℕ => α m * γ m) := summable_mul_diag hr hα hγk
  have hdiag : (∑' n : ℕ, shiftHead β α n * shiftZero (shiftOne γ) (n + 1))
      = β + ∑' m : ℕ, α m * γ m := by
    have hs : Summable (fun n : ℕ => shiftHead β α n * shiftZero (shiftOne γ) (n + 1)) := by
      refine (summable_nat_add_iff 1).mp ?_
      simpa only [shiftHead_succ, shiftZero_succ, shiftOne_succ] using hαγ
    rw [hs.tsum_eq_zero_add]
    simp only [shiftHead_zero, shiftZero_succ, shiftOne_zero, shiftHead_succ, shiftOne_succ,
      mul_one]
  -- the pointwise identity on the circle
  have hpoint : Set.EqOn
      (fun z : ℂ => (β / z + ∑' m : ℕ, α m * z ^ m) * (1 + ∑' k : ℕ, γ k / z ^ (k + 1)))
      (fun z : ℂ => (∑' n : ℕ, shiftHead β α n * z ^ n)
        * (∑' k : ℕ, shiftZero (shiftOne γ) k / z ^ k)) (Metric.sphere 0 r) := by
    intro z hzmem
    have hz' : ‖z‖ = r := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hzmem
      exact hzmem
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz'; linarith
    have hA : Summable (fun m : ℕ => α m * z ^ m) := by
      refine Summable.of_norm ?_
      have hnorm : (fun m : ℕ => ‖α m * z ^ m‖) = fun m : ℕ => ‖α m‖ * r ^ m := by
        funext m; rw [norm_mul, norm_pow, hz']
      rw [hnorm]; exact hα
    have hB : Summable (fun k : ℕ => γ k / z ^ (k + 1)) := by
      refine Summable.of_norm ?_
      have hnorm : (fun k : ℕ => ‖γ k / z ^ (k + 1)‖) = fun k : ℕ => ‖γ k‖ / r ^ (k + 1) := by
        funext k; rw [norm_div, norm_pow, hz']
      rw [hnorm]; exact hγ
    exact integrand_eq α γ β z hz0 hA hB
  rw [circleIntegral.integral_congr hr.le hpoint,
    circleIntegral_tsum_mul_tsum_div' (α := shiftHead β α) (γ := shiftZero (shiftOne γ)) hr hd hq,
    hdiag]

end Work.Repel.Koebe
