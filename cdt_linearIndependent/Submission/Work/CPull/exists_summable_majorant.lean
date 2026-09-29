import Mathlib
import Submission.Work.CPull.defs

namespace Work.CPull

/-- The absolute-summability radius of the power series `Σ aₙ wⁿ` strictly exceeds `‖Ψ 0‖` when
the pullback series `Σ aₙ Ψ(z)ⁿ` converges on a neighbourhood `U` of `0` and `deriv Ψ 0 ≠ 0`.

*Sketch.* `hU0` and `hΨ`/`hΨ'0` make `Ψ` a local biholomorphism at `0`, so `Ψ(U)` contains a
neighbourhood of `w₀ = Ψ 0` and hence a point `w₁` with `‖w₁‖ > ‖w₀‖`; equivalently, if
`‖Ψ z‖ ≤ ‖Ψ 0‖` on `U`, the maximum modulus principle (`Complex.eventually_eq_of_isLocalMax_norm`)
would make `Ψ` locally constant at `0`, contradicting `deriv Ψ 0 ≠ 0`.  By `hconv` the series
`Σ aₙ wⁿ` converges at `w₁`, so its radius of convergence `R` satisfies `R ≥ ‖w₁‖ > ‖w₀‖`; take
`‖Ψ 0‖ < s < R`, then `Σ ‖aₙ‖ n sⁿ` is summable (derive summability from `Summable.norm` at a
point of modulus `t` with `s < t < R`, then compare `n sⁿ ≤ C tⁿ`). -/
theorem exists_summable_majorant {a : ℕ → ℂ} {Ψ : ℂ → ℂ} {U : Set ℂ}
    (hUopen : IsOpen U) (hU0 : U ∈ nhds (0 : ℂ))
    (hΨ : DifferentiableOn ℂ Ψ (Metric.ball 0 1)) (hΨ'0 : deriv Ψ 0 ≠ 0)
    (hconv : ∀ z ∈ U, Summable (fun n : ℕ => a n * Ψ z ^ n)) :
    ∃ s : ℝ, ‖Ψ 0‖ < s ∧ Summable (fun n : ℕ => ‖a n‖ * n * s ^ n) := by
  -- ## Step 1: there is a point of `U` where `‖Ψ‖` exceeds `‖Ψ 0‖`.
  have hz_exists : ∃ z ∈ U, ‖Ψ 0‖ < ‖Ψ z‖ := by
    by_contra hcontra
    push_neg at hcontra
    -- `0` is a local maximum of `‖Ψ‖`, contradicting `deriv Ψ 0 ≠ 0`.
    have hmax : IsMaxOn (norm ∘ Ψ) U 0 := fun z hz => hcontra z hz
    have hloc : IsLocalMax (norm ∘ Ψ) 0 := hmax.isLocalMax hU0
    have hdiff : ∀ᶠ z in nhds (0 : ℂ), DifferentiableAt ℂ Ψ z :=
      hΨ.eventually_differentiableAt (Metric.ball_mem_nhds 0 one_pos)
    have heq : Ψ =ᶠ[nhds (0 : ℂ)] fun _ => Ψ 0 :=
      Complex.eventually_eq_of_isLocalMax_norm hdiff hloc
    have hderiv : deriv Ψ 0 = 0 := by
      rw [heq.deriv_eq]
      exact deriv_const (0 : ℂ) (Ψ 0)
    exact hΨ'0 hderiv
  obtain ⟨z₀, hz₀U, hz₀⟩ := hz_exists
  -- ## Step 2: the power series is summable at `w₁ = Ψ z₀`, `‖w₁‖ > ‖Ψ 0‖`.
  have hsum0 : Summable (fun n : ℕ => a n * Ψ z₀ ^ n) := hconv z₀ hz₀U
  have hsumNorm : Summable (fun n : ℕ => ‖a n * Ψ z₀ ^ n‖) := hsum0.norm
  have ht_pos : 0 < ‖Ψ z₀‖ := lt_of_le_of_lt (norm_nonneg _) hz₀
  -- a uniform bound for the terms of the summable series
  have hbound : ∀ n : ℕ, ‖a n * Ψ z₀ ^ n‖ ≤ ∑' k, ‖a k * Ψ z₀ ^ k‖ :=
    fun n => hsumNorm.le_tsum n (fun _ _ => norm_nonneg _)
  -- the geometric ratio `ρ = s / ‖Ψ z₀‖`
  set ρ : ℝ := (‖Ψ 0‖ + ‖Ψ z₀‖) / (2 * ‖Ψ z₀‖) with hρ_def
  have hρ_nn : 0 ≤ ρ := by
    rw [hρ_def]
    exact div_nonneg (by linarith [norm_nonneg (Ψ 0)]) (by linarith)
  have hρ_lt : ρ < 1 := by
    rw [hρ_def, div_lt_one (by linarith : (0 : ℝ) < 2 * ‖Ψ z₀‖)]
    linarith
  set s : ℝ := ρ * ‖Ψ z₀‖ with hs_def
  have hs_eq : s = (‖Ψ 0‖ + ‖Ψ z₀‖) / 2 := by
    rw [hs_def, hρ_def]
    field_simp
  have hs_gt : ‖Ψ 0‖ < s := by rw [hs_eq]; linarith
  have hs_nn : 0 ≤ s := mul_nonneg hρ_nn (le_of_lt ht_pos)
  refine ⟨s, hs_gt, ?_⟩
  have hρnorm : ‖ρ‖ < 1 := by rw [Real.norm_of_nonneg hρ_nn]; exact hρ_lt
  have hgeo : Summable (fun n : ℕ => (n : ℝ) * ρ ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hρnorm
  have hcomp : Summable (fun n : ℕ => (∑' k, ‖a k * Ψ z₀ ^ k‖) * ((n : ℝ) * ρ ^ n)) :=
    hgeo.mul_left _
  refine Summable.of_norm_bounded hcomp (fun n => ?_)
  rw [Real.norm_of_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg n)) (pow_nonneg hs_nn n))]
  have hkey : ‖a n‖ * (n : ℝ) * s ^ n = ‖a n * Ψ z₀ ^ n‖ * ((n : ℝ) * ρ ^ n) := by
    rw [hs_def, mul_pow, norm_mul, norm_pow]
    ring
  rw [hkey]
  exact mul_le_mul_of_nonneg_right (hbound n)
    (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hρ_nn n))

end Work.CPull
