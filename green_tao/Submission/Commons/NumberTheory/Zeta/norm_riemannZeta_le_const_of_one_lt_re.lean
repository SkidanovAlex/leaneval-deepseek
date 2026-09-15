import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Complex
open scoped Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- The `n`th term of the Dirichlet series for `ζ(s)` (shifted to start at `1`) has norm
`(n+1) ^ (-s.re)`. -/
private lemma norm_one_div_nat_add_one_cpow_gen (n : ℕ) (s : ℂ) :
    ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ = ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
  have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcast : (((n + 1 : ℕ) : ℂ)) = ((((n + 1 : ℕ) : ℝ) : ℂ)) := by norm_num
  calc
    ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ = ‖(((n + 1 : ℕ) : ℂ) ^ s)⁻¹‖ := by simp [one_div]
    _ = ‖(((n + 1 : ℕ) : ℂ) ^ s)‖⁻¹ := by rw [norm_inv]
    _ = (((n + 1 : ℕ) : ℝ) ^ s.re)⁻¹ := by
      rw [hcast]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0 s]
    _ = ((n + 1 : ℕ) : ℝ) ^ (-s.re) := by
      rw [Real.rpow_neg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]

/-- Termwise bound: for `σ ≤ s.re`, the norm of the `n`th Dirichlet-series summand of `ζ(s)`
is at most `(n+1) ^ (-σ)`. -/
private lemma zeta_term_norm_le_gen (s : ℂ) {σ : ℝ} (hs : σ ≤ s.re) (n : ℕ) :
    ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ ≤ ((n + 1 : ℕ) : ℝ) ^ (-σ) := by
  have h1 : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
  have hneg : -s.re ≤ -σ := by linarith
  calc
    ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ = ((n + 1 : ℕ) : ℝ) ^ (-s.re) :=
      norm_one_div_nat_add_one_cpow_gen n s
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (-σ) := Real.rpow_le_rpow_of_exponent_le h1 hneg

/-- The real `p`-series `∑' n, (n+1) ^ (-σ)` converges for `σ > 1`. -/
private lemma summable_nat_add_one_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := by
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
    rw [Real.summable_nat_rpow]
    linarith
  simpa using (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-σ)) 1).mpr hnat

/-- Dirichlet-series bound: for `σ ≤ s.re` with `σ > 1`, `ζ(s)` is bounded by the convergent
real `p`-series `∑' n, (n+1) ^ (-σ)`. -/
private lemma zeta_norm_le_tsum_gen (s : ℂ) {σ : ℝ} (hσ : 1 < σ) (hs : σ ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-σ) := by
  have hs1 : 1 < s.re := lt_of_lt_of_le hσ hs
  let f : ℕ → ℂ := fun n => 1 / (((n + 1 : ℕ) : ℂ) ^ s)
  let g : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ (-σ)
  have hzeta : riemannZeta s = ∑' n : ℕ, f n := by
    simpa [f] using zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hsum_g : Summable g := by
    simpa [g] using summable_nat_add_one_rpow_neg hσ
  have hterm : ∀ n : ℕ, ‖f n‖ ≤ g n := by
    intro n
    simpa [f, g] using zeta_term_norm_le_gen s hs n
  have hsum_norm : Summable (fun n : ℕ => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsum_g
  calc
    ‖riemannZeta s‖ = ‖∑' n : ℕ, f n‖ := by rw [hzeta]
    _ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, g n := Summable.tsum_le_tsum hterm hsum_norm hsum_g

/-- The Riemann zeta function is bounded on the half-plane `Re s ≥ σ` for every `σ > 1`. -/
theorem norm_riemannZeta_le_const_of_one_lt_re {σ : ℝ} (hσ : 1 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, σ ≤ z.re → ‖riemannZeta z‖ ≤ C := by
  refine ⟨∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-σ), ?_, ?_⟩
  · have hsum_g : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) :=
      summable_nat_add_one_rpow_neg hσ
    have hts := Summable.tsum_eq_zero_add hsum_g
    have hg0 : ((0 + 1 : ℕ) : ℝ) ^ (-σ) = 1 := by norm_num
    have hnonneg : 0 ≤ ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-σ) := by
      apply tsum_nonneg
      intro n
      exact le_of_lt (Real.rpow_pos_of_pos (by positivity) _)
    rw [hts, hg0]
    linarith
  · intro z hz
    exact zeta_norm_le_tsum_gen z hσ hz

end Commons.NumberTheory.Zeta
