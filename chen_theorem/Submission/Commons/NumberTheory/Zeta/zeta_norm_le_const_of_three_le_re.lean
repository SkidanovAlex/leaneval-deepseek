import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Complex Filter Set
open scoped Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- The `n`th term of the Dirichlet series for `ζ(s)` (shifted to start at `1`) has norm
`(n+1) ^ (-s.re)`. -/
private lemma norm_one_div_nat_add_one_cpow (n : ℕ) (s : ℂ) :
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

/-- Termwise bound: for `3 ≤ s.re`, the norm of the `n`th Dirichlet-series summand of `ζ(s)`
is at most `(n+1) ^ (-3)`. -/
private lemma zeta_term_norm_le (s : ℂ) (hs : 3 ≤ s.re) (n : ℕ) :
    ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ ≤ ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := by
  have h1 : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
  have hneg : -s.re ≤ -3 := by linarith
  calc
    ‖1 / (((n + 1 : ℕ) : ℂ) ^ s)‖ = ((n + 1 : ℕ) : ℝ) ^ (-s.re) :=
      norm_one_div_nat_add_one_cpow n s
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hneg

/-- The real `p`-series `∑' n, (n+1) ^ (-3)` converges. -/
private lemma summable_nat_add_one_rpow_neg_three :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)) := by
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)) := by
    rw [Real.summable_nat_rpow]
    norm_num
  have hh : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)) := by
    simpa using (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-3 : ℝ)) 1).mpr hnat
  exact hh

/-- Dirichlet-series bound: for `3 ≤ s.re` the series value `ζ(s)` is bounded by the
convergent real `p`-series `∑' n, (n+1) ^ (-3)`. -/
private lemma zeta_norm_le_tsum (s : ℂ) (hs : 3 ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := by
  have hs1 : 1 < s.re := by linarith
  let f : ℕ → ℂ := fun n => 1 / (((n + 1 : ℕ) : ℂ) ^ s)
  let g : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)
  have hzeta : riemannZeta s = ∑' n : ℕ, f n := by
    simpa [f] using zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  have hsum_g : Summable g := by
    simpa [g] using summable_nat_add_one_rpow_neg_three
  have hterm : ∀ n : ℕ, ‖f n‖ ≤ g n := by
    intro n
    simpa [f, g] using zeta_term_norm_le s hs n
  have hsum_norm : Summable (fun n : ℕ => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsum_g
  calc
    ‖riemannZeta s‖ = ‖∑' n : ℕ, f n‖ := by rw [hzeta]
    _ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hsum_norm
    _ ≤ ∑' n : ℕ, g n := Summable.tsum_le_tsum hterm hsum_norm hsum_g

/-- The Riemann zeta function is bounded on the half-plane of real part at least `3`. -/
theorem zeta_norm_le_const_of_three_le_re :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 3 ≤ s.re → ‖riemannZeta s‖ ≤ C := by
  let C : ℝ := ∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)
  refine ⟨C, ?_, ?_⟩
  · show 0 < C
    unfold C
    have hsum_g : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ)) :=
      summable_nat_add_one_rpow_neg_three
    have hts := Summable.tsum_eq_zero_add (f := fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-3 : ℝ))
      hsum_g
    have hg0 : ((0 + 1 : ℕ) : ℝ) ^ (-3 : ℝ) = 1 := by norm_num
    have hnonneg : 0 ≤ ∑' n : ℕ, ((n + 1 + 1 : ℕ) : ℝ) ^ (-3 : ℝ) := by
      apply tsum_nonneg
      intro n
      have hb : (0 : ℝ) < ((n + 1 + 1 : ℕ) : ℝ) := by positivity
      exact le_of_lt (Real.rpow_pos_of_pos hb _)
    rw [hts, hg0]
    linarith
  · intro s hs
    show ‖riemannZeta s‖ ≤ C
    simpa [C] using zeta_norm_le_tsum s hs

end Commons.NumberTheory.Zeta
