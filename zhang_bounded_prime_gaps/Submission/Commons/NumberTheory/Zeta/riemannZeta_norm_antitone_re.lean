import Mathlib.NumberTheory.LSeries.RiemannZeta
import Submission.Commons.NumberTheory.Zeta.riemannZeta_bound_sphere_two

open scoped BigOperators Topology
open Filter Finset

noncomputable section

namespace Commons.NumberTheory.Zeta

/-!
# Monotonicity of `‖ζ(σ)‖` for real `σ > 1`

For real `σ' ≤ σ` with `1 < σ'`, the modulus of the Riemann zeta function at the
real point `σ` is at most its modulus at `σ'`:

`‖ζ(σ)‖ ≤ ‖ζ(σ')‖`.

On the half-plane `1 < re s` the zeta function is given by the (absolutely convergent)
Dirichlet series `ζ(s) = ∑' n, 1 / (n + 1)^s`.  For real `σ > 1` every summand is a
nonnegative real number, so `‖ζ(σ)‖ = ∑' n, 1 / (n + 1)^σ`, and the claim follows from
the termwise inequality `1 / (n + 1)^σ ≤ 1 / (n + 1)^σ'` (base `n + 1 ≥ 1`, exponents
`σ' ≤ σ`) together with `Summable.tsum_le_tsum`.
-/

/-- The `n`-th summand of the Dirichlet series for `ζ` at the real point `σ` is the
coercion of the corresponding nonnegative real number. -/
private lemma inv_cpow_eq (n : ℕ) (σ : ℝ) :
    (1 : ℂ) / (((n : ℂ) + 1) ^ (σ : ℂ)) =
      Complex.ofReal ((1 : ℝ) / ((n : ℝ) + 1) ^ σ) := by
  have hb : (((n : ℂ) + 1)) = ((((n : ℝ) + 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hb, ← Complex.ofReal_cpow (x := (n : ℝ) + 1) (by positivity) σ]
  rw [← Complex.ofReal_one, ← Complex.ofReal_div]

/-- For real `σ > 1`, `ζ(σ)` is the coercion of the real `p`-series `∑' n, 1/(n+1)^σ`. -/
private lemma zeta_re_eq_tsum (σ : ℝ) (hσ : 1 < σ) :
    riemannZeta ((σ : ℝ) : ℂ) =
      Complex.ofReal (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ σ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := (σ : ℂ)) (by simpa using hσ)]
  rw [tsum_congr (fun n => inv_cpow_eq n σ), Complex.ofReal_tsum]

/-- The real `p`-series `∑' n, 1/(n+1)^σ` is antitone in `σ` on `(1, ∞)`. -/
private lemma tsum_rpow_comparison {σ σ' : ℝ} (h1 : 1 < σ') (h2 : σ' ≤ σ) :
    (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ σ) ≤
      (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ σ') := by
  have hσ : 1 < σ := lt_of_lt_of_le h1 h2
  have hsum' : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ σ') := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ σ') :=
      Real.summable_one_div_nat_rpow.mpr h1
    refine ((summable_nat_add_iff 1).mpr hbase).congr (fun n => ?_)
    push_cast
    ring_nf
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ σ) := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ σ) :=
      Real.summable_one_div_nat_rpow.mpr hσ
    refine ((summable_nat_add_iff 1).mpr hbase).congr (fun n => ?_)
    push_cast
    ring_nf
  refine Summable.tsum_le_tsum (fun n => ?_) hsum hsum'
  have hb : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hbb : ((n : ℝ) + 1) ^ σ' ≤ ((n : ℝ) + 1) ^ σ :=
    Real.rpow_le_rpow_of_exponent_le hb h2
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ σ' := Real.rpow_pos_of_pos (by positivity) _
  exact one_div_le_one_div_of_le hpos hbb

theorem riemannZeta_norm_antitone_re {σ σ' : ℝ} (h1 : 1 < σ') (h2 : σ' ≤ σ) :
    ‖riemannZeta ((σ : ℝ) : ℂ)‖ ≤ ‖riemannZeta ((σ' : ℝ) : ℂ)‖ := by
  have hσ : 1 < σ := lt_of_lt_of_le h1 h2
  rw [zeta_re_eq_tsum σ hσ, zeta_re_eq_tsum σ' h1]
  rw [Complex.norm_of_nonneg (tsum_nonneg (fun n => ?_)),
      Complex.norm_of_nonneg (tsum_nonneg (fun n => ?_))]
  · exact tsum_rpow_comparison h1 h2
  all_goals
    refine div_nonneg zero_le_one (le_of_lt ?_)
    exact Real.rpow_pos_of_pos (by positivity) _

end Commons.NumberTheory.Zeta