/-
# Auxiliary lemmas for `Work.LinnikAreas.efunBound`

This file collects the elementary ingredients for the bound
`‖E(x)‖ ≤ C √q log(2q+2) √x` on the error term `E(x) = A(x) - x L(1,χ)` of the divisor
function `λ = 1 * χ`:

* `chiPrefix` is the prefix sum `P(y) = Σ_{1 ≤ n ≤ y} χ(n)`;
* `chiPrefix_bound` is the Pólya–Vinogradov inequality in prefix form (imported from
  `Submission.Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov`);
* `LSeries_partial_bound_one` bounds the tail of the Dirichlet series of `L(1,χ)`
  (imported from `Submission.Commons.NumberTheory.DirichletCharacter.LFunction_partial_sums_bound`).

Everything here is unconditional and sorry-free.
-/
import Mathlib
import Submission.Work.LinnikAreas.RatioDefs
import Submission.Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_partial_sums_bound

namespace Work.LinnikAreas

open DirichletCharacter
open scoped BigOperators

noncomputable section

variable {q : ℕ} [NeZero q]

/-- `P(y) = Σ_{1 ≤ n ≤ y} χ(n)`: the prefix sums of the Dirichlet character `χ`. -/
def chiPrefix (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y, (χ (n : ZMod q) : ℂ)

@[simp] lemma chiPrefix_apply (χ : DirichletCharacter ℂ q) (y : ℕ) :
    chiPrefix χ y = ∑ n ∈ Finset.Icc 1 y, (χ (n : ZMod q) : ℂ) := rfl

/-- **Pólya–Vinogradov in prefix form**: all prefix sums of a non-principal character mod
`q ≥ 2` are bounded by `C √q log(2q+2)`. -/
theorem chiPrefix_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 2 ≤ q →
      ∀ y : ℕ, ‖chiPrefix χ y‖ ≤ C * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov
  refine ⟨C₀, hC₀pos, ?_⟩
  intro q _ χ hχ hq y
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have h0 : chiPrefix χ 0 = 0 := by
      rw [chiPrefix_apply, Finset.Icc_eq_empty_iff.mpr (by omega : ¬ (1:ℕ) ≤ 0),
        Finset.sum_empty]
    rw [h0, norm_zero]
    have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have hlog : (0:ℝ) ≤ Real.log (2*(q:ℝ)+2) := Real.log_nonneg (by linarith)
    exact mul_nonneg (mul_nonneg (le_of_lt hC₀pos) (Real.sqrt_nonneg _)) hlog
  · simpa [chiPrefix_apply] using hC₀ q hq χ hχ 1 y hy

/-- **Tail bound for the Dirichlet series of `L(1,χ)`**: for a non-principal character mod
`q ≥ 2` and `M ≥ 1`,
`‖Σ_{n ≤ M} χ(n)/n - L(1,χ)‖ ≤ C √q log(2q+2)/M`. -/
theorem LSeries_partial_bound_one :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 2 ≤ q →
      ∀ M : ℕ, 1 ≤ M →
        ‖(∑ n ∈ Finset.Icc 1 M, (χ (n : ZMod q) : ℂ) / (n : ℂ)) - LFunction χ 1‖
          ≤ C * Real.sqrt (q : ℝ) * Real.log (2 * (q : ℝ) + 2) / (M : ℝ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.DirichletCharacter.LFunction_partial_sums_bound
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro q _ χ hχ hq M hM
  have h := hC₀ q χ hχ hq (s := (1 : ℂ)) (by norm_num) (M := M) hM
  have hsum : (∑ n ∈ Finset.Icc 1 M, (χ (n : ZMod q) : ℂ) / (n : ℂ))
      = ∑ n ∈ Finset.Icc 1 M, (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-(1 : ℂ)) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Complex.cpow_neg_one]
    ring
  rw [hsum]
  have hsimp : (1 + ‖(1:ℂ)‖ / (1:ℂ).re) = 2 := by norm_num
  have hexp : (-(1:ℂ).re : ℝ) = -1 := by norm_num
  have hMpow : ((M:ℝ)) ^ (-(1:ℂ).re) = 1/(M:ℝ) := by
    rw [hexp, Real.rpow_neg_one, one_div]
  rw [hsimp, hMpow] at h
  calc ‖(∑ n ∈ Finset.Icc 1 M, (χ (n : ZMod q) : ℂ) * (n : ℂ) ^ (-(1:ℂ))) - LFunction χ 1‖
      ≤ C₀ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) * 2 * (1/(M:ℝ)) := h
    _ = 2 * C₀ * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ)+2) / (M:ℝ) := by ring

/-- The fractional part of `N/d` is at most `1`: `‖⌊N/d⌋ - N/d‖ ≤ 1` (for `d ≥ 1`). -/
lemma norm_div_sub_floor_le_one (N d : ℕ) (hd : 1 ≤ d) :
    ‖((N / d : ℕ) : ℂ) - (N : ℂ) / (d : ℂ)‖ ≤ 1 := by
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have h1 : ((N/d:ℕ):ℝ) ≤ (N:ℝ)/(d:ℝ) := by
    rw [le_div_iff₀ hd0]
    calc ((N/d:ℕ):ℝ) * (d:ℝ) = ((N/d * d : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (N:ℝ) := by exact_mod_cast Nat.div_mul_le_self N d
  have hs : N / d < N / d + 1 := Nat.lt_succ_self (N/d)
  have hdiv : N < (N/d + 1) * d :=
    (Nat.div_lt_iff_lt_mul (k := d) (x := N) (y := N/d + 1) (show 0 < d by omega)).mp hs
  have h3 : (N:ℝ) < (((N/d:ℕ):ℝ) + 1) * (d:ℝ) := by exact_mod_cast hdiv
  have h2 : (N:ℝ)/(d:ℝ) < ((N/d:ℕ):ℝ) + 1 := by
    rw [div_lt_iff₀ hd0]
    linarith
  have hreal : ((N / d : ℕ) : ℂ) - (N : ℂ) / (d : ℂ)
      = (((N / d : ℕ) : ℝ) - (N : ℝ) / (d : ℝ) : ℝ) := by
    rw [← Complex.ofReal_natCast (N/d)]
    rw [← Complex.ofReal_natCast d]
    rw [← Complex.ofReal_natCast N]
    rw [← Complex.ofReal_div]
    rw [← Complex.ofReal_sub]
  rw [hreal, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end Work.LinnikAreas
