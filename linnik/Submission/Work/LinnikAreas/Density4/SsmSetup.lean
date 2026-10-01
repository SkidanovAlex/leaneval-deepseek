/-
# Area 4 / HB §11 (11.9) — the interface for the smoothed-sum bound

Namespace `Work.LinnikAreas.Density4`.  This file (sorry-free) collects the vocabulary and the
elementary bookkeeping used by `Ssm_fixed_bound` (HB (11.9)):

* `mollCoeff`, `lcmF`, `mollSeries` — the coefficient `Ψ(n)Θ(n)χ(n)`, the finite "lcm" weight
  `F(s)` of HB §11, and the Dirichlet series `Σ_n Ψ(n)Θ(n)χ(n)n^{-w}` (which equals
  `L(w,χ)·F(w)` for `Re w > 1`);
* the pointwise bounds `|Ψ(n)|, |Θ(n)| ≤ τ(n)` and `‖Ψ(n)Θ(n)χ(n)‖ ≤ τ(n)²`, together with the
  absolute convergence `Σ τ(n)²n^{-σ} < ∞` for `σ > 1`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.zeroDetAux
import Submission.Work.LinnikAreas.Density4.det_split
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Work.LinnikContract.Areas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

open Work.LinnikContract

/-- The coefficient `Ψ(n)Θ(n)χ(n)` of the smoothed sum `Ssm = Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ}e^{-n/X}`
(HB (11.6), (11.7), (11.8)). -/
def mollCoeff (q : ℕ) [NeZero q] (U V W : ℝ) (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ((psiS U V n : ℝ) : ℂ) * ((thetaS W n : ℝ) : ℂ) * (χ (n : ZMod q) : ℂ)

/-- HB §11, the finite weight appearing after (11.8):
`F(s) = Σ_{v ≤ V, w ≤ W} ψ_v θ_w χ([v,w]) [v,w]^{-s}`. -/
def lcmF (q : ℕ) [NeZero q] (U V W : ℝ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 (Nat.ceil V), ∑ e ∈ Finset.Icc 1 (Nat.ceil W),
    ((psiM U V d : ℝ) : ℂ) * ((thetaM W e : ℝ) : ℂ)
      * (χ ((Nat.lcm d e : ℕ) : ZMod q)) * (((Nat.lcm d e : ℕ) : ℂ) ^ (-s))

/-- The Dirichlet series `Σ_n Ψ(n)Θ(n)χ(n)n^{-w}` of the mollified coefficients. -/
def mollSeries (q : ℕ) [NeZero q] (U V W : ℝ) (χ : DirichletCharacter ℂ q) (w : ℂ) : ℂ :=
  ∑' n : ℕ, mollCoeff q U V W χ n * ((n : ℂ) ^ (-w))

/-- `Ssm` in terms of `mollCoeff` (definitional unfolding). -/
lemma Ssm_eq_tsum_mollCoeff (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q)
    (ρ : ℂ) :
    Ssm q U V W X χ ρ
      = ∑' n : ℕ, mollCoeff q U V W χ n * ((n : ℂ) ^ (-ρ))
          * ((Real.exp (-(n:ℝ)/X) : ℝ) : ℂ) := by
  rw [Ssm]
  refine tsum_congr fun n => ?_
  simp only [detCoeff, mollCoeff]

/-- `|Ψ(n)| = |Σ_{d | n} ψ_d| ≤ τ(n)`: at most `n.divisors.card` terms, each of modulus `≤ 1`. -/
lemma abs_psiS_le_card_divisors {U V : ℝ} (hU : 0 < U) (n : ℕ) :
    |psiS U V n| ≤ ((n.divisors.card : ℕ) : ℝ) := by
  rw [psiS]
  calc |∑ d ∈ n.divisors, psiM U V d| ≤ ∑ d ∈ n.divisors, |psiM U V d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1:ℝ) := Finset.sum_le_sum fun d _ => abs_psiM_le_one hU d
    _ = ((n.divisors.card : ℕ) : ℝ) := by simp

/-- `|Θ(n)| = |Σ_{d | n} θ_d| ≤ τ(n)`. -/
lemma abs_thetaS_le_card_divisors (W : ℝ) (n : ℕ) :
    |thetaS W n| ≤ ((n.divisors.card : ℕ) : ℝ) := by
  rw [thetaS]
  calc |∑ d ∈ n.divisors, thetaM W d| ≤ ∑ d ∈ n.divisors, |thetaM W d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1:ℝ) := Finset.sum_le_sum fun d _ => abs_thetaM_le_one W d
    _ = ((n.divisors.card : ℕ) : ℝ) := by simp

/-- `‖Ψ(n)Θ(n)χ(n)‖ ≤ τ(n)²`. -/
lemma norm_mollCoeff_le (q : ℕ) [NeZero q] {U V W : ℝ} (hU : 0 < U)
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖mollCoeff q U V W χ n‖ ≤ ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
  have hψ : ‖((psiS U V n : ℝ) : ℂ)‖ ≤ ((n.divisors.card : ℕ) : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_psiS_le_card_divisors hU n
  have hθ : ‖((thetaS W n : ℝ) : ℂ)‖ ≤ ((n.divisors.card : ℕ) : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_thetaS_le_card_divisors W n
  have hχ : ‖(χ (n : ZMod q) : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  have hτ : (0:ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ‖mollCoeff q U V W χ n‖
      = ‖((psiS U V n : ℝ) : ℂ)‖ * ‖((thetaS W n : ℝ) : ℂ)‖ * ‖(χ (n : ZMod q) : ℂ)‖ := by
        simp only [mollCoeff, norm_mul]
    _ ≤ ((n.divisors.card : ℕ) : ℝ) * ((n.divisors.card : ℕ) : ℝ) * 1 := by
        exact mul_le_mul (mul_le_mul hψ hθ (norm_nonneg _) hτ) hχ (norm_nonneg _) (by positivity)
    _ = ((n.divisors.card : ℕ) : ℝ) ^ 2 := by ring

/-- Absolute convergence of the Dirichlet series of the mollified coefficients: for `σ > 1`,
`Σ_n ‖Ψ(n)Θ(n)χ(n)‖ n^{-σ} < ∞`. -/
lemma summable_norm_mollCoeff_mul_rpow (q : ℕ) [NeZero q] {U V W : ℝ} (hU : 0 < U)
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-σ)) := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DivisorBound.card_divisors_le_rpow ((σ - 1) / 4) (by linarith)
  set ε : ℝ := (σ - 1) / 4 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have key : ∀ n : ℕ, ‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-σ) ≤ C ^ 2 * (n : ℝ) ^ (-((σ+1)/2)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      norm_num
      rw [Real.zero_rpow (by linarith : -σ ≠ 0),
        Real.zero_rpow (by linarith : -((σ+1)/2) ≠ 0)]
      simp
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hτ0 : (0:ℝ) ≤ ((n.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsq : ((n.divisors.card : ℕ) : ℝ) ^ 2 ≤ (C * (n:ℝ) ^ ε) ^ 2 :=
      pow_le_pow_left₀ hτ0 (hC n) 2
    have hpow : (C * (n:ℝ) ^ ε) ^ 2 = C ^ 2 * (n : ℝ) ^ (2 * ε) := by
      have h1 : ((n:ℝ) ^ ε) ^ 2 = (n : ℝ) ^ (2 * ε) := by
        rw [sq, ← Real.rpow_add hn0]; ring_nf
      rw [mul_pow, h1]
    have hb : ‖mollCoeff q U V W χ n‖ ≤ C ^ 2 * (n : ℝ) ^ (2 * ε) := by
      calc ‖mollCoeff q U V W χ n‖ ≤ ((n.divisors.card : ℕ) : ℝ) ^ 2 := norm_mollCoeff_le q hU χ n
        _ ≤ (C * (n:ℝ) ^ ε) ^ 2 := hsq
        _ = C ^ 2 * (n : ℝ) ^ (2 * ε) := hpow
    have hexp : 2 * ε = (σ - 1) / 2 := by rw [hεdef]; ring
    calc ‖mollCoeff q U V W χ n‖ * (n : ℝ) ^ (-σ)
        ≤ (C ^ 2 * (n : ℝ) ^ (2 * ε)) * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (le_of_lt hn0) _)
      _ = C ^ 2 * ((n : ℝ) ^ (2 * ε) * (n : ℝ) ^ (-σ)) := by ring
      _ = C ^ 2 * (n : ℝ) ^ (2 * ε + -σ) := by rw [Real.rpow_add hn0]
      _ = C ^ 2 * (n : ℝ) ^ (-((σ+1)/2)) := by
          rw [hexp]; congr 2; ring
  refine Summable.of_nonneg_of_le (fun n => by positivity) key ?_
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-((σ + 1) / 2))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact h1.mul_left _


/-- The regularised integrand of the contour shift: `Γ(s+1)` times the difference quotient of
`L(ρ+·)` at `0` (which is entire), times `X^s F(ρ+s)`.  For `s ≠ 0` it equals the naive integrand
`Γ(s) X^s L(ρ+s) F(ρ+s)`: the pole of `Γ` at `0` is cancelled by the zero of `L` at `ρ`. -/
def Phi (q : ℕ) [NeZero q] (U V W X : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℂ → ℂ :=
  fun s => Complex.Gamma (s + 1) * dslope (fun u : ℂ => LFunction χ (ρ + u)) 0 s
    * (X : ℂ) ^ s * lcmF q U V W χ (ρ + s)

end Work.LinnikAreas.Density4
