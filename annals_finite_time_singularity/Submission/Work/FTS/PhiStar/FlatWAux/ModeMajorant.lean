import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux

noncomputable section

set_option autoImplicit false

/-!
# `Work.FTS.PhiStar.FlatWAux.ModeMajorant`

The `m`-series of the error term of the flat `W`-expansion, with the three `ψ`-dependent
constants (`Cd` for the coefficient decay, `CRG` for the rescaled radial bound, `CQ` for the
angular mode bound) stripped off, is summable with a bound proportional to `Cd · CRG · CQ`.

Writing `λ_m = lam m = 2m(2m+5)` and `q_m = √(2m+1)`, the `m`-th term of the series is

`Cd / (λ_m q_m) · λ_m^{-J} · (CRG / λ_m) · (CQ · (2m+1)²)`
  `= Cd · CRG · CQ · λ_m^{-(J+2)} · q_m^{-1} · (2m+1)²`,

i.e. `Cd·CRG·CQ` times the *shape function*

`F m = (λ_m √(2m+1))⁻¹ · (λ_m⁻¹)^J · λ_m⁻¹ · (2m+1)²`,

which is what we define below.  Since `λ_m ≥ 4m²` and `(2m+1)² ≤ 9m²` for `m ≥ 1`, and `J = 8`,

`F m = (2m+1)² / (λ_m^10 · √(2m+1)) ≤ 9m² / (4m²)^10 ≤ ((m+1)²)⁻¹`   (`m ≥ 1`),

so `F` is dominated by the summable comparison series `Σ_m ((m+1)²)⁻¹`; the constant of the
statement is then `K = ∑' m, F m` (the supremum, not a numerical value, so no sharp constant is
needed anywhere).  The term `m = 0` contributes `0` because `λ_0 = 0`.
-/

/-- The shape of the `m`-th term of the mode majorant, with the constants `Cd, CRG, CQ`
stripped off. -/
private def F (m : ℕ) : ℝ :=
  (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))⁻¹
    * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
    * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ * (2 * (m : ℝ) + 1) ^ 2

/-- `lam m = 2m(2m+5)` is nonnegative. -/
private lemma lam_nonneg (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  positivity

/-- The shape function is nonnegative. -/
private lemma F_nonneg (m : ℕ) : 0 ≤ F m := by
  have hA : (0 : ℝ) ≤ Work.FTS.PhiStar.Gegenbauer.lam m := lam_nonneg m
  simp only [F]
  positivity

/-- At `m = 0` the eigenvalue vanishes and the term is `0`. -/
private lemma F_zero : F 0 = 0 := by
  simp only [F, J, Work.FTS.PhiStar.Gegenbauer.lam]
  norm_num

/-- The basic lower bound `4m² ≤ λ_m` for `m ≥ 1`. -/
private lemma four_mul_sq_le_lam {m : ℕ} (hm : 1 ≤ m) :
    4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  nlinarith

/-- For `m ≥ 1` the shape function is bounded by `((m+1)²)⁻¹`. -/
private lemma F_le_pos {m : ℕ} (hm : 1 ≤ m) : F m ≤ (((m : ℝ) + 1) ^ 2)⁻¹ := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hMnn : (0 : ℝ) ≤ (m : ℝ) := by linarith
  have hA4 : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := four_mul_sq_le_lam hm
  have hS1 : 1 ≤ Real.sqrt (2 * (m : ℝ) + 1) := Real.one_le_sqrt.mpr (by linarith)
  have hc : (2 * (m : ℝ) + 1) ^ 2 ≤ 9 * (m : ℝ) ^ 2 := by nlinarith
  -- the term is `(2m+1)² / (λ_m^10 √(2m+1))`
  have hF : F m = (2 * (m : ℝ) + 1) ^ 2
      / ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1)) := by
    simp only [F, J]
    rw [mul_inv, inv_pow]
    ring_nf
  rw [hF]
  -- the denominator is at least `(4m²)^10`
  have hden : (4 * (m : ℝ) ^ 2) ^ 10 * 1
      ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1) := by
    have h4 : (4 * (m : ℝ) ^ 2) ^ 10 ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 :=
      pow_le_pow_left₀ (by positivity) hA4 10
    have h5 : (0 : ℝ) ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 := by positivity
    calc (4 * (m : ℝ) ^ 2) ^ 10 * 1 = (4 * (m : ℝ) ^ 2) ^ 10 := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 := h4
      _ = (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * 1 := by ring
      _ ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hS1 h5
  have hstep1 : (2 * (m : ℝ) + 1) ^ 2
        / ((Work.FTS.PhiStar.Gegenbauer.lam m) ^ 10 * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ 9 * (m : ℝ) ^ 2 / ((4 * (m : ℝ) ^ 2) ^ 10 * 1) :=
    div_le_div₀ (by positivity) hc (by positivity) hden
  have hstep2' : 9 * (m : ℝ) ^ 2 / ((4 * (m : ℝ) ^ 2) ^ 10 * 1) ≤ 1 / ((m : ℝ) + 1) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have ha1 : ((m : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith
    have ha2 : (9 * (m : ℝ) ^ 2) * ((m : ℝ) + 1) ^ 2
        ≤ (9 * (m : ℝ) ^ 2) * (4 * (m : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left ha1 (by positivity)
    have hpow : (4 * (m : ℝ) ^ 2) ^ 10 = 4 ^ 10 * (m : ℝ) ^ 20 := by ring
    have hM20 : (m : ℝ) ^ 4 ≤ (m : ℝ) ^ 20 := pow_le_pow_right₀ h1 (by norm_num)
    have ha4 : 9 * (m : ℝ) ^ 2 * (4 * (m : ℝ) ^ 2) ≤ 4 ^ 10 * (m : ℝ) ^ 20 := by
      have h3 : 9 * (m : ℝ) ^ 2 * (4 * (m : ℝ) ^ 2) = 36 * (m : ℝ) ^ 4 := by ring
      rw [h3]
      nlinarith [hM20, pow_nonneg hMnn 4]
    rw [hpow]
    linarith [ha2, ha4]
  have hstep2 : 9 * (m : ℝ) ^ 2 / ((4 * (m : ℝ) ^ 2) ^ 10 * 1) ≤ (((m : ℝ) + 1) ^ 2)⁻¹ := by
    simpa only [one_div] using hstep2'
  linarith [hstep1, hstep2]

/-- The shape function is bounded by `((m+1)²)⁻¹` for every `m`. -/
private lemma F_le (m : ℕ) : F m ≤ (((m : ℝ) + 1) ^ 2)⁻¹ := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [F_zero]
    norm_num
  · exact F_le_pos hm

/-- The comparison series `Σ_m ((m+1)²)⁻¹` is summable. -/
private lemma summable_inv_sq_shift : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) := by
  have h : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ (-(2 : ℝ))) := by
    have h0 : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) :=
      (Real.summable_nat_rpow).mpr (by norm_num)
    have h1 := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(2 : ℝ))) 1).mpr h0
    simpa only [Nat.cast_add, Nat.cast_one] using h1
  refine h.congr (fun m => ?_)
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m : ℝ) + 1)]
  norm_num

/-- The shape function is summable. -/
private lemma summable_F : Summable F :=
  Summable.of_nonneg_of_le F_nonneg F_le summable_inv_sq_shift

/-- The `m`-th term of the majorant is `Cd·CRG·CQ` times the shape function. -/
private lemma term_eq (Cd CRG CQ : ℝ) (m : ℕ) :
    Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
        * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
        * (CQ * (2 * (m : ℝ) + 1) ^ 2)
      = Cd * CRG * CQ * F m := by
  simp only [F, J, div_eq_mul_inv]
  ring

theorem ModeMajorant : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (Cd CRG CQ : ℝ), 0 ≤ Cd → 0 ≤ CRG → 0 ≤ CQ →
      Summable (fun m : ℕ =>
          Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * (CQ * (2 * (m : ℝ) + 1) ^ 2)) ∧
      (∑' m : ℕ, Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J
            * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
            * (CQ * (2 * (m : ℝ) + 1) ^ 2))
        ≤ K * Cd * CRG * CQ := by
  refine ⟨∑' m : ℕ, F m, tsum_nonneg F_nonneg, ?_⟩
  intro Cd CRG CQ _ _ _
  have hEq : ∀ m : ℕ,
      Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ J
          * (CRG / Work.FTS.PhiStar.Gegenbauer.lam m)
          * (CQ * (2 * (m : ℝ) + 1) ^ 2)
        = Cd * CRG * CQ * F m := fun m => term_eq Cd CRG CQ m
  constructor
  · exact (summable_F.mul_left (Cd * CRG * CQ)).congr (fun m => (hEq m).symm)
  · rw [tsum_congr hEq, tsum_mul_left]
    have hcomm : Cd * CRG * CQ * (∑' m : ℕ, F m)
        = (∑' m : ℕ, F m) * Cd * CRG * CQ := by ring
    rw [hcomm]

end

end Work.FTS.PhiStar.FlatWAux
