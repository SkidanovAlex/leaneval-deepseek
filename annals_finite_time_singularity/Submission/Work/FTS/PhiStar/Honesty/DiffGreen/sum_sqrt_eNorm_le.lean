import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.ClassCHon.CmpSupp.eNorm_bounds
import Submission.Work.EllipticEst.ModalSolution.cmode_bessel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.DiffGreen

/-- The mode norm dominates `m + 1`: from the closed form
`eNorm m = (2m+2)(2m+3)/(4m+5)` we have `(2m+2)(2m+3) - (m+1)(4m+5) = m + 1 ≥ 0`. -/
private lemma eNorm_ge_succ (m : ℕ) :
    (m : ℝ) + 1 ≤ Work.EllipticEst.ModalSolution.eNorm m := by
  rw [Work.FTS.ClassCHon.CmpSupp.eNorm_eq m,
    le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (m : ℝ) + 5)]
  nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

/-- Telescoping: `∑_{m<n} 1/((m+1)(m+2)) = 1 - 1/(n+1)`. -/
private lemma sum_range_inv_mul_succ (n : ℕ) :
    ∑ m ∈ Finset.range n, (((m : ℝ) + 1) * ((m : ℝ) + 2))⁻¹ = 1 - ((n : ℝ) + 1)⁻¹ := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep : (((k : ℝ) + 1) * ((k : ℝ) + 2))⁻¹
          = ((k : ℝ) + 1)⁻¹ - ((k : ℝ) + 2)⁻¹ := by
        rw [eq_sub_iff_add_eq]
        field_simp
        ring
      rw [hstep]
      push_cast
      ring

/-- The Cauchy–Schwarz weight sum: `m + 1 ≤ eNorm m` gives
`∑_{m≤N} 1/(eNorm m · (m+1)) ≤ 1 + ∑_{m<N} 1/((m+1)(m+2)) ≤ 2`. -/
private lemma sum_inv_eNorm_mul_le_two (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1),
      (Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹ ≤ 2 := by
  rw [Finset.sum_range_succ']
  have key : ∀ m : ℕ,
      (Work.EllipticEst.ModalSolution.eNorm (m + 1) * (((m + 1 : ℕ) : ℝ) + 1))⁻¹
        ≤ (((m : ℝ) + 1) * ((m : ℝ) + 2))⁻¹ := by
    intro m
    have h := (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds (m + 1)).2
    push_cast at h ⊢
    rw [inv_le_inv₀ (mul_pos (Work.EllipticEst.ModalSolution.eNorm_pos (m + 1)) (by positivity))
      (by positivity)]
    nlinarith [h]
  have hsum : ∑ m ∈ Finset.range N,
      (Work.EllipticEst.ModalSolution.eNorm (m + 1) * (((m + 1 : ℕ) : ℝ) + 1))⁻¹ ≤ 1 := by
    calc _ ≤ ∑ m ∈ Finset.range N, (((m : ℝ) + 1) * ((m : ℝ) + 2))⁻¹ :=
          Finset.sum_le_sum fun m _ => key m
      _ = 1 - ((N : ℝ) + 1)⁻¹ := sum_range_inv_mul_succ N
      _ ≤ 1 := by
          have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
          have := inv_pos.2 hpos
          linarith
  have h0 : (Work.EllipticEst.ModalSolution.eNorm 0 * ((0 : ℝ) + 1))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (mul_pos (Work.EllipticEst.ModalSolution.eNorm_pos 0) (by norm_num))]
    have h := (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds 0).1
    linarith
  linarith

/-- **The Cauchy–Schwarz sum step for the modal series.**  If `U ≥ 0` has Bessel-bounded
`eNorm`-weighted energy, `∑_{m≤N} eNorm m · U m² ≤ H` for every `N`, then

  `∑_{m≤N} U m / √(m+1) ≤ 2 √H`  for every `N`,

because `U m/√(m+1) = (√(eNorm m)·U m)·(1/(√(eNorm m)·√(m+1)))`, Cauchy–Schwarz over the
finite range gives `√(∑ eNorm m U m²)·√(∑ 1/(eNorm m (m+1)))`, and `m + 1 ≤ eNorm m`
(so `∑_{m≤N} 1/(eNorm m (m+1)) ≤ 1 + ∑_{m=1}^{N} 1/(m(m+1)) ≤ 2`); hence the constant `2`. -/
theorem sum_sqrt_eNorm_le {U : ℕ → ℝ} (hU : ∀ m : ℕ, 0 ≤ U m) {H : ℝ} (hH : 0 ≤ H)
    (hB : ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1),
      Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2 ≤ H) :
    ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1), U m / Real.sqrt ((m : ℝ) + 1)
      ≤ 2 * Real.sqrt H := by
  intro N
  -- The two Cauchy–Schwarz factors `√(f m)` and `√(g m)` multiply to `U m / √(m+1)`.
  have hf : ∀ m : ℕ, 0 ≤ Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2 :=
    fun m => mul_nonneg (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m)) (sq_nonneg _)
  have hg : ∀ m : ℕ, 0 ≤ (Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹ :=
    fun m => inv_nonneg.2 (mul_nonneg (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m))
      (by positivity))
  have hterm : ∀ m ∈ Finset.range (N + 1),
      Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2)
        * Real.sqrt ((Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹)
      = U m / Real.sqrt ((m : ℝ) + 1) := by
    intro m _
    have hE := Work.EllipticEst.ModalSolution.eNorm_pos m
    have h1 : Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2)
        = Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) * U m := by
      rw [Real.sqrt_mul (le_of_lt hE), Real.sqrt_sq (hU m)]
    have h2 : Real.sqrt ((Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹)
        = (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Real.sqrt ((m : ℝ) + 1))⁻¹ := by
      rw [Real.sqrt_inv, Real.sqrt_mul (le_of_lt hE)]
    rw [h1, h2]
    have hne : Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hE)
    have hne2 : Real.sqrt ((m : ℝ) + 1) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by positivity))
    field_simp
  calc ∑ m ∈ Finset.range (N + 1), U m / Real.sqrt ((m : ℝ) + 1)
      = ∑ m ∈ Finset.range (N + 1),
          Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2)
            * Real.sqrt ((Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹) :=
        (Finset.sum_congr rfl fun m hm => (hterm m hm).symm)
    _ ≤ Real.sqrt (∑ m ∈ Finset.range (N + 1),
            Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2)
          * Real.sqrt (∑ m ∈ Finset.range (N + 1),
            (Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹) :=
        Real.sum_sqrt_mul_sqrt_le _ hf hg
    _ ≤ Real.sqrt H * Real.sqrt 2 := by
        refine mul_le_mul (Real.sqrt_le_sqrt (hB N)) (Real.sqrt_le_sqrt (sum_inv_eNorm_mul_le_two N))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg H)
    _ ≤ 2 * Real.sqrt H := by
        have h2 : Real.sqrt 2 ≤ 2 := by
          have := Real.sqrt_two_lt_three_halves
          linarith
        have h3 : Real.sqrt H * Real.sqrt 2 ≤ Real.sqrt H * 2 :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg H)
        linarith

end Work.FTS.PhiStar.Honesty.DiffGreen
