import Mathlib
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert

namespace Work.KMTAreas

open Finset

/-- **Khintchine's inequality (upper bound), orthonormal-basis form.**

For every `p ≥ 1` there is `C > 0` such that for every finite-dimensional complex Hilbert
space `H` and every `x : H`, the average over the `2^{dim H}` sign choices `ε` of
`|⟨∑ᵢ εᵢ eᵢ, x⟩|^p` is at most `(C p^{1/2})^p ‖x‖^p`, where `e` is the standard orthonormal
basis of `H`.  Equivalently: `‖∑ᵢ εᵢ xᵢ‖_{L^p(ε)} ≤ C p^{1/2} ‖x‖`. -/
theorem khintchine_upper_orthonormal_basis (p : ℝ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [FiniteDimensional ℂ H] (x : H),
      (ENNReal.ofReal ((2 : ℝ) ^ Module.finrank ℂ H))⁻¹ *
        ∑ ε : Fin (Module.finrank ℂ H) → Bool,
          enorm (inner ℂ (∑ i, (if ε i then (1 : ℂ) else -1) • (stdOrthonormalBasis ℂ H) i) x) ^ p
        ≤ ENNReal.ofReal ((C * p ^ ((1:ℝ)/2)) ^ p) * enorm x ^ p := by
  obtain ⟨c, C, _hc, hC, kh⟩ := Commons.Analysis.Walsh.exists_khintchine_hilbert p hp
  refine ⟨C, hC, ?_⟩
  intro H _ _ _ x
  set d := Module.finrank ℂ H with hd
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have htwo : (0:ℝ) < (2:ℝ)^d := by positivity
  -- abbreviation of the quantity we average
  set S : ℝ := ∑ ε : Fin d → Bool,
      ‖inner ℂ (∑ i, (if ε i then (1 : ℂ) else -1) • (stdOrthonormalBasis ℂ H) i) x‖ ^ p with hS
  -- the linear functional `y ↦ ⟨y, x⟩` on the sign sums
  have hFF : ∀ ε : Fin d → Bool,
      inner ℂ (∑ i, (if ε i then (1 : ℂ) else -1) • (stdOrthonormalBasis ℂ H) i) x
        = ∑ i, (if ε i then (1 : ℂ) else -1) • (inner ℂ ((stdOrthonormalBasis ℂ H) i) x) := by
    intro ε
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left]
    cases ε i <;> simp
  -- Parseval for the standard orthonormal basis
  have hpar : (∑ i : Fin d, ‖inner ℂ (stdOrthonormalBasis ℂ H i) x‖ ^ 2) = ‖x‖ ^ 2 := by
    have h := OrthonormalBasis.sum_sq_norm_inner_right (stdOrthonormalBasis ℂ H) x
    simpa only [hd] using h
  -- the sum in the form produced by Khintchine
  have hsumk : (∑ ε : Fin d → Bool,
        ‖∑ i, (if ε i then (1 : ℂ) else -1) • (inner ℂ ((stdOrthonormalBasis ℂ H) i) x)‖ ^ p) = S := by
    rw [hS]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [hFF ε]
  -- the value of the `L²` norm of the coordinate vector
  have hBx : (∑ i : Fin d, ‖inner ℂ (stdOrthonormalBasis ℂ H i) x‖ ^ 2) ^ ((1:ℝ)/2) = ‖x‖ := by
    rw [hpar, ← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x)]
    rw [show (((2:ℕ):ℝ)) * (1/2) = 1 by norm_num, Real.rpow_one]
  -- Khintchine, instantiated at the coordinates of `x`
  have hKh := (kh (H := ℂ) d (fun i : Fin d => inner ℂ ((stdOrthonormalBasis ℂ H) i) x)).2
  rw [hsumk, hBx] at hKh
  -- the real-variable inequality
  have hSnn : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun ε _ => Real.rpow_nonneg (norm_nonneg _) _
  have hreal : ((2:ℝ)^d)⁻¹ * S ≤ (C * p ^ ((1:ℝ)/2)) ^ p * ‖x‖ ^ p := by
    have hSd : 0 ≤ S / (2:ℝ)^d := div_nonneg hSnn htwo.le
    have hpoweq : ((S / (2:ℝ)^d) ^ ((1:ℝ)/p)) ^ p = S / (2:ℝ)^d := by
      rw [← Real.rpow_mul hSd]
      rw [one_div_mul_cancel hp0.ne', Real.rpow_one]
    have hmono : ((S / (2:ℝ)^d) ^ ((1:ℝ)/p)) ^ p ≤ (C * p ^ ((1:ℝ)/2) * ‖x‖) ^ p :=
      Real.rpow_le_rpow (Real.rpow_nonneg hSd _) hKh hp0.le
    have hmul : (C * p ^ ((1:ℝ)/2) * ‖x‖) ^ p = (C * p ^ ((1:ℝ)/2)) ^ p * ‖x‖ ^ p :=
      Real.mul_rpow (mul_nonneg hC.le (Real.rpow_nonneg hp0.le _)) (norm_nonneg x)
    rw [hpoweq, hmul] at hmono
    rwa [div_eq_inv_mul] at hmono
  -- convert to `ℝ≥0∞`
  have hL : (ENNReal.ofReal ((2:ℝ)^d))⁻¹ *
      (∑ ε : Fin d → Bool,
        enorm (inner ℂ (∑ i, (if ε i then (1 : ℂ) else -1) • (stdOrthonormalBasis ℂ H) i) x) ^ p)
      = ENNReal.ofReal (((2:ℝ)^d)⁻¹ * S) := by
    rw [hS]
    rw [ENNReal.ofReal_mul (le_of_lt (inv_pos.2 htwo))]
    rw [ENNReal.ofReal_inv_of_pos htwo]
    rw [ENNReal.ofReal_sum_of_nonneg
      (f := fun ε : Fin d → Bool =>
        ‖inner ℂ (∑ i, (if ε i then (1 : ℂ) else -1) • (stdOrthonormalBasis ℂ H) i) x‖ ^ p)
      (fun ε _ => Real.rpow_nonneg (norm_nonneg _) _)]
    congr 1
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [← ofReal_norm]
    exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le
  have hR : ENNReal.ofReal ((C * p ^ ((1:ℝ)/2)) ^ p) * enorm x ^ p
      = ENNReal.ofReal ((C * p ^ ((1:ℝ)/2)) ^ p * ‖x‖ ^ p) := by
    rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (C * p ^ ((1:ℝ)/2)) ^ p)]
    rw [show ENNReal.ofReal (‖x‖ ^ p) = ENNReal.ofReal ‖x‖ ^ p from
      (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg x) hp0.le).symm]
    rw [ofReal_norm]
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal hreal

end Work.KMTAreas
