import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Submission.Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one

open Complex DirichletCharacter

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.DirichletCharacter

/-- The norm of the real `ζ`-Euler factor `(1 - p^{-σ})^{-1}`. -/
private lemma norm_zeta_eulerFactor (p : Nat.Primes) {σ : ℝ} (hσ : 0 < σ) :
    ‖(1 - (p : ℂ) ^ (-(σ : ℂ)))⁻¹‖ = (1 - (p : ℝ) ^ (-σ))⁻¹ := by
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast Nat.Prime.one_lt p.2
  have hppos : (0 : ℝ) ≤ (p : ℕ) := by positivity
  have hx1 : (p : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hc : (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by simp]
    exact (Complex.ofReal_cpow hppos (-σ)).symm
  have hsub : (1 : ℂ) - (((p : ℝ) ^ (-σ) : ℝ) : ℂ) = (((1 - (p : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
  rw [hc, hsub, ← Complex.ofReal_inv, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (by linarith))]

/-- Pointwise bound on the `L`-Euler factor by the `ζ`-Euler factor. -/
private lemma norm_L_eulerFactor_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    ‖1 - χ p * (p : ℂ) ^ (-s)‖ ≤ ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ := by
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast Nat.Prime.one_lt p.2
  have hspos : 0 < s.re := lt_trans zero_lt_one hs
  have hpn : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.Prime.pos p.2) (-s), Complex.neg_re]
  have hx0 : 0 ≤ (p : ℝ) ^ (-s.re) :=
    Real.rpow_nonneg (by positivity) _
  have h2 : ‖1 - χ p * (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ) ^ (-s.re) := by
    have h1 : ‖χ p * (p : ℂ) ^ (-s)‖ ≤ 1 * (p : ℝ) ^ (-s.re) := by
      rw [norm_mul, hpn]
      exact mul_le_mul (χ.norm_le_one (p : ZMod N)) le_rfl hx0 zero_le_one
    calc ‖1 - χ p * (p : ℂ) ^ (-s)‖
        ≤ ‖(1 : ℂ)‖ + ‖χ p * (p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ = 1 + ‖χ p * (p : ℂ) ^ (-s)‖ := by simp
      _ ≤ 1 + 1 * (p : ℝ) ^ (-s.re) := by linarith
      _ = 1 + (p : ℝ) ^ (-s.re) := by ring
  have hbase := norm_zeta_eulerFactor p hspos
  rw [hbase]
  have hx1 : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hpos : 0 < 1 - (p : ℝ) ^ (-s.re) := by linarith
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  nlinarith [sq_nonneg ((p : ℝ) ^ (-s.re))]

theorem LFunction_norm_ge_near_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    (s.re - 1) / 2 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have hspos : 0 < s.re := lt_trans zero_lt_one hs
  have hprod : HasProd (fun p : Nat.Primes => (1 - χ p * (p : ℂ) ^ (-s))⁻¹)
      (DirichletCharacter.LFunction χ s) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact DirichletCharacter.LSeries_eulerProduct_hasProd χ hs
  have hLne : DirichletCharacter.LFunction χ s ≠ 0 := by
    refine DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr ?_) (le_of_lt hs)
    intro h
    rw [h] at hs
    simp at hs
  have hprod_inv_norm : HasProd (fun p : Nat.Primes => ‖((1 - χ p * (p : ℂ) ^ (-s))⁻¹)⁻¹‖)
      ‖(DirichletCharacter.LFunction χ s)⁻¹‖ := (hprod.inv₀ hLne).norm
  have hbase : HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹)
      (riemannZeta ((s.re : ℝ) : ℂ)) :=
    riemannZeta_eulerProduct_hasProd (s := ((s.re : ℝ) : ℂ)) (by simpa using hs)
  have hbase_norm : HasProd (fun p : Nat.Primes => ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖)
      ‖riemannZeta ((s.re : ℝ) : ℂ)‖ := hbase.norm
  have hfin : ∀ S : Finset Nat.Primes,
      (∏ p ∈ S, ‖((1 - χ p * (p : ℂ) ^ (-s))⁻¹)⁻¹‖)
        ≤ ∏ p ∈ S, ‖(1 - (p : ℂ) ^ (-(s.re : ℂ)))⁻¹‖ := by
    intro S
    refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p _ => ?_)
    simpa only [inv_inv] using norm_L_eulerFactor_le χ hs p
  have hle : ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ ‖riemannZeta ((s.re : ℝ) : ℂ)‖ :=
    le_of_tendsto_of_tendsto' hprod_inv_norm hbase_norm hfin
  have hζ : ‖riemannZeta ((s.re : ℝ) : ℂ)‖ ≤ 2 / (s.re - 1) :=
    Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one hs hs2
  have hkey : ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ 2 / (s.re - 1) := le_trans hle hζ
  rw [norm_inv] at hkey
  have hLpos : 0 < ‖DirichletCharacter.LFunction χ s‖ := norm_pos_iff.mpr hLne
  have hvpos : 0 < 2 / (s.re - 1) := by
    apply div_pos (by norm_num)
    linarith
  have h2 : (2 / (s.re - 1))⁻¹ ≤ (‖DirichletCharacter.LFunction χ s‖⁻¹)⁻¹ :=
    (inv_le_inv₀ hvpos (inv_pos.mpr hLpos)).mpr hkey
  rw [inv_inv, inv_div] at h2
  exact h2

end Commons.NumberTheory.DirichletCharacter