import Mathlib
import Submission.Work.BMF.halasz_plancherel_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Expanding `‖dirSum‖²` as a double sum

The truncated Dirichlet series `dirSum f α N τ = Σ_{n ≤ N} f n log n · n^{-(1+α+iτ)}`
is a finite sum of exponentials in `τ`; the purpose of this file is to record that its
squared modulus is a finite double sum of exponentials, so that the integral in `τ` of
`‖dirSum‖² / ‖(1+α) + iτ‖²` can be evaluated term by term (see
`Submission.Work.BMF.integral_dirSum_sq`).
-/

open Complex MeasureTheory Real Finset

set_option maxHeartbeats 1000000

namespace Work.BMF

/-- The `n`-th coefficient of the truncated Dirichlet series, with the modulus part
`n^{-(1+α)}` split off: `cz f α n = f n · log n · n^{-(1+α)}`. -/
noncomputable def cz (f : ℕ → ℂ) (α : ℝ) (n : ℕ) : ℂ :=
  f n * (Real.log n : ℂ) * (((n : ℝ) ^ (-(1 + α)) : ℝ) : ℂ)

/-- The oscillatory factor `exp (-i τ log n)`. -/
noncomputable def ee (n : ℕ) (τ : ℝ) : ℂ :=
  Complex.exp (((Real.log n * (-τ) : ℝ) : ℂ) * Complex.I)

/-- Splitting a positive real power of a natural number into modulus and phase. -/
lemma cpow_lemma (n : ℕ) (hn : 0 < n) (a b : ℝ) :
    (n : ℂ) ^ ((a : ℂ) + (b : ℂ) * Complex.I)
      = (((n : ℝ) ^ a : ℝ) : ℂ) * Complex.exp (((Real.log n * b : ℝ) : ℂ) * Complex.I) := by
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hnne, ← Complex.natCast_log]
  rw [show (↑(Real.log n) : ℂ) * (↑a + ↑b * Complex.I)
        = ↑(Real.log n * a) + ↑(Real.log n * b) * Complex.I by push_cast; ring]
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.rpow_def_of_pos hnpos]

/-- `dirSum` written as a sum of coefficients times oscillatory factors. -/
lemma dirSum_eq (f : ℕ → ℂ) (α : ℝ) (N : ℕ) (τ : ℝ) :
    dirSum f α N τ = ∑ n ∈ Icc 1 N, cz f α n * ee n τ := by
  rw [dirSum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : 0 < n := hn1
  have harg : -(((1+α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
      = ((-(1+α) : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [harg, cpow_lemma n hn0 (-(1+α)) (-τ), cz, ee]
  ring

/-- The product of the oscillatory factor of `m` with the conjugate of the one of `n`. -/
lemma ee_mul_conj (m n : ℕ) (τ : ℝ) :
    ee m τ * starRingEnd ℂ (ee n τ)
      = Complex.exp (((-(Real.log m - Real.log n) * τ : ℝ) : ℂ) * Complex.I) := by
  simp only [ee]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Expansion of `‖dirSum f α N τ‖²` as a double sum of exponentials. -/
lemma dirSum_normSq (f : ℕ → ℂ) (α : ℝ) (N : ℕ) (τ : ℝ) :
    ‖dirSum f α N τ‖ ^ 2
      = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          (cz f α m * starRingEnd ℂ (cz f α n)
            * Complex.exp (((-(Real.log m - Real.log n) * τ : ℝ) : ℂ) * Complex.I)).re := by
  rw [dirSum_eq]
  have hmc : ∀ z : ℂ, ‖z‖ ^ 2 = (z * starRingEnd ℂ z).re := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj, Complex.ofReal_re]
  rw [hmc]
  rw [map_sum, Finset.sum_mul_sum]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul]
  congr 1
  rw [show cz f α m * ee m τ * (starRingEnd ℂ (cz f α n) * starRingEnd ℂ (ee n τ))
      = cz f α m * starRingEnd ℂ (cz f α n) * (ee m τ * starRingEnd ℂ (ee n τ)) by ring]
  rw [ee_mul_conj m n τ]

/-- The elementary identity `m^{-β} n^{-β} exp (-β|log m - log n|) = (max m n)^{-2β}`
for `m, n ≥ 1` and any real `β`. -/
theorem rpow_exp_abs_log (β : ℝ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (m : ℝ) ^ (-β) * (n : ℝ) ^ (-β) * Real.exp (-(β * |Real.log m - Real.log n|))
      = (((max m n : ℕ) : ℝ) ^ (-(2 * β))) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hmβ : (m : ℝ) ^ (-β) * (m : ℝ) ^ β = 1 := by
    rw [← Real.rpow_add hm0, show -β + β = 0 by ring, Real.rpow_zero]
  have hnβ : (n : ℝ) ^ (-β) * (n : ℝ) ^ β = 1 := by
    rw [← Real.rpow_add hn0, show -β + β = 0 by ring, Real.rpow_zero]
  have hmm : (m : ℝ) ^ (-β) * (m : ℝ) ^ (-β) = (m : ℝ) ^ (-(2 * β)) := by
    rw [← Real.rpow_add hm0, show -β + -β = -(2 * β) by ring]
  have hnn : (n : ℝ) ^ (-β) * (n : ℝ) ^ (-β) = (n : ℝ) ^ (-(2 * β)) := by
    rw [← Real.rpow_add hn0, show -β + -β = -(2 * β) by ring]
  rcases le_total m n with hmn | hmn
  · rw [max_eq_right hmn]
    have hle : Real.log m ≤ Real.log n := Real.log_le_log hm0 (by exact_mod_cast hmn)
    rw [abs_of_nonpos (by linarith : Real.log m - Real.log n ≤ 0)]
    have h1 : Real.exp (-(β * -(Real.log m - Real.log n))) = (m:ℝ)^β * (n:ℝ)^(-β) := by
      rw [show -(β * -(Real.log m - Real.log n)) = β * Real.log m + (-β) * Real.log n by ring,
        Real.exp_add, Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hn0]
      ring_nf
    rw [h1]
    rw [show ((m:ℝ)^(-β)) * ((n:ℝ)^(-β)) * ((m:ℝ)^β * (n:ℝ)^(-β))
          = ((m:ℝ)^(-β) * (m:ℝ)^β) * ((n:ℝ)^(-β) * (n:ℝ)^(-β)) by ring,
      hmβ, one_mul, hnn]
  · rw [max_eq_left hmn]
    have hle : Real.log n ≤ Real.log m := Real.log_le_log hn0 (by exact_mod_cast hmn)
    rw [abs_of_nonneg (by linarith : 0 ≤ Real.log m - Real.log n)]
    have h1 : Real.exp (-(β * (Real.log m - Real.log n))) = (m:ℝ)^(-β) * (n:ℝ)^β := by
      rw [show -(β * (Real.log m - Real.log n)) = (-β) * Real.log m + β * Real.log n by ring,
        Real.exp_add, Real.rpow_def_of_pos hm0, Real.rpow_def_of_pos hn0]
      ring_nf
    rw [h1]
    rw [show ((m:ℝ)^(-β)) * ((n:ℝ)^(-β)) * ((m:ℝ)^(-β) * (n:ℝ)^β)
          = ((m:ℝ)^(-β) * (m:ℝ)^(-β)) * ((n:ℝ)^(-β) * (n:ℝ)^β) by ring,
      hmm, hnβ, mul_one]

/-- The summand of the Cauchy-kernel integral in terms of the `UN` summand. -/
lemma summand_eq (f : ℕ → ℂ) (α : ℝ) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (cz f α m * starRingEnd ℂ (cz f α n)).re
        * Real.exp (-((1+α) * |Real.log m - Real.log n|))
      = ((f m * (Real.log m : ℂ)) * starRingEnd ℂ (f n * (Real.log n : ℂ))).re
          * (((max m n : ℕ) : ℝ) ^ (-(2 + 2 * α))) := by
  have hcz : cz f α m * starRingEnd ℂ (cz f α n)
      = ((f m * (Real.log m : ℂ)) * starRingEnd ℂ (f n * (Real.log n : ℂ)))
        * ((((m:ℝ)^(-(1+α)) * (n:ℝ)^(-(1+α))) : ℝ) : ℂ) := by
    simp only [cz, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  rw [hcz, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_assoc]
  rw [show ((m:ℝ)^(-(1+α)) * (n:ℝ)^(-(1+α)) * Real.exp (-((1+α) * |Real.log m - Real.log n|)))
        = (((max m n : ℕ) : ℝ) ^ (-(2 + 2 * α))) by
      rw [rpow_exp_abs_log (1+α) hm hn, show (2 * (1+α)) = (2+2*α) by ring]]

end Work.BMF
