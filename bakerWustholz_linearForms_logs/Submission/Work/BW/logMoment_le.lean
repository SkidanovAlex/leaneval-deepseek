import Mathlib
import Submission.Work.BW.mahlerDefs
import Submission.Work.BW.fejer_cos_sum_ge
import Submission.Work.BW.log_norm_exp_sub_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

/-! ### The Blanksby–Montgomery first-moment bound (their inequality (16))

The proof is Fourier-analytic.  For `0 < ε < 1`, real `θ` and `k : ℕ` the power series of the
complex logarithm gives

`log ‖1 - ε exp(2πi k θ)‖ = -∑_{m≥0} (ε^{m+1}/(m+1)) cos(2π(m+1)kθ) = -∑_{m≥0} c_m cos(m ψ)`

with `ψ = 2πkθ`.  Averaging over `k ≤ K` against the Fejér weights `w k = 1 - k/(K+1)` and using
the Fejér kernel bound `∑_{k=1}^K w k cos(kψ) ≥ -1/2` (proved in `fejer_cos_sum_ge`), each Fourier
mode contributes at most `(1/2) ∑_{m} ε^{m+1}/(m+1) = (1/2) log (1/(1-ε))`. -/

/-- **The Fourier expansion of a single logarithmic factor.**
For `0 < ε < 1`, `θ : ℝ` and `k : ℕ`,
`log ‖1 - ε exp(2πi k θ)‖ = -∑_{m} (ε^{m+1}/(m+1)) cos(2π(m+1)kθ)`. -/
private lemma log_norm_one_sub_exp_series (ε θ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ) :
    Real.log ‖(1:ℂ) - (ε:ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ:ℂ))‖
      = -∑' m : ℕ, (ε^(m+1)/((m:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ) := by
  have hkey := log_norm_exp_sub_one ε (le_of_lt hε0) hε1 (2*Real.pi*(k:ℝ)*θ)
  have hL : ‖(1:ℂ) - (ε:ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ:ℂ))‖
      = ‖(ε:ℂ) * Complex.exp (Complex.I * (((2*Real.pi*(k:ℝ)*θ : ℝ)) : ℂ)) - 1‖ := by
    rw [norm_sub_rev]
    congr 1
    rw [show (ε:ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ:ℂ))
        = (ε:ℂ) * Complex.exp (Complex.I * (((2*Real.pi*(k:ℝ)*θ : ℝ)) : ℂ)) from by
      congr 1
      push_cast
      ring_nf]
  rw [hL, hkey]
  congr 1
  refine tsum_congr (fun m => ?_)
  rw [show ((m:ℝ)+1) * (2*Real.pi*(k:ℝ)*θ) = 2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ from by ring]

/-- The series `∑_m (ε^{m+1}/(m+1)) · (Fejér-weighted cosine sum) ` converges absolutely. -/
private lemma summable_fejerW_cos_pow (ε θ : ℝ) (K : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Summable (fun m : ℕ => (ε^(m+1)/((m:ℝ)+1)) *
      (∑ k ∈ Finset.Icc 1 K,
        (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ))) := by
  have hAsumm : Summable (fun m : ℕ => ε^(m+1)/((m:ℝ)+1)) :=
    (Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_pos hε0])).summable
  have hA0 : ∀ m : ℕ, (0:ℝ) ≤ ε^(m+1)/((m:ℝ)+1) :=
    fun m => div_nonneg (pow_nonneg (le_of_lt hε0) _) (by positivity)
  have hKpos : (0:ℝ) < (K:ℝ)+1 := by positivity
  have hw0 : ∀ k ∈ Finset.Icc 1 K, (0:ℝ) ≤ 1 - (k:ℝ)/((K:ℝ)+1) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    have h1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
    have h2 : (k:ℝ) ≤ (K:ℝ) := by exact_mod_cast hk2
    rw [sub_nonneg, div_le_one hKpos]
    linarith
  have hw1 : ∀ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) ≤ 1 := by
    intro k hk
    have : (0:ℝ) ≤ (k:ℝ)/((K:ℝ)+1) := div_nonneg (by positivity) (le_of_lt hKpos)
    linarith
  have hcard : ((Finset.Icc 1 K).card : ℝ) = (K:ℝ) := by
    rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hCbdd : ∀ m : ℕ, |∑ k ∈ Finset.Icc 1 K,
        (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)| ≤ (K:ℝ) := by
    intro m
    calc |∑ k ∈ Finset.Icc 1 K,
            (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)|
        ≤ ∑ k ∈ Finset.Icc 1 K,
            |(1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k ∈ Finset.Icc 1 K,
            (1 - (k:ℝ)/((K:ℝ)+1)) * |Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)| := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [abs_mul, abs_of_nonneg (hw0 k hk)]
      _ ≤ ∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) * 1 := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (hw0 k hk)
      _ = ∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) := by simp
      _ ≤ ∑ k ∈ Finset.Icc 1 K, (1:ℝ) := Finset.sum_le_sum hw1
      _ = (K:ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  refine Summable.of_norm_bounded (g := fun m : ℕ => (K:ℝ) * (ε^(m+1)/((m:ℝ)+1)))
    (hAsumm.mul_left _) (fun m => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hA0 m)]
  have hb := hCbdd m
  nlinarith [hA0 m]

/-- `∑_{m≥0} ε^{m+1}/(m+1) = log (1/(1-ε))` for `0 < ε < 1`. -/
private lemma tsum_pow_div_eq_log (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∑' m : ℕ, ε^(m+1)/((m:ℝ)+1) = Real.log (1/(1-ε)) := by
  have h := (Real.hasSum_pow_div_log_of_abs_lt_one
    (by rwa [abs_of_pos hε0] : |ε| < 1)).tsum_eq
  rw [h, Real.log_div one_ne_zero (by linarith : (1:ℝ) - ε ≠ 0), Real.log_one]
  ring

/-- **The one-dimensional case.**  For a single `ε ∈ (0,1)` and `θ : ℝ`, the Fejér-weighted first
moment of `k ↦ log ‖1 - ε exp(2πi k θ)‖` is at most `(1/2) log (1/(1-ε))`. -/
private lemma logMoment_le_one (ε θ : ℝ) (K : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) *
        Real.log ‖(1:ℂ) - (ε:ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ:ℂ))‖
      ≤ (1/2) * Real.log (1/(1-ε)) := by
  have hAsumm : Summable (fun m : ℕ => ε^(m+1)/((m:ℝ)+1)) :=
    (Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_pos hε0])).summable
  have hA0 : ∀ m : ℕ, (0:ℝ) ≤ ε^(m+1)/((m:ℝ)+1) :=
    fun m => div_nonneg (pow_nonneg (le_of_lt hε0) _) (by positivity)
  have hcos_summ : ∀ k : ℕ, Summable (fun m : ℕ =>
      (ε^(m+1)/((m:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)) := by
    intro k
    refine Summable.of_norm_bounded (g := fun m : ℕ => ε^(m+1)/((m:ℝ)+1)) hAsumm (fun m => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hA0 m)]
    have h1 : |Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [hA0 m]
  have hC : ∀ m : ℕ, -(1/2:ℝ) ≤ ∑ k ∈ Finset.Icc 1 K,
      (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ) := by
    intro m
    have h := fejer_cos_sum_ge K (((m:ℝ)+1)*θ)
    have h' : (∑ k ∈ Finset.Icc 1 K,
          (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*(k:ℝ)*(((m:ℝ)+1)*θ)))
        = (∑ k ∈ Finset.Icc 1 K,
          (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show 2*Real.pi*(k:ℝ)*(((m:ℝ)+1)*θ) = 2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ from by ring]
    rwa [h'] at h
  have hsummable : ∀ k ∈ Finset.Icc 1 K, Summable (fun m : ℕ =>
      (1 - (k:ℝ)/((K:ℝ)+1)) *
        ((ε^(m+1)/((m:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ))) :=
    fun k _ => (hcos_summ k).mul_left _
  have hswap : (∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) *
          (-∑' m : ℕ, (ε^(m+1)/((m:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)))
      = -∑' m : ℕ, (ε^(m+1)/((m:ℝ)+1)) *
          (∑ k ∈ Finset.Icc 1 K,
            (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)) := by
    calc (∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) *
            (-∑' m : ℕ, (ε^(m+1)/((m:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)))
        = ∑ k ∈ Finset.Icc 1 K, -∑' m : ℕ, (1 - (k:ℝ)/((K:ℝ)+1)) *
            ((ε^(m+1)/((m:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [mul_neg, ← tsum_mul_left]
      _ = -∑ k ∈ Finset.Icc 1 K, ∑' m : ℕ, (1 - (k:ℝ)/((K:ℝ)+1)) *
            ((ε^(m+1)/((m:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)) :=
          Finset.sum_neg_distrib _
      _ = -∑' m : ℕ, ∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) *
            ((ε^(m+1)/((m:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)) := by
          rw [(Summable.tsum_finsetSum hsummable).symm]
      _ = -∑' m : ℕ, (ε^(m+1)/((m:ℝ)+1)) *
            (∑ k ∈ Finset.Icc 1 K,
              (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)) := by
          congr 1
          apply tsum_congr
          intro m
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
  have hACs : Summable (fun m : ℕ => (ε^(m+1)/((m:ℝ)+1)) *
      (∑ k ∈ Finset.Icc 1 K,
        (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ))) :=
    summable_fejerW_cos_pow ε θ K hε0 hε1
  have hle : ∀ m : ℕ, -((ε^(m+1)/((m:ℝ)+1)) *
      (∑ k ∈ Finset.Icc 1 K,
        (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)))
      ≤ (1/2) * (ε^(m+1)/((m:ℝ)+1)) := by
    intro m
    have h1 := hC m
    have h2 := hA0 m
    nlinarith [h1, h2]
  calc (∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) *
        Real.log ‖(1:ℂ) - (ε:ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ:ℂ))‖)
      = (∑ k ∈ Finset.Icc 1 K, (1 - (k:ℝ)/((K:ℝ)+1)) *
          (-∑' m : ℕ, (ε^(m+1)/((m:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ))) :=
        Finset.sum_congr rfl
          (fun k _ => by rw [log_norm_one_sub_exp_series ε θ hε0 hε1 k])
    _ = -∑' m : ℕ, (ε^(m+1)/((m:ℝ)+1)) *
          (∑ k ∈ Finset.Icc 1 K,
            (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ)) := hswap
    _ = ∑' m : ℕ, -((ε^(m+1)/((m:ℝ)+1)) *
          (∑ k ∈ Finset.Icc 1 K,
            (1 - (k:ℝ)/((K:ℝ)+1)) * Real.cos (2*Real.pi*((m:ℝ)+1)*(k:ℝ)*θ))) := by
        rw [tsum_neg]
    _ ≤ ∑' m : ℕ, (1/2) * (ε^(m+1)/((m:ℝ)+1)) :=
        Summable.tsum_le_tsum hle hACs.neg (hAsumm.mul_left _)
    _ = (1/2) * ∑' m : ℕ, ε^(m+1)/((m:ℝ)+1) := by rw [tsum_mul_left]
    _ = (1/2) * Real.log (1/(1-ε)) := by rw [tsum_pow_div_eq_log ε hε0 hε1]

/-- **Blanksby–Montgomery, Lemma 2, inequality (16)**: the Fejér-weighted first moment of
`σ k = ∑_j log ‖1 - ε_j exp(2πi k θ_j)‖` is at most `1/2 ∑_j log (1/(1-ε_j))`. -/
theorem logMoment_le {n : ℕ} (ε θ : Fin n → ℝ) (K : ℕ)
    (hε0 : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j < 1) :
    ∑ k ∈ Finset.Icc 1 K,
        (1 - (k:ℝ)/((K:ℝ)+1)) *
          (∑ j, Real.log ‖(1:ℂ) - (ε j : ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ j:ℂ))‖)
      ≤ (1/2) * ∑ j, Real.log (1/(1-ε j)) := by
  calc ∑ k ∈ Finset.Icc 1 K,
        (1 - (k:ℝ)/((K:ℝ)+1)) *
          (∑ j, Real.log ‖(1:ℂ) - (ε j : ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ j:ℂ))‖)
      = ∑ k ∈ Finset.Icc 1 K, ∑ j,
          (1 - (k:ℝ)/((K:ℝ)+1)) *
            Real.log ‖(1:ℂ) - (ε j : ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ j:ℂ))‖ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
    _ = ∑ j, ∑ k ∈ Finset.Icc 1 K,
          (1 - (k:ℝ)/((K:ℝ)+1)) *
            Real.log ‖(1:ℂ) - (ε j : ℂ) * Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ j:ℂ))‖ :=
        Finset.sum_comm
    _ ≤ ∑ j, (1/2) * Real.log (1/(1-ε j)) :=
        Finset.sum_le_sum (fun j _ => logMoment_le_one (ε j) (θ j) K (hε0 j) (hε1 j))
    _ = (1/2) * ∑ j, Real.log (1/(1-ε j)) := by rw [Finset.mul_sum]

end Work.BW
