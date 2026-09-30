import Mathlib
import Submission.Work.BW.mvdefs
import Submission.Work.BW.cosFourier_sub_cos
import Submission.Work.BW.fejer_cos_series_ge
import Submission.Work.BW.tsum_pow_div_shift

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

/-- The coefficient sequence of the tail `∑_{m} c_m cos(2π m t)` of the Fourier series of
`cosFourier ε`. -/
private noncomputable def tailCoeff (ε : ℝ) (m : ℕ) : ℝ := ε^(m+2)/((m:ℝ)+2)

private lemma tailCoeff_nonneg {ε : ℝ} (hε0 : 0 ≤ ε) (m : ℕ) : 0 ≤ tailCoeff ε m := by
  rw [tailCoeff]; positivity

private lemma tailCoeff_summable {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    Summable (tailCoeff ε) := by
  have hgeo : Summable (fun m : ℕ => ε^(m+2)) := by
    have h := summable_geometric_of_lt_one hε0 hε1
    simpa [pow_add, mul_comm] using h.mul_left (ε^2)
  refine Summable.of_norm_bounded hgeo (fun m => ?_)
  rw [tailCoeff, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (pow_nonneg hε0 _), abs_of_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ)+2)]
  have hle : (1:ℝ) ≤ (m:ℝ)+2 := by
    have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  calc ε^(m+2)/((m:ℝ)+2) ≤ ε^(m+2)/1 :=
        div_le_div_of_nonneg_left (pow_nonneg hε0 _) one_pos hle
    _ = ε^(m+2) := by ring

theorem fejer_cosFourier_tail_ge {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (K : ℕ) (θ ψ : ℝ) :
    -(1/2) * (Real.log (1/(1-ε)) - ε) ≤
      ∑ k ∈ Finset.Icc 1 K, fejerW K k * Real.cos (2*Real.pi*k*θ) *
        (cosFourier ε ((k:ℝ)*ψ) - ε * Real.cos (2*Real.pi*k*ψ)) := by
  have h := fejer_cos_series_ge (tailCoeff ε) (tailCoeff_nonneg hε0)
      (tailCoeff_summable hε0 hε1) K θ (fun m => ((m:ℝ)+2)*ψ)
  have hmass : (∑' m, tailCoeff ε m) = Real.log (1/(1-ε)) - ε := by
    simpa [tailCoeff] using tsum_pow_div_shift hε0 hε1
  rw [hmass] at h
  refine le_of_le_of_eq h ?_
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (2:ℝ)*Real.pi*(k:ℝ)*ψ = 2*Real.pi*((k:ℝ)*ψ) by ring,
    cosFourier_sub_cos hε0 hε1 ((k:ℝ)*ψ)]
  congr 1
  apply tsum_congr
  intro m
  rw [tailCoeff]
  congr 1
  ring

end Work.BW
