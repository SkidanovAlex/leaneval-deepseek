import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/--
Range of `κU` under the existence hypothesis `κ ≤ exp τ · κU` for some `τ ∈ [0,T]`,
`T = Tscale κ`: this is the arithmetic core of EKL §4.5 (Step 8 of `ROUTE_LEAD.md` §5).
-/
theorem step8_kappaU_range {κ κU T : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hU0 : 0 < κU)
    (hUκ : κU ≤ κ) (hT : T = Tscale κ)
    (hex : ∃ τ ∈ Set.Icc 0 T, κ ≤ Real.exp τ * κU) :
    κ ^ (5 / 4 : ℝ) ≤ κU ∧ κU ≤ κ ∧ 4 * T ≤ -Real.log κU ∧ -Real.log κU ≤ 5 * T := by
  obtain ⟨τ, hτIcc, hτineq⟩ := hex
  rw [Set.mem_Icc] at hτIcc
  obtain ⟨hτ0, hτ1⟩ := hτIcc
  have hlogneg : Real.log κ < 0 := Real.log_neg hκ0 hκ1
  have hTeq : T = -(1 / 4 : ℝ) * Real.log κ := by
    rw [hT, Tscale, abs_of_neg hlogneg]; ring
  have h4T : 4 * T = -Real.log κ := by rw [hTeq]; ring
  have h5T : 5 * T = -(5 / 4) * Real.log κ := by rw [hTeq]; ring
  -- the key lower bound `κ^(5/4) ≤ κU`
  have hpow : κ ^ (5 / 4 : ℝ) ≤ κU := by
    have hexpT : Real.exp (-T) = κ ^ (1 / 4 : ℝ) := by
      rw [show -T = (1 / 4 : ℝ) * Real.log κ by rw [hTeq]; ring]
      rw [Real.rpow_def_of_pos hκ0]
      ring_nf
    have hkey : κ * Real.exp (-T) = κ ^ (5 / 4 : ℝ) := by
      rw [hexpT]
      nth_rewrite 1 [show κ = κ ^ (1 : ℝ) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hκ0]
      norm_num
    have h1 : κ * Real.exp (-T) ≤ κ * Real.exp (-τ) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hκ0.le
    have h2 : κ * Real.exp (-τ) ≤ κU := by
      have hmul := mul_le_mul_of_nonneg_left hτineq (Real.exp_pos (-τ)).le
      have e : Real.exp (-τ) * (Real.exp τ * κU) = κU := by
        rw [← mul_assoc, ← Real.exp_add]; simp
      rw [e] at hmul
      rwa [mul_comm (Real.exp (-τ)) κ] at hmul
    calc κ ^ (5 / 4 : ℝ) = κ * Real.exp (-T) := hkey.symm
      _ ≤ κ * Real.exp (-τ) := h1
      _ ≤ κU := h2
  refine ⟨hpow, hUκ, ?_, ?_⟩
  · -- `4 T ≤ -log κU` from `κU ≤ κ`
    have hlog : Real.log κU ≤ Real.log κ := Real.log_le_log hU0 hUκ
    linarith
  · -- `-log κU ≤ 5 T` from `κ^(5/4) ≤ κU`
    have hpos : 0 < κ ^ (5 / 4 : ℝ) := Real.rpow_pos_of_pos hκ0 _
    have hlog : Real.log (κ ^ (5 / 4 : ℝ)) ≤ Real.log κU := Real.log_le_log hpos hpow
    rw [Real.log_rpow hκ0] at hlog
    linarith

end Work.EKLC8Core
