import Mathlib
import Submission.Work.Asymptotics.kernelTransform_seminorm_cuspHalf_TS_prelude
import Submission.Work.Asymptotics.TSasm.AexpGcusp24T2

namespace Work.Asymptotics

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology

noncomputable section

/-!
# Flatness and the cusp tail at the `T`-translate `1 + u`

For `u ∈ Tregion` with `Re u ≥ 1/4` the point `1 + u` is not in `𝒟`, but the kernel and the cusp
model at `1 + u` are the `T`-ladder combinations of their values at `u` and `u - 1` (both in
`𝒟`), so uniform flatness in `t → 0⁺` and the cusp-`i∞` tail estimate transfer from there.

## Main results

* `Work.Asymptotics.flat_vadd_one`;
* `Work.Asymptotics.tail_vadd_one`.
-/

/-- **Flatness of the kernel at `1 + u`** (for `u ∈ Tregion` with `Re u ≥ 1/4`). -/
theorem flat_vadd_one (ℓ : Work.Kernels.LogLambdaData) (u : ℍ)
    (hu : u ∈ Work.Asymptotics.Tregion) (hx : (1 : ℝ) / 4 ≤ u.re) :
    ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((1 : ℝ) +ᵥ u) t‖ ≤ c * t ^ N := by
  intro N hN
  have huD : u ∈ Work.Asymptotics.DomainD := hu.1
  have hx0 : 0 < u.re := by linarith
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD :=
    Work.Asymptotics.ts_vadd_neg_one_mem_DomainD_of_pos huD hx0
  obtain ⟨c1, hc1, h1⟩ := Work.Asymptotics.MFix.Kaxis_local_flat ℓ 24 (Or.inr rfl)
    (K := ({u} : Set ℍ)) isCompact_singleton (by rintro x rfl; exact huD) N hN
  obtain ⟨c2, hc2, h2⟩ := Work.Asymptotics.MFix.Kaxis_local_flat ℓ 24 (Or.inr rfl)
    (K := ({((-1 : ℝ) +ᵥ u)} : Set ℍ)) isCompact_singleton
    (by rintro x rfl; exact hu1D) N hN
  refine ⟨2 * c1 + c2, by positivity, fun t ht ht1 => ?_⟩
  have hK := Work.Asymptotics.Kaxis_T2_Kfun_s ℓ 24 (Or.inr rfl) ((-1 : ℝ) +ᵥ u) t
  rw [show ((2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u)) = ((1 : ℝ) +ᵥ u) from by rw [vadd_vadd]; norm_num,
      show ((1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u)) = u from by rw [vadd_vadd]; norm_num] at hK
  have hval : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((1 : ℝ) +ᵥ u) t
      = 2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t
        - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t := by
    linear_combination hK
  have b1 := h1 u t (by simp) ht ht1
  have b2 := h2 ((-1 : ℝ) +ᵥ u) t (by simp) ht ht1
  rw [hval]
  calc ‖2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t
        - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t‖
      ≤ ‖2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t‖
        + ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t‖ := norm_sub_le _ _
    _ = 2 * ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t‖
        + ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t‖ := by
        rw [norm_mul]; norm_num
    _ ≤ 2 * (c1 * t ^ N) + c2 * t ^ N := by linarith [b1, b2]
    _ = (2 * c1 + c2) * t ^ N := by ring

/-- **The cusp-`i∞` tail estimate at `1 + u`** (for `u ∈ Tregion` with `Re u ≥ 1/4`). -/
theorem tail_vadd_one (ℓ : Work.Kernels.LogLambdaData) (u : ℍ)
    (hu : u ∈ Work.Asymptotics.Tregion) (hx : (1 : ℝ) / 4 ≤ u.re) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ t : ℝ, 1 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((1 : ℝ) +ᵥ u) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((1 : ℝ) +ᵥ u) t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  have huD : u ∈ Work.Asymptotics.DomainD := hu.1
  have hx0 : 0 < u.re := by linarith
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD :=
    Work.Asymptotics.ts_vadd_neg_one_mem_DomainD_of_pos huD hx0
  obtain ⟨C1, M1, T1, hC1, hM1, hT1, hb1⟩ := Work.HFN.cusp_expansion_of_kernel ℓ 24
    (Or.inr rfl) (K := ({u} : Set ℍ)) isCompact_singleton (by rintro x rfl; exact huD)
  obtain ⟨C2, M2, T2, hC2, hM2, hT2, hb2⟩ := Work.HFN.cusp_expansion_of_kernel ℓ 24
    (Or.inr rfl) (K := ({((-1 : ℝ) +ᵥ u)} : Set ℍ)) isCompact_singleton
    (by rintro x rfl; exact hu1D)
  set D1 : ℝ := C1 * Real.exp (Real.pi * T1) with hD1
  set D2 : ℝ := C2 * Real.exp (Real.pi * T2) with hD2
  refine ⟨2 * D1 + D2, max M1 M2, 0, by positivity,
    le_trans hM1 (le_max_left M1 M2), le_rfl, fun t ht => ?_⟩
  have hK := Work.Asymptotics.Kaxis_T2_Kfun_s ℓ 24 (Or.inr rfl) ((-1 : ℝ) +ᵥ u) t
  rw [show ((2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u)) = ((1 : ℝ) +ᵥ u) from by rw [vadd_vadd]; norm_num,
      show ((1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u)) = u from by rw [vadd_vadd]; norm_num] at hK
  have hA := Work.Asymptotics.T2aux.Aexp_Gcusp24_T2 ℓ ((-1 : ℝ) +ᵥ u) t
  rw [show ((2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u)) = ((1 : ℝ) +ᵥ u) from by rw [vadd_vadd]; norm_num,
      show ((1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u)) = u from by rw [vadd_vadd]; norm_num] at hA
  have b1 := hb1 u t (by simp) ht
  have b2 := hb2 ((-1 : ℝ) +ᵥ u) t (by simp) ht
  have hval : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((1 : ℝ) +ᵥ u) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((1 : ℝ) +ᵥ u) t
      = 2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) u t)
        - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((-1 : ℝ) +ᵥ u) t) := by
    linear_combination hK - hA
  have hp1 : (1 + t) ^ M1 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hp2 : (1 + t) ^ M2 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
  have hbase : (0 : ℝ) ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_nonneg (by linarith) _
  have hexp1 : Real.exp (-(Real.pi * (t - T1))) = Real.exp (Real.pi * T1) * Real.exp (-(Real.pi * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp2 : Real.exp (-(Real.pi * (t - T2))) = Real.exp (Real.pi * T2) * Real.exp (-(Real.pi * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e1 : C1 * (1 + t) ^ M1 * Real.exp (-(Real.pi * (t - T1)))
      ≤ D1 * (1 + t) ^ (max M1 M2) * Real.exp (-(Real.pi * (t - 0))) := by
    rw [hexp1]
    have hD1' : (0:ℝ) ≤ D1 := by rw [hD1]; positivity
    have hpt : (0:ℝ) ≤ (1 + t) ^ M1 := Real.rpow_nonneg (by linarith) _
    have he : (0:ℝ) < Real.exp (Real.pi * T1) := Real.exp_pos _
    have hcombo : C1 * Real.exp (Real.pi * T1) ≤ D1 := by rw [hD1]
    calc C1 * (1 + t) ^ M1 * (Real.exp (Real.pi * T1) * Real.exp (-(Real.pi * t)))
        = (C1 * Real.exp (Real.pi * T1)) * (1 + t) ^ M1 * Real.exp (-(Real.pi * t)) := by ring
      _ ≤ D1 * (1 + t) ^ (max M1 M2) * Real.exp (-(Real.pi * t)) := by
          have h1 : (C1 * Real.exp (Real.pi * T1)) * (1 + t) ^ M1
              ≤ D1 * (1 + t) ^ (max M1 M2) := by
            have := mul_le_mul hcombo hp1 hpt hD1'
            simpa only [mul_assoc] using this
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = D1 * (1 + t) ^ (max M1 M2) * Real.exp (-(Real.pi * (t - 0))) := by
          rw [show (t - 0 : ℝ) = t by ring]
  have e2 : C2 * (1 + t) ^ M2 * Real.exp (-(Real.pi * (t - T2)))
      ≤ D2 * (1 + t) ^ (max M1 M2) * Real.exp (-(Real.pi * (t - 0))) := by
    rw [hexp2]
    have hD2' : (0:ℝ) ≤ D2 := by rw [hD2]; positivity
    have hpt : (0:ℝ) ≤ (1 + t) ^ M2 := Real.rpow_nonneg (by linarith) _
    have hcombo : C2 * Real.exp (Real.pi * T2) ≤ D2 := by rw [hD2]
    calc C2 * (1 + t) ^ M2 * (Real.exp (Real.pi * T2) * Real.exp (-(Real.pi * t)))
        = (C2 * Real.exp (Real.pi * T2)) * (1 + t) ^ M2 * Real.exp (-(Real.pi * t)) := by ring
      _ ≤ D2 * (1 + t) ^ (max M1 M2) * Real.exp (-(Real.pi * t)) := by
          have h1 : (C2 * Real.exp (Real.pi * T2)) * (1 + t) ^ M2
              ≤ D2 * (1 + t) ^ (max M1 M2) := by
            have := mul_le_mul hcombo hp2 hpt hD2'
            simpa only [mul_assoc] using this
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = D2 * (1 + t) ^ (max M1 M2) * Real.exp (-(Real.pi * (t - 0))) := by
          rw [show (t - 0 : ℝ) = t by ring]
  rw [hval]
  calc ‖2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) u t)
        - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((-1 : ℝ) +ᵥ u) t)‖
      ≤ ‖2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) u t)‖
        + ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((-1 : ℝ) +ᵥ u) t‖ :=
        norm_sub_le _ _
    _ = 2 * ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) u t‖
        + ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((-1 : ℝ) +ᵥ u) t‖ := by
        rw [norm_mul]; norm_num
    _ ≤ 2 * (C1 * (1 + t) ^ M1 * Real.exp (-(Real.pi * (t - T1))))
        + C2 * (1 + t) ^ M2 * Real.exp (-(Real.pi * (t - T2))) := by linarith [b1, b2]
    _ ≤ 2 * (D1 * (1 + t) ^ (max M1 M2) * Real.exp (-(Real.pi * (t - 0))))
        + D2 * (1 + t) ^ (max M1 M2) * Real.exp (-(Real.pi * (t - 0))) := by linarith [e1, e2]
    _ = (2 * D1 + D2) * (1 + t) ^ (max M1 M2) * Real.exp (-(Real.pi * (t - 0))) := by ring

end

end Work.Asymptotics
