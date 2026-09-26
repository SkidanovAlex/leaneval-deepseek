import Mathlib
import Submission.Work.CKFinal.bound_of_propagates_uniform
import Submission.Work.CKFinal.DQDefs
import Submission.Work.CKFinal.snd_deriv_dq_bound
import Submission.Work.CKFinal.dqDiff_propagates
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.DomainD

namespace Work.CKFinal

/-- Quantitative propagation estimate for the difference quotients of a family of global
solutions `G r` of `T2op (G r) = H r`, `S2op k (G r) = 0`: the difference quotients of `G` in the
family parameter are Cauchy on `ℍ`, with a bound linear in the step sizes. -/
theorem dq_propagation (k : ℤ) (Nf : ℝ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (G H : ℝ → UpperHalfPlane → ℂ) (CG CH NG NH : ℝ),
        0 ≤ CG → 0 ≤ CH → NG ≤ Nf → NH ≤ Nf →
        (∀ r : ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (G r)) →
        (∀ (l : ℕ) (r : ℝ), MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (fun τ : UpperHalfPlane => iteratedDeriv l (fun s : ℝ => H s τ) r)) →
        (∀ (r : ℝ) (τ : UpperHalfPlane), Work.Kernels.T2op (G r) τ = H r τ) →
        (∀ (r : ℝ) (τ : UpperHalfPlane), Work.Asymptotics.S2op k (G r) τ = 0) →
        (∀ (τ : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD →
          (∀ x : ℝ, DifferentiableAt ℝ (fun s : ℝ => G s τ) x) ∧
          (∀ x : ℝ, DifferentiableAt ℝ (deriv (fun s : ℝ => G s τ)) x)) →
        (∀ (τ : UpperHalfPlane),
          (∀ x : ℝ, DifferentiableAt ℝ (fun s : ℝ => H s τ) x) ∧
          (∀ x : ℝ, DifferentiableAt ℝ (deriv (fun s : ℝ => H s τ)) x)) →
        (∀ τ ∈ Work.Asymptotics.DomainD, ∀ x : ℝ,
          ‖deriv (deriv (fun s : ℝ => G s τ)) x‖ ≤ CG * (Work.Kernels.scale τ) ^ NG) →
        (∀ τ : UpperHalfPlane, ∀ x : ℝ,
          ‖deriv (deriv (fun s : ℝ => H s τ)) x‖ ≤ CH * (Work.Kernels.scale τ) ^ NH) →
        ∀ (r a b : ℝ) (τ : UpperHalfPlane), a ≠ 0 → b ≠ 0 →
          ‖(G (r + a) τ - G r τ) / a - (G (r + b) τ - G r τ) / b‖
            ≤ C * (CG + CH) * (|a| + |b|) * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨C₀, N₀, hC₀, hN₀, hprop⟩ := Work.CKFinal.bound_of_propagates_uniform k Nf
  refine ⟨C₀, N₀, hC₀, hN₀, ?_⟩
  intro G H CG CH NG NH hCG hCH hNG hNH hGmd hHiter hT hS hGd hHd hGb hHb r a b τ ha hb
  -- the functions `H s` are holomorphic in `τ`
  have hHmd : ∀ s : ℝ,
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (H s) :=
    fun s => by simpa [iteratedDeriv_zero] using hHiter 0 s
  -- the second difference of difference quotients satisfies the propagation hypotheses
  have hProp : Work.Asymptotics.Propagates k Set.univ (dqDiff G r a b) (dqDiff H r a b) 0 :=
    dqDiff_propagates k G H r a b hGmd hHmd hT hS
  -- the bound on `𝒟`, from the second-order mean value estimate
  have hbG : ∀ τ' ∈ Work.Asymptotics.DomainD,
      ‖dqDiff G r a b τ'‖ ≤ ((|a| + |b|) * CG) * (Work.Kernels.scale τ') ^ Nf := by
    intro τ' hτ'
    have h1 := snd_deriv_dq_bound (f := fun s : ℝ => G s τ')
      (C := CG * (Work.Kernels.scale τ') ^ NG) (hGd τ' hτ').1 (hGd τ' hτ').2 (hGb τ' hτ')
      r a b ha hb
    calc ‖dqDiff G r a b τ'‖
        = ‖(G (r + a) τ' - G r τ') / a - (G (r + b) τ' - G r τ') / b‖ := by rw [dqDiff_apply]
      _ ≤ (|a| + |b|) * (CG * (Work.Kernels.scale τ') ^ NG) := h1
      _ = ((|a| + |b|) * CG) * (Work.Kernels.scale τ') ^ NG := by ring
      _ ≤ ((|a| + |b|) * CG) * (Work.Kernels.scale τ') ^ Nf := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (add_nonneg (abs_nonneg a)
            (abs_nonneg b)) hCG)
          exact Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ') hNG
  -- the bound for the defect, everywhere
  have hbH : ∀ τ' : UpperHalfPlane,
      ‖dqDiff H r a b τ'‖ ≤ ((|a| + |b|) * CH) * (Work.Kernels.scale τ') ^ Nf := by
    intro τ'
    have h1 := snd_deriv_dq_bound (f := fun s : ℝ => H s τ')
      (C := CH * (Work.Kernels.scale τ') ^ NH) (hHd τ').1 (hHd τ').2 (hHb τ') r a b ha hb
    calc ‖dqDiff H r a b τ'‖
        = ‖(H (r + a) τ' - H r τ') / a - (H (r + b) τ' - H r τ') / b‖ := by rw [dqDiff_apply]
      _ ≤ (|a| + |b|) * (CH * (Work.Kernels.scale τ') ^ NH) := h1
      _ = ((|a| + |b|) * CH) * (Work.Kernels.scale τ') ^ NH := by ring
      _ ≤ ((|a| + |b|) * CH) * (Work.Kernels.scale τ') ^ Nf := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (add_nonneg (abs_nonneg a)
            (abs_nonneg b)) hCH)
          exact Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ') hNH
  -- propagate
  have hmain := hprop (dqDiff G r a b) (dqDiff H r a b) 0 ((|a| + |b|) * CG)
    ((|a| + |b|) * CH) 0 hProp
    (mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b)) hCG)
    (mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b)) hCH) le_rfl hbG hbH
    (fun τ' => by simp) τ
  calc ‖(G (r + a) τ - G r τ) / a - (G (r + b) τ - G r τ) / b‖
      = ‖dqDiff G r a b τ‖ := by rw [dqDiff_apply]
    _ ≤ C₀ * (((|a| + |b|) * CG) + ((|a| + |b|) * CH) + 0) * (Work.Kernels.scale τ) ^ N₀ :=
        hmain
    _ = C₀ * (CG + CH) * (|a| + |b|) * (Work.Kernels.scale τ) ^ N₀ := by ring

end Work.CKFinal
