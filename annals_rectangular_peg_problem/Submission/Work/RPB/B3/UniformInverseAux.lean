import Mathlib

/-!
# Auxiliary definitions and lemmas for `Work.RPB.B3.uniformInverse`

This module holds the vocabulary shared between the main lemma `uniformInverse` and the
sub-lemmas delegated for it:

* `inverseR S ε₀ τ t σ` — the "uniform inverse" in the `ρ`-variable: for `σ` in the range of
  `ρ ↦ S τ t ρ` on `(-ε₀, ε₀)` it is the (classically chosen) preimage, and `0` otherwise.
* `continuous_deriv_rho` — continuity of the partial derivative `(τ,t,ρ) ↦ ∂_ρ S(τ,t,ρ)`.
-/

open scoped ContDiff

namespace Work.RPB.B3

noncomputable section

/-- Given `S : ℝ → ℝ → ℝ → ℝ`, the "uniform inverse" in the `ρ`-variable near `ρ = 0`: for `σ` in
the range of `ρ ↦ S τ t ρ` on the interval `(-ε₀, ε₀)` it is the (classically chosen) preimage;
otherwise it is `0`. -/
noncomputable def inverseR (S : ℝ → ℝ → ℝ → ℝ) (ε₀ τ t σ : ℝ) : ℝ := by
  classical
  exact if h : ∃ ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ S τ t ρ = σ then Classical.choose h else 0

theorem inverseR_spec {S : ℝ → ℝ → ℝ → ℝ} {ε₀ τ t σ : ℝ}
    (h : ∃ ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ S τ t ρ = σ) :
    inverseR S ε₀ τ t σ ∈ Set.Ioo (-ε₀) ε₀ ∧ S τ t (inverseR S ε₀ τ t σ) = σ := by
  unfold inverseR
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem inverseR_eq {S : ℝ → ℝ → ℝ → ℝ} {ε₀ τ t σ ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (-ε₀) ε₀) (hSρ : S τ t ρ = σ)
    (huniq : ∀ ρ', ρ' ∈ Set.Ioo (-ε₀) ε₀ → S τ t ρ' = σ → ρ' = ρ) :
    inverseR S ε₀ τ t σ = ρ := by
  have h : ∃ ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ S τ t ρ = σ := ⟨ρ, hρ, hSρ⟩
  exact huniq _ (inverseR_spec h).1 (inverseR_spec h).2

/-- Period reduction in the `t`-variable: a `2π`-periodic function on the `t`-line is determined
by its values on `[0, 2π]`. -/
theorem rpbPeriodReduce (S : ℝ → ℝ → ℝ → ℝ)
    (hper : ∀ τ t ρ, S τ (t + 2 * Real.pi) ρ = S τ t ρ) (τ t : ℝ) :
    ∃ t₀ ∈ Set.Icc (0:ℝ) (2 * Real.pi), ∀ ρ, S τ t ρ = S τ t₀ ρ := by
  set k : ℤ := ⌊t / (2 * Real.pi)⌋ with hk
  refine ⟨t - k * (2 * Real.pi), ?_, ?_⟩
  · constructor
    · have h2pi : 0 < (2 : ℝ) * Real.pi := by positivity
      have h1 : (k : ℝ) ≤ t / (2 * Real.pi) := by
        rw [hk]; exact Int.floor_le _
      have h2 := (le_div_iff₀ h2pi).mp h1
      linarith
    · have h2pi : 0 < (2 : ℝ) * Real.pi := by positivity
      have h1 : t / (2 * Real.pi) < (k : ℝ) + 1 := by
        rw [hk]; exact Int.lt_floor_add_one _
      have h2 := (div_lt_iff₀ h2pi).mp h1
      linarith
  · intro ρ
    have hperf : Function.Periodic (fun s : ℝ => S τ s ρ) (2 * Real.pi) := fun s => hper τ s ρ
    have h := (hperf.int_mul k) (t - k * (2 * Real.pi))
    have harg : (t - k * (2 * Real.pi)) + k * (2 * Real.pi) = t := by ring
    rw [harg] at h
    exact h

/-- The partial derivative of `S` in the `ρ`-variable is continuous, jointly in `(τ,t,ρ)`. -/
theorem continuous_deriv_rho (S : ℝ → ℝ → ℝ → ℝ)
    (hS : ContDiff ℝ 4 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)) :
    Continuous fun p : ℝ × (ℝ × ℝ) => deriv (fun ρ => S p.1 p.2.1 ρ) p.2.2 := by
  have hfd : Continuous (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)) :=
    ContDiff.continuous_fderiv hS (by norm_num)
  have hkey : (fun p : ℝ × (ℝ × ℝ) => deriv (fun ρ => S p.1 p.2.1 ρ) p.2.2)
      = fun p => fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) p (0, (0, 1)) := by
    funext p
    rw [deriv]
    have hslice : (fun ρ : ℝ => S p.1 p.2.1 ρ)
        = (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) ∘ (fun r : ℝ => (p.1, (p.2.1, r))) :=
      rfl
    rw [hslice]
    have hm : HasFDerivAt (fun r : ℝ => (p.1, (p.2.1, r)))
        ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.inr ℝ ℝ ℝ)) p.2.2 := by
      simpa using (hasFDerivAt_const (p.1 : ℝ) (p.2.2 : ℝ)).prodMk
        (hasFDerivAt_prodMk_right (p.2.1 : ℝ) (p.2.2 : ℝ))
    have hSfd : HasFDerivAt (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)
        (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) p) p :=
      (hS.differentiable (by norm_num) p).hasFDerivAt
    rw [(hSfd.comp p.2.2 hm).fderiv]
    simp [ContinuousLinearMap.comp_apply]
  rw [hkey]
  exact hfd.clm_apply continuous_const

end

end Work.RPB.B3
