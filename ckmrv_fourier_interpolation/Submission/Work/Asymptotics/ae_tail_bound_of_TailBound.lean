import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs

namespace Work.Asymptotics

/-- From `TailBound` the difference `K(τ,it) - 𝒢(τ,it)` satisfies a single exponential bound
`C·t^M·e^{-πt}` on all of `[1,∞)` for each fixed `τ ∈ 𝒟`: the polynomial bound on the window
`[1,(scale τ)^{N₀}]` (where `(scale τ)^{N₀} ≥ 1` is the threshold beyond which `TailBound` gives
exponential decay) is absorbed into `e^{-πt}` at the cost of the finite factor
`e^{π(scale τ)^{N₀}}`, and beyond the threshold the decay is used directly.  The constants may
depend on `τ`, which is exactly what differentiation under the `trunc` integral needs. -/
theorem ae_tail_bound_of_TailBound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hT : Work.Asymptotics.TailBound ℓ d G) (τ : UpperHalfPlane)
    (hτ : τ ∈ Work.Asymptotics.DomainD) :
    ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧ ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))),
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
        ≤ C * t ^ M * Real.exp (-(Real.pi * t)) := by
  -- The two regimes of `TailBound`: a polynomial bound on all of `[1,∞)`, and exponential
  -- decay `e^{-πt}` beyond the `τ`-dependent threshold `(scale τ)^{N₀}`.
  obtain ⟨C₁, N₁, M₁, hC₁, hN₁, hM₁, hP⟩ := hT.1
  obtain ⟨N₀, C₂, N₂, M₂, hN₀, hC₂, hN₂, hM₂, hE⟩ := hT.2
  -- Abbreviations for the fixed `τ`: `S = scale τ`, `T = S^{N₀} ≥ 1` the threshold.
  set S : ℝ := Work.Kernels.scale τ with hSdef
  set T : ℝ := S ^ N₀ with hTdef
  -- The exponential factor paid on the window `[1,T]`, and the two case constants.
  set A : ℝ := C₁ * S ^ N₁ * (1 + T) ^ M₁ * Real.exp (Real.pi * T) with hAdef
  set B : ℝ := C₂ * S ^ N₂ with hBdef
  set C : ℝ := max A B + 1 with hCdef
  set M : ℝ := max M₁ M₂ with hMdef
  have hS1 : 1 ≤ S := by rw [hSdef]; exact Work.Kernels.one_le_scale τ
  have hSpos : 0 < S := by rw [hSdef]; exact Work.Kernels.scale_pos τ
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Real.one_le_rpow hS1 hN₀
  have h1T : 0 < 1 + T := by linarith
  have hApos : 0 < A := by
    rw [hAdef]
    exact mul_pos (mul_pos (mul_pos hC₁ (Real.rpow_pos_of_pos hSpos N₁))
      (Real.rpow_pos_of_pos h1T M₁)) (Real.exp_pos _)
  have hAleC : A ≤ C := by rw [hCdef]; linarith [le_max_left A B]
  have hBleC : B ≤ C := by rw [hCdef]; linarith [le_max_right A B]
  have hCpos : 0 < C := by rw [hCdef]; linarith [le_max_left A B, hApos]
  have hMnn : 0 ≤ M := by rw [hMdef]; exact le_trans hM₁ (le_max_left M₁ M₂)
  refine ⟨C, M, hCpos, hMnn, ?_⟩
  -- The bound holds for *every* `t ≥ 1`; a fortiori almost everywhere.
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ici]
  refine Filter.Eventually.of_forall (fun t ht => ?_)
  have ht1 : 1 ≤ t := ht
  have htM : 1 ≤ t ^ M := Real.one_le_rpow ht1 hMnn
  rcases le_total t T with htT | hTt
  · -- On the window `1 ≤ t ≤ T`: absorb the polynomial growth into `e^{-πt}`.
    have hpoly := hP τ hτ t ht1
    rw [← hSdef] at hpoly
    have hCS : 0 ≤ C₁ * S ^ N₁ := mul_nonneg hC₁.le (Real.rpow_nonneg hSpos.le N₁)
    have hle1 : (1 + t) ^ M₁ ≤ (1 + T) ^ M₁ :=
      Real.rpow_le_rpow (by linarith) (by linarith) hM₁
    have hle2 : C₁ * S ^ N₁ * (1 + t) ^ M₁ ≤ C₁ * S ^ N₁ * (1 + T) ^ M₁ :=
      mul_le_mul_of_nonneg_left hle1 hCS
    have hexp1 : Real.exp (Real.pi * T) * Real.exp (-(Real.pi * T)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hArel : C₁ * S ^ N₁ * (1 + T) ^ M₁ = A * Real.exp (-(Real.pi * T)) := by
      calc C₁ * S ^ N₁ * (1 + T) ^ M₁
          = C₁ * S ^ N₁ * (1 + T) ^ M₁ * 1 := by ring
        _ = C₁ * S ^ N₁ * (1 + T) ^ M₁
              * (Real.exp (Real.pi * T) * Real.exp (-(Real.pi * T))) := by rw [hexp1]
        _ = A * Real.exp (-(Real.pi * T)) := by rw [hAdef]; ring
    have hexpT_le : Real.exp (-(Real.pi * T)) ≤ Real.exp (-(Real.pi * t)) := by
      apply Real.exp_le_exp.mpr
      have : Real.pi * t ≤ Real.pi * T := mul_le_mul_of_nonneg_left htT Real.pi_pos.le
      linarith
    have hAexp : C₁ * S ^ N₁ * (1 + T) ^ M₁ ≤ A * Real.exp (-(Real.pi * t)) := by
      rw [hArel]
      exact mul_le_mul_of_nonneg_left hexpT_le hApos.le
    have hCexp : A * Real.exp (-(Real.pi * t)) ≤ C * t ^ M * Real.exp (-(Real.pi * t)) := by
      have hAC : A ≤ C * t ^ M := by
        calc A ≤ C := hAleC
          _ = C * 1 := by ring
          _ ≤ C * t ^ M := mul_le_mul_of_nonneg_left htM hCpos.le
      calc A * Real.exp (-(Real.pi * t))
          ≤ (C * t ^ M) * Real.exp (-(Real.pi * t)) :=
            mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le
        _ = C * t ^ M * Real.exp (-(Real.pi * t)) := by ring
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
        ≤ C₁ * S ^ N₁ * (1 + t) ^ M₁ := hpoly
      _ ≤ C₁ * S ^ N₁ * (1 + T) ^ M₁ := hle2
      _ ≤ A * Real.exp (-(Real.pi * t)) := hAexp
      _ ≤ C * t ^ M * Real.exp (-(Real.pi * t)) := hCexp
  · -- Beyond the threshold `t ≥ T`: use the exponential decay directly.
    have hexp := hE τ hτ t hTt
    rw [← hSdef, ← hBdef] at hexp
    have htM₂M : t ^ M₂ ≤ t ^ M := by
      rw [hMdef]
      exact Real.rpow_le_rpow_of_exponent_le ht1 (le_max_right M₁ M₂)
    have hBle2 : B * t ^ M₂ ≤ C * t ^ M := by
      have h0 : 0 ≤ t ^ M₂ := Real.rpow_nonneg (by linarith) M₂
      calc B * t ^ M₂ ≤ C * t ^ M₂ := mul_le_mul_of_nonneg_right hBleC h0
        _ ≤ C * t ^ M := mul_le_mul_of_nonneg_left htM₂M hCpos.le
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
        ≤ B * t ^ M₂ * Real.exp (-(Real.pi * t)) := hexp
      _ ≤ C * t ^ M * Real.exp (-(Real.pi * t)) := by
          calc B * t ^ M₂ * Real.exp (-(Real.pi * t))
              = (B * t ^ M₂) * Real.exp (-(Real.pi * t)) := by ring
            _ ≤ (C * t ^ M) * Real.exp (-(Real.pi * t)) :=
                mul_le_mul_of_nonneg_right hBle2 (Real.exp_pos _).le
            _ = C * t ^ M * Real.exp (-(Real.pi * t)) := by ring

end Work.Asymptotics
