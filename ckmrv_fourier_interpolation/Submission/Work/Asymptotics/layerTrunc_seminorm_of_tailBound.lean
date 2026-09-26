import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.TailIntegral
import Submission.Work.Asymptotics.abs_pow_mul_exp_le
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.layerTrunc_seminorm
import Submission.Work.Asymptotics.ae_bound_of_two_regime
import Submission.Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound
import Submission.Work.Asymptotics.exists_bound_iteratedDeriv_tailIntegral_two_regime

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ContDiff

namespace Work.Asymptotics

open Work.Kernels

/-- **The `r`-seminorms of the `trunc` piece from the two-regime `TailBound` hypothesis.**

`Work.Asymptotics.layerTrunc G ℓ d τ r = sinSq r · ∫_{t ≥ 1} (Kaxis (Kfun ℓ d) τ t - Aexp G τ t)
· e^{-π r² t} dt`, i.e. the contribution of `[1,∞)` of the contour integral (5.2), and `TailBound`
records the two regimes of the amplitude `h_τ(t) = Kaxis (Kfun ℓ d) τ t - Aexp G τ t`:

* `‖h_τ t‖ ≤ C (scale τ)^N (1+t)^M` for all `t ≥ 1` (no exponential decay inside the window);
* `‖h_τ t‖ ≤ C (scale τ)^N t^M e^{-πt}` for `t ≥ (scale τ)^{N₀}`.

**Strategy.**  With `A = scale τ ≥ 1` and threshold `B = A^{N₀} ≥ 1` one splits

  `∫_{t ≥ 1} h_τ(t) e^{-λt} dt = ∫_{1}^{A^{N₀}} h_τ(t) e^{-λt} dt + ∫_{t ≥ A^{N₀}} h_τ(t) e^{-λt} dt`.

The window piece is controlled by the polynomial bound (costing the factor `A^{N₀(M₁+l+1)}`), and
the tail piece by the exponential bound (costing the constant `tailDecay`); both carry the factor
`e^{-πλ}` with `λ = r²`, which is what absorbs `|r|^k` after the chain rule.  This is
`Work.Asymptotics.exists_bound_iteratedDeriv_tailIntegral_two_regime`; the global (crude) `e^{-πt}`
bound needed for the differentiation-under-the-integral formula comes from
`Work.Asymptotics.ae_bound_of_two_regime`.  Finally `layerTrunc = (2 - 2cos(πr²))·Ψ(r²)` by
`Work.Asymptotics.layerTrunc_eq_tailIntegral` and the composition is bounded by
`Work.Asymptotics.exists_seminorm_bound_of_iteratedDeriv_bound`. -/
theorem layerTrunc_seminorm_of_tailBound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hT : Work.Asymptotics.TailBound ℓ d G) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      τ ∈ Work.Asymptotics.DomainD →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r‖
        ≤ c * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨⟨C₁, N₁, M₁, hC₁, hN₁, hM₁, hb₁⟩, ⟨N₀, C₂, N₂, M₂, hN₀, hC₂, hN₂, hM₂, hb₂⟩⟩ := hT
  intro k l
  obtain ⟨c4, hc4, h4⟩ := exists_seminorm_bound_of_iteratedDeriv_bound k l
  obtain ⟨c6, N6, hc6, hN6, h6⟩ :=
    exists_bound_iteratedDeriv_tailIntegral_two_regime l N₀ C₁ N₁ M₁ C₂ N₂ M₂
      hC₁.le hN₁ hM₁ hC₂.le hN₂ hM₂ hN₀
  refine ⟨c4 * c6, N6, mul_nonneg hc4 hc6, ?_⟩
  intro τ r hτ
  have hA1 : 1 ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  set h : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp G τ t
    with hhdef
  -- measurability of the amplitude
  have hAexp : Measurable (fun t : ℝ => Aexp G τ t) := by
    unfold Aexp
    fun_prop
  have hhmeas : AEStronglyMeasurable h (volume.restrict (Set.Ici (1 : ℝ))) := by
    rw [hhdef]
    exact ((measurable_Kaxis_Kfun ℓ d hd τ).sub hAexp).aestronglyMeasurable
  -- the two regimes
  have hw : ∀ t : ℝ, 1 ≤ t → t ≤ (Work.Kernels.scale τ) ^ N₀ →
      ‖h t‖ ≤ C₁ * (Work.Kernels.scale τ) ^ N₁ * (1 + t) ^ M₁ := by
    intro t ht1 htB
    simpa only [hhdef] using hb₁ τ hτ t ht1
  have ht : ∀ t : ℝ, (Work.Kernels.scale τ) ^ N₀ ≤ t →
      ‖h t‖ ≤ C₂ * (Work.Kernels.scale τ) ^ N₂ * t ^ M₂ * Real.exp (-(Real.pi * t)) := by
    intro t htB
    simpa only [hhdef] using hb₂ τ hτ t htB
  -- the crude global exponential bound, used for integrability and the derivative formula
  obtain ⟨Cg, Mg, hCg, hMg, hglob⟩ :=
    ae_bound_of_two_regime h (Real.one_le_rpow hA1 hN₀)
      (mul_nonneg hC₁.le (Real.rpow_nonneg (le_trans zero_le_one hA1) N₁))
      (mul_nonneg hC₂.le (Real.rpow_nonneg (le_trans zero_le_one hA1) N₂)) hM₁ hM₂
      (fun t ht1 htB => by simpa only [mul_assoc] using hw t ht1 htB) ht
  have hglob_ae : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
      ‖h t‖ ≤ Cg * t ^ Mg * Real.exp (-(Real.pi * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht1
    exact hglob t (Set.mem_Ici.mp ht1)
  -- smoothness of the tail integral in `λ` and the two-regime derivative bound
  have hcont : ContDiffOn ℝ (l : ℕ∞ω) (tailIntegral h) (Set.Ioi (-1)) :=
    tailIntegral_contDiffOn l h hhmeas hCg hMg hglob_ae
  have hderiv : ∀ m : ℕ, m ≤ l → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (tailIntegral h) x‖
        ≤ (c6 * (Work.Kernels.scale τ) ^ N6) * Real.exp (-(Real.pi * x)) :=
    fun m hm x hx =>
      h6 h (Work.Kernels.scale τ) Cg Mg hA1 hCg hMg hhmeas hglob_ae hw ht m hm x hx
  have hmain := h4 (tailIntegral h) (c6 * (Work.Kernels.scale τ) ^ N6) (by positivity)
    hcont hderiv r
  have hfun : (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s)
      = fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * tailIntegral h (s ^ 2) := by
    funext s
    simp only [layerTrunc_eq_tailIntegral, ← hhdef]
  rw [hfun]
  calc (|r| ^ k) * ‖iteratedDeriv l
        (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ) * tailIntegral h (s ^ 2)) r‖
      ≤ c4 * (c6 * (Work.Kernels.scale τ) ^ N6) := hmain
    _ = (c4 * c6) * (Work.Kernels.scale τ) ^ N6 := by ring

end Work.Asymptotics
