import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.Asymptotics.layerLow_local_seminorm
import Submission.Work.Asymptotics.layerTrunc_local_seminorm
import Submission.Work.Asymptotics.highPart_seminorm_scaled
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.paperLayer_smooth

namespace Work.Asymptotics

open MeasureTheory Filter Topology UpperHalfPlane
open scoped Topology ContDiff

/-! ## `scale` is bounded on compact subsets of `ℍ` -/

/-- The scale `S τ = 1 + (im τ)⁻¹ + ‖τ‖` is continuous on the upper half plane. -/
lemma continuous_scale_localK : Continuous (fun τ : UpperHalfPlane => Work.Kernels.scale τ) := by
  rw [continuous_iff_continuousAt]
  intro τ
  have him : ContinuousAt (fun τ : UpperHalfPlane => τ.im) τ :=
    UpperHalfPlane.continuous_im.continuousAt
  have hinv : ContinuousAt (fun τ : UpperHalfPlane => (τ.im)⁻¹) τ :=
    ContinuousAt.inv₀ him (ne_of_gt τ.im_pos)
  unfold Work.Kernels.scale
  exact ContinuousAt.add (ContinuousAt.add continuousAt_const hinv)
    (continuous_norm.continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt)

/-- On a compact subset of `ℍ` the scale is bounded (by a constant `≥ 1`). -/
lemma exists_scale_bound_of_isCompact_localK {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ τ ∈ K, Work.Kernels.scale τ ≤ B := by
  obtain ⟨B, hB⟩ := (hK.image continuous_scale_localK).bddAbove
  exact ⟨max B 1, le_max_right _ _,
    fun τ hτ => le_trans (hB ⟨τ, hτ, rfl⟩) (le_max_left _ _)⟩

/-! ## The explicit `high` piece on a compact set -/

/-- **The `r`-seminorms of `highPart` on a compact `K ⊆ 𝒟`.**

This is `Work.Asymptotics.highPart_seminorm_scaled` with the `τ`-dependent factor
`(scale τ) ^ N` replaced by a constant, using that `scale` is bounded on `K` (and `≥ 1`). -/
lemma highPart_local_seminorm (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j))
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD) :
    ∀ k l : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r‖ ≤ c := by
  obtain ⟨B, hB1, hB⟩ := exists_scale_bound_of_isCompact_localK hK
  intro k l
  obtain ⟨c, N, hc, h⟩ := highPart_seminorm_scaled G hG k l
  refine ⟨c * max (B ^ N) 1, mul_nonneg hc (le_trans zero_le_one (le_max_right _ _)), ?_⟩
  intro τ r hτ
  have hsB : Work.Kernels.scale τ ≤ B := hB τ hτ
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hbound : (Work.Kernels.scale τ) ^ N ≤ max (B ^ N) 1 := by
    rcases le_or_gt 0 N with hN | hN
    · exact le_trans (Real.rpow_le_rpow (le_trans zero_le_one hs1) hsB hN) (le_max_left _ _)
    · have h2 : (Work.Kernels.scale τ) ^ N ≤ (1 : ℝ) ^ N :=
        Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1) hs1 (le_of_lt hN)
      rw [Real.one_rpow] at h2
      exact h2.trans (le_max_right _ _)
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r‖
      ≤ c * (Work.Kernels.scale τ) ^ N := h τ r (hsub hτ)
    _ ≤ c * max (B ^ N) 1 := mul_le_mul_of_nonneg_left hbound hc

/-! ## Smoothness of the three pieces for `τ ∈ K` -/

/-- For `τ ∈ K` the three pieces of the layer are smooth (indeed analytic) functions of `r`:
the two parametric integrals are differentiated under the integral sign (the flatness bound
`hflatK` with exponent `N = 0` dominates the integrand on `(0,1]`, the decay bound `hpolyK`
dominates it on `[1,∞)`), and `highPart` is an explicit expression in `psi1`, `exp` and the
constants `G i j τ`. -/
lemma layerPieces_contDiff_of_mem (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) {K : Set UpperHalfPlane}
    (hflatK : ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N)
    (hpolyK : ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) :
    ∀ τ : UpperHalfPlane, τ ∈ K →
      ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) ∧
      ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) ∧
      ContDiff ℝ ⊤ (fun s : ℝ => Work.Asymptotics.highPart G τ s) := by
  intro τ hτ
  obtain ⟨c, hc, hflat⟩ := hflatK 0 le_rfl
  obtain ⟨C, M, T₀, hC, hM, hT₀, hpoly⟩ := hpolyK
  have hmeasK : AEStronglyMeasurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable
  refine ⟨?_, ?_, contDiff_omega_highPart G τ⟩
  · -- the `low` piece
    have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      have := hflat τ t hτ ht.1 ht.2
      rwa [Real.rpow_zero, mul_one] at this
    have h := contDiff_omega_intervalIntegral_exp
      (κ := fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
      (B := c) hc.le hmeasK hbound
    simpa only [Work.Asymptotics.layerLow] using contDiff_omega_sinSq.mul h
  · -- the `trunc` piece
    have hmeasA : AEStronglyMeasurable (fun t : ℝ => Work.Asymptotics.Aexp G τ t)
        (volume.restrict (Set.Ici (1 : ℝ))) := by
      unfold Work.Asymptotics.Aexp; fun_prop
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp G τ t) (volume.restrict (Set.Ici (1 : ℝ))) :=
      ((measurable_Kaxis_Kfun ℓ d hd τ).aestronglyMeasurable).sub hmeasA
    have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ici (1 : ℝ))),
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
          ≤ (C * Real.exp (Real.pi * T₀) * 2 ^ M) * t ^ M
              * Real.exp (-(Real.pi * t)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ici] with t ht
      have ht1 : (1 : ℝ) ≤ t := ht
      have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
      have h1 := hpoly τ t hτ ht1
      have h2 : (1 + t) ^ M ≤ 2 ^ M * t ^ M := by
        calc (1 + t) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
          _ = 2 ^ M * t ^ M := Real.mul_rpow (by norm_num) ht0.le
      have h3 : Real.exp (-(Real.pi * (t - T₀)))
          = Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t)) := by
        rw [show -(Real.pi * (t - T₀)) = Real.pi * T₀ + -(Real.pi * t) by ring, Real.exp_add]
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := h1
        _ ≤ C * (2 ^ M * t ^ M)
              * (Real.exp (Real.pi * T₀) * Real.exp (-(Real.pi * t))) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h2 hC.le) (le_of_eq h3)
              (Real.exp_pos _).le (by positivity)
        _ = (C * Real.exp (Real.pi * T₀) * 2 ^ M) * t ^ M
              * Real.exp (-(Real.pi * t)) := by ring
    have h := contDiff_omega_integral_Ici_exp
      (ψ := fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp G τ t)
      (C := C * Real.exp (Real.pi * T₀) * 2 ^ M) (M := M) (by positivity) hM hmeas hbound
    simpa only [Work.Asymptotics.layerTrunc] using contDiff_omega_sinSq.mul h

/-! ## The target -/

/-- **The seminorm bound for the layer on a compact subset of `𝒟`** (the "interior" half of
CKMRV Proposition 4.6; the cusps need the contour shift of §5.2).

On a compact `K ⊆ 𝒟` the poles of `z ↦ K(τ,z)` stay a positive distance from the contour (the
genuine poles `τ = γz` with `φ(γ) ≠ 0` lie on or outside `∂𝒟`, the interior coincidences have
vanishing residue), so the contour integrand is uniformly bounded on `K × (0,1]` and the tail
`K - Aexp` is polynomially bounded on `[1,∞)` *and* exponentially small beyond the constant
threshold `T₀` (the cusp expansion of `z ↦ K(τ,z)` is valid for `Im z > max{Im w : w ∈ SL(2,ℤ)τ}`,
which is bounded on `K`).  With those three inputs the `low`, `trunc` and `high` pieces of
`paperLayer` are handled exactly as in the global statement, and since `scale τ` and `‖τ‖` are
bounded on `K` all the resulting bounds are absorbed into a single constant. -/
theorem paperLayer_local_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j))
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD)
    (hflatK : ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 0 < t → t ≤ 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c * t ^ N)
    (hpolyK : ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) :
    ∀ k l : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ), τ ∈ K →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer G ℓ d τ s) r‖
        ≤ c := by
  intro k l
  obtain ⟨c1, hc1, h1⟩ := layerLow_local_seminorm ℓ d hd hflatK k l
  obtain ⟨c2, hc2, h2⟩ := layerTrunc_local_seminorm ℓ d hd G hpolyK k l
  obtain ⟨c3, hc3, h3⟩ := highPart_local_seminorm G hG hK hsub k l
  refine ⟨c1 + c2 + c3, by positivity, fun τ r hτ => ?_⟩
  -- deconstruct the layer into its three pieces and differentiate the sum
  obtain ⟨hcdL, hcdT, hcdH⟩ := layerPieces_contDiff_of_mem ℓ d hd G hflatK hpolyK τ hτ
  have hsplitL : iteratedDeriv l
        (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
          + Work.Asymptotics.layerTrunc G ℓ d τ s) r
      = iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r :=
    iteratedDeriv_add (f := fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s)
      (g := fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s)
      ((hcdL.contDiffAt).of_le le_top) ((hcdT.contDiffAt).of_le le_top)
  have hsplit : iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer G ℓ d τ s) r
      = iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r := by
    have hfun : (fun s : ℝ => Work.Asymptotics.paperLayer G ℓ d τ s)
        = fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
            + Work.Asymptotics.layerTrunc G ℓ d τ s + Work.Asymptotics.highPart G τ s := by
      funext s; rw [Work.Asymptotics.paperLayer]
    have hE : (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
          + Work.Asymptotics.layerTrunc G ℓ d τ s + Work.Asymptotics.highPart G τ s)
        = (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
            + Work.Asymptotics.layerTrunc G ℓ d τ s)
          + (fun s : ℝ => Work.Asymptotics.highPart G τ s) := rfl
    rw [hfun, hE, iteratedDeriv_add
      (f := fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s
        + Work.Asymptotics.layerTrunc G ℓ d τ s)
      (g := fun s : ℝ => Work.Asymptotics.highPart G τ s)
      (((hcdL.add hcdT).contDiffAt).of_le le_top) ((hcdH.contDiffAt).of_le le_top), hsplitL]
  rw [hsplit]
  -- the triangle inequality and the three seminorm bounds
  have ha : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
      ≤ c1 := h1 τ r hτ
  have hb : (|r| ^ k)
      * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r‖ ≤ c2 := h2 τ r hτ
  have hc : (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r‖
      ≤ c3 := h3 τ r hτ
  have htri : ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r‖
      ≤ ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r‖ := by
    linarith [norm_add_le (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r)
        (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r),
      norm_add_le (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r)
        (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r)]
  calc (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r‖
      ≤ (|r| ^ k) * (‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r‖
        + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r‖) :=
        mul_le_mul_of_nonneg_left htri (by positivity)
    _ = (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d τ s) r‖
        + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerTrunc G ℓ d τ s) r‖
        + (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r‖ := by
          ring
    _ ≤ c1 + c2 + c3 := by linarith

end Work.Asymptotics
