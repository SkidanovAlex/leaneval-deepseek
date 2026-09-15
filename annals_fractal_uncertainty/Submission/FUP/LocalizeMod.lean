import Submission.FUP.LocalizeWindow

open FractalUncertainty MeasureTheory Metric Set Complex Filter FourierTransform
open scoped ENNReal BigOperators Topology FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# P5 preliminaries: the modulation `modFun` and the damping kernel

This module collects the pieces of the modulation sum of Han–Schlag's `cor:UPY` that are
independent of the `R`-arithmetic: the comparison of `modFun m` with `modEta (ellVec m)`,
the analogue of `subLp_modEta` for `modFun`, and the transfer of the damping bounds to the
pointwise Fourier transform of the damping *kernel*.
-/

namespace Submission.FUP

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

lemma modFun_eq_modEta (m : Fin d → ℤ) (f : ℝᵈ → ℂ) :
    modFun m f = modEta (ellVec m) f := rfl

lemma modPhase_eq_phaseEta (m : Fin d → ℤ) (x : ℝᵈ) :
    modPhase m x = phaseEta (ellVec m) x := rfl

/-- `subLp` commutes with the modulation `modFun m`. -/
lemma subLp_modFun (S : Set ℝᵈ) (hS : MeasurableSet S) (h : Lp ℂ 2 (volume : Measure ℝᵈ))
    (m : Fin d → ℤ) :
    subLp S ((memLp_modFun (m := m) (Lp.memLp h)).toLp (modFun m (h : ℝᵈ → ℂ))) hS
      = (memLp_modFun (m := m) ((Lp.memLp h).indicator hS)).toLp
          (modFun m (S.indicator (h : ℝᵈ → ℂ))) := by
  have := subLp_modEta (d := d) S hS h (ellVec m)
  simpa only [modFun_eq_modEta] using this

/-- `subLp S (modFun m f)` is `modFun m (subLp S f)`. -/
lemma subLp_modFun' (S : Set ℝᵈ) (hS : MeasurableSet S) (h : Lp ℂ 2 (volume : Measure ℝᵈ))
    (m : Fin d → ℤ) :
    subLp S ((memLp_modFun (m := m) (Lp.memLp h)).toLp (modFun m (h : ℝᵈ → ℂ))) hS
      = (memLp_modFun (m := m) (Lp.memLp (subLp S h hS))).toLp
          (modFun m ((subLp S h hS : ℝᵈ → ℂ))) := by
  rw [subLp_modFun S hS h m]
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards [subLp_coe S h hS] with x hx
  rw [modFun, modFun, hx]

/-- **The damping kernel.**  If `ψ ∈ L²` has Fourier support in the cube of radius `r`, then
`φ := 𝓕⁻ψ ∈ L¹ ∩ L²` is supported in the same cube and `𝓕φ = ψ` (as `L²` classes). -/
theorem exists_kernel_of_damping {ψ : Lp ℂ 2 (volume : Measure ℝᵈ)} {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      (∃ i : Fin d, r < |ξ i|) → ((𝓕 ψ : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0) :
    ∃ φ : Lp ℂ 2 (volume : Measure ℝᵈ), (𝓕 φ = ψ) ∧
      (∀ᵐ x ∂(volume : Measure ℝᵈ), (∃ i : Fin d, r < |x i|) → (φ : ℝᵈ → ℂ) x = 0) ∧
      MemLp (φ : ℝᵈ → ℂ) 1 (volume : Measure ℝᵈ) := by
  obtain ⟨φ, h1, h2, h3, -⟩ :=
    Commons.Analysis.Fourier.exists_compactlySupported_kernel_of_bandlimited d ψ r hr hsupp
  exact ⟨φ, h1, h2, h3⟩

/-- `𝓕 (φ : ℝᵈ → ℂ) =ᵐ ψ` for the kernel `φ` of `exists_kernel_of_damping`. -/
theorem fourier_kernel_ae {φ : Lp ℂ 2 (volume : Measure ℝᵈ)} {ψ : Lp ℂ 2 (volume : Measure ℝᵈ)}
    (hφ1 : MemLp (φ : ℝᵈ → ℂ) 1 (volume : Measure ℝᵈ)) (h : 𝓕 φ = ψ) :
    (fun ξ : ℝᵈ => 𝓕 (φ : ℝᵈ → ℂ) ξ) =ᵐ[volume]
      ((ψ : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) := by
  have h1 := Commons.Analysis.Fourier.fourier_toLp_ae_eq_fourier_of_memLp (V := ℝᵈ) hφ1
    (Lp.memLp φ)
  have h2 : ((𝓕 ((Lp.memLp φ).toLp (φ : ℝᵈ → ℂ)) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ)
      = ((𝓕 φ : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) := by
    rw [Lp.toLp_coeFn φ (Lp.memLp φ)]
  rw [h2, h] at h1
  exact h1.symm

/-- **The modulation sum for `1_S f`.**  The lattice bound `C₀` is as in
`sum_hsq_mod_le`/`Commons.Analysis.Fourier.finset_bracket_lattice_le`. -/
theorem sum_hsq_subLp_modFun_le (C₀ : ℝ)
    (hC₀ : ∀ (η : ℝᵈ) (s : Finset (Fin d → ℤ)),
      (∑ m ∈ s, (1 + ‖η + ellVec m‖ ^ 2) ^ (-(d : ℝ))) ≤ C₀)
    (f : Lp ℂ 2 (volume : Measure ℝᵈ)) (S : Set ℝᵈ) (hS : MeasurableSet S)
    (s : Finset (Fin d → ℤ)) :
    (∑ m ∈ s, hsq (subLp S
        ((memLp_modFun (m := m) (Lp.memLp f)).toLp (modFun m (f : ℝᵈ → ℂ))) hS))
      ≤ C₀ * ‖subLp S f hS‖ ^ 2 := by
  have h := sum_hsq_mod_le (d := d) C₀ hC₀ (subLp S f hS : ℝᵈ → ℂ)
    (Lp.memLp (subLp S f hS)) s
  rw [Lp.toLp_coeFn (subLp S f hS) (Lp.memLp (subLp S f hS))] at h
  refine (le_of_eq ?_).trans h
  exact Finset.sum_congr rfl (fun m _ => congrArg hsq (subLp_modFun' S hS f m))


/-! ## The damping witness gives the P4 hypotheses -/

/-- **The hinge lemma.**  From a damping witness `ψ` (as produced by `AdmitsL1Damping`) whose
multiplier decays on a set `Z` containing `ℓ + η + Y` for every `η ∈ [-2,2]^d`, the modulation
`f_m = modFun m f` (with Fourier support in `Y + ℓ`) satisfies the single-window estimate of
`window_bound`, with `𝓕 φ` replaced by `ψ`. -/
theorem window_bound_of_damping {q ε δ H ηL r c₁ c₃ α R : ℝ} (hd : 1 ≤ d)
    (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3)
    (hH0 : 0 < H) (hH1 : H ≤ 1) (hηL0 : 0 < ηL) (hc₁ : 0 < c₁) (hr0 : 0 < r)
    (hητ : 1 ≤ ηL * phiLens q ε (1 - 3 * δ))
    (hIbig : ENNReal.ofReal ((ηL * zpLamMax q ε) ^ d * (2 * (20 ^ d * H)))
      ≤ ENNReal.ofReal ((c₁ / 2) ^ d))
    (hc₃ : 0 < c₃) (hα0 : 0 < α) (hα1 : α ≤ 1) (hR0 : 0 < R) (hR1 : 1 ≤ R)
    (hRc : (2 * (d : ℝ) / c₃) ^ 2 ≤ R)
    (hQ4 : 4 * Real.pi * windowQ ηL q r ≤ c₃ * (Real.log (2 + R)) ^ (-α))
    {ψ : Lp ℂ 2 (volume : Measure ℝᵈ)}
    (hψsupp : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      (∃ i : Fin d, c₁ / 2 < |ξ i|) → ((𝓕 ψ : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0)
    (hψw : ∀ᵐ x ∂(volume : Measure ℝᵈ),
      ‖(ψ : ℝᵈ → ℂ) x‖ ≤ (1 + ‖x‖ ^ 2) ^ (-(d : ℝ) / 2))
    {Z : Set ℝᵈ}
    (hψdec : ∀ᵐ x ∂(volume : Measure ℝᵈ), x ∈ Z →
      ‖(ψ : ℝᵈ → ℂ) x‖ ≤ Real.exp (-(c₃ * l1norm x / (Real.log (2 + l1norm x)) ^ α)))
    {f : Lp ℂ 2 (volume : Measure ℝᵈ)} {Y : Set ℝᵈ} {m : Fin d → ℤ} {ηm : ℝᵈ}
    (hηm : ∀ i : Fin d, |ηm i| ≤ 2)
    (hfY : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y)
    (hZY : ∀ y ∈ Y, ellVec m + ηm + y ∈ Z)
    {γ : ℝᵈ} {a : (Fin d → ℤ) → Fin d → ℝ}
    (ha : ∀ n : Fin d → ℤ, ∀ i : Fin d,
      2 * (n i : ℝ) + γ i ≤ a n i ∧ a n i + 2 * c₁ ≤ 2 * (n i : ℝ) + γ i + 2) :
    ∫ ξ, ‖winP ((memLp_modFun (m := m) (Lp.memLp f)).toLp (modFun m (f : ℝᵈ → ℂ))) ηm ξ
          * (ψ : ℝᵈ → ℂ) ξ‖ ^ 2
      ≤ cellZConst q ε δ H ηL (c₁ / 4) d
        * (windowD d q ε ηL r * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d
            * (windowCW d * hsq ((memLp_modFun (m := m) (Lp.memLp f)).toLp
                (modFun m (f : ℝᵈ → ℂ))))))) ^ (1 - zpKappa δ H d)
        * (2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a)
              ((memLp_modFun (m := m) (Lp.memLp f)).toLp (modFun m (f : ℝᵈ → ℂ)))
              (measurableSet_locCubes c₁ a))
            + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 *
                hsq ((memLp_modFun (m := m) (Lp.memLp f)).toLp (modFun m (f : ℝᵈ → ℂ))))
            ^ (zpKappa δ H d)
        + (truncBeta d c₃ α R) ^ 2 * windowCW d *
            hsq ((memLp_modFun (m := m) (Lp.memLp f)).toLp (modFun m (f : ℝᵈ → ℂ))) := by
  classical
  set fM : Lp ℂ 2 (volume : Measure ℝᵈ) :=
    (memLp_modFun (m := m) (Lp.memLp f)).toLp (modFun m (f : ℝᵈ → ℂ)) with hfM
  obtain ⟨φ, hφft, hφsupp, hφ1⟩ := exists_kernel_of_damping (d := d)
    (by linarith : 0 < c₁ / 2) hψsupp
  have hφ2 : MemLp (φ : ℝᵈ → ℂ) 2 (volume : Measure ℝᵈ) := Lp.memLp φ
  have hfae := fourier_kernel_ae (d := d) (φ := φ) (ψ := ψ) hφ1 hφft
  have hφw : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ‖winW (φ : ℝᵈ → ℂ) ξ‖ ≤ (1 + ‖ξ‖ ^ 2) ^ (-(d : ℝ) / 2) := by
    filter_upwards [hfae, hψw] with ξ e1 e2
    rw [show winW (φ : ℝᵈ → ℂ) ξ = 𝓕 (φ : ℝᵈ → ℂ) ξ from rfl, e1]
    exact e2
  have hφdec : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), ξ ∈ Z →
      ‖winW (φ : ℝᵈ → ℂ) ξ‖ ≤ Real.exp (-(c₃ * l1norm ξ / (Real.log (2 + l1norm ξ)) ^ α)) := by
    filter_upwards [hfae, hψdec] with ξ e1 e2 hZ
    rw [show winW (φ : ℝᵈ → ℂ) ξ = 𝓕 (φ : ℝᵈ → ℂ) ξ from rfl, e1]
    exact e2 hZ
  have hae1 : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 fM : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) (ξ - ηm)
        = ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ((ξ - ηm) - ellVec m) := by
    have h := (measurePreserving_add_right (volume : Measure ℝᵈ) (-ηm)
      ).quasiMeasurePreserving.ae (fourier_modFun (m := m) (Lp.memLp f))
    simpa only [hfM, sub_eq_add_neg, add_assoc, Lp.toLp_coeFn f (Lp.memLp f)] using h
  have hY1 : ∀ᵐ ζ ∂(volume : Measure ℝᵈ),
      ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) (ζ - ellVec m) ≠ 0 →
        (ζ - ellVec m) ∈ Y :=
    (measurePreserving_add_right (volume : Measure ℝᵈ) (-ellVec m)
      ).quasiMeasurePreserving.ae hfY
  have hY' : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ((ξ - ηm) - ellVec m) ≠ 0 →
        ((ξ - ηm) - ellVec m) ∈ Y :=
    (measurePreserving_add_right (volume : Measure ℝᵈ) (-ηm)
      ).quasiMeasurePreserving.ae hY1
  have hdec : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), winP fM ηm ξ ≠ 0 →
      ‖winW (φ : ℝᵈ → ℂ) ξ‖ ≤ Real.exp (-(c₃ * l1norm ξ / (Real.log (2 + l1norm ξ)) ^ α)) := by
    filter_upwards [hae1, hY', hφdec] with ξ e1 e2 e3 hne
    rw [show winP fM ηm ξ = ((𝓕 fM : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) (ξ - ηm)
        from rfl, e1] at hne
    refine e3 ?_
    have hmem : ellVec m + ηm + ((ξ - ηm) - ellVec m) ∈ Z := hZY _ (e2 hne)
    have heq : ellVec m + ηm + ((ξ - ηm) - ellVec m) = ξ := by abel
    rwa [heq] at hmem
  have hmain := window_bound (d := d) (q := q) (ε := ε) (δ := δ) (H := H) (ηL := ηL) (r := r)
    (c₁ := c₁) (c₃ := c₃) (α := α) (R := R) hd hq hε0 hε1 hδ0 hδ3 hH0 hH1 hηL0 hc₁ hr0
    hητ hIbig hc₃ hα0 hα1 hR0 hR1 hRc hQ4 hφ1 hφ2 hφsupp hφw (f := fM) (ηm := ηm) hηm hdec ha
  have hpt : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ‖winP fM ηm ξ * (ψ : ℝᵈ → ℂ) ξ‖ ^ 2
        = ‖winP fM ηm ξ * winW (φ : ℝᵈ → ℂ) ξ‖ ^ 2 := by
    filter_upwards [hfae] with ξ e1
    rw [show winW (φ : ℝᵈ → ℂ) ξ = 𝓕 (φ : ℝᵈ → ℂ) ξ from rfl, e1]
  rw [show (∫ ξ, ‖winP fM ηm ξ * (ψ : ℝᵈ → ℂ) ξ‖ ^ 2)
      = ∫ ξ, ‖winP fM ηm ξ * winW (φ : ℝᵈ → ℂ) ξ‖ ^ 2 from
    integral_congr_ae hpt]
  exact hmain

end Submission.FUP
