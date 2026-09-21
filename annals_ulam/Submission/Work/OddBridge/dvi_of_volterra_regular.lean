import Mathlib
import Submission.Work.OddBridge.dvi_reduce

/-!
# `(dvi)` from the Volterra system, with the analytic inputs made explicit

`Work.OddBridge.dvi_of_volterra` claims that the Volterra system `VolterraEqOn` (the
componentwise formalisation of Ryabogin's `(hah44)`) implies the vector-valued `(dvi)`.

The passage needs an analytic input that the hypotheses `hvol`, `hae` do *not* provide: the
`i`-th component of the *vector-valued* derivative
`∂₁ (u ↦ ∫₀¹ (√(τ(1-τ)))⁻¹ • KvecM n h (u+τ(σ-u)) σ …)`  must be the *scalar* derivative
`∂₁ (u ↦ ∫₀¹ (√(τ(1-τ)))⁻¹ (Kvec …ᵢ) )` of the corresponding component, i.e. the kernel must be
differentiable in its first slot (`deriv_pi`).  In the paper this comes from the `C^∞`-smoothness
of the kernel `K₁`, `K₂`; in the workspace it is supplied by `G2_deriv_eq_integral`
(`Submission/Work/OddVolterra/Kernel/G2Deriv.lean`), which needs `ContDiff ℝ ⊤ h` and bounds.

This file records the *provable* version: the same conclusion, with the three regularity inputs
(differentiability of the inner vector function in `u` at `s`, interval integrability of its
`σ`-derivative, and interval integrability of the `Theta`-integrand, plus the inner `τ`-integrability
needed by the `KvecM → Kvec` bridge) taken as hypotheses.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

open Work.OddVolterra

noncomputable section

/-- A `Fin 4`-valued interval integral may be read off componentwise. -/
lemma intervalIntegral_apply_fin4 {g : ℝ → Fin 4 → ℝ} {a b : ℝ} (i : Fin 4)
    (h : IntervalIntegrable g volume a b) :
    (∫ s in a..b, g s) i = ∫ s in a..b, g s i := by
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
    (L := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) h
  rw [ContinuousLinearMap.proj_apply] at hcomm
  exact hcomm.symm

/-- A `Fin 2`-valued interval integral may be read off componentwise. -/
lemma intervalIntegral_apply_fin2 {g : ℝ → Fin 2 → ℝ} {a b : ℝ} (i : Fin 2)
    (h : IntervalIntegrable g volume a b) :
    (∫ s in a..b, g s) i = ∫ s in a..b, g s i := by
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
    (L := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i) h
  rw [ContinuousLinearMap.proj_apply] at hcomm
  exact hcomm.symm

/-- **The `(t₁)` row of the Volterra system**: the second component of the system, in scalar form. -/
lemma volterra_row_zero (n : ℕ) {h x y : ℝ → ℝ} {s : ℝ}
    (hvol : VolterraEqOn n h x y (Set.Ioo 0 1)) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hintTheta : IntervalIntegrable
      (fun σ : ℝ => Theta n h s σ (stateOf x y σ)) volume s 1) :
    - (G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) 0
      = - (∫ σ in s..1,
            deriv (fun u : ℝ => (G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0) s)
        + (Qtilde n h s) 0 := by
  have hv := hvol s hs
  have h2 : (Godd n h s (stateOf x y s)) 2
      = ((∫ σ in s..1, Theta n h s σ (stateOf x y σ)) + Xi n h s) 2 := by rw [hv]
  rw [Pi.add_apply] at h2
  have hG : (Godd n h s (stateOf x y s)) 2
      = - (G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) 0 := by
    simp [Godd, stateOf]
  have hX : (Xi n h s) 2 = (Qtilde n h s) 0 := by simp [Xi]
  have hT : (∫ σ in s..1, Theta n h s σ (stateOf x y σ)) 2
      = ∫ σ in s..1, - deriv (fun u : ℝ =>
          (G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0) s := by
    rw [intervalIntegral_apply_fin4 (i := 2) (h := hintTheta)]
    refine intervalIntegral.integral_congr (fun σ _ => ?_)
    simp [Theta, stateOf]
  rw [hG, hX, hT, intervalIntegral.integral_neg] at h2
  linarith [h2]

/-- **The `(t₂)` row of the Volterra system**: the third component of the system, in scalar form. -/
lemma volterra_row_one (n : ℕ) {h x y : ℝ → ℝ} {s : ℝ}
    (hvol : VolterraEqOn n h x y (Set.Ioo 0 1)) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hintTheta : IntervalIntegrable
      (fun σ : ℝ => Theta n h s σ (stateOf x y σ)) volume s 1) :
    - (G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) 1
      = - (∫ σ in s..1,
            deriv (fun u : ℝ => (G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1) s)
        + (Qtilde n h s) 1 := by
  have hv := hvol s hs
  have h2 : (Godd n h s (stateOf x y s)) 3
      = ((∫ σ in s..1, Theta n h s σ (stateOf x y σ)) + Xi n h s) 3 := by rw [hv]
  rw [Pi.add_apply] at h2
  have hG : (Godd n h s (stateOf x y s)) 3
      = - (G2 n h s s (x s) (y s) (deriv x s) (deriv y s)) 1 := by
    simp [Godd, stateOf]
  have hX : (Xi n h s) 3 = (Qtilde n h s) 1 := by simp [Xi]
  have hT : (∫ σ in s..1, Theta n h s σ (stateOf x y σ)) 3
      = ∫ σ in s..1, - deriv (fun u : ℝ =>
          (G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1) s := by
    rw [intervalIntegral_apply_fin4 (i := 3) (h := hintTheta)]
    refine intervalIntegral.integral_congr (fun σ _ => ?_)
    simp [Theta, stateOf]
  rw [hG, hX, hT, intervalIntegral.integral_neg] at h2
  linarith [h2]

/-- **`(dvi)` from the Volterra system, with the analytic inputs as hypotheses.** -/
theorem dvi_of_volterra_of_regularity (n : ℕ) {h x y : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hvol : VolterraEqOn n h x y (Set.Ioo 0 1))
    (hae : ∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
      KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ))
    (hintInner : ∀ σ : ℝ, ∀ u ∈ Set.Ioo a σ,
      IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
        KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ))
        volume (0 : ℝ) 1)
    (hdiff : ∀ s ∈ Set.Ioo a 1, ∀ σ ∈ Set.Ioo s 1,
      DifferentiableAt ℝ
        (fun u : ℝ => G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s)
    (hintOut : ∀ s ∈ Set.Ioo a 1,
      IntervalIntegrable (fun σ : ℝ =>
        deriv (fun u : ℝ => G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s) volume s 1)
    (hintTheta : ∀ s ∈ Set.Ioo a 1,
      IntervalIntegrable (fun σ : ℝ => Theta n h s σ (stateOf x y σ)) volume s 1) :
    ∀ s ∈ Set.Ioo a 1,
      - (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
          KvecM n h s s (x s) (y s) (deriv x s) (deriv y s))
        + (∫ σ in s..1, deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
            (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
            KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s)
      = Qtilde n h s := by
  intro s hs
  have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans ha hs.1, hs.2⟩
  rw [dvi_second_term_eq_G2 n ha hae hintInner s hs, dvi_first_term_eq n ha hae s hs]
  have key0 : (- (G2 n h s s (x s) (y s) (deriv x s) (deriv y s))
        + (∫ σ in s..1,
            deriv (fun u : ℝ => G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s)) 0
      = (Qtilde n h s) 0 := by
    have hrow := volterra_row_zero n hvol hs01 (hintTheta s hs)
    have hInt : (∫ σ in s..1,
          deriv (fun u : ℝ => G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s) 0
        = ∫ σ in s..1,
            deriv (fun u : ℝ =>
              (G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0) s := by
      rw [intervalIntegral_apply_fin2 (i := 0) (h := hintOut s hs)]
      refine intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2) (fun σ hσ => ?_)
      have hdp := deriv_pi (𝕜 := ℝ) (x := s) (ι := Fin 2) (E' := fun _ : Fin 2 => ℝ)
        (φ := fun u : ℝ => G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ))
        (fun j : Fin 2 => (differentiableAt_pi.mp (hdiff s hs σ hσ)) j)
      exact congrFun hdp 0
    rw [Pi.add_apply, Pi.neg_apply, hInt]
    linarith [hrow]
  have key1 : (- (G2 n h s s (x s) (y s) (deriv x s) (deriv y s))
        + (∫ σ in s..1,
            deriv (fun u : ℝ => G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s)) 1
      = (Qtilde n h s) 1 := by
    have hrow := volterra_row_one n hvol hs01 (hintTheta s hs)
    have hInt : (∫ σ in s..1,
          deriv (fun u : ℝ => G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s) 1
        = ∫ σ in s..1,
            deriv (fun u : ℝ =>
              (G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1) s := by
      rw [intervalIntegral_apply_fin2 (i := 1) (h := hintOut s hs)]
      refine intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2) (fun σ hσ => ?_)
      have hdp := deriv_pi (𝕜 := ℝ) (x := s) (ι := Fin 2) (E' := fun _ : Fin 2 => ℝ)
        (φ := fun u : ℝ => G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ))
        (fun j : Fin 2 => (differentiableAt_pi.mp (hdiff s hs σ hσ)) j)
      exact congrFun hdp 1
    rw [Pi.add_apply, Pi.neg_apply, hInt]
    linarith [hrow]
  funext i
  fin_cases i
  · exact key0
  · exact key1

end

end Work.OddBridge
