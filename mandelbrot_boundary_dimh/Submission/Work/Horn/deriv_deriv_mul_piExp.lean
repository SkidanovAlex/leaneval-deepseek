import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# `deriv (deriv (ζ ↦ ζ · π(H ζ))) 0 = 4πi · H'(0)`

Shishikura's germ normalisation uses the "lifted" coordinate `π(w) = exp(2πiw)`.  For an
analytic germ `H` at `0` with `H 0 = 0`, the push-down of `w ↦ w + H(w)` is
`ζ ↦ ζ · π(H(ζ))`, and the first non-trivial jet coefficient of this map at `0` is precisely
`4πi · H'(0)`.  Indeed `π(H(ζ)) = 1 + 2πi H'(0) ζ + O(ζ²)`, whence
`ζ π(H ζ) = ζ + 2πi H'(0) ζ² + O(ζ³)`, so the second derivative at `0` equals
`2 · 2πi H'(0) = 4πi H'(0)`.

The proof is organized around the elementary second-order Taylor lemma
`deriv_deriv_mul_of`: for a germ `φ` which is differentiable near `0` and whose derivative is
itself differentiable at `0` one has `deriv (deriv (ζ ↦ ζ · φ ζ)) 0 = 2 · deriv φ 0`.
-/

namespace Work.Horn

open MandelDim Filter Topology

noncomputable section

/-- `deriv π w = 2πi · π w` for the lift `π(w) = exp(2πiw)`. -/
theorem piExp_deriv (w : ℂ) :
    deriv MandelDim.piExp w = 2 * ↑Real.pi * Complex.I * MandelDim.piExp w := by
  unfold MandelDim.piExp
  rw [deriv_cexp (f := fun w : ℂ => 2 * ↑Real.pi * Complex.I * w) (by fun_prop),
    deriv_const_mul_id]
  ring

/-- `π(w) = exp(2πiw)` is entire. -/
theorem piExp_analyticAt (w : ℂ) : AnalyticAt ℂ MandelDim.piExp w := by
  unfold MandelDim.piExp
  fun_prop

/-- **Second-order Taylor lemma.**  For a germ `φ` differentiable near `0` whose derivative is
differentiable at `0`, the map `ζ ↦ ζ · φ ζ` has second derivative `2 · φ'(0)` at `0`. -/
theorem deriv_deriv_mul_of (φ : ℂ → ℂ)
    (h1 : ∀ᶠ ζ in 𝓝 (0 : ℂ), DifferentiableAt ℂ φ ζ)
    (h2 : DifferentiableAt ℂ (deriv φ) 0) :
    deriv (deriv (fun ζ : ℂ => ζ * φ ζ)) 0 = 2 * deriv φ 0 := by
  have h0φ : DifferentiableAt ℂ φ 0 := h1.self_of_nhds
  -- `(ζ ↦ ζ φ ζ)' = φ ζ + ζ φ' ζ` for `ζ` near `0`
  have hev : (fun ζ : ℂ => deriv (fun ζ : ℂ => ζ * φ ζ) ζ) =ᶠ[𝓝 (0 : ℂ)]
      (fun ζ : ℂ => φ ζ + ζ * deriv φ ζ) := by
    filter_upwards [h1] with ζ hζ
    rw [deriv_fun_mul (c := fun ζ : ℂ => ζ) (d := φ) differentiableAt_id hζ]
    simp
  rw [hev.deriv_eq]
  have hA : deriv (fun ζ : ℂ => φ ζ + ζ * deriv φ ζ) 0
      = deriv φ 0 + deriv (fun ζ : ℂ => ζ * deriv φ ζ) 0 := by
    simpa using deriv_fun_add (f := φ) (g := fun ζ : ℂ => ζ * deriv φ ζ) h0φ
      (differentiableAt_id.mul h2)
  rw [hA, deriv_fun_mul (c := fun ζ : ℂ => ζ) (d := deriv φ) differentiableAt_id h2]
  simp
  ring

/-- The push-down of `w ↦ w + H w` through `π` has second derivative `4πi H'(0)` at `0`. -/
theorem deriv_deriv_mul_piExp {H : ℂ → ℂ} (hH : AnalyticAt ℂ H 0) (h0 : H 0 = 0) :
    deriv (deriv (fun ζ : ℂ => ζ * MandelDim.piExp (H ζ))) 0
      = 4 * (Real.pi : ℂ) * Complex.I * deriv H 0 := by
  set φ : ℂ → ℂ := fun ζ => MandelDim.piExp (H ζ) with hφ
  have h1 : ∀ᶠ ζ in 𝓝 (0 : ℂ), DifferentiableAt ℂ φ ζ := by
    rw [hφ]
    filter_upwards [hH.eventually_analyticAt] with ζ hζ
    exact DifferentiableAt.comp (f := H) (g := MandelDim.piExp) ζ
      (piExp_analyticAt (H ζ)).differentiableAt hζ.differentiableAt
  have h2 : DifferentiableAt ℂ (deriv φ) 0 := by
    have hφa : AnalyticAt ℂ φ 0 := by
      rw [hφ]
      exact (piExp_analyticAt (H 0)).comp hH
    exact hφa.deriv.differentiableAt
  rw [deriv_deriv_mul_of φ h1 h2]
  have hdφ : deriv φ 0 = 2 * ↑Real.pi * Complex.I * deriv H 0 := by
    rw [hφ]
    change deriv (MandelDim.piExp ∘ H) 0 = 2 * ↑Real.pi * Complex.I * deriv H 0
    rw [deriv_comp (x := (0 : ℂ)) (h₂ := MandelDim.piExp) (h := H)
      (piExp_analyticAt (H 0)).differentiableAt hH.differentiableAt]
    rw [h0, piExp_deriv]
    simp [MandelDim.piExp]
  rw [hdφ]
  ring

end

end Work.Horn
