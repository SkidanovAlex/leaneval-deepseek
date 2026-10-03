import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Interfaces.Parabolic

/-!
# PERT · derivative of `τ₀ ∘ seedP` (chain rule for `f ↦ τ₀(τ (Φ⁻¹ w))`)

`seedP τ Φ Q w = τ (invOn Φ Q w)` is the seed value of the maximal-domain construction on the gate
image `Φ '' Q`.  Near a point `Φ ζ₀` at which `Φ` is conformal (`deriv Φ ζ₀ ≠ 0`), `invOn Φ Q` is a
local inverse of `Φ`, hence `HasStrictDerivAt (invOn Φ Q) (deriv Φ ζ₀)⁻¹ (Φ ζ₀)` (the inverse
function theorem, `HasStrictDerivAt.to_local_left_inverse`).  Composing with the (differentiable,
thanks to `τ ζ₀ ≠ 0`) map `w ↦ τ₀ (τ w)` gives the chain-rule formula.
-/

namespace Work.Pert

open MandelDim Complex Set Filter
open scoped Topology

theorem deriv_tau0_seedP {τ Φ : ℂ → ℂ} {Q : Set ℂ} {ζ₀ : ℂ}
    (hQ : IsOpen Q) (hΦ : DifferentiableOn ℂ Φ Q) (hinj : Set.InjOn Φ Q) (hζ₀ : ζ₀ ∈ Q)
    (hderΦ : deriv Φ ζ₀ ≠ 0) (hτ : DifferentiableAt ℂ τ ζ₀) (hτz : τ ζ₀ ≠ 0) :
    HasDerivAt (fun w => MandelDim.tau0 (Work.Pert.seedP τ Φ Q w))
      (deriv (fun ζ => MandelDim.tau0 (τ ζ)) ζ₀ / deriv Φ ζ₀) (Φ ζ₀) := by
  have hana : AnalyticAt ℂ Φ ζ₀ := hΦ.analyticAt (hQ.mem_nhds hζ₀)
  have hstr : HasStrictDerivAt Φ (deriv Φ ζ₀) ζ₀ := hana.hasStrictDerivAt
  -- `invOn Φ Q` is a local left inverse of `Φ` near `ζ₀`
  have hleft : ∀ᶠ x in 𝓝 ζ₀, invOn Φ Q (Φ x) = x := by
    filter_upwards [hQ.mem_nhds hζ₀] with x hx
    exact invOn_eq hinj ⟨x, hx, rfl⟩ hx rfl
  have hInv : HasStrictDerivAt (invOn Φ Q) (deriv Φ ζ₀)⁻¹ (Φ ζ₀) :=
    hstr.to_local_left_inverse hderΦ hleft
  -- the chosen preimage of `Φ ζ₀` is `ζ₀`
  have hu0 : invOn Φ Q (Φ ζ₀) = ζ₀ := invOn_eq hinj ⟨ζ₀, hζ₀, rfl⟩ hζ₀ rfl
  -- `w ↦ τ₀ (τ w)` is differentiable at `ζ₀`
  have htau0 : DifferentiableAt ℂ MandelDim.tau0 (τ ζ₀) := by
    unfold MandelDim.tau0
    fun_prop (disch := exact hτz)
  have hcompdiff : DifferentiableAt ℂ (fun ζ => MandelDim.tau0 (τ ζ)) ζ₀ :=
    htau0.comp ζ₀ hτ
  have hτa : HasDerivAt (fun ζ => MandelDim.tau0 (τ ζ))
      (deriv (fun ζ => MandelDim.tau0 (τ ζ)) ζ₀) ζ₀ := hcompdiff.hasDerivAt
  have hτa' : HasDerivAt (fun ζ => MandelDim.tau0 (τ ζ))
      (deriv (fun ζ => MandelDim.tau0 (τ ζ)) ζ₀) (invOn Φ Q (Φ ζ₀)) := by
    rw [hu0]; exact hτa
  -- chain rule
  have key := hτa'.comp (Φ ζ₀) hInv.hasDerivAt
  simpa [seedP, Function.comp_def, div_eq_mul_inv] using key

end Work.Pert
