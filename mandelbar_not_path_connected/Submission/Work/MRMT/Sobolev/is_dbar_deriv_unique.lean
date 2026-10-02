import Mathlib
import Submission.Work.MRMT.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Sobolev

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal ContDiff

/-- The weak (distributional) `∂̄`-derivative of a locally integrable function is unique almost
everywhere: if `g` and `g'` are both weak `∂̄`-derivatives of `f`, then `g = g'` a.e.

Indeed, for every test function `φ` the two defining relations give
`∫ g φ = ∫ g' φ`, i.e. `g - g'` annihilates every test function; a locally integrable function
with that property vanishes almost everywhere, which is
`ae_eq_of_integral_contDiff_smul_eq` (specialized to real-valued test functions, using that a
smooth compactly supported real function can be regarded as a complex-valued test function). -/
theorem is_dbar_deriv_unique {f g g' : ℂ → ℂ} (h : IsDbarDeriv f g) (h' : IsDbarDeriv f g') :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), g z = g' z := by
  refine ae_eq_of_integral_contDiff_smul_eq h.2.1 h'.2.1 ?_
  intro ψ hψ hψc
  -- regard the real-valued smooth compactly supported `ψ` as a complex test function
  let φ : 𝓓(⊤, ℂ) :=
    ⟨fun z => Complex.ofReal (ψ z),
      (ContinuousLinearMap.contDiff (Complex.ofRealCLM)).comp hψ,
      hψc.mono (fun z hz => by
        rw [Function.mem_support] at hz ⊢
        exact fun h => hz (by rw [h]; simp)),
      by intro z _; trivial⟩
  have hφ : ∀ z, (φ : ℂ → ℂ) z = Complex.ofReal (ψ z) := fun _ => rfl
  -- both weak derivatives test the same against `φ`, hence the integrals agree
  have key : ∫ z, g z * (φ : ℂ → ℂ) z = ∫ z, g' z * (φ : ℂ → ℂ) z := by
    have h1 : ∫ z, f z * dzbar (φ : ℂ → ℂ) z = - ∫ z, g z * (φ : ℂ → ℂ) z :=
      (h.2.2 φ).2.2
    have h2 : ∫ z, f z * dzbar (φ : ℂ → ℂ) z = - ∫ z, g' z * (φ : ℂ → ℂ) z :=
      (h'.2.2 φ).2.2
    have : - ∫ z, g z * (φ : ℂ → ℂ) z = - ∫ z, g' z * (φ : ℂ → ℂ) z := h1.symm.trans h2
    simpa using this
  have hfun : ∀ z, ψ z • g z = g z * (φ : ℂ → ℂ) z := by
    intro z
    rw [hφ z, RCLike.real_smul_eq_coe_mul]
    exact mul_comm _ _
  have hfun' : ∀ z, ψ z • g' z = g' z * (φ : ℂ → ℂ) z := by
    intro z
    rw [hφ z, RCLike.real_smul_eq_coe_mul]
    exact mul_comm _ _
  calc ∫ z, ψ z • g z = ∫ z, g z * (φ : ℂ → ℂ) z :=
        integral_congr_ae (Eventually.of_forall hfun)
    _ = ∫ z, g' z * (φ : ℂ → ℂ) z := key
    _ = ∫ z, ψ z • g' z := (integral_congr_ae (Eventually.of_forall hfun')).symm

end Work.MRMT.Sobolev
