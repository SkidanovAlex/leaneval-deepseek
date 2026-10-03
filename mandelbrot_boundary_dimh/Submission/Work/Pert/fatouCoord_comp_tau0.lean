import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert

open Set

/-- `τ₀` is an involution (the value at `0` is Lean's junk `0⁻¹ = 0`, which is fixed by `τ₀`). -/
private lemma tau0_tau0 (x : ℂ) : MandelDim.tau0 (MandelDim.tau0 x) = x := by
  simp only [MandelDim.tau0, div_eq_mul_inv]
  rw [mul_inv, inv_neg, inv_one, inv_inv]
  ring

/-- `τ₀` is injective (indeed a bijection of `ℂ`). -/
private lemma tau0_injective : Function.Injective MandelDim.tau0 := by
  intro a b hab
  have h := congrArg MandelDim.tau0 hab
  rwa [tau0_tau0 a, tau0_tau0 b] at h

/-- `τ₀` is holomorphic away from `0`. -/
private lemma differentiableOn_tau0 {Q : Set ℂ} (h0 : (0 : ℂ) ∉ Q) :
    DifferentiableOn ℂ MandelDim.tau0 Q := by
  intro z hz
  rw [show MandelDim.tau0 = fun y : ℂ => (-1 : ℂ) * y⁻¹ from rfl]
  exact ((differentiableAt_inv_iff.mpr (fun h => h0 (h ▸ hz))).const_mul (-1)).differentiableWithinAt

/-- The unperturbed limit coordinate on the `Φ₊` side: if a region `Q` (avoiding `0`) has
`tau0 '' Q` inside the parabolic basin, then `Φ₀ := d.Φ ∘ tau0` is a Fatou coordinate for
`F₀ = tau0 ∘ f₀ ∘ tau0` on `Q`, provided it is injective there.  (The Abel equation is
`d.Φ_abel` plus `tau0 ∘ tau0 = id`.) -/
theorem fatouCoord_comp_tau0 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Q : Set ℂ} (h0 : (0 : ℂ) ∉ Q)
    (hsub : ∀ ζ ∈ Q, MandelDim.tau0 ζ ∈ MandelDim.ParabolicBasin f₀ D₀)
    (hinj : Set.InjOn d.Φ (MandelDim.tau0 '' Q)) :
    MandelDim.IsFatouCoordOn (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
      (fun ζ : ℂ => d.Φ (MandelDim.tau0 ζ)) Q := by
  refine ⟨?_, ?_, ?_⟩
  · -- holomorphy: `Φ ∘ τ₀` with `τ₀ '' Q ⊆ basin`
    exact DifferentiableOn.comp d.Φ_holo (differentiableOn_tau0 h0) hsub
  · -- injectivity descends from `InjOn Φ (τ₀ '' Q)` along the injective `τ₀`
    intro a ha b hb hab
    exact tau0_injective (hinj ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hab)
  · -- the Abel equation: `Φ (F₀ ζ) = Φ (τ₀ (τ₀ (f₀ (τ₀ ζ)))) = Φ (f₀ (τ₀ ζ)) = Φ ζ + 1`
    intro ζ hζ _
    change d.Φ (MandelDim.tau0 (MandelDim.tau0 (f₀ (MandelDim.tau0 ζ)))) =
      d.Φ (MandelDim.tau0 ζ) + 1
    rw [tau0_tau0]
    exact d.Φ_abel (MandelDim.tau0 ζ) (hsub ζ hζ)

end Work.Pert
