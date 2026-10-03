import Mathlib
import Submission.Work.FatouL1.wideStripDefs

/-!
# `Work.FatouL1.derivCocycleProduct`

The Fatou coordinate `Φ` of a near-translation `F` on Shishikura's region `𝒬 = Qreg b₁ b₂`
satisfies the exact Abel equation `Φ (F z) = Φ z + 1` (`MandelDim.IsFatouCoordOn`).  Writing
`F` as a cocycle over `Φ` and differentiating the Abel equation — which is legitimate on a
neighbourhood of `z` because `𝒬` is open and `F` is continuous — gives the product rule for the
derivative of the cocycle:

`deriv Φ z = deriv Φ (F z) * deriv F z`.

This is the elementary chain-rule input used by the multiplicative-cocycle construction
(`Work.FatouL1.cocycleCorrection` and its variants).
-/

open MandelDim Set Metric Complex
open scoped Topology

namespace Work.FatouL1

noncomputable section

/-- **`Qreg b₁ b₂` is open.** Each defining condition is of the form `0 < f` or `f < 0` for a
continuous `f`, and `b₁`, `b₂` are `Option`s, so only a finite intersection occurs. -/
lemma isOpen_Qreg_derivCocycle (b₁ b₂ : Option ℂ) : IsOpen (MandelDim.Qreg b₁ b₂) := by
  have h1 : ∀ a : ℂ, IsOpen {z : ℂ | -|(z - a).im| < (z - a).re} := fun a =>
    isOpen_lt (by fun_prop) (by fun_prop)
  have h2 : ∀ b : ℂ, IsOpen {z : ℂ | (z - b).re < |(z - b).im|} := fun b =>
    isOpen_lt (by fun_prop) (by fun_prop)
  rcases b₁ with _ | a <;> rcases b₂ with _ | b
  · convert isOpen_univ using 1; ext z; simp [MandelDim.Qreg]
  · convert h2 b using 1; ext z; simp [MandelDim.Qreg]
  · convert h1 a using 1; ext z; simp [MandelDim.Qreg]
  · convert (h1 a).inter (h2 b) using 1
    ext z; simp [MandelDim.Qreg]

/-- **The derivative of the cocycle.**  A Fatou coordinate satisfies `Φ ∘ F = Φ + 1` on the
region; differentiating on a neighbourhood of an interior point `z` (possible because the region
is open and `F` is continuous there, with `F z` still in the region) gives the chain-rule
identity `deriv Φ z = deriv Φ (F z) * deriv F z`. -/
theorem derivCocycleProduct {b₁ b₂ : Option ℂ} {F Φ : ℂ → ℂ}
    (hΦ : MandelDim.IsFatouCoordOn F Φ (MandelDim.Qreg b₁ b₂))
    (hFd : DifferentiableOn ℂ F (MandelDim.Qreg b₁ b₂))
    {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) (hzF : F z ∈ MandelDim.Qreg b₁ b₂) :
    deriv Φ z = deriv Φ (F z) * deriv F z := by
  have hQ : IsOpen (MandelDim.Qreg b₁ b₂) := isOpen_Qreg_derivCocycle b₁ b₂
  -- differentiability at the two relevant points, from `DifferentiableOn` on an open set
  have hΦd : DifferentiableAt ℂ Φ z := hΦ.1.differentiableAt (hQ.mem_nhds hz)
  have hΦdF : DifferentiableAt ℂ Φ (F z) := hΦ.1.differentiableAt (hQ.mem_nhds hzF)
  have hFdz : DifferentiableAt ℂ F z := hFd.differentiableAt (hQ.mem_nhds hz)
  -- the Abel equation holds on a neighbourhood of `z`
  have hev : (fun w => Φ (F w)) =ᶠ[𝓝 z] fun w => Φ w + 1 := by
    filter_upwards [hFdz.continuousAt.tendsto.eventually (hQ.mem_nhds hzF),
      hQ.mem_nhds hz] with w hwF hwQ
    exact hΦ.2.2 w hwQ hwF
  have h1 : deriv (fun w => Φ (F w)) z = deriv (fun w => Φ w + 1) z :=
    Filter.EventuallyEq.deriv_eq hev
  have h2 : deriv (fun w => Φ w + 1) z = deriv Φ z := by
    change deriv (Φ + fun _ => (1 : ℂ)) z = deriv Φ z
    rw [deriv_add hΦd (differentiableAt_const 1), deriv_const]
    exact add_zero _
  have h3 : deriv (fun w => Φ (F w)) z = deriv Φ (F z) * deriv F z :=
    deriv_comp z hΦdF hFdz
  rw [← h2, ← h1, h3]

end

end Work.FatouL1
