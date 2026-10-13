import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open Set

namespace Work.FTS.StrongEps.KernAux

set_option autoImplicit false

/-- `sin (2 · arctan x) = 2x / (1 + x²)`. -/
theorem sin_two_arctan (x : ℝ) : Real.sin (2 * Real.arctan x) = 2 * x / (1 + x ^ 2) := by
  have hpos : 0 < √(1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp
  rw [Real.sq_sqrt (by positivity)]

/-- **The derivative of the `θ`-shift in its parameter**: for the shift
`thShift θ t = arctan (tan θ · e^{-t})`, differentiating in `t` gives
`∂_t (thShift θ t) = -(1/2) sin (2 · thShift θ t)`. -/
theorem hasDerivAt_thShift_snd (θ t : ℝ) :
    HasDerivAt (fun s : ℝ => Work.FTS.StrongEps.thShift θ s)
      (-(1 / 2) * Real.sin (2 * Work.FTS.StrongEps.thShift θ t)) t := by
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * (-1)) t :=
    (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  have htan : HasDerivAt (fun s : ℝ => Real.tan θ * Real.exp (-s))
      (Real.tan θ * (Real.exp (-t) * (-1))) t := hexp.const_mul (Real.tan θ)
  have hval : -(1 / 2) * Real.sin (2 * Work.FTS.StrongEps.thShift θ t)
      = 1 / (1 + (Real.tan θ * Real.exp (-t)) ^ 2) *
        (Real.tan θ * (Real.exp (-t) * (-1))) := by
    have hsin : Real.sin (2 * Work.FTS.StrongEps.thShift θ t)
        = 2 * (Real.tan θ * Real.exp (-t)) / (1 + (Real.tan θ * Real.exp (-t)) ^ 2) := by
      rw [show Work.FTS.StrongEps.thShift θ t
          = Real.arctan (Real.tan θ * Real.exp (-t)) from rfl, sin_two_arctan]
    rw [hsin]
    simp only [div_eq_mul_inv, one_mul]
    ring
  have harc : HasDerivAt (fun s : ℝ => Real.arctan (Real.tan θ * Real.exp (-s)))
      (1 / (1 + (Real.tan θ * Real.exp (-t)) ^ 2) *
        (Real.tan θ * (Real.exp (-t) * (-1)))) t :=
    HasDerivAt.comp_of_eq t (Real.hasDerivAt_arctan (Real.tan θ * Real.exp (-t))) htan rfl
  have hfun : (fun s : ℝ => Work.FTS.StrongEps.thShift θ s)
      = fun s : ℝ => Real.arctan (Real.tan θ * Real.exp (-s)) := rfl
  rw [hfun, hval]
  exact harc

/-- **The `t`-derivative of the shifted profile**: because the `θ`-shift is the translation
`ζ ↦ ζ - t` in the log coordinate `ζ = log tan θ`, differentiating the shifted profile in the
shift parameter is differentiation along `D_θ = sin(2θ) ∂_θ`, up to the factor `-1/2`. -/
theorem deriv_shift_snd (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.StrongEps.Quad) (p : ℝ × ℝ) :
    deriv (fun t : ℝ => g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ t)) p.2
      = -(1 / 2) * Work.Spaces.Dth g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
  have hopen : IsOpen Work.FTS.StrongEps.Quad := isOpen_Ioi.prod isOpen_Ioo
  have hz₀ : 0 < Work.FTS.StrongEps.zShift z p.1 := Work.FTS.StrongEps.zShift_pos hz
  have hθ₀ : Work.FTS.StrongEps.thShift θ p.2 ∈ Set.Ioo 0 (π / 2) :=
    Work.FTS.StrongEps.thShift_mem hθ
  have hmem : (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)
      ∈ Work.FTS.StrongEps.Quad := ⟨hz₀, hθ₀⟩
  have hcont : ContDiffAt ℝ 1 (Function.uncurry g)
      (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2) :=
    hg.contDiffAt (hopen.mem_nhds hmem)
  have hpair : ContDiffAt ℝ 1 (fun y : ℝ => (Work.FTS.StrongEps.zShift z p.1, y))
      (Work.FTS.StrongEps.thShift θ p.2) := by fun_prop
  have hslice : DifferentiableAt ℝ (fun y : ℝ => g (Work.FTS.StrongEps.zShift z p.1) y)
      (Work.FTS.StrongEps.thShift θ p.2) :=
    (ContDiffAt.comp (Work.FTS.StrongEps.thShift θ p.2) hcont hpair).differentiableAt_one
  have hG : HasDerivAt (fun y : ℝ => g (Work.FTS.StrongEps.zShift z p.1) y)
      (Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2))
      (Work.FTS.StrongEps.thShift θ p.2) := hslice.hasDerivAt
  have hmain : deriv (fun t : ℝ => g (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ t)) p.2
      = Work.Spaces.pth g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)
        * (-(1 / 2) * Real.sin (2 * Work.FTS.StrongEps.thShift θ p.2)) :=
    (HasDerivAt.comp_of_eq p.2 hG (hasDerivAt_thShift_snd θ p.2) rfl).deriv
  rw [hmain]
  unfold Work.Spaces.Dth
  ring

end Work.FTS.StrongEps.KernAux
