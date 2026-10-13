import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The first partial derivative of the `(z,θ)`-shift

`Work.FTS.StrongEps.zShift z s = z * e^{-s}` is the `z`-component of the two-dimensional
translation `(s,ζ) ↦ (s - p₁, ζ - p₂)` of the log-coordinates of the mollifier `Jeps`.
Differentiating the shifted profile in the shift parameter `s` therefore differentiates it in
the *logarithmic* radial variable: since `d/ds (z e^{-s}) = -(z e^{-s})`,

  `∂_s [ g (z e^{-s}) θ' ] = -(z ∂_z g) (z e^{-s}, θ') = -D_z g (z e^{-s}, θ')`,

which is exactly the identity proved below.  It is the statement that the shift acts on the
profile by transport along `D_z` (up to sign), i.e. the first half of the commutation of `J_ε`
with `D_z` (see `Submission/Work/FTS/StrongEps/Commute.lean`) that the design of the
`StrongEps` area is built on.

Note on notation: this file was delivered with a bare `π`, which — `autoImplicit` being
`false` in this project — is not the notation for `Real.pi` unless the `Real` scope is open,
so the statement did not even elaborate.  Opening the scope is the (only) faithful reading of
the requested statement: the `π` of `Work.FTS.StrongEps.Quad`, `θ ∈ (0,π/2)`, is `Real.pi`.
-/

open scoped Real

namespace Work.FTS.StrongEps.KernAux

/-- **The `z`-shift differentiates the profile along `D_z`.**  For `g` of class `C¹` on the
open quadrant, `z > 0` and `θ ∈ (0,π/2)`, the derivative in the shift parameter `s` of
`s ↦ g (z e^{-s}) (thShift θ p₂)` at `s = p₁` is `-D_z g` evaluated at the shifted point. -/
theorem deriv_shift_fst (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hg : ContDiffOn ℝ 1 (Function.uncurry g) Work.FTS.StrongEps.Quad) (p : ℝ × ℝ) :
    deriv (fun s : ℝ => g (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ p.2)) p.1
      = - Work.Spaces.Dz g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2) := by
  -- abbreviate the (constant) angular shift
  set c : ℝ := Work.FTS.StrongEps.thShift θ p.2 with hc
  -- the shifted angular variable stays in the open interval `(0,π/2)`
  have hcpos : 0 < c := by
    rw [hc, Work.FTS.StrongEps.thShift]
    exact (Real.arctan_pos).2
      (mul_pos (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2) (Real.exp_pos _))
  have hclt : c < π / 2 := by
    rw [hc, Work.FTS.StrongEps.thShift]; exact Real.arctan_lt_pi_div_two _
  -- the shifted radial variable stays positive
  have hapos : 0 < Work.FTS.StrongEps.zShift z p.1 := by
    rw [Work.FTS.StrongEps.zShift]; exact mul_pos hz (Real.exp_pos _)
  have hmem : (Work.FTS.StrongEps.zShift z p.1, c) ∈ Work.FTS.StrongEps.Quad :=
    ⟨hapos, hcpos, hclt⟩
  have hopen : IsOpen Work.FTS.StrongEps.Quad := isOpen_Ioi.prod isOpen_Ioo
  -- hence `g` is differentiable there, and so is its radial slice
  have hdiff : DifferentiableAt ℝ (Function.uncurry g) (Work.FTS.StrongEps.zShift z p.1, c) :=
    (hg.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hmem)
  have hslice : HasDerivAt (fun w : ℝ => g w c)
      (Work.Spaces.pz g (Work.FTS.StrongEps.zShift z p.1) c) (Work.FTS.StrongEps.zShift z p.1) := by
    have := (Work.Spaces.differentiableAt_curry_left hdiff).hasDerivAt
    simpa [Work.Spaces.pz] using this
  -- the shift itself: `d/ds (z e^{-s}) = -(z e^{-s})`
  have hzsh : HasDerivAt (fun s : ℝ => Work.FTS.StrongEps.zShift z s)
      (-(Work.FTS.StrongEps.zShift z p.1)) p.1 := by
    have h1 : HasDerivAt (fun s : ℝ => -s) (-1) p.1 := hasDerivAt_neg p.1
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-(Real.exp (-p.1))) p.1 :=
      h1.exp.congr_deriv (by ring)
    have h3 := h2.const_mul z
    simpa only [mul_neg, Work.FTS.StrongEps.zShift] using h3
  -- chain rule
  have hcomp := hslice.comp p.1 hzsh
  have hd : deriv (fun s : ℝ => g (Work.FTS.StrongEps.zShift z s) c) p.1
      = Work.Spaces.pz g (Work.FTS.StrongEps.zShift z p.1) c
        * (-(Work.FTS.StrongEps.zShift z p.1)) := hcomp.deriv
  rw [hd, Work.Spaces.Dz]
  ring

end Work.FTS.StrongEps.KernAux
