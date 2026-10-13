/-
Copyright: work module for the Elgindi finite-time singularity project.

# The two "slot" identities relating `D_z` to the second derivatives

The level-`0` estimate `EllWeak0` bounds `z²∂_z²Ψ'` and `∂_θ²Ψ'` for a datum `(F', Ψ')` of the
class, whereas the target of `shiftedTwoL2` bounds `D_z²(z²∂_z²Ψ)` and `D_z²(∂_θ²Ψ)`.  The bridge
is that the *difference quotient* of the once-shifted datum `(D_zF, D_zΨ)` has slots

  `z²∂_z²(dq c (D_zΨ)) = dq c (z²∂_z²(D_zΨ))`  (the chain rule, `DilBasic.zsq_pzIter_two_dq`),

and `z²∂_z²(D_zΨ) = D_z (z²∂_z²Ψ)`, `∂_θ²(D_zΨ) = D_z (∂_θ²Ψ)` — the two identities proved here
(on the open quadrant, as `AgreeOnQ` statements, so that `HkSq_congr_open` transfers them to the
integrals).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.Cores.Dil.DilBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `z`-derivatives of `D_z g` -/

/-- `∂_z (z ∂_z g) = ∂_z g + z ∂_z²g`. -/
theorem pz_Dz_eq {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (Work.Spaces.Dz g) z θ
        = Work.Spaces.pz g z θ + z * Work.Spaces.pzIter 2 g z θ := by
  intro z θ hz hθ
  have h2 := (hg.pz).hasDerivAt_slice hθ hz
  have hgoal : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz g z' θ)
      (Work.Spaces.pz g z θ + z * Work.Spaces.pzIter 2 g z θ) z := by
    have h := (hasDerivAt_id z).mul h2
    have hfun : (fun z' : ℝ => z' * Work.Spaces.pz g z' θ)
        = id * (fun z' : ℝ => Work.Spaces.pz g z' θ) := by
      funext z'; simp
    rw [hfun]
    simpa using h
  rw [show Work.Spaces.pz (Work.Spaces.Dz g) z θ
      = deriv (fun z' : ℝ => z' * Work.Spaces.pz g z' θ) z from rfl]
  exact hgoal.deriv

/-- `∂_z²(z ∂_z g) = 2 ∂_z²g + z ∂_z³g`. -/
theorem pzIter_two_Dz_eq {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pzIter 2 (Work.Spaces.Dz g) z θ
        = 2 * Work.Spaces.pzIter 2 g z θ + z * Work.Spaces.pzIter 3 g z θ := by
  intro z θ hz hθ
  have h1 := (hg.pz).hasDerivAt_slice hθ hz
  have h2 := (hg.pzIter 2).hasDerivAt_slice hθ hz
  have hprod : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pzIter 2 g z' θ)
      (Work.Spaces.pzIter 2 g z θ + z * Work.Spaces.pzIter 3 g z θ) z := by
    have h := (hasDerivAt_id z).mul h2
    have hfun : (fun z' : ℝ => z' * Work.Spaces.pzIter 2 g z' θ)
        = id * (fun z' : ℝ => Work.Spaces.pzIter 2 g z' θ) := by
      funext z'; simp
    rw [hfun]
    simpa using h
  have hsum : HasDerivAt
      (fun z' : ℝ => Work.Spaces.pz g z' θ + z' * Work.Spaces.pzIter 2 g z' θ)
      (Work.Spaces.pzIter 2 g z θ + (Work.Spaces.pzIter 2 g z θ
        + z * Work.Spaces.pzIter 3 g z θ)) z := h1.add hprod
  have hev : (fun z' : ℝ => Work.Spaces.pz (Work.Spaces.Dz g) z' θ)
      =ᶠ[𝓝 z] (fun z' : ℝ => Work.Spaces.pz g z' θ + z' * Work.Spaces.pzIter 2 g z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact pz_Dz_eq hg z' θ hz' hθ
  rw [show Work.Spaces.pzIter 2 (Work.Spaces.Dz g) z θ
      = deriv (fun z' : ℝ => Work.Spaces.pz (Work.Spaces.Dz g) z' θ) z from rfl]
  rw [hev.deriv_eq, hsum.deriv]
  ring

/-- `∂_z(z² ∂_z²g) = 2 z ∂_z²g + z² ∂_z³g`. -/
theorem pz_zsq_pzIter_two_eq {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 g z θ) z θ
        = 2 * z * Work.Spaces.pzIter 2 g z θ + z ^ 2 * Work.Spaces.pzIter 3 g z θ := by
  intro z θ hz hθ
  have h2 := (hg.pzIter 2).hasDerivAt_slice hθ hz
  have hsq : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hgoal : HasDerivAt (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 g z' θ)
      (2 * z * Work.Spaces.pzIter 2 g z θ + z ^ 2 * Work.Spaces.pzIter 3 g z θ) z := by
    have h := hsq.mul h2
    have hfun : (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 g z' θ)
        = (fun z' : ℝ => z' ^ 2) * (fun z' : ℝ => Work.Spaces.pzIter 2 g z' θ) := by
      funext z'; simp
    rw [hfun]
    exact h
  rw [show Work.Spaces.pz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 g z θ) z θ
      = deriv (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 g z' θ) z from rfl]
  exact hgoal.deriv

/-- **The first slot identity**: `z²∂_z²(D_z g) = D_z(z² ∂_z²g)` on the open quadrant. -/
theorem zsq_pzIter_two_Dz_AgreeOnQ {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    AgreeOnQ (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.Dz g) z θ)
      (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 g z θ)) := by
  intro z θ hz hθ hlt
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hlt⟩
  show z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.Dz g) z θ
      = Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 g z θ) z θ
  rw [pzIter_two_Dz_eq hg z θ hz hθ']
  simp only [Work.Spaces.Dz]
  rw [pz_zsq_pzIter_two_eq hg z θ hz hθ']
  ring

/-! ## The `θ`-derivatives of `D_z g` -/

/-- `∂_θ(D_z g) = D_z(∂_θ g)` on the open quadrant (Clairaut). -/
theorem pth_Dz_AgreeOnQ {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    AgreeOnQ (Work.Spaces.pth (Work.Spaces.Dz g)) (Work.Spaces.Dz (Work.Spaces.pth g)) := by
  intro z θ hz hθ hlt
  have hp : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ) :=
    ((smoothOpen_iff_forall g).mp hg 2).contDiffAt (isOpen_Q0.mem_nhds hp)
  have hclair : Work.Spaces.pz (Work.Spaces.pth g) z θ
      = Work.Spaces.pth (Work.Spaces.pz g) z θ :=
    Work.Spaces.pz_pth_comm (f := g) hcd
  show deriv (fun θ' : ℝ => z * Work.Spaces.pz g z θ') θ
      = Work.Spaces.Dz (Work.Spaces.pth g) z θ
  rw [deriv_const_mul_field]
  show z * Work.Spaces.pth (Work.Spaces.pz g) z θ
      = Work.Spaces.Dz (Work.Spaces.pth g) z θ
  rw [← hclair]
  rfl

/-- **The second slot identity**: `∂_θ²(D_z g) = D_z(∂_θ²g)` on the open quadrant. -/
theorem pthIter_two_Dz_AgreeOnQ {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    AgreeOnQ (Work.Spaces.pthIter 2 (Work.Spaces.Dz g))
      (Work.Spaces.Dz (Work.Spaces.pthIter 2 g)) := by
  have h1 := pth_Dz_AgreeOnQ hg
  have h2 := pth_Dz_AgreeOnQ (hg.pth)
  intro z θ hz hθ hlt
  have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ, hlt⟩
  have hp : (z, θ) ∈ Q0 := mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd' : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth g)) (z, θ) :=
    ((smoothOpen_iff_forall (Work.Spaces.pth g)).mp (hg.pth) 2).contDiffAt
      (isOpen_Q0.mem_nhds hp)
  have hclair : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth g)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) z θ :=
    Work.Spaces.pz_pth_comm (f := Work.Spaces.pth g) hcd'
  rw [Work.Spaces.pthIter_succ]
  show deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.Dz g) z θ') θ = _
  have hev : (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.Dz g) z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.Dz (Work.Spaces.pth g) z θ') := by
    filter_upwards [Ioo_mem_nhds hθ'.1 hθ'.2] with θ'' hθ''
    exact h1 z θ'' hz hθ''.1 hθ''.2
  rw [hev.deriv_eq]
  show deriv (fun θ' : ℝ => z * Work.Spaces.pz (Work.Spaces.pth g) z θ') θ = _
  rw [deriv_const_mul_field]
  show z * Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth g)) z θ
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 g) z θ
  rw [← hclair]
  show z * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth g)) z θ
      = Work.Spaces.Dz (Work.Spaces.pthIter 2 g) z θ
  rw [show Work.Spaces.pth (Work.Spaces.pth g) = Work.Spaces.pthIter 2 g from rfl]
  rfl

end Work.FTS.EllipticEst.Cores.Dil
