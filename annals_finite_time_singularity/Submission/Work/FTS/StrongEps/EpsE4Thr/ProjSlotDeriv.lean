/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/ProjSlotDeriv.lean` — slot derivatives of the
projected mollified family

The energy identities of `AprioriP` (level four and level six) are computed along the
**projected mollified** family `x(τ) = slice (JfamP ρ ε g) τ = Pz (J_ε (slice g τ))`, and their
slot facts need, for every word `X = D_z^j D_θ^i` (of the order the corresponding level requires),

  `∂_τ (X (x τ)) = X (∂_τ x τ) = X (Pz (J_ε (epsRHSP τ)))`.

This module performs the *algebraic* half of that, in the form in which it is consumed:

  `HasDerivWithinAt (fun s => mixed j i (slice (JfamP ρ ε g) s) z θ)
     (mixed j i (Pz (Jeps ρ ε (epsRHSP … τ))) z θ) (Icc 0 T) τ`

from the two *analytic* inputs at level `(j,i)`:

* `hJeps` — the mollified-but-unprojected version
  `∂_τ (J_ε (mixed j i (slice g τ))) = J_ε (mixed j i (epsRHSP τ))`.  This is the composition of
  `EpsE4Thr.mixed_slice_deriv` (the pointwise slot chain rule for the *raw* family) with
  `EpsE4Thr.Jeps_family_deriv` (differentiation of `J_ε` of an arbitrary family);
* `hL12` — the fake-time derivative of the `L₁₂`-zero mode, `EpsE4Thr.L12_Jeps_deriv`.

The algebra is the pointwise identity

  `mixed j i (Pz (J_ε f)) z θ = J_ε (mixed j i f) z θ − c(f) · mixed j i bump z θ`,
  `c(f) = L₁₂ (J_ε f) (0) / pzNorm`,

which uses, in this order: `Pz_apply`, the linearity of `mixed j i` on the difference
(`mixed_sub_of_contDiffOn_four`, which is why the statement carries `j + i ≤ 4`), the
homogeneity `mixed_const_mul`, and the commutation with the mollifier `mixed_Jeps`
(`D_z^j D_θ^i (J_ε f) = J_ε (D_z^j D_θ^i f)`).  The parameter `τ` enters only through the two
derivative hypotheses, so the statement is *level-free* in form and can be instantiated at
`j + i ≤ 4` (the level-four energy, `IP4 = IPiter 3`, needs at most order four) or, once the
linearity lemmas are available at higher order, at `j + i ≤ 6`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four
import Submission.Work.FTS.StrongEps.mixed_const_mul
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.JepsSmoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The pointwise identity of the projected slot**: for `j + i ≤ 4` and a profile `f` which is
`C^∞` on the open quadrant,

  `mixed j i (Pz (J_ε f)) z θ = J_ε (mixed j i f) z θ − c · mixed j i bump z θ`

with `c = L₁₂ (J_ε f) (0) / pzNorm`.  The constant `c` (in `(z,θ)`) comes out of the slot
operator by `mixed_const_mul`, and `mixed j i` commutes with `J_ε` by `mixed_Jeps`. -/
theorem mixed_Pz_Jeps_eq (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {j i : ℕ} (hji : j + i ≤ 4) :
    Work.Spaces.mixed j i (Pz (Work.FTS.StrongEps.Jeps ρ ε f)) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed j i f) z θ
        - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0 / pzNorm)
            * Work.Spaces.mixed j i bump z θ := by
  -- the projection written pointwise as `J_ε f - c·bump`
  have hPeq : Pz (Work.FTS.StrongEps.Jeps ρ ε f) = fun z' θ' =>
      Work.FTS.StrongEps.Jeps ρ ε f z' θ'
        - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0 / pzNorm) * bump z' θ' := by
    funext z' θ'
    rw [Pz_apply]
  rw [hPeq]
  -- the two `C^4` hypotheses of the difference rule
  have hJsm : ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε f)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.FTS.StrongEps.Jeps ρ ε f)).mp
      (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsm) 4
  have hBsm : ContDiffOn ℝ 4 (Function.uncurry (fun z' θ' =>
        (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0 / pzNorm) * bump z' θ'))
      Work.FTS.EllipticEst.Q0 := by
    have hb : ContDiffOn ℝ 4 (Function.uncurry bump) Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall bump).mp smoothOpen_bump 4
    have h := ContDiffOn.const_smul
      (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0 / pzNorm) hb
    refine h.congr ?_
    intro p _
    rcases p with ⟨z', θ'⟩
    rfl
  rw [Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four hji hz hθ hJsm hBsm]
  rw [Work.FTS.StrongEps.mixed_const_mul
    (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε f) 0 / pzNorm)
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall bump).mp smoothOpen_bump) hz hθ]
  exact congrArg (fun t => t - _ * Work.Spaces.mixed j i bump z θ)
    (Work.FTS.StrongEps.mixed_Jeps ρ hρ.moll hε hsm hz hθ j i)

/-- **The slot derivative of the projected mollified family.**  With the two analytic inputs at
level `(j,i)` — the mollified slot chain rule (`hJeps`) and the `L₁₂`-zero-mode derivative
(`hL12`) — the corresponding slot of the projected family `x(τ) = slice (JfamP ρ ε g) τ` has the
fake-time derivative `mixed j i (Pz (J_ε (epsRHSP … τ)))`. -/
theorem hasDerivWithinAt_mixed_JfamP {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α T ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam} {τ : ℝ}
    (hε : 0 < ε)
    (hsm : ∀ s ∈ Set.Icc 0 T,
      ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (slice g s)) Work.FTS.EllipticEst.Q0)
    (hsmR : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (epsRHSP α ρ ε Φs E g τ)) Work.FTS.EllipticEst.Q0)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) {j i : ℕ} (hji : j + i ≤ 4)
    (hτ : τ ∈ Set.Ioo 0 T)
    (hJeps : HasDerivWithinAt
      (fun s => Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed j i (slice g s)) z θ)
      (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g τ)) z θ)
      (Set.Icc 0 T) τ)
    (hL12 : HasDerivWithinAt
      (fun s => Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g s)) 0)
      (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
        (epsRHSP α ρ ε Φs E g τ)) 0) (Set.Icc 0 T) τ) :
    HasDerivWithinAt (fun s => Work.Spaces.mixed j i (slice (JfamP ρ ε g) s) z θ)
      (Work.Spaces.mixed j i (Pz (Work.FTS.StrongEps.Jeps ρ ε
        (epsRHSP α ρ ε Φs E g τ))) z θ) (Set.Icc 0 T) τ := by
  -- the pointwise expansion of the projected slot, at every `s` (and at `τ`)
  have hexp : ∀ s ∈ Set.Icc 0 T, Work.Spaces.mixed j i (slice (JfamP ρ ε g) s) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed j i (slice g s)) z θ
        - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g s)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump z θ := by
    intro s hs
    have h1 : slice (JfamP ρ ε g) s
        = Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g s)) := rfl
    rw [h1]
    exact mixed_Pz_Jeps_eq ρ hρ hε (hsm s hs) hz hθ hji
  have hval : Work.Spaces.mixed j i (Pz (Work.FTS.StrongEps.Jeps ρ ε
        (epsRHSP α ρ ε Φs E g τ))) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g τ)) z θ
        - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε
            (epsRHSP α ρ ε Φs E g τ)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump z θ :=
    mixed_Pz_Jeps_eq ρ hρ hε hsmR hz hθ hji
  rw [hval]
  refine (hJeps.sub ((hL12.div_const pzNorm).mul_const
    (Work.Spaces.mixed j i bump z θ))).congr ?_ ?_
  · intro s hs
    change Work.Spaces.mixed j i (slice (JfamP ρ ε g) s) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed j i (slice g s)) z θ
        - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g s)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump z θ
    exact hexp s hs
  · change Work.Spaces.mixed j i (slice (JfamP ρ ε g) τ) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed j i (slice g τ)) z θ
        - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε (slice g τ)) 0 / pzNorm)
            * Work.Spaces.mixed j i bump z θ
    exact hexp τ ⟨hτ.1.le, hτ.2.le⟩

end Work.FTS.StrongEps.EpsE4Thr
