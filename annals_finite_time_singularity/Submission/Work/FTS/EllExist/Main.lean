/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS.EllExist.Main` — the assembly of the existence node `EllClassO`

This module contains the *proof-level* content of the area `FTS/EllExist`: the reduction of the
existence node `EllClassO α g Ψ` (design `FTS/FTS_ELL_GALERKIN.md` §1 (b)) to

* the elliptic existence node for the **orthogonalised** source `orthSource g`, i.e. a function
  `Ψ'` with `Work.FTS.EllipticEst.TT.EllWeakPos α 4 (orthSource g) Ψ'` and
  `IsBslSol α (orthSource g) Ψ'` (supplied by `Work.FTS.PhiStar.bslOp_sol_exists 4`, used in
  `FTS/EllExist/Exists.lean`), and
* the three *singular-term* facts about `Gsing α g` (all-order smoothness on `(0,∞)`, the
  second-order ODE, and the decay at infinity).

Given those, the unshifted unknown `Ψ := unshift α g Ψ' = Ψ' - Gsing α g · sin 2θ` is an element
of `EllClassO α g Ψ`.

## Correction of the requested statement

The version of the existence node requested for this area (`ellClassO_exists`, with the hypothesis
`GalClass α g` only) is **false**.  `FTS/EllExist/Necessary.lean` proves the necessary condition

  `EllClassO α g Ψ → ∀ n, ContDiffOn ℝ n (Gsing α g) (Ioi 0)`,

and `NOTES_EllExist.md` in this directory records the explicit admissible counterexample: an
admissible profile whose angular profile pinches to `θ = 0` at a scale depending smoothly on `z`,
for which `z ↦ F_*(g)(z)` is `C⁹` but not `C¹⁰` at an interior point `z₀ > 0`.  Since
`Gsing α g` is an explicit functional of `F_*(g)` (and the singular-term ODE expresses `F_*(g)`
back in terms of `Gsing α g`), `Gsing α g` is then not `C^∞`, so no `Ψ` can lie in `EllClassO`.

`GalClass` constrains `g` only up to order `6` (`RegQ α 6 g` plus `DecayAll 6 g`) and gives no
domination uniform in `z` at the angular endpoints, which is exactly what an all-order
differentiation under the angular integral needs.

The corrected statement is `ellClassO_exists_of_inputs` of `FTS/EllExist/Exists.lean`, in which
the honest analytic inputs are made explicit; `ellClassO_of_bslOp_node` below is the assembly
proper and is unconditional.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.bslOp_sinG
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllExist.Defs
import Submission.Work.FTS.EllExist.Shift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The unshifted unknown of a shifted solution -/

/-- The inverse of `shiftSing α g`: subtract the same radial multiple of `sin 2θ`. -/
def unshift (α : ℝ) (g Ψ' : Fn) : Fn :=
  fun z θ => Ψ' z θ - Work.Elliptic.Gsing α g z * Real.sin (2 * θ)

@[simp] theorem unshift_apply (α : ℝ) (g Ψ' : Fn) (z θ : ℝ) :
    unshift α g Ψ' z θ = Ψ' z θ - Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl

/-- `shiftSing` and `unshift` are mutually inverse. -/
theorem shiftSing_unshift (α : ℝ) (g Ψ' : Fn) : shiftSing α g (unshift α g Ψ') = Ψ' := by
  funext z θ
  simp only [shiftSing_apply, unshift_apply]
  ring

/-! ## Smoothness, Dirichlet data and decay transfer -/

/-- `Gsing α g` times `sin 2θ` is `C^n` on the open quadrant as soon as `Gsing α g` is `C^n` on
`(0,∞)`. -/
theorem contDiffOn_Gsing_sin (α : ℝ) (g : Fn) (n : ℕ)
    (hG : ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0)) :
    ContDiffOn ℝ (n : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Elliptic.Gsing α g p.1 * Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Work.Elliptic.Gsing α g p.1)
      Work.FTS.EllipticEst.Q0 :=
    hG.comp contDiffOn_fst fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have h2 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 := by fun_prop
  exact h1.mul h2

/-- `SmoothOpen` transfers from `Ψ'` to `unshift α g Ψ'` as soon as `Gsing α g` is `C^∞` on
`(0,∞)`. -/
theorem smoothOpen_unshift (α : ℝ) (g Ψ' : Fn)
    (hΨ' : Work.FTS.EllipticEst.SmoothOpen Ψ')
    (hG : ∀ n : ℕ, ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0)) :
    Work.FTS.EllipticEst.SmoothOpen (unshift α g Ψ') := by
  rw [Work.FTS.EllipticEst.smoothOpen_iff_forall]
  intro n
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (Function.uncurry Ψ') Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ').mp hΨ' n
  have h2 := contDiffOn_Gsing_sin α g n (hG n)
  have hfun : Function.uncurry (unshift α g Ψ')
      = fun p : ℝ × ℝ => Function.uncurry Ψ' p
          - Work.Elliptic.Gsing α g p.1 * Real.sin (2 * p.2) := rfl
  rw [hfun]
  exact h1.sub h2

/-- The Dirichlet values transfer. -/
theorem unshift_zero (α : ℝ) (g Ψ' : Fn) (h : ∀ z, Ψ' z 0 = 0) :
    ∀ z, unshift α g Ψ' z 0 = 0 := by
  intro z; simp [unshift_apply, h z]

/-- The Dirichlet values transfer at `θ = π/2`. -/
theorem unshift_pi_half (α : ℝ) (g Ψ' : Fn) (h : ∀ z, Ψ' z (π / 2) = 0) :
    ∀ z, unshift α g Ψ' z (π / 2) = 0 := by
  intro z
  have hsin : Real.sin (2 * (π / 2)) = 0 := by
    rw [show 2 * (π / 2) = π from by ring, Real.sin_pi]
  simp [unshift_apply, h z, hsin]

/-- The decay transfers. -/
theorem tendsto_unshift (α : ℝ) (g Ψ' : Fn) (θ : ℝ)
    (hΨ' : Tendsto (fun z => Ψ' z θ) atTop (𝓝 0))
    (hG : Tendsto (fun z => Work.Elliptic.Gsing α g z) atTop (𝓝 0)) :
    Tendsto (fun z => unshift α g Ψ' z θ) atTop (𝓝 0) := by
  have hfun : (fun z => unshift α g Ψ' z θ)
      = fun z => Ψ' z θ - Work.Elliptic.Gsing α g z * Real.sin (2 * θ) := rfl
  rw [hfun]
  simpa using hΨ'.sub (hG.mul_const (Real.sin (2 * θ)))

/-! ## The assembly -/

/-- **The assembly of the existence node.**  From the elliptic node for the orthogonalised source
`orthSource g` (a `Ψ'` solving `bslOp α Ψ' = orthSource g` and lying in the weak hypothesis class
of the `ℋ⁴` estimate), together with all-order smoothness, the singular-term ODE and the decay of
`Gsing α g`, the unshifted function `unshift α g Ψ'` lies in `EllClassO α g Ψ`. -/
theorem ellClassO_of_bslOp_node {α : ℝ} {g : Fn}
    (hNode : ∃ Ψ' : Fn,
      Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g) Ψ' ∧
        Work.Elliptic.IsBslSol α (Work.Elliptic.orthSource g) Ψ')
    (hGsm : ∀ n : ℕ, ContDiffOn ℝ (n : WithTop ℕ∞) (Work.Elliptic.Gsing α g) (Set.Ioi 0))
    (hGode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α g) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α g) z
      = (15 / 4) * Work.Elliptic.Fstar g z)
    (hGdec : Tendsto (fun z => Work.Elliptic.Gsing α g z) atTop (𝓝 0)) :
    ∃ Ψ : Fn, EllClassO α g Ψ := by
  obtain ⟨Ψ', hWeak, hSol⟩ := hNode
  have hΨ'Sm : Work.FTS.EllipticEst.SmoothOpen Ψ' :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (fun n => Work.FTS.EllipticEst.TT.EllWeakPos.smooth hWeak n)
  have hSmU : Work.FTS.EllipticEst.SmoothOpen (unshift α g Ψ') :=
    smoothOpen_unshift α g Ψ' hΨ'Sm hGsm
  refine ⟨unshift α g Ψ', ?_, hSmU, ?_⟩
  · -- `IsBslSol α g (unshift α g Ψ')`
    refine ⟨?_, unshift_zero α g Ψ' hSol.2.1, unshift_pi_half α g Ψ' hSol.2.2.1, ?_⟩
    · -- the equation on the open quadrant
      intro z hz θ hθ0 hθ1
      have hcos : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
      have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩
      have hAt : ContDiffAt ℝ 2 (Function.uncurry (unshift α g Ψ')) (z, θ) :=
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall (unshift α g Ψ')).mp hSmU 2).contDiffAt
          (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
      have hGAt : ContDiffAt ℝ 2 (Work.Elliptic.Gsing α g) z :=
        (hGsm 2).contDiffAt (isOpen_Ioi.mem_nhds hz)
      have hsol : Work.Elliptic.bslOp α (shiftSing α g (unshift α g Ψ')) z θ
          = Work.Elliptic.orthSource g z θ := by
        rw [shiftSing_unshift α g Ψ']
        exact hSol.1 z hz θ hθ0 hθ1
      exact bslOp_eq_of_shiftSing_of_ode α g (unshift α g Ψ') z θ hAt hGAt hcos
        (hGode z hz) hsol
    · -- the decay
      intro θ hθ
      exact tendsto_unshift α g Ψ' θ (hSol.2.2.2 θ hθ) hGdec
  · -- the weak-class condition, transferred along `shiftSing α g (unshift α g Ψ') = Ψ'`
    show Work.FTS.EllipticEst.TT.EllWeakPos α 4 (Work.Elliptic.orthSource g)
      (shiftSing α g (unshift α g Ψ'))
    rw [shiftSing_unshift α g Ψ']
    exact hWeak

end Work.FTS.EllExist
