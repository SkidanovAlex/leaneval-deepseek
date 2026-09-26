import Mathlib
import Submission.Core.Final
import Submission.Work.RadialSpace.exists_contDiff_comp_sq
import Submission.Work.CKFinal.Shadow.Thm31Adapter
import Submission.Work.CKFinal.Shadow.adapter_decay
import Submission.Work.CKFinal.Shadow.RigidityP
import Submission.Work.CKFinal.Shadow.ExpansionData

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/CKFinal/DESIGN.md first (orchestrator design; your lemma is one node of its DAG; its §0 lists what is NOT actually proved and §5 what NOT to do). Clashes fixed by the lead (2026-09-25): Kaxis_bounded_compact's Pspace/Cseg/exists_local_bound_clean/… now carry a Kbc suffix; MiddleRange.Main's continuous_jInvariantFun is continuous_jInvariantFun_mr. Siblings run in parallel; import them when they land.

# ckmrv_of_satisfiesThm31_smooth  (namespace Work.CKFinal)  — interface fix (g)

FINDING: in this Mathlib `ContDiff ℝ ⊤ = ContDiff ℝ ω` (analytic; checked:
`example : (⊤ : WithTop ℕ∞) = ω := rfl`). `Submission.ckmrv_fourier_interpolation_of_satisfiesThm31`,
`Work.FunctionalEquations.Thm31Adapter`, `Work.Interpolation.adapter_decay` and the structure field
`Work.FE.FunctionalEquationSolution.smooth_F/_Ftilde` all demand real-ANALYTIC radial profiles.
CKMRV Thm 3.1 only needs C^∞, and the propagation argument only yields C^∞ (analyticity in r of the
extension off 𝒟 would need a Hartogs-type argument — do not attempt).

## The `C^∞` shadow

The whole chain `Work.FE.FunctionalEquationSolution → InterpolationBasis → CKMRV` is *proved* for
real-analytic radial profiles, but the construction (this project's `exists_thm31_pair`) only
produces `C^∞` ones.  Rather than weaken the proved chain in place — that would invalidate the
compiled state of every one of the several thousand modules below
`Submission.Work.FunctionalEquations.Basic` — the chain is *shadowed* here: the modules under
`Submission/Work/CKFinal/Shadow/` contain verbatim copies of exactly those declarations of the
chain whose types mention the solution structure, with

* `ContDiff ℝ ⊤` (analytic) replaced by `ContDiff ℝ ∞` (`Work.RadialSpace.Smooth`), and
* the solution structures re-declared with the weakened smoothness field,

placed inside the namespace prefix `Work.CKFinal.Shadow`.  Since Lean resolves a hierarchical name
to the innermost matching prefix first, every reference made *inside* the shadow files to a copied
declaration resolves to the copy, while references to everything else (the vocabulary `E`,
`dirichletTerm`, `rate`, …, and all of `Mathlib`) fall back to the original.  Nothing outside the
shadow is touched; the original analytic chain still compiles as before.

The shadow is generated mechanically by `_gen_shadow.py` from the declaration list in
`_shadow_decls.txt` (the type-mention closure of the structure over the proof cone of
`Work.Section8P.interpolationBasis_{eight,twentyfour}_of_functionalEquations` and
`Work.FE.expansionData_of_functionalEquations`); `_shadow_cfg.json` records the handful of aliases
(declarations of the unchanged vocabulary used unqualified inside the shadow namespace) and of
retained helper lemmas (`integral_rule`, `differentiableAt_profile`, the `KernelSchwartz` lemmas,
…), all of which are still proved from scratch with `ContDiff ℝ ∞` hypotheses.

The one genuinely analytic step of the chain, `Work.FunctionalEquations.contDiff_extFun`, is
replaced by its `C^∞` version, which uses the Borel-type lemma
`Work.RadialSpace.exists_contDiff_comp_sq` (an even smooth profile is a smooth function of `t ^ 2`)
together with smoothness of `x ↦ ‖x‖ ^ 2`.
-/

namespace Work.CKFinal

open scoped ContDiff

/-- `Submission.ckmrv_fourier_interpolation_of_satisfiesThm31` with `C^∞` (not analytic)
radial profiles: in this Mathlib `ContDiff ℝ ⊤` is `ContDiff ℝ ω`, which is stronger than
CKMRV Thm 3.1 needs and than the construction provides. -/
theorem ckmrv_of_satisfiesThm31_smooth
    (F8 Ft8 : UpperHalfPlane → ℝ → ℂ) (h8 : Work.Kernels.SatisfiesThm31 8 1 F8 Ft8)
    (hsF8 : ∀ τ : UpperHalfPlane, ContDiff ℝ ∞ (F8 τ))
    (hsFt8 : ∀ τ : UpperHalfPlane, ContDiff ℝ ∞ (Ft8 τ))
    (heF8 : ∀ τ : UpperHalfPlane, Function.Even (F8 τ))
    (heFt8 : ∀ τ : UpperHalfPlane, Function.Even (Ft8 τ))
    (F24 Ft24 : UpperHalfPlane → ℝ → ℂ) (h24 : Work.Kernels.SatisfiesThm31 24 2 F24 Ft24)
    (hsF24 : ∀ τ : UpperHalfPlane, ContDiff ℝ ∞ (F24 τ))
    (hsFt24 : ∀ τ : UpperHalfPlane, ContDiff ℝ ∞ (Ft24 τ))
    (heF24 : ∀ τ : UpperHalfPlane, Function.Even (F24 τ))
    (heFt24 : ∀ τ : UpperHalfPlane, Function.Even (Ft24 τ))
    (hdecF : Work.FE.TendsToZeroInStrip 24 1
      (fun τ x => if h : 0 < τ.im then F24 ⟨τ, h⟩ ‖x‖ else 0))
    (hdecFt : Work.FE.TendsToZeroInStrip 24 1
      (fun τ x => if h : 0 < τ.im then Ft24 ⟨τ, h⟩ ‖x‖ else 0)) :
    LeanEval.Analysis.CKMRVInterpolation.CKMRV 8 1 ∧
      LeanEval.Analysis.CKMRVInterpolation.CKMRV 24 2 := by
  -- `d = 8`: the interior adapter (the functional equations, from Theorem 3.1's hypotheses).
  obtain ⟨S8⟩ := Work.CKFinal.Shadow.Work.FunctionalEquations.Thm31Adapter (d := 8) (k₀ := 1)
    (by norm_num) F8 Ft8 h8 hsF8 hsFt8 heF8 heFt8
  -- `d = 24`: the same construction with the strip decay carried along.
  obtain ⟨S24, -, -, hdecS24, hdecT24⟩ :=
    Work.CKFinal.Shadow.Work.Interpolation.adapter_decay (d := 24) (k₀ := 2) (c := 1)
      (by norm_num) F24 Ft24 h24 hsF24 hsFt24 heF24 heFt24 hdecF hdecFt
  -- Steps 1-2 of CKMRV Section 3.1 for the two solutions ...
  haveI : NeZero 8 := ⟨by norm_num⟩
  haveI : NeZero 24 := ⟨by norm_num⟩
  obtain ⟨D8⟩ := Work.CKFinal.Shadow.Work.Section8P.interpolationBasis_eight_of_functionalEquations S8
  obtain ⟨basis24, hExp24⟩ :=
    Work.CKFinal.Shadow.Work.FE.expansionData_of_functionalEquations (n := 24) S24
  -- ... and the Section 8 normalisations (with the decay in dimension 24).
  obtain ⟨D24⟩ := Work.CKFinal.Shadow.Work.Section8P.interpolationBasis_twentyfour_of_functionalEquations
    S24 basis24 hExp24 hdecS24 hdecT24
  exact ⟨Submission.ckmrv_of_interpolationBasis 8 1 D8,
    Submission.ckmrv_of_interpolationBasis 24 2 D24⟩

end Work.CKFinal
