import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.E5Aux3.L12_slice_eq_zero_of_hkMem
import Submission.Work.FTS.StrongEps.E5L12Datum
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/rawSlice_L12_zero_proof.lean` — F6 (`rawSlice_L12_zero`)

**Verdict: the assigned statement is MIS-STATED (missing hypotheses), not provable as written.**
This file therefore carries (a) the verbatim assigned statement, left as `sorry` and documented,
and (b) the *repaired* statement `rawSlice_L12_zero_of_uniform`, which is proved (sorry-free) and
is the form the E4R3 session-22 report already prescribes as the repair.

## What the statement says, and what the conservation really needs

`IsEpsSolP` gives `∂_τ g = epsRHSP α ρ ε Φs E g τ` pointwise on the open quadrant, where

```
epsRHSP α ρ ε Φs E g τ = Pz (Jeps ρ ε (epsWP α ρ ε Φs E g τ))
```

(`PZeroScheme.epsRHSP_eq_Pz_Jeps_epsWP`, `rfl`).  The zero mode of the slice is conserved along the
scheme **iff** the zero mode of the right-hand side vanishes as a *number*:

```
∂_τ (L₁₂ (slice g τ)(0)) = L₁₂ (epsRHSP α ρ ε Φs E g τ)(0),
```

and `L₁₂ (Pz X)(0) = 0` is available only from the two integrability hypotheses of
`PZeroAux.Pz_l12` (`E5Aux2.L12_epsRHSP_zero`, `EpsSqTools.LinAux.L12_Pz_Jeps_zero`): the a.e.-in-`r`
integrability of the angular slice of `X = Jeps ρ ε (epsWP …)` on `Iθ`, and the integrability of its
`L₁₂`-density on `(0,∞)`.  Mathlib's Bochner integral is the junk value `0` off the integrable
functions, so the cancellation `L₁₂ (Pz X) 0 = L₁₂ X 0 − (L₁₂ X 0/pzNorm)·pzNorm` is genuinely
needed in the honest case, and those two integrabilities are *not* crude formalities: they are
statements about the size/regularity of the pre-mollified right-hand side `epsWP`.

The only *proved* route to the conclusion,
`StrongEps.E5Aux3.L12_slice_eq_zero_of_hkMem`, replaces them by two hypotheses on the scheme's
objects:

* `hRm` : `∀ τ ∈ Icc 0 T, HkMem α 4 (epsRHSP … τ) ∧ HkNorm α 4 (epsRHSP … τ) ≤ B` — the honest
  `ℋ⁴`-membership of the right-hand side together with a **uniform in τ** bound `B` (the DCT
  majorant of the Volterra/Fubini argument), and
* `hWm` : `∀ τ ∈ Icc 0 T, HkMem α 4 (Jeps ρ ε (epsWP … τ))` — the `ℋ⁴`-membership of the
  *mollified pre-mollified* right-hand side.

Everything else in that route *is* available here: `hc1 = hreg.1`, `hsm`/`hmem` from
`EpsDatumP.soft` + `OpenPkg.HkMem_mono_open`, and the datum slot `L₁₂ g₀ 0 = 0` from
`hd` by the proved `StrongEps.l12_zero_of_epsDatum`.

## Why `hRm`/`hWm` cannot be produced from the stated hypotheses

* `Φs` and `E` are *completely unconstrained* in the statement, and they enter the pre-mollified
  right-hand side through the arbitrary profile
  `slice (PsiCan Φs E (JfamP ρ ε g)) τ = fun z θ => Φs z θ + E (slice (JfamP ρ ε g) τ) z θ`
  (`Vocab.PsiCan`), which sits inside `gRHS` through `N α F Φ` and `mubar (N0 α F g) (N α F Φ)`
  (`Construction.gRHS`, `Construction.N`).  Hence the *size* of `epsWP` — and therefore of
  `epsRHSP` — is not determined by the hypotheses.
* The producers of `hRm`/`hWm` all need the ε-uniform operator packages plus uniform size data that
  the hypotheses do not carry: `EpsE4Thr.epsRHSP_hkMem_fam` and `EpsE4Thr.HkNorm_epsRHSP_le`
  (`hEll : ∀ u, ClassC α u → EllPkgGo α Ce u (E u) ∧ EllPkgK α 6 Ce u (E u)`,
  `hstar : StarPkgo2 α Cs Φs`, `hml : MuLamOK α C₀ Φs E`, and a uniform `HkNorm α 6 (slice g s) ≤ B`),
  `StrongEps.epsWP_hkMem4_bnd_unif` (same packages plus the class-`C`/ball/`ℋ⁶`-ball clauses of the
  projected family).
* `EpsRegP` supplies those clauses only *per slice*, never uniformly: per-slice `SmoothOpen`/`HkMem α 6`
  plus joint `C¹` do not bound `τ ↦ HkNorm α 6 (slice g τ)` (the `ℋ⁶`-norms may blow up while the
  values converge).  This is exactly the gap recorded in the area's own report to the lead —
  `Submission/Work/FTS/StrongEps/REPORT_LEAD_apriori4_decisions.md`, Decision (1) §Finding: the
  uniform `ℋ⁶` bound "is *not* a consequence of `IsEpsSolP + EpsRegP`" — and it is the same one
  that forced the sibling F6 docstring (`E4R3/Apriori4Leaves/RawSliceL12Zero.lean`) to say
  "if it cannot be produced from `EpsRegP`, return *missing hypothesis*".
* Independent confirmation: both reviewers of this exact path (recorded in `.fm3_reviews.json`,
  key `FTS/StrongEps/E4R3/Apriori4Proofs/rawSlice_L12_zero_proof`) concluded "probably wrong as
  stated", naming precisely these two groups; the lead's report prescribes the same repair
  ("add the uniform `epsRHSP`/`ℋ⁴` bound to its hypotheses").

## The repair

`rawSlice_L12_zero_of_uniform` below is the assigned statement *plus* `hRm`/`hWm`, and it is proved
by the proved `E5Aux3.L12_slice_eq_zero_of_hkMem`.  In the consumer `rawE6_ineq`'s setting the
operator packages are available from `E4Data` + `StarPkg6`, so only the uniform sizes must be
carried (the same information the `ℋ⁶`-half propagates; cf. the interval-local treatment of R2).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The repaired F6** (`rawSlice_L12_zero` with the two missing regularity hypotheses):
`L₁₂ (slice g τ)(0) = 0` along a regular `P₀`-solution, given

* `hRm` — `ℋ⁴`-membership of the scheme's right-hand side together with a uniform-in-`τ` bound
  (the dominated-convergence majorant of the Volterra/Fubini argument), and
* `hWm` — `ℋ⁴`-membership of the mollified pre-mollified right-hand side `Jeps ρ ε (epsWP … τ)`.

Every other input of the proved route is read off the assigned hypotheses: `hreg.1` is the joint
`C¹`-regularity, `EpsDatumP.soft` + `OpenPkg.HkMem_mono_open` give the per-slice
`SmoothOpen`/`HkMem α 4`, and `hd` gives `L₁₂ g₀ 0 = 0` through `StrongEps.l12_zero_of_epsDatum`. -/
theorem rawSlice_L12_zero_of_uniform {α ε T B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {g₀ : Fn} {g : Fam} (hρ : IsSmoothKernel ρ)
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hε : 0 < ε) (hT : 0 < T)
    (hd : ∀ ε' : ℝ, 0 < ε' → EpsDatum α ρ ε' g₀)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g) (hreg : EpsRegP α ρ ε T g)
    (hRm : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (epsRHSP α ρ ε Φs E g τ) ∧
      Work.Spaces.HkNorm α 4 (epsRHSP α ρ ε Φs E g τ) ≤ B)
    (hWm : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (Jeps ρ ε (epsWP α ρ ε Φs E g τ))) :
    ∀ τ ∈ Set.Icc 0 T, Work.Construction.L12 (slice g τ) 0 = 0 := by
  have h0 : Work.Construction.L12 g₀ 0 = 0 := l12_zero_of_epsDatum hα hρ hd
  refine Work.FTS.StrongEps.L12_slice_eq_zero_of_hkMem (α := α) (ε := ε) (T := T) (B := B)
    (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀) (g := g) hα hρ hε hT hsol hreg.1 ?_ ?_ hRm hWm h0
  · intro τ hτ
    exact (EpsDatumP.soft (hreg.2 τ hτ)).1
  · intro τ hτ
    exact Work.FTS.OpenPkg.HkMem_mono_open (EpsDatumP.soft (hreg.2 τ hτ)).1 4 (by norm_num)
      (EpsDatumP.soft (hreg.2 τ hτ)).2

/-- **The assigned statement (F6, `rawSlice_L12_zero`).**  Left unproved: as documented in the
module header it is mis-stated — it omits the uniform `ℋ⁴`-data `hRm`/`hWm` on the scheme's
right-hand side that the only available route (`E5Aux3.L12_slice_eq_zero_of_hkMem`, via
`PZeroAux.Pz_l12`/`E5Aux2.L12_epsRHSP_zero`) needs, and `EpsRegP`+`IsEpsSolP`+`hd` do not imply
them.  The repaired form is `rawSlice_L12_zero_of_uniform` above. -/
theorem rawSlice_L12_zero_proof {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hT : 0 < T)
    (hd : ∀ ε' : ℝ, 0 < ε' → Work.FTS.StrongEps.EpsDatum α ρ ε' g₀)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hreg : Work.FTS.StrongEps.EpsRegP α ρ ε T g) :
    ∀ τ ∈ Set.Icc 0 T, Work.Construction.L12 (Work.FTS.Galerkin.slice g τ) 0 = 0 := by sorry

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
