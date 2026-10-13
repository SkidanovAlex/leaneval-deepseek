/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsLimDbd` — why the requested form fails at `τ = T`, and two provable replacements

The requested lemma `Work.FTS.StrongEps.EpsLimDbd` (`Submission/Work/FTS/StrongEps/EpsLimDbd.lean`)
asks, from the component hypotheses of the limit package `EpsLimPkg` (in particular the equation
clause `heqT`, which is `EpsLimPkg.eqT` verbatim, i.e. a *within-`[0,T]`* derivative), for the
uniform `ℋ³`-bound on `gdot g τ` **for `0 < τ ≤ T`**.

For `τ < T` everything is fine: `Set.Icc 0 T ∈ 𝓝 τ`, so `HasDerivWithinAt` upgrades to an honest
`HasDerivAt` and the equation identifies `gdot g τ` with the limiting right-hand side
`dynLin α g τ + dynRHS α Φ g τ` on the open quadrant; `Work.FTS.StrongPersist.HkAddFin` plus the
level-three package `L3Data` (with the *pinned* bounds `Xn ≤ C₀α²`, `Xn6 ≤ B`) then give the
bound, and `HkMem_congr_Q0` / `HkSq_congr_open` transfer it from `dynLin + dynRHS` to `gdot g τ`.

**The statement is however false as written at `τ = T`**, and the reason is structural: the
hypothesis `heqT` is a *one-sided* (left) derivative at the right endpoint of `Icc 0 T`
(`Set.Icc 0 T ∉ 𝓝 T` for `T > 0`), and it does not determine `deriv (fun s => g z θ s) T`.
Concretely (`deriv_eq_of_hasDerivWithinAt_rightEndpoint` + `fderiv_zero_of_not_differentiableAt`):

`gdot g T = fun z θ => if DifferentiableAt ℝ (fun s => g z θ s) T then rhsFun α Φs E g T z θ else 0`
on the open quadrant,

and the differentiability set is *not* controlled by the hypotheses: they only involve the slices
`slice g τ` for `τ ∈ Set.Icc 0 T` and the within-`Set.Icc 0 T` derivatives, so they are invariant
under changing `g` on `{τ > T}`, whereas `gdot g T` is not — extending the family past `T` by
`g z θ T + (s - T)·(rhsFun α Φs E g T z θ + c z θ)` makes the honest derivative at `T` exist
exactly on `{c = 0}`, whose indicator can be taken non-measurable; then the `i = 0` slot
`(gdot g T · w / sin(2θ)^{η/2})²` of `HkIntegrand α 3 (gdot g T)` is not a.e. strongly
measurable, so `HkMem α 3 (gdot g T)` fails.  Hence the `τ = T` instance of the requested
conclusion is not implied by its hypotheses.

Two repairs, both proved below:

* `EpsLimDbd_of_Ici` — keep the conclusion `0 < τ → τ ≤ T` but ask for the derivative within the
  **half-line** `Set.Ici 0` (the convention of `Work.FTS.Galerkin.IsDynEqOn`); then every `τ > 0`
  is an *interior* point of that set and the derivative is honest;
* `EpsLimDbd_of_Icc` — keep the given equation hypothesis `heqT` (within `Set.Icc 0 T`) but
  conclude only for `0 < τ < T`.  This is the form actually consumed by
  `Submission/Work/FTS/StrongEps/Assembly.lean`, which picks for every `τ > 0` a piece with
  `τ < Tn` *strictly* (`lt_Tn_pidx`), so no endpoint is ever evaluated.

Both are corollaries of the core estimate `EpsLimDbd_aux`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.LimGdot
import Submission.Work.FTS.StrongPersist.Dbd
import Submission.Work.FTS.StrongPersist.L3DataFinal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option linter.unusedVariables false

/-! ## The mechanism at the right endpoint -/

/-- **The right endpoint of `Set.Icc 0 T`.**  At `T` a `HasDerivWithinAt`-hypothesis on
`Set.Icc 0 T` is a *left* derivative, and it agrees with the honest `deriv` at `T` exactly when the
function is honestly differentiable there.  Together with `fderiv_zero_of_not_differentiableAt`
(which gives `deriv f T = 0` in the other case) this says that from `HasDerivWithinAt f a
(Set.Icc 0 T) T` alone one can deduce nothing about `deriv f T`.

This is the reason why a hypothesis of the form `HasDerivWithinAt f a (Set.Icc 0 T) τ` cannot be
used at `τ = T`: the set is not a neighbourhood of its right endpoint. -/
theorem deriv_eq_of_hasDerivWithinAt_rightEndpoint {f : ℝ → ℝ} {a T : ℝ} (hT : 0 < T)
    (h : HasDerivWithinAt f a (Set.Icc 0 T) T) (hd : DifferentiableAt ℝ f T) :
    deriv f T = a := by
  have h2 : UniqueDiffWithinAt ℝ (Set.Icc 0 T) T := by
    refine uniqueDiffWithinAt_convex (convex_Icc 0 T) ?_ ?_
    · rw [interior_Icc]; exact ⟨T / 2, by constructor <;> linarith⟩
    · exact subset_closure ⟨le_of_lt hT, le_rfl⟩
  have h1 : HasDerivAt f (deriv f T) T := hd.hasDerivAt
  have e1 := h1.hasDerivWithinAt.derivWithin h2
  have e2 := h.derivWithin h2
  rw [← e1, e2]

/-! ## The core estimate

The whole analytic content of `EpsLimDbd` is here: it needs the equation *only* through the
identification `gdot g τ = rhsFun α Φs E g τ` on the open quadrant, at the fake times `τ` for
which the conclusion is asserted. -/

theorem EpsLimDbd_aux {α₂ Ce C3 Cpow C₀ K Cs T B : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {s : Set ℝ}
    (hL3 : Work.FTS.StrongPersist.L3Data α₂ Ce C3 Cpow) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 α₂)
    (hs : ∀ τ ∈ s, τ ∈ Set.Icc 0 T)
    (hb4 : ∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice g τ) ≤ C₀ * α ^ 2)
    (hb6 : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g τ) ≤ B)
    (hadm : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongPersist.H6Adm α (Work.FTS.Galerkin.slice g τ))
    (hell : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs
      (Work.FTS.Galerkin.slice g τ)
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
    (hlinc : ∀ τ ∈ Set.Icc 0 T, ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.StrongPersist.linPart α (Work.FTS.Galerkin.slice g τ)))
      Work.FTS.EllipticEst.Q0)
    (hrhsc : ∀ τ ∈ Set.Icc 0 T, ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs E g) g τ))
      Work.FTS.EllipticEst.Q0)
    (hμ : ∀ τ ∈ Set.Icc 0 T,
      |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1 / 2)
    (hlam : ∀ τ ∈ Set.Icc 0 T,
      |Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1)
    (hgd : ∀ τ ∈ s, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.FTS.Galerkin.gdot g τ z θ = rhsFun α Φs E g τ z θ) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ τ ∈ s,
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot g τ) ∧
        Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot g τ) ≤ Cd := by
  classical
  have hαpos : 0 < α := hα.1
  have hC3 : 0 < C3 := hL3.pos.1
  set Cd₀ : ℝ := Real.sqrt 2 * (C3 * (1 + C₀ * α ^ 2) ^ 4
      + C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + C₀ * α ^ 2) ^ 4 * (1 + B) ^ 2)
    with hCd₀
  refine ⟨|Cd₀| + 1, by have := abs_nonneg Cd₀; linarith, ?_⟩
  intro τ hτs
  have hτI : τ ∈ Set.Icc 0 T := hs τ hτs
  set f : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice g τ with hf
  set Φ : Work.FTS.Galerkin.Fam := Work.FTS.Nonlin.PsiCan Φs E g with hΦ
  obtain ⟨hmem1, hbnd1⟩ := hL3.lin α hα f (hadm τ hτI)
  obtain ⟨hmem2raw, hbnd2raw⟩ := hL3.rhs α hα E Φs (Work.FTS.Galerkin.slice Φ τ) f Cs
    (Work.FTS.Galerkin.muDyn α Φ g τ) (Work.FTS.Galerkin.lamDyn α Φ g τ) (C₀ * α ^ 2)
    (hell τ hτI) (hadm τ hτI) (hb4 τ hτI) (hμ τ hτI) (hlam τ hτI)
  set u : Work.FTS.Galerkin.Fn := Work.FTS.StrongPersist.linPart α f with hu
  set v : Work.FTS.Galerkin.Fn := Work.FTS.StrongPersist.rhsOf α
    (Work.FTS.Galerkin.muDyn α Φ g τ) (Work.FTS.Galerkin.lamDyn α Φ g τ)
    (Work.Construction.Ftau α g τ) (Work.FTS.Galerkin.slice Φ τ) f with hv
  have hmem2 : Work.Spaces.HkMem α 3 v := hmem2raw
  have hbnd2 : Work.Spaces.HkNorm α 3 v
      ≤ C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + C₀ * α ^ 2) ^ 4
        * (1 + Work.FTS.StrongGlobal.Xn6 α f) ^ 2 := hbnd2raw
  have hsum : Work.FTS.Galerkin.dynLin α g τ + Work.FTS.Galerkin.dynRHS α Φ g τ
      = fun z θ => u z θ + v z θ := by
    funext z θ
    simp only [Pi.add_apply, hu, hv, Work.FTS.StrongPersist.dynLin_eq_linPart,
      Work.FTS.StrongPersist.dynRHS_eq_rhsOf, hf]
  have hlreg : ContDiffOn ℝ 3 (Function.uncurry u) Work.FTS.EllipticEst.Q0 := by
    rw [hu, hf]; exact hlinc τ hτI
  have hregr : ContDiffOn ℝ 3 (Function.uncurry v) Work.FTS.EllipticEst.Q0 := by
    rw [hv, hf, ← Work.FTS.StrongPersist.dynRHS_eq_rhsOf α Φ g τ]
    exact hrhsc τ hτI
  have hadd := Work.FTS.StrongPersist.HkAddFin (α := α) (k := 3) hlreg hregr hmem1 hmem2
  -- the equation identifies `gdot g τ` with the sum on the open quadrant
  have hgd' : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.FTS.Galerkin.gdot g τ z θ = (fun z θ => u z θ + v z θ) z θ := by
    intro z θ hz
    have h2 : rhsFun α Φs E g τ z θ
        = Work.FTS.Galerkin.dynLin α g τ z θ + Work.FTS.Galerkin.dynRHS α Φ g τ z θ := rfl
    rw [hgd τ hτs z θ hz, h2]
    exact congrFun (congrFun hsum z) θ
  have hbnd1' : Work.Spaces.HkNorm α 3 u ≤ C3 * (1 + C₀ * α ^ 2) ^ 4 := by
    rw [hu]
    have hXn : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
    have hle : Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 := hb4 τ hτI
    have h1 : 1 + Work.FTS.Nonlin.Xn α f ≤ 1 + C₀ * α ^ 2 := by linarith
    have h2 : (0 : ℝ) ≤ 1 + Work.FTS.Nonlin.Xn α f := by linarith
    exact le_trans hbnd1 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 4) hC3.le)
  have hbnd2' : Work.Spaces.HkNorm α 3 v
      ≤ C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + C₀ * α ^ 2) ^ 4 * (1 + B) ^ 2 := by
    have hXn6 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 f
    have hle6 : Work.FTS.StrongGlobal.Xn6 α f ≤ B := hb6 τ hτI
    have h1 : 1 + Work.FTS.StrongGlobal.Xn6 α f ≤ 1 + B := by linarith
    have h2 : (0 : ℝ) ≤ 1 + Work.FTS.StrongGlobal.Xn6 α f := by linarith
    have hnn : (0 : ℝ) ≤ C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow)
        * (1 + C₀ * α ^ 2) ^ 4 := by
      have ha : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
      have hb : (0 : ℝ) ≤ α ^ (-Cpow) := Real.rpow_nonneg hαpos.le _
      have hc : (0 : ℝ) ≤ (1 + C₀ * α ^ 2) ^ 4 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg hC3.le ha) hb) hc
    exact le_trans hbnd2 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2 h1 2) hnn)
  refine ⟨?_, ?_⟩
  · refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 (α := α) (k := 3) hadd.1 ?_
    intro z hz θ hθ
    exact (hgd' z θ ⟨hz, hθ⟩).symm
  · have hsq : Work.Spaces.HkSq α 3 (Work.FTS.Galerkin.gdot g τ)
        = Work.Spaces.HkSq α 3 (fun z θ => u z θ + v z θ) :=
      Work.FTS.EllipticEst.HkSq_congr_open α 3
        (fun z θ hz hθ hlt => hgd' z θ ⟨hz, hθ, hlt⟩)
    have hnorm : Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot g τ)
        = Work.Spaces.HkNorm α 3 (fun z θ => u z θ + v z θ) := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsq]
    rw [hnorm]
    calc Work.Spaces.HkNorm α 3 (fun z θ => u z θ + v z θ)
        ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 3 u + Work.Spaces.HkNorm α 3 v) := hadd.2
      _ = Real.sqrt 2 * (Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.linPart α f)
            + Work.Spaces.HkNorm α 3 v) := by rw [hu]
      _ ≤ Real.sqrt 2 * (C3 * (1 + C₀ * α ^ 2) ^ 4
            + C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + C₀ * α ^ 2) ^ 4
              * (1 + B) ^ 2) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hbnd1' hbnd2') (Real.sqrt_nonneg 2)
      _ ≤ |Cd₀| + 1 := by
          rw [hCd₀]
          exact le_trans (le_abs_self _) (le_add_of_nonneg_right zero_le_one)

/-! ## Replacement 1 — honest derivative at every `τ > 0` (hypothesis within `Set.Ici 0`) -/

theorem EpsLimDbd_of_Ici {α₂ Ce C3 Cpow C₀ K Cs T B : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hL3 : Work.FTS.StrongPersist.L3Data α₂ Ce C3 Cpow) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 α₂) (hT : 0 ≤ T)
    (hb4 : ∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice g τ) ≤ C₀ * α ^ 2)
    (hb6 : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g τ) ≤ B)
    (heqT : ∀ τ ∈ Set.Icc 0 T, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivWithinAt (fun s => g z θ s) (Work.FTS.StrongEps.rhsFun α Φs E g τ z θ)
        (Set.Ici 0) τ)
    (hadm : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongPersist.H6Adm α (Work.FTS.Galerkin.slice g τ))
    (hell : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs
      (Work.FTS.Galerkin.slice g τ)
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
    (hlinc : ∀ τ ∈ Set.Icc 0 T, ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.StrongPersist.linPart α (Work.FTS.Galerkin.slice g τ)))
      Work.FTS.EllipticEst.Q0)
    (hrhsc : ∀ τ ∈ Set.Icc 0 T, ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs E g) g τ))
      Work.FTS.EllipticEst.Q0)
    (hμ : ∀ τ ∈ Set.Icc 0 T,
      |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1 / 2)
    (hlam : ∀ τ ∈ Set.Icc 0 T,
      |Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ τ, 0 < τ → τ ≤ T →
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot g τ) ∧
        Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot g τ) ≤ Cd := by
  obtain ⟨Cd, hCd, hb⟩ := EpsLimDbd_aux (s := Set.Ioc 0 T) (K := K) (g₀ := g₀) hL3 hα
    (fun _ hτ => ⟨le_of_lt hτ.1, hτ.2⟩) hb4 hb6 hadm hell hlinc hrhsc hμ hlam
    (fun τ hτ z θ hz => by
      have hnh : Set.Ici (0 : ℝ) ∈ 𝓝 τ := Ici_mem_nhds hτ.1
      have hd := (heqT τ ⟨le_of_lt hτ.1, hτ.2⟩ z θ hz).hasDerivAt hnh
      exact hd.deriv)
  exact ⟨Cd, hCd, fun τ h1 h2 => hb τ ⟨h1, h2⟩⟩

/-! ## Replacement 2 — the given hypothesis, conclusion for `τ < T` -/

theorem EpsLimDbd_of_Icc {α₂ Ce C3 Cpow C₀ K Cs T B : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hL3 : Work.FTS.StrongPersist.L3Data α₂ Ce C3 Cpow) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 α₂) (hT : 0 ≤ T)
    (hb4 : ∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice g τ) ≤ C₀ * α ^ 2)
    (hb6 : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g τ) ≤ B)
    (heqT : ∀ τ ∈ Set.Icc 0 T, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivWithinAt (fun s => g z θ s) (Work.FTS.StrongEps.rhsFun α Φs E g τ z θ)
        (Set.Icc 0 T) τ)
    (hadm : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongPersist.H6Adm α (Work.FTS.Galerkin.slice g τ))
    (hell : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs
      (Work.FTS.Galerkin.slice g τ)
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
    (hlinc : ∀ τ ∈ Set.Icc 0 T, ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.StrongPersist.linPart α (Work.FTS.Galerkin.slice g τ)))
      Work.FTS.EllipticEst.Q0)
    (hrhsc : ∀ τ ∈ Set.Icc 0 T, ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs E g) g τ))
      Work.FTS.EllipticEst.Q0)
    (hμ : ∀ τ ∈ Set.Icc 0 T,
      |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1 / 2)
    (hlam : ∀ τ ∈ Set.Icc 0 T,
      |Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ τ, 0 < τ → τ < T →
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot g τ) ∧
        Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot g τ) ≤ Cd := by
  obtain ⟨Cd, hCd, hb⟩ := EpsLimDbd_aux (s := Set.Ioo 0 T) (K := K) (g₀ := g₀) hL3 hα
    (fun _ hτ => ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩) hb4 hb6 hadm hell hlinc hrhsc hμ hlam
    (fun τ hτ z θ hz => by
      have hnh : Set.Icc (0 : ℝ) T ∈ 𝓝 τ := Icc_mem_nhds hτ.1 hτ.2
      have hd := (heqT τ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩ z θ hz).hasDerivAt hnh
      exact hd.deriv)
  exact ⟨Cd, hCd, fun τ h1 h2 => hb τ ⟨h1, h2⟩⟩

/-! ## Replacement 3 — the given hypotheses plus the *missing* endpoint identity

This isolates exactly the ingredient that the requested statement is missing: the identification
`gdot g T = rhsFun α Φs E g T` on the open quadrant, at the single right endpoint `τ = T` (which
`heqT`'s within-`Set.Icc 0 T` derivative fails to provide — see
`deriv_eq_of_hasDerivWithinAt_rightEndpoint`).  If the caller obtains that identity from the
construction of the limit family (e.g. as the `τ → T⁻` limit of the equation along the pieces, or
from honest differentiability at `T`), the requested conclusion — including `τ = T` — follows. -/

theorem EpsLimDbd_of_endpoint {α₂ Ce C3 Cpow C₀ K Cs T B : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hL3 : Work.FTS.StrongPersist.L3Data α₂ Ce C3 Cpow) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 α₂) (hT : 0 ≤ T)
    (hb4 : ∀ τ ∈ Set.Icc 0 T, Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice g τ) ≤ C₀ * α ^ 2)
    (hb6 : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongGlobal.Xn6 α (Work.FTS.Galerkin.slice g τ) ≤ B)
    (heqT : ∀ τ ∈ Set.Icc 0 T, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivWithinAt (fun s => g z θ s) (Work.FTS.StrongEps.rhsFun α Φs E g τ z θ)
        (Set.Icc 0 T) τ)
    (hadm : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongPersist.H6Adm α (Work.FTS.Galerkin.slice g τ))
    (hell : ∀ τ ∈ Set.Icc 0 T, Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs
      (Work.FTS.Galerkin.slice g τ)
      (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ))
    (hlinc : ∀ τ ∈ Set.Icc 0 T, ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.StrongPersist.linPart α (Work.FTS.Galerkin.slice g τ)))
      Work.FTS.EllipticEst.Q0)
    (hrhsc : ∀ τ ∈ Set.Icc 0 T, ContDiffOn ℝ 3
      (Function.uncurry (Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs E g) g τ))
      Work.FTS.EllipticEst.Q0)
    (hμ : ∀ τ ∈ Set.Icc 0 T,
      |Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1 / 2)
    (hlam : ∀ τ ∈ Set.Icc 0 T,
      |Work.FTS.Galerkin.lamDyn α (Work.FTS.Nonlin.PsiCan Φs E g) g τ| ≤ 1)
    (hend : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.FTS.Galerkin.gdot g T z θ = rhsFun α Φs E g T z θ) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ τ, 0 < τ → τ ≤ T →
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot g τ) ∧
        Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot g τ) ≤ Cd := by
  obtain ⟨Cd, hCd, hb⟩ := EpsLimDbd_aux (s := Set.Ioc 0 T) (K := K) (g₀ := g₀) hL3 hα
    (fun _ hτ => ⟨le_of_lt hτ.1, hτ.2⟩) hb4 hb6 hadm hell hlinc hrhsc hμ hlam
    (fun τ hτ z θ hz => by
      rcases eq_or_lt_of_le hτ.2 with hEq | hlt
      · rw [hEq]; exact hend z θ hz
      · have hnh : Set.Icc (0 : ℝ) T ∈ 𝓝 τ := Icc_mem_nhds hτ.1 hlt
        exact ((heqT τ ⟨le_of_lt hτ.1, le_of_lt hlt⟩ z θ hz).hasDerivAt hnh).deriv)
  exact ⟨Cd, hCd, fun τ h1 h2 => hb τ ⟨h1, h2⟩⟩

end Work.FTS.StrongEps
