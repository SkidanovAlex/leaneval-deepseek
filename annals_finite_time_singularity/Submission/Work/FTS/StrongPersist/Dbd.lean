/-
# `Work.FTS.StrongPersist.Dbd` — S6: the `ℋ³` bound on the right-hand side of the equation

Design `FTS_STRONG_ROUTE.md` §3, node **S6**:

> `dbd_of_eq`: `‖dynLin + dynRHS‖_{H³} ≤ C(Xn₄)`.

This is the estimate that produces the field `RegPkgMin.dbd` (a *uniform* `ℋ³` bound on
`∂_τ g`) from the equation `∂_τ g = -𝓛_Γ^T g + gRHS(…)`: the two summands are estimated
separately by the level-three operator package `L3Data`, and the sum is reassembled with the
triangle inequality of the weighted `ℋ³`-norm and the closure of `ℋ³` under addition at
*finite* smoothness (`HkAddFin`; only `C³` on the open quadrant is needed):

`|a + b|_{ℋ³} ≤ √2 (|a|_{ℋ³} + |b|_{ℋ³}) ≤ 2√2 C3 (1+Xn₄)⁴ · (1 + α^{-Cpow}) · (1+|Ce|+|Cs|)⁴`.

The constant depends on the solution only through its `ℋ⁴` norm and on the *elliptic*
constants `Ce` (perturbation) and `Cs` (star) — which are data of the problem, not of the
solution, and which the caller fixes once and for all.  The α-power is unavoidable: `gRHS`
contains the term `(1/α)L₁₂(f)·f`, so the estimate cannot be α-independent as `α → 0⁺` (see
`L3Data`'s documentation in `Clauses.lean`).

The elliptic side enters through the *split* context `Ell6Ctx` (the star solution plus the
linear perturbation), which is the satisfiable form of the elliptic a-priori data; the earlier
single-structure `Ell6Data` was vacuous.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Defs
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.HkAddFin
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist

open Work.FTS.Galerkin (Fn Fam slice gdot dynLin dynRHS)
open Work.FTS.Nonlin (Xn)
open Work.FTS.VocabO (HQo)
open Work.Spaces (HkMem HkSq HkNorm)

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

/-- The explicit constant of S6 as a function of the `ℋ⁴` norm:
`C(x) = 2√2 C3 (1+x)⁴`. -/
def dbdConst (C3 : ℝ) : ℝ → ℝ := fun x => 2 * Real.sqrt 2 * C3 * (1 + x) ^ 4

theorem dbdConst_nonneg {C3 : ℝ} (hC3 : 0 < C3) : ∀ x : ℝ, 0 ≤ x → 0 ≤ dbdConst C3 x := by
  intro x hx
  have h1 : (0 : ℝ) ≤ 1 + x := by linarith
  have h2 : (0 : ℝ) ≤ (1 + x) ^ 4 := by positivity
  have h3 : (0 : ℝ) ≤ 2 * Real.sqrt 2 * C3 := by positivity
  exact mul_nonneg h3 h2

/-- The elliptic factor of the S6 constant: `1 + (1+|Ce|+|Cs|)⁴`.  (One is added so that the
factor is never small: with `Ce, Cs` free there is no lower bound on `(1+|Ce|+|Cs|)⁴`.) -/
def dbdEll (Ce Cs : ℝ) : ℝ := 1 + (1 + |Ce| + |Cs|) ^ 4

theorem dbdEll_nonneg (Ce Cs : ℝ) : 0 ≤ dbdEll Ce Cs := by
  have h : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  rw [dbdEll]; linarith

theorem one_le_dbdEll (Ce Cs : ℝ) : 1 ≤ dbdEll Ce Cs := by
  have h : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
  rw [dbdEll]; linarith

/-- **S6 (`dbd_of_eq`).**  There is a constant function `Cd` of *two* variables — namely
`(x, y) ↦ dbdConst C3 x · (1 + α^{-Cpow}) · dbdEll Ce Cs · (1+y)²` — such that for every
`α ∈ (0, α₂]` and every `Cs`, every fake time `τ ≥ 0` and every profile `g(τ)` in the honest
level-six coercivity class whose elliptic side satisfies the *split* a-priori data `Ell6Ctx` and
whose equation sides are only `C³` on the open quadrant, the two sides of the dynamic equation
satisfy

`|dynLin α g τ + dynRHS α Φ g τ|_{ℋ³} ≤ Cd (Xn₄(g(τ))) (Xn₆(g(τ)))`,

together with the `ℋ³`-membership of that sum.  The modulation constants enter only through
the a-priori bounds `|μ̄| ≤ 1/2`, `|λ| ≤ 1` — exactly the smallness the continuation argument
supplies.

**Why two variables.**  The nonlinear side is estimated by the clause `L3Data.rhs`, whose
hypothesis (`EllPkgK α 6`) prices the transported residual by `Ce · |f|_{ℋ⁶}`; there is *no*
relation between `Xn₆` and `Xn₄` in the class `H6Adm`, so the `ℋ³`-bound on `gRHS` genuinely
carries a factor `(1 + Xn₆)` — see the documentation of `L3Data.rhs` in `Clauses.lean`.  This is
still exactly what the design's `‖dynLin + dynRHS‖_{H³} ≤ C(Xn₄)` asks for *after composition
with S2*: `persist_H6` bounds `Xn₆ ≤ F(Xn₄)` (a function of `Xn₄`, the horizon and the level-six
constants only), so substituting that bound into `Cd` gives a constant depending on `Xn₄` alone.

`Cd` is quantified *after* `Cs`: the elliptic star constant is part of the elliptic a-priori
data supplied by the caller, and the estimate is of the coarse polynomial form
`(1+|Ce|+|Cs|)⁴ (1+Xn₄)⁴ (1+Xn₆)² α^{-Cpow}`. -/
theorem dbd_of_eq {α₂ Ce C3 Cpow : ℝ} (hL3 : L3Data α₂ Ce C3 Cpow) :
    ∀ α ∈ Set.Ioc 0 α₂, ∀ Cs : ℝ, ∃ Cd : ℝ → ℝ → ℝ,
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Cd x y) ∧
      ∀ (E : Fn → Fn) (Φs : Fn) (g Φ : Fam) (τ : ℝ), 0 ≤ τ →
        H6Adm α (slice g τ) → Ell6Ctx α Ce Cs E Φs (slice g τ) (slice Φ τ) →
        ContDiffOn ℝ 3 (Function.uncurry (linPart α (slice g τ))) Work.FTS.EllipticEst.Q0 →
        ContDiffOn ℝ 3 (Function.uncurry (dynRHS α Φ g τ)) Work.FTS.EllipticEst.Q0 →
        |Galerkin.muDyn α Φ g τ| ≤ 1 / 2 → |Galerkin.lamDyn α Φ g τ| ≤ 1 →
        HkMem α 3 (dynLin α g τ + dynRHS α Φ g τ) ∧
        HkNorm α 3 (dynLin α g τ + dynRHS α Φ g τ)
          ≤ Cd (Xn α (slice g τ)) (Xn6 α (slice g τ)) := by
  intro α hα Cs
  have hαpos : 0 < α := hα.1
  have hA : (0 : ℝ) ≤ 1 + α ^ (-Cpow) := by
    have := Real.rpow_nonneg hαpos.le (-Cpow); linarith
  refine ⟨fun x y => dbdConst C3 x * (1 + α ^ (-Cpow)) * dbdEll Ce Cs * (1 + y) ^ 2, ?_, ?_⟩
  · intro x y hx hy
    have hy2 : (0 : ℝ) ≤ (1 + y) ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (dbdConst_nonneg hL3.pos.1 x hx) hA)
      (dbdEll_nonneg Ce Cs)) hy2
  intro E Φs g Φ τ hτ hreg hell hsl hsrhs hμ hlam
  set f : Fn := slice g τ with hf
  obtain ⟨hlinmem, hlinb⟩ := hL3.lin α hα f hreg
  obtain ⟨hrhsmem, hrhsb⟩ := hL3.rhs α hα E Φs (slice Φ τ) f Cs
    (Galerkin.muDyn α Φ g τ) (Galerkin.lamDyn α Φ g τ) (Xn α f) hell hreg le_rfl hμ hlam
  -- the source `F_* + f` is the fake-time source `Ftau α g τ` (definitionally)
  have hrhs' : HkMem α 3 (rhsOf α (Galerkin.muDyn α Φ g τ) (Galerkin.lamDyn α Φ g τ)
      (Work.Construction.Ftau α g τ) (slice Φ τ) f) := hrhsmem
  have hrhsb' : HkNorm α 3 (rhsOf α (Galerkin.muDyn α Φ g τ) (Galerkin.lamDyn α Φ g τ)
      (Work.Construction.Ftau α g τ) (slice Φ τ) f)
        ≤ C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + Xn α f) ^ 4
            * (1 + Xn6 α f) ^ 2 := hrhsb
  -- the two summands, as *functions*
  set u : Fn := linPart α f with hu
  set v : Fn := rhsOf α (Galerkin.muDyn α Φ g τ) (Galerkin.lamDyn α Φ g τ)
    (Work.Construction.Ftau α g τ) (slice Φ τ) f with hv
  have hsum : dynLin α g τ + dynRHS α Φ g τ = fun z θ => u z θ + v z θ := by
    funext z θ
    simp only [Pi.add_apply, hu, hv, dynLin_eq_linPart, dynRHS_eq_rhsOf, hf]
  -- the two slots are `C³` on the open quadrant, so `ℋ³` closes under the sum at *finite* order
  have hlreg : ContDiffOn ℝ 3 (Function.uncurry u) Work.FTS.EllipticEst.Q0 := by
    rw [hu, hf]; exact hsl
  have hregr : ContDiffOn ℝ 3 (Function.uncurry v) Work.FTS.EllipticEst.Q0 := by
    rw [hv, hf, ← dynRHS_eq_rhsOf]; exact hsrhs
  have hadd := HkAddFin (α := α) (k := 3) hlreg hregr hlinmem hrhs'
  rw [hsum]
  constructor
  · exact hadd.1
  · have htri : HkNorm α 3 (fun z θ => u z θ + v z θ)
        ≤ Real.sqrt 2 * (HkNorm α 3 u + HkNorm α 3 v) := hadd.2
    have hlinb' : HkNorm α 3 u ≤ C3 * (1 + Xn α f) ^ 4 := hlinb
    have hvb : HkNorm α 3 v ≤ C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + Xn α f) ^ 4
        * (1 + Xn6 α f) ^ 2 := hrhsb'
    calc HkNorm α 3 (fun z θ => u z θ + v z θ)
        ≤ Real.sqrt 2 * (HkNorm α 3 u + HkNorm α 3 v) := htri
      _ ≤ Real.sqrt 2 * (C3 * (1 + Xn α f) ^ 4
            + C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + Xn α f) ^ 4
              * (1 + Xn6 α f) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
            linarith [hlinb', hvb]
      _ ≤ dbdConst C3 (Xn α f) * (1 + α ^ (-Cpow)) * dbdEll Ce Cs * (1 + Xn6 α f) ^ 2 := by
            rw [dbdConst, dbdEll]
            have hX : (0 : ℝ) ≤ (1 + Xn α f) ^ 4 := by positivity
            have hY : (0 : ℝ) ≤ (1 + Xn6 α f) ^ 2 := by positivity
            have hY1 : (1 : ℝ) ≤ (1 + Xn6 α f) ^ 2 := by
              have h1 : (1 : ℝ) ≤ 1 + Xn6 α f := by
                have := Work.Spaces.HkNorm_nonneg α 6 f
                linarith
              nlinarith [h1]
            have hC3 : (0 : ℝ) ≤ C3 := hL3.pos.1.le
            have hK : (0 : ℝ) ≤ (1 + |Ce| + |Cs|) ^ 4 := by positivity
            have hE4K : (1 + |Ce| + |Cs|) ^ 4 ≤ 1 + (1 + |Ce| + |Cs|) ^ 4 := by linarith
            have hAA : (0 : ℝ) ≤ α ^ (-Cpow) := Real.rpow_nonneg hαpos.le _
            have hfac : 1 + (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + Xn6 α f) ^ 2
                ≤ 2 * ((1 + α ^ (-Cpow)) * (1 + (1 + |Ce| + |Cs|) ^ 4))
                    * (1 + Xn6 α f) ^ 2 := by
              nlinarith [hAA, hK, hY, hY1, hE4K, mul_nonneg hAA hK,
                mul_nonneg (mul_nonneg hAA hK) hY]
            have hnonneg : (0 : ℝ) ≤ Real.sqrt 2 * C3 * (1 + Xn α f) ^ 4 :=
              mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hC3) hX
            calc Real.sqrt 2 * (C3 * (1 + Xn α f) ^ 4
                  + C3 * (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + Xn α f) ^ 4
                    * (1 + Xn6 α f) ^ 2)
                = Real.sqrt 2 * C3 * (1 + Xn α f) ^ 4
                    * (1 + (1 + |Ce| + |Cs|) ^ 4 * α ^ (-Cpow) * (1 + Xn6 α f) ^ 2) := by ring
              _ ≤ Real.sqrt 2 * C3 * (1 + Xn α f) ^ 4
                    * (2 * ((1 + α ^ (-Cpow)) * (1 + (1 + |Ce| + |Cs|) ^ 4))
                        * (1 + Xn6 α f) ^ 2) :=
                    mul_le_mul_of_nonneg_left hfac hnonneg
              _ = 2 * Real.sqrt 2 * C3 * (1 + Xn α f) ^ 4 * (1 + α ^ (-Cpow))
                    * (1 + (1 + |Ce| + |Cs|) ^ 4) * (1 + Xn6 α f) ^ 2 := by ring

/-- **S6 in the form consumed by `RegPkgMin.dbd`.**  The `ℋ³` bound is transferred from
`dynLin + dynRHS` to the fake-time derivative `gdot g τ` itself: on the open quadrant the
equation identifies the two, and the weighted `ℋ³`-norm only sees the open quadrant
(`HkSq_congr_open`, `HkMem_congr_Q0`). -/
theorem dbd_of_eq_gdot {α₂ Ce C3 Cpow : ℝ} (hL3 : L3Data α₂ Ce C3 Cpow) :
    ∀ α ∈ Set.Ioc 0 α₂, ∀ Cs : ℝ, ∃ Cd : ℝ → ℝ → ℝ,
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ Cd x y) ∧
      ∀ (E : Fn → Fn) (Φs : Fn) (g Φ : Fam) (τ : ℝ), 0 ≤ τ →
        H6Adm α (slice g τ) → Ell6Ctx α Ce Cs E Φs (slice g τ) (slice Φ τ) →
        ContDiffOn ℝ 3 (Function.uncurry (linPart α (slice g τ))) Work.FTS.EllipticEst.Q0 →
        ContDiffOn ℝ 3 (Function.uncurry (dynRHS α Φ g τ)) Work.FTS.EllipticEst.Q0 →
        |Galerkin.muDyn α Φ g τ| ≤ 1 / 2 → |Galerkin.lamDyn α Φ g τ| ≤ 1 →
        (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
          gdot g τ z θ = dynLin α g τ z θ + dynRHS α Φ g τ z θ) →
        HkMem α 3 (gdot g τ) ∧
        HkNorm α 3 (gdot g τ) ≤ Cd (Xn α (slice g τ)) (Xn6 α (slice g τ)) := by
  intro α hα Cs
  obtain ⟨Cd, hCd, hmain⟩ := dbd_of_eq hL3 α hα Cs
  refine ⟨Cd, hCd, ?_⟩
  intro E Φs g Φ τ hτ hreg hell hsl hsrhs hμ hlam heq
  obtain ⟨hmem, hbnd⟩ := hmain E Φs g Φ τ hτ hreg hell hsl hsrhs hμ hlam
  have hcongr : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (dynLin α g τ + dynRHS α Φ g τ) z θ = gdot g τ z θ := by
    intro z θ hz hθ hlt
    exact (heq z θ ⟨hz, hθ, hlt⟩).symm
  refine ⟨?_, ?_⟩
  · refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 (α := α) (k := 3) hmem ?_
    intro z hz θ hθ
    exact hcongr z θ hz hθ.1 hθ.2
  · have hsq := Work.FTS.EllipticEst.HkSq_congr_open α 3 hcongr
    have hnorm : HkNorm α 3 (gdot g τ) = HkNorm α 3 (dynLin α g τ + dynRHS α Φ g τ) := by
      rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsq]
    rw [hnorm]
    exact hbnd

end Work.FTS.StrongPersist
