import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_RegExport.RXT0.DtauAux
import Submission.Work.FTS_RegExport.RXT.Sys.gdot_eq_profile
import Submission.Work.FTS_RegExport.RXT.Sys.JetCalc.RHSDefs
import Submission.Work.FTS.StrongEps.EpsSlotAux
import Submission.Work.FTS.StrongEps.mixed_sub_of_contDiffOn_four

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.DtauProto` — the assembly of RX-T0

The pieces, with the RX-T0 hypotheses in force:

* `dtau_jet_eq`: on the open quadrant, the mixed jets of `gdot g σ` and of the transport
  expression `RHS α Φs E g σ` agree for `σ ∈ (0,S]` (both are the `(E)`-form of the equation).
* `dtau_hId`: the integral identity
  `D^β g(τ) = D^β g(0) + ∫_0^τ D^β(RHS)(σ) dσ` for every `β = (b,a)`, `a + b ≤ 2`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT0

open Work.FTS.Galerkin (Fn Fam slice gdot)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG St1Class)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-- **`gdot g σ` is the transport expression on the open quadrant** (`0 < σ ≤ S`). -/
theorem dtau_jet_eq (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hμ : ClockBd α Φs E g) {S σ : ℝ} (hS : 0 < S) (hσ : σ ∈ Set.Ioc (0:ℝ) S)
    {b a : ℕ} (hba : a + b ≤ 2) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed b a (gdot g σ)))
      (Function.uncurry (Work.Spaces.mixed b a (Work.FTS_RegExport.RXT.Sys.RHS α Φs E g σ)))
      Work.FTS.EllipticEst.Q0 := by
  have hEqF := Work.FTS_RegExport.RXT.Sys.gdot_eq_profile (C₀ := C₀) (Φs := Φs) (E := E)
    (g := g) hS hα hα13 hEll hEL3 hStar hSol hOK hμ
  have hpoint := Work.FTS_RegExport.RXT.Sys.gdot_eq_RHS (Φs := Φs) (E := E) (g := g)
    (S := S) (α := α) hEqF
  refine Work.FTS.StrongEps.mixed_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ?_ b a
  intro p hp
  exact hpoint p.1 p.2 σ hp.1 hp.2.1 hp.2.2 hσ.1 hσ.2

/-- **The integral identity for the mixed jets**, with the transport expression as integrand. -/
theorem dtau_hId (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hμ : ClockBd α Φs E g) {S : ℝ} (hS : 0 < S) {b a : ℕ} (hba : a + b ≤ 2) :
    ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      Work.Spaces.mixed b a (slice g τ) z θ
        = Work.Spaces.mixed b a (slice g 0) z θ
          + ∫ σ in (0:ℝ)..τ,
              Work.Spaces.mixed b a (Work.FTS_RegExport.RXT.Sys.RHS α Φs E g σ) z θ := by
  intro z θ τ hz hθ hθ2 hτ0 hτS
  have hG := dtau_gdotLoc (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
    hα hα13 hEll hEL3 hStar hSol hOK hμ hS
  have hmii := dtau_mii (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
    hα hα13 hS hSol hOK hG b a hba z θ hz hθ hθ2 0 τ le_rfl hτ0 hτS
  have hInt : (∫ σ in (0:ℝ)..τ, Work.Spaces.mixed b a (gdot g σ) z θ)
      = ∫ σ in (0:ℝ)..τ,
          Work.Spaces.mixed b a (Work.FTS_RegExport.RXT.Sys.RHS α Φs E g σ) z θ := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun σ hσ => ?_))
    have hσ' : σ ∈ Set.Ioc (0:ℝ) τ := by rwa [uIoc_of_le hτ0] at hσ
    exact (dtau_jet_eq (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hμ hS ⟨hσ'.1, le_trans hσ'.2 hτS⟩ hba
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hθ2⟩))
  have h1 : Work.Spaces.mixed b a (slice g τ) z θ - Work.Spaces.mixed b a (slice g 0) z θ
      = ∫ σ in (0:ℝ)..τ,
          Work.Spaces.mixed b a (Work.FTS_RegExport.RXT.Sys.RHS α Φs E g σ) z θ := by
    rw [hmii, hInt]
  rw [sub_eq_iff_eq_add'] at h1
  exact h1

end Work.FTS_RegExport.RXT0
