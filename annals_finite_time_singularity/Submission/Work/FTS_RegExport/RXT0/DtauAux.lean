import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.Sys.gdot_regular
import Submission.Work.FTS_RegExport.RXT.Sys.coeff_jets
import Submission.Work.FTS_RegExport.RXT.coeff_C2
import Submission.Work.FTS_RegExport.RXT.Sys.gdot_eq_profile
import Submission.Work.FTS_RegExport.RXT.Sys.mixed_integral_identity

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.DtauAux` — the auxiliary facts behind RX-T0

Two things:

* `DtauAux.gdotLoc_of_hyp`: the regularity package `GdotLoc S g` of `∂_τ g` (spatial `C²` at each
  fake time, with locally uniform jet bounds) for a family `g` satisfying the RX-T0 hypotheses.
  Assembled from the already-proved St1-chain leaves `Sys.coeff_jets` (`CoeffJets`),
  `RXT.coeff_C2` (`C²` of the coefficient slices), `Sys.gdot_eq_profile` (the `(E)`-form of the
  equation for the raw `g`) and `Sys.gdot_regular` (the producer of `GdotLoc`).
* `DtauAux.dtau_mii`: the integrated identity
  `D^β g(τ₂) − D^β g(τ₁) = ∫_{τ₁}^{τ₂} D^β(∂_τ g)(σ) dσ` for *every* `β = (b,a)` with
  `a + b ≤ 2`, packaged out of the six-component statement `Sys.mixed_integral_identity`.
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

/-- **`GdotLoc S g` from the RX-T0 hypotheses.** -/
theorem dtau_gdotLoc (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hμ : ClockBd α Φs E g) {S : ℝ} (hS : 0 < S) :
    Work.FTS.RegExportIface.RXT.GdotLoc S g :=
  Work.FTS_RegExport.RXT.Sys.gdot_regular (C₀ := C₀) (Φs := Φs) (E := E) (g := g) hS hα hα13 hOK
    (Work.FTS_RegExport.RXT.Sys.coeff_jets (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hμ S hS)
    (Work.FTS_RegExport.RXT.coeff_C2 (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hα hα13 hEL3 hStar hOK)
    (Work.FTS_RegExport.RXT.Sys.gdot_eq_profile (C₀ := C₀) (Φs := Φs) (E := E) (g := g)
      hS hα hα13 hEll hEL3 hStar hSol hOK hμ)

/-- Every `(b,a)` with `a + b ≤ 2` occurs in the index list `idx`. -/
theorem dtau_idx_exists (b a : ℕ) (h : a + b ≤ 2) :
    ∃ k : Fin 6, Work.FTS.RegExportIface.RXT.idx k = (b, a) := by
  have hb : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases hb with rfl | rfl | rfl <;> rcases ha with rfl | rfl | rfl <;>
    first
      | exact ⟨0, by decide⟩
      | exact ⟨1, by decide⟩
      | exact ⟨2, by decide⟩
      | exact ⟨3, by decide⟩
      | exact ⟨4, by decide⟩
      | exact ⟨5, by decide⟩
      | (exfalso; omega)

/-- **The integrated identity for every slot of order `≤ 2`.** -/
theorem dtau_mii (hα : 0 < α) (hα13 : α ≤ 1 / 3) {S : ℝ} (hS : 0 < S)
    (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hG : Work.FTS.RegExportIface.RXT.GdotLoc S g) :
    ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₁ ≤ τ₂ → τ₂ ≤ S →
      Work.Spaces.mixed b a (slice g τ₂) z θ - Work.Spaces.mixed b a (slice g τ₁) z θ
        = ∫ σ in τ₁..τ₂, Work.Spaces.mixed b a (gdot g σ) z θ := by
  intro b a hba z θ hz hθ hθ2 τ₁ τ₂ h1 h2 h3
  obtain ⟨k, hk⟩ := dtau_idx_exists b a (by omega)
  have hmain := Work.FTS_RegExport.RXT.Sys.mixed_integral_identity hS hα hα13 hSol hOK hG
    k z θ hz hθ hθ2 τ₁ τ₂ h1 h2 h3
  have h1' : (Work.FTS.RegExportIface.RXT.idx k).1 = b := by rw [hk]
  have h2' : (Work.FTS.RegExportIface.RXT.idx k).2 = a := by rw [hk]
  rw [h1', h2'] at hmain
  exact hmain

end Work.FTS_RegExport.RXT0
