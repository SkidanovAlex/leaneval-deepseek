import Mathlib
import Submission.Work.Pi6.EFACTS.Basic
import Submission.Work.Pi6.EFACTS.Z.WangTauSLowValue
import Submission.Work.StemsB.wangTauS
import Submission.Work.Stems.wangOddStep
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Wang exactness of the cover, in terms of the geometric transgression

The library proves the shifted Wang sequence exact for the **generic** identification data `γ, τS`
(`Work.StemsB.wangCohShiftExact₂R/₃R` and `Work.Stems.wangCohShiftExactTotal`).  Instantiating
`γ = wangGammaExplicit` and `τS = wangTauS` (resp. `wangTauSLow` in the fibre's top degree), the
value theorems `Work.StemsB.wangTauS_value` and `Work.StemsB.wangTauSLow_value` identify the generic
transgression `wangCohShiftθR ℤ` with the **geometric** transgression `Work.StemsB.wangTheta`
(resp. `Work.StemsB.wangThetaLow`), the map whose multiplicativity is proved in
`Submission/Work/Pi6/EFACTS/Z/`.

The three spots below are the input to the computation of `H^*(E)` of the cover:
`H^{n+3}(E) → H^{n+3}(F) →^{θ_n} H^{n+1}(F) → H^{n+4}(E) → H^{n+4}(F)`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.Pi6.EFACTS

noncomputable section

variable {E : Type} [TopologicalSpace E]

/-- **The generic Wang transgression is the geometric one** (function form). -/
theorem wangCohShiftθR_eq_wangTheta (b : ℕ) (hb : 2 ≤ b) (p : C(E, Work.StemsB.SphModel b))
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) (n : ℕ) :
    ⇑(Work.StemsB.wangCohShiftθR ℤ (TopCat.of E) (Work.StemsB.wangA b p)
        (Work.StemsB.wangCohFsp b p) b (Work.StemsB.wangGammaExplicit b p hT_O)
        (Work.StemsB.wangTauS b hb E p hT_O d_G hT_G) n)
      = ⇑(Work.StemsB.wangTheta b hb p d_G hT_G hT_O n) :=
  funext (fun a => Work.StemsB.wangTauS_value b hb E p hT_O d_G hT_G n a)

/-- **Wang exactness, spot 2**: the image of the restriction is the kernel of the geometric
transgression (`H^{n+3}(E) → H^{n+3}(F) →^{θ_n} H^{n+1}(F)`). -/
theorem wangExact₂ (b : ℕ) (hb : 2 ≤ b) (p : C(E, Work.StemsB.SphModel b))
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact
      (Work.StemsB.wangCohShiftαR ℤ (TopCat.of E) (Work.StemsB.wangA b p)
        (Work.StemsB.wangCohFsp b p) b (Work.StemsB.wangGammaExplicit b p hT_O) (n + b))
      (⇑(Work.StemsB.wangTheta b hb p d_G hT_G hT_O n)) := by
  have h := Work.StemsB.wangCohShiftExact₂R ℤ (TopCat.of E) (Work.StemsB.wangA b p)
    (Work.StemsB.wangCohFsp b p) b (Work.StemsB.wangGammaExplicit b p hT_O)
    (Work.StemsB.wangTauS b hb E p hT_O d_G hT_G) n
  rwa [wangCohShiftθR_eq_wangTheta b hb p hT_O d_G hT_G n] at h

/-- **Wang exactness, spot 3**: the image of the geometric transgression is the kernel of `βS`
(`H^{n+3}(F) →^{θ_n} H^{n+1}(F) → H^{n+4}(E)`). -/
theorem wangExact₃ (b : ℕ) (hb : 2 ≤ b) (p : C(E, Work.StemsB.SphModel b))
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact (⇑(Work.StemsB.wangTheta b hb p d_G hT_G hT_O n))
      (Work.StemsB.wangCohShiftβSR ℤ (TopCat.of E) (Work.StemsB.wangA b p)
        (Work.StemsB.wangCohFsp b p) b (Work.StemsB.wangTauS b hb E p hT_O d_G hT_G) n) := by
  have h := Work.StemsB.wangCohShiftExact₃R ℤ (TopCat.of E) (Work.StemsB.wangA b p)
    (Work.StemsB.wangCohFsp b p) b (Work.StemsB.wangGammaExplicit b p hT_O)
    (Work.StemsB.wangTauS b hb E p hT_O d_G hT_G) n
  rwa [wangCohShiftθR_eq_wangTheta b hb p hT_O d_G hT_G n] at h

/-- **Wang exactness, the total-space spot**: the image of `βS` is the kernel of the next
restriction (`H^{n+1}(F) → H^{n+4}(E) → H^{n+4}(F)`). -/
theorem wangExactTot (b : ℕ) (hb : 2 ≤ b) (p : C(E, Work.StemsB.SphModel b))
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact
      (Work.StemsB.wangCohShiftβSR ℤ (TopCat.of E) (Work.StemsB.wangA b p)
        (Work.StemsB.wangCohFsp b p) b (Work.StemsB.wangTauS b hb E p hT_O d_G hT_G) n)
      (Work.StemsB.wangCohShiftαR ℤ (TopCat.of E) (Work.StemsB.wangA b p)
        (Work.StemsB.wangCohFsp b p) b (Work.StemsB.wangGammaExplicit b p hT_O) (n + b + 1)) :=
  Work.Stems.wangCohShiftExactTotal (R := ℤ) (TopCat.of E) (Work.StemsB.wangA b p)
    (Work.StemsB.wangCohFsp b p) b (Work.StemsB.wangGammaExplicit b p hT_O)
    (Work.StemsB.wangTauS b hb E p hT_O d_G hT_G) n

/-- **The low-degree Wang exactness** with the geometric low transgression: the image of the
restriction `H^{b-1}(E) → H^{b-1}(F)` is the kernel of `wangThetaLow`. -/
theorem wangExactLow (b : ℕ) (hb : 2 ≤ b) (p : C(E, Work.StemsB.SphModel b))
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) :
    Function.Exact
      (Work.StemsB.wangCohAlphaLowR ℤ (TopCat.of E) (Work.StemsB.wangA b p)
        (Work.StemsB.wangCohFsp b p) b (Work.StemsB.wangGammaExplicit b p hT_O))
      (⇑(Work.StemsB.wangThetaLow b hb E p d_G hT_G hT_O)) := by
  have h := Work.StemsB.wangCohExactSphereLow b hb E p hT_O d_G hT_G
  have h2 : ⇑(Work.StemsB.wangCohThetaLowR ℤ (TopCat.of E) (Work.StemsB.wangA b p)
        (Work.StemsB.wangCohFsp b p) b (Work.StemsB.wangGammaExplicit b p hT_O)
        (Work.StemsB.wangTauSLow b hb E p hT_O d_G hT_G))
      = ⇑(Work.StemsB.wangThetaLow b hb E p d_G hT_G hT_O) :=
    funext (fun a => Work.StemsB.wangTauSLow_value b hb E p hT_O d_G hT_G a)
  rwa [h2] at h

end

end Work.Pi6.EFACTS
