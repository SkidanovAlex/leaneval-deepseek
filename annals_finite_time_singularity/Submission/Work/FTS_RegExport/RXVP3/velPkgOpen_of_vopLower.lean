import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC
import Submission.Work.FTS_RegExport.RXT.velVanish2
import Submission.Work.FTS_RegExport.RXT0.RXJets.coeffcR
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
import Submission.Work.FTS_RegExport.RXVP3.bnd_open
import Submission.Work.FTS_RegExport.RXVP3.cont_open
import Submission.Work.FTS_RegExport.RXVP3.velPkgEasy
import Submission.Work.FTS_RegExport.RXVP3.vz0_of_vopLower
import Submission.Work.FTS_RegExport.VPOpen
import Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.XStep =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.XStep

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.EpsEngine (XBall Feps)
open Work.FTS.StrongEps.EpsLocalPStar (iter limFam)

set_option autoImplicit false

/-- **The residual bundle of the local-step chapter on the `X`-ball route.**

For every `α ∈ (0,1]`, every `ε ∈ (0,1]`, every admissible `(Φs, E)` (the elliptic/star packages)
*with the class radius `2 C₀`* and every `ℋ⁶`-size bound `M'` there are a positive horizon `δ` and a
positive ball radius `R` such that, for every datum `h₀` of the class

  `SmoothOpen h₀ ∧ HkMem α 6 h₀ ∧ HkSq α 6 h₀ ≤ M' ∧ ClassC α (P_z (J_ε h₀)) ∧ Xn α (P_z (J_ε h₀)) ≤ C₀ α²`

the datum is honest (`EpsMem α h₀`) with `EpsSq α h₀ ≤ R`, every Picard iterate's slice and the
limit family's slice lie in `XBall α ρ ε R (2 C₀)`, the limit family is jointly `C¹` on the slab
`(0,∞) × (0,π/2) × [0,δ]`, and every limit slice is an `EpsDatumP`.

The two numbers `M'` (the *datum's* `ℋ⁶`-size, which is what the local step's datum hypothesis gives)
and `R` (the *invariant* `X`-ball, chosen after `M'`) are deliberately different: this is exactly the
room that the `ℋ⁶`-ball invariant `E4R3.EngineResiduals` lacks. -/
def XStepInvariant (Ce Cs C₀ : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 → ∀ {Φs : Fn} {E : Fn → Fn},
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
    MuLamOK α (2 * C₀) Φs E →
    ∀ M' : ℝ, 0 ≤ M' → ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, 0 < R ∧
      ∀ h₀ : Fn,
        Work.FTS.EllipticEst.SmoothOpen h₀ → Work.Spaces.HkMem α 6 h₀ →
        Work.Spaces.HkSq α 6 h₀ ≤ M' →
        Work.FTS.ClassC.ClassC α (Pz (Jeps ρ ε h₀)) →
        Work.FTS.Nonlin.Xn α (Pz (Jeps ρ ε h₀)) ≤ C₀ * α ^ 2 →
        EpsMem α h₀ ∧ EpsSq α h₀ ≤ R ∧
        (∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
          XBall α ρ ε R (2 * C₀) (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ)) ∧
        (∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
          XBall α ρ ε R (2 * C₀) (slice (limFam (Feps α ρ ε Φs E) h₀) τ)) ∧
        (ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => limFam (Feps α ρ ε Φs E) h₀ p.1 p.2.1 p.2.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 δ)) ∧
        (∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
          EpsDatumP α ρ ε (slice (limFam (Feps α ρ ε Φs E) h₀) τ))



end Work.FTS.StrongEps.EpsE4Thr.XStep
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `velPkgOpen_of_vopLower` — `VelPkgOpen` from its fieldwise pieces, plus the one *missing*
hypothesis

`velPkgOpen_proved` (`RXVP3/velPkgOpen_proved.lean`, statement unchanged) asks for

`∀ S > 0, VelPkgOpen (pExp α) (maxMu …) (gS α (tauExt g)) (psiR α Φs E (tauExt g)) S`

from `hα, hα13, hEll, hEL3, hStar, hSol, hOK, hdat, hμ`.  Seven of the eight fields are proved
from exactly those hypotheses:

* `vanishK`, `c2`, `vth_ends` — `RXVP3.velPkgEasy` (uniform in `τ`);
* `vanish0` — `RXT.velVanish2` (sampled at `(j,i) = (0,0), (1,0), (0,1)`);
* `dbnd` — `RXT.Sys.coeff_dbnd`;
* `cont` — `RXVP3.cont_open`;
* `bnd` — `RXVP3.bnd_open`.

The eighth, `vz0` (`0 ≤ Vz7` on the open quadrant, for *all* `τ ≥ 0`), is **not** a consequence of
those hypotheses.  By the proved closed form (`RXVP3.vz0_of_vopLower.vz7_eq_of_vop`)

`Vz7 = (1 - μτ) + 2αG·V(Φ)`,  `Φ = psiR α Φs E (tauExt g)`,

so `vz0` is *equivalent* to the pointwise lower bound `2αG·V(Φ)(z,θ) ≥ -(1 - μτ)`; and by the
proved one-sided limit `RXVP2.velPkgSup_proved.Vz7_tendsto_nhdsWithin_left` the value of `Vz7`
at `θ → π/2⁻` is `1 - μτ + 4αG·∂_θΦ(z,π/2)`.  Hence `vz0` demands lower information on the *axis
slope* `∂_θΦ(z,π/2)` of the stream function — which none of `hEll`, `hEL3`, `hStar`, `hSol`,
`hOK`, `hdat`, `hμ` supplies (the BSL law with Dirichlet and decay does not force it to vanish:
the axisymmetric BSL operator is not symmetric under `r ↦ -r`), and which the design itself
assigns to a *separate* item (`StreamBdry`'s `hΦaxis`: `Φ = O(cos²θ)`).  The estimates available
from the hypotheses give only `Vz7 ≥ 1 - μτ - 4αG - O((Cs+CeC₀)α²)`, which is *negative* for
`α ∈ (1/8,1/3]` with `μτ ≈ 0` — precisely the range the statement allows (`hμ` gives only
`|μ| ≤ 1/2`).

This file therefore proves the package with that one hypothesis made explicit, in the sharp form
consumed by `RXVP3.vz0_of_vopLower`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

namespace Work.FTS_RegExport.RXVP3

set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}

/-- **`VelPkgOpen` at the constructed family, conditional on the (missing, non-derivable) pointwise
lower bound `2αG·V(Φ) ≥ -(1 - μτ)` on the open quadrant.** -/
theorem velPkgOpen_of_vopLower (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : ClockBd α Φs E g)
    (hVop : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      -(1 - Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g τ)
        ≤ 2 * pExp α * Work.Construction.Vop
            (slice (psiR α Φs E (tauExt g)) τ) z θ) :
    ∀ S > 0, Work.FTS_RegExport.VelPkgOpen (pExp α)
      (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g)
      (gS α (tauExt g)) (psiR α Φs E (tauExt g)) S := by
  intro S hS
  -- the three clauses of `velPkgEasy`, uniformly in `τ`
  obtain ⟨hE1, hE2, hE3⟩ := velPkgEasy (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hdat hμ
  -- the slots of `Φ̃` (order `≤ 2`)
  obtain ⟨Mv, hMv⟩ := Work.FTS_RegExport.RXT.velVanish2 (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
  -- the coefficient jets
  obtain ⟨Md, hMd⟩ := Work.FTS_RegExport.RXT.Sys.coeff_dbnd (α := α) (C₀ := C₀) (Ce := Ce)
    (Cs := Cs) (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
  -- the two sup/clause fields
  obtain ⟨M, hM⟩ := bnd_open (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hdat hμ
  have hCont := cont_open (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hdat hμ S hS
  have hVz0 := vz0_of_vopLower (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK hdat hμ hVop
  refine ⟨⟨M, hM⟩, hVz0, ?_, ?_, ?_, hCont, ?_, ?_⟩
  · -- `vth_ends`
    intro z τ hz hτ
    exact hE3 (max τ 1) (lt_of_lt_of_le zero_lt_one (le_max_right τ 1))
      τ ⟨hτ, le_max_left τ 1⟩ z hz
  · -- `c2`
    intro τ hτ
    exact hE2 (max S 1) (lt_of_lt_of_le zero_lt_one (le_max_right S 1))
      τ ⟨hτ.1, le_trans hτ.2 (le_max_left S 1)⟩
  · -- `dbnd`
    refine ⟨Md, ?_⟩
    intro τ hτ j i hji z θ hz hθ hθ2
    exact hMd τ hτ j i hji z θ hz hθ hθ2
  · -- `vanish0`
    refine ⟨Mv, ?_⟩
    intro τ hτ z θ hz hθ hθ2 Q hQ
    have h00 := hMv τ hτ z θ hz hθ hθ2 Q hQ 0 0 (by norm_num)
    have h10 := hMv τ hτ z θ hz hθ hθ2 Q hQ 1 0 (by norm_num)
    have h01 := hMv τ hτ z θ hz hθ hθ2 Q hQ 0 1 (by norm_num)
    simp only [Work.Spaces.mixed, Work.Spaces.DzIter, Work.Spaces.DthIter] at h00 h10 h01
    exact ⟨h00, h10, h01⟩
  · -- `vanishK`
    exact hE1 S hS

end Work.FTS_RegExport.RXVP3
end
end
