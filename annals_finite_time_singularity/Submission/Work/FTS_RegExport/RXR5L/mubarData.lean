/-
# `RXR5L/mubarData` — the `mubar` data of the RX-R5 producer

The two `mubar` clauses of `Work.FTS.RegPkgGal.R5Parts` at the sanitised right-Taylor family
`SG α g` and the stream function `SΨ α Φs E g`:

* the uniform bound of `μ̄(τ) = L₁₂(N₀(τ))(0) + L₁₂(N(τ))(0)` on `[0,S]`;
* its `α`-Hölder modulus in the fake time.

## Route

`μ̄(τ) = 2·pExp α·μ(τ) + L₁₂(3 D_θ(slice g τ)/(1+z))(0)` (definitional, `Construction.mufunS`),
where `μ = muDyn` is the modulation constant of the family.  Both terms are controlled through the
class-`C` approximating families `gn` of the `LimApprox` clause of `DynOK'`:

* at every approximant `w = slice (gn n) τ` (a `ClassC` datum of `ℋ⁴`-size `≤ C₀·(pExp α)²`) the
  value rows `KMu0_row`/`KMu1_row`/`KMu2_row` bound the three `L₁₂`-zero-modes, and the
  *difference* rows `DiffRow0`/`DiffRow1`/`DiffRow2` (at the profile exponent; the smallness
  hypothesis of `Work.FTS_MuLipC` is not needed and is dropped in `MubarRows.lean`) bound their
  fake-time differences by `Xn (slice (gn n) τ - slice (gn n) τ') ≤ L|τ - τ'|` (the
  `ℋ⁴`-Lipschitz clause of `LimApprox`);
* `muDyn` at the limit family is the pointwise limit of the approximants' modulations
  (`LimApprox` clause (d)), and a uniform bound/Hölder modulus passes to the limit by
  `le_of_tendsto`;
* the transport term at the limit family carries its own bound/modulus (`aux/Tlim_bounds`), and
  the `mubar` of the sanitised family is the `mubar` of the reference family by congruence on the
  open quadrant (`MubarAssemblyAux.mubar_sanitized_eq`).

The assembly itself is `Work.FTS_RegExport.RXR5L.mubarData_of_Tfacts` (`MubarCore.lean`).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF
import Submission.Work.FTS_RegExport.RXR5L.MubarCore
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS_RegExport.RXR5L

theorem mubarData {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    {g : Work.FTS.Galerkin.Fam}
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.mubar
        (Work.Construction.N0 (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
        (Work.Construction.N (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ))| ≤ M) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      |Work.Construction.mubar
          (Work.Construction.N0 (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
          (Work.Construction.N (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ)
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ))
        - Work.Construction.mubar
          (Work.Construction.N0 (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ')
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ'))
          (Work.Construction.N (Work.FTS.Regularity.pExp α) (Work.Construction.Ftau
            (Work.FTS.Regularity.pExp α) (Work.FTS_RegExport.RXR5.SG α g) τ')
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ'))|
        ≤ M * |τ - τ'| ^ α) := by
  exact mubarData_of_Tfacts hα hα13 hEll hStar hSol hOK hS
    (Work.FTS_RegExport.RXR5L.aux.Tlim_bounds (Φs := Φs) (E := E) hα hα13 hOK hS)

end Work.FTS_RegExport.RXR5L
