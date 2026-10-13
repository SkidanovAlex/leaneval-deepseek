/-
# `Work.FTS_RegExport.RXR5L.Ftau_C1Jet` — the class-1 jet of the full profile `F(τ) = F_* + g(τ)`

The `R5`-assembly (`Work.FTS.RegPkgGal.Der.R5Parts_of_pieces`) consumes `C1Jet`-regularity of the
*class data* of the fake-time flow.  This file supplies the base object: the full profile

  `Ftau (pExp α) (gS α (tauExt g)) τ z θ = F_*(z,θ) + gS α (tauExt g) z θ τ`

(`Work.Construction.Ftau` — the static profile plus the sanitised right-Taylor family `SG α g`,
which is *by definition* `gS α (tauExt g)`).

The proof is the additive closure of `C1Jet` applied to the two halves:

* the static profile `(z,θ) ↦ F_*(z,θ)` is a `C1Jet` with the constant `100 + 20·pExp α`
  (`RegPkgGal.Der.C1JetFstar`, `τ`-independent);
* the sanitised family `SG α g` is a `C1Jet` with some constant `N₁`
  (`RXR5L.SG_C1Jet`, from the dynamic package `DynOK'` and the `St1`-class data);

`Work.FTS.RegPkgGal.C1Jet.add` then gives the sum with constant
`(100 + 20·pExp α) + N₁`.  The hypothesis `hO1` (the `Dz`/`Dth` slots of `SG α g`) is not needed;
it belongs to the *derivative* slots of the profile, which are handled by the sibling nodes
`DzFtau_C1Jet` / `DthFtau_C1Jet`.
-/
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.SG_C1Jet
import Submission.Work.FTS.RegPkgGal.Der.C1JetFstar
import Submission.Work.FTS.RegPkgGal.Der.zderiv_N

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5L

theorem Ftau_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hO1 : ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂
        (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃
        (fun z θ τ => Work.Spaces.Dth (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ)) :
    ∃ N₄ : ℝ, 0 ≤ N₄ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₄
        (fun z θ τ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) := by
  obtain ⟨N₁, _hN₁0, hN₁⟩ := SG_C1Jet (S := S) hα hα13 hOK hS hSt1
  have hF : Work.FTS.RegPkgGal.C1Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ (_ : ℝ) => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) :=
    Work.FTS.RegPkgGal.Der.C1JetFstar (S := S) hα hα13
  have hsum : Work.FTS.RegPkgGal.C1Jet α S
      ((100 + 20 * Work.FTS.Regularity.pExp α) + N₁)
      (fun z θ τ =>
        Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + Work.FTS_RegExport.RXR5.SG α g z θ τ) :=
    Work.FTS.RegPkgGal.C1Jet.add hF hN₁
  exact ⟨100 + 20 * Work.FTS.Regularity.pExp α + N₁,
    by have hp := Work.FTS.Regularity.pExp_pos hα; linarith, hsum⟩

end Work.FTS_RegExport.RXR5L
