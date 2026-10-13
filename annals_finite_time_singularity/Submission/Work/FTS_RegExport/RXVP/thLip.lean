import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.THL.cs7_theta_holder
import Submission.Work.FTS_RegExport.THL.L.vz7_thHol

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP.thHol_proved` — the NEW clause of the repaired `VelPkg` (open producer)

RESTATED 2026-10-11 (`cbc/fts_thlip_o1_plans.md` ITEM A): `VelPkg.thLip` (θ-Lipschitz) became
`VelPkg.thHol` (θ-Hölder, `ThHol`), and `thLip_proved` became `thHol_proved` (A8). The full
Lipschitz `cs7` half below is NOT needed any more; the Hölder route needs no new analysis
(leaves A1a–A7 in `FTS_RegExport/THL/Leaves.lean`). History of the old clause:

Lead install 2026-10-11 (`cbc/fts_velpkg_fix.md` + `cbc/fts_velpkg_fix_REVIEW.md`). The repaired
`RegExportIface.VelPkg` = the area's `VelPkgOpen` (open-θ `bnd`/`vz0`/`cont`, no axis clause) +
`thLip`. The RX-VP split is `RXVP3.velPkgOpen_proved` + `thLip_proved` (below) → `velPkg`.

Route (REVIEW §3):
* `Vz7` half — from `dbnd`'s `|pth Vz7| ≤ M` + `θ`-differentiability (`c2` on `Q0`) by the mean
  value theorem on the convex `Ioo 0 (π/2)`; no new analysis (even global in `z`).
* `cs7` half — NEW analytic content, research-level, STRONGER than `dbnd`: in
  `Rop Φ̃ = (2 sinθ Φ̃ + αG sinθ z∂_zΦ̃ + cosθ ∂_θΦ̃)/cosθ` the `Φ̃` terms need only `∂²_θΦ̃`
  bounded (with `Φ̃(π/2) = 0`: `B − xB' = O(x²)`), but the term `αG·tanθ·D_zΦ̃` needs `∂²_θ(z∂_zΦ̃)`
  bounded up to both edges — one `z`-derivative beyond `dbnd` (the same missing near-axis sup
  estimates as `dbnd`/`vanish0`). Physically true: `D_z` commutes with `bslOp`, `D_zF ~ Γ ~ x^{2α}`
  gives `D_zΦ̃ = A_z·x + O(x^{2+2α})`, `x = π/2 − θ`; regular near `θ = 0`.
* Optional weaker variant: a Hölder `θ`-modulus `|V θ − V θ'| ≤ K|θ−θ'|^β`, `β ∈ (0,1]`, which needs
  only `C^{1,β}` of `D_zΦ̃` (requires a ~20-line change of `lip_edge_*` to a Cauchy-limit argument).
-/

namespace Work.FTS_RegExport.RXVP

open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- **A8 = RX-VP / `thHol` (OPEN; RESTATED 2026-10-11 from `thLip_proved`,
`cbc/fts_thlip_o1_plans.md` ITEM A)**: the `VelPkg.thHol` clause at `(gS α (tauExt g), psiR)`, same
hypotheses as `RegExportIface.velPkg`. Route (~30 lines): `β = pExp α / 20`; the `cs7` half is
`THL.cs7_theta_holder` (A6, a global constant, so any `δ` works), the `Vz7` half is
`THL.vz7_thHol` (A7). Leaves: `FTS_RegExport/THL/Leaves.lean`. -/
theorem thHol_proved (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hμ : ClockBd α Φs E g) :
    ∀ S > 0, ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧
      ThHol (Vz7 (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
        (psiR α Φs E (tauExt g))) S β ∧
      ThHol (cs7 (pExp α) (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g) (gS α (tauExt g))
        (psiR α Φs E (tauExt g))) S β := by
  intro S hS
  have hp : 0 < pExp α / 20 := by
    have := Work.FTS.Regularity.pExp_pos hα
    linarith
  have hp1 : pExp α / 20 ≤ 1 := by
    have := Work.FTS.Regularity.pExp_le_one hα13
    linarith
  refine ⟨pExp α / 20, hp, hp1, ?_, ?_⟩
  · exact Work.FTS_RegExport.THL.L.vz7_thHol (Φs := Φs) (E := E) hα hα13 hEll hEL3 hStar hSol hOK
      hμ S hS
  · obtain ⟨K, hK, hcs⟩ := Work.FTS_RegExport.THL.cs7_theta_holder (Φs := Φs) (E := E)
      hα hα13 hEll hEL3 hStar hSol hOK hμ S hS
    intro z₀ _
    exact ⟨K, hK, 1, one_pos, fun τ hτ z hz _ θ hθ θ' hθ' => hcs τ hτ z hz θ hθ θ' hθ'⟩

end Work.FTS_RegExport.RXVP
