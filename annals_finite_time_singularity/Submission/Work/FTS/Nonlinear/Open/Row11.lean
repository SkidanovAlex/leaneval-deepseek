/-
# Row 11 of the honest (open-quadrant) chapter — from `NonlinRows.NRow11_of_wlInf`

Row 11 (`N₁^{**} = 2 ℛ(Φ̃_*) F_*`) is the first row that needs the *closed-domain* `𝒲^{4,∞}`
pricing of the star coefficient: the frozen `VocabO.StarPkgo` carries only open-quadrant
`D`-sups (`WDMem`/`WDp`), which are blind to the behaviour at `z = 0` and to the angular decay,
and row 11 is **false** under them (`NonlinRows/NOTES_Rows.md` §3(c); design
`Submission/Work/FTS/STARPKG_T2_LEAD.md` §1.1, §1.6).

`VocabO2.StarPkgo2` adds exactly the missing field: its `RW` is
`WlInfMem α 4 ((z+1)/z · ℛ(α, Φ̃_*)) ∧ WlInf α 4 (…) ≤ Cs · α`, i.e. (definitionally, since
`VocabO2.PhiTs = PhiTil α (Fstar α) Φs`) the two hypotheses of the proved conditional lemma
`Work.FTS.NonlinRows.NRow11_of_wlInf`.
-/
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.NRow11

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

theorem Row11 (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N1ss α Φs) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * (α ^ 2) := by
  obtain ⟨K, hK, h⟩ := Work.FTS.NonlinRows.NRow11_of_wlInf IP hN hE
  refine ⟨K, hK, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hg hs hell
  exact h (Work.FTS.NonlinRows.Ctx.mk' hα hα1 hαα₂ hg hs.toStarPkgo hell) hs.RW.1 hs.RW.2

end Work.FTS.Nonlinear.Open
