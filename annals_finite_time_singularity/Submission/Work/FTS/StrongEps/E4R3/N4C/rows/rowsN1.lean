/-
# `E4R3/N4C/rows/rowsN1` — the honest (§8) rows 8–11 of the class-`C` row table

The four `Xn`-rows of the level-four nonlinear pairing, in the *honest* context
`Work.FTS.StrongEps.E4R3.N4C.CtxT` (i.e. with the profile `g` carrying only the class-`C`
data `ClassC α g` + `CoerAdmO α g`, and the star package `VocabO2.StarPkgo2`):

  `Xn α (N₁^{gg}) ≤ K α^{-1/2} X²`, `Xn α (N₁^{g*}) ≤ K √α X`,
  `Xn α (N₁^{*g}) ≤ K √α X`, `Xn α (N₁^{**}) ≤ K α²`,   (`X = Xn α g`).

Route (each row is the honest re-run of the frozen `NonlinRows.NRow8`/`NRow9`/`NRow10` against
the *open* packages; the only substitution is `galClass_HQo4 hgal → CtxT.hqo4`, see
`NOTES_rowsNT.md`):

* row 8: `N4Norm'.prod` on `H = ℛ(Φ̃_g)` (`EllPkgGo.R`) and `g ∈ HQo α 4`;
* row 9: `N4Norm'.wprod` on the `𝒲^{4,∞}`-coefficient `F_*` (`Fstar_W`) and `H`;
* row 10: `N4Norm'.wprod` on the weighted star coefficient `((z+1)/z)ℛ(Φ̃_*)`
  (`StarPkgo2.RW`) and the bounded radial factor `(z/(1+z))g` (`NRow10aux.mul_phi_Hk`);
* row 11: the priced honest row `StrongPersist.L3Rhs.N1ssPriced`.

The rows 9 and 10 halves live in the sibling modules `rows/rowN1gs.lean` and
`rows/rowN1sg.lean` and are imported below.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.Hon
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.HonDecay
import Submission.Work.FTS.StrongPersist.L3Rhs.N1ssPriced
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowN1gs
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowN1sg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Row 8: `N₁^{gg} = 2 ℛ(Φ̃_g) g` -/

theorem rowN1gg (IP : ℝ → Fn → Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      CtxT Cs Ce α₂ α g Φs Φg →
      Xn α (Work.FTS.Nonlin.N1gg α g Φg)
        ≤ K * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 2) := by
  obtain ⟨hCi, _⟩ := hN.pos
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ci * max Ce 1, mul_pos (mul_pos (by norm_num) hCi) hmax, ?_⟩
  intro α g Φs Φg h
  -- the coefficient `H = ℛ(Φ̃_g)` and the profile
  have hRreg : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := h.hell.R.1
  have hRB : Work.FTS.Nonlin.Xn α
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
      ≤ Ce * Work.FTS.Nonlin.Xn α g := h.hell.R.2
  have hg4 : Work.FTS.VocabO.HQo α 4 g := h.hqo4
  have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨h.hα, h.hαα₂⟩
  have hprod := hN.prod α hαIoc (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) g
    hRreg hg4
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg h.hα.le _
  -- `N₁^{gg}` is `2` times the product
  have heq : Work.FTS.Nonlin.N1gg α g Φg = fun z θ =>
      2 * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ * g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N1gg]
    ring
  rw [heq, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbound : Work.FTS.Nonlin.Xn α
        (fun z θ => Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ * g z θ)
      ≤ (Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
    refine le_trans hprod.2 ?_
    have hp : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCi.le hA
    have h1 : Ci * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
          * Work.FTS.Nonlin.Xn α g
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ce * Work.FTS.Nonlin.Xn α g)
          * Work.FTS.Nonlin.Xn α g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRB hp) hXg
    have h2 : Ci * α ^ (-(1 / 2 : ℝ)) * (Ce * Work.FTS.Nonlin.Xn α g)
          * Work.FTS.Nonlin.Xn α g
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
          * Work.FTS.Nonlin.Xn α g :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg) hp) hXg
    refine le_trans h1 (le_trans h2 ?_)
    have he : Ci * α ^ (-(1 / 2 : ℝ)) * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
          * Work.FTS.Nonlin.Xn α g
        = (Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
      ring
    rw [he]
  have h2bound := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)
  have he2 : 2 * ((Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2))
      = (2 * Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
    ring
  rw [he2] at h2bound
  exact h2bound

/-! ## Row 11: `N₁^{**} = 2 ℛ(Φ̃_*) F_*` -/

theorem rowN1ss (IP : ℝ → Fn → Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      CtxT Cs Ce α₂ α g Φs Φg →
      Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * α ^ 2 := by
  obtain ⟨C, hC, hCb⟩ := Work.FTS.StrongPersist.L3Rhs.N1ssPriced
  refine ⟨C * (1 + |Cs|), mul_pos hC (by positivity), ?_⟩
  intro α g Φs Φg h
  exact (hCb α ⟨h.hα, h.hα1⟩ Cs Φs h.hs).2

/-! ## Rows 9 and 10 (sibling modules `rows/rowN1gs`, `rows/rowN1sg`) -/

/-! ## The row table -/

theorem rowsN1 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg)
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gs α g Φg)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * α ^ 2 := by
  obtain ⟨K8, hK8, h8⟩ := rowN1gg IP hN hE
  obtain ⟨K9, hK9, h9⟩ := rowN1gs IP hN hE
  obtain ⟨K10, hK10, h10⟩ := rowN1sg IP hN hE
  obtain ⟨K11, hK11, h11⟩ := rowN1ss IP hN hE
  refine ⟨K8 + K9 + K10 + K11 + 1, by linarith, ?_⟩
  intro α g Φs Φg hctx
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hα : 0 < α := hctx.hα
  have e8 : K8 ≤ K8 + K9 + K10 + K11 + 1 := by linarith
  have e9 : K9 ≤ K8 + K9 + K10 + K11 + 1 := by linarith
  have e10 : K10 ≤ K8 + K9 + K10 + K11 + 1 := by linarith
  have e11 : K11 ≤ K8 + K9 + K10 + K11 + 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans (h8 hctx) (mul_le_mul_of_nonneg_right e8 ?_)
    exact mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
  · refine le_trans (h9 hctx) (mul_le_mul_of_nonneg_right e9 ?_)
    exact mul_nonneg (Real.sqrt_nonneg α) hXg
  · refine le_trans (h10 hctx) (mul_le_mul_of_nonneg_right e10 ?_)
    exact mul_nonneg (Real.sqrt_nonneg α) hXg
  · refine le_trans (h11 hctx) (mul_le_mul_of_nonneg_right e11 ?_)
    exact sq_nonneg α

end Work.FTS.StrongEps.E4R3.N4C.rows
