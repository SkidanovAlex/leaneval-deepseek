/-
# `SharpAux/HonestTermsBound` — the ten `ℋ⁴`-priced terms of the difference of `N`

The ten monomials `TRB, TUB, TVB, TDB, TEB, TRD, TUD, TVD, TDD, TED`
(`SharpAux/Defs.lean`) are those in which *both* factors are honest (`HQo α 4`) functions:
either an `h`/`g`/`g'`-derived atom, or an elliptic output `Rop/Uop/Vop(Φ̃_{g'})`,
`Rop/Uop/Vop(Φ̃_h)` of the packages `hell`, or one of the angular moments `FK g'`, `FK h`
possibly multiplied by `sin²θ`.

The proof is split by the two groups of terms: the five `g'`-side terms are `HonTerms.part1`, the
five `h`-side ones `HonTerms.part2` (the split exists only because the build system caps the size
of a single module).  Each part produces a `Kᵢ > 0` with the bound `Kᵢ·(1 + |g|_{ℋ⁵} + |g'|_{ℋ⁵})·
|h|_{ℋ⁵}`; the two constants are combined into `K₁ + K₂`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Part1
import Submission.Work.FTS.GalFields.RHS.SharpAux.HonTerms.Part2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.RHS.SharpAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem HonestTermsBound {α α₂ Ci Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {g g' h : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.GalClass α g' →
      Work.FTS.Nonlin.GalClass α h → α ≤ 1 →
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVB α EllSol g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVB α EllSol g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVB α EllSol g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDB α g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDB α g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDB α g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TEB α g' h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TEB α g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEB α g' h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRD α EllSol g h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRD α EllSol g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRD α EllSol g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUD α EllSol g h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUD α EllSol g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUD α EllSol g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVD α EllSol g h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVD α EllSol g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVD α EllSol g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDD α g h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDD α g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDD α g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TED α g h) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TED α g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TED α g h)
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h) := by
  obtain ⟨K1, hK1pos, h1⟩ := HonTerms.part1 hN hstar hell hα hαα₂
  obtain ⟨K2, hK2pos, h2⟩ := HonTerms.part2 hN hstar hell hα hαα₂
  refine ⟨K1 + K2, by linarith, ?_⟩
  intro g g' h hg hg' hh hα1
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1 hg hg' hh hα1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2 hg hg' hh hα1
  have hS0 : (0 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g' := by
    have h1 := Work.Spaces.HkNorm_nonneg α 5 g
    have h2 := Work.Spaces.HkNorm_nonneg α 5 g'
    linarith
  have hnh : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α h := Work.Spaces.HkNorm_nonneg α 5 h
  have up1 : ∀ {T : Fn},
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ K1 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h →
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ (K1 + K2) * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by
    rintro T ⟨hS, hM, hX⟩
    exact ⟨hS, hM, le_trans hX (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hS0) hnh)⟩
  have up2 : ∀ {T : Fn},
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ K2 * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h →
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ (K1 + K2) * (1 + Work.FTS.GalFields.Xn5 α g + Work.FTS.GalFields.Xn5 α g')
              * Work.FTS.GalFields.Xn5 α h := by
    rintro T ⟨hS, hM, hX⟩
    exact ⟨hS, hM, le_trans hX (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hS0) hnh)⟩
  exact ⟨up1 a1, up1 a2, up1 a3, up1 a4, up1 a5,
    up2 b1, up2 b2, up2 b3, up2 b4, up2 b5⟩

end Work.FTS.GalFields.RHS.SharpAux
