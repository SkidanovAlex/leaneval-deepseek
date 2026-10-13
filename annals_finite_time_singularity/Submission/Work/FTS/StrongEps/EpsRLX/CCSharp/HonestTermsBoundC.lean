/-
# `CCSharp/HonestTermsBoundC` — the ten `ℋ⁴`-priced terms at the `ClassC` level

The `ClassC`-port of `Work.FTS.GalFields.RHS.SharpAux.HonestTermsBound`: the ten monomials
`TRB, TUB, TVB, TDB, TEB, TRD, TUD, TVD, TDD, TED` in which both factors are honest (`HQo α 4`),
with the three `GalClass` hypotheses replaced by `ClassC`, `hell` by the `ClassC`-hypothesis
`hEll` on the elliptic operator, and `h := W₁ − W₂` produced by `CCSharp.sub_classC`.

The split into the two groups of five terms is the same one as in the `GalClass` version
(module size, and the two halves are independent):

* `CCSharp.HonTermsC.Part1C` — the five `g'`-side terms `TRB, TUB, TVB, TDB, TEB`
  (here with `g' := W₂`, `h := W₁ − W₂`);
* `CCSharp.HonTermsC.Part2C` — the five `h`-side terms `TRD, TUD, TVD, TDD, TED`
  (here with `g := W₁`, `h := W₁ − W₂`).

Each half produces `Kᵢ > 0` with the bound `Kᵢ·(1 + |W₁|_{ℋ⁵} + |W₂|_{ℋ⁵})·|W₁ − W₂|_{ℋ⁵}`; the
two constants are combined into `K₁ + K₂` exactly as in the `GalClass` version.  The intended
consumers are `Work.FTS.StrongEps.EpsRLX.CCSharp.NDiffIdC` and the `ClassC`-level assembly
`sharp_N_diff`, which recombines these ten bounds with the `𝒲^{4,∞}`-priced ten
(`CCSharp.WlInfTermsBoundC`).
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith.Frontend
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.Base
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.HonTermsC.Part1C
import Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.HonTermsC.Part2C

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.CCSharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem HonestTermsBoundC {α α₂ Ci Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u))
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ → α ≤ 1 →
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRB α E W₂ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUB α E W₂ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVB α E W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVB α E W₂ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDB α W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDB α W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDB α W₂ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TEB α W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TEB α W₂ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEB α W₂ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRD α E W₁ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUD α E W₁ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVD α E W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVD α E W₁ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDD α W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDD α W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDD α W₁ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TED α W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TED α W₁ (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TED α W₁ (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))
      := by
  obtain ⟨K1, hK1pos, h1⟩ := HonTermsC.Part1C hN hstar hEll hα hαα₂
  obtain ⟨K2, hK2pos, h2⟩ := HonTermsC.Part2C hN hstar hEll hα hαα₂
  have hK12 : 0 < K1 + K2 := by linarith
  refine ⟨K1 + K2, hK12, ?_⟩
  intro W₁ W₂ hW₁ hW₂ hα1
  have hsub : Work.FTS.ClassC.ClassC α (fun z θ => W₁ z θ - W₂ z θ) := sub_classC hW₁ hW₂
  obtain ⟨a1, a2, a3, a4, a5⟩ := h1 hW₁ hW₂ hsub hα1
  obtain ⟨b1, b2, b3, b4, b5⟩ := h2 hW₁ hW₂ hsub hα1
  have hS0 : (0 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂ := by
    have hW1 := Work.Spaces.HkNorm_nonneg α 5 W₁
    have hW2 := Work.Spaces.HkNorm_nonneg α 5 W₂
    linarith
  have hnh : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.Spaces.HkNorm_nonneg α 5 (fun z θ => W₁ z θ - W₂ z θ)
  have up1 : ∀ {T : Fn},
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ K1 * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) →
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ (K1 + K2) * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    rintro T ⟨hS, hM, hX⟩
    exact ⟨hS, hM, le_trans hX (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hS0) hnh)⟩
  have up2 : ∀ {T : Fn},
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ K2 * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) →
      Work.FTS.EllipticEst.SmoothOpen T ∧ Work.Spaces.HkMem α 4 T ∧
        Work.FTS.Nonlin.Xn α T
          ≤ (K1 + K2) * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    rintro T ⟨hS, hM, hX⟩
    exact ⟨hS, hM, le_trans hX (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) hS0) hnh)⟩
  exact ⟨up1 a1, up1 a2, up1 a3, up1 a4, up1 a5,
    up2 b1, up2 b2, up2 b3, up2 b4, up2 b5⟩

end Work.FTS.StrongEps.EpsRLX.CCSharp
