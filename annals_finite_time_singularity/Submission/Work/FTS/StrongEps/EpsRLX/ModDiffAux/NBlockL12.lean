import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.EpsRLX.NDiffClassC
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN
import Submission.Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `ModDiffAux/NBlockL12` — the `L₁₂`-zero-mode difference of the `N`-block on the class `C`

The `N`-component of the difference of the two modulation constants
(`Work.FTS.StrongEps.EpsRLX.ModDiffClassC`).

`L₁₂` is linear in the profile on the class (`GalFields.RHS.L12_sub_eq_of_smoothOpen`), so the
difference of the two `L₁₂`-values is the `L₁₂` of the difference of the two `N`-blocks; that
difference is estimated by the `ClassC`-level sharp `N`-difference
(`Work.FTS.StrongEps.EpsRLX.NDiffClassC`, whose `ℋ⁴`-honesty and `ℋ⁴`-bound are the two inputs
here), and `|L₁₂h(0)| ≤ C·|h|_{ℋ⁴}` (`GalBasis.cc.abs_L12_le_HkNorm`).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.ModDiffAux.NBlock

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **`SmoothOpen` and `ℋ⁴`-honesty of the `N`-block at a single class-`C` profile.**

`SmoothOpen` is `ClassCRHS.SmoothOpenRHS`; the `ℋ⁴`-honesty is `ClassCRHS.HkMemXnN`, whose two
size hypotheses `Xn α W ≤ C₀ α²`, `HkNorm α 6 W ≤ B` are satisfied by choosing
`C₀ := Xn α W / α²` and `B := HkNorm α 6 W` (this is why the `K` of `HkMemXnN` is *existential*
and may depend on the profile). -/
theorem smoothOpen_hkMem_N_single {α Ce Cs : ℝ} {Φs : Fn} {E : Fn → Fn} {W : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hW : Work.FTS.ClassC.ClassC α W)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce W (E W))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α (Work.Construction.Ftot α W)
        (fun z θ => Φs z θ + E W z θ)) ∧
      Work.Spaces.HkMem α 4 (Work.Construction.N α (Work.Construction.Ftot α W)
        (fun z θ => Φs z θ + E W z θ)) := by
  refine ⟨(Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα.1 hα.2 hW hell hstar).2.2.2.2, ?_⟩
  obtain ⟨_, _, hbd⟩ := Work.FTS.StrongEps.ClassCRHS.HkMemXnN (α := α) hα
    (C₀ := Work.FTS.Nonlin.Xn α W / α ^ 2) (B := Work.Spaces.HkNorm α 6 W)
    (Ce := Ce) (Cs := Cs) (Φs := Φs)
  refine (hbd hW ?_ le_rfl hell hstar).1
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt hα.1))]

/-- **The `L₁₂`-zero-mode difference of the `N`-term, on the class `C`** — the `N`-component of
the difference of the two modulation constants. -/
theorem L12NDiffClassC {α Ce Cs : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₁)
          (fun z θ => Φs z θ + E W₁ z θ)) 0
        - Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α W₂)
          (fun z θ => Φs z θ + E W₂ z θ)) 0|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
  obtain ⟨K₁, hK₁pos, hK₁⟩ := Work.FTS.StrongEps.EpsRLX.NDiffClassC (α := α)
    (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E) hα hEll hstar
  refine ⟨C * K₁ + 2, by positivity, ?_⟩
  intro W₁ W₂ hW₁ hW₂
  obtain ⟨hsm₁, hmem₁⟩ := smoothOpen_hkMem_N_single hα hW₁ (hEll W₁ hW₁).1 hstar
  obtain ⟨hsm₂, hmem₂⟩ := smoothOpen_hkMem_N_single hα hW₂ (hEll W₂ hW₂).1 hstar
  obtain ⟨hDsm, hDmem, hDXn⟩ := hK₁ hW₁ hW₂
  -- the right-hand side is nonnegative
  have hY₁ : 0 ≤ Work.FTS.GalFields.Xn5 α W₁ := Work.Spaces.HkNorm_nonneg α 5 W₁
  have hY₂ : 0 ≤ Work.FTS.GalFields.Xn5 α W₂ := Work.Spaces.HkNorm_nonneg α 5 W₂
  have hYh : 0 ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.Spaces.HkNorm_nonneg α 5 _
  have hAB : (0 : ℝ) ≤ (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
      * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    mul_nonneg (by linarith) hYh
  -- linearity of `L₁₂` in the profile
  have hlin := Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen
    (a := Work.Construction.N α (Work.Construction.Ftot α W₁)
      (fun z θ => Φs z θ + E W₁ z θ))
    (b := Work.Construction.N α (Work.Construction.Ftot α W₂)
      (fun z θ => Φs z θ + E W₂ z θ))
    hsm₁ hsm₂ hmem₁ hmem₂ 0 le_rfl
  rw [hlin]
  have hDXn' : Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ) z θ
          - Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ) z θ)
      ≤ K₁ * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) := by
    have h : K₁ * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))
        = K₁ * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by ring
    rw [h]; exact hDXn
  calc |Work.Construction.L12 (fun z θ =>
        Work.Construction.N α (Work.Construction.Ftot α W₁)
            (fun z θ => Φs z θ + E W₁ z θ) z θ
          - Work.Construction.N α (Work.Construction.Ftot α W₂)
            (fun z θ => Φs z θ + E W₂ z θ) z θ) 0|
      ≤ C * Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N α (Work.Construction.Ftot α W₁)
              (fun z θ => Φs z θ + E W₁ z θ) z θ
            - Work.Construction.N α (Work.Construction.Ftot α W₂)
              (fun z θ => Φs z θ + E W₂ z θ) z θ) := hC α _ hDmem
    _ ≤ C * (K₁ * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))) :=
        mul_le_mul_of_nonneg_left hDXn' (le_of_lt hCpos)
    _ ≤ (C * K₁ + 2) * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) := by
        have h1 : C * (K₁ * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)))
            = (C * K₁) * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
              * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right (by linarith [hCpos, hK₁pos]) hAB
    _ = (C * K₁ + 2) * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by ring

end Work.FTS.StrongEps.EpsRLX.ModDiffAux.NBlock
