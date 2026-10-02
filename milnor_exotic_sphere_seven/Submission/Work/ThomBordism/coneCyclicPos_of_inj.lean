import Mathlib
import Submission.Work.ThomBordism.chainSetup_cone

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open Work.TangentClasses Work.Cohomology

namespace Work.ThomBordism

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type}

/-- `totShiftD` vanishes on `0`. -/
theorem totShiftD_zero (Z : RealBundle B F ι) (n : ℕ) (W : Set B) (m : ℕ) :
    totShiftD Z n W m (0 : TotC Z W (m + n)) = 0 :=
  map_zero _

/-- **Cyclicity at `m` from injectivity of `ψ` at `m + 1`.**

Given that every cone-`(m+1)`-cycle `(a, b)` has its base component `a` a coboundary, the cone is
cyclic at degree `m + 1`: every such cycle differs from a cycle of the form `(0, b')` by a boundary.

Indeed, if `d a' = -a` then `q := (a', 0)` has `coneD m q = (a, ψ a')`, so
`(a, b) = (0, b - ψ a') + coneD m q`; and the second component `b - ψ a'` is a `Tot`-cycle because
`d(ψ a') = ψ(d a') = -ψ a = tD b`, the last equality being the second component of the cycle
condition on `(a, b)`. -/
theorem coneCyclicPos_of_inj {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U) (m : ℕ)
    (hinj : ∀ (a : Work.ThomBordism.BaseC W ((m + 1) + 1))
      (b : Work.ThomBordism.TotC Z W ((m + 1) + n)),
      Work.ThomBordism.ConeCycle Z n U τ W hW (m + 1) (a, b) →
        ∃ a' : Work.ThomBordism.BaseC W (m + 1),
          Work.Cohomology.cochainDiffLM ℤ (Work.ThomBordism.baseSSet W) (m + 1) a' = -a)
    {a : Work.ThomBordism.BaseC W ((m + 1) + 1)} {b : Work.ThomBordism.TotC Z W ((m + 1) + n)}
    (hcyc : Work.ThomBordism.ConeCycle Z n U τ W hW (m + 1) (a, b)) :
    ∃ (q : Work.ThomBordism.ConeC Z n W m) (b' : Work.ThomBordism.TotC Z W ((m + 1) + n)),
      Work.ThomBordism.ConeCycle Z n U τ W hW (m + 1) (0, b') ∧
      (a, b) = (0, b') + Work.ThomBordism.coneD Z n U τ W hW m q := by
  obtain ⟨a', ha'⟩ := hinj a b hcyc
  have hsnd := coneCycle_snd Z n U τ W hW m hcyc
  refine ⟨(a', (0 : TotC Z W (m + n))),
    b - psiAbsLM Z n U τ W hW (m + 1) a', ?_, ?_⟩
  · -- the second component is a `Tot`-cycle
    have hψ : totShiftD Z n W (m + 1) (psiAbsLM Z n U τ W hW (m + 1) a')
        = - psiAbsLM Z n U τ W hW ((m + 1) + 1) a := by
      have h1 : ((TotComplex Z W).d ((m + 1) + n) (((m + 1) + 1) + n)).hom
          (psiAbs Z n U τ W hW (m + 1) a')
          = psiAbs Z n U τ W hW ((m + 1) + 1)
              (cochainDiffLM ℤ (baseSSet W) (m + 1) a') := by
        rw [psiAbs_diff Z n U τ W hW (m + 1) a']
        rfl
      have h2 : psiAbs Z n U τ W hW ((m + 1) + 1)
            (cochainDiffLM ℤ (baseSSet W) (m + 1) a')
          = - psiAbs Z n U τ W hW ((m + 1) + 1) a := by
        rw [ha']
        exact map_neg (psiAbsLM Z n U τ W hW ((m + 1) + 1)) a
      show ((TotComplex Z W).d ((m + 1) + n) (((m + 1) + 1) + n)).hom
          (psiAbs Z n U τ W hW (m + 1) a')
        = - psiAbs Z n U τ W hW ((m + 1) + 1) a
      rw [h1, h2]
    have hzero : totShiftD Z n W (m + 1) b - -psiAbsLM Z n U τ W hW ((m + 1) + 1) a = 0 := by
      rw [sub_neg_eq_add]
      exact (add_comm (totShiftD Z n W (m + 1) b)
        (psiAbsLM Z n U τ W hW ((m + 1) + 1) a)).trans hsnd
    show coneD Z n U τ W hW (m + 1)
        (((0 : BaseC W ((m + 1) + 1)), b - psiAbsLM Z n U τ W hW (m + 1) a')) = 0
    rw [coneD_apply]
    rw [map_zero, map_zero, neg_zero, zero_add, totShiftD_sub, hψ, hzero]
    rfl
  · -- the splitting
    rw [coneD_apply]
    rw [Prod.mk_add_mk, Prod.mk.injEq]
    constructor
    · rw [ha', neg_neg, zero_add]
    · rw [totShiftD_zero, add_zero]
      exact (sub_add_cancel b (psiAbsLM Z n U τ W hW (m + 1) a')).symm

end

end Work.ThomBordism
