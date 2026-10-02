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
variable {ι : Type} (Z : RealBundle B F ι)

/-- `totDpred` vanishes on `0` (it is a differential of `TotComplex`). -/
theorem totDpred_zero (n : ℕ) (W : Set B) :
    totDpred Z n W (0 : TotC Z W (n - 1)) = 0 := by
  show ((TotComplex Z W).d (n - 1) (0 + n)).hom (0 : TotC Z W (n - 1)) = 0
  rw [map_zero]

/-- **First component of the cone-cycle condition at degree `0`.**

A cone-`0`-cycle `(a, b)` has `a` a cycle of the base complex.  This is the degree-`0` analogue of
`coneCycle_fst`, proved by the same component extraction (which avoids re-spelling the argument of
`cochainDiffLM`, cf. the header notes of `chainSetup_cone`). -/
theorem coneCycleZero_fst (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B)
    (hW : W ⊆ U) {a : BaseC W (0 + 1)} {b : TotC Z W (0 + n)}
    (h : ConeCycle Z n U τ W hW 0 (a, b)) :
    cochainDiffLM ℤ (baseSSet W) (0 + 1) a = 0 := by
  have h2 := congrArg Prod.fst h
  simpa only [coneD_apply, neg_eq_zero, prod_zero_fst] using h2

/-- **Second component of the cone-cycle condition at degree `0`.**

A cone-`0`-cycle `(a, b)` satisfies `ψ a + tD b = 0` in `Tot^n`.  This is the degree-`0` analogue of
`coneCycle_snd`; note that `coneCycle_snd` itself cannot be used here, since it only covers the
*positive* degrees `m + 1`. -/
theorem coneCycleZero_snd (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B)
    (hW : W ⊆ U) {a : BaseC W (0 + 1)} {b : TotC Z W (0 + n)}
    (h : ConeCycle Z n U τ W hW 0 (a, b)) :
    psiAbsLM Z n U τ W hW (0 + 1) a + totShiftD Z n W 0 b = 0 := by
  have h2 := congrArg Prod.snd h
  simpa only [coneD_apply, prod_zero_snd] using h2

/-- **The `ψ`-image of a primitive of `a` has the expected `Tot`-differential.**

If `d a' = -a` (with `a' ∈ Base^0`), then `tD (ψ a') = -ψ a`: this is the cochain-map property
`psiAbs_diff` at degree `0` combined with the linearity of `ψ`.  It is the degree-`0` analogue of the
`hψ` step in `coneCyclicPos_of_inj`. -/
theorem totShiftD_psi_zero (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B)
    (hW : W ⊆ U) {a : BaseC W (0 + 1)} {a' : BaseC W 0}
    (ha' : cochainDiffLM ℤ (baseSSet W) 0 a' = -a) :
    totShiftD Z n W 0 (psiAbsLM Z n U τ W hW 0 a')
      = - psiAbsLM Z n U τ W hW (0 + 1) a := by
  have hca : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of ↥W)) a' = -a := ha'
  show ((TotComplex Z W).d (0 + n) ((0 + 1) + n)).hom (psiAbs Z n U τ W hW 0 a')
      = - psiAbs Z n U τ W hW (0 + 1) a
  rw [psiAbs_diff Z n U τ W hW 0 a', hca]
  exact map_neg (psiAbsLM Z n U τ W hW (0 + 1)) a

/-- **Cyclicity of the cone at degree `0` from injectivity and surjectivity of `ψ` in degree `1`.**

This is the degree-`0` twin of `Work.ThomBordism.coneCyclicPos_of_inj_surj`, in the indexing in
which the primitives live one degree below `ConeC 0`, in the **Extra** term
`ExtraC = Base^0 ⊕ Tot^{n-1}`.

Given a cone-`0`-cycle `(a, b)`, `hinj` supplies `a' ∈ Base^0` with `d a' = -a`; then
`extraD (a', 0) = (a, ψ a')`, and the remainder `b - ψ a'` is a `Tot`-cycle (`totShiftD_psi_zero`
for the `ψ a'` half, the second component of the cycle condition for the `b` half).  Hence `hsurj`
splits `(0, b - ψ a') = extraD q'`, and additivity of `extraD` (proved in `chainSetup_cone`)
combines the two primitives into `extraD ((a',0) + q') = (a, b)`. -/
theorem coneCyclicZero_of_inj_surj {B : Type} [TopologicalSpace B] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} (Z : Work.TangentClasses.RealBundle B F ι)
    (n : ℕ) (U : Set B) (τ : Work.Thom.PieceCoh Z U n) (W : Set B) (hW : W ⊆ U)
    (hinj : ∀ (a : Work.ThomBordism.BaseC W (0 + 1)) (b : Work.ThomBordism.TotC Z W (0 + n)),
      Work.ThomBordism.ConeCycle Z n U τ W hW 0 (a, b) →
        ∃ a' : Work.ThomBordism.BaseC W 0,
          Work.Cohomology.cochainDiffLM ℤ (Work.ThomBordism.baseSSet W) 0 a' = -a)
    (hsurj : ∀ b : Work.ThomBordism.TotC Z W (0 + n),
      Work.ThomBordism.totShiftD Z n W 0 b = 0 →
        ∃ q : Work.ThomBordism.ExtraC Z n W,
          Work.ThomBordism.extraD Z n U τ W hW q = (0, b)) :
    Work.ThomBordism.ConeCyclicZero Z n U τ W hW := by
  intro p hp
  obtain ⟨a, b⟩ := p
  -- the two halves of the isomorphism at degree `1`
  obtain ⟨a', ha'⟩ := hinj a b hp
  have hsnd := coneCycleZero_snd Z n U τ W hW hp
  -- `b - ψ a'` is a `Tot`-cycle
  have hb' : totShiftD Z n W 0 (b - psiAbsLM Z n U τ W hW 0 a') = 0 := by
    rw [totShiftD_sub, totShiftD_psi_zero Z n U τ W hW ha', sub_neg_eq_add]
    exact (add_comm _ _).trans hsnd
  obtain ⟨q', hq'⟩ := hsurj (b - psiAbsLM Z n U τ W hW 0 a') hb'
  -- the primitive supplied by the injectivity step
  have he : extraD Z n U τ W hW (a', (0 : TotC Z W (n - 1)))
      = (a, psiAbsLM Z n U τ W hW 0 a') := by
    show (-(cochainDiffLM ℤ (baseSSet W) 0 a'),
        psiAbsLM Z n U τ W hW 0 a' + totDpred Z n W (0 : TotC Z W (n - 1)))
      = (a, psiAbsLM Z n U τ W hW 0 a')
    rw [ha', neg_neg, totDpred_zero Z n W, add_zero]
  -- combine the two primitives by additivity of `extraD`
  refine ⟨(a', (0 : TotC Z W (n - 1))) + q', ?_⟩
  rw [extraD_add, hq', he, Prod.mk_add_mk]
  simp only [Prod.mk.injEq]
  exact ⟨add_zero a, add_sub_cancel _ _⟩

end

end Work.ThomBordism
