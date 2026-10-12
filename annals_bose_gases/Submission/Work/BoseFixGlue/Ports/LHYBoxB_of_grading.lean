import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixGlue.Ports.Small
import Submission.Work.BoseKinLoc.Sector.boxFormB_eq_zero_of_eq_zero_on_abox
import Submission.Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Ports.LHYBoxB_of_grading`

The port of the proved BoseBox assembly
(`Work.BoseBox.boxBound_of_grading` + `Work.BoseBox.LHYBox_of_grading`) to the frozen
`Work.BoseBoxFix` vocabulary: the §6 grading node `NodeB2gB` together with the §7–§11
restricted-class node `NodeRestrictedB` at the a-priori parameter `J'` give FS `thm:LHY-Box`
(`LHYBoxB`) at the error coefficient raised by one, for every `lhyC ≤ J < J'` and
`0 ≤ η₀ < 2/323`.

Contents:

* `boxBoundB_of_grading` — the per-state heart: `NodeB2gB` + `NodeRestrictedB` at `J'` give the
  box bound `ℓ³Λ(a v, C+1, η₀, μ)‖Φ‖² ≤ wordB Φ` for every *low* state (`IsLowB` at `J`) with
  positive boxed norm.  The Lieb–Solovej loss of the replacement is the first unit of `Λ`'s error
  coefficient (`Work.BoseBox.exists_lsError_le_slack`), and the threshold guard `J' ≤ K_B³`
  follows from `μ(a v)³ ≤ J'^{-323/18}` (`Work.BoseBox.KB_cube_ge`).
* `boxBoundB_of_normB_eq_zero_aux` — the degenerate case `normB = 0`: such a state vanishes on
  `abox` (`eq_zero_on_abox_of_sqNormB_eq_zero`) and hence has `wordB = 0`
  (`boxFormB_eq_zero_of_eq_zero_on_abox`), so the box bound is `0 ≤ 0`.
* `LHYBoxB_of_grading` — the assembly: the `B0` dichotomy
  (`Work.BoseFixGlue.nodeB0B_dichotomy`, i.e. `Λ ≤ Θ`) splits every box state into the low class
  (handled by the grading + the restricted bound) and the class already satisfying the box bound;
  the degenerate states are handled by the previous lemma.  This is a verbatim port of
  `Work.BoseBox.LHYBox_of_grading`, with the extra zero-norm case.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixGlue.Ports

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The grading node plus the restricted bound give the box bound -/

/-- **`B2` composed with `NodeRestrictedB`** (port of `Work.BoseBox.boxBound_of_grading`): the
replacement state of `NodeB2gB` is restricted (`n₊ ≤ 𝓜`) and low at `J'`, so `NodeRestrictedB`
applies to it, and the Lieb–Solovej error is absorbed by raising the target's error coefficient
from `C` to `C + 1`.  The result is the box bound for all low states with positive boxed norm at
the hypothesis threshold `J`. -/
theorem boxBoundB_of_grading {v : ℝ³ → ℝ} {h : ScatSol v} {J J' η₀ C : ℝ}
    (hav : 0 < a v) (hC : 0 ≤ C) (hη₀ : 0 ≤ η₀) (hη₂ : η₀ < 2 / 323) (hJ'pos : 0 < J')
    (hg : NodeB2gB v h J J') (hr : NodeRestrictedB v h J' η₀ C) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        0 < normB v μ n Φ → IsLowB v h J μ n Φ → BoxBoundB v h η₀ (C + 1) μ n Φ := by
  obtain ⟨K, ε₁, hK0, hε₁, hg'⟩ := hg
  obtain ⟨ε₂, hε₂, habs⟩ :=
    Work.BoseBox.exists_lsError_le_slack (a := a v) hav hη₀ hη₂ hK0
  obtain ⟨ε₄, hε₄, hr'⟩ := hr
  refine ⟨min (J' ^ (-(323 / 18 : ℝ))) (min ε₁ (min ε₂ (min 1 ε₄))),
    lt_min (Real.rpow_pos_of_pos hJ'pos _)
      (lt_min hε₁ (lt_min hε₂ (lt_min one_pos hε₄))), ?_⟩
  intro μ hAdm n Φ hnorm hlow
  obtain ⟨hμ, hle, hpar⟩ := hAdm
  have ht0 : μ * (a v) ^ 3 ≤ J' ^ (-(323 / 18 : ℝ)) := le_trans hle (min_le_left _ _)
  have ht1 : μ * (a v) ^ 3 ≤ ε₁ :=
    le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht2 : μ * (a v) ^ 3 ≤ ε₂ :=
    le_trans hle (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have ht3 : μ * (a v) ^ 3 ≤ 1 :=
    le_trans hle (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have ht4 : μ * (a v) ^ 3 ≤ ε₄ :=
    le_trans hle (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  obtain ⟨Φ', hlow', hnorm', hword', hplus'⟩ := hg' μ ⟨hμ, ht1, hpar⟩ n Φ hnorm hlow
  have hguardJ' : J' ≤ (paramsAt μ (a v)).KB ^ 3 :=
    Work.BoseBox.KB_cube_ge hμ hav hJ'pos ht0
  have hrestr : BoxBoundB v h η₀ C μ n Φ' :=
    hr' μ ⟨hμ, ht4, hpar⟩ hguardJ' n Φ' hlow' hplus'
  have hN : 0 ≤ normB v μ n Φ := normB_nonneg v μ n Φ
  have hℓ3 : 0 ≤ sideAt μ (a v) ^ 3 := pow_nonneg (sideB_pos hμ hav).le 3
  -- the absorption: the Lieb–Solovej loss is at most one unit of the target's error
  have herr : K * μ ^ 2 * sideAt μ (a v) ^ 3
        / bigM (paramsAt μ (a v)) (a v) μ ^ 2 * normB v μ n Φ
      ≤ 4 * π * (a v) * μ ^ 2 * sideAt μ (a v) ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 + η₀)
        * normB v μ n Φ := by
    have h1 : K / bigM (paramsAt μ (a v)) (a v) μ ^ 2
        ≤ 4 * π * (a v) * (μ * (a v) ^ 3) ^ (1 / 2 + η₀) := habs μ hμ ht2
    have hstep : K * μ ^ 2 * sideAt μ (a v) ^ 3
          / bigM (paramsAt μ (a v)) (a v) μ ^ 2 * normB v μ n Φ
        = (K / bigM (paramsAt μ (a v)) (a v) μ ^ 2)
          * (μ ^ 2 * sideAt μ (a v) ^ 3 * normB v μ n Φ) := by
      ring
    have hstep2 : 4 * π * (a v) * (μ * (a v) ^ 3) ^ (1 / 2 + η₀)
          * (μ ^ 2 * sideAt μ (a v) ^ 3 * normB v μ n Φ)
        = 4 * π * (a v) * μ ^ 2 * sideAt μ (a v) ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 + η₀)
          * normB v μ n Φ := by
      ring
    rw [hstep, ← hstep2]
    exact mul_le_mul_of_nonneg_right h1 (mul_nonneg (mul_nonneg (sq_nonneg μ) hℓ3) hN)
  -- the constant shift
  have hshift : Lambda (a v) (C + 1) η₀ μ
      = Lambda (a v) C η₀ μ - 4 * π * μ ^ 2 * (a v) * (μ * (a v) ^ 3) ^ (1 / 2 + η₀) :=
    Work.BoseBox.Lambda_add_one _ _ _ _
  rw [BoxBoundB]
  have hbase : sideAt μ (a v) ^ 3 * Lambda (a v) C η₀ μ * normB v μ n Φ'
      ≤ wordB v h μ n Φ' := hrestr
  rw [hnorm'] at hbase
  rw [hshift]
  nlinarith [hbase, hword', herr, hN]

/-! ## 2. The degenerate case -/

/-- **A box state of vanishing boxed norm satisfies the box bound for every error coefficient.**
`normB = 0` means `∫_{abox} Φ² = 0`, i.e. `Φ` vanishes pointwise on the box
(`eq_zero_on_abox_of_sqNormB_eq_zero`); then `wordB Φ = boxFormB … Φ = 0`
(`boxFormB_eq_zero_of_eq_zero_on_abox`) and the box bound reduces to `0 ≤ 0`. -/
theorem boxBoundB_of_normB_eq_zero_aux {v : ℝ³ → ℝ} {h : ScatSol v}
    {η₀ C μ : ℝ} (hℓ : 0 < sideAt μ (a v)) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v)))
    (h0 : normB v μ n Φ = 0) : BoxBoundB v h η₀ C μ n Φ := by
  have hsq : Work.BoseKinLoc.sqNormB n (sideAt μ (a v)) (Φ : X n → ℝ) = 0 := h0
  have hz : ∀ x ∈ abox n (sideAt μ (a v)), (Φ : X n → ℝ) x = 0 :=
    Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero hℓ Φ.contDiff.continuous hsq
  have hword : wordB v h μ n Φ = 0 := by
    rw [Work.BoseFixGlue.wordB_eq v h μ n (Φ : X n → ℝ)]
    exact Work.BoseKinLoc.Sector.boxFormB_eq_zero_of_eq_zero_on_abox hℓ hz
  rw [BoxBoundB, hword, h0]
  simp

/-! ## 3. The assembly -/

theorem LHYBoxB_of_grading {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {J J' η₀ C : ℝ} (hlhy : Work.UBB.lhyC ≤ J) (hav : 0 < BoseGases.a v) (hC : 0 ≤ C)
    (hη₀ : 0 ≤ η₀) (hη₂ : η₀ < 2 / 323) (hJJ : J < J')
    (hg : Work.BoseBoxFix.NodeB2gB v h J J')
    (hr : Work.BoseBoxFix.NodeRestrictedB v h J' η₀ C) :
    Work.BoseBoxFix.LHYBoxB v h η₀ (C + 1) := by
  have hJ'pos : 0 < J' := lt_trans Work.UBB.lhyC_pos (lt_of_le_of_lt hlhy hJJ)
  obtain ⟨ε₀, hε₀, hbb⟩ := boxBoundB_of_grading hav hC hη₀ hη₂ hJ'pos hg hr
  have hC1 : 0 ≤ C + 1 := by linarith
  refine ⟨min ε₀ 1, lt_min hε₀ one_pos, ?_⟩
  intro μ hAdm n Φ
  have hAdm₁ : Adm v ε₀ μ := ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hℓ : 0 < sideAt μ (BoseGases.a v) := sideB_pos hAdm.1 hav
  rcases Work.BoseFixGlue.nodeB0B_dichotomy (v := v) (h := h) (J := J) (η₀ := η₀)
      (C := C + 1) (μ := μ) hlhy hC1 hη₀ hAdm.1 hav Φ with hlow | hbox
  · by_cases hnorm : 0 < normB v μ n Φ
    · exact hbb μ hAdm₁ n Φ hnorm hlow
    · exact boxBoundB_of_normB_eq_zero_aux hℓ Φ
        (le_antisymm (le_of_not_gt hnorm) (normB_nonneg v μ n Φ))
  · exact hbox

end Work.BoseFixGlue.Ports
