/-
# `Work.FTS.StrongPersist.N6.Majorant6`

The **pointwise majorant** of the level-six product rule: the level-six shift of
`Work.FTS.OpenPkg.ProdOpen.prod_majorant`.

Given `SmoothOpen f`, `HkMem α 6 f`, `SmoothOpen g`, `HkMem α 6 g` and `(z,θ)` in the open
quadrant, the level-six integrand of the product is dominated by

  `K/(γ-1)·(|f|²_{ℋ⁶} I⁶_g + |g|²_{ℋ⁶} I⁶_f) + K·((D_z⁵f·D_θg)² + (D_θf·D_z⁵g)²)·W²`,

where `I⁶_f` is the level-six integrand `HkIntegrand α 6 f`.  The two ingredients are the
level-six slot bounds `z_sum_bound6` (pure `D_z`-slots) and `m_sum_bound6` (mixed slots), which
are proved elsewhere.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6.ProdDefs6
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.StrongPersist.N6.z_sum_bound6
import Submission.Work.FTS.StrongPersist.N6.m_sum_bound6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

theorem prod_majorant6 : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → HkMem α 6 f →
    Work.FTS.EllipticEst.SmoothOpen g → HkMem α 6 g →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HkIntegrand α 6 (fun z θ => f z θ * g z θ) z θ
        ≤ K / (gam α - 1)
            * (HkSq α 6 f * HkIntegrand α 6 g z θ
              + HkSq α 6 g * HkIntegrand α 6 f z θ)
          + K * ((DzIter 5 f z θ * Dth g z θ) ^ 2
              + (Dth f z θ * DzIter 5 g z θ) ^ 2)
            * (Wt α z θ) ^ 2 := by
  obtain ⟨CZ, hCZpos, hZ⟩ := z_sum_bound6
  obtain ⟨CM, hCMpos, hM⟩ := m_sum_bound6
  refine ⟨7 * CZ + 49 * CM + 1, by positivity, ?_⟩
  intro α f g hα hα1 hF hmemF hG hmemG z θ hz hθ0 hθ1
  have hRnn : 0 ≤ Maj6 α f g z θ := Maj6_nonneg hα f g z θ
  have hZsum : ∑ i ∈ Finset.range 7, (DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 ≤ 7 * (CZ * Maj6 α f g z θ) := by
    calc ∑ i ∈ Finset.range 7, (DzIter i (fun z θ => f z θ * g z θ) z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ ∑ i ∈ Finset.range 7, (CZ * Maj6 α f g z θ) :=
          Finset.sum_le_sum (fun i hi => hZ α f g hα hα1 hF hmemF hG hmemG i
            (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) z θ hz hθ0 hθ1)
      _ = 7 * (CZ * Maj6 α f g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hMsum : ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ 49 * (CM * Maj6 α f g z θ) := by
    have hper : ∀ i ∈ Finset.range 7, ∀ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ CM * Maj6 α f g z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 6
      · rw [if_pos hc]
        exact hM α f g hα hα1 hF hmemF hG hmemG i j hc.1 hc.2 z θ hz hθ0 hθ1
      · rw [if_neg hc]
        exact mul_nonneg hCMpos.le hRnn
    calc ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7, (CM * Maj6 α f g z θ) :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hper i hi j hj))
      _ = 49 * (CM * Maj6 α f g z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hcomb : 7 * (CZ * Maj6 α f g z θ) + 49 * (CM * Maj6 α f g z θ)
      ≤ (7 * CZ + 49 * CM + 1) * Maj6 α f g z θ := by nlinarith [hRnn]
  rw [HkIntegrand]
  refine le_trans (add_le_add hZsum hMsum) (le_trans hcomb (le_of_eq ?_))
  rw [Maj6, SInv6, Texc6, div_eq_mul_inv]
  ring

end Work.FTS.StrongPersist.N6
