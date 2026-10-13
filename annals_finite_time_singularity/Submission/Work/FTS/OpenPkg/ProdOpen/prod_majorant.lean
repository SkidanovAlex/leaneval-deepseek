import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.ProdOpen.Tools1d
import Submission.Work.FTS.OpenPkg.ProdOpen.SlicesOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.PwOpen
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.OpenPkg.ProdOpen.ProdDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.z_sum_bound
import Submission.Work.FTS.OpenPkg.ProdOpen.m_sum_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.OpenPkg.ProdOpen

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Work.Spaces

theorem prod_majorant : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * g z θ) z θ
        ≤ K / (Work.Spaces.gam α - 1)
            * (Work.Spaces.HkSq α 4 f * Work.Spaces.HkIntegrand α 4 g z θ
              + Work.Spaces.HkSq α 4 g * Work.Spaces.HkIntegrand α 4 f z θ)
          + K * ((Work.Spaces.DzIter 3 f z θ * Work.Spaces.Dth g z θ) ^ 2
              + (Work.Spaces.Dth f z θ * Work.Spaces.DzIter 3 g z θ) ^ 2)
            * (Work.Spaces.Wt α z θ) ^ 2 := by
  obtain ⟨CZ, hCZpos, hZ⟩ := z_sum_bound
  obtain ⟨CM, hCMpos, hM⟩ := m_sum_bound
  refine ⟨5 * CZ + 25 * CM + 1, by positivity, ?_⟩
  intro α f g hα hα1 hF hmemF hG hmemG z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hRnn : 0 ≤ Maj α f g z θ := Maj_nonneg hα f g z θ
  have hZsum : ∑ i ∈ Finset.range 5, (DzIter i (fun z θ => f z θ * g z θ) z θ
        * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 ≤ 5 * (CZ * Maj α f g z θ) := by
    calc ∑ i ∈ Finset.range 5, (DzIter i (fun z θ => f z θ * g z θ) z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ ∑ i ∈ Finset.range 5, (CZ * Maj α f g z θ) :=
          Finset.sum_le_sum (fun i hi => hZ α f g hα hα1 hF hmemF hG hmemG i
            (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) z θ hz hθ0 hθ1)
      _ = 5 * (CZ * Maj α f g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  have hMsum : ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ 25 * (CM * Maj α f g z θ) := by
    have hper : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ CM * Maj α f g z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · rw [if_pos hc]
        exact hM α f g hα hα1 hF hmemF hG hmemG i j hc.1 hc.2 z θ hz hθ0 hθ1
      · rw [if_neg hc]
        exact mul_nonneg hCMpos.le hRnn
    calc ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (mixed j i (fun z θ => f z θ * g z θ) z θ * Wt α z θ) ^ 2 else 0)
        ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (CM * Maj α f g z θ) :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hper i hi j hj))
      _ = 25 * (CM * Maj α f g z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hcomb : 5 * (CZ * Maj α f g z θ) + 25 * (CM * Maj α f g z θ)
      ≤ (5 * CZ + 25 * CM + 1) * Maj α f g z θ := by nlinarith [hRnn]
  rw [HkIntegrand]
  refine le_trans (add_le_add hZsum hMsum) (le_trans hcomb (le_of_eq ?_))
  rw [Maj, SInv, Texc, div_eq_mul_inv]
  ring

end Work.FTS.OpenPkg.ProdOpen
