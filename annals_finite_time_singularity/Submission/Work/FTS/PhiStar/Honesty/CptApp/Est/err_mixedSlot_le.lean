import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.MixedSlotMoment
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.cutCoeff_omegaInd
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.cutCoeff_thShrink
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.err_expansion

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The mixed slot of the error against `Good`.**

For every `k` there is a universal constant `C > 0` such that for every `0 < α ≤ 1`, every
`n ≥ 3`, every `F` smooth on the open quadrant and every `i ≥ 1`, `i + j ≤ k`,

  `(D_z^j D_θ^i (err n F) · W)^2 ≤ C · Good α k n F`

at every point of the half-strip `[0,∞) × [0,π/2]`.

Route: split `err n F = (χζ - 1)·F - μ·ρ`; expand the mixed jet of the first product by the
two-operator Leibniz rule (`err_expansion`), bound each of the `(b,a)`-terms by `Base · Good`
(`ems_core_le`, with the coefficient bounds `cutCoeff_omegaInd` / `cutCoeff_thShrink` obtained
from the uniform-in-`n` cutoff estimates and the plateau vanishing), bound the moment term
`D_z^j μ · D_θ^i ρ` by the third group of `Good` (`ems_moment_sq_le`), and combine with
`(x - y)² ≤ 2x² + 2y²`; the boundary cases where `Wt` vanishes are trivial. -/
theorem err_mixedSlot_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 → 3 ≤ n →
      Work.FTS.EllipticEst.SmoothOpen F →
      ∀ (i j : ℕ), 1 ≤ i → i + j ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        (Work.Spaces.mixed j i (Work.FTS.PhiStar.Honesty.CptApp.err n F) z θ
            * Work.Spaces.Wt α z θ) ^ 2
          ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  obtain ⟨K, hKnn, hKb⟩ := Work.FTS.PhiStar.Honesty.CptApp.LamAux.chiR_dzIter_boundAux
  obtain ⟨L, hLnn, hLb⟩ := Work.FTS.PhiStar.Honesty.CptApp.EstAux.estZetaBound
  obtain ⟨hpz, hpθ⟩ := Work.FTS.PhiStar.Honesty.CptApp.EstAux.estPlateauZero
  have hpz' : ∀ (N b : ℕ) (z : ℝ), 2 ≤ N → 1 ≤ b → 2 / (N : ℝ) ≤ z → z ≤ (N : ℝ) →
      Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR N z) z 0 = 0 :=
    fun N b z hN hb h1 h2 => hpz N hN b hb z h1 h2
  have hpθ' : ∀ (N a : ℕ) (θ : ℝ), 2 ≤ N → 1 ≤ a → 2 / (N : ℝ) ≤ θ →
      θ ≤ Real.pi / 2 - 2 / (N : ℝ) →
      Work.Spaces.DthIter a (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR N θ) 0 θ = 0 :=
    fun N a θ hN ha h1 h2 => hpθ N hN a ha θ h1 h2
  set Ks : ℝ := ∑ b ∈ Finset.range (k + 1), K b with hKsdef
  set Ls : ℝ := ∑ a ∈ Finset.range (k + 1), L a with hLsdef
  have hKs0 : 0 ≤ Ks := by
    rw [hKsdef]; exact Finset.sum_nonneg fun b _ => hKnn b
  have hLs0 : 0 ≤ Ls := by
    rw [hLsdef]; exact Finset.sum_nonneg fun a _ => hLnn a
  have hKle : ∀ b ≤ k, K b ≤ Ks := by
    intro b hb
    rw [hKsdef]
    exact Finset.single_le_sum (f := K) (fun i _ => hKnn i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hb))
  have hLle : ∀ a ≤ k, L a ≤ Ls := by
    intro a ha
    rw [hLsdef]
    exact Finset.single_le_sum (f := L) (fun i _ => hLnn i)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))
  set Base : ℝ := (1 + Ks ^ 2) * (1 + Ls ^ 2) with hBasedef
  have hBase : 1 ≤ Base := by
    rw [hBasedef]
    nlinarith [hKs0, hLs0]
  have hCoeffInd : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a + b → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ := by
    intro n a b hn hab hak hbk z θ
    refine le_trans (Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.cutCoeff_omegaInd
      K L hKb hLb hpz' hpθ' n a b hn hab z θ) ?_
    refine mul_le_mul_of_nonneg_right ?_
      (Work.FTS.PhiStar.Honesty.CptApp.omegaInd_nonneg n z θ)
    rw [hBasedef]
    exact mul_le_mul (by nlinarith [hKle b hbk, hKnn b, hKs0])
      (by nlinarith [hLle a hak, hLnn a, hLs0]) (by positivity) (by positivity)
  have hCoeffTs : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ := by
    intro n a b hn ha hak hbk z θ
    refine le_trans (Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.cutCoeff_thShrink
      K L hKb hLb hpθ' n a b hn ha z θ) ?_
    refine mul_le_mul_of_nonneg_right ?_
      (Work.FTS.PhiStar.Honesty.CptApp.thShrink_nonneg n θ)
    rw [hBasedef]
    exact mul_le_mul (by nlinarith [hKle b hbk, hKnn b, hKs0])
      (by nlinarith [hLle a hak, hLnn a, hLs0]) (by positivity) (by positivity)
  exact ems_final_of k Base hBase hCoeffInd hCoeffTs
    (fun n hn F hF j i z θ hz hθ0 hθ1 =>
      Work.FTS.PhiStar.Honesty.CptApp.Est.Pieces.err_expansion n hn hF j i z θ hz hθ0 hθ1)

end Work.FTS.PhiStar.Honesty.CptApp.Est
