import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Have
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.GamSeqDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gamma_WlInf

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# All `D_θ`-iterates of `Gseq α d` are bounded on `Iθ`, uniformly in `α ∈ (0,1]`

The sequence `Gseq α d` is defined by `Gseq α 0 = q/2` and
`Gseq α (d+1) = D_θ (Gseq α d) + g · Gseq α d`,  `g = gfun α = (α-2)q - 2/3`.

Since `D_θ = sin(2θ)∂_θ` is a vector field it satisfies the Leibniz rule
(`Work.Spaces.dthU_iter_mul`), so an induction on `d` bounds every iterate:
if `|D_θ^m (Gseq α d) θ| ≤ M m` then

  `D_θ^m (Gseq α (d+1)) = D_θ^{m+1}(Gseq α d) + ∑_{i≤m} C(m,i) (D_θ^i g)(D_θ^{m-i}(Gseq α d))`,

and both factors are bounded uniformly in `α ∈ (0,1]`: the first by the induction
hypothesis, the second because `|D_θ^i (gfun α) θ| ≤ gBnd i` for `0 < α ≤ 1` and
`θ ∈ Iθ` (`dthU_gfun_le`).  Mirroring `Work.Spaces.Tfun_iter_bounded`.
-/

open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

set_option autoImplicit false

local notation "C∞" => (⊤ : ℕ∞)

/-- `gfun α` is `C^∞` as a function of `θ`. -/
theorem gfun_smooth (α : ℝ) : ContDiff ℝ C∞ (fun θ => gfun α θ) := by
  have h : (fun θ => gfun α θ)
      = (fun θ : ℝ => (α - 2) * Work.Spaces.qfun θ) - (fun _ : ℝ => 2 / 3) := by
    funext θ
    simp only [gfun, Pi.sub_apply]
  rw [h]
  exact (contDiff_const.mul Work.Spaces.qfun_smooth).sub contDiff_const

theorem Gseq_iter_bounded (d : ℕ) : ∃ M : ℕ → ℝ, (∀ m, 0 ≤ M m) ∧
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → ∀ m : ℕ,
      |Work.Spaces.dthU^[m] (Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gseq α d) θ| ≤ M m := by
  induction d with
  | zero =>
      refine ⟨Work.Spaces.qBound, Work.Spaces.qBound_nonneg, ?_⟩
      intro α hα hα1 θ hθ m
      have h0 : Gseq α 0 = fun θ : ℝ => (1 / 2 : ℝ) * Work.Spaces.qfun θ := by
        funext t; simp only [Gseq_zero]; ring
      calc |Work.Spaces.dthU^[m] (Gseq α 0) θ|
          = |(1 / 2 : ℝ) * Work.Spaces.dthU^[m] Work.Spaces.qfun θ| := by
            rw [h0, Work.Spaces.dthU_iter_const_mul]
        _ = (1 / 2) * |Work.Spaces.dthU^[m] Work.Spaces.qfun θ| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        _ ≤ (1 / 2) * Work.Spaces.qBound m :=
            mul_le_mul_of_nonneg_left (Work.Spaces.dthU_qfun_le_qBound m hθ) (by norm_num)
        _ ≤ Work.Spaces.qBound m := by linarith [Work.Spaces.qBound_nonneg m]
  | succ d ih =>
      obtain ⟨M, hM0, hMb⟩ := ih
      refine ⟨fun m => M (m + 1) + ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * gBnd i * M (m - i), ?_, ?_⟩
      · intro m
        exact add_nonneg (hM0 _) (Finset.sum_nonneg fun i _ =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (gBnd_nonneg i)) (hM0 _))
      · intro α hα hα1 θ hθ m
        have hTeq : Gseq α (d + 1) = Work.Spaces.dthU (Gseq α d)
            + (fun θ => gfun α θ) * (Gseq α d) := Gseq_succ α d
        have hdiff1 : ContDiff ℝ C∞ (Work.Spaces.dthU (Gseq α d)) :=
          Work.Spaces.dthU_smooth (Gseq_smooth α d)
        have hdiff2 : ContDiff ℝ C∞ ((fun θ => gfun α θ) * (Gseq α d)) :=
          (gfun_smooth α).mul (Gseq_smooth α d)
        have hdecomp : Work.Spaces.dthU^[m] (Gseq α (d + 1))
            = Work.Spaces.dthU^[m + 1] (Gseq α d)
              + Work.Spaces.dthU^[m] ((fun θ => gfun α θ) * (Gseq α d)) := by
          rw [hTeq, Work.Spaces.dthU_iter_add m _ _ hdiff1 hdiff2,
            Work.Spaces.dthU_iter_comp]
        have hleib : Work.Spaces.dthU^[m] ((fun θ => gfun α θ) * (Gseq α d))
            = ∑ i ∈ Finset.range (m + 1),
                Work.Spaces.dthCoef m (fun θ => gfun α θ) (Gseq α d) i :=
          Work.Spaces.dthU_iter_mul m _ _ (gfun_smooth α) (Gseq_smooth α d)
        calc |Work.Spaces.dthU^[m] (Gseq α (d + 1)) θ|
            = |Work.Spaces.dthU^[m + 1] (Gseq α d) θ
                + Work.Spaces.dthU^[m] ((fun θ => gfun α θ) * (Gseq α d)) θ| := by
                rw [hdecomp, Pi.add_apply]
          _ ≤ |Work.Spaces.dthU^[m + 1] (Gseq α d) θ|
                + |Work.Spaces.dthU^[m] ((fun θ => gfun α θ) * (Gseq α d)) θ| :=
                abs_add_le _ _
          _ = |Work.Spaces.dthU^[m + 1] (Gseq α d) θ|
                + |∑ i ∈ Finset.range (m + 1),
                    Work.Spaces.dthCoef m (fun θ => gfun α θ) (Gseq α d) i θ| := by
                rw [hleib, Finset.sum_apply]
          _ ≤ M (m + 1) + ∑ i ∈ Finset.range (m + 1),
                (m.choose i : ℝ) * gBnd i * M (m - i) := by
                apply add_le_add
                · exact hMb α hα hα1 θ hθ (m + 1)
                · calc |∑ i ∈ Finset.range (m + 1),
                          Work.Spaces.dthCoef m (fun θ => gfun α θ) (Gseq α d) i θ|
                      ≤ ∑ i ∈ Finset.range (m + 1),
                          |Work.Spaces.dthCoef m (fun θ => gfun α θ) (Gseq α d) i θ| :=
                        Finset.abs_sum_le_sum_abs _ _
                    _ ≤ ∑ i ∈ Finset.range (m + 1),
                          (m.choose i : ℝ) * gBnd i * M (m - i) := by
                        apply Finset.sum_le_sum
                        intro i hi
                        have habs : |Work.Spaces.dthCoef m (fun θ => gfun α θ) (Gseq α d) i θ|
                            = (m.choose i : ℝ)
                              * |Work.Spaces.dthU^[i] (fun θ => gfun α θ) θ|
                              * |Work.Spaces.dthU^[m - i] (Gseq α d) θ| := by
                          rw [Work.Spaces.dthCoef_apply, abs_mul, abs_mul,
                            abs_of_nonneg (Nat.cast_nonneg (m.choose i))]
                          ring
                        rw [habs]
                        exact mul_le_mul
                          (mul_le_mul_of_nonneg_left (dthU_gfun_le α hα hα1 θ hθ i)
                            (Nat.cast_nonneg _))
                          (hMb α hα hα1 θ hθ (m - i)) (abs_nonneg _)
                          (mul_nonneg (Nat.cast_nonneg _) (gBnd_nonneg i))

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
