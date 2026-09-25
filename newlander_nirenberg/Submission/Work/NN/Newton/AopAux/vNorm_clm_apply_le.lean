import Mathlib
import Submission.Work.NN.Newton.pushforward_norms

/-!
# The `vNorm`-bound for the pairing of a `C¹`-operator field with a `C¹`-vector field

`vNorm_clm_apply_le` sums the componentwise estimate `holderNorm_clm_apply_le` over the `n`
components of `ℂⁿ`: a vector `u` of components each bounded by `c` has `vNorm` at most
`n • c = ↑n * c`, and `↑n * (ofReal 8 * X) = ofReal (8 * n) * X`.  The finiteness hypotheses
`mNorm ≠ ⊤` and `vNorm ≠ ⊤` are propagated to the individual component families through
`vNorm_apply_le`, `mNorm_coef_le` and `mNorm_anti_le`.
-/

namespace Work.NN.Newton.AopAux

theorem vNorm_clm_apply_le {n : ℕ} {α : ℝ} {Ω : Set (Work.NN.Core.Cn n)}
    (hΩ : UniqueDiffOn ℝ Ω)
    {T : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {F : Work.NN.Core.Cn n → Work.NN.Core.Cn n}
    (hT : ContDiffOn ℝ 1 T Ω) (hF : ∀ p, ContDiffOn ℝ 1 (fun z => F z p) Ω)
    (hTfin : Work.NN.Newton.mNorm 1 α T Ω ≠ ⊤)
    (hFfin : Work.NN.Newton.vNorm 1 α F Ω ≠ ⊤) :
    Work.NN.Newton.vNorm 1 α (fun z => T z (F z)) Ω
      ≤ ENNReal.ofReal (8 * (n : ℝ)) * (Work.NN.Newton.mNorm 1 α T Ω
        * Work.NN.Newton.vNorm 1 α F Ω) := by
  have hS := Work.NN.Newton.SmoothFun.of_contDiffOn (k := 1) hT
  obtain ⟨hTb1, hTb2, hTc1, hTc2⟩ := hS
  have hcomp : ∀ j : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => (T z (F z)) j) Ω
      ≤ ENNReal.ofReal 8 * (Work.NN.Newton.mNorm 1 α T Ω * Work.NN.Newton.vNorm 1 α F Ω) := by
    intro j
    exact Work.NN.Newton.holderNorm_clm_apply_le hΩ j
      (fun p => hTc1 p j) (fun p => hTc2 p j) hF
      (fun p => ne_top_of_le_ne_top hTfin
        ((Work.NN.Newton.vNorm_apply_le 1 α (fun z => Work.NN.Newton.linCoef (T z) p) Ω j).trans
          (Work.NN.Newton.mNorm_coef_le 1 α T Ω p)))
      (fun p => ne_top_of_le_ne_top hTfin
        ((Work.NN.Newton.vNorm_apply_le 1 α (fun z => Work.NN.Newton.antiCoef (T z) p) Ω j).trans
          (Work.NN.Newton.mNorm_anti_le 1 α T Ω p)))
      (fun p => ne_top_of_le_ne_top hFfin (Work.NN.Newton.vNorm_apply_le 1 α F Ω p))
  have h8 : ((n : ENNReal) * ENNReal.ofReal 8) = ENNReal.ofReal (8 * (n : ℝ)) := by
    rw [mul_comm, ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
  refine (Work.NN.Newton.vNorm_le_sum 1 α (fun z => T z (F z)) Ω _ hcomp).trans (le_of_eq ?_)
  calc ∑ _j : Fin n, ENNReal.ofReal 8
        * (Work.NN.Newton.mNorm 1 α T Ω * Work.NN.Newton.vNorm 1 α F Ω)
      = (n : ENNReal) * (ENNReal.ofReal 8
          * (Work.NN.Newton.mNorm 1 α T Ω * Work.NN.Newton.vNorm 1 α F Ω)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal (8 * (n : ℝ)) * (Work.NN.Newton.mNorm 1 α T Ω
          * Work.NN.Newton.vNorm 1 α F Ω) := by
        rw [← mul_assoc, h8]

end Work.NN.Newton.AopAux
