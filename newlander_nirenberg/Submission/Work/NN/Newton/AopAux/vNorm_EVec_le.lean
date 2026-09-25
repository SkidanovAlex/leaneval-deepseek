import Mathlib
import Submission.Work.NN.Newton.pushforward_norms
import Submission.Work.NN.Newton.EVec_eq

namespace Work.NN.Newton.AopAux

/-- **Componentwise bound on the residual vector.**  The `k`-th residual vector
`E_k = (Lcoef A (·)_j k - ∂̄_k v_j)_j` has `C^{1,α}`-norm bounded by `n e`, provided each of its
components does.  Indeed `E_k` is, up to the harmless sign change, exactly the vector whose
components are the functions controlled by the hypotheses, so the bound is the componentwise
bound summed over the `n` components. -/
theorem vNorm_EVec_le {n : ℕ} {α e : ℝ} {Ω : Set (Work.NN.Core.Cn n)}
    {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {v : Fin n → Work.NN.Core.Cn n → ℂ} (k : Fin n) (hΩ : UniqueDiffOn ℝ Ω)
    (hsm : ∀ l : Fin n, ContDiffOn ℝ 1 (fun z => Work.CR.Flat.dbarCoord k (v l) z
      - Work.NN.Core.Lcoef A (fun y => y l) k z) Ω)
    (he : ∀ l : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => Work.CR.Flat.dbarCoord k (v l) z
      - Work.NN.Core.Lcoef A (fun y => y l) k z) Ω ≤ ENNReal.ofReal e) :
    Work.NN.Newton.vNorm 1 α (fun z => Work.NN.Newton.EVec A v k z) Ω
      ≤ ENNReal.ofReal ((n : ℝ) * e) := by
  unfold Work.NN.Newton.vNorm
  -- Each component of `E_k` is the negative of the function controlled by `hsm`/`he`.
  have h1 : (∑ j : Fin n, Work.CR.Flat.holderNorm 1 α
        (fun z => Work.NN.Newton.EVec A v k z j) Ω)
      ≤ ∑ _j : Fin n, ENNReal.ofReal e := by
    refine Finset.sum_le_sum fun j _ => ?_
    rw [show (fun z => Work.NN.Newton.EVec A v k z j)
        = -(fun z => Work.CR.Flat.dbarCoord k (v j) z
            - Work.NN.Core.Lcoef A (fun y => y j) k z) from by
          funext z; simp only [Work.NN.Newton.EVec, Pi.neg_apply]; ring]
    rw [Work.CR.Flat.Holder.holderNorm_neg (hsm j) hΩ]
    exact he j
  -- The constant componentwise bound sums to `n e`.
  have h2 : (∑ _j : Fin n, ENNReal.ofReal e) = ENNReal.ofReal ((n : ℝ) * e) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  rw [h2] at h1
  exact h1

end Work.NN.Newton.AopAux
