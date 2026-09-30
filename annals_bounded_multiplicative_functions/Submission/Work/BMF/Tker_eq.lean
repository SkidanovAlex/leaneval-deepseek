import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.kern_hasSum
import Submission.Work.BMF.kern_summable
import Submission.Work.BMF.Xsum_norm_pow
import Submission.Work.BMF.tsum_pi_prod
import Submission.Work.BMF.TentDefs
import Submission.Work.BMF.Tkeraux.Basic
import Submission.Work.BMF.Tkeraux.tsum_prod_kern
import Submission.Work.BMF.Tkeraux.Tker_summand_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset
open scoped BigOperators

/-- **The kernel-weighted `2s`-th moment expands into a pair sum of tent values.**

`Tker r s M₁ M₂ k γ ε = ∑'_c ∏_j kern (r M₁^{j+1}) (c_j) ‖Xsum k M₂ γ ε c‖^{2s}` is the
smoothed (kernel-weighted) `2s`-th moment of the inner `b`-sum.  Expanding `‖Xsum‖^{2s}` over
pairs of `s`-tuples of `[1, M₂]` and inserting the Fourier series of the tent in each frequency
variable turns it into a *finite* sum over pairs:

`Tker = ∑_p εp(ε) ∏_j (π² K_j/2) tent (1/(2K_j)) (γ_j · dvec (j+1) p)`, `K_j = r M₁^{j+1}`.

The interchange of the `c`-sum with the finite pair sum is `Summable.tsum_finsetSum`, each
single-`p` family being absolutely summable with majorant `∏_j ‖kern (rM₁^{j+1}) (c_j)‖`; the
inner `c`-sum then factorises over the `k` coordinates by `Work.BMF.Tkeraux.tsum_prod_kern`
(the multivariate tent Fourier series, valid for every scale, including `r = 0` where both
sides vanish). -/
theorem Tker_eq (r s M₁ M₂ k : ℕ) (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (γ : Fin k → ℝ) (ε : ℕ → ℂ) :
    ((Tker r s M₁ M₂ k γ ε : ℝ) : ℂ)
      = ∑ p : Pair s M₂, epsp ε p * ∏ j : Fin k,
          ((Real.pi ^ 2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ) / 2
              * tent (1 / (2 * ((r * M₁ ^ ((j : ℕ) + 1) : ℕ) : ℝ)))
                  (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)) : ℂ)) := by
  classical
  -- Step 1: move the real-to-complex cast inside the defining `tsum` of `Tker`.
  have hcast : ((Tker r s M₁ M₂ k γ ε : ℝ) : ℂ)
      = ∑' c : Fin k → ℤ,
          (((∏ j : Fin k, kern (r * M₁ ^ ((j : ℕ) + 1)) (c j))
            * ‖Xsum k M₂ γ ε c‖ ^ (2 * s) : ℝ) : ℂ) := by
    rw [Tker, Complex.ofReal_tsum]
  rw [hcast]
  -- Step 2: expand each summand over pairs (`Xsum_norm_pow` + the kernel prefactor).
  have hstep : (∑' c : Fin k → ℤ,
        (((∏ j : Fin k, kern (r * M₁ ^ ((j : ℕ) + 1)) (c j))
          * ‖Xsum k M₂ γ ε c‖ ^ (2 * s) : ℝ) : ℂ))
      = ∑' c : Fin k → ℤ, ∑ p : Pair s M₂, epsp ε p * ∏ j : Fin k,
          ((kern (r * M₁ ^ ((j : ℕ) + 1)) (c j) : ℂ)
            * eZ (((c j : ℤ) : ℝ) * (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ)))) :=
    tsum_congr fun c => Tkeraux.Tker_summand_eq r s M₁ M₂ k γ ε c
  rw [hstep]
  -- Step 3: summability of each single-pair family, so that the `c`-sum may be interchanged
  -- with the finite sum over pairs.
  have hbase : ∀ θ : Fin k → ℝ, Summable (fun c : Fin k → ℤ =>
      ∏ j : Fin k, ((kern (r * M₁ ^ ((j : ℕ) + 1)) (c j) : ℂ)
        * eZ (((c j : ℤ) : ℝ) * θ j))) := by
    intro θ
    have h3 : Summable (fun c : Fin k → ℤ => ∏ j : Fin k,
        ‖(kern (r * M₁ ^ ((j : ℕ) + 1)) (c j) : ℂ) * eZ (((c j : ℤ) : ℝ) * θ j)‖) :=
      (Tkeraux.tsum_prod_kern k (fun j => r * M₁ ^ ((j : ℕ) + 1)) θ).1
    exact Summable.of_norm (h3.congr fun c => (norm_prod _ _).symm)
  have hsumm : ∀ p ∈ (Finset.univ : Finset (Pair s M₂)), Summable (fun c : Fin k → ℤ =>
      epsp ε p * ∏ j : Fin k, ((kern (r * M₁ ^ ((j : ℕ) + 1)) (c j) : ℂ)
        * eZ (((c j : ℤ) : ℝ) * (γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ))))) := by
    intro p _
    exact (hbase (fun j => γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ))).mul_left (epsp ε p)
  rw [Summable.tsum_finsetSum (s := Finset.univ) hsumm]
  -- Step 4: evaluate the inner `c`-sum by the multivariate tent Fourier series.
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [tsum_mul_left,
    (Tkeraux.tsum_prod_kern k (fun j => r * M₁ ^ ((j : ℕ) + 1))
      (fun j => γ j * ((dvec ((j : ℕ) + 1) p : ℤ) : ℝ))).2]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast
  ring

end Work.BMF
