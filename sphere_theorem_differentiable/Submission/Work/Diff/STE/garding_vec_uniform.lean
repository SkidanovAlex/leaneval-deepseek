import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.GardingConst
import Submission.Work.Diff.STE.ga_const_bound
import Submission.Work.Diff.STE.garding_vec_direct
import Submission.Work.Diff.STE.garding_estimate
import Submission.Work.Diff.STE.pdVec_contDiff_periodic
import Submission.Work.Diff.STE.ENormSq_succ_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The multi-index Gårding estimate with a constant *uniform in the coefficients*

`Work.Diff.STE.garding_vec_direct` proves the `Hᵏ` Gårding estimate

  `Σ_{|l| = k} ⟨A ∂∂(∂^l u), ∂^l u⟩ ≤ -(lam/2) · ENormSq (k+1) u + C · ENormSq k u`

with a constant `C` that is *existential*: `C` may a priori depend on the coefficient matrix `A`.
For the parabolic bootstrap (where the coefficients vary — e.g. along a Galerkin approximation or
along a time-dependent family of metrics) one needs a *single* constant valid for **every**
coefficient matrix satisfying the standing bounds with the same `lam` and `K₁`.  This file
provides that:

  `∃ F : ℝ → ℝ → ℝ, (∀ lam > 0, ∀ K₁, 0 ≤ F lam K₁) ∧ (the estimate holds with `F lam K₁`)`.

The uniformity is a genuine mathematical statement: the constant produced by the classical proof
of the Gårding estimate is

  `gardingConst (card ι) lam K₁ = max K₁ 0 * n² * (max K₁ 0 * n + 1) / (2 lam)`,

which does not involve `A` at all.  That explicit constant is the content of
`Work.Diff.STE.ga_const_bound` (`Submission/Work/Diff/STE/ga_const_bound.lean`, proved from the
same ingredients as `garding_estimate`: `ga_operator_identity`, `elliptic_lower` and
`ga_first_order_bound`), and this file supplies the multi-index assembly: the `k`-fold derivative
`∂^l u` of a `C^{k+2}`, periodic `u` is `C²` and periodic (`pdVec_contDiff_periodic`), so the
scalar estimate applies to each `v_l = ∂^l u` with the *same* constant; summing over `l` and
identifying the two sums with `ENormSq (k+1) u` and `ENormSq k u` (`ENormSq_succ_eq`) gives the
claim.
-/

namespace Work.Diff.STE

theorem garding_vec_uniform {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ F : ℝ → ℝ → ℝ,
      (∀ (lam : ℝ), 0 < lam → ∀ K₁ : ℝ, 0 ≤ F lam K₁) ∧
      ∀ (lam : ℝ) (hlam : 0 < lam) (K₁ : ℝ)
        (A : ι → ι → (ι → ℝ) → ℝ)
        (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d))
        (hAper : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
        (hsym : ∀ c d x, A c d x = A d c x)
        (hpos : ∀ x (ξ : ι → ℝ),
          lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d x * ξ c * ξ d)
        (hK₁ : ∀ c d i x, |Work.Diff.STE.pdR i (A c d) x| ≤ K₁),
        ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (k + 2) u → Work.Diff.STE.Periodic1 u →
          (∑ l : Fin k → ι, Work.Diff.STE.L2re
              (fun x => ∑ c, ∑ d, A c d x
                * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) x)
              (Work.Diff.STE.pdVec k l u))
            ≤ -((lam / 2) * Work.Diff.STE.ENormSq (k + 1) u)
              + F lam K₁ * Work.Diff.STE.ENormSq k u := by
  -- The uniform constant: the explicit Gårding constant, which does not involve `A`.
  refine ⟨fun lam K₁ => gardingConst (Fintype.card ι) lam K₁, ?_, ?_⟩
  · intro lam hlam K₁
    exact gardingConst_nonneg hlam
  · intro lam hlam K₁ A hA hAper hsym hpos hK₁ u hu hup
    -- The scalar estimate applies to each `k`-fold derivative `∂^l u`, with the same constant.
    have hterm : ∀ l : Fin k → ι,
        L2re
            (fun x => ∑ c, ∑ d, A c d x * pd c (pd d (pdVec k l u)) x)
            (pdVec k l u)
          ≤ -((lam / 2) * ∑ i, ∫ x in unitCube, ‖pd i (pdVec k l u) x‖ ^ 2)
            + gardingConst (Fintype.card ι) lam K₁ * ∫ x in unitCube, ‖pdVec k l u x‖ ^ 2 := by
      intro l
      obtain ⟨hc, hp⟩ :=
        pdVec_contDiff_periodic k (k + 2) (Nat.le_add_right k 2) l u hu hup
      rw [withTop_natCast_sub] at hc
      exact ga_const_bound A hA hAper hsym lam hlam hpos K₁ hK₁ (pdVec k l u)
        (by simpa [Nat.add_sub_cancel] using hc) hp
    refine le_trans (Finset.sum_le_sum (fun l _ => hterm l)) ?_
    -- The sum of the second order terms is `ENormSq (k+1)`, the sum of the `L²` terms `ENormSq k`.
    have hS : (∑ l : Fin k → ι, ∑ i : ι, ∫ x in unitCube,
          ‖pd i (pdVec k l u) x‖ ^ 2)
        = ENormSq (k + 1) u := (ENormSq_succ_eq k u).symm
    have hT : (∑ l : Fin k → ι, ∫ x in unitCube,
          ‖pdVec k l u x‖ ^ 2)
        = ENormSq k u := rfl
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hS, hT]

end Work.Diff.STE
