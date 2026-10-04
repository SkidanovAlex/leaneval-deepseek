import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.garding_estimate
import Submission.Work.Diff.STE.pdVec_contDiff_periodic
import Submission.Work.Diff.STE.ENormSq_succ_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The multi-index (vector-valued) Gårding estimate, direct form

`Work.Diff.STE.garding_vec_direct` is the `Hᵏ` version of the scalar Gårding estimate
`Work.Diff.STE.garding_estimate` (design note `DESIGN.md`, Layer A9), in the *direct* form in
which the `k` derivatives are applied to `u` rather than to the operator:

  `Σ_{|l| = k} ⟨A ∂∂(∂^l u), ∂^l u⟩ ≤ -(lam/2) · ENormSq (k+1) u + C · ENormSq k u`.

This is the shape in which the estimate enters the parabolic energy method: the operator
`u ↦ Σ A_{cd} ∂_c∂_d u` never needs to be differentiated, so no commutator estimates are
required.  (The sibling file `garding_estimate_vec.lean` treats the other form, where `∂^l` is
applied to the whole operator `Σ A ∂∂u` and the commutator `[∂^l, A]` must be estimated.)

The proof is an assembly:

* the `k`-fold derivative `v_l := ∂^l u` of a `C^{k+2}` periodic function is `C²` and periodic
  (`pdVec_contDiff_periodic`), so the scalar estimate applies to each `v_l` — and the constant
  `C` produced by `garding_estimate` is *uniform* in `v_l`, so a single `C` serves all `l`;
* summing the `|ι|^k` inequalities over `l` and identifying the two sums with `ENormSq (k+1) u`
  and `ENormSq k u` via `ENormSq_succ_eq` finishes the proof.
-/

namespace Work.Diff.STE

theorem garding_vec_direct {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (A : ι → ι → (ι → ℝ) → ℝ)
    (hA : ∀ c d, ContDiff ℝ (⊤ : ℕ∞) (A c d)) (hAper : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
    (hsym : ∀ c d x, A c d x = A d c x)
    (lam : ℝ) (hlam : 0 < lam)
    (hpos : ∀ x (ξ : ι → ℝ), lam * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d x * ξ c * ξ d)
    (K₁ : ℝ) (hK₁ : ∀ c d i x, |Work.Diff.STE.pdR i (A c d) x| ≤ K₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (k + 2) u → Work.Diff.STE.Periodic1 u →
      (∑ l : Fin k → ι,
        Work.Diff.STE.L2re
          (fun x => ∑ c, ∑ d, A c d x * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) x)
          (Work.Diff.STE.pdVec k l u))
        ≤ -((lam / 2) * Work.Diff.STE.ENormSq (k + 1) u) + C * Work.Diff.STE.ENormSq k u := by
  obtain ⟨C, hC, hbound⟩ :=
    Work.Diff.STE.garding_estimate A hA hAper hsym lam hlam hpos K₁ hK₁
  refine ⟨C, hC, fun u hu hup => ?_⟩
  -- The scalar estimate applied to each `k`-fold derivative `∂^l u`, with the same constant `C`.
  have hterm : ∀ l : Fin k → ι,
      Work.Diff.STE.L2re
        (fun x => ∑ c, ∑ d, A c d x * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) x)
        (Work.Diff.STE.pdVec k l u)
      ≤ -((lam / 2) * ∑ i, ∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pd i (Work.Diff.STE.pdVec k l u) x‖ ^ 2)
        + C * ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l u x‖ ^ 2 := by
    intro l
    obtain ⟨hc, hp⟩ :=
      Work.Diff.STE.pdVec_contDiff_periodic k (k + 2) (Nat.le_add_right k 2) l u hu hup
    rw [Work.Diff.STE.withTop_natCast_sub] at hc
    exact hbound (Work.Diff.STE.pdVec k l u) (by simpa [Nat.add_sub_cancel] using hc) hp
  refine le_trans (Finset.sum_le_sum (fun l _ => hterm l)) ?_
  -- The sum of the lower order terms is `ENormSq (k+1)`, the sum of the `L²` terms is `ENormSq k`.
  have hS : (∑ l : Fin k → ι, ∑ i : ι, ∫ x in Work.Diff.STE.unitCube,
        ‖Work.Diff.STE.pd i (Work.Diff.STE.pdVec k l u) x‖ ^ 2)
      = Work.Diff.STE.ENormSq (k + 1) u := (Work.Diff.STE.ENormSq_succ_eq k u).symm
  have hT : (∑ l : Fin k → ι, ∫ x in Work.Diff.STE.unitCube,
        ‖Work.Diff.STE.pdVec k l u x‖ ^ 2)
      = Work.Diff.STE.ENormSq k u := rfl
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hS, hT]

end Work.Diff.STE
