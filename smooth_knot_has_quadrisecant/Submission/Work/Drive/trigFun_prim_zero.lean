import Mathlib
import Submission.Work.Drive.trigFun

namespace Work.Drive

open scoped Real

noncomputable section

/-- For a finitely supported `Q : ℤ →₀ E` and a finset `T` containing all nonzero elements of
`Q.support`, the sum `∑ k ∈ T, k⁻¹ • Q k` equals the `Finsupp.sum` of `Q` against `k ↦ k⁻¹ • ⋯`.
The frequency-`0` term contributes `0⁻¹ • Q 0 = 0` on both sides. -/
lemma sum_inv_smul_eq_finsupp_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (Q : ℤ →₀ E) (T : Finset ℤ) (hT : ∀ k ∈ Q.support, k ≠ 0 → k ∈ T) :
    (∑ k ∈ T, ((k:ℝ))⁻¹ • Q k) = Q.sum (fun j v => ((j:ℝ))⁻¹ • v) := by
  have hsum : Q.sum (fun j v => ((j:ℝ))⁻¹ • v)
      = ∑ k ∈ Q.support, ((k:ℝ))⁻¹ • Q k := rfl
  have h2 : ∑ k ∈ Q.support.erase 0, ((k:ℝ))⁻¹ • Q k
      = ∑ k ∈ T, ((k:ℝ))⁻¹ • Q k := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      exact hT x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx)
    · intro x hxT hxnot
      by_cases hxs : x ∈ Q.support
      · by_cases hx0 : x = 0
        · subst hx0; simp
        · exact absurd (Finset.mem_erase.mpr ⟨hx0, hxs⟩) hxnot
      · have hxq : Q x = 0 := by simpa [Finsupp.mem_support_iff] using hxs
        simp [hxq]
  have h1 : ∑ k ∈ Q.support.erase 0, ((k:ℝ))⁻¹ • Q k
      = ∑ k ∈ Q.support, ((k:ℝ))⁻¹ • Q k := by
    refine Finset.sum_subset (Finset.erase_subset 0 _) ?_
    intro x hx hxnot
    by_cases hx0 : x = 0
    · subst hx0; simp
    · exact absurd (Finset.mem_erase.mpr ⟨hx0, hx⟩) hxnot
  rw [hsum]
  exact h2.symm.trans h1

/-- The primitive `Work.Drive.TrigFun.prim P` (defined in `Submission/Work/Drive/trigFun.lean`) is
normalised so that its value at `0` is `0`.  Indeed, at `t = 0` the sum of the `cos` coefficients
of `prim P` is `(c 0) + Σ_{k ≠ 0} c k = (Σ_j (1/j) • d_j) - (Σ_{k ≠ 0} (1/k) • d_k) = 0`.
Route: `Finsupp.onFinset_apply`, `Real.cos_zero`, `Real.sin_zero`, `zero_smul`, and the
`insert 0`/`Finset.sum_insert` bookkeeping (`0 ∉ P.c.support ∪ P.d.support` need not hold; handle
that case by `Finset.insert_eq_self`). -/
theorem trigFun_prim_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Work.Drive.TrigFun E) : (Work.Drive.TrigFun.prim P).toFun 0 = 0 := by
  have hcval : ∀ k : ℤ, (TrigFun.prim P).c k
      = (if k = 0 then P.d.sum (fun j v => ((j:ℝ))⁻¹ • v)
          else -(((k:ℝ))⁻¹ • P.d k)) := by
    intro k
    simp only [TrigFun.prim, Finsupp.onFinset_apply]
  have key : (TrigFun.prim P).c.sum (fun k v => Real.cos ((k:ℝ)*0) • v)
      = ∑ k ∈ insert 0 (P.c.support ∪ P.d.support), (TrigFun.prim P).c k := by
    simp only [TrigFun.prim]
    rw [Finsupp.onFinset_sum]
    · apply Finset.sum_congr rfl
      intro k _
      rw [Finsupp.onFinset_apply]
      simp [Real.cos_zero]
    · intro a; simp
  have hd : (TrigFun.prim P).d.sum (fun k v => Real.sin ((k:ℝ)*0) • v) = 0 := by
    simp only [TrigFun.prim]
    rw [Finsupp.onFinset_sum]
    · apply Finset.sum_eq_zero
      intro k _
      simp [Real.sin_zero]
    · intro a; simp
  simp only [TrigFun.toFun]
  rw [key, hd, add_zero]
  have step : ∑ k ∈ insert 0 (P.c.support ∪ P.d.support), (TrigFun.prim P).c k
      = ∑ k ∈ insert 0 (P.c.support ∪ P.d.support),
          (if k = 0 then P.d.sum (fun j v => ((j:ℝ))⁻¹ • v)
            else -(((k:ℝ))⁻¹ • P.d k)) :=
    Finset.sum_congr rfl (fun k _ => hcval k)
  rw [step]
  rw [← Finset.insert_erase (Finset.mem_insert_self 0 (P.c.support ∪ P.d.support))]
  rw [Finset.sum_insert (Finset.notMem_erase (0:ℤ) (insert 0 (P.c.support ∪ P.d.support)))]
  rw [if_pos rfl]
  have hsum2 : ∑ k ∈ (insert 0 (P.c.support ∪ P.d.support)).erase 0,
        (if k = 0 then P.d.sum (fun j v => ((j:ℝ))⁻¹ • v)
          else -(((k:ℝ))⁻¹ • P.d k))
      = ∑ k ∈ (insert 0 (P.c.support ∪ P.d.support)).erase 0,
          -(((k:ℝ))⁻¹ • P.d k) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact if_neg (Finset.ne_of_mem_erase hk)
  rw [hsum2, Finset.sum_neg_distrib]
  rw [sum_inv_smul_eq_finsupp_sum P.d ((insert 0 (P.c.support ∪ P.d.support)).erase 0)
      (fun k hk hk0 => Finset.mem_erase.mpr ⟨hk0,
        Finset.mem_insert.mpr (Or.inr (Finset.mem_union.mpr (Or.inr hk)))⟩)]
  simp

end

end Work.Drive
