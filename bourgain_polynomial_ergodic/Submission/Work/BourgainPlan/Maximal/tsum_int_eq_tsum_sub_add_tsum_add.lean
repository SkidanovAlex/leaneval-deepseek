import Mathlib

namespace Work.BourgainPlan.Maximal

/-- The integers split into the two rays `{…, K-2, K-1}` and `{K, K+1, …}`; if the
corresponding one-sided sums over `ℕ` both converge, the sum over `ℤ` is their sum. -/
theorem tsum_int_eq_tsum_sub_add_tsum_add (f : ℤ → ℝ) (K : ℤ)
    (h1 : Summable fun n : ℕ => f (K - 1 - (n : ℤ))) (h2 : Summable fun n : ℕ => f (K + (n : ℤ))) :
    ∑' m : ℤ, f m = (∑' n : ℕ, f (K - 1 - (n : ℤ))) + (∑' n : ℕ, f (K + (n : ℤ))) := by
  -- Reindex `ℤ` as `ℕ ⊕ ℕ` via `inl n ↦ K - 1 - n`, `inr n ↦ K + n`.
  let e : ℕ ⊕ ℕ ≃ ℤ :=
    ((Equiv.sumComm ℕ ℕ).trans Equiv.intEquivNatSumNat.symm).trans (Equiv.addRight K)
  have he_inl : ∀ n : ℕ, e (Sum.inl n) = K - 1 - (n : ℤ) := fun n => by
    simp only [e, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl]
    show Equiv.intEquivNatSumNat.symm (Sum.inr n) + K = K - 1 - (n : ℤ)
    rw [show Equiv.intEquivNatSumNat.symm (Sum.inr n) = Int.negSucc n from rfl]
    omega
  have he_inr : ∀ n : ℕ, e (Sum.inr n) = K + (n : ℤ) := fun n => by
    simp only [e, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr]
    show Equiv.intEquivNatSumNat.symm (Sum.inl n) + K = K + (n : ℤ)
    rw [show Equiv.intEquivNatSumNat.symm (Sum.inl n) = (n : ℤ) from rfl]
    ring
  have hs_inl : Summable (fun n : ℕ => f (e (Sum.inl n))) := by
    simpa only [he_inl] using h1
  have hs_inr : Summable (fun n : ℕ => f (e (Sum.inr n))) := by
    simpa only [he_inr] using h2
  rw [← Equiv.tsum_eq e f]
  rw [Summable.tsum_sum (f := fun x : ℕ ⊕ ℕ => f (e x)) hs_inl hs_inr]
  simp only [he_inl, he_inr]

end Work.BourgainPlan.Maximal
