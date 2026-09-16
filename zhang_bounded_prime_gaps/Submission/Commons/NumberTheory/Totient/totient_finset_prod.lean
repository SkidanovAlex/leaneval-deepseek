import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Totient

namespace Commons.NumberTheory.Totient

open scoped BigOperators

/-- Euler's totient is multiplicative over a finite family of pairwise coprime
nonzero natural numbers: `φ (∏ i ∈ s, f i) = ∏ i ∈ s, φ (f i)`. -/
theorem totient_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (h0 : ∀ i ∈ s, f i ≠ 0)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (f i).Coprime (f j)) :
    (∏ i ∈ s, f i).totient = ∏ i ∈ s, (f i).totient := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h0t : ∀ i ∈ t, f i ≠ 0 := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have hcop_t : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → (f i).Coprime (f j) :=
      fun i hi j hj hij => hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hcop_at : (f a).Coprime (∏ i ∈ t, f i) :=
      Nat.Coprime.prod_right fun i hi =>
        hcop a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
          (by rintro rfl; exact ha hi)
    rw [Nat.totient_mul hcop_at, ih h0t hcop_t]

end Commons.NumberTheory.Totient