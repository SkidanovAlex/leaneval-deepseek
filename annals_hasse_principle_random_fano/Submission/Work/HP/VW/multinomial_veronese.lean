import Mathlib
import Submission.Work.HP.WedgeDefs

/-!
# The multinomial (Veronese) expansion of a linear form

For `z : ℝ^{n+1}` the `d`-th power of the linear form `∑ᵢ zᵢ` expands as

`(∑ i, z i)^d = ∑_{m : Mon d n} (d! / ∏ᵢ mᵢ!) * ∏ᵢ zᵢ^{mᵢ}`,

the sum running over the exponent vectors of degree-`d` monomials in `n+1` variables and
the weight being the multinomial coefficient `monWeight d n m`.

The identity is the classical multinomial theorem; Mathlib states it for sums indexed by
`Finset.piAntidiag`, and the content here is the change of summation from the antidiagonal
of `Fin (n+1) → ℕ` to the subtype `Mon d n` of degree-`d` exponent vectors.
-/

set_option autoImplicit false

open Finset

namespace Work.HP.VW

/-- Every function `k : Fin (n+1) → ℕ` of total mass `d` is the underlying function of an
exponent vector of `Mon d n`: the only content is `k i ≤ d`. -/
lemma exists_mon_of_mem_piAntidiag {d n : ℕ} {k : Fin (n + 1) → ℕ}
    (hk : k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) d) :
    ∃ m : Mon d n, (fun i => (m.1 i : ℕ)) = k := by
  rw [Finset.mem_piAntidiag] at hk
  have hle : ∀ i, k i ≤ d := by
    intro i
    have h := Finset.single_le_sum (f := k) (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
    rw [hk.1] at h
    exact h
  refine ⟨⟨fun i => ⟨k i, Nat.lt_succ_of_le (hle i)⟩, ?_⟩, ?_⟩
  · simpa using hk.1
  · rfl

theorem multinomial_veronese (d n : ℕ) (z : Fin (n + 1) → ℝ) :
    (∑ i, z i) ^ d =
      ∑ m : Work.HP.Mon d n, (Work.HP.monWeight d n m : ℝ) * ∏ i, z i ^ (m.1 i : ℕ) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin (n + 1))) z d]
  refine (Finset.sum_bij
    (fun (m : Mon d n) (_ : m ∈ Finset.univ) => (fun i => (m.1 i : ℕ))) ?_ ?_ ?_ ?_).symm
  · -- the underlying function of an exponent vector has total mass `d`
    intro a _
    rw [Finset.mem_piAntidiag]
    exact ⟨a.2, fun i _ => Finset.mem_univ i⟩
  · -- and the assignment is injective
    intro a₁ _ a₂ _ h
    exact Subtype.ext (funext fun i => Fin.ext (by simpa using congrFun h i))
  · -- and surjective
    intro b hb
    obtain ⟨m, hm⟩ := exists_mon_of_mem_piAntidiag hb
    exact ⟨m, Finset.mem_univ m, hm⟩
  · -- the weights agree: `monWeight` is the multinomial coefficient of `m`
    intro a _
    simp only [monWeight]

end Work.HP.VW
