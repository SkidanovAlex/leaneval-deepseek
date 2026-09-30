import Mathlib
import Submission.Work.BW.esymm_mul_powSum
import Submission.Work.BW.exists_fin_index_map
import Submission.Work.BW.multiset_eq_of_esymm_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Power sums determine a multiset of complex numbers

If two multisets `s`, `t` of complex numbers have the same cardinality `n` and the same power
sums `∑ z ^ m` for every `1 ≤ m ≤ n`, then `s = t`.

The proof reduces to the classical statement that the first `n` power sums determine the
elementary symmetric functions `e_1, …, e_n` (Newton's identities), which in turn determine the
characteristic polynomial `∏ (X - z)` of the multiset, hence its root multiset.

Concretely:

* `powSum_map_univ` rewrites a power sum of a `Fin N`-indexed family as an ordinary finite sum;
* `multiset_eq_of_powSum_eq_fin` is the `Fin N`-indexed form of the theorem: Newton's identities
  (from `esymm_mul_powSum`) give equality of all elementary symmetric functions by strong
  induction on the degree, and `multiset_eq_of_esymm_eq` converts that into equality of multisets;
* `multiset_eq_of_powSum_eq` enumerates an arbitrary multiset by `Fin n`
  (`exists_fin_index_map`) and applies the indexed result.
-/

namespace Work.BW

/-- The `m`-th power sum of the multiset `{z 0, …, z (N-1)}` is the ordinary finite sum of the
`m`-th powers. -/
theorem powSum_map_univ {N : ℕ} (z : Fin N → ℂ) (m : ℕ) :
    ((Finset.univ.val.map z).map (fun x => x ^ m)).sum = ∑ i, z i ^ m := by
  rw [Multiset.map_map]
  exact Finset.sum_map_val Finset.univ (fun i => z i ^ m)

/-- **Power sums determine a `Fin N`-indexed multiset.** If `z` and `w` have equal power sums
`∑ i, z i ^ m = ∑ i, w i ^ m` for all `1 ≤ m ≤ N`, then the underlying multisets agree. -/
theorem multiset_eq_of_powSum_eq_fin {N : ℕ} (z w : Fin N → ℂ)
    (h : ∀ m, 1 ≤ m → m ≤ N → (∑ i, z i ^ m) = (∑ i, w i ^ m)) :
    (Finset.univ.val.map z : Multiset ℂ) = (Finset.univ.val.map w) := by
  -- Newton's identities, by strong induction on the degree `k`, give equality of the
  -- elementary symmetric functions `e_k` for all `k ≤ N`.
  have hE : ∀ k, k ≤ N → (Finset.univ.val.map z).esymm k = (Finset.univ.val.map w).esymm k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0; simp
      · have hz := esymm_mul_powSum z k
        have hw := esymm_mul_powSum w k
        -- The right hand sides agree term by term: `e_{a.1}` by the induction hypothesis
        -- (`a.1 < k`), and the power sum `∑ i, z i ^ a.2` by the hypothesis (`1 ≤ a.2 ≤ N`).
        have hsum : (∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k,
              (-1 : ℂ) ^ a.1 * (Finset.univ.val.map z).esymm a.1 * (∑ i, z i ^ a.2))
            = (∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k,
              (-1 : ℂ) ^ a.1 * (Finset.univ.val.map w).esymm a.1 * (∑ i, w i ^ a.2)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          have hlt : a.1 < k := (Finset.mem_filter.mp ha).2
          have hsum_eq : a.1 + a.2 = k :=
            Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_filter.mp ha).1
          have h1 : (Finset.univ.val.map z).esymm a.1 = (Finset.univ.val.map w).esymm a.1 :=
            ih a.1 hlt (le_trans (le_of_lt hlt) hk)
          have h2 : (∑ i, z i ^ a.2) = (∑ i, w i ^ a.2) := by
            apply h a.2
            · omega
            · omega
          rw [h1, h2]
        have hkne : (k : ℂ) ≠ 0 := by
          have : k ≠ 0 := Nat.pos_iff_ne_zero.mp hkpos
          exact_mod_cast this
        have hkey : (k : ℂ) * (Finset.univ.val.map z).esymm k
            = (k : ℂ) * (Finset.univ.val.map w).esymm k := by
          rw [hz, hsum, ← hw]
        exact mul_left_cancel₀ hkne hkey
  exact multiset_eq_of_esymm_eq z w hE

/-- **Newton's identities (multiset form) determine the multiset.** Two multisets of complex
numbers of the same cardinality and with the same power sums of degrees `1, …, n` are equal. -/
theorem multiset_eq_of_powSum_eq {s t : Multiset ℂ} (hcard : s.card = t.card)
    (h : ∀ m : ℕ, 1 ≤ m → m ≤ s.card →
      (s.map (fun z => z ^ m)).sum = (t.map (fun z => z ^ m)).sum) : s = t := by
  -- Enumerate both multisets by `Fin s.card`.
  obtain ⟨z, hz⟩ := exists_fin_index_map s s.card rfl
  obtain ⟨w, hw⟩ := exists_fin_index_map t s.card hcard.symm
  have hzw : (Finset.univ.val.map z : Multiset ℂ) = (Finset.univ.val.map w) := by
    apply multiset_eq_of_powSum_eq_fin z w
    intro m hm1 hmN
    rw [← powSum_map_univ z m, ← powSum_map_univ w m,
        congrArg (fun u => (u.map (fun x => x ^ m)).sum) hz,
        congrArg (fun u => (u.map (fun x => x ^ m)).sum) hw,
        h m hm1 hmN]
  exact hz.symm.trans (hzw.trans hw)

end Work.BW
