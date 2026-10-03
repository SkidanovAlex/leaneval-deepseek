/-
Roots in a free group: every nontrivial element is a power of an element which is not a proper
power (its "primitive root").

The proof is a descent on the reduced-word length.  The only combinatorial input is the computation
of the reduced word of `u ^ k`, which Mathlib provides in the form
`FreeGroup.toWord_pow` together with `reduceCyclically.reduce_flatten_replicate`:
if `L = toWord u` is reduced and `k ≥ 1`, then
`toWord (u ^ k) = conj L ++ (replicate k (reduceCyclically L)).flatten ++ invRev (conj L)`,
so that `norm (u ^ k) = norm u + (k - 1) * (reduceCyclically L).length`.  The last factor is
positive when `u ≠ 1`, because `mk (reduceCyclically L)` is conjugate to `mk L = u`; hence
`norm u < norm (u ^ k)` for `k ≥ 2`, and taking a root of maximal exponent by strong induction on
`norm` produces a root which is not a proper power.
-/
import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- Length of the reduced word of a power: for a reduced word `L` and `1 ≤ k`,
`reduce ((replicate k L).flatten)` has length `L.length + (k - 1) * (reduceCyclically L).length`. -/
private theorem length_reduce_flatten_replicate [DecidableEq α] (L : List (α × Bool))
    (hred : FreeGroup.IsReduced L) {k : ℕ} (hk : 1 ≤ k) :
    (FreeGroup.reduce (List.replicate k L).flatten).length =
      L.length + (k - 1) * (FreeGroup.reduceCyclically L).length := by
  have hk0 : k ≠ 0 := by omega
  have h1 : (FreeGroup.reduce (List.replicate k L).flatten).length =
      2 * (FreeGroup.reduceCyclically.conjugator L).length +
        k * (FreeGroup.reduceCyclically L).length := by
    rw [FreeGroup.reduceCyclically.reduce_flatten_replicate hred k, if_neg hk0]
    simp [List.length_flatten, List.map_replicate, List.sum_replicate, FreeGroup.invRev_length]
    omega
  have h2 : L.length =
      (FreeGroup.reduceCyclically.conjugator L).length + (FreeGroup.reduceCyclically L).length
        + (FreeGroup.reduceCyclically.conjugator L).length := by
    have h := congr_arg List.length (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically L)
    simp only [List.length_append, FreeGroup.invRev_length] at h
    omega
  have hmul : (k - 1) * (FreeGroup.reduceCyclically L).length +
        (FreeGroup.reduceCyclically L).length
      = k * (FreeGroup.reduceCyclically L).length := by
    calc (k - 1) * (FreeGroup.reduceCyclically L).length + (FreeGroup.reduceCyclically L).length
        = (k - 1) * (FreeGroup.reduceCyclically L).length +
            1 * (FreeGroup.reduceCyclically L).length := by
          rw [one_mul]
      _ = ((k - 1) + 1) * (FreeGroup.reduceCyclically L).length := (Nat.add_mul _ _ _).symm
      _ = k * (FreeGroup.reduceCyclically L).length := by rw [Nat.sub_add_cancel hk]
  rw [h1, h2]
  omega

/-- The cyclic reduction of the reduced word of a nontrivial element is nonempty. -/
private theorem reduceCyclically_ne_nil [DecidableEq α] {L : List (α × Bool)}
    (h : FreeGroup.mk L ≠ 1) : FreeGroup.reduceCyclically L ≠ [] := by
  intro hnil
  have hmk0 : FreeGroup.mk (FreeGroup.reduceCyclically L) = 1 := by
    rw [← FreeGroup.toWord_inj]
    simp [hnil]
  have hc : FreeGroup.mk (FreeGroup.reduceCyclically.conjugator L)
      * FreeGroup.mk (FreeGroup.reduceCyclically L)
      * (FreeGroup.mk (FreeGroup.reduceCyclically.conjugator L))⁻¹ = FreeGroup.mk L := by
    have hcc := congr_arg FreeGroup.mk (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically L)
    simpa [FreeGroup.mul_mk, FreeGroup.inv_mk] using hcc
  apply h
  rw [← hc, hmk0]
  group

/-- The reduced length strictly increases under taking powers `k ≥ 2` of a nontrivial element. -/
private theorem norm_lt_norm_pow [DecidableEq α] (u : FreeGroup α) (hu : u ≠ 1) {k : ℕ}
    (hk : 2 ≤ k) : FreeGroup.norm u < FreeGroup.norm (u ^ k) := by
  have hk1 : 1 ≤ k := by omega
  have hLred : FreeGroup.IsReduced (FreeGroup.toWord u) := FreeGroup.isReduced_toWord
  have hmk : FreeGroup.mk (FreeGroup.toWord u) ≠ 1 := by rw [FreeGroup.mk_toWord]; exact hu
  have hnil : FreeGroup.reduceCyclically (FreeGroup.toWord u) ≠ [] := reduceCyclically_ne_nil hmk
  have hpow : FreeGroup.norm (u ^ k) = FreeGroup.norm u
      + (k - 1) * (FreeGroup.reduceCyclically (FreeGroup.toWord u)).length := by
    rw [FreeGroup.norm, FreeGroup.toWord_pow]
    exact length_reduce_flatten_replicate _ hLred hk1
  rw [hpow]
  have hm1 : 1 ≤ (FreeGroup.reduceCyclically (FreeGroup.toWord u)).length := by
    have h0 : (FreeGroup.reduceCyclically (FreeGroup.toWord u)).length ≠ 0 :=
      fun h0 => hnil (List.length_eq_zero_iff.mp h0)
    omega
  have hmul : 1 ≤ (k - 1) * (FreeGroup.reduceCyclically (FreeGroup.toWord u)).length :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  omega

/-- The same strict increase for `relatorNorm`. -/
private theorem relatorNorm_lt_relatorNorm_pow (u : FreeGroup α) (hu : u ≠ 1) {k : ℕ}
    (hk : 2 ≤ k) : relatorNorm u < relatorNorm (u ^ k) := by
  have h := @norm_lt_norm_pow α (Classical.decEq α) u hu k hk
  simpa [relatorNorm] using h

/-- Every nontrivial element of a free group is a power of an element which is not a proper power:
its root. -/
theorem exists_root {α : Type u} (r : FreeGroup α) (hr : r ≠ 1) :
    ∃ (u : FreeGroup α) (l : ℕ), 1 ≤ l ∧ r = u ^ l ∧ ¬ Work.OROneRel.IsProperPower u := by
  classical
  have key : ∀ n : ℕ, ∀ r : FreeGroup α, relatorNorm r = n → r ≠ 1 →
      (∃ (u : FreeGroup α) (l : ℕ), 1 ≤ l ∧ r = u ^ l ∧ ¬ IsProperPower u) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro r hrn hr
      by_cases hp : IsProperPower r
      · obtain ⟨v, k, hk, hvk⟩ := hp
        subst hvk
        have hv1 : v ≠ 1 := by
          intro h
          rw [h] at hr
          simp at hr
        have hlt : relatorNorm v < n := by
          rw [← hrn]
          exact relatorNorm_lt_relatorNorm_pow v hv1 hk
        obtain ⟨u, l, hl, hvl, hu⟩ := ih (relatorNorm v) hlt v rfl hv1
        exact ⟨u, l * k, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
          by rw [hvl, pow_mul], hu⟩
      · exact ⟨r, 1, le_refl 1, (pow_one r).symm, hp⟩
  exact key (relatorNorm r) r rfl hr

end Work.OROneRel
