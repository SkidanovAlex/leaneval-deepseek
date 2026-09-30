import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
namespace Work.BW.RB

/-- **Adding one generator raises the height by at least one.**

Let `I = Ideal.ofList f` be an ideal all of whose minimal primes have height `k`, and let `x`
lie in none of them.  Then the ideal `I + (x) = Ideal.ofList (f ++ [x])` has height at least
`k + 1`.

Proof.  `Ideal.height` is the infimum of the heights of the minimal primes, so it suffices to
bound the height of an arbitrary minimal prime `P` of `J = Ideal.ofList (f ++ [x])` from below.
Since `I ≤ J ≤ P` there is a minimal prime `Q` of `I` with `Q ≤ P`; by hypothesis `Q.height = k`,
and `x ∈ P` (as `x` generates `J`) while `x ∉ Q`.  Hence `Q < P` is a strict inclusion of prime
ideals, and `Ideal.height_add_one_le_of_lt_of_isPrime` gives `k + 1 = Q.height + 1 ≤ P.height`. -/
theorem ge_height_ofList_append_singleton {R : Type*} [CommRing R] [IsNoetherianRing R]
    {f : List R} {x : R} {k : ℕ}
    (hminht : ∀ Q ∈ (Ideal.ofList f).minimalPrimes, Q.height = (k : ℕ∞))
    (hx : ∀ Q ∈ (Ideal.ofList f).minimalPrimes, x ∉ Q) :
    (k : ℕ∞) + 1 ≤ (Ideal.ofList (f ++ [x])).height := by
  rw [Ideal.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun P hP => ?_
  have hJP : Ideal.ofList (f ++ [x]) ≤ P := hP.le
  have hIP : Ideal.ofList f ≤ P := by
    rw [Ideal.ofList_append] at hJP
    exact le_trans le_sup_left hJP
  haveI : P.IsPrime := hP.isPrime
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hIP
  have hxP : x ∈ P := hJP (Ideal.subset_span (by simp))
  have hxQ : x ∉ Q := hx Q hQ
  have hlt : Q < P := lt_of_le_of_ne hQP (fun he => hxQ (he ▸ hxP))
  haveI : Q.IsPrime := hQ.isPrime
  have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hminht Q hQ] at h
  exact h

end Work.BW.RB
