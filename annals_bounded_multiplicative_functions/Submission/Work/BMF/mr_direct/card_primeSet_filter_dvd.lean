import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.buchstab_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- The number of primes in `[P,Q]` dividing `n` equals `ω(n;P,Q)`.

`primeSet P Q` is the set of primes `p` with `⌈P⌉₊ ≤ p ≤ ⌊Q⌋₊`, while `omegaCount P Q n`
counts the primes `p ∈ [1,n]` with `P ≤ p ≤ Q` and `p ∣ n`.  For `n ≥ 1` any prime divisor
`p` of `n` satisfies `p ≤ n`, and the conditions `P ≤ p`, `p ≤ Q` are equivalent to
`⌈P⌉₊ ≤ p`, `p ≤ ⌊Q⌋₊` for a prime `p`; hence the two sets of primes coincide. -/
lemma card_primeSet_filter_dvd {P Q : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    ((Work.BMF.mrDirect.primeSet P Q).filter (fun p => p ∣ n)).card =
      Work.BMF.mrDirect.omegaCount P Q n := by
  rw [Work.BMF.mrDirect.omegaCount]
  congr 1
  ext p
  simp only [Work.BMF.mrDirect.primeSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, hp⟩, hdvd⟩
    have hp2 : 2 ≤ p := hp.two_le
    have hQpos : 0 ≤ Q := by
      have hne : ⌊Q⌋₊ ≠ 0 := by omega
      have hnot : ¬ (Q < 1) := fun h => hne ((Nat.floor_eq_zero (a := Q)).mpr h)
      linarith [not_lt.mp hnot]
    exact ⟨⟨by omega, Nat.le_of_dvd (by omega) hdvd⟩, hp,
      Nat.ceil_le.mp h1, (Nat.le_floor_iff hQpos).mp h2, hdvd⟩
  · rintro ⟨⟨h1, hnle⟩, hp, hP, hQ, hdvd⟩
    exact ⟨⟨⟨Nat.ceil_le.mpr hP,
      (Nat.le_floor_iff (le_trans (by positivity : (0:ℝ) ≤ (p:ℝ)) hQ)).mpr hQ⟩, hp⟩, hdvd⟩

end Work.BMF.mr_direct
