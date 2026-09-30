import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

/-- If `n ≠ 0` and `|n| < M ^ t`, then any `Finset` of primes, each strictly greater
than `M` and each dividing `n`, has at most `t - 1` elements.

Indeed the product of the (distinct) primes in `S` divides `n`, hence is at most `|n|`,
while it is at least `M ^ S.card` since every element of `S` exceeds `M`. Thus
`M ^ S.card ≤ |n| < M ^ t`, so `S.card < t` whenever `M ≥ 2` (which is forced by the
hypotheses). -/
theorem card_primes_gt_dvd_le (n : ℤ) (t M : ℕ) (hn : n ≠ 0) (hlt : n.natAbs < M ^ t)
    (S : Finset ℕ) (hSp : ∀ q ∈ S, Nat.Prime q) (hSM : ∀ q ∈ S, M < q)
    (hSd : ∀ q ∈ S, (q : ℤ) ∣ n) : S.card ≤ t - 1 := by
  have hNpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  -- The hypotheses force `M ≥ 2` (and `t ≥ 1`).
  have hM2 : 2 ≤ M := by
    by_contra h
    have hMle : M ≤ 1 := by omega
    have hpow : M ^ t ≤ 1 := by
      calc M ^ t ≤ 1 ^ t := Nat.pow_le_pow_left hMle t
        _ = 1 := by simp
    omega
  have hMpos : 0 < M := by omega
  set P : ℕ := S.prod (fun q => q) with hP
  -- The product of the primes of `S` divides `n`, since they are pairwise coprime.
  have hdvdZ : (P : ℤ) ∣ n := by
    rw [hP, Nat.cast_prod]
    exact Finset.prod_dvd_of_coprime
      (fun a ha b hb hab => ((Nat.coprime_primes (hSp a ha) (hSp b hb)).mpr hab).isCoprime)
      (fun i hi => hSd i hi)
  have hdvdN : P ∣ n.natAbs := by
    have h1 : (P : ℤ) ∣ ((n.natAbs : ℕ) : ℤ) :=
      (Int.dvd_natAbs (a := (P : ℤ)) (b := n)).2 hdvdZ
    exact Int.natCast_dvd_natCast.1 h1
  have hPle : P ≤ n.natAbs := Nat.le_of_dvd hNpos hdvdN
  -- And the product is at least `M ^ S.card`, since all its factors exceed `M`.
  have hPge : M ^ S.card ≤ P := by
    calc M ^ S.card = ∏ _x ∈ S, M := (Finset.prod_const M).symm
      _ ≤ ∏ q ∈ S, q := Finset.prod_le_prod (fun q hq => le_of_lt (hSM q hq))
      _ = P := by rw [hP]
  have hkey : M ^ S.card < M ^ t := by
    calc M ^ S.card ≤ P := hPge
      _ ≤ n.natAbs := hPle
      _ < M ^ t := hlt
  have hcard : S.card < t := by
    by_contra h
    have htle : t ≤ S.card := by omega
    have := Nat.pow_le_pow_right hMpos htle
    omega
  exact Nat.le_sub_one_of_lt hcard

end Work.BMF.recursion
