import Mathlib

namespace Work.BG

/-- Group-theoretic input for `Work.BG.nOrbCosets` (the coset covering part): if `H ◁ Q` has
index `3` and `g ∉ H`, then the three cosets `H`, `gH`, `g^2 H` cover `Q`, in the form: every
`x : Q` lies in `H`, or equals `c * g` with `c ∈ H`, or equals `c * g ^ 2` with `c ∈ H`.

Route: `Q ⧸ H` has `3` elements (`Subgroup.index_eq_card`) and the class of `g` is not `1`, so
its `Subgroup.zpowers` is `⊤` (`Subgroup.eq_top_of_card_eq`) and `g ^ 3 ∈ H`
(`Subgroup.pow_index_mem`, or Lagrange); `Subgroup.mem_zpowers_iff_mem_range_orderOf` writes the
class of `x` as `1`, `g` or `g ^ 2`.  Translating back through the quotient gives `x ∈ gH`, i.e.
`x = g * c` with `c ∈ H`, and then `H.Normal` rewrites this as `x = c' * g` with
`c' = g * c * g⁻¹ ∈ H`. -/
theorem nOrbCosetIndexThree {Q : Type} [Group Q] (H : Subgroup Q) [H.Normal]
    (h3 : H.index = 3) {g : Q} (hg : g ∉ H) (x : Q) :
    x ∈ H ∨ (∃ c ∈ H, x = c * g) ∨ (∃ c ∈ H, x = c * g ^ 2) := by
  classical
  -- The quotient `Q ⧸ H` has exactly three elements.
  have hcard : Nat.card (Q ⧸ H) = 3 := by
    rw [← Subgroup.index_eq_card]; exact h3
  have hfin : Finite (Q ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set p : Q ⧸ H := QuotientGroup.mk g with hp
  -- The class of `g` is nontrivial, hence has order `3` in the `3`-element quotient.
  have hpne : p ≠ 1 := by
    intro h
    exact hg ((QuotientGroup.eq_one_iff g).mp (hp ▸ h))
  have hdvd : orderOf p ∣ 3 := by
    rw [← hcard]; exact orderOf_dvd_natCard p
  have hord : orderOf p = 3 := by
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hpne
    · exact h
  -- So the class of `g` generates the whole quotient.
  have hfinz : Finite ↥(Subgroup.zpowers p) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; norm_num)
  have hz : Subgroup.zpowers p = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  have hmem : (QuotientGroup.mk x : Q ⧸ H) ∈ Subgroup.zpowers p := by
    rw [hz]; exact Subgroup.mem_top _
  -- Hence the class of `x` is `1`, `p` or `p ^ 2`.
  rw [mem_zpowers_iff_mem_range_orderOf] at hmem
  rw [hord, Finset.mem_image] at hmem
  obtain ⟨i, hi, hix⟩ := hmem
  rw [Finset.mem_range] at hi
  interval_cases i
  · left
    exact (QuotientGroup.eq_one_iff x).mp (by rw [← hix]; simp)
  · right; left
    refine ⟨x / g, (QuotientGroup.eq_iff_div_mem).mp ?_, (div_mul_cancel x g).symm⟩
    rw [← hix, pow_one, hp]
  · right; right
    refine ⟨x / g ^ 2, (QuotientGroup.eq_iff_div_mem).mp ?_,
      (div_mul_cancel x (g ^ 2)).symm⟩
    rw [← hix, hp, QuotientGroup.mk_pow]

end Work.BG
