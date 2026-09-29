import Mathlib

namespace Work.TMComp.IDSBox

theorem polyroots {p : Polynomial ℝ} {n : ℕ} (hmonic : p.Monic)
    (hdeg : p.natDegree = n) (T : Finset ℝ) (hcard : T.card = n)
    (hroot : ∀ t ∈ T, p.eval t = 0) :
    p.roots.Nodup ∧ p.roots.toFinset = T ∧ p.roots.card = n := by
  have hp : p ≠ 0 := hmonic.ne_zero
  -- Every element of `T` is a root of `p`.
  have hsub : T ⊆ p.roots.toFinset := by
    intro t ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact hroot t ht
  -- A monic polynomial of degree `n` has at most `n` roots (with multiplicity).
  have hle : p.roots.toFinset.card ≤ T.card := by
    calc p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le _
      _ ≤ p.natDegree := Polynomial.card_roots' p
      _ = n := hdeg
      _ = T.card := hcard.symm
  -- Since `T` has `n` elements and the distinct roots of `p` number at most `n`,
  -- the distinct roots of `p` are exactly `T`.
  have hTeq : p.roots.toFinset = T := (Finset.eq_of_subset_of_card_le hsub hle).symm
  have hTeqcard : p.roots.toFinset.card = n := by rw [hTeq, hcard]
  -- Counting multiplicities forces the number of roots (with multiplicity) to be `n`.
  have hcardroots : p.roots.card = n := by
    have h1 : p.roots.card ≤ n := by rw [← hdeg]; exact Polynomial.card_roots' p
    have h2 : n ≤ p.roots.card := by
      rw [← hTeqcard]
      exact Multiset.toFinset_card_le _
    omega
  refine ⟨?_, hTeq, hcardroots⟩
  -- Equal card of `p.roots` and its `toFinset` means `p.roots` has no repeats.
  rw [← Multiset.toFinset_card_eq_card_iff_nodup, hcardroots, hTeqcard]

end Work.TMComp.IDSBox
