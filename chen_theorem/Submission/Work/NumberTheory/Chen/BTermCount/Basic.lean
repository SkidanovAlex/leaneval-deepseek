import Submission.Work.NumberTheory.Chen.BTermCount.Defs

open Finset
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-!
# The `B`-term: elementary combinatorics

This module develops the elementary layer of the `B`-term (`Defs.lean`):

* membership lemmas for `bTripleSet`, `bProdSet`, `bTermSet`, `survivorSet`;
* the injections `p ↦ p + 2` giving the reductions
  `bTermCount ≤ bProdCount ≤ bTripleCount` and `bTermCount ≤ survivorCount + Y`;
* monotonicity of `bTermCount` in the sift limit `M` (a *smaller* `M` can only increase the
  count), and the structural inclusion `bTermSet ⊆ {p ∈ s0Set : 3 ≤ Ω (p+2)}`.
-/

/-! ## Membership -/

theorem mem_s0Set' {x M p : ℕ} :
    p ∈ Submission.s0Set x M ↔ p < x + 1 ∧ p.Prime ∧ Id (p + 2) M = 1 := by
  simp only [Submission.s0Set, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

theorem mem_oddLt' {M q : ℕ} : q ∈ oddLt M ↔ q.Prime ∧ 3 ≤ q ∧ q < M := by
  simp only [oddLt, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => ⟨h.2.1, h.2.2, h.1⟩, fun h => ⟨h.2.2, h.1, h.2.1⟩⟩

theorem mem_bTripleSet {x M Y : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ bTripleSet x M Y ↔ IsBTriple x M Y t := by
  rw [bTripleSet, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hq1 : 2 ≤ t.1 := h1.two_le
  have hq2 : 2 ≤ t.2.1 := h2.two_le
  have hq3 : 2 ≤ t.2.2 := h3.two_le
  have hle : t.2.1 * t.2.2 ≤ x + 2 := by
    calc t.2.1 * t.2.2 ≤ t.1 * (t.2.1 * t.2.2) := Nat.le_mul_of_pos_left _ (by omega)
      _ = t.1 * t.2.1 * t.2.2 := by ring
      _ ≤ x + 2 := h8
  have hb1 : t.2.1 ≤ x + 2 := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hle
  have hb2 : t.2.2 ≤ x + 2 := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hle
  simp only [Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hq1, by omega⟩, ⟨hq2, hb1⟩, ⟨hq3, hb2⟩⟩

theorem mem_bTermSet {x M Y p : ℕ} :
    p ∈ bTermSet x M Y ↔ p ∈ Submission.s0Set x M ∧ ∃ q q₂ q₃ : ℕ,
      q.Prime ∧ q₂.Prime ∧ q₃.Prime ∧ M ≤ q ∧ q < Y ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ p + 2 = q * q₂ * q₃ := by
  rw [bTermSet, Finset.mem_filter]

theorem mem_bProdSet {x M Y n : ℕ} :
    n ∈ bProdSet x M Y ↔ ∃ t ∈ bTripleSet x M Y, t.1 * t.2.1 * t.2.2 = n := by
  rw [bProdSet, Finset.mem_image]

theorem mem_survivorSet {x M Y n : ℕ} :
    n ∈ survivorSet x M Y ↔ n ∈ bProdSet x M Y ∧ ∀ q ∈ oddLt Y, ¬ q ∣ n - 2 := by
  rw [survivorSet, Finset.mem_filter]

theorem bProdSet_subset_Icc (x M Y : ℕ) : bProdSet x M Y ⊆ Finset.Icc 2 (x + 2) := by
  intro n hn
  rw [mem_bProdSet] at hn
  obtain ⟨t, ht, rfl⟩ := hn
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := mem_bTripleSet.mp ht
  rw [Finset.mem_Icc]
  refine ⟨?_, h8⟩
  have hbc : 1 ≤ t.2.1 * t.2.2 := by nlinarith [h2.two_le, h3.two_le]
  calc (2:ℕ) ≤ t.1 := h1.two_le
    _ ≤ t.1 * (t.2.1 * t.2.2) := Nat.le_mul_of_pos_right t.1 (by omega)
    _ = t.1 * t.2.1 * t.2.2 := by ring

/-! ## The injections -/

theorem bTermSet_prod_mem {x M Y p : ℕ} (hp : p ∈ bTermSet x M Y) :
    p + 2 ∈ bProdSet x M Y := by
  obtain ⟨hs0, q, q₂, q₃, hq, hq₂, hq₃, hMq, hqY, hYq₂, hq₂q₃, heq⟩ := mem_bTermSet.mp hp
  have hpx : p < x + 1 := (mem_s0Set'.mp hs0).1
  refine mem_bProdSet.mpr ⟨(q, q₂, q₃),
    mem_bTripleSet.mpr ⟨hq, hq₂, hq₃, hMq, hqY, hYq₂, hq₂q₃, by rw [← heq]; omega⟩, heq.symm⟩

/-- The map `p ↦ p + 2` is injective from `bTermSet` into `bProdSet`. -/
theorem bTermCount_le_bProdCount (x M Y : ℕ) :
    Submission.bTermCount x M Y ≤ bProdCount x M Y := by
  rw [bTermCount_eq_card_bTermSet x M Y]
  refine Finset.card_le_card_of_injOn (fun p => p + 2) ?_ ?_
  · intro p hp
    exact bTermSet_prod_mem hp
  · intro p _ p' _ h
    simp only at h
    omega

theorem bProdCount_le_bTripleCount (x M Y : ℕ) :
    bProdCount x M Y ≤ bTripleCount x M Y := by
  rw [bProdCount, bTripleCount]
  exact Finset.card_image_le

/-- **The `B`-term count is at most the number of triples.** -/
theorem bTermCount_le_bTripleCount (x M Y : ℕ) :
    Submission.bTermCount x M Y ≤ bTripleCount x M Y :=
  le_trans (bTermCount_le_bProdCount x M Y) (bProdCount_le_bTripleCount x M Y)

/-- **Every counted prime `p ≥ Y` gives a sieve survivor `p + 2`.** -/
theorem bTermSet_prod_mem_survivor {x M Y p : ℕ} (hp : p ∈ bTermSet x M Y) (hYp : Y ≤ p) :
    p + 2 ∈ survivorSet x M Y := by
  rw [mem_survivorSet]
  refine ⟨bTermSet_prod_mem hp, ?_⟩
  have hp' : p.Prime := (mem_s0Set'.mp (mem_bTermSet.mp hp).1).2.1
  intro q hq hdvd
  obtain ⟨hq', hq3, hqY⟩ := mem_oddLt'.mp hq
  have hsub : (p + 2) - 2 = p := by omega
  rw [hsub] at hdvd
  have hpq : p = q := (hp'.dvd_iff_eq hq'.ne_one).mp hdvd
  omega

/-- **The `B`-term count is at most the number of sieve survivors plus `Y`.**  Every counted
prime `p ≥ Y` has `p + 2` surviving the sieve with modulus `P(Y)`; at most `Y` counted primes
are `< Y`. -/
theorem bTermCount_le_survivorCount_add (x M Y : ℕ) :
    Submission.bTermCount x M Y ≤ survivorCount x M Y + Y := by
  rw [bTermCount_eq_card_bTermSet x M Y, survivorCount_eq_card]
  have hsplit := Finset.card_filter_add_card_filter_not (s := bTermSet x M Y) (p := fun p => Y ≤ p)
  have h1 : ((bTermSet x M Y).filter (fun p => Y ≤ p)).card
      ≤ (survivorSet x M Y).card := by
    refine Finset.card_le_card_of_injOn (fun p => p + 2) ?_ ?_
    · intro p hp
      rw [Finset.mem_coe, Finset.mem_filter] at hp
      exact bTermSet_prod_mem_survivor hp.1 hp.2
    · intro p _ p' _ h
      simp only at h
      omega
  have h2 : ((bTermSet x M Y).filter (fun p => ¬ Y ≤ p)).card ≤ Y := by
    refine le_trans (Finset.card_le_card ?_) (le_of_eq (Finset.card_range Y))
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Finset.mem_range]
    omega
  omega

/-! ## Structural facts -/

/-- Every element of `bTermSet` has `Ω (p+2) = 3 ≥ 3`: it is a product of exactly three primes. -/
theorem bTermSet_subset_badSet (x M Y : ℕ) :
    bTermSet x M Y ⊆ (Submission.s0Set x M).filter
      (fun p => 3 ≤ ArithmeticFunction.cardFactors (p + 2)) := by
  intro p hp
  obtain ⟨hs0, q, q₂, q₃, hq, hq₂, hq₃, -, -, -, -, heq⟩ := mem_bTermSet.mp hp
  rw [Finset.mem_filter]
  refine ⟨hs0, ?_⟩
  have h3 : ArithmeticFunction.cardFactors (q * q₂ * q₃) = 3 := by
    rw [ArithmeticFunction.cardFactors_mul (mul_ne_zero hq.ne_zero hq₂.ne_zero) hq₃.ne_zero,
      ArithmeticFunction.cardFactors_mul hq.ne_zero hq₂.ne_zero,
      ArithmeticFunction.cardFactors_apply_prime hq,
      ArithmeticFunction.cardFactors_apply_prime hq₂,
      ArithmeticFunction.cardFactors_apply_prime hq₃]
  rw [heq, h3]

theorem bTermCount_le_badCount (x M Y : ℕ) :
    Submission.bTermCount x M Y ≤ ((Submission.s0Set x M).filter
      (fun p => 3 ≤ ArithmeticFunction.cardFactors (p + 2))).card := by
  rw [bTermCount_eq_card_bTermSet x M Y]
  exact Finset.card_le_card (bTermSet_subset_badSet x M Y)

/-- `Id · M = 1` is monotone *downward* in `M` (a larger sift limit sieves more). -/
theorem Id_eq_one_of_le {m M M' : ℕ} (h : M ≤ M') (h1 : Commons.NumberTheory.Chen.ChenEight.Id m M' = 1) :
    Commons.NumberTheory.Chen.ChenEight.Id m M = 1 := by
  have hsub : oddLt M ⊆ oddLt M' := by
    intro p hp
    obtain ⟨hp', hp3, hpM⟩ := mem_oddLt'.mp hp
    exact mem_oddLt'.mpr ⟨hp', hp3, lt_of_lt_of_le hpM h⟩
  have hdvd : oddPrimLt M ∣ oddPrimLt M' := by
    rw [show oddPrimLt M = ∏ p ∈ oddLt M, p from rfl,
        show oddPrimLt M' = ∏ p ∈ oddLt M', p from rfl]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have hc : m.Coprime (oddPrimLt M') := by
    rw [Commons.NumberTheory.Chen.ChenEight.Id] at h1
    by_cases hcon : m.Coprime (oddPrimLt M')
    · exact hcon
    · rw [if_neg hcon] at h1
      exact absurd h1 (by norm_num)
  rw [Commons.NumberTheory.Chen.ChenEight.Id, if_pos (Nat.Coprime.coprime_dvd_right hdvd hc)]

/-- **Monotonicity in the sift limit.**  `bTermCount` can only *decrease* when `M` grows. -/
theorem bTermCount_mono_M {x M M' Y : ℕ} (h : M ≤ M') :
    Submission.bTermCount x M' Y ≤ Submission.bTermCount x M Y := by
  rw [bTermCount_eq_card_bTermSet x M' Y, bTermCount_eq_card_bTermSet x M Y]
  refine Finset.card_le_card ?_
  intro p hp
  obtain ⟨hs0, q, q₂, q₃, hq, hq₂, hq₃, hM'q, hqY, hYq₂, hq₂q₃, heq⟩ := mem_bTermSet.mp hp
  obtain ⟨hpx, hpp, hid⟩ := mem_s0Set'.mp hs0
  exact mem_bTermSet.mpr ⟨mem_s0Set'.mpr ⟨hpx, hpp, Id_eq_one_of_le h hid⟩,
    q, q₂, q₃, hq, hq₂, hq₃, le_trans h hM'q, hqY, hYq₂, hq₂q₃, heq⟩

end Work.NumberTheory.Chen.BTermCount
