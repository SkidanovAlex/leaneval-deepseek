import Mathlib

namespace Work.HP.MDEstimates

/-- Sum of `q ^ (a + b + c)` over a product box factors as a product of
geometric sums. -/
private lemma sum_box_pow (A B C : Finset ℕ) (q : ℝ) :
    (∑ k ∈ A.product (B.product C), q ^ (k.1 + k.2.1 + k.2.2))
      = (∑ a ∈ A, q ^ a) * (∑ b ∈ B, q ^ b) * (∑ c ∈ C, q ^ c) := by
  have h2 : (∑ bc ∈ B.product C, q ^ bc.1 * q ^ bc.2)
      = (∑ b ∈ B, q ^ b) * (∑ c ∈ C, q ^ c) := by
    trans ∑ b ∈ B, ∑ c ∈ C, q ^ b * q ^ c
    · exact Finset.sum_product B C (fun bc : ℕ × ℕ => q ^ bc.1 * q ^ bc.2)
    · exact (Finset.sum_mul_sum B C (fun b => q ^ b) (fun c => q ^ c)).symm
  have h1 : (∑ k ∈ A.product (B.product C), q ^ (k.1 + k.2.1 + k.2.2))
      = ∑ a ∈ A, ∑ bc ∈ B.product C, q ^ a * (q ^ bc.1 * q ^ bc.2) := by
    trans ∑ a ∈ A, ∑ bc ∈ B.product C, q ^ (a + bc.1 + bc.2)
    · exact Finset.sum_product A (B.product C)
        (fun k : ℕ × (ℕ × ℕ) => q ^ (k.1 + k.2.1 + k.2.2))
    · apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro bc _
      rw [pow_add, pow_add]; ring
  have h3 : (∑ a ∈ A, ∑ bc ∈ B.product C, q ^ a * (q ^ bc.1 * q ^ bc.2))
      = (∑ a ∈ A, q ^ a) * (∑ bc ∈ B.product C, q ^ bc.1 * q ^ bc.2) :=
    (Finset.sum_mul_sum A (B.product C) (fun a => q ^ a)
      (fun bc => q ^ bc.1 * q ^ bc.2)).symm
  rw [h1, h3, h2, mul_assoc]

/-- Per-term bound: on the simplex `a + b + c ≤ N` the weight collapses to
`2 ^ (3/2 (a+b) + 7/2 c) ≤ 2 ^ (7/2 N) · (1/4) ^ (N - c)`. -/
private lemma caseB_term_le (N a b c : ℕ) (h : a + b + c ≤ N) :
    ((2 : ℝ) ^ a * (2 : ℝ) ^ b) ^ ((3 : ℝ) / 2) * ((2 : ℝ) ^ c) ^ ((7 : ℝ) / 2)
      ≤ (2 : ℝ) ^ (((7 : ℝ) / 2) * (N : ℝ)) * ((1 : ℝ) / 4) ^ (N - c) := by
  have hc : c ≤ N := by omega
  have hL : ((2 : ℝ) ^ a * (2 : ℝ) ^ b) ^ ((3 : ℝ) / 2)
        * ((2 : ℝ) ^ c) ^ ((7 : ℝ) / 2)
      = (2 : ℝ) ^ (((a + b : ℕ) : ℝ) * ((3 : ℝ) / 2) + (c : ℝ) * ((7 : ℝ) / 2)) := by
    rw [← pow_add (2 : ℝ) a b]
    rw [← Real.rpow_natCast (2 : ℝ) (a + b), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_natCast (2 : ℝ) c, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hq : ((1 : ℝ) / 4) ^ (N - c) = (2 : ℝ) ^ ((-2 : ℝ) * (((N - c : ℕ)) : ℝ)) := by
    have h2 : (2 : ℝ) ^ ((-2 : ℝ)) = (1 : ℝ) / 4 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]; norm_num
    rw [← h2]
    rw [show ((2 : ℝ) ^ ((-2 : ℝ))) ^ (N - c)
          = ((2 : ℝ) ^ ((-2 : ℝ))) ^ (((N - c : ℕ)) : ℝ) from by rw [Real.rpow_natCast]]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hL, hq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
  have hcast1 : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by push_cast; ring
  have hcast2 : (((N - c : ℕ)) : ℝ) = (N : ℝ) - (c : ℝ) := by rw [Nat.cast_sub hc]
  rw [hcast1, hcast2]
  have hh : (a : ℝ) + b + c ≤ (N : ℝ) := by exact_mod_cast h
  linarith

/-- Geometric estimate for the Case B simplex: after the involution
`(a,b,c) ↦ (a,b,N-a-b-c)` the summand `(1/4)^(N-c)` becomes `(1/4)^(a+b+c)`,
and the simplex lies in the full box, whose sum is `(∑ (1/4)^a)^3 ≤ 2^3 = 8`. -/
private lemma caseB_geom (N : ℕ) :
    (∑ k ∈ ((Finset.range (N + 1)).product
        ((Finset.range (N + 1)).product (Finset.range (N + 1)))).filter
        (fun k => k.1 + k.2.1 + k.2.2 ≤ N),
      ((1 : ℝ) / 4) ^ (N - k.2.2)) ≤ 100 := by
  classical
  set S := ((Finset.range (N + 1)).product
        ((Finset.range (N + 1)).product (Finset.range (N + 1)))).filter
        (fun k => k.1 + k.2.1 + k.2.2 ≤ N) with hS
  let φ : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ := fun k => (k.1, k.2.1, N - k.1 - k.2.1 - k.2.2)
  have hmem : ∀ k, k ∈ S ↔ k.1 < N + 1 ∧ k.2.1 < N + 1 ∧ k.2.2 < N + 1
      ∧ k.1 + k.2.1 + k.2.2 ≤ N := by
    intro k
    rw [hS]
    constructor
    · intro hk
      obtain ⟨hkP, hkc⟩ := Finset.mem_filter.mp hk
      obtain ⟨ha, hbc⟩ := Finset.mem_product.mp hkP
      obtain ⟨hb, hcc⟩ := Finset.mem_product.mp hbc
      exact ⟨Finset.mem_range.mp ha, Finset.mem_range.mp hb, Finset.mem_range.mp hcc, hkc⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr h1,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr h2, Finset.mem_range.mpr h3⟩⟩, h4⟩
  have hφmaps : ∀ k ∈ S, φ k ∈ S := by
    intro k hk
    obtain ⟨h1, h2, h3, h4⟩ := (hmem k).mp hk
    refine (hmem (φ k)).mpr ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [φ]; omega
    · dsimp only [φ]; omega
    · dsimp only [φ]; omega
    · dsimp only [φ]; omega
  have hφφ : ∀ k ∈ S, φ (φ k) = k := by
    intro k hk
    obtain ⟨h1, h2, h3, h4⟩ := (hmem k).mp hk
    obtain ⟨x, yz⟩ := k
    obtain ⟨y, z⟩ := yz
    have h : x + y + z ≤ N := by omega
    dsimp only [φ]
    simp only [Prod.mk.injEq]
    refine ⟨trivial, trivial, ?_⟩
    omega
  have key : ∑ k ∈ S, ((1 : ℝ) / 4) ^ (N - k.2.2)
      = ∑ k ∈ S, ((1 : ℝ) / 4) ^ (k.1 + k.2.1 + k.2.2) := by
    refine Finset.sum_bij' (fun a _ => φ a) (fun b _ => φ b) (fun a ha => hφmaps a ha)
      (fun b hb => hφmaps b hb) (fun a ha => hφφ a ha) (fun b hb => hφφ b hb) ?_
    intro a ha
    obtain ⟨h1, h2, h3, h4⟩ := (hmem a).mp ha
    congr 1
    dsimp only [φ]
    omega
  rw [key]
  set P := (Finset.range (N + 1)).product ((Finset.range (N + 1)).product (Finset.range (N + 1))) with hP
  have hsub : S ⊆ P := by rw [hS, hP]; exact Finset.filter_subset _ _
  have hstep1 : ∑ k ∈ S, ((1 : ℝ) / 4) ^ (k.1 + k.2.1 + k.2.2)
      ≤ ∑ k ∈ P, ((1 : ℝ) / 4) ^ (k.1 + k.2.1 + k.2.2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i _ _
    positivity
  have hstep2 : ∑ k ∈ P, ((1 : ℝ) / 4) ^ (k.1 + k.2.1 + k.2.2)
      = (∑ a ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ a) ^ 3 := by
    rw [hP, sum_box_pow]
    ring
  have hgeom : (∑ a ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ a) ≤ 2 := by
    calc (∑ a ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ a)
        ≤ ∑ a ∈ Finset.range (N + 1), ((1 : ℝ) / 2) ^ a := Finset.sum_le_sum (fun i _ => by
              apply pow_le_pow_left₀ (by norm_num); norm_num)
      _ ≤ 2 := sum_geometric_two_le (N + 1)
  have hfin : (∑ a ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ a) ^ 3 ≤ 100 := by
    have h0 : 0 ≤ ∑ a ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ a :=
      Finset.sum_nonneg (fun i _ => by positivity)
    calc (∑ a ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ a) ^ 3
        ≤ 2 ^ 3 := pow_le_pow_left₀ h0 hgeom 3
      _ = 8 := by norm_num
      _ ≤ 100 := by norm_num
  calc ∑ k ∈ S, ((1 : ℝ) / 4) ^ (k.1 + k.2.1 + k.2.2)
      ≤ ∑ k ∈ P, ((1 : ℝ) / 4) ^ (k.1 + k.2.1 + k.2.2) := hstep1
    _ = (∑ a ∈ Finset.range (N + 1), ((1 : ℝ) / 4) ^ a) ^ 3 := hstep2
    _ ≤ 100 := hfin

theorem rpow_caseB_sum (N : ℕ) :
    (∑ k ∈ ((Finset.range (N + 1)).product
        ((Finset.range (N + 1)).product (Finset.range (N + 1)))).filter
        (fun k => k.1 + k.2.1 + k.2.2 ≤ N),
      ((2 : ℝ) ^ (k.1) * (2 : ℝ) ^ (k.2.1)) ^ ((3 : ℝ) / 2)
        * ((2 : ℝ) ^ (k.2.2)) ^ ((7 : ℝ) / 2))
      ≤ 100 * (2 : ℝ) ^ (((7 : ℝ) / 2) * (N : ℝ)) := by
  classical
  set S := ((Finset.range (N + 1)).product
        ((Finset.range (N + 1)).product (Finset.range (N + 1)))).filter
        (fun k => k.1 + k.2.1 + k.2.2 ≤ N) with hS
  have hle : (∑ k ∈ S, ((2 : ℝ) ^ (k.1) * (2 : ℝ) ^ (k.2.1)) ^ ((3 : ℝ) / 2)
        * ((2 : ℝ) ^ (k.2.2)) ^ ((7 : ℝ) / 2))
      ≤ ∑ k ∈ S,
          ((2 : ℝ) ^ (((7 : ℝ) / 2) * (N : ℝ)) * ((1 : ℝ) / 4) ^ (N - k.2.2)) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [hS] at hk
    exact caseB_term_le N k.1 k.2.1 k.2.2 (Finset.mem_filter.mp hk).2
  have hfactor : ∑ k ∈ S,
        ((2 : ℝ) ^ (((7 : ℝ) / 2) * (N : ℝ)) * ((1 : ℝ) / 4) ^ (N - k.2.2))
      = (2 : ℝ) ^ (((7 : ℝ) / 2) * (N : ℝ))
        * ∑ k ∈ S, ((1 : ℝ) / 4) ^ (N - k.2.2) := by
    rw [Finset.mul_sum]
  have hB : ∑ k ∈ S, ((1 : ℝ) / 4) ^ (N - k.2.2) ≤ 100 := by
    rw [hS]; exact caseB_geom N
  have hnonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (((7 : ℝ) / 2) * (N : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc (∑ k ∈ S, ((2 : ℝ) ^ (k.1) * (2 : ℝ) ^ (k.2.1)) ^ ((3 : ℝ) / 2)
          * ((2 : ℝ) ^ (k.2.2)) ^ ((7 : ℝ) / 2))
      ≤ ∑ k ∈ S,
          ((2 : ℝ) ^ (((7 : ℝ) / 2) * (N : ℝ)) * ((1 : ℝ) / 4) ^ (N - k.2.2)) := hle
    _ = (2 : ℝ) ^ (((7 : ℝ) / 2) * (N : ℝ))
          * ∑ k ∈ S, ((1 : ℝ) / 4) ^ (N - k.2.2) := hfactor
    _ ≤ (2 : ℝ) ^ (((7 : ℝ) / 2) * (N : ℝ)) * 100 :=
        mul_le_mul_of_nonneg_left hB hnonneg
    _ = 100 * (2 : ℝ) ^ (((7 : ℝ) / 2) * (N : ℝ)) := by rw [mul_comm]

end Work.HP.MDEstimates
