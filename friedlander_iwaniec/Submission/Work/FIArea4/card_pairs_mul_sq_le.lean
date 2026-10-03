import Mathlib
import Submission.Work.FIArea4.SqfreeKernel
import Submission.Work.FIArea4.sqfree_kernel
import Submission.Work.FIArea4.sqfreeKernel_eq_of_mul_sq
import Submission.Work.FIArea4.card_sqfreeKernel_eq_le_sqrt
import Submission.Work.FIArea4.sum_sqrt_div_mul_le

namespace Work.FIArea4

open scoped BigOperators

/-- The number of pairs `(r₁, r₂) ∈ [1,R] × [1,R']` with `r₁ * r₂` a perfect square (written in the
decidable form `Nat.sqrt (p.1*p.2)^2 = p.1*p.2`) is `O(√(R R') log(min R R'))`.  Proof sketch:
write `r = sqfreeKernel r * (sqPart r)^2`; if `r₁ r₂` is a square then `sqfreeKernel r₁ = sqfreeKernel r₂ = d`,
and the number of `r ≤ R` with `sqfreeKernel r = d` is `≤ √(R/d)`, so the count is
`≤ ∑_d √(R/d)√(R'/d) ≤ √(R R') ∑_{d ≤ min R R'} 1/d ≤ √(R R')(1 + log(min R R'))`. -/
theorem card_pairs_mul_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (R R' : ℕ), 1 ≤ R → 1 ≤ R' →
      (((Finset.Icc 1 R).product (Finset.Icc 1 R')).filter
          (fun p : ℕ × ℕ => Nat.sqrt (p.1 * p.2) ^ 2 = p.1 * p.2)).card
        ≤ C * Real.sqrt ((R : ℝ) * (R' : ℝ))
            * (Real.log (min (R : ℝ) (R' : ℝ)) + 1) := by
  refine ⟨1, one_pos, ?_⟩
  intro R R' hR hR'
  set S : Finset (ℕ × ℕ) := ((Finset.Icc 1 R).product (Finset.Icc 1 R')).filter
      (fun p : ℕ × ℕ => Nat.sqrt (p.1 * p.2) ^ 2 = p.1 * p.2) with hS
  -- ## Step 1: group the pairs by the common value of the squarefree kernel
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => sqfreeKernel p.1) (↑S : Set (ℕ × ℕ))
      (↑(Finset.Icc 1 (min R R')) : Set ℕ) := by
    intro p hp
    rw [hS] at hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.product_eq_sprod]
      at hp
    obtain ⟨⟨hpR, hpR'⟩, hsq⟩ := hp
    have h1a : 1 ≤ p.1 := (Finset.mem_Icc.mp hpR).1
    have h1b : 1 ≤ p.2 := (Finset.mem_Icc.mp hpR').1
    have h2a : p.1 ≤ R := (Finset.mem_Icc.mp hpR).2
    have h2b : p.2 ≤ R' := (Finset.mem_Icc.mp hpR').2
    -- the two kernels agree because `p.1 * p.2` is a square
    have hker : sqfreeKernel p.1 = sqfreeKernel p.2 :=
      sqfreeKernel_eq_of_mul_sq p.1 p.2 h1a h1b ⟨_, hsq.symm⟩
    obtain ⟨-, -, -, hdv1, -⟩ := sqfree_kernel p.1 (by omega)
    obtain ⟨-, -, -, hdv2, -⟩ := sqfree_kernel p.2 (by omega)
    have hk1 : sqfreeKernel p.1 ≤ p.1 := Nat.le_of_dvd (by omega) hdv1
    have hk2 : sqfreeKernel p.2 ≤ p.2 := Nat.le_of_dvd (by omega) hdv2
    have hk2' : sqfreeKernel p.1 ≤ p.2 := le_of_eq_of_le hker hk2
    simp only [Finset.mem_coe, Finset.mem_Icc]
    refine ⟨?_, le_min (le_trans hk1 h2a) (le_trans hk2' h2b)⟩
    by_contra hc
    have hc' : sqfreeKernel p.1 < 1 := not_le.mp hc
    have hz : sqfreeKernel p.1 = 0 := by omega
    obtain ⟨-, -, heq, -, -⟩ := sqfree_kernel p.1 (by omega)
    rw [hz] at heq
    simp at heq
    omega
  have hcard1 : S.card ≤ ∑ d ∈ Finset.Icc 1 (min R R'),
      (((Finset.Icc 1 R).filter (fun r => sqfreeKernel r = d)).card *
       ((Finset.Icc 1 R').filter (fun r => sqfreeKernel r = d)).card) := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_le_sum
    intro d hd
    have hsub : S.filter (fun p : ℕ × ℕ => sqfreeKernel p.1 = d) ⊆
        ((Finset.Icc 1 R).filter (fun r => sqfreeKernel r = d)) ×ˢ
        ((Finset.Icc 1 R').filter (fun r => sqfreeKernel r = d)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hpd⟩ := hp
      rw [hS] at hpS
      simp only [Finset.mem_filter, Finset.mem_product, Finset.product_eq_sprod] at hpS
      obtain ⟨⟨hpR, hpR'⟩, hsq⟩ := hpS
      have h1a : 1 ≤ p.1 := (Finset.mem_Icc.mp hpR).1
      have h1b : 1 ≤ p.2 := (Finset.mem_Icc.mp hpR').1
      have hker : sqfreeKernel p.1 = sqfreeKernel p.2 :=
        sqfreeKernel_eq_of_mul_sq p.1 p.2 h1a h1b ⟨_, hsq.symm⟩
      simp only [Finset.mem_product, Finset.mem_filter]
      exact ⟨⟨hpR, hpd⟩, ⟨hpR', by rw [← hker]; exact hpd⟩⟩
    calc (S.filter (fun p : ℕ × ℕ => sqfreeKernel p.1 = d)).card
        ≤ (((Finset.Icc 1 R).filter (fun r => sqfreeKernel r = d)) ×ˢ
           ((Finset.Icc 1 R').filter (fun r => sqfreeKernel r = d))).card :=
          Finset.card_le_card hsub
      _ = (((Finset.Icc 1 R).filter (fun r => sqfreeKernel r = d)).card *
           ((Finset.Icc 1 R').filter (fun r => sqfreeKernel r = d)).card) :=
          Finset.card_product _ _
  -- ## Step 2: each fiber has at most `√(N/d)` elements, so the sum is bounded by `∑ √(R/d)√(R'/d)`
  have hcard2 : (S.card : ℝ) ≤ ∑ d ∈ Finset.Icc 1 (min R R'),
      Real.sqrt ((R : ℝ) / (d : ℝ)) * Real.sqrt ((R' : ℝ) / (d : ℝ)) := by
    have hcast : (S.card : ℝ) ≤ ((∑ d ∈ Finset.Icc 1 (min R R'),
        (((Finset.Icc 1 R).filter (fun r => sqfreeKernel r = d)).card *
         ((Finset.Icc 1 R').filter (fun r => sqfreeKernel r = d)).card) : ℕ) : ℝ) := by
      exact_mod_cast hcard1
    refine hcast.trans ?_
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    rw [Nat.cast_mul]
    exact mul_le_mul (card_sqfreeKernel_eq_le_sqrt R d hd1)
      (card_sqfreeKernel_eq_le_sqrt R' d hd1) (by positivity) (Real.sqrt_nonneg _)
  -- ## Step 3: the resulting sum is `√(R R') · ∑ 1/d ≤ √(R R') (log(min R R') + 1)`
  calc (S.card : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 (min R R'),
          Real.sqrt ((R : ℝ) / (d : ℝ)) * Real.sqrt ((R' : ℝ) / (d : ℝ)) := hcard2
    _ ≤ Real.sqrt ((R : ℝ) * (R' : ℝ)) * (Real.log (min (R : ℝ) (R' : ℝ)) + 1) :=
        sum_sqrt_div_mul_le R R' hR hR'
    _ = 1 * Real.sqrt ((R : ℝ) * (R' : ℝ)) * (Real.log (min (R : ℝ) (R' : ℝ)) + 1) := by
        ring

end Work.FIArea4
