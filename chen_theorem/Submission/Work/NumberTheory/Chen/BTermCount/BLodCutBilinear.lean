import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodCut
import Submission.Work.NumberTheory.Chen.BTermCount.BLodTripleInj
import Submission.Work.NumberTheory.Chen.BTermCount.BLodBlockSplit
import Submission.Work.NumberTheory.Chen.BTermCount.BLodSmallLargeSplit
import Submission.Work.NumberTheory.Chen.BTermCount.BLodBilinearCut

namespace Work.NumberTheory.Chen.BTermCount

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-!
# The cut bilinear form of the `B`-term, in dyadic-block form

`BLodBilinearCut` evaluates the twisted character sum over the multiples of `t₁ t₂` in
`B̄ = bProdSet x M Y` as a bilinear form in the plain (unblocked) `a`-coefficient
`aCoeff0 M Y ·`, cut by `t₁ ∣ ·`.  The block decomposition of the plain `a`-coefficient
(`BLodBlockSplit`) turns that bilinear form into the sum, over the dyadic blocks
`j < blockCount M Y`, of the bilinear forms in the *blocked* cut coefficients
`aCut M Y j t₁`:

  `aCoeff0 M Y · * [t₁ ∣ ·] = ∑_{j < blockCount M Y} aCut M Y j t₁ ·`.

That is the identity proved here, in the shape needed by the large-sieve estimate
(`BLodCutLS`).
-/

/-- Two sums over finite sets agree when the support of the summand lies in both. -/
theorem sum_eq_sum_of_support_subset {α : Type*} (s t : Finset α) (f : α → ℂ)
    (h : ∀ a, f a ≠ 0 → a ∈ s ∧ a ∈ t) : ∑ a ∈ s, f a = ∑ a ∈ t, f a := by
  have h1 : ∑ a ∈ s ∩ t, f a = ∑ a ∈ s, f a :=
    Finset.sum_subset Finset.inter_subset_left (fun a ha hna => by
      by_contra hf
      exact hna (Finset.mem_inter.mpr ⟨ha, (h a hf).2⟩))
  have h2 : ∑ a ∈ s ∩ t, f a = ∑ a ∈ t, f a :=
    Finset.sum_subset Finset.inter_subset_right (fun a ha hna => by
      by_contra hf
      exact hna (Finset.mem_inter.mpr ⟨(h a hf).1, ha⟩))
  exact h1.symm.trans h2

/-- The plain `a`-coefficient cut by the divisibility condition `t₁ ∣ ·` is the sum, over
the dyadic blocks `j < blockCount M Y`, of the blocked cut coefficients `aCut M Y j t₁`. -/
theorem aCoeff0_mul_ite_eq_sum_aCut (M Y t₁ q : ℕ) (hM : 1 ≤ M) :
    aCoeff0 M Y q * (if t₁ ∣ q then (1 : ℂ) else 0)
      = ∑ j ∈ Finset.range (blockCount M Y), aCut M Y j t₁ q := by
  have hbs : aCoeff0 M Y q = ∑ j ∈ Finset.range (blockCount M Y), aCoeff M Y j q := by
    have h := BLodBlockSplit M Y 1 q hM
    rw [aCoeff0C, if_pos (Nat.coprime_one_right q), mul_one] at h
    refine h.trans ?_
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [aCoeffC, if_pos (Nat.coprime_one_right q), mul_one]
  rw [hbs, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [aCut]

/-- The bilinear form of `BLodLargeSieve`, written as a sum over the product of its two
index ranges. -/
theorem bilinForm_eq_sum_product (U V y : ℕ) (a b : ℕ → ℂ) (r : ℕ)
    (ψ : DirichletCharacter ℂ r) :
    bilinForm U V y a b r ψ
      = ∑ p ∈ Finset.Icc 1 U ×ˢ Finset.Icc 1 V,
          (if p.1 * p.2 ≤ y then (1 : ℂ) else 0) * a p.1 * b p.2
            * ψ (((p.1 * p.2 : ℕ)) : ZMod r) := by
  rw [bilinForm, Finset.sum_product]

attribute [local instance] Classical.propDecidable
theorem BLodCutBilinear (x M Y r t₁ t₂ : ℕ) (hM : 1 ≤ M) (ψ : DirichletCharacter ℂ r)
    (h₁ : ∀ p : ℕ, p.Prime → p ∣ t₁ → p < Y) (h₂ : ∀ p : ℕ, p.Prime → p ∣ t₂ → Y ≤ p) :
    (∑ n ∈ (bProdSet x M Y).filter (fun n => t₁ * t₂ ∣ n), ψ ((n:ℕ) : ZMod r))
      = ∑ j ∈ Finset.range (blockCount M Y),
          bilinForm (2 * blockStart M j) ((x + 2) / blockStart M j + 1) (x + 2)
            (aCut M Y j t₁) (bCut Y t₂) r ψ := by
  classical
  -- the unblocked cut bilinear form of `BLodBilinearCut`
  rw [BLodBilinearCut x M Y r t₁ t₂ hM ψ h₁ h₂]
  -- the plain cut `a`-coefficient is the sum of the blocked cut coefficients
  have hstep : ∀ q m : ℕ,
      (if q * m ≤ x + 2 then (1 : ℂ) else 0)
        * (aCoeff0 M Y q * (if t₁ ∣ q then (1 : ℂ) else 0))
        * (bCoeff Y m * (if t₂ ∣ m then (1 : ℂ) else 0))
        * ψ (((q * m : ℕ)) : ZMod r)
      = ∑ j ∈ Finset.range (blockCount M Y),
          (if q * m ≤ x + 2 then (1 : ℂ) else 0) * aCut M Y j t₁ q * bCut Y t₂ m
            * ψ (((q * m : ℕ)) : ZMod r) := by
    intro q m
    rw [aCoeff0_mul_ite_eq_sum_aCut M Y t₁ q hM, Finset.mul_sum]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [bCut]
  simp only [hstep]
  -- reassociate the double sum as a sum over the product of the two ranges, and commute
  -- the block index out to the front
  have hprod : (∑ q ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 ((x + 2) / M + 1),
        ∑ j ∈ Finset.range (blockCount M Y),
          (if q * m ≤ x + 2 then (1 : ℂ) else 0) * aCut M Y j t₁ q * bCut Y t₂ m
            * ψ (((q * m : ℕ)) : ZMod r))
      = ∑ p ∈ Finset.Icc 1 Y ×ˢ Finset.Icc 1 ((x + 2) / M + 1),
          ∑ j ∈ Finset.range (blockCount M Y),
            (if p.1 * p.2 ≤ x + 2 then (1 : ℂ) else 0) * aCut M Y j t₁ p.1 * bCut Y t₂ p.2
              * ψ (((p.1 * p.2 : ℕ)) : ZMod r) :=
    (Finset.sum_product (s := Finset.Icc 1 Y) (t := Finset.Icc 1 ((x + 2) / M + 1))
      (f := fun p : ℕ × ℕ => ∑ j ∈ Finset.range (blockCount M Y),
        (if p.1 * p.2 ≤ x + 2 then (1 : ℂ) else 0) * aCut M Y j t₁ p.1 * bCut Y t₂ p.2
          * ψ (((p.1 * p.2 : ℕ)) : ZMod r))).symm
  rw [hprod, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [bilinForm_eq_sum_product]
  -- the summands vanish away from the support of the two cut coefficients, which is
  -- contained in both index boxes
  refine sum_eq_sum_of_support_subset _ _ _ (fun p hp => ?_)
  have hp' :
      (if p.1 * p.2 ≤ x + 2 then (1 : ℂ) else 0) * aCut M Y j t₁ p.1 * bCut Y t₂ p.2
        * ψ (((p.1 * p.2 : ℕ)) : ZMod r) ≠ 0 := hp
  have hA : aCut M Y j t₁ p.1 ≠ 0 := fun h0 => hp' (by simp [h0])
  have hB : bCut Y t₂ p.2 ≠ 0 := fun h0 => hp' (by simp [h0])
  have hC : (if p.1 * p.2 ≤ x + 2 then (1 : ℂ) else 0) ≠ 0 := fun h0 => hp' (by simp [h0])
  have hcle : p.1 * p.2 ≤ x + 2 := by
    by_contra hlt
    exact hC (by rw [if_neg hlt])
  -- unpack the `a`-coefficient: `p.1` is a prime of the window block `j`
  have hA' : aCoeff M Y j p.1 ≠ 0 := fun h0 => hA (by simp [aCut, h0])
  have hcondA :
      p.1.Prime ∧ M ≤ p.1 ∧ p.1 < Y ∧ blockStart M j ≤ p.1 ∧ p.1 < 2 * blockStart M j := by
    by_contra hc
    exact hA' (by rw [aCoeff, if_neg hc])
  obtain ⟨hp1, hMp1, hp1Y, hbp1, hbp1'⟩ := hcondA
  -- unpack the `b`-coefficient: `p.2` is a product of two primes `≥ Y`
  have hB' : bCoeff Y p.2 ≠ 0 := fun h0 => hB (by simp [bCut, h0])
  obtain ⟨q₂, q₃, hq₂, hq₃, hYq₂, hle, hprod'⟩ : ∃ q₂ q₃ : ℕ,
      q₂.Prime ∧ q₃.Prime ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ q₂ * q₃ = p.2 := by
    by_contra hb
    exact hB' (by rw [bCoeff, if_neg hb])
  have hp1pos : 0 < p.1 := by omega
  have hbs1 : 0 < blockStart M j := by
    unfold blockStart
    exact Nat.mul_pos (by omega) (pow_pos (by norm_num) j)
  have hge1 : 1 ≤ p.2 := by
    have : 1 ≤ q₂ * q₃ := by nlinarith [hq₂.two_le, hq₃.two_le]
    omega
  have hdiv : p.2 ≤ (x + 2) / p.1 :=
    (Nat.le_div_iff_mul_le hp1pos).mpr (by rw [mul_comm]; exact hcle)
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨by omega, le_of_lt hp1Y⟩, hge1, ?_⟩
    have h2 : (x + 2) / p.1 ≤ (x + 2) / M := Nat.div_le_div_left hMp1 (by omega)
    omega
  · rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨by omega, le_of_lt hbp1'⟩, hge1, ?_⟩
    have h2 : (x + 2) / p.1 ≤ (x + 2) / blockStart M j := Nat.div_le_div_left hbp1 hbs1
    omega

end Work.NumberTheory.Chen.BTermCount
