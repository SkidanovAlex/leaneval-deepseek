import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs
import Submission.Work.NumberTheory.Chen.BTermCount.Basic

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

open Commons.NumberTheory.Chen.ChenEight

attribute [local instance] Classical.propDecidable

/-- **Uniqueness of the ordered factorisation of an integer as a product of two primes.**
If `a ≤ b` and `a' ≤ b'` are primes with `a * b = a' * b'`, then `a = a'` and `b = b'`. -/
theorem prime_pair_unique {a b a' b' : ℕ} (ha : a.Prime) (_hb : b.Prime) (ha' : a'.Prime)
    (hb' : b'.Prime) (hab : a ≤ b) (hab' : a' ≤ b') (h : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have hd : a ∣ a' * b' := by rw [← h]; exact dvd_mul_right a b
  rcases ha.dvd_mul.mp hd with h1 | h1
  · have haa' : a' = a := (ha'.dvd_iff_eq ha.ne_one).mp h1
    subst haa'
    exact ⟨rfl, Nat.mul_left_cancel ha.pos h⟩
  · have hb'a : b' = a := (hb'.dvd_iff_eq ha.ne_one).mp h1
    have hba' : b = a' := by
      have h' : a * b = a * a' := by rw [h, hb'a, Nat.mul_comm a' a]
      exact Nat.mul_left_cancel ha.pos h'
    have haa' : a = a' := by omega
    exact ⟨haa', by omega⟩

/-- The map `t ↦ (t.1, t.2.1 * t.2.2)` is injective on `bTripleSet x M Y`. -/
theorem bTripleSet_pair_inj {x M Y : ℕ} {t t' : ℕ × ℕ × ℕ}
    (ht : t ∈ bTripleSet x M Y) (ht' : t' ∈ bTripleSet x M Y)
    (h1 : t.1 = t'.1) (h2 : t.2.1 * t.2.2 = t'.2.1 * t'.2.2) : t = t' := by
  obtain ⟨hq, hq₂, hq₃, -, -, -, hle, -⟩ := mem_bTripleSet.mp ht
  obtain ⟨hq', hq₂', hq₃', -, -, -, hle', -⟩ := mem_bTripleSet.mp ht'
  obtain ⟨ha, hb⟩ := prime_pair_unique hq₂ hq₃ hq₂' hq₃' hle hle' h2
  exact Prod.ext h1 (Prod.ext ha hb)

theorem BLodBilinear (x M Y r d : ℕ) [NeZero d] (hM : 1 ≤ M) (h : r ∣ d) (ψ : DirichletCharacter ℂ r) :
    (∑ t ∈ bTripleSet x M Y, (DirichletCharacter.changeLevel h ψ)
        (((t.1 * t.2.1 * t.2.2 : ℕ)) : ZMod d))
      = ∑ m ∈ Finset.Icc 1 ((x + 2) / M + 1), ∑ q ∈ Finset.Icc 1 Y,
          (if q * m ≤ x + 2 then (1 : ℂ) else 0) * aCoeff0C M Y d q * bCoeffC Y d m *
            ψ (((q * m : ℕ)) : ZMod r) := by
  classical
  have hMpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one hM
  set P : Finset (ℕ × ℕ) :=
    (bTripleSet x M Y).image (fun t : ℕ × ℕ × ℕ => (t.1, t.2.1 * t.2.2)) with hP
  set A : Finset (ℕ × ℕ) := Finset.Icc 1 Y ×ˢ Finset.Icc 1 ((x + 2) / M + 1) with hA
  -- Injectivity of the pair map on `bTripleSet`
  have hinj : Set.InjOn (fun t : ℕ × ℕ × ℕ => (t.1, t.2.1 * t.2.2)) ↑(bTripleSet x M Y) := by
    intro t ht t' ht' he
    exact bTripleSet_pair_inj ht ht' (by simpa using congrArg Prod.fst he)
      (by simpa using congrArg Prod.snd he)
  -- ## Step 1: the left-hand side becomes a sum over the pair-set `P`
  have hL : (∑ t ∈ bTripleSet x M Y, (DirichletCharacter.changeLevel h ψ)
        (((t.1 * t.2.1 * t.2.2 : ℕ)) : ZMod d))
      = ∑ p ∈ P, (DirichletCharacter.changeLevel h ψ) (((p.1 * p.2 : ℕ)) : ZMod d) := by
    rw [hP]
    have h1 : (∑ t ∈ bTripleSet x M Y, (DirichletCharacter.changeLevel h ψ)
          (((t.1 * t.2.1 * t.2.2 : ℕ)) : ZMod d))
        = ∑ t ∈ bTripleSet x M Y, (DirichletCharacter.changeLevel h ψ)
              (((t.1 * (t.2.1 * t.2.2) : ℕ)) : ZMod d) := by
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [Nat.mul_assoc]
    rw [h1]
    exact (Finset.sum_image (f := fun p : ℕ × ℕ =>
      (DirichletCharacter.changeLevel h ψ) (((p.1 * p.2 : ℕ)) : ZMod d)) hinj).symm
  -- ## Step 2: the right-hand side becomes a sum over the index set `A`
  have hR : (∑ m ∈ Finset.Icc 1 ((x + 2) / M + 1), ∑ q ∈ Finset.Icc 1 Y,
          (if q * m ≤ x + 2 then (1 : ℂ) else 0) * aCoeff0C M Y d q * bCoeffC Y d m *
            ψ (((q * m : ℕ)) : ZMod r))
      = ∑ p ∈ A, (if p.1 * p.2 ≤ x + 2 then (1 : ℂ) else 0) * aCoeff0C M Y d p.1 *
            bCoeffC Y d p.2 * ψ (((p.1 * p.2 : ℕ)) : ZMod r) := by
    rw [hA, Finset.sum_comm]
    exact (Finset.sum_product (Finset.Icc 1 Y) (Finset.Icc 1 ((x + 2) / M + 1))
      (fun p : ℕ × ℕ => (if p.1 * p.2 ≤ x + 2 then (1 : ℂ) else 0) * aCoeff0C M Y d p.1 *
            bCoeffC Y d p.2 * ψ (((p.1 * p.2 : ℕ)) : ZMod r))).symm
  -- ## Step 3: `P ⊆ A`
  have hsub : P ⊆ A := by
    intro p hp
    rw [hP] at hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    rw [hA, Finset.mem_product]
    obtain ⟨hq, hq₂, hq₃, hMq, hqY, hYq₂, hq₂q₃, hprod⟩ := mem_bTripleSet.mp ht
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨le_trans hM hMq, le_of_lt hqY⟩
    · rw [Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hq₂.ne_zero hq₃.ne_zero)
      · have hMm : (t.2.1 * t.2.2) * M ≤ x + 2 := by
          calc (t.2.1 * t.2.2) * M ≤ (t.2.1 * t.2.2) * t.1 := Nat.mul_le_mul_left _ hMq
            _ = t.1 * t.2.1 * t.2.2 := by ring
            _ ≤ x + 2 := hprod
        have hd : t.2.1 * t.2.2 ≤ (x + 2) / M := (Nat.le_div_iff_mul_le hMpos).mpr hMm
        omega
  -- ## Step 4: a pair satisfying all the definiteness conditions lies in `P`
  have hP_mem : ∀ p : ℕ × ℕ, p.1 * p.2 ≤ x + 2 →
      (p.1.Prime ∧ M ≤ p.1 ∧ p.1 < Y) →
      (∃ q₂ q₃ : ℕ, q₂.Prime ∧ q₃.Prime ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ q₂ * q₃ = p.2) →
      p ∈ P := by
    intro p h1 h2 h3
    rw [hP]
    obtain ⟨q₂, q₃, hq₂, hq₃, hYq₂, hle, hm⟩ := h3
    obtain ⟨hqp, hMq, hqY⟩ := h2
    refine Finset.mem_image.mpr ⟨(p.1, q₂, q₃), ?_, ?_⟩
    · refine mem_bTripleSet.mpr ⟨hqp, hq₂, hq₃, hMq, hqY, hYq₂, hle, ?_⟩
      rw [Nat.mul_assoc, hm]
      exact h1
    · exact Prod.ext rfl hm
  -- ## Step 5: the summand vanishes off `P`
  have hzero : ∀ p ∈ A, p ∉ P →
      (if p.1 * p.2 ≤ x + 2 then (1 : ℂ) else 0) * aCoeff0C M Y d p.1 *
            bCoeffC Y d p.2 * ψ (((p.1 * p.2 : ℕ)) : ZMod r) = 0 := by
    intro p _ hpP
    by_cases h1 : p.1 * p.2 ≤ x + 2
    · by_cases h2 : p.1.Prime ∧ M ≤ p.1 ∧ p.1 < Y
      · by_cases h3 : ∃ q₂ q₃ : ℕ, q₂.Prime ∧ q₃.Prime ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ q₂ * q₃ = p.2
        · exact absurd (hP_mem p h1 h2 h3) hpP
        · have hb : bCoeffC Y d p.2 = 0 := by
            rw [bCoeffC_eq]
            have h0 : bCoeff Y p.2 = 0 := by
              unfold bCoeff
              rw [if_neg h3]
            rw [h0, zero_mul]
          rw [if_pos h1, hb]
          simp only [mul_zero, zero_mul]
      · have ha : aCoeff0C M Y d p.1 = 0 := by
          rw [aCoeff0C_eq]
          have h0 : aCoeff0 M Y p.1 = 0 := by
            unfold aCoeff0
            rw [if_neg h2]
          rw [h0, zero_mul]
        rw [if_pos h1, ha]
        simp only [mul_zero, zero_mul]
    · rw [if_neg h1]
      simp only [zero_mul]
  -- ## Step 6: on `P` the summand equals the character value
  have hPF : ∀ p ∈ P,
      (if p.1 * p.2 ≤ x + 2 then (1 : ℂ) else 0) * aCoeff0C M Y d p.1 *
            bCoeffC Y d p.2 * ψ (((p.1 * p.2 : ℕ)) : ZMod r)
        = (DirichletCharacter.changeLevel h ψ) (((p.1 * p.2 : ℕ)) : ZMod d) := by
    intro p hp
    rw [hP] at hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    dsimp only
    obtain ⟨hq, hq₂, hq₃, hMq, hqY, hYq₂, hle, hprod⟩ := mem_bTripleSet.mp ht
    have hif : t.1 * (t.2.1 * t.2.2) ≤ x + 2 := by rw [← Nat.mul_assoc]; exact hprod
    have ha : aCoeff0C M Y d t.1 = (if Nat.Coprime t.1 d then (1 : ℂ) else 0) := by
      rw [aCoeff0C_eq]
      have h1 : aCoeff0 M Y t.1 = 1 := by
        unfold aCoeff0
        rw [if_pos ⟨hq, hMq, hqY⟩]
      rw [h1, one_mul]
    have hb : bCoeffC Y d (t.2.1 * t.2.2)
        = (if Nat.Coprime (t.2.1 * t.2.2) d then (1 : ℂ) else 0) := by
      rw [bCoeffC_eq]
      have h1 : bCoeff Y (t.2.1 * t.2.2) = 1 := by
        unfold bCoeff
        rw [if_pos ⟨t.2.1, t.2.2, hq₂, hq₃, hYq₂, hle, rfl⟩]
      rw [h1, one_mul]
    rw [if_pos hif, ha, hb, changeLevel_apply_nat h ψ (t.1 * (t.2.1 * t.2.2))]
    by_cases hc : Nat.Coprime (t.1 * (t.2.1 * t.2.2)) d
    · have hc1 : Nat.Coprime t.1 d := (Nat.coprime_mul_iff_left.mp hc).1
      have hc2 : Nat.Coprime (t.2.1 * t.2.2) d := (Nat.coprime_mul_iff_left.mp hc).2
      rw [if_pos hc, if_pos hc1, if_pos hc2]
      ring
    · have hnot : ¬ (Nat.Coprime t.1 d ∧ Nat.Coprime (t.2.1 * t.2.2) d) :=
        fun hh => hc (Nat.Coprime.mul_left hh.1 hh.2)
      by_cases hc1 : Nat.Coprime t.1 d <;> by_cases hc2 : Nat.Coprime (t.2.1 * t.2.2) d
      · exact absurd ⟨hc1, hc2⟩ hnot
      · rw [if_neg hc, if_pos hc1, if_neg hc2]; ring
      · rw [if_neg hc, if_neg hc1]; ring
      · rw [if_neg hc, if_neg hc1]; ring
  -- ## Assembly
  rw [hL, hR]
  exact ((Finset.sum_congr rfl hPF).symm).trans (Finset.sum_subset hsub hzero)

end Work.NumberTheory.Chen.BTermCount
