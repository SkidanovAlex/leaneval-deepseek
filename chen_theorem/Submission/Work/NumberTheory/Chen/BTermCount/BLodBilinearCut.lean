import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs
import Submission.Work.NumberTheory.Chen.BTermCount.bRemCorrCharSum
import Submission.Work.NumberTheory.Chen.BTermCount.BLodBilinear

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# The cut bilinear form of the `B`-term

This module proves `BLodBilinearCut`: the version of the bilinear decomposition of the ternary
sequence `B̄ = bProdSet x M Y` in which the level of distribution is *cut down* by two moduli
`t₁` and `t₂` whose prime divisors are separated by the sift limit `Y`:

* every prime factor of `t₁` is `< Y`, hence can only divide the *small* prime `q ∈ [M,Y)`
  of a `B`-triple;
* every prime factor of `t₂` is `≥ Y`, hence can only divide the product `q₂ q₃` of the two
  *large* primes.

Consequently `t₁ t₂ ∣ q q₂ q₃` is equivalent to `t₁ ∣ q` and `t₂ ∣ q₂ q₃`, and the twisted
character sum over the multiples of `t₁ t₂` in `B̄` factors into the two coefficient sequences
`aCoeff0 · · · (if t₁ ∣ · then 1 else 0)` and `bCoeff · · · (if t₂ ∣ · then 1 else 0)`.
-/

/-- **Splitting of a divisor according to size of prime factors.**
If every prime divisor of `t₁` is `< Y` and every prime divisor of `t₂` is `≥ Y`, while
`q`, `q₂`, `q₃` are primes with `q < Y ≤ q₂` and `q < Y ≤ q₃`, then `t₁ t₂ ∣ q q₂ q₃` holds
exactly when `t₁ ∣ q` and `t₂ ∣ q₂ q₃`. -/
theorem dvd_mul_iff_dvd_left_and_right {Y t₁ t₂ q q₂ q₃ : ℕ}
    (h₁ : ∀ p : ℕ, p.Prime → p ∣ t₁ → p < Y)
    (h₂ : ∀ p : ℕ, p.Prime → p ∣ t₂ → Y ≤ p)
    (hq : q.Prime) (hq₂ : q₂.Prime) (hq₃ : q₃.Prime)
    (hqY : q < Y) (hYq₂ : Y ≤ q₂) (hYq₃ : Y ≤ q₃) :
    t₁ * t₂ ∣ q * (q₂ * q₃) ↔ t₁ ∣ q ∧ t₂ ∣ q₂ * q₃ := by
  constructor
  · intro h
    have h1 : t₁ ∣ q * (q₂ * q₃) := dvd_trans (dvd_mul_right t₁ t₂) h
    have h2 : t₂ ∣ q * (q₂ * q₃) := dvd_trans (dvd_mul_left t₂ t₁) h
    -- every prime divisor of `t₁` is `< Y`, so `t₁` is coprime to `q₂ q₃`
    have hc₁ : t₁.Coprime (q₂ * q₃) := by
      by_contra hc
      obtain ⟨r, hr, hrq, hrt⟩ := (not_coprime_iff_exists_prime_dvd t₁ (q₂ * q₃)).mp hc
      have hrY : r < Y := h₁ r hr hrt
      rcases (hr.dvd_mul.mp hrq) with hd | hd
      · have hqr : q₂ = r := (hq₂.dvd_iff_eq hr.ne_one).mp hd
        omega
      · have hqr : q₃ = r := (hq₃.dvd_iff_eq hr.ne_one).mp hd
        omega
    -- every prime divisor of `t₂` is `≥ Y > q`, so `t₂` is coprime to the prime `q`
    have hc₂ : t₂.Coprime q := by
      have hc₂' : q.Coprime t₂ := by
        by_contra hc
        obtain ⟨r, hr, hrt, hrq⟩ := (not_coprime_iff_exists_prime_dvd q t₂).mp hc
        have hqr : q = r := (hq.dvd_iff_eq hr.ne_one).mp hrq
        have hr' : Y ≤ r := h₂ r hr hrt
        omega
      exact hc₂'.symm
    exact ⟨Nat.Coprime.dvd_of_dvd_mul_right hc₁ h1, Nat.Coprime.dvd_of_dvd_mul_left hc₂ h2⟩
  · rintro ⟨ha, hb⟩
    exact mul_dvd_mul ha hb

/-- The product of the two `{0,1}`-valued divisibility indicators is the indicator of the
product divisibility. -/
theorem ite_mul_ite_dvd_eq (a b c d : ℕ) (h : a * b ∣ c * d ↔ a ∣ c ∧ b ∣ d) :
    (if a ∣ c then (1 : ℂ) else 0) * (if b ∣ d then (1 : ℂ) else 0)
      = (if a * b ∣ c * d then (1 : ℂ) else 0) := by
  by_cases hab : a * b ∣ c * d
  · rw [if_pos hab, if_pos (h.mp hab).1, if_pos (h.mp hab).2, mul_one]
  · rw [if_neg hab]
    by_cases hac : a ∣ c
    · by_cases hbd : b ∣ d
      · exact absurd (h.mpr ⟨hac, hbd⟩) hab
      · rw [if_pos hac, if_neg hbd, mul_zero]
    · rw [if_neg hac, zero_mul]

/-- The product map `t ↦ t.1 * t.2.1 * t.2.2` is injective on `bTripleSet x M Y`
(by uniqueness of the factorisation into primes). -/
theorem bTripleSet_prod_inj {x M Y : ℕ} {t t' : ℕ × ℕ × ℕ}
    (ht : t ∈ bTripleSet x M Y) (ht' : t' ∈ bTripleSet x M Y)
    (h : t.1 * t.2.1 * t.2.2 = t'.1 * t'.2.1 * t'.2.2) : t = t' := by
  obtain ⟨hq, hq₂, hq₃, hMq, hqY, hYq₂, hle, hprod⟩ := mem_bTripleSet.mp ht
  obtain ⟨hq', hq₂', hq₃', hMq', hqY', hYq₂', hle', hprod'⟩ := mem_bTripleSet.mp ht'
  have hYq₃' : Y ≤ t'.2.2 := le_trans hYq₂' hle'
  have ha : t.1 * (t.2.1 * t.2.2) = t'.1 * (t'.2.1 * t'.2.2) := by
    simpa only [Nat.mul_assoc] using h
  have hdvd : t.1 ∣ t'.1 * (t'.2.1 * t'.2.2) := by
    rw [← ha]; exact dvd_mul_right t.1 (t.2.1 * t.2.2)
  -- the prime `t.1 < Y` can only divide the prime `t'.1`
  have h1 : t.1 = t'.1 := by
    rcases (hq.dvd_mul.mp hdvd) with h | h
    · exact ((hq'.dvd_iff_eq hq.ne_one).mp h).symm
    · rcases (hq.dvd_mul.mp h) with hh | hh
      · have he : t'.2.1 = t.1 := (hq₂'.dvd_iff_eq hq.ne_one).mp hh
        omega
      · have he : t'.2.2 = t.1 := (hq₃'.dvd_iff_eq hq.ne_one).mp hh
        omega
  have h2 : t.2.1 * t.2.2 = t'.2.1 * t'.2.2 := by
    rw [h1] at ha
    exact Nat.mul_left_cancel hq'.pos ha
  obtain ⟨ha', hb'⟩ := prime_pair_unique hq₂ hq₃ hq₂' hq₃' hle hle' h2
  exact Prod.ext h1 (Prod.ext ha' hb')

/-- **The cut bilinear form of the `B`-term.**

For a Dirichlet character `ψ` of level `r` and moduli `t₁`, `t₂` whose prime divisors are
separated by the sift limit `Y` (all prime divisors of `t₁` below `Y`, all prime divisors of
`t₂` at least `Y`), the twisted character sum over the elements of `B̄ = bProdSet x M Y`
divisible by `t₁ t₂` equals the bilinear form in the coefficients `aCoeff0`, `bCoeff` cut by
`t₁`, `t₂`. -/
theorem BLodBilinearCut (x M Y r t₁ t₂ : ℕ) (hM : 1 ≤ M) (ψ : DirichletCharacter ℂ r)
    (h₁ : ∀ p : ℕ, p.Prime → p ∣ t₁ → p < Y) (h₂ : ∀ p : ℕ, p.Prime → p ∣ t₂ → Y ≤ p) :
    (∑ n ∈ (bProdSet x M Y).filter (fun n => t₁ * t₂ ∣ n), ψ ((n:ℕ) : ZMod r))
      = ∑ q ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 ((x + 2) / M + 1),
          (if q * m ≤ x + 2 then (1:ℂ) else 0)
            * (aCoeff0 M Y q * (if t₁ ∣ q then (1:ℂ) else 0))
            * (bCoeff Y m * (if t₂ ∣ m then (1:ℂ) else 0))
            * ψ ((q * m : ℕ) : ZMod r) := by
  classical
  have hMpos : 0 < M := lt_of_lt_of_le Nat.zero_lt_one hM
  -- injectivity of the pair map `t ↦ (t.1, t.2.1 * t.2.2)` on `bTripleSet`
  have hinj : Set.InjOn (fun t : ℕ × ℕ × ℕ => (t.1, t.2.1 * t.2.2)) ↑(bTripleSet x M Y) := by
    intro t ht t' ht' he
    exact bTripleSet_pair_inj ht ht' (by simpa using congrArg Prod.fst he)
      (by simpa using congrArg Prod.snd he)
  -- injectivity of the product map `t ↦ t.1 * t.2.1 * t.2.2` on `bTripleSet`
  have hinjProd : Set.InjOn (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2)
      ↑(bTripleSet x M Y) := fun t ht t' ht' h => bTripleSet_prod_inj ht ht' h
  set P : Finset (ℕ × ℕ) :=
    (bTripleSet x M Y).image (fun t : ℕ × ℕ × ℕ => (t.1, t.2.1 * t.2.2)) with hP
  set A : Finset (ℕ × ℕ) := Finset.Icc 1 Y ×ˢ Finset.Icc 1 ((x + 2) / M + 1) with hA
  set F : ℕ × ℕ → ℂ := fun p => (if p.1 * p.2 ≤ x + 2 then (1:ℂ) else 0)
        * (aCoeff0 M Y p.1 * (if t₁ ∣ p.1 then (1:ℂ) else 0))
        * (bCoeff Y p.2 * (if t₂ ∣ p.2 then (1:ℂ) else 0))
        * ψ (((p.1 * p.2 : ℕ)) : ZMod r) with hF
  -- ## The left-hand side as a sum over the `B`-triples
  have hL : (∑ n ∈ (bProdSet x M Y).filter (fun n => t₁ * t₂ ∣ n), ψ ((n:ℕ) : ZMod r))
      = ∑ t ∈ (bTripleSet x M Y).filter (fun t => t₁ * t₂ ∣ t.1 * t.2.1 * t.2.2),
          ψ (((t.1 * t.2.1 * t.2.2 : ℕ)) : ZMod r) := by
    rw [bProdSet, Finset.filter_image]
    refine Finset.sum_image (f := fun n : ℕ => ψ ((n:ℕ) : ZMod r))
      (g := fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2) ?_
    intro t ht t' ht' h
    exact hinjProd (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht').1 h
  -- ## `P ⊆ A`
  have hsub : P ⊆ A := by
    intro p hp
    rw [hP] at hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    rw [hA, Finset.mem_product]
    obtain ⟨hq, hq₂, hq₃, hMq, hqY, hYq₂, hle, hprod⟩ := mem_bTripleSet.mp ht
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
  -- ## A pair with a prime first coordinate in `[M,Y)` and a second coordinate a product of
  -- two primes `≥ Y` belongs to `P`
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
  -- ## The summand vanishes away from `P`
  have hzero : ∀ p ∈ A, p ∉ P → F p = 0 := by
    intro p _ hpP
    show (if p.1 * p.2 ≤ x + 2 then (1:ℂ) else 0)
        * (aCoeff0 M Y p.1 * (if t₁ ∣ p.1 then (1:ℂ) else 0))
        * (bCoeff Y p.2 * (if t₂ ∣ p.2 then (1:ℂ) else 0))
        * ψ (((p.1 * p.2 : ℕ)) : ZMod r) = 0
    by_cases hp1 : p.1 * p.2 ≤ x + 2
    · by_cases hp2 : p.1.Prime ∧ M ≤ p.1 ∧ p.1 < Y
      · by_cases hp3 : ∃ q₂ q₃ : ℕ, q₂.Prime ∧ q₃.Prime ∧ Y ≤ q₂ ∧ q₂ ≤ q₃ ∧ q₂ * q₃ = p.2
        · exact absurd (hP_mem p hp1 hp2 hp3) hpP
        · have hb : bCoeff Y p.2 = 0 := by
            rw [bCoeff, if_neg hp3]
          rw [if_pos hp1, hb]
          ring
      · have ha : aCoeff0 M Y p.1 = 0 := by
          rw [aCoeff0, if_neg hp2]
        rw [if_pos hp1, ha]
        ring
    · rw [if_neg hp1]
      ring
  -- ## On `P` the summand is the cut product
  have hPF : ∀ p ∈ P, F p =
      (if t₁ ∣ p.1 then (1:ℂ) else 0) * (if t₂ ∣ p.2 then (1:ℂ) else 0)
        * ψ (((p.1 * p.2 : ℕ)) : ZMod r) := by
    intro p hp
    rw [hP] at hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hq, hq₂, hq₃, hMq, hqY, hYq₂, hle, hprod⟩ := mem_bTripleSet.mp ht
    have hif : t.1 * (t.2.1 * t.2.2) ≤ x + 2 := by rw [← Nat.mul_assoc]; exact hprod
    have ha : aCoeff0 M Y t.1 = 1 := by rw [aCoeff0, if_pos ⟨hq, hMq, hqY⟩]
    have hb : bCoeff Y (t.2.1 * t.2.2) = 1 := by
      rw [bCoeff, if_pos ⟨t.2.1, t.2.2, hq₂, hq₃, hYq₂, hle, rfl⟩]
    show (if t.1 * (t.2.1 * t.2.2) ≤ x + 2 then (1:ℂ) else 0)
        * (aCoeff0 M Y t.1 * (if t₁ ∣ t.1 then (1:ℂ) else 0))
        * (bCoeff Y (t.2.1 * t.2.2) * (if t₂ ∣ t.2.1 * t.2.2 then (1:ℂ) else 0))
        * ψ (((t.1 * (t.2.1 * t.2.2) : ℕ)) : ZMod r)
      = (if t₁ ∣ t.1 then (1:ℂ) else 0) * (if t₂ ∣ t.2.1 * t.2.2 then (1:ℂ) else 0)
        * ψ (((t.1 * (t.2.1 * t.2.2) : ℕ)) : ZMod r)
    rw [if_pos hif, ha, hb]
    ring
  -- ## The right-hand side
  have hR : (∑ q ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 ((x + 2) / M + 1),
          (if q * m ≤ x + 2 then (1:ℂ) else 0)
            * (aCoeff0 M Y q * (if t₁ ∣ q then (1:ℂ) else 0))
            * (bCoeff Y m * (if t₂ ∣ m then (1:ℂ) else 0))
            * ψ ((q * m : ℕ) : ZMod r))
      = ∑ t ∈ (bTripleSet x M Y).filter (fun t => t₁ * t₂ ∣ t.1 * t.2.1 * t.2.2),
          ψ (((t.1 * t.2.1 * t.2.2 : ℕ)) : ZMod r) := by
    have step1 : (∑ q ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 ((x + 2) / M + 1),
          (if q * m ≤ x + 2 then (1:ℂ) else 0)
            * (aCoeff0 M Y q * (if t₁ ∣ q then (1:ℂ) else 0))
            * (bCoeff Y m * (if t₂ ∣ m then (1:ℂ) else 0))
            * ψ ((q * m : ℕ) : ZMod r)) = ∑ p ∈ A, F p := by
      rw [hA]
      exact (Finset.sum_product (Finset.Icc 1 Y) (Finset.Icc 1 ((x + 2) / M + 1)) F).symm
    have step2 : ∑ p ∈ A, F p = ∑ p ∈ P, F p := (Finset.sum_subset hsub hzero).symm
    have step3 : ∑ p ∈ P, F p = ∑ t ∈ bTripleSet x M Y, F (t.1, t.2.1 * t.2.2) := by
      rw [hP]
      exact Finset.sum_image hinj
    have step4 : ∑ t ∈ bTripleSet x M Y, F (t.1, t.2.1 * t.2.2)
        = ∑ t ∈ bTripleSet x M Y,
            (if t₁ * t₂ ∣ t.1 * t.2.1 * t.2.2 then (1:ℂ) else 0)
              * ψ (((t.1 * t.2.1 * t.2.2 : ℕ)) : ZMod r) := by
      refine Finset.sum_congr rfl (fun t ht => ?_)
      obtain ⟨hq, hq₂, hq₃, hMq, hqY, hYq₂, hle, hprod⟩ := mem_bTripleSet.mp ht
      have hYq₃ : Y ≤ t.2.2 := le_trans hYq₂ hle
      have hif : t.1 * (t.2.1 * t.2.2) ≤ x + 2 := by rw [← Nat.mul_assoc]; exact hprod
      have ha : aCoeff0 M Y t.1 = 1 := by rw [aCoeff0, if_pos ⟨hq, hMq, hqY⟩]
      have hb : bCoeff Y (t.2.1 * t.2.2) = 1 := by
        rw [bCoeff, if_pos ⟨t.2.1, t.2.2, hq₂, hq₃, hYq₂, hle, rfl⟩]
      have heq : t₁ * t₂ ∣ t.1 * (t.2.1 * t.2.2)
          ↔ t₁ ∣ t.1 ∧ t₂ ∣ t.2.1 * t.2.2 :=
        dvd_mul_iff_dvd_left_and_right h₁ h₂ hq hq₂ hq₃ hqY hYq₂ hYq₃
      have hit := ite_mul_ite_dvd_eq t₁ t₂ t.1 (t.2.1 * t.2.2) heq
      have hψ : ψ (((t.1 * (t.2.1 * t.2.2) : ℕ)) : ZMod r)
          = ψ (((t.1 * t.2.1 * t.2.2 : ℕ)) : ZMod r) := by rw [Nat.mul_assoc]
      have hcond : (if t₁ * t₂ ∣ t.1 * t.2.1 * t.2.2 then (1:ℂ) else 0)
          = (if t₁ * t₂ ∣ t.1 * (t.2.1 * t.2.2) then (1:ℂ) else 0) := by
        rw [Nat.mul_assoc]
      show (if t.1 * (t.2.1 * t.2.2) ≤ x + 2 then (1:ℂ) else 0)
          * (aCoeff0 M Y t.1 * (if t₁ ∣ t.1 then (1:ℂ) else 0))
          * (bCoeff Y (t.2.1 * t.2.2) * (if t₂ ∣ t.2.1 * t.2.2 then (1:ℂ) else 0))
          * ψ (((t.1 * (t.2.1 * t.2.2) : ℕ)) : ZMod r)
        = (if t₁ * t₂ ∣ t.1 * t.2.1 * t.2.2 then (1:ℂ) else 0)
          * ψ (((t.1 * t.2.1 * t.2.2 : ℕ)) : ZMod r)
      rw [if_pos hif, ha, hb, hψ, hcond, ← hit]
      ring
    have step5 : (∑ t ∈ bTripleSet x M Y,
            (if t₁ * t₂ ∣ t.1 * t.2.1 * t.2.2 then (1:ℂ) else 0)
              * ψ (((t.1 * t.2.1 * t.2.2 : ℕ)) : ZMod r))
        = ∑ t ∈ (bTripleSet x M Y).filter (fun t => t₁ * t₂ ∣ t.1 * t.2.1 * t.2.2),
            ψ (((t.1 * t.2.1 * t.2.2 : ℕ)) : ZMod r) := by
      rw [Finset.sum_filter (s := bTripleSet x M Y)
        (p := fun t : ℕ × ℕ × ℕ => t₁ * t₂ ∣ t.1 * t.2.1 * t.2.2)
        (f := fun t : ℕ × ℕ × ℕ => ψ (((t.1 * t.2.1 * t.2.2 : ℕ)) : ZMod r))]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      by_cases h : t₁ * t₂ ∣ t.1 * t.2.1 * t.2.2 <;> simp [h]
    exact step1.trans (step2.trans (step3.trans (step4.trans step5)))
  exact hL.trans hR.symm

end Work.NumberTheory.Chen.BTermCount
