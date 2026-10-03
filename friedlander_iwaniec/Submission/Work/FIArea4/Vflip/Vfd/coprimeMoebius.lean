import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.pairSum_large_sieve
import Submission.Work.FIArea4.Vflip.Vfd.coprimeSetup

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The Möbius expansion of a single summand carrying the coprimality condition. -/
lemma summand_moebius (R r1 r2 : ℕ) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2)
    (h1 : r1 ≤ 2*R) (h2 : r2 ≤ 2*R)
    (con : Prop) [Decidable con] (h : ℂ) :
    (if Nat.Coprime r1 r2 ∧ con then h else 0)
      = ∑ ρ ∈ Finset.Icc 1 (2*R),
          (if ρ ∣ r1 ∧ ρ ∣ r2 ∧ con then ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) * h else 0) := by
  have key : (if Nat.Coprime r1 r2 ∧ con then h else 0)
      = (if Nat.Coprime r1 r2 then (1:ℂ) else 0) * (if con then h else 0) := by
    by_cases hc : Nat.Coprime r1 r2 <;> by_cases hd : con <;> simp [hc, hd]
  have key2 : ∀ ρ : ℕ, (if ρ ∣ r1 ∧ ρ ∣ r2 ∧ con then ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) * h else 0)
      = (if ρ ∣ r1 ∧ ρ ∣ r2 then ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) else 0)
          * (if con then h else 0) := by
    intro ρ
    by_cases hd : ρ ∣ r1 ∧ ρ ∣ r2 <;> by_cases hc : con <;> simp [hd, hc]
  rw [key, coprime_indicator_sum R r1 r2 hr1 hr2 h1 h2, Finset.sum_mul]
  simp only [key2]

/-- Reindexing the `ρ`-multiples in a four-fold sum over the box. -/
lemma reindex_twice (R S ρ : ℕ) (hρ : 1 ≤ ρ) (F : ℕ → ℕ → ℕ → ℕ → ℂ) :
    (∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
     ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
       (if ρ ∣ r1 ∧ ρ ∣ r2 then F r1 s1 r2 s2 else 0))
    = ∑ u1 ∈ Finset.Icc 1 (2*R/ρ), ∑ s1 ∈ Finset.Icc 1 (2*S),
      ∑ u2 ∈ Finset.Icc 1 (2*R/ρ), ∑ s2 ∈ Finset.Icc 1 (2*S),
        F (ρ*u1) s1 (ρ*u2) s2 := by
  have h1 : (∑ r1 ∈ Finset.Icc 1 (2*R), ∑ s1 ∈ Finset.Icc 1 (2*S),
        ∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
          (if ρ ∣ r1 ∧ ρ ∣ r2 then F r1 s1 r2 s2 else 0))
      = ∑ r1 ∈ Finset.Icc 1 (2*R),
          (if ρ ∣ r1 then (∑ s1 ∈ Finset.Icc 1 (2*S), ∑ r2 ∈ Finset.Icc 1 (2*R),
            ∑ s2 ∈ Finset.Icc 1 (2*S), (if ρ ∣ r2 then F r1 s1 r2 s2 else 0)) else 0) := by
    refine Finset.sum_congr rfl (fun r1 _ => ?_)
    by_cases h : ρ ∣ r1
    · rw [if_pos h]
      refine Finset.sum_congr rfl (fun s1 _ => Finset.sum_congr rfl (fun r2 _ =>
        Finset.sum_congr rfl (fun s2 _ => ?_)))
      by_cases h2 : ρ ∣ r2
      · rw [if_pos ⟨h, h2⟩, if_pos h2]
      · rw [if_neg (fun hh => h2 hh.2), if_neg h2]
    · rw [if_neg h]
      exact Finset.sum_eq_zero (fun s1 _ => Finset.sum_eq_zero (fun r2 _ =>
        Finset.sum_eq_zero (fun s2 _ => by rw [if_neg (fun hh => h hh.1)])))
  rw [h1, ← Finset.sum_filter,
    sum_filter_dvd_Icc hρ (fun r1 => ∑ s1 ∈ Finset.Icc 1 (2*S), ∑ r2 ∈ Finset.Icc 1 (2*R),
      ∑ s2 ∈ Finset.Icc 1 (2*S), (if ρ ∣ r2 then F r1 s1 r2 s2 else 0))]
  refine Finset.sum_congr rfl (fun u1 _ => ?_)
  refine Finset.sum_congr rfl (fun s1 _ => ?_)
  have h2 : (∑ r2 ∈ Finset.Icc 1 (2*R), ∑ s2 ∈ Finset.Icc 1 (2*S),
        (if ρ ∣ r2 then F (ρ*u1) s1 r2 s2 else 0))
      = ∑ r2 ∈ Finset.Icc 1 (2*R),
          (if ρ ∣ r2 then (∑ s2 ∈ Finset.Icc 1 (2*S), F (ρ*u1) s1 r2 s2) else 0) := by
    refine Finset.sum_congr rfl (fun r2 _ => ?_)
    by_cases h : ρ ∣ r2
    · rw [if_pos h]
      exact Finset.sum_congr rfl (fun s2 _ => by rw [if_pos h])
    · rw [if_neg h]
      exact Finset.sum_eq_zero (fun s2 _ => by rw [if_neg h])
  rw [h2, ← Finset.sum_filter,
    sum_filter_dvd_Icc hρ (fun r2 => ∑ s2 ∈ Finset.Icc 1 (2*S), F (ρ*u1) s1 r2 s2)]

end

end Work.FIArea4.Vflip.Vfd
