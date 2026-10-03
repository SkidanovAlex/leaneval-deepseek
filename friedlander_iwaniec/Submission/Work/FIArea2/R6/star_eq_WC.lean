import Mathlib
import Submission.Work.FIArea2.R6.rect_quad_defs
import Submission.Work.FIArea2.R6.WCDefs

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- `nzB` and `zPz` denote the same non-zero integer box `[-N,N] \ {0}`. -/
private lemma nzB_eq_zPz (N : ℕ) : nzB N = zPz N := by rw [nzB]

/-- **The gcd-as-totient-sum identity.** For `D > 0`, `Σ_{c ∣ D} φ(c)·[c ∣ n] = gcd(D,n)`. -/
private lemma gcd_eq_sum_totient_ind (D n : ℕ) (hD : 0 < D) :
    (Nat.gcd D n : ℝ)
      = ∑ c ∈ D.divisors, (Nat.totient c : ℝ) * (if c ∣ n then (1 : ℝ) else 0) := by
  have hset : (Nat.gcd D n).divisors = D.divisors.filter (fun c => c ∣ n) := by
    ext c
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hcd, hcn⟩, _⟩
      exact ⟨⟨hcd, hD.ne'⟩, hcn⟩
    · rintro ⟨⟨hcd, _⟩, hcn⟩
      exact ⟨⟨hcd, hcn⟩, (Nat.gcd_pos_of_pos_left n hD).ne'⟩
  calc (Nat.gcd D n : ℝ)
      = ∑ c ∈ (Nat.gcd D n).divisors, (Nat.totient c : ℝ) := by
        rw [← Nat.cast_sum, Nat.sum_totient]
    _ = ∑ c ∈ D.divisors.filter (fun c => c ∣ n), (Nat.totient c : ℝ) := by rw [hset]
    _ = ∑ c ∈ D.divisors, (Nat.totient c : ℝ) * (if c ∣ n then (1 : ℝ) else 0) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        by_cases h : c ∣ n <;> simp [h]

/-- **Per-quadruple expansion of the gcd weight.**  For fixed `(h₁,h₂,w₁,w₂)` the weighted gcd
`gcd(D, |w₁h₁²-w₂h₂²|)/max(|w₁|,|w₂|)` (restricted to primitive `(w₁,w₂)` with `w₁h₁² ≠ w₂h₂²`)
is the `φ`-weighted sum over divisors `c ∣ D` of the indicator that `c ∣ w₁h₁²-w₂h₂²`. -/
private lemma key_term (D : ℕ) (hD : 0 < D) (a b u v : ℤ) :
    (if Nat.gcd u.natAbs v.natAbs = 1 ∧ u * a ^ 2 - v * b ^ 2 ≠ 0
       then (1 : ℝ) / ((max u.natAbs v.natAbs : ℕ) : ℝ)
         * (Nat.gcd D (u * a ^ 2 - v * b ^ 2).natAbs : ℝ)
       else 0)
      = ∑ c ∈ D.divisors, (Nat.totient c : ℝ)
          * (if Int.gcd u v = 1 ∧ u * a ^ 2 - v * b ^ 2 ≠ 0
               ∧ (c : ℤ) ∣ u * a ^ 2 - v * b ^ 2
             then (1 : ℝ) / ((max u.natAbs v.natAbs : ℕ) : ℝ) else 0) := by
  by_cases hP : Nat.gcd u.natAbs v.natAbs = 1 ∧ u * a ^ 2 - v * b ^ 2 ≠ 0
  · have hPg : Int.gcd u v = 1 := by rw [Int.gcd_eq_natAbs]; exact hP.1
    have hkey := gcd_eq_sum_totient_ind D (u * a ^ 2 - v * b ^ 2).natAbs hD
    rw [if_pos hP, hkey, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hz : (c : ℤ) ∣ u * a ^ 2 - v * b ^ 2 ↔ c ∣ (u * a ^ 2 - v * b ^ 2).natAbs := by
      have h := Int.natAbs_dvd_natAbs (a := (c : ℤ)) (b := u * a ^ 2 - v * b ^ 2)
      rw [Int.natAbs_natCast] at h
      exact h.symm
    by_cases hc' : (c : ℤ) ∣ u * a ^ 2 - v * b ^ 2
    · rw [if_pos (hz.mp hc'), if_pos ⟨hPg, hP.2, hc'⟩]
      ring
    · rw [if_neg (fun h => hc' (hz.mpr h)), if_neg (fun h => hc' h.2.2)]
      ring
  · rw [if_neg hP]
    refine (Finset.sum_eq_zero (fun c _ => ?_)).symm
    have hc' : ¬ (Int.gcd u v = 1 ∧ u * a ^ 2 - v * b ^ 2 ≠ 0
        ∧ (c : ℤ) ∣ u * a ^ 2 - v * b ^ 2) := by
      rintro ⟨hg, hne, _⟩
      rw [Int.gcd_eq_natAbs] at hg
      exact hP ⟨hg, hne⟩
    rw [if_neg hc', mul_zero]

/-- Swapping a sum over `c` past four `ℤ`-indexed sums. -/
private lemma sum5_comm {ι : Type*} (s : Finset ι) (A B C E : Finset ℤ)
    (f : ι → ℤ → ℤ → ℤ → ℤ → ℝ) :
    (∑ c ∈ s, ∑ h1 ∈ A, ∑ h2 ∈ B, ∑ w1 ∈ C, ∑ w2 ∈ E, f c h1 h2 w1 w2)
      = ∑ h1 ∈ A, ∑ h2 ∈ B, ∑ w1 ∈ C, ∑ w2 ∈ E, ∑ c ∈ s, f c h1 h2 w1 w2 := by
  rw [show (∑ c ∈ s, ∑ h1 ∈ A, ∑ h2 ∈ B, ∑ w1 ∈ C, ∑ w2 ∈ E, f c h1 h2 w1 w2)
      = (∑ h1 ∈ A, ∑ c ∈ s, ∑ h2 ∈ B, ∑ w1 ∈ C, ∑ w2 ∈ E, f c h1 h2 w1 w2)
      from Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h1 _ => ?_)
  rw [show (∑ c ∈ s, ∑ h2 ∈ B, ∑ w1 ∈ C, ∑ w2 ∈ E, f c h1 h2 w1 w2)
      = (∑ h2 ∈ B, ∑ c ∈ s, ∑ w1 ∈ C, ∑ w2 ∈ E, f c h1 h2 w1 w2)
      from Finset.sum_comm]
  refine Finset.sum_congr rfl (fun h2 _ => ?_)
  rw [show (∑ c ∈ s, ∑ w1 ∈ C, ∑ w2 ∈ E, f c h1 h2 w1 w2)
      = (∑ w1 ∈ C, ∑ c ∈ s, ∑ w2 ∈ E, f c h1 h2 w1 w2)
      from Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w1 _ => ?_)
  rw [show (∑ c ∈ s, ∑ w2 ∈ E, f c h1 h2 w1 w2)
      = (∑ w2 ∈ E, ∑ c ∈ s, f c h1 h2 w1 w2)
      from Finset.sum_comm]

theorem star_eq_WC (d r X Y : ℕ) (hd : 0 < d) :
    Work.FIArea2.R6.Star d r X Y
      = ∑ c ∈ d.divisors, (Nat.totient c : ℝ) * Work.FIArea2.R6.WC c r X Y := by
  rw [Work.FIArea2.R6.Star]
  simp only [Work.FIArea2.R6.WC]
  simp only [Finset.mul_sum]
  rw [sum5_comm d.divisors (zPz X) (zPz Y) (zPz r) (zPz r)]
  simp only [nzB_eq_zPz]
  refine Finset.sum_congr rfl (fun h1 _ => ?_)
  refine Finset.sum_congr rfl (fun h2 _ => ?_)
  refine Finset.sum_congr rfl (fun w1 _ => ?_)
  refine Finset.sum_congr rfl (fun w2 _ => ?_)
  exact key_term d hd h1 h2 w1 w2

end

end Work.FIArea2.R6
