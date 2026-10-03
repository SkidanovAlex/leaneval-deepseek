import Mathlib
import Submission.Work.FIArea4.flat_defs

/-!
# The bump sum over one residue class is bounded by the support count

For a bump majorant `f` with `0 ≤ f ≤ 1` supported in `[S/2, 5S/2]`, the lattice sum
`∑' m : ℤ, f (r a + m q)` over the arithmetic progression `r a + q ℤ` is at most the number of
elements of `suppBox S` lying in the residue class `r a mod q`.  Indeed every nonzero term of the
sum corresponds to a (positive) integer in `[S/2, 5S/2]` congruent to `r a` modulo `q`, and
different `m` give different integers.
-/

namespace Work.FIArea4

open Finset

lemma tsum_bump_le_card {S : ℕ} {f : ℝ → ℝ} (hS : 1 ≤ S)
    (hfnn : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hsupp : ∀ x, f x ≠ 0 → (S : ℝ) / 2 ≤ x ∧ x ≤ 5 * (S : ℝ) / 2)
    (r a q : ℕ) (hq : 0 < q) :
    ∑' m : ℤ, f ((r * a : ℝ) + (m : ℝ) * (q : ℝ))
      ≤ (((Work.FIArea4.suppBox S).filter (fun s => s % q = (r * a) % q)).card : ℝ) := by
  classical
  set Z : ℤ → ℤ := fun m => ((r * a : ℕ) : ℤ) + m * ((q : ℕ) : ℤ) with hZ
  have hZR : ∀ m : ℤ, ((Z m : ℤ) : ℝ) = (r * a : ℝ) + (m : ℝ) * (q : ℝ) := by
    intro m
    simp only [hZ]
    push_cast
    ring
  have hS1R : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqne : ((q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  -- the finite window containing the support
  set M : Finset ℤ := Finset.Icc (-((r * a : ℕ) : ℤ)) ((5 * S : ℕ) : ℤ) with hM
  have hsuppM : ∀ m : ℤ, f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) ≠ 0 → m ∈ M := by
    intro m hm
    obtain ⟨hlow, hhigh⟩ := hsupp _ hm
    rw [hM, Finset.mem_Icc]
    have hZRm : ((Z m : ℤ) : ℝ) = (r * a : ℝ) + (m : ℝ) * (q : ℝ) := hZR m
    have hZlow : (S : ℝ) / 2 ≤ (Z m : ℝ) := by rw [hZRm]; exact hlow
    have hZhigh : (Z m : ℝ) ≤ 5 * (S : ℝ) / 2 := by rw [hZRm]; exact hhigh
    have hran : (0 : ℝ) ≤ (r : ℝ) * (a : ℝ) := by positivity
    constructor
    · by_contra hcon
      rw [not_le] at hcon
      have hmneg : m < 0 := by
        have : (0 : ℤ) ≤ ((r * a : ℕ) : ℤ) := by positivity
        linarith
      have hmq : (m : ℝ) * (q : ℝ) ≤ (m : ℝ) := by
        have hmn : (m : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hmneg)
        have : (m : ℝ) * (q : ℝ) ≤ (m : ℝ) * 1 := mul_le_mul_of_nonpos_left hq1R hmn
        linarith
      have hlt' : (m : ℝ) + (r : ℝ) * (a : ℝ) < 0 := by
        have hh : (m : ℝ) < -(((r * a : ℕ)) : ℝ) := by
          have hh0 : (m : ℝ) < ((-((r * a : ℕ) : ℤ)) : ℝ) := by exact_mod_cast hcon
          simpa using hh0
        have hcast : (((r * a : ℕ)) : ℝ) = (r : ℝ) * (a : ℝ) := by push_cast; ring
        linarith
      have : (0 : ℝ) < (S : ℝ) / 2 := by linarith
      linarith
    · have hmle : (m : ℝ) ≤ 5 * (S : ℝ) / 2 := by
        rcases lt_or_ge m (0 : ℤ) with hm0 | hm0
        · have hm0R : (m : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hm0)
          linarith
        · have hm0R : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm0
          have : (m : ℝ) ≤ (m : ℝ) * (q : ℝ) := by nlinarith
          linarith
      have hmle' : (m : ℝ) ≤ (((5 * S : ℕ)) : ℝ) := by
        have : 5 * (S : ℝ) / 2 ≤ (((5 * S : ℕ)) : ℝ) := by push_cast; nlinarith
        linarith
      exact_mod_cast hmle'
  have hg0 : ∀ m ∉ M, f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) = 0 := by
    intro m hm
    by_contra h
    exact hm (hsuppM m h)
  set T : Finset ℕ := (Work.FIArea4.suppBox S).filter (fun s => s % q = (r * a) % q) with hT
  have hZnn : ∀ m : ℤ, f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) ≠ 0 → 0 ≤ Z m := by
    intro m hm
    have hlow := (hsupp _ hm).1
    have hZlow : (S : ℝ) / 2 ≤ (Z m : ℝ) := by rw [hZR m]; exact hlow
    have : (0 : ℝ) < (Z m : ℝ) := by linarith
    exact_mod_cast (le_of_lt this)
  have hZmod : ∀ m : ℤ, 0 ≤ Z m → (Z m).toNat % q = (r * a) % q := by
    intro m hz
    have h1 : Z m % ((q : ℕ) : ℤ) = (((r * a) % q : ℕ) : ℤ) := by
      simp only [hZ]
      rw [Int.add_mul_emod_self_right]
      exact (Int.natCast_emod (r * a) q).symm
    have hq0 : (0 : ℤ) ≤ ((q : ℕ) : ℤ) := by positivity
    have h2 : (Z m).toNat % q = (Z m % ((q : ℕ) : ℤ)).toNat := by
      have hh := Int.toNat_emod hz hq0
      rw [Int.toNat_natCast] at hh
      exact hh.symm
    rw [h2, h1, Int.toNat_natCast]
  have hZsR : ∀ m : ℤ, 0 ≤ Z m → (((Z m).toNat : ℕ) : ℝ) = (Z m : ℝ) := by
    intro m hz
    have hh := Int.toNat_of_nonneg hz
    have hh2 := congrArg (fun t : ℤ => (t : ℝ)) hh
    push_cast at hh2
    exact hh2
  have hZs_le : ∀ m : ℤ, f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) ≠ 0 → (Z m).toNat ≤ 5 * S / 2 := by
    intro m hm
    have hZnn := hZnn m hm
    have hhigh := (hsupp _ hm).2
    have hZhigh : (Z m : ℝ) ≤ 5 * (S : ℝ) / 2 := by rw [hZR m]; exact hhigh
    have hsR := hZsR m hZnn
    rw [Nat.le_div_iff_mul_le (by norm_num : (0:ℕ) < 2)]
    have : (((Z m).toNat : ℕ) : ℝ) * 2 ≤ (((5 * S : ℕ)) : ℝ) := by
      rw [hsR]; push_cast; linarith
    exact_mod_cast this
  have hZs_pos : ∀ m : ℤ, f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) ≠ 0 → 1 ≤ (Z m).toNat := by
    intro m hm
    have hlow := (hsupp _ hm).1
    have hZlow : (S : ℝ) / 2 ≤ (Z m : ℝ) := by rw [hZR m]; exact hlow
    have hZpos : (0 : ℤ) < Z m := by
      have : (0 : ℝ) < (Z m : ℝ) := by linarith
      exact_mod_cast this
    have : (1 : ℤ) ≤ ((Z m).toNat : ℤ) := by
      rw [Int.toNat_of_nonneg (le_of_lt hZpos)]; omega
    exact_mod_cast this
  have hZs_lo : ∀ m : ℤ, f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) ≠ 0 → S / 2 - 1 < (Z m).toNat := by
    intro m hm
    have hlow := (hsupp _ hm).1
    have hZlow : (S : ℝ) / 2 ≤ (Z m : ℝ) := by rw [hZR m]; exact hlow
    have hZnn := hZnn m hm
    have hsR := hZsR m hZnn
    have hSle : S ≤ 2 * (Z m).toNat := by
      have : (S : ℝ) ≤ 2 * (((Z m).toNat : ℕ) : ℝ) := by rw [hsR]; linarith
      exact_mod_cast this
    have hhalf : S / 2 ≤ (Z m).toNat := by
      rw [Nat.div_le_iff_le_mul_add_pred (by norm_num : (0:ℕ) < 2)]
      omega
    have hpos := hZs_pos m hm
    omega
  have hinj : Set.InjOn (fun m : ℤ => (Z m).toNat)
      ↑(M.filter (fun m : ℤ => f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) ≠ 0)) := by
    intro m1 h1 m2 h2 heq
    rw [Finset.mem_coe, Finset.mem_filter] at h1 h2
    have hz1 := hZnn m1 h1.2
    have hz2 := hZnn m2 h2.2
    have e1 : Z m1 = ((Z m1).toNat : ℤ) := (Int.toNat_of_nonneg hz1).symm
    have e2 : Z m2 = ((Z m2).toNat : ℤ) := (Int.toNat_of_nonneg hz2).symm
    have heq' : (Z m1).toNat = (Z m2).toNat := heq
    have hEq : ((Z m1).toNat : ℤ) = ((Z m2).toNat : ℤ) := by rw [heq']
    have hZZ : Z m1 = Z m2 := by rw [e1, e2, hEq]
    simp only [hZ] at hZZ
    have : m1 * ((q : ℕ) : ℤ) = m2 * ((q : ℕ) : ℤ) := by linarith
    exact mul_right_cancel₀ hqne this
  have hmaps : Set.MapsTo (fun m : ℤ => (Z m).toNat)
      ↑(M.filter (fun m : ℤ => f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) ≠ 0)) ↑T := by
    intro m hm
    rw [Finset.mem_coe, Finset.mem_filter] at hm
    rw [Finset.mem_coe, hT, Finset.mem_filter]
    exact ⟨by rw [Work.FIArea4.suppBox, Finset.mem_Ioc]; exact ⟨hZs_lo m hm.2, hZs_le m hm.2⟩,
      hZmod m (hZnn m hm.2)⟩
  have hcard : (M.filter (fun m : ℤ => f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) ≠ 0)).card ≤ T.card :=
    Finset.card_le_card_of_injOn (fun m : ℤ => (Z m).toNat) hmaps hinj
  rw [tsum_eq_sum (s := M) hg0]
  calc ∑ m ∈ M, f ((r * a : ℝ) + (m : ℝ) * (q : ℝ))
      ≤ ∑ m ∈ M, (if f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) ≠ 0 then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro m _
        by_cases h : f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) = 0
        · rw [h]; simp
        · rw [if_pos h]; exact hf1 _
    _ = ((M.filter (fun m : ℤ => f ((r * a : ℝ) + (m : ℝ) * (q : ℝ)) ≠ 0)).card : ℝ) := by
        rw [Finset.sum_boole]
    _ ≤ (T.card : ℝ) := by exact_mod_cast hcard
    _ = (((Work.FIArea4.suppBox S).filter (fun s => s % q = (r * a) % q)).card : ℝ) := by rw [hT]

end Work.FIArea4
