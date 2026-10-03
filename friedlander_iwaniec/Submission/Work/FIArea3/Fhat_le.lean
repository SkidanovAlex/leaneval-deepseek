import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FITop3.Majorant.fhat_upper

namespace Work.FIArea3

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The (7.7) mean value `Fhat Pa f = Σ_{⌊M/4⌋ ≤ u ≤ ⌈4M⌉} f u / √u` of a majorant is bounded by
`7√M`: `f ≤ 1` and the elementary telescoping bound `Σ_{u=1}^{b} 1/√u ≤ 2√b`.  (This is the
unconditional form of `Majorant.fhat_upper`, which assumes `16 ≤ M`.) -/
theorem Fhat_le (Pa : Work.FITop.Params) (f : ℤ → ℝ) (h : Work.FITop3.IsMajorant Pa f) :
    Work.FITop3.Fhat Pa f ≤ 7 * Real.sqrt Pa.M := by
  unfold Work.FITop3.Fhat
  set A : ℤ := ((⌊Pa.M / 4⌋₊ : ℕ) : ℤ) with hAdef
  set B : ℤ := ((⌈4 * Pa.M⌉₊ : ℕ) : ℤ) with hBdef
  set D : ℤ := ((⌊4 * Pa.M⌋₊ : ℕ) : ℤ) with hDdef
  have hM1 : (1:ℝ) ≤ Pa.M := by exact_mod_cast Pa.hM1
  have hMpos : (0:ℝ) < Pa.M := lt_of_lt_of_le (by norm_num) hM1
  -- step 1: termwise `f u / √u ≤ 1 / √u` on the support of `f`, and `0` off it
  have hstep1 : ∑ u ∈ Finset.Icc A B, f u / Real.sqrt (u : ℝ)
      ≤ ∑ u ∈ (Finset.Icc A B).filter (fun u => f u ≠ 0), (1:ℝ) / Real.sqrt (u : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro u _
    by_cases hf : f u = 0
    · rw [if_neg (by simp [hf]), hf]; simp
    · rw [if_pos hf]
      exact div_le_div_of_nonneg_right (h.2.1 u) (Real.sqrt_nonneg _)
  -- step 2: the support of `f` sits inside `[1, ⌊4M⌋]`
  have hsubset : (Finset.Icc A B).filter (fun u => f u ≠ 0) ⊆ Finset.Icc (1:ℤ) D := by
    intro u hu
    rw [Finset.mem_filter, Finset.mem_Icc] at hu
    obtain ⟨⟨hlo, hhi⟩, hfne⟩ := hu
    obtain ⟨hsup1, hsup2⟩ := h.2.2.2.1 u hfne
    have hpos : (0:ℝ) < (u:ℝ) := lt_of_lt_of_le (by linarith) hsup1
    have h1 : (1:ℤ) ≤ u := by
      have h0u : (0:ℤ) < u := by exact_mod_cast hpos
      omega
    have hu0 : (0:ℤ) ≤ u := le_trans (by norm_num) h1
    have htoNat : ((u.toNat : ℕ) : ℝ) = (u:ℝ) := by
      have hnat : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg hu0
      exact_mod_cast hnat
    have hle4M : ((u.toNat : ℕ) : ℝ) ≤ 4 * Pa.M := by rw [htoNat]; exact hsup2
    have hfloor : u.toNat ≤ ⌊4 * Pa.M⌋₊ := (Nat.le_floor_iff (by linarith)).mpr hle4M
    have hDz : ((u.toNat : ℕ) : ℤ) ≤ D := by
      rw [hDdef]
      exact_mod_cast hfloor
    have h2 : u ≤ D := by
      have hnat : ((u.toNat : ℕ) : ℤ) = u := Int.toNat_of_nonneg hu0
      rw [← hnat]
      exact hDz
    rw [Finset.mem_Icc]
    exact ⟨h1, h2⟩
  -- step 3: enlarge the summation set to `[1, ⌊4M⌋]`
  have hstep3 : ∑ u ∈ (Finset.Icc A B).filter (fun u => f u ≠ 0), (1:ℝ) / Real.sqrt (u : ℝ)
      ≤ ∑ u ∈ Finset.Icc (1:ℤ) D, (1:ℝ) / Real.sqrt (u : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun i _ _ => div_nonneg zero_le_one (Real.sqrt_nonneg _))
  -- step 4: `Σ_{u ≤ ⌊4M⌋} 1/√u ≤ 2√⌊4M⌋ ≤ 2√(4M) = 4√M ≤ 7√M`
  have hstep4 : ∑ u ∈ Finset.Icc (1:ℤ) D, (1:ℝ) / Real.sqrt (u : ℝ) ≤ 7 * Real.sqrt Pa.M := by
    rw [hDdef]
    have h1 : ∑ u ∈ Finset.Icc (1:ℤ) (((⌊4 * Pa.M⌋₊ : ℕ) : ℤ)), (1:ℝ) / Real.sqrt (u : ℝ)
        ≤ 2 * Real.sqrt ((⌊4 * Pa.M⌋₊ : ℝ)) :=
      Work.FITop3.Majorant.sum_Icc_one_sqrt_le ⌊4 * Pa.M⌋₊
    have hfl : ((⌊4 * Pa.M⌋₊ : ℕ) : ℝ) ≤ 4 * Pa.M := Nat.floor_le (by linarith)
    have hsqrt : Real.sqrt ((⌊4 * Pa.M⌋₊ : ℝ)) ≤ 2 * Real.sqrt Pa.M := by
      refine le_trans (Real.sqrt_le_sqrt hfl) ?_
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      have h4 : Real.sqrt (4:ℝ) = 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h4]
    have hnonneg : 0 ≤ Real.sqrt Pa.M := Real.sqrt_nonneg _
    linarith
  linarith [hstep1, hstep3, hstep4]

end

end Work.FIArea3
