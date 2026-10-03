import Mathlib
import Submission.Work.FIChain.lamPlusBDefs
import Submission.Work.FIChain.LamPlusBLayerDefs
import Submission.Work.FIChain.lamPlusB_upper_moebius
import Submission.Work.FIChain.PerLayerDefs
import Submission.Work.FIChain.LamPlusBSieveAssembly
import Submission.Work.FIChain.GpB_eq_VfB_add_oddLayers

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-!
# `Work.FIChain.lamPlusB_sum_eq_GpB`

The Finset sum `∑_{ν ∈ [1,Δ], ν squarefree} λ⁺_B(ν) · ν_Δ(ν)` of the `B`-delay Rosser–Iwaniec
upper weight against the Friedlander–Iwaniec density equals the divisor sum
`GpB B ν_Δ y_Δ Δ = ∑_{d ∣ P(y_Δ)} [rdPlusB B Δ d] μ(d) ν_Δ(d)`.

The two sums are supported in the same place:

* every divisor of `P(y_Δ) = ∏_{p < y_Δ} p` is squarefree, and if it is admissible
  (`rdPlusB 19 Δ d`) it satisfies `d < Δ` (`rdPlusB_lt`), hence `d ∈ [1,Δ]`;
* conversely, `lamPlusB 19 Δ d ≠ 0` forces `rdPlusB 19 Δ d`, hence (by `lamPlusB_support`) every
  prime factor `p` of `d` satisfies `p ^ 20 ≤ Δ`, so `p < y_Δ = ⌈Δ^{1/20}⌉₊ + 1`
  (`prime_mem_PB_y20`) and, `d` being squarefree, `d ∣ P(y_Δ)`.

The transfer of the summation range is the elementary two-sided support lemma
`sum_eq_of_support_eq` below.
-/

/-- **Two-sided support transfer for Finset sums.**  If two finsets `S`, `T` contain the same
nonzero elements of `g`, then `∑_{a ∈ S} g a = ∑_{a ∈ T} g a`. -/
lemma sum_eq_of_support_eq {S T : Finset ℕ} {g : ℕ → ℝ}
    (hST : ∀ a ∈ S, g a ≠ 0 → a ∈ T) (hTS : ∀ a ∈ T, g a ≠ 0 → a ∈ S) :
    ∑ a ∈ S, g a = ∑ a ∈ T, g a := by
  have h1 : ∑ a ∈ S, g a = ∑ a ∈ S ∪ T, g a := by
    refine Finset.sum_subset Finset.subset_union_left ?_
    intro a ha hnot
    by_contra hne
    exact hnot (hTS a ((Finset.mem_union.mp ha).resolve_left hnot) hne)
  have h2 : ∑ a ∈ T, g a = ∑ a ∈ S ∪ T, g a := by
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro a ha hnot
    by_contra hne
    exact hnot (hST a ((Finset.mem_union.mp ha).resolve_right hnot) hne)
  rw [h1, h2]

/-- **The range transfer.**  The Finset sum over the squarefree `ν ≤ Δ` of the weighted density
`λ⁺_B(ν) · ν_Δ(ν)` is the divisor sum over `P(y_Δ) = ∏_{p < y_Δ} p`. -/
lemma lamPlusB_sum_filter_eq_sum_divisors (Δ : ℕ) (hΔ : 3 ≤ Δ) :
    (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        lamPlusB 19 (Δ : ℝ) ν * nuFI Δ ν)
      = ∑ d ∈ (PB (yFI Δ)).divisors, lamPlusB 19 (Δ : ℝ) d * nuFI Δ d := by
  have hceil : ⌈yFI Δ⌉₊ = y20 Δ := by
    have h : yFI Δ = (y20 Δ : ℝ) := by
      simp [yFI, y20, Nat.cast_add, Nat.cast_one]
    rw [h, Nat.ceil_natCast]
  have hD1 : (1 : ℝ) < (Δ : ℝ) := by exact_mod_cast (by omega : 1 < Δ)
  refine sum_eq_of_support_eq ?_ ?_
  · -- squarefree `ν ≤ Δ` with `λ⁺ ≠ 0` divides `P (yFI Δ)`
    intro d hdS hne
    rw [Finset.mem_filter, Finset.mem_Icc] at hdS
    obtain ⟨⟨hd1, hdle⟩, hdsq⟩ := hdS
    have hlam : lamPlusB 19 (Δ : ℝ) d ≠ 0 := fun h => hne (by rw [h, zero_mul])
    rw [Nat.mem_divisors]
    refine ⟨?_, PB_ne_zero _⟩
    rw [← Nat.prod_primeFactors_of_squarefree hdsq]
    rw [Nat.prod_primeFactors_dvd_iff (PB_ne_zero (yFI Δ))]
    intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have h20 : (p : ℝ) ^ (20 : ℕ) ≤ (Δ : ℝ) := by
      have h := lamPlusB_support hlam p hp
      rwa [show ((19 : ℝ) + 1) = ((20 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    rw [PB_primeFactors, hceil]
    exact prime_mem_PB_y20 hpp h20
  · -- a divisor of `P (yFI Δ)` with `λ⁺ ≠ 0` is a squarefree `ν ≤ Δ`
    intro d hdT hne
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hlam : lamPlusB 19 (Δ : ℝ) d ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have hdvd : d ∣ PB (yFI Δ) := (Nat.mem_divisors.mp hdT).1
    have hsq : Squarefree d := Squarefree.squarefree_of_dvd hdvd (PB_squarefree _)
    have hrd : rdPlusB 19 (Δ : ℝ) d := by
      by_contra h
      rw [lamPlusB, if_neg h] at hlam
      exact hlam rfl
    have hlt : (d : ℝ) < (Δ : ℝ) := rdPlusB_lt (by norm_num) hD1 hsq hrd
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hsq.ne_zero, le_of_lt (by exact_mod_cast hlt : d < Δ)⟩,
      hsq⟩

theorem lamPlusB_sum_eq_GpB (Δ : ℕ) (hΔ : 3 ≤ Δ) :
    (∑ ν ∈ (Finset.Icc 1 Δ).filter Squarefree,
        Work.FIChain.lamPlusB 19 (Δ : ℝ) ν * Work.FIChain.nuFI Δ ν)
      = Work.FIChain.GpB 19 (Work.FIChain.nuFI Δ) (Work.FIChain.yFI Δ) (Δ : ℝ) := by
  rw [lamPlusB_sum_filter_eq_sum_divisors Δ hΔ, GpB]
  exact Finset.sum_congr rfl (fun d _ => by simp only [lamPlusB])

end Work.FIChain
