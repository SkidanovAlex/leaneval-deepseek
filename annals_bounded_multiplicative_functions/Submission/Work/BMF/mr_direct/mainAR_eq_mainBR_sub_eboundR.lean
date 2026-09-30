import Mathlib
import Submission.Work.BMF.mr_direct.range_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open scoped BigOperators
open Work.BMF.mrDirect

/-- `Σ` over a filtered set plus its complement (local copy, to avoid the heavier import of
`buchstab_identity`). -/
lemma mainAR_sum_filter_add (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℂ) :
    (∑ x ∈ s.filter p, f x) + (∑ x ∈ s.filter (fun x => ¬ p x), f x) = ∑ x ∈ s, f x := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : p x <;> simp [h]

/-- The range regrouping identity `mainAR = mainBR - eboundR`.

The range analogue of `Work.BMF.mr_direct.bi_mainA_eq_mainB_sub_ebound`: the canonical window
`winIdxR K A B (jdex K p)` of a prime `p ∈ primeSet P Q` contains the Buchstab interval
`natIcc (A/p) (B/p)`, so the difference of the window sum and the extra-range sum is exactly
the Buchstab interval sum. -/
theorem mainAR_eq_mainBR_sub_eboundR (b c : ℕ → ℂ) (K P Q A B : ℝ) (hK : 0 < K) (hP : 2 ≤ P)
    (hPQ : P ≤ Q) (hA : 0 < A) (hB : 0 ≤ B) :
    ∀ t : ℝ, Work.BMF.mrDirect.mainAR b c P Q A B t
      = Work.BMF.mrDirect.mainBR b c K P Q A B t - Work.BMF.mrDirect.eboundR b c K P Q A B t := by
  intro t
  unfold mainAR mainBR eboundR
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hpp, hPp, hpQ⟩ := (mem_primeSet (by linarith : (0:ℝ) ≤ Q)).mp hp
  have hwidx : p ∈ winPrimes K (jdex K p) := mem_winPrimes_jdex hK hpp
  have hsub := natIcc_div_subset_winIdxR (le_of_lt hA) hB hwidx
  have hfilt : (winIdxR K A B (jdex K p)).filter
        (fun m => m ∈ Work.BMF.natIcc (A / p) (B / p))
      = Work.BMF.natIcc (A / p) (B / p) := by
    ext m
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  have hkey : (∑ m ∈ winIdxR K A B (jdex K p),
        b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      - (∑ m ∈ (winIdxR K A B (jdex K p)).filter
          (fun m => m ∉ Work.BMF.natIcc (A / p) (B / p)),
        b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = ∑ m ∈ Work.BMF.natIcc (A / p) (B / p),
        b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
    rw [← mainAR_sum_filter_add (winIdxR K A B (jdex K p))
      (fun m => m ∈ Work.BMF.natIcc (A / p) (B / p))
      (fun m => b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
        (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))), hfilt]
    ring
  rw [remPolyR_eq_winIdxR, ← mul_sub, hkey]

end Work.BMF.mr_direct
