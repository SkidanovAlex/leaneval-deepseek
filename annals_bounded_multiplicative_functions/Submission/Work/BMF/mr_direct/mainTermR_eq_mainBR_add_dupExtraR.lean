import Mathlib
import Submission.Work.BMF.mr_direct.range_defs
import Submission.Work.BMF.mr_direct.buchstab_identity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The regrouping `mainTermR = mainBR + dupExtraR`

This is the range-generalised analogue of
`Work.BMF.mr_direct.bi_mainTerm_eq_mainB_add_dupExtra`: the main term
`Σ_j primePoly_j · remPolyR_j` of the Buchstab/Ramaré decomposition, grouped by the
canonical logarithmic window `j = jdex K p` of each prime, equals the main term `mainBR`
plus the contribution `dupExtraR` of the primes that are counted in a non-canonical window
(or lie outside `[P,Q]`).
-/

set_option autoImplicit false

namespace Work.BMF

namespace mr_direct

open Work.BMF.mrDirect

theorem mainTermR_eq_mainBR_add_dupExtraR (b c : ℕ → ℂ) (K P Q A B : ℝ) (hK : 0 < K) (hP : 2 ≤ P)
    (hPQ : P ≤ Q) :
    ∀ t : ℝ, (∑ j ∈ Work.BMF.mrDirect.indexSet K P Q,
        Work.BMF.mrDirect.primePoly c K j t * Work.BMF.mrDirect.remPolyR b P Q K A B j t)
      = Work.BMF.mrDirect.mainBR b c K P Q A B t
        + Work.BMF.mrDirect.dupExtraR b c K P Q A B t := by
  intro t
  set Ψ : ℕ → ℂ := fun p =>
    c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) *
      (∑ m ∈ winIdxR K A B (jdex K p),
        b m * (((omegaCount P Q m : ℕ) + 1 : ℕ) : ℂ)⁻¹ *
          (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) with hΨ
  have hmainB : mainBR b c K P Q A B t = ∑ p ∈ primeSet P Q, Ψ p := by
    unfold mainBR
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [remPolyR_eq_winIdxR]
  have hsplit : ∀ j ∈ indexSet K P Q,
      primePoly c K j t * remPolyR b P Q K A B j t =
        (∑ p ∈ (winPrimes K j).filter
            (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p),
          c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) * remPolyR b P Q K A B j t
        + (∑ p ∈ (winPrimes K j).filter
            (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)),
          c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) * remPolyR b P Q K A B j t := by
    intro j hj
    rw [primePoly_eq, ← bi_sum_filter_add (winPrimes K j)
      (fun p => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)
      (fun p => c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))]
    ring
  have hdup : dupExtraR b c K P Q A B t =
      ∑ j ∈ indexSet K P Q,
        (∑ p ∈ (winPrimes K j).filter
            (fun (p : ℕ) => ¬ (P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p)),
          c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) * remPolyR b P Q K A B j t := rfl
  have hcanon : (∑ j ∈ indexSet K P Q,
        (∑ p ∈ (winPrimes K j).filter
            (fun (p : ℕ) => P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j = jdex K p),
          c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) * remPolyR b P Q K A B j t)
      = ∑ p ∈ primeSet P Q, Ψ p := by
    rw [bi_primeSet_group Ψ K P Q hK hP hPQ]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨-, -, hjd⟩ := (Finset.mem_filter.mp hp).2
    show c p * (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) * remPolyR b P Q K A B j t = Ψ p
    rw [hjd, hΨ]
    rw [remPolyR_eq_winIdxR]
  rw [hmainB, hdup, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hcanon]

end mr_direct

end Work.BMF
